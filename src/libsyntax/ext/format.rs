// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use self::ArgumentType::*;
use self::Position::*;

use ast;
use codemap::Span;
use ext::base::*;
use ext::base;
use ext::build::AstBuilder;
use fmt_macros as parse;
use fold::Folder;
use parse::token;
use ptr::P;

use std::collections::HashMap;

#[derive(PartialEq)]
enum ArgumentType {
    Known(String),
    Unsigned
}

enum Position {
    Exact(usize),
    Named(String),
}

enum Count {
    None,
    Lit(usize),
    Arg(Position),
}

struct Piece {
    arg: Position,
    ty: String, 

    flags: u32,
    alignment: P<ast::Expr>,
    fill: Option<char>,
    precision: Count,
    width: Count,
}

struct Context<'a, 'b:'a> {
    ecx: &'a mut ExtCtxt<'b>,
    /// The macro's call site. References to unstable formatting internals must
    /// use this span to pass the stability checker.
    macsp: Span,
    /// The span of the format string literal.
    fmtsp: Span,

    /// Parsed argument expressions and the types that we've found so far for
    /// them.
    args: Vec<P<ast::Expr>>,
    arg_types: Vec<Option<ArgumentType>>,
    /// Parsed named expressions and the types that we've found for them so far.
    /// Note that we keep a side-array of the ordering of the named arguments
    /// found to be sure that we can translate them in the same order that they
    /// were declared in.
    names: HashMap<String, P<ast::Expr>>,
    name_types: HashMap<String, ArgumentType>,
    name_ordering: Vec<String>,

    /// The latest consecutive literal strings, or empty if there weren't any.
    literal: String,

    /// Collection of the compiled `rt::Argument` structures
    //pieces: Vec<P<ast::Expr>>,
    pieces: Vec<Piece>,
    /// Collection of string literals
    str_pieces: Vec<P<ast::Expr>>,

    name_positions: HashMap<String, usize>,

    /// Updated as arguments are consumed or methods are entered
    nest_level: usize,
    next_arg: usize,
    next_arg_trans: usize,
}

/// Parses the arguments from the given list of tokens, returning None
/// if there's a parse error so we can continue parsing other format!
/// expressions.
///
/// If parsing succeeds, the return value is:
///
///     Some((fmtstr, unnamed arguments, ordering of named arguments,
///           named arguments))
fn parse_args(ecx: &mut ExtCtxt, sp: Span, tts: &[ast::TokenTree])
              -> Option<(P<ast::Expr>, Vec<P<ast::Expr>>, Vec<String>,
                         HashMap<String, P<ast::Expr>>)> {
    let mut args = Vec::new();
    let mut names = HashMap::<String, P<ast::Expr>>::new();
    let mut order = Vec::new();

    let mut p = ecx.new_parser_from_tts(tts);

    if p.token == token::Eof {
        ecx.span_err(sp, "requires at least a format string argument");
        return None;
    }
    let fmtstr = p.parse_expr();
    let mut named = false;
    while p.token != token::Eof {
        if !panictry!(p.eat(&token::Comma)) {
            ecx.span_err(sp, "expected token: `,`");
            return None;
        }
        if p.token == token::Eof { break } // accept trailing commas
        if named || (p.token.is_ident() && p.look_ahead(1, |t| *t == token::Eq)) {
            named = true;
            let ident = match p.token {
                token::Ident(i, _) => {
                    panictry!(p.bump());
                    i
                }
                _ if named => {
                    ecx.span_err(p.span,
                                 "expected ident, positional arguments \
                                 cannot follow named arguments");
                    return None;
                }
                _ => {
                    ecx.span_err(p.span,
                                 &format!("expected ident for named argument, found `{}`",
                                         p.this_token_to_string()));
                    return None;
                }
            };
            let name: &str = &ident.name.as_str();

            panictry!(p.expect(&token::Eq));
            let e = p.parse_expr();
            match names.get(name) {
                None => {}
                Some(prev) => {
                    ecx.span_err(e.span,
                                 &format!("duplicate argument named `{}`",
                                         name));
                    ecx.parse_sess.span_diagnostic.span_note(prev.span, "previously here");
                    continue
                }
            }
            order.push(name.to_string());
            names.insert(name.to_string(), e);
        } else {
            args.push(p.parse_expr());
        }
    }
    Some((fmtstr, args, order, names))
}

impl<'a, 'b> Context<'a, 'b> {
    /// Verifies one piece of a parse string. All errors are not emitted as
    /// fatal so we can continue giving errors about this and possibly other
    /// format strings.
    fn verify_piece(&mut self, p: &parse::Piece) {
        match *p {
            parse::String(..) => {}
            parse::NextArgument(ref arg) => {
                // width/precision first, if they have implicit positional
                // parameters it makes more sense to consume them first.
                self.verify_count(arg.format.width);
                self.verify_count(arg.format.precision);

                // argument second, if it's an implicit positional parameter
                // it's written second, so it should come after width/precision.
                let pos = match arg.position {
                    parse::ArgumentNext => {
                        let i = self.next_arg;
                        if self.check_positional_ok() {
                            self.next_arg += 1;
                        }
                        Exact(i)
                    }
                    parse::ArgumentIs(i) => Exact(i),
                    parse::ArgumentNamed(s) => Named(s.to_string()),
                };

                let ty = Known(arg.format.ty.to_string());
                self.verify_arg_type(pos, ty);
            }
        }
    }

    fn verify_count(&mut self, c: parse::Count) {
        match c {
            parse::CountImplied | parse::CountIs(..) => {}
            parse::CountIsParam(i) => {
                self.verify_arg_type(Exact(i), Unsigned);
            }
            parse::CountIsName(s) => {
                self.verify_arg_type(Named(s.to_string()), Unsigned);
            }
            parse::CountIsNextParam => {
                if self.check_positional_ok() {
                    let next_arg = self.next_arg;
                    self.verify_arg_type(Exact(next_arg), Unsigned);
                    self.next_arg += 1;
                }
            }
        }
    }

    fn check_positional_ok(&mut self) -> bool {
        if self.nest_level != 0 {
            self.ecx.span_err(self.fmtsp, "cannot use implicit positional \
                                           arguments nested inside methods");
            false
        } else {
            true
        }
    }

    fn describe_num_args(&self) -> String {
        match self.args.len() {
            0 => "no arguments given".to_string(),
            1 => "there is 1 argument".to_string(),
            x => format!("there are {} arguments", x),
        }
    }

    fn verify_arg_type(&mut self, arg: Position, ty: ArgumentType) {
        match arg {
            Exact(arg) => {
                if self.args.len() <= arg {
                    let msg = format!("invalid reference to argument `{}` ({})",
                                      arg, self.describe_num_args());

                    self.ecx.span_err(self.fmtsp, &msg[..]);
                    return;
                }
                {
                    let arg_type = match self.arg_types[arg] {
                        None => None,
                        Some(ref x) => Some(x)
                    };
                    self.verify_same(self.args[arg].span, &ty, arg_type);
                }
                if self.arg_types[arg].is_none() {
                    self.arg_types[arg] = Some(ty);
                }
            }

            Named(name) => {
                let span = match self.names.get(&name) {
                    Some(e) => e.span,
                    None => {
                        let msg = format!("there is no argument named `{}`", name);
                        self.ecx.span_err(self.fmtsp, &msg[..]);
                        return;
                    }
                };
                self.verify_same(span, &ty, self.name_types.get(&name));
                if !self.name_types.contains_key(&name) {
                    self.name_types.insert(name.clone(), ty);
                }
                // Assign this named argument a slot in the arguments array if
                // it hasn't already been assigned a slot.
                if !self.name_positions.contains_key(&name) {
                    let slot = self.name_positions.len();
                    self.name_positions.insert(name, slot);
                }
            }
        }
    }

    /// When we're keeping track of the types that are declared for certain
    /// arguments, we assume that `None` means we haven't seen this argument
    /// yet, `Some(None)` means that we've seen the argument, but no format was
    /// specified, and `Some(Some(x))` means that the argument was declared to
    /// have type `x`.
    ///
    /// Obviously `Some(Some(x)) != Some(Some(y))`, but we consider it true
    /// that: `Some(None) == Some(Some(x))`
    fn verify_same(&self,
                   sp: Span,
                   ty: &ArgumentType,
                   before: Option<&ArgumentType>) {
        let cur = match before {
            None => return,
            Some(t) => t,
        };
        if *ty == *cur {
            return
        }
        match (cur, ty) {
            (&Known(ref cur), &Known(ref ty)) => {
                self.ecx.span_err(sp,
                                  &format!("argument redeclared with type `{}` when \
                                           it was previously `{}`",
                                          *ty,
                                          *cur));
            }
            (&Known(ref cur), _) => {
                self.ecx.span_err(sp,
                                  &format!("argument used to format with `{}` was \
                                           attempted to not be used for formatting",
                                           *cur));
            }
            (_, &Known(ref ty)) => {
                self.ecx.span_err(sp,
                                  &format!("argument previously used as a format \
                                           argument attempted to be used as `{}`",
                                           *ty));
            }
            (_, _) => {
                self.ecx.span_err(sp, "argument declared with multiple formats");
            }
        }
    }

    fn rtpath(ecx: &ExtCtxt, s: &str) -> Vec<ast::Ident> {
        ecx.std_path(&["fmt", "rt", "v1", s])
    }

    /// Translate the accumulated string literals to a literal expression
    fn trans_literal_string(&mut self) -> P<ast::Expr> {
        let sp = self.fmtsp;
        let s = token::intern_and_get_ident(&self.literal);
        self.literal.clear();
        self.ecx.expr_str(sp, s)
    }

    /// Translate a `parse::Piece` to a static `rt::Argument` or append
    /// to the `literal` string.
    fn trans_piece(&mut self, piece: &parse::Piece) -> Option<Piece> {
        let sp = self.macsp;
        match *piece {
            parse::String(s) => {
                self.literal.push_str(s);
                None
            }
            parse::NextArgument(ref arg) => {
                // - Translate Alignment
                let align = {
                    let align = {
                        let align = |name| {
                            let mut p = Context::rtpath(self.ecx, "Alignment");
                            p.push(self.ecx.ident_of(name));
                            self.ecx.path_global(sp, p)
                        };
                        match arg.format.align {
                            parse::AlignLeft => align("Left"),
                            parse::AlignRight => align("Right"),
                            parse::AlignCenter => align("Center"),
                            parse::AlignUnknown => align("Unknown"),
                        }
                        };
                    self.ecx.expr_path(align)
                    };
                let mut translate_pos = |pos|
                    match pos {
                        parse::ArgumentNext => {
                            // NOTE: verify_piece checks this
                            self.next_arg_trans += 1;
                            Position::Exact(self.next_arg_trans - 1)
                            },
                        parse::ArgumentIs(i) => Position::Exact(i),
                        parse::ArgumentNamed(n) => Position::Named( String::from(n) ),
                    }
                    ;
                let arg_pos = translate_pos(arg.position);
                // - Transator for width/precision
                let mut translate_count = |count|
                    match count
                    {
                    parse::Count::CountImplied => Count::None,
                    parse::Count::CountIs(v) => Count::Lit(v),
                    parse::Count::CountIsNextParam => Count::Arg( translate_pos(parse::ArgumentNext) ),
                    parse::Count::CountIsParam(i) => Count::Arg( translate_pos(parse::ArgumentIs(i)) ),
                    parse::Count::CountIsName(n) => Count::Arg( translate_pos(parse::ArgumentNamed(n)) ),
                    }
                    ;
                Some(Piece {
                    arg: arg_pos,
                    ty: String::from(arg.format.ty),

                    flags: arg.format.flags,
                    alignment: align,
                    fill: arg.format.fill,
                    precision: translate_count(arg.format.precision),
                    width: translate_count(arg.format.width),
                    })
            }
        }
    }

    /// Actually builds the expression which the iformat! block will be expanded
    /// to
    fn into_expr(mut self) -> P<ast::Expr> {
        let mut pos_arg_idents = Vec::new();
        let mut name_arg_idents = vec![None; self.name_positions.len()];
        let mut pats = Vec::new();  // match arm patterns (bindings to names)
        let mut heads = Vec::new(); // match's value

        // Right now there is a bug such that for the expression:
        //      foo(bar(&1))
        // the lifetime of `1` doesn't outlast the call to `bar`, so it's not
        // valid for the call to `foo`. To work around this all arguments to the
        // format! string are shoved into locals. Furthermore, we shove the address
        // of each variable because we don't want to move out of the arguments
        // passed to this function.

        let mut arg_spans = Vec::new();
        // Create bindings for all arguments
        for (i, e) in self.args.into_iter().enumerate() {
            arg_spans.push( e.span );

            let name = self.ecx.ident_of(&format!("__arg{}", i));
            pats.push(self.ecx.pat_ident(e.span, name));
            pos_arg_idents.push( self.ecx.expr_ident(e.span, name) );
            heads.push(self.ecx.expr_addr_of(e.span, e));
        }
        for name in &self.name_ordering {
            let e = match self.names.remove(name) {
                Some(e) => e,
                None => continue
            };

            arg_spans.push( e.span );

            let lname = self.ecx.ident_of(&format!("__arg{}", *name));
            pats.push( self.ecx.pat_ident(e.span, lname) );
            let name_index = *self.name_positions.get(name).unwrap();
            name_arg_idents[name_index] = Some( self.ecx.expr_ident(e.span, lname) );
            heads.push( self.ecx.expr_addr_of(e.span, e) );
        }

        let block = {
            let cparam_f = self.ecx.expr_ident(self.fmtsp, self.ecx.ident_of("f"));
            let mut calls = Vec::new();
            let name_positions = &self.name_positions;
            for (lit, piece) in Iterator::zip( self.str_pieces.into_iter(), self.pieces.into_iter().map(|v| Some(v)).chain(Some(None)) )
            {
                let fmtsp = self.fmtsp;
                let macsp = self.macsp;

                // 1. Print literal string
                let call = self.ecx.expr_method_call(self.fmtsp, cparam_f.clone(), self.ecx.ident_of("write_str"), vec![lit]);
                let try = self.ecx.expr_try(self.fmtsp, call);
                calls.push(self.ecx.stmt_expr( try ));

                if let Some(piece) = piece
                {
                    let get_arg_idx = |pos: &Position|
                        match pos {
                        &Position::Exact(i) => i,
                        &Position::Named(ref n) => pos_arg_idents.len() + name_positions[n],
                        }
                        ;
                    let get_arg_varname = |pos: &Position|
                        match pos {
                        &Position::Exact(i) => pos_arg_idents[i].clone(),
                        &Position::Named(ref n) => name_arg_idents[ name_positions[n] ].as_ref().unwrap().clone(),
                        }
                        ;
                    let set_value_e = |calls: &mut Vec<_>, ecx: &mut ExtCtxt, fcn_name, value_expr|
                        calls.push(ecx.stmt_expr( ecx.expr_method_call(macsp, cparam_f.clone(), ecx.ident_of(fcn_name), vec![ value_expr ]) ))
                            ;
                    let set_value = |calls: &mut _, ecx: &mut ExtCtxt, value, fcn_name|
                            match value {
                        Count::None => {},
                        Count::Lit(v) => {
                            let expr = ecx.expr_usize(fmtsp, v);
                            set_value_e(calls,ecx, fcn_name, expr)
                            },
                        Count::Arg(ref pos) => {
                            //let call =  ecx.expr_call_global(sp, ecx.std_path(&["fmt", "Formatter", "get_usize"]), vec![get_arg_varname(pos)]);
                            let call = ecx.expr_deref(fmtsp, get_arg_varname(pos));
                            set_value_e(calls,ecx, fcn_name, call)
                            },
                        }
                        ;

                    // 2. Print actual data
                    // - Reset the formatter
                    calls.push(self.ecx.stmt_expr( self.ecx.expr_method_call(self.macsp, cparam_f.clone(), self.ecx.ident_of("reset"), vec![
                        self.ecx.expr_u32(self.fmtsp, piece.flags),
                        piece.alignment,
                        ]) ));
                    // - Set fill
                    if let Some(c) = piece.fill {
                        calls.push(self.ecx.stmt_expr( self.ecx.expr_method_call(macsp,
                            cparam_f.clone(), self.ecx.ident_of("set_fill"), vec![ self.ecx.expr_lit(fmtsp, ast::LitChar(c)) ]
                            ) ));
                    }
                    // - Set precision and width
                    set_value(&mut calls, self.ecx, piece.precision, "set_precision");
                    set_value(&mut calls, self.ecx, piece.width, "set_width");

                    // - Call formatter
                    let arg_span = arg_spans[ get_arg_idx(&piece.arg) ];
                    let format_fn = self.ecx.std_path(&["fmt", Context::trait_name(self.ecx, arg_span, &piece.ty), "fmt"]);
                    let call = self.ecx.expr_call_global(fmtsp, format_fn, vec![ get_arg_varname(&piece.arg), cparam_f.clone()] );
                    let try = self.ecx.expr_try(self.fmtsp, call);
                    calls.push(self.ecx.stmt_expr( try ));
                }
            }
            if calls.len() == 0 {
                calls.push(self.ecx.stmt_let(self.macsp, false, self.ecx.ident_of("_"), cparam_f));
            }

            //self.ecx.expr_block( self.ecx.block(self.fmtsp, calls, Some(self.ecx.expr_ok(self.fmtsp, self.ecx.expr_tuple(self.fmtsp, vec![]))) ) )
            self.ecx.block( self.fmtsp, calls, Some(self.ecx.expr_ok(self.fmtsp, self.ecx.expr_tuple(self.fmtsp, vec![]))) )
            };

        // Constructs an AST equivalent to:
        //
        //      match (&arg0, &arg1) {
        //          (tmp0, tmp1) => args_array
        //      }
        //
        // It was:
        //
        //      let tmp0 = &arg0;
        //      let tmp1 = &arg1;
        //      args_array
        //
        // Because of #11585 the new temporary lifetime rule, the enclosing
        // statements for these temporaries become the let's themselves.
        // If one or more of them are RefCell's, RefCell borrow() will also
        // end there; they don't last long enough for args_array to use them.
        // The match expression solves the scope problem.
        //
        // Note, it may also very well be transformed to:
        //
        //      match arg0 {
        //          ref tmp0 => {
        //              match arg1 => {
        //                  ref tmp1 => args_array } } }
        //
        // But the nested match expression is proved to perform not as well
        // as series of let's; the first approach does.
        let closure = self.ecx.lambda_move(self.fmtsp, vec![self.ecx.ident_of("f")], block);
        let arm = self.ecx.arm(self.fmtsp,
            vec![ self.ecx.pat_tuple(self.fmtsp, pats) ],
            closure
            );
        let head = self.ecx.expr(self.fmtsp, ast::ExprTup(heads));
        let result = self.ecx.expr_match(self.fmtsp, head, vec!(arm));
        let closure_ptr = self.ecx.expr_addr_of(self.fmtsp, result);

        // Now create the fmt::Arguments struct with all our locals we created.
        self.ecx.expr_call_global(self.macsp,
            self.ecx.std_path(&["fmt", "Arguments", "new_v2"]),
            vec![closure_ptr]
            )
    }

    fn trait_name(ecx: &ExtCtxt, sp: Span, tyname: &str) -> &'static str {
        match &tyname[..] {
            ""  => "Display",
            "?" => "Debug",
            "e" => "LowerExp",
            "E" => "UpperExp",
            "o" => "Octal",
            "p" => "Pointer",
            "b" => "Binary",
            "x" => "LowerHex",
            "X" => "UpperHex",
            _ => {
                ecx.span_err(sp, &format!("unknown format trait `{}`", tyname));
                "Dummy"
            }
        }
    }
}

pub fn expand_format_args<'cx>(ecx: &'cx mut ExtCtxt, sp: Span,
                               tts: &[ast::TokenTree])
                               -> Box<base::MacResult+'cx> {

    match parse_args(ecx, sp, tts) {
        Some((efmt, args, order, names)) => {
            MacEager::expr(expand_preparsed_format_args(ecx, sp, efmt,
                                                      args, order, names))
        }
        None => DummyResult::expr(sp)
    }
}

/// Take the various parts of `format_args!(efmt, args..., name=names...)`
/// and construct the appropriate formatting expression.
pub fn expand_preparsed_format_args(ecx: &mut ExtCtxt, sp: Span,
                                    efmt: P<ast::Expr>,
                                    args: Vec<P<ast::Expr>>,
                                    name_ordering: Vec<String>,
                                    names: HashMap<String, P<ast::Expr>>)
                                    -> P<ast::Expr> {
    let arg_types: Vec<_> = (0..args.len()).map(|_| None).collect();
    let macsp = ecx.call_site();
    // Expand the format literal so that efmt.span will have a backtrace. This
    // is essential for locating a bug when the format literal is generated in
    // a macro. (e.g. println!("{}"), which uses concat!($fmt, "\n")).
    let efmt = ecx.expander().fold_expr(efmt);
    let mut cx = Context {
        ecx: ecx,
        args: args,
        arg_types: arg_types,
        names: names,
        name_positions: HashMap::new(),
        name_types: HashMap::new(),
        name_ordering: name_ordering,
        nest_level: 0,
        next_arg: 0,
        next_arg_trans: 0,
        literal: String::new(),
        pieces: Vec::new(),
        str_pieces: Vec::new(),
        macsp: macsp,
        fmtsp: efmt.span,
    };
    let fmt = match expr_to_string(cx.ecx,
                                   efmt,
                                   "format argument must be a string literal.") {
        Some((fmt, _)) => fmt,
        None => return DummyResult::raw_expr(sp)
    };

    let mut parser = parse::Parser::new(&fmt);

    loop {
        match parser.next() {
            Some(piece) => {
                if !parser.errors.is_empty() { break }
                cx.verify_piece(&piece);
                match cx.trans_piece(&piece) {
                    Some(piece) => {
                        let s = cx.trans_literal_string();
                        cx.str_pieces.push(s);
                        cx.pieces.push(piece);
                    }
                    None => {}
                }
            }
            None => break
        }
    }
    if !parser.errors.is_empty() {
        cx.ecx.span_err(cx.fmtsp, &format!("invalid format string: {}",
                                          parser.errors.remove(0)));
        return DummyResult::raw_expr(sp);
    }
    if !cx.literal.is_empty() {
        let s = cx.trans_literal_string();
        cx.str_pieces.push(s);
    }

    // Make sure that all arguments were used and all arguments have types.
    for (i, ty) in cx.arg_types.iter().enumerate() {
        if ty.is_none() {
            cx.ecx.span_err(cx.args[i].span, "argument never used");
        }
    }
    for (name, e) in &cx.names {
        if !cx.name_types.contains_key(name) {
            cx.ecx.span_err(e.span, "named argument never used");
        }
    }

    cx.into_expr()
}
