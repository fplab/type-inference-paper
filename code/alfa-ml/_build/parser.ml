
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | UNROLL
    | UNIT
    | TIMES
    | TID of (
# 9 "parser.mly"
       (string)
# 14 "parser.ml"
  )
    | THEN
    | RSQUARE
    | RPRJ
    | RPAREN
    | ROLL
    | REC
    | R
    | PLUS
    | OFTYPE
    | OF
    | NUM
    | MINUS
    | LT
    | LSQUARE
    | LPRJ
    | LPAREN
    | LET
    | L
    | INT of (
# 5 "parser.mly"
       (int)
# 37 "parser.ml"
  )
    | IN
    | IF
    | GT
    | FUN
    | FORALLT
    | FORALL
    | FIX
    | EQ
    | EOL
    | ELSE
    | EID of (
# 8 "parser.mly"
       (string)
# 52 "parser.ml"
  )
    | DOT
    | COMMA
    | CASE
    | BOOLLIT of (
# 10 "parser.mly"
       (bool)
# 60 "parser.ml"
  )
    | BOOL
    | BE
    | AT
    | ARROW
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState140
  | MenhirState136
  | MenhirState134
  | MenhirState132
  | MenhirState130
  | MenhirState128
  | MenhirState125
  | MenhirState121
  | MenhirState119
  | MenhirState116
  | MenhirState111
  | MenhirState107
  | MenhirState105
  | MenhirState103
  | MenhirState101
  | MenhirState100
  | MenhirState98
  | MenhirState94
  | MenhirState91
  | MenhirState87
  | MenhirState84
  | MenhirState79
  | MenhirState77
  | MenhirState72
  | MenhirState66
  | MenhirState65
  | MenhirState62
  | MenhirState60
  | MenhirState59
  | MenhirState58
  | MenhirState56
  | MenhirState55
  | MenhirState44
  | MenhirState40
  | MenhirState38
  | MenhirState35
  | MenhirState33
  | MenhirState31
  | MenhirState29
  | MenhirState27
  | MenhirState23
  | MenhirState21
  | MenhirState20
  | MenhirState19
  | MenhirState17
  | MenhirState16
  | MenhirState13
  | MenhirState10
  | MenhirState9
  | MenhirState7
  | MenhirState6
  | MenhirState5
  | MenhirState4
  | MenhirState2
  | MenhirState0

# 24 "parser.mly"
   open Syntax 
# 140 "parser.ml"

let rec _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | L ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | EID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | R ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LPAREN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | EID _v ->
                        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _, (e1 : (Syntax.Exp.t))), _, (x : (Syntax.Identifier.t))), _, (e2 : (Syntax.Exp.t))), _, (y : (Syntax.Identifier.t))), _, (e3 : (Syntax.Exp.t))) = _menhir_stack in
        let _15 = () in
        let _14 = () in
        let _12 = () in
        let _11 = () in
        let _10 = () in
        let _8 = () in
        let _7 = () in
        let _5 = () in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 54 "parser.mly"
    ( Exp.ECase (e1, x, e2, y, e3) )
# 252 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _), _, (i : (Syntax.Identifier.t))), _, (t : (Syntax.Typ.t))), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 46 "parser.mly"
    ( Exp.EFix (i, Some(t), e) )
# 267 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 48 "parser.mly"
    ( Exp.EFix (i, None, e) )
# 279 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (t : (Syntax.Identifier.t))), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 62 "parser.mly"
    ( Exp.ETypFun (t, e) )
# 291 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _), _, (i : (Syntax.Identifier.t))), _, (t : (Syntax.Typ.t))), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 42 "parser.mly"
    ( Exp.EFun (i, Some(t), e) )
# 306 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 44 "parser.mly"
    ( Exp.EFun (i, None, e) )
# 318 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState119
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ELSE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))), _, (e3 : (Syntax.Exp.t))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 40 "parser.mly"
    ( Exp.EIf (e1, e2, e3) )
# 431 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 50 "parser.mly"
    ( Exp.EInjL (e) )
# 442 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState125
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((((_menhir_stack, _menhir_s), _), _, (x : (Syntax.Identifier.t))), _, (y : (Syntax.Identifier.t))), _, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
        let _9 = () in
        let _7 = () in
        let _6 = () in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 56 "parser.mly"
    ( Exp.ELetPair (x, y, e1, e2) )
# 508 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState132
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState132)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (t : (Syntax.Typ.t))), _, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
        let _7 = () in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 36 "parser.mly"
    ( Exp.ELet (i, Some(t), e1, e2) )
# 572 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState136
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 38 "parser.mly"
    ( Exp.ELet (i, None, e1, e2) )
# 635 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState140 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState140
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState140)
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Syntax.Exp.t) = 
# 115 "parser.mly"
    ( e )
# 692 "parser.ml"
             in
            _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : (Syntax.Exp.t) = 
# 119 "parser.mly"
    ( Exp.EPair (e1, e2) )
# 717 "parser.ml"
             in
            _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 52 "parser.mly"
    ( Exp.EInjR (e) )
# 734 "parser.ml"
         in
        _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Syntax.Exp.t) = 
# 58 "parser.mly"
    ( Exp.ERoll (e) )
# 753 "parser.ml"
             in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Syntax.Exp.t) = 
# 60 "parser.mly"
    ( Exp.EUnroll (e) )
# 778 "parser.ml"
             in
            _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOL ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (
# 23 "parser.mly"
       (Syntax.Exp.t)
# 800 "parser.ml"
            ) = 
# 30 "parser.mly"
    ( e )
# 804 "parser.ml"
             in
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_1 : (
# 23 "parser.mly"
       (Syntax.Exp.t)
# 811 "parser.ml"
            )) = _v in
            Obj.magic _1
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_boolean : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Syntax.Exp.t)) = _v in
    let _v : (Syntax.Exp.t) = 
# 34 "parser.mly"
    ( e )
# 831 "parser.ml"
     in
    _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run98 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState98
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98

and _menhir_run101 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState101
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState101
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101

and _menhir_goto_ty : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Typ.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t1 : (Syntax.Typ.t))), _, (t2 : (Syntax.Typ.t))) = _menhir_stack in
        let _2 = () in
        let _v : (Syntax.Typ.t) = 
# 129 "parser.mly"
    ( Typ.TArrow (t1, t2) )
# 887 "parser.ml"
         in
        _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Syntax.Typ.t) = 
# 157 "parser.mly"
    ( Typ.TForall (i, t) )
# 907 "parser.ml"
             in
            _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : (Syntax.Typ.t) = 
# 153 "parser.mly"
    ( t )
# 931 "parser.ml"
             in
            _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (i : (Syntax.Identifier.t))), _, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _1 = () in
            let _v : (Syntax.Typ.t) = 
# 155 "parser.mly"
    ( Typ.TRec (i, t) )
# 957 "parser.ml"
             in
            _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOLLIT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | CASE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | EID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | FIX ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | FORALL ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | FUN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | IF ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | INT _v ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
                | L ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | LET ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | LPAREN ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | MINUS ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | R ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | ROLL ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | UNROLL ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState55
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOLLIT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                | CASE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | EID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                | FIX ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | FORALL ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | FUN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | IF ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | INT _v ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
                | L ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | LET ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | LPAREN ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | MINUS ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | R ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | ROLL ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | UNROLL ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState65
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RSQUARE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))), _, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 105 "parser.mly"
    ( Exp.ETypAp (e, t) )
# 1104 "parser.ml"
             in
            _menhir_goto_right _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState130
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_arith : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 | MenhirState2 | MenhirState4 | MenhirState5 | MenhirState7 | MenhirState140 | MenhirState134 | MenhirState136 | MenhirState130 | MenhirState132 | MenhirState16 | MenhirState125 | MenhirState17 | MenhirState19 | MenhirState119 | MenhirState121 | MenhirState116 | MenhirState55 | MenhirState58 | MenhirState111 | MenhirState65 | MenhirState66 | MenhirState87 | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EQ ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState107
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState107
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107)
        | GT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState105
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
        | LT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState103
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState103
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103)
        | MINUS ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | IN | OF | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _v : (Syntax.Exp.t) = 
# 67 "parser.mly"
    ( e )
# 1242 "parser.ml"
             in
            _menhir_goto_boolean _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | MINUS ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | IN | OF | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 71 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpLt, e2) )
# 1267 "parser.ml"
             in
            _menhir_goto_boolean _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | MINUS ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | IN | OF | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 69 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpGt, e2) )
# 1292 "parser.ml"
             in
            _menhir_goto_boolean _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | MINUS ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack)
        | PLUS ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | IN | OF | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 73 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpEq, e2) )
# 1317 "parser.ml"
             in
            _menhir_goto_boolean _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run77 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77

and _menhir_goto_ty_sum : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Typ.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState128 | MenhirState72 | MenhirState62 | MenhirState23 | MenhirState29 | MenhirState31 | MenhirState38 | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38)
        | BE | RPAREN | RSQUARE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _v : (Syntax.Typ.t) = 
# 127 "parser.mly"
    ( t )
# 1387 "parser.ml"
             in
            _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t1 : (Syntax.Typ.t))), _, (t2 : (Syntax.Typ.t))) = _menhir_stack in
        let _2 = () in
        let _v : (Syntax.Typ.t) = 
# 135 "parser.mly"
    ( Typ.TSum (t1, t2) )
# 1404 "parser.ml"
         in
        _menhir_goto_ty_sum _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_factor : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 | MenhirState2 | MenhirState4 | MenhirState5 | MenhirState140 | MenhirState7 | MenhirState136 | MenhirState134 | MenhirState132 | MenhirState130 | MenhirState125 | MenhirState16 | MenhirState17 | MenhirState121 | MenhirState119 | MenhirState19 | MenhirState116 | MenhirState55 | MenhirState58 | MenhirState111 | MenhirState65 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState94 | MenhirState87 | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TIMES ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | EQ | GT | IN | LT | MINUS | OF | PLUS | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _v : (Syntax.Exp.t) = 
# 77 "parser.mly"
    ( e )
# 1427 "parser.ml"
             in
            _menhir_goto_arith _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TIMES ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | EQ | GT | IN | LT | MINUS | OF | PLUS | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 79 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpPlus,e2) )
# 1450 "parser.ml"
             in
            _menhir_goto_arith _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TIMES ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | ELSE | EOL | EQ | GT | IN | LT | MINUS | OF | PLUS | RPAREN | THEN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 81 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpMinus, e2) )
# 1473 "parser.ml"
             in
            _menhir_goto_arith _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ty_prod : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Typ.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState128 | MenhirState72 | MenhirState62 | MenhirState23 | MenhirState29 | MenhirState31 | MenhirState35 | MenhirState40 | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | PLUS ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState40
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
        | ARROW | BE | RPAREN | RSQUARE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (t : (Syntax.Typ.t))) = _menhir_stack in
            let _v : (Syntax.Typ.t) = 
# 133 "parser.mly"
    ( t )
# 1523 "parser.ml"
             in
            _menhir_goto_ty_sum _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (t1 : (Syntax.Typ.t))), _, (t2 : (Syntax.Typ.t))) = _menhir_stack in
        let _2 = () in
        let _v : (Syntax.Typ.t) = 
# 141 "parser.mly"
    ( Typ.TProd (t1, t2) )
# 1540 "parser.ml"
         in
        _menhir_goto_ty_prod _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_app : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOLLIT _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | INT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState79 _v
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState79
        | COMMA | ELSE | EOL | EQ | GT | IN | LT | MINUS | OF | PLUS | RPAREN | THEN | TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _2 = () in
            let _v : (Syntax.Exp.t) = 
# 87 "parser.mly"
    ( Exp.EBinOp (e1, Exp.OpTimes, e2) )
# 1570 "parser.ml"
             in
            _menhir_goto_factor _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState79)
    | MenhirState0 | MenhirState2 | MenhirState4 | MenhirState5 | MenhirState7 | MenhirState140 | MenhirState134 | MenhirState136 | MenhirState130 | MenhirState132 | MenhirState16 | MenhirState125 | MenhirState17 | MenhirState19 | MenhirState119 | MenhirState121 | MenhirState116 | MenhirState55 | MenhirState58 | MenhirState111 | MenhirState65 | MenhirState66 | MenhirState87 | MenhirState94 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState101 | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOLLIT _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | INT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState100
        | COMMA | ELSE | EOL | EQ | GT | IN | LT | MINUS | OF | PLUS | RPAREN | THEN | TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _v : (Syntax.Exp.t) = 
# 85 "parser.mly"
    ( e )
# 1596 "parser.ml"
             in
            _menhir_goto_factor _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100)
    | _ ->
        _menhir_fail ()

and _menhir_run70 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
    let _2 = () in
    let _v : (Syntax.Exp.t) = 
# 103 "parser.mly"
    ( Exp.EPrjR (e) )
# 1615 "parser.ml"
     in
    _menhir_goto_right _menhir_env _menhir_stack _menhir_s _v

and _menhir_run71 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | AT ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | FORALLT ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LPAREN ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | NUM ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | REC ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | TID _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
        | UNIT ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run75 : _menhir_env -> 'ttv_tail * _menhir_state * (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
    let _2 = () in
    let _v : (Syntax.Exp.t) = 
# 101 "parser.mly"
    ( Exp.EPrjL (e) )
# 1663 "parser.ml"
     in
    _menhir_goto_right _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_base_ty : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Typ.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TIMES ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | FORALLT ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | LPAREN ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | NUM ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | REC ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | TID _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
        | UNIT ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState44
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
    | ARROW | BE | PLUS | RPAREN | RSQUARE ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (t : (Syntax.Typ.t))) = _menhir_stack in
        let _v : (Syntax.Typ.t) = 
# 139 "parser.mly"
    ( t )
# 1703 "parser.ml"
         in
        _menhir_goto_ty_prod _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_right : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState0 | MenhirState2 | MenhirState4 | MenhirState5 | MenhirState140 | MenhirState7 | MenhirState136 | MenhirState134 | MenhirState132 | MenhirState130 | MenhirState125 | MenhirState16 | MenhirState17 | MenhirState121 | MenhirState119 | MenhirState19 | MenhirState116 | MenhirState55 | MenhirState58 | MenhirState111 | MenhirState65 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState101 | MenhirState98 | MenhirState94 | MenhirState87 | MenhirState77 | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPRJ ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | LSQUARE ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack)
        | RPRJ ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | BOOLLIT _ | COMMA | EID _ | ELSE | EOL | EQ | GT | IN | INT _ | LPAREN | LT | MINUS | OF | PLUS | RPAREN | THEN | TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _v : (Syntax.Exp.t) = 
# 91 "parser.mly"
    ( e )
# 1734 "parser.ml"
             in
            _menhir_goto_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState100 | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPRJ ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | LSQUARE ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack)
        | RPRJ ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | BOOLLIT _ | COMMA | EID _ | ELSE | EOL | EQ | GT | IN | INT _ | LPAREN | LT | MINUS | OF | PLUS | RPAREN | THEN | TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Syntax.Exp.t))), _, (e2 : (Syntax.Exp.t))) = _menhir_stack in
            let _v : (Syntax.Exp.t) = 
# 93 "parser.mly"
    ( Exp.EBinOp (e1, OpAp, e2) )
# 1760 "parser.ml"
             in
            _menhir_goto_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | LPRJ ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | LSQUARE ->
            _menhir_run71 _menhir_env (Obj.magic _menhir_stack)
        | RPRJ ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | BOOLLIT _ | COMMA | EID _ | ELSE | EOL | EQ | GT | IN | INT _ | LPAREN | LT | MINUS | OF | PLUS | RPAREN | THEN | TIMES ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Syntax.Exp.t))) = _menhir_stack in
            let _1 = () in
            let _v : (Syntax.Exp.t) = 
# 95 "parser.mly"
    ( Exp.EUnOp (OpNeg, e) )
# 1787 "parser.ml"
             in
            _menhir_goto_app _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Syntax.Typ.t) = 
# 149 "parser.mly"
    ( Typ.TUnit )
# 1812 "parser.ml"
     in
    _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v

and _menhir_run25 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 9 "parser.mly"
       (string)
# 1819 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (
# 9 "parser.mly"
       (string)
# 1827 "parser.ml"
    )) = _v in
    let _v : (Syntax.Identifier.t) = 
# 161 "parser.mly"
    ( i )
# 1832 "parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState29 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState29
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | DOT ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState35
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState128 | MenhirState23 | MenhirState62 | MenhirState72 | MenhirState29 | MenhirState31 | MenhirState35 | MenhirState38 | MenhirState44 | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (i : (Syntax.Identifier.t))) = _menhir_stack in
        let _v : (Syntax.Typ.t) = 
# 151 "parser.mly"
    ( Typ.TVar (i))
# 1911 "parser.ml"
         in
        _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState58 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState58
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState58)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TID _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState27 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState27)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Syntax.Typ.t) = 
# 145 "parser.mly"
    ( Typ.TNum )
# 1999 "parser.ml"
     in
    _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | FORALLT ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | LPAREN ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | NUM ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | REC ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | TID _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
    | UNIT ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState31
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31

and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | TID _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _1 = () in
    let _v : (Syntax.Typ.t) = 
# 147 "parser.mly"
    ( Typ.TBool )
# 2060 "parser.ml"
     in
    _menhir_goto_base_ty _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_simple : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Exp.t) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (e : (Syntax.Exp.t)) = _v in
    let _v : (Syntax.Exp.t) = 
# 99 "parser.mly"
    ( e )
# 2072 "parser.ml"
     in
    _menhir_goto_right _menhir_env _menhir_stack _menhir_s _v

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState140 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState136 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState134 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState132 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState130 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState128 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState125 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState119 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState111 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState103 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState101 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState100 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState98 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState94 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState79 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState72 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState66 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState65 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState62 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState58 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState56 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState55 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState35 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState33 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState31 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState29 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState27 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState23 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState17 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState7 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState6 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState5 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState2 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        raise _eRR

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOLLIT _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
        | CASE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
        | FIX ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | FORALL ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | FUN ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | IF ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | INT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState2 _v
        | L ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | LET ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | MINUS ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | R ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | ROLL ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | UNROLL ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState2
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState2)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOLLIT _v ->
            _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
        | CASE ->
            _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
        | FIX ->
            _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | FORALL ->
            _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | FUN ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | IF ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | INT _v ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
        | L ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | LET ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | LPAREN ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | MINUS ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | R ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | ROLL ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | UNROLL ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState5
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | RPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState7 in
        let _menhir_env = _menhir_discard _menhir_env in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _2 = () in
        let _1 = () in
        let _v : (Syntax.Exp.t) = 
# 117 "parser.mly"
    ( Exp.ETriv )
# 2508 "parser.ml"
         in
        _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState7
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState9 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState17
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 5 "parser.mly"
       (int)
# 2588 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (
# 5 "parser.mly"
       (int)
# 2596 "parser.ml"
    )) = _v in
    let _v : (Syntax.Exp.t) = 
# 111 "parser.mly"
    ( Exp.ENumLiteral i )
# 2601 "parser.ml"
     in
    _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19

and _menhir_run20 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState20 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run56 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | TID _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState56 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState56

and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
    | LPAREN ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState59 in
        let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState60 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState60)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 8 "parser.mly"
       (string)
# 2714 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (i : (
# 8 "parser.mly"
       (string)
# 2722 "parser.ml"
    )) = _v in
    let _v : (Syntax.Identifier.t) = 
# 123 "parser.mly"
    ( i )
# 2727 "parser.ml"
     in
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState10 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState13 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOLLIT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                | CASE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | EID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                | FIX ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | FORALL ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | FUN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | IF ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | INT _v ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                | L ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | LET ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | LPAREN ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | MINUS ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | R ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | ROLL ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | UNROLL ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState21 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OFTYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState60 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | OFTYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState62
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 | MenhirState2 | MenhirState4 | MenhirState5 | MenhirState6 | MenhirState7 | MenhirState140 | MenhirState134 | MenhirState136 | MenhirState130 | MenhirState132 | MenhirState16 | MenhirState125 | MenhirState17 | MenhirState19 | MenhirState119 | MenhirState121 | MenhirState116 | MenhirState55 | MenhirState58 | MenhirState111 | MenhirState65 | MenhirState66 | MenhirState87 | MenhirState107 | MenhirState105 | MenhirState103 | MenhirState101 | MenhirState100 | MenhirState98 | MenhirState94 | MenhirState79 | MenhirState77 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (e : (Syntax.Identifier.t))) = _menhir_stack in
        let _v : (Syntax.Exp.t) = 
# 109 "parser.mly"
    ( Exp.EVar (e) )
# 2889 "parser.ml"
         in
        _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v
    | MenhirState84 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOLLIT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
                | CASE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | EID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
                | FIX ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | FORALL ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | FUN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | IF ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | INT _v ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
                | L ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | LET ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | LPAREN ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | MINUS ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | R ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | ROLL ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | UNROLL ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState87
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState91 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAREN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ARROW ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOLLIT _v ->
                    _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
                | CASE ->
                    _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | EID _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
                | FIX ->
                    _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | FORALL ->
                    _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | FUN ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | IF ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | INT _v ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
                | L ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | LET ->
                    _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | LPAREN ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | MINUS ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | R ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | ROLL ->
                    _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | UNROLL ->
                    _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState94
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState59 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ARROW ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState9 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOLLIT _v ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _v
            | CASE ->
                _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | EID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _v
            | FIX ->
                _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | FORALL ->
                _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | FUN ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | IF ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | INT _v ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState134 _v
            | L ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | LET ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | LPAREN ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | MINUS ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | R ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | ROLL ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | UNROLL ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState134
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState134)
        | OFTYPE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | FORALLT ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | LPAREN ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | NUM ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | REC ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | TID _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _v
            | UNIT ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState66 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState66
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState66

and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 10 "parser.mly"
       (bool)
# 3234 "parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (b : (
# 10 "parser.mly"
       (bool)
# 3242 "parser.ml"
    )) = _v in
    let _v : (Syntax.Exp.t) = 
# 113 "parser.mly"
    ( Exp.EBoolLiteral b )
# 3247 "parser.ml"
     in
    _menhir_goto_simple _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and main : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 23 "parser.mly"
       (Syntax.Exp.t)
# 3266 "parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env = let _tok = Obj.magic () in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOLLIT _v ->
        _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | CASE ->
        _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EID _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | FIX ->
        _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FORALL ->
        _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FUN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | IF ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | INT _v ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | L ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LET ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | LPAREN ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | MINUS ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | R ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ROLL ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | UNROLL ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)

# 269 "<standard.mly>"
  

# 3318 "parser.ml"
