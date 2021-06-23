
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | UNION
    | UINST
    | TRUE
    | SUBSETEQ
    | SUBSET
    | STRCONST of (
# 62 "specParser.mly"
       (string)
# 16 "specParser.ml"
  )
    | STEXC
    | STATE
    | STAR
    | SEMICOLON
    | RPAREN
    | RELATION
    | REF
    | RCURLY
    | RBRACE
    | PURE
    | PRIMITIVE
    | PLUS
    | PIPE
    | NUMEQ
    | NOT
    | MINUS
    | LPAREN
    | LESSTHAN
    | LCURLY
    | LBRACE
    | LAMBDA
    | INT of (
# 61 "specParser.mly"
       (int)
# 42 "specParser.ml"
  )
    | IMPL
    | IFF
    | ID of (
# 60 "specParser.mly"
        (string)
# 49 "specParser.ml"
  )
    | GREATERTHAN
    | FORMULA
    | FALSE
    | EXISTS
    | EXC
    | EQUALOP
    | EOL
    | EOF
    | DOT
    | DISJ
    | CROSSPRD
    | CONJ
    | COMMA
    | COLON
    | ASSUME
    | ARROW
    | ARMINUS
    | ANGRIGHT
    | ANGLEFT
    | ALL
  
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
  | MenhirState237
  | MenhirState235
  | MenhirState233
  | MenhirState231
  | MenhirState228
  | MenhirState223
  | MenhirState219
  | MenhirState215
  | MenhirState213
  | MenhirState204
  | MenhirState197
  | MenhirState195
  | MenhirState191
  | MenhirState187
  | MenhirState176
  | MenhirState174
  | MenhirState172
  | MenhirState169
  | MenhirState165
  | MenhirState163
  | MenhirState161
  | MenhirState159
  | MenhirState157
  | MenhirState152
  | MenhirState151
  | MenhirState149
  | MenhirState148
  | MenhirState145
  | MenhirState141
  | MenhirState138
  | MenhirState119
  | MenhirState118
  | MenhirState116
  | MenhirState114
  | MenhirState112
  | MenhirState111
  | MenhirState109
  | MenhirState103
  | MenhirState102
  | MenhirState97
  | MenhirState95
  | MenhirState91
  | MenhirState88
  | MenhirState81
  | MenhirState80
  | MenhirState78
  | MenhirState73
  | MenhirState71
  | MenhirState65
  | MenhirState63
  | MenhirState61
  | MenhirState59
  | MenhirState55
  | MenhirState49
  | MenhirState46
  | MenhirState41
  | MenhirState38
  | MenhirState37
  | MenhirState36
  | MenhirState34
  | MenhirState24
  | MenhirState22
  | MenhirState20
  | MenhirState12
  | MenhirState10
  | MenhirState7
  | MenhirState4
  | MenhirState3
  | MenhirState0

# 1 "specParser.mly"
  
open SpecLang
open RelLang
open Printf
module TypeSpec = SpecLang.RelSpec.TypeSpec
module RefTy = SpecLang.RefinementType
module Formula = SpecLang.RelSpec.Formula
let defaultCons = SpecLang.Con.default
let symbase = "sp_"
let count = ref 0
let genVar = fun _ -> 
  let id = symbase ^ (string_of_int (!count)) in 
  let () = count := !count + 1
    in
      Var.fromString id 
let ($) (f,arg) = f arg
let  empty = fun _ -> Vector.new0 ()
let print msg = let () = Printf.printf "%s" msg in ()


# 178 "specParser.ml"

let rec _menhir_goto_decsandtys : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decsandtys -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState237 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv907 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv905 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_predspec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 114 "specParser.mly"
    (
		 match d with 
		  RelSpec.T {preds;reldecs; primdecs; typespecs} -> 
                    RelSpec.T {preds= p :: preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = typespecs}

		)
# 203 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv906)) : 'freshtv908)
    | MenhirState235 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv911 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv909 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_primdec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 96 "specParser.mly"
                (match d with 
                  RelSpec.T ({preds;reldecs; primdecs; 
                  typespecs}) -> 
                    RelSpec.T {preds = preds;
		    		primdecs = p :: primdecs; 
                              reldecs=reldecs; 
                              typespecs = typespecs}
                )
# 227 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv910)) : 'freshtv912)
    | MenhirState233 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv915 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv913 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (r : 'tv_reldec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 87 "specParser.mly"
                  (
                    match d with 
                    RelSpec.T ({preds;reldecs; primdecs; typespecs}) -> 
                    RelSpec.T {preds = preds;
		    		reldecs = r ::reldecs; 
                              primdecs = primdecs;
                            typespecs = typespecs}
                          )
# 251 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv914)) : 'freshtv916)
    | MenhirState231 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv919 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv917 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (t : 'tv_typespec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 106 "specParser.mly"
                (
                  match d with
                 RelSpec.T {preds;reldecs; primdecs; 
                  typespecs} -> 
                    RelSpec.T {preds= preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = t :: typespecs}
                )
# 274 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv918)) : 'freshtv920)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv933) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv931) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let _v : 'tv_spec = 
# 82 "specParser.mly"
                   (
                  d)
# 290 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv929) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_spec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv927 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv923 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv921 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (s : 'tv_spec)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 312 "specParser.ml"
            ) = 
# 78 "specParser.mly"
               (s)
# 316 "specParser.ml"
             in
            _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv922)) : 'freshtv924)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv925 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv926)) : 'freshtv928)) : 'freshtv930)) : 'freshtv932)) : 'freshtv934)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typespec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typespec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv903 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv899 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run226 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | FORMULA ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | ID _v ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
        | LPAREN ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | PRIMITIVE ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | RELATION ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | EOF ->
            _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState231
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState231) : 'freshtv900)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv901 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv902)) : 'freshtv904)

and _menhir_goto_vartyseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv893 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv889 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv883 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_vartyatom = 
# 256 "specParser.mly"
                                  (
                match vas with
                        [x] -> x 
                        | _ -> (genVar (), RefTy.Sigma vas)
                  )
# 398 "specParser.ml"
                 in
                _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv884)
            | COMMA | LCURLY | RPAREN | SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv885 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_reftyatom = 
# 248 "specParser.mly"
                                        (RefTy.Sigma vas)
# 410 "specParser.ml"
                 in
                _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv886)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv887 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv888)) : 'freshtv890)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv891 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv892)) : 'freshtv894)
    | MenhirState213 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv897 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv895 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_varty)), _, (vts : 'tv_vartyseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_vartyseq = 
# 263 "specParser.mly"
                                       (vt :: vts)
# 437 "specParser.ml"
         in
        _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv896)) : 'freshtv898)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv873 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 451 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv871 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 459 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 466 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_reldec = 
# 144 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = p;
                mapp = patmseq})
# 476 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv872)) : 'freshtv874)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv877 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv875 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((pms : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatchseq = 
# 164 "specParser.mly"
                                               (pm :: pms)
# 493 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv876)) : 'freshtv878)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv881 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 501 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv879 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 509 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 516 "specParser.ml"
        ))) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_reldec = 
# 140 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = empty ();
                mapp = patmseq})
# 524 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv880)) : 'freshtv882)
    | _ ->
        _menhir_fail ()

and _menhir_goto_funparams : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_funparams -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv865 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv861 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv859 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (ps : 'tv_funparams)) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_ratom = 
# 204 "specParser.mly"
                                               (MultiR (ie, ps))
# 552 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv860)) : 'freshtv862)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv863 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv864)) : 'freshtv866)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv869 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv867 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (p : 'tv_funparam)), _, (ps : 'tv_funparams)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_funparams = 
# 214 "specParser.mly"
                                 (p::ps)
# 572 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv868)) : 'freshtv870)
    | _ ->
        _menhir_fail ()

and _menhir_goto_reftyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reftyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv857) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_reftyatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv855) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((rta : 'tv_reftyatom) : 'tv_reftyatom) = _v in
    ((let _v : 'tv_refty = 
# 243 "specParser.mly"
                      ( rta)
# 591 "specParser.ml"
     in
    _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv856)) : 'freshtv858)

and _menhir_reduce20 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_decsandtys = 
# 121 "specParser.mly"
                (RelSpec.T {
  			preds = Vector.new0 ();
  			reldecs = [];
                  primdecs = Vector.new0 ();
                  typespecs = []})
# 604 "specParser.ml"
     in
    _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_refty : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_refty -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv815 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv813 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vrta : 'tv_vartyatom)), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_refty = 
# 244 "specParser.mly"
                                      ( RefTy.Arrow (((fst (vrta)) , (snd vrta)), rt))
# 622 "specParser.ml"
         in
        _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv814)) : 'freshtv816)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv821 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 630 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 634 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv817 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 644 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 648 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState204
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState204) : 'freshtv818)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv819 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 686 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 690 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv820)) : 'freshtv822)
    | MenhirState215 | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv841 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 699 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv839 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 705 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 710 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_varty = 
# 266 "specParser.mly"
  (((Var.fromString i), rt))
# 716 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv837) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_varty) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv835 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv829 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv827) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState213 in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 741 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv823 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 752 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
                    | LBRACE ->
                        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | LCURLY ->
                        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | LPAREN ->
                        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | REF ->
                        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState215
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215) : 'freshtv824)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv825 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 778 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv826)) : 'freshtv828)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213) : 'freshtv830)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv831 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (vt : 'tv_varty)) = _menhir_stack in
            let _v : 'tv_vartyseq = 
# 262 "specParser.mly"
                    ([vt])
# 793 "specParser.ml"
             in
            _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv832)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv833 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv834)) : 'freshtv836)) : 'freshtv838)) : 'freshtv840)) : 'freshtv842)
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv845 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 808 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv843 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 814 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, (ps : 'tv_paramseq)), (i : (
# 60 "specParser.mly"
        (string)
# 819 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 237 "specParser.mly"
                                                         (
                                  TypeSpec.T {isAssume = false;
                                name = Var.fromString i;
                                params = Vector.fromList ps; 
                                refty = rt})
# 831 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv844)) : 'freshtv846)
    | MenhirState219 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv849 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 839 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv847 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 845 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 850 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typespec = 
# 233 "specParser.mly"
                               (      TypeSpec.T {isAssume = false;
                                       name = (Var.fromString i);
                                       params = empty ();
                                       refty = rt})
# 859 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv848)) : 'freshtv850)
    | MenhirState228 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv853 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 867 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv851 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 873 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 878 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 228 "specParser.mly"
                                      (
                                          TypeSpec.T {isAssume = true;
                                              name = (Var.fromString i);
                                              params = empty ();
                                              refty = rt})
# 889 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv852)) : 'freshtv854)
    | _ ->
        _menhir_fail ()

and _menhir_run157 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState157 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157

and _menhir_run159 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState159 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState159
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159

and _menhir_run161 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState161
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161

and _menhir_run163 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState163 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState163
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState163

and _menhir_run165 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165

and _menhir_goto_rpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv811) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_rpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv809) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ra : 'tv_rpatom) : 'tv_rpatom) = _v in
    ((let _v : 'tv_patom = 
# 302 "specParser.mly"
                  (Predicate.Rel ra)
# 1018 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv810)) : 'freshtv812)

and _menhir_goto_primdef : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_primdef -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv795 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1030 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv793 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1038 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 1045 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_primdef = 
# 135 "specParser.mly"
                                    (PrimitiveRelation.Nary
                (Var.fromString i, p))
# 1053 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv794)) : 'freshtv796)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv807 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 1061 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv805 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 1069 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 1076 "specParser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_primdec = 
# 130 "specParser.mly"
                                                    (PrimitiveRelation.T
                    {id=RelId.fromString i; 
                    def=PrimitiveRelation.alphaRename p})
# 1086 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv803) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv801 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv797 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run226 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | FORMULA ->
                _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | ID _v ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
            | LPAREN ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | PRIMITIVE ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | RELATION ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | EOF ->
                _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState235
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235) : 'freshtv798)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv799 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv800)) : 'freshtv802)) : 'freshtv804)) : 'freshtv806)) : 'freshtv808)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv791 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv785 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | LPAREN ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv786)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv787 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _v : 'tv_patmatchseq = 
# 165 "specParser.mly"
                          ([pm])
# 1161 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv788)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv789 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv790)) : 'freshtv792)

and _menhir_run44 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv783 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
    ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _v : 'tv_ratom = 
# 206 "specParser.mly"
                               (re)
# 1183 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv784)

and _menhir_goto_reldec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reldec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv781 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv777 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run226 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | FORMULA ->
            _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | ID _v ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
        | LPAREN ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | PRIMITIVE ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | RELATION ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | EOF ->
            _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState233
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233) : 'freshtv778)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv779 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv780)) : 'freshtv782)

and _menhir_reduce27 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1230 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1236 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_funparam = 
# 216 "specParser.mly"
                (Var.fromString i)
# 1241 "specParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv775) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_funparam) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv773 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv767 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv765) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState55 in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 1266 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv766)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55) : 'freshtv768)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv769 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_funparam)) = _menhir_stack in
        let _v : 'tv_funparams = 
# 213 "specParser.mly"
                       ([p])
# 1282 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv770)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv771 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv772)) : 'freshtv774)) : 'freshtv776)

and _menhir_goto_instexprs : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexprs -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState36 | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv759 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1301 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv757 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1309 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1316 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_instexpr = 
# 185 "specParser.mly"
                              (RInst {
                sargs = empty (); targs = empty();
                args = Vector.fromList ies;
                rel = RelId.fromString i})
# 1324 "specParser.ml"
         in
        _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv758)) : 'freshtv760)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv763 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv761 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_instexprs = 
# 191 "specParser.mly"
                                                    (ie :: ies)
# 1342 "specParser.ml"
         in
        _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv762)) : 'freshtv764)
    | _ ->
        _menhir_fail ()

and _menhir_goto_vartyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv755 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv751 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
        | LBRACE ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | LCURLY ->
            _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | LPAREN ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | REF ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState197
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197) : 'freshtv752)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv753 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv754)) : 'freshtv756)

and _menhir_reduce71 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (bt : 'tv_basety)) = _menhir_stack in
    let _v : 'tv_reftyatom = 
# 247 "specParser.mly"
                      ( bt)
# 1390 "specParser.ml"
     in
    _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_idseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_idseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv741 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1403 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv739 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1409 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1414 "specParser.ml"
        ))), _, (is : 'tv_idseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_idseq = 
# 180 "specParser.mly"
                            ((Var.fromString i)::is)
# 1420 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv740)) : 'freshtv742)
    | MenhirState10 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv749) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv745) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv743) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, (is : 'tv_idseq)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_conargs = 
# 177 "specParser.mly"
                                 (Vector.fromList is)
# 1441 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv744)) : 'freshtv746)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv747) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv748)) : 'freshtv750)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pred : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_pred -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv653 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv651 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 297 "specParser.mly"
                                           (Predicate.Exists (binds, pr))
# 1469 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv652)) : 'freshtv654)
    | MenhirState169 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv657 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv655 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 292 "specParser.mly"
                              (Predicate.If (pa,pr))
# 1482 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv656)) : 'freshtv658)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv661 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv659 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 293 "specParser.mly"
                             (Predicate.Iff (pa,pr))
# 1495 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv660)) : 'freshtv662)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv665 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv663 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 295 "specParser.mly"
                              (Predicate.Disj (pa,pr))
# 1508 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv664)) : 'freshtv666)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv669 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv667 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 294 "specParser.mly"
                              (Predicate.Conj (pa,pr))
# 1521 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv668)) : 'freshtv670)
    | MenhirState148 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv673 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv671 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 296 "specParser.mly"
                                           (Predicate.Forall (binds, pr) )
# 1535 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv672)) : 'freshtv674)
    | MenhirState119 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv681 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv677 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv675 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (pr : 'tv_pred)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_patom = 
# 300 "specParser.mly"
                              (pr)
# 1556 "specParser.ml"
             in
            _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv676)) : 'freshtv678)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv679 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv680)) : 'freshtv682)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv689 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1571 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv685 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1581 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv683 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1588 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), _, (v : (
# 60 "specParser.mly"
        (string)
# 1593 "specParser.ml"
            ))), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 279 "specParser.mly"
                                                       (RefinementType.Base ((Var.fromString v), 
                ty, pr))
# 1603 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv684)) : 'freshtv686)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv687 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1613 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv688)) : 'freshtv690)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv697 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv693 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv691 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 277 "specParser.mly"
                                           (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, pr))
# 1637 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv692)) : 'freshtv694)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv695 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv696)) : 'freshtv698)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv711 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1652 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv707 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1662 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv703 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1672 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 1677 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv699 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1688 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1692 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
                    | LBRACE ->
                        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState195
                    | LCURLY ->
                        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState195
                    | LPAREN ->
                        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState195
                    | REF ->
                        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState195
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState195) : 'freshtv700)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv701 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1718 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1722 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv702)) : 'freshtv704)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv705 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1733 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv706)) : 'freshtv708)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv709 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1744 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv710)) : 'freshtv712)
    | MenhirState204 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((('freshtv725 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1753 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1757 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv721 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1767 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1771 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv719 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1778 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1782 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, (ef : (
# 60 "specParser.mly"
        (string)
# 1787 "specParser.ml"
            ))), _, (pre : 'tv_pred)), (resvar : (
# 60 "specParser.mly"
        (string)
# 1791 "specParser.ml"
            ))), _, (resty : 'tv_refty)), _, (post : 'tv_pred)) = _menhir_stack in
            let _10 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_mty = 
# 282 "specParser.mly"
                                                                                         (RefTy.MArrow (Effect.fromString ef, pre, (resvar, resty), post))
# 1801 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv717) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv715) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv713) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((mtype : 'tv_mty) : 'tv_mty) = _v in
            ((let _v : 'tv_refty = 
# 245 "specParser.mly"
                  (mtype)
# 1818 "specParser.ml"
             in
            _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv714)) : 'freshtv716)) : 'freshtv718)) : 'freshtv720)) : 'freshtv722)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv723 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1828 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 1832 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv724)) : 'freshtv726)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv737 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1841 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv735 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1847 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 1852 "specParser.ml"
        ))), _, (p : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_predspec = 
# 128 "specParser.mly"
                                       (Formula.Form{name=Var.fromString i;pred = p})
# 1859 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv733) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_predspec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv731 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv727 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run226 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | FORMULA ->
                _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | ID _v ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState237 _v
            | LPAREN ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | PRIMITIVE ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | RELATION ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | EOF ->
                _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState237
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState237) : 'freshtv728)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv729 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv730)) : 'freshtv732)) : 'freshtv734)) : 'freshtv736)) : 'freshtv738)
    | _ ->
        _menhir_fail ()

and _menhir_goto_rexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv581 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv579 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv580)) : 'freshtv582)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv585 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv583 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 195 "specParser.mly"
                                (U(ra,re))
# 1934 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv584)) : 'freshtv586)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv589 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv587 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 197 "specParser.mly"
                               (ADD(ra,re))
# 1947 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv588)) : 'freshtv590)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv593 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv591 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 196 "specParser.mly"
                                (D(ra,re))
# 1960 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv592)) : 'freshtv594)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv597 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv595 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 194 "specParser.mly"
                                   (X(ra,re))
# 1973 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv596)) : 'freshtv598)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv601 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv599 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 198 "specParser.mly"
                                  (SUBS(ra,re))
# 1986 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv600)) : 'freshtv602)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv605 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv603 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (cp : 'tv_conpat)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_patmatch = 
# 169 "specParser.mly"
              (match cp with (c,vlop) -> (c, vlop, Expr re))
# 2001 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv604)) : 'freshtv606)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv609 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2009 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv607 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2015 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2020 "specParser.ml"
        ))), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatch = 
# 170 "specParser.mly"
                                 ((Con.fromString i, None, Expr re))
# 2026 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv608)) : 'freshtv610)
    | MenhirState88 | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv613 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv611 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (re : 'tv_rexpr)) = _menhir_stack in
        let _v : 'tv_primdef = 
# 134 "specParser.mly"
                   (PrimitiveRelation.Nullary re)
# 2038 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv612)) : 'freshtv614)
    | MenhirState152 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv621 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGRIGHT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv617 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv615 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_rpatom = 
# 323 "specParser.mly"
                                   (Predicate.RelPredicate.Q (re))
# 2059 "specParser.ml"
             in
            _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv616)) : 'freshtv618)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv619 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv620)) : 'freshtv622)
    | MenhirState223 | MenhirState204 | MenhirState191 | MenhirState187 | MenhirState116 | MenhirState118 | MenhirState148 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState169 | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv625 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv623 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv624)) : 'freshtv626)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv629 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv627 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 326 "specParser.mly"
                                      (Predicate.RelPredicate.SubEq(re1,re2))
# 2102 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv628)) : 'freshtv630)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv633 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv631 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 325 "specParser.mly"
                                    (Predicate.RelPredicate.Sub(re1,re2))
# 2115 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv632)) : 'freshtv634)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv637 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv635 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 327 "specParser.mly"
                                   (Predicate.RelPredicate.NEq(re1, re2) )
# 2128 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv636)) : 'freshtv638)
    | MenhirState163 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv641 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv639 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 328 "specParser.mly"
                                         (Predicate.RelPredicate.NEq(re1, re2))
# 2141 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv640)) : 'freshtv642)
    | MenhirState165 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv645 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv643 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 324 "specParser.mly"
                                     (Predicate.RelPredicate.Eq(re1,re2))
# 2154 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv644)) : 'freshtv646)
    | MenhirState119 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv649 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv647 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv648)) : 'freshtv650)
    | _ ->
        _menhir_fail ()

and _menhir_goto_instexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv547 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv543 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LBRACE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState41
            | LPAREN | RBRACE | STAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv541 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_instexprs = 
# 190 "specParser.mly"
                                      ([ie])
# 2212 "specParser.ml"
                 in
                _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv542)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41) : 'freshtv544)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv545 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv546)) : 'freshtv548)
    | MenhirState223 | MenhirState191 | MenhirState204 | MenhirState187 | MenhirState116 | MenhirState118 | MenhirState119 | MenhirState148 | MenhirState151 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState169 | MenhirState165 | MenhirState163 | MenhirState161 | MenhirState159 | MenhirState157 | MenhirState152 | MenhirState88 | MenhirState91 | MenhirState71 | MenhirState20 | MenhirState22 | MenhirState65 | MenhirState63 | MenhirState61 | MenhirState59 | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv561 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv557 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv555 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState49 in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 2245 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RPAREN ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv551 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2256 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv549 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2263 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (i : (
# 60 "specParser.mly"
        (string)
# 2268 "specParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _v : 'tv_ratom = 
# 205 "specParser.mly"
                                       (R (ie, Var.fromString i))
# 2275 "specParser.ml"
                     in
                    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv550)) : 'freshtv552)
                | COMMA ->
                    _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv553 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2287 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv554)) : 'freshtv556)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49) : 'freshtv558)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv559 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv560)) : 'freshtv562)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv569 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2307 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv565 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2317 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv563 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2324 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 2329 "specParser.ml"
            ))), _, (p : 'tv_params)), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 153 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = p;
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2342 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv564)) : 'freshtv566)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv567 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2352 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv568)) : 'freshtv570)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv577 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2361 "specParser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv573 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2371 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv571 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2378 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 2383 "specParser.ml"
            ))), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 148 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = empty ();
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2394 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv572)) : 'freshtv574)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv575 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2404 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv576)) : 'freshtv578)
    | _ ->
        _menhir_fail ()

and _menhir_reduce67 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
    let _v : 'tv_ratom = 
# 208 "specParser.mly"
                (V (el))
# 2417 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_elemseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elemseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv535 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv531 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv527 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv525 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (els : 'tv_elemseq)) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 203 "specParser.mly"
                                                (T(Vector.fromList els))
# 2451 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv526)) : 'freshtv528)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv529 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv530)) : 'freshtv532)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv533 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv534)) : 'freshtv536)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv539 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv537 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (el : 'tv_elem)), _, (els : 'tv_elemseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_elemseq = 
# 219 "specParser.mly"
                                    (el::els)
# 2478 "specParser.ml"
         in
        _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv538)) : 'freshtv540)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_basety : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState228 | MenhirState219 | MenhirState102 | MenhirState215 | MenhirState195 | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv515 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        (_menhir_reduce71 _menhir_env (Obj.magic _menhir_stack) : 'freshtv516)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv523 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2502 "specParser.ml"
        ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv519 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2512 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv517 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2519 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (i : (
# 60 "specParser.mly"
        (string)
# 2524 "specParser.ml"
            ))), _, (bt : 'tv_basety)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartyatom = 
# 251 "specParser.mly"
  (
                  match bt with 
                     RefTy.Base (v,_,_) -> ((Var.fromString i),bt)
                       | _ -> raise (Failure "Impossible case of basety")
		)
# 2536 "specParser.ml"
             in
            _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv518)) : 'freshtv520)
        | COMMA ->
            _menhir_reduce71 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv521 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2548 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv522)) : 'freshtv524)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tybindseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tybindseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState145 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv501 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv499 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_vartybind)), _, (vts : 'tv_tybindseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tybindseq = 
# 332 "specParser.mly"
                                            (vt :: vts)
# 2569 "specParser.ml"
         in
        _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv500)) : 'freshtv502)
    | MenhirState138 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv507 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv503 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState148
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148) : 'freshtv504)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv505 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv506)) : 'freshtv508)
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv513 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv509 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState151 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState151
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151) : 'freshtv510)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv511 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv512)) : 'freshtv514)
    | _ ->
        _menhir_fail ()

and _menhir_goto_params : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_params -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv489 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2674 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv487 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2680 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2685 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _v : 'tv_params = 
# 159 "specParser.mly"
                       ((RelId.fromString i)::p)
# 2690 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv488)) : 'freshtv490)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv497 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2698 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv493 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2708 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv491 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2718 "specParser.ml"
                )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState7 in
                ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | ID _v ->
                    _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState73 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73) : 'freshtv492)
            | ID _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
            | LPAREN ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState7
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv494)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv495 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2746 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv496)) : 'freshtv498)
    | _ ->
        _menhir_fail ()

and _menhir_goto_conpat : _menhir_env -> 'ttv_tail -> 'tv_conpat -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv485 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv481 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv477 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | LPAREN ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | TRUE ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv478)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv479 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv480)) : 'freshtv482)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv483 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv484)) : 'freshtv486)

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 2807 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv471 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2819 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv472)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv473 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2835 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2840 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_idseq = 
# 179 "specParser.mly"
             ([Var.fromString i])
# 2845 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv474)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv475 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2855 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv476)

and _menhir_goto_conargs : _menhir_env -> 'ttv_tail -> 'tv_conargs -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv469 * (
# 60 "specParser.mly"
        (string)
# 2866 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let (_v : 'tv_conargs) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv467 * (
# 60 "specParser.mly"
        (string)
# 2873 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let ((co : 'tv_conargs) : 'tv_conargs) = _v in
    ((let (_menhir_stack, (i : (
# 60 "specParser.mly"
        (string)
# 2879 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_conpat = 
# 174 "specParser.mly"
                          ((Con.fromString i, Some co))
# 2884 "specParser.ml"
     in
    _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv468)) : 'freshtv470)

and _menhir_goto_paramseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_paramseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState97 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv451 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2897 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv449 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2903 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2908 "specParser.ml"
        ))), _, (pseq : 'tv_paramseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_paramseq = 
# 162 "specParser.mly"
                                  ((RelId.fromString i)::pseq)
# 2914 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv450)) : 'freshtv452)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv465 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv461 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv457 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 2935 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv453 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 2946 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
                    | LBRACE ->
                        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | LCURLY ->
                        _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | LPAREN ->
                        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | REF ->
                        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102) : 'freshtv454)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv455 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 2972 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv456)) : 'freshtv458)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv459 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv460)) : 'freshtv462)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv463 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv464)) : 'freshtv466)
    | _ ->
        _menhir_fail ()

and _menhir_reduce22 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let t = () in
    let _v : 'tv_elem = 
# 222 "specParser.mly"
              (Bool(true))
# 3000 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_patom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState223 | MenhirState191 | MenhirState204 | MenhirState187 | MenhirState116 | MenhirState119 | MenhirState148 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState169 | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv443 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | CONJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv431 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState176
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176) : 'freshtv432)
        | DISJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv433 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174) : 'freshtv434)
        | IFF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv435 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172) : 'freshtv436)
        | IMPL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv437 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState169 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState169
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState169) : 'freshtv438)
        | RCURLY | RPAREN | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv439 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (pa : 'tv_patom)) = _menhir_stack in
            let _v : 'tv_pred = 
# 291 "specParser.mly"
                 (pa)
# 3149 "specParser.ml"
             in
            _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv440)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv441 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv442)) : 'freshtv444)
    | MenhirState118 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv447 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv445 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (pa : 'tv_patom)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 299 "specParser.mly"
                     (Predicate.Not pa)
# 3169 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv446)) : 'freshtv448)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ratom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_ratom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv429 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARMINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv415 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState65
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState65 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState65
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState65
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState65
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv416)
    | CROSSPRD ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv417 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState63 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState63
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63) : 'freshtv418)
    | MINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv419 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState61
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState61 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState61
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState61
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState61
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61) : 'freshtv420)
    | PLUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv421 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59) : 'freshtv422)
    | UNION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv423 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46) : 'freshtv424)
    | ANGRIGHT | CONJ | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | NUMEQ | PIPE | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv425 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ra : 'tv_ratom)) = _menhir_stack in
        let _v : 'tv_rexpr = 
# 199 "specParser.mly"
                 (ra)
# 3300 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv426)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv427 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv428)) : 'freshtv430)

and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3314 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_bpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_bpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv413) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_bpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv411) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ba : 'tv_bpatom) : 'tv_bpatom) = _v in
    ((let _v : 'tv_patom = 
# 301 "specParser.mly"
                  (Predicate.Base ba)
# 3334 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv412)) : 'freshtv414)

and _menhir_reduce24 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3341 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3347 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_elem = 
# 224 "specParser.mly"
            (Var(Var.fromString i))
# 3352 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce32 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3359 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3365 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_instexpr = 
# 182 "specParser.mly"
                (RInst { sargs = empty (); 
                targs = empty(); args = empty (); 
                rel = RelId.fromString i})
# 3372 "specParser.ml"
     in
    _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37

and _menhir_goto_elem : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState34 | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv399 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv393 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | ID _v ->
                _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
            | TRUE ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState34
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34) : 'freshtv394)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv395 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
            let _v : 'tv_elemseq = 
# 218 "specParser.mly"
                  ([el])
# 3424 "specParser.ml"
             in
            _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv396)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv397 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv398)) : 'freshtv400)
    | MenhirState223 | MenhirState191 | MenhirState204 | MenhirState187 | MenhirState116 | MenhirState118 | MenhirState148 | MenhirState151 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState169 | MenhirState165 | MenhirState163 | MenhirState161 | MenhirState159 | MenhirState157 | MenhirState152 | MenhirState88 | MenhirState91 | MenhirState71 | MenhirState20 | MenhirState65 | MenhirState63 | MenhirState61 | MenhirState59 | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv401 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        (_menhir_reduce67 _menhir_env (Obj.magic _menhir_stack) : 'freshtv402)
    | MenhirState119 | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv409 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv405 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv403 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (el : 'tv_elem)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_ratom = 
# 207 "specParser.mly"
                              (T[el])
# 3456 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv404)) : 'freshtv406)
        | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | SUBSET | SUBSETEQ | UNION ->
            _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv407 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv408)) : 'freshtv410)
    | _ ->
        _menhir_fail ()

and _menhir_run139 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv389 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 3483 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv385 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3494 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState141
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141) : 'freshtv386)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv387 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3516 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv388)) : 'freshtv390)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv391 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv392)

and _menhir_run107 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3531 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_tyd : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tyd -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState103 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv345 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv343 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (t : 'tv_tyd)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_tyd = 
# 269 "specParser.mly"
             (TyD.makeTRef t )
# 3552 "specParser.ml"
         in
        _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv344)) : 'freshtv346)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv351 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3560 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv347 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3570 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116) : 'freshtv348)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv349 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3608 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv350)) : 'freshtv352)
    | MenhirState141 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv369 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3617 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv365 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3627 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv363 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3634 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), (v : (
# 60 "specParser.mly"
        (string)
# 3639 "specParser.ml"
            ))), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartybind = 
# 335 "specParser.mly"
   ((v, ty))
# 3647 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv361) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_vartybind) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv359 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | COMMA ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv353 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LPAREN ->
                    _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState145
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState145) : 'freshtv354)
            | DOT ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv355 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (vty : 'tv_vartybind)) = _menhir_stack in
                let _v : 'tv_tybindseq = 
# 331 "specParser.mly"
                          ([vty])
# 3678 "specParser.ml"
                 in
                _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv356)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv357 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv358)) : 'freshtv360)) : 'freshtv362)) : 'freshtv364)) : 'freshtv366)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv367 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3695 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv368)) : 'freshtv370)
    | MenhirState112 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv379 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv371 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187) : 'freshtv372)
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv375 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv373 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 274 "specParser.mly"
                              (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, 
                Predicate.truee()))
# 3751 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv374)) : 'freshtv376)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv377 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv378)) : 'freshtv380)
    | MenhirState228 | MenhirState219 | MenhirState102 | MenhirState215 | MenhirState111 | MenhirState195 | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv383 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv381 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ty : 'tv_tyd)) = _menhir_stack in
        let _v : 'tv_basety = 
# 271 "specParser.mly"
                (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty,
                Predicate.truee()))
# 3772 "specParser.ml"
         in
        _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv382)) : 'freshtv384)
    | _ ->
        _menhir_fail ()

and _menhir_reduce94 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3781 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (
# 60 "specParser.mly"
        (string)
# 3787 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_tyd = 
# 267 "specParser.mly"
            (TyD.fromString t)
# 3792 "specParser.ml"
     in
    _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3799 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState4 _v
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv341 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3813 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3818 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_params = 
# 158 "specParser.mly"
                ([RelId.fromString i])
# 3823 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv342)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 3843 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv329) = Obj.magic _menhir_stack in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 3855 "specParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv327) = Obj.magic _menhir_stack in
            let ((i : (
# 60 "specParser.mly"
        (string)
# 3863 "specParser.ml"
            )) : (
# 60 "specParser.mly"
        (string)
# 3867 "specParser.ml"
            )) = _v in
            ((let _v : 'tv_conargs = 
# 176 "specParser.mly"
               (Vector.fromList [Var.fromString i])
# 3872 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv328)) : 'freshtv330)
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv331) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10) : 'freshtv332)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv333 * (
# 60 "specParser.mly"
        (string)
# 3892 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, (i : (
# 60 "specParser.mly"
        (string)
# 3897 "specParser.ml"
            ))) = _menhir_stack in
            let _v : 'tv_conpat = 
# 173 "specParser.mly"
               ((Con.fromString i, None))
# 3902 "specParser.ml"
             in
            _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv334)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv335 * (
# 60 "specParser.mly"
        (string)
# 3912 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv336)) : 'freshtv338)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv339 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3926 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQUALOP ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv323 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3938 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState71 _v
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | LPAREN ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState71
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71) : 'freshtv324)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv325 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3966 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv326)

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3974 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | RBRACE | STAR ->
        _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_run89 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv319 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4031 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv315 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4042 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
            | LAMBDA ->
                _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | LPAREN ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | TRUE ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState91
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv316)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv317 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4072 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv318)) : 'freshtv320)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv321 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv322)

and _menhir_run96 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 4087 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv309 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4099 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97) : 'freshtv310)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv311 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4115 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 4120 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_paramseq = 
# 161 "specParser.mly"
                    ([RelId.fromString i])
# 4125 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv312)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv313 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4135 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv314)

and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONJ | DISJ | IFF | IMPL | RCURLY | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv305 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 298 "specParser.mly"
             (Predicate.truee())
# 4154 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv306)
    | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | RPAREN | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv307 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)

and _menhir_run118 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
    | LBRACE ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | LPAREN ->
        _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | NOT ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | TRUE ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState118
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118

and _menhir_run119 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | EXISTS ->
        _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState119 _v
    | LAMBDA ->
        _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | LBRACE ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | LPAREN ->
        _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | NOT ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | TRUE ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState119
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState119

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv301 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | ID _v ->
            _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv299 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState24 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv295 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv293 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 202 "specParser.mly"
                                    (T(Vector.fromList []))
# 4269 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv294)) : 'freshtv296)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv297 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)) : 'freshtv300)
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24) : 'freshtv302)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv303 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)

and _menhir_run120 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv289 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4305 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv265 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4316 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv229 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4326 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv225 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4336 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv223 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4343 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4348 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 309 "specParser.mly"
                                           (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, false))
# 4358 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv224)) : 'freshtv226)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv227 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4368 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv228)) : 'freshtv230)
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv237 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4377 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 4382 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv233 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4393 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4397 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv231 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4404 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4408 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4413 "specParser.ml"
                    ))), (i2 : (
# 60 "specParser.mly"
        (string)
# 4417 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 305 "specParser.mly"
                                           (Predicate.BasePredicate.varEq 
                      (Var.fromString i1, Var.fromString i2))
# 4426 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv232)) : 'freshtv234)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv235 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4436 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4440 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv236)) : 'freshtv238)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv245 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4449 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
       (int)
# 4454 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv241 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4465 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4469 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv239 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4476 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4480 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4485 "specParser.ml"
                    ))), (rhs : (
# 61 "specParser.mly"
       (int)
# 4489 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 315 "specParser.mly"
                                              (Predicate.BasePredicate.varIntEq 
                      (Var.fromString i1, rhs))
# 4498 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv240)) : 'freshtv242)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv243 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4508 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4512 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv244)) : 'freshtv246)
            | STRCONST _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv253 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4521 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (string)
# 4526 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv249 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4537 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4541 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv247 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4548 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4552 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4557 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (string)
# 4561 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 317 "specParser.mly"
                                                   (
       				let rhstrimmed = String.sub (rhs) (1) ((String.length rhs) - 2) in 
       				Predicate.BasePredicate.varStrEq 
                      (Var.fromString i1, rhstrimmed))
# 4572 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv248)) : 'freshtv250)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv251 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4582 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4586 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv252)) : 'freshtv254)
            | TRUE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv261 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4595 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv257 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4605 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv255 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4612 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4617 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 307 "specParser.mly"
                                          (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, true))
# 4627 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv256)) : 'freshtv258)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv259 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4637 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv260)) : 'freshtv262)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv263 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4648 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv264)) : 'freshtv266)
        | GREATERTHAN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv285 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4657 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv273 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4667 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 4672 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv269 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4683 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4687 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv267 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4694 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4698 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4703 "specParser.ml"
                    ))), (i2 : (
# 60 "specParser.mly"
        (string)
# 4707 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 311 "specParser.mly"
                                                (Predicate.BasePredicate.varGt 
                      (Var.fromString i1, Var.fromString i2))
# 4716 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv268)) : 'freshtv270)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv271 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4726 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4730 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv272)) : 'freshtv274)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv281 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4739 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
       (int)
# 4744 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv277 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4755 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4759 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv275 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4766 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4770 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4775 "specParser.ml"
                    ))), (rhs : (
# 61 "specParser.mly"
       (int)
# 4779 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 313 "specParser.mly"
                                                  (Predicate.BasePredicate.varIntGt 
                      (Var.fromString i1, rhs))
# 4788 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv276)) : 'freshtv278)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv279 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4798 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4802 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv280)) : 'freshtv282)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv283 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4813 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv284)) : 'freshtv286)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv287 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4824 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv288)) : 'freshtv290)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv291 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv292)

and _menhir_run138 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState138
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
       (int)
# 4852 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv221) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ii : (
# 61 "specParser.mly"
       (int)
# 4862 "specParser.ml"
    )) : (
# 61 "specParser.mly"
       (int)
# 4866 "specParser.ml"
    )) = _v in
    ((let _v : 'tv_elem = 
# 221 "specParser.mly"
              (Int(ii))
# 4871 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv222)

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 4878 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | LPAREN ->
        _menhir_reduce32 _menhir_env (Obj.magic _menhir_stack)
    | ANGRIGHT | ARMINUS | CONJ | CROSSPRD | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | MINUS | NUMEQ | PIPE | PLUS | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv219) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let f = () in
    let _v : 'tv_elem = 
# 223 "specParser.mly"
               (Bool(false))
# 4906 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv220)

and _menhir_run149 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState149
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149

and _menhir_run152 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState152
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState152
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState152
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState152
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152

and _menhir_run103 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
    | LBRACE ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState103
    | REF ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState103
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv217 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState109 in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4976 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv213 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4987 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | LCURLY ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | LPAREN ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState111
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111) : 'freshtv214)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv215 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5013 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv216)) : 'freshtv218)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109

and _menhir_run112 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv211 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState112 in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 5035 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv207 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5046 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114) : 'freshtv208)
        | PIPE | RCURLY ->
            _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv209 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5070 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv210)) : 'freshtv212)
    | LBRACE ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState112
    | REF ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState112
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState112

and _menhir_run104 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv203 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 5095 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv199 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5106 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv197 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5113 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), (t : (
# 60 "specParser.mly"
        (string)
# 5118 "specParser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_tyd = 
# 268 "specParser.mly"
                      (TyD.makeTList (TyD.fromString t))
# 5125 "specParser.ml"
             in
            _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv198)) : 'freshtv200)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv201 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5135 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)) : 'freshtv204)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv205 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)

and _menhir_run190 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 5150 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LCURLY ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv193 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5162 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGLEFT ->
            _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | EXISTS ->
            _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
        | LAMBDA ->
            _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | LBRACE ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | LPAREN ->
            _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | NOT ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | TRUE ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState191
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191) : 'freshtv194)
    | COMMA | RPAREN | SEMICOLON ->
        _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv195 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5202 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState237 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv55 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState235 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState233 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState231 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState228 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv63 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5235 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv65 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5244 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState219 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5253 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState215 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv69 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5262 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState213 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * 'tv_varty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState204 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv73 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5276 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 5280 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState197 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv75 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv77 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5294 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 60 "specParser.mly"
        (string)
# 5298 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5307 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv81 * _menhir_state) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv85 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState169 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv89 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState165 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv91 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState163 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv99 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState152 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv101 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv103 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv105 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState148 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv107 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState145 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state * 'tv_vartybind)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState141 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv111 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5391 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState138 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv113 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState119 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState118 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv117 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv119 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5415 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv121 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5424 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState112 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv124)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv125 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5438 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv127 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState103 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv129 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv131 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 5457 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState97 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv133 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5466 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv135 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv137 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5480 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv139 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5489 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv141 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5498 "specParser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv143 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5507 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv145 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv147 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5521 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv149 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5530 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv151 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv153 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv157 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv159 * _menhir_state * 'tv_funparam)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv161 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv163 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv165 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5579 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv169 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv171 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5593 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * 'tv_elem)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv175 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv177 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv179 * _menhir_state) * 'tv_conpat))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv181 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5622 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState10 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv183) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv184)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv185 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5635 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5644 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv189 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5653 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv191) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv192)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 5674 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv43 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5685 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState80 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81) : 'freshtv44)
        | ID _v ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
        | LPAREN ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState80
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80) : 'freshtv46)
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv51 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv47 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 5718 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3) : 'freshtv48)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv49 * _menhir_state)) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)) : 'freshtv52)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)

and _menhir_run85 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RELATION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv39 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv35 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 5763 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv31 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5774 "specParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | FALSE ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                | ID _v ->
                    _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                | INT _v ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                | LAMBDA ->
                    _menhir_run89 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                | LCURLY ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                | LPAREN ->
                    _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                | TRUE ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88) : 'freshtv32)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv33 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5804 "specParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)) : 'freshtv36)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv37 * _menhir_state)) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)) : 'freshtv40)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv41 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)

and _menhir_run95 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95

and _menhir_run218 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 5839 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5851 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
        | LBRACE ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | LCURLY ->
            _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | LPAREN ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | REF ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5877 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run221 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 5894 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv19 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5905 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | EXISTS ->
                _menhir_run149 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
            | LAMBDA ->
                _menhir_run138 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LPAREN ->
                _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | NOT ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | TRUE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223) : 'freshtv20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv21 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5943 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv22)) : 'freshtv24)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)

and _menhir_goto_start : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5958 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5967 "specParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv15) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5975 "specParser.ml"
    )) : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5979 "specParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv16)) : 'freshtv18)

and _menhir_run226 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 5995 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv7 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 6006 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run190 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | LCURLY ->
                _menhir_run112 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | LPAREN ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState228
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228) : 'freshtv8)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv9 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 6032 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv13 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv14)

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

and start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6059 "specParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv5) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASSUME ->
        _menhir_run226 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        ((let _1 = () in
        let _v : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6091 "specParser.ml"
        ) = 
# 79 "specParser.mly"
              (RelSpec.mk_empty_relspec ())
# 6095 "specParser.ml"
         in
        _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2)) : 'freshtv4)
    | FORMULA ->
        _menhir_run221 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ID _v ->
        _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LPAREN ->
        _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | PRIMITIVE ->
        _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | RELATION ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv6))

# 233 "/home/ashish/.opam/4.03.0/lib/menhir/standard.mly"
  

# 6116 "specParser.ml"
