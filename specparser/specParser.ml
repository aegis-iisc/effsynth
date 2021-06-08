
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
  | MenhirState229
  | MenhirState227
  | MenhirState225
  | MenhirState223
  | MenhirState220
  | MenhirState215
  | MenhirState211
  | MenhirState206
  | MenhirState199
  | MenhirState193
  | MenhirState191
  | MenhirState189
  | MenhirState185
  | MenhirState174
  | MenhirState172
  | MenhirState170
  | MenhirState167
  | MenhirState163
  | MenhirState161
  | MenhirState159
  | MenhirState157
  | MenhirState155
  | MenhirState150
  | MenhirState149
  | MenhirState147
  | MenhirState146
  | MenhirState143
  | MenhirState139
  | MenhirState136
  | MenhirState117
  | MenhirState116
  | MenhirState114
  | MenhirState112
  | MenhirState110
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


# 176 "specParser.ml"

let rec _menhir_goto_decsandtys : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decsandtys -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState229 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv881 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv879 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
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
# 201 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv880)) : 'freshtv882)
    | MenhirState227 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv885 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv883 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
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
# 225 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv884)) : 'freshtv886)
    | MenhirState225 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv889 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv887 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
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
# 249 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv888)) : 'freshtv890)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv893 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv891 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
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
# 272 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv892)) : 'freshtv894)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv907) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv905) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let _v : 'tv_spec = 
# 82 "specParser.mly"
                   (
                  d)
# 288 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv903) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_spec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv901 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv897 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv895 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (s : 'tv_spec)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 310 "specParser.ml"
            ) = 
# 78 "specParser.mly"
               (s)
# 314 "specParser.ml"
             in
            _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv896)) : 'freshtv898)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv899 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv900)) : 'freshtv902)) : 'freshtv904)) : 'freshtv906)) : 'freshtv908)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typespec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typespec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv877 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv873 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | FORMULA ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | ID _v ->
            _menhir_run210 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
        | LPAREN ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | PRIMITIVE ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | RELATION ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | EOF ->
            _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState223
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223) : 'freshtv874)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv875 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv876)) : 'freshtv878)

and _menhir_goto_vartyseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv867 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv863 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv857 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_vartyatom = 
# 262 "specParser.mly"
                                  (
                      
                      match vas with
                          [x] -> x 
                        | _ -> (genVar (), RefTy.Tuple 
                            (Vector.fromList vas))
                  )
# 398 "specParser.ml"
                 in
                _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv858)
            | COMMA | RPAREN | SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv859 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_reftyatom = 
# 249 "specParser.mly"
                                        (
                         
                          match vas with
                                 
                          [(v, (RefTy.Base (_, _, _) as refty))] -> 
                              RefTy.alphaRenameToVar (refty) v
                        | [(v,refty)] -> refty
                        | _ -> RefTy.Tuple (Vector.fromList vas))
# 417 "specParser.ml"
                 in
                _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv860)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv861 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv862)) : 'freshtv864)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv865 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv866)) : 'freshtv868)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv871 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv869 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_varty)), _, (vts : 'tv_vartyseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_vartyseq = 
# 271 "specParser.mly"
                                       (vt :: vts)
# 444 "specParser.ml"
         in
        _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv870)) : 'freshtv872)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv847 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 458 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv845 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 466 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 473 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_reldec = 
# 144 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = p;
                mapp = patmseq})
# 483 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv846)) : 'freshtv848)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv851 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv849 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((pms : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatchseq = 
# 164 "specParser.mly"
                                               (pm :: pms)
# 500 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv850)) : 'freshtv852)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv855 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 508 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv853 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 516 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 523 "specParser.ml"
        ))) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_reldec = 
# 140 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = empty ();
                mapp = patmseq})
# 531 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv854)) : 'freshtv856)
    | _ ->
        _menhir_fail ()

and _menhir_goto_funparams : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_funparams -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv839 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv835 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv833 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (ps : 'tv_funparams)) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_ratom = 
# 204 "specParser.mly"
                                               (MultiR (ie, ps))
# 559 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv834)) : 'freshtv836)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv837 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv838)) : 'freshtv840)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv843 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv841 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (p : 'tv_funparam)), _, (ps : 'tv_funparams)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_funparams = 
# 214 "specParser.mly"
                                 (p::ps)
# 579 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv842)) : 'freshtv844)
    | _ ->
        _menhir_fail ()

and _menhir_reduce20 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_decsandtys = 
# 121 "specParser.mly"
                (RelSpec.T {
  			preds = Vector.new0 ();
  			reldecs = [];
                  primdecs = Vector.new0 ();
                  typespecs = []})
# 594 "specParser.ml"
     in
    _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_refty : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_refty -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState199 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv805 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_refty) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv803 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((rt : 'tv_refty) : 'tv_refty) = _v in
        ((let (_menhir_stack, _menhir_s, (vrta : 'tv_vartyatom)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_refty = 
# 244 "specParser.mly"
                                      (  
                                          RefTy.Arrow (((fst (vrta)) , (snd vrta)), rt))
# 616 "specParser.ml"
         in
        _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv804)) : 'freshtv806)
    | MenhirState109 | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv819) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_refty) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv817) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((rt : 'tv_refty) : 'tv_refty) = _v in
        ((let _v : 'tv_varty = 
# 273 "specParser.mly"
                 (let open RefTy in 
                        match rt with
                          Base (v,_,_) -> (v,alphaRename rt)
                        | Tuple _ -> (genVar (),rt)
                        | Arrow _ -> (genVar (),rt)
			| MArrow _ -> (genVar (), rt) 
              )
# 637 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv815) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_varty) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv813 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv807 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LCURLY ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LPAREN ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206) : 'freshtv808)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv809 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (vt : 'tv_varty)) = _menhir_stack in
            let _v : 'tv_vartyseq = 
# 270 "specParser.mly"
                    ([vt])
# 676 "specParser.ml"
             in
            _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv810)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv811 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv812)) : 'freshtv814)) : 'freshtv816)) : 'freshtv818)) : 'freshtv820)
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv823 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 691 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_refty) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv821 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 699 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((rt : 'tv_refty) : 'tv_refty) = _v in
        ((let (((_menhir_stack, _menhir_s), _, (ps : 'tv_paramseq)), (i : (
# 60 "specParser.mly"
        (string)
# 706 "specParser.ml"
        ))) = _menhir_stack in
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
# 718 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv822)) : 'freshtv824)
    | MenhirState211 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv827 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 726 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_refty) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv825 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 734 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((rt : 'tv_refty) : 'tv_refty) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 741 "specParser.ml"
        ))) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typespec = 
# 233 "specParser.mly"
                               (      TypeSpec.T {isAssume = false;
                                       name = (Var.fromString i);
                                       params = empty ();
                                       refty = rt})
# 750 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv826)) : 'freshtv828)
    | MenhirState220 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv831 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 758 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_refty) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv829 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 766 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((rt : 'tv_refty) : 'tv_refty) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 773 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 228 "specParser.mly"
                                      (
                                          TypeSpec.T {isAssume = true;
                                              name = (Var.fromString i);
                                              params = empty ();
                                              refty = rt})
# 784 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv830)) : 'freshtv832)
    | _ ->
        _menhir_fail ()

and _menhir_run155 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155

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

and _menhir_goto_rpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv801) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_rpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv799) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ra : 'tv_rpatom) : 'tv_rpatom) = _v in
    ((let _v : 'tv_patom = 
# 315 "specParser.mly"
                  (Predicate.Rel ra)
# 913 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv800)) : 'freshtv802)

and _menhir_goto_primdef : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_primdef -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv785 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 925 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv783 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 933 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 940 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_primdef = 
# 135 "specParser.mly"
                                    (PrimitiveRelation.Nary
                (Var.fromString i, p))
# 948 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv784)) : 'freshtv786)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv797 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 956 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv795 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 964 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 971 "specParser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_primdec = 
# 130 "specParser.mly"
                                                    (PrimitiveRelation.T
                    {id=RelId.fromString i; 
                    def=PrimitiveRelation.alphaRename p})
# 981 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv793) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv791 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv787 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | FORMULA ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | ID _v ->
                _menhir_run210 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
            | LPAREN ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | PRIMITIVE ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | RELATION ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | EOF ->
                _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState227
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227) : 'freshtv788)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv789 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv790)) : 'freshtv792)) : 'freshtv794)) : 'freshtv796)) : 'freshtv798)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv781 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv775 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv776)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv777 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _v : 'tv_patmatchseq = 
# 165 "specParser.mly"
                          ([pm])
# 1056 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv778)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv779 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv780)) : 'freshtv782)

and _menhir_run44 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv773 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
    ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _v : 'tv_ratom = 
# 206 "specParser.mly"
                               (re)
# 1078 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv774)

and _menhir_goto_reldec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reldec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv771 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv767 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | FORMULA ->
            _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | ID _v ->
            _menhir_run210 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
        | LPAREN ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | PRIMITIVE ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | RELATION ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | EOF ->
            _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState225
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225) : 'freshtv768)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv769 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv770)) : 'freshtv772)

and _menhir_reduce27 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1125 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1131 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_funparam = 
# 216 "specParser.mly"
                (Var.fromString i)
# 1136 "specParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv765) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_funparam) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv763 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv757 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv755) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState55 in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 1161 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv756)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55) : 'freshtv758)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv759 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_funparam)) = _menhir_stack in
        let _v : 'tv_funparams = 
# 213 "specParser.mly"
                       ([p])
# 1177 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv760)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv761 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv762)) : 'freshtv764)) : 'freshtv766)

and _menhir_goto_instexprs : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexprs -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState36 | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv749 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1196 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv747 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1204 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1211 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_instexpr = 
# 185 "specParser.mly"
                              (RInst {
                sargs = empty (); targs = empty();
                args = Vector.fromList ies;
                rel = RelId.fromString i})
# 1219 "specParser.ml"
         in
        _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv748)) : 'freshtv750)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv753 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv751 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_instexprs = 
# 191 "specParser.mly"
                                                    (ie :: ies)
# 1237 "specParser.ml"
         in
        _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv752)) : 'freshtv754)
    | _ ->
        _menhir_fail ()

and _menhir_goto_reftyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reftyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv745) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_reftyatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv743) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((rta : 'tv_reftyatom) : 'tv_reftyatom) = _v in
    ((let _v : 'tv_refty = 
# 243 "specParser.mly"
                      ( rta)
# 1256 "specParser.ml"
     in
    _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv744)) : 'freshtv746)

and _menhir_goto_vartyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv741 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv737 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
        | LBRACE ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | LCURLY ->
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | LPAREN ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | REF ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState199
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199) : 'freshtv738)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv739 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv740)) : 'freshtv742)

and _menhir_goto_idseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_idseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv727 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1305 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv725 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1311 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1316 "specParser.ml"
        ))), _, (is : 'tv_idseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_idseq = 
# 180 "specParser.mly"
                            ((Var.fromString i)::is)
# 1322 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv726)) : 'freshtv728)
    | MenhirState10 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv735) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv731) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv729) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, (is : 'tv_idseq)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_conargs = 
# 177 "specParser.mly"
                                 (Vector.fromList is)
# 1343 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv730)) : 'freshtv732)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv733) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv734)) : 'freshtv736)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pred : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_pred -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv647 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv645 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 310 "specParser.mly"
                                           (Predicate.Exists (binds, pr))
# 1371 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv646)) : 'freshtv648)
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv651 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv649 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 305 "specParser.mly"
                              (Predicate.If (pa,pr))
# 1384 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv650)) : 'freshtv652)
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv655 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv653 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 306 "specParser.mly"
                             (Predicate.Iff (pa,pr))
# 1397 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv654)) : 'freshtv656)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv659 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv657 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 308 "specParser.mly"
                              (Predicate.Disj (pa,pr))
# 1410 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv658)) : 'freshtv660)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv663 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv661 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 307 "specParser.mly"
                              (Predicate.Conj (pa,pr))
# 1423 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv662)) : 'freshtv664)
    | MenhirState146 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv667 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv665 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 309 "specParser.mly"
                                           (Predicate.Forall (binds, pr) )
# 1437 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv666)) : 'freshtv668)
    | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv675 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv671 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv669 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (pr : 'tv_pred)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_patom = 
# 313 "specParser.mly"
                              (pr)
# 1458 "specParser.ml"
             in
            _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv670)) : 'freshtv672)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv673 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv674)) : 'freshtv676)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv683 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1473 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv679 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1483 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv677 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1490 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), _, (v : (
# 60 "specParser.mly"
        (string)
# 1495 "specParser.ml"
            ))), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 292 "specParser.mly"
                                                       (RefinementType.Base ((Var.fromString v), 
                ty, pr))
# 1505 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv678)) : 'freshtv680)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv681 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1515 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv682)) : 'freshtv684)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv691 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv687 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv685 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 290 "specParser.mly"
                                           (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, pr))
# 1539 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv686)) : 'freshtv688)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv689 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv690)) : 'freshtv692)
    | MenhirState189 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv697 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1554 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv693 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1564 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191) : 'freshtv694)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv695 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1586 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv696)) : 'freshtv698)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv711 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1595 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv707 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1605 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv705 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1612 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s, (ef : (
# 60 "specParser.mly"
        (string)
# 1617 "specParser.ml"
            ))), _, (pre : 'tv_pred)), _, (resty : 'tv_tyd)), _, (post : 'tv_pred)) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_mty = 
# 295 "specParser.mly"
                                                                      (RefTy.MArrow (Effect.fromString ef, pre, resty, post))
# 1626 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv703) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv701) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv699) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((mtype : 'tv_mty) : 'tv_mty) = _v in
            ((let _v : 'tv_refty = 
# 246 "specParser.mly"
                  (mtype)
# 1643 "specParser.ml"
             in
            _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv700)) : 'freshtv702)) : 'freshtv704)) : 'freshtv706)) : 'freshtv708)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv709 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1653 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv710)) : 'freshtv712)
    | MenhirState215 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv723 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1662 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv721 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 1668 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 1673 "specParser.ml"
        ))), _, (p : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_predspec = 
# 128 "specParser.mly"
                                       (Formula.Form{name=Var.fromString i;pred = p})
# 1680 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv719) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_predspec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv717 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv713 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | FORMULA ->
                _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | ID _v ->
                _menhir_run210 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
            | LPAREN ->
                _menhir_run95 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | PRIMITIVE ->
                _menhir_run85 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | RELATION ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | EOF ->
                _menhir_reduce20 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229) : 'freshtv714)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv715 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv716)) : 'freshtv718)) : 'freshtv720)) : 'freshtv722)) : 'freshtv724)
    | _ ->
        _menhir_fail ()

and _menhir_goto_rexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv575 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv573 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv574)) : 'freshtv576)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv579 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv577 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 195 "specParser.mly"
                                (U(ra,re))
# 1755 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv578)) : 'freshtv580)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv583 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv581 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 197 "specParser.mly"
                               (ADD(ra,re))
# 1768 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv582)) : 'freshtv584)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv587 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv585 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 196 "specParser.mly"
                                (D(ra,re))
# 1781 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv586)) : 'freshtv588)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv591 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv589 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 194 "specParser.mly"
                                   (X(ra,re))
# 1794 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv590)) : 'freshtv592)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv595 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv593 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 198 "specParser.mly"
                                  (SUBS(ra,re))
# 1807 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv594)) : 'freshtv596)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv599 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv597 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (cp : 'tv_conpat)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_patmatch = 
# 169 "specParser.mly"
              (match cp with (c,vlop) -> (c, vlop, Expr re))
# 1822 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv598)) : 'freshtv600)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv603 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1830 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv601 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 1836 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 1841 "specParser.ml"
        ))), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatch = 
# 170 "specParser.mly"
                                 ((Con.fromString i, None, Expr re))
# 1847 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv602)) : 'freshtv604)
    | MenhirState88 | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv607 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv605 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (re : 'tv_rexpr)) = _menhir_stack in
        let _v : 'tv_primdef = 
# 134 "specParser.mly"
                   (PrimitiveRelation.Nullary re)
# 1859 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv606)) : 'freshtv608)
    | MenhirState150 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv615 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGRIGHT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv611 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv609 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_rpatom = 
# 336 "specParser.mly"
                                   (Predicate.RelPredicate.Q (re))
# 1880 "specParser.ml"
             in
            _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv610)) : 'freshtv612)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv613 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv614)) : 'freshtv616)
    | MenhirState215 | MenhirState193 | MenhirState189 | MenhirState185 | MenhirState114 | MenhirState116 | MenhirState146 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState167 | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv619 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv617 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv618)) : 'freshtv620)
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv623 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv621 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 339 "specParser.mly"
                                      (Predicate.RelPredicate.SubEq(re1,re2))
# 1923 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv622)) : 'freshtv624)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv627 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv625 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 338 "specParser.mly"
                                    (Predicate.RelPredicate.Sub(re1,re2))
# 1936 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv626)) : 'freshtv628)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv631 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv629 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 340 "specParser.mly"
                                   (Predicate.RelPredicate.NEq(re1, re2) )
# 1949 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv630)) : 'freshtv632)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv635 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv633 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 341 "specParser.mly"
                                         (Predicate.RelPredicate.NEq(re1, re2))
# 1962 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv634)) : 'freshtv636)
    | MenhirState163 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv639 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv637 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 337 "specParser.mly"
                                     (Predicate.RelPredicate.Eq(re1,re2))
# 1975 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv638)) : 'freshtv640)
    | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv643 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run163 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run161 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run159 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run155 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv641 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv642)) : 'freshtv644)
    | _ ->
        _menhir_fail ()

and _menhir_goto_instexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv541 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv537 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LBRACE ->
                _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState41
            | LPAREN | RBRACE | STAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv535 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_instexprs = 
# 190 "specParser.mly"
                                      ([ie])
# 2033 "specParser.ml"
                 in
                _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv536)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41) : 'freshtv538)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv539 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv540)) : 'freshtv542)
    | MenhirState215 | MenhirState189 | MenhirState193 | MenhirState185 | MenhirState114 | MenhirState116 | MenhirState117 | MenhirState146 | MenhirState149 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState167 | MenhirState163 | MenhirState161 | MenhirState159 | MenhirState157 | MenhirState155 | MenhirState150 | MenhirState88 | MenhirState91 | MenhirState71 | MenhirState20 | MenhirState22 | MenhirState65 | MenhirState63 | MenhirState61 | MenhirState59 | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv555 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv551 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv549 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState49 in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 2066 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RPAREN ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv545 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2077 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv543 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2084 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (i : (
# 60 "specParser.mly"
        (string)
# 2089 "specParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _v : 'tv_ratom = 
# 205 "specParser.mly"
                                       (R (ie, Var.fromString i))
# 2096 "specParser.ml"
                     in
                    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv544)) : 'freshtv546)
                | COMMA ->
                    _menhir_reduce27 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv547 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2108 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv548)) : 'freshtv550)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49) : 'freshtv552)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv553 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv554)) : 'freshtv556)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv563 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2128 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv559 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2138 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv557 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2145 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 2150 "specParser.ml"
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
# 2163 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv558)) : 'freshtv560)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv561 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2173 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv562)) : 'freshtv564)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv571 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2182 "specParser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv567 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2192 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv565 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2199 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), (i : (
# 60 "specParser.mly"
        (string)
# 2204 "specParser.ml"
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
# 2215 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv566)) : 'freshtv568)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv569 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 2225 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv570)) : 'freshtv572)
    | _ ->
        _menhir_fail ()

and _menhir_reduce67 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
    let _v : 'tv_ratom = 
# 208 "specParser.mly"
                (V (el))
# 2238 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_elemseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elemseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv529 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv525 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv521 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv519 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (els : 'tv_elemseq)) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 203 "specParser.mly"
                                                (T(Vector.fromList els))
# 2272 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv520)) : 'freshtv522)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv523 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv524)) : 'freshtv526)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv527 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv528)) : 'freshtv530)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv533 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv531 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (el : 'tv_elem)), _, (els : 'tv_elemseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_elemseq = 
# 219 "specParser.mly"
                                    (el::els)
# 2299 "specParser.ml"
         in
        _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv532)) : 'freshtv534)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_basety : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv517 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv511 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (bt : 'tv_basety)) = _menhir_stack in
        let _v : 'tv_vartyatom = 
# 258 "specParser.mly"
                      (
                      match bt with 
                       RefTy.Base (v,_,_) -> (v,bt)
                       | _ -> raise (Failure "Impossible case of basety"))
# 2328 "specParser.ml"
         in
        _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv512)
    | COMMA | RPAREN | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv513 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (bt : 'tv_basety)) = _menhir_stack in
        let _v : 'tv_reftyatom = 
# 248 "specParser.mly"
                      ( bt)
# 2338 "specParser.ml"
         in
        _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv514)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv515 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv516)) : 'freshtv518)

and _menhir_goto_tybindseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tybindseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv497 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv495 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_vartybind)), _, (vts : 'tv_tybindseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tybindseq = 
# 345 "specParser.mly"
                                            (vt :: vts)
# 2363 "specParser.ml"
         in
        _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv496)) : 'freshtv498)
    | MenhirState136 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv503 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv499 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState146
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146) : 'freshtv500)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv501 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv502)) : 'freshtv504)
    | MenhirState147 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv509 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv505 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState149
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149) : 'freshtv506)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv507 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv508)) : 'freshtv510)
    | _ ->
        _menhir_fail ()

and _menhir_goto_params : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_params -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv485 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2468 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv483 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2474 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2479 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _v : 'tv_params = 
# 159 "specParser.mly"
                       ((RelId.fromString i)::p)
# 2484 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv484)) : 'freshtv486)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv493 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2492 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv489 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2502 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv487 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2512 "specParser.ml"
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
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState73) : 'freshtv488)
            | ID _v ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
            | LPAREN ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState7
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv490)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv491 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 2540 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv492)) : 'freshtv494)
    | _ ->
        _menhir_fail ()

and _menhir_goto_conpat : _menhir_env -> 'ttv_tail -> 'tv_conpat -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv481 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv477 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv473 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv474)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv475 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv476)) : 'freshtv478)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv479 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv480)) : 'freshtv482)

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 2601 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv467 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2613 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv468)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv469 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2629 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2634 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_idseq = 
# 179 "specParser.mly"
             ([Var.fromString i])
# 2639 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv470)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv471 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2649 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv472)

and _menhir_goto_conargs : _menhir_env -> 'ttv_tail -> 'tv_conargs -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv465 * (
# 60 "specParser.mly"
        (string)
# 2660 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let (_v : 'tv_conargs) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv463 * (
# 60 "specParser.mly"
        (string)
# 2667 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let ((co : 'tv_conargs) : 'tv_conargs) = _v in
    ((let (_menhir_stack, (i : (
# 60 "specParser.mly"
        (string)
# 2673 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_conpat = 
# 174 "specParser.mly"
                          ((Con.fromString i, Some co))
# 2678 "specParser.ml"
     in
    _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv464)) : 'freshtv466)

and _menhir_goto_paramseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_paramseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState97 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv447 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2691 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv445 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 2697 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 2702 "specParser.ml"
        ))), _, (pseq : 'tv_paramseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_paramseq = 
# 162 "specParser.mly"
                                  ((RelId.fromString i)::pseq)
# 2708 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv446)) : 'freshtv448)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv461 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv457 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv453 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 2729 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv449 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 2740 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
                    | LBRACE ->
                        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | LCURLY ->
                        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | LPAREN ->
                        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | REF ->
                        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState102
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102) : 'freshtv450)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv451 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 2766 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv452)) : 'freshtv454)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv455 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv456)) : 'freshtv458)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv459 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv460)) : 'freshtv462)
    | _ ->
        _menhir_fail ()

and _menhir_reduce22 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let t = () in
    let _v : 'tv_elem = 
# 222 "specParser.mly"
              (Bool(true))
# 2794 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_patom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState215 | MenhirState189 | MenhirState193 | MenhirState185 | MenhirState114 | MenhirState117 | MenhirState146 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState167 | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv439 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | CONJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv427 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState174
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174) : 'freshtv428)
        | DISJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv429 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172) : 'freshtv430)
        | IFF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv431 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170) : 'freshtv432)
        | IMPL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv433 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167) : 'freshtv434)
        | RCURLY | RPAREN | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv435 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (pa : 'tv_patom)) = _menhir_stack in
            let _v : 'tv_pred = 
# 304 "specParser.mly"
                 (pa)
# 2943 "specParser.ml"
             in
            _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv436)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv437 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv438)) : 'freshtv440)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv443 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv441 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (pa : 'tv_patom)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 312 "specParser.mly"
                     (Predicate.Not pa)
# 2963 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv442)) : 'freshtv444)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ratom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_ratom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv425 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARMINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv411 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState65) : 'freshtv412)
    | CROSSPRD ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv413 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63) : 'freshtv414)
    | MINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv415 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState61) : 'freshtv416)
    | PLUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv417 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59) : 'freshtv418)
    | UNION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv419 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46) : 'freshtv420)
    | ANGRIGHT | CONJ | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | NUMEQ | PIPE | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv421 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ra : 'tv_ratom)) = _menhir_stack in
        let _v : 'tv_rexpr = 
# 199 "specParser.mly"
                 (ra)
# 3094 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv422)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv423 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv424)) : 'freshtv426)

and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3108 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_bpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_bpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv409) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_bpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv407) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ba : 'tv_bpatom) : 'tv_bpatom) = _v in
    ((let _v : 'tv_patom = 
# 314 "specParser.mly"
                  (Predicate.Base ba)
# 3128 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv408)) : 'freshtv410)

and _menhir_reduce24 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3135 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3141 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_elem = 
# 224 "specParser.mly"
            (Var(Var.fromString i))
# 3146 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce32 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3153 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3159 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_instexpr = 
# 182 "specParser.mly"
                (RInst { sargs = empty (); 
                targs = empty(); args = empty (); 
                rel = RelId.fromString i})
# 3166 "specParser.ml"
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
        let (_menhir_stack : 'freshtv395 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv389 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34) : 'freshtv390)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv391 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
            let _v : 'tv_elemseq = 
# 218 "specParser.mly"
                  ([el])
# 3218 "specParser.ml"
             in
            _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv392)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv393 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv394)) : 'freshtv396)
    | MenhirState215 | MenhirState189 | MenhirState193 | MenhirState185 | MenhirState114 | MenhirState116 | MenhirState146 | MenhirState149 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState167 | MenhirState163 | MenhirState161 | MenhirState159 | MenhirState157 | MenhirState155 | MenhirState150 | MenhirState88 | MenhirState91 | MenhirState71 | MenhirState20 | MenhirState65 | MenhirState63 | MenhirState61 | MenhirState59 | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv397 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        (_menhir_reduce67 _menhir_env (Obj.magic _menhir_stack) : 'freshtv398)
    | MenhirState117 | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv405 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv401 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv399 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (el : 'tv_elem)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_ratom = 
# 207 "specParser.mly"
                              (T[el])
# 3250 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv400)) : 'freshtv402)
        | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | SUBSET | SUBSETEQ | UNION ->
            _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv403 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv404)) : 'freshtv406)
    | _ ->
        _menhir_fail ()

and _menhir_run137 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv385 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 3277 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv381 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3288 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState139
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState139
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139) : 'freshtv382)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv383 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3310 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv384)) : 'freshtv386)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv387 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv388)

and _menhir_run107 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3325 "specParser.ml"
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
        let (_menhir_stack : ('freshtv335 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv333 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (t : 'tv_tyd)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_tyd = 
# 282 "specParser.mly"
             (TyD.makeTRef t )
# 3346 "specParser.ml"
         in
        _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv334)) : 'freshtv336)
    | MenhirState112 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv341 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3354 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv337 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3364 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState114
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114) : 'freshtv338)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv339 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3402 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)) : 'freshtv342)
    | MenhirState139 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv359 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3411 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv355 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3421 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv353 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3428 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), (v : (
# 60 "specParser.mly"
        (string)
# 3433 "specParser.ml"
            ))), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartybind = 
# 348 "specParser.mly"
   ((v, ty))
# 3441 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv351) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_vartybind) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv349 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | COMMA ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv343 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LPAREN ->
                    _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState143
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143) : 'freshtv344)
            | DOT ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv345 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (vty : 'tv_vartybind)) = _menhir_stack in
                let _v : 'tv_tybindseq = 
# 344 "specParser.mly"
                          ([vty])
# 3472 "specParser.ml"
                 in
                _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv346)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv347 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv348)) : 'freshtv350)) : 'freshtv352)) : 'freshtv354)) : 'freshtv356)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv357 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3489 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv358)) : 'freshtv360)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv369 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv361 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185) : 'freshtv362)
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv365 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv363 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 287 "specParser.mly"
                              (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, 
                Predicate.truee()))
# 3545 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv364)) : 'freshtv366)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv367 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv368)) : 'freshtv370)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv375 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3560 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv371 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3570 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193) : 'freshtv372)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((('freshtv373 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3608 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv374)) : 'freshtv376)
    | MenhirState220 | MenhirState211 | MenhirState102 | MenhirState109 | MenhirState206 | MenhirState199 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv379 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv377 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ty : 'tv_tyd)) = _menhir_stack in
        let _v : 'tv_basety = 
# 284 "specParser.mly"
                (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty,
                Predicate.truee()))
# 3623 "specParser.ml"
         in
        _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv378)) : 'freshtv380)
    | _ ->
        _menhir_fail ()

and _menhir_reduce94 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3632 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (
# 60 "specParser.mly"
        (string)
# 3638 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_tyd = 
# 280 "specParser.mly"
            (TyD.fromString t)
# 3643 "specParser.ml"
     in
    _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3650 "specParser.ml"
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
        let (_menhir_stack : 'freshtv331 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3664 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3669 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_params = 
# 158 "specParser.mly"
                ([RelId.fromString i])
# 3674 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv332)
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
        let (_menhir_stack : 'freshtv327) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 3694 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv319) = Obj.magic _menhir_stack in
            let (_v : (
# 60 "specParser.mly"
        (string)
# 3706 "specParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv317) = Obj.magic _menhir_stack in
            let ((i : (
# 60 "specParser.mly"
        (string)
# 3714 "specParser.ml"
            )) : (
# 60 "specParser.mly"
        (string)
# 3718 "specParser.ml"
            )) = _v in
            ((let _v : 'tv_conargs = 
# 176 "specParser.mly"
               (Vector.fromList [Var.fromString i])
# 3723 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv318)) : 'freshtv320)
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv321) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10) : 'freshtv322)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv323 * (
# 60 "specParser.mly"
        (string)
# 3743 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, (i : (
# 60 "specParser.mly"
        (string)
# 3748 "specParser.ml"
            ))) = _menhir_stack in
            let _v : 'tv_conpat = 
# 173 "specParser.mly"
               ((Con.fromString i, None))
# 3753 "specParser.ml"
             in
            _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv324)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv325 * (
# 60 "specParser.mly"
        (string)
# 3763 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv326)) : 'freshtv328)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv329 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv330)

and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3777 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQUALOP ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv313 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3789 "specParser.ml"
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
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71) : 'freshtv314)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv315 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3817 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)

and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3825 "specParser.ml"
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
        let (_menhir_stack : 'freshtv309 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 3882 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv305 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3893 "specParser.ml"
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
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv306)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv307 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 3923 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)) : 'freshtv310)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv311 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv312)

and _menhir_run96 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 3938 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv299 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3950 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97) : 'freshtv300)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv301 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3966 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 60 "specParser.mly"
        (string)
# 3971 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_paramseq = 
# 161 "specParser.mly"
                    ([RelId.fromString i])
# 3976 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv302)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv303 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 3986 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)

and _menhir_run115 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONJ | DISJ | IFF | IMPL | RCURLY | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv295 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 311 "specParser.mly"
             (Predicate.truee())
# 4005 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv296)
    | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | RPAREN | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv297 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
    | LBRACE ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | LPAREN ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | NOT ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | TRUE ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | EXISTS ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
    | LAMBDA ->
        _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | LBRACE ->
        _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | LPAREN ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | NOT ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | TRUE ->
        _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState117

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv291 * _menhir_state) = Obj.magic _menhir_stack in
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
            let (_menhir_stack : ('freshtv289 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState24 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv285 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv283 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 202 "specParser.mly"
                                    (T(Vector.fromList []))
# 4120 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv284)) : 'freshtv286)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv287 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv288)) : 'freshtv290)
        | TRUE ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState24
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24) : 'freshtv292)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv293 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv294)

and _menhir_run118 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv279 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4156 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv255 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4167 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv219 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4177 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv215 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4187 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv213 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4194 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4199 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 322 "specParser.mly"
                                           (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, false))
# 4209 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv214)) : 'freshtv216)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv217 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4219 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv218)) : 'freshtv220)
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv227 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4228 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 4233 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv223 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4244 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4248 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv221 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4255 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4259 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4264 "specParser.ml"
                    ))), (i2 : (
# 60 "specParser.mly"
        (string)
# 4268 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 318 "specParser.mly"
                                           (Predicate.BasePredicate.varEq 
                      (Var.fromString i1, Var.fromString i2))
# 4277 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv222)) : 'freshtv224)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv225 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4287 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4291 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv226)) : 'freshtv228)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv235 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4300 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
       (int)
# 4305 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv231 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4316 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4320 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv229 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4327 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4331 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4336 "specParser.ml"
                    ))), (rhs : (
# 61 "specParser.mly"
       (int)
# 4340 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 328 "specParser.mly"
                                              (Predicate.BasePredicate.varIntEq 
                      (Var.fromString i1, rhs))
# 4349 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv230)) : 'freshtv232)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv233 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4359 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4363 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv234)) : 'freshtv236)
            | STRCONST _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv243 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4372 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (string)
# 4377 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv239 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4388 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4392 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv237 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4399 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4403 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4408 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (string)
# 4412 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 330 "specParser.mly"
                                                   (
       				let rhstrimmed = String.sub (rhs) (1) ((String.length rhs) - 2) in 
       				Predicate.BasePredicate.varStrEq 
                      (Var.fromString i1, rhstrimmed))
# 4423 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv238)) : 'freshtv240)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv241 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4433 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (string)
# 4437 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv242)) : 'freshtv244)
            | TRUE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv251 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4446 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv247 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4456 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv245 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4463 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4468 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 320 "specParser.mly"
                                          (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, true))
# 4478 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv246)) : 'freshtv248)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv249 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4488 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv250)) : 'freshtv252)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv253 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4499 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv254)) : 'freshtv256)
        | GREATERTHAN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv275 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4508 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv263 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4518 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 60 "specParser.mly"
        (string)
# 4523 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv259 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4534 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4538 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv257 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4545 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4549 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4554 "specParser.ml"
                    ))), (i2 : (
# 60 "specParser.mly"
        (string)
# 4558 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 324 "specParser.mly"
                                                (Predicate.BasePredicate.varGt 
                      (Var.fromString i1, Var.fromString i2))
# 4567 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv258)) : 'freshtv260)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv261 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4577 "specParser.ml"
                    ))) * (
# 60 "specParser.mly"
        (string)
# 4581 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv262)) : 'freshtv264)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv271 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4590 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
       (int)
# 4595 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv267 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4606 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4610 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv265 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4617 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4621 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 60 "specParser.mly"
        (string)
# 4626 "specParser.ml"
                    ))), (rhs : (
# 61 "specParser.mly"
       (int)
# 4630 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 326 "specParser.mly"
                                                  (Predicate.BasePredicate.varIntGt 
                      (Var.fromString i1, rhs))
# 4639 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv266)) : 'freshtv268)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv269 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4649 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
       (int)
# 4653 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv270)) : 'freshtv272)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv273 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4664 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv274)) : 'freshtv276)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv277 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4675 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv278)) : 'freshtv280)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv281 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv282)

and _menhir_run136 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
       (int)
# 4703 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv211) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ii : (
# 61 "specParser.mly"
       (int)
# 4713 "specParser.ml"
    )) : (
# 61 "specParser.mly"
       (int)
# 4717 "specParser.ml"
    )) = _v in
    ((let _v : 'tv_elem = 
# 221 "specParser.mly"
              (Int(ii))
# 4722 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv212)

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 4729 "specParser.ml"
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
    let (_menhir_stack : 'freshtv209) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let f = () in
    let _v : 'tv_elem = 
# 223 "specParser.mly"
               (Bool(false))
# 4757 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv210)

and _menhir_run147 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState147
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147

and _menhir_run150 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState150
    | ID _v ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
    | INT _v ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState150 _v
    | LCURLY ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState150
    | LPAREN ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState150
    | TRUE ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState150
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState150

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
        _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState109 _v
    | LBRACE ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | LCURLY ->
        _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | LPAREN ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | REF ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState109
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState109

and _menhir_run110 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv207 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState110 in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4848 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv203 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4859 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState112 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState112
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState112
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState112) : 'freshtv204)
        | PIPE | RCURLY ->
            _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv205 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4883 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)) : 'freshtv208)
    | LBRACE ->
        _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | REF ->
        _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState110
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110

and _menhir_run104 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv199 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 60 "specParser.mly"
        (string)
# 4908 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv195 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4919 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv193 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4926 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), (t : (
# 60 "specParser.mly"
        (string)
# 4931 "specParser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_tyd = 
# 281 "specParser.mly"
                      (TyD.makeTList (TyD.fromString t))
# 4938 "specParser.ml"
             in
            _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv194)) : 'freshtv196)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv197 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 4948 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)) : 'freshtv200)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv201 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)

and _menhir_run188 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 4963 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LCURLY ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv189 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 4975 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGLEFT ->
            _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | EXISTS ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | FALSE ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | ID _v ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
        | INT _v ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
        | LAMBDA ->
            _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | LBRACE ->
            _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | LCURLY ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | LPAREN ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | NOT ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | TRUE ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState189
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState189) : 'freshtv190)
    | ARROW | COMMA | RPAREN | SEMICOLON ->
        _menhir_reduce94 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv191 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5015 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv192)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState229 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv55 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv56)
    | MenhirState227 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv57 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)
    | MenhirState225 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv59 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv60)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv61 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)
    | MenhirState220 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv63 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5048 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState215 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv65 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5057 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState211 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5066 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv69 * _menhir_state * 'tv_varty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState199 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv73 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5085 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv75 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5094 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState189 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv77 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5103 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv79 * _menhir_state) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv83 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv85 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv87 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState163 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv89 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv91 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState150 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv99 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv101 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState147 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv103 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState146 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv105 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState143 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv107 * _menhir_state * 'tv_vartybind)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState139 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv109 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5187 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState136 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv113 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState114 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv117 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5211 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState112 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv119 * _menhir_state) * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5220 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv121 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState109 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv124)
    | MenhirState103 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv125 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv127 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 60 "specParser.mly"
        (string)
# 5244 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState97 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv129 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5253 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv131 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv133 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5267 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv135 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5276 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv137 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5285 "specParser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState80 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv139 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5294 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv141 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState73 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv143 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5308 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState71 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv145 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5317 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState65 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv147 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState63 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv149 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState61 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv151 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv153 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * _menhir_state * 'tv_funparam)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv157 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv159 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState41 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv161 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv163 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5366 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv165 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState36 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv167 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5380 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState34 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * _menhir_state * 'tv_elem)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv171 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState22 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv173 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv175 * _menhir_state) * 'tv_conpat))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv177 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5409 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState10 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv180)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv181 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5422 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState4 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv183 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5431 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv185 * _menhir_state)) * (
# 60 "specParser.mly"
        (string)
# 5440 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv188)

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
# 5461 "specParser.ml"
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
# 5472 "specParser.ml"
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
# 5505 "specParser.ml"
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
# 5550 "specParser.ml"
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
# 5561 "specParser.ml"
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
# 5591 "specParser.ml"
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

and _menhir_run210 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 60 "specParser.mly"
        (string)
# 5626 "specParser.ml"
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
# 5638 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState211 _v
        | LBRACE ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | LCURLY ->
            _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | LPAREN ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | REF ->
            _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState211
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState211) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29 * _menhir_state * (
# 60 "specParser.mly"
        (string)
# 5664 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run213 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
# 5681 "specParser.ml"
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
# 5692 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | EXISTS ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | FALSE ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | ID _v ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
            | INT _v ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState215 _v
            | LAMBDA ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | LBRACE ->
                _menhir_run118 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | LCURLY ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | LPAREN ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | NOT ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | TRUE ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState215
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState215) : 'freshtv20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv21 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5730 "specParser.ml"
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
# 5745 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5754 "specParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv15) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5762 "specParser.ml"
    )) : (
# 75 "specParser.mly"
       (SpecLang.RelSpec.t)
# 5766 "specParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv16)) : 'freshtv18)

and _menhir_run218 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
# 5782 "specParser.ml"
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
# 5793 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run188 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
            | LBRACE ->
                _menhir_run104 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | LCURLY ->
                _menhir_run110 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | LPAREN ->
                _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | REF ->
                _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState220
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220) : 'freshtv8)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv9 * _menhir_state) * (
# 60 "specParser.mly"
        (string)
# 5819 "specParser.ml"
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
# 5846 "specParser.ml"
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
        _menhir_run218 _menhir_env (Obj.magic _menhir_stack) MenhirState0
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
# 5878 "specParser.ml"
        ) = 
# 79 "specParser.mly"
              (RelSpec.mk_empty_relspec ())
# 5882 "specParser.ml"
         in
        _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2)) : 'freshtv4)
    | FORMULA ->
        _menhir_run213 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ID _v ->
        _menhir_run210 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
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
  

# 5903 "specParser.ml"
