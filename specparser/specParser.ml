
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | UNION
    | UINST
    | TYPE
    | TRUE
    | SUBSETEQ
    | SUBSET
    | STRCONST of (
# 63 "specParser.mly"
       (string)
# 17 "specParser.ml"
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
    | OF
    | NUMEQ
    | NOT
    | MINUS
    | LPAREN
    | LESSTHAN
    | LCURLY
    | LBRACE
    | LAMBDA
    | INT of (
# 62 "specParser.mly"
       (int)
# 44 "specParser.ml"
  )
    | IMPL
    | IFF
    | ID of (
# 61 "specParser.mly"
        (string)
# 51 "specParser.ml"
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
  | MenhirState252
  | MenhirState250
  | MenhirState248
  | MenhirState246
  | MenhirState244
  | MenhirState241
  | MenhirState236
  | MenhirState232
  | MenhirState228
  | MenhirState226
  | MenhirState217
  | MenhirState210
  | MenhirState208
  | MenhirState204
  | MenhirState200
  | MenhirState189
  | MenhirState187
  | MenhirState185
  | MenhirState182
  | MenhirState178
  | MenhirState176
  | MenhirState174
  | MenhirState172
  | MenhirState170
  | MenhirState165
  | MenhirState164
  | MenhirState162
  | MenhirState161
  | MenhirState158
  | MenhirState154
  | MenhirState151
  | MenhirState132
  | MenhirState131
  | MenhirState129
  | MenhirState127
  | MenhirState125
  | MenhirState124
  | MenhirState122
  | MenhirState116
  | MenhirState115
  | MenhirState110
  | MenhirState108
  | MenhirState104
  | MenhirState101
  | MenhirState94
  | MenhirState93
  | MenhirState91
  | MenhirState86
  | MenhirState84
  | MenhirState78
  | MenhirState76
  | MenhirState74
  | MenhirState72
  | MenhirState68
  | MenhirState62
  | MenhirState59
  | MenhirState54
  | MenhirState51
  | MenhirState50
  | MenhirState49
  | MenhirState47
  | MenhirState37
  | MenhirState35
  | MenhirState33
  | MenhirState25
  | MenhirState23
  | MenhirState20
  | MenhirState17
  | MenhirState16
  | MenhirState12
  | MenhirState7
  | MenhirState5
  | MenhirState3
  | MenhirState0

# 1 "specParser.mly"
  
open SpecLang
open RelLang
open Printf
module TypeSpec = SpecLang.RelSpec.TypeSpec
module RefTy = SpecLang.RefinementType
module Formula = SpecLang.RelSpec.Formula
let defaultCons = SpecLang.Tycon.default
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


# 185 "specParser.ml"

let rec _menhir_goto_decsandtys : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decsandtys -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv969 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv967 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_predspec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 129 "specParser.mly"
    (
		 match d with 
		  RelSpec.T {typedefs;preds;reldecs; primdecs; typespecs} -> 
                    RelSpec.T {typedefs=typedefs;preds= p :: preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = typespecs}

		)
# 210 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv968)) : 'freshtv970)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv973 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv971 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_primdec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 111 "specParser.mly"
                (match d with 
                  RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) -> 
                    RelSpec.T {
                              typedefs=typedefs;
                              preds = preds;
		    		                  primdecs = p :: primdecs; 
                              reldecs=reldecs; 
                              typespecs = typespecs}
                )
# 235 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv972)) : 'freshtv974)
    | MenhirState248 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv977 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv975 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (r : 'tv_reldec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 101 "specParser.mly"
                  (
                    match d with 
                    RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) -> 
                    RelSpec.T {typedefs=typedefs;
                              preds = preds;
		    		                  reldecs = r ::reldecs; 
                              primdecs = primdecs;
                            typespecs = typespecs}
                          )
# 260 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv976)) : 'freshtv978)
    | MenhirState246 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv981 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv979 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (td : 'tv_typedef)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 88 "specParser.mly"
                  (
                    match d with 
                          RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) ->    
                              RelSpec.T {
                              typedefs = td :: typedefs;
                              preds = preds;
                              reldecs = reldecs; 
                              primdecs = primdecs;
                              typespecs = typespecs}
                  )
# 286 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv980)) : 'freshtv982)
    | MenhirState244 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv985 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv983 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (t : 'tv_typespec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 122 "specParser.mly"
                (
                  match d with
                 RelSpec.T {typedefs;preds;reldecs; primdecs;typespecs} -> 
                    RelSpec.T {typedefs=typedefs;preds= preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = t :: typespecs}
                )
# 308 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv984)) : 'freshtv986)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv999) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv997) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let _v : 'tv_spec = 
# 83 "specParser.mly"
                   (
                  d)
# 324 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv995) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_spec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv993 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv989 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv987 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (s : 'tv_spec)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 346 "specParser.ml"
            ) = 
# 79 "specParser.mly"
               (s)
# 350 "specParser.ml"
             in
            _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv988)) : 'freshtv990)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv991 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv992)) : 'freshtv994)) : 'freshtv996)) : 'freshtv998)) : 'freshtv1000)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typespec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typespec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv965 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv961 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | FORMULA ->
            _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | ID _v ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState244 _v
        | LPAREN ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | PRIMITIVE ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | RELATION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | TYPE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | EOF ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack) MenhirState244
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState244) : 'freshtv962)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv963 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv964)) : 'freshtv966)

and _menhir_goto_vartyseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState122 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv955 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv951 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv945 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_vartyatom = 
# 293 "specParser.mly"
                                  (
                match vas with
                        [x] -> x 
                        | _ -> (genVar (), RefTy.Sigma vas)
                  )
# 434 "specParser.ml"
                 in
                _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv946)
            | COMMA | LCURLY | RPAREN | SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv947 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_reftyatom = 
# 285 "specParser.mly"
                                        (RefTy.Sigma vas)
# 446 "specParser.ml"
                 in
                _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv948)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv949 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv950)) : 'freshtv952)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv953 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv954)) : 'freshtv956)
    | MenhirState226 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv959 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv957 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_varty)), _, (vts : 'tv_vartyseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_vartyseq = 
# 300 "specParser.mly"
                                       (vt :: vts)
# 473 "specParser.ml"
         in
        _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv958)) : 'freshtv960)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv935 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 487 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv933 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 495 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 502 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_reldec = 
# 169 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = p;
                mapp = patmseq})
# 512 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv934)) : 'freshtv936)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv939 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv937 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((pms : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatchseq = 
# 189 "specParser.mly"
                                               (pm :: pms)
# 529 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv938)) : 'freshtv940)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv943 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 537 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv941 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 545 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 552 "specParser.ml"
        ))) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_reldec = 
# 165 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = empty ();
                mapp = patmseq})
# 560 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv942)) : 'freshtv944)
    | _ ->
        _menhir_fail ()

and _menhir_goto_funparams : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_funparams -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv927 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv923 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv921 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (ps : 'tv_funparams)) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_ratom = 
# 241 "specParser.mly"
                                               (MultiR (ie, ps))
# 588 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv922)) : 'freshtv924)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv925 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv926)) : 'freshtv928)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv931 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv929 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (p : 'tv_funparam)), _, (ps : 'tv_funparams)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_funparams = 
# 251 "specParser.mly"
                                 (p::ps)
# 608 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv930)) : 'freshtv932)
    | _ ->
        _menhir_fail ()

and _menhir_goto_reftyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reftyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv919) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_reftyatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv917) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((rta : 'tv_reftyatom) : 'tv_reftyatom) = _v in
    ((let _v : 'tv_refty = 
# 280 "specParser.mly"
                      ( rta)
# 627 "specParser.ml"
     in
    _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv918)) : 'freshtv920)

and _menhir_reduce21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_decsandtys = 
# 136 "specParser.mly"
                (RelSpec.T {
                    typedefs=[];
  			            preds = Vector.new0 ();
  			            reldecs = [];
                    primdecs = Vector.new0 ();
                    typespecs = []})
# 641 "specParser.ml"
     in
    _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_refty : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_refty -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv877 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv875 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vrta : 'tv_vartyatom)), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_refty = 
# 281 "specParser.mly"
                                      ( RefTy.Arrow (((fst (vrta)) , (snd vrta)), rt))
# 659 "specParser.ml"
         in
        _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv876)) : 'freshtv878)
    | MenhirState208 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv883 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 667 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 671 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv879 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 681 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 685 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState217 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState217
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState217) : 'freshtv880)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv881 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 723 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 727 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv882)) : 'freshtv884)
    | MenhirState228 | MenhirState124 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv903 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 736 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv901 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 742 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 747 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_varty = 
# 303 "specParser.mly"
  (((Var.fromString i), rt))
# 753 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv899) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_varty) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv897 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv891 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv889) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState226 in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 778 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv885 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 789 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
                    | LBRACE ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState228
                    | LCURLY ->
                        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState228
                    | LPAREN ->
                        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState228
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState228
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228) : 'freshtv886)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv887 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 815 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv888)) : 'freshtv890)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState226) : 'freshtv892)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv893 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (vt : 'tv_varty)) = _menhir_stack in
            let _v : 'tv_vartyseq = 
# 299 "specParser.mly"
                    ([vt])
# 830 "specParser.ml"
             in
            _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv894)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv895 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv896)) : 'freshtv898)) : 'freshtv900)) : 'freshtv902)) : 'freshtv904)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv907 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 845 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv905 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 851 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, (ps : 'tv_paramseq)), (i : (
# 61 "specParser.mly"
        (string)
# 856 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 274 "specParser.mly"
                                                         (
                                  TypeSpec.T {isAssume = false;
                                name = Var.fromString i;
                                params = Vector.fromList ps; 
                                refty = rt})
# 868 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv906)) : 'freshtv908)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv911 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 876 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv909 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 882 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 887 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typespec = 
# 270 "specParser.mly"
                               (      TypeSpec.T {isAssume = false;
                                       name = (Var.fromString i);
                                       params = empty ();
                                       refty = rt})
# 896 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv910)) : 'freshtv912)
    | MenhirState241 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv915 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 904 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv913 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 910 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 915 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 265 "specParser.mly"
                                      (
                                          TypeSpec.T {isAssume = true;
                                              name = (Var.fromString i);
                                              params = empty ();
                                              refty = rt})
# 926 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv914)) : 'freshtv916)
    | _ ->
        _menhir_fail ()

and _menhir_run170 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState170
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState170
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState170
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState170
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170

and _menhir_run172 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState172
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState172
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState172
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState172
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172

and _menhir_run174 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState174
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState174
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState174
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState174
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174

and _menhir_run176 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176

and _menhir_run178 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState178 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState178 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState178

and _menhir_goto_rpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv873) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_rpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv871) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ra : 'tv_rpatom) : 'tv_rpatom) = _v in
    ((let _v : 'tv_patom = 
# 342 "specParser.mly"
                  (Predicate.Rel ra)
# 1055 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv872)) : 'freshtv874)

and _menhir_goto_primdef : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_primdef -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv857 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1067 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv855 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1075 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 1082 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_primdef = 
# 160 "specParser.mly"
                                    (PrimitiveRelation.Nary
                (Var.fromString i, p))
# 1090 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv856)) : 'freshtv858)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv869 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 1098 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv867 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 1106 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 1113 "specParser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_primdec = 
# 155 "specParser.mly"
                                                    (PrimitiveRelation.T
                    {id=RelId.fromString i; 
                    def=PrimitiveRelation.alphaRename p})
# 1123 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv865) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv863 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv859 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | FORMULA ->
                _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | ID _v ->
                _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState250 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | EOF ->
                _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack) MenhirState250
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState250) : 'freshtv860)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv861 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv862)) : 'freshtv864)) : 'freshtv866)) : 'freshtv868)) : 'freshtv870)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv853 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv847 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
        | LPAREN ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState91
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv848)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv849 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _v : 'tv_patmatchseq = 
# 190 "specParser.mly"
                          ([pm])
# 1200 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv850)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv851 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv852)) : 'freshtv854)

and _menhir_run57 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv845 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
    ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _v : 'tv_ratom = 
# 243 "specParser.mly"
                               (re)
# 1222 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv846)

and _menhir_goto_reldec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reldec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv843 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv839 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | FORMULA ->
            _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | ID _v ->
            _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState248 _v
        | LPAREN ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | PRIMITIVE ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | RELATION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | TYPE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | EOF ->
            _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack) MenhirState248
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState248) : 'freshtv840)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv841 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv842)) : 'freshtv844)

and _menhir_reduce28 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1271 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1277 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_funparam = 
# 253 "specParser.mly"
                (Var.fromString i)
# 1282 "specParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv837) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_funparam) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv835 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv829 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv827) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState68 in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 1307 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce28 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv828)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68) : 'freshtv830)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv831 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_funparam)) = _menhir_stack in
        let _v : 'tv_funparams = 
# 250 "specParser.mly"
                       ([p])
# 1323 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv832)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv833 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv834)) : 'freshtv836)) : 'freshtv838)

and _menhir_goto_instexprs : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexprs -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState49 | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv821 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1342 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv819 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1350 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1357 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_instexpr = 
# 222 "specParser.mly"
                              (RInst {
                sargs = empty (); targs = empty();
                args = Vector.fromList ies;
                rel = RelId.fromString i})
# 1365 "specParser.ml"
         in
        _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv820)) : 'freshtv822)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv825 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv823 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_instexprs = 
# 228 "specParser.mly"
                                                    (ie :: ies)
# 1383 "specParser.ml"
         in
        _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv824)) : 'freshtv826)
    | _ ->
        _menhir_fail ()

and _menhir_goto_vartyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv817 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv813 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState210 _v
        | LBRACE ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LCURLY ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LPAREN ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | REF ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210) : 'freshtv814)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv815 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv816)) : 'freshtv818)

and _menhir_reduce72 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (bt : 'tv_basety)) = _menhir_stack in
    let _v : 'tv_reftyatom = 
# 284 "specParser.mly"
                      ( bt)
# 1431 "specParser.ml"
     in
    _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_tpatmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tpatmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv807 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1443 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv805 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1451 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((cons : 'tv_tpatmatchseq) : 'tv_tpatmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (tn : (
# 61 "specParser.mly"
        (string)
# 1458 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typedef = 
# 145 "specParser.mly"
                (Algebraic.TD {
                    typename = Var.fromString tn;   
                    constructors = cons    
                    }
                )
# 1469 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv803) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typedef) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv801 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv797 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | FORMULA ->
                _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | ID _v ->
                _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState246 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | EOF ->
                _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack) MenhirState246
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState246) : 'freshtv798)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv799 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv800)) : 'freshtv802)) : 'freshtv804)) : 'freshtv806)) : 'freshtv808)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv811 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv809 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((tpms : 'tv_tpatmatchseq) : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (tpm : 'tv_tpatmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tpatmatchseq = 
# 193 "specParser.mly"
                                                    (tpm :: tpms)
# 1528 "specParser.ml"
         in
        _menhir_goto_tpatmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv810)) : 'freshtv812)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typenameseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typenameseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv791 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1542 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typenameseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv789 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1550 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((tnseq : 'tv_typenameseq) : 'tv_typenameseq) = _v in
        ((let (_menhir_stack, _menhir_s, (typename : (
# 61 "specParser.mly"
        (string)
# 1557 "specParser.ml"
        ))) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typenameseq = 
# 202 "specParser.mly"
                                                   (TyD.fromString (typename):: tnseq)
# 1563 "specParser.ml"
         in
        _menhir_goto_typenameseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv790)) : 'freshtv792)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv795 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1571 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typenameseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv793 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1579 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((typeargs : 'tv_typenameseq) : 'tv_typenameseq) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1586 "specParser.ml"
        ))) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tpatmatch = 
# 200 "specParser.mly"
                                        (Algebraic.Const {name=i;args=typeargs})
# 1592 "specParser.ml"
         in
        _menhir_goto_tpatmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv794)) : 'freshtv796)
    | _ ->
        _menhir_fail ()

and _menhir_goto_idseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_idseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv779 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1607 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv777 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1613 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1618 "specParser.ml"
        ))), _, (is : 'tv_idseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_idseq = 
# 217 "specParser.mly"
                            ((Var.fromString i)::is)
# 1624 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv778)) : 'freshtv780)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv787) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv783) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv781) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, (is : 'tv_idseq)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_conargs = 
# 214 "specParser.mly"
                                 (Vector.fromList is)
# 1645 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv782)) : 'freshtv784)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv785) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv786)) : 'freshtv788)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pred : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_pred -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv691 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv689 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 336 "specParser.mly"
                                           (Predicate.Exists (binds, pr))
# 1673 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv690)) : 'freshtv692)
    | MenhirState182 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv695 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv693 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 331 "specParser.mly"
                              (Predicate.If (pa,pr))
# 1686 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv694)) : 'freshtv696)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv699 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv697 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 332 "specParser.mly"
                             (Predicate.Iff (pa,pr))
# 1699 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv698)) : 'freshtv700)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv703 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv701 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 334 "specParser.mly"
                              (Predicate.Disj (pa,pr))
# 1712 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv702)) : 'freshtv704)
    | MenhirState189 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv707 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv705 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 333 "specParser.mly"
                              (Predicate.Conj (pa,pr))
# 1725 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv706)) : 'freshtv708)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv711 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv709 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 335 "specParser.mly"
                                           (Predicate.Forall (binds, pr) )
# 1739 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv710)) : 'freshtv712)
    | MenhirState132 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv719 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv715 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv713 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (pr : 'tv_pred)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_patom = 
# 340 "specParser.mly"
                              (pr)
# 1760 "specParser.ml"
             in
            _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv714)) : 'freshtv716)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv717 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv718)) : 'freshtv720)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv727 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1775 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv723 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1785 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv721 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1792 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), _, (v : (
# 61 "specParser.mly"
        (string)
# 1797 "specParser.ml"
            ))), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 318 "specParser.mly"
                                                       (RefinementType.Base ((Var.fromString v), 
                ty, pr))
# 1807 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv722)) : 'freshtv724)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv725 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1817 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv726)) : 'freshtv728)
    | MenhirState200 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv735 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv731 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv729 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 316 "specParser.mly"
                                           (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, pr))
# 1841 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv730)) : 'freshtv732)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv733 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv734)) : 'freshtv736)
    | MenhirState204 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv749 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1856 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv745 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1866 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv741 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1876 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 1881 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv737 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1892 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1896 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState208 _v
                    | LBRACE ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState208
                    | LCURLY ->
                        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState208
                    | LPAREN ->
                        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState208
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState208
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState208) : 'freshtv738)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv739 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1922 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1926 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv740)) : 'freshtv742)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv743 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1937 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv744)) : 'freshtv746)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv747 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1948 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv748)) : 'freshtv750)
    | MenhirState217 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((('freshtv763 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1957 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1961 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv759 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1971 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1975 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv757 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1982 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1986 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, (ef : (
# 61 "specParser.mly"
        (string)
# 1991 "specParser.ml"
            ))), _, (pre : 'tv_pred)), (resvar : (
# 61 "specParser.mly"
        (string)
# 1995 "specParser.ml"
            ))), _, (resty : 'tv_refty)), _, (post : 'tv_pred)) = _menhir_stack in
            let _10 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_mty = 
# 321 "specParser.mly"
                                                                                         (RefTy.MArrow (Effect.fromString ef, pre, (resvar, resty), post))
# 2005 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv755) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv753) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv751) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((mtype : 'tv_mty) : 'tv_mty) = _v in
            ((let _v : 'tv_refty = 
# 282 "specParser.mly"
                  (mtype)
# 2022 "specParser.ml"
             in
            _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv752)) : 'freshtv754)) : 'freshtv756)) : 'freshtv758)) : 'freshtv760)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv761 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2032 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 2036 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv762)) : 'freshtv764)
    | MenhirState236 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv775 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2045 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv773 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2051 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2056 "specParser.ml"
        ))), _, (p : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_predspec = 
# 153 "specParser.mly"
                                       (Formula.Form{name=Var.fromString i;pred = p})
# 2063 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv771) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_predspec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv769 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv765 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | FORMULA ->
                _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | ID _v ->
                _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState252 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | EOF ->
                _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState252) : 'freshtv766)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv767 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv768)) : 'freshtv770)) : 'freshtv772)) : 'freshtv774)) : 'freshtv776)
    | _ ->
        _menhir_fail ()

and _menhir_goto_rexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv619 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv617 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv618)) : 'freshtv620)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv623 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv621 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 232 "specParser.mly"
                                (U(ra,re))
# 2140 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv622)) : 'freshtv624)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv627 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv625 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 234 "specParser.mly"
                               (ADD(ra,re))
# 2153 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv626)) : 'freshtv628)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv631 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv629 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 233 "specParser.mly"
                                (D(ra,re))
# 2166 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv630)) : 'freshtv632)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv635 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv633 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 231 "specParser.mly"
                                   (X(ra,re))
# 2179 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv634)) : 'freshtv636)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv639 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv637 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 235 "specParser.mly"
                                  (SUBS(ra,re))
# 2192 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv638)) : 'freshtv640)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv643 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv641 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (cp : 'tv_conpat)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_patmatch = 
# 206 "specParser.mly"
              (match cp with (c,vlop) -> (c, vlop, Expr re))
# 2207 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv642)) : 'freshtv644)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv647 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2215 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv645 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2221 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 2226 "specParser.ml"
        ))), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatch = 
# 207 "specParser.mly"
                                 ((Tycon.fromString i, None, Expr re))
# 2232 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv646)) : 'freshtv648)
    | MenhirState101 | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv651 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv649 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (re : 'tv_rexpr)) = _menhir_stack in
        let _v : 'tv_primdef = 
# 159 "specParser.mly"
                   (PrimitiveRelation.Nullary re)
# 2244 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv650)) : 'freshtv652)
    | MenhirState165 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv659 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGRIGHT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv655 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv653 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_rpatom = 
# 363 "specParser.mly"
                                   (Predicate.RelPredicate.Q (re))
# 2265 "specParser.ml"
             in
            _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv654)) : 'freshtv656)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv657 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv658)) : 'freshtv660)
    | MenhirState236 | MenhirState217 | MenhirState204 | MenhirState200 | MenhirState129 | MenhirState131 | MenhirState161 | MenhirState189 | MenhirState187 | MenhirState185 | MenhirState182 | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv663 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run178 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run176 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run174 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run172 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv661 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv662)) : 'freshtv664)
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv667 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv665 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 366 "specParser.mly"
                                      (Predicate.RelPredicate.SubEq(re1,re2))
# 2308 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv666)) : 'freshtv668)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv671 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv669 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 365 "specParser.mly"
                                    (Predicate.RelPredicate.Sub(re1,re2))
# 2321 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv670)) : 'freshtv672)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv675 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv673 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 367 "specParser.mly"
                                   (Predicate.RelPredicate.NEq(re1, re2) )
# 2334 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv674)) : 'freshtv676)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv679 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv677 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 368 "specParser.mly"
                                         (Predicate.RelPredicate.Grt(re1, re2))
# 2347 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv678)) : 'freshtv680)
    | MenhirState178 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv683 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv681 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 364 "specParser.mly"
                                     (Predicate.RelPredicate.Eq(re1,re2))
# 2360 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv682)) : 'freshtv684)
    | MenhirState132 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv687 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run178 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run176 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run174 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run172 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run170 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv685 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv686)) : 'freshtv688)
    | _ ->
        _menhir_fail ()

and _menhir_goto_instexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv585 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv581 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LBRACE ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | LPAREN | RBRACE | STAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv579 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_instexprs = 
# 227 "specParser.mly"
                                      ([ie])
# 2418 "specParser.ml"
                 in
                _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv580)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54) : 'freshtv582)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv583 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv584)) : 'freshtv586)
    | MenhirState236 | MenhirState204 | MenhirState217 | MenhirState200 | MenhirState129 | MenhirState131 | MenhirState132 | MenhirState161 | MenhirState164 | MenhirState189 | MenhirState187 | MenhirState185 | MenhirState182 | MenhirState178 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState165 | MenhirState101 | MenhirState104 | MenhirState84 | MenhirState33 | MenhirState35 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv599 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv595 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv593 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState62 in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 2451 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RPAREN ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv589 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2462 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv587 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2469 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (i : (
# 61 "specParser.mly"
        (string)
# 2474 "specParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _v : 'tv_ratom = 
# 242 "specParser.mly"
                                       (R (ie, Var.fromString i))
# 2481 "specParser.ml"
                     in
                    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv588)) : 'freshtv590)
                | COMMA ->
                    _menhir_reduce28 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv591 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2493 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv592)) : 'freshtv594)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62) : 'freshtv596)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv597 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv598)) : 'freshtv600)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv607 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2513 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv603 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2523 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv601 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2530 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2535 "specParser.ml"
            ))), _, (p : 'tv_params)), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 178 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = p;
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2548 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv602)) : 'freshtv604)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv605 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2558 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv606)) : 'freshtv608)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv615 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2567 "specParser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv611 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2577 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv609 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2584 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2589 "specParser.ml"
            ))), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 173 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = empty ();
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2600 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv610)) : 'freshtv612)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv613 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2610 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv614)) : 'freshtv616)
    | _ ->
        _menhir_fail ()

and _menhir_reduce68 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
    let _v : 'tv_ratom = 
# 245 "specParser.mly"
                (V (el))
# 2623 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_elemseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elemseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv573 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv569 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv565 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv563 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (els : 'tv_elemseq)) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 240 "specParser.mly"
                                                (T(Vector.fromList els))
# 2657 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv564)) : 'freshtv566)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv567 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv568)) : 'freshtv570)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv571 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv572)) : 'freshtv574)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv577 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv575 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (el : 'tv_elem)), _, (els : 'tv_elemseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_elemseq = 
# 256 "specParser.mly"
                                    (el::els)
# 2684 "specParser.ml"
         in
        _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv576)) : 'freshtv578)
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
    | MenhirState241 | MenhirState232 | MenhirState115 | MenhirState228 | MenhirState208 | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv553 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        (_menhir_reduce72 _menhir_env (Obj.magic _menhir_stack) : 'freshtv554)
    | MenhirState124 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv561 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2708 "specParser.ml"
        ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv557 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2718 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv555 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2725 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (i : (
# 61 "specParser.mly"
        (string)
# 2730 "specParser.ml"
            ))), _, (bt : 'tv_basety)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartyatom = 
# 288 "specParser.mly"
  (
                  match bt with 
                     RefTy.Base (v,_,_) -> ((Var.fromString i),bt)
                       | _ -> raise (Failure "Impossible case of basety")
		)
# 2742 "specParser.ml"
             in
            _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv556)) : 'freshtv558)
        | COMMA ->
            _menhir_reduce72 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv559 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2754 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv560)) : 'freshtv562)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tybindseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tybindseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState158 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv539 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv537 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_vartybind)), _, (vts : 'tv_tybindseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tybindseq = 
# 372 "specParser.mly"
                                            (vt :: vts)
# 2775 "specParser.ml"
         in
        _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv538)) : 'freshtv540)
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv545 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv541 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState161 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState161
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161) : 'freshtv542)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv543 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv544)) : 'freshtv546)
    | MenhirState162 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv551 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv547 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState164
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164) : 'freshtv548)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv549 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv550)) : 'freshtv552)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tpatmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tpatmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv535 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv529 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv530)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv531 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (tpm : 'tv_tpatmatch)) = _menhir_stack in
        let _v : 'tv_tpatmatchseq = 
# 194 "specParser.mly"
                            ([tpm])
# 2898 "specParser.ml"
         in
        _menhir_goto_tpatmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv532)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv533 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv534)) : 'freshtv536)

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 2912 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv523 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2924 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv524)
    | PIPE | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv525 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2940 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (typename : (
# 61 "specParser.mly"
        (string)
# 2945 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_typenameseq = 
# 203 "specParser.mly"
                            ([TyD.fromString (typename)])
# 2950 "specParser.ml"
         in
        _menhir_goto_typenameseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv526)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv527 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2960 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv528)

and _menhir_goto_params : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_params -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv513 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2974 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv511 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2980 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 2985 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _v : 'tv_params = 
# 184 "specParser.mly"
                       ((RelId.fromString i)::p)
# 2990 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv512)) : 'freshtv514)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv521 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2998 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv517 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3008 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv515 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3018 "specParser.ml"
                )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState20 in
                ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | ID _v ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86) : 'freshtv516)
            | ID _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv518)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv519 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3046 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv520)) : 'freshtv522)
    | _ ->
        _menhir_fail ()

and _menhir_goto_conpat : _menhir_env -> 'ttv_tail -> 'tv_conpat -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv509 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv505 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv501 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | LPAREN ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33) : 'freshtv502)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv503 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv504)) : 'freshtv506)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv507 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv508)) : 'freshtv510)

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3107 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv495 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3119 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25) : 'freshtv496)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv497 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3135 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3140 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_idseq = 
# 216 "specParser.mly"
             ([Var.fromString i])
# 3145 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv498)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv499 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3155 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv500)

and _menhir_goto_conargs : _menhir_env -> 'ttv_tail -> 'tv_conargs -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv493 * (
# 61 "specParser.mly"
        (string)
# 3166 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let (_v : 'tv_conargs) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv491 * (
# 61 "specParser.mly"
        (string)
# 3173 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let ((co : 'tv_conargs) : 'tv_conargs) = _v in
    ((let (_menhir_stack, (i : (
# 61 "specParser.mly"
        (string)
# 3179 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_conpat = 
# 211 "specParser.mly"
                          ((Tycon.fromString i, Some co))
# 3184 "specParser.ml"
     in
    _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv492)) : 'freshtv494)

and _menhir_goto_paramseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_paramseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv475 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3197 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv473 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3203 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3208 "specParser.ml"
        ))), _, (pseq : 'tv_paramseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_paramseq = 
# 187 "specParser.mly"
                                  ((RelId.fromString i)::pseq)
# 3214 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv474)) : 'freshtv476)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv489 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv485 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv481 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 3235 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv477 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 3246 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
                    | LBRACE ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | LCURLY ->
                        _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | LPAREN ->
                        _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115) : 'freshtv478)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv479 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 3272 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv480)) : 'freshtv482)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv483 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv484)) : 'freshtv486)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv487 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv488)) : 'freshtv490)
    | _ ->
        _menhir_fail ()

and _menhir_reduce23 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let t = () in
    let _v : 'tv_elem = 
# 259 "specParser.mly"
              (Bool(true))
# 3300 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_patom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState236 | MenhirState204 | MenhirState217 | MenhirState200 | MenhirState129 | MenhirState132 | MenhirState161 | MenhirState189 | MenhirState187 | MenhirState185 | MenhirState182 | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv467 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | CONJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv455 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState189
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState189) : 'freshtv456)
        | DISJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv457 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState187 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState187
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState187) : 'freshtv458)
        | IFF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv459 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState185
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185) : 'freshtv460)
        | IMPL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv461 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState182 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState182 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState182
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState182) : 'freshtv462)
        | RCURLY | RPAREN | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv463 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (pa : 'tv_patom)) = _menhir_stack in
            let _v : 'tv_pred = 
# 330 "specParser.mly"
                 (pa)
# 3449 "specParser.ml"
             in
            _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv464)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv465 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv466)) : 'freshtv468)
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv471 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv469 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (pa : 'tv_patom)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 339 "specParser.mly"
                     (Predicate.Not pa)
# 3469 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv470)) : 'freshtv472)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ratom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_ratom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv453 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARMINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv439 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv440)
    | CROSSPRD ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv441 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76) : 'freshtv442)
    | MINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv443 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74) : 'freshtv444)
    | PLUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv445 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72) : 'freshtv446)
    | UNION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv447 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59) : 'freshtv448)
    | ANGRIGHT | CONJ | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | NUMEQ | PIPE | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv449 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ra : 'tv_ratom)) = _menhir_stack in
        let _v : 'tv_rexpr = 
# 236 "specParser.mly"
                 (ra)
# 3600 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv450)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv451 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv452)) : 'freshtv454)

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3614 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_bpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_bpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv437) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_bpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv435) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ba : 'tv_bpatom) : 'tv_bpatom) = _v in
    ((let _v : 'tv_patom = 
# 341 "specParser.mly"
                  (Predicate.Base ba)
# 3634 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv436)) : 'freshtv438)

and _menhir_reduce25 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3641 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3647 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_elem = 
# 261 "specParser.mly"
            (Var(Var.fromString i))
# 3652 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce33 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3659 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3665 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_instexpr = 
# 219 "specParser.mly"
                (RInst { sargs = empty (); 
                targs = empty(); args = empty (); 
                rel = RelId.fromString i})
# 3672 "specParser.ml"
     in
    _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_goto_elem : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState47 | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv423 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv417 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState47
            | ID _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState47
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47) : 'freshtv418)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv419 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
            let _v : 'tv_elemseq = 
# 255 "specParser.mly"
                  ([el])
# 3724 "specParser.ml"
             in
            _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv420)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv421 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv422)) : 'freshtv424)
    | MenhirState236 | MenhirState204 | MenhirState217 | MenhirState200 | MenhirState129 | MenhirState131 | MenhirState161 | MenhirState164 | MenhirState189 | MenhirState187 | MenhirState185 | MenhirState182 | MenhirState178 | MenhirState176 | MenhirState174 | MenhirState172 | MenhirState170 | MenhirState165 | MenhirState101 | MenhirState104 | MenhirState84 | MenhirState33 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv425 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        (_menhir_reduce68 _menhir_env (Obj.magic _menhir_stack) : 'freshtv426)
    | MenhirState132 | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv433 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv429 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv427 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (el : 'tv_elem)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_ratom = 
# 244 "specParser.mly"
                              (T[el])
# 3756 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv428)) : 'freshtv430)
        | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | SUBSET | SUBSETEQ | UNION ->
            _menhir_reduce68 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv431 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv432)) : 'freshtv434)
    | _ ->
        _menhir_fail ()

and _menhir_run152 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv413 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 3783 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv409 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3794 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
            | LBRACE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154) : 'freshtv410)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv411 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3816 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv412)) : 'freshtv414)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv415 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv416)

and _menhir_run120 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3831 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce99 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_tyd : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tyd -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv369 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv367 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (t : 'tv_tyd)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_tyd = 
# 307 "specParser.mly"
             (TyD.makeTRef t )
# 3852 "specParser.ml"
         in
        _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv368)) : 'freshtv370)
    | MenhirState127 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv375 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3860 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv371 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3870 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState129
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129) : 'freshtv372)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv373 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3908 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv374)) : 'freshtv376)
    | MenhirState154 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv393 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3917 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv389 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3927 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv387 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3934 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), (v : (
# 61 "specParser.mly"
        (string)
# 3939 "specParser.ml"
            ))), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartybind = 
# 375 "specParser.mly"
   ((v, ty))
# 3947 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv385) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_vartybind) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv383 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | COMMA ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv377 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LPAREN ->
                    _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState158
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158) : 'freshtv378)
            | DOT ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv379 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (vty : 'tv_vartybind)) = _menhir_stack in
                let _v : 'tv_tybindseq = 
# 371 "specParser.mly"
                          ([vty])
# 3978 "specParser.ml"
                 in
                _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv380)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv381 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv382)) : 'freshtv384)) : 'freshtv386)) : 'freshtv388)) : 'freshtv390)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv391 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3995 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv392)) : 'freshtv394)
    | MenhirState125 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv403 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv395 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState200 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState200
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState200) : 'freshtv396)
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv399 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv397 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 313 "specParser.mly"
                              (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, 
                Predicate.truee()))
# 4051 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv398)) : 'freshtv400)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv401 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv402)) : 'freshtv404)
    | MenhirState241 | MenhirState232 | MenhirState115 | MenhirState228 | MenhirState124 | MenhirState208 | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv407 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv405 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ty : 'tv_tyd)) = _menhir_stack in
        let _v : 'tv_basety = 
# 310 "specParser.mly"
                (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty,
                Predicate.truee()))
# 4072 "specParser.ml"
         in
        _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv406)) : 'freshtv408)
    | _ ->
        _menhir_fail ()

and _menhir_reduce99 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4081 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (
# 61 "specParser.mly"
        (string)
# 4087 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_tyd = 
# 305 "specParser.mly"
           (TyD.fromString t)
# 4092 "specParser.ml"
     in
    _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4099 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv361 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4111 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5) : 'freshtv362)
    | PIPE | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv363 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4127 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4132 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_tpatmatch = 
# 199 "specParser.mly"
              (Algebraic.Const {name=i;args=[]})
# 4137 "specParser.ml"
         in
        _menhir_goto_tpatmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv364)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv365 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4147 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv366)

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4155 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv359 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4169 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4174 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_params = 
# 183 "specParser.mly"
                ([RelId.fromString i])
# 4179 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv360)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv355) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4199 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv347) = Obj.magic _menhir_stack in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 4211 "specParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv345) = Obj.magic _menhir_stack in
            let ((i : (
# 61 "specParser.mly"
        (string)
# 4219 "specParser.ml"
            )) : (
# 61 "specParser.mly"
        (string)
# 4223 "specParser.ml"
            )) = _v in
            ((let _v : 'tv_conargs = 
# 213 "specParser.mly"
               (Vector.fromList [Var.fromString i])
# 4228 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv346)) : 'freshtv348)
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv349) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv350)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv351 * (
# 61 "specParser.mly"
        (string)
# 4248 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, (i : (
# 61 "specParser.mly"
        (string)
# 4253 "specParser.ml"
            ))) = _menhir_stack in
            let _v : 'tv_conpat = 
# 210 "specParser.mly"
               ((Tycon.fromString i, None))
# 4258 "specParser.ml"
             in
            _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv352)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv353 * (
# 61 "specParser.mly"
        (string)
# 4268 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv354)) : 'freshtv356)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv357 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv358)

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4282 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQUALOP ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv341 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4294 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84) : 'freshtv342)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv343 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4322 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4330 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState51
    | RBRACE | STAR ->
        _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51

and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce23 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35

and _menhir_run102 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4387 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv333 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4398 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | LAMBDA ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | LPAREN ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104) : 'freshtv334)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv335 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4428 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv336)) : 'freshtv338)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv339 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4443 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv327 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4455 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110) : 'freshtv328)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv329 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4471 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4476 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_paramseq = 
# 186 "specParser.mly"
                    ([RelId.fromString i])
# 4481 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv330)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv331 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4491 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv332)

and _menhir_run130 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONJ | DISJ | IFF | IMPL | RCURLY | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv323 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 338 "specParser.mly"
             (Predicate.truee())
# 4510 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv324)
    | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | RPAREN | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce23 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv325 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv326)

and _menhir_run131 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
    | LBRACE ->
        _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | LPAREN ->
        _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | NOT ->
        _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | TRUE ->
        _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState131
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131

and _menhir_run132 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | EXISTS ->
        _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
    | LAMBDA ->
        _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | LBRACE ->
        _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | LPAREN ->
        _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | NOT ->
        _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | TRUE ->
        _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState132
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState132

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv319 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState37
        | ID _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv317 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState37 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv313 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv311 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 239 "specParser.mly"
                                    (T(Vector.fromList []))
# 4625 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv312)) : 'freshtv314)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv315 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)) : 'freshtv318)
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState37
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37) : 'freshtv320)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv321 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv322)

and _menhir_run133 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv307 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4661 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv283 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4672 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv247 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4682 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv243 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4692 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv241 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4699 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4704 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 349 "specParser.mly"
                                           (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, false))
# 4714 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv242)) : 'freshtv244)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv245 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4724 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv246)) : 'freshtv248)
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv255 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4733 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 4738 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv251 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4749 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4753 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv249 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4760 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4764 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4769 "specParser.ml"
                    ))), (i2 : (
# 61 "specParser.mly"
        (string)
# 4773 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 345 "specParser.mly"
                                           (Predicate.BasePredicate.varEq 
                      (Var.fromString i1, Var.fromString i2))
# 4782 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv250)) : 'freshtv252)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv253 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4792 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4796 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv254)) : 'freshtv256)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv263 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4805 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (int)
# 4810 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv259 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4821 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 4825 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv257 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4832 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 4836 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4841 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (int)
# 4845 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 355 "specParser.mly"
                                              (Predicate.BasePredicate.varIntEq 
                      (Var.fromString i1, rhs))
# 4854 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv258)) : 'freshtv260)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv261 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4864 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 4868 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv262)) : 'freshtv264)
            | STRCONST _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv271 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4877 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 63 "specParser.mly"
       (string)
# 4882 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv267 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4893 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 4897 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv265 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4904 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 4908 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4913 "specParser.ml"
                    ))), (rhs : (
# 63 "specParser.mly"
       (string)
# 4917 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 357 "specParser.mly"
                                                   (
       				let rhstrimmed = String.sub (rhs) (1) ((String.length rhs) - 2) in 
       				Predicate.BasePredicate.varStrEq 
                      (Var.fromString i1, rhstrimmed))
# 4928 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv266)) : 'freshtv268)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv269 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4938 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 4942 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv270)) : 'freshtv272)
            | TRUE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv279 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4951 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv275 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4961 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv273 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4968 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4973 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 347 "specParser.mly"
                                          (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, true))
# 4983 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv274)) : 'freshtv276)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv277 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4993 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv278)) : 'freshtv280)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv281 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5004 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv282)) : 'freshtv284)
        | GREATERTHAN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv303 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5013 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv291 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5023 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 5028 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv287 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5039 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5043 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv285 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5050 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5054 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5059 "specParser.ml"
                    ))), (i2 : (
# 61 "specParser.mly"
        (string)
# 5063 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 351 "specParser.mly"
                                                (Predicate.BasePredicate.varGt 
                      (Var.fromString i1, Var.fromString i2))
# 5072 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv286)) : 'freshtv288)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv289 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5082 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5086 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv290)) : 'freshtv292)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv299 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5095 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (int)
# 5100 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv295 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5111 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5115 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv293 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5122 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5126 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5131 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (int)
# 5135 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 353 "specParser.mly"
                                                  (Predicate.BasePredicate.varIntGt 
                      (Var.fromString i1, rhs))
# 5144 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv294)) : 'freshtv296)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv297 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5154 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5158 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)) : 'freshtv300)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv301 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5169 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv302)) : 'freshtv304)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv305 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5180 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv306)) : 'freshtv308)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv309 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv310)

and _menhir_run151 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 62 "specParser.mly"
       (int)
# 5208 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv239) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ii : (
# 62 "specParser.mly"
       (int)
# 5218 "specParser.ml"
    )) : (
# 62 "specParser.mly"
       (int)
# 5222 "specParser.ml"
    )) = _v in
    ((let _v : 'tv_elem = 
# 258 "specParser.mly"
              (Int(ii))
# 5227 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv240)

and _menhir_run49 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 5234 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49
    | LPAREN ->
        _menhir_reduce33 _menhir_env (Obj.magic _menhir_stack)
    | ANGRIGHT | ARMINUS | CONJ | CROSSPRD | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | MINUS | NUMEQ | PIPE | PLUS | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce25 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49

and _menhir_run42 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv237) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let f = () in
    let _v : 'tv_elem = 
# 260 "specParser.mly"
               (Bool(false))
# 5262 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv238)

and _menhir_run162 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run152 _menhir_env (Obj.magic _menhir_stack) MenhirState162
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162

and _menhir_run165 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState165 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState165
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState165

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
    | LBRACE ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | REF ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_run122 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv235 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState122 in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5332 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv231 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5343 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState124 _v
            | LBRACE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | LCURLY ->
                _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | LPAREN ->
                _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState124
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState124) : 'freshtv232)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv233 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5369 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv234)) : 'freshtv236)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState122

and _menhir_run125 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv229 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState125 in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5391 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv225 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5402 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
            | LBRACE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState127
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127) : 'freshtv226)
        | PIPE | RCURLY ->
            _menhir_reduce99 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv227 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5426 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv228)) : 'freshtv230)
    | LBRACE ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState125
    | REF ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState125
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125

and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv221 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5451 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv217 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5462 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv215 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5469 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), (t : (
# 61 "specParser.mly"
        (string)
# 5474 "specParser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_tyd = 
# 306 "specParser.mly"
                         (TyD.makeTList (TyD.fromString t))
# 5481 "specParser.ml"
             in
            _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv216)) : 'freshtv218)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv219 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5491 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv220)) : 'freshtv222)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv223 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)

and _menhir_run203 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 5506 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LCURLY ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv211 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5518 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGLEFT ->
            _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | EXISTS ->
            _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState204 _v
        | LAMBDA ->
            _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | LBRACE ->
            _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | LPAREN ->
            _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | NOT ->
            _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | TRUE ->
            _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState204
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState204) : 'freshtv212)
    | COMMA | RPAREN | SEMICOLON ->
        _menhir_reduce99 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv213 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5558 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv214)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv63 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv65 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState248 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState246 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv69 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState244 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState241 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv73 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5596 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState236 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv75 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5605 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv77 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5614 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState228 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5623 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState226 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * _menhir_state * 'tv_varty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState217 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv83 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5637 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 5641 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv85 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState208 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv87 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5655 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 5659 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState204 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv89 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5668 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState200 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv91 * _menhir_state) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState189 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState187 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState182 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv99 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState178 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv101 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv103 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState174 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv105 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv107 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState165 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv113 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState162 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv117 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState158 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv119 * _menhir_state * 'tv_vartybind)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState154 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv121 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5752 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv124)
    | MenhirState132 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv125 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv127 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv129 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5776 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState127 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv131 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5785 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState125 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv133 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState124 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv135 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5799 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState122 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv137 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv141 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 5818 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv143 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5827 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv145 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv147 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5841 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv149 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 5850 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv151 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5859 "specParser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv153 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5868 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv157 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 5882 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv159 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5891 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv161 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv163 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv165 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv167 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * _menhir_state * 'tv_funparam)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv171 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv175 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv177 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5940 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv181 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5954 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv183 * _menhir_state * 'tv_elem)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv185 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv189 * _menhir_state) * 'tv_conpat))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv191 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5983 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv192)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv193) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv194)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv195 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 5996 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv197 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6005 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv199 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6014 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv200)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv201 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv203 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6028 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv204)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv205 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6037 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv207 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6046 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv208)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv209) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv210)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv59 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6067 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv55 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6078 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3) : 'freshtv56)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv57 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6096 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)) : 'freshtv60)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv61 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6120 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv43 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6131 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState93 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94) : 'freshtv44)
        | ID _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
        | LPAREN ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState93
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv46)
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
# 61 "specParser.mly"
        (string)
# 6164 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv48)
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

and _menhir_run98 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
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
# 61 "specParser.mly"
        (string)
# 6209 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv31 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6220 "specParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | ID _v ->
                    _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
                | INT _v ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
                | LAMBDA ->
                    _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | LCURLY ->
                    _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | LPAREN ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | TRUE ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101) : 'freshtv32)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv33 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6250 "specParser.ml"
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

and _menhir_run108 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108

and _menhir_run231 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 6285 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6297 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState232 _v
        | LBRACE ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState232
        | LCURLY ->
            _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState232
        | LPAREN ->
            _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState232
        | REF ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState232
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState232) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6323 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run234 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6340 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv19 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6351 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | EXISTS ->
                _menhir_run162 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState236 _v
            | LAMBDA ->
                _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | LBRACE ->
                _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | LPAREN ->
                _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | NOT ->
                _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | TRUE ->
                _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState236
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState236) : 'freshtv20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv21 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6389 "specParser.ml"
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
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6404 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6413 "specParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv15) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6421 "specParser.ml"
    )) : (
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6425 "specParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv16)) : 'freshtv18)

and _menhir_run239 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6441 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv7 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6452 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run203 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
            | LBRACE ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | LCURLY ->
                _menhir_run125 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | LPAREN ->
                _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState241
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241) : 'freshtv8)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv9 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6478 "specParser.ml"
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
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6505 "specParser.ml"
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
        _menhir_run239 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        ((let _1 = () in
        let _v : (
# 76 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6537 "specParser.ml"
        ) = 
# 80 "specParser.mly"
              (RelSpec.mk_empty_relspec ())
# 6541 "specParser.ml"
         in
        _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2)) : 'freshtv4)
    | FORMULA ->
        _menhir_run234 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ID _v ->
        _menhir_run231 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LPAREN ->
        _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | PRIMITIVE ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | RELATION ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | TYPE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv6))

# 233 "/home/ashish/.opam/4.03.0/lib/menhir/standard.mly"
  

# 6564 "specParser.ml"
