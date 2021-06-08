(* these need updation to OCAML Layout and TyDesc*)
exception Unimplemented of string
exception Error of string
open Vector

let debug = true 
let ($) (f, arg) =  f arg
let (<<) f g x = f (g x)

let count = ref 0 

let get_fresh (pre:string)= 
  let next = !count in 
  let _ = count := !count + 1 in 
  (pre^"_"^(string_of_int next))

module Ident = struct 
 type t = string 

 let create s = s 
 let equal t1 t2 = (t1 = t2) 
 let name t = t 
 



end 


(*helper module*)

module Helper = struct 
	
let rec keepAll f l =  
   match l with 
    [] -> []
    | x :: l' -> if (f x ) then (x :: keepAll f l') else (keepAll f l')
let rec my_find_map (f) l = 
  match l with 
        [] -> None 
        | x :: xs -> match (f x) with
                        | Some v -> Some v 
                        | None -> my_find_map f xs 

(*Remove Vector from here*)  
let mkMapper eqns cmp restore = 
  fun t' -> match (my_find_map (fun (t, ts) -> if t = t' then Some ts else None ) eqns ) with
      Some ts -> ts 
    |None -> restore t'



let vecToStr f vec = match List.length vec with
      0 -> ""
    | _ -> " "^(Vector.toString f vec)

let varStrEq (v1, v2) = (Ident.name v1 = Ident.name v2)
let varSubs  (n, o) v = if (varStrEq (v, o)) 
  then n else v


end

(*Types varaiable 'a , 'b etc*)
module Tyvar = 
struct
  type t = Ident.t

  let symbase = "int"


  let newSVar = fun _ ->
    let id = symbase ^ string_of_int !count in 
    let _ = count := !count + 1
    in 
    Ident.create id


  let equal (t1,t2) = Ident.equal t1 t2
  let toString = Ident.name
  let fromString s = Ident.create s

end 

module Var = struct

  type t = Ident.t
  let toString = Ident.name



  let symbase = "var_"


  let get_fresh_var s = 
    let id = symbase^(s)^ string_of_int !count in 
    let _ = count := !count + 1
    in 
    Ident.create id


  let fromString s = Ident.create s
  let noName = Ident.create ""
  let equal t1 t2 = Ident.equal t1 t2
end

module RelId =
struct 
  type t = Ident.t
  let equal (t1,t2) = Ident.equal t1 t2
  let toString = Ident.name
  let fromString s = Ident.create s
end


module SVar = 
struct 
  type t = Ident.t

  let symbase = "'t"
  let  count = ref 0

  let newSVar = fun _ ->
    let id = symbase ^ string_of_int !count in 
    let _ = count := !count + 1
    in 
    Ident.create id

  let eq v1 v2 = Ident.equal v1 v2  
  let toString  = Ident.name  

end
exception SpecLangEx of string
exception TyConEx of string 

module Tycon= 
struct
  type t = Ident.t
  let toString  = Ident.name  
  let equals(t1,t2) = (Ident.name t1 = Ident.name t2  )
  
  let fromString s = Ident.create s 
end



(*This will be replaced with our base types and functions over it*)     
module TyD = 
  struct 
type loc = string 


type t = 
        | Ty_unknown
        | Ty_alpha of Tyvar.t
        | Ty_unit 
        | Ty_ref of t 
        | Ty_list of t (*only list and no other user define algebraic data types*)
        | Ty_int 
        | Ty_bool
        | Ty_string
        | Ty_char         
        | Ty_heap
        | Ty_arrow of t * t


(*check if two types are same*)
  let rec sametype t1 t2 = 
        match (t1, t2) with
        | ((Ty_alpha tvar1), (Ty_alpha tvar2)) -> (Tyvar.equal(tvar1, tvar2)) 
                
        | (Ty_unit, Ty_unit) -> true
        | ((Ty_ref  ta1),( Ty_ref ta2))  -> sametype ta1 ta2 
        | ((Ty_list  ta1), (Ty_list ta2)) -> sametype ta1 ta2
        | (Ty_int, Ty_int) -> true
        | (Ty_bool, Ty_bool)  -> true
        | (Ty_char, Ty_char) -> true        
        | (Ty_heap, Ty_heap)  -> true
        | (Ty_string, Ty_string) -> true

        | ((Ty_arrow  (t11 , t12) ), 
                Ty_arrow (t21, t22)) -> (sametype t11 t21) && (sametype t12 t22)
        | (_, _) -> false  
   
(*base types from string*)    
 let fromString s = 
        match s with 
        | "int" -> Ty_int 
        | "bool" -> Ty_bool 
        | "char" -> Ty_char 
        | "heap" -> Ty_heap
        | "unit" -> Ty_unit
        | "string" -> Ty_string
        | _ -> Ty_alpha (Tyvar.fromString s)

 let rec toString t = 
      match t with
        | Ty_unknown -> "Ty_unknown" 
        | Ty_alpha tvar -> Tyvar.toString tvar
        | Ty_unit -> "Ty_unit"
        | Ty_ref  t -> ("Ty_ref "^(toString t)) 
        | Ty_list  t -> ("Ty_list "^(toString t))
        | Ty_int -> "Ty_int"
        | Ty_bool -> "Ty_bool"
        | Ty_char -> "Ty_char"        
        | Ty_heap  -> "Ty_heap"
        | Ty_string -> "Ty_string"
        | Ty_arrow  (_ , _)-> "Function type"

 let makeTunknown () = Ty_unknown           
 let makeTList t = Ty_list t 
 let makeTRef t = Ty_ref t
 
  
 let instantiateTyvars substs tyd = 
      try 
       Ty_alpha  (List.assq tyd substs)
      with 
      | Not_found -> 
      let () = List.iter (fun (tyd1, tyvar) -> Printf.printf "%s" ((toString tyd1)^"|-> "^(Tyvar.toString tyvar))) substs in 
        raise (SpecLangEx ( "Type being Instantiated, Not present "^(toString tyd)))
     
   (*Assuming all types all types are unifiable*)
  let unifiable (t1,t2) = 
    true 

  let unify t1 t2 = 
        if sametype t1 t2 then 
                t1 
        else raise (SpecLangEx ("Non Unifiable types"))
  end

module Con = struct
      
  type t =
        ILit of int
        |BLit of bool 
        |CLit of char 
        |Llit of t list           
        |SLit of string 
        |ULit 
        |Cons
        | Nil     
        | NamedCons of Ident.t

  let default = Cons

  let fromString s = 
        match s with 
        | "nil" -> Nil
        | "cons" -> Cons
        | _ -> NamedCons (Ident.create s)

  let toString t = match t with 
         ILit i -> ("ILit "^(string_of_int i)) 
        |BLit b -> match b with 
                   true -> "BLit true"
                   | false -> "BLit false"
        | _ -> raise (Unimplemented "to string Con")
(*
        |CLit of char 
        |Llit of lit list           
        |SLit of string 
        |ULit 
        |Cons
        | Nil     
        | NamedCons of Ident.t
*)
 
open TyD 
  let getType t =
        match t with 
         ILit _ -> Ty_int
        |BLit _ -> Ty_bool
        |CLit _  -> Ty_char 
        |Llit lst  ->  (*TODO monomorphic, use the typing info from the ocaml*)  
                                Ty_list (Ty_int)            
        |SLit s  -> Ty_string
        |ULit -> Ty_unit
        |Nil -> Ty_list (Ty_int)
        |_ -> raise (Unimplemented "no type inference for" )
 
end                    




(*remains as it is with needed changes for TyD and SVar*)
module TupSort = 
struct
  type tT = T of TyD.t | S of SVar.t
  type t = Tuple of tT list
  type cs = Eq of t*t

  let tTToString tT = match tT with 
      T tyd -> TyD.toString tyd
    | S svar -> SVar.toString svar


  let toString (Tuple tts) = List.fold_left (fun parsedStr tT ->  parsedStr^(tTToString tT)) "TupleSort " tts

  let toString = fun t -> "{"^(toString t)^"}" 
  let fromSVar = fun t ->  Tuple [S t]

  let filter_map  f l =
    let rec aux accu = function
      | [] -> List.rev accu
      | x :: l1 ->
          match f x with
          | None -> aux accu l1
          | Some v -> aux (v :: accu) l1
    in
    aux [] l 


  let getSVars (Tuple tts) = 
    filter_map (fun tT -> match tT with S t -> Some t | _ -> None) tts

  let tTeq t1 t2 = match (t1, t2) with 
    |(T tyd1, T tyd2) ->TyD.sametype tyd1 tyd2
    |(S v1, S v2) -> SVar.eq v1 v2
    | (_, _) -> false

  let equal (Tuple tydv1) (Tuple tydv2) =
    (List.length tydv1 = List.length tydv2) && 
    (List.for_all2 tTeq tydv1 tydv2)

  let unionType ((Tuple tydv1) as t1, (Tuple tydv2) as t2) = 
    match (List.length tydv1, List.length tydv2) with
    |(0, _) -> ([], Tuple tydv1)
    |(_, 0) -> ([], Tuple tydv2)
    |(n1, n2) -> if (equal (Tuple tydv1) (Tuple tydv2)) then ([], Tuple tydv1)
        else ([Eq (Tuple tydv1  ,Tuple tydv2)], Tuple tydv1)

  let crossPrdType (Tuple tyds1 as t1, Tuple tyds2 as t2) = 
    match (List.length tyds1, List.length tyds2) with
      (0,_) -> ([], Tuple tyds1)
    | (_,0) -> ([], Tuple tyds2)
    | _ -> ([], Tuple (List.concat [tyds1; tyds2]))

  let instSVars (Tuple ttl) mapSVar = 
    Tuple (List.concat  
          (List.map (fun tt -> match tt with 
                T _ -> [tt] 
                | S t -> (fun (Tuple ttl') -> ttl') (mapSVar t)) ttl) )  

  let mapTyD (Tuple ttl) f = Tuple (List.map (fun tt -> match tt with 
        T tyd -> T (f tyd)
      | _ -> tt) ttl )

  (* Tuple Sort Constraint Solving *)

  let eq = fun (Eq (x,y)) -> (x, y) 

  type sol = (SVar.t * t)
  
  let trySolveConstraint (c:cs) : sol option =
    let len = List.length in   
    
    let assertNotCirc (v, rt) = (* assert true in *) 
      let rhsvs = (getSVars rt) in 
      let cStr = fun _ -> (SVar.toString v)^" = "^ (toString rt) in
      let () = assert (List.for_all (fun rhsv ->
                       not (SVar.eq v rhsv)) rhsvs)  
        
      in () in   
     (match (eq c) with
      |(Tuple [S v1], Tuple []) -> None
      |(Tuple [], Tuple [S v2]) -> None
      |(Tuple [S v1], rty2) -> (assertNotCirc (v1, rty2); Some (v1, rty2))
      |(rty1, Tuple [S v2]) -> (assertNotCirc (v2, rty1); Some (v2, rty1))
      | _ -> None )
  
  let clearTautologies cs =
    let taut = fun (tt1, tt2) ->
      match (tt1, tt2) with
      |(T tyd1, T tyd2) -> (assert ( TyD.sametype tyd1 tyd2); true)
      |(S v1, S v2) -> SVar.eq v1 v2
      | _ -> false
    in 
    Helper.keepAll (fun (Eq (Tuple ts1, Tuple ts2)) -> 
        match (ts1, ts2) with
        | ([tt1], [tt2]) -> not (taut (tt1, tt2))
        | (_, _) ->  true) cs

  (* Applies reltyvar eqn( v=rt) iin cs.
   * Post condition : v does not occur in cs 
  *)
  let applyRelTyVarEqn eqn cs     =
    List.map (fun (Eq (rt1, rt2)) -> 
        let mapSVar = Helper.mkMapper [eqn] SVar.eq fromSVar in 
        let rt1' = instSVars rt1 mapSVar in 
        let rt2' = instSVars rt2 mapSVar in 
        Eq (rt1', rt2')) cs


  let elabcs cs  = 
    let len = List.length in 
    let (no, yes) = List.partition (fun (Eq (Tuple ts1, Tuple ts2)) ->  
        if (len ts1 = len ts2) then true else false) cs in
    let yes' = match yes with 
        [] -> failwith "Unsolvable TupSort Constraint"
      | Eq  (Tuple ts1, Tuple ts2) ::  yes' -> 
          List.concat [List.map2 (fun t1 t2 -> Eq (Tuple [t1], Tuple [t2] )) ts1 ts2; yes'] 
    in List.concat[yes';no]         

  (* Solve a constraint, applies the solution to the rest, and 
   * clears any new tautologoes. Repeats this process until threre are no more constraints, or the residue os 
   * unsolvable.
   * Invariant : 
           * sol :....
  *)
  exception Return of (sol list)

  let rec relTyVarEqns cs  =
    try
      let cs = clearTautologies cs in 
      let _ = match cs with
          [] -> (raise (Return []))
        | _ -> () 
      in (*This is a simplification, implement the correct semantics of Vector.loop this must return a pair*)
      let solEqnOp = Vector.loop(cs, (fun c -> match (trySolveConstraint c) with 
            Some sol -> Some (Some sol)
          | _ -> None), (fun () -> None) ) in

      (*The issue is that solEqnOp is returning a wrong type*)
      let (eqns, residue) = match solEqnOp with
          None -> ([], elabcs cs)
        | Some ((t, ts) as solEqn) -> 
            let newcs = applyRelTyVarEqn (t, ts) cs in 
            let moreEqns = relTyVarEqns newcs in 
            let moreEqnFn = Helper.mkMapper moreEqns SVar.eq fromSVar in 
            let solEqn' = match moreEqns with 
                [] -> solEqn
              |_ ->  (t, instSVars ts moreEqnFn)  in 
            (solEqn'::moreEqns, []) in 
      let newEqns = relTyVarEqns residue in                    
      let newEqFn = Helper.mkMapper newEqns SVar.eq fromSVar in 
      let eqns' = match newEqns with 
          [] -> eqns
        | _ -> List.map (fun (t, ts) -> (t, (instSVars ts newEqFn))) eqns in 

      List.concat [eqns'; newEqns]

    with
      Return l -> l

  (* Solve constraints and return solutions *)
  let solvecs cs = Helper.mkMapper (relTyVarEqns cs) SVar.eq fromSVar



end

module TS = TupSort

module SimpleProjSort = struct
  type t = ColonArrow of (TyD.t * TupSort.t)

  let toString (ColonArrow (tyD, tupsort)) = 
    (TyD.toString tyD)^ " :-> "^(TupSort.toString tupsort)
  (* The pretty-printing will be added later*)
  (*let layout t = Layout.str ( toString t)*)

  let newSPSort tyd rt  = ColonArrow (tyd, rt)

  let domain (ColonArrow (d, _)) = d

  let range (ColonArrow (_,r)) = r

  let mapTyD (ColonArrow (tyd, ts)) f =
    ColonArrow (
     tyd, TS.mapTyD ts f)
end

module SPS = SimpleProjSort 

module ProjSort = struct
  type t = T of {paramsorts : SimpleProjSort.t list;
                 sort : SimpleProjSort.t}

  let toString (T {paramsorts; sort}) =
    match List.length paramsorts with
      0 -> SimpleProjSort.toString sort
    |_ -> (Vector.toString (SimpleProjSort.toString) paramsorts)
          ^ " :-> "^ (SimpleProjSort.toString sort)

  let newProjSort paramsorts sort =  T {paramsorts = paramsorts; sort = sort}                

  let simple sps = T {paramsorts = Vector.new0 (); sort = sps}

  let domain (T {sort; _}) = SimpleProjSort.domain sort

  let range (T {sort; _}) = SimpleProjSort.range sort


end 

module PS = ProjSort 

module ProjSortScheme = struct 
  exception PSSInst of string 

  type t = T of {svars : SVar.t list; 
                 sort : ProjSort.t}

  let toString (T{svars;sort})= (Vector.toString (SVar.toString) svars)^". "^
                                (ProjSort.toString sort)

  let simple sps = T {svars = Vector.new0 (); sort = ProjSort.simple sps}


  let generalize (sv, s) = T {svars = sv; sort = s}

  let instantiate (T{svars;sort}, tsv) = 
    let svarMap = try 
        Vector.zip svars tsv 
      with 
      _ -> raise (PSSInst "PSS inst error1") in
    let mapsSVar = fun t -> 
      match (Vector.peekMap (svarMap, fun (t', ts) -> if (SVar.eq t t') then 
          Some ts else None ) )
      with 
        Some ts -> ts 
      |None -> raise (PSSInst "PSS inst error2") in 

    let PS.T {paramsorts;sort = (SPS.ColonArrow (tyd, ts)) } = sort in 
    let sort' = SPS.ColonArrow (tyd, TS.instSVars ts mapsSVar) in 
    let ps' = Vector.map (paramsorts, fun (SPS.ColonArrow (tyd,ts)) -> SPS.ColonArrow (tyd, TS.instSVars ts mapsSVar))  in 
    PS.T {paramsorts = ps'; sort = sort'}  

end

module PSS = ProjSortScheme

module ProjTypeScheme = struct 
  exception PTSInst of string
  type t = T of {tyvars : Tyvar.t list; sortscheme : ProjSortScheme.t}

  let toString (T {tyvars; sortscheme}) = (Vector.toString (Tyvar.toString) tyvars) 
                                          ^ " @ss: " ^ (ProjSortScheme.toString sortscheme)

  let paramSorts ( T {sortscheme = PSS.T {sort = ProjSort.T {paramsorts; _}; _}; _} ) = paramsorts

  let groundSort (T {sortscheme = PSS.T {sort = ProjSort.T{sort;_}; _};_}) = sort

  let simple (tyvars, sps) = T {tyvars = tyvars; sortscheme = PSS.simple sps}

  let generalize (tyvars, ss) = T {tyvars=tyvars; sortscheme = ss}
  (*TODO Ashish
   * Instantiate returns the same ProjSortScheme*)
  let instantiate (T {tyvars;sortscheme=ss} as pts, tydlist) = 
    let lentyDlist = (List.length tydlist) in
    let lentyvar = (List.length tyvars) in

    (* let tyvmap = try 
      (List.map2 (fun x y  -> (x,y)) tydlist tyvars) with 
        _ -> raise (PTSInst "PTS : insufficient or more type args") in
 *)
    let f = fun tyd -> tyd in  
     (* try    
      TyD.instantiateTyvars tyvmap 
    with 
    | _ -> raise (PTSInst "Error while instantiating Tyvars") 
  in 
 *)
    let PSS.T{sort = PS.T{paramsorts; sort = (SPS.ColonArrow (tyd, ts))}; svars} = ss in 
    
    let sort' = SPS.ColonArrow (f tyd, TS.mapTyD ts f) in 
    let ps' = List.map (fun (SPS.ColonArrow (tyd, ts)) -> SPS.ColonArrow (f tyd, ts)) paramsorts in 
    let s' = PS.T {paramsorts = ps'; sort = sort'} in 
    let ss' = PSS.T {svars = svars; sort = s'} in 

    ss'
  let domain (T {sortscheme = PSS.T { sort = ProjSort.T{sort = SPS.ColonArrow (tyd,_);_}; _};_ }) = tyd





end 
module PTS = ProjTypeScheme 

module RelLang = 
struct
  open Helper
  type elem = Int of int 
            | Bool of bool
            | Var of Ident.t

  type instexpr = RInst of {targs: TyD.t list;
                            sargs : TupSort.t list;
                            args : instexpr list;
                            rel : RelId.t       }

   (*define heap expr*)
   


  (*to define a predicate sel h inp = ls we need elem as expression as well*)      
  
   type expr = 
            | V of elem    
            | T of elem list 
            | X of expr * expr 
            | U of expr * expr 
            | D of expr * expr 
            | ADD of expr * expr
            | SUBS of expr * expr
            | R of instexpr * Ident.t
            | MultiR of instexpr * (Ident.t list) 
  type term = Expr of expr
            |Star of instexpr


 

  let relexpr_for_var (v : Var.t) =
        V(Var (Var.toString v)) 
  let relexpr_for_int (i : int) =
        T ([Int i])
  let  relexpr_for_bool (b : bool) = 
        T ([Bool b])
  
  let rId = fun c -> T  (Vector.new1 (Var c)) (* define Vector.new0 similar to the mlton basic type of vector*)
   
  let empty () = [] 

  let rNull = fun _ -> T ([])

  let instOfRel = fun rel ->
    let empty = fun _ -> Vector.new0 () in 
    RInst {targs= empty (); sargs = empty (); args = empty (); rel= rel}


  (*Creates an expr (expr ty above) for a given relation name and a parameter variable*)
  let relationInstantiationExp relname param : expr = 
        let created_inst_rel_exp  =  R (instOfRel relname, param) in 
        created_inst_rel_exp
        



  let instOfPolyRel = fun rel -> 
    (fun targs -> let empty = fun _ -> Vector.new0 () in 
      RInst {targs=targs; sargs=empty (); args= empty (); rel= rel} )

  let appR = fun (rid, targs, x) -> R (instOfPolyRel rid targs, x)

  let elemToString = fun el -> 
    match el with 
      Int i -> string_of_int i
    | Bool b -> string_of_bool b
    | Var v -> Ident.name v (* define the Var moudle*)

  let rec ieToString (RInst {targs; sargs; args; rel}) = 
    let tstr = vecToStr TyD.toString targs in 
    let sstr = vecToStr TupSort.toString sargs in 
    let rstr = vecToStr ieToString args in 
    "(" ^ (RelId.toString rel)^tstr^sstr^rstr ^ ")"

  let rec exprToString exp = match exp with 
     V e -> ("("^(elemToString  e)^")")
    |T elevc -> "{(" ^ (List.fold_left (fun acc e -> 
        (elemToString e)^acc) "" elevc) ^ ")}"
    | X (e1, e2) -> "(" ^ (exprToString e1) ^ " X " ^ (exprToString e2) ^ ")"         

    | U (e1, e2) -> "(" ^ (exprToString e1) ^ " U " ^ (exprToString e2) ^ ")"  

    | D (e1, e2) -> "(" ^ (exprToString e1) ^ " - " ^ (exprToString e2) ^ ")"      

    | ADD (e1, e2) ->   "(" ^ (exprToString e1) ^ " + " ^ (exprToString e2) ^ ")"
    | SUBS (e1, e2) ->   "(" ^ (exprToString e1) ^ " -- " ^ (exprToString e2) ^ ")"
    
    | R (ie, arg) ->  
        (ieToString ie) ^ "(" ^ (Ident.name arg) ^ ")"
    | MultiR (ie, argl) -> 
        (ieToString ie) ^ "(" ^ (List.fold_left (fun _acc arg -> (_acc^", "^(Ident.name arg))) (" ") argl )^" )"    
  
  let exprToString = exprToString


  let termToString = fun trm -> match trm with 
      Expr e -> exprToString e
    | Star ie -> (ieToString ie) ^ "*"

  (*fun app (relId,var) = R(relId,var)*)
  let union (e1, e2) = U (e1,e2)
  let crossprd (e1,e2) = X (e1,e2)
  let diff (e1,e2) = D (e1,e2)
  let add (e1, e2) = ADD (e1, e2)
  let subs (e1, e2) = SUBS(e1, e2)
  let rNull _ = T []



  let (%) = fun f g x  -> f (g x)  

  let rec ieApplySubsts substs (RInst {rel;args;targs;sargs}) = 
    let doIt = ieApplySubsts substs in 
    let vtor = ((RelId.fromString) % (SVar.toString)) in 
    let subst v = List.fold_left (fun r (n,o) -> if ( Ident.name o = RelId.toString r) then 
                                     (vtor n) else r) v substs in 
    RInst {rel=subst rel; args=List.map doIt args;targs=targs; sargs=sargs } 

  let rec applySubsts substs rexpr = 
    let doIt = applySubsts substs  in 
    let subst v = List.fold_left (fun v (newEl, oldEl) -> 
         if (Ident.name oldEl = Ident.name v) then newEl else v) v substs in 
    let elemSubst elem = 
      match elem with 
        Var v -> 
          Var (subst v)
      | c -> c in
    match rexpr with 
      T elem -> T (List.map elemSubst elem)
    | X (e1, e2) -> X (doIt e1, doIt e2)
    | U (e1, e2) -> U (doIt e1, doIt e2)
    | D (e1, e2) -> D (doIt e1, doIt e2)
    | ADD (e1, e2) -> ADD (doIt e1, doIt e2)
    | SUBS(e1, e2) -> SUBS (doIt e1, doIt e2)
    | R (ie, argvar) -> R (ieApplySubsts substs ie, subst argvar)
    | MultiR (ie, argvarl) -> MultiR (ieApplySubsts substs ie, (List.map (fun argvar -> subst  argvar) argvarl))    
    | V e -> V (elemSubst e)  
  let rec mapInstExpr t f = 
    let g = fun x -> mapInstExpr x f in 
    let doIt = fun cons -> fun (x1, x2) -> cons (g x1 , g x2) in  

    match t with 
      X (x, y) ->  X ( g x, g y) 
    | U (x, y) -> U (g x, g y)
    | D (x, y) -> D (g x, g y)
    | ADD (x,y) -> ADD (g x, g y)
    | SUBS (x,y) -> SUBS (g x, g y)
    | T _ -> t
    | R (ie, x) -> R (f ie, x)
    | V e -> t 


  let mapTyD t f = 
    let rec doItIE (RInst{targs;sargs;args;rel}) = 
      let targs' = List.map f targs in
      let sargs' = List.map (fun ts -> TS.mapTyD ts f) sargs in 
      let args' =  List.map doItIE args in 
      RInst {targs=targs'; sargs=sargs'; args=args';rel=rel}

    in 
    mapInstExpr t doItIE

  let mapSVar t f =
    let rec doItIE (RInst {targs;sargs;args;rel}) = 
      let sargs' = List.map  (fun ts -> TS.instSVars ts f ) sargs in 
      let args' = List.map doItIE args in 
      RInst {targs=targs; sargs=sargs'; args=args';rel=rel}

    in
    mapInstExpr t doItIE

  let mapRel t f =
    let rec doItIE (RInst {targs;sargs;args;rel}) = 
      let rel' = f rel in 
      let args' = List.map doItIE args in 
      RInst {targs=targs; sargs=sargs;args=args';rel=rel'}

    in
    mapInstExpr t doItIE
end       
(*The Con.t must be replaced with the exact constructor*)
module StructuralRelation = struct (*<R, Tr m Const x , y -> r | Nil -> r ->*)
  type t = T of {id:RelId.t ; params : RelId.t list; mapp: ( Con.t * Ident.t list option * RelLang.term) list}
  (* Not allowed in Ocaml, this can always be replaces by application of T*)
  (*let newSR data = T data*)

  let conMapToString mapp =
    let conmap = "{" ^ (Vector.toString (fun (c,vlo,trm) ->
        let cstr = Con.toString c in 
        let vseq = match vlo with 
            None -> ""
          | Some vl -> Vector.toString Ident.name vl in 
        let trmstr = RelLang.termToString trm
        in
        cstr ^ vseq ^ " => " ^ trmstr
      ) mapp) ^ "}\n"
    in
    conmap

  let toString = fun (T{id;params;mapp}) -> 
    let relid = RelId.toString id in 
    let relstr = match List.length params with
        0 -> relid
      | _ -> relid ^ (List.fold_right (fun rid acc -> acc ^ " " ^ (RelId.toString rid)) params "" ) 
    in 

    let conmap = conMapToString mapp in 

    "relation (" ^ relstr ^ ") = " ^ conmap
end

module PrimitiveRelation = struct
  type def = Nullary of RelLang.expr
           | Nary of Ident.t * def 

  type t = T of {id: RelId.t; def:def}

  let rec defToString def = match def with 
      (Nullary rexpr) -> RelLang.exprToString rexpr
    |(Nary (v,def)) -> "\\"^(Ident.name v)^"."^(defToString def)

  let toString = fun (T {id;def}) -> "primitive relation "
                                     ^(RelId.toString id)^" = "^(defToString def)

  let rec applySubsts def substs = match def with 
      (Nary (v,def))  ->  Nary (v, applySubsts def substs)
    |(Nullary rexpr) ->  Nullary (RelLang.applySubsts substs rexpr)

  let rec instantiate def substs = 
      match def with  
    	| (Nary (v, def), arg :: args) ->  instantiate (def,args) ((arg,v)::substs)
    	| (def, [])  -> applySubsts def  substs
    	| (_,_)  -> failwith "Invalid primitive relation instantiation"
(* 
	let instantiate = fun (def, args) -> instantiate (def, Vector.toList args) []
 *)
  let symbase = "pv_" 

  let count = ref 0 

  let genVar = fun _ ->
    let id = symbase ^ (string_of_int (!count)) in 
    let _ = count := !count + 1 in 
    Var.fromString id

  let rec alphaRename x y = match (x,y) with 
      ((Nary (v,def)), substs) -> 
        let newV = genVar () in 
        Nary (newV, alphaRename def ((newV,v)::substs))
    | ((Nullary rexpr), substs) ->	Nullary (RelLang.applySubsts
                                              (substs) rexpr)

  let alphaRename =fun def -> alphaRename def []

end
module TyDBinds = struct
  module Key = struct
    type t = Var.t
    (*let layout = L.str <<  Var.toString (*Create a Layout Module*)*)
    let equal (v1, v2) = (Var.toString v1) = (Var.toString v2)
  end

  module Value = struct 
    type t = TyD.t
    let equal (v1, v2) = TyD.sametype v1 v2     
    (*let layout = fun x -> x*) 

  end 
  
  module TydMap = Applicativemap.ApplicativeMap (Key) (Value)
  type t = TydMap.t
  let mem = TydMap.mem 
  let find = TydMap.find
  let add = TydMap.add
  let empty = TydMap.empty




  exception KeyNotFound = TydMap.KeyNotFound

end

module TyDB = TyDBinds


(*Predicates*)
module Predicate = 
struct
  exception RelPredicateException of string

  

  (*submodule *)
  module BasePredicate = struct
    open Helper    
    type expr = Int of int
              | Bool of bool
              | Str of string   
              | Var of Var.t
    type t =  Iff of t * t
           | Eq of expr * expr
           | Gt of expr * expr

    let exprToString e = 
        match e with 
        Int i -> (string_of_int i)
        | Bool b -> (string_of_bool b)
        | Str s -> "<"^s^">" 
        | Var v -> (Var.toString v)
    
    (*TODO implement full*)
    let rec footprint ( bp : t) : (Var.t list) = 
        match bp with 
         | Iff (t1, t2) -> []
         | Eq (t1, t2) -> []
         | Gt (t1, t2) -> []


    let rec toString bp = match bp with
        Eq (Int i1,Int i2) -> (string_of_int i1) ^ " = " 
                              ^ (string_of_int i2)
      | Eq (Bool b1,Bool b2) -> (string_of_bool b1) ^ " = " 
                                ^ (string_of_bool b2)
      | Eq (Var v1, Var v2) -> (Var.toString v1) ^ " = " 
                               ^ (Var.toString v2)
      | Eq (Var v, Bool b) -> (Var.toString v) ^ " = " 
                              ^ (string_of_bool b)
      | Eq (Var v, Int i) -> (Var.toString v) ^ " = " 
                              ^ (string_of_int i)
      | Eq (e1, e2) -> (exprToString e1)^" = "^(exprToString e2)  
      | Iff (t1,t2) -> (toString t1) ^ " <=> " ^ (toString t2) 
      | Gt ( t1, t2) -> (exprToString t1) ^  " > "^(exprToString t2)   
        
    let varEq (v1, v2) = Eq (Var v1, Var v2)
    let varBoolEq (v,b) = Eq (Var v, Bool b)
    let varIntEq (v, i) = Eq (Var v, Int i)
    let varGt (v1, v2) = Gt (Var v1, Var v2) 
    let varIntGt (v1, i) = Gt (Var v1, Int i)    
    let varStrEq (v1, s) = Eq (Var v1, Str s)
               

    let rec  applySubst subst t = 
      let varSubst = varSubs subst in 
      match t with 
      |Eq (Var v1, Var v2) -> Eq (Var (varSubst v1), Var (varSubst v2))
      | Eq (Var v, e) -> Eq (Var (varSubst v), e)
      | Eq (e, Var v) -> Eq (e, Var  v)
      | Iff (t1,t2) -> Iff (t1, t2)
      | Gt (Var v1, Var v2) -> Gt (Var (varSubst v1), Var (varSubst v2))
      | Gt (Var v, e) -> Gt (Var (varSubst v), e)
      | Gt (e, Var v) -> Gt (e, Var  v)
       


  end 
  (*submodule*)
  module RelPredicate = struct

    type expr = RelLang.expr
    type t = 
           | NEq of expr * expr (*numeric equality*)       
           | Eq of expr * expr
           | Sub of expr * expr
           | SubEq of expr * expr
           | Grt of expr * expr
           | Q of expr              
    let rec footprint (rp : t) = []

    let toString rp = match rp with

        Eq (e1,e2) -> (RelLang.exprToString e1) ^ " = "
                      ^ (RelLang.exprToString e2)
      | Sub (e1,e2) -> (RelLang.exprToString e1) ^ " C "
                       ^ (RelLang.exprToString e2)
      | SubEq (e1,e2) -> (RelLang.exprToString e1) ^ " C= "
                         ^ (RelLang.exprToString e2)
      | Grt (e1,e2) -> (RelLang.exprToString e1) ^ " > "
                              ^ (RelLang.exprToString e2)
      | NEq (e1, e2)->   (RelLang.exprToString e1) ^ " =="
                              ^ (RelLang.exprToString e2)
      | Q e -> ("Qualifier "^(RelLang.exprToString e))  
    
   let exprMap rp f = match rp with 
        Eq (e1,e2) -> Eq (f e1, f e2)
      | Sub (e1,e2) -> Sub (f e1, f e2)
      | SubEq (e1,e2) -> SubEq (f e1, f e2)
      | Grt (e1,e2) -> Grt (f e1, f e2)

      |  NEq (e1,e2) -> NEq (f e1, f e2)
      | Q e -> Q (f e)

   let applySubst subst t = exprMap t (RelLang.applySubsts ( [subst]))

   let mapTyD t f = 
      let g = RelLang.mapTyD in 
      let doIt = fun (x1,x2)  -> ((g x1 f), (g x2 f)) in

      match t with 
        Eq (x,y) -> let (x1, y1) = doIt (x, y) in  
          Eq (x1, y1)
      | Sub (x,y) -> 
          let (x1, y1) = doIt (x, y) in   
          Sub  (x1,y1)
      | SubEq (x,y) -> 
          let (x1, y1) = doIt (x, y) in   
          SubEq (x1,y1)
      |  Grt (x,y) -> let (x1, y1) = doIt (x, y) in  
          Grt (x1, y1)
      |  NEq (x,y) -> let (x1, y1) = doIt (x, y) in  
          NEq (x1, y1)
      | Q e -> let (e1, e2)  = doIt (e, e) in (Q e1)    
    
    let mapSVar t f = 
      let  g = RelLang.mapSVar in 
      let doIt = fun (x1,x2) -> (g x1 f, g x2 f) in 
      match t with 
        Eq (x,y) -> let (x1, y1) = doIt (x, y) in  
          Eq (x1, y1)
      | Sub (x,y) -> 
          let (x1, y1) = doIt (x, y) in   
          Sub  (x1,y1)
      | SubEq (x,y) -> 
          let (x1, y1) = doIt (x, y) in   
          SubEq (x1,y1)
      |   Grt (x,y) -> let (x1, y1) = doIt (x, y) in  
          Grt (x1, y1)
      | NEq (x,y) -> let (x1, y1) = doIt (x, y) in  
          NEq (x1, y1)
      | Q (e) -> let (e1, e2) = doIt (e, e) in (Q e1 )  
  end 
(*main type for the module*)
type t = True 
         |  False
         |  Base of BasePredicate.t 
         |  Rel of RelPredicate.t
         |  Exists of TyDBinds.t * t
         |  Not of t
         |  Conj of t * t
         |  If of t * t
         |  Iff of t * t
         |  Disj of t * t
         |  Dot of t * t
         | Forall of TyDBinds.t * t 

let list_disjunction (ls: t list)  : t =  
        List.fold_left (fun acct disj -> (Disj (acct, disj))) (False)  ls 


let list_conjunction (ls : t list) : t =  
        List.fold_left (fun acct conj -> (Conj (acct, conj))) (True)  ls 


(*create a invariant h h'
*       \Forall h, v, h'. h' = h*)
        
let heap_inv_predicate (result : (Var.t*TyD.t))  : t  = 
        let h_ident = Var.fromString "h" in 
        let h'_ident = Var.fromString "h'" in 
        let v_indet = Var.fromString "v" in 
        let bvs = [(h_ident, TyD.Ty_heap);
                   (result);
                   (h'_ident, TyD.Ty_heap)] in 
        let inv=  Forall (bvs, Rel (RelPredicate.Eq ((RelLang.V (RelLang.Var (Ident.create "h")),RelLang.V (RelLang.Var (Ident.create "h'")))))) in 
        inv 

let getForAllTrue (bvs : TyDBinds.t) : t =  
        Forall (bvs, True)

(*splits_h_h1_h2*)
let heap_splits_predicate (heapfull : Var.t) (heapfrag1 : Var.t) (heapfrag2 : Var.t) : t = 
       let _dom_full = RelLang.MultiR ( (RelLang.instOfRel (RelId.fromString "dom")), [(heapfull)]) in 
       let _dom_h1 =  RelLang.MultiR ( (RelLang.instOfRel (RelId.fromString "dom")), [(heapfrag1)]) in 
       let _dom_h2 =  RelLang.MultiR ( (RelLang.instOfRel (RelId.fromString "dom")), [(heapfrag2)]) in 
        
       (*disjoint h1 h2*) 
        let _union_h_h1_h2 =  
          Rel (RelPredicate.Eq (RelLang.U (_dom_h1, _dom_h2 ), _dom_full)) in 
        let _disjoint_h_h1_h2 = 
           Rel (RelPredicate.Eq (RelLang.D (_dom_full, _dom_h1), _dom_h2)) in 
        
        let _splits_h1_h2 = Conj (_union_h_h1_h2, _disjoint_h_h1_h2) in 
  
         _splits_h1_h2 

let heap_preserve frame pre post = 
        True
(*let heap_frame_h (h_frame : Var.t) (h_initial : Var.t) (h_final : Var.t) : t 
        (*\forall x in dom (h_frame) sel h_final x  = sel h_initial x*
         * 
        (*frame h2 h h_int
         *x in dom h  ~  (dom h - {(x)}) C dom h *)

         *)
         let _dom_frame =  MultiR ( (RelLang.instOfRel (RelId.fromString "dom")), [(h_frame)]) in 
        
        (*{(x)}*)
         let _bound_x = Var.get_fresh_var "x" in 
         let x_tuple = RelLang.T [(_bound_x)] in 
         let _x_in_dom_h_frame  = 
           RelPredicate.Subset((RelLang.D (_dom_frame, x_tuple)), _dom_frame)  in 
        
         let sel_eq_init_finlal =  (RP.Eq ( MultiR ( (RelLang.instOfRel (RelId.fromString "sel")), [(_h_initial); (_bound_x)]),
                 MultiR ( (RelLang.instOfRel (RelId.fromString "sel")), [(_h_final); (_bound_x)])) in 
         (**)
        let frame_pred = P.Forall  
*)        

let rec footprint (phi: t) : (Var.t list) = 
     match phi  with 
        True -> [] 
      | False -> [] 
      | Base bp -> (BasePredicate.footprint bp)
      | Rel rp -> (RelPredicate.footprint rp )
      | Exists (binds,t) ->
                footprint t
      | Not t -> footprint t 
      | Conj (e1,e2) ->  List.append (footprint e1) (footprint e2)
      | Disj (e1,e2) ->   List.append (footprint e1) (footprint e2)
      | If (e1,e2) ->  List.append (footprint e1) (footprint e2)
      | Iff (e1,e2) ->   List.append (footprint e1) (footprint e2)
      | Dot (e1,e2) ->   List.append (footprint e1) (footprint e2)
      | Forall (binds,t) ->
                footprint t
   

let rec dropBvs t = 
        match t with 
        | Forall (tyds, t1) -> dropBvs t1 
        | Exists (tyds, t1) -> dropBvs t1
        | _ -> t

let rec get_dot_locals t = 
        match t with 
       | Dot (t1, t2) ->  (t1, t2)
       | Not t -> (True, t)
       | Conj (e1,e2) -> let (t1, t1') = get_dot_locals e1 in 
                                let (t2, t2') = get_dot_locals e2 in 
                                 (Conj (t1 ,t2), Conj(t1', t2')) 
       | Disj (e1,e2) -> let (t1, t1') = get_dot_locals e1 in 
                                let (t2, t2') = get_dot_locals e2 in 
                                (Conj (t1 ,t2), Disj(t1', t2')) 
      
        | _ -> (True, t) 
let rec getBVs t = 
        match t with 
        | Forall (binds, t) -> binds
        | _ -> [] 

        
let rec toString t = match t with
        True -> "true" 
      | False ->  "false" 
      | Base bp -> (BasePredicate.toString bp)
      | Rel rp -> (RelPredicate.toString rp )
      | Exists (binds,t) ->
                        let _exists_ = "Exists \n \t" in 

                        let bindstr = List.fold_left (fun acc (k,v) -> (acc^ "\n Key ="^(Var.toString k)^" Value = "^(TyD.toString v))) " " binds in 

                       let _t_string = toString t in 
                        let _predicate = (_exists_^(bindstr)^"{ "^(_t_string)^" }") in 
                        _predicate

      | Not t -> ("Not "^(toString t))
      | Conj (e1,e2) -> ("\n Conj <c "^(toString e1 )^"\n \t , "^(toString e2)^" >c ")
                      
      | Disj (e1,e2) ->  ("Disj \n  "^(toString e1 )^"\n  "^(toString e2))
      
      | If (e1,e2) -> ("\n Impl < "^(toString e1 )^"\n \t "^(toString e2)^" >"  )

      | Iff (e1,e2) ->  ("DoubleImpl \n "^(toString e1 )^"\n  "^(toString e2))

      | Dot (e1,e2) ->  ("Dot "^(toString e1 )^", "^(toString e2))

      | Forall (binds,t) ->
                        let _for_all = "Forall \n \t" in 
                        let bindstr = List.fold_left (fun acc (k,v) -> (acc^ "\n Key ="^(Var.toString k)^" Value = "^(TyD.toString v))) " " binds in 
                        let _t_string = toString t in 
                        let _predicate = (_for_all^(bindstr)^"{ "^(_t_string)^" }") in 
                        _predicate


  let truee  _ = True
  let falsee _ = False 
  let isFalse e = match e with 
      False -> true | _ -> false
  let baseP p = Base p 
  let conj (t1, t2) = Conj (t1, t2)
  let conjR (t, r) = Conj (t, Rel r)
  let conJP (t,p) = Conj (t, Base p)

  let rec applySubst ((nw, ol) as subst) t = 
        match t with 
      True -> True
    | False -> False
    | Base bp ->
          Base (BasePredicate.applySubst subst bp)
    | Rel rp ->
         Rel (RelPredicate.applySubst subst rp)
    | Exists (tyDB,t) -> 
        if (TyDBinds.mem tyDB ol)
        then let expstr = ("Attempted substitution "^(Ident.name nw)^"  on existentially quantified variable "^(Ident.name ol)) in 
            raise (RelPredicateException expstr) 
        else Exists (tyDB,applySubst subst t)
    | Not t -> Not (applySubst subst t )
    | Conj (t1,t2) -> Conj (applySubst subst t1, applySubst subst t2)
    | Disj (t1,t2) -> Disj (applySubst subst t1, applySubst subst t2)
    | If (t1,t2) ->
          If (applySubst subst t1, applySubst subst t2)
    | Iff (t1,t2) ->
        Iff (applySubst subst t1, applySubst subst t2)
    | Dot (t1,t2) -> Dot (applySubst subst t1, applySubst subst t2)
    | Forall (tyDB,t) -> 
        if (TyDBinds.mem tyDB ol)
        then let expstr = ("Attempted substitution "^(Ident.name nw)^"  on existentially quantified variable "^(Ident.name ol)) in 
            raise (RelPredicateException expstr) 
        else Forall (tyDB,applySubst subst t)
   
 let rec reduce ((nw, ol) as subst) t = 
    match t with 
      True -> True
    | False -> False
    | Base bp ->
          Base (BasePredicate.applySubst subst bp)
    | Rel rp ->
         Rel (RelPredicate.applySubst subst rp)
    | Exists (tyDB,t) -> 
        (applySubst subst t)
    | Not t -> Not (applySubst subst t )
    | Conj (t1,t2) -> Conj (applySubst subst t1, applySubst subst t2)
    | Disj (t1,t2) -> Disj (applySubst subst t1, applySubst subst t2)
    | If (t1,t2) ->
          If (applySubst subst t1, applySubst subst t2)
    | Iff (t1,t2) ->
        Iff (applySubst subst t1, applySubst subst t2)
    | Dot (t1,t2) -> Dot (applySubst subst t1, applySubst subst t2)
    | Forall (tyDB,t) ->
         (applySubst subst t)
  
  let rec reduceMany substs t = 
    List.fold_right (fun subst t ->
        reduce subst t) substs t 


  (* telescoped substitutions *)
  let rec applySubsts substs t = 
    List.fold_right (fun subst t ->
        applySubst subst t) substs t 

  let exists (tyb,t) = Exists (tyb,t)

  let dot (t1,t2) = Dot (t1,t2)

  let disj (t1, t2) = Disj (t1,t2)
  
  let rec mapRP t f = match t with  
      Rel rp -> Rel (f rp)
    | Exists (tyDB,t) -> Exists (tyDB, mapRP t f)
    | Not t -> Not (mapRP t f)
    | Conj (t1,t2) -> Conj (mapRP t1 f, mapRP t2 f)
    | Disj (t1,t2) -> Disj (mapRP t1 f, mapRP t2 f)
    | If (t1,t2) -> If (mapRP t1 f, mapRP t2 f)
    | Iff (t1,t2) -> Iff (mapRP t1 f, mapRP t2 f)
    | Dot (t1,t2) -> Dot (mapRP t1 f, mapRP t2 f)
    | Forall (tyDB,t) -> Forall (tyDB, mapRP t f)
    | _ -> t 

  let rec mapTyD t f = match t with 
      Rel rp -> Rel (RelPredicate.mapTyD rp f)
    | Exists (tyDB,t) -> Exists (TyDBinds.TydMap.map  
                                   (fun (v,tyd) -> (v,f tyd)) tyDB, mapTyD t f)
    | Forall (tyDB,t) -> Forall (TyDBinds.TydMap.map  
                                   (fun (v,tyd) -> (v,f tyd)) tyDB, mapTyD t f)
   
    | Not t -> Not (mapTyD t f)
    | Conj (t1,t2) -> Conj (mapTyD t1 f, mapTyD t2 f)
    | Disj (t1,t2) -> Disj (mapTyD t1 f, mapTyD t2 f)
    | If (t1,t2) -> If (mapTyD t1 f, mapTyD t2 f)
    | Iff (t1,t2) -> Iff (mapTyD t1 f, mapTyD t2 f)
    | Dot (t1,t2) -> Dot (mapTyD t1 f, mapTyD t2 f)
    | _ -> t

  let mapsSVar t f = mapRP t (fun rp  -> RelPredicate.mapSVar rp f)

  let rec get_bounded_vars (p:t) = 
   match p with 
       True -> []
        | False  -> []
        | _ -> raise (Unimplemented "Predicate.get_bounded_var ")

  let first_pred (_pred : t) = 
     match _pred with 
       | Conj (p1, p2) -> p1
       | _ -> raise (Error "First defined only for a Conjunction") 


  let rest_pred (_pred :t) = 
     match _pred with 
       | Conj (p1, p2) -> p2
       | _ -> raise (Error "Rest defined only for a Conjunction") 


  let pred_conjunction (_pred_list : t list) = 
          List.fold_left (fun conjunct p -> Conj (conjunct, p)) (True) _pred_list  


(*{v : tau | pred} {v : tau | v = Inl x /\ pred x*)
  let exc_success_predicate (result : (Var.t * TyD.t)) (pred : t) : t = 
        let (result_var, result_ty) = result in 
        let _x_ident = Var.get_fresh_var "x" in 
        (*get an expression Inl x*)        
        let _Inl_x_expr = RelLang.relationInstantiationExp "Inl" "x" in 
        let _v_eq_inl_x = Rel (RelPredicate.Eq (RelLang.V (RelLang.Var(Ident.create (Var.toString result_var)))
                                                , _Inl_x_expr)) in  
        let pred_of_x = applySubst (_x_ident, result_var) pred in 
        let exc_predicate = Conj(_v_eq_inl_x, pred_of_x) in 
        exc_predicate

 (*TODO Later 
* let nondet_predicate (result : (Var.t * TyD.t) (pred:Predicate.t) : t = 
*)
        



end

module P = Predicate

(*define a lattice here*)
module Effect = struct 
     type t = 
        | Pure 
        | Exc
        | State 
        | StExc 
        | Nondet 
        | StNondet 
        | ExNondet 
        | ALL

     let fromString se = 
        match se with 
        | "Pure" -> Pure 
        | "Exc" -> Exc 
        | "State" -> State
        | "StExc" -> StExc
        | "Nondet" -> Nondet
        | "All" -> ALL

     let  toString t = 
       match t with  
        | Pure -> "Pure"
        | Exc -> "Exc"
        | State -> "State"
        | StExc  -> "StateExc"
        | Nondet -> "Nondet"
        | StNondet -> "StNondet"
        | ExNondet -> "ExNondet"
        | ALL -> "All"


      (* lattice : A more elegant way will be to define the order formally and then defined 
*       a lub function, however in this case, the following enumeration sufficies*)
     (*type lattice = {bot = Pure, top = ALL }*)   

       let equall t1 t2 = 
                (toString t1) = (toString t2) 
        
       let lub t1 t2 =  
        if (equall t1 t2) then t1 
        else 
                match (t1, t2) with 
                | (Pure , _) -> t2 
                | (ALL, _) -> ALL
                | (_, Pure) -> t1
                | (_, ALL) -> ALL 
                | (State,Exc) -> StExc
                | (StExc, State) 
                | (StExc, Exc)
                | (Exc, StExc) 
                | (State, StExc) -> StExc
                | (State,Nondet) -> StNondet
                | (StNondet, State) 
                | (StNondet, Nondet)
                | (Nondet, StNondet) 
                | (State, StNondet) -> StNondet
                | (Nondet,Exc) -> ExNondet
                | (ExNondet, Exc) 
                | (ExNondet, Nondet)
                | (Exc, ExNondet) 
                | (Nondet, ExNondet) -> ExNondet
                | (_, _) -> ALL 


 


       end 



(*A module defining the refinement types *)
module RefinementType = 
struct 
  exception RefTyEx of string 
  type t = 
      Base of Var.t * TyD.t * Predicate.t 
    | Tuple of (Var.t * t) list
    | Arrow of (Var.t * t) * t
    (*Additional Computation type, the return type is TyD.t rather that RefTy.t as any constraint on the return value is defined in the post predicate*)    
    | MArrow of Effect.t * (Predicate.t)  * TyD.t * (Predicate.t) (*pre x:\tau post*)           
    (*get the effect from the Monadic types*)    
    


   let rec get_effect t : Effect.t = 
        match t with 
        | MArrow (e1, _,_,_) -> e1 
        | Arrow ((arg, argty), body) -> get_effect body
        | _ -> Effect.Pure 

   let rec toString rty = match rty with 
        Base(var,td,pred) -> ("Base {" ^ (Var.toString var)^ ":" ^ (TyD.toString td) ^(" | ")^(Predicate.toString pred))^"}" 
        (*| Tuple tv -> L.vector (List.rev (List.map (fun (v,t) ->  L.seq [L.str (Var.toString v); L.str ":"; layout t]) tv))*)
        | Arrow ((v1,t1),t2) ->  (" Arrow ( ( "^(Var.toString v1)^" , "^(toString t1)^" ),"^(toString t2)) 
| MArrow (eff, p1,t1,p2) -> ("MArrrow ( "^(Effect.toString eff)^" \n PRE { \n "^(Predicate.toString p1)^(" \n } \n RET :  ")^(TyD.toString t1)^" \n { POST "^(Predicate.toString p2)^" \n } \n )")

   let rec getBodyType t = 
        match t with 
           | MArrow (_,_,_,_) -> t 
           | Arrow ((v,ta),tb) -> getBodyType tb 
           | _ -> t

   (*least effect of types*)
   let lub_effects (ty1:t) (ty2:t) : Effect.t = 
        Effect.lub (get_effect ty1) (get_effect ty2)

   (*define lifting function from each lower type to upper types*)

  (*define lifting from pure --> state *)      
   let rec liftState (lower : t) : ( t ) = 
        match lower with
         (*This case will never be encountered
          * If the lower is a normalized Pure of the form Pure {True} t {}*)
         MArrow (e, pre, result_ty, post ) ->
                (**)
                let result_var = (Var.get_fresh_var "v") in 

                (match e with
                  | Effect.Pure -> 
                                let _default_pre = Predicate.True in 
                                let _default_post = Predicate.heap_inv_predicate (result_var, result_ty) in 
                                MArrow (Effect.State, _default_pre, result_ty, _default_post)
                  | _ -> (*Just resturn the same type*)lower      
                ) 


                                
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftState resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post_0 = Predicate.heap_inv_predicate (v, basety) in 
                                let  _default_post = Predicate.Conj (_default_post_0, pred) in 
                                MArrow (Effect.State, _default_pre, basety, _default_post) 

        | _ -> raise (Error "Unhandled Lifting") 

   (*define lifting from pure --> Exc *)      
    let rec liftExc (lower : t) : ( t ) = 
        match lower with
         (*If the lower is a normalized Pure of the form Pure {True} t {}*)
                                        
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftExc resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post = Predicate.exc_success_predicate (v, basety) pred in 
                                MArrow (Effect.Exc, _default_pre, basety, _default_post) 

        | _ -> raise (Error "Unhandled Lifting from ") 



    (*define lifting from pure --> Nondet *) 

   (*TODO Expand later*)     
    let liftNondet (lower : t) : ( t ) =  lower
      (*  match lower with
                                        
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftNondet resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post_0 = Predicate.nondet (v, basety) in 
                                let  _default_post = Predicate.Conj (_default_post_0, pred) in 
                                MArrow (Effect.Nondet, _default_pre, basety, _default_post) 

        | _ raise (Error "Unhandled Lifting from ") 
       *)
  (*define lifting from ST --> StExc and Exc --> STExc and Pure --> STExcp *)      
    let rec liftStExc (lower : t) : ( t ) = 
        match lower with
         (*If the lower is a normalized Pure of the form Pure {True} t {}*)
         MArrow (e, pre, result_ty, post ) ->
                (**)
                let result_var = (Var.get_fresh_var "v") in 

                (match e with
                  | Effect.State -> (*let lower = State {pre} t  {\h v h'. \post} lift to StExc {pre} t {\h v h'. v = Inl x /\ post x*)
                                let _lifted_post = Predicate.exc_success_predicate (result_var, result_ty) post in 
                                MArrow (Effect.StExc, pre, result_ty, _lifted_post) 


                  | Effect.Exc -> (*let lower =  Exc {pre} t  {\post} lift to StExc {pre} t {\h v h'.  post v /\ Inv h h'*)
                                let bound_vars_post = Predicate.getBVs post in 
                                 (match bound_vars_post with 
                                  | [(v,vty)] ->   let _default_state_inv_pred = Predicate.heap_inv_predicate (v, vty) in 
                                                   let _lifted_post = Predicate.Conj(post, _default_state_inv_pred) in 
                                                   MArrow (Effect.StExc, pre, result_ty, _lifted_post)
                                  | [] -> 
                                        let fresh_result_var = Var.get_fresh_var "v" in 
                                        let _default_state_inv_pred = Predicate.heap_inv_predicate (fresh_result_var, result_ty) in 
                                        let _lifted_post = Predicate.Conj(post, _default_state_inv_pred) in 
                                        MArrow (Effect.StExc, pre, result_ty, _lifted_post)

                                  | _ -> raise (Error ("Lifting for a Exc to STExc with mutiple bounded vars not implemented"))
                                 )
        
                 | _ -> (*Just resturn the same type*)lower      
                ) 


        (*Pure to StExc lifting*)                        
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftStExc resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                (*pick from pure to ST and then from at to STExc*)
                                let lifted_in_st = liftState lower in
                                liftStExc lifted_in_st


        | _ -> raise (Error "Unhandled Lifting from ") 

 

  (*define lifting from pure --> Nondet *)      
    let liftExNondet (lower : t) : ( t ) =  lower
   (*     match lower with
         (*If the lower is a normalized Pure of the form Pure {True} t {}*)
         MArrow (e, pre, result_ty, post ) ->
                (**)
                let result_var = (Var.get_fresh_var "v") in 

                (match e with
                  | Effect.Nondet -> (*TODO*)
                                let _default_pre = Predicate.True in 
                                let _default_post = Predicate.nondet (result_var, result_ty) in 
                                MArrow (Effect.Nondet, _default_pre, result_ty, _default_post)
                  | Effect.Exc -> 


        
                 | _ -> (*Just resturn the same type*)lower      
                ) 


                                
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftNondet resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post_0 = Predicate.nondet (v, basety) in 
                                let  _default_post = Predicate.Conj (_default_post_0, pred) in 
                                MArrow (Effect.Nondet, _default_pre, basety, _default_post) 

        | _ raise (Error "Unhandled Lifting from ") 

 *)

  (*define lifting from pure --> Nondet *)      
    let liftStNondet (lower : t) : ( t ) = lower 
       (* match lower with
         (*If the lower is a normalized Pure of the form Pure {True} t {}*)
         MArrow (e, pre, result_ty, post ) ->
                (**)
                let result_var = (Var.get_fresh_var "v") in 

                (match e with
                  | Effect.St -> (*TODO*)
                                let _default_pre = Predicate.True in 
                                let _default_post = Predicate.nondet (result_var, result_ty) in 
                                MArrow (Effect.Nondet, _default_pre, result_ty, _default_post)
                  | Effect.Nondet -> 


        
                 | _ -> (*Just resturn the same type*)lower      
                ) 


                                
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftNondet resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post_0 = Predicate.nondet (v, basety) in 
                                let  _default_post = Predicate.Conj (_default_post_0, pred) in 
                                MArrow (Effect.Nondet, _default_pre, basety, _default_post) 

        | _ raise (Error "Unhandled Lifting from ") 

        *)


  (*define lifting from pure --> Nondet *)      
    let liftAll (lower : t) : ( t ) =  lower 
       (* match lower with
         (*If the lower is a normalized Pure of the form Pure {True} t {}*)
         MArrow (e, pre, result_ty, post ) ->
                (**)
                let result_var = (Var.get_fresh_var "v") in 

                (match e with
                  | Effect.St -> (*TODO*)
                                let _default_pre = Predicate.True in 
                                let _default_post = Predicate.nondet (result_var, result_ty) in 
                                MArrow (Effect.Nondet, _default_pre, result_ty, _default_post)
                  | Effect.Exc -> 

                  | Effect.Nondet ->
                  | Effect.StExc ->

                  | Effect.StNondet -> 
                  | Effect.ExcNondet -> 
                  

        
                 | _ -> (*Just resturn the same type*)lower      
                ) 


                                
        |  Arrow ((v, argty), resty) -> (*(x:t) -> {v : ty | pred}*)
                                let _lifted_resty = liftNondet resty in 
                                Arrow ((v, argty), _lifted_resty)
        | Base (v, basety, pred) -> 
                                let _default_pre = Predicate.True in 
                                let _default_post_0 = Predicate.nondet (v, basety) in 
                                let  _default_post = Predicate.Conj (_default_post_0, pred) in 
                                MArrow (Effect.Nondet, _default_pre, basety, _default_post) 

        | _ raise (Error "Unhandled Lifting from ") 
*)
 
        (*polymorphic lifting of type*)
    let liftM (lower : t) (target: Effect.t ) : t = 
        let m1 = get_effect lower in 
        if (Effect.equall m1 target) then 
                let () = Printf.printf "%s" ("\n Equall effects no lifting needed "^(Effect.toString m1)^" == "^(Effect.toString target)) in 
                lower 
        else 
                ( match (m1, target) with 
                  | (Effect.Pure, Effect.State) -> liftState lower
                  | (Effect.Pure, Effect.Exc) -> liftExc lower
                  | (_, Effect.StExc) -> liftStExc lower 
                  | (_, _) -> raise (Error ("Unhandled lifting for "^(toString lower)))
                )
                
                  




     
  (*Additional functions for MArrow *)
  let precondition (_mArrow  : t)  =
     match _mArrow with 
       | MArrow (eff, pre, b, post) -> pre 
       | _ -> raise (Error "precondition defined for a MArrow type only")

                      
  let postcondition (_mArrow  : t)  =
     match _mArrow with 
       | MArrow (eff, pre, b, post) -> post 
       | _ -> raise (Error "postcondition defined for a MArrow type only")

 (* lift_base : basety -> ty*)
  let lift_base bt = 
      Base ("noname", bt, True)



    (* Records are tuples with fixed bound var *)
  (* Needs extension for {'a | r} list *)


  let symbase = "v_" 
  let count = ref 0
  let genVar = fun _ ->
    let id = symbase ^ (string_of_int !count) in 
    let _  = count := !count + 1 in 
    Var.fromString id	
    (*currently there i sonly one type variable 'a*)
  let emptyVar () = Var.fromString ""    


  (*TODO Relook at this function, what should differentuate between a computation and a function type 
*       We can drop the dependent function type or can use them for typing pure computations like Constructors*)      
  let rec fromTyD tyD = 
    let open TyD in 
    match tyD with 
      Ty_arrow (td1,td2) ->
        (*TODO do we need empty var here
*        the type is (x:\tau) -> tau*)
        Arrow ( (emptyVar (), fromTyD td1),
               fromTyD td2)
  
    |  tyD -> Base (genVar(), tyD, Predicate.truee())
   
   let rec toTyD t = match t with
        Base (v,tdes,p) -> tdes
      (*| Tuple tv -> TyD.makeTtuple (List.map (fun (v,t) ->  
              let ty_desc_for_t = toTyD t in 
              ty_desc_for_t)  tv)*)
      | Arrow ((v1,t1),t2) -> TyD.Ty_arrow ((toTyD t1), (toTyD t2))
      | MArrow (eff, p1 , tb, p2) -> TyD.Ty_arrow (Ty_unit, tb)  
     
 
  let compare_types (t1:t)  (t2 :t) : bool = 
        TyD.sametype (toTyD t1) (toTyD t2) 
    
 
  let  rec mapBaseTy t f = match t with
      Base (v,t,p) -> 
        (* let () = Printf.printf "%s" "\nBase substs" in 
         *)let (x,y,z) = f (v,t,p) in 
        Base (x,y,z)
    | Tuple tv -> 
     (*  let () = Printf.printf "%s" "\nTuple substs" in 
      *)   Tuple (List.map (fun (v,t) -> 
        (v,mapBaseTy t f)) tv)
    | Arrow ((v1,t1),t2) ->
     (*      let () = Printf.printf "%s" "\nArrow substs" in 
      *)      Arrow ((v1,mapBaseTy t1 f), 
                                   mapBaseTy t2 f)

  let mapTyD t f = mapBaseTy t (fun (v,t,p) -> 
      (v,f t, P.mapTyD p f)) 

  
  let rec applySubsts substs refty = 
	   mapBaseTy refty (fun (bv,t,pred) ->
	   (* if List.exists (fun(n,ol) -> 
          let () = Printf.printf "%s" ("Matching Replaced "^(Var.toString ol)) in 
          varStrEq (ol,bv)) substs 
				then  raise (RefTyEx ("Attempted substitution of bound var "))
				else  *)(bv,t,Predicate.applySubsts substs pred))

  let  alphaRenameToVar refty newbv = match refty with
      Base (bv,t,p) -> Base (newbv,t,
                             (Predicate.applySubst (newbv,bv) p))
    | _ -> raise (RefTyEx "alphaRename attempted on non-base type")

  let alphaRename refty = alphaRenameToVar refty (genVar())


  let exnTyp = fun _ -> Base (genVar(),TyD.Ty_unit,
                              Predicate.falsee())

  let mapSVar t f = mapBaseTy t (fun (v,t,p) ->
     							(v,t, (Predicate.mapsSVar p f)))

     				
  let newLongVar = fun (var,fld) -> Var.fromString( 
        (Var.toString var)^"."^(Var.toString fld))
    
           (*
				     * Decomposes single tuple bind of form v ↦ {x0:T0,x1:T1} to
				     * multiple binds : [v.x0 ↦ T0, v.x1 ↦ T1]
				     *)
  
  let rec decomposeTupleBind (tvar , (Tuple refTyBinds) as tty) =
     					
              let  bindss = List.map (fun ((_,refTy) as refTyBind) -> 
      										match refTy with 
        											Tuple _ -> decomposeTupleBind refTyBind
      											| _ -> Vector.new1 refTyBind) 
     												refTyBinds in 
     				let binds = List.map (fun (v,ty) -> (newLongVar (tvar,v), ty)) (List.concat bindss) in 
     		     			binds
  

  let uncurry_Arrow (arrowty) =
    let Arrow ((_, frstargTy), res) = arrowty in  
      
      let rec get_params ty params resTy  = 
        match ty with
          | Arrow ((arg, argTy) as argBind, remainingTy)  ->
            let params' = (argBind :: params) in 
                get_params remainingTy params' resTy 

          | _ -> (params, ty)
    in 
    let (parametersTyBind, resTy ) =  get_params arrowty [] res in
     (List.rev parametersTyBind, resTy)
 
end

module RefTy = RefinementType 

module RelSpec = struct 
  module TypeSpec =
    struct
      type t = T of {isAssume : bool;
                   name:Var.t;
                   params: RelId.t list;
                   refty : RefinementType.t}
        let toString  = fun (T{name;params;refty;isAssume}) ->
         
                    let str = "Assume "^ (string_of_bool isAssume)^
                                   "\n name "^(Var.toString name) ^ " : " ^
       				   "\n params "^(Vector.toString RelId.toString params)^ 
       				   "\n Type "^(RefinementType.toString refty) in 
                                        str 
                
                     
   end
  module Formula = 
    struct
     type t = Form of {name: Var.t; 
                          pred: Predicate.t}

     let toString = fun (Form {name;pred}) -> ("Formula "^(Var.toString name)^" =  "^(Predicate.toString pred)) 


    end
  
  type t = T of {
                preds : Formula.t list;        
                reldecs : StructuralRelation.t list;
                 primdecs : PrimitiveRelation.t list;
                 typespecs : TypeSpec.t list}
   (*let layout = fun (T {reldecs;primdecs;typespecs;_}) ->
      				      let srs = Vector.toString (StructuralRelation.toString) (reldecs) in 
      				      let prs = Vector.toString (PrimitiveRelation.toString) (primdecs) in 
      				      let tslyt = L.align (Vector.toListMap (typespecs,
      				          TypeSpec.layout))
      				      in
      				        L.align [L.str srs; L.str prs; tslyt]

   let toString t = L.toString (layout t)   
   *)
   let toString t = 
        let T {reldecs;primdecs;typespecs;preds} = t in 
        let ps =  List.fold_left (fun psacc p -> (psacc^" \n "^(Formula.toString p))) " Formulas " preds in 
        let srs = List.fold_left (fun srsacc sr -> (srsacc^" \n "^(StructuralRelation.toString sr))) " SRs " reldecs in 
        let prs = List.fold_left (fun prsacc pr -> (prsacc^" \n "^(PrimitiveRelation.toString pr))) " PRs " primdecs in 
        let tss = List.fold_left (fun tsacc ts -> (tsacc^" \n "^(TypeSpec.toString ts))) " TSs " typespecs in 
        
       ("RelSpec { "^srs^"; "^prs^"; "^tss^"; "^ps^" }")
        
   let mk_empty_relspec () = T {
        preds = [];
        reldecs= [];
        primdecs = [];
        typespecs =[]}                
end

(*
module ParamRefType =  struct
  type t = T of {params : (RelId.t * SimpleProjSort.t) list; refty : RefinementType.t}

  let layout (T {params; refty}) = 
    let typedParamLyt (r,sprojty) = L.str  
        ((RelId.toString r) ^ " :: " ^
         (SPS.toString sprojty)) in 
    let paramslyt = 
      let consFun = fun x xs -> x :: xs in 
      List.fold_right (consFun) [] (List.map typedParamLyt params) in 
    let reftylyt = RefinementType.layout refty in 
    L.seq [(L.seq paramslyt); L.str ". "; reftylyt]

  let parametrize (sortedParams,refTy) = T {params=sortedParams; refty=refTy}

  let mapTyD (T {params;refty}) f = 
    let params' = List.map (fun (r,sps) -> (r, SPS.mapTyD sps f)) params  in 
    let refty' = RefTy.mapTyD refty f in
    T {params=params'; refty=refty'}

end

module PRf = ParamRefType

module RefinementSortScheme = struct
  type t = T of {svars: SVar.t list; prefty : ParamRefType.t }

  let layout (T {svars; prefty}) =  
    let svlyt = 
      let consFun  = fun x xs -> x :: xs in 
      List.fold_right (consFun) [] (List.map (fun sv -> L.str (SVar.toString sv)) svars) in 
    let prflyt = ParamRefType.layout prefty in 
    L.seq [(L.seq svlyt); L.str ". "; prflyt]

  let fromRefTy = fun refTy -> T {svars = empty(); prefty = ParamRefType.T {params=empty(); refty=refTy}}

  let toRefTy = fun (T {prefty = ParamRefType.T {refty;_} ;_}) -> refty

  let generalize = fun (svars,prefty) -> T {svars=svars; prefty=prefty}

  let mapTyD (T {svars;prefty}) f = T {svars=svars;prefty=PRf.mapTyD prefty f}

end

module RefSS = RefinementSortScheme

module RefinementTypeScheme =
struct
  type t = T of {tyvars : Tyvar.t list;
                 refss : RefinementSortScheme.t;
                 (* ICFP taking its toll What does this signify *)
                 isAssume : bool}

  let generalizeRefTy = fun (tyvars, refTy) ->
    T {tyvars = tyvars; refss = RefSS.fromRefTy refTy; 
       isAssume = false}

  let generalize = fun (tyvars, refss) ->
    T {tyvars = tyvars; refss = refss; isAssume = false}

  let generalizeAssump = fun (tyvars, refss, isAssume) ->
    T {tyvars = tyvars; refss = refss; isAssume = isAssume}

  let isAssumption = fun(T {isAssume;_}) -> isAssume

  let specialize = fun (T {tyvars;refss;_}) ->
    refss

  let specializeRefTy = fun (T {tyvars;refss;_}) ->
    RefSS.toRefTy refss

  let layout (T {tyvars;refss;isAssume}) =
    let flaglyt = (if isAssume then L.str "Assumption: " else
                     L.empty) in 
    let tyvlyt =
      let consFun = fun x xs -> x :: xs in  
      List.fold_right (consFun) [] (List.map (fun tyv ->
          L.str (Tyvar.toString tyv)) tyvars) in 
    let refsslyt = RefinementSortScheme.layout refss in 
    L.seq ( [flaglyt;( L.seq tyvlyt);refsslyt])

  let toString t = Layout.toString (layout t) 

  let instantiate (T{tyvars;refss;_},tydvec) =
    let len = List.length in 
    let _ = assert (len tyvars = len tydvec) in 
    let tyvmap = Vector.zip tydvec tyvars
            (*
		           * It is possible that we encounter a tyvar
		           * that is not generalized in this RefTyS.
		           * We do not panic.
		           *)
    in
    RefSS.mapTyD refss (TyD.instantiateTyvars tyvmap)
end

module  RefTyS = RefinementTypeScheme

module Bind = struct
  exception BindException of string 

  type transformer = Fr of Var.t list * RelLang.expr 
  type expr = Expr of {ground : RelId.t * TyD.t list * Var.t;
                       fr : transformer}

  type abs = Abs of Var.t * expr

  type def = 
      Def of  {tyvars : Tyvar.t list; params : RelId.t list; abs : abs}
    | BogusDef

  let symbase = "v_"

  let count = ref 0

  let genVar = fun _ -> 
    let id = symbase ^ (string_of_int (!count)) in 
    let _ = count := !count + 1
    in
    Var.fromString id 

  let frToString (Fr (vs,rexpr)) =
    let vsStr = Vector.toString Var.toString vs in 
    let reStr = RelLang.exprToString rexpr
    in
    "\\"^vsStr^". "^reStr

  let bindExprToString (Expr {ground = (r,tydv,x);fr}) =
    let tydStr = Vector.toString TyD.toString tydv in 
    let vStr = Var.toString x in 
    let gStr = (RelId.toString r)^" "^tydStr^" ("^vStr^")" in 
    let frStr = frToString fr in

    "bind ("^gStr^","^frStr^")"

  let absToString (Abs (v,bindex)) = 
    let bStr = bindExprToString bindex in
    "\\"^(Var.toString v)^". "^bStr

  let defToString definition = 
      match definition with  
     | (Def {tyvars;params=rs;abs}) ->
      let tyvStr = Vector.toString Tyvar.toString tyvars in 
      let absStr = absToString abs in 
      let rsStr = fun _ -> Vector.toString RelId.toString rs in
      
        (match Vector.length rs with 
          0 -> absStr
          | _ -> (tyvStr ^" \\"^(rsStr ())^". "^absStr))


    | BogusDef -> "-- NA --"

  let groundRelTyS pts = 
    let PTS.T {tyvars;sortscheme = PSS.T {sort = ProjSort.T 
                                              {paramsorts; sort=groundSort}; _}} = pts in 
    (* SVar to Tyvar map *)
    let svarMap = List.map (fun (SPS.ColonArrow (a, TS.Tuple [TS.S t])) -> (t,a)) paramsorts in 
    let mapSVar = fun t -> 
      match Vector.peekMap (svarMap, fun (t',a) -> if (SVar.eq t t') then Some a else None) with
        Some a -> a 
      | None -> raise (BindException "SVar impossible case") in 
    let SPS.ColonArrow (tyd,TS.Tuple tts) = groundSort in
    let tyds = List.map (fun tt -> match tt with  
          TS.S t -> TS.T ( mapSVar t )
        | _ -> tt) tts in 

    PTS.simple (tyvars, SPS.ColonArrow (tyd, TS.Tuple tyds))


  let makeGroundDef (params,rterm) : RelLang.term = 
    let open RelLang in 
    let  empty = fun _ -> Vector.new0 () in 
    let isParam = fun rid -> List.exists (fun p ->
        RelId.toString rid = RelId.toString p) params in 
    let rec doItExp exp = match exp with
        U (e1,e2) -> U (doItExp e1, doItExp e2)
      | X (e1,e2) -> X (doItExp e1, doItExp e2)
      | D (e1,e2) -> D (doItExp e1, doItExp e2)
      | R (RInst {rel;targs;sargs;args},x) -> if isParam rel 
          then RelLang.rId x
          else (R (RInst {rel=rel; targs=targs; sargs=empty();
                          args=empty()},x))
      | _ -> exp

    in
    match rterm with  
      Expr exp -> Expr ( doItExp exp )
    | Star (RInst {rel;targs;sargs;args}) -> Star (
        RInst {rel=rel; targs=targs; sargs=sargs; 
               args=empty()} )


  let makeBindDef (id,params,pts) : def =
    let PTS.T {sortscheme = PSS.T {sort = PS.T {paramsorts = 
                                                  paramSorts; sort=groundSort}; _}; tyvars} = pts in 

    (* SVar to RelId map *)

    let svarMap = List.map2 (fun (SPS.ColonArrow (_,TS.Tuple [TS.S t])) rid -> (t,rid)) paramSorts params  in 
  
    let mapSVar = fun t -> match Vector.peekMap (svarMap,  
                                                fun (t',rid) -> if (SVar.eq t t') then Some rid else None) with
      Some rid -> 
          rid 
    | None -> raise (BindException "No Bind definition found for ") in 
  
    let SPS.ColonArrow (_,TS.Tuple tts) = groundSort in 

    let () = Printf.printf "%s" ("\n Size of tts "^(string_of_int (List.length tts))) in 
 
    let (bvs,rApps) = Vector.unzip (List.map ( fun tt -> 
        let v = genVar () in 
        match tt with 
          TS.T tyd -> (v,RelLang.rId v)
        | TS.S t -> (v, RelLang.appR (mapSVar t, empty (), v))
      ) tts) in 
     let () = List.iter (fun rApp -> Printf.printf "%s" ("\n Rapp "^RelLang.exprToString rApp)  
               ) rApps in 
 
    let () = Printf.printf "%s" ("\n >>>><<<<<<") in 
 
    let xexpr = List.fold_right 
        (fun rApp xop -> 
          match xop with 
              None -> let () = Printf.printf "%s" "@ this node None " in
                let () = Printf.printf "%s" ("\n Rapp "^RelLang.exprToString rApp) in 
               Some rApp 
            | Some xexpr ->  let () = Printf.printf "%s" "@ this node Some " in 
                let () = Printf.printf "%s" ("\n Rapp "^RelLang.exprToString rApp) in 
                let () = Printf.printf "%s" ("\n xexpr "^RelLang.exprToString xexpr) in  
                Some (RelLang.crossprd (rApp,xexpr))
            | _ -> let () = Printf.printf "%s" "@ this node Some " in 
                  None 
        )rApps None 

     in 
      let xexpr = match  xexpr with
      | Some s -> s 
      | None  ->  raise (SpecLangEx "No expr to bind")
    in 
    let () = Printf.printf "%s" ("\n >>>><<<<<<") in 
    let bv = genVar () in 
 
    let fr = Fr (bvs,xexpr) in 
 
    let targs = List.map (TyD.makeTvar) tyvars in 
    let bindex = Expr {ground = (id,targs,bv); fr=fr} in 
    let bindabs = Abs (bv,bindex)
    in
    let () = Printf.printf "%s" ("\n >>>><<<<<<") in 
 
    Def {tyvars=tyvars; params=params; abs=bindabs}

  let instantiate (Def {tyvars;params;abs},tydvec,ridvec) : abs =
    let tsubsts = try Vector.zip tydvec tyvars with 
        _ -> raise (BindException  "Bind : tyvar inst error") in 
    let rmap = try  Vector.zip params ridvec with 
      | _ -> raise (BindException "Bind : params inst error") in 
    let err = fun _ -> raise (BindException "Bind: inst error") in 
    let mapt = TyD.instantiateTyvars tsubsts in  
    let mapr = Helper.mkMapper rmap RelId.equal err in 
    let  Abs (bv,Expr {ground=(gr,targs,_); fr=Fr (xs,rexpr)}) = abs in 
    let targs' = List.map  mapt targs in 
    let ground' = (gr,targs',bv) in 
    let rexpr' = RelLang.mapRel rexpr mapr in 
    let expr' = Expr {ground=ground'; fr = Fr (xs,rexpr')} in 
    let abs' = Abs (bv, expr') in 
    abs'

  let instantiate (BogusDef, _, _) = raise (BindException "Cannot instantiate \
                                                           								\ bogus bind def")

  let fromAbs (abs:abs) : def = Def {tyvars=empty (); params=empty (); abs=abs}
end
*)
