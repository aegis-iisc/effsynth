(*defined Var or import from the specLang*)
open Printf 
open SpecLang 
exception IncorrectExp of string     

module RefTy = RefinementType

type var = Var.t 


type caseExp = {constuctor : var;
                args : var list ;
                exp : typedMonExp}

and  monExp = 
        | Evar of var 
        | Elam of (typedMonExp list) * typedMonExp (*Named Lambda Elam x1 : t1, x2:t2 . body *)
        | Efix of var * typedMonExp 
        | Eapp of monExp * (monExp list) (*Eapp foo [x1, x2, x3,...xn] *)
        | Ematch of typedMonExp * (caseExp list) 
        | Elet of monExp * typedMonExp * typedMonExp
        | Eret of monExp 
        | Ebind of monExp * monExp * monExp
        | Ecapp of var * ( monExp list ) 
        | Ehole of RefTy.t(*a hole in place of an expression*)
        | Edo of monExp * monExp (*do x <- E*)
        | Eskip   

and typedMonExp = {expMon:monExp; ofType:RefTy.t }


type path =  monExp list 


(*The t ~ H relation
The exact logic can be made less or more precise*)
let satHypothesis (t : path) (hypothesis : path) : bool = 
    true


let rec equalMonExp m1 m2 =
      match (m1, m2) with
        | (Evar v1, Evar v2) -> Var.equal v1 v2 
        | (Elam (arglist1, body1), Elam (arglist2, body2)) ->
                (try
                    (List.fold_left2 (fun accBool arg1 arg2 -> 
                        accBool && (equalTypedMonExp arg1 arg2)) true arglist1 arglist2) 
                    && (equalTypedMonExp body1 body2) 
                with 
                 Invalid_argument e -> false)

        | (Efix (name1, body1), Efix (name2, body2)) -> 
                (Var.equal name1 name2) && (equalTypedMonExp body1 body2) 
        | (Eapp (fun1, arglist1), Eapp (fun2, arglist2))->
                (try
                    (equalMonExp fun1 fun2) && 
                
                    (List.fold_left2 (fun accBool arg1 arg2 -> 
                        accBool && (equalMonExp arg1 arg2)) true arglist1 arglist2) 
                    
                with 
                 Invalid_argument e -> false)

                 
        | (Ematch (matchingArg1, caselist1),Ematch (matchingArg2, caselist2)) -> 
                (equalTypedMonExp matchingArg1 matchingArg2)  
                         
        | (Edo (bound1, exp1), Edo (bound2, exp2)) -> 
                (equalMonExp bound1 bound2 && equalMonExp exp1 exp2)
        | (Ehole t1, Ehole t2) ->
                 (RefTy.compare_types t1 t2)    
        |  (_,_) -> false         

and equalTypedMonExp tme1 tme2 = 
    equalMonExp tme1.expMon tme2.expMon


        
let equalPath p1 p2 = 
       try 
            List.fold_left2 (fun accBool ci cj -> 
                accBool && equalMonExp ci cj) true p1 p2 
       with 
           Invalid_argument e-> false   


let rec doExp (ls : monExp list) : monExp= 
    match ls with 
        [] -> Eskip
        | x :: xs -> Edo (x, doExp (xs))
(*normal form*)
(*
type caseIExp = Case of {constuctor : var;
                args : var list ;
                exp : monIExp}


and  monEExp = 
        | Evar of var 
        | Eapp of monEExp * monIExp (*all application will be of the form x I1 I2....*)
        | Eret of monIExp
        | Ebind of monExp * monEExp  * monEExp
        | Elloc of monExp           
        | Eget of monEExp
        | Eset of monEExp * monIExp
                  
and monIExp = 
        | Elam of monEExp * monIExp
        | Efix of var * monIExp
        | Ematch of monEExp * (caseIExp list) 
        | Elet of monEExp * monIExp * monIExp
        | Ecapp of var * ( monIExp list ) 
        | Ehole (*a hole in place of an expression*)
        | Edo of monEExp * monIExp (*do E; retrun K*)

and normalMonExp = 
        | E of monEExp 
        | I of monIExp 
and typedNormalExp = {nme:normalMonExp;rt:RefTy.t}            
*)

let rec monExp_toString (m:monExp) = 
    match m with 
        | Evar v -> (v)
        | Eret ret ->  ("return "^(monExp_toString ret))
        | Ebind (mne, mne1, mne2) -> ((monExp_toString mne1)^" \n \t >>= \lambda"^
                                    (monExp_toString mne)^" . \n \t "^
                                    (monExp_toString mne2 ))  
        | Ecapp (cname, argls) -> "Ecapp "^(cname)^" ( "^(
                                List.fold_left (fun accstr ai -> 
                                                accstr^", "^(monExp_toString ai)) "" argls

                                                )^" )" 
        | Ematch (matchingArg, caselist) -> 
                let caselist_toString = 
                    List.fold_left (fun accstr casei -> (accstr^" \n | "^(caseExp_toString casei))) " " caselist 
                in 
                ("Ematch "^(typedMonExp_toString matchingArg)^" with "^caselist_toString)
        | Eapp (fun1, arglsit) -> 
            ("apply "^(monExp_toString fun1)^"  ("^
                (List.fold_left 
                    (fun accStr argi -> accStr^", "^(monExp_toString argi)^" )") ""  arglsit))        
        
        | Edo (bound, exp) -> 
                ("do "^(monExp_toString bound)^" <- "^(monExp_toString exp)) 
        | Eskip -> "Eskip"
        | Ehole t -> ("[?? : "^(RefTy.toString t^"]"))
        | _ -> "Other expression"  


(*We will add more auxiliary functions here as we go along synthesis*)
and typedMonExp_toString (t:typedMonExp) : string = 
   let {expMon;ofType} = t in  
   ("{ \n"^monExp_toString expMon^" \n }") 

and caseExp_toString (t : caseExp) : string = 
    let argsToString = List.fold_left (fun accstr argi -> (accstr^" ,"^(Var.toString argi))) " " t.args in 
    ("CASE "^(Var.toString t.constuctor)^" ( "^(argsToString)^" ) -> "^(typedMonExp_toString t.exp))

let rec componentNameForMonExp mExp = 
        match mExp with 
         | Evar v -> (v)
         | Eapp (v , _) -> 
                (match v with 
                    | Evar v1 -> v1
                    | _ -> raise (IncorrectExp "a component is either a variable or a fun app"))
         | Ecapp (v, args) -> v
         | Edo (bound, exp) -> componentNameForMonExp exp
         | _ -> raise (IncorrectExp "a component is either a variable or a fun app")
       
        


let getExp (t : typedMonExp) =
    let {expMon;_} = t in expMon

let getType (t : typedMonExp) = 
   let {ofType;_} = t in ofType

(*placeholder , TODO implement complete later*)
let rec buildProgramTerm (path : path) =  
        match path with
            | [] -> Eskip
            | x :: xs ->
                match x with 
                | Edo (boundx, expx) ->  
                    Ebind (boundx, expx, buildProgramTerm xs)
                | Eapp (name, args) -> 
                     let boundVar = Var.get_fresh_var "bound" in 
                     let boundx = Evar (boundVar) in 
                                
                     Ebind (boundx, x, buildProgramTerm xs)    

                 | Evar v ->
                        let boundVar = Var.get_fresh_var "bound" in 
                        let boundx = Evar (boundVar) in 
                      
                        Ebind (boundx, x, buildProgramTerm xs )
                 | Eret retme -> 
                        x
                 | _ -> raise (IncorrectExp "Building Illformed Term")      
                                       

let pathToString (p:path) = 
        (List.fold_left (fun accstr ei -> accstr^(" ---> ")^(monExp_toString ei)) "PATH " p)^"\n"

let previousComponent (p:path) = 
    if (List.length p < 2) then None 
        else 
         Some (List.nth (p) ((List.length p) - 2))

let previousPath (p : path) =
        if (List.length p < 1) then None
        else 
         Some (List.rev (List.tl (List.rev p)))


let merge matchingArg constructors consArgsList caseBodyList = 
       let () = Printf.printf "%s" (string_of_int (List.length constructors) )in 
       assert (List.length constructors == List.length consArgsList);
       assert (List.length consArgsList == List.length caseBodyList);
       
            
       let rec loop c a b cexpList = 
            match (c, a, b) with 
                | ([],[],[]) -> cexpList
                | (x::xs, y::ys, z::zs) -> 
                     let caseExp_i = {constuctor =x;args=y;exp=z} in 
                     loop xs ys zs (cexpList@[caseExp_i])     
        in 
        
       let megerdCaseExpList = loop constructors consArgsList caseBodyList [] in 
       
       let mergedExp = Ematch(matchingArg, megerdCaseExpList) in 
       mergedExp



 (*finds the last hole in the program and returns a prefix, the hole and 
 the suffix of the path*)      
 let getLastHole path = 
    let revPath = List.rev path in 
    let rec recurse p suffix= 
     match p with 
        [] -> (None, [], suffix)      
        | x :: xs -> 
            (match x with 
                | (Edo (x1,e)) ->
                    (match e with 
                        | Ehole _ ->
                                (Some x, xs, suffix)
                        | _ ->  recurse xs (suffix@[x]))
                | (Ehole _) -> (Some x, xs, suffix)
                | _ ->  recurse xs (suffix@[x]))

   in 
   let (hole, rev_prefix, rev_sufix) = recurse revPath [] in 
   (hole, List.rev (rev_prefix), List.rev (rev_sufix))



let rec isComplete path = 
    let (hls,_,_) = getLastHole path in 
    match hls with 
        | None -> true
        | Some _ -> false 