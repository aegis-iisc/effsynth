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
        | Elam of monExp * typedMonExp
        | Efix of var * typedMonExp 
        | Eapp of monExp * typedMonExp (*Evar v v1*)
        | Ematch of typedMonExp * (caseExp list) 
        | Elet of monExp * typedMonExp * typedMonExp
        | Eret of typedMonExp 
        | Ebind of monExp * typedMonExp * typedMonExp
        | Ecapp of var * ( monExp list ) 
        | Ehole (*a hole in place of an expression*)
        | Edo of monExp * monExp (*do E; retrun K*)
        | Eskip   

and typedMonExp = {expMon:monExp; ofType:RefTy.t }


type path =  monExp list 



let rec equalMonExp m1 m2 =
      match (m1, m2) with
        | (Evar v1, Evar v2) -> Var.equal v1 v2 
        | (Elam (arg1, body1), Elam (arg2, body2)) ->
                (equalMonExp arg1 arg2) && (equalTypedMonExp body1 body2) 
        | (Efix (name1, body1), Efix (name2, body2)) -> 
                (Var.equal name1 name2) && (equalTypedMonExp body1 body2) 
        | (Eapp (fun1, arg1), Eapp (fun2, arg2))->
                (equalMonExp fun1 fun2) && (equalTypedMonExp arg1 arg2) 
        | (Ematch (matchingArg1, caselist1),Ematch (matchingArg2, caselist2)) -> 
                (equalTypedMonExp matchingArg1 matchingArg2)  
                         
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
        | Evar v -> ("Evar "^v)
        | Eret ret ->  ("Eret "^(typedMonExp_toString ret))
        | Ebind (mne, tmne1, tmne2) -> ("Ebind "^(monExp_toString mne)^" <- "^
                                            (typedMonExp_toString tmne1)^" in "^
                                            (typedMonExp_toString tmne2 ))  
        | Ecapp (cname, argls) -> "Ecapp "^(cname)^" ( "^(
                                List.fold_left (fun accstr ai -> 
                                                accstr^", "^(monExp_toString ai)) "" argls

                                                )^" )" 
        | Ematch (matchingArg, caselist) -> 
                let caselist_toString = 
                    List.fold_left (fun accstr casei -> (accstr^" \n | "^(caseExp_toString casei))) " " caselist 
                in 
                ("Ematch "^(typedMonExp_toString matchingArg)^" with "^caselist_toString)
        | Eapp (fun1, arg1) -> ("Eapp "^(monExp_toString fun1)^" \n ("^(typedMonExp_toString arg1)^")")         
        | _ -> "Other expression"  


(*We will add more auxiliary functions here as we go along synthesis*)
and typedMonExp_toString (t:typedMonExp) : string = 
   let {expMon;ofType} = t in  
   ("{ \n"^monExp_toString expMon^" \n }") 

and caseExp_toString (t : caseExp) : string = 
    let argsToString = List.fold_left (fun accstr argi -> (accstr^" ,"^(Var.toString argi))) " " t.args in 
    ("CASE "^(Var.toString t.constuctor)^" ( "^(argsToString)^" ) -> "^(typedMonExp_toString t.exp))

let componentNameForMonExp mExp = 
        match mExp with 
         | Evar v -> (v)
         | Eapp (v , arg) -> 
                (match v with 
                    | Evar v1 -> v1
                    | _ -> raise (IncorrectExp "a component is either a variable or a fun app"))
         | _ -> raise (IncorrectExp "a component is either a variable or a fun app")
       
        


let getExp (t : typedMonExp) =
    let {expMon;_} = t in expMon

let getType (t : typedMonExp) = 
   let {ofType;_} = t in ofType

(*placeholder , TODO implement complete later*)
let buildProgramTerm (path : path) =  
        match path with
            | [] -> Eskip
            | x :: _ -> x


let pathToString (p:path) = 
        (List.fold_left (fun accstr ei -> accstr^("--->")^(monExp_toString ei)) "PATH " p)^"\n"

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