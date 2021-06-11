module Syn = Lambdasyn 
open SpecLang 

exception NoMappingForVar of string
exception IllegalConstructorType of string    
(*A var to refinement type mapping typing environment*)
module TypingEnv = struct

module TypingEnvKey =
       struct
         type t = Var.t
         let equal(t1,t2)  =  Var.equal t1 t2
       end

module TypingEnvValue =
       struct
         (*Need to change later to scehema*)
         type t = RefinementType.t
         let equal (t1,t2) = RefinementType.compare_types t1 t2           
end

module TyMap   = Applicativemap.ApplicativeMap (TypingEnvKey) (TypingEnvValue) 

type t = TyMap.t
let empty = TyMap.empty
let mem = TyMap.mem
let find t var = 
    try (TyMap.find t var) 
  with 
  | (TyMap.KeyNotFound k) -> raise (NoMappingForVar k)

let add = fun t -> fun var rt -> TyMap.add t var rt
let remove = TyMap.remove

(*enumerate variables and find macthing types*)
let enumerateAndFind t (rt:TypingEnvValue.t) : ((TypingEnvKey.t*TypingEnvValue.t) list)   = 
        TyMap.enumerate t rt 
          
           

end 

(*The constructor environment Sigma*)
module Constructors = struct


module ConstructorEnvKey =
       struct
         type t = Var.t
         let equal(t1,t2)  =  Var.equal t1 t2
       end

module ConstructorEnvValue =
       struct
         (*Need to change later to scehema*)
         type t = RefinementType.t
         let equal (t1,t2) = RefinementType.compare_types t1 t2           

end

module ConsMap   = Applicativemap.ApplicativeMap (ConstructorEnvKey) (ConstructorEnvValue) 

type t = ConsMap.t
let empty = ConsMap.empty
let mem = ConsMap.mem
let find t tyd = 
    try (ConsMap.find t tyd) 
  with 
  | (ConsMap.KeyNotFound k) -> raise (NoMappingForVar k)

let add = fun t -> fun tyd sort -> ConsMap.add t tyd sort 
let remove = ConsMap.remove

let rec findCons4RetT t retT acc : ((Var.t*RefinementType.t)list ) = 
        match t with 
        | [] -> acc
        | (vi, rti):: xs -> 
                match rti with 
                 | RefinementType.Arrow ((v,t1), t2) -> 
                        if (RefinementType.compare_types t2 retT) then 
                          let acc = (vi, rti) :: acc in 
                          findCons4RetT xs retT acc 
                        else
                          findCons4RetT xs retT acc
                 | _ -> raise (IllegalConstructorType "findCons4RetT")   
end 




(*To be populated later*)
module RelationalEnv = struct



end

module ExploredTerms = struct 
  type t = Var.t list
  let empty = []  
  let find t (e:Var.t) = List.find (fun e' -> (Var.equal e e')) t 
  let add t e = e::t
  let remove t e  =
        List.filter (fun e' -> not (Var.equal e e')) t 

  let mem t e = List.exists e t 

end


module ExploredPaths = struct 
  type t = Var.t list
  let empty = []  
  let find t (e:Var.t) = List.find (fun e' -> (Var.equal e e')) t 
  let add t e = e::t
  let remove t e  =
        List.filter (fun e' -> not (Var.equal e e')) t 

  let mem t e = List.exists e t 
  let fromList ls = ls
end




