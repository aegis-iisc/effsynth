open Printf
open SpecLang

module RefTy = RefinementType


type var = Var.t


type caseExp = {constuctor : var;
                args : var list ;
                exp : typedMonExp}

and  monExp = 
        | Evar of var 
        | Elam of var * typedMonExp
        | Efix of var * typedMonExp
        | Eapp of typedMonExp * typedMonExp
        | Ematch of typedMonExp * (caseExp list) 
        | Elet of var * typedMonExp * typedMonExp
        | Eret of typedMonExp 
        | Ebind of var * typedMonExp * typedMonExp
        | Elloc of typedMonExp           
        | Eget of typedMonExp 
        | Eset of typedMonExp * typedMonExp
        | Ecapp of var * ( typedMonExp list ) 



and typedMonExp = {expMon:monExp; ofType:RefTy.t }

val  monExp_toString : monExp -> string 

val  typedMonExp_toString : typedMonExp ->  string  
 
