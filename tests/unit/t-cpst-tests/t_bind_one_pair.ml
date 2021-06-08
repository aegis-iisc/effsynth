module Trans = TypedTransLang
module SB = SigmaBuilder
module TM = TypesMap
module FM = FormMap
module F = T_iota
module S = T_lambda  
open SB  

let specfile = "tests/unit/t-cpst-tests/t_bind_one_pair.spec"  

(*parse the associated spec file*)
let ast = SB.parseLSpecFile specfile 
let () = Printf.printf "%s" ("\n ########SPECS######### \n "^(SpecLang.RelSpec.toString ast)) 
let (tenv, formenv) =  SB.buildSigma ast  
let getType s = TM.find tenv s  
let getFormula s = FM.find formenv s 
let gamma = SB.initializeGamma ast 
(*define placeholder functions in L term with types*)

(*define transducer*)     
let t_bind =                    
        let trans_first = T_one_simple.t_one in 
        let trans_second = T_pair.t_pair in 
        Trans.Lambda (T_var "zero", getType "zero", Trans.Bind (trans_first, trans_second)) 
let () = 
   Morpheus.verifyCPST gamma t_bind (getType "annot")     
