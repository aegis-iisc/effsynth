module Env = Environment
module Syn = Lambdasyn
module VC = TransTypeChecker.VerificationC   
open SpecLang 
open Env    
module Gamma = Env.TypingEnv 
module Sigma = Env.Constructors
module VCE = Vcencode 
exception SynthesisException of string 
let rec esynthesize gamma sigma spec = 
      match spec with 
      (*Tvar case*)
      | RefTy.Base (v, t, pred) -> 
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
         
         let rec verifyFound fs  = 
            match fs with
             | [] -> None 
             | (vi, rti) :: xs -> 
                
                let vc = VC.fromTypeCheck gamma (rti, spec) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                match result with 
                | VCE.Success -> Some (Syn.Evar (vi)) 

                | VCE.Failure -> verifyFound xs
                | VCE.Undef -> None  
                
         in 
         verifyFound foundTypes
     (*TODO Other cases*)                   


     | _ -> raise (SynthesisException "Illegal elimination form")       


  
(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
let rec synthesize gamma sigma spec = 
     match spec with 
      | RefTy.Base (v, t, pred) -> esynthesize gamma sigma spec  
      | RefTy.MArrow (eff, pre, t, post) -> esynthesize gamma sigma spec  
      | RefTy.Arrow (rta, rtb) -> esynthesize gamma sigma spec
      | _ -> None  


