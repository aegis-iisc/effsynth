open SpecLang 
module SEL = SpecElab
module Synth = Synthesis
module Lambda = Lambdasyn 
exception CompilerExc of string  
let () = 

  let num_args = (Array.length Sys.argv) - 1 in 
  if num_args = 1 then  
    let spec_file = Sys.argv.(1) in 
    let _ = Printf.printf "%s" ("\n specfile :: "^spec_file) in 
    let ast = SEL.parseLSpecFile spec_file in 
    (* let () = Printf.printf "%s" ("\n List of components available") in  *)
    let string_ast = RelSpec.toString ast in 
    let () = Printf.printf "%s" string_ast in 
    let (gamma, sigma, goal) = SEL.elaborateEnvs ast in 
    let synthterm = Synth.synthesize gamma sigma goal in   
    	    (*run the initial environment builder*)    
    match synthterm with 
        | None -> Printf.printf "%s" "Synthesis returned witout result"
        | Some t -> Printf.printf "%s" ("Success : "^(Lambda.typedMonExp_toString t))
   
  else
    let exception_msg = (" Incorrect Number of argumnets, required 1, provided "^(string_of_int num_args)^" Usage :: ./compile.native <path_to_ml_file> <path_to_spec_file>") in  
    raise (CompilerExc  exception_msg)
 
  
