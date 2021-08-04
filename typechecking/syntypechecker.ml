module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredTerms 
module DPred = Knowledge.DiffPredicate
module DMap = Knowledge.DistinguisherMap


module VCE = Vcencode 
module P = Predicate  
module RP = Predicate.RelPredicate
exception SynthesisException of string 
exception Unhandled
open Syn



(*TODO : 1. This needs to be generalized for different alfgebraic constructors 
        2. Currently mannualy generating nil and cons preds, this has to be populated 
        by parsing relations from the programmer*)       
let generateNilConstraints (macthedArg) = 
      (*len (ls) = 0*)
      let nil_length = 
        P.Rel(RP.NEq 
              ( R (RelLang.instOfRel (RelId.fromString "len"), macthedArg),
                RelLang.relexpr_for_int 0
              )
              )  
      in 
      let () = Printf.printf "%s" ("Nil Length "^(Predicate.toString nil_length)) in 
      nil_length  




let generateConsConstraints (macthedArg : Var.t) (arg_x: Var.t) (arg_xs : Var.t) = 
    let cons_length =  P.Rel
      (RP.NEq( 
        R( (RelLang.instOfRel (RelId.fromString "len")), macthedArg),
                        
       ADD(
          R ( RelLang.instOfRel (RelId.fromString "len"), 
                arg_xs
              ),
          RelLang.relexpr_for_int 1))
        )  in 
     let cons_length_grt_0 = 
      P.Rel(RP.Grt 
              ( R (RelLang.instOfRel (RelId.fromString "len"), macthedArg),
                RelLang.relexpr_for_int 0
              )
              )
      in 
      let cons_length = Predicate.Conj (cons_length, cons_length_grt_0) in 
  let () = Printf.printf "%s" ("Cons Length "^(Predicate.toString cons_length)) in 
      
    cons_length


(*TODO :: build a typechecker for the *)
let typecheck (gamma : Gamma.t) (sigma:Sigma.t) (t : Syn.typedMonExp) : (RefTy.t * (VC.t) list) = 
	(*place holders*)
	((RefTy.fromTyD TyD.Ty_unit), []) 


open VerificationC
open TyD    
let mon_bind  (acc_delta : Predicate.t) 
              (acc_gamma: VerificationC.vctybinds) 
              (acc_type: RefTy.t) 
              (ci_type :RefTy.t) = 
     match (acc_type, ci_type) with 
      | (RefTy.MArrow (eff1, phi1, (v1,t1), phi1') , RefTy.MArrow (eff2,phi2, (v2, t2), phi2')) -> 
              
                let fresh_h_int = Var.get_fresh_var "h_int" in 
                let _Gamma = VC.extend_gamma (fresh_h_int, (RefTy.lift_base Ty_heap)) acc_gamma in 
      

                
               (*Create Bounded new type*)
                (*no type inference so need to provide the type for the bound variable of a formula*)
                let bv_h = Var.get_fresh_var "h" in 
                let _Gamma = VC.extend_gamma (bv_h, (RefTy.lift_base Ty_heap)) _Gamma in 
                let bv_x = Var.get_fresh_var "x" in 
                let _Gamma = VC.extend_gamma (bv_x,  t1) _Gamma in 
                let bv_h' = Var.get_fresh_var "h'" in 
                let _Gamma = VC.extend_gamma (bv_h', (RefTy.lift_base Ty_heap)) _Gamma in 
                
				(*Following type is now created in this extended environment*)
                (*\forall x, h_int. ( \phi1') h x h_int => \phi2 h_int x)*)
                        
               
                 
                (*phi1 h*)
                let f1_pre = (VC.apply phi1 [(bv_h, Ty_heap)]) in 
                

                
               (*  let () = Printf.printf "%s" "\n Generating The Path Induction pre " in 
                *)
                
                let f2_pre =  P.If ((VC.apply phi1' [(bv_h, Ty_heap); (bv_x, RefTy.toTyD t1); (fresh_h_int, Ty_heap)]), 
                                    ((VC.apply phi2 [(fresh_h_int, Ty_heap)]))
                                                  )
                                            
                                        
                                     

                in

                let bind_pre (*create pre-condition*) =  P.Forall ([(bv_h, Ty_heap)], P.Conj (f1_pre, f2_pre))  in 
                (* let () = Printf.printf "%s" ("\n PRE \n "^(Predicate.toString bind_pre)) in  
              *)
                (* let () = Printf.printf "%s" "\n Generating The Path Induction post " in 
                 *)
                (*creating post*)
                (*forall v h h' x h_int. phi1 x h h_int*)
                
                let (bv_v)= Var.get_fresh_var "v" in 
                let _Gamma = VC.extend_gamma (bv_v,  t2) _Gamma in 
                
                 
                (*Add h' to the Gamma*)

                let local_var_binds = [(bv_h, Ty_heap);(bv_v, RefTy.toTyD t2);(bv_h', Ty_heap) ] in 
                
                let bind_post (*create post-condition*) = 
                 P.Forall (local_var_binds, P.Conj (( VC.apply phi1' [(bv_h, Ty_heap);(bv_x, RefTy.toTyD t1);(fresh_h_int,Ty_heap)]),
                                                (VC.apply phi2' [(fresh_h_int ,Ty_heap);(bv_v, RefTy.toTyD t2); (bv_h', Ty_heap)])))
                               in 

 
             (*    let () = Printf.printf "%s" ("\n POST \n "^(Predicate.toString bind_post)) in  
              *)                          
               
                (*least uppper bound*)
                let lubM = Effect.lub eff1 eff2  in                 
                let new_acc_ty = RefTy.MArrow (lubM, bind_pre , (bv_v,t2), bind_post) in
                
                (*
                let () = Printf.printf "%s"  (" \n \n \n >>>>>>>>>>><<<<<<<<<<<<<<<<< Gamma AFTER BIND "^(string_gamma _Gamma)) in  
                let () = Printf.printf "%s" (" \n \n \n >>>>>>>>>>>>>>>>>>>>>>>>>> VCS AFTER BIND "^(string_for_vcs acc_vc')) in  
                let () = Printf.printf "%s"  (" \n  >>>>>>>>>>><<<<<<<<<<<<<<<<< Accumulated Type "^(RefTy.toString  new_acc_ty)) in  *)
                (_Gamma, acc_delta, new_acc_ty)
                        
                
      | (_, _) -> raise (Error ("binding non copmputations "^(RefTy.toString acc_type)^(" >>= ")^(RefTy.toString ci_type)^" \n"))     



(*path is a list of variables
This seems to be a bit broken, we should be able to get a type for a path without a pre-condition
  
*)
let typeForPath gamma sigma delta spec (path:Syn.path)  = 
	
  let rec accumulatePathType remaining_path acc_gamma acc_delta acc_type = 
        match remaining_path with 
	         [] -> (acc_gamma, acc_delta, acc_type) 
	         
           | ei :: cs -> 
	          	let ci = Syn.componentNameForMonExp ei in  
              let found_type = Gamma.find gamma ci in 
              let ci_type = 
                 match found_type with 
                   | RefTy.MArrow (_,_,(_,_),_) -> found_type
                   | RefTy.Arrow ((_,_), retTy) -> retTy 
              in        
	          	let (acc_gamma, acc_delta, acc_type) = mon_bind acc_delta acc_gamma acc_type ci_type in
	                  accumulatePathType cs acc_gamma acc_delta acc_type
	        

	  in

let RefTy.MArrow (_, pre,  (_,_), post) = spec in 

	let initial_effect = Effect.Pure in 
	let retResult = Var.get_fresh_var "v" in 
    let unKnownType = RefTy.Base (retResult, TyD.Ty_unknown , Predicate.True) in 
    let bv_h = Var.get_fresh_var "h" in 
    let gamma = VC.extend_gamma (bv_h, (RefTy.lift_base Ty_heap)) gamma in 
    let bv_x = Var.get_fresh_var "x" in 
    let  gamma  = VC.extend_gamma (retResult,  unKnownType) gamma in 
    let bv_h' = Var.get_fresh_var "h'" in 
    let gamma = VC.extend_gamma (bv_h', (RefTy.lift_base Ty_heap)) gamma in 

    let pre_h = VC.apply pre [(bv_h, Ty_heap)] in 
    let pre_h' = VC.substi pre (bv_h', Ty_heap) 1 in 
    let pre_h_v_h' = VC.apply pre_h' [(bv_h', Ty_heap)] in 
    
    
    let preInit = P.Forall ([(bv_h, Ty_heap)], pre_h) in 
    let postInit = P.Forall ([(bv_h, Ty_heap);(retResult, Ty_unknown);(bv_h', Ty_heap)], pre_h_v_h') in 
    let initial_type = RefTy.MArrow (initial_effect, 
       										preInit, (retResult, unKnownType), 
       										postInit) in
       				
 	 accumulatePathType path gamma delta initial_type   



let typeForPathSuffix gamma sigma delta suffix prefixType =

	let rec accumulatePathType remaining_path acc_gamma acc_delta acc_type = 
         	
         	match remaining_path with 
	         [] -> (acc_gamma, acc_delta, acc_type) 
	         | (ci, rti) ::  cs -> 
	          	let ci_type = rti in 
	          	let (acc_gamma, acc_delta, acc_type) = mon_bind acc_delta acc_gamma  acc_type ci_type in
	                 accumulatePathType cs acc_gamma acc_delta acc_type
	        

	  in

   
	 accumulatePathType suffix gamma delta prefixType   

let typeCheckPath gammaMap sigmaMap deltaPred (path : Syn.path) (spec : RefTy.t) = 


	
	let (gammaMap, deltaPred, path_type) = 
			typeForPath gammaMap sigmaMap deltaPred spec path in 
	
	let gammacap = DPred.T{gamma=gammaMap;
							sigma = sigmaMap;
							delta = deltaPred} in 
			 

	let RefTy.MArrow (eff, _,_,_) = spec in 
	let RefTy.MArrow (effi, _,_,_) = path_type in 
	 
    if (not (Effect.isSubEffect effi eff))  
            then (false, gammacap, path_type)   
    else    
          (*   let () = Printf.printf "%s" ("Found Path Type "^(RefTy.toString path_type)) in 
            let () = Printf.printf "%s" ("Compared Against Spec "^(RefTy.toString spec)) in 
	       *)  
	       	let vc = VC.fromTypeCheck gammaMap [deltaPred] (path_type, spec) in  

	        (*make a direct call to the SMT solver*)
	        let vcStandard = VC.standardize vc in 
	        let () = Printf.printf "%s" (VC.string_for_vc_stt vcStandard) in  
	        let result = VCE.discharge vcStandard  in 
	        match result with 
	        | VCE.Success -> 
	                      (true, gammacap, path_type)
	        | VCE.Failure -> 
	                      (false, gammacap, path_type) 
	        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
	        