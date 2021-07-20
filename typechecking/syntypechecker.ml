module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredTerms                 
module VCE = Vcencode 
module P = Predicate  
exception SynthesisException of string 
exception Unhandled
open Syn




(*TODO :: build a typechecker for the *)
let typecheck (gamma : Gamma.t) (sigma:Sigma.t) (t : Syn.typedMonExp) : (RefTy.t * (VC.t) list) = 
	(*place holders*)
	((RefTy.fromTyD TyD.Ty_unit), []) 


open VerificationC
open TyD    
let mon_bind  (acc_delta : Predicate.t) (acc_gamma: VerificationC.vctybinds) (acc_type: RefTy.t) (ci_type :RefTy.t) = 
     match (acc_type, ci_type) with 
      | (RefTy.MArrow (eff1, phi1, (v1,t1), phi1') , RefTy.MArrow (eff2,phi2, (v2, t2), phi2')) -> 
              
                let () = Printf.printf "%s" ("\n Type t1 "^(RefTy.toString t1)) in
                let () = Printf.printf "%s" ("\n Type t2 "^(RefTy.toString t2)) in
  
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
                

                
                let () = Printf.printf "%s" "\n Generating The Path Induction pre " in 
               
                
                let f2_pre =  P.If ((VC.apply phi1' [(bv_h, Ty_heap); (bv_x, RefTy.toTyD t1); (fresh_h_int, Ty_heap)]), 
                                    ((VC.apply phi2 [(fresh_h_int, Ty_heap)]))
                                                  )
                                            
                                        
                                     

                in

                let bind_pre (*create pre-condition*) =  P.Forall ([(bv_h, Ty_heap)], P.Conj (f1_pre, f2_pre))  in 
                let () = Printf.printf "%s" ("\n PRE \n "^(Predicate.toString bind_pre)) in  
             
                let () = Printf.printf "%s" "\n Generating The Path Induction post " in 
                
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

 
                let () = Printf.printf "%s" ("\n POST \n "^(Predicate.toString bind_post)) in  
                                       
               
                (*least uppper bound*)
                let lubM = Effect.lub eff1 eff2  in                 
                let new_acc_ty = RefTy.MArrow (lubM, bind_pre , (bv_v,t2), bind_post) in
                
                (*
                let () = Printf.printf "%s"  (" \n \n \n >>>>>>>>>>><<<<<<<<<<<<<<<<< Gamma AFTER BIND "^(string_gamma _Gamma)) in  
                let () = Printf.printf "%s" (" \n \n \n >>>>>>>>>>>>>>>>>>>>>>>>>> VCS AFTER BIND "^(string_for_vcs acc_vc')) in  
                let () = Printf.printf "%s"  (" \n  >>>>>>>>>>><<<<<<<<<<<<<<<<< Accumulated Type "^(RefTy.toString  new_acc_ty)) in  *)
                (_Gamma, acc_delta, new_acc_ty)
                        
                
      | (_, _) -> raise (Error ("binding non copmputations "^(RefTy.toString acc_type)^(" >>= ")^(RefTy.toString ci_type)^" \n"))     



(*path is a list of variables*)
let typeForPath gamma sigma delta spec path  = 
	let RefTy.MArrow (_, pre,  (_,_), post) = spec in 
	
	let rec accumulatePathType remaining_path acc_gamma acc_delta acc_type = 
        match remaining_path with 
	         [] -> (acc_gamma, acc_delta, acc_type) 
	         | ci :: cs -> 
	          	let ci_type = Gamma.find gamma ci in 
	          	let (acc_gamma, acc_delta, acc_type) = mon_bind acc_delta acc_gamma  acc_type ci_type in
	                  accumulatePathType cs acc_gamma acc_delta acc_type
	        

	  in

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
	         | ci ::  cs -> 
	          	let ci_type = Gamma.find gamma ci in 
	          	let (acc_gamma, acc_delta, acc_type) = mon_bind acc_delta acc_gamma  acc_type ci_type in
	                  accumulatePathType cs acc_gamma acc_delta acc_type
	        

	  in

   
	 accumulatePathType suffix gamma delta prefixType   

