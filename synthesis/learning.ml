module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredTerms                 
module VCE = Vcencode 
module P = Predicate  
module SynTC = Syntypechecker
module DPred = Knowledge.DiffPredicate
module DMap = Knowledge.DistinguisherMap
exception LearningException of string 
exception Unhandled
open Syn

module Message = struct 

  let show (s:string) = Printf.printf "%s" ("\n"^s) 


end


type exploredTree = Leaf 
					| Node of exploredTree list	


type path =  Var.t list 


let hoarePre gammacap spec path ci rti = 


	

(*a routine to verify that the choice ci, in the current gamma satisfies the distinguishing constraints*)
let distinguish gamma dps spec path ci rti= 
 	
 	let () =Message.show ("Potential Component  "^(Var.toString ci)) in 
	let RefTy.MArrow (_, ci_pre,  (_,_), c_post) = rti in 
	(*extract fields from gamma^*)
	let gammaMap = DPred.getGamma gamma in 
	let sigmaMap = DPred.getSigma gamma in 
	let deltaPred = DPred.getDelta gamma in 
	(*but this should be typed in the output heap*)
	(*\Gamma |= post_path => pre*)
	
	(*??TODO : we need a function generating strongest postcondition for a path*)

	(*either first component or *)
	let (gammaMap, deltaPred, path_type) = SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in 
	
	Message.show (">>>>>>>>>>>PATH TYPE "^RefTy.toString path_type);
	
	let RefTy.MArrow (_,post_pre,(_,t), post_path) = path_type in 
	let h_var  = Var.get_fresh_var "h" in 
    let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

	let h'_var  = Var.get_fresh_var "h'" in 
    let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

    let x_var = Var.get_fresh_var "x" in 

    let gammaMap = Gamma.add gammaMap h_var h_type in 
    let gammaMap = Gamma.add gammaMap h'_var h'_type in 
    let gammaMap = Gamma.add gammaMap x_var t in 

	
    
    let post_path_applied = VC.apply post_path [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
              

	(*substitute current heap values for pre*)
    let ci_pre_applied = VC.apply ci_pre [(h'_var, TyD.Ty_heap)] in 
   

	let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 	
    let post_path_imp_pre_ci = Predicate.Forall (bvs, P.If (post_path_applied, ci_pre_applied)) in   
           
	let vc1 = VC.VC(gammaMap, deltaPred, post_path_imp_pre_ci) in 


	(*construct VCs ci_post => D(ci)*)
	
	let potential_path = path@[ci] in 
	



	let (gammaMap, deltaPred, potential_path_type) = SynTC.typeForPathSuffix gammaMap sigmaMap deltaPred [ci] path_type in 



	let diffpred_ci = 
			try
				DMap.find dps ci 
			with 
				Knowledge.NoMappingForVar e -> DPred.empty
	in 			

	let diffpred_ci_gammaCap = DPred.getGammaCap diffpred_ci in 
	let diffpred_ci_learntPred = DPred.getLearnt diffpred_ci in 

	(*TODO ??*)
	Message.show "Potential Path Type";
	Message.show (RefTy.toString potential_path_type);

	let RefTy.MArrow (_,pot_path_pre,(_,t), pot_path_post) = potential_path_type in 
	let h_var  = Var.get_fresh_var "h" in 
    let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

	let h'_var  = Var.get_fresh_var "h'" in 
    let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

    let x_var = Var.get_fresh_var "x" in 

    let gammaMap  = Gamma.add gammaMap h_var h_type in 
    let gammaMap = Gamma.add gammaMap h'_var h'_type in 
    let gammaMap = Gamma.add gammaMap  x_var t in 


    let pot_path_post_applied = VC.apply pot_path_post 
    						[(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
    
          

	(*substitute current heap values for pre*)
    let d_ci_applied_h' = VC.apply diffpred_ci_learntPred [(h'_var, TyD.Ty_heap)] in 
   

	let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 	
    let pot_path_posti_imp_d_ci = Predicate.Forall (bvs, P.If (pot_path_post_applied, d_ci_applied_h')) in   

    let gammaMap4vc2 = gammaMap@(DPred.getGamma diffpred_ci_gammaCap) in 
    let deltaPred4vc2 = Predicate.Conj(deltaPred, (DPred.getDelta diffpred_ci_gammaCap)) in  
    let vc2 = VC.VC(gammaMap4vc2, deltaPred4vc2, pot_path_posti_imp_d_ci) in 

    Message.show ("\n Predicate testsed "^(Predicate.toString pot_path_posti_imp_d_ci));

	let vcs = [vc1;vc2] in 
	
	let vcsStandard = List.map (fun vc -> VC.standardize vc) vcs in 
	
	
	let discharge_vc vcStandard = 
		try
		Message.show ("\n Printing VCs");
        Message.show ("\n"^(VC.string_for_vc_stt vcStandard));      
        let result = VCE.discharge vcStandard  in 
		    match result with 
		    | VCE.Success -> 
		                    true
		    | VCE.Failure -> 
		                    false
		    | VCE.Undef -> raise (LearningException "Typechecking Did not terminate")  
		    
		 with
		 	VerificationC.Error e -> raise (LearningException "Checking a distingushing predicate did not terminate")

	in 	 	

	let isDistinguished = List.fold_left (fun failure svci -> failure && discharge_vc svci) true vcsStandard in  
	
	 
	let () =  
	if (isDistinguished) then 
		Message.show (" Show ***************D (ci) Successful************"^(Var.toString ci))
	else 
	    Message.show ("Show ***************Selection Failed************"^(Var.toString ci))
	
	in                   
	let RefTy.MArrow (_,_, (_,_), potential_path_post) = potential_path_type in 
	let gammaCapPotential = DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
	(gammaCapPotential, potential_path_post, isDistinguished)






let chooseC gammacap path spec (dps : DMap.t) = 
    let RefTy.MArrow (eff, pre, (v, t), post) = spec in 
    let gamma = DPred.getGamma gammacap in 
    let c_wellRetType = Gamma.enumerateAndFind gamma spec in 
   
    let c_es = List.filter (fun (vi, ti) -> 
    					let RefTy.MArrow (effi, _,(_,_), _) = ti in 
						Effect.isSubEffect effi eff) c_wellRetType in 
    
    (*choosing a component*)
    let rec choice potentialChoices gammacap dps  : (Knowledge.DistinguisherMap.t * Var.t) option= 
    	Message.show "Choice ";
    	match potentialChoices with 
    		| [] -> None
    		| (vi, rti) :: xs -> 
    			
    			(*check the hoare pre-condition rule*)
    			let (phi_ci', allowed) = hoarePre gammacap spec path vi rti 
    			if (allowed) then 
    				let (gamma_potential, phi_ci', isDistinguished) = distinguish gammacap dps spec path vi rti in 
	                if (isDistinguished) then 
	                	Some (dps, vi)  
	                else 
	                   (*~phi_ci'*)
	                   let not_phi_ci' =  Predicate.Not phi_ci' in 
	                   (*D(ci)*)
	                   let dp_ci = 
	                   			try 
	                   				DMap.find dps vi 
	                   			with 
	                   			 	Knowledge.NoMappingForVar e -> DPred.empty

	                   in 
	                   let learnt_knowledge_diff_pred = DPred.DP {gammacap=gamma_potential; learnt=not_phi_ci'} in
	                   (*The two gamma will have overlap, requires thinking*)
	                   let updated_dp_ci = DPred.conjunction dp_ci learnt_knowledge_diff_pred in 
	                   let updated_dps = DMap.replace dps vi updated_dp_ci in 
	                   choice xs gammacap updated_dps 
	             else
	             	

     in 
    let result = choice c_es gammacap dps in 
    match result with
    	| None -> raise (LearningException "ChoiceC Failure")
    	| Some (dps, vi) -> 
    			(dps, vi, path@[vi])



(* 
let deduceR gamma tree compi path spec dp  = 
		??

let learnP gamma tree compi path dp = 

	??

let backtrackC gamma tree compi path dp = 

	??
 *)





(*cdcleffSynthesizeBind : DPred.gammaCap -> DMap.t -> RefTy.t -> Syn.monExp*)
let cdcleffSynthesizeBind (gammaCap : DPred.gammaCap)  
					(dps : DMap.t) (spec : RefTy.t) : Syn.monExp = 
	Message.show "in CDCL";
	
(* 	Message.show ("Gamma at CDCL"^(Gamma.toString (DPred.getGamma gammaCap)));				
 *)	let p = [] in 
	(*the main while loop in the paper*)
	let rec loop gammacap  path spec dpreds =
		let (dps, ci, pi) = chooseC gammacap path spec dpreds  in 
		let (res, dp, tk, ck, pk) = deduceR gammacap ci pi spec dp in 
	    if (res) then 
	    			Syn.buildProgramTerm tk ck pk 
	    else 
	    	let dp = learnP gamma tk ck pk dp in 
	    	let (dp, tj, cj, pj, gamma) = backtrackC gamma tk ck pk dp in 
	    	loop gamma tj pj spec dp
 		*)
		Syn.buildProgramTerm ci pi

	in 

	loop gammaCap p spec dps  




