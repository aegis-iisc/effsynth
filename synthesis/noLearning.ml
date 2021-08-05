module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredPaths  

module VCE = Vcencode 
module P = Predicate  
module SynTC = Syntypechecker
module DPred = Knowledge.DiffPredicate
module DMap = Knowledge.DistinguisherMap
module PGMap = Knowledge.PathGammaMap
exception LearningException of string 
exception Unhandled
open Syn

module Message = struct 

  let show (s:string) = Printf.printf "%s" ("\n"^s) 


end

let itercount = ref 0 

type exploredTree = Leaf 
					| Node of exploredTree list	

type choiceResult = 
		| Nothing of DMap.t * Predicate.t list 
		| Chosen of (DMap.t *  Syn.monExp * path)

type deduceResult = 
		| Success of path
		| Conflict of { env :DPred.gammaCap; 
						dps:DMap.t ; 
						conflictpath : path;
						conflictpathtype : RefTy.t;
						disjuncts : Predicate.t list
						}

(*The standard hoare-pecondition check*)
let hoarePre gamma spec path ci rti = 
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
	
	(* Message.show (">>>>>>>>>>>PATH TYPE "^RefTy.toString path_type);
	 *)
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
	let vcStandard =  VC.standardize vc1 in 
	

	let discharge_vc vcStandard = 
		try
		Message.show ("\n Printing VCs");
        Message.show ("\n"^(VC.string_for_vc_stt vcStandard));      
        let result = VCE.discharge vcStandard  in 
		    match result with 
		    | VCE.Success -> 
		                    Message.show (" Show ***************D (ci) hoarePre Successful************"^(Var.toString ci));
		                    true
		    | VCE.Failure -> 
		    				Message.show (" Show ***************D (ci) hoarePre Failed************"^(Var.toString ci));
		                    false
		    | VCE.Undef -> raise (LearningException "Typechecking Did not terminate")  
		    
		 with
		 	VerificationC.Error e -> raise (LearningException "Checking a distingushing predicate did not terminate")

	in 	 	

	let allowed = discharge_vc vcStandard in  
	let gammaCap = DPred.T {gamma=gammaMap;sigma=sigmaMap;delta=deltaPred} in 
	
	(*return the gamma, the formula \phi_post => pre_ci, and result if the compoenent is allowed*)                   
	(*(gammaCap, post_path_imp_pre_ci, allowed)*)
	(*return the gamma, the formula pre_ci, and result if the compoenent is allowed*)                   
	(gammaCap, ci_pre, allowed)




let rec chooseC gammacap exploredpaths path spec 
	(dps : DMap.t) 
	(p2gMap : PGMap.t) :  (DPred.gammaCap * Explored.t * PGMap.t * choiceResult)= 
    let RefTy.MArrow (eff, pre, (v, t), post) = spec in 
    let gamma = DPred.getGamma gammacap in 
    let c_wellRetType = Gamma.enumerateAndFind gamma spec in 
   
    let c_es = List.filter (fun (vi, ti) -> 
    					let RefTy.MArrow (effi, _,(_,_), _) = ti in 
						Effect.isSubEffect effi eff) c_wellRetType in 
    
    

    (*choosing a component
    The failing disjunct keeps the list of failing Predicates while checking the Hoare Post => Pre implication*)
    let rec choice potentialChoices gammacap exploredpaths dps 
    			(failingDisjuncts : Predicate.t list) 
    			(p2gMap : PGMap.t) : (DPred.gammaCap * Explored.t * PGMap.t * choiceResult)= 
    	Message.show "Choice ";
    	
    	
    	match potentialChoices with 
    		| [] -> 
    		    (gammacap, exploredpaths,  p2gMap,  Nothing (dps, failingDisjuncts)) 
    		| (vi, rti) :: xs -> 
    			
    			let monExp_vi = Syn.Evar vi in  (*apply vi e_arg*)
                            
    			(*check the hoare pre-condition rule*)
    			let potential_path = path@[monExp_vi] in 
    			if (Explored.mem exploredpaths potential_path) then 
    					choice xs gammacap exploredpaths dps failingDisjuncts p2gMap
	            		
				else    
	    			let (gammacap, post_imp_phi_ci', allowed) = hoarePre gammacap spec path vi rti in 
	    			if (allowed) then 
	    				(
	    				Message.show (" Show *************** Hoare-Allowed : ********"^(Var.toString vi));
						(gammacap, exploredpaths, p2gMap, Chosen (dps, monExp_vi, potential_path))  
		                )	
		             else
		             	(
		             	Message.show (" Show *************** Hoare-Not-Allowed : Chose another************"); 
	    				choice xs gammacap exploredpaths dps failingDisjuncts p2gMap
		               )
		
     in 
    let failingDisjuncts = [] in  
    choice c_es gammacap exploredpaths dps failingDisjuncts p2gMap
   


and deduceR (gamma:DPred.gammaCap) exploredpaths (compi:Syn.monExp) (path:path) (spec: RefTy.t) 
				(dps : DMap.t) (p2gMap : PGMap.t) : (DPred.gammaCap * Explored.t * PGMap.t * deduceResult) = 
	Message.show (" EXPLORED :: "^(pathToString path));
	
	
	if (!itercount > 100) then 
                (* let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in  *)
         raise (LearningException "FORCED STOPPED") 
    else
    	let _ = itercount := !itercount + 1 in  
        let gammaMap = DPred.getGamma gamma in 
		let sigmaMap = DPred.getSigma gamma in 
		let deltaPred = DPred.getDelta gamma in 
		

	(* 	let (gammaMap, deltaPred, path_type) = SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in 
	 *)	let (verified, gamma, path_type) = SynTC.typeCheckPath gammaMap sigmaMap deltaPred path spec in 
		
		if (verified) then 
			 (
			 Message.show ("Show :: Found a correct Path "^(pathToString path));
			 (gamma, exploredpaths, p2gMap, Success path)
			 ) 
		else 
			(
				Message.show ("Show :: Incomplete Path "^(pathToString path)^" Now chosing Next component "^(Syn.monExp_toString compi));
			
				let (gamma, exploredpaths, p2gMap, nextComponent) = chooseC gamma exploredpaths path spec dps p2gMap in 
				match nextComponent with 
					| Nothing (dps', failingDisjuncts) ->  
									Message.show ("Show :: Conflicting path found "^(pathToString path));
										(gamma, 
										exploredpaths,
										p2gMap, 
										Conflict 
										{env=gamma;
										 dps=dps';
										 conflictpath=path;
										 conflictpathtype=path_type;
										 disjuncts= failingDisjuncts}
										)
					(*see if we also need to return an updated gamma*)					
					| Chosen	(dps', ci', pi') -> deduceR gamma exploredpaths ci' pi' spec dps' p2gMap				
			)
				 





let learnP gamma dps path path_type disjuncts = 
	(* Message.show ("**************Show :: LearnP For Conflict Path ********"^(pathToString path));
	Message.show ("**************Show :: LearnP Initial DPS ********"^(DMap.toString dps));
	 *)                	
	match path with 
	| [] -> raise (LearningException "learning called on an empty path")
	| x :: xs -> 
		let gammaMap = DPred.getGamma gamma in 
		let sigmaMap = DPred.getSigma gamma in 
		let deltaPred = DPred.getDelta gamma in 
		
		let RefTy.MArrow (eff, phi_k, (v, t), phi_k') = path_type in 
	    let negationPost = Predicate.Not phi_k' in


	    (* let disjunction =  List.fold_left (fun disjunct p -> Predicate.Disj (disjunct, p)) (False) disjuncts  in 
	     *)(*the disjunction is not needed*)
	    (* let learntPredicte = Predicate.Disj (negationPost, disjunction) in 
	     *)
	     let learntPredicte = negationPost in 
	     let learnt_dp = DPred.DP {gammacap = gamma;learnt= learntPredicte } in 

	    let conflictNode = List.hd (List.rev (path)) in 
	(*     Message.show ("**************Show :: LearnP Adding DP for Conflict Node ********"^(Var.toString conflictNode));
	 *)
	    let dp_conflictNode = 
	                   			try 
	                   				DMap.find dps conflictNode 
	                   			with 
	                   			 	Knowledge.NoMappingForVar e -> DPred.empty

	                   in 
	                
	    
	    let updated_dp_conflictingNode = DPred.conjunction dp_conflictNode learnt_dp in 
	    
	    let updated_dps = DMap.replace dps conflictNode updated_dp_conflictingNode in 
	(*     Message.show ("**************Show :: LearnP Final DPS ********"^(DMap.toString updated_dps));
	 *)                           
	    (updated_dps)

	

let backtrackC gamma dps path p2gMap spec = 
	let gammaMap = DPred.getGamma gamma in 
	let sigmaMap = DPred.getSigma gamma in 
	let deltaPred = DPred.getDelta gamma in 
		

	let conflict_node = List.hd (List.rev path) in  
	match previousPath path with 
		| None -> raise (LearningException "No possible backtracking")
		| Some p_kminus1 ->
			 (gamma, p_kminus1, dps, p2gMap)		
			  (*e -> raise (LearningException ("No gamma for Path "^(pathToString p_kminus1)))*)			

(*cdcleffSynthesizeBind : DPred.gammaCap -> DMap.t -> RefTy.t -> Syn.monExp*)
let cdcleffSynthesizeBind (gammaCap : DPred.gammaCap)  
						(dps : DMap.t) 
						(spec : RefTy.t) : Syn.monExp option= 
	Message.show "Show :: in CDCL";
	
(* 	Message.show ("Gamma at CDCL"^(Gamma.toString (DPred.getGamma gammaCap)));				
 *)	let p = [] in 
	let pathGammaMap = PGMap.empty in 
	let exploredpaths = Explored.empty in 
	(*the main while loop in the paper*)
	let rec loop gammacap exploredpaths path spec dps path2GammaMap =
		Message.show (" EXPLORED :: "^(pathToString path));
		         	
		let (gammacap, exploredpaths, p2gMap, chooseres) = chooseC gammacap exploredpaths path spec dps path2GammaMap in 
		
		match chooseres with 
			| Nothing _ -> 
				
				if (List.length path > 0) then  
					let gammaMap = DPred.getGamma gammacap in 
					Message.show (" Show :: Conflict Path  Found  while backtracking");
	             	
					let sigmaMap = DPred.getSigma gammacap in 
					let deltaPred = DPred.getDelta gammacap in 
	

					let conflictpath = path in 
					
					let exploredpaths = Explored.add exploredpaths conflictpath in 
	             			
					
					let gammacap = DPred.T {gamma = gammaMap; sigma=sigmaMap; delta= deltaPred} in 
					

					(*TODO :: hack passing empty disjunct, but disjuncts are not needed anyway*)
					Message.show ("**************Show :: Backtracking From ********"^(pathToString conflictpath));
	             	let (gammacap, backpath, dps, p2gMap) = backtrackC gammacap dps conflictpath p2gMap spec in
	         		Message.show ("**************Show :: Backtracked To ********"^(pathToString backpath));
	             	
	         		loop gammacap exploredpaths backpath spec dps p2gMap 
 				else			
					raise (LearningException "No program and No possible backtracking")
			| Chosen (dps', ci, pi) ->  
				Message.show (" EXPLORED :: "^(pathToString pi));
	    
				Message.show (" ShowPath :: "^pathToString pi);
	    		Message.show ("Show :: Chosen "^(Syn.monExp_toString ci));
				Message.show(" Run deduceR");
				let (gammacap, exploredpaths, p2gMap, deduceres) = deduceR gammacap exploredpaths ci pi spec dps' p2gMap in 
			    match deduceres with 
			    	| Success p -> 
						Message.show (" EXPLORED :: "^(pathToString p));
	    	    		Some (Syn.buildProgramTerm  p)
			    	| Conflict {env;dps;conflictpath;conflictpathtype;disjuncts} -> 
			    			Message.show (" Show :: Conflict Path  Found  ");
	             			let exploredpaths = Explored.add exploredpaths conflictpath in 
	             			Message.show ("**************Show :: Backtracking From ********"^(pathToString conflictpath));
	             			

	             			let (gammacap, backpath, dps, p2gMap) = backtrackC env dps conflictpath p2gMap spec in
	             			Message.show ("**************Show :: Backtracked to ********"^(pathToString backpath));
	             			
	             		
	             			loop gammacap exploredpaths backpath spec dps p2gMap 
 							 
	              			
			    		(*let dp = learnP gamma tk ck pk dp in 
			    		let (dp, tj, cj, pj, gamma) = backtrackC gamma tk ck pk dp in 
			    		loop gamma tj pj spec dp
		 		 *)
		
	in 

	loop gammaCap exploredpaths p spec dps pathGammaMap




