module Syn = Lambdasyn
module VC = VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Components = Environment.Components
module Explored = Environment.ExploredTerms                 
module VCE = Vcencode 
module DPred = Knowledge.DiffPredicate
module DMap = Knowledge.DistinguisherMap
module P = Predicate  
module SynTC = Syntypechecker




exception SynthesisException of string 
exception Unhandled


module PGMap = Knowledge.PathGammaMap
exception LearningException of string 


open Syn

module Message = struct 

  let show (s:string) = Printf.printf "%s" ("\n"^s) 


end



module Bidirectional : sig
  val itercount : int ref 
  val enumerated : Var.t list ref  
  val subprobplem : Var.t list ref 
  val learnConst : bool 
  val noLearnConst : bool 

  type ('a, 'b) result = 
            Success of 'a 
            | Fail of 'b
            | Terminate


 val enumPureE : Explored.t -> Gamma.t -> Sigma.t -> Predicate.t -> RefTy.t ->  Syn.typedMonExp option 
 val enumerateEffAndFind : Explored.t -> VC.vctybinds -> Sigma.t -> VC.pred list ->  RefTy.t -> (Explored.t * Syn.typedMonExp option) 
 val esynthesizeScalar : Gamma.t -> Sigma.t -> Predicate.t -> RefTy.t -> Syn.typedMonExp option  
 val esynthesizeRet :  Gamma.t -> Sigma.t -> RefTy.t ->  (Syn.typedMonExp option)  

 
 val isynthesizeMatch : VC.vctybinds -> Sigma.t -> Predicate.t -> (Var.t * RefTy.t) -> RefTy.t ->  Syn.typedMonExp option 
 val isynthesizeFun : VC.vctybinds -> Sigma.t -> Predicate.t -> RefTy.t  -> Syn.typedMonExp option
 val esynthesizeFun : Explored.t -> VC.vctybinds -> Sigma.t -> Predicate.t ->  RefTy.t -> (Syn.typedMonExp option)
 val synthesize :  VC.vctybinds -> Sigma.t -> Predicate.t-> RefTy.t -> bool -> Syn.typedMonExp option 


val litercount : int ref   
  type exploredTree = Leaf 
                    | Node of exploredTree list 
  type choiceResult = 
        | Nothing of DMap.t * Predicate.t list 
        | Chosen of (DMap.t * Syn.monExp * path)

  type deduceResult = 
        | Success of path
        | Conflict of { env :DPred.gammaCap; 
                        dps:DMap.t ; 
                        conflictpath : path;
                        conflictpathtype : RefTy.t;
                        disjuncts : Predicate.t list
                        }

   val hoarePre :  DPred.gammaCap -> RefTy.t ->  path -> Syn.monExp -> RefTy.t -> (DPred.gammaCap * Predicate.t * bool)                      
   val distinguish : DPred.gammaCap -> DMap.t -> RefTy.t ->  path -> Var.t -> RefTy.t -> (DPred.gammaCap * Predicate.t * bool)
   
   val chooseC :  DPred.gammaCap -> path -> RefTy.t -> DMap.t -> PGMap.t -> (DPred.gammaCap * PGMap.t * choiceResult)
   val deduceR : DPred.gammaCap -> Syn.monExp ->  path -> RefTy.t -> 
                DMap.t -> PGMap.t -> (DPred.gammaCap * PGMap.t * deduceResult)

   val learnP :  DPred.gammaCap -> DMap.t -> path -> RefTy.t -> Predicate.t list -> DMap.t 
    
   val backtrackC : DPred.gammaCap -> DMap.t -> path -> PGMap.t -> RefTy.t  -> (DPred.gammaCap * path * DMap.t * PGMap.t)
   val cdcleffSynthesizeBind :  DPred.gammaCap ->   DMap.t  -> RefTy.t -> Syn.monExp option
  

end = struct

let itercount = ref 0 
let enumerated = ref [] 
let subprobplem = ref []

let learnConst = true 
let noLearnConst = false

type ('a, 'b) result = 
            Success of 'a 
            | Fail of 'b
            | Terminate



let litercount = ref 0 

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


let enumPureE explored gamma sigma delta (spec : RefTy.t) : Syn.typedMonExp option  = 
    (*can enumerate a variable of refined basetype, an arrow type or a effectful component*)
    match spec with 
      (*Tvar case*)
      | RefTy.Base (v, t, pred) -> 
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
         
         (*filter the explored*)
         
         let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in  
         let rec verifyFound fs  = 
            match fs with
             | [] -> None 
             | (vi, rti) :: xs -> 
                 Message.show ("Show ::  EnumPure "^(Var.toString vi));        
                Message.show ("Show ::  Delta "^(Predicate.toString delta));        
                

                (*substitute, bound variables in both with the argument variable*)
                let rti_bound_vi = RefTy.alphaRenameToVar rti vi in 
                let spec_bound_vi = RefTy.alphaRenameToVar spec vi in 
                let vc = VC.fromTypeCheck gamma [delta] (rti_bound_vi, spec_bound_vi) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                match result with 
                | VCE.Success -> Some {expMon = (Syn.Evar (vi)) ; ofType = rti}
                | VCE.Failure -> verifyFound xs
                | VCE.Undef -> None  
                
         in 
         verifyFound foundTypes
      | RefTy.Arrow ((v, t1), t2) -> 
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
         let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in 
         let rec verifyFound fs  = 
            match fs with
             | [] -> None 
             | (vi, rti) :: xs -> 
                (*filter on effects before actuall checking the hoare triples*) 
            
                let vc = VC.fromTypeCheck gamma VC.empty_delta (rti, spec) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                match result with 
                | VCE.Success -> Some ({expMon=(Syn.Evar (vi)); ofType=rti}) 
                | VCE.Failure -> verifyFound xs
                | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                
         in 
         verifyFound foundTypes

     

      | RefTy.MArrow (eff, pre, (v, t), post) -> 
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
          (*filter the explored*)
         let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in  
                  
         let rec verifyFound fs  = 
            match fs with
             | [] -> None 
             | (vi, rti) :: xs -> 
                (*filter on effects before actuall checking the hoare triples*) 
                let RefTy.MArrow (effi, _,_,_) = rti in  
                if (not (Effect.isSubEffect effi eff))  
                        then verifyFound xs    
                else        
                        let vc = VC.fromTypeCheck gamma VC.empty_delta (rti, spec) in 
                        (*make a direct call to the SMT solver*)
                        let vcStandard = VC.standardize vc in 
                        let result = VCE.discharge vcStandard  in 
                        match result with 
                        | VCE.Success -> let retMonExp = Syn.Eret (Syn.Evar (vi)) in 
                                          Some {expMon = retMonExp; ofType=rti}
                        | VCE.Failure -> verifyFound xs
                        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                        
         in 
         verifyFound foundTypes

      | _ -> raise (SynthesisException "Illegal elimination form")       




let rec enumerateEffAndFind explored gamma sigma delta (spec : RefTy.t)  : (Explored.t * Syn.typedMonExp option) = 
   match spec with 
       | RefTy.MArrow (eff, pre, (v, t), post) -> 
         Message.show ("Spec "^(RefTy.toString spec));
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
         
          (*filter the explored*)
         let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in  
         Message.show "FOUND COMPONENTS ";
         let () = List.iter (fun (vi,_) -> Message.show (Var.toString vi)) foundTypes in 

         (* let () = List.iter (fun (vi, rti) -> Printf.printf "%s" ("\n Gamma |- "^(Var.toString vi)^" : "^(RefTy.toString rti))) foundTypes in           
          *)

         let rec verifyFound explored fs  = 
            let () = Printf.printf "%s" ("\n *********************Enumeration Iteration*****************"^(string_of_int(!itercount))) in
            if (!itercount > 1000) then 
                (* let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in  *)
                raise (SynthesisException "FORCED STOPPED") 
            else 
            let _ = itercount := !itercount + 1 in  
            match fs with
             | [] -> (explored, None) 
             | (vi, rti) :: xs -> 
                (*filter on effects before actuall checking the hoare triples*) 
                let RefTy.MArrow (effi, _,_,_) = rti in  
                if (not (Effect.isSubEffect effi eff))  
                        then verifyFound explored xs    
                else    
                        let _ = enumerated := (vi :: !enumerated) in     
                        let () =Message.show ("Found after Enumeration "^(RefTy.toString rti)) in 
                        let () =Message.show ("Compared Against Spec "^(RefTy.toString spec)) in 
                         try
                              let vc = VC.fromTypeCheck gamma delta (rti, spec) in  

                            (*make a direct call to the SMT solver*)
                            let vcStandard = VC.standardize vc in 
                            Message.show (VC.string_for_vc_stt vcStandard); 
                            let result = VCE.discharge vcStandard  in 
                            match result with 
                            | VCE.Success -> 
                                            let explored = vi :: explored in 
                                            Message.show ("***************Selection Successful************"^(Var.toString vi));    
                                            let retMonExp = Syn.Eret (Syn.Evar (vi)) in 
                                            (explored, Some {expMon = retMonExp; ofType=rti})
                            | VCE.Failure -> 
                                            Message.show ("***************Selection Failed************"^(Var.toString vi));    
                                            verifyFound explored xs
                            | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                            
                             with 
                        VerificationC.Error e -> verifyFound explored xs
          in 
         verifyFound explored foundTypes

      | _ -> raise (SynthesisException ("Effectful Enumeration for non MArrow Type"^(RefTy.toString spec)))  



let createSubts (args : Syn.monExp list) (formals : (Var.t * RefTy.t) list) : (Var.t * Var.t) list =
     if (not (List.length args = List.length formals)) then 
        raise (SynthesisException "The formals and actual arguments size Mismacth") 
     else
        let formalVars = List.map (fun (vi, ti) -> vi) formals in 
        let actualVars = List.map (fun (mei) -> 
                                        match mei with 
                                            | Syn.Evar vi -> vi 
                                            | _ -> raise (SynthesisException "The Normal Form requires applications c
                                                    of the form F (xi, x2,...xn)")
                                        ) args in 
       List.combine (actualVars) (formalVars)                                    



(*The standard hoare-pecondition check
ei is the expression to be added,
and rti is the type for the ei
    *)
let hoarePre gamma spec path ei rti = 
    
    let () =Message.show ("Potential Component/Function  "^(Syn.monExp_toString ei)) in 
    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
    (*TODO :: THE Hoare Rule for effectful function application is not well implemented*)        
    match ei with 
      | Eapp (ci, args) -> 
            let () =Message.show ("Show :: HoarePre Eapp case  "^(Syn.monExp_toString ei)) in 
  
            let uncurriedCompType = 
                match rti with 
                    | RefTy.Arrow ((_,_), _) -> 
                        RefTy.uncurry_Arrow rti
                    | RefTy.Uncurried(_,_) -> rti
                    | _ -> raise (SynthesisException "Illegal Type for Eapp") 
             in 
            let RefTy.Uncurried(formals, retty) =  uncurriedCompType in 
           
            (*Pre[ei/formali] Pre v:t Post[ei/foramli]*)             

            let RefTy.MArrow (_, ci_pre,  (vi,_), ci_post) = retty in 
            (*Pre[ei/formali]*)
            let subs = createSubts args formals in 
            let preWithActuals = Predicate.applySubsts subs ci_pre in 

            (*Post[ei/foramli]*)
            let postWithActuals = Predicate.applySubsts subs ci_post in 

            let vcStandard = 
                if (List.length path > 0) then 
                    
                    let (gammaMap, deltaPred, prefixPathType) =
                                SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in
                         
                 
                    let RefTy.MArrow (_,path_pre,(_,t), path_post) = prefixPathType in 
                        

                    let h_var  = Var.get_fresh_var "h" in 
                    let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                    let h'_var  = Var.get_fresh_var "h'" in 
                    let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

                    let x_var = Var.get_fresh_var "x" in 

                    let gammaMap = Gamma.add gammaMap h_var h_type in 
                    let gammaMap = Gamma.add gammaMap h'_var h'_type in 
                    let gammaMap = Gamma.add gammaMap x_var t in 

                    let post_path_applied = VC.apply path_post 
                            [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
                    (*substitute current heap values for pre*)
                    let ci_pre_applied = VC.apply preWithActuals [(h'_var, TyD.Ty_heap)] in 
                   

                    let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in  
                    let post_path_imp_pre_ci = Predicate.Forall (bvs, P.If (post_path_applied, ci_pre_applied)) in   
                           
                    let vc1 = VC.VC(gammaMap, deltaPred, post_path_imp_pre_ci) in 
                    let vcStandard =  VC.standardize vc1 in 
                    vcStandard
                else
                    let RefTy.MArrow(_,goal_pre,(_,_), goal_post) = spec in 
                    let h_var  = Var.get_fresh_var "h" in 
                    let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                    let gammaMap = Gamma.add gammaMap h_var h_type in 
                    
                    (*gaolpre => rti_pre*)

                    let goal_pre_applied = VC.apply goal_pre [(h_var, TyD.Ty_heap)] in 

                    let ci_pre_applied = VC.apply preWithActuals [(h_var, TyD.Ty_heap)] in 
                                    
                    let bvs = [(h_var, TyD.Ty_heap)] in                
                    let goal_pre_imp_ci_pre = Predicate.Forall (bvs, P.If (goal_pre_applied, ci_pre_applied)) in 
                    let vc1 = VC.VC(gammaMap, deltaPred, goal_pre_imp_ci_pre) in 
                    let vcStandard =  VC.standardize vc1 in 
                    vcStandard

                in                     
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

            let allowed = discharge_vc vcStandard in  
            let gammaCap = DPred.T {gamma=gammaMap;sigma=sigmaMap;delta=deltaPred} in 
            
            (*return the gamma, the formula \phi_post => pre_ci, and result if the compoenent is allowed*)                   
            (*(gammaCap, post_path_imp_pre_ci, allowed)*)
            (*return the gamma, the formula pre_ci, and result if the compoenent is allowed*)                   
            (gammaCap, ci_pre, allowed)

                




      | Evar _ -> 
            let () =Message.show ("Show :: HoarePre Evar case  "^(Syn.monExp_toString ei)) in 
  
            let RefTy.MArrow (_, ci_pre,  (_,_), c_post) = rti in  
                
            let vcStandard= 
             if (List.length path > 0) then 
                (*extract fields from gamma^*)
                (*but this should be typed in the output heap*)
                (*\Gamma |= post_path => pre*)
                
                (*a function generating strongest postcondition for a path*)

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
                vcStandard
             else 
                let RefTy.MArrow(_,goal_pre,(_,_), goal_post) = spec in 
                let h_var  = Var.get_fresh_var "h" in 
                let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                let gammaMap = Gamma.add gammaMap h_var h_type in 
                
                (*gaolpre => rti_pre*)

                let goal_pre_applied = VC.apply goal_pre [(h_var, TyD.Ty_heap)] in 

                let ci_pre_applied = VC.apply ci_pre [(h_var, TyD.Ty_heap)] in 
                                
                let bvs = [(h_var, TyD.Ty_heap)] in                
                let goal_pre_imp_ci_pre = Predicate.Forall (bvs, P.If (goal_pre_applied, ci_pre_applied)) in 
                let vc1 = VC.VC(gammaMap, deltaPred, goal_pre_imp_ci_pre) in 
                let vcStandard =  VC.standardize vc1 in 
                vcStandard
            in         
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

            let allowed = discharge_vc vcStandard in  
            let gammaCap = DPred.T {gamma=gammaMap;sigma=sigmaMap;delta=deltaPred} in 
            
            (*return the gamma, the formula \phi_post => pre_ci, and result if the compoenent is allowed*)                   
            (*(gammaCap, post_path_imp_pre_ci, allowed)*)
            (*return the gamma, the formula pre_ci, and result if the compoenent is allowed*)                   
            (gammaCap, ci_pre, allowed)

        | _ -> raise (LearningException ("Hoare Pre Can be checked on Evar or Eapp, Incorrect Path element "^(Syn.monExp_toString ei)))    

    


(*a routine to verify that the choice ci, in the current gamma satisfies the distinguishing constraints*)
let distinguish gamma dps spec path rti= 
    

    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
    
    let (gammaMap, deltaPred, potential_path_type)= 
        if (List.length path > 0) then 
                let (gammaMap, deltaPred, path_type) = SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in 
                (*construct VCs ci_post => D(ci)*)
                let (gammaMap, deltaPred, potential_path_type) = 
                    match rti with 
                        | RefTy.MArrow (_, _ , (_,_),_) -> 
                                let potential_path = path@[Syn.Evar ci] in 
                                 SynTC.typeForPathSuffix gammaMap sigmaMap deltaPred [(ci, rti)] path_type 
                        | RefTy.Arrow ((_,_),_) ->          
                                let () =  Message.show ("Show An arrow in the potential path HERE ") in
                                raise (LearningException "ARROW POTENTIAL PATH NOT HANDLED")    
               

                in 
                (gammaMap, deltaPred, potential_path_type)
        else 
              let (gammaMap, deltaPred, potential_path_type) = 
                match rti with 
                    | RefTy.MArrow (_, _ , (_,_),_) -> 
                            let potential_path = path@[Syn.Evar ci] in 
                             SynTC.typeForPath gammaMap sigmaMap deltaPred spec potential_path  
                    | RefTy.Arrow ((_,_),_) ->          
                            let () =  Message.show ("Show An arrow in the potential path HERE ") in
                            raise (LearningException "ARROW POTENTIAL PATH NOT HANDLED")    
               in 
               (gammaMap, deltaPred, potential_path_type)

    in            
    let diffpred_ci = 
            try
                DMap.find dps ci 
            with 
                Knowledge.NoMappingForVar e -> DPred.empty
    in          

    let diffpred_ci_gammaCap = DPred.getGammaCap diffpred_ci in 
    let diffpred_ci_learntPred = DPred.getLearnt diffpred_ci in 

    
    Message.show (RefTy.toString potential_path_type);



    let diffpred_ci_learntPred = DPred.getLearnt diffpred_ci in 
(* 
    Message.show "DiffPredicate";
    Message.show ("DISTINGUISH DiffPredicate "^(Predicate.toString diffpred_ci_learntPred));
 *)
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

(*     Message.show ("\n Predicate testsed "^(Predicate.toString pot_path_posti_imp_d_ci));
 *)
    let vcs = [vc2] in 
        
        
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








let learnP gamma dps (path:Syn.path) path_type disjuncts = 
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
        let conflictNode_var = Syn.componentNameForMonExp conflictNode in 
        let dp_conflictNode = 
                                try 
                                    DMap.find dps conflictNode_var 
                                with 
                                    Knowledge.NoMappingForVar e -> DPred.empty

                       in 
                    
        
        let updated_dp_conflictingNode = DPred.conjunction dp_conflictNode learnt_dp in 
        
        let updated_dps = DMap.replace dps conflictNode_var updated_dp_conflictingNode in 
    (*     Message.show ("**************Show :: LearnP Final DPS ********"^(DMap.toString updated_dps));
     *)                           
        (updated_dps)

    

let backtrackC gamma dps path p2gMap spec = 
    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
        

    let conflict_node = List.hd (List.rev path) in  
    let conflictNodeComponent = Syn.componentNameForMonExp conflict_node in 
        
    match previousPath path with 
        | None -> raise (LearningException "No possible backtracking")
        | Some p_kminus1 ->
            try 
                if (List.length p_kminus1 > 0) then 
                    let k_minus1 = List.hd (List.rev p_kminus1) in 
                    let gamma_kminus1 = PGMap.find p2gMap p_kminus1  in 

                    let gammaMap_km1 = DPred.getGamma gamma_kminus1 in 
                    let sigmaMap_km1 = DPred.getSigma gamma_kminus1 in 
                    let deltaPred_km1 = DPred.getDelta gamma_kminus1 in 

                    (*TODO :: This might lead to unsoundness as the two paths will have two different Gamma*)
                    
                    let (gammaMap_km1, deltaPred_km1, type_pkminus1) = SynTC.typeForPath gammaMap_km1 sigmaMap_km1 deltaPred_km1 spec p_kminus1 in 
                    Message.show ("Show >>>>>>>>>>>>>>>"^(RefTy.toString type_pkminus1));
                    let RefTy.MArrow (_, _, (_,_), post_kminus1 ) = type_pkminus1 in 
                    
                    let ann_k_type = Gamma.find gammaMap_km1 conflictNodeComponent in
                    (*the type for the conflict node can be an Arrow*)
                    
                    let ann_k_computation_type = RefTy.findComputationType ann_k_type in 
                                        
                    let RefTy.MArrow (_, pre_k,(_,_),_) = ann_k_computation_type in 

                    let gamma_kminus1 = DPred.T{gamma=gammaMap_km1; sigma = sigmaMap_km1; delta= deltaPred_km1} in 
                    
                    let learnt_predicate = Predicate.Not (Predicate.If (post_kminus1, pre_k)) in 
                    let diffpred_kminus1_k = DPred.DP {gammacap = gamma_kminus1; learnt=learnt_predicate} in 
                    let var_k_minus1 = Syn.componentNameForMonExp k_minus1 in 
                    let dp_kminus1 = 
                                    try 
                                        DMap.find dps var_k_minus1
                                    with 
                                        Knowledge.NoMappingForVar e -> DPred.empty

                    in 
                        
                    let updated_dp_kminus1 = DPred.conjunction dp_kminus1 diffpred_kminus1_k in 
                    let updated_dps = DMap.replace dps var_k_minus1 updated_dp_kminus1 in 
                    (gamma_kminus1, p_kminus1, updated_dps, p2gMap) 
             
                else 
                    (gamma, p_kminus1, dps, p2gMap)     
            with 
                e -> raise e
              (*e -> raise (LearningException ("No gamma for Path "^(pathToString p_kminus1)))*)            



          



(*The function application synthesis for pure componenent, we can try to replace this with say SYPET*)
let rec esynthesizePureApp gamma sigma delta spec : Syn.typedMonExp option = 
    
    (*This is a simplified version of the return typed guided component synthesis as in SYPET*)

    Message.show ("Show esynthesizePureApp ");
    (*TODO :: Filtering pure functions is required*)
    let potentialChoices = Gamma.lambdas4RetType gamma spec in 
    

    (*Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show ("Show Potential Functions");
    Message.show (List.fold_left (fun acc (vi, _) -> acc^", \n Show"^Var.toString vi) " " potentialChoices);
   

    let rec choice potentialChoices gamma sigma delta = 
        match potentialChoices with 
            | [] -> 
                None 
             (*no more effectful components try pure function/constructor application*)
            | (vi, rti) :: xs ->
                Message.show ("Show Pure Component "^(Var.toString vi));
             
                match rti with 
                    | RefTy.Arrow ((varg, argty), _) -> 
                        Message.show (" Show *************** Arrow Component ************"^(Var.toString vi));
                        let uncurried = RefTy.uncurry_Arrow rti in 
                        let RefTy.Uncurried (args_ty_list, retty) = uncurried in 

                        (*Currently the argument is always a scalar/Base Refinement*)
                        Message.show (" Show *************** Synthesizing Args ei : ti for ************"^(Var.toString vi));
                        
                        let e_args =  List.map (fun (argi, argtyi) -> esynthesizeScalar gamma sigma delta argtyi) args_ty_list  in 
                        let all_successful = List.filter (fun e_argi -> match e_argi with 
                                                            | Some ei -> true
                                                            | None -> false) e_args in 
                        let all_successful = List.map (fun (Some ei) -> ei) all_successful in 
                        
                        (*length of synthesized args match with the formal parameter*)
                        let e_allsuccessful = (if ((List.length all_successful) = (List.length args_ty_list)) 
                                                then Some all_successful
                                                else None) in 

                        (match e_allsuccessful with (*BEGIN1*)
                            | None -> (*Atleast one required argument cannot be synthesized thus cannot make the call*)
                                    Message.show (" Show *************** Synthesizing Args ei : Failed for some  arg");
                        
                                    choice xs gamma sigma delta 
                            | Some es -> 
                                let monExps_es = List.map (fun ei -> ei.expMon) es in 
                                let appliedMonExp = Syn.Eapp (Syn.Evar vi, monExps_es) in  (*apply vi e_arg*)
                                Some {expMon= appliedMonExp; ofType=spec}                                  
                                  

                        ) (*END1*)  
                     | _ -> raise (SynthesisException  "Illegeal choice for Pure Application")   


       in 
       choice potentialChoices gamma sigma delta 


and esynthesizeConsApp gamma sigma delta spec : Syn.typedMonExp option  = 

 (*This is a simplified version of the return typed guided component synthesis as in SYPET*)

        let RefTy.Base (v, t, pred) = spec in 
        let exploredCons = Sigma.empty in 
        (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
        let foundCons = Sigma.findCons4retT sigma spec in 
        Message.show "Found Cons";
        let () = List.iter(fun (coname, _) ->  Message.show (coname)) foundCons in 
      

    Message.show ("Show esynthesizeConsApp ");


    (*TODO :: Filtering cons*)
    let potentialChoices = Gamma.lambdas4RetType gamma spec in 
    
    let RefTy.Base (v, t, pred) = spec in 
        (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
    let potentialChoices = Sigma.findCons4retT sigma spec in 
    Message.show "Found Cons";
        

    (*Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show (List.fold_left (fun acc (consName, _) -> acc^", \n Show"^Var.toString consName) " " potentialChoices);
   

    let rec choice potentialChoices gamma sigma delta = 
        match potentialChoices with 
            | [] -> 
                Message.show ("Show No more choices for ConsApp");
                
                None 
             (*no more effectful components try pure function/constructor application*)
            | (vi, rti) :: xs ->
                Message.show ("Show Pure Component "^(Var.toString vi));
                let getExpandedConsType refTy =  
                        (match refTy with
                           | RefTy.Arrow ((_, t1 ), t2) -> 
                                (match t1 with 
                                 | RefTy.Base(va, ta, preda) -> [t1]
                                 | RefTy.Tuple listArgs -> listArgs 
                                 | _ -> raise (SynthesisException ("Illegal Constructor Type "^(RefTy.toString refTy)))
                                )

                           | _ -> raise (SynthesisException "Constructor Type must be an Arrow"))      
                 in 
                 let consArgs = getExpandedConsType rti in 
                 Message.show (" Show *************** Synthesizing Constructor Args ei : ti for ************"^(Var.toString vi));
                
                let e_args =  List.map (fun (cargtyi) -> esynthesizeScalar gamma sigma delta cargtyi) consArgs  in 
                let all_successful = List.filter (fun e_argi -> match e_argi with 
                                                    | Some ei -> true
                                                    | None -> false) e_args in 
                let all_successful = List.map (fun (Some ei) -> ei) all_successful in 
                
                (*length of synthesized args match with the formal parameter*)
                let e_allsuccessful = (if ((List.length all_successful) = (List.length consArgs)) 
                                        then Some all_successful
                                        else None) in 

                (match e_allsuccessful with (*BEGIN1*)
                    | None -> (*Atleast one required argument cannot be synthesized thus cannot make the call*)
                            choice xs gamma sigma delta 
                    | Some es -> 
                        let monExps_es = List.map (fun ei -> ei.expMon) es in 
                        let appliedConsMonExp = Syn.Ecapp (vi, monExps_es) in  (*apply vi e_arg*)
                        Some {expMon= appliedConsMonExp; ofType=spec}                                  
                          

                ) 

       in 
       choice potentialChoices gamma sigma delta 





(*Top lvel goal synthesis for scalar Types*)
and esynthesizeScalar gamma sigma delta spec : Syn.typedMonExp option  = 
    (*TODO Other cases*) 
     Message.show ("Show :: esynthesizeScalar for "^(RefTy.toString spec)); 
     let explored = Explored.empty in    
     let foundbyEnum = enumPureE explored gamma sigma delta spec in 
     match foundbyEnum with 
       | Some t -> 
                  Message.show ("Show :: Found Scalar "^(Syn.typedMonExp_toString t)); 
     
                    Some t       
       | None ->
               Message.show ("Show :: No Scalar found, Call esynthesizePureApp "); 
     
               let appterm = esynthesizePureApp gamma sigma delta spec in 
                match appterm with 
                | Some t1 -> Some t1 
                | None ->
                        Message.show ("Show :: No pureApp found, Call esynthesizeConsApp "); 
      
                        (*constructor application*)
                        let constAppterm = esynthesizeConsApp gamma sigma delta spec in 
                        match constAppterm with 
                          | Some t2 ->  constAppterm
                          | None -> None   
 
(*T-ret rule*)
and  esynthesizeRet gamma sigma spec : (Syn.typedMonExp option)=  
     let 
     RefTy.MArrow (eff, pre, (v, t), post) = spec in
     (match eff with 
       | Effect.Pure -> 
              let RefTy.Base (vi , ti, pred) = t in 
              let retT  = RefTy.applySubsts [(v, vi)] t in
              (*either find a variable in the gamma or find a funapplication term or a constructor application term*)
              let exp = esynthesizeScalar gamma sigma Predicate.True retT in  
              (match exp with 
                | Some e -> Some e 
                | None -> None              
              ) 
       | _ -> None
     )
 




(* TODO :: First implement a special rule for list, then generalize it to ant algebraic type, say tree*)
and isynthesizeMatch gamma sigma delta argToMatch spec : Syn.typedMonExp option = 
    Message.show ("Show :: Synthesize Match "^(RefTy.toString spec));
    let (matchingArg, matchingArgType) = argToMatch in 
    let RefTy.Base(_, argBase, argBasePhi) = matchingArgType in 
     
    Message.show ("Show :: List "^(TyD.toString argBase));
           
 (*list constructor case, work on the genaral case later*)   
  match argBase with 
    | Ty_list _ 
    | Ty_alpha _ -> 
          
          assert (TyD.isList argBase);      
          Message.show ("Show LIST CASE ??"^(TyD.toString argBase)^" PHI "^(Predicate.toString argBasePhi));
          
          let x_var = Var.get_fresh_var "x" in 
          let xs_var = Var.get_fresh_var "xs" in 
          
          let gamma_c= Gamma.add gamma x_var (RefTy.fromTyD (TyD.Ty_int)) in 
          let gamma_c = Gamma.add gamma_c xs_var ((RefTy.fromTyD (TyD.Ty_list TyD.Ty_int))) in 


          let phi_c = SynTC.generateConsConstraints  matchingArg x_var xs_var in 
          let phi_n = SynTC.generateNilConstraints   matchingArg in 
          Message.show ("Show :: "^(Predicate.toString phi_c));
          Message.show ("Show :: "^(Predicate.toString phi_n));


          let delta_n = Predicate.Conj (delta, phi_n) in 
          let delta_c = Predicate.Conj (delta, phi_c) in 


          

          let gamma_n = gamma in 
          let e_n = synthesize gamma_n sigma delta_n spec learnConst in 
          (match e_n with 
            | Some exp_n -> 

                  Message.show ("Show :: Successfully Synthesisized Nil Branch Now Trying Cons");
                  let e_c = synthesize gamma_c sigma delta_c spec learnConst in 
                  (match (e_c) with 
                   | (Some exp_c)-> 
                          Message.show ("Show :: Successfully Synthesisized Cons Branch ");
                  
                          let caseExps = [exp_n; exp_c] in 
                          let consArgs = [[];[x_var;xs_var]] in
                          (*General Case : we will have the constructor name in the Sigma*)
                          let cons = [Var.fromString "Nil"; Var.fromString "Cons"] in 
                          let matchingArg = {Syn.expMon = Syn.Evar matchingArg; 
                                                Syn.ofType = matchingArgType} in  
                          let matchExp = Syn.merge matchingArg cons consArgs caseExps in

                          Some {Syn.expMon = matchExp;
                                Syn.ofType = spec} 
                    | None ->
                            Message.show ("Show :: Failed Synthesisized Cons Branch ");
                   
                            None) 
             | None -> 
                        Message.show ("Show :: Failed Synthesisized Nil Branch");
                        None )           
         
    | _ ->   
        Message.show "Show :: Non List Case";
        synthesize gamma sigma delta spec learnConst 
  
  

                                    


(*Top level syntheis goals for Lambda, same as the traditional syntehsis rules
calls the top-level macthing and application followed by the standard learning based rule *)
and isynthesizeFun gamma sigma delta spec : Syn.typedMonExp option= 
  (*TODO unhandled case of isynthesize*)   
  let uncurried_spec = RefTy.uncurry_Arrow spec in 
  let RefTy.Uncurried ( fargs_type_list, retT) = uncurried_spec  in
  Message.show ("Show "^RefTy.toString uncurried_spec); 
  (*extend gamma*)
  (*first try a match case, if it does not succeed, try the non-matching case*)
  let gamma_extended = Gamma.append  gamma fargs_type_list in 
  (*ASSUMPTION, the argumnet to deconstruct will be at the head*)
  let argToMatch = List.hd (fargs_type_list) in 
  (*Given disjunctions in the spec we can directly try match*)
  Message.show ("Show Trying :: Non-Match case"); 
        (*TODO *make a call to conditional case*)
  let simple_exp = synthesize gamma_extended sigma delta retT learnConst in 
  
       

  match simple_exp with 
    | Some e ->
            Message.show ("Show Found a Non-Match solution"); 
  
            Some e
    | None ->
          Message.show ("Show Non-Match case failed :: Try Match"); 
          let match_expression = isynthesizeMatch gamma_extended sigma delta argToMatch retT in 
          match_expression
        
(*enumerates and finds function term variable of functional type*)
and esynthesizeFun explored gamma sigma delta spec : Syn.typedMonExp option = 
       let foundbyEnum = enumPureE explored gamma sigma delta spec in 
       match foundbyEnum with 
               | Some t -> Some t 
               | None -> 
                     (*if we cannot find a function of the given type we can make a call to iRule for function synthesis*)   
                     isynthesizeFun gamma sigma delta spec               



(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
and  synthesize gamma sigma delta spec learning : (Syn.typedMonExp option)=  
   match spec with 
      | RefTy.Base (v, t, pred) -> 
            Message.show "Show ***********Calling Scalar synthesize***************";
            esynthesizeScalar gamma sigma delta spec  
      | RefTy.Arrow (rta, rtb) -> 
            Message.show "Show ***********Calling S-FUNC synthesize***************";
            isynthesizeFun gamma sigma delta spec  (*applies Tfix and Tabs one after the other*)
      | RefTy.MArrow (eff, pre, t, post) -> (* let res = esynthesizeEff Explored.empty gamma sigma VC.empty_delta spec in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"\n \t --"^(Var.toString vi))) "SUB " !subprobplem) in 
                  *)
              Message.show "Show ***********Calling CDCL synthesize***************";
             (*testing cdcl approach*)
             let gammacap = DPred.T {gamma = gamma; sigma=sigma;delta= delta} in 
             let dps_empty = DMap.empty in 
             let res = 
                if (learning) then 
                 cdcleffSynthesizeBind gammacap dps_empty spec 
                else  
                 NoLearning.cdcleffSynthesizeBind gammacap dps_empty spec 
             in  
             (match res with 
                Some me ->    
                    Some {Syn.expMon=me;Syn.ofType = spec}
                | None -> None     
              )  
                (*main effectful synthesis rules*)
      | _ -> None  


and chooseC gammacap path spec (dps : DMap.t) (p2gMap : PGMap.t) :  (DPred.gammaCap * PGMap.t * choiceResult)= 
    let RefTy.MArrow (eff, pre, (v, t), post) = spec in 
    let gamma = DPred.getGamma gammacap in 
    
    (*This is a simplified version of the return typed guided component synthesis as in SYPET*)

    let c_wellRetType = Gamma.enumerateAndFind gamma spec in 
    let c_wellRetTypeLambda = Gamma.lambdas4RetType gamma spec in 
    
    let c_es = List.filter (fun (vi, ti) -> 
                                let effi = RefTy.get_effect ti in 
                                if (effi = Effect.Pure) then false 
                                else 
                                    Effect.isSubEffect effi eff) gamma (*c_wellRetType*) in 
    

    (*Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show (List.fold_left (fun acc (vi, _) -> acc^", "^Var.toString vi) " " c_es);

    (*choosing a component
    The failing disjunct keeps the list of failing Predicates while checking the Hoare Post => Pre implication*)
    let rec choice potentialChoices 
                    gammacap 
                    dps 
                    (failingDisjuncts : Predicate.t list) 
                    (p2gMap : PGMap.t) : (DPred.gammaCap * PGMap.t * choiceResult)= 
        Message.show "Choice ";
        
        match potentialChoices with 
        | [] -> 
             (*no more effectful components try pure function/constructor application*)


            (gammacap, p2gMap,  Nothing (dps, failingDisjuncts)) 
        | (vi, rti) :: xs ->
                Message.show ("Show Component "^(Var.toString vi));
             
            match rti with 
                | RefTy.Arrow ((varg, argty), _) -> 
                    Message.show (" Show *************** Arrow Component ************"^(Var.toString vi));
                    let uncurried = RefTy.uncurry_Arrow rti in 
                    let RefTy.Uncurried (args_ty_list, retty) = uncurried in 

                    let gammaMap = DPred.getGamma gammacap in 
                    let sigmaMap = DPred.getSigma gammacap in 
                    let deltaPred = DPred.getDelta gammacap in 
                    (*Currently the argument is always a scalar/Base Refinement*)
                    Message.show (" Show *************** Synthesizing Args ei : ti for ************"^(Var.toString vi));
                    
                    let e_args =  List.map (fun (argi, argtyi) -> esynthesizeScalar gammaMap sigmaMap deltaPred argtyi) args_ty_list  in 
                    
                    let all_successful = List.filter (fun e_argi -> match e_argi with 
                                                        | Some ei -> true
                                                        | None -> false) e_args in 
                    let all_successful = List.map (fun (Some ei) -> ei) all_successful in 
                    
                    (*length of synthesized args match with the formal parameter*)
                    let e_allsuccessful = (if ((List.length all_successful) = (List.length args_ty_list)) 
                                            then Some all_successful
                                            else None) in 

                    (match e_allsuccessful with (*BEGIN1*)
                        | None -> (*Atleast one required argument cannot be synthesized thus cannot make the call*)
                                choice xs gammacap dps failingDisjuncts p2gMap
                        | Some es -> 
                            let monExps_es = List.map (fun ei -> ei.expMon) es in 
                            
                            let appliedMonExp = Syn.Eapp (Syn.Evar vi, monExps_es) in  (*apply vi e_arg*)
                            
                            Message.show (" Show *************** Calling Hoare-Pre ************"^(Var.toString vi));
                            (*TODO :: ADD the rule for function application in getting the hoarePre*)
                            let (gammacap, post_imp_phi_ci', allowed) = hoarePre gammacap spec path appliedMonExp rti in
                            
                            if (allowed) then 
                                let () = Message.show (" Show *************** Hoare-Allowed************"^(Var.toString vi)) in 
                                Message.show (" Show *************** Calling Distinguish ************"^(Var.toString vi));
                                let boundVar = Var.get_fresh_var "bound" in 
                                let bound = Syn.Evar (boundVar) in 
                                let doExpForApp = Syn.Edo (bound, appliedMonExp) in 
                                            

                                let (gamma_with_ci, phi_ci', isDistinguished) = distinguish gammacap dps spec path doExpForApp rti in 
                                
                                if (isDistinguished) then 
                                    (* IMPLEMENT TODO :: NEED to add the rule for binding a variable to the return type of call
                                       x_bound <- F (xis) Pre v Post, we must add Post[x_bound/v] in the Gamma*)

                                    let boundVar = Var.get_fresh_var "bound" in 
                                    Message.show (" Show *************** Distinguished : Returning the choice ************"^(Var.toString vi));  
                                    let bound = Syn.Evar (boundVar) in 
                                    let sanitizedRetTy = RefTy.sanitizeMArrow retty in 
                                    Message.show ("Show Sanitized:: "^(RefTy.toString sanitizedRetTy));
                                    
                                    let RefTy.MArrow (_,_,(vret, tret),_) = retty  in 
                                    let RefTy.Base (var4Ret, _,_) = tret in  
                                    let gamma_with_ci = DPred.addGamma (gamma_with_ci) boundVar tret in     
                                    let doExpForApp = Syn.Edo (bound, appliedMonExp) in 
                                    
                                    let new_path = path@[doExpForApp] in 
                                    
                                    (* let retVar = Predicate.getRetVar phi_ci' in 
                                    Message.show ("Show PredicateRet:: "^(Var.toString retVar));
                                
                                    
                                    let boundingSem = Predicate.reduce (boundVar, retVar) phi_ci' in 
                                    
                                    Message.show ("Show_PostWITH_BOUND:: "^(Predicate.toString boundingSem));
                                 *)

                                    let p2gMap = PGMap.add p2gMap (new_path) gamma_with_ci in 
                                    
                                    (*chosen a ci s.t. path--> ci is allowed and distinguished*)
                                    (gamma_with_ci, p2gMap, Chosen (dps, doExpForApp, new_path))  
                                else
                                    (*~phi_ci'*)
                                   let not_phi_ci' =  Predicate.Not phi_ci' in 
                                   Message.show (" Show *************** Not-Distinguished : Now Adding conjunct ************"^(Var.toString vi));
                                   (*D(ci)*)
                                   let dp_ci = 
                                            try 
                                                DMap.find dps vi 
                                            with 
                                                Knowledge.NoMappingForVar e -> DPred.empty

                                   in 
                                   let learnt_diff_conjunct = DPred.DP {gammacap=gamma_with_ci; learnt=not_phi_ci'} in
                                   (*The two gamma will have overlap, requires thinking*)
                                   let updated_dp_ci = DPred.conjunction dp_ci learnt_diff_conjunct in 
                                   let updated_dps = DMap.replace dps vi updated_dp_ci in 
                                   (*make a different choice*)
                                   choice xs gammacap updated_dps failingDisjuncts p2gMap
                                    
                            else (*allowed = false*)
                                let failing_predicate = post_imp_phi_ci' in 
                                Message.show (" Show *************** Hoare-Not-Allowed : Now Adding Disjuncts ************");
                                (*if Case c1...ck ----> vi  , add D (ck) = pre (vi) *)
                                let dps= 
                                    if (List.length path > 0) then 
                                        (*D(ci)*)               
                                        let c_terminial = List.hd (List.rev (path)) in 
                                        let c_terminial_var = componentNameForMonExp c_terminial in 
                                        let dp_cterminal = 
                                                    try 
                                                        DMap.find dps c_terminial_var 
                                                    with 
                                                        Knowledge.NoMappingForVar e -> DPred.empty

                                           in 
                                          
                                        let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate} in
                                           (*The two gamma will have overlap, requires thinking
                                             take disjunction*)
                                        let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in 
                                        let dps = DMap.replace dps c_terminial_var updated_dp_cterminal in 
                                        dps  
                                    else 
                                        dps  
                                in      
                                let failingDisjuncts = failing_predicate :: failingDisjuncts in 
                                choice xs gammacap dps failingDisjuncts p2gMap
                              

                    ) (*END1*)  

            
                | RefTy.MArrow (_,_,(_,_),_) -> 
                
                (*check the hoare pre-condition rule*)
                        let monExpForComp = Syn.Evar vi in     
                        

                        let (gammacap, post_imp_phi_ci', allowed) = hoarePre gammacap spec path monExpForComp rti in 
                        if (allowed) then 
                            (
                            Message.show (" Show *************** Hoare-Allowed : Now Checking distingushing Predicate ************"^(Var.toString vi));
                            let (gamma_with_ci, phi_ci', isDistinguished) = distinguish gammacap dps spec path vi rti in 
                            if (isDistinguished) then 
                                (
                                Message.show (" Show *************** Distinguished : Returning the choice ************"^(Var.toString vi));  
                            (*  Message.show (" Show *************** PGMap Before ************"^(PGMap.toString p2gMap));  
                             *) 
                                let boundVar = Var.get_fresh_var "bound" in 
                                let bound = Syn.Evar (boundVar) in 
                                let doExpForComp = Syn.Edo (bound, monExpForComp) in 
                                

                                let RefTy.MArrow (_,_,(vrti, trti),_) = rti  in
                                let gamma_with_ci = DPred.addGamma (gamma_with_ci) boundVar trti in     
                                    
                                let new_path =  path@[doExpForComp] in 
                                (* let retVar = Predicate.getRetVar phi_ci' in 
                                let bindingSem = Predicate.reduce (boundVar, retVar) phi_ci' in 
                                Message.show ("Show_PostWITH_BOUND:: "^(Predicate.toString boundingSem));
                                *)
                                    
                                let p2gMap = PGMap.add p2gMap new_path gamma_with_ci in 
                            (*  Message.show (" Show *************** PGMap After ************"^(PGMap.toString p2gMap));  
                             *) (*chosen a ci s.t. path--> ci is allowed and distinguished*)
                                (gamma_with_ci, p2gMap, Chosen (dps, doExpForComp, new_path))  
                            )
                            else
                                (Message.show (" Show *************** Not-Distinguished : Now Adding conjunct ************"^(Var.toString vi)); 
                             
                               (*~phi_ci'*)
                               let not_phi_ci' =  Predicate.Not phi_ci' in 
                               (*D(ci)*)
                              
                               let dp_ci = 
                                        try 
                                            DMap.find dps vi 
                                        with 
                                            Knowledge.NoMappingForVar e -> DPred.empty

                               in 

                               let learnt_diff_conjunct = DPred.DP {gammacap=gamma_with_ci; learnt=not_phi_ci'} in
                               (*The two gamma will have overlap, requires thinking*)
                               let updated_dp_ci = DPred.conjunction dp_ci learnt_diff_conjunct in 
                               let updated_dps = DMap.replace dps vi updated_dp_ci in 
                               (*make a different choice*)
                               choice xs gammacap updated_dps failingDisjuncts p2gMap)
                            )   
                         else

                            (
                            Message.show (" Show *************** Hoare-Not-Allowed : Now Adding Disjuncts ************"); 
                            let failing_predicate = post_imp_phi_ci' in 
                            (*if Case c1...ck ----> vi  , add D (ck) = pre (vi) *)
                            let dps= 
                                if (List.length path > 0) then 
                                    (*D(ci)*)               
                                    let c_terminial = List.hd (List.rev (path)) in
                                     let c_terminial_var = componentNameForMonExp c_terminial in 
                                        
                                    let dp_cterminal = 
                                                try 
                                                    DMap.find dps c_terminial_var 
                                                with 
                                                    Knowledge.NoMappingForVar e -> DPred.empty

                                       in 
                                      
                                    let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate} in
                                       (*The two gamma will have overlap, requires thinking
                                         take disjunction*)
                                    let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in 
                                    let dps = DMap.replace dps c_terminial_var updated_dp_cterminal in 
                                    dps  
                                else 
                                    dps  
                            in      
                            let failingDisjuncts = failing_predicate :: failingDisjuncts in 
                            choice xs gammacap dps failingDisjuncts p2gMap
                           )
                         (*?? Add (phi' => phi_ci_pre) as a disjunct in the Differentiating predicate
                 TODO add the disjunction predicate learnt from the failure of choosing a component*)   

     in 
    let failingDisjuncts = [] in  
    choice c_es gammacap dps failingDisjuncts p2gMap
   
 

and deduceR (gamma:DPred.gammaCap) 
            (compi:Syn.monExp) 
            (path:path) 
            (spec: RefTy.t) 
            (dps : DMap.t) 
            (p2gMap : PGMap.t) : (DPred.gammaCap * PGMap.t * deduceResult) = 
    
    Message.show (" EXPLORED :: "^(pathToString path));
        
    if (!litercount > 100) then 
                (* let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in  *)
         raise (LearningException "FORCED STOPPED") 
    else
        let _ = litercount := !litercount + 1 in  
        let gammaMap = DPred.getGamma gamma in 
        let sigmaMap = DPred.getSigma gamma in 
        let deltaPred = DPred.getDelta gamma in 
        

    (*  let (gammaMap, deltaPred, path_type) = SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in 
     *) let (verified, gamma, path_type) = SynTC.typeCheckPath gammaMap sigmaMap deltaPred path spec in 
        
        (*If the path failed for the lack of return type try to synthesize a scalar using the return type*)


        if (verified) then 
             (

                    let () = Message.show ("Show :: Found a correct Path "^(pathToString path)) in 
                    (gamma, p2gMap, Success path)
             ) 
        else 
            (*This is UGLY :( *)
             (
                let RefTy.MArrow (eff, _,(vspecp, tspec),_) = spec in 
                let RefTy.MArrow (effi, _,(vpath, tpath),_) = path_type in 
                let basePath = RefTy.toTyD tpath in 
                let baseSpec = RefTy.toTyD tspec in 
  

                let fillerTest = 
                    
                    if (not (TyD.sametype  basePath baseSpec)) 
                        then(
                            Message.show ("Show :: Return Type Mismacth "^(pathToString path)^
                        " Now checking for a pure component to reach goal type ");
                          let retExp = esynthesizePureApp gammaMap sigmaMap deltaPred tspec in 
                          (match retExp with 
                            | Some e -> 
                                 Message.show ("Show Found a pure component app "^(Syn.typedMonExp_toString e));
                                
                                let boundVar = Var.get_fresh_var "bound" in 
                                let bound = Syn.Evar (boundVar) in 
                                let doExpForPure = Syn.Edo (bound, e.expMon) in 
                                   
                                let completePath = path@[doExpForPure] in 
                                let (verified_complete, gamma_complete, path_type_complete) = 
                                SynTC.typeCheckPath gammaMap sigmaMap deltaPred completePath spec in 
                                (if (verified_complete) then 
                                    let () = Message.show ("Show :: Found correct path "^(Syn.pathToString completePath)) in 
                             
                                    Some (gamma_complete, completePath)
                                else None)      
                          
                            | None -> 
                                 let retExp = esynthesizeConsApp gammaMap sigmaMap deltaPred tspec in 
                                    (match retExp with 
                                    | Some e -> 
                                         Message.show ("Show Found a Cons APP "^(Syn.typedMonExp_toString e));
                                        
                                        let boundVar = Var.get_fresh_var "bound" in 
                                        let bound = Syn.Evar (boundVar) in 
                                        let doExpForPure = Syn.Edo (bound, e.expMon) in 
                                           
                                        let completePath = path@[doExpForPure] in 
                                        let (verified_complete, gamma_complete, path_type_complete) = 
                                        SynTC.typeCheckPath gammaMap sigmaMap deltaPred completePath spec in 
                                        (if (verified_complete) then 
                                            let () = Message.show ("Show :: Found correct path "^(Syn.pathToString completePath)) in 
                                     
                                            Some (gamma_complete, completePath)
                                        else None)      
                                  
                                     | None -> None   
                                   )
                            )                   
                         )else None
                    
                  in       
                match fillerTest with 
                    | Some (completeGamma, completePath) -> (completeGamma, p2gMap, Success completePath)
                    | None -> 
                
                        Message.show ("Show :: Incomplete Path "^(pathToString path)^" Now chosing Next component "^(Syn.monExp_toString compi));
                       
                        let (gamma, p2gMap, nextComponent) = chooseC gamma path spec dps p2gMap in 
                        (match nextComponent with 
                            | Nothing (dps', failingDisjuncts) ->  
                                            Message.show ("Show :: Conflicting path found "^(pathToString path));
                                                (gamma, 
                                                p2gMap, 
                                                Conflict 
                                                {env=gamma;
                                                 dps=dps';
                                                 conflictpath=path;
                                                 conflictpathtype=path_type;
                                                 disjuncts= failingDisjuncts}
                                                )
                            (*see if we also need to return an updated gamma*)                  
                            | Chosen    (dps', ci', pi') -> deduceR gamma ci' pi' spec dps' p2gMap              
                        )
            )



(*cdcleffSynthesizeBind : DPred.gammaCap -> DMap.t -> RefTy.t -> Syn.monExp*)
 and cdcleffSynthesizeBind (gammaCap : DPred.gammaCap)  
                           (dps : DMap.t) 
                           (spec : RefTy.t) : Syn.monExp option= 
    Message.show "Show :: in CDCL";
    
(*  Message.show ("Gamma at CDCL"^(Gamma.toString (DPred.getGamma gammaCap)));              
 *) let p = [] in 
    let pathGammaMap = PGMap.empty in 
    (*the main while loop in the paper*)
    let rec loop gammacap path spec dps path2GammaMap =
        
        Message.show (" EXPLORED :: "^(pathToString path));
                                
        let (gammacap, p2gMap, chooseres) = chooseC gammacap path spec dps path2GammaMap in 
        
        match chooseres with 
            | Nothing _ -> 
                
                if (List.length path > 0) then  
                    let gammaMap = DPred.getGamma gammacap in 
                    Message.show (" Show :: Conflict Path  Found  while backtracking");
                    
                    let sigmaMap = DPred.getSigma gammacap in 
                    let deltaPred = DPred.getDelta gammacap in 
    

                    let conflictpath = path in 
                    
                    let (gammaMap, deltaPred, conflictpathtype) = 
                                SynTC.typeForPath gammaMap sigmaMap deltaPred spec conflictpath in 
                
                    let gammacap = DPred.T {gamma = gammaMap; sigma=sigmaMap; delta= deltaPred} in 
                    

                    (*TODO :: hack passing empty disjunct, but disjuncts are not needed anyway*)
                    let dps = learnP gammacap dps path conflictpathtype [] in 
                    Message.show ("**************Show :: Backtracking From ********"^(pathToString conflictpath));
                    let (gammacap, backpath, dps, p2gMap) = backtrackC gammacap dps conflictpath p2gMap spec in
                    Message.show ("**************Show :: Backtracked To ********"^(pathToString backpath));
                    
                    loop gammacap backpath spec dps p2gMap 
                else            
                    None
            | Chosen (dps', ei, pi) ->  
                
                Message.show (" EXPLORED :: "^(pathToString pi));
                Message.show ("Show :: Chosen "^(Syn.monExp_toString ei));
            (*  Message.show ("New DPS "^(DMap.toString dps));
             *) Message.show(" Run deduceR");
                let (gammacap, p2gMap, deduceres) = deduceR gammacap ei pi spec dps' p2gMap in 
                match deduceres with 
                    | Success p ->
                            Message.show (" EXPLORED :: "^(pathToString p));
             
                            Some (Syn.buildProgramTerm  p)
                    | Conflict {env;dps;conflictpath;conflictpathtype;disjuncts} -> 
                            Message.show (" Show :: Conflict Path  Found  :: Calling learnP Now");
                            (* Message.show ("**************Show :: Printing The Learnt DPS Before LP ********"^((DMap.toString dps)));
                            Message.show ("**************Show :: Printing The CPTYPE Before LP ********"^((RefTy.toString conflictpathtype)));
                            Message.show ("**************Show :: Printing The GammaCap Before LP ********"^((DPred.gammaCapToString env)));
                             *)
                            let dps = learnP env dps conflictpath conflictpathtype disjuncts in 
                            
                        (*  Message.show ("**************Show :: Printing The Learnt DPS Before BT ********"^((DMap.toString dps)));
                         *) Message.show ("**************Show :: Backtracking From ********"^(pathToString conflictpath));
                            
                            
                            let (gammacap, backpath, dps, p2gMap) = backtrackC env dps conflictpath p2gMap spec in
                            Message.show ("**************Show :: Backtracked to ********"^(pathToString backpath));
                            
                            (* Message.show ("**************Show :: Printing The Learnt DPS After BT ********"^((DMap.toString dps)));
                             *)(*  Syn.buildProgramTerm  conflictpath
                             *) 
                             
                            Message.show ("**************Show :: LOOP ********"^(pathToString backpath));
                            (* Message.show ("**************Show :: Printing The GammaCap After BT ********"^((DPred.gammaCapToString env)));
  *)
                            loop gammacap backpath spec dps p2gMap 
                             
                            
                        (*let dp = learnP gamma tk ck pk dp in 
                        let (dp, tj, cj, pj, gamma) = backtrackC gamma tk ck pk dp in 
                        loop gamma tj pj spec dp
                 *)
        
    in 

    loop gammaCap p spec dps pathGammaMap

end



