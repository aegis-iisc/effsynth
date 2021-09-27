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
module PTypeMap = Knowledge.PathTypeMap
module P = Predicate  
module SynTC = Syntypechecker
module WPP2CMap = Knowledge.WPPathChildrenMap
module PWPMap = Knowledge.PathWPMap




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
 val synthesize :  VC.vctybinds -> Sigma.t -> Predicate.t-> RefTy.t -> bool -> bool -> int ->  Syn.typedMonExp option 


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

   val hoarePre :  DPred.gammaCap -> PTypeMap.t -> RefTy.t ->  path -> Syn.monExp -> RefTy.t -> (DPred.gammaCap * PTypeMap.t * Predicate.t * bool)                      
   val distinguish : DPred.gammaCap -> PTypeMap.t -> DMap.t -> RefTy.t ->  path -> Syn.monExp -> RefTy.t -> 
                                    (DPred.gammaCap * Predicate.t * PTypeMap.t * Predicate.t * bool)
   
   val chooseC :  DPred.gammaCap -> path -> RefTy.t -> DMap.t -> PGMap.t ->  PTypeMap.t ->  
                                                                (DPred.gammaCap * PGMap.t * PTypeMap.t * choiceResult)
   val deduceR : DPred.gammaCap -> Syn.monExp ->  path -> RefTy.t -> 
                DMap.t -> PGMap.t -> PTypeMap.t -> (DPred.gammaCap * PGMap.t * PTypeMap.t * deduceResult)

   val learnP :  DPred.gammaCap -> DMap.t -> path -> RefTy.t -> Predicate.t list -> DMap.t 
    
   val backtrackC : DPred.gammaCap -> PTypeMap.t -> DMap.t -> path -> PGMap.t -> RefTy.t  -> (DPred.gammaCap * path * DMap.t * PGMap.t * PTypeMap.t)
   val cdcleffSynthesizeBind :  DPred.gammaCap ->   DMap.t  -> RefTy.t -> Syn.monExp option
  
   val createWP : VC.vctybinds ->  RefTy.t -> Predicate.t ->  
            ((Var.t * TyD.t)* (Var.t * TyD.t)) list -> (VC.vctybinds * Predicate.t)
     

end = struct

let itercount = ref 0 
let enumerated = ref [] 
let subprobplem = ref []

let tryCount = ref 0

let learnConst = true 
let noLearnConst = false
let bidirectional = ref false
let maxPathLength = ref 0
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
let hoarePre gamma ptypeMap spec path ei rti = 
    
    let () =Message.show ("Potential Component/Function  "^(Syn.monExp_toString ei)) in 
    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
        
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
                    
                    let (gammaMap, deltaPred, ptypeMap, prefixPathType) =
                                SynTC.typeForPath ptypeMap gammaMap sigmaMap deltaPred spec path in
                         
                 
                    let RefTy.MArrow (_,path_pre,(_,t), path_post) = prefixPathType in 
                        
                    (*hoarePre Query
                    given pre_path = \FA h. P
                          post_path = \FA h, v, h'. Q
                          ci_pre = \FA h. Pre_ci
                        -> 
                        \FA h0 v0 h0'.
                           P h0 /\ Q h0 v0 h0' => Pre_ci h0 
                       *)    
                    let h_var  = Var.get_fresh_var "h" in 
                    let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                    let h'_var  = Var.get_fresh_var "h'" in 
                    let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

                    let x_var = Var.get_fresh_var "x" in 

                    let gammaMap = Gamma.add gammaMap h_var h_type in 
                    let gammaMap = Gamma.add gammaMap h'_var h'_type in 
                    let gammaMap = Gamma.add gammaMap x_var t in 

                    let pre_path_applied = VC.apply path_pre [(h_var, TyD.Ty_heap)] in 

                    let post_path_applied = VC.apply path_post 
                            [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
                    (*substitute current heap values for pre*)
                    let ci_pre_applied = VC.apply preWithActuals [(h'_var, TyD.Ty_heap)] in 
                   

                    let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in  
                    let post_path_imp_pre_ci = Predicate.Forall (bvs, P.If (
                                                                        P.Conj (
                                                                        pre_path_applied, post_path_applied
                                                                        ), ci_pre_applied)) in   
                           
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
            (gammaCap, ptypeMap, ci_pre, allowed)

                




      | Evar _ -> 
            let () =Message.show ("Show :: HoarePre Evar case  "^(Syn.monExp_toString ei)) in 
  
            let RefTy.MArrow (_, ci_pre,  (_,_), c_post) = rti in  
                
            let vcStandard= 
             if (List.length path > 0) then 
                (*extract fields from gamma^*)
                (*but this should be typed in the output heap*)
                (*\Gamma |= post_path => pre*)
                
                (*a function generating strongest postcondition for a path*)

                let (gammaMap, deltaPred, ptypeMap, path_type) = SynTC.typeForPath ptypeMap gammaMap sigmaMap deltaPred spec path in 
                
                (* Message.show (">>>>>>>>>>>PATH TYPE "^RefTy.toString path_type);
                 *)
                let RefTy.MArrow (_,pre_path,(_,t), post_path) = path_type in 
                
                (*hoarePre Query
                    given pre_path = \FA h. P
                          post_path = \FA h, v, h'. Q
                          ci_pre = \FA h. Pre_ci
                        -> 
                        \FA h0 v0 h0'.
                           P h0 /\ Q h0 v0 h0' => Pre_ci h0 
                *)

                let h_var  = Var.get_fresh_var "h" in 
                let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                let h'_var  = Var.get_fresh_var "h'" in 
                let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

                let x_var = Var.get_fresh_var "x" in 

                let gammaMap = Gamma.add gammaMap h_var h_type in 
                let gammaMap = Gamma.add gammaMap h'_var h'_type in 
                let gammaMap = Gamma.add gammaMap x_var t in 

                let pre_path_applied = VC.apply pre_path [(h_var, TyD.Ty_heap)] in 

                let post_path_applied = VC.apply post_path [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
                (*substitute current heap values for pre*)
                let ci_pre_applied = VC.apply ci_pre [(h'_var, TyD.Ty_heap)] in 
               

                let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in  
                let post_path_imp_pre_ci = Predicate.Forall (bvs, P.If (
                                                                    P.Conj(
                                                                    pre_path_applied,
                                                                    post_path_applied
                                                                    ), ci_pre_applied)) in   
                       
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
            (gammaCap, ptypeMap, ci_pre, allowed)

        | _ -> raise (LearningException ("Hoare Pre Can be checked on Evar or Eapp, Incorrect Path element "^(Syn.monExp_toString ei)))    

    


(*a routine to verify that the choice ci, in the current gamma satisfies the distinguishing constraints*)
let distinguish gamma ptypeMap dps spec path ci rti= 
    
    let ci_name = Syn.componentNameForMonExp ci in 
    
     Message.show (" Show ***************Distinguish Call************"^(Var.toString ci_name));
    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
    let potential_path = path@[ci] in 

    let (gammaMap, deltaPred, ptypeMap,  potential_path_type) = 
                SynTC.typeForPath ptypeMap gammaMap sigmaMap deltaPred spec potential_path in 
    


    let RefTy.MArrow (_,potential_path_pre,(_,t), potential_path_post) = 
        potential_path_type in 
    

    
    
    let diffpred_ci = 
            try
                DMap.find dps ci_name 
            with 
                Knowledge.NoMappingForVar e -> DPred.empty
    in          


    
    let diffpred_ci_gammaCap = DPred.getGammaCap diffpred_ci in 
    let diffpred_ci_learntPred = DPred.getLearnt diffpred_ci in 
    let previous = DPred.getPrevious diffpred_ci in 


    let gammaMap4vc2 = gammaMap@(DPred.getGamma diffpred_ci_gammaCap) in 
    let deltaPred4vc2 = Predicate.Conj(deltaPred, (DPred.getDelta diffpred_ci_gammaCap)) in  
   
    (*till we have not seen ci in a conflict node*)
    if (diffpred_ci_learntPred == P.True 
        || DPred.noConjuncts diffpred_ci_learntPred) then
         (*Trivial case sp (pre, (path :: ci)) => True*)
          let () = Message.show ("Show ***********DiffPredicate "^(Predicate.toString diffpred_ci_learntPred)) in 
          Message.show (" Show ***************Checking ~ (D(ci).previous => sp (pre, (path :: ci))************"^(Var.toString ci_name));
          
         
          if (previous = P.True || Syn.pathLength path < 2) then  (*first visit*) 
             let () = Message.show (" Show ************ D(ci).previous == True "^(Predicate.toString previous)) in 
             let gammaCapPotential = 
              DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                    (gammaCapPotential, potential_path_post, ptypeMap,  potential_path_post, true)
          else (*Syn.pathLength >= 2*)
                (*The semantic apporach is not working, let us trying syntactic unrolling of depth 2.
                i.e. we only allow ci.ci.cj and never ci.ci.ci.cj*)
                
                (*get the last two components from the path*)
                let lastCMonExp = List.hd (List.rev path) in 
                let penultimateCMonExp = Syn.previousComponent path in
                match penultimateCMonExp with 
                    | None -> 
                        let gammaCapPotential = 
                        DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                        (gammaCapPotential, potential_path_post, ptypeMap,  potential_path_post, true)
                    | Some mexp -> 
                        let ultimateCName = Syn.componentNameForMonExp lastCMonExp in 
                        let penultimateCName = Syn.componentNameForMonExp mexp in 
                        if (Var.equal (ci_name) ultimateCName && Var.equal (ci_name) penultimateCName) then 
                            let gammaCapPotential = 
                            DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                            (gammaCapPotential, potential_path_post, ptypeMap,  potential_path_post, false)
                        else 
                            let gammaCapPotential = 
                            DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                            (gammaCapPotential, potential_path_post, ptypeMap,  potential_path_post, true)
                                

                (*construct and check VC D(ci).previous =>  sp (pre, (path :: ci)) (ci)
                return false
                *)
                (* let () = Message.show (" Show ************ D(ci).previous != True | Previous = "^(Predicate.toString previous)) in 
                let () = Message.show (" Show ************ pre =  "^(Predicate.toString potential_path_pre)) in 
                
                let () = Message.show (" Show ************ sp (pre, path :: ci) =  "^(Predicate.toString potential_path_post)) in 
                
                let h_var  = Var.get_fresh_var "h" in 
                let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

                let h'_var  = Var.get_fresh_var "h'" in 
                let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

                let x_var = Var.get_fresh_var "x" in 

                let gammaMap  = Gamma.add gammaMap h_var h_type in 
                let gammaMap = Gamma.add gammaMap h'_var h'_type in 
                let gammaMap = Gamma.add gammaMap  x_var t in 

                let pre_applied =
                            VC.apply potential_path_pre 
                                        [(h_var, TyD.Ty_heap)] in 
                 

                let sp_applied = VC.apply potential_path_post 
                                        [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
                
            
                 (*substitute current heap values for D(ci).previous *)
                let d_ci_prev_applied = 
                        VC.apply previous [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 

       

                let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in  
                let previous_imp_sp = Predicate.Forall (bvs, P.If (P.Conj(pre_applied, 
                                                            d_ci_prev_applied), sp_applied)) in   
                
                let vc_progress = VC.VC(gammaMap4vc2, deltaPred4vc2, previous_imp_sp) in 


                let vc_progress_st = VC.standardize vc_progress in 
                
                

                let noProgress = 
                    Message.show ("\n Printing VC");
                    Message.show ("\n"^(VC.string_for_vc_stt vc_progress_st));      
                   
                     match (VCE.discharge vc_progress_st) with 
                        | VCE.Success ->
                                        true
                        | VCE.Failure -> 
                                        false
                                        
                        | VCE.Undef -> raise (LearningException "Typechecking Did not terminate")  
                        
            
                in      
               
               if (noProgress) then 
                    let () = Message.show (" Show ************ (D(ci).previous => sp (pre, path :: ci)  ") in      
                    let gammaCapPotential = 
                     DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                        (gammaCapPotential, previous, ptypeMap,  potential_path_post, false)
                else 
                    let () = Message.show (" Show ************ NOT (D(ci).previous => sp (pre, path :: ci)  ") in      
                    let gammaCapPotential = 
                     DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
                        (gammaCapPotential, previous, ptypeMap,  potential_path_post, true)
                 *)                  

                            
             

    else
        (*construct and check VCs sp (pre, (path :: ci)) => D(ci)*)
        let () =   Message.show (" Show ***************DISTINGUISH DiffPredicate != True ************"^(Predicate.toString diffpred_ci_learntPred)) in 
   

        let h_var  = Var.get_fresh_var "h" in 
        let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

        let h'_var  = Var.get_fresh_var "h'" in 
        let h'_type = RefTy.fromTyD (TyD.Ty_heap) in 

        let x_var = Var.get_fresh_var "x" in 

        let gammaMap  = Gamma.add gammaMap h_var h_type in 
        let gammaMap = Gamma.add gammaMap h'_var h'_type in 
        let gammaMap = Gamma.add gammaMap  x_var t in 


        let pot_path_post_applied = VC.apply potential_path_post 
                                [(h_var, TyD.Ty_heap);(x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in 
        
              

        (*substitute current heap values for D(ci).learnt*)
        let d_ci_applied_h' = VC.apply diffpred_ci_learntPred [(h'_var, TyD.Ty_heap)] in 
       

        let bvs = [(h_var, TyD.Ty_heap); (x_var, RefTy.toTyD t); (h'_var, TyD.Ty_heap)] in  
        let pot_path_posti_imp_d_ci = Predicate.Forall (bvs, P.If (pot_path_post_applied, d_ci_applied_h')) in   

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
            Message.show (" Show ***************D (ci) Successful************"^(Var.toString ci_name))
        else 
            Message.show ("Show ***************Selection Failed************"^(Var.toString ci_name))
        
        in                   
        let gammaCapPotential = DPred.T {gamma=gammaMap4vc2;sigma=sigmaMap;delta=deltaPred4vc2} in 
        (gammaCapPotential, previous, ptypeMap,  potential_path_post, isDistinguished)



let createWP (gammaMap: VC.vctybinds) 
            (ciSpec : RefTy.t) (qPost : Predicate.t) 
            (subst : ((Var.t * TyD.t)* (Var.t * TyD.t)) list) : (VC.vctybinds * Predicate.t) = 
        let RefTy.Uncurried (formals, retty) = RefTy.uncurry_Arrow ciSpec in 
        let RefTy.MArrow (eff, pre, (vret, tret), post) = retty in 

        Message.show ("Show  :: Pre Initial "^(Predicate.toString pre)) ;
        Message.show ("Show  :: Post Initial "^(Predicate.toString pre)) ;
        
        
        let h = Var.get_fresh_var "h" in 
        let h' = Var.get_fresh_var "h'" in 
        let v = Var.get_fresh_var "v" in 

        let gammaMap = VC.extend_gamma (h, (RefTy.lift_base Ty_heap)) gammaMap in 
        let gammaMap = VC.extend_gamma (h', (RefTy.lift_base Ty_heap)) gammaMap in 
        let gammaMap = VC.extend_gamma (v, (tret)) gammaMap in 
    
        let pre_applied = VC.apply pre [(h, TyD.Ty_heap)] in
        let post_applied = VC.apply post [(h, TyD.Ty_heap); (v, RefTy.toTyD (tret));
                                                            (h', TyD.Ty_heap)] in 

        Message.show ("Show  :: Pre_applied "^(Predicate.toString pre_applied));
        Message.show ("Show  :: Post_applied "^(Predicate.toString post_applied));
                                                    
        (*wp = \forall Q h. Pre h /\ \forall v', h. Post h v h' => Q v h'*)
        Message.show ("Enter");
        let bvsQ = Predicate.getBVs qPost in 
        (*TODO Ugly for now, think of a funcamental way of distinguishing between the 
            goal post and other weakest-pres acting as post*)
         let qPost_applied = 
            if (List.length bvsQ = 1)
                then VC.apply qPost [(h', TyD.Ty_heap)]
            else if (List.length bvsQ = 3) then  
                VC.apply qPost [(h, TyD.Ty_heap); (v, RefTy.toTyD (tret));
                                                            (h', TyD.Ty_heap)]
            else 
                raise (SynthesisException "qPost should have form forall h v h. Q or forall h. Q")                                                            
        in 
        Message.show ("Exit");

        let pre_applied = VC.subst subst pre_applied in 
        let post_applied = VC.subst subst post_applied in 

        Message.show ("Show  :: Pre_actual2Foraml "^(Predicate.toString pre_applied));
        Message.show ("Show  :: Post_actual2Foraml "^(Predicate.toString post_applied));
                                                    
        let bvs_inner = [(v, RefTy.toTyD (tret));(h', TyD.Ty_heap)] in 
        let innerPred = Predicate.Forall (bvs_inner, Predicate.If (post_applied, qPost_applied)) in 
        let outerPred = Predicate.Forall ([(h, TyD.Ty_heap)], 
                                            Predicate.Conj(pre_applied, innerPred)) in 
        
         
        Message.show ("Show  :: Weakest Precondition "^(Predicate.toString outerPred)) ;

        (gammaMap, outerPred)


(* let wpForPath (gammaMap: VC.vctybinds) 
              (ciSpec : RefTy.t) 
              (qPost : Predicate.t) 
              (subst : ((Var.t * TyD.t)* (Var.t * TyD.t)) list) : (VC.vctybinds * Predicate.t) = 
 *)

type wpresult =   Continue 
                | Flip (*Change Direction with information for the forward pass and a lookahead decision*) 
                | Break (*Change Direction without any lookahead*)
                | Complete 

let wpPreCheck gamma sigma delta wp : wpresult =
    
    Message.show ("\n Printing WP "^(Predicate.toString wp));
             
    let wp_weaker = Predicate.weakenWP wp in 
    Message.show ("\n Printing WP_WEAKER "^(Predicate.toString wp_weaker));
    
    let wpVC = VC.VC(gamma, delta, wp_weaker) in 


    let wpStandard = VC.standardize wpVC  in 
    

    
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

      Message.show ("\n Printing VCs");
      Message.show ("\n"^(VC.string_for_vc_stt wpStandard));      
      
    
    let wpCheck = discharge_vc wpStandard in 
    
    if (wpCheck) then 
        
        Continue 
    else 
        (*TODO :: expand on FLIP and BREAK CASES*)
       Break   
    







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
        
        let conflictNode = List.hd (List.rev (path)) in 
        let conflictNode_var = Syn.componentNameForMonExp conflictNode in 
        
        (*get the older D(conflict) *)
        let dp_conflictNode = 
                                try 
                                    DMap.find dps conflictNode_var 
                                with 
                                    Knowledge.NoMappingForVar e -> DPred.empty

        in 
                    
        
        (*updating the D(conflict)*)
        let RefTy.MArrow (eff, phi_k, (v, t), phi_k') = path_type in 
        let negationPost = Predicate.Not phi_k' in


        let learntPredicte = negationPost in 
        let learnt_dp = DPred.DP {gammacap = gamma;learnt= learntPredicte; previous=DPred.getPrevious dp_conflictNode} in 

        
        let updated_dp_conflictingNode = DPred.conjunction dp_conflictNode learnt_dp in 
        let updated_dps = DMap.replace dps conflictNode_var updated_dp_conflictingNode in 
                                   
        (updated_dps)

    

let backtrackC gamma ptypeMap dps path p2gMap spec = 
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
                    
                    let (gammaMap_km1, deltaPred_km1, ptypeMap, type_pkminus1) = SynTC.typeForPath ptypeMap gammaMap_km1 sigmaMap_km1 deltaPred_km1 spec p_kminus1 in 
                    Message.show ("Show >>>>>>>>>>>>>>>"^(RefTy.toString type_pkminus1));
                    
                    let var_k_minus1 = Syn.componentNameForMonExp k_minus1 in 
                    (*get the older D (Terminal (pk-1)*)
                    let dp_kminus1 = 
                                    try 
                                        DMap.find dps var_k_minus1
                                    with 
                                        Knowledge.NoMappingForVar e -> DPred.empty

                    in 
                    
                    let RefTy.MArrow (_, _, (_,_), post_kminus1 ) = type_pkminus1 in 
                    
                    let ann_k_type = Gamma.find gammaMap_km1 conflictNodeComponent in
                    (*the type for the conflict node can be an Arrow*)
                    
                    let ann_k_computation_type = RefTy.findComputationType ann_k_type in 
                                        
                    let RefTy.MArrow (_, pre_k,(_,_),_) = ann_k_computation_type in 

                    let gamma_kminus1 = DPred.T{gamma=gammaMap_km1; sigma = sigmaMap_km1; delta= deltaPred_km1} in 
                    
                    let learnt_predicate = Predicate.Not (Predicate.If (post_kminus1, pre_k)) in 
                    let diffpred_kminus1_k = DPred.DP {gammacap = gamma_kminus1; learnt=learnt_predicate;
                                                        previous=DPred.getPrevious dp_kminus1} in 
                        
                    let updated_dp_kminus1 = DPred.conjunction dp_kminus1 diffpred_kminus1_k in 
                    let updated_dps = DMap.replace dps var_k_minus1 updated_dp_kminus1 in 
                    (gamma_kminus1, p_kminus1, updated_dps, p2gMap, ptypeMap) 
             
                else 
                    (gamma, p_kminus1, dps, p2gMap, ptypeMap)     
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
          let e_n = synthesize gamma_n sigma delta_n spec learnConst !bidirectional !maxPathLength in 
          (match e_n with 
            | Some exp_n -> 

                  Message.show ("Show :: Successfully Synthesisized Nil Branch Now Trying Cons");
                  let e_c = synthesize gamma_c sigma delta_c spec learnConst !bidirectional !maxPathLength in 
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
        synthesize gamma sigma delta spec learnConst !bidirectional !maxPathLength
  
  

                                    


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
  let simple_exp = synthesize gamma_extended sigma delta retT learnConst !bidirectional !maxPathLength in 
  
       

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


(*The main entry for the synthesize*)
(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
and  synthesize  gamma sigma delta spec learning  bi max : (Syn.typedMonExp option)=  
   bidirectional := bi;
   maxPathLength := max;
   match spec with 
      | RefTy.Base (v, t, pred) -> 
            Message.show "Show ***********Calling Scalar synthesize***************";
            esynthesizeScalar gamma sigma delta spec  
      | RefTy.Arrow (rta, rtb) -> 
            Message.show "Show ***********Calling S-FUNC synthesize***************";
            isynthesizeFun gamma sigma delta spec  (*applies Tfix and Tabs one after the other*)
      | RefTy.MArrow (eff, pre, (v,t), post) -> (* let res = esynthesizeEff Explored.empty gamma sigma VC.empty_delta spec in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"\n \t --"^(Var.toString vi))) "SUB " !subprobplem) in 
                  *)
            let initialPost = post in 

             (*testing cdcl approach*)
            let gammacap = DPred.T {gamma = gamma; sigma=sigma;delta= delta} in 
            let dps = DMap.empty in 
            let uncurriedSpec = RefTy.uncurry_Arrow spec in 
            let RefTy.Uncurried (formals, bodyType) = uncurriedSpec in 
            let RefTy.MArrow (eff, pre, (v, t), post) = bodyType in 
            
            let initialP = [(Syn.Ehole t)] in
            let requiredEff = RefTy.get_effect spec in 
            let initial_path2WPMap = PWPMap.empty in 
            let initial_path2WPMap = PWPMap.add initial_path2WPMap initialP initialPost in 
            let initial_path2VisitedMap = WPP2CMap.empty in 
           
            let rec bidirectionalSearch 
                            (path2wpMap : PWPMap.t)
                            (path2visitedMap : WPP2CMap.t)
                            (gammacap : DPred.gammaCap) 
                            (path: Syn.path) 
                            (eff : Effect.t)
                            (pre : Predicate.t)  
                            (post : Predicate.t) : Syn.typedMonExp option =
    

                            
                if (learning) then 
                    if (!bidirectional) then
                        
                        (*initial path H1 : pair*)
                     let () = Message.show ("Show EXPLORED :: "^Syn.pathToString path) in 
                   
                    let () = Message.show "Show ***********Calling weakestPreSynththesis***************" in 
                    if (!itercount >= 3) then 
                            None 
                    else 
                        let () = itercount := !itercount + 1 in 
                        let (path2wpMap, path2visitedMap, wp, backpath, gammacap', wpresult) = 
                                weakestPreSynththesis path2wpMap 
                                                            path2visitedMap
                                                            gammacap path eff pre post  in 
                       
                        match wpresult with 
                            | Complete -> 
                                        Message.show "Show ***********WP : COMPLETE ***************";
                                        Some {Syn.expMon=Syn.buildProgramTerm backpath;Syn.ofType = spec}
                            | _ ->     
                                    Message.show "Show ***********WP : FLIP/BREAK : Calling CDCL ***************";
                                   (*if there are holes in the backpath, find the last hole and try makes the forward call
                                   TODO This must be transformed into a Sigma synthesis*)
                                   Message.show ("Show WP : BackwardPath "^(Syn.pathToString backpath));
                                   let (lastHole, prefix, suffix) = Syn.getLastHole backpath in 
                                   (*if the backpath has hole then ret type is last hole type
                                   else 
                                    ret type = Top*)
                                   let topType = 
                                      match lastHole with 
                                        | None -> RefTy.fromTyD (TyD.Ty_unknown) 
                                        | Some h -> 
                                           let (_, terminal_holeType)  = 
                                                (match h with 
                                                 | Syn.Ehole t -> (None, t) 
                                                 | Syn.Edo (bound, hole) -> (match hole with
                                                                         | Syn.Ehole t -> (Some bound, t)
                                                                         | _ -> raise (SynthesisException "Illegeal Hole Expression") )
                                                 | _ -> raise (SynthesisException "Hole can be of the form [??:t] | do x <- [??:t]")
                                                ) 
                                               in  terminal_holeType
                                   in                   

                                   (* 
                                   let topType = RefTy.fromTyD (TyD.Ty_unknown) in 
                                    *)(* raise (SynthesisException "FORCE-STOPPED POST BACKWARD");
                                    *)
                                    (*Current Algorithm does not use the backpath*)
                                    let new_forward_spec = RefTy.MArrow (eff, pre, (v,topType), wp) in 
                                    let forwardRes = cdcleffSynthesizeBind gammacap' dps new_forward_spec in 
                                    (match forwardRes with 
                                        | Some fres -> 
                                            let backres = Syn.buildProgramTerm backpath in 
                                            Some {Syn.expMon = (Syn.Edo (fres, backres)); 
                                                    Syn.ofType = spec}
                                        | None -> 
                                            (*remove the path till the last decision level 
                                                backpath = H1 -> H2 ....C1 -> C2....Ck 
                                                backtrack to c2 .....Ck 

                                                *)
                                            let backtrackingPath = 
                                                if (List.length suffix > 1) then List.tl suffix
                                                else initialP    
                                            in     
                                            let wp4back = 
                                                if (List.length backtrackingPath = 0) then 
                                                    initialPost
                                                else 
                                                    (try
                                                        PWPMap.find path2wpMap backtrackingPath 
                                                    with 
                                                      | e -> raise (SynthesisException ("NO Mapping "^(Syn.pathToString backtrackingPath))); )
                                            in 
                                            (*A map tracking last visited children for a backward path*)
                                            bidirectionalSearch path2wpMap path2visitedMap 
                                                                            gammacap 
                                                                                backtrackingPath eff pre wp4back 
                                            
                                    )                                            
                          
                                               
                                      
                                    
                    else
                        let () = Message.show "Show ***********Bidirection FALSE : Calling CDCL***************" in 
                        let res = cdcleffSynthesizeBind gammacap dps spec in 
                        (match res with 
                            | Some me ->  Some {Syn.expMon = me; 
                                                    Syn.ofType = spec}
                            | None -> None                         )
                else 
                    let res = cdcleffSynthesizeBind gammacap dps spec in 
                 
                    (match res with 
                            | Some me ->  Some {Syn.expMon = me; 
                                                    Syn.ofType = spec}
                            | None -> None                         )
                 (* NoLearning.cdcleffSynthesizeBind gammacap dps_empty spec  *)
             in  
             
             bidirectionalSearch initial_path2WPMap initial_path2VisitedMap gammacap initialP requiredEff pre post 
                       
                
      | _ -> None  


and chooseC gammacap path spec (dps : DMap.t) (p2gMap : PGMap.t) (ptypeMap : PTypeMap.t) 
                                                :  (DPred.gammaCap * PGMap.t * PTypeMap.t * choiceResult)= 
    
if (List.length path > !maxPathLength) then 
    (gammacap, p2gMap, ptypeMap, Nothing (dps, [])) 
else        
                                          

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
    

    (*TODO Add pure functions and constructors as well in the choice*)
    (* let c_es = c_es@c_wellRetTypeLambda in  *)
    Message.show (List.fold_left (fun acc (vi, _) -> acc^", "^Var.toString vi) " " c_es);

    (*choosing a component
    The failing disjunct keeps the list of failing Predicates while checking the Hoare Post => Pre implication*)
    let rec choice potentialChoices 
                    gammacap 
                    dps 
                    (failingDisjuncts : Predicate.t list) 
                    (p2gMap : PGMap.t) 
                    (ptypeMap : PTypeMap.t)    
                    : (DPred.gammaCap * PGMap.t * PTypeMap.t *  choiceResult)= 
        Message.show "Choice ";
        
        match potentialChoices with 
        | [] -> 
             (*no more effectful components try pure function/constructor application*)


            (gammacap, p2gMap, ptypeMap, Nothing (dps, failingDisjuncts)) 
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
                    (*All arguments are  always a scalar/Base Refinement*)
                    Message.show (" Show *************** Synthesizing Args ei : ti for ************"^(Var.toString vi));
                    
                    (**)
                    let e_args =  List.map (fun (argi, argtyi) -> 
                        esynthesizeScalar gammaMap sigmaMap deltaPred argtyi) args_ty_list  in 
                    
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
                                choice xs gammacap dps failingDisjuncts p2gMap ptypeMap
                        | Some es -> 
                            let monExps_es = List.map (fun ei -> ei.expMon) es in 
                            let appliedMonExp = Syn.Eapp (Syn.Evar vi, monExps_es) in  (*apply vi e_arg*)
                            
                            Message.show (" Show *************** Calling Hoare-Pre ************"^(Var.toString vi));
                            (*TODO :: ADD the rule for function application in getting the hoarePre*)
                            let (gammacap, ptypeMap, post_imp_phi_ci', allowed) = hoarePre gammacap ptypeMap spec path appliedMonExp rti in
                            
                            if (allowed) then 
                                let () = Message.show (" Show *************** Hoare-Allowed************"^(Var.toString vi)) in 
                                Message.show (" Show *************** Calling Distinguish ************"^(Var.toString vi));
                                let boundVar = Var.get_fresh_var "bound" in 
                                let bound = Syn.Evar (boundVar) in 
                                let doExpForApp = Syn.Edo (bound, appliedMonExp) in 
                                            

                                let (gamma_with_ci, previous, ptypeMap,  phi_ci', isDistinguished) = 
                                            distinguish gammacap ptypeMap dps spec path doExpForApp rti in 
                                
                                let dp_ci = 
                                            try 
                                                DMap.find dps vi 
                                            with 
                                                Knowledge.NoMappingForVar e -> DPred.empty

                                in


                                let dp_ci = DPred.focusedUpdatePrevious dp_ci previous in 
                                
                                (* let updated_dp_ci_prev = DPred.DP {gammacap=gamma_with_ci; 
                                                                learnt=DPred.getLearnt dp_ci;
                                                                previous=previous} in
                                (* TODO :: The two gamma will have overlap, requires thinking*)
                                let dp_ci = DPred.conjunction dp_ci updated_dp_ci_prev in 
                                 *)   
                                   
                                if (isDistinguished) then 
                                    (* IMPLEMENT TODO :: 
                                        NEED to add the rule for binding a variable to the return type of call
                                       x_bound <- F (xis) Pre v Post, we must add Post[x_bound/v] in the Gamma*)

                                    let () = Message.show (" Show *************** Distinguished : Returning the choice ************"^(Var.toString vi)) in  
                                    let RefTy.MArrow (_,_,(vret, tret),_) = retty  in 
                                    let RefTy.Base (var4Ret, _,_) = tret in  
                                    let gamma_with_ci = DPred.addGamma (gamma_with_ci) boundVar tret in     
                                    
                                    let new_path = path@[doExpForApp] in 
                                    let p2gMap = PGMap.add p2gMap (new_path) gamma_with_ci in 
                                    
                                    (*chosen a ci s.t. path--> ci is allowed and distinguished*)
                                    (*update the DMap ( vi)*)
                                    let dps = DMap.replace dps vi dp_ci in 
                                   
                                    (gamma_with_ci, p2gMap, ptypeMap, Chosen (dps, doExpForApp, new_path))  
                                else
                                    (*~phi_ci'*)
                                   let not_phi_ci' =  Predicate.Not phi_ci' in 
                                   Message.show (" Show *************** Not-Distinguished : Now Adding D(ci) conjunct ************"^(Var.toString vi));
                                   
                                   (*update the Gamma_cap and learnt for vi*)
                                   let dp_ci = DPred.focusedUpdateGamma dp_ci gamma_with_ci in 
                                   let dp_ci = DPred.focusedUpdateLearnt dp_ci not_phi_ci' "Conj" in 
                                   let dps = DMap.replace dps vi dp_ci in 
                                   (*make a different choice*)
                                   choice xs gammacap dps failingDisjuncts p2gMap ptypeMap
                                   

                                   (* let learnt_diff_conjunct = DPred.DP {gammacap=gamma_with_ci; learnt=not_phi_ci'; previous = previous} in
                                    TODO :: The two gamma will have overlap, requires thinking
                                   
                                   let updated_dp_ci = DPred.conjunction dp_ci learnt_diff_conjunct in 
                                    *)

                            else (*allowed = false*)
                                let failing_predicate = post_imp_phi_ci' in 
                                Message.show (" Show *************** Hoare-Not-Allowed : Now Adding D(ci) Disjuncts ************");
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
                                        (*D(c_terminal).learnt = D(c_terminal).learnt \/ failing_predicate*)
                                        let dp_cterminal = DPred.focusedUpdateGamma dp_cterminal gammacap in                                         
                                        let dp_cterminal = DPred.focusedUpdateLearnt dp_cterminal failing_predicate "Disj" in

                                        (* let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate;
                                                                            previous=DPred.getPrevious dp_cterminal} in
                                           (*The two gamma will have overlap, requires thinking
                                             take disjunction*)
                                        let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in  *)
                                        let dps = DMap.replace dps c_terminial_var dp_cterminal in 
                                        dps  
                                    else 
                                        dps  
                                in      
                                let failingDisjuncts = failing_predicate :: failingDisjuncts in 
                                choice xs gammacap dps failingDisjuncts p2gMap ptypeMap
                              

                         ) (*END1*)  

            
                | RefTy.MArrow (_,_,(_,_),_) -> 
                
                (*check the hoare pre-condition rule*)
                        let monExpForComp = Syn.Evar vi in     
                        let boundVar = Var.get_fresh_var "bound" in 
                        let bound = Syn.Evar (boundVar) in 
                        let doExpForComp = Syn.Edo (bound, monExpForComp) in 
                               

                        let (gammacap, ptypeMap, post_imp_phi_ci', allowed) = hoarePre gammacap ptypeMap spec path monExpForComp rti in 
                        if (allowed) then 
                            let () =  Message.show (" Show *************** 
                                        Hoare-Allowed : Now Checking distingushing Predicate ************"^(Var.toString vi)) in 
                            let (gamma_with_ci, previous, ptypeMap, phi_ci', isDistinguished) = distinguish gammacap ptypeMap dps spec path doExpForComp rti in 
                            
                            let dp_ci = 
                                        try 
                                            DMap.find dps vi 
                                        with 
                                                Knowledge.NoMappingForVar e -> DPred.empty

                            in
                            let dp_ci = DPred.focusedUpdatePrevious dp_ci previous in 
                               (* 
                                let updated_dp_ci_prev = DPred.DP {gammacap=gamma_with_ci; 
                                                                learnt=DPred.getLearnt dp_ci;
                                                                previous=previous} in
                                (* TODO :: The two gamma will have overlap, requires thinking*)
                                let dp_ci = DPred.conjunction dp_ci updated_dp_ci_prev in 
                               
 *)

                            if (isDistinguished) then 
                                
                                let () = 
                                    Message.show (" Show *************** Distinguished : Returning the choice ************"^
                                            (Var.toString vi)) in 
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
                                let dps = DMap.replace dps vi dp_ci in 
                                (gamma_with_ci, p2gMap, ptypeMap, Chosen (dps, doExpForComp, new_path))  
                            
                            else
                                let () = 
                                    Message.show (" Show *************** Not-Distinguished : 
                                                    Now Adding conjunct ************"^(Var.toString vi)) in  
                             
                               (*~phi_ci'*)
                               let not_phi_ci' =  Predicate.Not phi_ci' in 
                              
                              (*update the Gamma_cap and learnt for vi*)
                                let dp_ci = DPred.focusedUpdateGamma dp_ci gamma_with_ci in 
                                let dp_ci = DPred.focusedUpdateLearnt dp_ci not_phi_ci' "Conj" in 
                                let dps = DMap.replace dps vi dp_ci in 
                               (*     
                               let learnt_diff_conjunct = DPred.DP {gammacap=gamma_with_ci; learnt=not_phi_ci'; previous = previous} in
                               The two gamma will have overlap, requires thinking
                               let updated_dp_ci = DPred.conjunction dp_ci learnt_diff_conjunct in 
                               let updated_dps = DMap.replace dps vi updated_dp_ci in 
                                *)
                                (*make a different choice*)
                               choice xs gammacap dps failingDisjuncts p2gMap ptypeMap
                               
                         else (*~(HoareCheck)*)

                            
                            let () = 
                                Message.show (" Show *************** 
                                        Hoare-Not-Allowed : Now Adding Disjuncts ************") in 
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
                                    let dp_cterminal = DPred.focusedUpdateGamma dp_cterminal gammacap in                                         
                                    let dp_cterminal = DPred.focusedUpdateLearnt dp_cterminal failing_predicate "Disj" in
  
                                   (*let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate; previous=DPred.getPrevious dp_cterminal} in
                                     let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in 
                                    *) 
                                    let dps = DMap.replace dps c_terminial_var dp_cterminal in 
                                    dps  
                                else 
                                    dps  
                            in      
                            let failingDisjuncts = failing_predicate :: failingDisjuncts in 
                            choice xs gammacap dps failingDisjuncts p2gMap ptypeMap
                           
                         (*?? Add (phi' => phi_ci_pre) as a disjunct in the Differentiating predicate
                 TODO add the disjunction predicate learnt from the failure of choosing a component*)   

     in 
    let failingDisjuncts = [] in  
    choice c_es gammacap dps failingDisjuncts p2gMap ptypeMap
   
 

and deduceR (gamma:DPred.gammaCap) 
            (compi:Syn.monExp) 
            (path:path) 
            (spec: RefTy.t) 
            (dps : DMap.t) 
            (p2gMap : PGMap.t) 
            (ptypeMap : PTypeMap.t): (DPred.gammaCap * PGMap.t * PTypeMap.t * deduceResult) = 
    
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
     *) let (verified, ptypeMap, gamma, path_type) = SynTC.typeCheckPath ptypeMap gammaMap sigmaMap deltaPred path spec in 
        
        (*If the path failed for the lack of return type try to synthesize a scalar using the return type*)


        if (verified) then 
             (

                    let () = Message.show ("Show :: Found a correct Path "^(pathToString path)) in 
                    (gamma, p2gMap, ptypeMap, Success path)
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
                        then
                            (*first check for a bounded program term in the scope which have the correct type 
                            *)
                            let _ = Message.show ("Show :: Return Type Mismatch "^(pathToString path)^
                           " Now checking for a scalar or a pure component to reach goal type ") in 
                          (*TODO :: focus the scalar search to bound program variables and 
                            arguments , then we will not have ghost variables from the heap 
                            returned
                            Alternatively, we can have two different Gamma, one for 
                            program variables and other for verification variables
                            *)      
                          let scalarInEnv = esynthesizeScalar gammaMap sigmaMap deltaPred tspec in 
                            match scalarInEnv with 
                               | Some e -> 
                                    Message.show ("Show Found a pure Scalar "^(Syn.typedMonExp_toString e));
                                    let doExpForPure = Syn.Eret(e.expMon) in 
                                    let completePath = path@[doExpForPure] in 
                                    let (verified_complete, ptypeMap, gamma_complete, path_type_complete) = 
                                        SynTC.typeCheckPath ptypeMap gammaMap sigmaMap deltaPred completePath spec in 
                                         if (verified_complete) then 
                                            let () = Message.show ("Show :: Found correct path "^(Syn.pathToString completePath)) in 
                                            Some (ptypeMap, gamma_complete, completePath)
                                         else None

                              | None ->           
                                    let retExp = esynthesizePureApp gammaMap sigmaMap deltaPred tspec in 
                                      (match retExp with 
                                        | Some e -> 
                                             Message.show ("Show Found a pure component app "^(Syn.typedMonExp_toString e));
                                            
                                            let boundVar = Var.get_fresh_var "bound" in 
                                            let bound = Syn.Evar (boundVar) in 
                                            let doExpForPure = Syn.Edo (bound, e.expMon) in 
                                               
                                            let completePath = path@[doExpForPure] in 
                                            let (verified_complete, ptypeMap, gamma_complete, path_type_complete) = 
                                            SynTC.typeCheckPath ptypeMap gammaMap sigmaMap deltaPred completePath spec in 
                                            
                                            (if (verified_complete) then 
                                                let () = Message.show ("Show :: Found correct path "^(Syn.pathToString completePath)) in 
                                         
                                                Some (ptypeMap, gamma_complete, completePath)
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
                                                    let (verified_complete, ptypeMap, gamma_complete, path_type_complete) = 
                                                    SynTC.typeCheckPath ptypeMap gammaMap sigmaMap deltaPred completePath spec in 
                                                    (if (verified_complete) then 
                                                        let () = Message.show ("Show :: Found correct path "^(Syn.pathToString completePath)) in 
                                                 
                                                        Some (ptypeMap, gamma_complete, completePath)
                                                    else None)      
                                              
                                                 | None -> None   
                                               )
                                        )                   
                    else 
                            None
                    
                  in       
                match fillerTest with 
                    | Some (ptypeMap, completeGamma, completePath) -> (completeGamma, p2gMap, ptypeMap, Success completePath)
                    | None -> 
                       
                        Message.show ("Show :: Incomplete Path "^(pathToString path)^" Now chosing Next component "^(Syn.monExp_toString compi));
                       
                        let (gamma, p2gMap, ptypeMap, nextComponent) = chooseC gamma path spec dps p2gMap ptypeMap in 
                        (match nextComponent with 
                            | Nothing (dps', failingDisjuncts) ->  
                                            Message.show ("Show :: Conflicting path found "^(pathToString path));
                                                (gamma, 
                                                p2gMap, 
                                                ptypeMap,
                                                Conflict 
                                                {env=gamma;
                                                 dps=dps';
                                                 conflictpath=path;
                                                 conflictpathtype=path_type;
                                                 disjuncts= failingDisjuncts}
                                                )
                            (*see if we also need to return an updated gamma*)                  
                            | Chosen    (dps', ci', pi') -> deduceR gamma ci' pi' spec dps' p2gMap ptypeMap             
                        )
            )


(*The forward synthesis algorithm*)
(*cdcleffSynthesizeBind : DPred.gammaCap -> DMap.t -> RefTy.t -> Syn.monExp*)
 and cdcleffSynthesizeBind (gammaCap : DPred.gammaCap)  
                           (dps : DMap.t) 
                           (spec : RefTy.t) : Syn.monExp option= 
    Message.show ("Show :: in CDCL :: GOAL "^(RefTy.toString spec));
    
(*  Message.show ("Gamma at CDCL"^(Gamma.toString (DPred.getGamma gammaCap)));              
 *) let p = [] in 
    let pathGammaMap = PGMap.empty in 
    let ptypeMap = PTypeMap.empty in 
    (*the main while loop in the paper*)
    let rec loop gammacap path spec dps path2GammaMap ptypeMap =
        
        Message.show (" EXPLORED :: "^(pathToString path));
                                
        let (gammacap, p2gMap, ptypeMap, chooseres) = chooseC gammacap path spec dps path2GammaMap ptypeMap in 
        
        match chooseres with 
            | Nothing _ -> 
                
                if (List.length path > 0) then  
                    let gammaMap = DPred.getGamma gammacap in 
                    Message.show (" Show :: Conflict Path  Found  while backtracking");
                    
                    let sigmaMap = DPred.getSigma gammacap in 
                    let deltaPred = DPred.getDelta gammacap in 
    

                    let conflictpath = path in 
                    
                    let (gammaMap, deltaPred, ptypeMap, conflictpathtype) = 
                                SynTC.typeForPath ptypeMap gammaMap sigmaMap deltaPred spec conflictpath in 
                
                    let gammacap = DPred.T {gamma = gammaMap; sigma=sigmaMap; delta= deltaPred} in 
                    

                    (*TODO :: hack passing empty disjunct, but disjuncts are not needed anyway*)
                    let dps = learnP gammacap dps path conflictpathtype [] in 
                    Message.show ("**************Show :: Backtracking From ********"^(pathToString conflictpath));
                    let (gammacap, backpath, dps, p2gMap, ptypeMap) = backtrackC gammacap ptypeMap dps conflictpath p2gMap spec in
                    Message.show ("**************Show :: Backtracked To ********"^(pathToString backpath));
                    
                    loop gammacap backpath spec dps p2gMap ptypeMap 
                else            
                    None
            | Chosen (dps', ei, pi) ->  
                
                Message.show (" EXPLORED :: "^(pathToString pi));
                Message.show ("Show :: Chosen "^(Syn.monExp_toString ei));
            (*  Message.show ("New DPS "^(DMap.toString dps));
             *) Message.show(" Run deduceR");
                let (gammacap, p2gMap, ptypeMap, deduceres) = deduceR gammacap ei pi spec dps' p2gMap ptypeMap in 
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
                            
                            
                            let (gammacap, backpath, dps, p2gMap,ptypeMap) = backtrackC env ptypeMap dps conflictpath p2gMap spec in
                            Message.show ("**************Show :: Backtracked to ********"^(pathToString backpath));
                            
                            (* Message.show ("**************Show :: Printing The Learnt DPS After BT ********"^((DMap.toString dps)));
                             *)(*  Syn.buildProgramTerm  conflictpath
                             *) 
                             
                            Message.show ("**************Show :: LOOP ********"^(pathToString backpath));
                            (* Message.show ("**************Show :: Printing The GammaCap After BT ********"^((DPred.gammaCapToString env)));
  *)
                            loop gammacap backpath spec dps p2gMap ptypeMap
                             
                            
                        (*let dp = learnP gamma tk ck pk dp in 
                        let (dp, tj, cj, pj, gamma) = backtrackC gamma tk ck pk dp in 
                        loop gamma tj pj spec dp
                 *)
        
    in 

    loop gammaCap p spec dps pathGammaMap ptypeMap











and  weakestPreSynththesis  
                            (path2wpMap : PWPMap.t)
                            (path2visitedMap : WPP2CMap.t)
                            (gammacap : DPred.gammaCap) 
                            (path: Syn.path) 
                            (eff : Effect.t)
                            (pre : Predicate.t)  
                            (post : Predicate.t) : (PWPMap.t * WPP2CMap.t *  Predicate.t * Syn.path * DPred.gammaCap * wpresult) =
    
    let gammaMap = DPred.getGamma gammacap in 
    let sigmaMap = DPred.getSigma gammacap in 
    let deltaPred = DPred.getDelta gammacap in 


    
    (*add the formals in the gamma if not already present*)
    (* 
        let gammaMap = List.fold_left (fun _g (vi, ti) -> 
                                           if (not (Gamma.mem _g vi)) then 
                                                Gamma.add _g vi ti 
                                           else 
                                                _g      
                                        ) gammaMap formals  in 

        
        let gammacap = DPred.updateGamma gammacap gammaMap in 
        
     *)    
 (*takes an incomplete path and returns a new incomplete path*)
    Message.show "Show ***********Calling bottomUpChoose***************";
        
    let (path2wpMap, path2visitedMap, gammacap, wp_ci, backpath, result) = 
            bottomUpChoose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred path eff pre post in
    (*depending on the result from the backward synthesis either call forward, continue *)
    match result with 
        (*TODO :: At the moment we treat Break and Flip in a similar manner, returning to the forward Call*)
        | Break   
            (*directly return, the caller in synthesis makes a call to forward synthesis*)
            
        | Flip (*make a call to forward analysis with a structure of the program captured as *)
            -> (path2wpMap, path2visitedMap, wp_ci, backpath, gammacap, Break) 
        | Continue ->
                (*a path cretaed by updating the last hole in the path, continue the backward search*)
                       
                let updatedPath = backpath in 
                let isComp = Syn.isComplete updatedPath in 
                if (Syn.isComplete updatedPath) then 
                    let verified = SynTC.verifyWP gammacap pre wp_ci in 
                    if (verified)
                        then 
                        let () = Message.show "Show *********** Verify :: Success***************" in 
                        let successProgram = (Syn.buildProgramTerm  updatedPath) in 
                        (path2wpMap, path2visitedMap, wp_ci, updatedPath, gammacap, Complete)
                    else 
                        (*recursively solve the subproblem, without any holes*)
                        let () = Message.show "Show ***********Verify :: Failure***************" in 
                        weakestPreSynththesis path2wpMap path2visitedMap gammacap updatedPath eff pre wp_ci
                else (*try filling some more holes*)
                    let () = Message.show "Show ***********Incomplete Path :: Continue WP***************" in 
                        
                    weakestPreSynththesis path2wpMap path2visitedMap gammacap updatedPath eff pre wp_ci  
                   
(*this is the place where we use the Weakest Pre-condition solution to chose the next *)
and bottomUpChoose 
                path2wpMap
                path2visitedMap
                 gammaMap sigmaMap deltaPred 
                (path : Syn.path) 
                (eff : Effect.t) 
                (pre:Predicate.t) 
                (post:Predicate.t) : (PWPMap.t * WPP2CMap.t * DPred.gammaCap * Predicate.t * Syn.path * wpresult)  = 
    
    Message.show ("Show :: EXPLORED :: WP :: PATH "^(Syn.pathToString path));
    let gammacap = DPred.T{gamma=gammaMap;sigma=sigmaMap;delta=deltaPred} in 
    
    (*recursive loop, used by both paths with holes and without holes*)            
    let rec wp_choose
                    (path2wpMap : PWPMap.t)     
                    (path2visitedMap  : WPP2CMap.t) 
                    gammaMap sigmaMap deltaPred 
                    potentialChoices 
                    (prefixPath : Syn.path)
                    (holeVar : Syn.monExp)
                    (holeType : RefTy.t)
                    (suffixPath : Syn.path)
                    (pre:Predicate.t) 
                    (post:Predicate.t) : (PWPMap.t * WPP2CMap.t * DPred.gammaCap * Predicate.t * Syn.path * wpresult) = 
                
    let gammacap = DPred.T{gamma=gammaMap;sigma=sigmaMap;delta=deltaPred} in 
      match potentialChoices with 
        (*@Comment TODO currently the returned path in Break is not used in the forward, when used missing the current Hole will 
        have effect , it should be prefixPath@hole@suffixPath*) 
        [] -> 
                Message.show (" Show : WP : Finished Backward Checks : Try forward ");
                let hole = Syn.Edo (holeVar, Syn.Ehole holeType) in 
                let path2wpMap = PWPMap.add path2wpMap suffixPath post in
                (path2wpMap, path2visitedMap, gammacap, post, prefixPath@[hole]@suffixPath, Break)
        | (vi, rti) :: xs -> 
            
            Message.show (" WPPathChildrenMap "^(WPP2CMap.toString path2visitedMap)); 
            let visited4Suffix = 
                    try
                     WPP2CMap.find path2visitedMap suffixPath 
                    with 
                        | e -> [] 
            in              
            if (List.exists (fun visitedi -> Var.equal vi visitedi) visited4Suffix) then 
                let () = Message.show (" Show *************** WP : Already visited path"^(Syn.pathToString suffixPath)^" <- "^(Var.toString vi)) in 
                wp_choose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred xs prefixPath holeVar holeType suffixPath pre post
            else 

                let uncurried = RefTy.uncurry_Arrow rti in 
                let RefTy.Uncurried (args_ty_list, retty) = uncurried in 
                    
                match retty with
                 | RefTy.Base (u, td, phi) -> 
                    (* raise (SynthesisException "Unhandled wp_choose"); 
     *)
                    let holeBaseType = RefTy.toTyD holeType in 
                    
                    if (not (RefTy.compare_types holeType retty) &&
                            not (holeBaseType = TyD.Ty_unknown)) then 
                        (*skip this components*)
                        
                        let () = Message.show (" Show *************** WP : Non-Match Return Type Skipping "^(Var.toString vi)) in 
                        Message.show ("Show WP HoleType : "^(RefTy.toString holeType));
                        Message.show ("Show WP ViRetTy  : "^(RefTy.toString retty));


                        wp_choose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred xs prefixPath holeVar holeType suffixPath pre post
                    else    
                        let () = Message.show (" Show *************** WP : Matching Return Type "^(TyD.toString holeBaseType)) in 
                       
                        let () = Message.show (" Show *************** WP : Synthesizing Args ei : ti for ************"^(Var.toString vi)) in 
                        
                        (*TODO create a unit test for this*)
                        (*create holes if required and 
                            (actual*Tyd)/(foraml*Tyd) subst for the arguments*)
                        let (newbindings, subst, holes) = List.fold_left 
                                            (fun (bindingsAcc, substAcc, holesAcc) (argi, ti) -> 
                                            (*synthesize the ith argument from the environment*)
                                            let actualArgi = esynthesizeScalar gammaMap sigmaMap deltaPred ti in
                                            let base_ti = RefTy.toTyD ti in 
                                            let boundVari = Var.get_fresh_var argi in 
                                            match actualArgi with 
                                                | None ->  
                                                          ( bindingsAcc@[boundVari, ti],
                                                            substAcc@[((boundVari, base_ti), 
                                                                            (argi, base_ti))], 
                                                                holesAcc@[(Syn.Edo (Syn.Evar (boundVari), 
                                                                                    Syn.Ehole ti))
                                                                        ])  
                                                | Some ei -> 
                                                          let ei_monExp = ei.expMon in 
                                                          let Syn.Evar xi = ei_monExp in 
                                                          ( bindingsAcc@[(xi, ti)],
                                                            substAcc@[(
                                                                    (xi, base_ti), 
                                                                    (argi, base_ti)
                                                                    )], 
                                                                holesAcc)


                                                      ) ([],[],[]) args_ty_list 

                        in 


                        (*No WP CHecks required , directly creaate a pure App*)
                        let actualArgs = List.map (fun (vi,ti) -> Syn.Evar vi) newbindings in 
                        let appliedMonExp = Syn.Edo (   holeVar,
                                                        Syn.Eapp (Syn.Evar vi, actualArgs)) in  (*apply vi e_arg*)
                        let synthesized_partial = holes@[appliedMonExp] in 
                        let updatedPath = prefixPath@synthesized_partial@suffixPath in 
                        

                        (*The holesVar -> Type match must be made visible in the environment*)
                        let gammaMap  = DPred.getGamma gammacap in 
                        let gammaMap = List.fold_left (fun _gamma holei ->
                                                       let Syn.Edo (evar, ehole) = holei in 
                                                       let Syn.Evar hole_vi = evar in 
                                                       let Syn.Ehole hole_ti = ehole in 
                                                       VC.extend_gamma (hole_vi, hole_ti) _gamma) gammaMap holes in 

                        let gammacap = DPred.updateGamma gammacap gammaMap in 



                        (*The Post Spec remains the same*)
                        



                        let () = Message.show (" Show *************** WP : UPDATED PATH "^(Syn.pathToString updatedPath)) in 
                        
                        (*Calculate post/fun return type see rule for bind-backward
                         for simple expamples this will work just replacing the return type,
                        but for more complex Post. just replacing the variable type may makes the 
                        Post invalid, 
                        E.g. v : pair .Q = Mem (res) /\ fst (v) > 0
                        changing v to Top . will make the fst(v) > 0 as invalid

                        .*)    
                        let new_retType = TyD.Ty_unknown in 
                        let new_retVar = Var.get_fresh_var "v" in 

                        let new_retBind = (new_retVar, new_retType)  in 
                        let new_post = VC.substi post (new_retBind) 2 in 
                        Message.show (" Show :: WP :: NEW POST "^(Predicate.toString new_post));
                        (* TODO :: add to visited and path2WP maps*)

                        let path2wpMap =  PWPMap.add path2wpMap updatedPath new_post in 
                        let path2visitedMap = WPP2CMap.replace path2visitedMap suffixPath (vi :: visited4Suffix) in 


                        (path2wpMap, path2visitedMap, gammacap, new_post, updatedPath, Continue)            

                 | RefTy.MArrow (effret, preRet, (vret, retbt), postRet) -> 
                    Message.show (" Show *************** WP : Arrow Component ************"^(Var.toString vi));
                    (* let RefTy.MArrow (_,_,(_,retbt),_) = retty in 
                     *)
                    let holeBaseType = RefTy.toTyD holeType in 
                    
                    if (not (RefTy.compare_types holeType retbt) &&
                            not (holeBaseType = TyD.Ty_unknown)) then 
                        (*skip this components*)
                        
                        let () = Message.show (" Show *************** WP : Non-Match Return Type") in 
                        Message.show ("Show WP HoleType : "^(RefTy.toString holeType));
                        Message.show ("Show WP ViRetTy  : "^(RefTy.toString retbt));


                        wp_choose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred xs prefixPath holeVar holeType suffixPath pre post
                    else    
                        let () = Message.show (" Show *************** WP : Matching Return Type") in 
                        (*Currently the argument is always a scalar/Base Refinement*)
                        let () = Message.show (" Show *************** WP : Synthesizing Args ei : ti for ************"^(Var.toString vi)) in 
                        
                        (*TODO create a unit test for this*)
                        (*create holes if required and 
                            (actual*Tyd)/(foraml*Tyd) subst for the arguments*)
                        let (newbindings, subst, holes) = List.fold_left 
                                            (fun (bindingsAcc, substAcc, holesAcc) (argi, ti) -> 
                                            (*synthesize the ith argument from the environment*)
                                            let actualArgi = esynthesizeScalar gammaMap sigmaMap deltaPred ti in
                                            let base_ti = RefTy.toTyD ti in 
                                            let boundVari = Var.get_fresh_var argi in 
                                            match actualArgi with 
                                                | None ->  
                                                          ( bindingsAcc@[boundVari, ti],
                                                            substAcc@[((boundVari, base_ti), 
                                                                            (argi, base_ti))], 
                                                                holesAcc@[(Syn.Edo (Syn.Evar (boundVari), 
                                                                                    Syn.Ehole ti))
                                                                        ])  
                                                | Some ei -> 
                                                          let ei_monExp = ei.expMon in 
                                                          let Syn.Evar xi = ei_monExp in 
                                                          ( bindingsAcc@[(xi, ti)],
                                                            substAcc@[(
                                                                    (xi, base_ti), 
                                                                    (argi, base_ti)
                                                                    )], 
                                                                holesAcc)


                                                      ) ([],[],[]) args_ty_list 

                        in 

                        
                      
                        (*create the wp*) 
                        (*either a Pure function or an effectful arrow component*)    
                       (*  match retty with 
                            | RefTy.Base (vret, tret, pred) -> 
                                raise (SynthesisException "Unhandled WP CHOOSE");
                                (*Simpler Case, can always be called*)
                            | RefTy.MArrow (effret, preRet, (vret, tret), postRet) ->
                        *)         
                        let () = Message.show (" Show *************** WP : Generating WP for Effectful Ci "^(Var.toString vi)) in 
                        (*Case which checks the dual of the forward condition*)
                        (*\Gamma |- wp (vi, post*)    
                        let (gammaMap, wp_vi_post) = 
                                (*WP :: given Post, preRet, postRet, actualArgi*)
                                createWP gammaMap retty post subst  in 

                        let extended_gammaMap = (*EXTEND GAMMA WITH new bindings*)
                                    List.fold_left (fun _g (vi, ti) -> 
                                         VC.extend_gamma (vi, ti) _g) gammaMap newbindings in 
                        let gammacap = DPred.updateGamma gammacap extended_gammaMap in 
                                   
                        let (wpCheck) = 
                             wpPreCheck extended_gammaMap sigmaMap deltaPred wp_vi_post  in
                           
                        let actualArgs = List.map (fun (vi,ti) -> Syn.Evar vi) newbindings in 
                                         
                        match wpCheck with 
                            | Break -> 
                                    Message.show (" Show *************** WP : Break WP_Check Failed for Ci "^(Var.toString vi));
                                    wp_choose path2wpMap 
                                                path2visitedMap 
                                                    gammaMap 
                                                        sigmaMap 
                                                            deltaPred xs prefixPath holeVar holeType suffixPath pre post
                            | Continue -> (*Ci is a correct wp choice*)
                                    Message.show (" Show *************** WP : Continue  Ci "^(Var.toString vi));
                                    let appliedMonExp = Syn.Edo ( holeVar,
                                                                    Syn.Eapp (Syn.Evar vi, actualArgs)) in 
                                    Message.show ("Show WP :: HOles "^(Syn.pathToString actualArgs));
                                    (*The current component is successfully chosen*)
                                    
                                    let synthesized_partial = holes@[appliedMonExp] in 
                                    let updatedPath = prefixPath@synthesized_partial@suffixPath in 
                                    (*call using an updated gamma, where the holeVar is not available*)
                                    let Syn.Evar holeVarPlain = holeVar in 
                                    let gammaMap = DPred.getGamma gammacap in 
                                    let gammaMap = Gamma.remove gammaMap holeVarPlain  in 
                                    let gammacap = DPred.updateGamma gammacap gammaMap in 
                                    (*add to path2wp and visited map*)
                                    let path2wpMap =  PWPMap.add path2wpMap updatedPath wp_vi_post in 
                                    let path2visitedMap = WPP2CMap.replace path2visitedMap suffixPath (vi :: visited4Suffix) in 

                                    (path2wpMap, path2visitedMap, gammacap, wp_vi_post, updatedPath, Continue)
                            | Flip -> 
                                    Message.show (" Show *************** WP : Flip  Ci "^(Var.toString vi));
                                                        
                                    let appliedMonExp = Syn.Eapp (Syn.Evar vi, actualArgs) in 
                                    let synthesized_partial = holes@[appliedMonExp] in 
                                    let updatedPath = prefixPath@synthesized_partial@suffixPath in 
                                    let path2wpMap =  PWPMap.add path2wpMap updatedPath wp_vi_post in 
                                                                            
                                    
                                    (path2wpMap, path2visitedMap, gammacap, wp_vi_post, updatedPath, Flip)
        in 
                


    (*TODO Implement the breaking into subproblems using disjunction rule*)
    let (lastHole, prefixPath, suffixPath) = Syn.getLastHole path in 
    match lastHole with 
        | None -> 
                let () = Message.show ("Show *********** No More Holes***************") in 
                let isComp = Syn.isComplete path in 
                if (isComp) then 
                    let verified = SynTC.verifyWP gammacap pre post in 
                    if (verified)
                        then 
                        let () = Message.show "Show *********** NO Holes :: Verify :: Success***************" in 
                        let successProgram = (Syn.buildProgramTerm  path) in 
                        (path2wpMap, path2visitedMap, gammacap, post, path, Complete)
                    else 
                       let () = Message.show "Show *********** NO Holes :: Verify :: Failure***************" in 
                        
                       (*TODO Make Ty_unknown TOP, this would mean filtering for Ty_unknown should 
                        give all components with any return type*)
                       let topType  = RefTy.fromTyD (TyD.Ty_unknown) in  
                       let holeVar = Syn.Evar (Var.get_fresh_var "ret") in 
                       let c_wellRetType = Gamma.enumerateAndFind gammaMap topType in 
                       let c_wellRetTypeLambda = Gamma.lambdas4RetType gammaMap 
                                                 (RefTy.MArrow (eff, pre, (Var.get_fresh_var "v", topType), post)) in 
            
                       let c_es = List.filter (fun (vi, ti) -> 
                                        let effi = RefTy.get_effect ti in 
                                        if (effi = Effect.Pure) then false 
                                        else 
                                            Effect.isSubEffect effi eff) gammaMap (*c_wellRetType*) in 



                        wp_choose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred c_es prefixPath holeVar topType suffixPath (pre:Predicate.t) post
                else (*try filling some more holes*)
                    raise  (SynthesisException "DEAD CODE");   
                
        | Some lastHole -> 
            
            Message.show ("Show *********** Found a Hole***************"^(Syn.monExp_toString lastHole));
            (*hole will either be of the form [?? : T] or x <- [?? : T]*)
            let (bindingVar , holeType)  = 
                match lastHole with 
                 | Syn.Ehole t -> (None, t) 
                 | Syn.Edo (bound, hole) -> (match hole with
                                         | Syn.Ehole t -> (Some bound, t)
                                         | _ -> raise (SynthesisException "Illegeal Hole Expression") )

            in 

            let holeVar = 
                match bindingVar with 
                    | None -> Syn.Evar (Var.get_fresh_var "ret")  
                    | Some b -> b 
             in
            Message.show (" Show :: WP :: bindingVar "^(Syn.monExp_toString holeVar));


            (*This is a simplified version of the return typed guided component synthesis as in SYPET*)
            let c_wellRetType = Gamma.enumerateAndFind gammaMap holeType in 
            
           

            (*change the def and usages of lambdas$RetType*)
            let c_wellRetTypeLambda = Gamma.lambdas4RetType gammaMap holeType in 

           (*   Message.show ("Show Potential Functions 1");
             Message.show (List.fold_left (fun acc (vi, _) -> acc^", \n Show "^Var.toString vi) " " c_wellRetTypeLambda);
            *)


            
            (*effectful component list*)
            let c_es = List.filter (fun (vi, ti) -> 
                                        let effi = RefTy.get_effect ti in 
                                        if (effi = Effect.Pure) then false 
                                        else 
                                            Effect.isSubEffect effi eff) gammaMap (*c_wellRetType*) in 
            
             let c_es = c_wellRetTypeLambda@c_es in 

             Message.show ("Show Potential Functions");
             Message.show (List.fold_left (fun acc (vi, _) -> acc^", \n Show"^Var.toString vi) " " c_es);
   
                                                                  

            wp_choose path2wpMap path2visitedMap gammaMap sigmaMap deltaPred c_es prefixPath holeVar holeType suffixPath (pre:Predicate.t) post

end