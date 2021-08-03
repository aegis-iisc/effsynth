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
 val project : Predicate.t -> Gamma.t -> (RefTy.t list) ->(Var.t * RefTy.t) list 
 val esynthesizeApp :  Gamma.t -> Sigma.t -> Predicate.t -> RefTy.t  ->  Syn.typedMonExp option   
 val esynthesizeScalar : Gamma.t -> Sigma.t -> Predicate.t -> RefTy.t -> Syn.typedMonExp option  
 val isynthesizeConstApp : Gamma.t -> Sigma.t -> RefTy.t -> ((Var.t * RefTy.t) list * Syn.typedMonExp) option  
 val isynthesizeHoles : Gamma.t -> Sigma.t -> RefTy.t ->  ((Var.t * RefTy.t) list* Syn.typedMonExp) option   
 val isynthesizeConstApp : Gamma.t -> Sigma.t -> RefTy.t ->  ((Var.t * RefTy.t) list * Syn.typedMonExp) option   
 val esynthesizeBind :  Explored.t ->VC.vctybinds -> Sigma.t -> VC.pred list ->  RefTy.t -> (Explored.t * Syn.typedMonExp option) 

(*T-ret rule*)
val esynthesizeRet :  Gamma.t -> Sigma.t -> RefTy.t ->  (Syn.typedMonExp option)  

val esynthesizeEffSigma : VC.vctybinds -> Sigma.t ->  VC.pred list -> RefTy.t ->  RefTy.t -> (Var.t list) option
val esynthesizeBindSpecial : Explored.t -> VC.vctybinds -> Sigma.t ->  VC.pred list ->  RefTy.t -> (Syn.typedMonExp option) 

 val esynthesizeEff : Explored.t -> VC.vctybinds -> Sigma.t ->  VC.pred list->  RefTy.t -> (Syn.typedMonExp option) 
 val isynthesizeMatch : VC.vctybinds -> Sigma.t -> Predicate.t -> Var.t ->   RefTy.t -> RefTy.t ->  Syn.typedMonExp option 
 val isynthesizeFun : VC.vctybinds -> Sigma.t -> Predicate.t -> RefTy.t  -> Syn.typedMonExp option
  val esynthesizeFun : Explored.t -> VC.vctybinds -> Sigma.t -> Predicate.t ->  RefTy.t -> (Syn.typedMonExp option)
 val synthesize :  VC.vctybinds -> Sigma.t -> Predicate.t-> RefTy.t -> bool -> Syn.typedMonExp option 


val litercount : int ref   
  type exploredTree = Leaf 
                    | Node of exploredTree list 
  type choiceResult = 
        | Nothing of DMap.t * Predicate.t list 
        | Chosen of (DMap.t *  Var.t * path)

  type deduceResult = 
        | Success of path
        | Conflict of { env :DPred.gammaCap; 
                        dps:DMap.t ; 
                        conflictpath : path;
                        conflictpathtype : RefTy.t;
                        disjuncts : Predicate.t list
                        }

   val hoarePre :  DPred.gammaCap -> RefTy.t ->  path -> Var.t -> RefTy.t -> (DPred.gammaCap * Predicate.t * bool)                      
   val distinguish : DPred.gammaCap -> DMap.t -> RefTy.t ->  path -> Var.t -> RefTy.t -> (DPred.gammaCap * Predicate.t * bool)
   
   val chooseC :  DPred.gammaCap -> path -> RefTy.t -> DMap.t -> PGMap.t -> (DPred.gammaCap * PGMap.t * choiceResult)
   val deduceR : DPred.gammaCap -> Var.t ->  path -> RefTy.t -> 
                DMap.t -> PGMap.t -> (DPred.gammaCap * PGMap.t * deduceResult)

   val learnP :  DPred.gammaCap -> DMap.t -> path -> RefTy.t -> Predicate.t list -> DMap.t 
    
   val backtrackC : DPred.gammaCap -> DMap.t -> path -> PGMap.t -> RefTy.t  -> (DPred.gammaCap * path * DMap.t * PGMap.t)
   val cdcleffSynthesizeBind :  DPred.gammaCap ->   DMap.t  -> RefTy.t -> Syn.monExp
  

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
        | Chosen of (DMap.t *  Var.t * path)

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
                        | VCE.Success -> let retMonExp = Syn.Eret ({expMon=(Syn.Evar (vi)); ofType=rti}) in 
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
                                            let retMonExp = Syn.Eret ({expMon=(Syn.Evar (vi)); ofType=rti}) in 
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



(*The main projection function which pushes information from Goal to inner nodes*)       
(*TODO :: Test this
 *  shape of baseRefinement is Base (Var.t * TyD.t * Predicate.t) *)
let project (goalPred:Predicate.t) gamma (args:RefTy.t list)  : (Var.t * RefTy.t) list = 
        let conjuncts = Predicate.conjunctify goalPred in 
        (*assume for any type t = C([xi:ti]) there exists relations [pri : (v : t) :-> ti] with relids "pri" *)
        (*projects the goalPredicate conjuncts to those conjuncts containing projection relations in the set {pr1, pr2, .... prk}*)
        let project_k (k:int) conjs = 
                let relID_k = RelId.fromString ("proj"^(string_of_int k)) in
                List.map (fun ci -> 
                                (*gives a list of RelId.t*)        
                                let rels_ci = Predicate.getRelation ci in 
                                if (List.mem relID_k rels_ci) then 
                                  let maxId = Predicate.maxProjRel rels_ci in 
                                  if (maxId > k)
                                        then P.True 
                                  else 
                                        ci          
                                else 
                                   P.True) conjs 

        in 
        
        let lower (relId, newVar) conjs =
                (*TODO define lowerRelIdToVar which lowers the projection relations in a Predicate to a variable 
                 * for example*)
                List.map (fun ci -> Predicate.lowerRelIdToVar ci (relId, newVar)) conjs 

        in 
        let relId_argVar_associated_proj = 
                        List.mapi (fun i argi -> 
                                let ithRelId = RelId.fromString ("proj"^(string_of_int (i+1))) in 
                                            (*{RelId.name="proj";RelId.id= (i+1)} in*)
                                let ithProj = project_k (i+1) conjuncts in
                                let ithVariable = 
                                        let fresh_v = Var.get_fresh_var "x" in 
                                        RelId.fromString ((Var.toString fresh_v)^(string_of_int (i+1))) 
                                in 

                                   
                                (ithRelId, ithVariable, ithProj)) args in 

        let argVar_associated_loweredProj = List.map (fun (relIdi, variId, proji) -> 
                                                        let lowered = lower (relIdi, variId) proji in 
                                                        (variId, lowered)) relId_argVar_associated_proj

        in 
        let results = List.map2 (fun (vari, loweredi) argi -> 
                                        let baseT = RefTy.toTyD argi in 
                                        let predT =  Predicate.list_conjunction loweredi in 
                                        (*let {RelId.name=varname;_}*)
                                        let varname  = vari in 
                                        (varname, RefTy.Base (varname, baseT, predT))) argVar_associated_loweredProj args   

        in results
        
        




(*The standard hoare-pecondition check*)
let hoarePre gamma spec path ci rti = 
    let () =Message.show ("Potential Component/Function  "^(Var.toString ci)) in 
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



    


(*a routine to verify that the choice ci, in the current gamma satisfies the distinguishing constraints*)
let distinguish gamma dps spec path ci rti= 
    

    let gammaMap = DPred.getGamma gamma in 
    let sigmaMap = DPred.getSigma gamma in 
    let deltaPred = DPred.getDelta gamma in 
        
    let (gammaMap, deltaPred, path_type) = SynTC.typeForPath gammaMap sigmaMap deltaPred spec path in 
            
    (*construct VCs ci_post => D(ci)*)
    
    Message.show ("HERE");
    let (gammaMap, deltaPred, potential_path_type) = 
        match rti with 
            | RefTy.MArrow (_, _ , (_,_),_) -> 
                     Message.show ("HERE in MARROW"^(Var.toString ci));
   
                    let potential_path = path@[ci] in 
                     SynTC.typeForPathSuffix gammaMap sigmaMap deltaPred [(ci, rti)] path_type 
            | RefTy.Arrow ((_,_),_) ->          
                    let () =  Message.show ("Show An arrow in the potential path HERE ") in
                    raise (LearningException "ARROW POT PATH NOT HANDLED")    
   

    in                 
(* 
    Message.show " DISTINGUISH Potential Path Type";
    Message.show (" DISTINGUISH Potential Path "^(pathToString potential_path));
    
 *)

(*  Message.show " DISTINGUISH DPS";
    Message.show (" DISTINGUISH DPS"^(DMap.toString dps));
 *) 

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
            try 
                if (List.length p_kminus1 > 0) then 
                    let k_minus1 = List.hd (List.rev p_kminus1) in 
                    let gamma_kminus1 = PGMap.find p2gMap p_kminus1  in 

                    let gammaMap_km1 = DPred.getGamma gamma_kminus1 in 
                    let sigmaMap_km1 = DPred.getSigma gamma_kminus1 in 
                    let deltaPred_km1 = DPred.getDelta gamma_kminus1 in 

                    (*TODO :: This might lead to unsoundness as the two paths will have two different Gamma*)
                    
                    let (gammaMap_km1, deltaPred_km1, type_pkminus1) = SynTC.typeForPath gammaMap_km1 sigmaMap_km1 deltaPred_km1 spec p_kminus1 in 
                    let RefTy.MArrow (_, _, (_,_), post_kminus1 ) = type_pkminus1 in 
                    let ann_k_type = Gamma.find gammaMap_km1 conflict_node in
                    
                    let RefTy.MArrow (_, pre_k,(_,_),_) = ann_k_type in 

                    let gamma_kminus1 = DPred.T{gamma=gammaMap_km1; sigma = sigmaMap_km1; delta= deltaPred_km1} in 
                    
                    let learnt_predicate = Predicate.Not (Predicate.If (post_kminus1, pre_k)) in 
                    let diffpred_kminus1_k = DPred.DP {gammacap = gamma_kminus1; learnt=learnt_predicate} in 
                    let dp_kminus1 = 
                                    try 
                                        DMap.find dps k_minus1
                                    with 
                                        Knowledge.NoMappingForVar e -> DPred.empty

                    in 
                        
                    let updated_dp_kminus1 = DPred.conjunction dp_kminus1 diffpred_kminus1_k in 
                    let updated_dps = DMap.replace dps k_minus1 updated_dp_kminus1 in 
                    (gamma_kminus1, p_kminus1, updated_dps, p2gMap) 
             
                else 
                    (gamma, p_kminus1, dps, p2gMap)     
            with 
                e -> raise e
              (*e -> raise (LearningException ("No gamma for Path "^(pathToString p_kminus1)))*)            



          



(*The Tapp rule*) 
let rec esynthesizeApp gamma sigma delta spec  : Syn.typedMonExp option =  
        (*explore the functions in gamma with the required body type*)
        let funType = RefTy.Arrow ((Var.get_fresh_var "v", RefTy.fromTyD Ty_unknown), spec) in  
        let explored = Explored.empty in 
        let rec choose explored ftype : (Syn.typedMonExp option)=  
                let efun =  esynthesizeFun explored gamma sigma P.True ftype in 
                match efun with 
                        | None -> None
                        | Some {expMon=lam;ofType=rtlam} -> 
                                let Syn.Evar vlam = lam in                               
                                (match rtlam with 
                                 | RefTy.Arrow ((v1, t1), t2) -> 
                                         match esynthesizeScalar gamma sigma delta t1 with 
                                          | Some eargTMExp -> 
                                                 let eargExp = Syn.getExp eargTMExp in 
                                                 let eargType = Syn.getType eargTMExp in 
                                                 (match eargExp with 
                                                    | Syn.Evar earg ->     
                                                         let constraintsArg = VC.fromTypeCheck gamma VC.empty_delta (eargType, t1) in
                                                         let subst = [(earg, v1)] in 
                                                         let substitutedType = RefTy.applySubsts subst t2 in
                                                         let vc= VC.fromTypeCheck gamma VC.empty_delta (substitutedType, spec) in 
                                                        
                                                         (*make a direct call to the SMT solver*)
                                                         let vcStandard = VC.standardize vc in 
                                                         let result = VCE.discharge vcStandard  in 
                                                           match result with 
                                                                | VCE.Success ->
                                                                          let funTerm = {expMon = lam; ofType= rtlam} in  
                                                                          let argTerm = {expMon = eargExp; ofType = eargType} in       
                                                                          Some {expMon = (Syn.Eapp (funTerm, argTerm)); ofType=substitutedType}   
                                                                | VCE.Failure -> (*make another choice for the function*)choose (vlam :: explored) ftype
                                                                | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                                                    (*Argument must be a variable*)
                                                    | _ -> choose (vlam :: explored) ftype
                                                 )      
                                       | None ->  choose (vlam :: explored) ftype
                                                
 
                                 | _ -> raise (SynthesisException ("Application over a non arrow type"^(RefTy.toString rtlam)))
                                )           
        in                      
        choose explored funType 


(*Top lvel goal synthesis for scalar Types*)
and esynthesizeScalar gamma sigma delta spec : Syn.typedMonExp option  = 
    (*TODO Other cases*) 
     let explored = Explored.empty in    
     let foundbyEnum = enumPureE explored gamma sigma delta spec in 
     match foundbyEnum with 
       | Some t -> Some t       
       | None -> None 
             (*    
             let appterm = esynthesizeApp gamma sigma delta spec in 
                match appterm with 
                | Some t1 -> Some t1 
                | None -> 
                        (*constructor application*)
                        let constAppterm = isynthesizeConstApp gamma sigma spec in 
                        match constAppterm with 
                          | Some t2 -> let (argLists, constAppExp) = t2 in Some constAppExp
                          | None -> None   *)       
(*@arg : spec - a spec of the required base types 
 * @ret : A Sigma type (vi, rti) list and a typed Expression applying a Constructor to argumnests C (vi) *)
and isynthesizeConstApp gamma sigma spec : ((Var.t * RefTy.t) list * Syn.typedMonExp) option = 
        Message.show "isynthesizeConstApp";
        Message.show ("Spec "^(RefTy.toString spec));
        let RefTy.Base (v, t, pred) = spec in 
        let exploredCons = Sigma.empty in 
        (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
        let foundCons = Sigma.findCons4retT sigma spec in 
        Message.show "Found Cons";
        let () = List.iter(fun (coname, _) ->  Message.show (coname)) foundCons in 
        match foundCons with 
           | [] -> 
                    Message.show "Non constructors found,  try another approach";
                    None 
           | (x::xs) -> 
                let (vi, rti) = x in 
                let getExpandedConsType refTy =  
                        match refTy with
                           | RefTy.Arrow ((_, t1 ), t2) -> 
                                match t1 with 
                                 | RefTy.Base(va, ta, preda) -> [t1]
                                 | RefTy.Tuple listArgs -> listArgs                               
                 in 
                 let consArgs = getExpandedConsType rti in 
                 (*auxiliary function project projects/pushes the given constraints on the output to argumenets of the constructor
                  *
                  * *)
                 (*Sigma type*)
                 let consArgsWithInferredTypes = project pred gamma consArgs in 
                 let consArgsNames = List.map (fun (vi, rti) -> vi) consArgsWithInferredTypes in 
                 let consArgNameList = List.map (fun vi -> (Syn.Evar vi)) consArgsNames in   
                 let consAppExp = {Syn.expMon= (Syn.Ecapp (vi, consArgNameList)); Syn.ofType=spec} in 
                 let () = Printf.printf "%s" ("<<<<<<<<<<<<<<<>>>>>>>>>>>>>>>>>>>>>>>") in
                 Message.show ("ConsApp "^Syn.typedMonExp_toString consAppExp);
                 let () = List.iter (fun (vi, rti) -> 
                                    Message.show ((Var.toString vi)^" : "^(RefTy.toString rti))) 
                                            consArgsWithInferredTypes in 
                 Some (consArgsWithInferredTypes, consAppExp) 
                 



(*creates a list of missing args required while synthesizing the intro term for spec*)
and  isynthesizeHoles gamma sigma spec : ((Var.t * RefTy.t) list* Syn.typedMonExp) option  = 
        (*To syntesize holes, try applying Consrtructors in sigma or functions in gamma
         * Currently only trying constructor application*)
        let missingTypedArgsList_constAppExp = isynthesizeConstApp gamma sigma spec in 
         missingTypedArgsList_constAppExp 

(*T-ret rule*)
and  esynthesizeRet gamma sigma spec : (Syn.typedMonExp option)=  
     let RefTy.MArrow (eff, pre, (v, t), post) = spec in
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
 




(*The general bind rule for let \Sigma (xi : \taui) <- e1 in e2
 * delta  = . | pred :: delta
TODO :: FInish this definition*)
and  esynthesizeBind explored gamma sigma delta spec : (Explored.t *(Syn.typedMonExp option)) = 
   
    Message.show ("esynthesizeBind");
   (*actual knapsack*)
   let rec enumerateSubProblems explored goalspec  =  
        (*We need to divide the effects and the intermediate heap constraints in a way which gives two subproblems*)
        let RefTy.MArrow (eff, pre, t , post) = goalspec in 
        (*TODO break based on effects*)
        let gamma = Gamma.filterOnEffectSet gamma eff in 
     
       

       (*we need to break the interval into eff pre and post into subproblems*)
       let retResult = (Var.get_fresh_var "v") in 
       let unKnownType = RefTy.Base (retResult, TyD.Ty_unknown , Predicate.True) in 
       let spec1 = RefTy.MArrow (eff, pre, (retResult, unKnownType), Predicate.True) in 
       (*right now we dont have any explored set*)
       Message.show "PARTIAL PATH";
       let () = Message.show (List.fold_left 
                                (fun str vi -> (str^"\t --"^(Var.toString vi))) "SUB " (List.rev !subprobplem)) in  
       let explored_one_level_up = explored in 
       let (explored, e1_res) = enumerateEffAndFind explored gamma sigma delta spec1 in 
       match e1_res with 
            | Some e1 -> 
               let exp1 = Syn.getExp e1 in 
                let () = 
                match exp1 with      
                    | Syn.Evar c1 -> 
                            subprobplem :=  c1 :: (!subprobplem);      

                    | Syn.Eret tme ->
                         let Syn.Evar c1 = Syn.getExp tme in
                        subprobplem :=  c1 :: (!subprobplem);       
                in                 
               Message.show "PARTIAL PATH NEW";
               let () = Message.show (List.fold_left (fun str vi -> (str^"\t --"^(Var.toString vi))) "NEW " (List.rev !subprobplem)) in 
        
               (* Message.show "Found e1 in (x <- e1 in e2), Synthesizing now e2 "; *)
               let fstType = Syn.getType e1 in 
               assert (RefTy.isEffectful fstType);
               let RefTy.MArrow (eff1, pre1, (x1, t1), post1) = fstType in 
               let gamma = Gamma.add gamma x1 t1 in 
                
               let pre1 = pre in  
               (*create an intermediate heap*)
               let h_var  = Var.get_fresh_var "h" in 
               let h_type = RefTy.fromTyD (TyD.Ty_heap) in 

               let h_int_var  = Var.get_fresh_var "h_i" in 
               let h_int_type = RefTy.fromTyD (TyD.Ty_heap) in 

               let gamma = Gamma.add gamma h_var h_type in 
               let gamma = Gamma.add gamma h_int_var h_int_type in 
               let post1_on_hi = VC.apply post1 [(h_var, TyD.Ty_heap);(x1, RefTy.toTyD t1); (h_int_var, TyD.Ty_heap)] in 
               let bvs = [(h_int_var, TyD.Ty_heap)] in 
               
               (*substitute current heap values for pre*)
               let pre1_on_h = VC.apply pre1 [(h_var, TyD.Ty_heap)] in 
               let pre1_h = Predicate.Forall ([(h_var, TyD.Ty_heap)], pre1_on_h) in   

               (*forall hi : heap. Post hi*)
               let post1_hi = Predicate.Forall (bvs, post1_on_hi) in 
               
               (*also apply the hi as the first argument to post*)
               let post_hi = VC.substi post (h_int_var, TyD.Ty_heap) 1 in 
               
               Message.show ("post_substituted "^(Predicate.toString post_hi));
               (*TODO This needs to changes as we add effect guided rules *)
               let retResult = (Var.get_fresh_var "v") in 
               let unKnownType = RefTy.Base (retResult, TyD.Ty_unknown , Predicate.True) in 
               (*add the pre1 to the delta*)
               let delta = pre1_h :: delta in 
               let spec2 = RefTy.MArrow (eff, post1_hi, 
                                (retResult, unKnownType), 
                                post_hi) in 
               
               let e2_res = esynthesizeEff explored gamma sigma delta spec2 in 
               (match e2_res with 
                | Some e2 -> 
                        Message.show "Found e2 in (x <- e1 in e2)";
                        Message.show (Syn.typedMonExp_toString e2); 
                        let exp2 = Syn.getExp e2 in 
                        let () = match exp1 with      
                          | Syn.Evar c2 -> 
                            subprobplem := (c2 :: !subprobplem); 
                            
                          | Syn.Eret tme -> 
                             let Syn.Evar c2 = Syn.getExp tme in 
                              subprobplem := (c2:: !subprobplem);  
                             
                         in       

                        
                        let boundMonExp = Syn.Ebind ((Syn.Evar x1), e1, e2) in 
                        let boundTypedMonExpp = {Syn.expMon = boundMonExp;  Syn.ofType= spec} in 
                        (explored, Some boundTypedMonExpp) 

                | None -> 
                        
                        let exp1 = Syn.getExp e1 in 
                        match exp1 with      
                          | Syn.Evar c1 -> 
                            (*  let explored = Explored.add explored c1 in 
                             *)
                             let () = subprobplem := (List.tl !subprobplem) in  
                             enumerateSubProblems explored goalspec
                          | Syn.Eret tme -> 
                             let Syn.Evar c1 = Syn.getExp tme in 
                            (*  Message.show ("EXPLORED::BEFORE"^(Explored.toString explored));       
                             let explored = Explored.add explored c1 in 
                             Message.show ("EXPLORED::AFTER"^(Explored.toString explored));
                             *)
                             let () = subprobplem := (List.tl !subprobplem) in  
                             enumerateSubProblems explored goalspec
                )            
            | None ->
                    Message.show "THE PATH ENDED WITHOUT RESULT"; 
                    Message.show ("THE LAST COMPONENT "^(List.hd explored));
                    (explored, None)  
                       


    in 
    enumerateSubProblems explored spec        


(*accumulatedMonExps are strucutured as list of component names*)
and esynthesizeEffSigma gamma sigma delta sigmaType spec : (Var.t list) option = 
       (* the real enumeration of component sequencing will happen here
        *)
   let RefTy.Sigma (ls) = sigmaType in  
   let RefTy.MArrow (eff, pre, _ , post) = spec in 
   (*delta = .| pred /\ delta*)
   (*explored in this case will be list of paths*)
   (*accumulateMonExps are the list of componensts c1 ; c2 ;..., ck*)
   (*TODO this is similar to esynthesizeBind buth it  has an extra information in Tuple list from the sigma type
   REDO this*)
   let rec esynthesizePath explored gamma sigma delta accumulatedMonExps ltuples : ((Var.t list), (Environment.ExploredTerms.t)) result = 
     match ltuples with 
        | [] -> 
                (*create a condition [\Gaamma\ |= delta =>  post*)

                let delta_as_predicate = Predicate.pred_conjunction delta in 
                let vc_delta_impl_post = VC.VC(gamma, delta_as_predicate, post) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc_delta_impl_post in 
                let result = VCE.discharge vcStandard  in 
                   (match result with 
                        | VCE.Success ->
                           Success accumulatedMonExps
                        | VCE.Failure -> 
                          let failingPath = Environment.ExploredPaths.fromList accumulatedMonExps in 
                          let explored = failingPath @ explored in 
                          Fail explored
                        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                  )
       

        | (xi , ti) :: xs -> 
                
                assert (not (Gamma.mem gamma xi)); 
                let delta_as_predicate = Predicate.pred_conjunction delta in
                let vi = Var.get_fresh_var "v" in 
                let ciType = RefTy.MArrow (eff, delta_as_predicate, (vi, ti), P.True) in  
                (*stop when you do not find any new ci*)
        
                let (explored, foundCi)  = enumerateEffAndFind explored gamma sigma delta ciType in 
                match foundCi with
                 | None -> Terminate
                 | Some expci ->  
                        let {Syn.expMon=ci;Syn.ofType=rti} = expci in  
                        let Syn.Evar ci_name = ci in 
                        let RefTy.MArrow (eff_ci, pre_ci, (v_ci, t_ci), post_ci ) = rti in 
                        let delta = let d1 =  P.If (delta_as_predicate, pre_ci) in
                                    let d2 =  P.Conj(delta_as_predicate, d1)  in 
                                    ((P.Conj (d2, post_ci)) :: delta )    
                        in 

                        let accumulatedMonExps = ci_name :: accumulatedMonExps in 
                        let gamma = (xi, ti) :: gamma in 
                        esynthesizePath  explored gamma sigma delta accumulatedMonExps xs 
                           
    in 
    (*a trivial traversal to find a path of do c1;c2;...ck with a backtracking to initial  problem upon failure*)
    let rec traverse_with_backtrack explored  : ((Var.t list) option )= 
        let init_delta = pre::delta  in 
        let effSigma = esynthesizePath explored gamma sigma init_delta [] ls in 
        (match effSigma with 
         | Success res -> Some res
         | Terminate -> None
         | Fail updatedExplored -> traverse_with_backtrack updatedExplored   
        )
         
    in 
    (*start the traversal with empty explored set*)
    let init_explored = Environment.ExploredPaths.empty in 
    traverse_with_backtrack init_explored




(*The special bind rule for let  \Sigma (xi : \taui) <- e1 in return e2 *)
and esynthesizeBindSpecial explored gamma sigma delta spec : (Syn.typedMonExp option) = 
   let RefTy.MArrow (eff, pre, (v,t), post) = spec in
   (*let retConstraints = RefTy.retRefinement post in*)
   let retExpressionsType = t in 
   Message.show ("EsynthesizeBindSpecial Return Type"^(RefTy.toString t)); 
   let holes = isynthesizeHoles gamma sigma retExpressionsType in    
   match holes with 
        |  Some (requiredHoles, returnExp) ->
       (*find out the \Sigma (xi : \taui) using the return statement*) 

           let sigma_xi = requiredHoles in 
           let sigma_xiType = RefTy.Sigma sigma_xi in
           let fresh_v = Var.get_fresh_var "v" in  
           (* let fstSpec = RefTy.MArrow (eff, pre, (fresh_v, sigma_xiType), post) in      *)
           let fstSpec = spec in
           Message.show ("SigmaType "^(RefTy.toString sigma_xiType));
           (* let sigmaExpRes = esynthesizeEffSigma gamma sigma delta sigma_xiType fstSpec in  *)
             
             let sigmaExpRes = esynthesizeEff explored gamma Sigma.empty delta fstSpec in 
           (match sigmaExpRes with 
                | None -> None 
                | Some bodyE-> 
                        let x1 = Var.get_fresh_var "x1" in 
                        let boundMonExp = Syn.Ebind ((Syn.Evar x1), bodyE, returnExp ) in 
                        let boundTypedMonExp = {Syn.expMon = boundMonExp;  Syn.ofType= spec} in 
                        Some boundTypedMonExp
            )
        | None -> 
            let () = Printf.printf "%s" "No Holes from the return type" in


            None                 



(*Top level synthesis goals for effectful computation Types*)
and   esynthesizeEff explored gamma sigma delta spec = 
(*the order of rules is Try return e, and let x <- e1 in return e2 and finally let x <- e1 in e2*)    
     let (explored, cres) = enumerateEffAndFind explored gamma sigma delta spec in 
     match cres with
        |Some res -> 
            let () = Printf.printf "%s" "Single Component Enumeration Succeeded" in 
            let exp1 = Syn.getExp res in 
                let () = 
                match exp1 with      
                    | Syn.Evar c1 -> 
                            subprobplem :=  c1 :: (!subprobplem);      

                    | Syn.Eret tme ->
                         let Syn.Evar c1 = Syn.getExp tme in
                        subprobplem :=  c1 :: (!subprobplem);       
                in                 
               Message.show "PARTIAL PATH NEW";
               let () = Message.show (List.fold_left (fun str vi -> (str^"\t --"^(Var.toString vi))) "SUB " (List.rev !subprobplem)) in 
        
            Some res 
        | None -> (*else see if of the form Pure {} ....*) 
            let () = Printf.printf "%s" "\n Single Component Enumeration Failed, trying the eRet Case" in 
            let returnExp = esynthesizeRet gamma sigma spec in 
            match returnExp with 
                | Some t -> Some t 
                | None -> 
                    let () = Printf.printf "%s" "\n eRet Failed, the effect is not Pure, Attempting esynthesizeBindSpecial" in 
            
                    let bindSpecial= esynthesizeBindSpecial explored gamma sigma delta spec in 
                    match bindSpecial with 
                    | Some t -> Some t 
                    | None ->  
                            Message.show "bindSpecial failed, Attempting Simple Bind Enumeration";             
                            Message.show ("EXPLORED1 "^(Explored.toString explored));
                            let (explored, bindExp) = esynthesizeBind explored gamma sigma delta spec in 
                            
                            match bindExp with 
                             | Some t -> Some t 
                             | None -> None

(* TODO :: First implement a special rule for list, then generalize it to ant algebraic type, say tree*)
and isynthesizeMatch gamma sigma delta matchingArg matchingArgType spec : Syn.typedMonExp option = 
    Message.show ("Show :: Synthesize Match "^(RefTy.toString spec));
   
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
          Message.show ("Show :: Synthesisized Nil Branch Now Trying Cons");

          

          let e_c = synthesize gamma_c sigma delta_c spec learnConst in 
          Message.show ("Show :: Synthesisized Cons Branch ");


          (match (e_n, e_c) with 
           | (Some exp_n, Some exp_c)-> 
                  let caseExps = [exp_n; exp_c] in 
                  let consArgs = [[];[x_var;xs_var]] in
                  (*General Case : we will have the constructor name in the Sigma*)
                  let cons = [Var.fromString "Nil"; Var.fromString "Cons"] in 
                  let matchingArg = {Syn.expMon = Syn.Evar matchingArg; 
                                        Syn.ofType = matchingArgType} in  
                  let matchExp = Syn.merge matchingArg cons consArgs caseExps in

                  Some {Syn.expMon = matchExp;
                        Syn.ofType = spec} 
            |(_,_) -> None)      
 
    | _ ->   
        Message.show "Show :: Non List Case";
        synthesize gamma sigma delta spec learnConst 
  
  

                                    


(*Top level syntheis goals for Lambda, same as the traditional syntehsis rules
calls the top-level macthing and application followed by the standard learning based rule *)
and isynthesizeFun gamma sigma delta spec : Syn.typedMonExp option= 
  (*TODO unhandled case of isynthesize*)   
  let RefTy.Arrow ((x, argT), retT) = spec in 
  (*extend gamma*)
  (*first try a match case, if it does not succeed, try the non-matching case*)
  let gamma_extended = Gamma.add gamma x argT in 
  let match_expression = isynthesizeMatch gamma_extended sigma delta x argT retT in 
  match match_expression with 
    | Some e -> Some e
    | None ->  
        (*TODO *make a call to conditional case*)
        synthesize gamma_extended sigma delta retT learnConst 
  
       
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
                 Some {Syn.expMon=res;Syn.ofType = spec} 
                (*main effectful synthesis rules*)
      | _ -> None  


and chooseC gammacap path spec (dps : DMap.t) (p2gMap : PGMap.t) :  (DPred.gammaCap * PGMap.t * choiceResult)= 
    let RefTy.MArrow (eff, pre, (v, t), post) = spec in 
    let gamma = DPred.getGamma gammacap in 
    let c_wellRetType = Gamma.enumerateAndFind gamma spec in 
   
    let c_wellRetTypeLambda = Gamma.lambdas4RetType gamma spec in 
    let c_es = List.filter (fun (vi, ti) -> 
                        let RefTy.MArrow (effi, _,(_,_), _) = ti in 
                        Effect.isSubEffect effi eff) c_wellRetType in 
    
    let c_es = c_es@c_wellRetTypeLambda in 

    (*choosing a component
    The failing disjunct keeps the list of failing Predicates while checking the Hoare Post => Pre implication*)
    let rec choice potentialChoices gammacap dps (failingDisjuncts : Predicate.t list) (p2gMap : PGMap.t) : (DPred.gammaCap * PGMap.t * choiceResult)= 
        Message.show "Choice ";
        
        (* let potentialChoices = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in  
        Message.show "UNExplored Comn ";
         let () = List.iter (fun (vi,_) -> Message.show (Var.toString vi)) foundTypes in 
 *)
        match potentialChoices with 
        | [] -> 
             Message.show ("Show HERE No more component");
            
            (gammacap, p2gMap,  Nothing (dps, failingDisjuncts)) 
        | (vi, rti) :: xs ->
                Message.show ("Show Component "^(Var.toString vi));
             
            match rti with 
                | RefTy.Arrow ((varg, argty), retty) -> 
                    Message.show (" Show *************** Arrow Component ************"^(Var.toString vi));
                
                    let gammaMap = DPred.getGamma gammacap in 
                    let sigmaMap = DPred.getSigma gammacap in 
                    let deltaPred = DPred.getDelta gammacap in 
                    (*Currently the argument is always a scalar/Base Refinement*)
                    let e_arg =  esynthesizeScalar gammaMap sigmaMap deltaPred argty  in 
                    (match e_arg with (*BEGIN1*)
                        | None -> choice xs gammacap dps failingDisjuncts p2gMap
                        | Some e -> 
                            let (gammacap, post_imp_phi_ci', allowed) =  hoarePre gammacap spec path vi retty in
                            
                            if (allowed) then 
                                
                                let (gamma_with_ci, phi_ci', isDistinguished) = distinguish gammacap dps spec path vi retty in 
                                let () =  Message.show ("Show HERE ") in 
            
                                if (isDistinguished) then 
                                    let p2gMap = PGMap.add p2gMap (path@[vi]) gamma_with_ci in 
                                    (*chosen a ci s.t. path--> ci is allowed and distinguished*)
                                    (gamma_with_ci, p2gMap, Chosen (dps, vi, path@[vi]))  
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
                                   let learnt_diff_conjunct = DPred.DP {gammacap=gamma_with_ci; learnt=not_phi_ci'} in
                                   (*The two gamma will have overlap, requires thinking*)
                                   let updated_dp_ci = DPred.conjunction dp_ci learnt_diff_conjunct in 
                                   let updated_dps = DMap.replace dps vi updated_dp_ci in 
                                   (*make a different choice*)
                                   choice xs gammacap updated_dps failingDisjuncts p2gMap
                                    
                            else
                                let failing_predicate = post_imp_phi_ci' in 
                                (*if Case c1...ck ----> vi  , add D (ck) = pre (vi) *)
                                let dps= 
                                    if (List.length path > 0) then 
                                        (*D(ci)*)               
                                        let c_terminial = List.hd (List.rev (path)) in 
                                        let dp_cterminal = 
                                                    try 
                                                        DMap.find dps c_terminial 
                                                    with 
                                                        Knowledge.NoMappingForVar e -> DPred.empty

                                           in 
                                          
                                        let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate} in
                                           (*The two gamma will have overlap, requires thinking
                                             take disjunction*)
                                        let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in 
                                        let dps = DMap.replace dps c_terminial updated_dp_cterminal in 
                                        dps  
                                    else 
                                        dps  
                                in      
                                let failingDisjuncts = failing_predicate :: failingDisjuncts in 
                                choice xs gammacap dps failingDisjuncts p2gMap
                              

                    ) (*END1*)  

            
                | RefTy.MArrow (_,_,(_,_),_) -> 
                
                (*check the hoare pre-condition rule*)
                            
                        let (gammacap, post_imp_phi_ci', allowed) = hoarePre gammacap spec path vi rti in 
                        if (allowed) then 
                            (
                            Message.show (" Show *************** Hoare-Allowed : Now Checking distingushing Predicate ************"^(Var.toString vi));
                            let (gamma_with_ci, phi_ci', isDistinguished) = distinguish gammacap dps spec path vi rti in 
                            if (isDistinguished) then 
                                (
                                Message.show (" Show *************** Distinguished : Returning the choice ************"^(Var.toString vi));  
                            (*  Message.show (" Show *************** PGMap Before ************"^(PGMap.toString p2gMap));  
                             *) 
                                let p2gMap = PGMap.add p2gMap (path@[vi]) gamma_with_ci in 
                            (*  Message.show (" Show *************** PGMap After ************"^(PGMap.toString p2gMap));  
                             *) (*chosen a ci s.t. path--> ci is allowed and distinguished*)
                                (gamma_with_ci, p2gMap, Chosen (dps, vi, path@[vi]))  
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
                                    let dp_cterminal = 
                                                try 
                                                    DMap.find dps c_terminial 
                                                with 
                                                    Knowledge.NoMappingForVar e -> DPred.empty

                                       in 
                                      
                                    let learnt_diff_disjunct  = DPred.DP {gammacap=gammacap; learnt=failing_predicate} in
                                       (*The two gamma will have overlap, requires thinking
                                         take disjunction*)
                                    let updated_dp_cterminal = DPred.disjunction dp_cterminal learnt_diff_disjunct in 
                                    let dps = DMap.replace dps c_terminial updated_dp_cterminal in 
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
   


and deduceR (gamma:DPred.gammaCap) (compi:Var.t) (path:path) (spec: RefTy.t) 
                (dps : DMap.t) (p2gMap : PGMap.t) : (DPred.gammaCap * PGMap.t * deduceResult) = 
    
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
        
        if (verified) then 
             (
             Message.show ("Show :: Found a correct Path "^(pathToString path));
             (gamma, p2gMap, Success path)
             ) 
        else 
            (
                Message.show ("Show :: Incomplete Path "^(pathToString path)^" Now chosing Next component "^(Var.toString compi));
            
                let (gamma, p2gMap, nextComponent) = chooseC gamma path spec dps p2gMap in 
                match nextComponent with 
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
                 



(*cdcleffSynthesizeBind : DPred.gammaCap -> DMap.t -> RefTy.t -> Syn.monExp*)
 and cdcleffSynthesizeBind (gammaCap : DPred.gammaCap)  
                    (dps : DMap.t) (spec : RefTy.t) : Syn.monExp = 
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
                    raise (LearningException "No program and No possible backtracking")
            | Chosen (dps', ci, pi) ->  
                
                Message.show (" EXPLORED :: "^(pathToString pi));
        
                Message.show (" ShowPath :: "^pathToString pi);
        
                Message.show ("Show :: Chosen "^(Var.toString ci));
            (*  Message.show ("New DPS "^(DMap.toString dps));
             *) Message.show(" Run deduceR");
                let (gammacap, p2gMap, deduceres) = deduceR gammacap ci pi spec dps' p2gMap in 
                match deduceres with 
                    | Success p ->
                            Message.show (" EXPLORED :: "^(pathToString p));
             
                            Syn.buildProgramTerm  p
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



