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
module CDCL = Learning
module P = Predicate  
module SynTC = Syntypechecker

exception SynthesisException of string 
exception Unhandled
open Syn

module Message = struct 

  let show (s:string) = Printf.printf "%s" ("\n"^s) 


end

let itercount = ref 0 
let enumerated = ref [] 
let subprobplem = ref []

let learnConst = true 
let noLearnConst = false

type ('a, 'b) result = 
            Success of 'a 
            | Fail of 'b
            | Terminate


 

let enumPureE explored gamma sigma (spec : RefTy.t) : Syn.typedMonExp option  = 
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
                 
                let vc = VC.fromTypeCheck gamma (VC.empty_delta) (rti, spec) in 
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
        
        



          



(*The Tapp rule*) 
let rec esynthesizeApp gamma sigma spec  : Syn.typedMonExp option =  
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
                                         match esynthesizeScalar gamma sigma t1 with 
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
and esynthesizeScalar gamma sigma spec : Syn.typedMonExp option  = 
    (*TODO Other cases*) 
     let explored = Explored.empty in    
     let foundbyEnum = enumPureE explored gamma sigma spec in 
     match foundbyEnum with 
       | Some t -> Some t       
       | None -> 
                
             let appterm = esynthesizeApp gamma sigma spec in 
                match appterm with 
                | Some t1 -> Some t1 
                | None -> 
                        (*constructor application*)
                        let constAppterm = isynthesizeConstApp gamma sigma spec in 
                        match constAppterm with 
                          | Some t2 -> let (argLists, constAppExp) = t2 in Some constAppExp
                          | None -> None         
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
              let exp = esynthesizeScalar gamma sigma retT in  
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
          let e_c = synthesize gamma_c sigma delta_c spec learnConst in 

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
  let macth_expression = isynthesizeMatch gamma_extended sigma delta x argT retT in 
  match macth_expression with 
    | Some e -> Some e
    | None ->  
        (*TODO *make a call to conditional case*)
        synthesize gamma_extended sigma delta retT learnConst 
  
       
(*enumerates and finds function term variable of functional type*)
and esynthesizeFun explored gamma sigma delta spec : Syn.typedMonExp option = 
       let foundbyEnum = enumPureE explored gamma sigma spec in 
       match foundbyEnum with 
               | Some t -> Some t 
               | None -> 
                     (*if we cannot find a function of the given type we can make a call to iRule for function synthesis*)   
                     isynthesizeFun gamma sigma delta spec               



(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
and  synthesize gamma sigma delta spec learning : (Syn.typedMonExp option)=  
   match spec with 
      | RefTy.Base (v, t, pred) -> esynthesizeScalar gamma sigma spec  
      | RefTy.Arrow (rta, rtb) -> 
                 Message.show "***********Calling S-FUNC synthesize***************";
                    
                isynthesizeFun gamma sigma delta spec  (*applies Tfix and Tabs one after the other*)
      | RefTy.MArrow (eff, pre, t, post) -> (* let res = esynthesizeEff Explored.empty gamma sigma VC.empty_delta spec in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in 
                 let () = Message.show (List.fold_left (fun str vi -> (str^"\n \t --"^(Var.toString vi))) "SUB " !subprobplem) in 
                  *)
                  Message.show "***********Calling CDCL synthesize***************";
                 (*testing cdcl approach*)
                 let gammacap = DPred.T {gamma = gamma; sigma=sigma;delta= delta} in 
                 let dps_empty = DMap.empty in 
                 let res = 
                    if (learning) then 
                     Learning.cdcleffSynthesizeBind gammacap dps_empty spec 
                    else  
                     NoLearning.cdcleffSynthesizeBind gammacap dps_empty spec 
                 in     
                 Some {Syn.expMon=res;Syn.ofType = spec} 
                (*main effectful synthesis rules*)
      | _ -> None  

