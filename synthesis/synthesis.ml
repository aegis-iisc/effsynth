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

module Message = struct 

  let show (s:string) = Printf.printf "%s" ("\n"^s) 


end

let itercount = ref 0 
let enumerated = ref [] 


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




let rec enumerateEffAndFind explored gamma sigma delta (spec : RefTy.t)  : (Syn.typedMonExp option) = 
   match spec with 
       | RefTy.MArrow (eff, pre, (v, t), post) -> 
         let foundTypes = Gamma.enumerateAndFind gamma spec in 
         List.iter (fun (v, ft) -> Message.show (RefTy.toString ft));
          (*filter the explored*)
         let foundTypes = List.filter (fun (vi, _) -> not (Explored.mem explored vi)) foundTypes in  
         (* let () = List.iter (fun (vi, rti) -> Printf.printf "%s" ("\n Gamma |- "^(Var.toString vi)^" : "^(RefTy.toString rti))) foundTypes in           
          *)
         let rec verifyFound fs  = 
            let () = Printf.printf "%s" ("\n *********************Enumeration Iteration*****************"^(string_of_int(!itercount))) in
            if (!itercount > 100) then 
                let () = Message.show (List.fold_left (fun str vi -> (str^"::"^(Var.toString vi))) "ENUM " !enumerated) in 
                raise (SynthesisException "FORCED STOPPED") 
            else 
            let _ = itercount := !itercount + 1 in  
            match fs with
             | [] -> None 
             | (vi, rti) :: xs -> 
                (*filter on effects before actuall checking the hoare triples*) 
                let RefTy.MArrow (effi, _,_,_) = rti in  
                if (not (Effect.isSubEffect effi eff))  
                        then verifyFound xs    
                else    
                        let _ = enumerated := (vi :: !enumerated) in     
                        let () =Message.show ("Found after Enumeration "^(RefTy.toString rti)) in 
                        let () =Message.show ("Compared Against Spec "^(RefTy.toString spec)) in 
                        let vc = VC.fromTypeCheck gamma delta (rti, spec) in 
                        (*make a direct call to the SMT solver*)
                        let vcStandard = VC.standardize vc in 
                        Message.show (VC.string_for_vc_stt vcStandard);
                        let result = VCE.discharge vcStandard  in 
                        match result with 
                        | VCE.Success -> let retMonExp = Syn.Eret ({expMon=(Syn.Evar (vi)); ofType=rti}) in 
                                          Some {expMon = retMonExp; ofType=rti}
                        | VCE.Failure -> verifyFound xs
                        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                        
         in 
         verifyFound foundTypes

      | _ -> raise (SynthesisException ("Effectful Enumeration for non MArrow Type"^(RefTy.toString spec)))  



(*The main projection function which pushes information from Goal to inner nodes*)       
(*TODO :: Test this
 *  shape of baseRefinement is Base (Var.t * TyD.t * Predicate.t) *)
let project (goalPred:Predicate.t) gamma (args:RefTy.t list)  : (Var.t * RefTy.t) list = 
        let conjuncts = Predicate.conjunctify goalPred in 
        (*assume for any type t = C([xi:ti]) there exists relations [pri : (v : t) :-> ti] with relids "pri" *)
        (*projects the goalPredicate conjuncts to those conjuncts containing projection relations in the set {pr1, pr2, .... prk}*)
        let project_k (k:int) conjs = 
                let relID_k = RelId.fromString ("pr"^(string_of_int k)) in
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
        
        




(*Top level syntheis goals for Lambda, same as the traditional syntehsis rules *)
let rec isynthesizeFun gamma sigma spec = 
  (*TODO unhandled case of isynthesize*)   
  None

       
(*enumerates and finds function term variable of functional type*)
let esynthesizeFun explored gamma sigma spec : Syn.typedMonExp option = 
       let foundbyEnum = enumPureE explored gamma sigma spec in 
       match foundbyEnum with 
               | Some t -> Some t 
               | None -> 
                     (*if we cannot find a function of the given type we can make a call to iRule for function synthesis*)   
                     isynthesizeFun gamma sigma spec               

          



(*The Tapp rule*) 
let rec esynthesizeApp gamma sigma spec  : Syn.typedMonExp option =  
        (*explore the functions in gamma with the required body type*)
        let funType = RefTy.Arrow ((Var.get_fresh_var "v", RefTy.fromTyD Ty_unknown), spec) in  
        let explored = Explored.empty in 
        let rec choose explored ftype : (Syn.typedMonExp option)=  
                let efun =  esynthesizeFun explored gamma sigma ftype in 
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
        let RefTy.Base (v, t, pred) = spec in 
        let exploredCons = Sigma.empty in 
        (*find a C \in Sigma with shape C : (xi:\tau:i) -> t *)
        let foundCons = Sigma.findCons4retT sigma spec in 
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
                 Some (consArgsWithInferredTypes, consAppExp) 
                 



(*creates a list of missing args required while synthesizing the intro term for spec*)
let isynthesizeHoles gamma sigma spec : ((Var.t * RefTy.t) list* Syn.typedMonExp) option  = 
        (*To syntesize holes, try applying Consrtructors in sigma or functions in gamma
         * Currently only trying constructor application*)
        let missingTypedArgsList_constAppExp = isynthesizeConstApp gamma sigma spec in 
         missingTypedArgsList_constAppExp 

(*T-ret rule*)
let esynthesizeRet gamma sigma spec : (Syn.typedMonExp option)=  
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
let rec esynthesizeBind gamma sigma delta spec : (Syn.typedMonExp option) = 
   
    Message.show ("esynthesizeBind");

     (*We need to divide the effects and the intermediate heap constraints in a way which gives two subproblems*)
   let RefTy.MArrow (eff, pre, t , post) = spec in 
   (*TODO break based on effects*)
   let gamma = Gamma.filterOnEffectSet gamma eff in 

   let rec enumerateSubProblems explored  =  
       (*we need to break the interval into eff pre and post into subproblems*)
       let retResult = (Var.get_fresh_var "v") in 
       let unKnownType = RefTy.Base (retResult, TyD.Ty_unknown , Predicate.True) in 
       let spec1 = RefTy.MArrow (eff, pre, (retResult, unKnownType), Predicate.True) in 
       (*right now we dont have any explored set*)
       
       let e1_res = enumerateEffAndFind explored gamma sigma delta spec1 in 
       
       match e1_res with 
            | Some e1 -> 
                Message.show "Found e1 in (x <- e1 in e2), Synthesizing now e2 ";
               let fstType = Syn.getType e1 in 
               assert (RefTy.isEffectful fstType);
               let RefTy.MArrow (eff1, pre1, (x1, t1), post1) = fstType in 
               let gamma = Gamma.add gamma x1 t1 in 
                
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
               
               let e2_res = esynthesizeEff gamma sigma delta spec2 in 
               (match e2_res with 
                | Some e2 -> 
                        Message.show "Found e2 in (x <- e1 in e2)";
                        Message.show (Syn.typedMonExp_toString e2); 
                        let boundMonExp = Syn.Ebind ((Syn.Evar x1), e1, e2) in 
                        let boundTypedMonExpp = {Syn.expMon = boundMonExp;  Syn.ofType= spec} in 
                        Some boundTypedMonExpp 

                | None -> 
                        let Syn.Evar c1 = Syn.getExp e1  in 
                        let explored = Explored.add explored c1 in 
                        enumerateSubProblems explored 
                )            
            | None ->
                    Message.show "First component finding failed"; 
                    None   



    in 
    enumerateSubProblems Explored.empty         


(*accumulatedMonExps are strucutured as list of component names*)
and esynthesizeEffSigma gamma sigma delta sigmaType spec : (Var.t list) option = 
       (* the real enumeration of component sequencing will happen here
        *)
   let RefTy.Sigma (ls) = sigmaType in  
   let RefTy.MArrow (eff, pre, _ , post) = spec in 
   (*delta = .| pred /\ delta*)
   (*explored in this case will be list of paths*)
   (*accumulateMonExps are the list of componensts c1 ; c2 ;..., ck*)
   let rec esynthesizePath explored gamma sigma delta accumulatedMonExps ltuples : ((Var.t list), (Environment.ExploredPaths.t)) result = 
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
        
                let foundCi  = enumerateEffAndFind explored gamma sigma delta ciType in 
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
and esynthesizeBindSpecial gamma sigma delta spec : (Syn.typedMonExp option) = 
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
           let fstSpec = RefTy.MArrow (eff, pre, (fresh_v, sigma_xiType), post) in     
           let sigmaExpRes = esynthesizeEffSigma gamma sigma delta sigma_xiType fstSpec in 
           (match sigmaExpRes with 
                | None -> None 
                | Some list_comps -> 
                        let exp_for_comps = List.map (fun ci_name -> Syn.Evar ci_name) list_comps in
                        let exp = Syn.doExp (exp_for_comps@[(Syn.getExp returnExp)]) in
                        Some {Syn.expMon = exp; Syn.ofType=spec}
            )
        | None -> 
            let () = Printf.printf "%s" "No Holes from the return type" in


            None                 



(*Top level synthesis goals for effectful computation Types*)
and   esynthesizeEff  gamma sigma delta spec = 
(*the order of rules is Try return e, and let x <- e1 in return e2 and finally let x <- e1 in e2*)    
     let cres = enumerateEffAndFind Environment.ExploredPaths.empty gamma sigma delta spec in 
     match cres with
        |Some res -> 
            let () = Printf.printf "%s" "Component Enumeration Succeeded" in 
            Some res 
        | None -> (*else see if of the form Pure {} ....*) 
            let () = Printf.printf "%s" "Component Enumeration Failed, trying the eRet Case" in 
            let returnExp = esynthesizeRet gamma sigma spec in 
            match returnExp with 
                | Some t -> Some t 
                | None -> 
                    let () = Printf.printf "%s" "eRet Failed, the effect is not Pure, Attempting esynthesizeBindSpecial" in 
            
                    let bindSpecial= esynthesizeBindSpecial gamma sigma delta spec in 
                    match bindSpecial with 
                    | Some t -> Some t 
                    | None ->  
                            Message.show "bindSpecial failed, Attempting Simple Bind Enumeration";             
                            let bindExp = esynthesizeBind gamma sigma delta spec in 
                            match bindExp with 
                             | Some t -> Some t 
                             | None -> None             

  
(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
let rec synthesize gamma sigma spec : (Syn.typedMonExp option)=  
   match spec with 
      | RefTy.Base (v, t, pred) -> esynthesizeScalar gamma sigma spec  
      | RefTy.Arrow (rta, rtb) -> isynthesizeFun gamma sigma spec  (*applies Tfix and Tabs one after the other*)
      | RefTy.MArrow (eff, pre, t, post) -> esynthesizeEff gamma sigma VC.empty_delta spec (*main effectful synthesis rules*)
      | _ -> None  

