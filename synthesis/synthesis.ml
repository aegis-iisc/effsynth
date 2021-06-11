module Syn = Lambdasyn
module VC = TransTypeChecker.VerificationC   
open SpecLang 
module Gamma = Environment.TypingEnv 
module Sigma = Environment.Constructors
module Explored = Environment.ExploredTerms                 
module VCE = Vcencode 
module P = Predicate  
exception SynthesisException of string 
exception Unhandled

let enumPureE explored gamma sigma spec = 
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
                 
                let vc = VC.fromTypeCheck gamma (rti, spec) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                match result with 
                | VCE.Success -> Some (Syn.Evar (vi)) 

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
            
                let vc = VC.fromTypeCheck gamma (rti, spec) in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                match result with 
                | VCE.Success -> Some ({expMon=(Syn.Evar (vi)); ofType=rti}) 
                | VCE.Failure -> verifyFound xs
                | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                
         in 
         verifyFound foundTypes

     

      | RefTy.MArrow (eff, pre, t, post) -> 
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
                        let vc = VC.fromTypeCheck gamma (rti, spec) in 
                        (*make a direct call to the SMT solver*)
                        let vcStandard = VC.standardize vc in 
                        let result = VCE.discharge vcStandard  in 
                        match result with 
                        | VCE.Success -> Some (Syn.Eret ({expMon=(Syn.Evar (vi)); ofType=rti})) 

                        | VCE.Failure -> verifyFound xs
                        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                        
         in 
         verifyFound foundTypes

      | _ -> raise (SynthesisException "Illegal elimination form")       

(*core enumeration for effectful terms*)
let enumerateEffE explored gamma sigma spec = 






(*Top level syntheis goals for App *)
let rec isynthesizeFun gamma sigma spec = 
  (*TODO unhandled case of isynthesize*)   
  None

(*enumerates to find if there is a variable else synthesizes a term of the type spec and returns*)
let isynthesizeScalar gamma sigma spec : (Var.t * RefTy.t) 
        
(*enumerates and finds a variable of functional type*)
let esynthesizeFun explored gamma sigma spec : (Var.t * Refty.t) = 
       let foundbyEnum = enumPureE explored gamma sigma spec in 
       match foundbyEnum with 
               | Some t -> Some t 
               | None -> 
                     (*if we cannot find a function of the given type we can make a call to iRule for function synthesis*)   
                     let appterm = esynthesizeApp explored gamma sigma spec in 
                        match appterm with 
                        | Some t1 -> Some t1 
                        | None -> isynthesizeFun gamma sigma spec               

          



(*The Tapp rule*) 
let esynthesizeApp gamma sigma spec =  
        (*explore the functions in gamma with the required body type*)
        let funType = RefTy.Arrow ((Var.get_fresh_var "v", Ty_unknown), spec) in  
        let explored = Explorer.empty in 
        let rec choose explored ftype =  
                let efun =  esynthesizeFun explored gamma sigma fType in 
                match efuns with 
                        | None -> None
                        | Some (vlam, rtlam) -> 
                                match rtlam with 
                                 | RefTy.Arrow ((v1, t1), t2) -> 
                                         let (earg, etype) = isynthesizeScalar gamma sigma t1 in 
                                         let constraintsArg = VC.fromTypeCheck etype t1 in 
                                         let substitutedType = RefTy.applySubsts [(earg, v1)] t2 in
                                         let vc= VC.fromTypeCheck substitutedType spec in 
                                        
                                         (*make a direct call to the SMT solver*)
                                        let vcStandard = VC.standardize vc in 
                                        let result = VCE.discharge vcStandard  in 
                                           match result with 
                                                | VCE.Success ->
                                                        try 
                                                          let funTerm = {expMon = Sigma.find (vlam); ofType= rtlam} in  in
                                                           Some funTerm(*create a term*) 
                                                        with 
                                                          | e -> raise e 
                                                | VCE.Failure -> (*make another choice for the function*)choose (vlam :: explored) ftype
                                                | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
                               
                                 | _ -> raise (SynthesisException ("Application over a non arrow type"^RefTy.toString rtlam)
        in 
        choose explored funType 


(*Top lvel goal synthesis for scalar Types*)
let rec esynthesizeScalar gamma sigma spec = 
    (*TODO Other cases*) 
     let explored = Explorer.empty in    
     let foundbyEnum = enumPureE explored gamma sigma spec in 
     match foundbyEnum with 
       | Some t -> Some t       
       | None -> 
                
             let appterm = esynthesizeApp explored gamma sigma spec in 
                match appterm with 
                | Some t1 -> Some t1 
                | None -> 
                        (*constructor application*)
                        let constAppterm = isynthesiszeConstApp gamma sigma spec in 
                        match constAppterm with 
                          | Some t2 -> Some t2
                          | None -> None             
(**)       
let project (goalPred:Predicate.t) gamma args  



let isynthesizeConstApp gamma sigma spec : (Syn.typedMonExp list * Syn.typedMonExp) = 
        let RefTy.Base (v, t, pred) = spec in 
        let exploredCons = Sigma.empty in 
        (*find a C \in Sigma with shape C : (xi:\tau:i) -> *)
        let foundCons = Sigma.findCons4retT sigma spec in 
        match foundCons with 
           | [] -> None 
           | Some ls -> 
                let (vi, rti) = List.head ls in 
                let getExpandedConsType refTy =  
                        match refTy with
                           | RefTy.Arrow ((_, t1 ), t2) -> 
                                match t1 with 
                                 | RefTy.Base(va, ta, preda) -> [t1;t2]
                                 | RefTy.Tuple listArgs -> List.append listArgs t2                               
                 in 
                 let consArgs = getExpandedConsType rti in 

                 (*auxiliary function project projects/pushes the given constraints on the output to argumenets of the constructor
                  *
                  * *)
                 let consArgsWithInferredTypes = project gamma pred consArgs in 
                 let consArgsNames = List.map (fun (vi, rti) -> v1) consArgsWithInferredTypes in 
                 let consAppExp = Syn.Ecapp (vi, consArgsName) in 

                 (consArgsWithInferredTypes, consAppExp) 
                 




(*creates a list of missing args required while synthesizing the intro term for spec*)
let rec isynthesizeHoles gamma sigma spec : (Syn.typedMonExp* (Syn.typedMonExp list)) = 
        let (missingTypedArgsList, constExp) = isynthesizeConstApp gamma sigma spec in 
        (missingTypedArgsList, constExp) 

(*T-ret*)
let esynthesizeRet gamma sigma spec =  
  let RefTy.MArrow (eff, pre, t, post) = spec in 
  let constraints  = RefTy.getRetConstraints post (*define a function to extract the constraints over t from the post*)
  let refT = RefTy.Base ((Var.get_fresh_var "v"), t, constraints) in 
 
  (*either find a variable in the gamma or find a funapplication term or a constructor application term*)
  let exp = esynthesizeScalar gamma sigma 
  match exp with 
    | Some e -> Some e 
    | None -> None              

(*The general bind rule for let \Sigma (xi : \taui) <- e1 in e2*)
let rec esynthesizeBind gamma sigma spec = 
     (*We need to divide the effects and the intermediate heap constraints in a way which gives two subproblems*)
   let RefTy.MArrow (eff, pre, t , post) = spec in 
   None (*The general bind case will only be called after the special case fails to find a solution*)     


type ('a, 'b) result = Success of 'a 
            | Fail of 'b
            | Terminate


let esynthesizeEffSigma gamma sigma sigmaType spec : (Var.t list) option = 
       (* the real enumeration of component sequencing will happen here
        *)
   let RefTy.Tuple (ls) = sigmaType in  
   let RefTy.MArrow (eff, pre, _ , post) = spec in 
   (*delta = .| pred /\ delta*)
   (*explored in this case will be list of paths*)
   (*accumulateMonExps are the list of componensts c1 ; c2 ;..., ck*)
   let esynthesizePath gamma sigma explored delta accumulatedMonExps ltuples : ((Var.t list), (Env.ExploredPaths.t)) result = 
     match ltuples with 
        | [] -> 
                
                let vc = VC.create gamma delta post in 
                (*make a direct call to the SMT solver*)
                let vcStandard = VC.standardize vc in 
                let result = VCE.discharge vcStandard  in 
                   match result with 
                        | VCE.Success ->
                           Left accumulatedMonExps
                        | VCE.Failure -> 
                          let failingPath = Env.ExploredPaths.fromList accumulatedMonExps in 
                          let explored = failingPath :: explored in 
                          Right explored
                        | VCE.Undef -> raise (SynthesisException "Typechecking Did not terminate")  
       

        | (xi , ti) :: xs -> 
                assert (not (Gamma.mem gamma xi) 
                let ciType = RefTy.MArrow (eff, delta, ti, P.True) in  
                (*stop when you do not find any new ci*)
                let foundCi  = enumerateEffAndFind gamma sigma explored delta ciType in 
                match foundCi with
                 | None -> Terminate
                 | Some (ci, rti) -> 
                        let c_rti = RefTy.MArrrow (eff_ci, pre_ci, t_ci, post_ci ) in 
                        let delta = let d1 =  P.If (delta, pre_ci) in
                                    let d2 =  P.Conj(delta, d1)  in 
                                    P.Conj (d2, post_ci)   
                        in 
                        let accumulatedMonExps = ci :: accumulatedMonExps in 
                        let gamma = (xi, ti) :: gamma in 
                        esynthesizePath gamma sigma delta accumulatedMonExps xs 
                           
    in 
    let effSigma = synthesizePath gamma sigma Env.ExploredPaths.empty pre [] ls in 
    match effSigma with 
     | Success res -> Some res
     | Terminiate -> None
     | Fail updatedExplored -> synthesizePath gamma sigma updatedExplored pre [] ls  
     

(*The special bind rule for let  \Sigma (xi : \taui) <- e1 in return e2 *)
let rec esynthesizeBindSpecial gammma sigma spec : (Syn.monExp option) = 
   let RefTy.MArrow (eff, pre, t, post) = spec in
   let retConstraints = RefTy.retRefinement post in 
   (*let refT = RefTy.Base ((Var.get_fresh_var "v"), t, retConstraints) in *)
   let (requiredHoles, returnExp) =  isynthesizeHoles gamma sigma spec in    
   (*find out the \Sigma (xi : \taui) using the return statement*) 
   let sigma_xi = RefTy.tupleTypeFromList requiredHoles in 
   let fstSpec = RefTy.MArrow (eff, pre,  RefTy.toTyD (sigma_xi), post) in     
   let sigmaExpRes = esynthesizeEffSigma gamma sigma sigma_xi fstSpec in 
   match sigmaExp with 
        | None -> None 
        | Some sigmaExp -> 
                let exp = Syn.Edo (fstExp, retrunExp) in
                Someexp




(*Top level synthesis goals for effectful computation Types*)
and   esynthesizeEff gamma sigma spec = 
(*the order of rules is Try return e, and let x <- e1 in e2*)    
     let returnExp = esynthesizeRet gamma sigma spec in 
     match returnExp with 
        | Some t -> Some t 
        | None -> 
                let bindSpecial= esynthesizeBindSpecial gamma sigma spec in 
                match bindSpecial with 
                | Some t -> Some t 
                | None ->               
                        let bindExp = esynthesizeBind gamma sigma spec in 
                        match bindExp with 
                         | Some t -> Some t 
                         | None -> None             

  
(*In some cases the input spec can be more than the RefinementType*)
(*synthesize : TypingEnv.t -> Constructors.t -> RefinementType.t -> Syn.typedMonExp option *)
let rec synthesize gamma sigma spec =  
   match spec with 
      | RefTy.Base (v, t, pred) -> esynthesizeScalar gamma sigma spec  
      | RefTy.Arrow (rta, rtb)> isynthesizeFun gamma sigma spec  (*applies Tfix and Tabs one after the other*)
      | RefTy.MArrow (eff, pre, t, post) -> esynthesizeEff gamma sigma spec (*main effectful synthesis rules*)
      | _ -> None  

