module Syn = Lambdasyn 
open SpecLang 
module Gamma = Environment.TypingEnv
module Sigma = Environment.Constructors 
module P = Predicate

exception NoMappingForVar of string
    
(*A var to refinement type mapping typing environment*)

module DiffPredicate = struct
	type gammaCap =  T of {gamma : Gamma.t; sigma : Sigma.t; delta : P.t}
	type t = DP of {gammacap : gammaCap; learnt : P.t}


	let emptyGammaCap = T {gamma= Gamma.empty; sigma = Sigma.empty; delta = P.True}

	let getGamma gcap = 
		let T {gamma ;sigma ;delta} = gcap in 
		gamma

	let getSigma gcap = 
		let T {gamma ;sigma ;delta} = gcap in 
		sigma
	let getDelta gcap = 
		let T {gamma ;sigma ;delta} = gcap in 
		delta 
			
	



	let getGammaCap dpred = 
		let DP {gammacap;_} = dpred in 
		gammacap

	let getLearnt dpred = 
		let DP {learnt;_} = dpred in 
		learnt
	
	let empty = DP {gammacap = emptyGammaCap; learnt = P.True}
	
	let gammaCapToString g = 
		let T {gamma;sigma;delta} = g in 
		let str = 
			let gammaStr = "gamma TBU" in 
			let sigmaStr = "sigma TBU" in 
			let deltaStr = Predicate.toString delta in 
			(gammaStr^sigmaStr^deltaStr) in 
		str	 

	let appendGammaCap gcap1 gcap2 = 
		let T {gamma= gamma1;sigma=sigma1;delta=delta1}  = gcap1 in 
		let T {gamma= gamma2;sigma=sigma2;delta=delta2}  = gcap2 in 
		T {gamma=gamma1@gamma2 ; 
			sigma = sigma1@sigma2 ; 
			delta= P.Conj (delta1, delta2)} 


	let toString t = "DiffPredicate TBU"

	let equal t1 t2 = 
	 (*TODO ??*)
	 true


	 let no_pollution t1 t2 = 
	 (*TODO ?? *)
	  true


	(*gamma1, pred1 /\ gamma2, pred2 =  noOverlap(gamma1;gamma2), pred1/\ pred2*)
	let conjunction t1 t2 = 
		(*the pollution of gammas must be *)
		let DP {gammacap=gcap1; learnt=learnt1} = t1 in 
		let DP {gammacap =gcap2; learnt=learnt2} = t2 in 
		assert (no_pollution  gcap1 gcap2);
		let gamma = appendGammaCap gcap1 gcap2 in 
		let pred = Predicate.Conj(learnt1, learnt2) in 
		DP {gammacap=gamma;learnt=pred} 
end

module DistinguisherMap = struct

module Component =
       struct
         type t = Var.t (*a variable capturing the  name*)
         let equal(t1,t2)  =  Var.equal t1 t2
       end

module Disntinguisher =
       struct
         (*Need to change later to scehema*)
         type t = DiffPredicate.t
         let equal (t1,t2) = DiffPredicate.equal t1 t2           
end

module Map   = Applicativemap.ApplicativeMap (Component) (Disntinguisher) 

type t = Map.t
let empty = Map.empty
let mem =  Map.mem
let find t var = 
    try (Map.find t var) 
  with 
  | (Map.KeyNotFound k) -> raise (NoMappingForVar k)

let add = fun t -> fun var rt -> Map.add t var rt
let remove = Map.remove
let replace = Map.replace 


end 

