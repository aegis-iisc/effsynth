D : [nlrecord];
D' : [nlrecord];
d : ref [nlrecord];


confirmU :  (n  : { v : string | true})-> 
		  (u : { v :string | true}) -> 
		State {\(h:heap).
				\(D : [nlrecord]).
				(dsel (h, d) = D =>  subscribed (D, n, u) = true)}
			v : {v : unit | true}
			{ \(h: heap),(v : unit),(h': heap).
				\(D : [nlrecord]), (D' : [nlrecord]).
				dsel (h', d) = D'/\
				dsel (h, d) = D /\
				subscribed (D', n, u) = true /\ 		
				nlmem (D', n, u) = true /\
				confirmed (D', n, u) = true};


confirmS :  (n  : { v : string | true})-> 
		  (u : { v :string | true}) -> 
		State {\(h:heap).
				\(D : [nlrecord]).
				(dsel (h, d) = D =>  subscribed (D, n, u) = false)}
			v : {v : unit | true}
			{ \(h: heap),(v : unit),(h': heap).
				\(D : [nlrecord]), (D' : [nlrecord]).
				dsel (h', d) = D'/\
				dsel (h, d) = D /\
				subscribed (D', n, u) = true /\ 		
				nlmem (D', n, u) = true /\
				confirmed (D', n, u) = true};


subscribe : (n  : { v : string | true})-> 
			 (u : { v :string | true}) -> 
					State {\(h : heap). 
							\(D : [nlrecord]).
								dsel (h, d) = D => 
									(nlmem (D , n , u) = true /\ confirmed (D, n, u) = true
									/\ subscribed (D, n, u) = false)}
					v : { v : unit | true}  
						{\(h: heap),(v : unit),(h': heap).
							\(D : [nlrecord]), (D' : [nlrecord]).
							dsel (h', d) = D'/\
							dsel (h, d) = D /\
							nlmem (D', n, u) = true /\
							subscribed (D', n, u) = true 		
							};	



unsubscribe : (n  : { v : string | true})-> 
			 (u : { v :string | true}) -> 
					State {\(h : heap). 
							\(D : [nlrecord]).
								dsel (h, d) = D => 
									(nlmem (D , n , u) = true /\ confirmed (D, n, u) = true /\
									subscribed (D, n, u) = true)}
					v : { v : unit | true}  
						{\(h: heap),(v : unit),(h': heap).
							\(D : [nlrecord]), (D' : [nlrecord]).
							dsel (h', d) = D'/\
							dsel (h, d) = D /\
							nlmem (D', n, u) = true /\
							subscribed (D', n, u) = false 		
							};	




read :  (n  : { v : string | true})-> 
		(u : { v :string | true}) -> 
		State {\(h : heap). 
				\(D : [nlrecord]).
					dsel (h, d) = D =>
						(nlmem (D , n , u) = true /\ 
						subscribed (D, n, u) = true
						)
				}
				v : { v : [string] | true}  
			{\(h: heap),(v : [string]),(h': heap).
				\(D : [nlrecord]), (D' : [nlrecord]).
				dsel (h', d) = D'/\
				dsel (h, d) = D /\
				nlmem (D', n, u) = true /\
				subscribed (D', n, u) = true /\ 		
				v = articles (D', n, u)};
		
		 
remove : (n  : { v : string | true})-> 
		 (u : { v :string | true}) -> 
				State {\(h : heap). 
						\(D : [nlrecord]).
						(dsel (h, d) = D =>
							(nlmem (D , n , u) = true /\
							subscribed (D, n, u) = false) 
						)	
					}
				v : { v : unit | true}  
				{\(h: heap),(v : unit),(h': heap).
						\(D : [nlrecord]), (D' : [nlrecord]).
							dsel (h', d) = D' /\ 
							dsel (h, d) = D /\
							nlmem (D', n, u) = false 
				};
		 
goal : 	 (n  : { v : string | true})-> 
		 (u : { v :string | true}) -> 
				State {\(h : heap). 
						\(D : [nlrecord]).
						(dsel (h, d) = D /\ 
						subscribed (D, n, u) = true)}
				v : { v : [string] | true}  
				{\(h: heap),(v : [string]),(h': heap).
						\(D : [nlrecord]), (D' : [nlrecord]).
							dsel (h', d) = D' /\ 
							dsel (h, d) = D /\
							nlmem (D', n, u) = false /\
							v = articles (D', n, u)};
		 
