dtab : ref [int];
cstab : ref [srpair];
D : [int];
CS : [srpair];

add_device : (d : { v : int | true}) -> State {
										\(h : heap).	
										\(D : [int]), (CS : [srpair]).
										didsel (h, dtab) = D =>		
										device (D, d) = false}
										v : {v : unit | true}
										{\(h: heap),(v : unit),(h': heap).
											\(D : [int]), (D' : [int]).
											dissel (h, dtab) = D /\		
											didsel (h', dtab) = D' /\
											dcssel (h', cstab) = dcssel (h, cstab) /\
											device (D', d) = true	/\
											dsize (D') == dsize (D) + 1 	
										};  




diff_device : (d : { v : int | true}) -> State {
										\(h : heap).
											\(D : [int]), (CS : [srpair]).
											didsel (h, dtab) = D =>	
											dsize (D) > 1}
											v : {v : int | true}
											{\(h: heap),(v : int),(h': heap).
												\(D : [int]), (D' : [int]),(CS : [srpair]),(CS' : [srpair]).
												 D' = D /\
												 CS' = CS /\
												device (D', v) = true /\ 
												not ([v = d])
											}; 


add_connection : (s : { v : int | true}) 
					-> (r : { v : int | true}) -> 
									State {
										\(h : heap).
											\(D : [int]), (CS : [srpair]).
											didsel (h, dtab) = D =>	
											(device (D, s) = true /\ device (D, r) = true)	
											}
											v : {v : unit | true}
											{\(h: heap),(v : unit),(h': heap).
												\(D : [int]), (D' : [int]),(CS : [srpair]),(CS' : [srpair]).
												 D' = D /\
												 cansend (CS', s, r) = true 
											}; 



make_central : (d : { v : int | true}) -> State {
										\(h : heap).
											\(D : [int]).
											didsel (h, dtab) = D =>	
											device (D, d) = true	
											}
											v :  { v : unit | true}
										 { \(h: heap),(v : unit),(h': heap).
												\(CS : [srpair]), (CS' : [srpair]).
										 		didsel (h', dtab) = didsel (h, dtab) /\
												central (CS', d) = true
										 };





delete_device : (d : { v : int | true}) -> 
								State {\(h : heap).
											\(D : [int]), (CS : [srpair]),(y : int).
											didsel (h, dtab) = D =>	
											(device (D, d) = true /\ 
											device (D, y) = true /\ 
											central (CS, y) = true)}
									v : {v : unit | true}
								 { \(h: heap),(v : unit),(h': heap).
										\(D : [int]), (D' : [int]), (y : int).
										 device (D', d) = false /\
								 		 device(D', y) = true => 
								 		 cansend(D', y, d) = false
								 };		 



goal : (d : { v : int | true}) -> 
	   (x : { v : int | true}) -> 		
	 				State {\(h: heap).true} 
								v : {v : int | true} 
		 						{\(h: heap),(v : int),(h': heap).
		 							\(D : [int]), (D' : [int]),(CS : [srpair]),(CS' : [srpair]).
									cansend (CS', d, x)
		 						};
