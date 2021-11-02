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




is_device : (d : { v : int | true}) -> State {
										\(h : heap).true}
										v : {v : bool | true}
										{\(h: heap),(v : unit),(h': heap).
											\(D : [did]), (D' : [did]).
										[v = true] <=> device (D, d) = true /\ 
										[v = false] <=> device (D, d) = false
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


(*add this device and make the device central if not present,
if present, make the device central.
requires a check that the device is present and if it is not requires removing the central device*)
goal : (d : { v : int | true}) -> 
	   			State {\(h: heap).			
	   						\(D : [int]), (CS : [srpair]) .
								dsize (D) > 0} 
								v : {v : int | true} 
		 						{\(h: heap),(v : int),(h': heap).
		 							\(D : [int]), (D' : [int]),(CS : [srpair]),(CS' : [srpair]).
									device (D', d) = true 
									central (CS', d) = true
		 						};
