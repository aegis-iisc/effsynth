vec : ref vec;
V : vec;
V' : vec;
num : ref int; 
Max : int;


create : (capacity : { v : int | (v > 0 \/ [v=0]) /\ not (Max > v)}) -> 
        (dummy : a) -> 
       	State {\(h : heap). true} 
			v : ref vec 
		{ \(h : heap), (v : ref vec), (h' : heap). 
				\(V : vec), (V' : vec).
			      vdom (h, v) = false /\
                  vdom (h', v) = vdom (h, v) U {(v)} /\
                  vsel (h', v) = V' /\
                  velems (V') = empty /\
                  vlen (V') = 0
        };

make : (dummy : a) -> 
       (n : { v : int | (v > 0 \/ [v=0]) /\ not (Max > v)}) -> 
        (x : a) ->       
            State {\(h : heap). true} 
			    v : ref vec 
		        {\(h : heap), (v : ref vec), (h' : heap). 
				    \(V : vec), (V' : vec).
	                vdom (h, v) = false /\
                    vdom (h', v) = vdom (h, v) U {(v)} /\
                    vsel (h', v) = V' /\ 
                    velems (V') = {(x)} /\
                    vlen (V') = n 
                };


init : (dummy : a ) -> 
       (n : int) ->  
       (f : (x : int) -> { v :  a| true}) -> 
        State {\(h : heap). true} 
			    v : ref vec 
		        {\(h : heap), (v : ref vec), (h' : heap). 
				    \(V : vec), (V' : vec).
	                vdom (h, v) = false /\
                     vlen (V') = n 
                };


resize : (vec : ref vec) -> 
         (n : { v : int | (v > 0 \/ [v=0]) /\ not (Max > v)}) -> 
         (x : a) ->       
         State {\(h : heap). vdom (h, vec) = true} 
			 v : { v : unit | true}    
             {\(h : heap), (v : unit), (h' : heap). 
				    \(V : vec), (V' : vec).
	                vsel (h, vec) = V /\    
                    vsel (h', vec) = V' /\ 
                    velems (V') C= velems (V) /\
                    vlen (V') = n 
                    };


clear : (vec : ref vec) ->  
            State {\(h : heap). vdom (h, vec) = true} 
			 v : { v : unit | true}    
             {\(h : heap), (v : unit), (h' : heap). 
				    \(V : vec), (V' : vec).
	                vsel (h, vec) = V /\    
                    vsel (h', vec) = V' /\ 
                    velems (V') = empty /\
                    vlen (V') = 0 
            };



is_empty : (vec : ref vec) ->  
                State {\(h : heap). vdom (h, vec) = true} 
			    v : { v : bool | true}   
                {\(h : heap), (v : bool), (h' : heap). 
				    \(V : vec), (V' : vec).
	                  vsel (h, vec) = V /\
                      ([v = true] <=> len (V) = 0) /\ 
                      velems (V) = empty /\ 
                      [h' = h]
                    };

                
length :  (vec : ref vec) ->  
                State {\(h : heap). vdom (h, vec) = true} 
			    v : { v : int | true}   
                {\(h : heap), (v : int), (h' : heap). 
				    \(V : vec).
	                  v = vlen (V) /\
                      [h' = h]
                    };
       



get : (vec : ref vec) -> 
        (n : int) ->  
           State {\(h : heap).
                        \(V: vec). 
                        vdom (h, vec) = true /\ 
                        (vsel (h, vec) = V => 
                        vlen (V) > n)
                } 
			    v : { v : a | true}   
                {\(h : heap), (v : a), (h' : heap). 
				    \(V : vec).
	                sel (h, vec) = V /\
                    {(v)} C= elems (V)
                    /\ [h' = h]
                };



set : (vec : ref vec) -> 
        (n : int) ->  
        (x: a) -> 
           State {\(h : heap).
                        \(V: vec). 
                        vdom (h, vec) = true /\ 
                        (vsel (h, vec) = V => 
                        vlen (V) > n)
                } 
			    v : { v : unit | true}   
                {\(h : heap), (v : unit), (h' : heap). 
				    \(V : vec), (V' : vec).
	                sel (h, vec) = V /\
                    sel (h', vec) = V' /\
                    {(x)} C= elems (V')
                };


sub : (vec : ref vec) -> 
     (offset : int) ->  
     (n : int) -> 
        State {\(h : heap).
                \(V: vec). 
                        vdom (h, vec) = true /\ 
                        (vsel (h, vec) = V => 
                        vlen (V) > n /\ 
                        vlen (V) > offset + n )
                } 
			     v : ref vec  
                {\(h : heap), (v : ref vec), (h' : heap). 
				    \(NV : vec).
	                sel (h, vec) = V /\
                    sel (h', v) = NV /\
                    vdom (h', v) = true /\
                    sel (h, vec) = sel (h', vec) /\
                    elems (NV) C= elems (V) /\
                    len (V) > len (NV) 
                };



fill : (vec : ref vec) -> 
     (offset : int) ->  
     (n : int) -> 
     (x : a )  ->   
        State {\(h : heap).
                \(V: vec). 
                        vdom (h, vec) = true /\ 
                        (vsel (h, vec) = V => 
                        vlen (V) > n /\ 
                        vlen (V) > offset + n )
                } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				    \(V : vec), (V' : vec).
	                sel (h, vec) = V /\
                    sel (h', vec) = V' /\
                    elems (V') C= elems (V) /\  
                    {(x)} C= elems (V') /\
                    len (V') = len (V) 
                };

blit : (a1 : ref vec) -> 
       (ofs1 : int) ->  
       (a2 : ref vec) -> 
       (ofs2 : int) ->  
       (n : int) -> 
       State {\(h : heap).
                \(V1: vec), (V2 : vec). 
                        vdom (h, a1) = true /\ 
                        vdom (h, a2) =  true/\
                        ((vsel (h, a1) = V1 /\ vsel (h, a2) = V2) => 
                         (vlen (V1) > ofs1 + n /\
                         vlen (V2) > ofs2 + n ))
                } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				 \(V1: vec), (V2 : vec), (V1': vec), (v2' : vec). 
                    vsel (h, a2) = V2 /\ 
                    vsel (h', a2) = V2' /\
                    vsel (h', a1) = vsel (h, a1) /\
                    len (V2') = len (V2) 
                };



append : (a1 : ref vec) -> 
         (a2 : ref vec) -> 

          State {\(h : heap).
                \(V1: vec), (V2 : vec). 
                        vdom (h, a1) = true /\ 
                        vdom (h, a2) =  true/\
                        ((vsel (h, a1) = V1 /\ vsel (h, a2) = V2) => 
                         Max > (vlen (V1) + vlen (V2)))
                 } 
			     v : { v : ref vec | true} 
                {\(h : heap), (v : ref vec), (h' : heap). 
				 \(V1: vec), (V2 : vec), (VN : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, a2) = V2 /\
                    vsel (h', v) = VN /\
                    dom (h', v) = true /\
                    vsel (h', a1) = vsel (h, a1) /\
                    vsel (h', a2) = vsel (h, a2) /\
                    len (VN) = len (V1) + len (V2)
                };



merge_right : (a1 : ref vec) -> 
         (a2 : ref vec) -> 

          State {\(h : heap).
                \(V1: vec), (V2 : vec). 
                        vdom (h, a1) = true /\ 
                        vdom (h, a2) =  true/\
                        ((vsel (h, a1) = V1 /\ vsel (h, a2) = V2) => 
                         Max > (vlen (V1) + vlen (V2)) /\
                         disjoint (V1, V2) = true)
                 } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				 \(V1: vec), (V2 : vec), (V2' : vec), (V1' : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, a2) = V2 /\
                    vsel (h', a1) = V1' /\
                    vsel (h', a2) = V2' /\
                    elems (V2') = empty /\
                    vlen (V2') = 0 /\
                    elems (V1') = elems (V1) U elems (V2) /\
                    len (V1') = len (V1) + len (V2) /\
                    disjoint (V1', V2') = true
                };



map :  (dummy : b) -> 
       (a1 : ref vec) ->  
       (f : (x : a) -> { v :  b| true}) ->
          State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true} 
			     v : { v : ref vec | true} 
                {\(h : heap), (v : ref vec), (h' : heap). 
				 \(V1: vec), (VN : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, v) = VN /\
                    len (VN) = len (V1) /\
                    vsel (h', a1) = vsel (h, a1)
                };




mapi :  (dummy : b) -> 
       (a1 : ref vec) ->  
       (f : (i : int) -> (x : a) -> { v :  b| true}) ->
          State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true} 
			     v : { v : ref vec | true} 
                {\(h : heap), (v : ref vec), (h' : heap). 
				 \(V1: vec), (VN : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, v) = VN /\
                    len (VN) = len (V1) /\
                    vsel (h', a1) = vsel (h, a1)
                };




copy : (a1 : ref vec) -> 
            State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true
                 } 
			     v : { v : ref vec | true} 
                {\(h : heap), (v : ref vec), (h' : heap). 
				 \(V1: vec), (VN : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, v) = VN /\
                    vsel (h', a1) = vsel (h, a1) /\
                    velems (VN) = velems (V1) /\
                    vlen (VN) = vlen (V1) 
                };


fold_left : (a1 : ref vec)  -> 
        (f :  (l : a) -> (r : b)  -> {v : a | true}) -> 
        ( l0 : a) -> 
        {v : a | true};

        


fold_right : (a1 : ref vec)  -> 
        (f :  (l : b) -> (r : a)  -> {v : a | true}) -> 
        (l0 : a) -> 
        {v : a | true};



push : (a1 : ref vec)  -> 
       (x : a) -> 
       State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true
                 } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				 \(V1: vec), (V1' : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h', a1) = V1' /\
                    velems (V1') = {(x)} U velems (V1) /\
                    vlen (V1') = vlen (V1) + 1
                };



pop : (a1 : ref vec)  -> 
       State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(V1: vec), (V1' : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h', a1) = V1' /\
                    {(x)} C= velems (V1) /\
                    vlen (V1') = vlen (V1) - 1
                };


top: (a1 : ref vec)  -> 
       State {\(h : heap).
                \(V1: vec). 
                        vdom (h, a1) = true
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(V1: vec), (V1' : vec). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h', a1) = V1' /\
                    {(x)} C= velems (V1) /\
                    vlen (V1') = vlen (V1) - 1
                };
