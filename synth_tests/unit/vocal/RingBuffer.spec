create: (capacity : { v : int | (v > 0 \/ [v=0]) /\ not (Max > v)}) -> 
        (dummy : a) -> 
       	State {\(h : heap). true} 
			v : ref buffer 
		{ \(h : heap), (v : ref buffer), (h' : heap). 
				\(V : buffer), (V' : buffer).
			      vdom (h, v) = false /\
                  vdom (h', v) = vdom (h, v) U {(v)} /\
                  rsel (h', v) = V' /\
                  relems (V') = empty /\
                  rlen (V') = 0
        };



length :  (vec : ref buffer) ->  
                State {\(h : heap). vdom (h, vec) = true} 
			    v : { v : int | true}   
                {\(h : heap), (v : int), (h' : heap). 
				    \(V : buffer).
	                  v = rlen (V) /\
                      [h' = h]
                    };
       



clear : (vec : ref buffer) ->  
            State {\(h : heap). vdom (h, vec) = true} 
			 v : { v : unit | true}    
             {\(h : heap), (v : unit), (h' : heap). 
				    \(V : buffer), (V' : buffer).
	                rsel (h, vec) = V /\    
                    rsel (h', vec) = V' /\ 
                    relems (V') = empty /\
                    rlen (V') = 0 
            };


pop : (a1 : ref buffer)  -> 
       State {\(h : heap).
                \(V1: buffer). 
                        vdom (h, a1) = true
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(V1: buffer), (V1' : buffer). 
                    rsel (h, a1) = V1 /\ 
                    rsel (h', a1) = V1' /\
                    {(x)} C= relems (V1) /\
                    rlen (V1') = rlen (V1) - 1
                };



get : (vec : ref buffer) -> 
        (n : int) ->  
           State {\(h : heap).
                        \(V: buffer). 
                        vdom (h, vec) = true /\ 
                        (vsel (h, vec) = V => 
                        vlen (V) > n)
                } 
			    v : { v : a | true}   
                {\(h : heap), (v : a), (h' : heap). 
				    \(V : buffer).
	                sel (h, vec) = V /\
                    {(v)} C= elems (V)
                    /\ [h' = h]
                };


copy : (a1 : ref buffer) -> 
            State {\(h : heap).
                \(V1: buffer). 
                        vdom (h, a1) = true
                 } 
			     v : { v : ref buffer | true} 
                {\(h : heap), (v : ref buffer), (h' : heap). 
				 \(V1: buffer), (VN : buffer). 
                    vsel (h, a1) = V1 /\ 
                    vsel (h, v) = VN /\
                    vsel (h', a1) = vsel (h, a1) /\
                    velems (VN) = velems (V1) /\
                    vlen (VN) = vlen (V1) 
                };
