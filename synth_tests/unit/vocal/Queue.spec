create : (u : unit) ->   
       	State {\(h : heap). true} 
			v : ref queue 
		{ \(h : heap), (v : ref queue), (h' : heap). 
				\(V' : queue).
			      vdom (h', v) = vdom (h, v) U {(v)} /\
                  vsel (h', v) = V' /\
                  velems (V') = empty /\
                  vlen (V') = 0
        };


add : (x : a) -> 
     (q : ref queue)  -> 
       State {\(h : heap).
                \(V1: queue). 
                        vdom (h, q) = true
                 } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1') = {(x)} U qelems (Q1) /\
                    qlen (Q1') = qlen (Q1) + 1
                };


push : (x : a) -> 
        (q : ref queue)  -> 
         State {\(h : heap).
                \(Q1: queue). 
                        vdom (h, q) = true
                 } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1') = {(x)} U qelems (Q1) /\
                    qlen (Q1') = qlen (Q1) + 1
                };


take :  (q : ref queue)  -> 
         State {\(h : heap).
                \(Q1: queue). 
                        vdom (h, q) = true /\
                        (qsel (h, q) = Q1 => 
                        qlen (Q1) > 0) 
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1) = {(v)} U qelems (Q1') /\
                    qlen (Q1') = qlen (Q1) - 1
                };

pop : (q : ref queue)  -> 
         State {\(h : heap).
                \(Q1: queue). 
                        vdom (h, q) = true /\
                        (qsel (h, q) = Q1 => 
                        qlen (Q1) > 0) 
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1) = {(v)} U qelems (Q1') /\
                    qlen (Q1') = qlen (Q1) - 1
                };
peek : (q : ref queue)  -> 
         State {\(h : heap).
                \(Q1: queue). 
                        vdom (h, q) = true /\
                        (qsel (h, q) = Q1 => 
                        qlen (Q1) > 0) 
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1) = qelems (Q1') /\
                    qlen (Q1') = qlen (Q1)
                };

top : (q : ref queue)  -> 
         State {\(h : heap).
                \(Q1: queue). 
                        dom (h, q) = true /\
                        (qsel (h, q) = Q1 => 
                        qlen (Q1) > 0) 
                 } 
			     v : { v : a | true} 
                {\(h : heap), (v : a), (h' : heap). 
				 \(Q1: queue), (Q1' : queue). 
                    qsel (h, q) = Q1 /\ 
                    qsel (h', q) = Q1' /\
                    qelems (Q1) = qelems (Q1') /\
                    qlen (Q1') = qlen (Q1)
                };


clear : (q : ref queue) ->  
            State {\(h : heap). dom (h, queue) = true } 
			 v : { v : unit | true}    
             {\(h : heap), (v : unit), (h' : heap). 
				    \(V : queue), (V' : queue).
	                qsel (h, q) = Q /\    
                    qsel (h', q) = Q' /\ 
                    qelems (Q') = empty /\
                    qlen (Q') = 0 
            };


copy : (q1 : ref queue) -> 
            State {\(h : heap).
                \(Q1: queue). 
                        dom (h, q1) = true
                 } 
			     v : { v : ref queue | true} 
                {\(h : heap), (v : ref queue), (h' : heap). 
				 \(Q1: queue), (QN : queue). 
                    qsel (h, q1) = Q1 /\ 
                    qsel (h', v) = QN /\
                    qsel (h', q1) = vsel (h, q1) /\
                    qelems (QN) = qelems (Q1) /\
                    qlen (QN) = vlen (Q1) 
                };


is_empty : (q : ref queue) ->  
                State {\(h : heap). dom (h, q) = true} 
			    v : { v : bool | true}   
                {\(h : heap), (v : bool), (h' : heap). 
				    \(Q : queue), (Q' : queue).
	                  qsel (h, vec) = Q /\
                      ([v = true] <=> qlen (Q) = 0) /\ 
                      qelems (Q) = empty /\ 
                      [h' = h]
                    };


length :  (q : ref queue) ->  
                State {\(h : heap). 
                            dom (h, q) = true} 
			    v : { v : int | true}   
                {\(h : heap), (v : int), (h' : heap). 
				    \(Q : queue).
	                  v = qlen (Q) /\
                      [h' = h]
                    };
       



transfer : (q1 : ref queue) -> 
           (q2 : ref queue) -> 
            State {\(h : heap).
                     dom (h, q1) = true /\ dom (h, q2) = true
                 } 
			     v : { v : unit | true} 
                {\(h : heap), (v : unit ), (h' : heap). 
				 \(Q1: queue), (Q2 : queue), (Q1' : queue), (Q2' : queue). 
                    qsel (h, q1) = Q1 /\ 
                    qsel (h', q1) = Q1' /\
                    qsel (h, q2) = Q2 /\
                    qsel (h', q2) = Q2' /\
                    
                    qelems (Q1') = empty /\
                    qelems (Q2') = qelems (Q1) U qelems (_Q2) /\
                    qlen (Q2') = qlen (Q1) + qlen (Q2) /\
                    qlen (Q1') = 0
                };


