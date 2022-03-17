
get_content : (c : cell) -> 
        State {\(h : heap). 
                \(N : node).
                dom (h, c) = true /\
                llsel (h, c) = N /\ 
                cons (N) = true} 
			v : {v : a | true}  
		{\(h : heap), (v : a), (h' : heap). 
				\(N' : node).
			      llsel (h', c) = llsel (h, c) /\ 
                  v = content (N')
                  
        };

set_content : (c : cell) ->
               (data : a) -> 
        State {\(h : heap).         
                \(N : node).
                dom (h, c) = true /\
                llsel (h, c) = N /\ 
                cons (N) = true} 
				v : {v : unit | true}
		{\(h : heap), (v : unit), (h' : heap). 
				\(N' : node), (N : node).
			      llsel (h', c) = N' /\
                  llsel (h, c) = N /\
                  content (N') = data /\
                  next (N') = next (N) /\
                  cons (N') = true
        };


get_next : (c : cell) -> 
         State {\(h : heap). 
                \(N : node).
                dom (h, c) = true /\
                llsel (h, c) = N /\ 
                cons (N) = true} 
			v : {v : cell | true} 
		{\(h : heap), (v : cell), (h' : heap). 
				\(N' : node).
			      llsel (h', c) = llsel (h, c) /\ 
                  v = next (N')
        };


set_next : (c : cell) ->
            (n : cell) ->
               (data : a) -> 
        State {\(h : heap).         
                \(N : node).
                dom (h, c) = true /\
                dom (h, n) = true /\
                llsel (h, c) = N /\ 
                cons (N) = true} 
				v : {v : unit | true}
		{\(h : heap), (v : unit), (h' : heap). 
				\(N' : node), (N : node).
			      llsel (h', c) = N' /\
                  llsel (h, c) = N /\
                  next (N') = n /\
                  content (N') = content (N) /\
                  cons (N') = true
        };
