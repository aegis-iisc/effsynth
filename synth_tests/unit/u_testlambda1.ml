res : int;


bar : State  {\(h : heap). sel (h, res) == 5} 
		v : { v : int | true} 
	{\(h : heap), (v : int), (h' : heap). 
		sel (h', res) == sel (h, res) + 2};


foo : State  {\(h : heap). (sel (h, res) == 0)} 
	v : { v : int |  [v=5]} 
	{\(h : heap), (v : int), (h' : heap).  sel (h', res) == v /\ [v=5]};


foo' : (ls : { v : list | len (v) == 0}) -> 
	
	State  {\(h : heap). not (sel (h, res) > 20)} 
	v : { v : int |  [v=20]} 
	{\(h : heap), (v : int), (h' : heap). sel (h', res) == v /\ [v=10]};



goal : (ls : list) -> 
	State  
        {\(h : heap). sel( h, res) = 0 } 
	v : { v : int | true} 
	{\(h : heap), (v : int), (h' : heap). 
		sel (h', res) == 10 
		};

		

goal ls = 
	[] -> 	(*pre /\ len ls = 0*)
		foo' ls
	| x :: xs -> 
		(*pre /\ len ls = 1 + len (xs)*) 
			x1 <- foo;
			x2 <- bar;
			x4 <- baz;  
			return x4
