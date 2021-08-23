tbl : string list;

mem : ({s : string | true}) -> 
			State  {\(h : heap). true} 
			v : { v : bool | true} 
			{\(h : heap), (v : bool), (h' : heap). 
				sel (h', tbl) = tbl' /\ 
				([v==true] <=> mem tbl' s) /\ 
				[v==false] <=> not (mem tbl' s)};

fresh_str : State  {\(h : heap). true} 
			v : { v : string | true} 
			{\(h : heap), (v : string), (h' : heap). 
				len (v) = 3 /\
				sel (h', tbl) = tbl' /\ 
				not (mem tbl' s)};


add : ({s : string | true}) ->  
			State  {\(h : heap). sel (h, tbl) = tbl /\ not (mem tbl s)} 
				v : { v : unit | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				sel (h', tbl) = tbl' /\ 
				(mem tbl' s) /\ 
				len (tbl') == len (tbl) + len (s) /\ 
				size (tbl') == size (tbl) + 1};
				

remove 	: ({s : string | true}) ->  
			State  {\(h : heap). sel (h, tbl) = tbl /\ (mem tbl s)} 
				v : { v : unit | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				sel (h', tbl) = tbl' /\ 
				not (mem tbl' s) /\ 
				len (tbl') == len (tbl) - len (s) /\ 
				size (tbl') == size (tbl) - 1};

take_head : State  {\(h : heap). sel (h, tbl) = tbl /\ size (tbl) > 0} 
				v : { v : string | true} 
			{\(h : heap), (v : unit), (h' : heap). 
				sel (h, tbl) = tbl /\ 
				not (mem tbl' v) /\ 
				len (tbl') == len (tbl) - len (v) /\ 
				size (tbl') == size (tbl) - 1};



average_len : State  {\(h : heap). sel (h, tbl) = tbl /\ size (tbl) > 0} 
				v : { v : float | true} 
			 {\(h : heap), (v : float), (h' : heap). 
				sel (h', tbl) = tbl' /\ 
				 not (min (tbl') > v) /\
				 not (v > max (tbl')) /\
				 sel (h', tbl) = sel (h, tbl)};


twice_average_len : 
			State  {\(h : heap). sel (h, tbl) = tbl /\ size (tbl) > 0} 
				v : { v : float | true} 
			 {\(h : heap), (v : float), (h' : heap). 
				not (min (tbl') > v)};



sort : State  {\(h : heap). true} 
				v : { v : unit | true} 
			 {\(h : heap), (v : unit), (h' : heap). 
				sel (h, tbl) = tbl /\ 
				 sorted (tbl)};



size : Pure  {\(h : heap). true} 
				v : { v : int | true} 
			 {\(h : heap), (v : int), (h' : heap). 
				sel (h, tbl) = tbl /\ 
				 size (tbl) == v};



length : Pure  {\(h : heap). true} 
				v : { v : int | true} 
			 {\(h : heap), (v : int), (h' : heap). 
				sel (h, tbl) = tbl /\ 
				 len (tbl) == v};


(*a goal query, for synthesizing a program taking a string parameter, and an initial state,
and adds two new strings to the table. If the given s is present in the table then it adds two fresh_strings, else it adds this string and  another fresh string and returns the avg_length of the table strings 

The specification captures this scenario.
*)

goal : ({s : string | true}) -> 
	State {\(h : heap). sel h tbl = tbl0}
			v : {v : float | true}
		  {\(h : heap), (v : float), (h' : heap). 
				sel (h', tbl) = tbl' /\ 
				(* min <= avg <= max*)
				not (min (tbl') > v) /\
				not (v > max (tbl')) /\
				
				size (tbl') = size (tbl) + 2 /\
				mem (tbl', s) /\
				
				(*two conditions*)
				(not mem (tbl, s) /\ len (tbl') == len (tbl) + len (s) + 3) \/ 
				(mem (tbl, s) /\ len (tbl') == len (tbl) + 6)
				};
