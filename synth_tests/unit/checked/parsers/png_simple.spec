len : ref int;


type pngpair = Pair of int * [char];
type pngtriple = Triple of {len : int; ts : [char] ; data : [char]}; 


createTriple  :  (x : { v : int | true}) ->  
				 (y : { v : [char] | true}) -> 
				 (z : {v : [char] | true}) -> 
				 	{v : pngtriple | length (z) + length (y) == x}; 	

getFuel : (u :{ v : unit | true})  -> 
				State {\(h : heap).true} 
				v : { v : int | true} 
				{\(h: heap),(v : int),(h': heap).
					sel (h', len) == sel (h, len) /\
					sel (h', len) == v};


putFuel : (x : { v : int | true})-> 
			State {\(h : heap).
				true} 
				v : { v : unit | true} 
				{\(h: heap),(v : unit),(h': heap).
					sel (h', len) == x};


natural : State {\(h : heap).
				true} 
				v : { v : [char] | true} 
			  	{\(h: heap),(v : [char]),(h': heap).
					sel (h', len) == sel (h, len) /\
					asciinumber (v) = true)};



uppercase  : State {\(h : heap).
				true} 
				v : { v : [char] | true} 
			  	{\(h: heap),(v : [char]),(h': heap).
					\(e : char), (cc : int).
					sel (h', len) = sel (h, len) /\
					asciiupper (cc) = true)};


alphanum : State {\(h : heap).
				true} 
				v : { v : [char] | true} 
			  	{\(h: heap),(v : [char]),(h': heap).
					\(e : char), (cc : int).
					sel (h', len) = sel (h, len) /\
					asciialphanum (cc) = true)};

length : State {\(h : heap).
				sel (h, len) = 0} 
				v : { v : int | true} 
			  	{\(h: heap),(v : int),(h': heap).
					sel (h', len) == v /\
                    [v > 4] };



typespec : State {\(h : heap).
				sel (h, len) > 4} 
				v : { v : [char] | true} 
			  	{\(h: heap),(v : [char]),(h': heap).
					sel (h', len) == sel (h, len) - 4
					/\ sel (h', len) > 0};



content : State {\(h : heap).
				sel (h, len) > 0} 
				v : { v : [char] | true} 
			  	{\(h: heap),(v : [char]),(h': heap).
					sel (h', len) == sel (h, len) -- length (v)
					/\ sel (h', len) == 0};


(*Generates a parser x<- len () ; y <- typespec (); z <- content () ; return Triple (x, y, z)*)
goal : State {\(h : heap).
				sel (h, len) == 0} 
				v : { v : pngtriple | true}
				{\(h: heap),(v : pngtriple),(h': heap).
				 \(X : int), (Y:[char]), (Z:[char]).
				  (pnglen (v) = X /\
				  pngts (v) = Y /\
				  pngdata (v) = Z) => 	(
					  		sel (h', len) == 0 /\
				  			length (X) = length (Z) + length (Y)
						  )};
