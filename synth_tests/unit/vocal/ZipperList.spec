

empty : (u :  unit) -> 
        { v : ziplist | zelems (v) = empty /\ zlen (v) = 0};



is_empty : (z : ziplist)  -> 
    {v : bool |   [b = true] <=> zelems (z) = empty};

length : (z : ziplist)  -> 
    {v : int |   v = zlen (z) };



to_list : (z : ziplist) -> {v : [a] |  len (v)  = zlen (z) /\ elems (v) = zelems (z) }; 




make : (l : [a]) -> {v : ziplist | zlen (v) = len (v) /\ zelems (v) = elems (l)};

move_left : (z1 : ziplist) -> 
            {v : ziplist | zlen (v) = zlen (z1) /\ 
                zelems (v) = zelems (z1)};


insert_left : (x : a) -> 
              (z1 : ziplist) -> 
              {v : ziplist | zlen (v) = zlen (z1) + 1/\ 
                zelems (v) = {(x)} U zelems (z1)};



val remove_left : 'a t -> 'a t
(*@ r = remove_left z
    requires 0 < z.idx
    ensures  r.seq = z.seq[.. z.idx - 1] ++ z.seq[z.idx ..]
    ensures  r.idx = z.idx - 1*)

