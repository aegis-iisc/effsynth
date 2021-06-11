x1 : {v : int | [v = 0]};
y1 : {v : int | [v = 2]};

length : State {\(h : heap). true} 
	int {\(h : heap), (v : int), (h' : heap). h =  h' };		

goal :  State {\(h : heap). true} 
	int {\(h : heap), (v : int), (h' : heap). h =  h' };		


