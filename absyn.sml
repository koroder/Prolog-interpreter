signature ABSYN =
	sig
	datatype tree =  Null
	                |Leaf of string
	                |Node of (string)*(tree list)
	                 			 
  	end

structure Absyn :> ABSYN =
	struct
	datatype tree =  Null
	                |Leaf of string
	                |Node of (string)*(tree list)			 
  	end;
