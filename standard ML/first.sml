(* comments *)

val x = 34;

val y = 17;

val z = x + y + 1;

val abs_of_z = if z > 0 then z else 0-z;

val simpl_abs_z = abs(z);

fun pow(x:int, y:int) = 
	if y = 0
	then 1
	else x*pow(x,y-1)

fun cube(x:int) = 
	pow(x,3)
