(*
	-在命令行中输入 use "filename.sml"; 来加载代码文件
	
	-sml 不允许赋值操作,所有数据都是immutable的
	 但可以重复定义同命变量或函数,后定义的会将之前定义的shadow掉
	 但之前定义的依然还在，不会受影响
	
	-sml中负号用~而不是－来表示
	 如：－123应写成：~123
*)

(*variable binding*)
val x = 34		(* x:int *)

val y = 17

val re = 1.234	(* re:real *)

val z = x + y + 1

(* if-else 也是表达式级别的*)
val abs_of_z = if z > 0 then z else 0-z

val simpl_abs_z = abs(z)


(*function binding*)
fun pow(x:int, y:int) = 	(* int*int -> int *)
	if y = 0
	then 1
	else x*pow(x,y-1)

fun cube(x:int) = 			(* int -> int *)
	pow(x,3)


(*前面定义的会被hidden掉*)
fun cube(x:int) = 
	x * x * x


(* pair *)
val pa = (1,2)				(* int*int *)
val pb = (3,true)			(* int*bool *)

val pa1 = #1 pa
val pa2 = #2 pa


(* tuple *)
val tpa = (1,2,true,3.4)	(* int*int*bool*real *)
val tp1 = #1 tpa
val tp2 = #2 tpa
val tp3 = #3 tpa
val tp4 = #4 tpa


(* list *)
val la = []					(* 'a list *)
val lb = [1,2,3]			(* int list *)
val lc = [true,false,true]	(* bool list *)
val ld = 2::[1,2,3]

val flag = null la  (*flag = true*)
val flag2 = null lb (*flag2 = false*)

val hlb = hd lb		(* hlb = 1 *)
val tlb = tl lb		(* tlb = [2,3] *)




(* binding in local: let expression *)
(*--------------------------------------------------*)
(*
	syntex:
	let b1 b2 b3 ... in exp end

	-let是表达式级别，可以多重嵌套
*)

val aa = let 
			val x = 1
		 in
		 	(let val x = 2 in x+1 end) + 
		 	(let val y = x + 2 in y + 1 end)
		 end



fun countup_from1 (x:int) = 
	let fun count (from:int, to:int) =
			if from = to
			then to::[]
			else from::count(from+1,to)
	in
		count(1,x)
	end



(* option type *)
(* similar in Coq *)
(*
	NONE		: a' option
	SOME 12		: int option
	SOME true	: bool option

	valOf (SOME 5)	返回5
	valOf NONE 		导致异常

	isSome NONE	: false
	isSome SOME 5 : true
*)
fun max_of_list (l:int list) =
	if l = []
	then NONE
	else let val h = hd l val t = tl l val ret = max_of_list t
		 in 
			if isSome ret
		 	then if h > valOf ret then SOME h
		 		 else ret
		 	else SOME h
		 end


(* bool expression *)
val b1 = true andalso false
val b2 = true orelse false
val b3 = not true

val b4 = (x = 55)
val b5 = 23<54 andalso 43>54
val b6 = 12<>13






