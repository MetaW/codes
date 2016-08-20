{-
	content:
	1. typeclass
	2. pattern match
	3. guard
	4. let-in
	5. case...of...
	6. 特殊的函数:操作符
-}
--------------------------------------------------------
--------------------------------------------------------



--函数的typeclass
{-
	函数声明时一般要先声明类型，但如果Haskell能够根据函数中
	所使用的运算等推出typeclass则可以不写
	eg:
	myadd x y = x + y
	其类型就能推断为：myadd :: Num a => a -> a -> a

	可以手动指明typeclass与type
	也可以只写type不写typeclass
	eg:
	myadd :: Integral a => a -> a -> a
	myadd x y = x + y
	这样myadd就只能传入整数,而无法再处理小数了
-}
myadd :: Integral a => a -> a -> a
myadd x y = x + y








--pattern match
--------------------------------------------------------
--------------------------------------------------------

{-
	模式匹配通过检查数据的特定结构来检查其是否匹配,
	并按模式从中取得数据
	在定义函数时,可以为不同的模式分别定义函数本身,
	这就让源代码 更加简洁易读
	可以匹配一切数据类型:数字,字符,list,元组,等等
-}

--用法:eg
sayNumber :: Integral a => a -> [Char]
sayNumber 1 = "It is one!"
sayNumber 2 = "It is Two!"
sayNumber 3 = "It is Three!"
sayNumber 4 = "It is Four!"
sayNumber x = "Oh! It's too big for me!"
--模式匹配省去了好多if－else的复杂语句
--类似于c中的switch－case，传入的参数会从上往下依次检查是否匹配
--若匹配则返回函数值，并完成函数调用，不会再往下找
--最后一个是通用的情况，可以匹配任何值

--用模式匹配很自然的实现递归,像归纳定义一样
fact :: Integral a => a -> a
fact 0 = 1
fact n = n * fact (n-1)

--模式匹配要全面,即能匹配所有的情况,否则无法匹配时会发生崩溃
--eg:
toStr :: Char -> [Char]
toStr 'a' = "apple"
toStr 'b' = "banana"
toStr 'c' = "candy"
--当输入如'd'时就会崩溃


--要写成这样：
toStr2 :: Char -> [Char]
toStr2 'a' = "apple"
toStr2 'b' = "banana"
toStr2 'c' = "candy"
toStr2 x = "any"







--更丰富的pattern match
-------------------------------------------------------
--匹配tuple

addVect :: Num a => (a,a) -> (a,a) -> (a,a)
addVect x y = (fst x + fst y, snd x + snd y)
--上面的写法太麻烦

--可以这样写
addVect2 :: Num a => (a,a) -> (a,a) -> (a,a)
addVect2 (x1,y1) (x2,y2) = (x1+x2, y1+y2)

--匿名变量
{-
	haskell中有很多情况需要一个变量但后面根本用不到他
	这时可以使用匿名变量"_"来代替实际变量
-}
--例子:为三元组定义查询函数

first :: (a,b,c) -> a
first (x,_,_) = x

second :: (a,b,c) -> b
second (_,x,_) = x

third :: (a,b,c) -> c
third (_,_,x) = x








--对list的模式匹配
-----------------------------------------------------------
--list comprehension中"<-"的匹配(本质上还是对tuple的匹配)
aa = [a+b|(a,b)<-[(1,2),(4,21),(12,4),(9,5)]]

--直接对list的匹配
--一般把list"[1,2,3,4]"看成"1:2:3:4:[]"的形式,后者是本质，前者是语法糖
--匹配时除了空list直接用[]匹配，其他list一般用(x:x:x:[])或(x:x:x:x)的形式
--来匹配，前者匹配list中所有的元素，后者中最后的"x"可以匹配剩余的任意个元素
----注意: 放在前面的变量只匹配一个元素，最后一个变量匹配剩余的所有的元素
----	 因此除非最后用了":[]"否则最后一个变量的类型为list!!!,
--eg:
sayList :: Show a => [a] -> [Char]
sayList [] = "oh! the list is empty!"
sayList (x:[]) = "the list has one elem:" ++ (show x)
sayList (_:y:[]) = "the list has two elem:" ++ (show y) ++ "," ++ (show y)
sayList (x:y:_) = "oh! the list is too long for me!"

myLength :: Num b => [a] -> b
myLength [] = 0
myLength (_:x) = 1 + myLength x

--一个方便的关键字"as"
myAnaly :: [Char] -> [Char]
myAnaly [] = "the list is empty!"
myAnaly all@(x:_) = "the first elem of " ++ all ++ " is " ++ "x"
--可以看出as可以保留匹配前的数据，这样在后面用到它时不用再用x:x:...一个个拼接了
--在较大的匹配中比较有用









--guard
--------------------------------------------------------
--------------------------------------------------------
{-
	前面的模式匹配简化了函数中有多个if-else语句时的情况
	然而模式匹配并不能处理一些依据bool值的多分枝情况，
	比如对输入值的范围作判断，不同的范围处理方式不同，此时匹配就无法使用了
	这时可以用guard来简化一大堆if-else 的情况。
-}

myHeight :: RealFloat a => a -> [Char]
myHeight x
	| x < 160 = "haha, you are too short!"
	| x < 170 = "you are not tall at all!"
	| x < 180 = "well!!!"
	| x < 190 = "you are too tall!"
	| otherwise = "Are you humanbeings?"
--使用guard时也是从上倒下一次检测是否满足，满足就返回对应值然后退出
--最后一个otherwise满足所有情况

--另一个例子
myMax :: Ord a => a -> a -> a
myMax x y
	| x > y = x
	| otherwise = y









--where语句
----------------------------------------------------------
--在guard中如果判断条件是一个依赖于参数的复杂的表达式
--那么在每个情况下都要重复写这个表达式，这很麻烦，可以在函数最后用where
--语句定义一些变量，并在前面使用它们
--eg:

sayArea :: RealFloat a => a -> [Char]
sayArea r
	| area <= small = "the cycle is small"
	| area <= middle = "the cycle is middle"
	| area <= big = "the cycle is big"
	| otherwise = "the cycle is huge!"
	where area = 3.14*r*r
	      small = 10
	      middle = 20
	      big = 30

{-
	注意：这里where后面有多个变量，多个变量一定要位于同一列，而且每一个变量
	前面的空白部分的空白符要保持一致，例如前面的area之前由一个tab和6个字符
	组成(空格也视为字符)，那么small，middle，big前面都要由一个tab和6个
	字符，不能用tab代替空格，也不能用空格代替tab，否则就会有parse error!

	!!!但可以用匹配方便的避免上述麻烦的情况：
	eg:
	where (area:small:middle:big:[]) = [3.14*r*r,10,20,30]
-}

--  !!!注意where中还可以定义局部函数，其方法与定义变量相似，就不再举例








--let...in...
----------------------------------------------------------
----------------------------------------------------------
{-
	let...in...与where的作用类似也是定义局部变量或函数，这里在let与in
	之间定义局部量，在in之后使用。
	！！！但let-in与where有很大的不同，let-in是表达式，而where是语法结构
	这就表示let-in可以放在任何地方，像使用加法一样使用let-in，
	而where只能放在函数定义的最后
	表达式就是值，可以想数值那样使用它！！！
	!!!在Haskell中if－else居然也是表达式，看看下面的例子：

	--但let-in也有缺点，由于它是表达式，所以不能像where那样在多个guard中使用
-}
--if-else
bb = [if 2>3 then "hehe" else "haha", "hello", "world"]
	--bb=["haha","hello","world"]

cc = 2*(if 23<=34 then 5 else 6)	--cc=10

--而let-in一样可以这样用
--eg:
dd = [2, (let a = 3 in a*5), 10]		--dd=[2,15,10]
ee = 2 + (let cube x = x * x in cube 10)	--ee = 102


myAddSqre x y = let sqre x = x * x in
	(sqre x) + (sqre y)









--case...of...
--------------------------------------------------------
--------------------------------------------------------
{-
	case...of...与前面的函数模式匹配类似，其实后者只是case...of...
	的语法糖。但case...of...是表达式，所以用处更广泛！！！
	case...of...的用法为：
	case expression of 	pattern -> result
						pattern -> result
						pattern -> result

	!!!与where类似，每个pattern前的空白符结构要一致，否则会有语法错误。
-}
--eg:
ff = [12,45,case (2,24,13) of (1,_,_) -> 111
                              (2,_,_) -> 222
                              (3,_,_) -> 333
                              (_,_,_) -> 000]


sayList2 :: Show a => [a] -> [Char]
sayList2 x = case x of [] -> "oh! the list is empty!"
                       (x:[]) -> "the list has one elem:" ++ (show x)
                       (_:y:[]) -> "the list has two elem:" ++ (show y) ++ "," ++ (show y)
                       (x:y:_) -> "oh! the list is too long for me!"

--这与前面的sayList效果一样








-- 操作符
---------------------------------------------------------
{-
	haskell 支持像定义函数那样定义操作符：

infixr 5 +++

(+++) :: [a] -> [a] -> [a]
(+++) [] y = y
(+++) (x:xl) y = x:(xl ++ y)

-- 操作符左右结合，优先级的指定:
infixr 优先级 操作符
infixl 优先级 操作符


    中缀操作符变前缀加():
    (1 + 2) == (+) 1 2


    前缀操作符变中缀加``:
    eg: add x y = x + y

    add 3 5 = 3 `add` 5

-}
