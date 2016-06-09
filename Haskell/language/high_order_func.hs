{-
	内容:
	1. curried function
	2. high order function
	3. map, filter
	4. foldl, foldr
	5. scanl, scanr
	6. $运算符 (syntax suger)
	7. function composition (syntax suger)

-}

-------------------------------------------------------------
-------------------------------------------------------------
{-
    haskell中的函数可以作为参数和返回值传来传去,这样的
    函数就被称作高阶函数.
    本质上的所有函数都只有一个参数，所有多个参数的函数都是
    curried function 

	多参函数都可以只传入一部分参数来调用，返回的不是一个具体值
	而是另一个函数，它的参数为剩下还未传入值的参数。
-}

--eg:
biggest :: (Num a, Ord a) => a -> a -> a ->a
biggest x y z
	| x>y&&x>z = x
	| y>z = y
	| otherwise = z


biggestWith100 :: (Num a, Ord a) => (a -> a -> a)
biggestWith100 = biggest 100
--这样就很简单的得到了另一个函数,它是biggest已经传入一个100后的
--剩余的函数,且这个新函数也不用写任何参数,就自动有两个参数。


--刚才说本质上的所有函数都只有一个参数,多个参数都是柯里化的结果
--eg:
aa = ((biggest 10) 20) 30
--等价于
bb = biggest 10 20 30




--高阶函数
-----------------------------------------------------
--高阶函数即可以把函数作为参数或返回函数的函数
--eg:
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)
--该函数接受一个函数和一个数据作为参数
{-
	如果有个函数要我们给它传个一元函数,大可以
	不全调用一个函数让它剩一个参数,再把它交出去
-}
cc = applyTwice (+10) 2		--cc=22
dd = applyTwice (2:) []		--dd=[2,2]
ee = applyTwice ("haha " ++) "wll" 	--ee="haha haha wll"


--eg2:
myZipWith :: (t -> t2 -> t1) -> [t] -> [t2] -> [t1]
myZipWith _ [] _ = []
myZipWith _ _ [] = []
myZipWith f (x:xl) (y:yl) = (f x y):myZipWith f xl yl
{-
	若在使用高阶函数的时候不清楚其类型为何,就先忽略掉它的类型声明
	再到ghci下用:t命令来看下haskell的类型推导 
-}

ff = myZipWith (+) [1,2,3] [4,5,6]		--ff=[5,7,9]
gg = myZipWith (*) [1,2,3,4,5] [10,10]  --gg=[10,20]





--map,filter
-----------------------------------------------------
--map传入一个一元函数和一个list,对list中每一个元素调用该一元函数
--并返回得到的新list
--map的实现
mymap :: (a -> b) -> [a] -> [b]
mymap _ [] = []
mymap f (x:xl) = (f x):map f xl

hh = mymap (+5) [1,2,3,4]		--hh=[6,7,8,9]
--事实上用list comprehension可以达到和map一样的效果


--filter传入一个一元函数和一个list,对list中每一个元素调用该一元函数,
--该函数返回bool值，返回的新list只包含满足该函数的元素
--filter的实现
myfilter :: (a -> Bool) -> [a] -> [a]
myfilter _ [] = []
myfilter f (x:xl)
	| (f x)     = x:myfilter f xl
	| otherwise = myfilter f xl


ii = myfilter (>5) [1,2,3,4,5,6,7,8]	--ii=[6,7,8]
--事实上用list comprehension也可以达到和filter一样的效果

--重写qst
qst :: Ord a => [a] -> [a]
qst [] = []
qst (x:xl) = qst (filter (<=x) xl) ++ x:qst (filter (>x) xl)






--惰性求值与无穷list
----------------------------------------------------
{-
	haskell是惰性求值的语言
	因此可以使用无穷list(无穷流)
-}


--匿名函数lambda
----------------------------------------------------
{-
	syntex:
	(\ x -> x * 2)
	(\ x y -> x + y)
	(\ l -> length l > 10)

-}

kk = filter (\x -> x > 5) [2,3,5,7,90,23,4,1]	-- kk = [7,90,23]

--example
addThree :: (Num a) => a -> a -> a -> a
addThree = \x -> \y -> \z -> x + y + z





--foldl,foldr
--------------------------------------------------
{-
	foldl f e [a,b,c]
	==> (f(f(f e a) b) c)

	foldr f e [a,b,c]
	==> (f a (f b (f c e)))

	所有遍历 list 中元素并据此返回一个值的操作都可以交给 fold 实现
-}


isAllPosit::(Ord a, Num a) =>[a] -> Bool
isAllPosit l = foldl (\acc x -> acc&&(x>0)) True l


mySum :: (Num a) => [a] -> a
mySum = foldl (+) 0


myElem :: Eq a => a -> [a] -> Bool
myElem e l = foldl (\acc x -> acc||(x == e)) False l


myMap2 :: (a -> a1) -> [a] -> [a1]
myMap2 f l = foldr (\x acc -> f x:acc) [] l


myReverse :: [a] -> [a]
myReverse = foldl (\acc x -> x:acc) []


--foldl1 与 foldr1 的行为与 foldl 和 foldr 相似
--只是你无需明确提供初始值。他们假定 list 的首个或末尾元素作为起始值






--scanl, scanr
--------------------------------------------------
{-
	scanl 和 scanr 与 foldl 和 foldr 相似,只是它们会记
	录下累加值的所有状态到一个 list。也有 scanl1 和 scanr1。
-}

mm = scanl (+) 0 [1,2,3,4]	-- mm = [0,1,3,6,10]

nn = scanr (+) 0 [1,2,3,4]	-- nn = [10,9,7,4,0]

oo = scanl1 (+) [1,2,3,4]	-- oo = [1,3,6,10]

pp = scanr1 (+) [1,2,3,4]	-- pp = [10,9,7,4]





-- $ 运算符
-------------------------------------------------
{-
	作用：f $ x = f x

	普通的函数调用是左结合的，拥有最高优先级：
	f a b c = (((f a) b) c)

	$ 是中缀运算符，是右结合的，且拥有最低优先级

	用处:语法糖
	$可以改变求值顺序,减少括号数量
	(f (g (p x))) = f $ g $ p x

	eg: sqrt 3 + 4 + 5 = (sqrt 3) + 4 + 5
		sqrt $ 3 + 4 + 5 = sqrt (3 + 4 + 5)
-}

--实现
($) :: (a -> b) -> a -> b
f $ x = f x




-- function composition
{-
	f (g x) = (f . g) x

	. 是右结合的

	f (g (p x)) = (f . g . p) x

	用处:语法糖
	可以用 f . g . p 代替 \x -> f (g (p x))
-}

--实现
(.) :: (b -> c) -> (a -> b) -> a -> c
f . g = \x -> f (g x)

{-
example:

fn x = ceiling (negate (tan (cos (max 50 x))))
==>
fn = ceiling . negate . tan . cos . max 50

-}





