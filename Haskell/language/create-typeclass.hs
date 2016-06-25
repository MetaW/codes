{-
	content:
	1. create typeclass
	2. typeclass instance
	3. subclass
	4. 一个实例
	5. typeclass: functor
	6. :kind
-}



-- create typeclass
------------------------------------------------------
{-
	typeclsaa 就像是 interface ,一个typeclass定义了一些行为
	(像是比较相不相等, 比较大小顺序, 能否穷举)而我们会把希望满足
	这些性质的 type 定义成这些 typeclass 的 instance.

	typeclass 的行为是由定义的函数来描述,并写出对应的实现. 当我们把一
	个类型定义成某个 typeclass 的 instance 就表示我们可以对那个类型
	使用 typeclass 中定义的函数。
-}
{-
eg: Eq

class Eq a where
	(==) :: a -> a -> Bool
	(/=) :: a -> a -> Bool
	x == y = not (x /= y)
	x /= y = not (x == y)

-}




-- typeclass instance
---------------------------------------------------
----- 自动创建 typeclass 的 instance
-- 使用 deriving (typeclass ...)
-- data TrafficLight = Red | Green | Yellow deriving (Eq, Show)


----- 手动创建 typeclass 的 instance
{-
	由于使用 deriving 创建的 typeclass instance 默认实现的
	function可能不满足我们的需求，如：
	show Red 默认就是 Red, 我们要想让它显示为 Red Light，就
	需要把该类型手动创建为某 typeclass 的 instance.

	另外，自动创建的instance只能在定义时进行，这样一些已经定义的
	type就无法通过自动的方式加入新的typeclass， 而手动的可以。
-}

data TrafficLight = Red | Green | Yellow

instance Eq TrafficLight where
	(==) Red Red = True
	(==) Green Green = True
	(==) Yellow Yellow = True
	(==) _ _ = False

instance Show TrafficLight where
	show Red = "Red Light"
	show Green = "Green Light"
	show Yellow = "Yellow Light"






-- subclass
---------------------------------------------------
{-
	有时候我们在定义一个 typeclass 时需要令他的 instance
	首先满足是另一个 typeclass 的 instance (添加类型约束)。
	即该 typeclass 的 instance 是某些 typeclass 的 instance
	的子集。
-}
-- eg!!!:

-- class (Eq a) => Num a where
--		...
{-
	这就是 subclass 在做的事: 帮 Num 加上限制。也就是说当我们
	定义 Num 中的函数体,我们可以缺省 Num 的 instance: a 是属
	于 Eq 因此能使用 ==。
-}

-- 同理当 instance 是多态类型的type，手动约束它到某个typeclass的
-- instance 时要这样写：
{-}
instance (Eq m) => Eq (Maybe m) where
	(==) Just x Just y = x == y
	(==) Nothing Nothing = True
	(==) _ _ = False
-}






-- 一个实例
-------------------------------------------------------------
{-
	我们创建一个弱类型的 if 语句，它能接受很多类型作为
	条件，不仅仅是Bool类型。
	这里使用typeclass实现dispatch，当然，可以不这样做。
-}
class WeakYesNo a where
	yesno :: a -> Bool

instance WeakYesNo Int where
	yesno 0 = False
	yesno _ = True

instance WeakYesNo [a] where
	yesno [] = False
	yesno _ = True

instance WeakYesNo Bool where
	yesno True = True
	yesno False = False

instance WeakYesNo (Maybe m) where
	yesno Nothing = False
	yesno _ = True

-- 使用typeclass来定义函数: weakIf
weakIf ::(WeakYesNo a) => a -> b -> b -> b
weakIf cond trueRes elseRes = if yesno cond then trueRes else elseRes

-- example:
aa = weakIf (length [1,2,3]) "hehe" "haha"	-- aa = "hehe"
bb = weakIf [] 123 456		-- bb = 456
cc = weakIf True [] [1,2]	-- cc = []
dd = weakIf (Just "wooo") 2.11 3.22		-- dd = 2.11






-- typeclass: functor
------------------------------------------------------------
{-
	functor是一种特殊的typeclass，它只接受 * -> * 的类型作为参数，
	它用于将“盒子”中的数据从一种类型转化为另一种类型，最具代表性的是
	map函数。

	常见的"盒子"有: List, Map, Tree, Maybe, Either, IO ...
-}
-- functor 的定义

class Functor t where
	fmap :: (a -> b) -> t a -> t b


-- 使list成为Functor的instance
{-
instance Functor [] where
	fmap = map
-}


-- 使Maybe成为Functor的instance
{-
instance Functor Maybe where
	fmap f (Just x) = Just (f x)
	fmap f Nothing = Nothing
-}


-- 使Either成为Functor的instance
{-
	由于Functor要求类型的kind为 * -> * 的，而Either是 * -> * -> * 的
	所以Either无法直接加入Functor,必须实例化一个参数，如 Either a
	才能加入Functor

instance Functor (Either a) where
	fmap f (Left x) = Left (f x)
	fmap f (Right x) = Right x
-}


-- 使IO成为Functor的instance
{-
instance Functor IO where
	fmap f actions = do
		result <- actions
		return (f result)
--	If you ever find yourself binding the result of an I/O action
	to a name, only to apply a function to that and call that
	something else, consider using fmap

	eg:
	line <- getLine
	res = f line
	==>
	res = fmap f getLine
-}



-- 使 函数类型:(* -> *) 成为Functor的instance
{-
	由于形如 Int -> String 的式子也是type，因为实际上 (->) 也
	是类型构造子!!!
	a -> b 就是 (->) a b
	:k (->) == * -> * -> *

	因此与前面的 Either 类似，(->) a 也可以变为 Functor 的instance!
	just like Maybe, ((->) a) is also a "BOX"!

instance Functor ((->) a) where
	fmap f g = \x -> f (g x)

-- 事实上 fmap f g => f . g
-}



-- kind 命令
------------------------------------------------------------
{-
	value has a type, type has a kind

	:t 123					:k Int
	==> Int					==> *

	:t sqrt					:k Maybe
	==> a -> a				==> * -> *

	:t (+)					:k Map
	==> a -> a -> a			==> * -> * -> *

	:t (+3)					:k Map String
	==> a -> a				==> * -> *

	value is isomorphism with type
-}
