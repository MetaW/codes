{-
	content:
	1. create typeclass
	2. typeclass instance
	3. subclass
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
-- eg:
-- class (Eq a) => Num a where
--		...
{-
	这就是 subclass 在做的事: 帮 Num 加上限制。也就是说当我们
	定义 Num 中的函数体,我们可以缺省 Num 的 instance: a 是属
	于 Eq 因此能使用 ==。
-}


-- 当 instance 是多态类型的type，手动约束它到某个typeclass的
-- instance 时要这样写：
{-}
instance Eq (Maybe m) where
	(==) Just x Just y = x == y
	(==) Nothing Nothing = True
	(==) _ _ = False
-}

 
