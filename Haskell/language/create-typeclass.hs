{-
	content:
	1. 创建typeclass
	3.
	4.
-}



-- 
------------------------------------------------------
{-
	typeclsaa 就像是 interface ,一个typeclass定义了一些行为
	(像是比较相不相等, 比较大小顺序, 能否穷举)而我们会把希望满足
	这些性质的 type 定义成这些 typeclass 的 instance.

	typeclass 的行为是由定义的函数来描述,并写出对应的实现. 当我们把一
	个类型定义成某个 typeclass 的 instance 就表示我们可以对那个类型
	使用 typeclass 中定义的函数。
-}
-- eg: Eq

class Eq a where
	(==) :: a -> a -> Bool
	(/=) :: a -> a -> Bool
	x == y = not (x /= y)
	x /= y = not (x == y)



