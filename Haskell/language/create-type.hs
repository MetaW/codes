{-
	content:
	1. 简单的 data type 定义
	2. deriving
	3. 在module中创建data type
	4. record
	5. 带有参数的 data type
-}



{-
	!!!caution!!!:
	module,type,constructor 首字母要大写
	varivale,function首字母必须小些
-}

data Bool = 
	  False 
	| True


-- 含参数的构造子
data Shape = 
	  Circle Float Float Float
	| Rectangle Float Float Float Float


-- 构造子的模式匹配
surface :: Shape -> Float
surface (Circle _ _ r) = pi * (r^2)
surface (Rectangle x1 y1 x2 y2) = (abs $ x1 - x2) * (abs $ y1 - y2)







-- deriving
--------------------------------------------------
{-
	上面创造出来的type不属于任何typeclass, 这会产生一些问题,
	如不属于 Show 的typeclass 就无法在 GHCi 中显示其值。

	使用 deriving 可以使其属于某个 typeclass
-}

data Point = Point Float Float deriving (Show)

data NewShape = NewCircle Point Float | NewRectangle Point Point deriving (Show)
-- 这样 Point 和 NewShape 类型的数据就能直接在ghci中显示了


-- 注意pattern match的syntax

newSurface :: NewShape -> Float
newSurface (NewCircle _ r) =  pi * (r^2)
newSurface (NewRectangle (Point x1 y1) (Point x2 y2)) = (abs $ x1 - x2) * (abs $ y1 - y2)






-- 在module中创建data type的方法
----------------------------------------------------
-- eg:
{-

module Shape
(	Point(..),		-- data type
	NewShape(..),	-- data type
	Newsurface		-- function
)where

data Point = Point Float Float deriving (Show)

data NewShape = NewCircle Point Float | NewRectangle Point Point deriving (Show)

NewSurface :: NewShape -> Float
NewSurface (NewCircle _ r) =  pi * (r^2)
NewSurface (NewRectangle (Point x1 y1) (Point x2 y2)) = (abs $ x1 - x2) * (abs $ y1 - y2)

-}








-- Record
----------------------------------------------------
{-
	若constructor的参数太多,那么模式匹配其中某一项等其它
	场合会很麻烦,record syntax 简化了这种情况。
-}
-- eg:

data Person = Person { 	firstName :: String,
						lastName :: String,
						age :: Int,
						height :: Float,
						phoneNumber :: String
					 } 	deriving (Show)


{-
	事实上 record 只是语法糖， 它相当于自动生成以下函数:

firstName :: Person -> String
firstName (Person str _ _ _ _) = str

lastName :: Person -> String
lastName (Person _ str _ _ _) = str

age :: Person -> Int
age (Person _ _ t _ _) = t

height :: Person -> Float
height (_ _ _ f _) = f

phoneNumber :: Person -> String
phoneNumber (Person _ _ _ _ str) = str

-}


-- 创建数据时与普通的data type一样
aa = Person "haha" "haha" 123 12.0 "12333"

-- 当然也可以写成下面这样：
bb = Person {firstName = "haha", lastName = "haha", age = 123, height = 12.0, phoneNumber = "12333"}





-- 带有参数的 data type
--------------------------------------------------


















