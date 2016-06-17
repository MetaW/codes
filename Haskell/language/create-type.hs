import qualified Data.Map as Map

{-
	content:
	1. 简单的 data type 定义
	2. deriving
	3. 在module中创建data type
	4. record
	5. 带有参数的 data type
	6. typeclass 的作用
	7. Maybe, Either
	8. 

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
{-
	polymorphic data type
-}

data Maybe a = Nothing | Just a deriving (Show)
-- Haskell 具有自动类型推导的能力，因此 Just 'a' 类型为 Maybe Char
 

{-
	Haskell 不支持在 data 声明中加类型约束，因为没有必要，
	免得在函数声明时写过多不必要的类型约束。

	由于类型约束都是为了满足某些函数的要求，因此约束只需写在
	对于函数的定义处即可，如果写在 data 的声明处，那么与它
	相关的函数都要写这些类型约束，这显然是不必要的。
-}


data Vector a = Vector a a a deriving (Show)

-- 在函数上加类型约束
vplus :: (Num a) => Vector a -> Vector a -> Vector a
vplus (Vector a1 a2 a3) (Vector b1 b2 b3) = Vector (a1 + b1) (a2 + b2) (a3 + b3)

vectmult :: (Num a) => Vector a -> Vector a -> Vector a
vectmult (Vector a1 a2 a3) (Vector b1 b2 b3) = Vector (a1 * b1) (a2 * b2) (a3 * b3)


{-
	注意区分类型构造子 vector t 和值构造子 Vector t t t
	声明函数时必须用类型构造子声明,而不能用值构造子。
-}









-- typeclass 的作用
---------------------------------------------------
{-
	haskell 中的 typeclass 类似于java中的 interface
	它规定并实现了一些行为(函数)，例如：
	Eq: 能够进行 == 或 /= 操作
	Show: 实现了 show 函数，能够将数据转成字符串
	Read: 实现了 read 函数，能够将字符串转为某个类型的数据
	Ord: 实现了 compare 函数，能够判断数据类型的优先级
	...
	
	若一个type是某个typeclass的一员,则称该type为该
	typeclass 的instance
-}
-- eg:

data Day = Monday | Tuesday | Wednsday | Thursday | Friday | Saturday | Sunday
			deriving (Eq, Ord, Show, Read, Bounded, Enum)








-- 为type起别名
--------------------------------------------------
-- eg:
type MyString = [Char]

-- 使用别名是为了让类型声明更加易读
-- eg:

type Name = String
type Phone = Int
type Address = String


-- 类型别名也是可以有参数的
type AssocList k v = [(k,v)]


-- 我们可以用不全调用来得到新的函数,
-- 同样也可以使用不全调用得到新的类型构造子

type IntMap v = Map.Map Int v
{-- or
type IntMap = Map Int
-}






-- Maybe, Either
-------------------------------------------------
{-
	Maybe 是最常见的表示可能失败的计算的类型了。但有时 Maybe 
	也并不是十分的好用,因为 Nothing 中包含的信息还是太少。
	要是我们不关心函数失败的原因,它还是不错的。
	Either 可以更好的显示错误信息，错误一律用 Left 值构造子, 
	而结果一律用 Right
-}

data Either a b = Left a | Right b deriving (Eq, Ord, Read, Show)









-- recursive data structure
--------------------------------------------------

data MyList a = Empty | Cons a (MyList a) deriving (Eq, Ord, Show, Read)













