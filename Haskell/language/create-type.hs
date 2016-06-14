{-
	content:
	1.
	2.
	3.
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

