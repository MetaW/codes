--type
--用:t exp来查看exp的类型

--一些类型：
--Int 		4byte整数
--Integer 	大整数长度不限
--Float 	浮点数
--Double	双精度浮点数
--Bool		布尔
--Char		字符
--[xx]		xx类型的list
--(x,y,...)	tuple类型由长度和各元素类型确定
--Ordering	顺序类型，值有三个：LT,EQ,GT
--a			一些类型

--minBound可以返回一个类型的成员值的下限
--maxBound可以返回一个类型的成员值的上限
aa = minBound :: Int
bb = maxBound :: Int


--typeclass
--------------------------------------------------------
--typeclass描述了一些类型的集合,一般用于支持多类型的函数,类似于范型
--	=>符号叫类型约束，它的左边为typeclass规定了函数支持的类型，右边为

-- 函数的类型
--eg :t sum 返回 sum :: Num a => [a] -> a
--即sum涉及的typeclass为Num,类型为[a]->a,a为Num中的任意类型
--eg :t fromIntegral(将整数数值类型转化为通用的数值类型)
--返回:fromIntegral :: (Num b, Integral a) => a -> b



--函数类型一般为 x->y->z->w等类似的形式,其中最后一个为返回值类型,前面的
--为参数类型


--常见的typeclass
--Num 		包含了一些数值类型，如Int,Float等
--Integral	包含整数的数值类型：Int,Integer
--Floating	包含实数的数值类型：Float,Double
--Eq 		包含了可以判等的类型
--Ord 		包含了可以比较大小的类型
--Show		包含了可以转换为字符串的类型(在show函数中使用)
--Read 		包含了可以由字符串转换而得到的类型

--read函数与show函数
--show将参数专为字符串
cc = show 123.32		--cc="123.32"
dd = show True			--dd="True"
ee = show 321			--ee="321"

--read将字符串中内容转为指定类型
--由于 read :: Read a => String -> a 可知返回的类型不确定
--由于Haskell最终要明确所以类型，因此使用read时要指明转换后的类型
ff = read "123.43"::Float 		--ff=123.43
gg = read "4"::Float 			--gg=4.0

--如果转换后直接用于计算,Haskell可以推算出类型，则可以不写明
hh = read "123.11" + 5.3
ii = read "[1,32,43]" ++ [212,111]










