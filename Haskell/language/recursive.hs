{-
	内容：一些递归的例子
-}

-------------------------------------------------------------
-------------------------------------------------------------

--eg:求list最大值
myMax :: Ord a => [a] -> a
myMax [] = error "error! the list can not be empty!" --这里是用了异常
myMax (x:[]) = x
myMax (x:y) 
	| x > max = x
	| otherwise = max
	where max = myMax y


--eg:replicate
myReplic :: (Num a, Ord a) => a -> b -> [b]
myReplic n x
	| n <= 0 = []
	| otherwise = x:myReplic (n-1) x

--eg:take
myTake :: (Num a, Ord a) => a -> [b] -> [b]
myTake n [] = []
myTake n (x:xl)
	| n <= 0 = []
	| otherwise = x:myTake (n-1) xl


--eg:zip
myZip :: [a] -> [b] -> [(a,b)]
myZip [] _ = []
myZip _ [] = []
myZip (x:xl) (y:yl) = (x, y):myZip xl yl


--快速排序！！！
qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xl) = let h = qsort [t|t<-xl,t<=x]
                   t = qsort [t|t<-xl,t>x]
               in	h ++ [x] ++ t

--version2
qst :: Ord a => [a] -> [a]
qst [] = []
qst (x:xl) = qst [t|t<-xl,t<=x] ++ x:qst [t|t<-xl,t>x]
















