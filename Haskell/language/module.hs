{-
	content:
	1. import
	2. :browse
	3. Data.List
	4. Data.Char
	5. Data.Map (字典)
-}


-- import
-----------------------------------------------------
-- 使用import来装载一个module
{-
	Prolude 是一个自动加载的module，其中包含一些常用的基本的义
	用:browse Prolude 命令来查看具体定义的内容

-}
import Data.List
-- Data.List 是一个module,其中包含许多处理list的函数


-- 若仅加载一个module中的某些定义,方法如下：
import Data.List (nub, sort)


-- 若加载某个module时,一些定义不想加载进来，方法为:
import Data.List hiding (nub, sort)


--避免命名冲突
import qualified Data.Map 
-- 这样调用Data.Map中的定义只能用Data.Map.xxx来进行了

-- 若觉得每次都写Data.Map 太麻烦可以为其定义alias
import qualified Data.Map as M
-- 这样就能用 M.xxx 代替 Data.Map.xxx 了






-- :broese
--------------------------------------------------------
-- :browse 命令，查看一个module中的所有定义的name和type
-- eg: 
{-
	:broese Data.List
-}






-- Data.List
-------------------------------------------------------
-- Data.List应用的示例

aa = intersperse '.' "wanglulu"	-- aa = "w.a.n.g.l.u.l.u"

bb = intersperse 0 [1,2,3,4]	-- bb = [1,0,2,0,3,0,4]


cc = transpose [[1,2,3],	-- cc =[[1,4,7],
				[4,5,6],	--		[2,5,8],
				[7,8,9]]	--		[3,6,9]]

-- nub 删除重复元素
ccc = nub [1,2,3,3,2,5,6,1,1,2,3]
	-- ccc = [1,2,3,5,6]


-- foldl', foldl1' 是foldl和foldl1的严格版本
-- 如果用惰性 fold 时经常遇到溢出错误,就应换用它们的严格版



-- iterate 取一个函数和一个值作参数。它会用该值去调用该函数
-- 并用所得的结果再次调用该函数,产生一个无限的 list

dd = take 10 (iterate (*2) 1)	-- dd = [1,2,4,8,16,32,64,128,256,512]

ee = take 3 (iterate (++ "hehe") "hehe")
								-- ee = ["hehe","hehehehe","hehehehehehe"]


-- takeWhile 类似于filter。但它从一个 list 中取元素,一旦遇到
-- 不符合条件的某元素就停止。常用于处理无穷list

ff = takeWhile (>3) [6,5,4,3,2,1,9,10,12,14]	-- f = [6,5,4]

gg = sort [2,4,7,45,7,3,1,3,5657,98]	-- gg = [1,2,3,3,4,7,7,45,98,5657]



-- group 取一个 list 作参数,并将其中相邻并相等的
-- 元素各自归类,组成一个个子 list

hh = group [1,1,2,2,3,4,4,2,2,1]
-- hh = [[1,1],[2,2],[3],[4,4],[2,2],[1]]




-- isInfixOf 搜索字串 [a] -> [a] -> Bool
ii = isInfixOf "wll" "my name is wll and you?"	-- ii = True

jj = isInfixOf "Wll" "my name is wll and you?"	-- jj = False




-- partition
kk = partition (>3) [1,2,5,6,3,2,1,5,7,9]
	-- kk = ([5,6,5,7,9],[1,2,3,2,1])

ll = partition (`elem` ['A'..'Z']) "guyGUYGYUGbvgvVYTUCFUT"
	-- ll = ("GUYGYUGVYTUCFUT","guybvgv")



-- lines, unlines
mm = lines "first line\nsecond line\nthrid line"
	-- mm = ["first line","second line","thrid line"]

nn = unlines ["first line","second line","thrid line"]
	-- nn = "first line\nsecond line\nthrid line\n"



-- words, unwords
oo = words "Hello My name is\nwanglulu"
	-- oo = ["Hello","My","name","is","wanglulu"]

pp = unwords ["Hello","My","name","is","wanglulu"]
	-- pp = "Hello My name is wanglulu"




-- 差集操作 \\
qq = [1..10] \\ [1,2,3,8,9,10]
	-- qq = [4,5,6,7]

-- 并集 union
rr = [1,1,1] `union` [2,2,2]
	-- rr = [1,1,1,2]

-- 交集 intersect
ss = [1,1,1,2,2,2] `intersect` [2,2,2]
	-- ss = [2,2,2]






-- Data.Char
------------------------------------------------------
-- 包含一些处理字符的函数
import Data.Char
{-
	Char -> Bool:

	isControl
	isSpace
	isLower
	isUper
	isAlpha
	isAlphaNum
	isDigit
	isPrint

-}

-- eg:
tt = all isLower "hi, i am happly"
	-- tt = False

uu = all isLower "hiiamhappy"
	-- uu = True

{-
	toUpper : 将一个字符转为大写字母,若该字符不是小写字母,就按原值返回.
	toLower
	digitToInt
-}

vv = map digitToInt "FF85AB"
	-- vv = [15,15,8,5,10,11]



-- ord, chr
{-
	ord 'a' => 97
	chr 97  => 'a'
-}

ww = map ord "abcdefgh"	-- ww = [97,98,99,100,101,102,103,104]






-- Data.Map (字典)
----------------------------------------------------
-- Data.Map与Prelude中的部分函数有冲突，因此
import qualified Data.Map as M


xx = M.fromList [("lulu",170), ("god",195), ("naruto",173)]
	-- xx = fromList [("god",195),("lulu",170),("naruto",173)]

	










