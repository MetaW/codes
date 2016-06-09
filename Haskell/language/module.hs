{-
	content:
	1. import
	2. :browse
	3. Data.List
	4.
	5.
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

-- 若觉得每次都写Data.Map 太妈烦可以为其定义alias
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



