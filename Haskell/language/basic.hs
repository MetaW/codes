
--在GHCI中加载此文件,要输入":l filename.hs"就行了
--加载之后提示符变为"Main>",若要重新加载,可以输入":r"

{-
这种注释可以跨行
-}


--/////////////////////////////////////
--函数定义

add x y =  x + y
sub x y = x - y
mul x y = x * y
div x y = x / y

--//////////////////////////////////////
--定义变量
v1 = 10
v2 = 2323

--///////////////////////////////////////
--if分支

big x y =   if x>y
            then x
            else y

biggest x y z = if x>y
                then (if x>z
                      then x
                      else z)
                else (if y>z
                      then y
                      else z)


--///////////////////////////////////////
--bool表达式
cond1 = False
cond2 = True
cond3 = (1>2)&&(2<=3)||(4==5)
cond4 = cond1||cond2
cond5 = not cond1
cond6 = 3 /= 4  --/=表示不等于



--///////////////////////////////////////
--局部函数
func x =
  let next x = x+1  --这里定义了3个局部函数
      pre x = x-1
      sqre x = x*x
  in  add (next x) (sqre x)








