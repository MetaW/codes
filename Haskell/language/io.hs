{-
    content:
    1. compile a source file
    2. mian & IO actions
    3.
-}

-- compile a source file
--------------------------------------------------------
{-
    在终端下输入 ghc --make filename
    就能进行编译了m之后会生成可执行文件, 输入 ./filename 就能执行了
-}





-- mian & IO actions
--------------------------------------------------------
{-
    haskell 将 pure 的代码和具有 side effect 的代码分隔开了,
    所有具有side effect的代码必须写到 main 的后面，它是一个类似
    于命令式的编程环境。

    !!!而且每个文件中main只能出现一次!!!
-}
-- main = putStrLn "hello world"
-- or:
main = do
    putStrLn "hello, what is your name?"
    name <- getLine
    putStrLn ("hey " ++ name)
