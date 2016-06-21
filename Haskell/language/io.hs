import Data.Char
import Control.Monad

{-
    content:
    1. compile a source file
    2. mian & IO actions
    3. some io functions
    4. when
    5. sequence
-}

-- compile a source file
--------------------------------------------------------
{-
    在终端下输入 ghc --make filename
    就能进行编译了m之后会生成可执行文件, 输入 ./filename 就能执行了

    !也可以直接在终端输入 runhaskell filename, 效果和编译后执行一样。
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
main :: IO ()
main = do
    putStrLn "hello, what is your name?"
    name <- getLine
    putStrLn ("hey " ++ name)

{-
    aa <- getLine
    the operator <- is a syntex suger, which take the
    value out of the box "IO xxx", and set aa with
    the fitched value obviously the value should have the type xxx.

    <- can mutate a variable, so it is impure.
-}

{-
    I/O actions will only be performed when they are given a
    name of main or when they're inside a bigger I/O action
    within a do block. We can also use a do block to glue
    together a few I/O actions and then use that I/O action
    in another do block, they'll be performed only if they
    eventually fall into main.
-}






-- let
--------------------------------------------------------
-- example:
code :: IO ()
code = do
    putStrLn "what is your first name?"
    firstName <- getLine
    putStrLn "what is your last name?"
    lastName <- getLine
    let bigFirstName = map toUpper firstName
        bigLastName = map toUpper lastName
    putStrLn $ "hey " ++ bigFirstName ++ bigLastName ++ ", how are you?"






-- some io functions
--------------------------------------------------------
{-
putStr "haha"
-- similar to putStrLn, just without a new line

putChar 'a'

-- definition
putStr :: String -> IO ()
putStr [] = return ()
putStr (x:xl) = do
    putChar x
    putStr xl

-- print = putStrLn . show
-- print can print any type that ia an instance of Show
-- putStrLn can only print String
print "haha"
print [1,2,3]
print 123
print True


getChar :: IO Char
-}





-- when
--------------------------------------------------------
{-
    in module Control.Monad there is a function "when" which
    works like it in imp lang, but it is acturaly just a function.
    its type:
    when :: Monad m => Bool -> m () -> m ()
-}
-- import Control.Monad

code4 = do
    c <- getChar
    when (c /= ' ') $ do
        putChar c
        code4






-- sequence
--------------------------------------------------------
{-
    sequence :: Monad m => [m a] -> m [a]
-}
code5 = do
    a <- getChar
    b <- getChar
    c <- getChar
    print [a,b,c]

-- equals to:
code6 = do
    abc <- sequence [getChar, getChar, getChar]
    print abc



// to "mapM and mapM_"




-- more example
--------------------------------------------------------
code2 :: IO ()
code2 = do
    line <- getLine
    if null line
        then return ()  -- main has a IO value, so () must be transformed into IO () type with "return".
        else do     -- do is similar to begin in scheme
            putStrLn $ reverse line
            code2

-- return in haskell is different with it in other imp language,
-- it is just a function with type "Monad m => a -> m a"
-- and the exec of it woundn't end a method like in C++/Java.
-- eg:
code3 = do
    return ()
    return "haha"
    line <- getLine
    aa <- return 443
    putStrLn line
    print aa


-- take params
tt :: String -> IO ()
tt x = do
    putStrLn x
