import Data.Char
import System.IO
import System.Directory
import System.Environment

{-
    contents:
    1. basic file operation
    2. readFile, writeFile, appendFile
    3. removeFile, renameFile
    4. command line arguments
    
-}

-- basic file operation
---------------------------------------------------------
code0 = do
    handle <- openFile "example.txt" ReadMode
    contents <- hGetContents handle
    putStrLn contents
    hClose handle

{-
    openFile :: FilePath -> IOMode -> IO Handle
        type FilePath = String
        data IOMode = ReadMode | WriteMode | AppendMode | ReadWriteMode

    hGetContents :: Handle -> IO String
    -- hGetContents is lazy, it only reads if needed. Great feature for reading big file.
    hClose :: Handle -> IO ()
-}


---------- another way: withFile
{-
    use withFile
    withFile :: FilePath -> IOMode -> (Handle -> IO r) -> IO r
-}

code = do
    withFile "example.txt" ReadMode (\handle -> do
        contents <- hGetContents handle
        putStrLn contents)
-- it has the same effect as the code in main

-- definition of withFile
withFile' :: FilePath -> IOMode -> (Handle -> IO r) -> IO r
withFile' path mode f = do
    handle <- openFile "example.txt" ReadMode
    result <- f handle
    hClose handle
    return result


----- other functions
----- read:
-- hGetLine
-- hGetChar
--
----- write:
-- hPutStr
-- hPutStrLn
-- hPutChar







-- readFile, writeFile, appendFile
---------------------------------------------------------
{-
    readFile is useful in some cases:
    readFile :: FilePath -> IO String
-}

code2 = do
    contents <- readFile "example.txt"
    putStr contents
-- code2 has the same effect with main


{-
    writeFile will clear or create a file and write from the begining
    writeFile :: FilePath -> String -> IO ()
-}
-- example:
code3 = do
    contents <- readFile "example.txt"
    writeFile "newFile.txt" (map toUpper contents)


{-
    appendFile is similar to writeFile, but it append instead of clear a file and write.
    appendFile :: FilePath -> String -> IO ()
-}
-- example:
code4 = do
    line <- getLine
    appendFile "newFile.txt" (line ++ "\n")







-- removeFile, renameFile
---------------------------------------------------------
-- import System.Directory
{-
    removeFile can remove a file
    removeFile :: FilePath -> IO ()

    renameFile can rename a file
    renameFile :: FilePath -> FilePath -> IO ()
-}
-- example:
code5 = do
    tempHandle <- openFile "temp.txt" WriteMode
    hClose tempHandle
    renameFile "temp.txt" "newName.txt"
    removeFile "newName.txt"






-- command line arguments
---------------------------------------------------------
-- import System.Environment
{-
    sometimes we need to pass some params to a program in the terminal,
    that is command line arguments.

    -- functions:
    getArgs :: IO [String]
    getProgName :: IO String
-}

main = do
    args <- getArgs
    pname <- getProgName
    putStrLn "the args are:"
    mapM_ putStrLn args
    putStrLn "the name of the program is:"
    putStrLn pname
