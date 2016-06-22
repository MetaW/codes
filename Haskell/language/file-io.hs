{-
    contents:
    1.
    2.
    3.
    4.
-}

-- example:
import System.IO

main = do
    handle <- openFile "example.txt" ReadMode
    contents <- hGetContents handle
    putStrLn contents
    hClose handle

{-
    openFile :: FilePath -> IOMode -> IO Handle
        type FilePath = String
        data IOMode = ReadMode | WriteMode | AppendMode | ReadWriteMode

    hGetContents :: Handle -> IO String

    hClose :: Handle -> IO ()
-}
