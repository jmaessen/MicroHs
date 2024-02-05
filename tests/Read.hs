module Read(main) where
import Prelude
import Text.Read

main :: IO ()
main = do
  print (read "123"   :: Int)
  print (read " 123"  :: Int)
  print (read "123 "  :: Int)
  print (read "-123"  :: Int)
  print (read "(123)" :: Int)
  print (read "0x7b"  :: Int)
  print (read "0o173" :: Int)
  print (read "0b01111011" :: Int)
  print (read "2147483647" :: Int)
  print (read "-2147483648" :: Int)
  if _wordSize == 64 then do
    print (read "9223372036854775807" :: Int)
    print (read "-9223372036854775808" :: Int)
   else do
    putStrLn "9223372036854775807"
    putStrLn "-9223372036854775808"
  print (read "123"   :: Integer)
  print (read " 123"  :: Integer)
  print (read "123 "  :: Integer)
  print (read "-123"  :: Integer)
  print (read "(123)" :: Integer)
  print (read "1234567890123456789012345678901234567890" :: Integer)
  print (read "[1,2, 3]" :: [Int])
  print (read "False" :: Bool)
  print (read "True" :: Bool)
  print (reads "123 4" :: [(Int, String)])
  print (readMaybe "123" :: Maybe Int)
  print (readMaybe "apa" :: Maybe Int)
  print (read "1.25" :: Double)
  print (read "-1e20" :: Double)
  print (read "-1e+5" :: Double)
  print (read "1.5e+5" :: Double)
  print (read "5e-1" :: Double)
  print (read "[EQ,GT,LT]" :: [Ordering])
  print (read "Nothing" :: Maybe Int)
  print (read "Just 123" :: Maybe Int)
  print (read "Just (Just 123)" :: Maybe (Maybe Int))
  print (read "Just Nothing" :: Maybe (Maybe Int))
  print (readMaybe "Just Just 123" :: Maybe (Maybe (Maybe Int)))
  print (read "Left True" :: Either Bool Int)
  print (read "Right 123" :: Either Bool Int)
  print (read "()" :: ())
  print (read "(True,123)" :: (Bool, Int))
