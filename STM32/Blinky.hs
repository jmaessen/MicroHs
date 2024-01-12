module Blinky(main) where
--import Primitives
--import Data.Bool
import Prelude

--foreign import ccall "set_led" setLed :: Int -> Int -> IO ()

{-
main :: IO ()
main = --setLed (0::Int) (1::Int)
  blinky (500::Int)

blinky :: Int -> IO ()
blinky n =
  oneByOne n (1::Int) `primThen`
  oneByOne n (0::Int) `primThen`
  blinky (n `primIntAdd` 1)

oneByOne :: Int -> Int -> IO ()
oneByOne n on =
  setLed (0::Int) on `primThen`
  wait n `primThen`
  setLed (1::Int) on `primThen`
  wait n `primThen`
  setLed (2::Int) on `primThen`
  wait n `primThen`
  setLed (3::Int) on `primThen`
  wait n

foreign import ccall "set_led" setLed :: Int -> Int -> IO ()

-}

main :: IO ()
main = blinky (500::Int)

blinky :: Int -> IO ()
blinky n = do
  oneByOne n True
  oneByOne n False
  blinky (n + 1)

oneByOne :: Int -> Bool -> IO ()
oneByOne n on = forM_ [0..3] $ \ led -> do
  setLed led on
  wait (n + led)
{-
 do
  setLed (0::Int) on
  wait n
  setLed (1::Int) on
  wait n
  setLed (2::Int) on
  wait n
  setLed (3::Int) on
  wait n
-}

foreign import ccall "set_led" set_led :: Int -> Int -> IO ()

setLed :: Int -> Bool -> IO ()
setLed led on = set_led led $ if on then 1 else 0
  --print ("setLed",led,on)

wait :: Int -> IO ()
wait n = do
  --print ("wait", n)
  seq (loop n) (return ())

loop :: Int -> ()
loop n = if n == 0 then () else loop (n - 1)
