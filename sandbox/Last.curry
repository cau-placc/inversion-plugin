--import System
import System.Environment
--import Control.Findall

main :: IO ()
main = do
  (s:_) <- getArgs
  let x = read s :: Int
  --print $ allValues $ last (take x (repeat ()))
  print $ last (take x (repeat ()))

last :: Data a => [a] -> a
last (_ ++ [x]) = x
