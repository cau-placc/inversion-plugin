module Bench where

import Criterion.Main
import Criterion.Types

import Main hiding ( main )
import RunEgison
import qualified App

main :: IO ()
main = do
  let xs = 5000 : map (+5000) xs :: [Int]
  let ys = 10 : map (+10) ys :: [Int]
  putStrLn "Benchmarking"
  defaultMainWith
    (defaultConfig {reportFile = Just "benchmarks.html"}) $
    [bgroup "last" (map (\x -> bench (show x) (nf last2 (take x (repeat ())))) (take 10 xs))]
    ++ [bgroup "app2" (map (\x -> bench (show x) (nf app2 (gen x))) (take 10 ys))]
    ++ [bgroup "app3" (map (\x -> bench (show x) (nf app3 (gen x))) (take 10 ys))]
    ++ [bgroup "app4" (map (\x -> bench (show x) (nf app4 (gen x))) (take 10 ys))]
    ++ [bgroup "Egison.app2" (map (\x -> bench (show x) (nf App.app2 (gen x))) (take 8 ys))]
    ++ [bgroup "Egison.app3" (map (\x -> bench (show x) (nf App.app3 (gen x))) (take 4 ys))]
    ++ [bgroup "Egison.app4" (map (\x -> bench (show x) (nf App.app4 (gen x))) (take 2 ys))]
