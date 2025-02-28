{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--full"                      @-}
{-@ LIQUID "--etabeta"                   @-}
{-@ LIQUID "--dependantcase"             @-}

module ArrayProps.Partition2 where

import Prelude hiding (map, zipWith, all)

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:[a] -> { ys:[b] | len xs = len ys } @-}
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

{-@ reflect zipWith @-}
{-@ zipWith :: (a -> b -> c) -> xs:[a] -> { ys:[b] | len xs = len ys } -> [c] @-}
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f []     []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool
all p []     = True
all p (x:xs) = p x && all p xs

{-@ reflect nng @-}
nng :: Int -> Bool
nng x = x >= 0

--------------------------------------------------------------------------------
-- The program
--------------------------------------------------------------------------------
-- {-@ reflect boolToInt @-}
-- boolToInt :: Bool -> Int
-- boolToInt True = 1
-- boolToInt False = 0

{-@ reflect scan @-}
scan op ne xs = drop 1 $ scanl op ne xs

{-@ reflect map2 @-}
map2 = zipWith

{-@ reflect map3 @-}
map3 = zipWith3

part2IndicesOriginal :: [Bool] -> [Int]
part2IndicesOriginal cs =
  let n = length cs
      tflgs = map (\c -> if c then 1 else 0) cs
      fflgs = map (\b -> 1 - b) tflgs
      indsT = scan (+) 0 tflgs
      tmp = scan (+) 0 fflgs
      lst = if n > 0 then indsT !! (n - 1) else 0
      indsF = map (\t -> t + lst) tmp
   in map3 (\c indT indF -> if c then indT - 1 else indF - 1) cs indsT indsF

{-@ reflect helper1 @-}
helper1 True indT _  = indT - 1
helper1 False _ indF = indF - 1

{-@ reflect part2Indices @-}
part2Indices :: [Bool] -> [Int]
part2Indices cs =
  let n = length cs
      tflgs = map (\c -> if c then 1 else 0) cs
      fflgs = map (\b -> 1 - b) tflgs
      indsT = scan (+) 0 tflgs
      tmp = scan (+) 0 fflgs
      lst = if n > 0 then indsT !! (n - 1) else 0
      indsF = map (\t -> t + lst) tmp
   in map3 helper1 cs indsT indsF

--------------------------------------------------------------------------------
-- The post-condition
--------------------------------------------------------------------------------
-- {-@ allZ :: xs:[Bool] -> { all nng (fun xs) } @-}
-- allZ :: [Bool] -> ()
-- allZ []           = ()
-- allZ (True  : xs) = allZ xs
-- allZ (False : xs) = allZ xs

{-@ inc :: {v:Int | v >= 0} -> {v:Int | v >= 0} @-}
inc :: Int -> Int
inc x = plus x one

{-@ one :: {v:Int | v >= 0} @-}
one :: Int
one = undefined

{-@ plus :: x:Int -> y:Int -> {v:Int| v = x + y} @-}
plus :: Int -> Int -> Int
plus = undefined
