{-# OPTIONS_GHC-fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--full"                      @-}
{-@ LIQUID "--etabeta"                   @-}
{-@ LIQUID "--dependantcase"             @-}


module Test where

import Prelude hiding (map, all, scan, zip3)

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:[a] -> { ys:[b] | len xs == len ys } @-}
map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

{-@ reflect map3 @-}
{-@ map3 :: (a -> b -> c -> d) -> xs:[a] -> { ys:[b] | len xs == len ys } -> { zs:[c] | len xs = len zs } -> [d] @-}
map3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
map3 f []     []     []     = []
map3 f (x:xs) (y:ys) (z:zs) = f x y z : map3 f xs ys zs


{-@ reflect zip3 @-}
{-@ zip3 :: xs:[a] -> { ys:[b] | len xs == len ys } -> { zs:[c] | len xs = len zs } -> [(a,b,c)] @-}
zip3 = map3 (\x y z -> (x,y,z))

{-@ reflect scanNat @-}
{-@ scanNat :: (Nat -> Nat -> Nat) -> Nat -> xs:[Nat] -> {ys:[Nat] | len ys == len xs} @-}
scanNat :: (Int -> Int -> Int) -> Int -> [Int] -> [Int]
scanNat op acc [] = []
scanNat op acc (x:xs) = x `op` acc : scanNat op (x `op` acc) xs 


--------------------------------------------------------------------------------
-- The program
--------------------------------------------------------------------------------
{-@ reflect tflagsLam @-}
tflagsLam :: Bool -> Int
tflagsLam True = 1
tflagsLam False = 0

{-@ reflect tFlags @-}
{-@ tFlags :: cs:[Bool] -> {is : [OneOrZero] | len is == len cs} @-}
tFlags :: [Bool] -> [Int]
tFlags cs = map tflagsLam cs

{-@ reflect nng @-}
nng :: Int -> Bool
nng x = x >= 0

{-@ reflect natAdd @-}
{-@ natAdd :: Nat -> Nat -> Nat @-}
natAdd :: Int -> Int -> Int
natAdd x y = x + y

{-@ reflect zeroNat @-}
{-@ zeroNat :: Nat @-}
zeroNat :: Int
zeroNat = 0

{-@ reflect indsT @-}
{-@ indsT :: cs : [Bool] -> {ys : [Nat] | True} @-}
indsT :: [Bool] -> [Int]
indsT cs =
  let tflgs = tFlags cs
      indsT = scanNat natAdd zeroNat tflgs
  in indsT

{-@ type OneOrZero = {v:Int | v == 0  || v == 1} @-}

{-@ reflect fflagsLam @-}
{-@ fflagsLam :: OneOrZero -> Nat @-}
fflagsLam :: Int -> Int
fflagsLam b = 1 - b

{-@ reflect fFlags @-}
{-@ fFlags :: xs:[OneOrZero] -> {is : [Nat] | len is == len xs} @-}
fFlags :: [Int] -> [Int]
fFlags tflgs = map fflagsLam tflgs

{-@ reflect tmpW @-}
{-@ tmpW :: cs : [Bool] -> {ys : [Nat] | True} @-}
tmpW :: [Bool] -> [Int]
tmpW cs =
  let tflgs = tFlags cs
      fflgs = fFlags tflgs
      tmp = scanNat natAdd zeroNat fflgs
  in tmp

{-@ reflect index @-}
{-@ index :: xs:[a] -> { i:Nat | i < len xs } -> a @-}
index :: [a] -> Int -> a
index [] _ = error "impossible"
index (x:_) 0 = x
index (_:xs) i = index xs (i - 1)

{-@ reflect indsFLam @-}
{-@ indsFLam :: Nat -> Nat -> Nat @-}
indsFLam :: Int -> Int -> Int
indsFLam lst t = t + lst

{-@ reflect mapLam @-}
mapLam :: (Bool, Int, Int) -> Int
mapLam (True, indT, _)  = indT - 1
mapLam (False, _, indF) = indF - 1

{-@ reflect almost_part2Indices @-}
almost_part2Indices :: [Bool] -> [(Bool, Int, Int)]
almost_part2Indices cs =
  let tflgs = tFlags cs
      fflgs = fFlags tflgs
      indsT = scanNat natAdd zeroNat tflgs
      tmp = scanNat natAdd zeroNat fflgs
      n = length cs
      lst = if n > 0 then index indsT (n - 1) else 0
      indsF = map (indsFLam lst) tmp
   in zip3 cs indsT indsF

{-@ reflect part2Indices @-}
part2Indices cs =
  let res = almost_part2Indices cs
  in map mapLam res

{-@ reflect p @-}
p :: (Bool, Int, Int) -> Bool
p (True, t, f) = t >= 0
p (False, t, f) = f >= 0

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool
all p []     = True
all p (x:xs) = p x && all p xs

{-@ allP :: cs : [Bool] -> {v : () | all p (almost_part2Indices cs)} @-}
allP :: [Bool] -> ()
allP [] = ()
allP (True  : cs) = allP cs
allP (False : cs) = allP cs
