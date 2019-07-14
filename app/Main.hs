{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import JellyVM.LL.Types
import JellyVM.LL.LL
import JellyVM.LAM.LAM
import JellyVM.LAM.Types (Dump (Null))
import Criterion.Measurement (secs, getTime)

main :: IO ()
main = do
    (t, res) <- time $ run (linear add) (one :⌟ two) Null
    print res
    putStrLn $ "In " <> secs t

time :: a -> IO (Double, a)
time f = do
    begin  <- getTime
    let result = f
    end    <- getTime
    pure $ (,) (end - begin) result

zero = Zero' :· Unit
one = Succ :· zero
two = Succ :· one

add = Lapp :∘ (Nrec (Lcur Cl) (Lcur (Succ :∘ Lapp)) :× Id)