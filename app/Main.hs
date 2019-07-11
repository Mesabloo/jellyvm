module Main where

import LL.Types
import LL.LL
import LAM.LAM
import LAM.Types (Dump (Null))

main :: IO ()
main = print $ run (linear add) (one :⌟ two) Null

zero = Zero' :· Unit
one = Succ :· zero
two = Succ :· one

add = Lapp :∘ (Nrec (Lcur Cl) (Lcur (Succ :∘ Lapp)) :× Id)