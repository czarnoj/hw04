{-
HW 4 - Quickcheck
==================

This homework assignment is composed of two problems.

Make all of your edits in the files [`Sat.hs`](Sat.hs) and
[`AVL.hs`](AVL.hs).

Problem - A SAT solver
----------------------
See [`Sat.lhs`](Sat.html)

This problem gives you more experience with quickcheck. You might want to review the [`QuickCheck`](../../lectures/soln/04-quickcheck/QuickCheck.html) lecture notes before you begin.

Problem - AVL trees
-------------------------
See [`AVL.lhs`](AVL.html)

This problem is based on balanced binary search trees. You might want to review the [`RedBlack`](../../lectures/stub/05-persistent/RedBlack.html) lecture notes before you begin.
-}

module Main where

import qualified AVL
import qualified Sat

{-
>
-}

main :: IO ()
main = do
  putStrLn "This is Sat"
  Sat.main
  putStrLn "This is AVL"
  AVL.main
