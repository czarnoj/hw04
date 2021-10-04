{-
Using QuickCheck to develop a SAT solver
========================================

The [Davis-Putnam-Logemann-Loveland
algorithm](http://en.wikipedia.org/wiki/DPLL_algorithm) is a method for
deciding the satisfiability of propositional logic formulae. Although the SAT
problem is NP-complete, it is still remarkably amenable to automation, and
high-performance SAT-solvers are heavily used in modern software
verification, constraint solving, and optimization.  Your task in this
problem is to implement one of the basic ideas behind the DPLL algorithm and check
your implementation using QuickCheck.

We'll lead you through the main steps, but if you're not already
familiar with the basics of SAT solving you will need to do a little
reading about the basic ideas in DPLL.

- [DPLL Wikipedia page](http://en.wikipedia.org/wiki/DPLL_algorithm)

Throughout, try to use library functions to make your code short and
elegant.  None of the requested function bodies should take much more
than a dozen or so lines.  Style counts!
-}

---------------------------------------------------------------------------

module Sat where

{-
In this problem, we will use a data structure from Haskell's standard
library, implementing Finite Maps.  The two import declarations below
say: (1) import the type `Map` from the module `Data.Map` as an unqualified
identifier, so that we can use just `Map a b` as a type; and (2) import
everything else from `Data.Map` as qualified identifiers, written
`Map.member`, etc.

This data structure is defined in the
[`containers`](http://hackage.haskell.org/package/containers) Haskell package
(included with GHC). For a short introduction, see
the containers [tutorial
documentation](https://haskell-containers.readthedocs.io/en/latest/).
-}

{-
We will also make other library functions available.
-}

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
{-
Finally, import definitions for QuickCheck.
-}

import Test.HUnit (Test (..), assertBool, runTestTT, (~:), (~?=))
import Test.QuickCheck

---------------------------------------------------------------------------
-- Basic types

{-
The DPLL algorithm works on formulae that are in [Conjunctive Normal
Form (CNF)](http://en.wikipedia.org/wiki/Conjunctive_normal_form),
i.e. formulae that consist of a conjunction of _clauses_, where each
clause is a disjunction of _literals_, i.e. positive or negative
propositional variables. For example,

    (A \/ B \/ C) /\ (not A) /\ (not B \/ C)

is a CNF formula.
-}

-- | An expression in CNF (conjunctive normal form) is a conjunction
-- of clauses. We store these clauses in the conjunction in a list.
newtype CNF = Conj {clauses :: [Clause]} deriving (Eq, Ord, Show)

-- | A clause is a disjunction of a number of literals, again storing
-- each literal in a list.
newtype Clause = Disj {lits :: [Lit]} deriving (Eq, Ord, Show)

-- | A literal is either a positive or a negative variable
data Lit = Lit {polarity :: Bool, var :: Var} deriving (Eq, Ord, Show)

-- | A variable is just a character
newtype Var = Var Char
  deriving (Eq, Ord, Show)

-- A few variables for test cases
vA, vB, vC, vD :: Var
vA = Var 'A'
vB = Var 'B'
vC = Var 'C'
vD = Var 'D'

{-
Here's how the formula from above is represented:
-}

exampleFormula :: CNF
exampleFormula =
  Conj
    [ Disj [Lit True vA, Lit True vB, Lit True vC],
      Disj [Lit False vA],
      Disj [Lit False vB, Lit True vC]
    ]

-------------------------------------------------------------------------

{-
The next few operations allow us to work with formulae, clauses, literals and
variables.

First observe that `clauses` will extract the list of clauses from a `CNF`,
`lits` will extract the list of literals from a `Clause`, and `var` will extract the
variable from a `Literal`.

We also have two functions for working with the polarity of a literal.
-}

-- | Is the literal positive?
isPos :: Lit -> Bool
isPos = polarity

-- | Negate a literal
neg :: Lit -> Lit
neg (Lit b x) = Lit (not b) x

{-
CNF formulae and Clauses also form a monoid:
-}

instance Semigroup CNF where
  Conj c1 <> Conj c2 = Conj (c1 <> c2)

instance Monoid CNF where
  mempty = Conj mempty

{-
>
-}

instance Semigroup Clause where
  Disj c1 <> Disj c2 = Disj (c1 <> c2)

instance Monoid Clause where
  mempty = Disj mempty

{-
Variables are enumerable. However, only the first 26 will print
nicely.
-}

instance Enum Var where
  toEnum i = Var (toEnum (i + fromEnum 'A'))
  fromEnum (Var v) = fromEnum v - fromEnum 'A'

-- | A long list of variables
allVars :: [Var]
allVars = [vA ..]

-------------------------------------------------------------------------

{-
Sometimes we need to know about all of the variables that appear in a
particular formula. We can use a finite map structure to calculate this
information. (You'll need to refer to the documentation for the
[`Data.Map`](https://hackage.haskell.org/package/containers-0.6.2.1/docs/Data-Map-Lazy.html)
module to complete this part.)
-}

-- | The number of times each variable appears in the formula
-- >>> countVars exampleFormula
-- fromList [(Var 'A',2),(Var 'B',2),(Var 'C',2)]
countVars :: CNF -> Map Var Int
countVars = undefined

-- | All of the variables that appear anywhere in the formula, in sorted order
-- >>> vars exampleFormula
-- [Var 'A',Var 'B',Var 'C']
vars :: CNF -> [Var]
vars = undefined

{-
Here are two test cases, using the example formula above. Make sure to add
a few of your own unit tests, too!
-}

testCountVars :: Test
testCountVars =
  "countVars"
    ~: countVars exampleFormula ~?= Map.fromList [(vA, 2), (vB, 2), (vC, 2)]

testVars :: Test
testVars =
  "vars"
    ~: vars exampleFormula ~?= [vA, vB, vC]

-------------------------------------------------------------------------

{-
Of course, most of the testing we will do in this homework will use QuickCheck.

To do that, we need to be able to generate arbitrary formulae. The following
generators should be parameterized by the number of distinct variables to use.  When
you are testing solvers below, you'll find that changing this number affects
the efficiency of certain solvers and also the distribution of satisfiable
random formulae.

For example, if we sample from `genVar` below, we should only see three different variables.

    *Sat> xs <- sample' (genVar 3)
    *Sat> xs
    [Var 'A',Var 'A',Var 'C',Var 'C',Var 'A',Var 'C',Var 'B',Var 'A',Var 'C',Var 'A',Var 'A']
-}

-- | Generate a random variable (limited to the first `n` variables).
genVar :: Int -> Gen Var
genVar n | n < 1 = error "Must supply a positive number to genVar"
genVar n = undefined

-- | Generate a random literal with `n` distinct variables.
genLit :: Int -> Gen Lit
genLit n = undefined

-- | Generate a random Clause with `n` distinct variables.
genClause :: Int -> Gen Clause
genClause n = undefined

-- | Generate a random CNF with `n` distinct variables.
genCNF :: Int -> Gen CNF
genCNF n = undefined

-- make sure that genVars produces the right number of variables.
testGenVars :: Test
testGenVars =
  "genVar" ~: do
    xs <- sample' (genVar 3)
    return $ length (List.nub xs) == 3

-- make sure that arbitrary formulae don't contain too many variables.
testGenCNF :: Test
testGenCNF =
  "genCNF" ~: do
    xs <- sample' (genCNF defaultNumVariables)
    return $ all (\c -> length (countVars c) <= defaultNumVariables) xs

{-
We use these generators in our `Arbitrary` instances along with
appropriate definitions for `shrink`.
-}

defaultNumVariables :: Int
defaultNumVariables = 7

instance Arbitrary Var where
  arbitrary = genVar defaultNumVariables
  shrink v
    | v == vA = []
    | otherwise = [vA .. pred v]

instance Arbitrary Lit where
  arbitrary = genLit defaultNumVariables
  shrink (Lit b v) =
    map (`Lit` v) (shrink b)
      ++ map (Lit b) (shrink v)

instance Arbitrary Clause where
  arbitrary = genClause defaultNumVariables
  shrink (Disj l) = map Disj (shrink l)

instance Arbitrary CNF where
  arbitrary = genCNF defaultNumVariables
  shrink (Conj x) = map Conj (shrink x)

---------------------------------------------------------------------
-- Satisfiable and unsatisfiable formulae

{-
Our example formula is said to be _satisfiable_ because it is possible to find
an assignment of truth values to variables -- namely

    A |-> False
    B |-> True
    C |-> True

— that makes the example formula true.  On the other hand, this formula
-}

--  A /\ (not A)
unSatFormula :: CNF
unSatFormula = Conj [Disj [Lit True vA], Disj [Lit False vA]]

{-
is _unsatisfiable_ because there is no such assignment.

An assignment of truth values to variables is called a _valuation_. (In
logic, valuations usually assign a truth value to _all_ variables of a
formula.  Here we will do things a little bit differently and define a
valuation to be a map from _some_ variables to truth values.)
-}

-- | Assignments of values to (some) variables
type Valuation = Map Var Bool

emptyValuation :: Valuation
emptyValuation = Map.empty

fromList :: [(Var, Bool)] -> Valuation
fromList = Map.fromList

{-
For instance, the valuation above is represented thus:
-}

exampleValuation :: Valuation
exampleValuation = Map.fromList [(vA, False), (vB, True), (vC, True)]

{-
We say that a CNF formula is _satisfied by_ a valuation if the
valuation makes the formula true.
-}

litSatisfied :: Valuation -> Lit -> Bool
litSatisfied a lit = a Map.!? var lit == Just (polarity lit)

satisfiedBy :: CNF -> Valuation -> Bool
satisfiedBy p a = all (any (litSatisfied a) . lits) (clauses p)

{-
Take a moment to look at the definition of `satisfiedBy` and consider the following
two formulae.

- This first formula is a conjunction of zero clauses, all of which must be
  satisfied for the formula to be true. So this formula will be satisfied
  by any valuation, including the empty one. We can view this formula as equivalent
  to the logical formula "True".
-}

validFormula :: CNF
validFormula = Conj []

{-
- On the other hand, `anotherUnsatFormula` below is the conjunction of a single
  clause.  That clause must be satisfied in order for the whole formula to be
  true.  However, that clause is a disjunction; there must be some true literal
  in the clause for it to be satisfied, and there isn't.  So this formula
  cannot be satisfied by any valuation. We can view this formula as equivalent
  to the logical formula "False".
-}

anotherUnsatFormula :: CNF
anotherUnsatFormula = Conj [Disj []]

{-
Let's create a few tests for `satisfiedBy`.  Our example formula is satisfied by
the example valuation.  (Add a few more tests of formulae and their
satisfying valuations to the list below.)
-}

testSatisfiedBy :: Test
testSatisfiedBy =
  "satisfiedBy"
    ~: TestList
      [ "exampleFormula"
          ~: assertBool "" (exampleFormula `satisfiedBy` exampleValuation),
        "another example" ~: assertBool "" (error "ADD your own test case here")
      ]

{-
Note that our unsatisfiable formula is not satisfied by ANY valuation. This is
a property that we can check with QuickCheck, because we can generate
arbitrary valuations.
-}

prop_unSatBy :: Valuation -> Property
prop_unSatBy v = property (not (unSatFormula `satisfiedBy` v))

{-
Valuations support two main operations: extending them with a new binding and
checking what is the value of a variable. These are just the appropriate operations
from the `Data.Map` library.
-}

extend :: Var -> Bool -> Valuation -> Valuation
extend = Map.insert

value :: Var -> Valuation -> Maybe Bool
value = Map.lookup

---------------------------------------------------------------------------
-- Simple SAT Solver

{-
A solver is a function that finds a satisfying valuations for a given formula
(assuming one exists).
-}

type Solver = CNF -> Maybe Valuation

{-
We start with a simple combinatorial solver that basically tries all
possible valuations and stops whenever it finds a satisfying
valuation.

The first step is to implement the `makeValuations` function that
calculates _all_ the valuations for the given variables.
-}

makeValuations :: [Var] -> [Valuation]
makeValuations = undefined

{-
To test your implementation, QuickCheck the following property stating
that `makeValuations` is correct, in the sense that it has the right
length (2^*n*, where *n* is the number of variables in the set)
and all its elements are distinct.
-}

prop_makeValuations :: CNF -> Property
prop_makeValuations p =
  length valuations === 2 ^ length ss
    .&&. allElementsDistinct valuations
  where
    valuations = makeValuations ss
    ss = vars p

allElementsDistinct :: Eq a => [a] -> Bool
allElementsDistinct [] = True
allElementsDistinct (x : xs) =
  x `notElem` xs
    && allElementsDistinct xs

{-
Your first sat solver should now simply search the list of all
valuations for one that satisfies the given formula:
-}

sat0 :: Solver
sat0 = undefined

{-
To check that it works, QuickCheck the property `prop_satResultSound sat0`,
stating that a successful result returned by a `sat0` is always a
satisfying valuation.
-}

prop_satResultSound :: Solver -> CNF -> Property
prop_satResultSound solver p = case solver p of
  Just a -> collect "sat" $ p `satisfiedBy` a
  Nothing -> collect "unsat" $ property True

{-
A solver is also *complete* if whenever it fails to find a satisfying
assignment, then that formula is unsatisfiable. We say that a solver is
correct if it is both sound and complete.
-}

-- a formula is unsatisfiable when there is no satisfying valuation
-- out of all of the possible assignments of variables to truth values.
unsatisfiable :: CNF -> Bool
unsatisfiable p = not . any (p `satisfiedBy`) $ makeValuations (vars p)

prop_satResultCorrect :: Solver -> CNF -> Property
prop_satResultCorrect solver p = property $ case solver p of
  Just a -> p `satisfiedBy` a
  Nothing -> unsatisfiable p

{-
This property will always be expensive to test, so we separate full correctness
from soundness.

-}

---------------------------------------------------------------------------
-- Instantiation

{-
The simple solver we have just developed is very inefficient.  One reason for
 this is that it evaluates the whole formula every time it tries a different
 valuation. Indeed, we can do much better: once we choose a truth value for a
 propositional variable, we can simplify the formula to take this choice into
 account.

For instance, imagine we have the CNF formula

    (A \/ not B) /\ (not A \/ B \/ C).

If we instantiate `A` to `True`, then the formula becomes
`(True \/ not B) /\ (False \/ B \/ C)`, which can be simplified to `(B \/ C)`.

Note: if a variable is not present in a formula, `instantiate` should return
the formula unchanged.

Please implement the `instantiate` function:
-}

instantiate :: CNF -> Var -> Bool -> CNF
instantiate = undefined

{-
Informally, the correctness property for `instantiate` is that, if `s`
is a formula and `v` a variable, `s` should be satisfiable iff either
`instantiate s v True` or `instantiate s v False` is satisfiable.  Use
the simple satisfiability checker `sat0` to state this formally as a
QuickCheck property.  Use QuickCheck (in GHCi) to test whether your
implementation of `instantiate` has this property.
-}

prop_instantiate :: CNF -> Var -> Bool
prop_instantiate = undefined

{-
Now use `instantiate` to write a sat solver that, at each step, chooses a
variable and recursively tries instantiating it with both `True` and `False`.
The algorithm should proceed like this:

1. First, check if the formula is either `satisfied` (returning an empty
valuation if so) or `falsified` (returning `Nothing`).  A formula has been
satisfied when it is satisfied by the empty valuation (i.e. we have already
instantiated enough variables in the formula that the others don't matter.)
Alternatively, a formula is `falsified` when, like `anotherUnsatFormula`, it
contains a clause with an empty disjunction.

2. Otherwise, choose one of the variables in the formula, instantiate
it with both `True` and `False`, and see if either of the resulting
formulae are satisfiable.  If so, add an appropriate binding for the
variable we instantiated to the resulting `Valuation` and return it.

IMPLEMENTATION NOTES:

  - Make sure that your definition of `falsified` doesn't rely on the formula
    being *completely* instantiated. It is possible to cut off large parts of the
    search space by identifying unsatifiable formula as soon as possible.
  - If your implementation determines that instantiating a variable with, say `True`
    produces a satisfying valuation, make sure that it does not also test whether
    instantiating that variable with `False` also works. You only need to find
    one valuation and can cut off the search at that point.
-}

sat1 :: Solver
sat1 = sat
  where
    sat = undefined

{-
To check that it works, QuickCheck the property
`prop_satResultSound sat1`, `prop_satResult sat1`, plus this one
that says that it should agree with our previous solver
(and any others that you can think of).
-}

prop_sat1 :: CNF -> Property
prop_sat1 s = property (Maybe.isJust (sat1 s) == Maybe.isJust (sat0 s))

{-
If you run this file, you'll see that `sat1` is significantly faster than `sat0`.
This is only the beginning. Modern SAT solvers employ a number of techniques
to speed up this process including unit propagation, pure literal elimination,
clause learning, and much more.
-}

------------------------------------------------------------------------------
-- All the tests in one convenient place:

quickCheckN :: Testable prop => Int -> prop -> IO ()
quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n}

main :: IO ()
main = do
  putStrLn "Unit tests:"
  _ <-
    runTestTT $
      TestList
        [ testCountVars,
          testVars,
          testGenVars,
          testGenCNF,
          testSatisfiedBy
        ]
  putStrLn "Quickcheck properties:"
  putStrLn "prop_unSatBy"
  quickCheckN 500 prop_unSatBy
  putStrLn "prop_satResultSound sat0"
  quickCheckN 500 $ prop_satResultSound sat0
  putStrLn "prop_satResultCorrect sat0"
  quickCheckN 500 $ prop_satResultCorrect sat0
  putStrLn "prop_instantiate"
  quickCheckN 500 prop_instantiate
  putStrLn "prop_sat1"
  quickCheckN 500 prop_sat1
  putStrLn "prop_satResultSound sat1"
  quickCheckN 500 $ prop_satResultSound sat1
  putStrLn "prop_satResultCorrect sat1"
  quickCheckN 500 $ prop_satResultCorrect sat1
