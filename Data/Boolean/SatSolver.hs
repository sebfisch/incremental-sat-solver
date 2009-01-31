-- |
-- Module      : Data.Boolean.SatSolver
-- Copyright   : Sebastian Fischer
-- License     : BSD3
-- 
-- Maintainer  : Sebastian Fischer (sebf@informatik.uni-kiel.de)
-- Stability   : experimental
-- Portability : portable
-- 
-- This Haskell library provides an implementation of the
-- Davis-Putnam-Logemann-Loveland algorithm
-- (cf. <http://en.wikipedia.org/wiki/DPLL_algorithm>) for the boolean
-- satisfiability problem. It not only allows to solve boolean
-- formulas in one go but also to add constraints and query bindings
-- of variables incrementally.
-- 
-- The implementation is not sophisticated at all but uses the basic
-- DPLL algorithm with unit propagation.
-- 
module Data.Boolean.SatSolver (

  Boolean(..), SatSolver,

  newSatSolver, isSolved, 

  lookupVar, assertTrue, branchOnVar, selectBranchVar, solve, isSolvable

  ) where

import Data.List
import Data.Boolean

import Control.Monad.Writer

import qualified Data.IntMap as IM

-- | A @SatSolver@ can be used to solve boolean formulas.
-- 
data SatSolver = SatSolver { clauses :: CNF, bindings :: IM.IntMap Bool }
 deriving Show

-- | A new SAT solver without stored constraints.
-- 
newSatSolver :: SatSolver
newSatSolver = SatSolver [] IM.empty

-- | This predicate tells whether all constraints are solved.
-- 
isSolved :: SatSolver -> Bool
isSolved = null . clauses

-- |
-- We can lookup the binding of a variable according to the currently
-- stored constraints. If the variable is unbound, the result is
-- @Nothing@.
-- 
lookupVar :: Int -> SatSolver -> Maybe Bool
lookupVar name = IM.lookup name . bindings

-- | 
-- We can assert boolean formulas to update a @SatSolver@. The
-- assertion may fail if the resulting constraints are unsatisfiable.
-- 
assertTrue :: MonadPlus m => Boolean -> SatSolver -> m SatSolver
assertTrue formula solver = do
  newClauses <- foldl (addClause (bindings solver))
                      (return (clauses solver))
                      (booleanToCNF formula)
  simplify (solver { clauses = newClauses })

-- |
-- This function guesses a value for the given variable, if it is
-- currently unbound. As this is a non-deterministic operation, the
-- resulting solvers are returned in an instance of @MonadPlus@.
-- 
branchOnVar :: MonadPlus m => Int -> SatSolver -> m SatSolver
branchOnVar name solver =
  maybe (branchOnUnbound name solver)
        (const (return solver))
        (lookupVar name solver)

-- |
-- We select a variable from the shortest clause hoping to produce a
-- unit clause.
--
selectBranchVar :: SatSolver -> Int
selectBranchVar = literalVar . head . head . sortBy shorter . clauses

-- | 
-- This function guesses values for variables such that the stored
-- constraints are satisfied. The result may be non-deterministic and
-- is, hence, returned in an instance of @MonadPlus@.
-- 
solve :: MonadPlus m => SatSolver -> m SatSolver
solve solver
  | isSolved solver = return solver
  | otherwise = branchOnUnbound (selectBranchVar solver) solver >>= solve

-- |
-- This predicate tells whether the stored constraints are
-- solvable. Use with care! This might be an inefficient operation. It
-- tries to find a solution using backtracking and returns @True@ if
-- and only if that fails.
-- 
isSolvable :: SatSolver -> Bool
isSolvable = not . null . solve


-- private helper functions

addClause :: MonadPlus m => IM.IntMap Bool -> m [Clause] -> Clause -> m [Clause]
addClause binds mclauses newClause = do
  oldClauses <- mclauses
  let unboundLits = foldl (addUnbound binds) (Just []) newClause
  maybe (return oldClauses)
        (\lits -> guard (not (null lits)) >> return (lits:oldClauses))
        unboundLits

addUnbound :: IM.IntMap Bool -> Maybe Clause -> Literal -> Maybe Clause
addUnbound binds mlits lit = do
  lits <- mlits
  maybe (Just (lit:lits))
        (\b -> guard (b /= isPositiveLiteral lit) >> return lits)
        (IM.lookup (literalVar lit) binds)

updateSolver :: MonadPlus m => CNF -> [(Int,Bool)] -> SatSolver -> m SatSolver
updateSolver cs bs solver = do
  bs' <- foldr (uncurry insertBinding) (return (bindings solver)) bs
  return $ solver { clauses = cs, bindings = bs' }

insertBinding :: MonadPlus m
              => Int -> Bool -> m (IM.IntMap Bool) -> m (IM.IntMap Bool)
insertBinding name newValue binds = do
  bs <- binds
  maybe (return (IM.insert name newValue bs))
        (\oldValue -> do guard (oldValue==newValue); return bs)
        (IM.lookup name bs)

simplify :: MonadPlus m => SatSolver -> m SatSolver
simplify solver = do
  (cs,bs) <- runWriterT . simplifyClauses . clauses $ solver
  updateSolver cs bs solver

simplifyClauses :: MonadPlus m => CNF -> WriterT [(Int,Bool)] m CNF
simplifyClauses [] = return []
simplifyClauses allClauses = do
  let shortestClause = head . sortBy shorter $ allClauses
  guard (not (null shortestClause))
  if null (tail shortestClause)
   then propagate (head shortestClause) allClauses >>= simplifyClauses
   else return allClauses

propagate :: MonadPlus m => Literal -> CNF -> WriterT [(Int,Bool)] m CNF
propagate literal allClauses = do
  tell [(literalVar literal, isPositiveLiteral literal)]
  return (foldr prop [] allClauses)
 where
  prop c cs | literal `elem` c = cs
            | otherwise        = filter (invLiteral literal/=) c : cs

branchOnUnbound :: MonadPlus m => Int -> SatSolver -> m SatSolver
branchOnUnbound name solver =
  guess (Pos name) solver `mplus` guess (Neg name) solver

guess :: MonadPlus m => Literal -> SatSolver -> m SatSolver
guess literal solver = do
  (cs,bs) <- runWriterT (propagate literal (clauses solver) >>= simplifyClauses)
  updateSolver cs bs solver

shorter :: [a] -> [a] -> Ordering
shorter []     []     = EQ
shorter []     _      = LT
shorter _      []     = GT
shorter (_:xs) (_:ys) = shorter xs ys


