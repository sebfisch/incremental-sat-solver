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
-- Davis-Putnam-Logemann-Loveland (DPLL) algorithm
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

  lookupVar, assertTrue, branchOnVar, satisfy, selectBranchVar

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
-- @Nothing@. We use @Int@s as variable names.
-- 
lookupVar :: Int -> SatSolver -> Maybe Bool
lookupVar name = IM.lookup name . bindings

-- | 
-- We can assert boolean formulas to update a @SatSolver@. The
-- assertion may fail if the resulting constraints are unsatisfiable.
-- 
assertTrue :: MonadPlus m => Boolean -> SatSolver -> m SatSolver
assertTrue formula solver =
  simplify (solver { clauses = booleanToCNF formula ++ clauses solver })

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
-- This function guesses values for variables such that the stored
-- constraints are satisfied. The result may be non-deterministic and
-- is, hence, returned in an instance of @MonadPlus@.
-- 
satisfy :: MonadPlus m => SatSolver -> m SatSolver
satisfy solver
  | isSolved solver = return solver
  | otherwise = branchOnUnbound (selectBranchVar solver) solver >>= satisfy

-- |
-- We select a variable from the shortest clause hoping to produce a
-- unit clause.
--
selectBranchVar :: SatSolver -> Int
selectBranchVar = literalVar . head . head . sortBy shorter . clauses


-- private helper functions

updateSolver :: CNF -> [(Int,Bool)] -> SatSolver -> SatSolver
updateSolver cs bs solver =
  solver { clauses  = cs,
           bindings = foldr (uncurry IM.insert) (bindings solver) bs }

simplify :: MonadPlus m => SatSolver -> m SatSolver
simplify solver = do
  (cs,bs) <- runWriterT . simplifyClauses . clauses $ solver
  return $ updateSolver cs bs solver

simplifyClauses :: MonadPlus m => CNF -> WriterT [(Int,Bool)] m CNF
simplifyClauses [] = return []
simplifyClauses clauses = do
  let shortestClause = head . sortBy shorter $ clauses
  guard (not (null shortestClause))
  if null (tail shortestClause)
   then propagate (head shortestClause) clauses >>= simplifyClauses
   else return clauses

propagate :: MonadPlus m => Literal -> CNF -> WriterT [(Int,Bool)] m CNF
propagate literal clauses = do
  tell [(literalVar literal, isPositiveLiteral literal)]
  return (foldr prop [] clauses)
 where
  prop c cs | literal `elem` c = cs
            | otherwise        = filter (invLiteral literal/=) c : cs

branchOnUnbound :: MonadPlus m => Int -> SatSolver -> m SatSolver
branchOnUnbound name solver =
  guess (Pos name) solver `mplus` guess (Neg name) solver

guess :: MonadPlus m => Literal -> SatSolver -> m SatSolver
guess literal solver = do
  (cs,bs) <- runWriterT (propagate literal (clauses solver) >>= simplifyClauses)
  return $ updateSolver cs bs solver

shorter :: [a] -> [a] -> Ordering
shorter []     []     = EQ
shorter []     _      = LT
shorter _      []     = GT
shorter (_:xs) (_:ys) = shorter xs ys


