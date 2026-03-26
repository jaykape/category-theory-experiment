module Main where

import Data.List (intercalate)

import CategoryTheory.Core
import CategoryTheory.Free
import CategoryTheory.Functorial
import CategoryTheory.Kleisli
import CategoryTheory.Small

section :: String -> IO ()
section title = do
  putStrLn ""
  putStrLn (replicate 72 '=')
  putStrLn title
  putStrLn (replicate 72 '=')

reportChecks :: [String] -> IO ()
reportChecks [] = putStrLn "All checks passed."
reportChecks errs = mapM_ putStrLn errs

coreDemo :: IO ()
coreDemo = do
  section "Core category experiments"
  let samples = [0 .. 10]
  putStrLn $ "Pipeline description: " ++ sampleNumericDescription
  putStrLn $ "Pipeline on [0..5]: " ++ show (runOnList sampleNumericPipeline [0 .. 5])
  putStrLn $ "Left identity holds on increment: " ++ show (leftIdentityLaw samples incrementH)
  putStrLn $ "Right identity holds on double: " ++ show (rightIdentityLaw samples doubleH)
  putStrLn $ "Associativity holds on increment/double/square: "
    ++ show (associativityLaw samples squareH doubleH incrementH)
  putStrLn $ "assocPair forwards ((1,2),3) to: " ++ show (runIso assocPair ((1 :: Int, 2 :: Int), 3 :: Int))
  putStrLn $ "swapPair backwards (True,'x') to: " ++ show (runInverseIso swapPair (True, 'x'))

smallCategoryDemo :: IO ()
smallCategoryDemo = do
  section "Finite categories"
  let ordinal4 = finiteOrdinal 4
  putStrLn "Ordinal category 4 (objects 0 <= 1 <= 2 <= 3):"
  putStrLn (prettyCategory ordinal4)
  putStrLn "Validation result:"
  reportChecks (verifyCategory ordinal4)

  let boolMonoid = monoidCategory "*" "False" ["False", "True"] op
      op g f = show ((read g :: Bool) || (read f :: Bool))
  putStrLn "Boolean OR as a one-object category:"
  putStrLn (prettyCategory boolMonoid)
  putStrLn "Validation result:"
  reportChecks (verifyCategory boolMonoid)

freeCategoryDemo :: IO ()
freeCategoryDemo = do
  section "Free category on a graph"
  putStrLn "Sample generating graph:"
  mapM_ print sampleGraph
  putStrLn "Some paths from A to C with depth <= 3:"
  mapM_ putStrLn samplePathsFromAToC
  putStrLn "Validation result for the bounded free category:"
  reportChecks (verifyCategory sampleFreeCategory)

functorDemo :: IO ()
functorDemo = do
  section "Functors and natural transformations"
  case ordinalInclusion 3 5 of
    Nothing -> putStrLn "Could not build inclusion functor."
    Just inclusion -> do
      putStrLn "Inclusion functor Ord(3) -> Ord(5):"
      putStrLn (prettyFunctor inclusion)
      putStrLn "Functor validation:"
      reportChecks (verifyFunctor inclusion)

  let shift = ordinalShiftEndofunctor 4
  putStrLn "Shift endofunctor on Ord(4):"
  putStrLn (prettyFunctor shift)
  putStrLn "Shift functor validation:"
  reportChecks (verifyFunctor shift)

  let eta = pointwiseShift 4
  putStrLn "Natural transformation Id => Shift on Ord(4):"
  putStrLn (prettyNaturalTransformation eta)
  putStrLn "Naturality validation:"
  reportChecks (verifyNaturalTransformation eta)

kleisliDemo :: IO ()
kleisliDemo = do
  section "Kleisli categories"
  putStrLn "Maybe pipeline results for [4, 1, 0, -1]:"
  mapM_ print [(x, runMaybePipeline x) | x <- [4, 1, 0, -1]]

  putStrLn "Reachable numbers from 1 in 4 bounded list-steps (bound 20):"
  print (reachableIn 4 20 1)

  putStrLn "Checked computation over Either String:"
  mapM_ print [(input, runCheckedComputation input) | input <- ["10", "7", "0", "hello"]]

  putStrLn "List-valued token expansion for category-theory-flavored names:"
  mapM_ print [(w, expandTokens w) | w <- ["Yoneda/Lemma", "Kleisli-Arrow", "Adjoint/Functor-Lab"]]

main :: IO ()
main = do
  section "categorical-lab"
  putStrLn "A tiny playground for experimenting with category theory in Haskell."
  putStrLn $ "Modules: " ++ intercalate ", "
    [ "Core"
    , "Small"
    , "Free"
    , "Functorial"
    , "Kleisli"
    ]
  coreDemo
  smallCategoryDemo
  freeCategoryDemo
  functorDemo
  kleisliDemo
