module CategoryTheory.Kleisli where

import Text.Read (readMaybe)

import CategoryTheory.Core

newtype KleisliC m a b = KleisliC { runKleisliC :: a -> m b }

instance Monad m => Cat (KleisliC m) where
  idC = KleisliC pure
  KleisliC g <<< KleisliC f = KleisliC (f >=> g)

(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >=> g = \a -> f a >>= g

liftPure :: Monad m => (a -> b) -> KleisliC m a b
liftPure f = KleisliC (pure . f)

iterateKleisli :: Monad m => Int -> KleisliC m a a -> KleisliC m a a
iterateKleisli n f
  | n <= 0 = idC
  | otherwise = foldr1 (<<<) (replicate n f)

safeReciprocal :: KleisliC Maybe Double Double
safeReciprocal = KleisliC $ \x ->
  if x == 0 then Nothing else Just (1 / x)

safeRoot :: KleisliC Maybe Double Double
safeRoot = KleisliC $ \x ->
  if x < 0 then Nothing else Just (sqrt x)

safeLogBase10 :: KleisliC Maybe Double Double
safeLogBase10 = KleisliC $ \x ->
  if x <= 0 then Nothing else Just (logBase 10 x)

maybePipeline :: KleisliC Maybe Double Double
maybePipeline = safeLogBase10 <<< safeRoot <<< safeReciprocal

runMaybePipeline :: Double -> Maybe Double
runMaybePipeline = runKleisliC maybePipeline

nondeterministicStep :: KleisliC [] Int Int
nondeterministicStep = KleisliC $ \x -> [x + 1, x * 2]

boundedStep :: Int -> KleisliC [] Int Int
boundedStep bound = KleisliC $ \x -> filter (<= bound) [x + 1, x * 2]

reachableIn :: Int -> Int -> Int -> [Int]
reachableIn steps bound start =
  runKleisliC (iterateKleisli steps (boundedStep bound)) start

parsePositiveInt :: KleisliC (Either String) String Int
parsePositiveInt = KleisliC $ \text ->
  case readMaybe text of
    Nothing -> Left ("Could not parse an integer from: " ++ show text)
    Just n
      | n > 0 -> Right n
      | otherwise -> Left "Expected a positive integer."

requireEven :: KleisliC (Either String) Int Int
requireEven = KleisliC $ \n ->
  if even n then Right n else Left "Expected an even integer."

invertInt :: KleisliC (Either String) Int Double
invertInt = KleisliC $ \n ->
  if n == 0 then Left "Cannot divide by zero."
  else Right (1 / fromIntegral n)

checkedComputation :: KleisliC (Either String) String Double
checkedComputation = invertInt <<< requireEven <<< parsePositiveInt

runCheckedComputation :: String -> Either String Double
runCheckedComputation = runKleisliC checkedComputation

normalizeWord :: KleisliC [] String String
normalizeWord = KleisliC $ \w ->
  [map toLowerAscii w, filter (/= '-') (map toLowerAscii w)]

splitOnSlash :: KleisliC [] String String
splitOnSlash = KleisliC $ \w -> wordsLikeSlash w

expandTokens :: String -> [String]
expandTokens = runKleisliC (splitOnSlash <<< normalizeWord)

wordsLikeSlash :: String -> [String]
wordsLikeSlash [] = [""]
wordsLikeSlash s = go s ""
  where
    go [] acc = [reverse acc]
    go ('/' : rest) acc = reverse acc : go rest ""
    go (c : rest) acc = go rest (c : acc)

toLowerAscii :: Char -> Char
toLowerAscii c
  | 'A' <= c && c <= 'Z' = toEnum (fromEnum c + 32)
  | otherwise = c
