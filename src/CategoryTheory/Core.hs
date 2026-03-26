module CategoryTheory.Core where

import Data.List (intercalate)

infixr 9 <<<

-- | A very small category interface used throughout the repo.
class Cat k where
  idC :: k a a
  (<<<) :: k b c -> k a b -> k a c

-- | The ordinary category of Haskell functions.
newtype Hask a b = Hask { runHask :: a -> b }

instance Cat Hask where
  idC = Hask id
  Hask g <<< Hask f = Hask (g . f)

-- | Reverse the direction of a category.
newtype Op k a b = Op { getOp :: k b a }

instance Cat k => Cat (Op k) where
  idC = Op idC
  Op f <<< Op g = Op (g <<< f)

-- | Product of two categories over the same objects.
data ProductCat k l a b = ProductCat
  { leftComponent :: k a b
  , rightComponent :: l a b
  }

instance (Cat k, Cat l) => Cat (ProductCat k l) where
  idC = ProductCat idC idC
  ProductCat g1 g2 <<< ProductCat f1 f2 = ProductCat (g1 <<< f1) (g2 <<< f2)

-- | An isomorphism in an arbitrary category.
data Iso k a b = Iso
  { to   :: k a b
  , from :: k b a
  }

invertIso :: Iso k a b -> Iso k b a
invertIso (Iso f g) = Iso g f

composeIso :: Cat k => Iso k b c -> Iso k a b -> Iso k a c
composeIso (Iso f g) (Iso h i) = Iso (f <<< h) (i <<< g)

runIso :: Iso Hask a b -> a -> b
runIso (Iso f _) = runHask f

runInverseIso :: Iso Hask a b -> b -> a
runInverseIso (Iso _ g) = runHask g

assocPair :: Iso Hask ((a, b), c) (a, (b, c))
assocPair = Iso
  { to = Hask $ \((a, b), c) -> (a, (b, c))
  , from = Hask $ \(a, (b, c)) -> ((a, b), c)
  }

swapPair :: Iso Hask (a, b) (b, a)
swapPair = Iso
  { to = Hask $ \(a, b) -> (b, a)
  , from = Hask $ \(b, a) -> (a, b)
  }

duplicate :: Hask a (a, a)
duplicate = Hask $ \a -> (a, a)

firstH :: Hask a b -> Hask (a, c) (b, c)
firstH (Hask f) = Hask $ \(a, c) -> (f a, c)

secondH :: Hask a b -> Hask (c, a) (c, b)
secondH (Hask f) = Hask $ \(c, a) -> (c, f a)

fanout :: Hask a b -> Hask a c -> Hask a (b, c)
fanout (Hask f) (Hask g) = Hask $ \a -> (f a, g a)

curryH :: Hask ((a, b)) c -> Hask a (b -> c)
curryH (Hask f) = Hask $ \a -> \b -> f (a, b)

uncurryH :: Hask a (b -> c) -> Hask (a, b) c
uncurryH (Hask f) = Hask $ \(a, b) -> f a b

evalH :: Hask (a -> b, a) b
evalH = Hask $ \(f, a) -> f a

-- | Extensional equality on a finite list of samples.
extensionalEq :: Eq b => [a] -> Hask a b -> Hask a b -> Bool
extensionalEq samples (Hask f) (Hask g) = all (\x -> f x == g x) samples

leftIdentityLaw :: Eq b => [a] -> Hask a b -> Bool
leftIdentityLaw samples f = extensionalEq samples (idC <<< f) f

rightIdentityLaw :: Eq b => [a] -> Hask a b -> Bool
rightIdentityLaw samples f = extensionalEq samples (f <<< idC) f

associativityLaw :: Eq d => [a] -> Hask c d -> Hask b c -> Hask a b -> Bool
associativityLaw samples h g f =
  extensionalEq samples ((h <<< g) <<< f) (h <<< (g <<< f))

endoPower :: Cat k => Int -> k a a -> k a a
endoPower n f
  | n <= 0 = idC
  | otherwise = foldr1 (<<<) (replicate n f)

chainH :: [Hask a a] -> Hask a a
chainH [] = idC
chainH fs = foldr1 (<<<) fs

prettyPipeline :: [String] -> String
prettyPipeline = intercalate " <<< "

incrementH :: Hask Int Int
incrementH = Hask (+ 1)

doubleH :: Hask Int Int
doubleH = Hask (* 2)

squareH :: Hask Int Int
squareH = Hask (\x -> x * x)

stringifyH :: Hask Int String
stringifyH = Hask show

sampleNumericPipeline :: Hask Int String
sampleNumericPipeline = stringifyH <<< squareH <<< doubleH <<< incrementH

sampleNumericDescription :: String
sampleNumericDescription = prettyPipeline ["show", "square", "double", "(+1)"]

runOnList :: Hask a b -> [a] -> [b]
runOnList (Hask f) = map f
