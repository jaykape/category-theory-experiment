module CategoryTheory.Functorial where

import Data.List (intercalate)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)

import CategoryTheory.Small

data FunctorMap = FunctorMap
  { fmSource   :: SmallCategory
  , fmTarget   :: SmallCategory
  , fmObjMap   :: Map ObjName ObjName
  , fmMorMap   :: Map MorName MorName
  } deriving (Eq, Show)

mapObject :: FunctorMap -> ObjName -> Maybe ObjName
mapObject f obj = M.lookup obj (fmObjMap f)

mapMorphism :: FunctorMap -> MorName -> Maybe MorName
mapMorphism f mor = M.lookup mor (fmMorMap f)

verifyFunctor :: FunctorMap -> [String]
verifyFunctor f =
  verifyCoverage f
    ++ verifyTyping f
    ++ verifyIdentityPreservation f
    ++ verifyCompositionPreservation f

verifyCoverage :: FunctorMap -> [String]
verifyCoverage f = objectErrors ++ morphismErrors
  where
    objectErrors =
      [ "Functor is missing an image for object " ++ obj ++ "."
      | obj <- allObjects (fmSource f)
      , M.notMember obj (fmObjMap f)
      ]

    morphismErrors =
      [ "Functor is missing an image for morphism " ++ mor ++ "."
      | mor <- map morName (allMorphisms (fmSource f))
      , M.notMember mor (fmMorMap f)
      ]

verifyTyping :: FunctorMap -> [String]
verifyTyping f = concatMap checkOne (allMorphisms (fmSource f))
  where
    checkOne mor =
      case ( mapObject f (dom mor)
           , mapObject f (cod mor)
           , mapMorphism f (morName mor) >>= lookupMorphism (fmTarget f)
           ) of
        (Just dom', Just cod', Just imageMor)
          | dom imageMor == dom' && cod imageMor == cod' -> []
          | otherwise ->
              [ "Functor sends " ++ morName mor ++ " to a morphism with the wrong source/target."
              ]
        _ -> ["Functor could not resolve the image of morphism " ++ morName mor ++ "."]

verifyIdentityPreservation :: FunctorMap -> [String]
verifyIdentityPreservation f =
  [ "Functor does not preserve the identity on object " ++ obj ++ "."
  | obj <- allObjects (fmSource f)
  , let sourceIdent = M.lookup obj (scIdentities (fmSource f))
  , let targetObj = mapObject f obj
  , let targetIdent = targetObj >>= (`M.lookup` scIdentities (fmTarget f))
  , let imageIdent = sourceIdent >>= mapMorphism f
  , imageIdent /= targetIdent
  ]

verifyCompositionPreservation :: FunctorMap -> [String]
verifyCompositionPreservation f = concatMap checkOne (M.toList (scCompose (fmSource f)))
  where
    target = fmTarget f
    checkOne ((g, h), gh) =
      case (mapMorphism f g, mapMorphism f h, mapMorphism f gh) of
        (Just g', Just h', Just gh') ->
          case composeNamed target g' h' of
            Just actual | actual == gh' -> []
            _ -> ["Functor does not preserve composition for " ++ g ++ " ∘ " ++ h ++ "."]
        _ -> ["Functor is missing data for composition check involving " ++ g ++ " and " ++ h ++ "."]

identityFunctor :: SmallCategory -> FunctorMap
identityFunctor cat = FunctorMap
  { fmSource = cat
  , fmTarget = cat
  , fmObjMap = M.fromList [(obj, obj) | obj <- allObjects cat]
  , fmMorMap = M.fromList [(morName mor, morName mor) | mor <- allMorphisms cat]
  }

composeFunctors :: FunctorMap -> FunctorMap -> Maybe FunctorMap
composeFunctors g f
  | fmTarget f /= fmSource g = Nothing
  | otherwise = Just FunctorMap
      { fmSource = fmSource f
      , fmTarget = fmTarget g
      , fmObjMap = M.mapMaybe (mapObject g) (fmObjMap f)
      , fmMorMap = M.mapMaybe (mapMorphism g) (fmMorMap f)
      }

ordinalInclusion :: Int -> Int -> Maybe FunctorMap
ordinalInclusion small big
  | small > big = Nothing
  | otherwise = Just FunctorMap
      { fmSource = finiteOrdinal small
      , fmTarget = finiteOrdinal big
      , fmObjMap = M.fromList [(show i, show i) | i <- [0 .. small - 1]]
      , fmMorMap = M.fromList
          [ (show i ++ "<=" ++ show j, show i ++ "<=" ++ show j)
          | i <- [0 .. small - 1]
          , j <- [i .. small - 1]
          ]
      }

ordinalShiftEndofunctor :: Int -> FunctorMap
ordinalShiftEndofunctor n = FunctorMap
  { fmSource = cat
  , fmTarget = cat
  , fmObjMap = M.fromList [(show i, show (shift i)) | i <- [0 .. n - 1]]
  , fmMorMap = M.fromList
      [ (name i j, name (shift i) (shift j))
      | i <- [0 .. n - 1]
      , j <- [i .. n - 1]
      ]
  }
  where
    cat = finiteOrdinal n
    shift i = min (n - 1) (i + 1)
    name i j = show i ++ "<=" ++ show j

data NaturalTransformation = NaturalTransformation
  { ntLeft       :: FunctorMap
  , ntRight      :: FunctorMap
  , ntComponents :: Map ObjName MorName
  } deriving (Eq, Show)

verifyNaturalTransformation :: NaturalTransformation -> [String]
verifyNaturalTransformation nt =
  verifyParallelFunctors nt
    ++ verifyComponentTyping nt
    ++ verifyNaturalitySquares nt

verifyParallelFunctors :: NaturalTransformation -> [String]
verifyParallelFunctors nt
  | fmSource (ntLeft nt) /= fmSource (ntRight nt) = ["Natural transformation uses functors with different sources."]
  | fmTarget (ntLeft nt) /= fmTarget (ntRight nt) = ["Natural transformation uses functors with different targets."]
  | otherwise = []

verifyComponentTyping :: NaturalTransformation -> [String]
verifyComponentTyping nt =
  [ "Component at object " ++ obj ++ " has the wrong source or target."
  | obj <- allObjects source
  , let component = M.lookup obj (ntComponents nt) >>= lookupMorphism target
  , let leftObj = mapObject (ntLeft nt) obj
  , let rightObj = mapObject (ntRight nt) obj
  , case (component, leftObj, rightObj) of
      (Just mor, Just a, Just b) -> dom mor /= a || cod mor /= b
      _ -> True
  ]
  where
    source = fmSource (ntLeft nt)
    target = fmTarget (ntLeft nt)

verifyNaturalitySquares :: NaturalTransformation -> [String]
verifyNaturalitySquares nt = concatMap checkOne (allMorphisms source)
  where
    source = fmSource (ntLeft nt)
    target = fmTarget (ntLeft nt)

    checkOne mor =
      case ( mapMorphism (ntLeft nt) (morName mor)
           , mapMorphism (ntRight nt) (morName mor)
           , M.lookup (dom mor) (ntComponents nt)
           , M.lookup (cod mor) (ntComponents nt)
           ) of
        (Just fMor, Just gMor, Just etaA, Just etaB) ->
          let leftSide = composeNamed target gMor etaA
              rightSide = composeNamed target etaB fMor
          in case (leftSide, rightSide) of
               (Just leftResult, Just rightResult) | leftResult == rightResult -> []
               _ -> ["Naturality square fails for morphism " ++ morName mor ++ "."]
        _ -> ["Natural transformation is missing data for morphism " ++ morName mor ++ "."]

pointwiseShift :: Int -> NaturalTransformation
pointwiseShift n = NaturalTransformation
  { ntLeft = identityFunctor cat
  , ntRight = ordinalShiftEndofunctor n
  , ntComponents = M.fromList [(show i, componentName i) | i <- [0 .. n - 1]]
  }
  where
    cat = finiteOrdinal n
    componentName i = show i ++ "<=" ++ show (min (n - 1) (i + 1))

prettyFunctor :: FunctorMap -> String
prettyFunctor f = unlines
  [ "Object map: " ++ intercalate ", " [a ++ " ↦ " ++ b | (a, b) <- M.toList (fmObjMap f)]
  , "Morphism map: " ++ intercalate ", " [a ++ " ↦ " ++ b | (a, b) <- M.toList (fmMorMap f)]
  ]

prettyNaturalTransformation :: NaturalTransformation -> String
prettyNaturalTransformation nt =
  "Components: " ++ intercalate ", " [obj ++ " ↦ " ++ mor | (obj, mor) <- M.toList (ntComponents nt)]
