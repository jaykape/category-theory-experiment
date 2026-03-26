module CategoryTheory.Small where

import Data.List (intercalate, nub, sortBy)
import Data.Ord (comparing)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.Set as S
import Data.Set (Set)

import CategoryTheory.Core

type ObjName = String
type MorName = String

data Morphism = Morphism
  { morName :: MorName
  , dom     :: ObjName
  , cod     :: ObjName
  } deriving (Eq, Ord, Show)

data SmallCategory = SmallCategory
  { scObjects    :: Set ObjName
  , scMorphisms  :: Map MorName Morphism
  , scIdentities :: Map ObjName MorName
  , scCompose    :: Map (MorName, MorName) MorName
  } deriving (Eq, Show)

emptyCategory :: SmallCategory
emptyCategory = SmallCategory S.empty M.empty M.empty M.empty

mkMorphism :: MorName -> ObjName -> ObjName -> Morphism
mkMorphism = Morphism

addObject :: ObjName -> SmallCategory -> SmallCategory
addObject obj cat = cat { scObjects = S.insert obj (scObjects cat) }

addObjects :: [ObjName] -> SmallCategory -> SmallCategory
addObjects objs cat = cat { scObjects = S.union (S.fromList objs) (scObjects cat) }

addMorphism :: Morphism -> SmallCategory -> SmallCategory
addMorphism mor cat =
  cat
    { scObjects = S.insert (dom mor) $ S.insert (cod mor) (scObjects cat)
    , scMorphisms = M.insert (morName mor) mor (scMorphisms cat)
    }

addMorphisms :: [Morphism] -> SmallCategory -> SmallCategory
addMorphisms mors cat = foldr addMorphism cat mors

addIdentity :: ObjName -> MorName -> SmallCategory -> SmallCategory
addIdentity obj name cat =
  addMorphism (mkMorphism name obj obj) (cat
    { scIdentities = M.insert obj name (scIdentities cat) })

addComposition :: MorName -> MorName -> MorName -> SmallCategory -> SmallCategory
addComposition g f h cat = cat { scCompose = M.insert (g, f) h (scCompose cat) }

lookupMorphism :: SmallCategory -> MorName -> Maybe Morphism
lookupMorphism cat name = M.lookup name (scMorphisms cat)

sourceObject :: SmallCategory -> MorName -> Maybe ObjName
sourceObject cat name = dom <$> lookupMorphism cat name

targetObject :: SmallCategory -> MorName -> Maybe ObjName
targetObject cat name = cod <$> lookupMorphism cat name

allObjects :: SmallCategory -> [ObjName]
allObjects = sortBy compare . S.toList . scObjects

allMorphisms :: SmallCategory -> [Morphism]
allMorphisms cat = sortOnName (M.elems (scMorphisms cat))
  where
    sortOnName = sortByName
    sortByName = sortOn morName

sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn f = sortBy (comparing f)

homSet :: SmallCategory -> ObjName -> ObjName -> [MorName]
homSet cat a b =
  [ name
  | (name, mor) <- M.toList (scMorphisms cat)
  , dom mor == a
  , cod mor == b
  ]

outbound :: SmallCategory -> ObjName -> [MorName]
outbound cat a = [ name | (name, mor) <- M.toList (scMorphisms cat), dom mor == a ]

inbound :: SmallCategory -> ObjName -> [MorName]
inbound cat a = [ name | (name, mor) <- M.toList (scMorphisms cat), cod mor == a ]

composeNamed :: SmallCategory -> MorName -> MorName -> Maybe MorName
composeNamed cat g f = M.lookup (g, f) (scCompose cat)

verifyObjectsMentioned :: SmallCategory -> [String]
verifyObjectsMentioned cat =
  [ "Morphism " ++ name ++ " references an object outside the object set."
  | (name, mor) <- M.toList (scMorphisms cat)
  , not (S.member (dom mor) (scObjects cat) && S.member (cod mor) (scObjects cat))
  ]

verifyIdentities :: SmallCategory -> [String]
verifyIdentities cat =
  missing ++ mistyped ++ lawFailures
  where
    missing =
      [ "Missing identity for object " ++ obj ++ "."
      | obj <- allObjects cat
      , M.notMember obj (scIdentities cat)
      ]

    mistyped =
      [ "Identity " ++ name ++ " is not an endomorphism on " ++ obj ++ "."
      | (obj, name) <- M.toList (scIdentities cat)
      , case lookupMorphism cat name of
          Nothing -> True
          Just mor -> dom mor /= obj || cod mor /= obj
      ]

    lawFailures =
      [ msg
      | (obj, ident) <- M.toList (scIdentities cat)
      , mor <- outbound cat obj ++ inbound cat obj
      , msg <- checkIdentity obj ident mor
      ]

    checkIdentity obj ident mor =
      let leftCheck = do
            m <- lookupMorphism cat mor
            if cod m == obj
              then case composeNamed cat ident mor of
                     Just result | result == mor -> []
                     _ -> ["Left identity law fails for " ++ ident ++ " and " ++ mor ++ "."]
              else []
          rightCheck = do
            m <- lookupMorphism cat mor
            if dom m == obj
              then case composeNamed cat mor ident of
                     Just result | result == mor -> []
                     _ -> ["Right identity law fails for " ++ mor ++ " and " ++ ident ++ "."]
              else []
      in leftCheck ++ rightCheck

verifyCompositionsTyped :: SmallCategory -> [String]
verifyCompositionsTyped cat = concatMap checkOne (M.toList (scCompose cat))
  where
    checkOne ((g, f), h) =
      case (lookupMorphism cat g, lookupMorphism cat f, lookupMorphism cat h) of
        (Just gm, Just fm, Just hm) ->
          concat
            [ [ "Composition uses non-composable pair " ++ g ++ " ∘ " ++ f ++ "."
              | cod fm /= dom gm
              ]
            , [ "Composition result " ++ h ++ " has wrong source/target for " ++ g ++ " ∘ " ++ f ++ "."
              | dom hm /= dom fm || cod hm /= cod gm
              ]
            ]
        _ -> ["Composition table references unknown morphisms in " ++ g ++ " ∘ " ++ f ++ " = " ++ h ++ "."]

verifyAssociativity :: SmallCategory -> [String]
verifyAssociativity cat = nub . concat $ do
  f <- names
  g <- names
  h <- names
  pure (checkTriple h g f)
  where
    names = M.keys (scMorphisms cat)

    checkTriple h g f =
      case (lookupMorphism cat h, lookupMorphism cat g, lookupMorphism cat f) of
        (Just hm, Just gm, Just fm)
          | cod fm == dom gm && cod gm == dom hm ->
              let left = composeNamed cat h g >>= \hg -> composeNamed cat hg f
                  right = composeNamed cat g f >>= \gf -> composeNamed cat h gf
              in case (left, right) of
                   (Just a, Just b) | a == b -> []
                   _ -> ["Associativity fails for triple (" ++ h ++ ", " ++ g ++ ", " ++ f ++ ")."]
        _ -> []

verifyCategory :: SmallCategory -> [String]
verifyCategory cat =
  verifyObjectsMentioned cat
    ++ verifyIdentities cat
    ++ verifyCompositionsTyped cat
    ++ verifyAssociativity cat

isValidCategory :: SmallCategory -> Bool
isValidCategory = null . verifyCategory

prettyCategory :: SmallCategory -> String
prettyCategory cat = unlines
  [ "Objects: " ++ intercalate ", " (allObjects cat)
  , "Morphisms:"
  ]
  ++ unlines
      [ "  - " ++ morName mor ++ " : " ++ dom mor ++ " -> " ++ cod mor
      | mor <- sortOn morName (M.elems (scMorphisms cat))
      ]
  ++ unlines
      [ "Identities: " ++ intercalate ", " [obj ++ " ↦ " ++ ident | (obj, ident) <- sortOn fst (M.toList (scIdentities cat))]
      , "Compositions:"
      ]
  ++ unlines
      [ "  - " ++ g ++ " ∘ " ++ f ++ " = " ++ h
      | ((g, f), h) <- sortOn fst (M.toList (scCompose cat))
      ]

discreteCategory :: [ObjName] -> SmallCategory
discreteCategory objs =
  foldr addIdentityWithLaw base uniqueObjs
  where
    uniqueObjs = nub objs
    base = addObjects uniqueObjs emptyCategory
    addIdentityWithLaw obj cat =
      let ident = "id_" ++ obj
      in addComposition ident ident ident (addIdentity obj ident cat)

finiteOrdinal :: Int -> SmallCategory
finiteOrdinal n
  | n <= 0 = emptyCategory
  | otherwise = foldr addAllCompositions catWithMorphisms allPairs
  where
    objs = map show [0 .. n - 1]
    pairs = [(i, j) | i <- [0 .. n - 1], j <- [i .. n - 1]]
    morFor i j = show i ++ "<=" ++ show j
    morphisms = [mkMorphism (morFor i j) (show i) (show j) | (i, j) <- pairs]
    identities = [(show i, morFor i i) | i <- [0 .. n - 1]]

    catWithMorphisms =
      addMorphisms morphisms emptyCategory
        { scObjects = S.fromList objs
        , scIdentities = M.fromList identities
        }

    allPairs =
      [ ((j, k), (i, j))
      | i <- [0 .. n - 1]
      , j <- [i .. n - 1]
      , k <- [j .. n - 1]
      ]

    addAllCompositions ((j, k), (i, j)) cat =
      addComposition (morFor j k) (morFor i j) (morFor i k) cat

monoidCategory :: ObjName -> MorName -> [MorName] -> (MorName -> MorName -> MorName) -> SmallCategory
monoidCategory objectLabel identityElement elements op =
  foldr addAllCompositions catWithMorphisms pairs
  where
    unique = nub elements
    morphisms = [mkMorphism name objectLabel objectLabel | name <- unique]
    catWithMorphisms =
      addMorphisms morphisms emptyCategory
        { scObjects = S.singleton objectLabel
        , scIdentities = M.singleton objectLabel identityElement
        }
    pairs = [(g, f) | g <- unique, f <- unique]
    addAllCompositions (g, f) cat = addComposition g f (op g f) cat

oppositeCategory :: SmallCategory -> SmallCategory
oppositeCategory cat =
  SmallCategory
    { scObjects = scObjects cat
    , scMorphisms = M.map reverseMorphism (scMorphisms cat)
    , scIdentities = scIdentities cat
    , scCompose = M.fromList [((f, g), h) | ((g, f), h) <- M.toList (scCompose cat)]
    }
  where
    reverseMorphism mor = mor { dom = cod mor, cod = dom mor }
