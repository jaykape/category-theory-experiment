module CategoryTheory.Free where

import Data.List (intercalate, nub)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import CategoryTheory.Small

data Edge = Edge
  { edgeLabel  :: String
  , edgeFrom   :: ObjName
  , edgeTo     :: ObjName
  } deriving (Eq, Ord, Show)

newtype Path = Path { unPath :: [Edge] }
  deriving (Eq, Ord, Show)

identityPath :: ObjName -> Path
identityPath _ = Path []

singletonPath :: Edge -> Path
singletonPath edge = Path [edge]

pathLength :: Path -> Int
pathLength = length . unPath

pathSource :: ObjName -> Path -> ObjName
pathSource fallback (Path []) = fallback
pathSource _ (Path (edge : _)) = edgeFrom edge

pathTarget :: ObjName -> Path -> ObjName
pathTarget fallback (Path []) = fallback
pathTarget _ (Path edges) = edgeTo (last edges)

isComposableChain :: Path -> Bool
isComposableChain (Path []) = True
isComposableChain (Path [_]) = True
isComposableChain (Path (e1 : e2 : rest)) = edgeTo e1 == edgeFrom e2 && isComposableChain (Path (e2 : rest))

composePath :: Path -> Path -> Maybe Path
composePath (Path right) (Path left) =
  case (left, right) of
    ([], _) -> Just (Path right)
    (_, []) -> Just (Path left)
    _
      | edgeTo (last left) == edgeFrom (head right) -> Just (Path (left ++ right))
      | otherwise -> Nothing

pathName :: ObjName -> ObjName -> Path -> MorName
pathName src tgt (Path []) = "id_" ++ src
pathName src tgt (Path edges) = src ++ "-[" ++ intercalate ";" (map edgeLabel edges) ++ "]->" ++ tgt

prettyPath :: ObjName -> ObjName -> Path -> String
prettyPath src tgt path = pathName src tgt path

enumeratePaths :: Int -> [Edge] -> ObjName -> ObjName -> [Path]
enumeratePaths maxDepth edges start goal
  | maxDepth < 0 = []
  | otherwise = nub (basePaths ++ extendFrom start maxDepth)
  where
    basePaths = [identityPath start | start == goal]

    outgoing obj = [e | e <- edges, edgeFrom e == obj]

    extendFrom obj depth
      | depth == 0 = []
      | otherwise = do
          edge <- outgoing obj
          let target = edgeTo edge
          let tailPaths
                | target == goal = [Path []]
                | otherwise = extendFrom target (depth - 1)
          rest <- tailPaths
          pure $ case rest of
            Path [] -> singletonPath edge
            _ -> Path (edge : unPath rest)

allObjectsInGraph :: [Edge] -> [ObjName]
allObjectsInGraph edges = nub ([edgeFrom e | e <- edges] ++ [edgeTo e | e <- edges])

freeCategoryAsSmall :: Int -> [Edge] -> SmallCategory
freeCategoryAsSmall maxDepth edges =
  foldr addCompositionEntry catWithMorphisms compositionEntries
  where
    objects = allObjectsInGraph edges
    paths =
      [ (src, tgt, path)
      | src <- objects
      , tgt <- objects
      , path <- enumeratePaths maxDepth edges src tgt
      ]

    pathMorphisms =
      [ mkMorphism (pathName src tgt path) src tgt
      | (src, tgt, path) <- paths
      ]

    identityMap = M.fromList [(obj, pathName obj obj (identityPath obj)) | obj <- objects]

    catWithMorphisms =
      addMorphisms pathMorphisms emptyCategory
        { scObjects = S.fromList objects
        , scIdentities = identityMap
        }

    pathLookup = M.fromList [((src, tgt, pathName src tgt path), path) | (src, tgt, path) <- paths]

    compositionEntries = do
      (src1, mid1, name1, path1) <- lookupRows pathLookup
      (src2, tgt2, name2, path2) <- lookupRows pathLookup
      if tgt2 == src1
        then case composePath path1 path2 of
               Just composed
                 | pathLength composed <= maxDepth ->
                     let composedName = pathName src2 mid1 composed
                     in [(name1, name2, composedName)]
               _ -> []
        else []

    lookupRows lookupMap =
      [ (src, tgt, name, path)
      | ((src, tgt, name), path) <- M.toList lookupMap
      ]

    addCompositionEntry (g, f, h) cat = addComposition g f h cat

sampleGraph :: [Edge]
sampleGraph
  = [ Edge "f" "A" "B"
    , Edge "g" "B" "C"
    , Edge "h" "A" "C"
    , Edge "u" "C" "A"
    ]

sampleFreeCategory :: SmallCategory
sampleFreeCategory = freeCategoryAsSmall 3 sampleGraph

samplePathsFromAToC :: [String]
samplePathsFromAToC =
  [ prettyPath "A" "C" path
  | path <- enumeratePaths 3 sampleGraph "A" "C"
  ]

walksFrom :: Int -> [Edge] -> ObjName -> [String]
walksFrom maxDepth edges start =
  [ prettyPath start (pathTarget start path) path
  | path <- concat [enumeratePaths maxDepth edges start goal | goal <- allObjectsInGraph edges]
  ]
