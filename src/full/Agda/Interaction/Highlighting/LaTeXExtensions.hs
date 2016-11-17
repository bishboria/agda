module Agda.Interaction.Highlighting.LaTeXExtensions
  (
    writeHighlightingDataToFile
  , getReplacementDataFromFile
  , processNonCodeToken
  , processCodeToken
  , Replacements
  , ReplacementMap
  ) where

import Prelude hiding (null)

import Data.Function (on)
import qualified Data.HashMap.Strict as H
import Data.List hiding (null)
import Data.List.Split
import qualified Data.Map as Map
import System.Directory
import System.IO

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Internal
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TypeChecking.Monad
import Agda.Utils.Lens

----------
---------- for processing latex
----------

import qualified Data.List   as List
import Data.Text (Text)
import qualified Data.Text          as T



-------------
-------------
-- Exported type things
-------------
-------------

type Replacements   = [(String, String, String)]
type ReplacementMap = [(String,String)]



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
----- Exported functions
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

writeHighlightingDataToFile :: FilePath -> Interface -> IO ()
writeHighlightingDataToFile file i = do
   writeReplacementFile Col (map (\x -> fst x ++ "\t" ++ snd x)) (file ++ ".coloring") i
   writeReplacementFile Rep (map (\x -> fst x ++ "\t"))          (file ++ ".replacements") i

getReplacementDataFromFile :: FilePath -> IO Replacements
getReplacementDataFromFile file = do
  colors       <- readFile $ file ++ ".agdai.coloring"
  replacements <- readFile $ file ++ ".agdai.replacements"
  let sc = init $ map ((\l -> (head l, last l)) . splitOn "\t") $ splitOn "\n" colors
  let sr = init $ map ((\l -> (head l, last l)) . splitOn "\t") $ splitOn "\n" replacements
  let src = map (\p -> (fst $ fst p , snd $ fst p , snd p)) $ zip sr $ map snd sc
  let nonCodeReplacements = datatononcodereplacement src
  let codereplacements    = datatoreplacement sr
  let scnc = map (\p -> (fst p , fst $ snd p, snd $ snd p)) $ zip (map fst codereplacements) $ zip (map snd codereplacements) (map snd nonCodeReplacements)
  return scnc

processNonCodeToken :: Replacements -> Text -> Text
processNonCodeToken replacements = processNonCode' (strRep $ transformNonCode replacements)

processCodeToken :: Text -> Replacements -> Text
processCodeToken tok replacements = T.pack $ strRep (transformCode replacements) $ T.unpack tok

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
----- Stuff to make ^^ work
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

{-
  FIXME:
    - Use printing of sigSections in order to work out where the named arguments
      of constructors appear...
-}
writeReplacementFile :: OutFile -> (ReplacementMap -> [String]) -> FilePath -> Interface -> IO ()
writeReplacementFile outF extruder file i = do
  let nestedDefs   = H.toList $ iSignature i ^. sigDefinitions
      sectionNames = nub $ map (last . splitOn "." . show . fst) $ Map.toList $ iSignature i ^. sigSections
      process      = concat.map nub.groupBy ((==) `on` fst).sortBy (compare `on` fst).concat
      flattendDefs = process $ map showInterfaceFunc nestedDefs
      modules      = map (\x -> (x,"Module")) $ sectionNames \\ (map fst flattendDefs)
      defs         = extruder (modules ++ flattendDefs)
      finished     = unlines defs

  -- print "****************************** Definitions"
  -- print nestedDefs

  exists <- doesFileExist file
  if   exists
  then mergeFile outF file (modules ++ flattendDefs)
  else writeFile file finished

showInterfaceFunc :: (QName , Definition) -> [(String, String)]
showInterfaceFunc p = let x       = snd p
                          defn    = theDef x
                          defType = head $ splitOn " " $ show defn
                          name    = last $ splitOn "." $ show $ defName x
                          foo     = if defType == "Constructor" then "InductiveConstructor" else defType
                      in  (name , foo) : showDefn defn


{-
  FIXME:
    - I'm still missing named arguments to constructors
      - WHERE ARE THEY?
-}
showDefn :: Defn -> ReplacementMap
showDefn x = case x of
  (Function c _ _ _ _ _ _ _ _ _ _ _ _) -> showNamedClauses c
  _                                    -> []
  -- (Constructor a b c d e f)            -> [("CON A" , show a)
  --                                         ,("CON B" , show b)
  --                                         ,("CON C" , show c)
  --                                         ,("CON D" , show d)
  --                                         ,("CON E" , show e)
  --                                         ,("CON F" , show f)
  --                                         ]
  -- (Datatype a b c d e f g h i j)       -> [("DATATYPE A" , show a)
  --                                         ,("DATATYPE B" , show b)
  --                                         ,("DATATYPE C" , show c)
  --                                         ,("DATATYPE D" , show d)
  --                                         ,("DATATYPE E" , show e)
  --                                         ,("DATATYPE F" , show f)
  --                                         ,("DATATYPE G" , show g)
  --                                         ,("DATATYPE H" , show h)
  --                                         ,("DATATYPE I" , show i)
  --                                         ,("DATATYPE J" , show j)
  --                                         ]
  -- _                                    -> []


{-
  FIXME:

  Function needs to be improved:
    - Variables used in constructors aren't being written to file as 'Bound'
    - not outputting all things yet
      - NOTFINISHEDYET
      - SOMETHINGELSE
      - show r?

-}
showNamedClauses :: [Clause] -> ReplacementMap -- who,var
showNamedClauses []        = []
showNamedClauses (c : cs') = showClause c ++ showTerm c ++ showNamedClauses cs'
  where
    showClause = peelNames.namedClausePats
    showTerm c = case clauseBody c of
      Nothing -> []
      Just x  -> showT x

    showT (Var i xs) = showElims xs -- [("VAR " ++ show i ++ show xs , "BOUND")]
    showT (Lam _ t)  = [(absName t , "Bound")]
    showT (Def _ xs) = showElims xs
    showT (Pi d r)   = showDom d  -- show r?
    showT (Con h as) = showCon h ++ blargArgs as
    showT x          = [] -- [("NOTFINISHEDYET" , show x)]

    showElims []       = []
    showElims (e : es) = showElim e ++ showElims es

    showElim (Apply a) = showT $ unArg a
    showElim x         = [] -- [ ("SOMETHINGELSE", show x) ]

    showDom d = showT $ unEl $ unDom d

    showCon h = [(lastName h, "InductiveConstructor")]

    lastName = last . splitOn "." . show . conName

    blargArgs []       = []
    blargArgs (a : as) = (showT $ unArg a) ++ blargArgs as

    peelNames []       = []
    peelNames (p : ps) = let var = peelName p
                         in  if   var == "" || var == "="
                             then peelNames ps
                             else (var, "Bound") : peelNames ps

    -- this needs to be fixed so that empty strings, garbage, don't show up
    peelName = head.drop 1.splitOneOf "( ".show


mergeFile :: OutFile -> FilePath -> [(String,String)] -> IO ()
mergeFile outFile file unsaveddata = do
  filedata <- readFile file
  print filedata -- because lazy io.
  let saveddata = init $ map ((\l -> (head l, last l)) . splitOn "\t") $ splitOn "\n" filedata
  writeFile file $ toString $ merge outFile saveddata unsaveddata
    where
      toString []       = []
      toString (p : ps) = (fst p) ++ "\t" ++ (snd p) ++ "\n" ++ toString ps

merge :: OutFile -> ReplacementMap -> ReplacementMap -> ReplacementMap
merge outF [] ys = map (\p -> (fst p, if outF == Rep then "" else snd p)) ys
merge _ xs [] = xs
merge outF xss@((fx , sx) : xs) yss@((fy , sy) : ys) | fx == fy  = (fx , sx) : merge outF xs  ys
                                                     | fx < fy   = (fx , sx) : merge outF xs  yss
                                                     | otherwise = (fy , if outF == Rep then "" else sy) : merge outF xss ys

data OutFile = Col | Rep deriving (Eq)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-----
-----
----- LaTeX processing
-----
-----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

strRep :: ReplacementMap -> String -> String
strRep = flip $ List.foldl' replace
  where
    replace s (a,b) = let [ss,aa,bb] = [T.pack x | x <- [s,a,b]]
                      in  T.unpack $ T.replace aa bb ss

processNonCode' :: (String -> String) -> Text -> Text
processNonCode' f = T.pack . List.intercalate " " . map f . splitOn " " . T.unpack

wrap :: String -> String
wrap x = "$" ++ x ++ "$"

fstTrip :: (String,String,String) -> String
fstTrip (a,b,c) = a

sndTrip :: (String,String,String) -> String
sndTrip (a,b,c) = b

lstTrip :: (String,String,String) -> String
lstTrip (a,b,c) = c

transformNonCode :: Replacements -> ReplacementMap
transformNonCode replacements = zip (map (wrap.fstTrip) replacements) (map (wrap.lstTrip) replacements)

transformCode :: Replacements -> ReplacementMap
transformCode replacements = zip (map fstTrip replacements) (map sndTrip replacements)

datatononcodereplacement :: Replacements -> ReplacementMap
datatononcodereplacement [] = []
datatononcodereplacement ((sym , rep , color) : ps) =
  let r = if rep == "" then sym else rep
  in  (sym , "\\Agda"++color++"{"++r++"}") : datatononcodereplacement ps

datatoreplacement :: ReplacementMap -> ReplacementMap
datatoreplacement [] = []
datatoreplacement ((sym , rep) : rs) =
  (sym , if rep == "" then sym else rep) : datatoreplacement rs
