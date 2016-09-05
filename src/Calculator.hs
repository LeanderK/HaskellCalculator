module Calculator
    ( doCalc
    ) where

import Data.List.Split
import Text.Read
import Data.Matrix
import Control.Monad as M
import Data.Vector as Vec (toList, replicate, zipWith, Vector, (//), map, fromList)
import Debug.Trace
import Text.Printf

-- | an input Line
data Line = Line [Integer]

-- | takes a square-matrix, the result-vector and solves the linear system
doCalc :: IO ()
doCalc = do
  putStrLn "give me your matrix!"
  matrixLine1String <- getLine
  let matrixLine1 = parseLine matrixLine1String
  case matrixLine1 of
    Right firstLine -> do
      matrixLinesString <- M.replicateM (lineLength firstLine - 1) getLine
      let maybeMatrix = constructMatrix firstLine matrixLinesString
      case maybeMatrix of
        Right matrix -> do
          putStrLn "whats the result-Vector?"
          resultString <- getLine
          let result = parseValidateResult resultString firstLine
          case result of
            Right (Line x) ->
                case solve matrix x of
                  Right result -> putStrLn ("result:" ++ show result)
                  Left x -> putStrLn x
            Left x -> putStrLn x
        Left x -> putStrLn x
    Left x -> putStrLn x

-- | parses a line and validates that it has the same lenght as the first line
parseValidateResult :: String -> Line -> Either String Line
parseValidateResult input (Line firstLine) = do
  result <- parseLine input
  let valid = lineLength result == length firstLine
  if valid
    then Right result
    else Left "invalid result vector lenght"

-- | parses a line
parseLine :: String -> Either String Line
parseLine x = fmap Line (listToInt $ splitOn " " x)

lineLength :: Line -> Int
lineLength (Line x) = length x

listToInt :: [String] -> Either String [Integer]
listToInt strings = case M.mapM (\x -> readMaybe x :: Maybe Integer) strings of
  Just list -> Right list
  Nothing -> Left "only integers allowed, sry!"

-- | constructs a matrix from the first line and remaining input
constructMatrix :: Line -> [String] -> Either String (Matrix Float)
constructMatrix (Line firstLine) matrixLinesString = do
  remainingLines <- M.mapM (flip parseValidateResult $ Line firstLine) matrixLinesString
  let matchesLinesAmount = length remainingLines == (length firstLine - 1)
  let valid = matchesLinesAmount && not (null firstLine)
  if valid
    then Right (getMatrix (firstLine : Prelude.map (\(Line x) -> x) remainingLines))
    else Left "the matrix is not valid"

getMatrix :: [[Integer]] -> Matrix Float
getMatrix xs = fromLists $ (Prelude.map . Prelude.map) fromIntegral xs

-- | takes a linear system and solves it if it is unique solvable
solve :: Matrix Float -> [Integer] -> Either String [Float]
solve m b =
  let (u, l, p) = decompose m
      trace = Debug.Trace.trace ("decomp: \n u: " ++ show u ++ "\n l: " ++ show l ++ "\n p: " ++ show p) u
  in
    if determinante u l p == 0.0
      then Left "no unique solution for the equation system does exist"
      else Right (solveLower l (solveUpper u (permutate p b)))

-- | takes a permutation matrix and a vector and permutates the verctor
permutate :: Matrix Float -> [Integer] -> [Float]
permutate m b = permHelp m (Vec.fromList $ Prelude.map fromIntegral b) 0 []
    where permHelp m b i r
           | i == nrows m = r
           | otherwise = permHelp m b (i + 1) (sumFloat (Vec.zipWith (*) (getRow (nrows m - i) m) b) : r)

solveUpper :: Matrix Float -> [Float] -> [Float]
solveUpper u b = Vec.toList $ solveMatrix u 0 (\x -> nrows u - x) (reverse b) (Vec.replicate (nrows u) 0.0)

solveLower :: Matrix Float -> [Float] -> [Float]
solveLower u b = Vec.toList $ solveMatrix u 0 (+ 1) b (Vec.replicate (nrows u) 0.0)

-- | solves the linear system A*x=b for x recoursivly
solveMatrix :: Matrix Float -- ^ the linear system (A), must be an upper or lower triangular matrix
               -> Int -- ^ the current step
               -> (Int -> Int) -- ^ function that takes the spep and produces an matrix index
               -> [Float] -- ^ the ouput (b)
               -> Vector Float -- ^ the (maybe paritally solved) x vector
               -> Vector Float
solveMatrix u i getMatrixIndex (b : bs) r =
  let index = getMatrixIndex i
      (vecIndex, new) = (index - 1, calc u index b r)
      trace = Debug.Trace.trace (printf "Vec: %s, replace (%d, %f)" (show r) vecIndex new) vecIndex in
  solveMatrix u (i + 1) getMatrixIndex bs (r // [(vecIndex, new)])
solveMatrix _ _ _ [] r = r

-- | calculates (b_i - sum a_ij*x_j)/a_ii
calc :: Matrix Float -> Int -> Float -> Vector Float -> Float
calc u i b r =
  let sum = sumFloat (Vec.zipWith (*) (getRow i u) r)
      res = unsafeGet i i u
      trace = Debug.Trace.trace (printf "Step %d: (%f - %f)/%f" i b sum res) b
      calcRes = (b - sum)/ res
      trace2 = Debug.Trace.trace (printf "Res Step %d: %f" i calcRes) calcRes in
      calcRes

sumFloat :: Vector Float -> Float
sumFloat = foldr (+) 0.0

-- | computes the determinante for A = P^-1*L*U
determinante :: Matrix Float -> Matrix Float -> Matrix Float -> Float
determinante u l p = ((-1) ^ nrows p) * getDiagonalProduct u * getDiagonalProduct l
  where getDiagonalProduct m = product $ Prelude.map (\i -> getElem i i m) [1..nrows m]

-- | performes an LU decomposition using partial pivoting
decompose :: Matrix Float -> (Matrix Float, Matrix Float, Matrix Float)
decompose input = recDecomp input (identity $ nrows input) (identity $ nrows input) 1

recDecomp :: Matrix Float -- ^ the input matrix A in step 1 or the upper matrix in step n
          -> Matrix Float -- ^ the lower matrix
          -> Matrix Float -- ^ the permutation matrix
          -> Int -- ^ the permutation matrix
          -> (Matrix Float, Matrix Float, Matrix Float) -- ^ (u,l,p)
recDecomp u l p i = if i > nrows u
  then (u, l, p)
  else recDecomp nu nl sp (i+1)
  where
    (su, sl, sp) = swapLargestRow u l p i
    pivot = getElem i i su
    koeffVec = Prelude.map (\(index, val) -> (index, val/pivot)) $ drop i ( zip [1..] ( Vec.toList $ getCol i su))
    nu = foldr (eliminateFromUpper i) su koeffVec
    nl = foldr (\(index, koeff) sl -> setElem koeff (index, i) sl) sl koeffVec


-- | adds the pivot-row x-times to the specified row
eliminateFromUpper :: Int -- ^ input
                    -> (Int, Float) -- ^ (index, koeff)
                    -> Matrix Float -> Matrix Float
eliminateFromUpper piv (_, 0) tmpU = tmpU
eliminateFromUpper piv (index, koeff) tmpU = combineRows index (-1 * koeff) piv tmpU

swapLargestRow :: Matrix Float -> Matrix Float -> Matrix Float -> Int -> (Matrix Float, Matrix Float, Matrix Float)
swapLargestRow u l p i = (swapMatrix u, l, swapMatrix p)
  where
    swapMatrix = switchRows i getLargestRowIndex
    getLargestRowIndex = fst $ foldr1 compareForLargest $ drop (i - 1) $ zip [1..] $ Vec.toList $ getCol i u
    compareForLargest (xIndex, xVal) (yIndex, yVal) = if xVal > yVal
      then (xIndex, xVal)
      else (yIndex, yVal)
