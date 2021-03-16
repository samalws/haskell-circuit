import Data.Maybe


-- random helper functions

zipPartial :: [a] -> [b] -> [(a,b)]
zipPartial [] [] = []
zipPartial (x:xr) (y:yr) = (x,y):(zipPartial xr yr)

mapLookupPartial :: Eq a => [a] -> [(a,b)] -> [b]
mapLookupPartial x y = map fromJust $ map (\z -> lookup z y) x

applyOutputs :: [a] -> [b] -> [(a,b)] -> [(a,b)]
applyOutputs x y e = (zipPartial x y) ++ e

_incBoolsPartial :: [Bool] -> [Bool]
_incBoolsPartial (False:rest) = (True:rest)
_incBoolsPartial (True:rest)  = (False:(_incBoolsPartial rest))

incBoolsPartial :: [Bool] -> [Bool]
incBoolsPartial = reverse . _incBoolsPartial . reverse

_boolCounter :: Int -> [Bool] -> [[Bool]]
_boolCounter 0 _ = []
_boolCounter n x = x:(_boolCounter (n-1) (incBoolsPartial x))

boolCounter :: Int -> [[Bool]]
boolCounter n = _boolCounter (2^n) (replicate n False)

showBools :: [Bool] -> String
showBools = map (\x -> if x then '1' else '0')

countToPrefixed :: String -> Int -> [String]
countToPrefixed s n = map (s ++) $ map show [1..n]

boolsToInt :: [Bool] -> Int
boolsToInt [] = 0
boolsToInt (h:t) = (if h then (2^(length t)) else 0) + (boolsToInt t)


-- combinatorial circuit

data CombCircuit = GND | NAND | NET [(CombCircuit,[String],[String])] [String] [String] deriving Show


-- evaluating combinatorial circuits

evalNet :: [(String,Bool)] -> [String] -> [(CombCircuit,[String],[String])] -> [Bool]
evalNet env otps [] = mapLookupPartial otps env
evalNet env otps ((c,inp,out):rest) = evalNet newEnv otps rest where
  newEnv = applyOutputs out outVals env
  outVals = evalComb c $ mapLookupPartial inp env

evalComb :: CombCircuit -> [Bool] -> [Bool]
evalComb GND [] = [False]
evalComb NAND (a:(b:[])) = [not (a && b)]
evalComb (NET elems inpNames otps) inpVals = evalNet (zipPartial inpNames inpVals) otps elems


-- truth table stuff

makeFnTruthTable :: ([Bool] -> [Bool]) -> Int -> [([Bool],[Bool])]
makeFnTruthTable f n = zipPartial cnt $ map f cnt where cnt = boolCounter n

makeTruthTable :: CombCircuit -> Int -> [([Bool],[Bool])]
makeTruthTable c n = makeFnTruthTable (evalComb c) n

showTruthTable :: [([Bool],[Bool])] -> String
showTruthTable = foldr (++) "" . map (++ "\n") . map (\(a,b) -> showBools a ++ " " ++ showBools b)

printTruthTable :: CombCircuit -> Int -> IO ()
printTruthTable c n = putStrLn $ showTruthTable $ makeTruthTable c n

checkBehavior :: CombCircuit -> ([Bool] -> [Bool]) -> Int -> Bool
checkBehavior c f n = and $ map (\(a,b) -> a == b) $ zipPartial (makeTruthTable c n) (makeFnTruthTable f n)


-- gate utilities

comp :: CombCircuit -> CombCircuit -> Int -> Int -> Int -> CombCircuit
comp c1 c2 n1 n2 n3 = NET [(c1,v1,v2),(c2,v2,v3)] v1 v3 where
  v1 = countToPrefixed "a" n1
  v2 = countToPrefixed "b" n2
  v3 = countToPrefixed "c" n3

-- only use on monoid 2-input gates
-- does a thing like ((A + B) + C) + D
-- n is number of inputs
combN :: CombCircuit -> Int -> CombCircuit
combN c 2 = c
combN c n = NET [(cc,v,["b"]),(c,["x","b"],["c"])] i ["c"] where
  cc = combN c (n-1)
  v = countToPrefixed "a" (n-1)
  i = "x":v

-- does bitwise combination
combNIndividually :: CombCircuit -> Int -> CombCircuit
combNIndividually c 1 = c
combNIndividually c n = NET [(c,["a","b"],["c"]),(combNIndividually c (n-1),i1++i2,o)] (["a"]++i1++["b"]++i2) ("c":o) where
  i1 = countToPrefixed "a" (n-1)
  i2 = countToPrefixed "b" (n-1)
  o =  countToPrefixed "o" (n-1)


-- basic logic gates

inv :: CombCircuit
inv = NET [(NAND,["a","a"],["na"])] ["a"] ["na"]

invN :: Int -> CombCircuit
invN n = NET c i o where
  c = map (\nn -> (inv,['i':(show nn)],['o':(show nn)])) [1..n]
  i = countToPrefixed "i" n
  o = countToPrefixed "o" n

true :: CombCircuit
true = comp GND inv 0 1 1

const1 :: Bool -> CombCircuit
const1 b = if b then true else GND

constN :: [Bool] -> CombCircuit
constN bs = NET c [] o where
  o = countToPrefixed "o" $ length bs
  c = map (\(b,n) -> (const1 b,[],[n])) $ zipPartial bs o

-- feed values into a circuit, optionally having some remaining arguments put on end
feedVals :: CombCircuit -> [Bool] -> Int -> Int -> CombCircuit
feedVals c bs remaining outNum = NET [(constN bs,[],v1),(c,v1++v2,v3)] v2 v3 where
  v1 = countToPrefixed "a" $ length bs
  v2 = countToPrefixed "b" remaining
  v3 = countToPrefixed "o" outNum

-- ditto but remaining arguments put at beginning
feedValsEnd :: CombCircuit -> [Bool] -> Int -> Int -> CombCircuit
feedValsEnd c bs remaining outNum = NET [(constN bs,[],v1),(c,v2++v1,v3)] v2 v3 where
  v1 = countToPrefixed "a" $ length bs
  v2 = countToPrefixed "b" remaining
  v3 = countToPrefixed "o" outNum

and2 :: CombCircuit
and2 = comp NAND inv 2 1 1

andN :: Int -> CombCircuit
andN = combN and2

nand2 :: CombCircuit
nand2 = NAND

nandN :: Int -> CombCircuit
nandN n = comp (andN n) inv n 1 1

norN :: Int -> CombCircuit
norN n = comp (invN n) (andN n) n n 1

nor2 :: CombCircuit
nor2 = norN 2

or2 :: CombCircuit
or2 = comp nor2 inv 2 1 1

orN :: Int -> CombCircuit
orN = combN or2

xor2 :: CombCircuit
xor2 = NET [(or2,i,["x"]),(nand2,i,["y"]),(and2,["x","y"],["c"])] i ["c"] where i = ["a","b"]

xorN :: Int -> CombCircuit
xorN = combN xor2

xnorN :: Int -> CombCircuit
xnorN n = comp (xorN n) inv n 1 1

xnor2 :: CombCircuit
xnor2 = xnorN 2


-- multiplexers

mux1_1 :: CombCircuit
mux1_1 = NET [(inv,["s"],["ns"]),(and2,["a","ns"],["c1"]),(and2,["b","s"],["c2"]),(or2,["c1","c2"],["c"])] ["s","a","b"] ["c"]

muxN_1 :: Int -> CombCircuit
muxN_1 1 = mux1_1
muxN_1 n = NET [(muxN_1 (n-1),sr++v1,["c1"]),(muxN_1 (n-1),sr++v2,["c2"]),(mux1_1,["s","c1","c2"],["c"])] i ["c"] where
  v1 = countToPrefixed "a" (2^(n-1))
  v2 = countToPrefixed "b" (2^(n-1))
  sr = countToPrefixed "s" (n-1)
  i = ["s"] ++ sr ++ v1 ++ v2

-- N_N : selector bits _ output bits
muxN_N :: Int -> Int -> CombCircuit
muxN_N n m = NET muxes (sels++inps) otps where
  -- input bit name format: aN_M where M is the string index and N is the string number
  -- output bit name format: oM
  sels = countToPrefixed "s" n
  muxes = map (\mm -> (muxN_1 n,sels ++ inpsSub mm,[otps !! (mm-1)])) [1..m]
  inpsSub mm = map (\nn -> "a" ++ show nn ++ "_" ++ show mm) [1..(2^n)]
  inps = concat $ map (\nn -> countToPrefixed ("a" ++ show nn ++ "_") m) [1..(2^n)]
  otps = countToPrefixed "o" m
  

-- equality checker

eqN :: Int -> CombCircuit
eqN n = comp (combNIndividually xnor2 n) (andN n) (n+n) n 1

eqToN :: [Bool] -> CombCircuit
eqToN bs = feedVals (eqN n) bs n 1 where n = length bs


-- arbitrary boolean logic to combinatorial circuit

produceBehavior :: ([Bool] -> [Bool]) -> Int -> Int -> CombCircuit
produceBehavior f inl outl = feedValsEnd (muxN_N inl outl) (concat $ map snd $ makeFnTruthTable f inl) inl outl


-- test behaviors
and2_Behavior :: [Bool] -> [Bool]
and2_Behavior (a:(b:[])) = [a && b]

muxN_N_Behavior :: Int -> Int -> [Bool] -> [Bool]
muxN_N_Behavior n m inp = otp where
  sel = take n inp
  vals = drop n inp
  nthStr nn = take m $ drop (nn * m) vals
  otp = nthStr $ boolsToInt sel

-- make sure produceBehavior works
check_produceBehavior :: CombCircuit -> Int -> Int -> Bool
check_produceBehavior c inl outl = (makeTruthTable c inl) == (makeTruthTable (produceBehavior (evalComb c) inl outl) inl)



main = return ()
