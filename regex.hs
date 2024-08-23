import Data.List
import Data.Maybe

data ENFA = ENFA Int [(Int, Int, Int)] Int [Int] deriving (Show)
data NFA = NFA Int [(Int, Int, Int)] Int [Int] deriving (Show)

data Regex = Empty | Epsilon | Single Int | Plus Regex Regex | Times Regex Regex | Star Regex deriving (Show)

epsilon :: Int
epsilon = -1

empty :: ENFA
empty = ENFA 1 [] 0 []

singleEps :: ENFA
singleEps = ENFA 1 [] 0 [0]

single :: Int -> ENFA
single a = ENFA 2 [(0, a, 1)] 0 [1]

translateTransitions :: Int -> [(Int, Int, Int)] -> [(Int, Int, Int)]
translateTransitions x = map (\(q1, a, q2) -> (q1 + x, a, q2 + x))

plus :: ENFA -> ENFA -> ENFA
plus (ENFA qs1 t1 q01 f1) (ENFA qs2 t2 q02 f2) = ENFA (qs1 + qs2 + 1) ([(q_start, epsilon, q01), (q_start, epsilon, q02 + qs1)] ++ t1 ++ translateTransitions qs1 t2) q_start (f1 ++ map (+ qs1) f2)
  where
    q_start = qs1 + qs2

times :: ENFA -> ENFA -> ENFA
times (ENFA qs1 t1 q01 f1) (ENFA qs2 t2 q02 f2) = ENFA (qs1 + qs2) (t1 ++ translateTransitions qs1 t2 ++ map (,epsilon,q02 + qs1) f1) q01 (map (+ qs1) f2)
  where
    q_start = qs1 + qs2

star :: ENFA -> ENFA
star (ENFA qs t q0 f) = ENFA (qs + 1) ([(qs, epsilon, q0)] ++ map (,epsilon,qs) f ++ t) qs [qs]

regexENFA :: Regex -> ENFA
regexENFA Empty = empty
regexENFA Epsilon = singleEps
regexENFA (Single a) = single a
regexENFA (Plus r1 r2) = plus (regexENFA r1) (regexENFA r2)
regexENFA (Times r1 r2) = times (regexENFA r1) (regexENFA r2)
regexENFA (Star r) = star (regexENFA r)

filterTransitions :: (Int -> Int -> Bool) -> [(Int, Int, Int)] -> [Int]
filterTransitions pred t = nub $ map (\(r1, a, r2) -> r2) $ filter (\(r1, a, r2) -> pred r1 a) t

epsilonPaths :: ENFA -> Int -> [Int]
epsilonPaths enfa r = epsilonFull enfa [r]

epsilonFull :: ENFA -> [Int] -> [Int]
epsilonFull nfa rs
    | rs' == rs = rs
    | otherwise = epsilonFull nfa rs'
  where
    rs' = epsilonStep nfa rs

epsilonStep :: ENFA -> [Int] -> [Int]
epsilonStep (ENFA qs t q0 f) rs = nub $ concatMap (\r -> filterTransitions (\r1 a -> r1 == r && a == epsilon) t) rs ++ rs

reachable :: ENFA -> Int -> Int -> [Int]
reachable (ENFA qs t q0 f) r a = rs''
  where
    rs = epsilonPaths (ENFA qs t q0 f) r
    rs' = filterTransitions (\r1 b -> a == b && r1 `elem` rs) t
    rs'' = concatMap (epsilonPaths (ENFA qs t q0 f)) rs'

removeEpsilons :: ENFA -> NFA
removeEpsilons (ENFA qs t q0 f) = NFA qs t' q0 f'
  where
    s = if null t then -1 else maximum $ map (\(r1, a, r2) -> a) t
    t' = filter (\(r1, a, r2) -> r2 `elem` reachable enfa r1 a) [(r1, a, r2) | r1 <- [0 .. qs - 1], a <- [0 .. s], r2 <- [0 .. qs - 1]]
    f' = filter (\r1 -> not $ null $ intersect (epsilonPaths enfa r1) f) [0 .. qs - 1]
    enfa = ENFA qs t q0 f

next :: NFA -> [Int] -> Int -> [Int]
next (NFA qs t q0 f) set a = filterTransitions (\r1 b -> a == b && r1 `elem` set) t

accepts :: NFA -> [Int] -> Bool
accepts (NFA qs t q0 f) w = (\set -> (not . null) (set `intersect` f)) $ foldl (next (NFA qs t q0 f)) [q0] w

epsAccepts :: ENFA -> [Int] -> Bool
epsAccepts nfa = accepts (removeEpsilons nfa)

searchNext :: NFA -> ([(Int, Int)], Int) -> Int -> ([(Int, Int)], Int)
searchNext (NFA qs t q0 f) (set, n) a = (nubBy (\(r1, n1) (r2, n2) -> r1 == r2) mapped, n+1)
    where mapped = map (\(r1, a, r2) -> (r2, if r1 == q0 then n else snd $ head $ filter (\(r, a) -> r == r1) set)) filtered
          filtered = filter (\(r1, b, r2) -> a == b && any (\(r, a) -> r == r1) set) t

takeWhilePlusOne :: (a -> Bool) -> [a] -> [a]
takeWhilePlusOne pred [] = []
takeWhilePlusOne pred (x:xs) | pred x = x : takeWhilePlusOne pred xs
                             | otherwise = [x]

nfaSearch :: NFA -> [Int] -> Maybe (Int, Int)
nfaSearch (NFA qs t q0 f) w = if not $ pred res then Just ((snd . head) $ filter (\(q, n) -> q `elem` f) (fst res), snd res) else Nothing
    where
        res = last $ takeWhilePlusOne pred $ scanl (searchNext (NFA qs t q0 f)) ([(q0, 0)], 0) w
        pred (set, n) = null (map fst set `intersect` f)

enfaSearch :: ENFA -> [Int] -> Maybe (Int, Int)
enfaSearch nfa = nfaSearch (removeEpsilons nfa)

search :: String -> String -> Either String (String, (Int, Int))
search regS s = maybe (Left "Parse error") searchReg (parseRegex regS)
    where searchReg reg = maybe (Left "No occurrence") (\(a, b) -> Right (drop a $ take b s, (a, b))) (enfaSearch enfa (stringAscii s))
            where enfa = ENFA qs (map (q0,, q0) [0..length ascii] ++ t) q0 f -- construction assuming q0 is not reachable from q0
                    where (ENFA qs t q0 f) = regexENFA reg 

ascii :: [Char]
ascii = " !\"#$%&'()*+,−./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~"

charAscii :: Char -> Int
charAscii c = fromJust $ elemIndex c ascii

stringAscii :: String -> [Int]
stringAscii = map charAscii

data ParseToken = LBracket | PlusT | TimesT | Ex Regex deriving (Show)
parseRegexChar :: Char -> [ParseToken] -> Maybe [ParseToken]
parseRegexChar '(' [] = Just [LBracket]
parseRegexChar '(' (LBracket : ts) = Just (LBracket : LBracket : ts)
parseRegexChar '(' (PlusT : ts) = Just (LBracket : PlusT : ts)
parseRegexChar '(' (TimesT : ts) = Just (LBracket : TimesT : ts)
parseRegexChar '(' (Ex reg2 : PlusT : Ex reg1 : ts) = Just (LBracket : TimesT : Ex reg2 : PlusT : Ex reg1 : ts)
parseRegexChar '(' (Ex reg2 : TimesT : Ex reg1 : ts) = Just (LBracket : TimesT : Ex (Times reg1 reg2) : ts)
parseRegexChar '(' (Ex reg : ts) = Just (LBracket : TimesT : (Ex reg : ts))

parseRegexChar '*' (Ex reg : ts) = Just (Ex (Star reg) : ts)
parseRegexChar '*' _ = Nothing

parseRegexChar '+' (Ex reg2 : PlusT : Ex reg1 : ts) = Just (PlusT : Ex (Plus reg1 reg2) : ts)
parseRegexChar '+' (Ex reg2 : TimesT : Ex reg1 : ts) = Just (PlusT : Ex (Times reg1 reg2) : ts)
parseRegexChar '+' (Ex reg : ts) = Just (PlusT : Ex reg : ts)
parseRegexChar '+' _ = Nothing

parseRegexChar ')' (LBracket : ts) = Just (Ex Epsilon : ts)
parseRegexChar ')' (Ex reg : LBracket : ts) = Just (Ex reg : ts)
parseRegexChar ')' (Ex reg3 : TimesT : Ex reg2 : PlusT : Ex reg1 : LBracket : ts) = Just (Ex (Plus reg1 (Times reg2 reg3)) : ts)
parseRegexChar ')' (Ex reg2 : PlusT : Ex reg1 : LBracket : ts) = Just (Ex (Plus reg1 reg2) : ts)
parseRegexChar ')' (Ex reg2 : TimesT : Ex reg1 : LBracket : ts) = Just (Ex (Times reg1 reg2) : ts)
parseRegexChar ')' _ = Nothing

parseRegexChar c [] = Just [Ex (Single (charAscii c))]
parseRegexChar c (LBracket : ts) = Just (Ex (Single (charAscii c)) : LBracket : ts)
parseRegexChar c (PlusT : ts) = Just (Ex (Single (charAscii c)) : PlusT : ts)
parseRegexChar c (TimesT : ts) = Just (Ex (Single (charAscii c)) : TimesT : ts)
parseRegexChar c (Ex reg2 : PlusT : Ex reg1 : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex reg2 : PlusT : Ex reg1 : ts)
parseRegexChar c (Ex reg2 : TimesT : Ex reg1 : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex (Times reg1 reg2) : ts)
parseRegexChar c (Ex reg : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex reg : ts)

parseRegex :: String -> Maybe Regex
parseRegex s = case stack of
    Just [Ex reg] -> Just reg
    _ -> Nothing
    where stack = foldl (\ts c -> ts >>= parseRegexChar c) (Just []) ("(" ++ s ++ ")")

fits :: String -> String -> Maybe Bool
fits regS s = do
    reg <- parseRegex regS
    let enfa = regexENFA reg
    return $ epsAccepts enfa (stringAscii s)

