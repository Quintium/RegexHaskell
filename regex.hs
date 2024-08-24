import Data.List
import Data.Array
import Data.Maybe
import Control.Monad.State

-- epsilon-NFA, ENFA (qs - number of states) (t - transitions in the form of (q1, a, q2)) (q0 - start state) (f - finish states) 
data ENFA = ENFA Int [(Int, Int, Int)] Int [Int] deriving (Show) -- epsilon-NFA, epsilon represented by -1
data NFA = NFA Int [(Int, Int, Int)] Int [Int] deriving (Show) -- NFA, no epsilon allowed

-- Plus - union, Times - Concatenation, star - Kleene-star
data Regex = Empty | Epsilon | Single Int | Plus Regex Regex | Times Regex Regex | Star Regex deriving (Show)

-- epsNFAs for regex blocks

epsilon :: Int
epsilon = -1

empty :: ENFA
empty = ENFA 1 [] 0 []

singleEps :: ENFA
singleEps = ENFA 1 [] 0 [0]

single :: Int -> ENFA
single a = ENFA 2 [(0, a, 1)] 0 [1]

-- helper function to translate states of NFAs by given amount
translateTransitions :: Int -> [(Int, Int, Int)] -> [(Int, Int, Int)]
translateTransitions x = map (\(q1, a, q2) -> (q1 + x, a, q2 + x))

-- combining epsNFAs

plus :: ENFA -> ENFA -> ENFA
plus (ENFA qs1 t1 q01 f1) (ENFA qs2 t2 q02 f2) = ENFA (qs1 + qs2 + 1) t' q0' f'
  where
    -- second states are translated as to not collide with first
    t' = [(q0', epsilon, q01), (q0', epsilon, q02 + qs1)] ++ t1 ++ translateTransitions qs1 t2
    f' = f1 ++ map (+ qs1) f2
    q0' = qs1 + qs2

times :: ENFA -> ENFA -> ENFA
times (ENFA qs1 t1 q01 f1) (ENFA qs2 t2 q02 f2) = ENFA (qs1 + qs2) t' q01 f'
  where
    -- second states are translated as to not collide with first
    t' = t1 ++ translateTransitions qs1 t2 ++ map (,epsilon,q02 + qs1) f1
    f' = map (+ qs1) f2

star :: ENFA -> ENFA
star (ENFA qs t q0 f) = ENFA (qs + 1) t' q0' f'
    where
        t' = [(q0', epsilon, q0)] ++ map (, epsilon, q0') f ++ t
        f' = [q0']
        q0' = qs

regexENFA :: Regex -> ENFA
regexENFA Empty = empty
regexENFA Epsilon = singleEps
regexENFA (Single a) = single a
regexENFA (Plus r1 r2) = plus (regexENFA r1) (regexENFA r2)
regexENFA (Times r1 r2) = times (regexENFA r1) (regexENFA r2)
regexENFA (Star r) = star (regexENFA r)

-- create adjacency list for every state in the form of r1 -> [(a, r2), (a', r2')]; O(qs + |t|)
adjacencyList :: ENFA -> Array Int [(Int, Int)]
adjacencyList (ENFA qs t q0 f) = accumArray (flip (:)) [] (0, qs-1) [(r1, (a, r2)) | (r1, a, r2) <- t] 

-- epsilonAllPairs nfa ! q1 ! q2 <=> path q1 -> q2 through epsilons exists
epsilonAllPairs :: ENFA -> Array Int (Array Int Bool)
epsilonAllPairs (ENFA qs t q0 f) = array (0, qs-1) [(r, epsilonSinglePairs adjList r) | r <- [0..qs-1]]
    where adjList = adjacencyList (ENFA qs t q0 f)

-- calculate which states can be reached through epsilons from given state
epsilonSinglePairs :: Array Int [(Int, Int)] -> Int -> Array Int Bool
epsilonSinglePairs adjList q = execState (dfs adjList q) (listArray (0, qs-1) (replicate qs False))
    where qs = rangeSize $ bounds adjList

-- perform depth-first-search on graph with given adjacency list starting from q
-- state captures nodes visited already
dfs :: Array Int [(Int, Int)] -> Int -> State (Array Int Bool) ()
dfs adjList q = do
    reachable <- get
    unless (reachable ! q) 
        (do
            put $ reachable // [(q, True)]
            mapM_ (\(a, r2) -> when (a == epsilon) $ dfs adjList r2) (adjList ! q)
        )

-- removes duplicates/calculates intersection in a list of states with good performance

removeDupQ :: Int -> [Int] -> [Int]
removeDupQ qs as = filter (arr !) [0..qs-1]
    where arr = accumArray (||) False (0,qs-1) [(a, True) | a <- as]

intersectQ :: Int -> [Int] -> [Int] -> [Int]
intersectQ qs as bs = filter (\q -> arr ! q == 2) [0..qs-1]
    where arr = accumArray (+) 0 (0,qs-1) [(a, 1) | a <- as ++ bs]

-- convert epsNFA to NfA
removeEpsilons :: ENFA -> NFA
removeEpsilons (ENFA qs t q0 f) = NFA qs t' q0 f'
  where
    t' = concatMap (\(r1, a, r2) -> [(r1', a, r2') | r1' <- backwardList ! r1, r2' <- forwardList ! r2]) $ filter (\(r1, a, r2) -> a /= epsilon) t
    f' = removeDupQ qs $ concatMap (backwardList !) f

    -- calculate, for every state, which states it can reach through epsilon (forwardList), or from which states it can be reached (backwardList)
    forwardList = array (0,qs-1) [(q, filter (\r -> allPairs ! q ! r) [0..qs-1]) | q <- [0..qs-1]]
    backwardList = array (0,qs-1) [(q, filter (\r -> allPairs ! r ! q) [0..qs-1]) | q <- [0..qs-1]]
    allPairs = epsilonAllPairs enfa
    enfa = ENFA qs t q0 f

-- one nfa iteration, from the current states to the states after reading "a"
next :: NFA -> Array Int (Array Int [Int]) -> [Int] -> Int -> [Int]
next (NFA qs t q0 f) alphAdjList [] a = [] -- optimization, technically not needed
next (NFA qs t q0 f) alphAdjList set a = removeDupQ qs $ concatMap (alphAdjList ! a !) set

accepts :: NFA -> [Int] -> Bool
accepts (NFA qs t q0 f) w = (\set -> (not . null) (intersectQ qs set f)) $ foldl (next (NFA qs t q0 f) alphAdjList) [q0] w
    where 
        -- alphAdjList ! a ! q = all states that can be reached from q with a
        alphAdjList = array (0, length ascii-1) [(a, accumArray (flip (:)) [] (0, qs-1) (alphLists ! a)) | a <- [0..length ascii-1]]
        alphLists = accumArray (flip (:)) [] (0, length ascii-1) [(a, (r1, r2)) | (r1, a, r2) <- t] 

epsAccepts :: ENFA -> [Int] -> Bool
epsAccepts nfa = accepts (removeEpsilons nfa)

fits :: String -> String -> Maybe Bool
fits regS s = do
    reg <- parseRegex regS
    let enfa = regexENFA reg
    return $ epsAccepts enfa (stringAscii s)

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

specialChars :: [Char]
specialChars = "()+*"

charAscii :: Char -> Int
charAscii c = fromJust $ elemIndex c ascii

stringAscii :: String -> [Int]
stringAscii = map charAscii

data RegexChar = Special Char | Normal Char

regexString :: String -> [RegexChar]
regexString "" = []
regexString "!" = []
regexString ('!':c:s) = Normal c : regexString s
regexString (c:s) | c `elem` specialChars = Special c : regexString s
                  | otherwise = Normal c : regexString s

data ParseToken = LBracket | PlusT | TimesT | Ex Regex deriving (Show)
parseRegexChar :: RegexChar -> [ParseToken] -> Maybe [ParseToken]
parseRegexChar (Special '(') [] = Just [LBracket]
parseRegexChar (Special '(') (LBracket : ts) = Just (LBracket : LBracket : ts)
parseRegexChar (Special '(') (PlusT : ts) = Just (LBracket : PlusT : ts)
parseRegexChar (Special '(') (TimesT : ts) = Just (LBracket : TimesT : ts)
parseRegexChar (Special '(') (Ex reg2 : PlusT : Ex reg1 : ts) = Just (LBracket : TimesT : Ex reg2 : PlusT : Ex reg1 : ts)
parseRegexChar (Special '(')(Ex reg2 : TimesT : Ex reg1 : ts) = Just (LBracket : TimesT : Ex (Times reg1 reg2) : ts)
parseRegexChar (Special '(') (Ex reg : ts) = Just (LBracket : TimesT : (Ex reg : ts))

parseRegexChar (Special '*') (Ex reg : ts) = Just (Ex (Star reg) : ts)
parseRegexChar (Special '*') _ = Nothing

parseRegexChar (Special '+') (Ex reg2 : PlusT : Ex reg1 : ts) = Just (PlusT : Ex (Plus reg1 reg2) : ts)
parseRegexChar (Special '+') (Ex reg2 : TimesT : Ex reg1 : ts) = Just (PlusT : Ex (Times reg1 reg2) : ts)
parseRegexChar (Special '+') (Ex reg : ts) = Just (PlusT : Ex reg : ts)
parseRegexChar (Special '+')_ = Nothing

parseRegexChar (Special ')') (LBracket : ts) = Just (Ex Epsilon : ts)
parseRegexChar (Special ')') (Ex reg : LBracket : ts) = Just (Ex reg : ts)
parseRegexChar (Special ')') (Ex reg3 : TimesT : Ex reg2 : PlusT : Ex reg1 : LBracket : ts) = Just (Ex (Plus reg1 (Times reg2 reg3)) : ts)
parseRegexChar (Special ')') (Ex reg2 : PlusT : Ex reg1 : LBracket : ts) = Just (Ex (Plus reg1 reg2) : ts)
parseRegexChar (Special ')') (Ex reg2 : TimesT : Ex reg1 : LBracket : ts) = Just (Ex (Times reg1 reg2) : ts)
parseRegexChar (Special ')') _ = Nothing

parseRegexChar (Normal c) [] = Just [Ex (Single (charAscii c))]
parseRegexChar (Normal c) (LBracket : ts) = Just (Ex (Single (charAscii c)) : LBracket : ts)
parseRegexChar (Normal c) (PlusT : ts) = Just (Ex (Single (charAscii c)) : PlusT : ts)
parseRegexChar (Normal c) (TimesT : ts) = Just (Ex (Single (charAscii c)) : TimesT : ts)
parseRegexChar (Normal c) (Ex reg2 : PlusT : Ex reg1 : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex reg2 : PlusT : Ex reg1 : ts)
parseRegexChar (Normal c) (Ex reg2 : TimesT : Ex reg1 : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex (Times reg1 reg2) : ts)
parseRegexChar (Normal c) (Ex reg : ts) = Just (Ex (Single (charAscii c)) : TimesT : Ex reg : ts)

parseRegex :: String -> Maybe Regex
parseRegex s = case stack of
    Just [Ex reg] -> Just reg
    _ -> Nothing
    where stack = foldl (\ts c -> ts >>= parseRegexChar c) (Just []) (regexString $ "(" ++ s ++ ")")