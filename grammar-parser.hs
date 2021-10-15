-- Carson Kim  
-- Winter 2021
-- Transition-Based CFG Parsing (Chomsky Normal Form)


{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# OPTIONS_GHC -fwarn-incomplete-uni-patterns #-}

module FinalProject where

import Control.Applicative(liftA, liftA2, liftA3)

type Configuration a b = ([a],[b])

data StackSymbol nt = Plain nt | Barred nt deriving (Eq,Show)

data Cat = S | NP | VP | PP | V | P | D | N deriving (Show, Eq, Ord)

data RewriteRule nt t = NTRule nt (nt,nt) | TRule nt t deriving (Show, Eq)

---- CFG Setup -------

type CFG nt t = ([nt], [t], [nt], [RewriteRule nt t])

type GenericCFG nt t  = ([nt], [t], nt, [RewriteRule nt t])

cfg1 :: GenericCFG Cat String 
cfg1 = ([VP,NP,PP,V,P], ["watches","spies","telescopes","with", "he"], VP, 
                        [(NTRule VP (V,NP)), (NTRule NP (NP,PP)), (NTRule PP (P,NP)),
                         (NTRule VP (VP,PP)),  (TRule NP "telescopes"),
                         (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), 
                         (TRule VP "spies"),   (TRule NP "spies"), (TRule V "watches"), 
                         (TRule NP "he"), (NTRule VP (VP, NP)), (NTRule S (NP, VP))])

cfg2 :: GenericCFG Cat String 
cfg2 = ([D, NP, N, S, VP, V], ["the", "baby", "saw", "the", "boy"], S, 
                        [(NTRule VP (V,NP)), (NTRule S (NP, VP)), (NTRule NP (NP,PP)), (NTRule PP (P,NP)),
                         (NTRule VP (VP,PP)), (NTRule NP (D, N)), (TRule V "saw"), (TRule N "baby"), (TRule N "boy"), 
                         (TRule D "the")])


-- starting configurations corresponding to cfg1
bu1 :: Configuration Cat String
bu1 = ([], ["he", "watches","spies","with", "telescopes"])

td1 :: Configuration Cat String
td1 = ([S],["he", "watches","spies","with", "telescopes"])

lc1 :: Configuration (StackSymbol Cat) String
lc1 = ([Barred S], ["he", "watches","spies","with", "telescopes"])

lc1fail :: Configuration (StackSymbol Cat) String
lc1fail = ([Plain S], ["he", "watches","spies","with", "telescopes"])

lc2fail :: Configuration (StackSymbol Cat) String
lc2fail = ([], ["he", "watches","spies","with", "telescopes"])


-- starting configurations corresponding to cfg2
bu2 :: Configuration Cat String 
bu2 = ([], ["the", "baby", "saw", "the", "boy"])

td2 :: Configuration Cat String
td2 = ([S], ["the", "baby", "saw", "the", "boy"])

lc2 :: Configuration (StackSymbol Cat) String
lc2 = ([Barred S], ["the", "baby", "saw", "the", "boy"])


--------------------------------------------------
--        Parsing Schema Implementation         --
--------------------------------------------------

---- General Helper Functions ---- 
----------------------------------

-- get list of Rewrite Rules from a cfg ---- 
getRules :: GenericCFG nt t -> [RewriteRule nt t]
getRules cfg = let (syms, terms, start, r) = cfg in r 

-- gets left-hand side of rules
getLHS :: RewriteRule nt t -> nt
getLHS rule = case rule of
    TRule x y -> x 
    NTRule lhs (a, b) -> lhs

--- convert configs of type maybe to vanilla --- 
filterValidConfigs :: [Maybe (Configuration nt t)] -> [Configuration nt t]
filterValidConfigs list = case list of 
    [] -> []
    x:rest -> case x of 
        Nothing -> filterValidConfigs rest
        Just a -> [a] ++ (filterValidConfigs rest)

--- remove configs that exceed the size limit ----
filterLongConfigs :: Int -> [Configuration nt t] -> [Configuration nt t]
filterLongConfigs bound configs = case configs of 
    [] -> []
    x:rest -> case x of 
        (symbols, strings) -> if length(symbols) <= bound then x:(filterLongConfigs bound rest) else (filterLongConfigs bound rest)

 --- Get max load for a list of list of configs (many paths) ----
maxLoadMany :: [[Configuration nt t]] -> Int
maxLoadMany paths = let calculateHelper paths = case paths of 
                                    [] -> [0]
                                    x:rest -> (maxLoad x):(calculateHelper rest) in 
    maximum (calculateHelper paths)

---- Get max load for just one list ---- 
maxLoad:: [Configuration nt t] -> Int
maxLoad configs = let calculateHelper configs = case configs of                                                         
                                [] -> [0]
                                x:rest -> case x of 
                                     (symbols, string) -> [length(symbols)]++calculateHelper(rest) in 
    maximum (calculateHelper configs)
    
-- Left-Corner Parser Helpers --- 

plainSymbols :: [StackSymbol nt] -> [nt]
plainSymbols symbols = case symbols of 
            [] -> []
            (Plain sym):rest -> sym:(plainSymbols rest)
            (Barred sym):rest -> sym:(plainSymbols rest) 



---------------------------
--    Bottom-Up Parser   -- 
---------------------------

isValidShift :: (Eq nt, Eq t) =>  RewriteRule nt t -> t -> Bool 
isValidShift rule symbol = case rule of 
    TRule a b -> if b == symbol then True else False
    NTRule c d -> False 

isValidReduce :: (Eq nt, Eq t) => RewriteRule nt t -> [nt] -> Bool 
isValidReduce rule symbols = case rule of 
    TRule a b -> False
    NTRule nt0 (nt1, nt2) -> case symbols of 
        [] -> False
        _ -> if (nt1 == (head symbols)) && (nt2 == (last symbols)) then True else False

shift :: (Eq nt, Eq t) => Configuration nt t -> RewriteRule nt t-> Maybe (Configuration nt t)
shift config rule = let (symbols, string) = config in case string of
    [] -> Nothing
    x:rest -> if (isValidShift rule x) then Just ((symbols ++ [getLHS rule]), rest) else Nothing

reduce ::(Eq nt, Eq t) => Configuration nt t -> RewriteRule nt t-> Maybe (Configuration nt t)
reduce config rule = let (symbols, string) = config in case symbols of 
    [] -> Nothing
    x:[] -> Nothing
    x:rest -> let i = (length symbols) - 2 in if (isValidReduce rule (drop i symbols)) then 
        let load = take ((length symbols) - 2) symbols in Just (load ++ [getLHS rule], string) else Nothing

buParser ::  (Eq nt, Eq t) => [RewriteRule nt t] -> Configuration nt t -> [[Configuration nt t]]
buParser rules config = let (symbols, string) = config in case config of
    ([nt], []) -> [[([nt], [])]]
    ([], []) -> []
    (a, b) -> let configList = (filterValidConfigs(map (\r -> (shift config r)) rules)) ++ (filterValidConfigs(map (\r -> (reduce config r)) rules)) in case configList of
        [] -> []
        _ ->  let paths = concat (map(\c -> buParser rules c) configList) in 
                map(\c -> config:c) paths


--------------------------
--    Top-Down Parser   --
--------------------------

predict :: (Eq nt, Eq t) => Configuration nt t -> RewriteRule nt t -> Maybe (Configuration nt t)
predict config rule = let (symbols, string) = config in case symbols of 
    [] -> Nothing
    x:rest -> case rule of 
        TRule a b -> Nothing
        NTRule nt0 (nt1, nt2) -> if nt0 == x then Just (nt1:nt2:rest, string) else Nothing 

match :: (Eq nt, Eq t) => Configuration nt t -> RewriteRule nt t -> Maybe (Configuration nt t)
match config rule = let (symbols, string) = config in case string of 
    [] -> Nothing
    x:rest -> case symbols of 
        [] -> Nothing
        x':rest' -> case rule of 
            NTRule nt0 (nt1, nt2) -> Nothing
            TRule nt t -> if x == t && x' == nt then Just (rest', rest) else Nothing

tdParser :: (Eq nt, Eq t) => [RewriteRule nt t] -> Configuration nt t -> [[Configuration nt t]]
tdParser rules config = let (symbols, string) = config in let upperBound = length string * 2 in case config of
    ([], []) -> [[config]]
    ([], b) -> []
    (a, b) -> let unboundedList = filterValidConfigs(map (\r -> match config r) rules) ++ filterValidConfigs(map (\r -> predict config r) rules) in 
                let configList = filterLongConfigs upperBound unboundedList in case configList of
                    [] -> []
                    _ -> let paths = concat (map(\c -> tdParser rules c) configList) in 
                            map(\c -> config:c) paths

----------------------------------
--   Left-Corner Eager Parser   --
----------------------------------

isValidlcShift :: (Eq nt, Eq t) =>  RewriteRule nt t -> t -> Bool 
isValidlcShift rule symbol = case rule of 
    TRule a b -> if b == symbol then True else False
    NTRule c d -> False 

lcShift :: (Eq nt, Eq t) => Configuration (StackSymbol nt) t -> RewriteRule nt t -> Maybe (Configuration (StackSymbol nt) t)
lcShift config rule = let (symbols, string) = config in case string of
    [] -> Nothing
    x:rest -> if (isValidShift rule x) then Just (([Plain (getLHS rule)] ++ symbols), rest) else Nothing

lcMatch :: (Eq nt, Eq t) => Configuration (StackSymbol nt) t -> RewriteRule nt t -> Maybe (Configuration (StackSymbol nt) t)
lcMatch config rule = let (symbols, string) = config in case string of 
    [] -> Nothing
    x:rest -> case symbols of 
        [] -> Nothing
        x':rest' -> case x' of 
            Plain sym -> Nothing 
            Barred sym -> case rule of 
                NTRule nt0 (nt1, nt2) -> Nothing
                TRule nt t -> if x == t && sym == nt then Just (rest', rest) else Nothing

lcPredict :: (Eq nt, Eq t) => Configuration (StackSymbol nt) t -> RewriteRule nt t -> Maybe (Configuration (StackSymbol nt) t)
lcPredict config rule = let (symbols, string) = config in case symbols of 
    [] -> Nothing
    x:rest -> case x of 
        Barred sym -> Nothing
        Plain sym -> case rule of 
                        TRule a b -> Nothing
                        NTRule nt0 (nt1, nt2) -> if sym == nt1 then Just ((Barred nt2:Plain nt0:rest), string) else Nothing

lcConnect :: (Eq nt, Eq t) => Configuration (StackSymbol nt) t -> RewriteRule nt t -> Maybe (Configuration (StackSymbol nt) t)
lcConnect config rule = let (symbols, string) = config in case symbols of
    [] -> Nothing
    x:[] -> Nothing
    x:y:rest -> case x of 
        Barred sym -> Nothing
        Plain sym -> case y of 
            Plain sym' -> Nothing
            Barred sym' -> case rule of 
                TRule a b -> Nothing
                NTRule nt0 (nt1, nt2) -> if sym == nt1 && sym' == nt0 then Just ((Barred nt2:rest), string) else Nothing


lcParser :: (Eq nt, Eq t) => [RewriteRule nt t] -> Configuration (StackSymbol nt) t -> [[Configuration (StackSymbol nt) t]]
lcParser rules config = let (symbols, string) = config in let upperBound = length string * 2 in case config of 
    ([], []) -> [[config]]
    ([], b) -> []
    (a, b) -> let unboundedList = filterValidConfigs(map (\r -> lcShift config r) rules) ++ filterValidConfigs(map (\r -> lcMatch config r) rules) ++ filterValidConfigs(map (\r -> lcPredict config r) rules) ++ filterValidConfigs(map(\r -> lcConnect config r) rules)
                         in 
                let configList = filterLongConfigs upperBound unboundedList in case configList of
                    [] -> []
                    _ -> let paths = concat (map(\c -> lcParser rules c) configList) in 
                                map(\c -> config:c) paths 
                        


