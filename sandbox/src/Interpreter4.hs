{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter4 where

type Id = String

data Val = List [Val] | Int Integer | Char Char | Bool Bool
  deriving (Eq, Show)

data Cmd = Skip
         | Assign Id Expr
         | Seq Cmd Cmd
         | Ite Expr Cmd Cmd
         | While Expr Cmd
         | Error
  deriving Show

data Expr = Var Id
          | Val Val
          | Eq Expr Expr
          | Not Expr
          | And Expr Expr
          | Or Expr Expr
          | Cons Expr Expr
          | Head Expr
          | Tail Expr
          | Lt Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
  deriving Show

type Env = [(Id, Val)]

eval :: Env -> Expr -> Maybe Val
eval env (Var v)        = lookup v env
eval env (Val x)        = Just x
eval env (Eq e1 e2)     = Bool <$> ((==) <$> eval env e1 <*> eval env e2)
eval env (Not e)        | Just (Bool a) <- eval env e
                        = Just (Bool (not a))
eval env (And e1 e2)    | Just (Bool a) <- eval env e1
                        , Just (Bool b) <- eval env e2
                        = Just (Bool (a && b))
eval env (Or e1 e2)     | Just (Bool a) <- eval env e1
                        , Just (Bool b) <- eval env e2
                        = Just (Bool (a || b))
eval env (Cons e1 e2)   | Just x <- eval env e1
                        , Just (List xs) <- eval env e2
                        = Just (List (x:xs))
eval env (Head e)       | Just (List (x:_)) <- eval env e
                        = Just x
eval env (Tail e)       | Just (List (_:xs)) <- eval env e
                        = Just (List xs)
eval env (Lt e1 e2)     | Just (Int i) <- eval env e1
                        , Just (Int j) <- eval env e2
                        = Just (Bool (i < j))
eval env (Add e1 e2)    | Just (Int i) <- eval env e1
                        , Just (Int j) <- eval env e2
                        = Just (Int (i + j))
eval env (Sub e1 e2)    | Just (Int i) <- eval env e1
                        , Just (Int j) <- eval env e2
                        = Just (Int (i - j))
eval env (Mul e1 e2)    | Just (Int i) <- eval env e1
                        , Just (Int j) <- eval env e2
                        = Just (Int (i * j))
eval _   _              = Nothing

run :: Env -> Cmd -> Maybe Env
run env Skip          = Just env
run env (Assign v e)  = eval env e >>= \x -> Just ((v, x) : env)
run env (Seq c1 c2)   = run env c1 >>= \env' -> run env' c2
run env (Ite e c1 c2) | Just (Bool b) <- eval env e
                      = run env (if b then c1 else c2)
run env (While e c)   | Just (Bool b) <- eval env e
                      = run env (if b then Seq c (While e c) else Skip)
run _   _             = Nothing


--

-- Graph walk test program
-- Expects inputs in variables "graph" and "path", puts output in variable "result"

{-
graph = ["abc", "bd", "c", "dac"]
path = "abd"

# initialize visited list with empty list
visited = ""
result = True
while not(path == ""):
    x = path[:1]
    # check if x is part of the graph. if not then abort the loop
    is_in_graph = False
    graph_copy = graph[:]
    while not(graph_copy == []):
        if graph_copy[0][:1] == x:
            is_in_graph = True
            graph_copy = []
        else:
            graph_copy = graph_copy[1:]
    if is_in_graph:
        # check if visited is empty
        if visited == "":
            visited = x
            path = path[1:]
        else:
            # check if x was already visited before
            was_already_visited = False
            visited_copy = visited[:]
            while not(visited_copy == ""):
                if visited_copy[0] == x:
                    was_already_visited = True
                    visited_copy = ""
                else:
                    visited_copy = visited_copy[1:]
            if was_already_visited:
                result = False
                path = ""
            else:
                # check if x is reachable from the last visited node (head of visited)
                is_reachable = False
                graph_copy = graph[:]
                while not(graph_copy == []):
                    # find entry for last visited node (head of visited)
                    if graph_copy[0][:1] == visited[:1]:
                        # check if x is in the successors of last visited node (i.e., is reachable)
                        successors = graph_copy[0][1:]
                        while not(successors == ""):
                            if successors[:1] == x:
                                is_reachable = True
                                successors = ""
                            else:
                                successors = successors[1:]
                        graph_copy = []
                    else:
                        graph_copy = graph_copy[1:]
                if is_reachable:
                    visited = x + visited
                    path = path[1:]
                else:
                    result = False
                    path = ""
    else:
        error
-}

isWalkProgram :: Cmd
isWalkProgram = foldl1 Seq
  [ Assign "visited" (Val (List []))
  , Assign "result" (Val (Bool True))
  , While (Not (Eq (Var "path") (Val (List [])))) (foldl1 Seq
      [ Assign "current" (Head (Var "path"))
      , Assign "is_in_graph" (Val (Bool False))
      , Assign "graph_copy" (Var "graph")
      , While (Not (Eq (Var "graph_copy") (Val (List []))))
          (Ite (Eq (Head (Head (Var "graph_copy"))) (Var "current"))
            (foldl1 Seq [ Assign "is_in_graph" (Val (Bool True))
                        , Assign "graph_copy" (Val (List []))
                        ])
            (Assign "graph_copy" (Tail (Var "graph_copy"))))
      , Ite (Var "is_in_graph")
          (Ite (Eq (Var "visited") (Val (List [])))
            (foldl1 Seq [ Assign "visited" (Cons (Var "current") (Val (List [])))
                        , Assign "path" (Tail (Var "path"))
                        ])
            (foldl1 Seq [ Assign "already_visited" (Val (Bool False))
                        , Assign "visited_copy" (Var "visited")
                        , While (Not (Eq (Var "visited_copy") (Val (List []))))
                            (Ite (Eq (Head (Var "visited_copy")) (Var "current"))
                              (foldl1 Seq [ Assign "already_visited" (Val (Bool True))
                                          , Assign "visited_copy" (Val (List []))
                                          ])
                              (Assign "visited_copy" (Tail (Var "visited_copy"))))
                        , Ite (Var "already_visited")
                            (foldl1 Seq [ Assign "result" (Val (Bool False))
                                        , Assign "path" (Val (List []))
                                        ])
                            (foldl1 Seq [ Assign "is_reachable" (Val (Bool False))
                                        , Assign "graph_copy" (Var "graph")
                                        , While (Not (Eq (Var "graph_copy") (Val (List []))))
                                            (Ite (Eq (Head (Head (Var "graph_copy"))) (Head (Var "visited")))
                                              (foldl1 Seq [ Assign "successors" (Tail (Head (Var "graph_copy")))
                                                          , While (Not (Eq (Var "successors") (Val (List []))))
                                                              (Ite (Eq (Head (Var "successors")) (Var "current"))
                                                                (foldl1 Seq [ Assign "is_reachable" (Val (Bool True))
                                                                            , Assign "successors" (Val (List []))
                                                                            ])
                                                                (Assign "successors" (Tail (Var "successors"))))
                                                          , Assign "graph_copy" (Val (List []))
                                                          ])
                                              (Assign "graph_copy" (Tail (Var "graph_copy"))))
                                        , Ite (Var "is_reachable")
                                            (foldl1 Seq [ Assign "visited" (Cons (Var "current") (Var "visited"))
                                                        , Assign "path" (Tail (Var "path"))
                                                        ])
                                            (foldl1 Seq [ Assign "result" (Val (Bool False))
                                                        , Assign "path" (Val (List []))
                                                        ])
                                        ])
                        ]))
          Error
      ])
  ]

type Node = Char

type Graph = [[Node]]

type Path = [Node]

isWalk :: Graph -> Path -> Bool
isWalk g p | Just (Bool b) <- run [("graph", List (map (List . map Char) g)), ("path", List (map Char p))] isWalkProgram >>= lookup "result" = b

isWalkRef :: Graph -> Path -> Bool
isWalkRef g p = isWalk' p []
  where isInGraph x = x `elem` map head g
        isReachableFrom x y = case lookup y (map (\str -> (head str, tail str)) g) of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = x `notElem` (y:ys) && isReachableFrom x y && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ "abc"
        , "bd"
        , "c"
        , "dac"
        ]

---

-- Faculty test program
-- Expects input in variable "x", puts output in variable "y"

-- IF x < 0 THEN
--   ERROR
-- ELSE
--   y = 1;
--   WHILE NOT(x == 0) DO
--     y = y * x;
--     x = x - 1
--   OD
-- FI

facultyProgram :: Cmd
facultyProgram = Ite (Lt (Var "x") (Val (Int 0)))
  Error
  (foldl1 Seq [ Assign "y" (Val (Int 1))
              , While (Not (Eq (Var "x") (Val (Int 0)))) (foldl1 Seq
                  [ Assign "y" (Mul (Var "y") (Var "x"))
                  , Assign "x" (Sub (Var "x") (Val (Int 1)))
                  ])
              ])

faculty :: Integer -> Maybe Integer
faculty x | Just (Int y) <- run [("x", Int x)] facultyProgram >>= lookup "y" = Just y
          | otherwise                                                        = Nothing

-- Test with: head $ $(inv 'test) (Just 3628800)

facultyRef :: Integer -> Maybe Integer
facultyRef x = if x < 0 then Nothing else Just (faculty' x)
  where faculty' 0  = 1
        faculty' x' = x' * faculty' (x' - 1)


--

-- Matching test program
-- Expects inputs in variables Xs and Ys, output is Xs with Xs == [] if Xs was part of Ys

{-
xs = "allo" # zu suchendes wort
ys = "aloallo" # zu durchsuchendes wort

while len(ys) != 0:
    as1 = xs[:]
    bs = ys[:]
    while len(as1) != 0 and len(bs) != 0:
        if as1[:1] == bs[:1]:
            as1 = as1[1:]
            bs = bs[1:]
        else:
            bs = []
    if len(as1) == 0:
        ys = []
        xs = []
    else:
        ys = ys[1:]
print(len(xs) == 0)
-}

matchProgram :: Cmd
matchProgram = foldl1 Seq
  [ While (Not (Eq (Var "str") (Val (List [])))) (foldl1 Seq
      [ Assign "substr_copy" (Var "substr")
      , Assign "str_copy" (Var "str")
      , While (And (Not (Eq (Var "substr_copy") (Val (List [])))) (Not (Eq (Var "str_copy") (Val (List [])))))
          (Ite (Eq (Head (Var "substr_copy")) (Head (Var "str_copy")))
            (foldl1 Seq [ Assign "substr_copy" (Tail (Var "substr_copy"))
                        , Assign "str_copy" (Tail (Var "str_copy"))
                        ])
            (Assign "str_copy" (Val (List []))))
      , Ite (Eq (Var "substr_copy") (Val (List [])))
          (foldl1 Seq [ Assign "str" (Val (List []))
                      , Assign "substr" (Val (List []))
                      ])
          (Assign "str" (Tail (Var "str")))
      ])
  , Assign "matched" (Eq (Var "substr") (Val (List [])))
  ]

match :: String -> String -> Bool
match xs ys | Just (Bool b) <- run [("substr", List (map Char xs)), ("str", List (map Char ys))] matchProgram >>= lookup "matched" = b

-- Equivalent test program in Haskell

matchRef :: String -> String -> Bool
matchRef [] _      = True
matchRef _  []     = False
matchRef xs (y:ys) = match' xs (y:ys) || matchRef xs ys
  where match' []      _     = True
        match' (x:xs) (y:ys) = x == y && match' xs ys
        match' _      _      = False

-- Test with:
-- $(partialInv 'match True [1]) "abc" True
-- $(partialInv 'matchRef True [1]) "abc" True

--TODO: in den anhang
