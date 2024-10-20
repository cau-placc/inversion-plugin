{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter3 where

type VarName = String

data Cmd = Skip
         | Assign VarName LExpr
         | Seq Cmd Cmd
         | Ite BExpr Cmd Cmd
         | While BExpr Cmd
  deriving Show

data LExpr = Var String
           | Elem Char
           | Nil
--           | Cons LExpr LExpr
           | Cons String LExpr
           | Append LExpr LExpr
           | Head LExpr
           | Tail LExpr
  deriving Show

data BExpr = Tru
           | Eq LExpr LExpr
           | Not BExpr
           | And BExpr BExpr
           | Or BExpr BExpr
  deriving Show

f x | True <- x = x

type Env = [(VarName, [String])]

evalL :: Env -> LExpr -> Maybe [String]
evalL env (Var v)    = lookup v env
--evalL env (Elem c)   = Just [c]
evalL _   Nil        = Just []
evalL env (Cons s e) = (s :) <$> evalL env e
--evalL env (Cons e1 e2) = (:) <$> (evalL env e1 >>= safeHead) <*> evalL env e2
--  where safeHead []    = Nothing
--        safeHead (x:_) = Just x
evalL env (Append e1 e2)   = (++) <$> evalL env e1 <*> evalL env e2
evalL env (Head e)   = return . head <$> evalL env e
evalL env (Tail e)   = tail <$> evalL env e

evalB :: Env -> BExpr -> Maybe Bool
evalB _   Tru         = Just True
evalB env (Eq e1 e2)  = (==) <$> evalL env e1 <*> evalL env e2
evalB env (Not e)     = not  <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2

run :: Env -> Cmd -> Maybe Env
run env Skip          = Just env
run env (Assign v a)  = evalL env a >>= \i -> Just ((v, i) : env)
run env (Seq c1 c2)   = run env c1 >>= \env' -> run env' c2
run env (Ite e c1 c2) = evalB env e >>= \b -> run env (if b then c1 else c2)
run env (While e c)   = evalB env e >>= \b -> run env (if b then Seq c (While e c) else Skip)

--

-- Matching test program
-- Expects inputs in variables graph and path, output is result with Xs == [] if path is cycle-free

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
        result = False
        path = ""

print(result)
-}

--TODO: encode true as nil

example :: Cmd
example = foldl1 Seq
  [ Assign "visited" Nil
  , Assign "result" Nil
  , While (Not (Eq (Var "path") Nil)) (foldl1 Seq
      [ Assign "current" (Head (Var "path"))
      , Assign "is_in_graph" (Cons "False" Nil)
      , Assign "graph_copy" (Var "graph")
      , While (Not (Eq (Var "graph_copy") Nil))
          (Ite (Eq (Head (Head (Var "graph_copy"))) (Var "current"))
            (foldl1 Seq [ Assign "is_in_graph" Nil
                        , Assign "graph_copy" Nil
                        ])
            (Assign "graph_copy" (Tail (Var "graph_copy"))))
      , Ite (Eq (Var "is_in_graph") Nil)
          (Ite (Eq (Var "visited") Nil)
            (foldl1 Seq [ Assign "visited" (Var "current")
                        , Assign "path" (Tail (Var "path"))
                        ])
            (foldl1 Seq [ Assign "already_visited" (Cons "False" Nil)
                        , Assign "visited_copy" (Var "visited")
                        , While (Not (Eq (Var "visited_copy") Nil))
                            (Ite (Eq (Head (Var "visited_copy")) (Var "current"))
                              (foldl1 Seq [ Assign "already_visited" Nil
                                          , Assign "visited_copy" Nil
                                          ])
                              (Assign "visited_copy" (Tail (Var "visited_copy"))))
                        , Ite (Eq (Var "already_visited") Nil)
                            (foldl1 Seq [ Assign "result" (Cons "False" Nil)
                                        , Assign "path" Nil
                                        ])
                            (foldl1 Seq [ Assign "is_reachable" (Cons "False" Nil)
                                        , Assign "graph_copy" (Var "graph")
                                        , While (Not (Eq (Var "graph_copy") Nil))
                                            (Ite (Eq (Head (Head (Var "graph_copy"))) (Head (Var "visited")))
                                              (foldl1 Seq [ Assign "successors" (Tail (Head (Var "graph_copy")))
                                                          , While (Not (Eq (Var "successors") Nil))
                                                              (Ite (Eq (Head (Var "successors")) (Var "current"))
                                                                (foldl1 Seq [ Assign "is_reachable" Nil
                                                                            , Assign "successors" Nil
                                                                            ])
                                                                (Assign "successors" (Tail (Var "successors"))))
                                                          , Assign "graph_copy" Nil
                                                          ])
                                              (Assign "graph_copy" (Tail (Var "graph_copy"))))
                                        , Ite (Eq (Var "is_reachable") Nil)
                                            (foldl1 Seq [ Assign "visited" (Append (Var "current") (Var "visited"))
                                                        , Assign "path" (Tail (Var "path"))
                                                        ])
                                            (foldl1 Seq [ Assign "result" (Cons "False" Nil)
                                                        , Assign "path" Nil
                                                        ])
                                        ])
                        ]))
          (foldl1 Seq [ Assign "result" (Cons "False" Nil)
                      , Assign "path" Nil
                      ])
      ])
  ]
--TODO: apend notwendig?

test :: Graph -> Path -> Bool
test g p = maybe undefined id (run [("graph", g), ("path", map return p)] example >>= fmap null . lookup "result")

-- Test with: head $ $(inv 'test) (Just 3628800)

--

type Node = Char

type Graph = [[Node]]

type Path = [Node]

ref :: Graph -> Path -> Bool
ref g p = isWalk' p []
  where isInGraph x = x `elem` map head g
        isReachableFrom x y = case lookup y (map (\str -> (head str, tail str)) g) of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = isReachableFrom x y && x `notElem` (y:ys) && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ "abc"
        , "bd"
        , "c"
        , "dac"
        ]

-- Equivalent test program in Haskell


-- $(partialInv 'ref True [0]) graph True (should result in 17 cycle-free walks)
-- Test with: head $ $(inv 'ref True) (Just 3628800)
