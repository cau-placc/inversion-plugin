
{-append [] ys = ys
append (x:xs) ys = x : append xs ys

appendInv ys = ([], ys)
appendInv (x:zs) = case appendInv zs of
  (xs,ys) -> (x:xs, ys)
-}

appendInv :: [a] -> [([a], [a])]
appendInv ys = [([], ys)] ++ (case ys of {[] -> []; x:zs -> appendInv zs >>= \ (xs,ys) -> [(x:xs,ys)]})

--TODO: ..., because 'Int ist einfach ein kack Datentyp' [TeegenPrott2022KackDatentypInt].
--TODO: könnte peano intern für int(eger) nehmen
--TODO: cantor als gegenbeispiel für peano (-> case study)
--TODO: note context on inverse (missing)
--TODO: O(n*m)
--TODO: peano for connection with list length (known from curry, and proving (kai))


--TODO: l-inverse: fInv . f   -> x `elem` fInv (f x) für alle values x
--TODO: r-inverse: map f . fInv   -> map ((== x) . f) (fInv x) für alle values x




--TODO: Num instanz für peano angeben

{-findrep :: [Int] -> [Int] -> [Int]
findrep [] _  = []
findrep xs [] = xs
findrep (x:xs) -}

----

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

-- :t $(inv 'snoc)


-- $(ioInv 'f [[|| x ||], [|| [free 1] ||]] [|| free 1 ||])

--TODO: (vgl. minikanren post von dmitri) conjunction order problem in prolog/minikanren

reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = reverse2 xs ++ [x]

reverseAcc2 :: [a] -> [a]
reverseAcc2 xs = reverseAcc xs []
  where reverseAcc [] ys = ys
        reverseAcc (x:xs) ys = reverseAcc xs (x:ys)


and'2 :: [Bool] -> Bool
and'2 [] = True
and'2 (False:_) = False
and'2 (_:bs) = and'2 bs

all2 f = and'2 . map f
