module AVLo where

data Arv a = No a (Arv a) (Arv a)
            | Vazia
            deriving (Show, Eq)

altura :: Arv a -> Int
altura Vazia = 0
altura (No _ esq dir) = 1 + max (altura esq) (altura dir)

desvio :: Arv a -> Int
desvio Vazia = 0
desvio (No _ esq dir) = altura esq - altura dir

pesquisaAVL :: Ord a => a -> Arv a -> Bool
pesquisaAVL x Vazia = False
pesquisaAVL x (No y esq dir)
    | x == y = True
    | x<y = pesquisaAVL x esq
    | x>y = pesquisaAVL x dir

rodarDir :: Arv a -> Arv a
rodarDir (No x (No y t1 t2) t3) = No y t1 (No x t2 t3)
rodarDir t = t -- nada a fazer nos outros casos

rodarEsq :: Arv a -> Arv a
rodarEsq (No x t1 (No y t2 t3)) = No y (No x t1 t2) t3
rodarEsq t = t -- nada a fazer nos outros casos

corrigeDir :: Arv a -> Arv a
corrigeDir (No x t1 t2)
    | desvio t1 == -1 = rodarDir (No x (rodarEsq t1) t2)
    | otherwise = rodarDir (No x t1 t2)
corrigeDir t = t -- nada a fazer noutros casos

corrigeEsq :: Arv a -> Arv a
corrigeEsq (No x t1 t2)
    | desvio t2 == 1 = rodarEsq (No x t1 (rodarDir t2))
    | otherwise = rodarEsq (No x t1 t2)
corrigeEsq t = t -- nada a fazer noutros casos

reequilibrar :: Arv a -> Arv a
reequilibrar t
    | d== 2 = corrigeDir t
    | d== -2 = corrigeEsq t
    | otherwise = t
    where d = desvio t

inserirAVL :: Ord a => a -> Arv a -> Arv a
inserirAVL x Vazia = No x Vazia Vazia
inserirAVL x (No y esq dir)
    | x==y -- já ocorre
    = No y esq dir
    | x<y  -- inserir à esquerda
    = reequilibrar (No y (inserirAVL x esq) dir)
    | x>y-- inserir à direita
    = reequilibrar (No y esq (inserirAVL x dir))

{-removerAVL :: Ord a => a -> Arv a -> Arv a 
removerAVL x Vazia = Vazia
removerAVL x (No y esq dir)
    | x < y = reequilibrar (No y (removerAVL x esq) dir)
    | x > y = reequilibrar (No y esq (removerAVL x dir))
    | otherwise = case (esq, dir) of
        (Vazia, Vazia) -> Vazia
        (Vazia, _) -> dir
        (_, Vazia) -> esq
        _ -> let (minDir, newDir) = removeMin dir
             in reequilibrar (No minDir esq newDir)

removeMin :: Arv a -> (a, Arv a)
removeMin (No y Vazia dir) = (y, dir)
removeMin (No y esq dir) = let (minEsq, newEsq) = removeMin esq
                           in (minEsq, reequilibrar (No y newEsq dir))
                           -}