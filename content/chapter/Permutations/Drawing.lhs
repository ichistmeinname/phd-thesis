> {-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
> 
> import Free
> import Control.Monad (MonadPlus(..))
>
> data List m a = Nil | Cons (m a) (m (List m a))
>
> deriving instance Show a => Show (List (Free Sort) a)
> deriving instance Show a => Show (List [] a)
>
> consM :: Monad m => m a -> m (List m a) -> m (List m a)
> consM mx mxs = return (Cons mx mxs)
>
> nilM :: Monad m => m (List m a)
> nilM = return Nil
>
> insert :: Monad m => (m a -> m a -> m Bool) -> m a -> m (List m a) -> m (List m a)
> insert p mx mxs = mxs >>= \xs -> case xs of
>                                   Nil -> consM mx nilM
>                                   Cons my mys -> p mx my >>= \b ->
>                                                  if b then consM mx (consM my mys)
>                                                  else consM my (insert p mx mys)
>
> insertionSort :: Monad m => (m a -> m a -> m Bool) -> m (List m a) -> m (List m a)
> insertionSort p mxs = mxs >>= \xs -> case xs of
>                                        Nil -> nilM
>                                        Cons my mys -> insert p my (insertionSort p mys)

> convert :: Monad m => [a] -> m (List m a)
> convert = foldr (\x xs -> consM (return x) xs) nilM
>
> fromPure :: Free f a -> a
> fromPure (Pure x) = x
>
> nf :: Free Sort (List (Free Sort) a) -> Free Sort [a]
> nf (Pure xs) = case xs of
>                  Nil -> return []
>                  Cons fx fxs -> nf fxs >>= \xs -> return (fromPure fx : xs)
> nf (Impure fx) = case fx of
>                    None -> Impure None
>                    Choice id fx fy -> nf fx >>= \fx' -> nf fy >>= \fy' -> Impure (Choice id (return fx') (return fy'))
>                    
>
> decisions1 :: IO ()
> decisions1 = putStrLn (pretty (insertionSort cmp (convert [(1 :: Int)..3])))

> headM :: MonadPlus m => m (List m a) -> m a
> headM mxs = mxs >>= \xs -> case xs of
>                              Nil -> mzero
>                              Cons mz _ -> mz
>
> tailM :: MonadPlus m => m (List m a) -> m (List m a)
> tailM mxs = mxs >>= \xs -> case xs of
>                              Nil -> mzero
>                              Cons _ mzs -> mzs

> pickMin :: MonadPlus m => (m a -> m a -> m Bool)
>         -> m (List m a) -> m (List m a)
> pickMin p mxs = mxs >>= \xs ->
>                 case xs of
>                   Cons my mys -> mys >>= \ys ->
>                     case ys of
>                       Nil -> consM my nilM
>                       _ -> return (pickMin p mys) >>= \mShare ->
>                            return (headM mShare) >>= \mz ->
>                            p my mz >>= \b ->
>                            if b then consM my (return ys)
>                            else consM mz (consM my (tailM mShare))
>                   Nil -> mzero

> decisions2 :: IO ()
> decisions2 = putStrLn (pretty (pickMin cmp (convert [(1 :: Int)..3])))


pickMin :: (a -> a -> Bool) -> [a] -> (a,[a])
pickMin _ [x]     = (x,[])
pickMin p (x:xs@(_ : _))  =  let (m,l) = pickMin p xs
                             in if p x m then (x,xs) else (m,x:l)
