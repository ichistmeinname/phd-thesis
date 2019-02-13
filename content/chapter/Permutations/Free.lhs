> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE GADTs, FlexibleInstances, StandaloneDeriving #-}
>
>module Free where

> import Control.Monad
> import Control.Applicative
>
> data Free f alpha = Pure alpha | Impure (f (Free f alpha))

> deriving instance Show a => Show (Free Sort a)
>

> instance Functor f => Functor (Free f) where
>   fmap f (Pure x) = Pure (f x)
>   fmap f (Impure fx) = Impure (fmap (fmap f) fx)
> 
> instance Functor f => Applicative (Free f) where
> 
> instance Functor f => Monad (Free f) where
>   return = Pure
>   Pure x >>= f = f x
>   Impure fx >>= f = Impure (fmap (>>= f) fx)
> 
> data Sort a = Choice (Maybe (String,String)) a a | None deriving Show
>
> instance Functor Sort where
>   fmap f (Choice id m1 m2 ) = Choice id (f m1) (f m2)
>   fmap f None = None
>
> instance Alternative (Free Sort) where
>   empty = mzero
>   (<|>) = mplus
> 
> instance MonadPlus (Free Sort) where
>   mzero = Impure None
>   mplus m1 m2 = Impure (Choice Nothing m1 m2)
> 
> cmp :: Show alpha => alpha -> alpha -> Free Sort Bool
> cmp x y = Impure (Choice (Just (show x,show y)) (return True) (return False))
>  
> pretty :: Show alpha => Free Sort alpha -> String
> pretty = unlines . draw Nothing
> 
> draw :: Show alpha => Maybe Bool -> Free Sort alpha -> [String]
> draw _ (Pure x) = ["+-" ++ show x]
> draw _ (Impure None) = ["+- mzero"]
> draw topM (Impure (Choice cmp m1 m2)) =
>   map (prefixTop++) m1s
>     ++ cmpStr cmp
>     ++ map (prefixBottom++) m2s
>  where
>   m1s = draw (Just False) m1
>   m2s = draw (Just True) m2
>   prefixTop =
>     case topM of
>          Nothing  -> spaces False
>          Just top -> spaces top
>   prefixBottom =
>     case topM of
>          Nothing  -> spaces False
>          Just top -> spaces (not top)
>   spaces b =
>     (if b then '|' else ' ') : replicate (cmpLength cmp) ' '
>   cmpStr Nothing = ["+--+"]
>   cmpStr (Just (x,y)) = ["+- " ++ x ++ " <= " ++ y ++ " -+"]
>   cmpLength Nothing = 4
>   cmpLength (Just (x,y)) = length x + length y + 8
