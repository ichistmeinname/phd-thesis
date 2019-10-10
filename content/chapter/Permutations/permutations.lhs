%if False

> {-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

> import Control.Monad (MonadPlus(..))
> import Control.Applicative (Alternative(..))

%endif

\section{Non-deterministic Sorting Functions in Haskell}

After discussing non-deterministic sorting functions in the functional language Curry with built-in non-determinism, we switch to Haskell as an exemplary functional language without non-determinism.
We reimplement a selection of the sorting functions introduced in the \autoref{sec:NDCurry} in Haskell using a naive model of non-determinism based on lists.
As we want to test out different models later, we refactor the list-specific implementations to monad-generic implementations for the sorting algorithm.

We will notice a difference between the Curry and the Haskell implementation when testing the sorting functions on concrete lists.
This difference is not a new insight, but interesting nonetheless: Curry's non-determinism can exploit non-strictness in a way the Haskell model of non-determinism using a monadic interface cannot.

\subsection{Modeling Non-determinism}

In a pure functional language like Haskell, we can express non-deterministic function using lists to represent multiple non-deterministic results as we have already introduced and discussed in \autoref{subsec:monadicAbstractions}.
That is, we reuse the type synonym \hinl{ND} in order to distinguish between list values that are used to model non-determinism and list values in the common sense.
Recall that we use the monadic operations \hinl{return} and \hinl{(>>=)} for lists when working with \hinl{ND} as well as the convenience operator \hinl{(?)} to combine multiple non-deterministic results.

\begin{minted}{haskell}
instance Monad ND where
  return x = [x]
  xs >>= f = concat (map f xs)

(?) :: ND a -> ND a -> ND a
(?) = (++)
\end{minted}
     
Using the monadic abstraction and the helper function, we can define the non-deterministic comparison function \hinl{coinCmpND} --- corresponding to the function \hinl{coinCmp} that we have used in Curry before, which transfers easily to the list model in Haskell.

%if False

> coinCmpND :: a -> a -> ND Bool
> coinCmpND _ _ = return True ? return False

%endif

\begin{minted}{haskell}
coinCmpND :: a -> a -> ND Bool
coinCmpND _ _ = [True] ? [False]
\end{minted}

\paragraph{Example: Non-deterministic application of filter}
Equipped with these auxiliary functions, let us consider the Haskell function \hinl{filterND :: (a -> ND Bool) -> [a] -> ND [a]}, which is a non-deterministic extension of the higher-order function \hinl{filter}.

%if False

> filterND :: (a -> ND Bool) -> [a] -> ND [a]
> filterND _ []      = return []
> filterND p (x:xs)  = p x >>= \b ->
>                      if b then filterND p xs >>= \ys -> return (x:ys)
>                           else filterND p xs

%endif

\begin{minted}{haskell}
filterND _ []     = return []
filterND p (x:xs) = p x >>= \b ->
                    if b then filterND p xs >>= \ys -> return (x:ys)
                         else filterND p xs
\end{minted}

Note that the potentially non-deterministic values occur in the result of the predicate and in the resulting type of the overall function \hinl{filterND}; moreover, the input list is a deterministic argument.
We need to process the potentially non-deterministic computations resulting from the predicate check \hinl{p x} and the recursive call \hinl{filterND p xs} using \hinl{(>>=)} to handle each possible value of the computation.
The attentive reader notices that the definition of \hinl{filterND} is not specific to the specified type \hinl{ND}, but works for any monad.
That is, since we solely rely on the abstractions provided by monads, we can generalise the type definition.
The resulting definition is \hinl{filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]}; the implementation stays the same.\footnote{Note that the definition of \hinl{filterM} is based on the \hinl{Applicative} instead of \hinl{Monad} type class now. \url{http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad.html\#v:filterM} (last accessed: 2019-09-10)}

%if False

> filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM _ []      = return []
> filterM f (x:xs)  =  f x >>= \p ->
>                      if p  then filterM f xs >>= \ys -> return (x:ys)
>                            else filterM f xs

%endif

When running concrete example, we then instantiate the monadic contexts with \hinl{ND} to illustrate the behaviour of a non-deterministic version.

Since \hinl{filter} needs to be applied to a unary predicate, we partially apply \hinl{coinCmpND} with \hinl{42} in the examples.

\begin{hrepl}
\haskellrepl filterM (coinCmpND 42) [1,2,3]
\{ [1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], [] \}
\end{hrepl}

As a side note, consider the following urge to outsource the duplicate call to \hinl{filterM p xs} in both branches of the if-then-else-expression.

%if False
   
> filterM' :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM' _ []      = return []
> filterM' f (x:xs)  =  f x >>= \p ->
>                       filterM' f xs >>= \ys ->
>                       return (if p then x:ys else ys)

%endif

\begin{minted}{haskell}
filterM' :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM' _ []     = return []
filterM' f (x:xs) = f x >>= \p ->
                    filterM' f xs >>= \ys ->
                    return (if p then x:ys else ys)
\end{minted}

This transformation, which computes the non-deterministic computation \hinl{filterM p xs} only once, is still equivalent to the original implementation of \hinl{filterM}.

\begin{hrepl}
\haskellrepl filterM' (coinCmpND 42) [1,2,3]
\{ [1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], [] \}
\end{hrepl}

We must be aware, however, that the transformation is only valid because we use the result of \hinl{filterM p xs} in both branches of the if-then-else-expression.
In the next paragraph we discuss an example that yields different results before and after the transformation.

\paragraph{Example: Non-deterministic application of insert}
Consider the following two monadic versions of the function \cinl{insert} we defined in Curry.

%if False
         
> insertM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
> insertM _ x []     = return [x]
> insertM p x (y:ys) =  p x y >>= \b ->
>                       if b  then return (x:y:ys)
>                             else insertM p x ys >>= \zs -> return (y:zs)

> insertM' :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
> insertM' _ x []     = return [x]
> insertM' p x (y:ys) =  p x y >>= \b ->
>                        insertM' p x ys >>= \zs ->
>                        return (if b then x:y:ys else y:zs)

%endif

\begin{minted}{haskell}
insertM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
insertM _ x []     = return [x]
insertM p x (y:ys) = p x y >>= \b ->
                     if b  then return (x:y:ys)
                           else insertM p x ys >>= \zs -> return (y:zs)

insertM' :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
insertM' _ x []     = return [x]
insertM' p x (y:ys) = p x y >>= \b ->
                      insertM' p x ys >>= \zs ->
                      return (if b then x:y:ys else y:zs)
\end{minted}

The alternative version \hinl{insertM'} computes the potentially non-deterministic computation of the recursive call to \hinl{insertM; p x ys} before checking the condition \hinl{b} such that it does not behave as the original version of \hinl{insertM} anymore.
 
\begin{hrepl}
\haskellrepl insertM coinCmpND 1 [2,3]
\{ [1,2,3], [2,1,3], [2,3,1] \}

\haskellrepl insertM' coinCmpND 1 [2,3]
\{ [1,2,3], [1,2,3], [2,1,3], [2,3,1] \}
\end{hrepl}

The exemplary calls using the non-deterministic comparison function \hinl{coinCmpND} do not yield the same results.
When we apply a monadic version of insert to \hinl{coinCmpND}, we expect $n+1$ results for a input list of length $n$ --- the same result we observed in Curry.
The application \hinl{insertM' coinCmpND}, however, yields $2^n$ results.

\begin{hrepl}
\haskellrepl length (insertM' coinCmpND 1 [2,3])
4

\haskellrepl length (insertM' coinCmpND 1 [2..4])
8

\haskellrepl length (insertM' coinCmpND 1 [2..11])
1024
\end{hrepl}

Due to the call to \hinl{insertM' p x ys} before checking the Boolean value \hinl{b}, we need to evaluate the recursive call, even though we do not need the resulting variable binding \hinl{zs} when taking the else-branch.
The important insight is that we need to be careful when using the \hinl{(>>=)}-operator.
In most settings, and the list instance is no exception, \hinl{(>>=)} needs to be interpreted as a sequencing operator that is strict in its first argument.
That is, if we have an expression \hinl{mx >>= f}, we cannot proceed with \hinl{f} without evaluating \hinl{mx} first.

In order to check the claim about the strictness of \hinl{(>>=)} in case of \hinl{ND}, recall that the corresponding \hinl{Monad} instance for \hinl{ND} is the one for lists based on \hinl{concat} and \hinl{map}
That is, let us retake a look at the definition of \hinl{concat} to see that the resulting function is indeed strict in its argument of type \hinl{ND a}.

\begin{minted}{haskell}
concat :: [[a]] -> [a]
concat []     = []
concat (xs:xss) = xs ++ xxss
\end{minted}

The function definition of \hinl{concat} makes a case distinction on its first argument.
That is, in order to evaluate an expression like

\begin{minted}{haskell}
insertM' p x ys >>= \zs -> return (if b then x:y:ys else y:zs)
\end{minted}

\noindent we need to evaluate \hinl{insertM' p x ys} first.
In this example, we trigger the evaluation of the non-deterministic comparison function \hinl{coinCmp} although we do not need the result \hinl{zs} if the condition \hinl{b} is \hinl{True}.

As example, consider the excerpt of a step-wise evaluation of the example from above listed in \autoref{fig:filterMStep}.
Note that we need to evaluate \hinl{filterM' (coinCmpND 42) [1,2,3]} and all recursive calls of \hinl{filterM'} that arise during evaluation.

\begin{figure}
\plainhs
\begin{spec}
  filterM' (coinCmpND 42) [1,2,3]
= {- Definition of |filterM'| -}
  coinCmpND 42 1  >>= \p -> filterM' (coinCmpND 42) [2,3]
                  >>= \ys -> return (if p then 1:ys else ys)
= {- Definition of |coinCmpND| -}
  [True, False] >>= \p ->  filterM' (coinCmpND 42) [2,3] >>= \ys ->
                           return (if p then 1:ys else ys)
= {- Definition of |(>>=)| -}
  filterM' (coinCmpND 42) [2,3] >>= \ys -> return (if True then 1:ys else ys)
  ++
  [False] >>= \p ->  filterM' (coinCmpND 42) [2,3] >>= \ys ->
                     return (if p then 1:ys else ys)
= {- Definition of |(>>=)| -}
  filterM' (coinCmpND 42) [2,3] >>= \ys -> return (if True then 1:ys else ys)
  ++
  filterM' (coinCmpND 42) [2,3] >>= \ys -> return (if False then 1:ys else ys)
  ++
  [] >>= \p ->  filterM' (coinCmpND 42) [2,3] >>= \ys ->
                 return (if False then 1:ys else ys)
= {- Definition of |filterM'| -}
  (coinCmpND 42 2 >>= \p ->  filterM' (coinCmpND 42) [3] >>= \ys ->
                             return (if p then 1:ys else ys)) >>= \ys ->
  return (if True then 1:ys else ys)
  ++ ... ++ ...
= {- Definition of |coinCmpND| -}
  [True, False] >>= \p ->  filterM' (coinCmpND 42) [3] >>= \ys ->
                           return (if p then 1:ys else ys)) >>= \ys ->
  return (if True then x:ys else ys)
  ++ ... ++ ...
= {- Definition of |(>>=)| -}
  (filterM' (coinCmpND 42) [3] >>= \ys -> return (if True then 1:ys else ys)
   ++ filterM' (coinCmpND 42) [3] >>= \ys -> return (if False then 1:ys else ys)
   ++ [] >>= \p ->  filterM' (coinCmpND 42) [3] >>= \ys ->
                    return (if p then 1:ys else ys)) >>= \ys ->
  return (if True then 1:ys else ys)
  ++ ... ++ ...
= {- Definition of |filterM'| -}
  ...
\end{spec}
\framedhs
\caption{Extract of a step-wise evaluation of \hinl{filterM' (coinCmpND 42) [1,2,3]}}
\label{fig:filterMStep}
\end{figure}

\subsection{Drawing Decision Trees}
\label{subsec:drawing}

Thanks to the generic implementation using a monadic interface, we are free to use whatever instance fits our purpose to actually run the sorting functions.
For example, we can generate decision trees like in Curry by using a monad that keeps track of all operations and pretty prints the non-deterministic parts of our computation.
As first step, we generalise the comparison function \hinl{coinCmpND} to \hinl{MonadPlus}, which is an extension of the \hinl{Monad} type class that introduces an additional function \hinl{mplus} to combine monadic computations and \hinl{mzero} as neutral element for the function \hinl{mplus}.

\begin{minted}{haskell}
class Monad m => MonadPlus m where
  mplus :: m a -> m a -> m a
  mzero :: m a
\end{minted}

The idea of the non-deterministic comparison function \hinl{coinCmpND} is to yield two results non-deterministically.
In the concrete implementation using lists, we define \hinl{coinCmpND} based on singleton lists \hinl{[True]} and \hinl{[False]} that are combined using the concatenation operator \hinl{(++)}.
A generalisation using \hinl{MonadPlus} replaces the concatenation operator by \hinl{mplus}.

%if False

> coinCmp :: MonadPlus m => a -> a -> m Bool
> coinCmp _ _ = return True `mplus` return False

%endif

\begin{minted}{haskell}
coinCmp :: MonadPlus m => a -> a -> m Bool
coinCmp _ _ = return True `mplus` return False
\end{minted}
  
As second step, we use a monad instance that can interpret all monadic
operations in an abstract way: the free monad \citep{swierstra2008data} we introduced in \autoref{subsec:freeMonad}.
As we are interested in pretty printing the non-deterministic components of our monadic computations, we need a suitable functor to model non-determinism.
The important primitive operations of non-determinism are exactly the ones provided by the \hinl{MonadPlus} type class: an operator to combine two effectful computations and the failing computation.
Note that the simplified version in the introduction (\autoref{subsec:freeMonad}) does not have a representation for the latter computation.
Since we want to print the arguments the non-deterministic comparison function is applied to, we store additional information in the constructor as follows.

%if False

> data Sort a = Choice (Maybe (String,String)) a a | Fail deriving Show

%endif

\begin{minted}{haskell}
data Sort a = Choice (Maybe (String,String)) a a || Fail deriving Show
\end{minted}

In order to use \hinl{Free Sort} as underlying monad in a non-deterministic application of, for example, \hinl{filterM coinCmp}, we need to define a functor instance for \hinl{Sort} and a \hinl{MonadPlus} instance for \hinl{Free Sort}.

%if False

> deriving instance Show a => Show (Free Sort a)
>
> instance Alternative (Free Sort) where
>   empty = mzero
>   (<|>) = mplus

> instance Functor Sort where
>   fmap f (Choice id m1 m2 ) = Choice id (f m1) (f m2)
>   fmap _ Fail = Fail
>
> instance MonadPlus (Free Sort) where
>   mzero = Impure Fail
>   mplus m1 m2 = Impure (Choice Nothing m1 m2)

%endif

\begin{minted}{haskell}
instance Functor Sort where
 fmap f (Choice id m1 m2 ) = Choice id (f m1) (f m2)
 fmap _ Fail = Fail

instance MonadPlus (Free Sort) where
 mzero = Impure Fail
 mplus m1 m2 = Impure (Choice Nothing m1 m2)
\end{minted}

Note that, initially, we do not have any information about the arguments of the \hinl{mplus} operator, so we use \hinl{Nothing}.
We add information to the structure when we apply the function that introduces non-determinism.
For example, we define the non-deterministic function \hinl{cmpCoinFree} that stores the string representation of its arguments and non-deterministically yields \hinl{True} and \hinl{False} as follows.

%if False

> coinCmpFree :: Show a => a -> a -> Free Sort Bool
> coinCmpFree x y =
>   Impure (Choice (Just (show x,show y)) (return True) (return False))

%endif

\begin{minted}{haskell}
coinCmpFree :: Show a => a -> a -> Free Sort Bool
coinCmpFree x y =
  Impure (Choice (Just (show x,show y)) (return True) (return False))
\end{minted}

Now we can apply \hinl{filterM} to our non-determinism-tracking comparison function \hinl{cmpCoinFree} and get a \hinl{Free Sort}-term that contains information about the arguments that need to be compared.

\begin{hrepl}
\haskellrepl filterM (coinCmpFree 42) [1,2]
Impure (Choice  (Just ("42","1"))
                (Impure (Choice (Just ("42","2")) (Pure [1,2])  (Pure [1])))
                (Impure (Choice (Just ("42","2")) (Pure [2])    (Pure []))))
\end{hrepl}

Since this term representation looks more complicated than helpful, as last step, we define a pretty printing function for \hinl{Free Sort}.
The function
\begin{minted}{haskell}
pretty :: Show a => Free Sort a -> String
\end{minted}
produces a decision tree similar to the one we got to know from Curry.
Now we take a look at the well-arranged decision tree resulting from the above call.

\begin{hrepl}
\haskellrepl putStrLn (pretty (filterM (coinCmpFree 42) [1,2]))
                          +-[1,2]
             +- 42 <= 2  -+
             ||            +-[1]
+- 42 <= 1  -+
             ||            +-[2]
             +- 42 <= 2  -+
                          +-[]
\end{hrepl}

%if False

> pretty :: Show alpha => Free Sort alpha -> String
> pretty = unlines . draw Nothing
> 
> draw :: Show alpha => Maybe Bool -> Free Sort alpha -> [String]
> draw _ (Pure x) = ["+-" ++ show x]
> draw _ (Impure Fail) = ["+- mzero"]
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

%endif

We will use these drawing capabilities in the next section when we compare our implementation of sorting functions in Haskell with the implementation in Curry.

\subsection{Curry versus Monadic Non-determinism}
With this insight about the strictness of \hinl{(>>=)} in mind, we check out the consequences when applying a non-deterministic comparison function to monadic sorting functions.
That is, we transform the Curry implementation discussed in \autoref{sec:NDCurry} to Haskell.

\paragraph{Insertion Sort}\label{par:insert}
As we have just seen the definition of \hinl{insertM}, we start with \hinl{insertionSort}.

%if False

> insertionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> insertionSortM _ []      = return []
> insertionSortM p (x:xs)  = insertionSortM p xs >>= \ys -> insertM p x ys

%endif

\begin{minted}{haskell}
insertionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
insertionSortM _ []     = return []
insertionSortM p (x:xs) = insertionSortM p xs >>= \ys -> insertM p x ys
\end{minted}

Note that is again crucial to introduce potentially non-deterministic values only as result of the comparison function and the result of the function itself.
This observation also applies to the definition of \hinl{insertM}, the input list \hinl{ys} needs to be deterministic.
That is, in order to insert the head element \hinl{x} into the already sorted tail, we unwrap the monadic context using \hinl{(>>=)} and apply \hinl{insertM} to each possible value of the computation \hinl{insertionSortM p xs}.

Applying \hinl{insertionSortM} to \hinl{coinCmpND} and exemplary list values yields the expected permutations, more precisely, exact the permutations of the input list.

\begin{hrepl}
\haskellrepl insertionSortM coinCmpND [1..3]
\{ [1,2,3], [2,1,3], [2,3,1], [1,3,2], [3,1,2], [3,2,1] \}

\haskellrepl let fac n = if n == 0 then 1 else n * fac (n-1) in
        all (\func n -> length (insertionSortM coinCmpND [1..n]) == fac n)
            [1..10]
True
\end{hrepl}

The second example call checks for lists of length 1 to 10, if the number of non-deterministic results is equal to the factorial of the corresponding length, which is indeed the case.
Now we know that both implementations compute the same number of results.
The interesting question is, however, if they behave the same in all contexts.

Recall that the Curry implementation defines \hinl{insertionSortM} using a let-declaration for the recursive call.
This recursive call only has to be evaluated if we demand more than one element of the resulting list.
In the example below, we call \hinl{insertionSort} on a non-empty list to compute the head element of all non-deterministic results and count the number of non-deterministic results afterwards.

\begin{hrepl}
\haskellrepl map (\func n ->  length (insertionSortM coinCmpND [1..n] >>= \func xs ->
                    return (head xs)))
             [5..10]
[120,720,5040,40320,362880,3628800]
\end{hrepl}

Again, we have $n!$ non-deterministic results for an input list of length $n$.
The result illustrates that all resulting permutations need to be computed to yield the corresponding head element.
Next, we compare the behaviour of the Haskell implementation with the Curry implementation \cyinl{insertionSort}.

\begin{cyrepl}
\curryrepl map (\func n -> length (allValues (head (insertionSort coinCmp [1..n]))))
           [5..10]
[16,32,64,128,256,512]
\end{cyrepl}

In Curry we do not need to evaluate all non-deterministic computations to yield the head element.
Instead of $n!$ number of non-deterministic results, we only get $2^{(n-1)}$ results for an input list of length $n$.
The crucial difference between the Haskell and the Curry implementation with respect to the model of non-determinism is that Haskell's non-determinism is flat, while in Curry non-deterministic computations can occur in arbitrarily deep positions.
Here, deep position means that the non-determinism is not visible at the outermost constructor, but hides in the component of a constructor.

Consider the following non-deterministic expression \cinl{exp} of type \cinl{[Bool]} and its projection to the head element and tail, respectively, in Curry.

\begin{cyrepl}
\curryrepl let exp = True : ([] ? [False]) in head exp
True
\curryrepl let exp = True : ([] ? [False]) in tail exp
[]
[False]
\end{cyrepl}

The list \cyinl{exp} is non-deterministic in its tail component, the head element is deterministic and the top-level list constructor \cyinl{(:)} is also deterministic.
That is, on the one hand applying \cyinl{head} to \cyinl{exp} does not trigger any non-determinism, the evaluation yields a deterministic result, namely \cyinl{True}.
On the other hand the non-determinism appears in the overall result when we project to the tail of the list \cyinl{exp}.
This application yields the two results \cyinl{[]} and \cyinl{[False]}.
In contrast, we cannot model the same behaviour in Haskell when using a list-based model for non-deterministic computations.

\begin{hrepl}
\haskellrepl let exp = True : (return [] ? return [False]) in head exp
    * Couldn't match expected type ‘[Bool]’
                  with actual type ‘ND [Bool]’
    * In the second argument of ‘(:)’, namely
        ‘(return [] ? return [False])’
      In the expression: True : (return [] ? return [False])
      In an equation for ‘exp’:
          exp = True : (return [] ? return [False])
\end{hrepl}

The error message says that the list constructor \hinl{(:)} expects a second argument of type \hinl{[Bool]}, but we apply it to an argument of type \hinl{ND [Bool]}.
Due to the explicit modeling of non-determinism that is visible in the type-level, i.e., using \hinl{ND}, we cannot construct non-deterministic computations that occur deep in the arguments of constructors like \hinl{(:)} out of the box.
In contrast, Curry's non-determinism is not visible on the type-level, such that we can use non-determinism expressions in any constructor argument without altering the type of the expression.
We can reconcile the computation we want to express with the explicit non-determinism in Haskell by binding the non-deterministic computation first and reuse the list constructor then.

\begin{hrepl}
\haskellrepl  return [] ? return [False] >>= \func nd ->
       let exp = True : nd in return (head exp)
\{ True, True \}

\haskellrepl  return [] ? return [False] >>= \func nd ->
       let exp = True : nd in return (tail exp)
\{ [], [False] \}
\end{hrepl}

In this case, however, the non-determinism is definitely triggered: even though \hinl{head} does not need to evaluate its tail --- where the non-determinism occurs, the first argument of \hinl{(>>=)} is evaluated.
 The overall computation then yields two results.
All in all, the main insight here is that the non-determinism in Curry can occur deep within data structure components and gives us the possibility to exploit non-strictness.
In contrast, the naive Haskell model using lists can only express flat non-determinism, that is, all possibly deep occurrences of non-determinism are pulled to the top-level.

\paragraph{Selection Sort}

Whereas the application of insertion sort to a non-deterministic comparison function yields the same number of results for the Haskell as well as the Curry implementation, we will now take a look at an example that yields duplicate results: selection sort.
We directly define the version of selection sort that uses \hinl{pickMinM} instead of traversing the list twice.

%if False
   
> pickMinM :: Monad m => (a -> a -> m Bool) -> [a] -> m (a, [a])
> pickMinM _ [x] = return (x,[])
> pickMinM p (x:xs) =  pickMinM p xs >>= \(m,l) ->
>                      p x m >>= \b ->
>                      return (if b then (x,xs) else (m, x:l))
>
> selectionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> selectionSortM _ []  = return []
> selectionSortM p xs  =  pickMinM p xs >>= \(m,l) ->
>                         selectionSortM p l >>= \ys ->
>                         return (m:ys)

%endif

\begin{minted}{haskell}
pickMinM :: Monad m => (a -> a -> m Bool) -> [a] -> m (a, [a])
pickMinM _ [x]    = return (x,[])
pickMinM p (x:xs) = pickMinM p xs >>= \(m,l) ->
                    p x m >>= \b ->
                    return (if b then (x,xs) else (m, x:l))

selectionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
selectionSortM _ [] = return []
selectionSortM p xs = pickMinM p xs >>= \(m,l) ->
                      selectionSortM p l >>= \ys ->
                      return (m:ys)
\end{minted}

The application of \hinl{selectionSortM} to \hinl{coinCmpND} yields more results than expected, the resulting function enumerates some permutations multiple times.

\begin{hrepl}
\haskellrepl selectionSortM coinCmpND [1,2,3]
\{ [1,2,3], [1,3,2], [2,1,3], [2,3,1], [1,2,3], [1,3,2], [3,1,2], [3,2,1] \}

\haskellrepl all (\func n -> length (selectionSortM coinCmpND [1..n]) == $2^(\frac{n*(n-1)}{2})$)
             [1..7]
True
\end{hrepl}

\noindent
In fact, we get
\[
2^{\frac{n (n-1)}{2}}
\]
results for an input list of length $n$.
Note that this function grows much faster than the number of permutations $n!$.
For example, for $n=10$ there are $n! = 3 628 800$ permutations, whereas an application of \hinl{selectionSort} to the list \hinl{[1..10]} yields
\[
2^{\frac{10*9}{2}} = 2^{45} = 35 184 372 088 832
\]
results.

More generally, for $n >= 7$ we have that $n \leq 2^{\frac{n-1}{2}}$ such that we can make the following estimation.

\[
n! \leq n^n \leq {2^{\frac{n-1}{2}}}^n = 2^{\frac{n * (n-1)}{2}}
\]
     
Since the number of results for \hinl{selectionSort} applied to a non-deterministic comparison function differs from the result we got for the Curry implementation, we compare the underlying decision trees.
The non-determinism produced by \hinl{selectionSort} arises from the usage of \hinl{coinCmpND}, which is only evaluated in the auxiliary function \hinl{pickMinM}.
That is, it is sufficient to take a look at the decision tree for a sub-call of \hinl{pickMinM} to detect the different behaviour.
We compute the decision tree displayed left in \autoref{fig:pickDecision} by applying a free monad based data type as described in \autoref{subsec:drawing}.
The right side of the figure recapitulates the decision tree when using the Curry implementation.

\begin{figure}
\begin{minipage}{0.44\textwidth}
\begin{verbatim}
                      +-(1,[2,3])
           +- 1 <= 2 -+
           |          +-(2,[1,3])
+- 2 <= 3 -+
           |          +-(1,[2,3])
           +- 1 <= 3 -+
                      +-(3,[1,2])

\end{verbatim}
\end{minipage}
$\quad$ \vline $\quad$
\begin{minipage}{0.50\textwidth}
\begin{verbatim}
           +- (1, [2,3])
           |
+- 1 <= _ -+
           |          +-(2,[1,3])
           +- 2 <= 3 -+
                      +-(3,[1,2])
\end{verbatim}
\end{minipage}

\caption{Decision trees for the expressions \hinl{pickMinM coinCmpND [1,2,3]} in Haskell (left) and \cyinl{pickMin coinCmp [1,2,3]} in Curry (right)}
\label{fig:pickDecision}
\end{figure}

The monadic version is more strict: the recursive call to \hinl{pickMinM} needs to be evaluated in order to apply the predicate \hinl{p}.
In the Curry version, however, we can already take the \cyinl{True}-branch for the application of \cyinl{p} without considering the recursive call first.
Thus, the first result \cyinl{(1, [2,3])} triggers only one non-deterministic decision in Curry.
Of course, the number of unnecessarily triggered non-deterministic decisions in the Haskell version increases with each recursive call of \hinl{pickMinM}.
That is, when we apply \hinl{pickMinM} to a longer list, the number of duplicate results increases with the length of the list.

\begin{hrepl}
\haskellrepl map  (\func n -> length (pickMinM coinCmpND [1..n] >>= return . fst ))
             [1..20]
[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,
65536,131072,262144,524288]
\end{hrepl}

More precisely, \hinl{pickMinM coinCmpND xs} yields $2^{\hinl{length xs}}$ results, while the Curry version only yields \hinl{length n} results.
Note that the second variant, i.e., the Curry version, is what we expect in the first place: picking a minimum with a non-deterministic predicate is basically a function that non-deterministically yields each element of the list.

In the end, \hinl{pickMinM} and \cyinl{pickMin}, respectively, are the functions used to implement the selection sort algorithm and, thus, determine the number of permutations.
Whereas \cyinl{selectionSort} yields only the permutations of the input list in Curry, we get duplicate permutations in the Haskell version.

\paragraph{Other Sorting Algorithms}

The remaining sorting algorithms discussed in \autoref{sec:NDCurry}, i.e., bubble sort, quick sort and merge sort, yield the same results for the monadic Haskell version as they do in Curry.
 However, we can observe a similar effects as with \hinl{insertionSortM} in \autoref{par:insert} concerning non-strictness.
When we demand only the head elements of all permutations, the monadic Haskell versions need to trigger more non-determinism than is necessary in the Curry version.
\autoref{fig:strictSort} visualises the number of triggered non-deterministic computations that are necessary to compute only the head element of all permutations.
We observe that all Curry implementations (completely coloured bars) compute less non-deterministic computations than all Haskell implementations.
One interesting contrast is the behaviour of bubble sort: the Curry version only needs to trigger one non-deterministic computation for each element of the list.
That is, the number of non-deterministic computations is linear in the length of the list, whereas the Haskell version triggers $n!$ non-deterministic computations for an input list of length $n$.
Note that the evaluation of all permutations for bubble sort needs to trigger $n!$ non-deterministic computations as well, that is, in this case demanding only the head of each permutations is as strict as evaluating all list elements of each permutation.

\begin{figure}
\input{content/figures/permutations}
\caption{Comparison of the number of triggered non-deterministic computations for demanding the head element of all permutations}
\label{fig:strictSort}
\end{figure}

%if False

> bubbleM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> bubbleM _ [x]     = return [x]
> bubbleM p (x:xs)  =  bubbleM p xs >>= \(y:ys) ->
>                      p x y >>= \b ->
>                      return (if b then x : y : ys else y : x : ys)
>
> bubbleSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> bubbleSortM _ [] =  return []
> bubbleSortM p xs =  bubbleM p xs >>= \(y:ys) ->
>                     fmap (y:) (bubbleSortM p ys)

\begin{spec}
\haskellrepl bubbleSortM coinCmpND [1,2,3]
{ [1,2,3], [1,3,2], [2,1,3], [2,3,1], [1,3,2], [1,2,3], [3,1,2], [3,2,1] }
\end{spec}

\begin{figure}
\begin{verbatim}
                                 +-[1,2,3]
                      +- 2 <= 3 -+
                      |          +-[1,3,2]
           +- 1 <= 2 -+
           |          |          +-[2,1,3]
           |          +- 1 <= 3 -+
           |                     +-[2,3,1]
+- 2 <= 3 -+
           |                     +-[1,3,2]
           |          +- 3 <= 2 -+
           |          |          +-[1,2,3]
           +- 1 <= 3 -+
                      |          +-[3,1,2]
                      +- 1 <= 2 -+
                                 +-[3,2,1]
\end{verbatim}
\caption{Decision tree for the expression |bubbleSortM coinCmpND [1,2,3]|}
\label{fig:bubbleDecision}
\end{figure}

> partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
> partitionM _ []      = return ([],[])
> partitionM p (x:xs)  = do
>   b <- p x
>   (ys,zs) <- partitionM p xs
>   return (if b then (x:ys,zs) else (ys,x:zs))
>
> quickSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> quickSortM _ []      = return []
> quickSortM p (x:xs)  = do
>   (ys,zs) <- partitionM (\y -> p y x) xs
>   ys' <- quickSortM p ys
>   zs' <- quickSortM p zs
>   return (ys' ++ [x] ++ zs')

> quickSortFilterM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> quickSortFilterM _ []      = return []
> quickSortFilterM p (x:xs)  = do
>   ys <- filterM (\y -> p y x) xs
>   zs <- filterM (\y -> fmap not (p y x)) xs
>   ys' <- quickSortFilterM p ys
>   zs' <- quickSortFilterM p zs
>   return (ys' ++ [x] ++ zs')


> divideN :: [a] -> ([a],[a])
> divideN xs = divideN' xs (length xs `div` 2)
>  where  divideN' []      _  = ([],[])
>         divideN' (y:ys)  n  | n == 0     = ([],y:ys)
>                             | otherwise  =  let (l1,l2) = divideN' ys (n-1)
>                                             in (y:l1,l2)
>
> mergeM :: Monad m => (a -> a -> m Bool) -> [a] -> [a] -> m [a]
> mergeM _ []     l       = return l
> mergeM _ (x:xs) []      = return (x:xs)
> mergeM p (x:xs) (y:ys)  = do
>   b <- p x y
>   if b then mergeM p xs (y:ys) >>= return . (x:)
>        else mergeM p (x:xs) ys >>= return . (y:)
>
> mergeSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> mergeSortM _ []               = return []
> mergeSortM _ [x]              = return [x]
> mergeSortM p l@(_ : (_ : _))  = do
>   let (ys,zs) = divideN l
>   ys' <- mergeSortM p ys
>   zs' <- mergeSortM p zs
>   mergeM p ys' zs'

\subsection{Getting Rid of Duplicates}
\begin{itemize}
\item drawing decision tree using free monad
\item properties of predicates to prevent duplicates
  \begin{itemize}
  \item state monad to track result of compared pairs
  \item consistency, totality, transitivity
  \end{itemize}
\end{itemize}

%endif
