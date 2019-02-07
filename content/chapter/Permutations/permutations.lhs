\framedhs
\section{Non-deterministic Sorting Functions in Haskell}

After discussing non-deterministic sorting functions in a language with built-in non-determinism, we switch to Haskell as exemplary functional language without non-determinism.
We reimplement a selection of the sorting functions introduced in the \autoref{sec:NDCurry} in Haskell using a naive modell of non-determinism based on lists.
As we want to test out different models later, we refactor the list-specific implementations to monad-generic implementations for the sorting algorithm.

We will notice a difference between the Curry and the Haskell implementation when testing the sorting functions on concrete lists.
This difference is not a new insight, but interesting nonetheless: Curry's non-determinism can exploit non-strictness in a way the Haskell model of non-determinism using a monadic interface cannot.

Last but not least, we reexamine the sorting algorithms that compute duplicate permutations and discuss how we can prevent these results in the Haskell implementation.
Due to the general monadic interface, we can use a state-based monad that keeps track of the decisions when applying the comparision functions.
This way, the comparison function can behave in a consistent way; consistency is the property that we already discussed in the context of bubble sort in \autoref{subsec:CurryBubble}.
In addition to consistency, we discuss other properties of the comparision function that are necessary in the Haskell implementation of bubble sort and quick sort.

\subsection{Modelling Non-determinism}

In a pure functional language like Haskell, we can express non-deterministic function using lists to represent multiple non-deterministic results.
In order to distinguish between list values that are used to model non-determinism and list values in the common sense, we introduce the following data type |ND|, which is basically a renaming of the list data type.
We define a new data type in order to define a custom show instance --- otherwise we could have also used a typesynonym for lists instead.

> data ND a = Nil | Cons a (ND a)

%if False

> instance Show a => Show (ND a) where
>   show Nil = "{ }"
>   show xs@(Cons _ _) = "{ " ++ showCommaSep xs ++ " }"
>    where showCommaSep (Cons y Nil)          = show y
>          showCommaSep (Cons y ys@(Cons _ _)) = show y ++ ", " ++ showCommaSep ys

%endif

When working with non-deterministic computations represented as |ND|, we need a mechanism to define functions that yield non-deterministic results and to use non-deterministic computations as arguments of these functions.
In the list model we can use the function |applyND :: (a -> ND b) -> ND a -> ND b| to apply a non-deterministic function on a non-deterministic computation and cobmine all non-deterministic results via concatenation.
On top of the definition of |applyND|, we introduce a smart constructor for a singleton result to simplify the usage of the |ND| type.

> applyND :: (a -> ND b) -> ND a -> ND b
> applyND f Nil = Nil
> applyND f (Cons x xs) = f x +++ applyND f xs
>  where Nil +++ ys = ys
>        Cons z zs +++ ys = Cons z (zs +++ ys)

> singleton :: a -> ND a
> singleton x = Cons x Nil

Note that, |applyND| corresponds to |concatMap| when using predefined lists.

\paragraph{Example: Non-deterministic definition of filter}
Equipped with these auxiliary functions, let us consider the Haskell function |filterND :: (a -> ND Bool) -> [a] -> ND [a]|, which is a non-deterministic extension of the higher-order function |filter|.

> filterND :: (a -> ND Bool) -> [a] -> ND [a]
> filterND _ []      = singleton []
> filterND p (x:xs)  =
>   applyND (\b -> if b  then applyND (\ys -> singleton (x:ys)) (filterND p xs)
>                        else filterND p xs) (p x)

Note that the potentially non-deterministic values occur in the result of the predicate and in the resulting type of the overall function |filterND|; moreover, the input list is a deterministic argument.
We need to process the potentially non-deterministic computations resulting from the predicate check |f x| and the recursive call |filterND f xs| using |applyND| to handle each possible value of the computation.
Since the definition using |applyND| explictely looks more complicated than necessary, a natural next step is to generalise the definition of |filterND| to any monadic effect.
That is, instead of explicitely using lists to model non-determinism, we solely rely on the abstractions provided by monads.
The resulting definition is |filterM|\footnote{Note that the definition of |filterM| is based on the |Applicative| instead of |Monad| type class now. \url{http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad.html\#v:filterM} (last accessed: 2019-02-05}.

> filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM _ []      = return []
> filterM f (x:xs)  =  f x >>= \p ->
>                      if p  then filterM f xs >>= \ys -> return (x:ys)
>                            else filterM f xs

Note that the list-specific operations to lift a value and to combine all results of effectful computations correspond to the monadic |return| and |(>>=)| operations.
In case of |ND|, we can easliy define a suitable |Monad| instance that implements the necessary operations using |singleton| and |applyND|.

%if False

> instance Functor ND where
>   fmap f Nil = Nil
>   fmap f (Cons x xs) = Cons (f x) (fmap f xs)
>
> instance Applicative ND where
>   pure x = Cons x Nil
>   Nil <*> _ = Nil
>   Cons _ _ <*> Nil = Nil
>   Cons f fxs <*> Cons x xs = Cons (f x) (fxs <*> xs)

%endif

> instance Monad ND where
>   return = singleton
>   nd >>= f = applyND f nd

As an example, we instantiate the monadic contexts with |ND| to illustrate the behaviour of a non-deterministic version of |filter|.
We test the applications with the non-deterministic comparision function |coinCmpList| --- corresponding to the function |coinCmp| that we have used in Curry before, which transmits easily to the list model in Haskell.

> coinCmpList :: a -> a -> ND Bool
> coinCmpList _ _ = Cons True (Cons False Nil)

Since |filter| needs to applied to a unary predicate, we partially apply |coinCmpList| with |42| in the examples.
Applying the orginal definition |filterND| and the generalised version |filterM| yield the same results.

\begin{spec}
replHS> filterND (coinCmpList 42) [1,2,3]
{ [1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], [] }

replHS> filterM (coinCmpList 42) [1,2,3]
{ [1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], [] }
\end{spec}

As a side note, consider the following urge to outsource the duplicate call to |filterM f xs| in both branches of the if-then-else-expression.

> filterM' :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM' _ []      = return []
> filterM' f (x:xs)  =  f x >>= \p ->
>                       filterM' f xs >>= \ys ->
>                       return (if p then x:ys else ys)

This transformation that computes the non-deterministic computation |filterM f xs| only once, is still equivalent to |filterM|.

\begin{spec}
replHS> filterM' (coinCmpList 42) [1,2,3]
{ [1,2,3], [1,2], [1,3], [1], [2,3], [2], [3], [] }
\end{spec}

We must be aware, however, that the transformation is only valid because we use the result of |filterM f xs| in both branches of the if-then-else-expression.

\paragraph{Strictness of |(>>=)| for list monad}
Consider the following non-deterministic version of the function insert and its alternative definition |insertM'|.

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

The alternative version |insertM'| computes the potentially non-deterministic computation of the recursive call to |insertM; p x ys| before checking the condition |b| does not behave as the original version of |insertM| anymore.
 
\begin{spec}
replHS> insertM coinCmpList 1 [2,3]
{ [1,2,3], [2,1,3], [2,3,1] }

replHS> insertM' coinCmpList 1 [2,3]
{ [1,2,3], [1,2,3], [2,1,3], [2,3,1] }
\end{spec}

The exemplary calls using the non-deterministic comparision function |coinCmpList| do not yield the same results.
When we apply a monadic version of |insert| to |coinCmpList|, we expect $n+1$ results for a input list of length $n$ --- the same result we observed in Curry.
The usage of |insertM'|, however, yields $n^2$ results.

\begin{spec}
replHS> length (insertM' coinCmpList 1 [2,3])
4

replHS> length (insertM' coinCmpList 1 [2..4])
8

replHS> length (insertM' coinCmpList 1 [2..11])
1024
\end{spec}

Due to the call to |insertM' p x ys| before checking the boolean value |b|, we need to evaluate the recursive call even though, we do not need to resulting variable binding |zs| when taking the |else|-branch.
The important insight is that we need to be careful when using the |(>>=)|-operator.
In most settings, and the list instance is no exception, |(>>=)| needs to be interpreted as a sequencing operator that is strict in its first argument.
That is, if we have an expression |mx >>= f|, we cannot proceed with |f| without evaluating |mx| first.

In order to check the claim about the strictness of |(>>=)| in case of |ND|, recall that we implemented the |Monad| instance of |ND| using |applyND| for the implementation of |(>>=)|.
That is, let us retake a look at the definition of |applyND| to see that the resulting function is indeed strict in its argument of type |ND a|.

\begin{spec}
applyND :: (a -> ND b) -> ND a -> ND b
applyND f Nil = Nil
applyND f (Cons x xs) = f x +++ applyND f xs
 where Nil +++ ys = ys
       Cons z zs +++ ys = Cons z (zs +++ ys)
\end{spec}

The function definition of |applyND| makes a case distinction on the second argument |ND a|.
That is, in order to evaluate an expression like

\begin{spec}
insertM' p x ys >>= \zs -> return (if b then x:y:ys else y:zs)
\end{spec}

we need to evaluate |insertM' p x ys| first.
In this example, we trigger the evaluation of the non-deterministic comaprision function |coinCmp| although we do not need the result |zs| if |b| is |True|.
Consider the excerpt of a step-wise evaluation of the example from above listed in \autoref{fig:filterMStep}.
Note that we need to evaluate |filterM' (coinCmpList 42) [1,2,3]| and all recursive calls of |filterM'| that arise during evaluation.

\begin{figure}
\plainhs
\begin{spec}
  filterM' (coinCmpList 42) [1,2,3]
= {- Definition of |filterM'| -}
  coinCmpList 42 1  >>= \p -> filterM' (coinCmpList 42) [2,3]
                    >>= \ys -> return (if p then x:ys else ys)
= {- Definition of |coinCmpList| -}
  Cons True (Cons False Nil) >>= \p ->  filterM' (coinCmpList 42) [2,3] >>= \ys ->
                                        return (if p then x:ys else ys)
= {- Definition of |(>>=)| -}
  filterM' (coinCmpList 42) [2,3] >>= \ys -> return (if p then x:ys else ys)
  +++
  Cons False Nil >>= \p ->  filterM' (coinCmpList 42) [2,3] >>= \ys ->
                            return (if p then x:ys else ys)
= {- Definition of |(>>=)| -}
  filterM' (coinCmpList 42) [2,3] >>= \ys -> return (if True then x:ys else ys)
  +++
  filterM' (coinCmpList 42) [2,3] >>= \ys -> return (if False then x:ys else ys)
  +++
  Nil >>= \p ->  filterM' (coinCmpList 42) [2,3] >>= \ys ->
                 return (if False then x:ys else ys)
= {- Definition of |filterM'| -}
  (coinCmpList 42 2 >>= \p ->  filterM' (coinCmpList 42) [3] >>= \ys ->
                               return (if p then x:ys else ys)) >>= \ys ->
  return (if True then x:ys else ys)
  +++ ... +++ ...
= {- Definition of |coinCmpList| -}
  (Cons True (Cons False Nil) >>= \p ->  filterM' (coinCmpList 42) [3] >>= \ys ->
                                         return (if p then x:ys else ys)) >>= \ys ->
  return (if True then x:ys else ys)
  +++ ... +++ ...
= {- Definition of |(>>=)| -}
  (filterM' (coinCmpList 42) [3] >>= \ys -> return (if True then x:ys else ys)
   +++ filterM' (coinCmpList 42) [3] >>= \ys -> return (if False then x:ys else ys)
   +++ Nil >>= \p ->  filterM' (coinCmpList 42) [3] >>= \ys ->
                      return (if p then x:ys else ys)) >>= \ys ->
  return (if True then x:ys else ys)
  +++ ... +++ ...
= {- Definition of |filterM'| -}
  ...
\end{spec}
\framedhs
\caption{Step-wise evaluation of |filterM' (coinCmpList 42) [1,2,3]|}
\label{fig:filterMStep}
\end{figure}

\subsection{Curry vs Monadic Non-determinism}
With this insight about the strictness of |(>>=)| in mind, we check out the consequences when applying a non-deterministic comparision function to monadic sorting functions.
That is, we transform the Curry implementation discussed in \autoref{sec:NDCurry} to Haskell.

\paragraph{InsertionSort}
As we have just seen the definition of |insertM|, we start with |insertionSort|.

> insertionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> insertionSortM _ []      = return []
> insertionSortM p (x:xs)  = insertionSortM p xs >>= \ys -> insertM p x ys

Note that is again crucial to introduced potentially non-deterministic values only as result of the comparison function and the result of the function itself.
This observation also applies to the definition of |insertM|, the input list |ys| needs to be deterministic.
That is, in order to insert the head element |x| into the already sorted tail, we unwrap the monadic context using |(>>=)| and apply |insertM| to each possible value of the computation |insertionSortM p xs|.

Applying |insertionSortM| to |coinCmpList| and exemplary list values, yield the expected permutations, more precisely, exact the permutations of the input list.

\begin{spec}
replHS> insertionSortM coinCmpList [1..3]
{ [1,2,3], [2,1,3], [2,3,1], [1,3,2], [3,1,2], [3,2,1] }

replHS> let fac n = if n == 0 then 1 else n * fac (n-1) in
        all  (\n -> lengthND (insertionSortM coinCmpList [1..n]) == fac n)
             True [1..10]
True
\end{spec}

The second example call checks for lists of length 1 to 10, if the number of non-deterministic results is equal to the factorial of that number, which is indeed the case.
Now we know that both implementations compute the same results.
The interesting question is, however, if they behave the same in all contexts.

Recall that the Curry implementation defines |insertionSortM| using a let-declaration for the recursive call.
This recursive call only has to be evaluated if we demand more than one element of the resulting list.
In the example below, we call |insertionSort| on a non-empty-list to compute the head element of all non-deterministic results and count the number of non-deterministic results afterwards.

\begin{spec}
replHS> map  (\n ->  lengthND (insertionSortM coinCmpList [1..n] >>= \xs ->
                     return (head xs)))
             [5..10]
[120,720,5040,40320,362880,3628800]
\end{spec}

Again, we have $n!$ non-deterministic results for an input list of length $n$.
The result illustrates that all resulting permutations need to be computed to yield the corresponding head element.
Next, we compare the behaviour of the Haskell implementation with the Curry implementation |insertionSort|.

\plainhs
\begin{spec}
repl> map (\n -> length (allValues (head (insertionSort coinCmp [1..(n::Int)])))) [5..10]
[16,32,64,128,256,512]
\end{spec}
\framedhs

Let us reconsider the Curry implementation of |insert| as comparison.

\plainhs
\begin{spec}
insert :: (a -> a -> Bool) -> a -> [a] -> [a]
insert _ x [] = [x]
insert p x (y:ys) = if p x y then x:y:ys else y : insert p x ys
\end{spec}
\framedhs

\begin{itemize}
\item non-determinism is not visible at the type-level
\item non-determinism can occur in constructor components (deep vs. flat)
\item thus, non-determinism can be non-stricter than instances using lists (or trees)
\end{itemize}

\subsection{Getting Rid of Duplicates}
\begin{itemize}
\item drawing decision tree using free monad
\item properties of predicates to prevent duplicates
  \begin{itemize}
  \item state monad to track result of compared pairs
  \item consistency, totality, transitivity
  \end{itemize}
\end{itemize}
