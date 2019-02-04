\section{Non-deterministic Sorting Functions in Haskell}

After discussing non-deterministic sorting functions in a language with built-in non-determinism, we switch to Haskell as exemplary functional language without non-determinism.
We reimplement a selection of the sorting functions introduced in the \autoref{sec:NDCurry} in Haskell using a naive modell of non-determinism based on lists.
As we want to test out different models later, we already start with a monad-generic implementation for the sorting algorithm and the non-deterministic comparison function |coinCmp|.

We will notice a difference between the Curry and the Haskell implementation when testing the sorting functions on concrete lists.
This difference is not a new insight, but interesting nonetheless: Curry's non-determinism can exploit non-strictness in a way the Haskell model of non-determinism using a monadic interface cannot.

Last but not least, we reexamine the sorting algorithms that compute duplicate permutations and discuss how we can prevent these results in the Haskell implementation.
Due to the general monadic interface, we can use a state-based monad that keeps track of the decisions when applying the comparision functions.
This way, the comparison function can behave in a consistent way; consistency is the property that we already discussed in the context of bubble sort in \autoref{subsec:CurryBubble}.
In addition to consistency, we discuss other properties of the comparision function that are necessary in the Haskell implementation of bubble sort and quick sort.

\subsection{Modelling Non-determinism}

In a pure functional language like Haskell, we can express non-deterministic function using lists to represent multiple non-deterministic results.
In order to distinguish between list values that are used to model non-determinism and list values in the common sense, we introduce the following type synonym |ND|, which is basically a renaming of the list data type.

> type ND a = [a]

When working with non-deterministic computations represented as |ND|, we need a mechanism to define functions that yield non-deterministic results and to use non-deterministic computations as arguments of these functions.
In the list model we can use the function |concatMap :: (a -> ND b) -> ND a -> ND b| to apply a non-deterministic function on a non-deterministic computation and cobmine all non-deterministic results via concatenation.

Let us, for example, consider the Haskell function |filterND :: (a -> ND Bool) -> [a] -> ND [a]|, which is a non-deterministic extension of the the higher-order function |filter|.

> filterND :: (a -> ND Bool) -> [a] -> ND [a]
> filterND _ []     = [[]]
> filterND f (x:xs) = concatMap (\p -> if p then concatMap (\ys -> [x:ys]) (filterND f xs) else filterND f xs) (f x)

Note that we need to process the potentially non-deterministic computations resulting from the predicate check |f x| and the recursive call |filterND f xs| using |concatMap| to handle each possible value of the computation.
Since the definition using |concatMap| explictely is more complicated than necessary, we give an alternative version using list comprehensions.

> filterNDC :: (a -> ND Bool) -> [a] -> ND [a]
> filterNDC _ []     = [[]]
> filterNDC f (x:xs) = [if p then x:ys else ys | p <- f x, ys <- filterND f xs]

Thanks to the list comprehension, the mapping over all non-deterministic computations becomes more apparent.
Since list comprehensions are just a special syntatic sugar for monadic operations, a natural next step is to generalise the definition of |filterND| to any monadic effect.
That is, instead of explicitely using lists to model non-determinism, we solely rely on the abstractions provided by monads.
The resulting definition is |filterM|\footnote{Note that the definition of |filterM| is based on the |Applicative| instead of |Monad| type class now. \url{http://hackage.haskell.org/package/base-4.12.0.0/docs/src/Control.Monad.html#filterM} (last accessed: 2019-02-04)}.

> filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM _ []      = return []
> filterM f (x:xs)  = f x >>= \p -> if p then filterM f xs >>= \ys -> return (x:ys) else filterM f xs

Note that the list-specific operations to lift a value and to combine all results of effectful computation correspond to the monadic |return| and |(>>=)| operations.
As a side note, consider the following urge to outsource the duplicate call to |filterM f xs| in both branches of the if-then-else-expression.

> filterM' :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM' _ []      = return []
> filterM' f (x:xs)  = f x >>= \p -> filterM f xs >>= \ys -> return (if p then x:ys else ys)

This transformation that computes the non-deterministic computation |filterM f xs| only once, is still equivalent to |filterM|.
As an example, we instantiate the monadic contexts with list to illustrate the behaviour of a non-deterministic version of |filter|.

\begin{spec}
replHS> filterM coinCmpList [1,2,3]
[[1,2,3],[1,2],[1,3],[1],[2,3],[2],[3],[]]

replHS> filterM' coinCmpList [1,2,3]
[[1,2,3],[1,2],[1,3],[1],[2,3],[2],[3],[]]
\end{spec}

Here, the non-deterministic comparision function |coinCmpList| that we have used in Curry before, transmits easily to the list model in Haskell.

> coinCmpList :: a -> a -> ND Bool
> coinCmpList _ _ = [True,False]

We must be aware, however, that the transformation is only valid because we use the result of |filterM f xs| in both branches of the if-then-else-expression.
Consider the following non-deterministic version of the function insert and its alternative definition |insertM'|.

> insertM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
> insertM _ x []     = return [x]
> insertM p x (y:ys) = p x y >>= \b -> if b then return (x:y:ys) else insertM p x ys >>= \zs -> return (y:zs)

> insertM' :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
> insertM' _ x []     = return [x]
> insertM' p x (y:ys) = p x y >>= \b -> insertM' p x ys >>= \zs -> return (if b then x:y:ys else y:zs)

The alternative version |insertM'| computes the potentially non-deterministic computation of the recursive call to |insertM; p x ys| before checking the condition |b| does not behave as the original version of |insertM| anymore.
 
\begin{spec}
replHS> insertM coinCmpList 1 [2,3]
[[1,2,3],[2,1,3],[2,3,1]]

replHS> insertM' coinCmpList 1 [2,3]
[[1,2,3],[1,2,3],[2,1,3],[2,3,1]]
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


 \begin{itemize}
\item using list monad
\item generalisation to arbitrary monad: enables usage of set-based instance as well
\end{itemize}

\subsection{Exemplary Sorting Functions}
\begin{itemize}
\item monadic abstraction for sorting function sufficient; |?|-like operator only necessary for comparison function
\end{itemize}

\subsection{Curry vs Monadic Non-determinism}
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
