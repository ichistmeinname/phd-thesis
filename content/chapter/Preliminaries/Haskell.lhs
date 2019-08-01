\section{Functional Programming}


\begin{itemize}
\item non-strictness and laziness
\item type-classes: Monads
\item modelling side-effects with monads
\item free monad?
\end{itemize}

\subsection{Non-strictness and Laziness}

\subsection{Modelling Side-Effects}

As a pure language, Haskell does not allow any side-effects unless they are explicitly modeled.
We can, for example, explicitly model partiality using the following data type.

%if False

\begin{code}
data Partial a = Undefined
               | Defined a
  deriving Show
\end{code}

%endif

\begin{minted}{haskell}
data Partial a = Undefined
               || Defined a
\end{minted}

These constructors represent undefined and defined values, respectively.
Note that Haskell also has an ambient effects of partiality: the polymorphic value \hinl{undefined} can be used without any indication on the type-level.
When \hinl{undefined} needs be evaluated, it yields run-time error.
That is, consider the following usages of \hinl{undefined}.

\begin{verbatim}
λ> head undefined
*** Exception: Prelude.undefined

λ> 1 : 2 : undefined
[1,2*** Exception: Prelude.undefined
\end{verbatim}

Using the \hinl{Partial} type, we can model a function that access the head of a list that explicitly yields \hinl{Undefined} value instead of a run-time error.

%if False

\begin{code}
headPartial :: [a] -> Partial a
headPartial []    = Undefined
headPartial (x:_) = Defined x
\end{code}

%endif

\begin{minted}{haskell}
headPartial :: [a] -> Partial a
headPartial []    = Undefined
headPartial (x:_) = Defined x
\end{minted}

Another prominent example for an explicitly modeled side-effect is non-determinism.
We model functions that possibly produce several results using lists.
In order to not confuse the modeled non-determinism with lists that we use algebraic datatypes, we use a type synonym \hinl{ND}.
On top of that, we use the following convenient functions to yield a deterministic result and combine two potentially non-deterministic results.

%if False

\begin{code}
type ND a = [a]

det :: a -> ND a
det x = [x]

(?) :: ND a -> ND a -> ND a
(?) = (++)
\end{code}

The former function yields a singleton list whereas the latter corresponds to concatenating the two lists.

%endif


\begin{minted}{haskell}
type ND a = [a]
\end{minted}

Using this representation of non-determinism, we define a function that non-deterministically inserts a given element at all possible positions of a list.

%if False

\begin{code}
insertND :: a -> [a] -> ND [a]
insertND x []     = [[x]]
insertND x (y:ys) = let zs = insertND x ys in (x : y : ys) : map (y:) zs
\end{code}

%endif

\begin{minted}{haskell}
insertND :: a -> [a] -> ND [a]
insertND x []     = det [x]
insertND x (y:ys) = det (x : y : ys) ? map (y:) (insertND x ys)
\end{minted}

The first rule is deterministic, it yields one list as result that contains just the element \hinl{x} we want to insert to the list.
The second case yields at least two results.
The first non-deterministic result inserts the element in front of the list.
For the second result, we produce all non-deterministic lists for the recursive call \hinl{insertND x ys} and insert the first element \hinl{y} to the front of all these resulting lists.

As an example, we insert \hinl{1} non-deterministically into the list \hinl{[2..5]}.
Note that we manipulate the output to use set-like parentheses for the lists that correspond to the modeled non-determinism of type \hinl{ND}.

\begin{verbatim}
λ> insertND 1 []
{ [1] }

λ> insertND 1 [2..5]
{ [1,2,3,4,5] , [2,1,3,4,5] , [2,3,1,4,5] , [2,3,4,1,5] , [2,3,4,5,1] }
\end{verbatim}

A commonly used abstraction to model side-effects are monads.
Using a type constructor class, a monad provides the following two operations.

\begin{minted}{haskell}
class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b
\end{minted}

A type constructor class allows to define overloaded functions for type constructors like \hinl{Partial} or \hinl{[]}.
Note that we define an instance for \hinl{[]} instead of \hinl{ND}, because we can define type class instances for data types only, not for type synonyms.
That is, we can define type class instances for our modeled side-effects \hinl{Partial} and \hinl{[]} as follows\footnote{Strictly speaking, the instance for lists is already predefined.}.

%if False

\begin{code}
instance Functor Partial where
  fmap f (Defined x) = Defined (f x)
  fmap f Undefined   = Undefined

instance Applicative Partial where
  pure = Defined
  Defined f <*> Defined x = Defined (f x)
  _         <*> _         = Undefined

instance Monad Partial where
  return = Defined
  Defined x >>= f = f x
  Undefined >>= f = Undefined
\end{code}

%endif

\begin{minted}{haskell}
instance Monad Partial where
  return = Defined
  Defined x >>= f = f x
  Undefined >>= f = Undefined

instance Monad [] where
  return   = det
  xs >>= f = concat (map f xs)
\end{minted}

We reimplement the definition of \hinl{insertND} using \hinl{(>>=)} as follows, which leads to a more natural implementation concerning the seperation of operation on lists as data structures and lists as model for non-determinism.
More precisely, the \hinl{(>>=)}-operator gives us access to each list of the non-deterministic result.

%if False

\begin{code}
insertM :: a -> [a] -> ND [a]
insertM x []     = return [x]
insertM x (y:ys) = return (x : y : ys) ? (insertM x ys >>= \zs -> return (y:zs))
\end{code}

%endif

\begin{minted}{haskell}
insertND :: a -> [a] -> ND [a]
insertND x []     = return [x]
insertND x (y:ys) = return (x : y : ys)
                  ? (insertND x ys >>= \zs -> return (y:zs))
\end{minted}

\subsection{Free Monad}
