%if False

\begin{code}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

import Debug.Trace
\end{code}

%endif
        
\section{Functional Programming}

We present all concepts related to pure functional programming in this thesis using the language Haskell.
As we assume a basic familiarity of the reader regarding functional programming in Haskell, we will focus on specific and advanced topics we will make use of.
For a more detailed introduction to Haskell, we recommend interested reader to take a look at other sources \citep{hudak2007history, hutton2016programming}.

First of, we illustrate the advantages and subtleties of Haskell's non-strict and especially lazy evaluation strategy using a handful of examples.
Next we show how to model side-effects that are not allowed otherwise due to Haskell's purity.
We use a monadic abstraction to illustrate how to model partiality and non-determinism.
Finally, we generalise the monadic abstraction to use free monads instead, a representation that we will make use of in different parts of this thesis.

If not expliclity stated differently, we use GHC 8.4.3 to compile and run the presented Haskell code.
We display the interaction with GHC's REPL using a prompt showing a lambda  --- \verb|λ>| --- at the start of each command.

\subsection{Non-strictness and Laziness}

Haskell's evaluation strategy is call-by-need.
That is, subexpressions are only evaluated when explicitly needed and shared expressions only once -- that is, call-by-need combines the advantages of both, call-by-name and call-by-value.

Consider the following example that demonstrates the non-strictness part of Haskell's lazy evaluation.
We compute the head of a partial list: the head element is defined but the remaining list is not.

\begin{verbatim}
λ> head (1 : undefined)
1
\end{verbatim}

Non-strictness allows us to work on partial values and, more importantly, that non-demanded partial values are not computed.
The demand-driven evaluation comes in not only in case of partial values, but also in case of expensive computations.

The next example uses a function that computes the factorial of a given number as representative of such an expensive computation and the function \hinl{const :: a -> b -> a} that ignores its second and yields its first argument.

\begin{verbatim}
λ> const 42 (fac 100)
42
\end{verbatim}

The evaluation immediately yields \hinl{42} as the second argument of \hinl{const} is not demanded, thus, not computed.

The second component of lazy evaluation --- sharing expressions --- is in most cases only observable regarding the performance of programs.
We can, however, observe the difference of a shared expression and an expression that needs to be evaluated multiple times by using Haskell's \hinl{trace} function.
Using \hinl{trace} that is of type \hinl{String -> a -> a} we can print debug messages on the console while evaluating a program.
More precisely, the first argument is the message we want to log and the second argument the expresion we want to log the message for.

In order to illustrate how \hinl{trace} works, consider the following two examples.

\begin{verbatim}
λ> let log42 = trace "fortytwo" 42 in log42 + 103
fortytwo
145

λ> let log42 = trace "fortytwo" 42 in const 103 log42
103
\end{verbatim}

In both cases we want to log the message \hinl{"fortytwo"} when the variable \hinl{log42} is used and \hinl{42} is the actual value that is used to compute with.
The first example logs the message during evaluation and then yields \hinl{145} as result.
In the second example, we do not observe any logging message, because, again, the second argument of \hinl{const} does not need to be computed.

In order to observe that we shared an expression, we consider the following two expressions that doubles a value that is traced as side-effect.

\begin{minted}{haskell}
test1 n = trace "<msg>" n + trace "<msg>" n
test2 n = let x = trace "<msg>" n in x + x
\end{minted}

\begin{verbatim}
λ> test1 42
<msg>
<msg>
84

λ> test2 42
<msg>
84
\end{verbatim}

The first example logs the message two times for each call to \hinl{trace} whereas the second example shares the effectful expression \hinl{trace "<msg>" 42} by binding it to a variable \hinl{x} that is used then used to double the value.
Although the first example \hinl{test1} looks like an inlined version of \hinl{test2}, due to Haskell's call-by-need semantics these expressions have different results when used in combination with a side-effect like tracing.

%if False

\begin{code}
doublePlus :: Int -> Int
doublePlus x = x + x

doubleMult :: Int -> Int
doubleMult x = 2 * x

test1 n = trace "<msg>" n + trace "<msg>" n
test2 n = let x = trace "<msg>" n in x + x
test3 n = doublePlus (trace "<msg>" n)
test4 n = doubleMult (trace "<msg>" n)
\end{code}

%endif


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

\subsection{Modelling Side-Effects Using Free Monads}
\label{subsec:freeMonad}

Recently, the functional programming community uses a slight different approach for modelling side-effects.
The overall monadic structure is still the key of the representation of such effects.
One observation that lead to the other abstraction is that all representations of suce side-effects have operations to lift a value into the effects (\hinl{return}) and to manipulate the values of an effect (\hinl{(>>=)}) in common.
This observation lead to a monad instance that can interpret all monadic operations in an abstract way: the free monad \citep{swierstra2008data}.
Consider the following data type \hinl{Free} that is parametrised of a type constructor \hinl{f} and a value type \hinl{a}.

\begin{minted}{haskell}
data Free f a = Pure a || Impure (f (Free f a))
\end{minted}

The general idea behind free monads is the observation that monadic computations are either pure values or impure effects.
We represent the impure effect using the type constructor \hinl{f} and pure values are of type \hinl{a}.
The nice property of the \hinl{Free} data type is that \hinl{Free f} is a monad, if \hinl{f} is a functor.

\begin{minted}{haskell}
instance Functor f => Monad (Free f) where
  return = Pure
  Pure x >>= f = f x
  Impure fx >>= f = Impure (fmap (>>= f) fx)
\end{minted}

We represent all impure operations we need to model using the functor \hinl{f}.
In case of \hinl{Partial}, we have one operation, namely \hinl{Undefined}; the other constructor \hinl{Defined} is already taken care of by \hinl{Pure}.
Moreover, we observe that \hinl{Undefined} does not contains any further values but is a possible value of its own: it is a nullary operation.
In contrast, we modelled the binary operation \hinl{(?) :: ND a -> ND a -> ND a} for non-determinism that combines two non-deterministic computations.
The corresponding functor, thus, needs to make use of the recursive type argument \hinl{Free f a}.
More concretely, since \hinl{Free} already models the constructor for defined values using \hinl{Pure}, we functors takes care of the values constructed using \hinl{Undefined} for \hinl{Partial} and \hinl{(?)} for \hinl{ND}, respectively.
The functors corresponding to the nullary operation \hinl{Undefined} and the one for binary operation \hinl{(?)} look as follows\footnote{In the former case we follow the same naming conventions as \citet{swierstra2008data}.}.

\begin{minted}{haskell}
data One a    = One
data Choice a = Choice a a
\end{minted}

The key idea for \hinl{Partial} is that we represent \hinl{Undefined} as \hinl{Impure One}; together with \hinl{Pure} corresponding to \hinl{Defined}, we can represent the same programs as before.
Note that the functor \hinl{Choice} for non-determinism used in combination with \hinl{Free} resembles a tree rather than a list.
A leaf corresponds to \hinl{det} while a branch with two subtrees \hinl{t1} and \hinl{t2} is represented as \hinl{Impure (Choice t1' t2')} where \hinl{t1'} and \hinl{t2'} are the transformations to \hinl{Free Choice} of the initial subtrees.

A variety of common monads are free monads.
A counterexample is the list monad, which is why we rather chose a tree encoding to represent non-determinism.
More precisely, there is no functor \hinl{f} such that type \hinl{Free f a} is isomorphic to \hinl{[a]} \citep{swierstra2008data}.
Other popular representations are the identity monad and the error maybe using the following functors.

\begin{minted}{haskell}
data Zero a
data Const e a = Const a
\end{minted}

Using the types as underlying effect, we get the identity monad using \hinl{Free Zero} and the error monad can be represented using \hinl{Free (Const e)}, where \hinl{e} is the type of the error.

Our running example from the preceding section for non-deterministically inserting an element at each possibile position in a list looks as follows using a representation based on \hinl{Free Choice}.

\begin{minted}{haskell}
(??) :: Free Choice a -> Free Choice a -> Free Choice a
fx ?? fy = Impure (Choice fx fy)
              
insertFree :: a -> [a] -> Free Choice [a]
insertFree x []     = return [x]
insertFree x (y:ys) = return (x : y : ys)
                    ?? (insertFree x ys >>= \zs -> return (y:zs))
\end{minted}

We define the smart constructor for choices \hinl{(??)} as indicated above, but besides swapping this operator and the name of the function the implementation stays exactly the same, because we already rely on the monadic abstraction that we can reuse now.
The exemplary call also reveals five resulting lists.

\begin{verbatim}
λ> insertFree 1 [2..5]
Impure (Choice (Pure [1,2,3,4,5])
       (Impure (Choice (Pure [2,1,3,4,5])
               (Impure (Choice (Pure [2,3,1,4,5])
                       (Impure (Choice (Pure [2,3,4,1,5])
                                       (Pure [2,3,4,5,1]))))))))
\end{verbatim}

%if False

\begin{code}
data Free f a = Pure a | Impure (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Impure fx) = Impure (fmap (fmap f) fx)

instance Functor f => Applicative (Free f) where
  pure                     = Pure
  Pure f     <*> Pure x    = Pure (f x)
  Pure f     <*> Impure fx = Impure (fmap (Pure f <*>) fx)
  Impure ffx <*> ax        = Impure (fmap (<*> ax) ffx)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure x >>= f = f x
  Impure fx >>= f = Impure (fmap (>>= f) fx)

data Zero a
data One a     = One
data Const e a = Const a

data Choice a = Choice a a | Fail
  deriving Show

instance Functor Choice where
  fmap f (Choice x y) = Choice (f x) (f y)

deriving instance Show a => Show (Free Choice a)

(??) :: Free Choice a -> Free Choice a -> Free Choice a
fx ?? fy = Impure (Choice fx fy)
              
insertFree :: a -> [a] -> Free Choice [a]
insertFree x []     = return [x]
insertFree x (y:ys) = return (x : y : ys)
                    ?? (insertFree x ys >>= \zs -> return (y:zs))
\end{code}

%endif
