%if False

\begin{code}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Preliminaries.Haskell where

import Debug.Trace
import Prelude hiding (head)
\end{code}

%endif
        
\section{Functional Programming}
\label{sec:Haskell}

We present all concepts related to pure functional programming in this thesis using the language Haskell.
As we assume a basic familiarity of the reader regarding functional programming in Haskell, we will focus on specific and advanced aspects we will make use of.
For a more detailed introduction to Haskell, we recommend interested readers to take a look at other sources \citep{hudak2007history, hutton2016programming}.

First, we illustrate the advantages and subtleties of Haskell's non\--strict and especially lazy evaluation strategy using a handful of examples.
Next, we show how to work with side effects and other effectful operations that are not allowed otherwise due to Haskell's purity.
In this matter, we discuss how to model such effects using monadic abstraction.
More precisely, we illustrate how to model partiality and non\--determinism using monads.
Finally, we generalise the monadic abstraction to use free monads instead, a representation that we will make use of in different parts of this thesis.

If not explicitly stated differently, we use GHC 8.4.3 to compile and run the presented Haskell code.
We display the interaction with GHC's REPL using a prompt showing a lambda  --- \haskellrepl --- at the start of each command.

\subsection{Non\--strictness and Laziness}

Haskell's evaluation strategy is call\--by\--need \citep{ariola1997call}.
The strategy evaluates sub\--expressions only when explicitly needed and shared expressions only once.
That is, call\--by\--need combines the advantages of both, call\--by\--name and call\--by\--value.
Call\--by\--name semantics behaves non\--strict and evaluates expressions only when needed; call\--by\--value semantics corresponds to a strict evaluation, having the advantage that it evaluates expressions only once.
The combination of non\--strictness and sharing, which Haskell employs, is often called lazy evaluation.

In order to demonstrate the non\--strictness part of Haskell's lazy evaluation, we use the following definition of \hinl{head} to project the first element of a list.

%if False

\begin{code}
head :: [a] -> a
head []      = undefined
head (x : _) = x
\end{code}

%endif

\begin{haskellcode}
head :: [a] -> a
head []      = undefined
head (x : _) = x
\end{haskellcode}
\label{code:haskell_head}

Let us compute the head of a partial list: the head element is defined but the remaining list is not.
In Haskell the value \hinl{undefined} represents a partial value that produces a run\--time error, when evaluation demands the value.

\begin{hrepl}
\haskellrepl head (1 : undefined)
1
\end{hrepl}

Non\--strictness allows us to work on partial values and, more importantly, and does not evaluate non\--demanded sub-expressions.
The demand\--driven evaluation comes into play not only in case of partial values, but also in case of expensive computations.

The next example uses a function that computes the factorial of a given number as representative of such an expensive computation, and the function \hinl{const :: a -> b -> a} that ignores its second and yields its first argument.

\begin{hrepl}
\haskellrepl const 42 (fac 100)
42
\end{hrepl}

The evaluation immediately yields \hinl{42} as the second argument of \hinl{const} is not demanded, thus, not computed.

The second component of lazy evaluation --- sharing expressions --- is in most cases only observable regarding the performance of programs.
We can, however, observe the difference of a shared expression and an expression that needs to be evaluated multiple times by using Haskell's \hinl{trace} function.
Using \hinl{trace :: String -> a -> a} we can print debug messages on the console while evaluating a program.
More precisely, the first argument is the message we want to log and the second argument the expression we want to log the message for.

In order to illustrate how \hinl{trace} works, consider the following two examples.

\begin{hrepl}
\haskellrepl let log42 = trace "fortytwo" 42 in 103 + log42
fortytwo
145

\haskellrepl let log42 = trace "fortytwo" 42 in const 103 log42
103
\end{hrepl}

In both cases we want to log the message \texttt{"fortytwo"} when the variable \hinl{log42} is used, and \hinl{42} is the actual value that is used to compute with.
The first example logs the message during evaluation and then yields \hinl{145} as result.
In the second example, we do not observe any logging message, because, again, the second argument of \hinl{const} does not need to be computed.

In order to observe that we shared an expression, we consider the following two expressions that double a value that is traced with a message.

\begin{haskellcode}
test1, test2 :: Int -> Int
test1 n = trace "msg" n + trace "msg" n
test2 n = let x = trace "msg" n in x + x
\end{haskellcode}

\begin{hrepl}
\haskellrepl test1 42
msg
msg
84

\haskellrepl test2 42
msg
84
\end{hrepl}

The first example logs the message two times for each call to \hinl{trace}, whereas the second example shares the effectful expression \texttt{trace "msg" 42} by binding it to a variable \hinl{x} and doubles the pure value \hinl{42} only.
Although the first example \hinl{test1} looks like an inlined version of \hinl{test2}, due to Haskell's call\--by\--need semantics these expressions have different results when used in combination with a side effect like tracing.

%if False

\begin{code}
doublePlus :: Int -> Int
doublePlus x = x + x

doubleMult :: Int -> Int
doubleMult x = 2 * x

test1 n = trace "msg" n + trace "msg" n
test2 n = let x = trace "msg" n in x + x
test3 n = doublePlus (trace "msg" n)
test4 n = doubleMult (trace "msg" n)
\end{code}

%endif


\subsection{Monadic Abstractions}
\label{subsec:monadicAbstractions}

In a functional programming language like Haskell, we are used to define functions that map input values to output values.
If a program, however, does not only return a value, but additionally has an observable interaction with the outside world (for example through an additional context that needs to be considered), such a program is said to have computational \emph{effects}.
As a pure language, Haskell does not allow any side effects conceptually, unless they are explicitly modelled.
Such an explicit model becomes visibile at the type\--level.
For example, Haskell models the interaction with the user through reading input and printing output explicitly with the type \hinl{IO} \citep{wadler1997declare}.
Such an explicit model of computational effects capture the necessity to represent the additional context the function interacts with.
Haskell's notion of purity allows, however, computational effects like tracing and partiality --- using \hinl{trace} and \hinl{undefined}, respectively --- that we discussed above.
Effects that do not have explicit constructs for propagation and representation are sometimes called ambient or implicit effects \citep{filinski1996controlling}; in Haskell these examples, thus, are usually not visibile in the type signature.

In this thesis, we are interested in explicit representations of effects like partiality as well as non\--determinism.
We can, for example, explicitly model partiality using the following data type.\footnote{Note that the definition is equivalent to the \hinl{Maybe} type, here, we decide for an aptronym using a custom definition \hinl{Partial} instead.}

%if False

\begin{code}
data Partial a = Undefined
               | Defined a
  deriving Show
\end{code}

%endif

\begin{haskellcode}
data Partial a = Undefined
               || Defined a
\end{haskellcode}
\label{code:partial_haskell}

These constructors represent undefined and defined values, respectively.
As noted above, Haskell also has an implicit model of partiality: the polymorphic value \hinl{undefined} can be used without any indication on the type\--level.
The evaluation of \hinl{undefined} yields a run\--time error.
Consider the following examples that demand the evaluation of \hinl{undefined}.

\begin{hrepl}
\haskellrepl head []
*** Exception: Prelude.undefined

\haskellrepl head (tail [1])
*** Exception: Prelude.undefined
\end{hrepl}

Using the \hinl{Partial} type, we can model a function that accesses the head of a list that explicitly yields \hinl{Undefined} instead of a run\--time error.

%if False

\begin{code}
headPartial :: [a] -> Partial a
headPartial []    = Undefined
headPartial (x:_) = Defined x
\end{code}

%endif

\begin{haskellcode}
headPartial :: [a] -> Partial a
headPartial []    = Undefined
headPartial (x:_) = Defined x
\end{haskellcode}

The representation of the exemplary expressions from above evaluates the undefined value explicitly using the appropriate constructor.

\begin{hrepl}
\haskellrepl headPartial []
Undefined

\haskellrepl headPartial (tail [1])
Undefined
\end{hrepl}

Note that a corresponding implementation of \hinl{tailPartial} would not compose with \hinl{headPartial} anymore as in the original example above.
Before we talk about this downside of the model, let us take a look at a representation for non\--determinism as effect.
We model functions that possibly produce several results (non\--deterministically) using lists.
In order to not confuse the representation of non\--determinism using lists with lists that we use as algebraic datatypes in type signatures of functions, we use a type synonym \hinl{ND} for the former usage of lists.

\begin{haskellcode}
type ND a = [a]
\end{haskellcode}

On top of that, we use the following convenience functions to yield a deterministic result and combine two potentially non\--deterministic results.

%if False

\begin{code}
type ND a = [a]

det :: a -> ND a
det x = [x]

(?) :: ND a -> ND a -> ND a
(?) = (++)
\end{code}
%endif

\begin{haskellcode}
det :: a -> ND a
det x = [x]

(?) :: ND a -> ND a -> ND a
(?) = (++)
\end{haskellcode}

The former function yields a singleton list, whereas the latter corresponds to the concatenation of the two lists.
Using this representation of non\--determinism and these convenience functions, we define the function \hinl{insertND} that non\--deterministically inserts a given element at all possible positions of a list.

%if False

\begin{code}
insertND :: a -> [a] -> ND [a]
insertND x []     = det [x]
insertND x (y:ys) = det (x : y : ys) ? map (y:) (insertND x ys)
\end{code}

%endif

\begin{haskellcode}
insertND :: a -> [a] -> ND [a]
insertND x []     = det [x]
insertND x (y:ys) = det (x : y : ys) ? map (y:) (insertND x ys)
\end{haskellcode}

The first rule is deterministic, it yields one list as result that contains just the element \hinl{x} we want to insert to the list.
The second rule yields at least two results.
The first argument of the \hinl{(?)}\--operator inserts the element in front of the list and yields the deterministic result.
For the second argument, we map over all lists for the recursive call \hinl{insertND x ys} by inserting the first element \hinl{y} to the front of all these resulting lists.
Note that the \hinl{map} functions transforms elements of type \hinl{ND [a]} to \hinl{ND [a]}, since \hinl{ND} is just a type synonym for lists.

As an example, we non\--deterministically insert \hinl{1} into the list \hinl{[2..5]}.
Note that we manipulate the output for the REPL to use set\--like parentheses for the lists that correspond to the modelled non\--determinism of type \hinl{ND}.

\begin{hrepl}
\haskellrepl insertND 1 []
\{ [1] \}

\haskellrepl insertND 1 [2,3,4,5]
\{ [1,2,3,4,5] , [2,1,3,4,5] , [2,3,1,4,5] , [2,3,4,1,5] , [2,3,4,5,1] \}
\end{hrepl}

A commonly used abstraction to model all these computational effects are monads \citep{moggi1989computational}: the most common monadic abstraction is the \hinl{IO} type mentioned in the beginning.
Using a type constructor class, a monad provides the following two operations.

\begin{haskellcode}
class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b
\end{haskellcode}

A type constructor class allows to define overloaded functions for type constructors like \hinl{IO}, \hinl{Partial}, and \hinl{[]}.
Note that we define an instance for \hinl{[]} instead of \hinl{ND}, because we can define type class instances for data types only, not for type synonyms\footnote{Note that we can define such instances using \hinl{TypeSynonymInstances} if these instances do not overlap with predefined ones.}.
That is, we can define type class instances for our modelled effects \hinl{Partial} and \hinl{[]} as follows\footnote{Strictly speaking, the instance for lists is already predefined.}.

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

\begin{haskellcode}
instance Monad Partial where
  return          = Defined
  Defined x >>= f = f x
  Undefined >>= f = Undefined

instance Monad [] where
  return   = det
  xs >>= f = concat (map f xs)
\end{haskellcode}

We reimplement the definition of \hinl{insertND} using \hinl{(>>=)} as follows, which leads to a more natural implementation concerning the separation of operation on lists as data structures and lists as model for non\--determinism.
More precisely, instead of using \hinl{map}, the usage of the \hinl{(>>=)}\--operator gives us access to each list of the non\--deterministic result.

%if False

\begin{code}
insertM :: a -> [a] -> ND [a]
insertM x []     = return [x]
insertM x (y:ys) = return (x : y : ys) ? (insertM x ys >>= \zs -> return (y:zs))
\end{code}

%endif

\begin{haskellcode}
insertND :: a -> [a] -> ND [a]
insertND x []     = return [x]
insertND x (y:ys) = return (x : y : ys)
                  ? (insertND x ys >>= \zs -> return (y:zs))
\end{haskellcode}

Now recall the example for partiality again and let us define the \hinl{tail} function using \hinl{Partial}, analogous to \hinl{headPartial}.

%if False

\begin{code}
tailPartial :: [a] -> Partial [a]
tailPartial []     = Undefined
tailPartial (_:xs) = Defined xs
\end{code}

%endif

\begin{haskellcode}
tailPartial :: [a] -> Partial [a]
tailPartial []     = Undefined
tailPartial (_:xs) = Defined xs
\end{haskellcode}

As already noted above, the composition \hinl{headPartial . tailPartial} is not possible although we can compose \hinl{head . tail} in the original Haskell code.

\begin{hrepl}
\haskellrepl headPartial (tailPartial [])
    • Couldn't match expected type ‘[a]’
                  with actual type ‘Partial [a0]’
    • In the first argument of ‘headPartial’, namely ‘(tailPartial [])’
      In the expression: headPartial (tailPartial [])
      In an equation for ‘it’: it = headPartial (tailPartial [])
\end{hrepl}

The problem of this composition is that the resulting type of \hinl{tailPartial}, namely \hinl{Partial [a]} is not the type \hinl{headPartial} expects as first argument.
We can circumvent the typing problem using the operator \hinl{(>>=)} to access the list within the \hinl{Partial}\--result of \hinl{tailPartial}, which yields the expected result \hinl{Undefined}, as follows.

\begin{hrepl}
\haskellrepl tailPartial [1] >>= headPartial
Undefined
\end{hrepl}

As second example, we use \hinl{(>>=)} to compose a pure and an effectful function.
Since the \hinl{(>>=)} operator needs a monadic function as second argument, we use \hinl{return} to lift the pure function into the monadic context.
Here, we compute the head element of all the lists resulting from the usage of \hinl{insertND}.

\begin{hrepl}
\haskellrepl insertND 1 [2,3,4,5] >>= return . head
\{ 1 , 2 , 2 , 2 , 2 \}
\end{hrepl}

Note, however, that the usage of \hinl{(>>=)} to make the composition work can have unintended effects in case the second function does not demand its argument.
For example, the expression \hinl{const 42 (tail [])} yields \hinl{42} and not a run\--time error.
Hence, we expect the corresponding usage of \hinl{tailPartial} to yield \hinl{Defined 42}.

\begin{hrepl}
\haskellrepl const 42 (tail [])
42
\haskellrepl tailPartial [] >>= return . const 42
Undefined
\end{hrepl}

We do not go into more details concerning this unintended behaviour here, but hope that the curious reader awaits the coming chapters eagerly, as we will discuss this model of non\--determinism more thoroughly for Haskell in \autoref{ch:permutations}, and again in \autoref{ch:reasoning} when we discuss representations of effects in the proof assistant Coq.

\subsection{Free Monads}
\label{subsec:freeMonad}

Recently, the functional programming community started using a slightly different approach for modelling effects.
The overall monadic structure is still the key of the representation.
One observation that leads to the other abstraction is that all representations of such effects have two operations in common: one to lift a value into the effect representation (\hinl{return}) and one to manipulate the values of an effect (\hinl{(>>=)}).
This observation finally leads to a monad instance that can interpret all monadic operations in an abstract way: the free monad \citep{swierstra2008data}.
Consider the following data type \hinl{Free} that is parametrised by a type constructor \hinl{f} and a value type \hinl{a}.

\begin{haskellcode}
data Free f a = Pure a
              || Impure (f (Free f a))
\end{haskellcode}

The general idea behind free monads is the observation that monadic computations are either pure values or impure effects.
We represent the impure effect using the type constructor \hinl{f} and pure values are of type \hinl{a}.
The nice property of the \hinl{Free} data type is that \hinl{Free f} is a monad, if \hinl{f} is a functor.

\begin{haskellcode}
instance Functor f => Monad (Free f) where
  return          = Pure
  Pure x    >>= f = f x
  Impure fx >>= f = Impure (fmap (>>= f) fx)
\end{haskellcode}

We represent impure operations using the functor \hinl{f}.
More precisely, the functor \hinl{f} represents the syntax of the effectful computation, that is, the operations that are added on top of the pure values we usually work with.
In case of \hinl{Partial}, we have one operation, namely \hinl{Undefined} that corresponds to Haskell's \hinl{undefined} value associated with partiality.
The other constructor \hinl{Defined} is already taken care of by \hinl{Pure}.
Moreover, we observe that \hinl{Undefined} does not contain any further values but is a possible value of its own: it is a nullary operation.
In contrast, we modelled the binary operation \hinl{(?) :: ND a -> ND a -> ND a} for non\--determinism that combines two non\--deterministic computations.
The corresponding functor, thus, needs to make use of the recursive type argument \hinl{Free f a}.
More concretely, since \hinl{Free} already models the constructor for defined and deterministic values using \hinl{Pure}, the functor takes care of the values constructed using \hinl{Undefined} for \hinl{Partial} and \hinl{(?)} for \hinl{ND}, respectively.
The functors corresponding to the nullary operation \hinl{Undefined} and to the binary operation \hinl{(?)} look as follows\footnote{In the former case we follow the same naming conventions as \citet{swierstra2008data}.}.

\begin{haskellcode}
data One a    = One
data Choice a = Choice a a
\end{haskellcode}

\begin{table*}[t]
\begin{tabular}{llll}
Description & Functor & Monadic Values & Free Values \\
\toprule
Totality                         & \hinl{Zero}                     & \hinl{Identity x}   & \hinl{Pure x}\\[0.5em]
\multirow{2}{*}{Partiality}      & \multirow{2}{*}{\hinl{One}}     & \hinl{Just x}       & \hinl{Pure x}\\
                                 &                                 & \hinl{Nothing}      & \hinl{Impure One}\\[0.5em]
\multirow{2}{*}{Error}           & \multirow{2}{*}{\hinl{Const e}} & \hinl{Right x}      & \hinl{Pure x}\\
                                 &                                 & \hinl{Left y}       & \hinl{Impure (Const y)}\\[0.5em]
\multirow{2}{*}{Non\--determinism} & \multirow{2}{*}{\hinl{Choice}}  & \hinl{Leaf x}       & \hinl{Pure x}\\
                                 &                                 & \hinl{Branch t1 t2} & \hinl{Impure (Choice t1' t2')}\\
\bottomrule
\end{tabular}
\caption{Overview of values represented using the direct interpretation as monad and using \hinl{Free} with the corresponding functor}
\label{tab:valueOverview}
\end{table*}

Intuitively, the number of constructors of the functor corresponds to the number of operations the effect introduces and the arguments of each constructor indicate the arity of the corresponding operations.
The key idea for \hinl{Partial} is that we represent \hinl{Undefined} as \hinl{Impure One}; together with \hinl{Pure} corresponding to \hinl{Defined}, we can represent the same programs as before.
Note that the functor \hinl{Choice} for non\--determinism used in combination with \hinl{Free} resembles a tree rather than a list.
A leaf corresponds to \hinl{det} while a branch with two sub\--trees \hinl{t1} and \hinl{t2} is represented as \hinl{Impure (Choice t1' t2')} where \hinl{t1'} and \hinl{t2'} are the transformations to \hinl{Free Choice} of the initial sub\--trees \hinl{t1} and \hinl{t2}.
\autoref{tab:valueOverview} gives an overview of the value correspondences between the monadic representation and the representation using \hinl{Free} with the associated functor.
The monad instance for \hinl{Free} demands the type parameter \hinl{f} to have a \hinl{Functor} constraint.
We present the corresponding type class definition in Haskell as well as the definition of the instances for the concrete functors we use in this section in \appref{sec:appendix:functor}.

A variety of common monads are isomorphic to a representation using free monads.
A counterexample, however, is the list monad; as \citet{swierstra2008data} states, there is no functor \hinl{f} such that type \hinl{Free f a} is isomorphic to \hinl{[a]}.\footnote{A proof sketch of this observation can be found in \appref{sec:appendix:freeList}.}
Due to this counterexample, we rather chose a tree encoding to represent non\--determinism.
In \autoref{ch:reasoning} we restate this isomorphism property and will show that the free monad applied to the functors \hinl{One} and \hinl{Choice} are isomorphic to \hinl{Maybe} and a leaf-labeled binary tree, respectively.
Other popular representations are the identity monad and the error monad using the following functors.

\begin{haskellcode}
data Zero a
data Const e a = Const e
\end{haskellcode}

Using the types as underlying effect, we get the identity monad using \hinl{Free Zero} and the error monad can be represented using \hinl{Free (Const e)}, where \hinl{e} is the type of the error.
\autoref{tab:effectOverview} gives an overview of different monads and their representation using \hinl{Free}.

\begin{table*}[t]
\begin{tabular}{lll}
Description & Monadic Representation & Free Representation \\
\toprule
Totality        & \hinl{data Identity a = Identity a}            & \hinl{Free Zero a}\\[0.25em]
Partiality      & \hinl{data Maybe a = Just a || Nothing}  & \hinl{Free One a}\\[0.25em]
Error           & \hinl{data Either b a = Right a || Left b}    & \hinl{Free (Const b) a}\\[0.25em]
Non\--det. & \hinl{data Tree a = Lf a || Nd (Tree a) (Tree a)} & \hinl{Free Choice a}\\
\bottomrule
\end{tabular}
\caption{Overview of monads and the corresponding representation using \hinl{Free} and the associated functor}
\label{tab:effectOverview}
\end{table*}

Our running example from the preceding section for non\--deterministically inserting an element at each possibile position in a list looks as follows using a representation based on \hinl{Free Choice}.

\begin{haskellcode}
insertFree :: a -> [a] -> Free Choice [a]
insertFree x []     = return [x]
insertFree x (y:ys) = return (x : y : ys)
                    ?? (insertFree x ys >>= \zs -> return (y:zs))
\end{haskellcode}

We define the smart constructor for choices \hinl{(??)} as indicated above and can, thus, nearly reuse the implementation from before, because we already rely on the monadic abstraction.

\begin{haskellcode}
(??) :: Free Choice a -> Free Choice a -> Free Choice a
(??) fx fy = Impure (Choice fx fy)
\end{haskellcode}              

Note that the underlying representation of non\--determinism changed from lists to trees, but otherwise the functions behave the same.
The exemplary call also reveals five resulting lists.

\begin{hrepl}
\haskellrepl insertFree 1 [2..5]
Impure (Choice (Pure [1,2,3,4,5])
       (Impure (Choice (Pure [2,1,3,4,5])
               (Impure (Choice (Pure [2,3,1,4,5])
                       (Impure (Choice (Pure [2,3,4,1,5])
                                       (Pure [2,3,4,5,1]))))))))
\end{hrepl}

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
