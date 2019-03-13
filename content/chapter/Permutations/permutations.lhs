%if False

> {-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

> import Control.Monad (MonadPlus(..))
> import Control.Applicative (Alternative(..))

%endif

\framedhs
\section{Non-deterministic Sorting Functions in Haskell}

After discussing non-deterministic sorting functions in a language with built-in non-determinism, we switch to Haskell as exemplary functional language without non-determinism.
We reimplement a selection of the sorting functions introduced in the \autoref{sec:NDCurry} in Haskell using a naive modell of non-determinism based on lists.
As we want to test out different models later, we refactor the list-specific implementations to monad-generic implementations for the sorting algorithm.

We will notice a difference between the Curry and the Haskell implementation when testing the sorting functions on concrete lists.
This difference is not a new insight, but interesting nonetheless: Curry's non-determinism can exploit non-strictness in a way the Haskell model of non-determinism using a monadic interface cannot.

Last but not least, we reexamine the sorting algorithms that compute duplicate permutations and discuss how we can prevent these results in the Haskell implementation.
Due to the general monadic interface, we can use a state-based monad that keeps track of the decisions when applying the comparison functions.
This way, the comparison function can behave in a consistent way; consistency is the property that we already discussed in the context of bubble sort in \autoref{subsec:CurryBubble}.
In addition to consistency, we discuss other properties of the comparison function that are necessary in the Haskell implementation of bubble sort and quick sort.

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
In the list model we can use the function |applyND :: (a -> ND b) -> ND a -> ND b| to apply a non-deterministic function on a non-deterministic computation and combine all non-deterministic results via concatenation.
On top of the definition of |applyND|, we introduce a smart constructor for a singleton result to simplify the usage of the |ND| type.

> applyND :: (a -> ND b) -> ND a -> ND b
> applyND f Nil = Nil
> applyND f (Cons x xs) = f x +++ applyND f xs
>
> (+++) :: ND a -> ND a -> ND a
> Nil +++ ys = ys
> Cons z zs +++ ys = Cons z (zs +++ ys)

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
Since the definition using |applyND| explicitly looks more complicated than necessary, a natural next step is to generalise the definition of |filterND| to any monadic effect.
That is, instead of explicitly using lists to model non-determinism, we solely rely on the abstractions provided by monads.
The resulting definition is |filterM|\footnote{Note that the definition of |filterM| is based on the |Applicative| instead of |Monad| type class now. \url{http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Monad.html\#v:filterM} (last accessed: 2019-02-05}.

> filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
> filterM _ []      = return []
> filterM f (x:xs)  =  f x >>= \p ->
>                      if p  then filterM f xs >>= \ys -> return (x:ys)
>                            else filterM f xs

Note that the list-specific operations to lift a value and to combine all results of effectful computations correspond to the monadic |return| and |(>>=)| operations.
In case of |ND|, we can easily define a suitable |Monad| instance that implements the necessary operations using |singleton| and |applyND|.

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
We test the applications with the non-deterministic comparison function |coinCmpList| --- corresponding to the function |coinCmp| that we have used in Curry before, which transmits easily to the list model in Haskell.

> coinCmpList :: a -> a -> ND Bool
> coinCmpList _ _ = singleton True +++ singleton False

Since |filter| needs to applied to a unary predicate, we partially apply |coinCmpList| with |42| in the examples.
Applying the original definition |filterND| and the generalised version |filterM| yield the same results.

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

The exemplary calls using the non-deterministic comparison function |coinCmpList| do not yield the same results.
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
In this example, we trigger the evaluation of the non-deterministic comparison function |coinCmp| although we do not need the result |zs| if |b| is |True|.
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

\subsection{Drawing Decision Trees}
\label{subsec:drawing}

Thanks to the generic implementation using a monadic interface, we are free to use whatever instance fits our purpose to actually run the sorting functions.
For example, we can generate decision trees like in Curry by using a monad that keeps track of all operations and pretty prints the non-deterministic parts of our computation.
As first step, we generalise the comparison function |coinCmpList| to |MonadPlus|, which is an extension of the |Monad| type class that introduces an additional function |mplus| to combine monadic computations and |mzero| as neutral element for the function |mplus|.

\begin{spec}
class Monad m => MonadPlus m where
      mplus :: m a -> m a -> m a
      mzero :: m a
\end{spec}

The idea of the non-deterministic comparison function |coinCmpList| is to yield two results non-deterministically.
In the concrete implementation using lists, we define |coinCmpList| based on singleton lists |[True]| and |[False]| that are combined using the concatenation operator |(++)|.
A generalisation using |MonadPlus| replaces the singleton operator by |return|, as the structure inherits all functions of |Monad|, and the concatenation operator by |mplus|.

> coinCmp :: MonadPlus m => a -> a -> m Bool
> coinCmp _ _ = return True `mplus` return False

As second step, we define a monad instance that can interpret all monadic operations in an abstract way: the free monad \citet{swierstra2008data}.
Consider the following data type |Free| that is parametrised of a type constructor |f| and a value type |a|.

> data Free f a = Pure a | Impure (f (Free f a))

The general idea behind free monads is the realisation that monadic computations are either pure values or impure effects.
We represent the impure effect using the type constructor |f| and pure values are of type |a|.
The nice property of the |Free| data type is that |Free f| is a monad, if |f| is a functor.

%if False

> deriving instance Show a => Show (Free Sort a)
>
> instance Functor f => Functor (Free f) where
>   fmap f (Pure x) = Pure (f x)
>   fmap f (Impure fx) = Impure (fmap (fmap f) fx)
> 
> instance Functor f => Applicative (Free f) where
   
%endif
 
> instance Functor f => Monad (Free f) where
>   return = Pure
>   Pure x >>= f = f x
>   Impure fx >>= f = Impure (fmap (>>= f) fx)

A variety of common monads are free monads.
The most popular representations are the identity monad, the maybe monad and the error maybe.
Consider the following parametrised data types.

> data Zero a
> data One a = One
> data Const e a = Const a

Using the types as underlying effect, we get the identity monad using |Free Zero|, the maybe monad corresponds to |Free One| and the error monad can be represented using |Free (Const e)|, where |e| is the type of the error.
As we are interested in pretty printing the non-deterministic components of our monadic computations, we need an effect to model non-determinism.
The import effects of non-determinism are exactly the ones provided by the |MonadPlus| type class: a operator to combine two effectful computations and the failing computation.
We define the following data type that represents exactly these operations.

\begin{spec}
data NonDet a = Choice a a | Fail
\end{spec}

Since we want to print the arguments the non-deterministic comparison function is applied to, we store additional information in the constructor as follows.

> data Sort a = Choice (Maybe (String,String)) a a | Fail deriving Show

In order to |Free Sort| as underlying monad in an non-deterministic application of, for example, |filterM|, we need to define a functor instance for |Sort| and a |MonadPlus| instance for |Free Sort|.

%if False

> instance Alternative (Free Sort) where
>   empty = mzero
>   (<|>) = mplus

%endif

> instance Functor Sort where
>   fmap f (Choice id m1 m2 ) = Choice id (f m1) (f m2)
>   fmap _ Fail = Fail
>
> instance MonadPlus (Free Sort) where
>   mzero = Impure Fail
>   mplus m1 m2 = Impure (Choice Nothing m1 m2)

Note that, initially, we do not have any information about the arguments of the |mplus| operator, so we use |Nothing|.
We add information to the structure when we apply the function that introduces non-determinism.
For example, we define non-deterministic function |cmpCoinFree| that stores the string representation of its arguments and non-deterministically yields |True| and |False|.

> coinCmpFree :: Show a => a -> a -> Free Sort Bool
> coinCmpFree x y =
>   Impure (Choice (Just (show x,show y)) (return True) (return False))

Now we can apply |filterM| to our non-determinism-tracking comparison function |cmpCoinFree| and get a |Free Sort|-term that gives information about the arguments that need to be compared.

\begin{spec}
replHS> filterM (coinCmpFree 42) [1,2]
Impure (Choice  (Just ("42","1"))
                (Impure (Choice (Just ("42","2")) (Pure [1,2])  (Pure [1])))
                (Impure (Choice (Just ("42","2")) (Pure [2])    (Pure []))))
\end{spec}

Note that the first argument is always |42|, because we use |coinCmpFree 42| as predicate argument for |filterM|.
Since this term representation looks more complicated than helpful, as last step, we define a pretty printing function for |Free Sort|.
The function |pretty :: Show a => Free Sort a -> String| prints a decision tree similar to the one we got to know from Curry.
Now we take a look at the well-arranged decision tree resulting from the above call.

\begin{spec}
replHS> putStrLn (pretty (filterM (coinCmpFree 42) [1,2]))
                          +-[1,2]
             +- 42 <= 2  -+
             |            +-[1]
+- 42 <= 1  -+
             |            +-[2]
             +- 42 <= 2  -+
                          +-[]
\end{spec}

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

\subsection{Curry vs Monadic Non-determinism}
With this insight about the strictness of |(>>=)| in mind, we check out the consequences when applying a non-deterministic comparison function to monadic sorting functions.
That is, we transform the Curry implementation discussed in \autoref{sec:NDCurry} to Haskell.

\paragraph{Insertion Sort}\label{par:insert}
As we have just seen the definition of |insertM|, we start with |insertionSort|.

> insertionSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
> insertionSortM _ []      = return []
> insertionSortM p (x:xs)  = insertionSortM p xs >>= \ys -> insertM p x ys

Note that is again crucial to introduce potentially non-deterministic values only as result of the comparison function and the result of the function itself.
This observation also applies to the definition of |insertM|, the input list |ys| needs to be deterministic.
That is, in order to insert the head element |x| into the already sorted tail, we unwrap the monadic context using |(>>=)| and apply |insertM| to each possible value of the computation |insertionSortM p xs|.

Applying |insertionSortM| to |coinCmpList| and exemplary list values, yield the expected permutations, more precisely, exact the permutations of the input list.

% if False

> lengthND :: ND a -> Int
> lengthND Nil = 0
> lengthND (Cons _ xs) = 1 + lengthND xs

% endif

\begin{spec}
replHS> insertionSortM coinCmpList [1..3]
{ [1,2,3], [2,1,3], [2,3,1], [1,3,2], [3,1,2], [3,2,1] }

replHS> let fac n = if n == 0 then 1 else n * fac (n-1) in
        all  (\n -> lengthND (insertionSortM coinCmpList [1..n]) == fac n)
             [1..10]
True
\end{spec}

The second example call checks for lists of length 1 to 10, if the number of non-deterministic results is equal to the factorial of that number, which is indeed the case.
Here, the function |lengthND| is the ordinary |length| function on lists adapted to our custom list data type |ND|.
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
repl> map  (\n -> length (allValues (head (insertionSort coinCmp [1..n]))))
           [5..10]
[16,32,64,128,256,512]
\end{spec}
\framedhs

In Curry we do not need to evaluate all non-deterministic computations to yield the head element.
Instead of $n!$ number of non-deterministic results, we only get $2^(n-1)$ results for an input list of length $n$.
The difference between the Haskell and the Curry implementation with respect to the used model of non-deterministic is that Haskell's non-determinism is flat, while non-deterministic computations can occur in deep positions in Curry.
Here, deep means that the non-deterministic is not visible at the outermost constructor, but occurs in the component of a constructor.

Consider the following non-deterministic expression |exp| of type |[Bool]| and its projection to the head element and tail, respectively, in Curry.

\plainhs
\begin{spec}
repl> let exp = True : ([] ? [False]) in head exp
True
repl> let exp = True : ([] ? [False]) in tail exp
[]
[False]
\end{spec}
\framedhs

The list |exp| is non-deterministic in its tail component, the head element is deterministic and the top-level list constructor |(:)| is also deterministic.
That is, on the one hand applying |head| to |exp| does not trigger any non-deterministic, the evaluation yields a deterministic results, namely |True|.
On the other hand the non-determinism appears in the overall result when we project the tail of the list |exp|, this application yields the two results |[]| and |[False]|.
In contrast, we cannot model the same behaviour in Haskell when using a list-based model for non-deterministic computations.

\begin{spec}
repl> let exp = True : (singleton [] +++ singleton [False]) in head exp
<interactive>:88:19-52: error:
    * Couldn't match expected type ‘[Bool]’
                  with actual type ‘ND [Bool]’
    * In the second argument of ‘(:)’, namely
        ‘(singleton [] +++ singleton [False])’
      In the expression: True : (singleton [] +++ singleton [False])
      In an equation for ‘exp’:
          exp = True : (singleton [] +++ singleton [False])
\end{spec}

The error message says that the list constructor |(:)| expects a second argument of type |[Bool]|, but we apply it to an argument of type |ND [Bool]|.
Due to the explicit modelling of non-determinism that is visible in the type-level, i.e., using |ND|, we cannot construct non-deterministic computations that occur deep in the arguments of constructors like |(:)| out of the box.
In contrast, Curry's non-determinism is not visible on the type-level, such that we can use non-determinism expressions in any constructor argument without altering the type of the expression.
We can reconcile the computation we want to express with the explicit non-determinism in Haskell by binding the non-deterministic computation first and reuse the list constructor then.

\begin{spec}
repl>  singleton [] +++ singleton [False] >>= \nd ->
       let exp = True : nd in return (head exp)
{ True, True }

repl>  singleton [] +++ singleton [False] >>= \nd ->
       let exp = True : nd in return (tail exp)
{ [], [False] }
\end{spec}

In this case, however, the non-determinism is definitely triggered: even though |head| does not need to evaluate its tail, where the non-determinism occurs, the first argument of |(>>=)| is evaluated, yielding two results.
All in all, the main insight here is that the non-determinism in Curry can occur deep within data structure components and gives us the possibility to exploit non-strictness.
In contrast, the naive Haskell model using lists can only express flat non-determinism, that is, all possibly deep occurrences of non-determinism is pulled to the top-level constructor.

\paragraph{Selection Sort}

Whereas the application of insertion sort to a non-deterministic comparison function yields the same number of results for the Haskell as well as the Curry implementation, we will now take a look at an example that yields duplicate results: selection sort.
We directly define the version of selection sort that uses |pickMinM| instead of traversing the list twice.

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

The application of |selectionSortM| to |coinCmpList| yields more results than expected, the resulting function enumerates some permutations multiple times.

\begin{spec}
replHS> selectionSortM coinCmpList [1,2,3]
{ [1,2,3], [1,3,2], [2,1,3], [2,3,1], [1,2,3], [1,3,2], [3,1,2], [3,2,1] }

replHS> all  (\n -> lengthND (selectionSortM coinCmpList [1..n]) == 2^(frac (n*(n-1)) 2))
             [1..7]
True
\end{spec}
\noindent
In fact, we get
\[
2^{\frac{n (n-1)}{2}}
\]
results for for an input list of length $n$.
Note that this function grows much faster than the number of permutations, $n!$.
That is, for $n=10$ there are $n! = 3 628 800$ permutations, whereas an application of |selectionSort| to the list |[1..10]| yields
\[
2^{\frac{10*9}{2}} = 2^{45} = 35 184 372 088 832
\]
number of results.

Since the number of results for |selectionSort| applied to a non-deterministic comparison functions differs with the result we got for the Curry implementation, we compare the underlying decision trees.
The non-determinism produced by |selectionSort| arises from the usage of |coinCmpList|, which is only evaluated in the auxiliary function |pickMinM|.
That is, it is sufficient to take a look at the decision tree for a subcall of |pickMin| to detect the different behaviour.
We compute the decision tree displayed left in \autoref{fig:pickDecision} by applying a free monad based data type as described in \autoref{subsec:drawing}.
The right side of the figure recaps the decision tree when using the Curry implementation.

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
\vline $\quad$
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

\caption{Decision trees for the expressions |pickMinM coinCmpList [1,2,3]| in Haskell (left) and |pickMinM coinCmp [1,2,3]| in Curry (right)}
\label{fig:pickDecision}
\end{figure}

The monadic version is more strict: the recursive call to |pickMinM| needs to be evaluated in order to apply the predicate |p|.
In the Curry version, however, we can already take the |True|-branch for the application of |p| without considering the recursive call first.
Thus, the first result |(1, [2,3])| triggers only one non-deterministic decision in Curry.
Of course, the number of unnecessary triggered non-deterministic decisions in the Haskell version increases with each recursive call of |pickMin|.
That is, when we apply |pickMin| to a longer list elements, the number of duplicate results increases dependent of the length of the list.

\begin{spec}
replHS> map  (\n -> lengthND (pickMinM coinCmpList [1..n] >>= return . fst ))
             [1..20]
[1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,
65536,131072,262144,524288]
\end{spec}

More precisely, |pickMinM coinCmpList xs| yields $2^{|length xs|}$ results, while the Curry version only $length n$ results.
Note that the second variant, i.e., the Curry version, is what we expect in the first place: picking a minimum with a non-deterministic predicate is basically a function that non-deterministically yields each element of the list.

In the end, |pickMinM| and |pickMin|, respectively, are the functions used to implement the selection sort algorithm and, thus, determines the number of permutations.
Whereas |selectionSort| yields only the permutations of the input list in Curry, we get duplicate permutations in the Haskell version.

\paragraph{Other Sorting Algorithms}

The remaining sorting algorithms discussed in \autoref{sec:NDCurry}, i.e., bubble sort, quick sort and merge sort, yield the same results for the monadic Haskell version as they do in Curry.
 However, we can observe a similar effects as with |insertionSortM| in \autoref{par:insert} concerning non-strictness.
When we demand only the head elements of all permutations, the monadic Haskell versions need to trigger more non-deterministic that is necessary in the Curry version.
\autoref{fig:strictSort} visualises the number of triggered non-deterministic computations that are necessary to compute only the head element of all permutations.
We observe that all Curry implementations (completely coloured bars) compute less non-deterministic computations than all Haskell implementations.
One interesting contrast is the behaviour of bubble sort: the Curry version only needs to trigger a constant number of non-deterministic computation (constant with respect to the length of the input list), whereas the Haskell version triggers $n!$ non-deterministic computations for an input list of length $n$.
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
replHS> bubbleSortM coinCmpList [1,2,3]
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
\caption{Decision tree for the expression |bubbleSortM coinCmpList [1,2,3]|}
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
