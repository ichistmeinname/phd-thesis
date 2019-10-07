
The declarative programming paradigm allows the user to concentrate on finding a solution to a problem without explicitly stating the control-flow of the program but rather specifying which sub-problems to solve first.
Representatives of declarative programming are functional and logic programming languages.

The first group of languages consists of functions in the mathematical sense: input arguments uniquely determine the result.
This property is especially interesting in the context of purely functional programming languages and called \emph{referential transparency}: every function call with the same arguments always evaluates to the same result regardless of the context and concrete order of evaluation \citep{horowitz1983fundamentals}.
A pure programming language does not have any side effects like mutable state, that is, variables are only abbreviations for expressions and not references that are manipulated by updates or other modifications.
In this thesis, all declarative programming languages we consider are pure and also statically typed.
That is, every expression has a type, which is checked at compile time and does not change within the course of evaluating the overall program.

In this thesis we work with three different languages: Haskell \citep{jones2002haskell} as representative for a functional language, Curry \citep{hanus1995curry} for functional logic programming, and Coq \citep{barras1997coq} as dependently typed language and representative for interactive theorem provers.
We expect the reader to be familiar with the basics of Haskell in order to directly start with more advanced features in the next section.
Topics we cover include Haskell's demand-driven evaluation strategy and monadic abstractions.
We then move over to the integration of logic features that is Curry; here, the combination of non-determinism and laziness is especially interesting.
Lastly, we will take a look at a richer type system for functional programming using the example of the interactive theorem prover Coq.
After a quick introduction to its syntax, we will discuss how to use the dependent type system to state and prove properties about functional programs.
