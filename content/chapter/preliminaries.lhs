
The declarative programming paradigm allows the user to concentrate on finding a solution to a problem without explicitly stating the control-flow of the program but rather specifying what sub-problems to solve first.
Representatives of declarative programming are functional and logic programming languages.
The first group of languages, consists of functions in the mathematical sense: input arguments uniquely determine one result.
This property is especially interesting in the context of pure functional programming languages and called \emph{referential transparency}: every function call with the same arguments always evaluates to the same result regardless of the context and concrete order of evaluation \citep{horowitz1983fundamentals}.
A pure programming language does not have any side-effects like mutable state, i.e., variables are only abbreviations for expressions and not references that are manipulated by updates or other modifications.
In this thesis, all declarative programming languages we consider are pure and also statically typed.
That is, every expression has a type that is checked at compile time, which does not change within the course of evaluating the overall program.

In this thesis, we work with three different languages: Haskell as representative for a functional language, Curry for functional logic programming, and Coq as dependently typed language and representative for interactive theorem provers.