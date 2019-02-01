> module Permutations

\section{Non-deterministic Sorting Functions in Haskell}

After discussing non-deterministic sorting functions in a language with built-in non-determinism, we switch to Haskell as exemplary functional language without non-determinism.
We reimplement a selection of the sorting functions introduced in the \autoref{sec:NDCurry} in Haskell using naive modell of non-determinism based on lists.
As we want to test out differnt models later, we already start with a monad-generic implementation for the sorting algorithm and the non-deterministic comparison function |coinCmp|.

We will notice a difference between the Curry and the Haskell implementation when testing the sorting functions on concrete lists.
This difference is not a new insight, but interesting nonetheless: Curry's non-determinism can exploit non-strictness in a way the Haskell model of non-determinism using a monadic interface cannot.

Last but not least, we reexamine the sorting algorithms that compute duplicate permutations and discuss how we can prevent these results in the Haskell implementation.
Due to the general monadic interface, we can use a state-based monad that keeps track of the decisions when applying the comparision functions.
This way, the comparison function can behave in a consistent way; consistency is the property that we already discussed in the context of bubble sort in \autoref{subsec:CurryBubble}.
In addition to consistency, we discuss other properties of the comparision function that are necessary in the Haskell implementation of bubble sort and quick sort.

\subsection{Modelling Non-determinism}

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
