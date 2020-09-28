# Effectful Programming in Declarative Languages with an Emphasis on Non–Determinism: Applications and Formal Reasoning

* Submission: October, 25th, 2019
* Defense: February, 7th, 2020
* Publication: May, 28th, 2020

## Abstract

This thesis investigates effectful declarative programming with an emphasis on non–determi- nism as an effect.
On the one hand, we are interested in developing applications using non–determinism as underlying implementation idea.
We discuss two applications using the functional logic programming language Curry.
The key idea of these implementations is to exploit the interplay of non–determinism and non–strictness that Curry employs.  
The first application investigates sorting algorithms parametrised over a comparison function.
By applying a non–deterministic predicate to these sorting functions, we gain a permutation enumeration function.
We compare the implementation in Curry with an implementation in Haskell that uses a monadic interface to model non–determinism.  
The other application that we discuss in this work is a library for probabilistic programming.
Instead of modelling distributions as list of event and probability pairs, we model distributions using Curry’s built–in non–determinism.  
In both cases we observe that the combination of non–determinism and non–strictness has advantages over an implementation using lists to model non–determinism.  
On the other hand, we present an idea to apply formal reasoning on effectful declarative programming languages.
In order to start with simple effects, we focus on modelling a functional subset first. That is, the effects of interest are totality and partiality.
We then observe that the general scheme to model these two effects can be generalised to capture a wide range of effects.
Obviously, the next step is to apply the idea to model non– determinism.
More precisely, we implement a model for the non–determinism of Curry: non– strict non–determinism with call–time choice.
Therefore, we finally discuss why the current representation models call–by–name rather than Curry’s call–by–need semantics and give an outlook on ideas to tackle this problem.

## How to build

The build is hard-coded to my machine; adapt the location of your `shake`-executable [1] in the `build.sh` file if -- for some reason -- you want to compile the tex-sources.
Note that you need to have lhs2tex [2], coqdoc [3] and pygments [4] installed as well.

[1] [Shake build tool](https://hackage.haskell.org/package/shake)
[2] [lhs2tex](https://hackage.haskell.org/package/lhs2tex)
[3] [coqdoc](https://github.com/coq/coq/wiki/Installation%20of%20Coq%20on%20Linux)
[4] [pygments](https://pygments.org/download/)
