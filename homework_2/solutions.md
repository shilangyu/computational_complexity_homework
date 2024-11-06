---
title: Computational complexity, Homework 2
geometry: margin=2.5cm
author:
  - Dario Halilovic
  - Toni Jubés Monforte
  - Marcin Wojnarowski
date: 1-11-2024
---

# 1

To prove $\mathsf{NP}^\mathsf{SAT} = \Sigma_2\mathsf{P}$ we prove the inclusion in both directions

## $\mathsf{NP}^\mathsf{SAT} \subseteq \Sigma_2\mathsf{P}$

Let $L \in \mathsf{NP}^\mathsf{SAT}$. Then

$$
  x \in L \iff \exists y \, M^\mathsf{SAT}(x, y) = 1
$$

For $i$-th $\mathsf{SAT}$ oracle query, we encode its answer $a_i$ and its certificate assignment $c_i$ (if the answer is positive). Additionally, we also store an encoded arbitrary assignment $w$. That way, we can construct $M'$ which does not have access to the $\mathsf{SAT}$ oracle, but instead reaches for the encoded answers:

1. $M'$ runs as $M^\mathsf{SAT}$
2. when $M$ performs its $i$-th query the oracle, $M'$ reaches for $a_i$ to get the answer
   1. if the answer is positive, $M'$ verifies that $c_i$ is a correct satisfying assignment
   2. otherwise it checks that $w$ is not a satisfying assignment

Notice how every step of $M'$ is poly-time bounded, thus $M'$ runtime is poly-time.

We must check all possible assignments for an unsat formula, thus we universally quantify $w$:

\begin{align}
  x \in L &\iff \exists y \, M^\mathsf{SAT}(x, y) = 1 \\
          &\iff \exists y \, \exists a_1 \exists c_1 \, \cdots \, \exists a_{q(x, y)} \exists c_{q(x, y)} \, \forall w \, M'(x, y, \langle a_1, c_1, \cdots, a_{q(x, y)}, c_{q(x, y)}\rangle, w) = 1 \\
          &\iff \exists \langle y, a_1, c_1, \cdots, a_{q(x, y)}, c_{q(x, y)}\rangle \, \forall w \, M'(x, y, \langle a_1, c_1, \cdots, a_{q(x, y)}, c_{q(x, y)}\rangle, w) = 1 \label{eq:sigma_form}
\end{align}

$M^\mathsf{SAT}$ makes $q(x, y)$-many $\mathsf{SAT}$ queries, where $q$ is a polynomial function. We additionally note that all $a_i$, $c_i$, $w$, $y$ are poly-size bounded. Thus we quantify over poly-size variables.

\autoref{eq:sigma_form} is of the $\Sigma_2\mathsf{P}$ form, thus $L \in \Sigma_2\mathsf{P}$

## $\Sigma_2\mathsf{P} \subseteq \mathsf{NP}^\mathsf{SAT}$

Let $L \in \Sigma_2\mathsf{P}$. Then

$$
  x \in L \iff \exists y \forall z \, M(x, y, z) = 1
$$

Where $M$ runs in $poly(|x|)$. Given $x$ and $y$, $\forall z \, M(x, y, z) = 1$ is a $\Pi_1\mathsf P = \mathsf{coNP}$ problem. But we know that $\mathsf{coNP} \subseteq \mathsf{P}^{\mathsf{SAT}}$. Let $M'$ be a TM with the $\mathsf{SAT}$ oracle that solves $\forall z \, M(x, y, z) = 1$.

We construct an NTM $N$ which chooses $y$ non-deterministically and runs $M'$. Then

$$
  x \in L \iff N(x) = 1
$$

So $L \in \mathsf{NP}^\mathsf{SAT}$.

Thus, $\mathsf{NP}^\mathsf{SAT} = \Sigma_2\mathsf{P}$ $\square$.

# 2

# 3
