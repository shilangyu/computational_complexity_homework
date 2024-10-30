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

### $\mathsf{NP}^\mathsf{SAT} \subseteq \Sigma_2\mathsf{P}$

Let $L \in \mathsf{NP}^\mathsf{SAT}$. Then

TODO

### $\Sigma_2\mathsf{P} \subseteq \mathsf{NP}^\mathsf{SAT}$

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

# 2

# 3
