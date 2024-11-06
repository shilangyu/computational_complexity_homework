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

# 2
We define a set of oracles $\mathcal{A}$ as follows:
$$
\mathcal{A} = \left\{ A \subseteq \{0, 1\}^* : \forall n \in \mathbb{N}, \ \ |A \cap \{0, 1\}^n| \in \{0, 2^{n-1}\} \right\}
$$
Given an oracle $A \in \mathcal{A}$, we define the language $L_A$:
$$
L_A = \left\{ 1^n : |A \ \cap \ \{0,1\}^n|/2^n = \frac{1}{2} \right\}
$$


We have  
$L_A \in \mathsf{RP}^A$
for every $A$ in $\mathcal{A}$
since $L_A$ can be decided by an $\mathsf{RP}^A$ machine that, on input $1^n$, creates a random binary string $x \in \{0, 1\}^n$ and checks if $x \in A$. This machine accepts if $x \in A$ and rejects otherwise. As each string is equally likely to be chosen, the probability of acceptance is $1/2$ if $|A \cap \{0, 1\}^n| = 2^{n-1}$ (i.e. $1^n \in L_A$) and $0$ otherwise.
Thus, $\forall A \in \mathcal{A}$, $L_A \in \mathsf{RP}^A$.

Constructing $A$ such that $L_A \notin \mathsf{coRP}^A$ is more difficult. As done in an exercise in the course, we will construct $A$ dynamically so that no $\mathsf{coRP}$ machine $M$ correctly decides $L_A$. Since it is the case of $\mathsf{coRP}^A$, we will find an oracle $A$ and language $L_A$ that, for each $\mathsf{coRP}$ machine $M$ with access to the oracle $A$, there exists a string in the language $1^n \in L_A$ that outputs $M^A(1^n) = 0$ with non-zero probability, which violates the definition of a $\mathsf{coRP}$ machine. 

We let $\mathcal{M}$ be the set of all $\mathsf{coRP}$ Turing machines while having oracle access. This set is countable and hence there exists a sequence $(M_i)_{i \in \mathbb{N}}$ of non-deterministic Turing machines that contains all of $\mathcal{M}$. Furthermore, we impose that each $M \in \mathcal{M}$ appears infinitely many times\footnote{By the countable axiom of choice, a countable union of countable sets is countable.}.

We will construct $A$ dynamically, by specifying what elements of $\{0, 1\}^n$ it contains for increasingly larger values of $n$. To do so, it might be easier to think of $A$ as a function 
$$
A : \{0, 1\}^* \to \{0, 1, *\}
$$
where $A(x) = 0$ if $x \notin A$, $A(x) = 1$ if $x \in A$ and $A(x) = *$ if the membership is not yet fixed. We thus start with $A(x) := *$ for all $x \in \{0, 1\}^*$ and fix membership values on the fly.

For increasing values of $i = 0, 1, 2, \ldots$, we try to set $A$ in such a way that $M_i$ fails to decide $L_A$. At each step $i$, we run $M_i$ on input $1^i$ with oracle $A$, which will query $A$ only on the membership of some elements of length $i$. Whenever a membership query is made on input $x$, we set its undefined value $*$ to $A(x) := 0$. If $1^i \notin L_A$, $M_i$ might accept $1^i$ with probability at most $1/2$. If it is the case, we reset our membership to undefined for all length $n$, i.e., $A(x) := *$ for all $x$ of length $i$, and run the machine again. Almost surely, $M_i$ will eventually in a finite time reject $1^n$.

If $M_i$ rejects $1^n$ with oracle $A$, we need to check how many values of $x$ of length $n$ were queried by $M_i$. Let $\Gamma = \{x_1, \ldots, x_p\}$ be the set of membership queries made to $A$ on this path. If $|\Gamma| > 2^{n-1}$, we set $A(x) = 0$ for all $x \in \{0, 1\}^n$ that are not in $\Gamma$ so that $1^n \notin L_A$, and we move on to the next $i$. Otherwise, if $|\Gamma| \leq 2^{n-1}$, we can choose $2^{n-1}$ strings of length $n$ that are not in $\Gamma$ and set $A(x) = 1$. Thus, on this instance which happens with non-zero probability, the $\mathsf{coRP}$ machine $M_i^A$ will be rejecting $1^n$ even though $1^n \in L_A$, ruling out $M_i^A$ as a decider for $L_A$.

Finally, since each $M \in \mathcal{M}$ appears infinitely many times in the sequence, at some point it must hold that $|\Gamma| = n^{O(1)} \geq 2^{n-1}$, causing at least one input to be wrongly decided by $M_i$. 

Since there is no $\mathsf{coRP}$ machine that can decide $L_A$ with oracle $A$, we have that $L_A \notin \mathsf{coRP}^A$.

In conclusion, we have shown that for every $A \in \mathcal{A}$, $L_A \in \mathsf{RP}^A$; and that there exists an $A$ such that $L_A \notin \mathsf{coRP}^A$, which implies that $\mathsf{RP}^A \neq \mathsf{coRP}^A$ for some $A$. $\square$

# 3
