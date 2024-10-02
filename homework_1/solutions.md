---
title: Computational complexity, Homework 1
geometry: margin=2.5cm
author:
  - Marcin Wojnarowski
  - Dario Halilovic
  - Toni Jubés Monforte
date: 1-10-2024
---

# 1

We show both sides of the implication:

- $(\implies)$: Let $M$ be a decisive polytime NTM that decides the language $L$. Notice
first that one may decide if $x \in L$ or $x \not\in L$ by running $M$ on the input $x$, and if there is a computation path that outputs __yes__, then $x \in L$; otherwise, $x \not\in L$, and it must be the case that there is a computation path that outputs __no__(by decisiveness).

This observation is sufficient to construct two polytime verifiers $V$ and $V'$ that will show that $L \in NP$ and $L \in coNP$, respectively, by interpreting the certificate $C$ as the computation path, and running $M$ deterministically with that computation path. Specifically, on input $\langle x, C \rangle$, the verifier $V$:
    - Runs $M$ on the input $x$ by interpreting $C$ as the computation path.
    - Outputs __yes__ if $M$ returns __yes__, and outputs __false__ otherwise.

Similarly, on input $\langle x, C \rangle$, the verifier $V'$:
    - Runs $M$ on the input $x$ by interpreting $C$ as the computation path.
    - Outputs __yes__ if $M$ returns __no__, and outputs __false__ otherwise.

Since $M$ decides $L$, for $x \in L$, there exists a computation of $M$ that halts with output __yes__, thus showing that $V$ is a polytime verifier for $L$. Moreover, for $x \not\in L$, there exists a computation path of $M$ such that the output is __no__, and therefore $V'$ is also a polytime verifier for $\overline{L}$.

- $(\impliedby)$: Let $L \in NP \cap coNP$, and let $V$ and $V'$ be polytime verifiers for $L$ and $\overline{L}$, respectively. We construct a decisive NTM $M$ that decides $L$ the following way:
    - Non-deterministically choose each bit of the certificate $C$,
    - Run the verifier $V(x, C)$ and output __yes__ if the verifier outputs __yes__.
    - Run the verifier $V'(x, C)$ and output __no__ if the verifier outputs __yes__.
    - Output __maybe__.

If $x \in L$, there exists a computation that will output __yes__ by the definition of $V$, and symmetrically if $x \not\in L$ there exists a computation that will output __no__. Thus $M$ decides $L$.

# 2

# 3
