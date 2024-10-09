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

Example inline math $x = \frac{1}{\lambda}$

Example block

$$
\begin{matrix}
	x &=& r \sin \theta \cos \phi \\
	y &=& r \sin \theta \sin \phi \\
	z &=& r \cos \theta \\
\end{matrix}
$$

# 2

We first verify the $\textsc{D3SAT}$ problem through the same witness function as with $\textsc{SAT}$, which we know is a polynomial one. Thus, $\textsc{D3SAT}$ is in $\mathsf{NP}$.

To prove that the $\textsc{D3SAT}$ problem is $\mathsf{NP}$-hard, we will reduce from $\textsc{SAT}$ to $\textsc{D3SAT}$. Given an instance of $\textsc{SAT}$, we can construct an equivalent instance of $\textsc{D3SAT}$ by transforming each clause into equivalent clauses with three distinct variables. We separate the processing of these clauses into four different cases:

1. If the clause has three distinct variables, i.e., $C$ is equivalent to $(x_1 \lor x_2 \lor x_3)$, we leave it as is.
2. If the clause is a tautology, i.e., in $C$ there is a variable $x$ and its negation $\neg x$, we directly skip it as it will always be satisfied no matter the assignment.
3. If the clause has only two distinct variables due to a repetition of a literal, i.e., $C$ is equivalent to $(x_1 \lor x_1 \lor x_2)$, we can replace it with two clauses: $(x_1 \lor x_2 \lor x_3) \land (x_1 \lor x_2 \lor \neg x_3)$, where $x_3$ is a new variable.
4. If the clause has only one distinct variable, i.e., $C$ is equivalent to $(x_1 \lor x_1 \lor x_1)$, we can replace similarly to what we did in the previous case but with two more clauses and a new variable: $(x_1 \lor x_2 \lor x_3) \land (x_1 \lor x_2 \lor \neg x_3) \land (x_1 \lor \neg x_2 \lor x_3) \land (x_1 \lor \neg x_2 \lor \neg x_3)$, where $x_2$ and $x_3$ are new variables.

It is direct to see that the first and second cases are equivalent to the original $\textsc{SAT}$ instance. The third and fourth cases are equivalent to the original $\textsc{SAT}$ instance because the new variables $x_2$ and $x_3$ are not present in any other clause, and the new clauses are true if and only if the original clause is true. 

The transformation is linear in the size of the problem, the fourth case being the worst, where for 1 original clause we create 4. Thus, since the resulting instance of $\textsc{D3SAT}$ is satisfiable if and only if the original $\textsc{SAT}$ instance is satisfiable, $\textsc{D3SAT}$ is $\mathsf{NP}$-hard.
# 3
