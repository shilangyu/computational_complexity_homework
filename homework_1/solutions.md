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

# 3
To prove that the KERNEL problem is in NP, we need to show that given a polynomial size certificate, we can verify in polynomial time if it is a valid solution. The certificate for the KERNEL problem is a possible solution represented by a set of vertices $S$ such that $|S| \leq k$. We then need to check if this solution satisfies the two conditions:
* The vertices in $S$ are not connected between each other (independence).
* The set $S \cup N(S)$ contains all the vertices in the graph (dominance).

Checking for the independence condition is straightforward. We iterate over all pairs of vertices in $S$ and check if there is an edge between them. If we find an edge, we return false. This process has a time complexity of $O(k^2)$, which is polynomial in the size of the input.

Checking for the dominance condition is also polynomial. We iterate over all vertices in the graph and check if they are in $S$ or in the neighborhood of $S$. This process has a time complexity of $O(n)$, where $n$ is the number of vertices in the graph.

Thus, since we can verify the correctness of a solution in polynomial time, the KERNEL problem is in NP.

To prove that it is NP-Hard, we will reduce SAT to KERNEL. Given an instance of SAT, we create a new graph $G$ with the following structure:
* For each variable $x_i$, we create three vertices: $x_i$, $\neg x_i$, and $t_i$. We add edges to connect them all with each other (such that this subgraph has a triangle structure).
* For each clause $C_j$, we create a vertex $c_j$ and connect it through edges with the vertices corresponding to the literals in the clause (either some $x_i$ or $\neg x_i$).

To put an example, we have the following graph for the SAT instance $(x_1 \lor x_2 \lor x_3) \land (\neg x_1) \land (\neg x_2 \lor \neg x_3)$:

Now, we will prove that the SAT instance is satisfiable if and only if the graph has a kernel of size $k \leq m$, where $m$ is the number of variables in the SAT instance.


