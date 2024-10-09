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

To prove that the KERNEL problem is in NP, we need to show that given a polynomial size certificate, we can verify in polynomial time a valid witness function. The certificate for the KERNEL problem is a possible solution represented by a set of vertices $S\subseteq V$ such that $|S| \leq k$. For the witness function, we need to check if this solution satisfies the two conditions:

* (Independence) The vertices in $S$ are not connected between each other.
* (Dominance) The set $S \cup N(S)$ contains all the vertices in the graph.

Checking for the independence condition is straightforward. We iterate over all pairs of vertices in $S$ and check if there is an edge between them. If we find an edge, it is not a valid certificate. This process has a time complexity of $O(k^2)=O(|V|^2)$, which is polynomial in the size of the input.

Checking for the dominance condition is also polynomial. We first create the neighborhood set $N(S)$ by iterating over the connections of $S$, and then iterate over all vertices in the graph and check if they are in $S$ or in $N(S)$. This process has a time complexity of $O(k|V|+|V|)=O(|V|^2)$, where $n$ is the number of vertices in the graph.

Thus, since we can verify the correctness of a solution in polynomial time, the KERNEL problem is in NP.

To prove that it is NP-Hard, we will reduce SAT to KERNEL. Given an instance of SAT, we create a new graph $G$ with the following structure:

* For each variable $x_i$, we create three vertices: $x_i$, $\neg x_i$, and $t_i$. We add edges to connect them all with each other (such that this subgraph has a triangle structure).
* For each clause $C_j$, we create a vertex $c_j$ and connect it through edges with the vertices corresponding to the literals in the clause (either some $x_i$ or $\neg x_i$).

To put an example, we have the following graph for the SAT instance $(x_1 \lor x_2 \lor x_3) \land (\neg x_1) \land (\neg x_2 \lor \neg x_3)$:

![](KERNEL_example.png){width=256px}

Now, we will prove that the SAT instance is satisfiable if and only if the graph has a kernel of size $\leq m$, where $m$ is the number of variables in the SAT instance.

$(\implies):$ If the SAT instance is satisfiable, we can construct a kernel of size $m$ by selecting the vertices corresponding to the true literals in a valid assignment, for every $i$, we pick vertex $x_i$ if the variable $x_i$ is true, and $\neg x_i$ otherwise.

Since we are only selecting one value per variable for any $i$, both vertices $x_i$ and $\neg x_i$ will never be connected. Thus, since we do not pick any other vertex and different variables are not directly connected, the set is independent.

Since the assignment satisfies all clauses, any clause vertex will be connected to at least one vertex in the kernel set. Moreover, since the assignment chooses a value for each variable $x_i$, every triangle in the graph will have at least one vertex in the kernel set. Thus, the chosen subset would be dominating.

$(\impliedby):$ For the first proof, we will start with some observations and use them to construct a valid assignment for the SAT instance given a kernel of size $\leq m$.

**Observation 1**: For every variable triangle, we need to pick one of the nodes $x_i$, $\neg x_i$, or $t_i$ for the kernel set to be dominating, since $t_i$ is only directly connected to $x_i$ and $\neg x_i$.

**Corollary 1**: For a set $S$ to be dominating (kernel), it must have a size of at least $m$, being the number of variables in the SAT instance, or equivalently, the number of variables $t_i$.

From this observation and its corollary, we can conclude that the problem of finding a kernel of size $\leq m$ in this type of graph is equivalent to finding a kernel of size exactly $m$. Knowing that there needs to be $m$ nodes connecting to the $t_i$ vertices, we can do the following observation:

**Observation 2**: When looking for a kernel of size $m$, no clause vertex can be in the kernel set, as they are not connected to any $t_i$.

Thus, we can conclude that every kernel of size $m$ will only have exactly one vertex per variable triangle. Now, we just need to take care of the case that one of the picked variables is $t_i$ instead of $x_i$ or $\neg x_i$. We can do this by the following observation:

**Observation 3**: If a variable vertex $t_i$ is in a kernel set, the set created by copying this kernel set and substituting the vertex $t_i$ with either $x_i$ or $\neg x_i$ is also a kernel.

**Proof**: Since the original kernel set $S$ is dominating ($S \cup N(S) = V$), the set $S' = S \setminus \{t_i\} \cup \{x_i\}$ is also dominating because of $S \cup N(S) \subseteq S' \cup N(S') \subseteq V$, since $\{t_i\} \cup N(t_i) \subseteq \{x_i\} \cup N(x_i)$. The same argument can be made for the case where $t_i$ is substituted with $\neg x_i$. Since the set $S'$ is also independent (we still have one vertex per variable triangle), we can conclude that $S'$ is a valid kernel set.

From these observations, we can construct a valid assignment for the SAT instance given a kernel of size $m$ (from Observation 2, it generalizes to $\leq m$). For every picked vertex in the kernel set (one vertex for each variable from Observation 1), we set the corresponding variable to true if the picked vertex is the vertex $x_i$, and false otherwise (even if it is $t_i$, from Observation 3 we can arbitrarily choose it to be false). From the dominance property, we know that every clause vertex is connected to at least one picked vertex, so one of its literals will be set to true, making the clause satisfied. Thus, the constructed assignment satisfies all clauses, and the SAT instance is satisfiable.

Thus, we have shown that the SAT instance is satisfiable if and only if the graph has a kernel of size $\leq m$, where $m$ is the number of variables in the SAT instance. Since SAT is NP-complete, this shows that KERNEL is NP-complete.
