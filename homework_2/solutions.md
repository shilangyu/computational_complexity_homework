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


Define the following variant of the problem:
\begin{align*}
\textsc{3-FixedColourGame} = \{\langle G, c \rangle \,:\, & G \textrm{ is a graph such that Alice has a winning} \\ 
& \textrm{strategy where every allowed 3-coloring } \hat{c} : V \to \{1, 2, 3\} \\ & \textrm{satisfies } \forall x \in \textrm{dom}(c), \hat{c}(x) = c(x) \}
\end{align*}
We argue that $\textsc{3-ColourGame} \in \mathsf{PSPACE}$ by showing that we can solve $\textsc{3-FixedColourGame}$ recursively while re-using a polynomial amount of memory. Indeed, it is enough to solve $\textsc{3-FixedColourGame}$ since
\[
\langle G \rangle \in \textsc{3-ColourGame} \iff \langle G, \emptyset \rangle \in \textsc{3-FixedColourGame}
\]

Let $k(c) = \min(V \setminus \textrm{dom}(c))$ denote the minimal vertex $v \in V$ not in the domain of $c$. Notice that if $\textrm{dom}(c) \neq V$, one has
\begin{align*}
\langle G, c \rangle \in \textsc{3-FixedColourGame} \iff \exists c_0\, \left\langle G, c \cup \{(k(c), c_0)\} \right\rangle \not\in \textsc{3-FixedColourGame}
\end{align*}
This gives us a recursive procedure to solve $\textsc{3-ColourGame}$ as follows:

\begin{algorithm}
    \caption{Poly-space algorithm for $\textsc{3-ColourGame}$}
    \label{alg:algorithm-label}
    \begin{algorithmic}[1]
        \Procedure{HasWinningStrategy}{$G, c$}
            \If{$\textrm{dom}(c) = V$ and $c$ is a 3-coloring of $G$}
                \State \Return {true}
            \EndIf
            \State $v \gets k(c)$
            \For{$c_0 \in \{1, 2, 3\}$}
                \If {$v$ can be colored by $c_0$ and \textsc{HasWinningStrategy}($G$, $c \cup \{(v, c_0)\}$) = false}
                    \State \Return{true}
                \EndIf
            \EndFor
            
            \State \Return{false}
        \EndProcedure

        \vspace{1em}

        \Procedure{Solve3ColourGame}{$G$}
            \State \Return{\textsc{HasWinningStrategy}($G, \emptyset$)}
        \EndProcedure
    \end{algorithmic}
\end{algorithm}

The above algorithm needs $O(n^2)$ space to store $G$, as well as
\[
s(n) = s(n-1) + O(\log(n)) = O(n \log(n))
\]
space from the recursion, hence showing that $\textsc{3-ColourGame} \in \mathsf{PSPACE}$.

To show that $\textsc{3-ColourGame}$ is $\mathsf{PSPACE}$-complete, we reduce in polynomial-time from $\textsc{TQBF}$. Given a Boolean formula $F$ of the form
\[
\exists x_1 \forall x_2 \ldots \forall x_{n-1} \exists x_n \varphi(x_1, \ldots, x_n)
\]
where $\varphi$ is a CNF formula, we construct a graph $G$ such that $\langle G \rangle \in \textsc{3-ColourGame}$ if and only if $F \in \textsc{TQBF}$.

Our graph consists in three parts:

1. First, a triangle composed of 3 vertices: $T$ (True), $F$ (False) and $B$ (Base). These 3 vertices are used to force a 3-coloring to pick a color for true and false assignments of a variable.

2. Second, we create two vertices $x_i$ and $\overline{x_i}$ for every quantified variable $x_i$, connect them to each other, and connect them to vertex $B$.

3. Third, we follow the encoding of CNF clauses used in the reduction from $\textsc{SAT}$ to the decision version of 3-colorability. For each clause of the form $v_1 \lor v_2 \lor v_3 \lor \ldots \lor v_k = (((v_1 \lor v_2) \lor v_3) \lor \ldots ) \lor v_k$, we connect them by stacking OR-gadgets as follows:

\begin{figure}[H]
    \centering
    \begin{tikzpicture}
        \begin{scope}[every node/.style={circle,thick,draw,minimum size = 1.75em}]
        % First gadget
        \node (v1) at (0,0) {$v_1$};
        \node (v2) at (1.5,0) {$v_2$};
        \node (above_v1) at (0,1.25) {};
        \node (above_v2) at (1.5,1.25) {};
        \node (middle_v1_v2) at (0.75, 2.5) {};

        \draw (v1) -- (above_v1);
        \draw (v2) -- (above_v2);
        \draw (above_v1) -- (above_v2);
        \draw (above_v1) -- (middle_v1_v2);
        \draw (above_v2) -- (middle_v1_v2);

        % Second gadget
        \node (above_middle_v1_v2) at (0.75, 3.75) {};
        \node (v3) at (2.25, 2.5) {$v_3$};
        \node (above_v3) at (2.25, 3.75) {};
        \node (middle_v1_v2_v3) at (1.5, 5) {};

        \draw (middle_v1_v2) -- (above_middle_v1_v2);
        \draw (v3) -- (above_v3);
        \draw (above_v3) -- (above_middle_v1_v2);
        \draw (above_v3) -- (middle_v1_v2_v3);
        \draw (above_middle_v1_v2) -- (middle_v1_v2_v3);

        % Third gadget 
        \node (stack) at (2.5, 6.25) {};
        \node (above_stack) at (2.5, 7.5) {};
        \node (vk) at (4, 6.25) {$v_k$};
        \node (above_vk) at (4, 7.5) {};
        \node (root) at (3.25, 8.75) {};

        \draw (stack) -- (above_stack);
        \draw (vk) -- (above_vk);
        \draw (above_stack) -- (above_vk);
        \draw (above_stack) -- (root);
        \draw (above_vk) -- (root);
        \end{scope}

        
        \draw (middle_v1_v2_v3) -- (stack) node[midway,fill=white] {$\cdots$};

        % Selected region
        \draw[dotted] plot [smooth] coordinates {
            (-0.5, -0.5)
            (-0.5, 1.5)
            (0.75, 3)
            (2, 1.5)
            (2, -0.5)
            (-0.5, -0.5)
        };
        \node[text width=2cm] at (-1.25, 2) {OR-gadget for $v_1 \lor v_2$};
    \end{tikzpicture}
    \caption{Encoding of clause $v_1 \lor \ldots \lor v_k$}
    \label{fig:clause-encoding}
\end{figure}

The top of the stack is then connected to the $B$ and $F$ vertices (so that it is colored with the same color as $T$).
\end{enumerate}

An example of the graph generated by the reduction is given in Figure~\ref{fig:full-example}.

\begin{figure}[H]
    \centering
    \begin{tikzpicture}
        \begin{scope}[every node/.style={circle,thick,draw,minimum size = 1.75em}]
        % First component
        \node (T) at (0,2) {$T$};
        \node (F) at (1.5,2) {$F$};
        \node (B) at (0.75, 0.75) {$B$};

        \draw (T) -- (F) -- (B) -- (T);

        % Variables
        \node (x1)     at (-3, -2) {$x_1$};
        \node (x1_neg) at (-1.5, -2) {$\overline{x_1}$};
        \draw (x1) -- (x1_neg) -- (B) -- (x1);

        \node (x2)     at (0, -2) {$x_2$};
        \node (x2_neg) at (1.5, -2) {$\overline{x_2}$};
        \draw (x2) -- (x2_neg) -- (B) -- (x2);

        \node (x3)     at (3, -2) {$x_3$};
        \node (x3_neg) at (4.5, -2) {$\overline{x_3}$};
        \draw (x3) -- (x3_neg) -- (B) -- (x3);

        % Gadgets
        \node (below_x1) at (-3, -3.5) {};
        \node (below_x2) at (0, -3.5) {};
        \node (middle_x1_x2) at (-1.5, -5) {};
        \draw (x1) -- (below_x1);
        \draw (x2) -- (below_x2);
        \draw (below_x1) -- (below_x2) -- (middle_x1_x2) -- (below_x1);

        \node (below_x2_neg) at (1.5, -3.5) {};
        \node (below_x3) at (3, -3.5) {};
        \node (middle_x2_neg_x3) at (2.25, -5) {};
        \draw (x2_neg) -- (below_x2_neg);
        \draw (x3) -- (below_x3);
        \draw (below_x2_neg) -- (below_x3) -- (middle_x2_neg_x3) -- (below_x2_neg);

        % Bent arrows for gadgets rule to B and F
        \draw plot [smooth] coordinates {
            (middle_x1_x2.west)
            (-4, -4)
            (-4, -1)
            (B.west)
        };
        \draw plot [smooth] coordinates {
            (middle_x1_x2.west)
            (-5, -4)
            (-3, 3)
            (F.north)
        };

        \draw plot [smooth] coordinates {
            (middle_x2_neg_x3.east)
            (5, -4)
            (5, -1)
            (B.east)
        };
        \draw plot [smooth] coordinates {
            (middle_x2_neg_x3.east)
            (5.5, -4)
            (5.5, 3)
            (F.east)
        };
        
        \end{scope}
    \end{tikzpicture}
    \caption{Graph generated for the formula $\exists x_1 \forall x_2 \exists x_3 \, (x_1 \lor x_2) \land (\neg x_2 \lor x_3)$. A winning strategy for Alice would be to color $x_1$ and $x_3$ the same color as $T$, which make the OR-gadgets true irrespective of the color Bob chooses for $x_2$ ($T$ or $F$).}
    \label{fig:full-example}
\end{figure}

We now describe the order of processing Alice and Bob follow:
1. First, Alice and/or Bob pick colors for the $T$, $F$ and $B$ vertices.
2. Then, Alice and Bob successively pick a color for $x_i$, for $i = 1, \ldots, n$. Notice that since $x_i$ is connected to $B$, the chosen color is either that of vertex $T$ or $F$. Moreover, since $\overline{x_i}$ is connected to $x_i$ and $B$, there is only one possibility for coloring $\overline{x_i}$, and thus it can be filled by either player.
3. Finally, Alice plays alone on the rest of the graph (this can be simulated by adding dummy vertices that Bob colors on his turns).

The reduction can be done in polynomial time, since the size of the graph is polynomial in the size of the formula and the number of variables. 

Notice that Alice and Bob have picked an assignment of variables in phase 2, and the assignment makes the CNF true if and only if the remainder of the graph is 3-colorable. Therefore, Alice has a winning strategy if and only if, for every variable assignment that Bob makes, Alice can choose her variables accordingly to make the graph 3-colorable. Notice that since Alice plays alone at the end, the graph is 3-colorable if and only if Alice wins.

This shows that Alice has a winning strategy if and only if $F \in \textsc{TQBF}$, hence $\textsc{3-ColourGame}$ is $\mathsf{PSPACE}$-complete.
