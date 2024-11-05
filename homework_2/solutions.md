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
