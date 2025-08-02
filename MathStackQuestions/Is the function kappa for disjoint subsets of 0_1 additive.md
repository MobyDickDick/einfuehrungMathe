
## Is the function $\kappa$ for disjoint subsets of $(0,1)$ additive?

Let $\kappa$ denote an outer measure on subsets of the open interval $(0,1)$, defined constructively via open covers:

$$
\kappa(A) := \inf\left\{ \sum_{i} |U_i| \;\middle|\; A \subseteq \bigcup_i U_i,\; U_i \text{ open intervals} \right\}.
$$

In addition, assume that for every subset $A \subseteq (0,1)$, the measure $\kappa$ is approximable from below by compact subsets:

$$
\kappa(A) = \sup\left\{ \kappa(K) \;\middle|\; K \subseteq A,\; K \text{ compact} \right\}.
$$

Then the following should hold for disjoint compact subsets:

$$
K_1 \cap K_2 = \emptyset \quad \Longrightarrow \quad \kappa(K_1 \cup K_2) = \kappa(K_1) + \kappa(K_2).
$$

Indeed, let

$$
\delta(K_1, K_2) := \min\{ |x - y| \;\middle|\; x \in K_1,\; y \in K_2 \} > 0,
$$

since otherwise $K_1 \cap K_2 \neq \emptyset$. L
