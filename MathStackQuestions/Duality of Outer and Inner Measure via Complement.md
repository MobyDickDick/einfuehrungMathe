
## Lemma: Duality of Outer and Inner Measure via Complement

**Lemma.**  
Let $M \subset (0,1)$. Then
$$
\kappa(M) + \nu((0,1) \setminus M) = 1,
$$
and therefore,
$$
\kappa(M) = \nu(M).
$$

**Proof.**  

Let $\mathbb{V}_M$ denote the family of open sets $U \subset (0,1)$ such that $M \subseteq U$.

Let $\mathbb{W}_M$ denote the family of compact (or closed) subsets $K \subset (0,1)$ such that $K \subseteq M$.

Let $A := (0,1) \setminus M$.

The outer measure is defined by:
$$
\kappa(M) := \inf\{ \lambda(U) \mid U \in \mathbb{V}_M \},
$$
and the inner measure by:
$$
\nu(M) := \sup\{ \lambda(K) \mid K \in \mathbb{W}_M \}.
$$

We now observe:
$$
\begin{align}
1 - \kappa(M)
  &= \lambda((0,1)) - \inf \{ \lambda(U) \mid U \in \mathbb{V}_M \} \\
  &= \sup \{ \lambda((0,1) \setminus U) \mid U \in \mathbb{V}_M \} \\
  &= \sup \{ \lambda(K) \mid K \in \mathbb{W}_A \} \\
  &= \nu((0,1) \setminus M)
\end{align}
$$

Hence:
$$
1 - \kappa(M) = \nu((0,1) \setminus M).
$$

But from the previous result, we also know:
$$
\nu(M) + \nu((0,1) \setminus M) = 1,
$$
so we conclude:
$$
1 - \kappa(M) = 1 - \nu(M),
$$
and therefore:
$$
\kappa(M) = \nu(M).
$$

Since the roles of $M$ and $(0,1) \setminus M$ can be interchanged, it also follows that:
$$
\kappa((0,1) \setminus M) = \nu((0,1) \setminus M).
$$

$\blacksquare$
