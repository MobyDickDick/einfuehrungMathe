
## Lemma: Countable Additivity for Disjoint Compact Subsets of $(0,1)$

**Lemma.**  
Let $(K_n)_{n \in \mathbb{N}}$ be a sequence of pairwise disjoint compact subsets of $(0,1)$. Then
$$
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right) = \sum_{n \in \mathbb{N}} \lambda(K_n).
$$

**Proof.**  
We first note that
$$
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right) \leq \sum_{n \in \mathbb{N}} \lambda(K_n)
$$
holds by countable subadditivity of the outer measure $\lambda$.

To prove the reverse inequality, fix $\varepsilon > 0$.  
By the previous lemma, for each $n \in \mathbb{N}$ there exists an open set $U_n \supseteq K_n$ such that
$$
\lambda(U_n) < \lambda(K_n) + \frac{\varepsilon}{2^n}.
$$

Then
$$
\bigcup_{n \in \mathbb{N}} U_n
$$
is an open set containing $\bigcup_{n \in \mathbb{N}} K_n$, so we have:
$$
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right)
\leq \lambda\left( \bigcup_{n \in \mathbb{N}} U_n \right)
\leq \sum_{n \in \mathbb{N}} \lambda(U_n)
< \sum_{n \in \mathbb{N}} \left( \lambda(K_n) + \frac{\varepsilon}{2^n} \right)
= \sum_{n \in \mathbb{N}} \lambda(K_n) + \varepsilon.
$$

Since this holds for all $\varepsilon > 0$, it follows that
$$
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right) \leq \sum_{n \in \mathbb{N}} \lambda(K_n)
\quad \text{and} \quad
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right) \geq \sum_{n \in \mathbb{N}} \lambda(K_n).
$$

Hence equality holds:
$$
\lambda\left( \bigcup_{n \in \mathbb{N}} K_n \right) = \sum_{n \in \mathbb{N}} \lambda(K_n).
$$

$\blacksquare$
