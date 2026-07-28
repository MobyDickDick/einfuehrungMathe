
## Lemma: Additivity of Inner Measure on Complements

**Lemma.**  
Let $M \subset (0,1)$. Then
$$
\nu(M) + \nu((0,1) \setminus M) = 1.
$$

**Proof (by contradiction).**  
Suppose instead that
$$
\chi := 1 - \nu(M) - \nu((0,1) \setminus M) > 0.
$$

From the definition of $\nu(M)$ and $\nu((0,1)\setminus M)$, we can choose disjoint sequences of compact sets:
- $(K_n)_{n \in \mathbb{N}}$ with $K_n \subset M$ and
  $$
  \sum_{n \in \mathbb{N}} \lambda(K_n) > \nu(M) - \frac{\chi}{4},
  $$
- $(L_n)_{n \in \mathbb{N}}$ with $L_n \subset (0,1) \setminus M$ and
  $$
  \sum_{n \in \mathbb{N}} \lambda(L_n) > \nu((0,1)\setminus M) - \frac{\chi}{4}.
  $$

These sequences are pairwise disjoint by construction.

Let
$$
K := \bigcup_{n \in \mathbb{N}} K_n, \quad
L := \bigcup_{n \in \mathbb{N}} L_n.
$$

Let $\varepsilon := \chi / 4 > 0$.  
By the openness approximation lemma, we can find open supersets $U_1 \supseteq K$ and $U_2 \supseteq L$ such that:
$$
\lambda(U_1) < \lambda(K) + \varepsilon, \quad
\lambda(U_2) < \lambda(L) + \varepsilon.
$$

Then
$$
\lambda(U_1 \cup U_2) \leq \lambda(U_1) + \lambda(U_2)
< \lambda(K) + \lambda(L) + 2\varepsilon
< \nu(M) + \nu((0,1)\setminus M) + \frac{\chi}{2} = 1 - \frac{\chi}{2}.
$$

Define
$$
K_R := (0,1) \setminus (U_1 \cup U_2),
$$
a closed subset of $(0,1)$ with
$$
\lambda(K_R) = 1 - \lambda(U_1 \cup U_2) > \frac{\chi}{2} > 0.
$$

Now, $K_R$ is disjoint from both $K$ and $L$, hence
$$
K_R \cap M \subseteq M \setminus K, \quad
K_R \cap ((0,1)\setminus M) \subseteq (0,1)\setminus M \setminus L.
$$

Since $K_R$ has positive outer measure and is disjoint from all the $K_n$ and $L_n$, we must have:
- Either $\kappa(K_R \cap M) > 0$, hence also $\nu(K_R \cap M) > 0$, or
- $\kappa(K_R \cap ((0,1)\setminus M)) > 0$, hence also $\nu(K_R \cap ((0,1)\setminus M)) > 0$.

But this contradicts the assumption that
- $\nu(M) \geq \sum \lambda(K_n) > \nu(M) - \chi/4$, and similarly
- $\nu((0,1)\setminus M) \geq \sum \lambda(L_n) > \nu((0,1)\setminus M) - \chi/4$,

because otherwise one could further increase the value of $\nu(M)$ or $\nu((0,1)\setminus M)$ by including part of $K_R$, contradicting the assumption that the original sequences $(K_n)$ and $(L_n)$ nearly saturated their respective suprema.

Hence, the assumption $\chi > 0$ must be false, and we conclude:
$$
\nu(M) + \nu((0,1) \setminus M) = 1.
$$

$\blacksquare$
