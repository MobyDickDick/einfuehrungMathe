
## Lemma: Open Cover Approximation for Compact Sets

**Lemma.**  
Let $K \subset (0,1)$ be compact. Then for every $\varepsilon > 0$, there exists an open set $U \supseteq K$ such that
$$
\lambda(U) < \nu(K) + \varepsilon,
$$
where $\lambda$ denotes the standard Lebesgue outer measure and $\nu(K)$ is the inner measure defined by
$$
\nu(K) := \sup\{ \lambda(F) \mid F \subseteq K,\; F \text{ compact} \}.
$$

**Proof.**  
Since $K$ is compact in $(0,1)$, its complement $(0,1) \setminus K$ is open. Thus it can be written as a **finite or countable disjoint union** of open intervals:
$$
(0,1) \setminus K = \bigcup_{n=1}^{N} (a_n, b_n), \quad \text{where } 0 \leq N \leq \infty,\ a_n < b_n.
$$
(Empty intervals are omitted.)  
Assume $N = \infty$; the finite case follows analogously.

We may reorder the intervals so that their lengths are non-increasing:
$$
\forall n\in \mathbb{N} \quad b_k - a_k \geq b_{k+1} - a_{k+1}
$$
Then
$$
\sum_{n=1}^{\infty} (b_n - a_n) = \lambda\big((0,1)\setminus K\big) = 1 - \nu(K).
$$
Since the series converges, for any given $\varepsilon > 0$ we can choose $m \in \mathbb{N}$ such that
$$
\sum_{n=1}^m (b_n - a_n) > 1 - \nu(K) - \frac{\varepsilon}{2}.
$$
Now define for each $n = 1, \dotsc, m$ the **closed intervals**
$$
J_n := [a_n, b_n],
$$
and set
$$
A := \bigcup_{n=1}^m J_n.
$$
Then $A$ is compact, and
$$
U := (0,1) \setminus A
$$
is an open set containing $K$, because the remaining intervals $(a_n, b_n)$ with $n > m$ still lie in $U$.

Now:
$$
\lambda(U) = 1 - \lambda(A) = 1 - \sum_{n=1}^m (b_n - a_n) < \nu(K) + \frac{\varepsilon}{2}.
$$

To reduce the measure further and ensure an **open cover** of $K$, we **shrink** each interval $J_n$ by defining:
$$
J_n' := [a_n + \delta_n,\; b_n - \delta_n],
$$
where $\delta_n > 0$ is chosen such that:
$$
\delta_n < \frac{1}{2}(b_n - a_n) \quad \text{and} \quad \sum_{n=1}^m 2\delta_n < \frac{\varepsilon}{2}.
$$

Letting
$$
U_\varepsilon := (0,1) \setminus \bigcup_{n=1}^m J_n',
$$
we obtain an open set $U_\varepsilon \supseteq K$, and its measure satisfies:
$$
\lambda(U_\varepsilon) = 1 - \sum_{n=1}^m \big( (b_n - a_n) - 2\delta_n \big) = \lambda(U) + \sum_{n=1}^m 2\delta_n < \nu(K) + \varepsilon.
$$

$\blacksquare$

---

**Remarks.**

- In the case where $(0,1) \setminus K$ is already a finite union of open intervals, the same argument applies with the sum taken up to $N$.
- This lemma shows that for compact $K \subset (0,1)$, the outer measure $\kappa(K)$ can be approximated from above by open supersets with measure arbitrarily close to $\nu(K)$.
- This is a key step toward proving $\nu = \kappa$ on all subsets of $(0,1)$ by approximating general sets via compacts and open covers.
