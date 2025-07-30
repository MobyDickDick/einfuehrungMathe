

Title: Is every superdense null subset of (0,1) equinumerous to $\mathbb{R}$?

**Question:**  

Every subset $M \subset \mathbb{R}$ with $\lambda*(M)>0$ ist equinumerous to $\mathbb{R}$ (look at https://math.stackexchange.com/questions/4420470/cardinality-of-a-subset-of-mathbbr-of-positive-outer-measure ). 

In my post https://math.stackexchange.com/questions/5086426/is-every-uncountable-subset-of-mathbb-r-equinumerous-to-a-superdense-subset-o/5086451 I tried to show that every every uncountable subset of $\mathbb{R}$ is equinumerous to a superdense subset of (0,1)

So the question remains:  
> Is every superdense null subset of (0,1) also equinumerous to $\mathbb{R}$?

Let us define a subset $M \subset (0,1)$ to be *superdense* if it is uncountable and intersects every open subinterval $$(a,b) \subset (0,1)\Leftarrow   a< b $$ in uncountably many points.

Assume further that $M$ is a *null set*, i.e., it has Lebesgue outer measure zero (or alternatively, vanishes under a naively defined outer measure $\kappa$, approximated by open intervals).

> **Conjecture:** Every superdense null set $M \subset (0,1)$ is equinumerous to the set of real numbers $\mathbb{R}$.

This post tries to present two complementary constructive proofs for this fact:

- One based on a **Cantor-style recursive midpoint construction**,
- The other based on a **canonical open-compact exclusion principle**.

Both work under minimal assumptions, without invoking ZFC, the Axiom of Choice, or advanced measure theory.

---

## **Definitions (for clarity)**

Let $M \subseteq (0,1)$ be a set.

We say that $M$ is **superdense** if:
$$
\forall\, a,b \in (0,1),\; a < b\; \Rightarrow\; |M \cap (a,b)| > \aleph_0.
$$

We say that $M$ is a **null set** (with respect to a naive outer measure $\kappa$) if:
$$
\forall \varepsilon > 0,\; \exists \text{ open cover } U = \bigcup_{i \in \mathbb{N}} I_i \supseteq M \text{ with } \sum_i |I_i| < \varepsilon.
$$

---

## **First Proof: Recursive Cantor-style midpoint construction**

We construct a compact perfect subset $K \subseteq M$ by recursion.

Start with the full interval $(0,1)$. Because $M$ is superdense, we can choose four distinct points $x_1, x_2, x_3$ and $x_4$ in $M$ with $x_1<x_2<x_3<x_4$and $$x_2 - x_1 + x_4 - x_3 < \frac{2}{3}$$. These four points define a pair of closed intervals $I_{1,1} := [x_1, x_2]$ and $I_{1,2} := [x_3, x_4]$.

Now proceed recursively:
- In each of the left and right thirds of each interval from generation $n$, choose two new points of $M$ and create subintervals contained in $M$, with length at most $\frac{2}{3}$ of the parent interval (exclude as in the Cantor Set the middle part of the three intervals.
- Define $K_n := \bigcup_{k=1}^{2^n} I_{n,k}$.
- Let $K := \bigcap_{n=1}^\infty K_n$.

Then $K \subseteq M$, $K$ is closed (nested intersection of closed sets), bounded (in $(0,1)$), and perfect (by construction, every point is a limit point).
Thus $K$ is compact and perfect, hence $K \sim \mathbb{R}$.

Because $K \subseteq M$, and $M \setminus K$ is still superdense and null, we can repeat the process and obtain disjoint perfect compact sets $K_n \subseteq M$ with $K_n \sim \mathbb{R}$.

Therefore,
$$
M \supseteq \bigcup_{n \in \mathbb{N}} K_n \sim \mathbb{R}.
$$

---



## **Second Proof: Canonical open-compact exhaustion argument**

1. Start with an initial compact set $K_1 \subset M$ containing countably many accumulation points.

2. Given $K_1,\dots,K_n$, let:
   $$
   K_{n,t} := \bigcup_{k=1}^n K_k
   $$
   and define the remaining part:
   $$
   M_{n,d} := M \setminus K_{n,t}.
   $$
   Since $M$ is a null set, we can cover $M_{n,d}$ by an open cover $U_n$ with
   $$
   \kappa(M_{n,d}) < \frac{1}{2^n}.
   $$
   Using the superdensity of $M$, we extract a compact set $K_{n+1} \subset M_{n,d}$ with **countably infinitely many accumulation points**.

3. Repeat recursively.

### Measure result:

By construction:
$$
\kappa\left(M \setminus \bigcup_{n=1}^N K_n\right) < \frac{1}{2^{N-1}} \Rightarrow \kappa\left(M \setminus \bigcup_{n=1}^\infty K_n\right) = 0.
$$

Let:
$$
R := M \setminus \bigcup_{n=1}^\infty K_n.
$$

## Lemma: $R$ is not superdense

**Proof:** If $R$ were superdense, then in each step $n$ one could find a compact $K_{n+1} \subset R$ with countably infinitely many accumulation points. But that contradicts the definition of $R$ as what remains **after** all such compact extractions. Therefore, $R$ cannot be superdense. ∎

## Conclusion

Since $R$ is not superdense, but $M$ is, $R$ must be "negligible" in structure. So:
$$
M = \bigcup_{n=1}^\infty K_n.
$$

At least one $K_m$ must be uncountable (otherwise $M$ would be countable, contradicting superdensity). Since $K_m$ is compact with infinitely many accumulation points, we conclude:
$$
K_m \sim \mathbb{R},\quad \text{and hence } M \sim \mathbb{R}.
$$

## Optional Reformulation via Canonical Exhaustion

Let:
- $\mathbb{V} := \{ U \subset (0,1) \mid U \text{ open},\; M \subset U \}$
- $\mathbb{W} := \{ K \subset (0,1) \mid K \text{ compact},\; K \subset M \}$

Then the canonical exhaustion statement is:
$$
\bigcap_{\substack{U \in \mathbb{V},\\ K \in \mathbb{W},\\ K \subset M \subset U}} (U \setminus K) = \emptyset
$$

This is logically equivalent to:
$$
M = \bigcup_{K \in \mathbb{W}} K.
$$

In our concrete case with nested open covers $U_n$ and pairwise disjoint compact sets $K_n$, which must exist (take a look at the first proof above) one can write:
$$
\bigcap_{n \in \mathbb{N}} (U_n \setminus K_n) = \emptyset
$$

which reflects the exhaustion structure of $M$ explicitly.

∎

---
## **Conclusion**

Using either the recursive midpoint construction or the canonical open-compact exhaustion argument, we have shown that every superdense null subset $M \subset (0,1)$ is equinumerous to $\mathbb{R}$.

This result highlights the richness of uncountable null sets in $(0,1)$ and their structural alignment with the real line — even in fully constructive frameworks.

∎
