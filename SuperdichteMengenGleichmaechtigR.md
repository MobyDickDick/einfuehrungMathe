In [this earlier post](https://math.stackexchange.com/questions/5086426/is-every-uncountable-subset-of-mathbb-r-equinumerous-to-a-superdense-subset-o/5086451), an attempt was made to show that every uncountable subset of $\mathbb{R}$ is equinumerous to a superdense subset of $(0,1)$.

This raises the following question:

> **Is every superdense null subset of $(0,1)$ also equinumerous to $\mathbb{R}$?**

A subset $M \subset (0,1)$ is said to be **superdense** if it is uncountable and intersects every open subinterval $(a,b) \subset (0,1)$ in uncountably many points.

Assume further that $M$ is a **null set**, meaning it has Lebesgue outer measure zero—or, alternatively, that it vanishes under a naively defined outer measure $\kappa$, approximated via open intervals.

> **Conjecture:** Every superdense null set $M \subset (0,1)$ is equinumerous to the real numbers $\mathbb{R}$.

Two complementary constructive arguments supporting this claim are presented below:

- One based on a **Cantor-style recursive midpoint construction**,  
- The other based on a **canonical open-compact exhaustion principle**.

Both approaches operate under minimal assumptions, avoiding the Axiom of Choice, ZFC, or advanced measure-theoretic tools.

---

## **Definitions (for clarity)**

A set $M \subseteq (0,1)$ is **superdense** if
$$
\forall\, a,b \in (0,1),\; a < b\; \Rightarrow\; |M \cap (a,b)| > \aleph_0.
$$

The set $M$ is a **null set** (with respect to a naive outer measure $\kappa$) if
$$
\forall \varepsilon > 0,\; \exists \text{ open cover } U = \bigcup_{i \in \mathbb{N}} I_i \supseteq M \text{ with } \sum_i |I_i| < \varepsilon.
$$

---

## **First Proof: Recursive Cantor-style midpoint construction**

A compact perfect subset $K \subseteq M$ can be constructed recursively.

Begin with the full interval $(0,1)$. Since $M$ is superdense, four distinct points $x_1, x_2, x_3, x_4 \in M$ can be selected such that $x_1 < x_2 < x_3 < x_4$ and
$$
x_2 - x_1 + x_4 - x_3 < \frac{2}{3}.
$$
These points define two closed intervals:  
$I_{1,1} := [x_1, x_2]$ and $I_{1,2} := [x_3, x_4]$.

Now proceed recursively:
- In each of the left and right thirds of every interval at generation $n$, choose two new points in $M$ to form subintervals contained in $M$, ensuring that the length is at most $\frac{2}{3}$ of the parent interval (as in the Cantor set construction, the middle third is excluded).
- Define $K_n := \bigcup_{k=1}^{2^n} I_{n,k}$.
- Let $K := \bigcap_{n=1}^\infty K_n$.

Then $K \subseteq M$, $K$ is closed (being a nested intersection of closed sets), bounded within $(0,1)$, and perfect (since every point is a limit point). Hence, $K$ is compact and perfect, so $K \sim \mathbb{R}$.

Since $K \subseteq M$, and $M \setminus K$ remains superdense and null set, the process may be repeated to construct disjoint compact perfect sets $K_n \subseteq M$, each equinumerous to $\mathbb{R}$.

Therefore:
$$
M \supseteq \bigcup_{n \in \mathbb{N}} K_n \sim \mathbb{R}.
$$

---

## **Second Proof: Canonical open-compact exhaustion argument**

>Remark: I'm not quite sure if my arguments here are really valid. Plese help me to improve it or to show that it can't be true. Thank you:-) !

1. Begin with a compact set $K_1 \subset M$ that contains countably infinitely many accumulation points.

2. Given $K_1, \dots, K_n$, define:
   $$
   K_{n,t} := \bigcup_{k=1}^n K_k,
   $$
   and the remainder:
   $$
   M_{n,d} := M \setminus K_{n,t}.
   $$

   Since $M$ is a null set, it is possible to cover $M_{n,d}$ with an open set $U_n$ such that
   $$
   \kappa(M_{n,d}) < \frac{1}{2^n}.
   $$

   Using the superdensity of $M$, a compact set $K_{n+1} \subset M_{n,d}$ can be extracted with countably infinitely many accumulation points.

3. Repeat this process inductively.

### Measure result:

By construction:
$$
\kappa\left(M \setminus \bigcup_{n=1}^N K_n\right) < \frac{1}{2^{N-1}} \Rightarrow \kappa\left(M \setminus \bigcup_{n=1}^\infty K_n\right) = 0.
$$

Let:
$$
R := M \setminus \bigcup_{n=1}^\infty K_n.
$$

---

### Lemma: $R$ is not superdense

**Proof:**  
If $R$ were superdense, then in each step $n$, a compact subset $K_{n+1} \subset R$ with countably infinitely many accumulation points could be extracted, contradicting the definition of $R$ as the remainder after the full extraction.  
Hence, $R$ cannot be superdense. ∎

---

## **Conclusion**

Since $R$ is not superdense but $M$ is, $R$ must be structurally negligible. Therefore:
$$
M = \bigcup_{n=1}^\infty K_n.
$$

At least one of the compact sets $K_m$ must be uncountable—otherwise, $M$ would be countable, contradicting its superdensity. Because $K_m$ is compact with infinitely many accumulation points, it follows that
$$
K_m \sim \mathbb{R},\quad \text{and thus } M \sim \mathbb{R}.
$$

---

## **Optional Reformulation via Canonical Exhaustion**

Let:
- $\mathbb{V} := \{ U \subset (0,1) \mid U \text{ open},\; M \subset U \}$,
- $\mathbb{W} := \{ K \subset (0,1) \mid K \text{ compact},\; K \subset M \}$.

Then the following canonical exhaustion principle holds:
$$
\bigcap_{\substack{U \in \mathbb{V},\\ K \in \mathbb{W},\\ K \subset M \subset U}} (U \setminus K) = \emptyset.
$$

This is logically equivalent to:
$$
M = \bigcup_{K \in \mathbb{W}} K.
$$

In the specific construction described above—using nested open covers $U_n$ (as M is a null set, a sequence $$(U_n)_{n\in \mathbb{N}} \wedge \lambda*(U_n) < \frac{1}{2^n}$$ can get established)
and disjoint compact subsets $K_n \subset M$ (as guaranteed by the previous argument)—one obtains:
$$
\bigcap_{n \in \mathbb{N}} (U_n \setminus K_n) = \emptyset,
$$
which reflects the exhaustion structure of $M$ in explicit, constructive terms.

---

## **Final Conclusion**

Using either the recursive midpoint construction or the canonical open-compact exhaustion argument, it follows that every superdense null subset $M \subset (0,1)$ is equinumerous to $\mathbb{R}$.

This result highlights the structural richness of uncountable null sets in $(0,1)$, and their alignment with the cardinality and accumulation-point topology of the real line—even within a purely constructive framework.

∎
