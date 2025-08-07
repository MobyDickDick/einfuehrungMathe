
## Every Superdense Null Subset of $(0,1)$ is Equinumerous to $\mathbb{R}$ (via Cantor-style Construction)

This post presents evidence suggesting that every uncountable subset of the real numbers could be equinumerous to the real numbers themselves.  
If the conjecture below holds, then the overall argument may form part of a complete proof.

In [this earlier post](https://math.stackexchange.com/questions/5086426/is-every-uncountable-subset-of-mathbb-r-equinumerous-to-a-superdense-subset-o/5086451), an attempt was made to show that every uncountable subset of $\mathbb{R}$ is equinumerous to a superdense subset of $(0,1)$.

This raises the converse question:

> **Is every superdense null subset of $(0,1)$ also equinumerous to $\mathbb{R}$?**

Definitions:

- A subset $M \subset (0,1)$ is **superdense** if
  $$
  \forall\, a,b \in (0,1),\; a < b \Rightarrow |M \cap (a,b)| > \aleph_0.
  $$

- The set $M$ is a **null set** (with respect to a naive outer measure $\kappa$) if
  $$
  \forall \varepsilon > 0,\; \exists \text{ open cover } U = \bigcup_{i \in \mathbb{N}} I_i \supseteq M \text{ with } \sum_i |I_i| < \varepsilon.
  $$

The following describes a **Cantor-style midpoint construction** that extracts a compact perfect subset $K \subseteq M$ equinumerous to $\mathbb{R}$.

---

### Recursive Construction

Start with the interval $(0,1)$. Since $M$ is superdense, four points can be found such that
$$
x_1 < x_2 < x_3 < x_4 \in M
$$
and the outer intervals
$$
I_{1,1} := [x_1, x_2],\quad I_{1,2} := [x_3, x_4]
$$
have total length less than $\frac{2}{3}$.

Proceed recursively:

- For each interval $I_{n,k}$ from generation $n$, select two subintervals in the left and right thirds of $I_{n,k}$.
- The subintervals are closed and have total length $\leq \frac{2}{3}$ of the parent interval.
- The **endpoints** of all intervals are chosen from $M$.
- Let $K_n := \bigcup_{k=1}^{2^n} I_{n,k}$.

Define:
$$
K := \bigcap_{n=1}^\infty K_n.
$$

---

### Why $K \subseteq M$

At every step of the construction, the intervals $I_{n,k} = [a_{n,k}, b_{n,k}]$ are chosen such that **both endpoints** $a_{n,k}, b_{n,k} \in M$. These endpoints are retained in all future generations and thus lie in every $K_n$. Therefore:
$$
a_{n,k},\ b_{n,k} \in \bigcap_{n=1}^\infty K_n = K.
$$

Any point not serving as an endpoint of some interval in the construction may be excluded in a later step. Hence, **all points in $K$ arise from endpoints in $M$**, and it follows that
$$
K \subseteq M.
$$

---

### Properties of $K$

- $K$ is a nested intersection of closed intervals $\Rightarrow$ **closed**.
- $K \subset (0,1)$ $\Rightarrow$ **bounded**.
- Every point of $K$ is a limit point of $K$ $\Rightarrow$ **perfect**.

Thus, $K$ is **compact and perfect**, i.e., a **Cantor-type set**. In particular,
$$
K \sim \mathbb{R}.
$$

---

### Repetition and Conclusion

Since $K \subseteq M$, and $M$ remains superdense and null after removing $K$, the process can be repeated to produce disjoint compact perfect subsets $K_n \subset M$.

Let
$$
M' := \bigcup_{n \in \mathbb{N}} K_n.
$$

Then $M' \subseteq M$ and
$$
M' \sim \mathbb{R}.
$$

Thus,
$$
M \sim \mathbb{R}.
$$

Do you think this could be a way of showing that my conjecture is true?
