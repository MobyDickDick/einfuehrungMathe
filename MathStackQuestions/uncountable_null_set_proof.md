**Title:** Constructive proof: Every uncountable null subset of $[0,1]$ is equinumerous to $\mathbb{R}$

**Question:**
Let $M \subseteq [0,1]$ be a set with the following properties:

1. $M$ is uncountable,
2. $M$ has outer measure zero, i.e. for every $\varepsilon > 0$, there exists an open set $U$ with $M \subseteq U$ and $\lambda(U) < \varepsilon$,
3. $M$ is **superdense**, i.e., intersects every open interval in $[0,1]$ in an uncountable set.

Can one constructively prove that $M$ has the same cardinality as $\mathbb{R}$?

That is, can we avoid any use of the Axiom of Choice or existence of non-measurable sets, and instead use an explicit process to show $|M| = |\mathbb{R}|$?

---

**Answer:**
Yes, one can give a fully constructive proof that any uncountable, superdense subset of $[0,1]$ with outer measure zero is equinumerous to $\mathbb{R}$. Below are two independent and constructive approaches.

In fact, one can even **reduce the general case** (of any uncountable null set $M \subseteq [0,1]$) to the superdense case, by mapping $M$ onto a superdense null set.

---

### **Reduction: From general uncountable null sets to superdense null sets**

Let $M \subseteq [0,1]$ be uncountable and have outer measure zero. We construct a superdense null set $M^*$ such that $M \sim M^*$.

1. Fix an open cover $U_1 \supseteq M$ with $\lambda(U_1) < 1$, and write $U_1 = \bigcup_{n} I_n$ as a union of disjoint open intervals with rational endpoints.
2. Enumerate the intervals $I_n$ and assign to each a disjoint open interval $J_n \subseteq (0,1)$ with length $2^{-n}$.
3. Construct a bijection $f_n: I_n \to J_n$ (e.g., linear and increasing).
4. Define $f: M \to \bigcup_n J_n$ by $f(x) = f_n(x)$ for $x \in I_n$.

Then $M^* := f(M)$ is:
- uncountable (since $f$ is injective),
- of outer measure zero (as $\lambda(\bigcup_n J_n) < 1$),
- and superdense (since the $J_n$ are dense and $M$ is uncountable).

So $M$ can be mapped bijectively to a **superdense null subset** of $[0,1]$.

---

### **Approach 1: Cantor-type construction (binary refinement method)**

Let $M \subseteq [0,1]$ be an uncountable, superdense set with outer measure zero. We construct a perfect subset $P \subseteq M$ by imitating the construction of the classical Cantor set, but restricting ourselves to subintervals that intersect $M$ in an uncountable way.

#### Step-by-step:
1. Begin with the interval $[0,1]$. Subdivide it into two intervals of equal length: $[0,1/2]$ and $[1/2,1]$.
2. Since $M$ is superdense, each of these intervals intersects $M$ uncountably. Choose both and repeat the process on each.
3. At each stage, divide each retained interval into two equal parts and retain only those subintervals that intersect $M$ uncountably.
4. Proceed recursively. Since $M$ intersects every open subinterval uncountably, this process continues indefinitely.

This produces a tree of nested closed intervals $I_{n,k}$, where each path down the tree defines a point in the limit set $P$. Since we retain two branches at each step (due to superdensity), the limit set $P$ is a **perfect subset of $M$**.

Every perfect subset of $[0,1]$ has cardinality $\mathfrak{c}$, so $|M| = \mathfrak{c} = |\mathbb{R}|$.

---

### **Approach 2: Exhaustion via compact subsets with multiple accumulation points**

Let $M \subseteq [0,1]$ be uncountable and superdense with $\kappa(M) = 0$ (outer measure zero).

#### 1. Outer approximations with open sets

For each $n \in \mathbb{N}$, choose an open set $U_n \supseteq M$ such that
$$
\lambda(U_n) < 2^{-n}, \quad \text{and} \quad U_{n+1} \subseteq U_n.
$$

#### 2. Inductive construction of compact subsets

We build a sequence of compact sets $T_1, T_2, \dots$ with $T_k \subseteq M$, such that:
- Each $T_k$ lies within $U_k$,
- The sets $T_k$ are pairwise disjoint,
- Each $T_k$ has at least two accumulation points,
- $M = \bigcup_{k \in \mathbb{N}} T_k$.

We proceed as follows:
- At step $k$, consider the set $R_k := M \setminus \bigcup_{i=1}^{k-1} T_i$.
- Since $R_k$ is a subset of $U_k$ and $\lambda(U_k) \to 0$, we can "linearly straighten" $U_k$ into an interval $[0,\varepsilon_k]$ via a piecewise affine bijection.
- We map $R_k$ bijectively to a set $R_k' \subseteq [0,\varepsilon_k]$ and find a compact subset $T_k' \subseteq R_k'$ with at least two accumulation points.
- The preimage $T_k := f_k^{-1}(T_k') \subseteq M$ is then compact with the same properties and becomes part of our collection.

#### 3. Exhaustion and cardinality argument

This process yields
$$
M = \bigcup_{k \in \mathbb{N}} T_k, \quad T_k \in \Omega \text{ (compact with $\geq 2$ accumulation points)}.
$$
Since the union is uncountable and the index set is countable, at least one of the $T_k$ must be uncountable.

But every compact, uncountable subset of $[0,1]$ contains a perfect subset, and every perfect subset of $[0,1]$ is of cardinality $\mathfrak{c}$.

Thus, $M$ contains a subset of cardinality $\mathfrak{c}$ and hence $|M| = |\mathbb{R}|$.

---

### **Conclusion**
Every uncountable null subset $M \subseteq [0,1]$ can be mapped bijectively to a superdense null subset, and every such superdense null set contains a perfect subset. Hence $|M| = \mathfrak{c}$. No use of the Axiom of Choice, Vitali sets, or non-measurable subsets is required.

This provides a powerful alternative to classical arguments relying on cardinal arithmetic or diagonalization.

