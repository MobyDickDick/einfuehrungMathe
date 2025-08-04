
## Can every subset of $(0,1)$ be written as a countable intersection of open sets?

Let $M \subset (0,1)$ be an arbitrary subset. It is well known that closed sets are $G_\delta$, and open sets are trivially so. But what about **arbitrary** sets $M$?

I would like to give a constructive sketch (not relying on classical measure theory) showing that **every** $M \subset (0,1)$ can be expressed as a countable intersection of open sets, i.e.,

$$
M = \bigcap_{n \in \mathbb{N}} U_n \quad \text{with open } U_n \subset (0,1).
$$

To do so, we use a classification of the points in $M$ into three categories, based on measure and local cardinality, and build disjoint compact approximations from each.

---

## Constructive Sketch

We define three pairwise disjoint regions of $M$ and exhaust them by disjoint compact sets.

---

### Step 1: Decompose $M$ into three regions

Let $M = M_1 \cup M_2 \cup M_3$, where:

- $M_1$: compact part with positive measure,
- $M_2$: uncountably dense but locally measure-zero,
- $M_3$: locally countable part.

#### (a) Region $M_1$: Compact measure-carrying core

Let $(K_{n,1})_{n \in \mathbb{N}}$ be a disjoint sequence of compact sets such that

$$
\kappa(M) = \kappa\left( \bigcup_{n \in \mathbb{N}} K_{n,1} \right),
$$

where $\kappa$ is the outer measure defined via open covers.

Define $M_1 := \bigcup_{n \in \mathbb{N}} K_{n,1}$.

#### (b) Region $M_3$: Locally countable

Define

$$
M_3 := \left\{ x \in M \;\middle|\; \exists \varepsilon > 0:\; |M \cap U_\varepsilon(x)| \leq \aleph_0 \right\}.
$$

This set is at most countable, hence can be written as a union of disjoint compact sets $(K_{n,3})$.

#### \(c\) Region $M_2$: Overabundant but null

Let $M_2 := M \setminus (M_1 \cup M_3)$. Then each $x \in M_2$ satisfies:

- For every $\varepsilon > 0$, $|M \cap U_\varepsilon(x)| > \aleph_0$,
- But there exists $\varepsilon_0 > 0$ such that $\kappa(M \cap U_{\varepsilon_0}(x)) = 0$.

---

### Step 2: Transform $M_2$ into a superdense model

Let $M_{2,1} \subset M_2$ be obtained by removing all points $x = \sup I$ for open intervals $I \subset (0,1) \setminus M_2$ with $\sup I \in M_2$. This removes at most countably many points.

Now define a bijective, monotonically increasing continuous map

$$
\psi: M_{2,1} \to M_4,
$$

where $M_4 \subset (0,1)$ is a superdense null set (i.e. uncountable in every open interval, but with outer measure zero).

In another post I tried to show that  $M_4$ can be exhausted by a sequence of compact subsets of M_4:

$$
M_4 = \bigcup_{n \in \mathbb{N}} \widetilde{K}_n.
$$

Define preimages $K_{n,2} := \psi^{-1}(\widetilde{K}_n) \subset M_{2,1} \subset M_2$. Then $(K_{n,2})$ is a disjoint sequence of compact sets. Add the removed supremum points to the $K_{n,2}$ without loss of disjointness.

Thus:

$$
M_2 = \bigcup_{n \in \mathbb{N}} K_{n,2}.
$$

---

### Step 3: Construct the open sets

Now define:

$$
U_n := (0,1) \setminus \bigcup_{k=1}^n \left( K_{k,1} \cup K_{k,2} \cup K_{k,3} \right).
$$

Each $U_n$ is open, and

$$
M = \bigcap_{n \in \mathbb{N}} U_n.
$$

So every $M \subset (0,1)$ is a $G_\delta$ set, with open sets $U_n$ constructively built from disjoint compact approximations.

$\blacksquare$
