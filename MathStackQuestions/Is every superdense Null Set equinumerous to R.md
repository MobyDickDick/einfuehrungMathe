

---
title: "Is every superdense Null Set equinumerous to $\mathbb{R}?$"
---

## Question

Let $M \subseteq [0,1]$ be an uncountable set of Lebesgue measure zero such that:

 For every open interval $I \subseteq (0,1)$, the intersection $M \cap I$ is uncountable (i.e., $M$ is superdense).

**Conjecture:** $M \sim \mathbb{R}$. Can this be shown constructively?

---

## Attempted Proof (Canonical Exhaustion)

With $\mathbb{V}$ as the set of all open supersets of M and $\mathbb{W}$ as the set of all closed subsets of M ist must be true that:

$$
\bigcap_{\substack{
  U \in \mathbb{V} \\
  K \in \mathbb{W} \\
  K \subset M \subset U
}} U \setminus K = \emptyset
$$

Can it been shown that there must be two sequences $\left(U_n\right)_{n\in \mathbb{N}}$  and $\left(K_n\right)_{n\in \mathbb{N}}$ such that (with $n\in \mathbb{N}$):

1. $K_n \subseteq M$ for all $n$,
2. Each $K_n$ is compact and has at least countably many accumulation points,
3. The sequence is pairwise disjoint: $K_n \cap K_m = \emptyset$ for $n \ne m$,
4. $M = \bigcup_{n\in\mathbb{N}} K_n$.

Since $M$ is uncountable and superdense, there exists some compact $K_1 \subseteq M \cap (0,1)$ with at least countably many accumulation points.

Now assume compact sets $K_1, \dots, K_n \subseteq M$ have been constructed, all pairwise disjoint. Let
$$
K_{\le n} := \bigcup_{k=1}^n K_k.
$$
Because each $K_k$ is compact, so is their union. Then the set $(0,1) \setminus K_{\le n}$ is open, and due to the superdensity of $M$, the intersection $M \cap ((0,1) \setminus K_{\le n})$ is still uncountable. Hence, one can choose another compact subset $K_{n+1} \subseteq M \setminus K_{\le n}$ with countably many accumulation points.

This construction gives a disjoint sequence $(K_n)_{n\in\mathbb{N}}$ of compact subsets of $M$, such that:
$$
M = \bigcup_{n\in\mathbb{N}} K_n.
$$

Proof htat **countably many such compact sets suffice**:

- Each step removes a compact subset $K_n$ from $M$, and the remaining set $M \setminus K_{\le n}$ remains uncountable and superdense.
- At each stage, choose $K_n$ from within an open cover $U_n$ satisfying $\lambda(U_n) < 2^{-n}$, so the total measure of the uncovered portion of $[0,1]$ tends to zero.
- Furthermore, since the sets $K_n$ are constructed inside ever finer regions of $(0,1)$, the **maximum spacing between distinct points** in each $K_n$ becomes arbitrarily small as $n \to \infty$.

Hence, the union of all $K_n$ eventually captures all points of $M$, and there is **no room left** for further disjoint compact subsets beyond countably many steps.

Now observe:
- Each $K_n$ is compact and (by assumption) contains infinitely many accumulation points.
- Therefore, at least one $K_n$ must be uncountable.
- Since each compact metric space with at least countably many accumulation points is of cardinality $\mathfrak{c}$, it follows that at least one $K_n \sim \mathbb{R}$.

Thus, $M \sim \mathbb{R}$, as required.

---

## Related Constructive Lemma

Suppose there is given a sequence of open sets $(U_n)_{n \in \mathbb{N}}$ with the following properties:

1. $M \subseteq U_n \subseteq [0,1]$,
2. $\lambda(U_n) < 2^{-n}$,
3. For all $x \in U_n$, there exists $y \in M$ with $|x - y| < 2^{-n}$.

Then one can construct compact, pairwise disjoint sets $K_n \subseteq M$, such that:

- $\forall n\in\mathbb{N}:\ K_n \subseteq M$,
- $\forall n \ne m: K_n \cap K_m = \emptyset$,
- $\bigcup_{n \in \mathbb{N}} K_n = M$,
- each $K_n$ has at least countably many accumulation points in $M$.

This leads to the same conclusion: $M \sim \mathbb{R}$.

---

## Summary

If a null set $M \subseteq [0,1]$ is superdense (uncountable and intersecting every open interval uncountably), then it is equinumerous with $\mathbb{R}$. This follows constructively by decomposing $M$ into disjoint compact subsets with accumulation structure, observing the vanishing measure and shrinking scale, and deducing cardinality via known properties of compact metric spaces.
