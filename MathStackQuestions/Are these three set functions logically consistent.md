## 0. Motivation

The aim is to motivate the idea that there may exist a function — denoted by $\nu$ or $\kappa$ — satisfying the following properties:

$$
\nu((0,1)) = 1
$$

and for every subset $M \subseteq (0,1)$,
$$
\nu(M) + \nu((0,1) \setminus M) = 1.
$$

The hope is to establish these properties without invoking any advanced theory, but rather through elementary and intuitive arguments drawn from basic real analysis.

As a first step, it would be desirable to show that
$$
\kappa(M) = \nu(M) \quad \text{for all } M \subset (0,1),
$$
thereby justifying the definition of $\nu$ in terms of a more primitive outer measure $\kappa$.

## 1. Definitions

Three functions are defined on subsets of the unit interval:

$$
\lambda, \nu, \kappa : \mathcal{P}([0,1]) \to [0,1] 
$$

Let $M \subseteq [0,1]$. Consider the following collections:

- $\mathbb{V} := \{ U \subseteq [0,1] \mid U \text{ is open and } M \subseteq U \}$
- $\mathbb{W} := \{ T \subseteq [0,1] \mid T \text{ is compact and } T \subseteq M \}$

For any open set $U \subseteq [0,1]$ that can be written as a **disjoint** union of open intervals $(a_k, b_k)$, define:

$$
\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)
$$


Using this, define:

- $\kappa(M) := \inf\{ \lambda(U) \mid U \in \mathbb{V} \}$
- $\nu(M) := \sup\{ \lambda(T) \mid T \in \mathbb{W} \}$

For compact sets $T \subseteq [0,1]$, let $\lambda(T) := 1 - \lambda([0,1] \setminus T)$, assuming the complement is open and its $\lambda$-value is well-defined via disjoint intervals.

---

## 2. Question


Given these definitions:

> Does it follow that for all $M \subseteq [0,1]$, we have
>
> $$
  \kappa(M) = \nu(M) \quad 
  $$
---

## 3. Preliminary Observation

For open sets $U \subseteq [0,1]$, the value $\lambda(U)$ is well-defined and finite.

For compact sets $T \subseteq [0,1]$, the value $\lambda(T)$ can be derived from the complement, which is open. Since open sets can be approximated from within by compact subsets and from outside by open supersets, the following appears to hold:

$$
\lambda(U) = \kappa(U) = \nu(U), \quad \lambda(T) = \kappa(T) = \nu(T)
$$

---

## 4. Main Argument: Why $\kappa(M) = \nu(M)$?

Let $M \subseteq [0,1]$. Due to the definition of $\nu(M)$, there must exist a sequence of compact sets $(T_k)_{k \in \mathbb{N}} \subseteq \mathbb{W}$ such that $T_k \subset T_{k+1}$ and:

$$
\lim_{k \to \infty} \lambda(T_k) = \nu(M)
$$

Let $T := \bigcup_{k} T_k \subseteq M$. Suppose, for contradiction, that:

$$
\kappa(M \setminus T) > 0
$$

Then, by the definition of $\kappa$, there exists a compact set $T_W \subseteq M \setminus T$ such that $\lambda(T_W) > 0$. Since $T_W$ is disjoint from every $T_k$, one can choose $n \in \mathbb{N}$ such that:

$$
\lambda(T_n) > \nu(M) - \lambda(T_W)
$$

Then $T_n \cup T_W \subseteq M$ is compact and satisfies:

$$
\lambda(T_n \cup T_W) = \lambda(T_n) + \lambda(T_W) > \nu(M)
$$

This contradicts the definition of $\nu(M)$ as a supremum. Therefore:

$$
\kappa(M \setminus T) = 0
$$

Consequently:

$$
\kappa(M) \leq \kappa(T) + \kappa(M \setminus T) = \kappa(T)
$$

and since $T \subseteq M$, also $\kappa(T) \leq \kappa(M)$. Hence:

$$
\kappa(M) = \kappa(T) = \lambda(T) = \nu(M)
$$

---

## 5. Alternative Argument (via mutual approximation)

For every set M it's true that:
$$
\bigcap_{U \in \mathbb{V}} U = \bigcup_{T \in \mathbb{W}} T
$$

This implies:

$$
\bigcap_{U \in \mathbb{V}} U \setminus \bigcup_{T \in \mathbb{W}} T = \emptyset
$$

which by De Morgan yields:

$$
\bigcap_{U \in \mathbb{V}} \bigcap_{T \in \mathbb{W}} U \setminus T = \emptyset
$$

Hence:

$$
\inf\{ \lambda(U \setminus T) \mid T \subset M \subset U,\ T \in \mathbb{W},\ U \in \mathbb{V} \} = 0
$$

and thus:

$$
\inf\{ \lambda(U) - \lambda(T) \mid T \subset M \subset U,\ T \in \mathbb{W},\ U \in \mathbb{V} \} = 0
$$

That gives:

$$
\inf\{ \lambda(U) \mid M \subset U,\ U \in \mathbb{V} \} = \sup\{ \lambda(T) \mid T \subset M,\ T \in \mathbb{W} \}
$$

Therefore:

$$
\kappa(M) = \nu(M)
$$

$\Box$

