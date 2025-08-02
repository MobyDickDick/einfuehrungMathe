
IWe define three functions $$\lambda, \nu, \kappa :  \mathcal{P}([0,1]) \rightarrow \mathbb{R}$$

> Are these functions internally consistent and equal for all $M⊆(0,1)$, based solely on the definitions provided?

**1. Definitions**

Let $M \subseteq [0,1]$. Define:

$\mathbb{V} := \{ U \subseteq [0,1] \mid U \text{ open},\ M \subseteq U \}$

$\mathbb{W} := \{ T \subseteq [0,1] \mid T \text{ compact},\ T \subseteq M \}$

Defining $\lambda$:
- For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$ and given
$$k, n\subset \mathbb{N} \wedge k\neq n \Rightarrow (a_k, b_k)\cap (a_n, b_n)=\emptyset$$let set:  
  $$\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$$

Defining $\kappa$ and $\nu$:

- $\kappa(M) := \inf\{ \lambda(U) \mid U \supseteq M \wedge U \in \mathbb{V}\}$

- $\nu(M) := \sup\{ \lambda(T) \mid T \subseteq M \wedge T \in \mathbb{W}\}$


---

**2. Goal**

Seeking to prove:
$$\forall M\in [0,1]: \kappa(M) =\nu(M) \wedge \kappa([0,1] \setminus M) =\nu([0,1] \setminus M)$$

---

**3. Lemma:** For any open set $U \subseteq [0,1]$, and any compact set $T \subseteq [0,1]$:
$$\lambda(U) =\nu(U) = \kappa(U), \quad \lambda(T) =\nu(T) = \kappa(T)$$

**Proof:**

- *Case 1: Open set $U$.*  
  Since $U$ is open, it belongs to the collection used to define $\kappa(U)$:  
  $$\kappa(U) \leq \lambda(U) \leq \kappa(U) \Rightarrow \kappa(U) = \lambda(U)$$
  Similarly, $U$ can be approximated from inside by compact $K_n \subset U$ with $\lambda(K_n) \to \lambda(U)$:  
  $$\nu(U) = \lambda(U)$$  
  Hence:  
  $$\kappa(U) =\nu(U) = \lambda(U)$$

- *Case 2: Compact set $T$.*  
  Then $[0,1] \setminus T$ is open, and  
  $$\lambda(T) := 1 - \lambda([0,1] \setminus T)$$  
  Moreover, $\nu(T) = \lambda(T)$ for compact sets.
But $$\lambda(T)$$ can get approximated directly as well. Since 
$$U := (0,1)\setminus T$$is open, It can get constructed with a series 
$$(I_k)_{k\in \mathbb{N}}$$of open intervals with falling lengths:
$$\sup(I_k) - \inf(I_k) > \sup(I_{k+1}) - \inf(I_{k+1})$$  for $k\in\mathbb{N}$ 
It is also possible that only for finite natural numbers  the Intervals I_k are non-empty. That is, it is possible for a given $j\in \mathbb{N}$ and for all $k \in \mathbb{N}$ with $k>j$ is $I_k = \emptyset$. The total length of $U_1$ can a get evaluated by $$\lambda(U_1)= \sum_{k\in \mathbb{N}} \lambda(I_k)$$

As $$T\cup U_1 = (0,1)$$ it follows that $$\lambda(T\cup U_1) = \lambda((0,1))= 1$$. For a given $\varepsilon > 0$ there must be a natural number $n\in \mathbb{N}$ with 
$$\sum_{k = 1}^n \lambda(I_k) >1- \lambda(T)-\varepsilon/2 $$
Then $$(0,1)\setminus\bigcup_{k=1}^n I_k$$ consists of at most {n+1} points and or Intervals. So  there must obviously be an open set $U_2 \supset T$ with 
	$$\lambda(U_2) < \lambda(T) +  \varepsilon$$
	and $$\lambda(T) +\varepsilon/2 < \lambda(U_2)<\lambda(T)+\epsilon$$
letting $\varepsilon \rightarrow 0$ gives $$\kappa(T)=\lambda(T)$$

---

**4. Proof**

**4.1 Classic contradiction using a compact remainder**

Let $\nu(M) = \sup\{ \lambda(T) \mid T \subset M,\ T \in \mathbb{W} \}$.
Then there exists an increasing sequence $\left(T_k\right)_{k \in \mathbb{N}}$ of compact sets with $T_k \subset T_{k+1}$ such that:

$$
\lim_{k \to \infty} \lambda(T_k) = \nu(M)
$$

Let $T := \bigcup_{k \in \mathbb{N}} T_k$. Suppose:

$$
\kappa(M \setminus T) > 0
$$

Then there would exist a compact set $T_W \subset M \setminus T$ with $\lambda(T_W) > 0$.

Let $\varepsilon := \lambda(T_W)> 0$. Since $T_W$ would be disjoint from all $T_k$, we could find some $j \in \mathbb{N}$ such that:

$$
\lambda(T_j) > \nu(M) - \varepsilon
$$

Then it would be:

$$
\lambda(T_j \cup T_W) = \lambda(T_j) + \lambda(T_W) > \nu(M)
$$

But $T_j \cup T_W$ is compact and contained in $M$, contradicting the definition of $\nu(M)$ as the supremum over compact subsets of $M$.

Hence:

$$
\kappa(M \setminus T) = 0
$$

Now use:

$$
\kappa(M) \leq \kappa(T) + \kappa(M \setminus T) = \kappa(T)
$$

And since $T = \bigcup_{k \in \mathbb{N}} T_k \subset M$, we also have:

$$
\kappa(T) \leq \kappa(M)
$$

Hence:

$$
\kappa(T) \leq \kappa(M) \leq \nu(T)
$$

Thus:

$$
\kappa(M) = \nu(M)
$$

$\Box$

**4.2 Second Proof: Abstract measure argument via mutual approximation**

Let $M \subset (0,1)$ be arbitrary, and let $\mathbb{V}$ be the collection of all open supersets of $M$, and $\mathbb{W}$ be the collection of all compact subsets of $M$. We aim to show:

$\nu(M) = \kappa(M)$

i.e.

$\sup\{ \lambda(T) \mid T \in \mathbb{W} \} = \inf\{ \lambda(U) \mid U \in \mathbb{V} \}$

For all $T \in \mathbb{W}$ and $U \in \mathbb{V}$, the set difference $U \setminus T$ is open (since $T$ is compact and $U$ is open). Moreover, since $T \subset M \subset U$, we have:

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

---

### My Question

Are my arguments correct, and do they sound logical? Especially:

- Do these arguments succeed without invoking $\sigma$-algebras or Carathéodory's extension?
- Is the identity $\kappa(M) =\nu(M)$ really forced by the mutual approximation structure?
- Could these be validated in a formal proof assistant like Lean?

Any insights, corrections or feedback are welcome!

