


**Title:** How to prove that inner and outer measure coincide for all subsets of $(0,1)$ using compact and open approximations?

---

I am studying a variant of outer and inner measure, defined as follows for arbitrary subsets $M \subseteq (0,1)$, using only compact subsets and open supersets of $M$, all within $\mathbb{R}$:

---

**1. Definitions**

Let $M \subseteq (0,1)$ be any subset.
Let $\mathbb{V}$ be the set of all open supersets of $M$.
Let $\mathbb{W}$ be the set of all compact subsets of $M$.

We define the following:

- The outer measure:  
  $\kappa(M) := \inf\{ \lambda(U) \mid U \supseteq M \wedge U \in \mathbb{V}\}$

- The inner measure:  
  $\nu(M) := \sup\{ \lambda(T) \mid T \subseteq M \wedge T \in \mathbb{W}\}$

Here, $\lambda$ is the standard length of open or compact subsets of $\mathbb{R}$, defined as:

- For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$, we set:  
  $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$

- For compact $T \subseteq (0,1)$, we set:  
  $\lambda(T) := 1 - \lambda((0,1) \setminus T)$ where $(0,1) \setminus T$ is open

---

**2. Goals**

We aim to prove the following statements for all subsets $M \subseteq [0,1]$:

1. Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$
2. Equality of inner and outer measure: $\kappa(M) =\nu(M)$ and $\kappa([0,1] \setminus M) =\nu([0,1] \setminus M)$
3. Strict additivity for disjoint sets: If $M_1, M_2 \subseteq [0,1]$ with $M_1 \cap M_2 = \emptyset$, then:  
   $\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$
4. Generalization: $\kappa(M) = \sum_{z \in \mathbb{Z}} \kappa([z,z+1] \cap M)$ for arbitrary $M \subseteq \mathbb{R}$

---

**3. Lemmas and Proofs**

**3.1 Lemma:** For any open set $U \subseteq [0,1]$, and any compact set $T \subseteq [0,1]$:
$$\lambda(U) =\nu(U) = \kappa(U), \quad \lambda(T) =\nu(T) = \kappa(T)$$

**Proof:**

- *Case 1: Open set $U$.*  
  Since $U$ is open, it belongs to the collection used to define $\kappa(U)$:  
  $$\kappa(U) \leq \lambda(U) \leq \kappa(U) \Rightarrow \kappa(U) = \lambda(U)$$
  Similarly, $U$ can be approximated from inside by compact $K_n \subset U$ with $\lambda(K_n) \to \lambda(U)$:  
  $$u(U) = \lambda(U)$$  
  Hence:  
  $$\kappa(U) =\nu(U) = \lambda(U)$$

- *Case 2: Compact set $T$.*  
  Then $[0,1] \setminus T$ is open, and  
  $$\lambda(T) := 1 - \lambda([0,1] \setminus T)$$  
  Since open supersets $U \supseteq T$ exist with $\lambda(U) \to \lambda(T)$,  
  $$\kappa(T) = \lambda(T)$$  
  Also, since $T$ is compact and $T \subseteq M$:  
  $$u(T) = \lambda(T)$$  
  So:  
  $$\kappa(T) =\nu(T) = \lambda(T) \quad \blacksquare$$

---

**3.2 Lemma:** If $T \subseteq M \subseteq [0,1]$ and $T$ is compact, then  
$$\kappa(M \setminus T) = \kappa(M) - \kappa(T)$$

**Proof:**

Let $U \supseteq M$ be open. Then $U \setminus T$ is open and $M \setminus T \subseteq U \setminus T$:

$$\lambda(U) = \lambda(U \setminus T) + \lambda(U \cap T) \geq \lambda(U \setminus T) + \lambda(T)$$
$$\Rightarrow \lambda(U \setminus T) \leq \lambda(U) - \lambda(T)$$

Taking infimum over $U$:

$$\kappa(M \setminus T) \leq \kappa(M) - \lambda(T) = \kappa(M) - \kappa(T)$$

Conversely, let $V \supseteq M \setminus T$ be open. Then $V \cup T \supseteq M$, and

$$\kappa(M) \leq \lambda(V \cup T) \leq \lambda(V) + \lambda(T)$$
$$\Rightarrow \kappa(M) - \lambda(T) \leq \lambda(V)$$

Taking infimum over $V$:

$$\kappa(M) - \kappa(T) \leq \kappa(M \setminus T)$$

Hence:

$$\kappa(M \setminus T) = \kappa(M) - \kappa(T) \quad \blacksquare$$

---

**4. Main Theorems**

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

Then there exists a compact set $T_W \subset M \setminus T$ with $\lambda(T_W) > 0$.

Let $\varepsilon := \lambda(T_W)> 0$. Since $T_W$ is disjoint from all $T_k$, we can find some $j \in \mathbb{N}$ such that:

$$
\lambda(T_j) > \nu(M) - \varepsilon
$$

Then:

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

**4.3 Complementarity: $\kappa(M) + \kappa((0,1) \setminus M) = 1$**

*Proof:*  
As 

$\kappa(M)=\nu(M)$ and $\kappa((0,1)\setminus M)=\nu((0,1)\setminus M)$, for every $\varepsilon > 0$ there must be two compact subsets $T_{M} \subset M$ and $T_{(0,1)\setminus M} \subset (0,1)\setminus M$ with  
$\nu(M)-\varepsilon/2 < \lambda(T_{M}) \wedge  
\nu((0,1)\setminus M)-\varepsilon/2 < \lambda(T_{(0,1)\setminus M})$

Then  
$\nu(M)+ \nu((0,1)\setminus M) -\varepsilon < \lambda(T_{M})+\lambda(T_{(0,1)\setminus M}) < 1$  
or  
$\nu(M)+ \nu((0,1)\setminus M)< 1+ \varepsilon$  
With $\nu(M)=\kappa(M)$ and $\nu((0,1)\setminus M)=\kappa((0,1)\setminus M)$  
$\kappa(M)+ \kappa((0,1)\setminus M)< 1+ \varepsilon$  
Letting $\varepsilon \rightarrow 0$ gives $\kappa(M)+ \kappa((0,1)\setminus M) \leq 1$  
With $\kappa(M)+ \kappa((0,1)\setminus M) \geq 1$ this results in  
$\kappa(M)+ \kappa((0,1)\setminus M) = 1$

$\Box$

**4.4 Additivity:** If $M_1 \cap M_2 = \emptyset$, then  
$\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$

*Proof:*  
For every $\varepsilon > 0$ there must be two compact, disjoint subsets $T_1 \subset M_1$ and $T_2 \subset M_2$ with  
$\kappa(M_1)-\varepsilon/2 < \lambda(T_1) \wedge \kappa(M_2)-\varepsilon/2 < \lambda(T_2)$  
So  
$\kappa(M_1) + \kappa(M_2) < \lambda(T_1) +\lambda(T_2)+\varepsilon$  
As $T_1 \cup T_2 \subset M_1 \cup M_2$ we can state  
$\lambda(T_1\cup T_2) \leq \kappa(M_1 \cup M_2)$  
Therefore $\kappa(M_1) + \kappa(M_2) \leq \kappa(M_1 \cup M_2) +\varepsilon$ 

Letting $\varepsilon \rightarrow 0$ results to 

$\kappa(M_1) + \kappa(M_2) \leq \kappa(M_1 \cup M_2)$ 


With $\kappa(M_1 \cup M_2) \leq \kappa(M_1) + \kappa(M_2)$ the proof is complete.

$\Box$

**4.5 Generalization to $\mathbb{R}$**

For $M \subseteq \mathbb{R}$, define:  
$\kappa(M) := \sum_{z \in \mathbb{Z}} \kappa((M - z) \cap (0,1))$  
This is well-defined (possibly infinite). All earlier properties remain valid per interval.  

I suggest that the generalization to $\mathbb{C}^n$ (for any natural number $n$) can be easily established.

$\Box$

---

### My Question

Are these constructive proofs correct and logically sound? Especially:

- Do these arguments succeed without invoking $\sigma$-algebras or Carathéodory's extension?
- Is the identity $\kappa(M) =\nu(M)$ really forced by the mutual approximation structure?
- Could these be validated in a formal proof assistant like Lean?

Any insights, corrections or feedback are welcome!

---

**Tags**: `real-analysis`, `measure-theory`, `outer-measure`, `inner-measure`, `constructive-mathematics`, `formal-verification`
