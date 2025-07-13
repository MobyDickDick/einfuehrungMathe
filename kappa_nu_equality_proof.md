
**Title:** How to prove that inner and outer measure coincide for all subsets of $(0,1)$ using compact and open approximations?

----------

I am studying a variant of outer and inner measure, defined as follows for arbitrary subsets $M \subseteq (0,1)$, using only compact subsets and open supersets of $M$, all within $\mathbb{R}$:

----------

**1. Definitions**

Let $M \subseteq (0,1)$ be any subset.

We define the following:

-   The outer measure:  
    $\kappa(M) := \inf{ \lambda(U) \mid U \supseteq M \wedge U \text{ open in } [0,1] }$
    
-   The inner measure:  
    $\nu(M) := \sup{ \lambda(T) \mid T \subseteq M \wedge T \text{ compact in } [0,1] }$
    

Here, $\lambda$ is the standard length of open or compact subsets of $\mathbb{R}$, defined as:

-   For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$, we set:  
    $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$
    
-   For compact $T \subseteq (0,1)$, we set:  
    $\lambda(T) := 1 - \lambda((0,1) \setminus T)$ where $(0,1) \setminus T$ is open
    

----------

**2. Goals**

We aim to prove the following statements for all subsets $M \subseteq [0,1]$:

1.  Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$
    
2.  Equality of inner and outer measure: $\kappa(M) = \nu(M)$ and $\kappa([0,1] \setminus M) = \nu([0,1] \setminus M)$
    
3.  Strict additivity for disjoint sets: If $M_1, M_2 \subseteq [0,1]$ with $M_1 \cap M_2 = \emptyset$, then:  
    $\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$
    
4.  Generalization: $\kappa(M) = \sum_{z \in \mathbb{Z}} \kappa([z,z+1] \cap M)$ for arbitrary $M \subseteq \mathbb{R}$
    

----------

**3. Lemmas and Proofs**

**3.1 Lemma:** For open $U$ and closed $T$ subsets of $[0,1]$:  
$\lambda(U) = \nu(U) = \kappa(U)$, $\lambda(T) = \nu(T) = \kappa(T)$

_Proof:_ Open sets can be approximated from below by compact subsets; compact sets from above by open sets. The infimum and supremum of $\lambda$ coincide by definition.

**3.2 Lemma:** If $T \subseteq M \subseteq [0,1]$ and $T$ is compact, then  
$\kappa(M \setminus T) = \kappa(M) - \kappa(T)$

_Proof:_ $T$ is compact, hence measurable. The measure of $M$ splits into that of $T$ and the rest by disjoint additivity (proved later).

**3.3 Lemma:** $\kappa(M) = 0 \Leftrightarrow \nu(M) = 0$

_Proof:_ Immediate from $\nu(M) \leq \kappa(M)$. If $\nu(M) > 0$, then $\kappa(M) > 0$. Conversely, if $\kappa(M) = 0$, then any compact subset $T \subseteq M$ has $\lambda(T) = 0$, so $\nu(M) = 0$.

**3.4 Lemma:** If $M_1 \subseteq M_2 \wedge \kappa(M_2 \setminus M_1) = 0$, then $\kappa(M_1) = \kappa(M_2)$

_Proof:_ Follows from $\kappa(M_2) = \kappa(M_1) + \kappa(M_2 \setminus M_1)$ and $\kappa(M_2 \setminus M_1) = 0$.

**3.5 Lemma:**  If $(T_{k})_{k\in \mathbb N} T_k$ is a sequence of compact and pairwise disjoint sets with $T := \bigcup_{k\in \mathbb{N}}$, then $\kappa(T)= \sum_{k\in \mathbb{N }}\lambda(T_k)$  

----------

**4. Main Theorems**

**4.1 Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$**

Construct disjoint compact sets $T_k \subseteq M$ and $S_k \subseteq [0,1] \setminus M$ such that:  
$\sum \lambda(T_k) = \nu(M)$, $\sum \lambda(S_k) = \nu([0,1] \setminus M)$

For $\varepsilon > 0$, find open supersets $U_M, U_{[0,1]\setminus M}$ of these unions with total measure less than $1 - \Delta/2$, where $\Delta := 1 - \nu(M) - \nu([0,1] \setminus M)$. The uncovered remainder $R$ has $\lambda(R) > 0$.

This implies either $\kappa(M \cap R) > 0$ or $\kappa(([0,1] \setminus M) \cap R) > 0$, contradicting maximality of $\nu(M)$ or $\nu([0,1] \setminus M)$.

Hence: $\nu(M) + \nu([0,1] \setminus M) = 1$, and by same approximation via compact sets and open supersets:  
$\kappa(M) + \kappa([0,1] \setminus M) = 1$  
$\Box$

**4.2 Equality of $\nu(M)$ and $\kappa(M)$**

Since $\kappa(M) + \kappa([0,1] \setminus M) = 1$ and $\nu(M) + \nu([0,1] \setminus M) = 1$, and $\nu \leq \kappa$, it follows:  
$\kappa(M) = \nu(M)$, $\kappa([0,1] \setminus M) = \nu([0,1] \setminus M)$  
$\Box$

**4.3 Additivity:** If $M_1 \cap M_2 = \emptyset$, then  
$\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$

_Proof:_ Use identity:  
$[0,1] \setminus (M_1 \cup M_2) = ([0,1] \setminus M_1) \setminus M_2$

So:  
$\kappa([0,1] \setminus (M_1 \cup M_2)) = \kappa([0,1] \setminus M_1) - \kappa(M_2)$  
$\Rightarrow 1 - \kappa(M_1 \cup M_2) = 1 - \kappa(M_1) - \kappa(M_2)$  
$\Rightarrow \kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$  
$\Box$

**4.4 Generalization to $\mathbb{R}$**

For $M \subseteq \mathbb{R}$, define:  
$\kappa(M) := \sum_{z \in \mathbb{Z}} \kappa((M - z) \cap (0,1))$

This is well-defined (possibly infinite). All earlier properties remain valid per interval.  
$\Box$

----------

### My Question

Is this constructive proof approach sound and complete?  
Are there any overlooked details or logical gaps?  
Especially:

-   Does this argument work without invoking $\sigma$-algebras or Carath'eodory's extension?
    
-   Does the definition of $\nu(M)$ via compact subsets ensure $\kappa(M) = \nu(M)$ for all $M \subseteq [0,1]$?
    

Also: If there is a real chance that the argument might be correct, would anyone be willing to help verify these claims using **Lean** or another formal proof assistant?

Any feedback or comparison with known constructions would be greatly appreciated.

----------

**Tags**: `real-analysis`, `measure-theory`, `outer-measure`, `inner-measure`, `constructive-mathematics`
