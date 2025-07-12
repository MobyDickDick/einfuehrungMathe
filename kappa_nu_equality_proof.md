
**Title:** How to prove that inner and outer measure coincide for all subsets of [0,1][0,1] using compact and open approximations?

----------

I am studying a variant of outer and inner measure, defined as follows for arbitrary subsets $M \subseteq (0,1)$, using only compact subsets and open supersets of $M$, all within $\mathbb{R}$:

----------

**1. Definitions**

Let $M \subseteq (0,1)$ be any subset.

We define the following:

-   The outer measure:  
    $\kappa(M) := \inf { \lambda(U) \mid U \supseteq M \wedge U \text{ open in } [0,1] }$
    
-   The inner measure:  
    $\nu(M) := \sup { \lambda(T) \mid T \subseteq M \wedge T \text{ compact in } [0,1] }$
    

Here, $\lambda$ is the standard length of open or compact subsets of $\mathbb{R}$, defined as:

-   For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$, we set:  
    $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$
    
-   For compact $T \subseteq (0,1)$, we set:  
    $\lambda(T) := 1 - \lambda((0,1) \setminus T)$ where $(0,1) \setminus T$ is open
    

----------

**2. Goals**

We aim to prove the following three statements for all subsets $M \subseteq [0,1]$:

1.  Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$
    
2.  Equality of inner and outer measure: $\kappa(M) = \nu(M) \wedge \kappa ([0,1]\setminus M) = \nu([0,1]\setminus M)$
    
3.  Strict additivity for disjoint sets: If $M_1, M_2 \subseteq [0,1]$ with $M_1 \cap M_2 = \emptyset$, then:  
    $\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$
    
4.  The generalization to arbitrary sets is reasonably possible with the concept $\kappa(M) = \sum_{z\in \mathbb{Z}} \kappa([z,z+1]\cap M)$ for arbitrary $M \subseteq \mathbb{R}$
    

----------

**3. Proof of Propositions:**

_3.1 $\kappa(M) + \kappa([0,1] \setminus M) = 1$_

For open ($U$) and closed subsets ($T$) of $[0,1]$ the following equations hold:  
$\lambda(U)=\nu(U)=\kappa(U)$  
$\lambda(T)=\nu(T)=\kappa(T)$

If $T \subseteq M \subseteq [0,1]$ and $T$ is compact, then  
$\kappa(M\setminus T) = \kappa(M) - \kappa(T)$

Assume, for contradiction:  
$\Delta:=1-\nu(M)-\nu([0,1]\setminus M)>0$

define:  
$\varepsilon:=\Delta/4$

Then we can find (by the definition of the suprema):

-   Compact $T_M \subseteq M$ with $\lambda(T_M) > \nu(M) - \varepsilon$
    
-   Compact $T_{[0,1] \setminus M} \subseteq [0,1] \setminus M$ with:  
    $\lambda(T_{[0,1] \setminus M}) > \nu([0,1] \setminus M) - \varepsilon$
    

This implies:  
$\nu(M \setminus T_M) = \nu(M) - \lambda(T_M) < \varepsilon \Rightarrow - \lambda(T_M) < \varepsilon - \nu(M)$   
as well as  
$\kappa(M\setminus T_M) = \kappa(M) - \kappa(T_M]) =\kappa(M) - \nu(T_M)= \kappa(M)- \nu(M)+ \varepsilon$

Similarly:  
$\nu(([0,1]\setminus M) \setminus T_{[0,1]\setminus M}) = \nu([0,1]\setminus M) - \lambda(T_[0,1]\setminus M) < \varepsilon \Rightarrow - \lambda(T_{[0,1]\setminus M}) < \varepsilon - \nu([0,1]\setminus M)$   
and also  
$\kappa([0,1]\setminus M\setminus T_{[0,1]\setminus }) = \kappa([0,1]\setminus M) - \kappa(T_{[0,1]\setminus M }) =\kappa([0,1]\setminus M) - \nu(T_{[0,1]\setminus M })= \kappa([0,1]\setminus M)- \nu([0,1]\setminus M)+ \varepsilon$

Therefore:  
$\kappa([0,1]) = \kappa(M \cup ([0,1] \setminus M)) \leq \kappa(M) + \kappa([0,1] \setminus M) < \nu(M) + \nu([0,1] \setminus M) + 2\varepsilon = 1 - \Delta + 2\varepsilon$

But since $\varepsilon = \Delta / 4$, this leads to a contradiction:  
$1 < 1$, which is impossible.

Therefore, $1 = \nu(M) + \nu([0,1] \setminus M)$ must hold for all $M \subseteq [0,1]$.

Now:  
$\sup { \lambda(T_M) + \lambda(T_{[0,1] \setminus M}) \mid T_M \subseteq M, T_{[0,1] \setminus M} \subseteq [0,1]\setminus M, \text{both compact} } = 1$

So for every $\varepsilon > 0$, there exist compact sets $T_M \subset M$ and $T_{[0,1] \setminus M} \subset [0,1] \setminus M$ such that  
$\lambda(T_M \cup T_{[0,1] \setminus M}) > 1 - \varepsilon$

Then both $(0,1)\setminus T_M$ and $(0,1)\setminus T_{[0,1]\setminus M}$ are open supersets of $(0,1)\setminus M$ and $M$, respectively, so:  
$\kappa(M) + \kappa([0,1] \setminus M) < \varepsilon$  
Letting $\varepsilon \to 0$ yields the desired result:

$\kappa(M) + \kappa([0,1]\setminus M) = 1$  
$\Box$

----------

_3.2. Equality of inner and outer measure: $\kappa(M) = \nu(M) \wedge \kappa ([0,1]\setminus M) = \nu([0,1]\setminus M)$_

Since $\kappa(M)+\kappa([0,1]\setminus M) =1$:

$\kappa([0,1]\setminus M) = 1 -\kappa(M) = \nu([0,1]\setminus M)$  
$\Rightarrow \kappa(M) = 1 - \nu([0,1]\setminus M) = \nu(M)$  
$\Box$

----------

_3.3 Additivity for Disjoint Sets_

Let $M_1, M_2 \subseteq [0,1]$ be disjoint: $M_1 \cap M_2 = \emptyset$.

Then:  
$\kappa([0,1] \setminus (M_1 \cup M_2)) = \kappa(([0,1] \setminus M_1) \setminus M_2) = \kappa([0,1] \setminus M_1) - \kappa(M_2)$

So:  
$1 - \kappa(M_1 \cup M_2) = 1 - \kappa(M_1) - \kappa(M_2)$  
$\Rightarrow \kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$  
$\Box$

----------

_3.4 Generalization_

For a given set $M \subseteq \mathbb{R}$ and every $z \in \mathbb{Z}$, the translation $(M - z) \cap (0,1)$ maps $M \cap (z, z+1)$ bijectively to $(M - z) \cap (0,1)$.

Define:  
$\kappa_z(M) := \kappa((M - z) \cap (0,1))$

Then $\kappa(M) := \sum_{z \in \mathbb{Z}} \kappa_z(M)$ is well-defined, though possibly divergent for unbounded sets.

----------

### My Question

Is this constructive proof approach sound and complete?  
Are there any overlooked details or logical gaps?  
Especially:

-   Does this argument work without invoking $\sigma$-algebras or Carath'eodory's extension?
    
-   Does the definition of $\nu(M)$ via compact subsets ensure $\kappa(M) = \nu(M)$ for all $M \subseteq [0,1]$ as shown?
    

Also: if there's a real chance that the argument might be correct, would anyone be willing to help me verify these claims using Lean or another formal proof assistant?

Any feedback or comparison with known constructions would be greatly appreciated.

----------

**Tags**: `real-analysis`, `measure-theory`, `outer-measure`, `inner-measure`, `constructive-mathematics`
