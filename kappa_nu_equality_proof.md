
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
    $\lambda(T) :=\{ 1 - \lambda((0,1) \setminus T)\}$ where $(0,1) \setminus T$ is open
    

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

*3.0.0 Lemma: Mesures of open and closed sets*

For open ($U$) and closed subsets ($T$) of $[0,1]$ the following equations hold:  
$\lambda(U)=\nu(U)=\kappa(U)$  
$\lambda(T)=\nu(T)=\kappa(T)$

(Proof later or easy)

*3.0.1 Lemma: Measures of a difference set with compact subtrahend*

If $T \subseteq M \subseteq [0,1]$ and $T$ is compact, then  
$\kappa(M\setminus T) = \kappa(M) - \kappa(T)$

(Proof later or easy)

*3.0.2 Lemma: Measures of masses with zero measures*

$\kappa(M) = 0 \Leftrightarrow \nu(M)=0$ 

because 

$\nu(M) >0 \Rightarrow \kappa(M) \geq \nu(M)>0$

and 

$\kappa(M) = 0 \Rightarrow 0 \leq \nu(M) \leq \kappa(M) \Rightarrow \nu(M)= 0$

*3.0.3 Lemma: Measure of a set intersected with an open set*

$M \subseteq (0,1)\wedge U \subset (0,1) \Rightarrow \\ \mu(M) = \kappa(M\setminus U) + \kappa(M\cap U)$

(Proof later or easy)

*3.0.4 Lemma: Equal measures when difference set with subset is equal*

$M_1 \subseteq M_2 \wedge \kappa(M_2\setminus M_1)=0 \Rightarrow \kappa(M_1)=\kappa(M_2)$

(Proof later)


*3.0.5 Lemma: Exhausting the inner Mass of a set*

Let $M \subset [0,1]$. Then there exists of sequence  $(T_{k})_{k\in  \mathbb{N}}$ of compact subsets with  

*Proof:*

Is $\nu(M) =0$ then $(\emptyset)_{k\in \mathbb{N}}$ is the searched sequence.

So let $\nu(M)>0$

By definition of suprema there must be at least a compact subset $T_1$ of M with 

$\lambda(T_1) \geq \nu(M)/2$ 

as well as 

$\nu(M\setminus T_1) = \nu(M) -\nu(T_1) \leq \nu(M)/2$

And with for given $k\in \mathbb{N}$, assuming that

$\nu(M\setminus \bigcup_{j\in \mathbb{N}\wedge j\leq k}T_k) = \nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k} \nu(T_M)  \leq \nu(M)/2^k$ 

there must exist a compact set

$T_{k+1}\subseteq M$

with 

$\nu(T_{k+1}\cap \bigcup_{j\in \mathbb{N}\wedge j < k} T_j) =0$

and

$\lambda(T_{k+1}) \geq (\nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k} \nu(T_k))/2$ 

($T_{k+1}$ can be the empty set if the difference is already zero).

Then

-$\lambda(T_{k+1}) \leq - (\nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k} \nu(T_k))/2$ 
 
So 

$\nu(M\setminus \bigcup_{j\in \mathbb{N}\wedge j\leq k+1}T_k) = \\ \nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k}\nu(T_k) - \lambda(T_{k+1})  \leq \\ \nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k}\nu(T_k)  - (\nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k} \nu(T_M))/2 = \\(\nu(M) -\sum_{j\in \mathbb{N} \wedge j\leq k} \nu(T_M))/2 \leq \\ \nu(M)/2^{k+}$ 

As $k\rightarrow \infty$
 
 $\nu(M\setminus \bigcup_{j\in \mathbb{N}\wedge j\leq k+1}T_k) \rightarrow 0$
  
 Therefore
 
 $\nu(M\setminus \bigcup_{k\in \mathbb{N}}T_k) = 0$
  
and due to Lemma

_3.1 $\kappa(M) + \kappa([0,1] \setminus M) = 1$_

Assume, for contradiction:  

$\Delta:=1-\nu(M)-\nu([0,1]\setminus M)>0$

There must exist two sequences 

$(T_{M\,,k})_{k\in \mathbb(N)}$ 

and 

$(T_{[0,1]\setminus M,\;k})_{k\in \mathbb(N)}$ 

with disjoint and compact subsets of $M$ and $[0,1]\setminus M$ and
 
$\sum_{k\in\mathbb{N}}\lambda(T_{M\,k}) = \nu(M)\wedge \sum_{k\in\mathbb{N}}\lambda(T_{[0,1]\setminus M\,k}) =\nu([0,1]\setminus M)$

For $\epsilon > 0$ with $\epsilon < \Delta/4$ create open sets  $U_M$ and $U_{[0,1]\setminus M}$ of

$\bigcup_{k\in \mathbb{N} }T_{M\,,k}$ 

and 

$\bigcup_{k\in \mathbb{N} }T_{[0,1[\,,k}$ 

with 

$\lambda(U_M) <\lambda(\bigcup_{k\in \mathbb{N} }T_{M\,,k}) + \epsilon = \nu(M) + \epsilon$

and
$\lambda(U_{[0,1]\setminus M}) <\lambda(\bigcup_{k\in \mathbb{N} }T_{[0,1]\setminus M\,,k}) + \epsilon = \nu([0,1]\setminus M)+\epsilon$

Now we have the situation that $\lambda([0,1]\setminus(U_M\cup  U_{[0,1]\setminus M}) =1- \lambda(U_M) -\lambda(U_[0,1]\setminus M) =1-  \nu(M) -\nu([0,1]\setminus M) - 2\cdot \epsilon =\Delta - 2\cdot \epsilon =$

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
