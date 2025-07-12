**Title:** How to prove that inner and outer measure coincide for all subsets of \([0,1]\) using compact and open approximations?

---

I am studying a variant of outer and inner measure, defined as follows for arbitrary subsets $M \subseteq (0,1)$, using only compact subsets and open supersets of $M$, all within $\mathbb{R}$:

----------

**1. Definitions**

Let $M \subseteq (0,1)$ be any subset.

We define the following:

-   The outer measure:  
    $\kappa(M) := \inf \{ \lambda(U) \mid U \supseteq M \wedge U \text{ open in } [0,1] \}$
    
-   The inner measure:  
    $\nu(M) := \sup \{ \lambda(T) \mid T \subseteq M \wedge T \text{ compact in } [0,1] \}$
    

Here, $\lambda$ is the standard length of open or compact subsets of $\mathbb{R}$, defined as:

-   For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$, we set:  
    $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$
    
-   For compact $T \subseteq (0,1)$, we set:  
    $\lambda(T) := 1 - \lambda((0,1) \setminus T)$ where $(0,1) \setminus T$ is open
    

----------

**2. Goals**

We aim to prove the following three statements for all subsets $M \subseteq [0,1]$:

1. Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$

2. Equality of inner and outer measure: $\kappa(M) = \nu(M) \wedge  \kappa ([0,1]\setminus M) = \nu([0,1]\setminus M)$

3. Strict additivity for disjoint sets: If $M_1, M_2 \subseteq  [0,1]$ with $M_1 \cap M_2 = \emptyset$, then:  
$\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$

4. The generalization to arbitrary sets is reasonably possible with the  concept $\kappa(M) = \sum_{z\in \mathbb{Z}} \kappa([z,z+1]\cap M)$ for arbitrary set $\subset(M)$

----------

**3. Proof of Propositions:**

*3.1 $\kappa(M) + \kappa([0,1] \setminus M) = 1$*

For open (U) and closed subsets (T) of [0,1] the following equations hold:
$\lambda(U)=\nu(U)=\kappa(U)$ 
$\lambda(T)=\nu(T)=\kappa(T)$

If $T \subseteq M \subseteq [0,1]$ and $T$ is compact, then
$\kappa(M\setminus T) = \kappa(M) - \kappa(T)$


Assume, for contradiction:  
$Δ:=1−ν(M)-ν([0,1]∖M)>0$

and define:

$ϵ:=Δ/4$
Then we can find (by the definition of the suprema):

-   Compact $T_M \subseteq M$ with $\lambda(T_M) > \nu(M) - \varepsilon$
    
-   Compact $T_{[0,1] \setminus M} \subseteq [0,1] \setminus M$ with:  
    $\lambda(T_{[0,1] \setminus M}) > \nu([0,1] \setminus M) - \varepsilon$
    
    This implies
    $\kappa(M \setminus T_M) = \kappa(M) - \lambda(T_M) < \varepsilon$
    as well as 
    $\kappa(M) \leq  \kappa(T_M) +\kappa(M\setminus T_M)  < 
    \nu(T_M) + \varepsilon$
    
	$\kappa(M \setminus T_{[0,1]\setminus M}) = \kappa(M) - \lambda(T_{[0,1]\setminus M}) < \varepsilon$
	and also
	$\kappa([0,1]\setminus M) \leq  \kappa(T_{[0,1]\setminus M}) +\kappa(M\setminus T_{[0,1]\setminus M})  < \nu(T_{[0,1]\setminus M}) + \varepsilon$
    
	
Therefore, we have 

$\kappa([0,1]) = \kappa(M\cup[0,1]\setminus M) \leq \kappa(M) + \kappa([0,1]\setminus M) < \nu(M) + \nu([0,1]\setminus M) + 2\cdot \varepsilon =  \nu(M) + \nu([0,1]\setminus M) +\Delta / 2 <\nu(M) + \nu([0,1]\setminus M) +\Delta =  \nu(M) + \nu([0,1]\setminus M) + 1 - \nu(M) - \nu([0,1]\setminus M) = 1$

or $1 < 1$, which is clearly a contradiction to the fundamental fact $1 = 1$

Therefore, the equation $1 = \nu(M) + \nu([0,1]\setminus M)$ must hold for every set $M\subseteq [0,1]$

For all $T_M\in M$ and $T_{[0,1]\setminus M} \in [0,1]$ are disjoint sets, the equality

$\sup \{ \lambda(T_M) \mid T_M \subseteq M \wedge T_M \text{ compact in } \mathbb{R} \} +\sup \{ \lambda(T_{[0,1]\setminus M})) \mid T_{[0,1]\setminus M} \subseteq [0,1]\setminus M \wedge T_{[0,1]\setminus M} \text{ compact in } \mathbb{R} \} =
\sup \{ \lambda(T_M)+ \lambda(T_{[0,1]\setminus M})\mid T_M \subseteq M \wedge T_M \text{ compact in } \mathbb{R} \wedge T_{[0,1]\setminus M} \subseteq M \wedge T_{[0,1]\setminus M} \text{ compact in } \mathbb{R} \}$

is true.

So we can write:

$\sup \{ \lambda(T_M) \mid T_M \subseteq M \wedge T_M \text{ compact in } \mathbb{R} \} +\sup \{ \lambda(T_{[0,1]\setminus M})) \mid T_{[0,1]\setminus M} \subseteq [0,1]\setminus M \wedge T_{[0,1]\setminus M} \text{ compact in } \mathbb{R} \} =
\sup \{ \lambda(T_M)+ \lambda(T_{[0,1]\setminus M})\mid T_M \subseteq M \wedge T_M \text{ compact in } \mathbb{R} \wedge T_{[0,1]\setminus M} \subseteq M \wedge T_{[0,1]\setminus M} \text{ compact in } \mathbb{R} \}=
\sup \{ \lambda(T_M \cup T_{[0,1]\setminus M})\mid T_M \subseteq M \wedge T_M \text{ compact in } \mathbb{R} \wedge T_{[0,1]\setminus M} \subseteq M \wedge T_{[0,1]\setminus M} \text{ compact in } \mathbb{R} \} =1$


Therefore, for every $\varepsilon> 0$ there have to be two compact sets  $T_{M}\subseteq  M$ and $T_{[0,1]\setminus M}\subseteq T_{[0,1]\setminus M})$ with $\lambda(T_M\cup T_{[0,1]\setminus M}) > 1 -\varepsilon/2)$ 

Then both sets $(0,1)\setminus T_M$ and $(0,1)\setminus T_{[0,1]\setminus M}$ are open supersets of $(0,1)\M$ and $M$ with
$\kappa((0,1)\setminus M) + \kappa(M) < \varepsilon/2 + \varepsilon/2 = \varepsilon$. Letting $\varepsilon \rightarrow 0$ this results in 
$\kappa(M) + \kappa([0,1]\setminus M) = 1$ 
$\Box$

----------

*3.2. Equality of inner and outer measure: $\kappa(M) = \nu(M) \wedge  \kappa ([0,1]\setminus M) = \nu([0,1]\setminus M)$*
Since $\kappa(M)+\kappa([0,1]\setminus M) =1$

$\kappa([0,1]\setminus M) = 1 -\kappa(M) = 1 - \inf\{\lambda(U) \mid U \supset M\wedge U \text{is open}\} = \lambda([0,1])- \inf\{\lambda(U) \mid U \supset M\wedge U \text{is open}\}=
\sup\{[0,1]\setminus U \mid  U \supset M\wedge U \text{is open}\}=
\sup\{T \mid  T \subseteq [0,1]\setminus M\wedge U \text{is closed}\} =\nu([0,1]\setminus M)$

or 


$\kappa([0,1]\setminus M) = \nu([0,1]\setminus M)$

Therefore 

$\kappa(M) = 1-\kappa([0,1]\setminus M) =  1- \nu([0,1]\setminus M) =\nu(M)$

or 

$\nu(M) + \nu([0,1]\setminus M) = 1$

$\Box$

----------

*3.3 Additivity for Disjoint Sets*

Let $M_1, M_2 \subseteq [0,1]$ be disjoint: $M_1 \cap M_2 = \emptyset$.  

On the one side, we have:

$\kappa([0,1]\setminus (M_1 \cup M_2) )= 1 - \kappa(M_1 \cup M_2)$

On the other side, we have 

$[0,1]\setminus (M_1 \cup M_2)= ([0,1]\setminus M_1) \setminus M_2$

As M_1 and M_2 are disjoint sets.
This gives
$\kappa([0,1]\setminus (M_1 \cup M_2) ) = \kappa(([0,1]\setminus M_1) \setminus M_2) = \kappa( [0,1]\setminus M_1)) - \kappa(M_2) =1 - \kappa(M_1)) - \kappa(M_2)$

Therefore, we have $1 - \kappa(M_1 \cup M_2 )= 1- \kappa(M_1)) - \kappa(M_2)$
which resolves to $\kappa(M_1 \cup M_2 )= \kappa(M_1)) + \kappa(M_2)$

*3.3 Generalization*
For a given Set $M\subseteq \mathbb{R}$ and for every $z \in \mathbb{Z}$ the simple translation $(M - z)\cap(0,1)$ translates $M\cap(z,z+1)$ maps bijectively to $M-z\cap(0,1)$. 
So, the function $\kappa_z(M) := \kappa((M-z)\cap(0,1))$ gives a well-defined value. Therefore, it is possible to define $\kappa(M) := \sum_{k\in \mathbb{Z}} \kappa_z(M)$, even if the sum might diverge (i.e., be infinite) for unbounded sets.

---

### My Question

Is this constructive proof approach sound and complete?  
Are there any overlooked details or logical gaps?  
Especially:  
- Does this argument work without invoking σ-algebras or Carathéodory's extension?
- Does the definition of $\nu(M)$ via compact subsets ensure $\kappa(M) = \nu(M)$ for all $M \subseteq [0,1]$ as shown?

Any feedback or comparison with known constructions would be greatly appreciated.


---

**Tags**: `real-analysis`, `measure-theory`, `outer-measure`, `inner-measure`, `constructive-mathematics`
