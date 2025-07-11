
**Title: Proof Outline: Equality of** $\kappa(M)$ **and** $\nu(M)$ **for All Subsets** $M \subseteq [0,1]$

----------

**1. Definitions**

Let $M \subseteq [0,1]$ be any subset. We define the following:

-   The outer measure:  
    $\kappa(M) := \inf \{ \lambda(U) \mid U \supseteq M \wedge U \text{ open in } \mathbb{R} \}$
    
-   The inner measure:  
    $\nu(M) := \sup { 1 - \lambda((0,1) \setminus T) \mid T \subseteq M \wedge T \text{ compact in } \mathbb{R} }$
    

Here, $\lambda$ is the standard length of open or compact subsets of $\mathbb{R}$, defined as:

-   For open $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$, we set:  
    $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$
    
-   For compact $T \subset (0,1)$, we set:  
    $\lambda(T) := 1 - \lambda((0,1) \setminus T)$ where $(0,1) \setminus T$ is open
    

----------

**2. Goals**

We aim to prove the following three statements for all subsets $M \subseteq [0,1]$:

(a) $\kappa(M) = \nu(M) \wedge \kappa([0,1]\M) = \nu([0,1]\M)$

(b) $\kappa(M) + \kappa([0,1] \setminus M) = 1$

(c) Strict additivity for disjoint sets: If $M_1, M_2 \subseteq \mathbb{R}$ with $M_1 \cap M_2 = \emptyset$, then:  
$\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$

----------

**3. Proof of Equality: $\kappa(M) = \nu(M)$**

For open (U) and closed subsets (T) of [0,1] the following equations hold:
$\lambda(U)=\nu(U)=\kappa(U)$ as well as
$\lambda(T)=\nu(T)=\kappa(T)$

Assume, for contradiction:  
$\nu(M) < \kappa(M) \wedge \nu([0,1] \setminus M) < \kappa([0,1] \setminus M)$

Let:

$Δ:=(κ(M)−ν(M))+(κ([0,1]∖M)−ν([0,1]∖M))>0$

and define:

$ϵ:=Δ/4$
Then we can find:

-   Compact $T_M \subset M$ with $\lambda(T_M) > \nu(M) - \epsilon$
    
-   Compact $T_{[0,1] \setminus M} \subset [0,1] \setminus M$ with:  
    $\lambda(T_{[0,1] \setminus M}) > \nu([0,1] \setminus M) - \epsilon$
    

Now choose open sets:

-   $U_M \supseteq T_M$ with $\lambda(U_M) < \lambda(T_M) + \epsilon$
    
-   $U_{[0,1] \setminus M} \supseteq T_{[0,1] \setminus M}$ with $\lambda(U_{[0,1] \setminus M}) < \lambda(T_{[0,1] \setminus M}) + \epsilon$
    

Define:  
$U := U_M \cup U_{[0,1] \setminus M} \quad \text{(open)}$  
Then:  
$\lambda(U) < \nu(M) + \nu([0,1] \setminus M) + 4\epsilon = \kappa(M) + \kappa([0,1] \setminus M) - 2\Delta + 4\epsilon$  
Since $\epsilon = \Delta/4$, this becomes:  
$\lambda(U) < 1 - \Delta <1$

Then the complement $T := [0,1] \setminus U$ satisfies $\kappa(T) > 0$ but:  
$\kappa(T \cap M) = 0 \wedge \kappa(T \setminus M) = 0 \Rightarrow \kappa(T) =\kappa(T\cap (M\cup([0,1]\setminus M))\leq \kappa(T\cap M) + kappa(T\cap M) + \kappa(T \setminus M) \leq 0+ 0 = 0$
Which is a contradiction.
Hence:

$(\nu (M)=ν(M))\vee(\nu ([0,1]\setminus M)=ν([0,1]\setminus M))$

Assuming $\nu (M)=\kappa(M)$ then the same argumentation gives
$\nu([0,1]\setminus M) = \kappa([0,1] \setminus M)$

Assuming $\nu ([0,1]\setminus M)=\kappa([0,1]\setminus M)$

Then you can swap $M$ and $[0,1]\setminus M$ and this yields the corresponding conclusion $\nu(M)=\kappa(M)$

$\Box$

----------

**4. Complementarity: $\kappa(M) + \kappa([0,1] \setminus M) = 1$**

Let $M \subseteq [0,1]$. Let $T \subseteq M$ compact with $\lambda(T) > \kappa(M) - \epsilon$ and let $U \supseteq M$ open with $\lambda(U) < \kappa(M) + \epsilon$.

Then the set $[0,1] \setminus T$ is open and contains $[0,1] \setminus M$, so:  
$\kappa([0,1] \setminus M) \leq \lambda([0,1] \setminus T) = 1 - \lambda(T) < 1 - (\kappa(M) - \epsilon) = 1 - \kappa(M) + \epsilon$

Letting $\epsilon \to 0$, we obtain:  
$\kappa([0,1] \setminus M) \leq 1 - \kappa(M)$

Similarly, from the open set $U \supseteq M$, the set $[0,1] \setminus U$ is compact and contained in $[0,1] \setminus M$, so:  
$\nu([0,1] \setminus M) \geq \lambda([0,1] \setminus U) = 1 - \lambda(U) > 1 - (\kappa(M) + \epsilon) = 1 - \kappa(M) - \epsilon$

Letting $\epsilon \to 0$, we obtain:  
$\kappa([0,1] \setminus M) \geq 1 - \kappa(M)$  
Hence:  
$\kappa(M) + \kappa([0,1] \setminus M) = 1 \quad \Box$

----------

**5. Additivity for Disjoint Sets**

Let $M_1, M_2 \subseteq \mathbb{R}$ be disjoint: $M_1 \cap M_2 = \emptyset$.  
Let $U_1 \supseteq M_1$, $U_2 \supseteq M_2$ be open with:  
$\lambda(U_1) < \kappa(M_1) + \epsilon/2, \quad \lambda(U_2) < \kappa(M_2) + \epsilon/2$

Then $U_1 \cup U_2 \supseteq M_1 \cup M_2$ is open and:  
$\kappa(M_1 \cup M_2) \leq \lambda(U_1 \cup U_2) \leq \lambda(U_1) + \lambda(U_2) < \kappa(M_1) + \kappa(M_2) + \epsilon$  
Letting $\epsilon \to 0$, we obtain:  
$\kappa(M_1 \cup M_2) \leq \kappa(M_1) + \kappa(M_2)$

Conversely, for compact sets $T_1 \subseteq M_1$, $T_2 \subseteq M_2$:  
$\nu(M_1 \cup M_2) \geq \lambda(T_1 \cup T_2) = \lambda(T_1) + \lambda(T_2)$  
Letting the suprema run over $T_1, T_2$, we obtain:  
$\nu(M_1 \cup M_2) \geq \nu(M_1) + \nu(M_2)$  
Since $\kappa = \nu$, this yields:  
$\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2) \quad \Box$
