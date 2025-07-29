
Title: Is every subset of ℝ equinumerous to a superdense subset of (0,1)?

**Question:**  
Let us define a subset $S \subseteq (0,1)]$ to be *superdense* if it is uncountable and intersects every non-empty open subinterval $(a,b) \subseteq [0,1]$ with $a,b\in (0,1) \wedge a <b$ in uncountably many points.

> **Claim:** Every subset $A \subseteq \mathbb{R}$ is equinumerous to a *superdense* subset of \([0,1]\).

This seems intuitively plausible:
- Since $\mathbb{R} \sim (0,1)$, and every $A \subseteq \mathbb{R}$ has cardinality $\leq \mathfrak{c}$,
- one can inject $A$ into \([0,1]\),
- and potentially "spread out" the image of $A$ across many open intervals.

However:
- I have not seen this exact statement discussed in standard textbooks.
- Is this claim known or even trivial in descriptive set theory or topology?
- Does the image set $f(A) \subseteq [0,1]$ always admit a transformation into a *superdense* set (in the above sense), even if $A$ is strange (e.g. a Vitali set or Bernstein set)?
- Are there canonical examples for such embeddings?

---

**Definitions (for clarity):**  
Let's say a set $S \subseteq (0,1)$ is *superdense* if for every interval $(a,b) \subseteq [0,1]$ we have  

$$
|S \cap (a,b)| > \aleph_0.
$$
with $\aleph_0$ as the the cardinality of the natural numbers.

---

**Answer (constructive embedding):**  

Let A bet a uncoutable subset of $\mathbb{R}$ and  $\psi: \mathbb{R} \to (0,1)$ be the bijection
$$
\psi(x) := \frac{1}{2} \cdot \left(1 +  \frac{x}{\sqrt {x^2+1}}\right)
$$
This function is continuous, strictly increasing, and maps $\mathbb{R}$ bijectively onto $(0,1)$.

Now define
$$
B := \psi(A) \subseteq (0,1).
$$

Which must have the same cardinality as $A$
Let $(0,1)$ divide up into two different disjunct subsets of $(0,1)$ named $L$ (as "lean") and $F$ (as "fat"). For every point $x$ in $L$ it is true that there is an open Interval $I_x$ with the property 

$$
|I \cap B)| \leq  \aleph_0  \wedge \{\inf I, \sup I \}\subset \mathbb{Q}
$$

Define simply 
$$F := (0,1)\setminus L$$

Then $L$ must be an open set and therefore $F$ must be a closed set.
As there is only a countable number of such intervals $I$,  it must be true that 
$$
		|L| \leq \aleph_0
$$
Therefore, it can be concluded that
$$
		|F| > \aleph_0
$$
And it must be
 $$\left|F\right|=|A|$$ 

By construction, every single point $x\in F$ has to be a limit point. So $F$ is a perfect set and therefore bijective to (0,1). There must exist monotone and continuous function with maps $F$ subjectively to (0,1).

Perhaps the function $\Psi$ could start with
$$ 
  x_0 := \sup F \cap  \left( \inf F, \frac{\inf F + \sup F} {2}\right)
$$

As $F$ is a closed set and nonempty, this suprema must exist. Then let set

$$
\Psi(x_0):= \frac{1}{2}
$$

Moreover, by construction it must be true that. 

$$ 
   \left|F\cap \left( \inf F, \frac{\inf F + \sup F} {2}\right)\right| > \aleph_0
$$
as well as 
$$ 
\left|F\cap \left(\frac{\inf F + \sup F} {2}, \sup F\right)\right| > \aleph_0
$$

Therefore, the whole process can be started again. For every $n\in \mathbb{N}$ can be established points $x,y \in B$ with $x\neq y$ and
$$ 
\left|\Psi(x)-\Psi(y)\right| \leq 2^{-n}
$$
And by construction, this function has to be continuous and because the $F$ is closed, the image $\Psi\left( A\right)$ must also be closed. Therefore it can be concluded that 
$$
\Psi\left(F\right)=\left(0,1\right)
$$


--

Let  $S:=\Psi(F)$ and $(a,b) \subseteq (0,1)$ with $a<b$ be an arbitrary open interval. $S$ must be equonomerous to $F$ because only a countable number of poi
Title: Is every subset of ℝ equinumerous to a superdense subset of (0,1)?

**Question:**  
Let us define a subset $S \subseteq (0,1)$ to be *superdense* if it is uncountable and intersects every non-empty open subinterval $(a,b) \subseteq [0,1]$ with $a,b \in (0,1),\; a < b$ in uncountably many points.

> **Claim:** Every subset $A \subseteq \mathbb{R}$ is equinumerous to a *superdense* subset of $[0,1]$.

This seems intuitively plausible:
- Since $\mathbb{R} \sim (0,1)$, and every $A \subseteq \mathbb{R}$ has cardinality $\leq \mathfrak{c}$,
- one can inject $A$ into $[0,1]$,
- and potentially "spread out" the image of $A$ across many open intervals.

However:
- I have not seen this exact statement discussed in standard textbooks.
- Is this claim known or even trivial in descriptive set theory or topology?
- Does the image set $f(A) \subseteq [0,1]$ always admit a transformation into a *superdense* set (in the above sense), even if $A$ is strange (e.g., a Vitali set or a Bernstein set)?
- Are there canonical examples of such embeddings?

---

**Definitions (for clarity):**  
We say a set $S \subseteq (0,1)$ is *superdense* if for every interval $(a,b) \subseteq [0,1]$, we have
$$
|S \cap (a,b)| > \aleph_0
$$
where $\aleph_0$ denotes the cardinality of the natural numbers.

---

**Answer (constructive embedding):**

Let $A \subseteq \mathbb{R}$ be an uncountable set, and define the bijection
$$
\psi(x) := \frac{1}{2} \cdot \left(1 + \frac{x}{\sqrt{x^2 + 1}} \right), \quad \psi: \mathbb{R} \to (0,1).
$$
This function is continuous, strictly increasing, and maps $\mathbb{R}$ bijectively onto $(0,1)$.

Define
$$
B := \psi(A) \subseteq (0,1),
$$
which clearly has the same cardinality as $A$.

Now divide $(0,1)$ into two disjoint subsets: a "lean" part $L$ and a "fat" part $F$, defined as follows.  
Let $x \in (0,1)$ be in $L$ if there exists a rational open interval $I_x \ni x$ such that
$$
|I_x \cap B| \leq \aleph_0 \quad \text{and} \quad \inf I_x, \sup I_x \in \mathbb{Q}.
$$
Then define
$$
F := (0,1) \setminus L.
$$

Since only countably many such rational intervals exist, the set $L$ is a countable union of open intervals and hence open, while $F$ is closed. Moreover, since at most countably many $x \in (0,1)$ satisfy the above condition, we have
$$
|L| \leq \aleph_0 \quad \text{and thus} \quad |F| > \aleph_0.
$$
So $|F| = |A|$, and by construction, each $x \in F$ is a limit point of $B$. Hence, $F$ is perfect and uncountable — thus $F \sim (0,1)$.

There must exist a continuous, strictly increasing, surjective function $\Psi: F \to (0,1)$. One possible construction (sketched here) begins as follows:

Let
$$
x_0 := \sup \left( F \cap \left( \inf F,\; \frac{\inf F + \sup F}{2} \right) \right),
$$
which exists since $F$ is closed and nonempty. Define
$$
\Psi(x_0) := \frac{1}{2}.
$$

By symmetry of the interval and uncountability of $F \cap \left(\inf F,\; \tfrac{\inf F + \sup F}{2}\right)$, the construction can proceed recursively to define $\Psi$ on all of $F$, ensuring that for every $n \in \mathbb{N}$, there exist distinct $x,y \in F$ with
$$
|\Psi(x) - \Psi(y)| \leq 2^{-n}.
$$

The function $\Psi$ constructed this way is continuous, increasing, and surjective onto $(0,1)$. Since $F$ is closed, $\Psi(F) = (0,1)$.

Let $S := \Psi(B) \subseteq (0,1)$. Then $S \sim B \sim A$. 

Let $\Phi$ be a function derived from $\Psi$, modified (if necessary) to be injective everywhere but still $\Phi(F')=(0,1)$ with the new set $F'$ is a subset of $F$ and has at most a countable number of points less than $F$.
Then
$$
S' := \Phi(F') \subseteq (0,1)
$$
is also equinumerous to $A$.

Now, take any open interval $(a,b) \subseteq (0,1)$. Since $\Phi$ is strictly increasing and continuous, its inverse maps open intervals to open intervals. Therefore,
$$
F' \cap \Phi^{-1}((a,b))
$$
is uncountable, and
$$
S' \cap (a,b) = \Phi\left(F' \cap \Phi^{-1}((a,b))\right)
$$
is uncountable as well.

Thus, $S' \subseteq (0,1) \subseteq [0,1]$ is superdense and equinumerous to $A$.

∎

---

**Tags:**  
cardinality, real-analysis, general-topology, uncountable-sets, set-theory
nt $x,y \in F$ can have the same image value under  the function$\Psi$. Let denote $\Phi$ the function with the property that $Phi(x)$ for all but at most countable number of  points in $F$ and $\Phi$ is bijective. Therefore, the new original set $F'$ is equonumerous to $F$ and therefore to $A$ and $S':= \Phi(F')$ is also equonumerous to $A$.
Since $\Phi$ is continuous and strictly increasing, the preimage $\Phi^{-1}((a,b)) \subseteq \mathbb{R}$ is also an open interval.
$$
F' \cap \Phi^{-1}((a,b))
$$
is uncountable. Because $F'$ is uncountable and if $(a,b) \cap \Phi^{-1}((a,b))$ would be empty, by construction of $\Phi$ it would be
$$
\Phi\left(a\right) = \Phi\left(b\right) 
$$
which would be a contraction to the construction of $\Phi$. But as there exists at least one single point $x\in F' \cap \Phi^{-1}((a,b))$, this means that 
$$
\left|F'\cap\Phi^{-1}((a,b))\right| > \aleph_0
$$

Then
$$
S' \cap (a,b) = \Phi(F \cap \Phi^{-1}((a,b)))
$$
is uncountable as well.

Thus, $S' \subseteq (0,1) \subseteq [0,1]$ is superdense and equinumerous to $A$.

∎

---

**Tags:**  
cardinality, real-analysis, general-topology, uncountable-sets, set-theory
