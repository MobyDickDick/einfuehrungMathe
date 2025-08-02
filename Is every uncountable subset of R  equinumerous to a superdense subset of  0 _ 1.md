

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

|S \cap (a,b)| > \aleph_0,

$$

where $\aleph_0$ denotes the cardinality of the natural numbers.



---



**Answer (constructive embedding):**



Let $A \subseteq \mathbb{R}$ be an uncountable set, and define the bijection

$$

g(x) := \frac{1}{2} \cdot \left(1 + \frac{x}{\sqrt{x^2 + 1}} \right), \quad \psi: \mathbb{R} \to (0,1).

$$

This function is continuous, strictly increasing, and maps $\mathbb{R}$ bijectively onto $(0,1)$.



Define

$$

B := g(A) \subseteq (0,1),

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

Hence, $F$ is perfect and uncountable — thus $F \sim (0,1)$.



There must exist a continuous, increasing and surjective function $\Psi: F \to (0,1)$. One possible construction (sketched here) begins as follows:



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





Let $\Phi$ be a function derived from $\Psi$, modified (if necessary) to be injective everywhere, such that $\Phi(F') = (0,1)$, where $F' \subseteq F$ has at most countably many points less than $F$. Let also



$$

B' := B\cap F'

$$

As $F'\subset F$ and has at most a countable number of points less than F, then $B'$ has at most countable numbers of points less then $B$ and is therefore equnumerous to $B$ as well as to $A$.



Then

$$

S' := \Phi(B') \subseteq (0,1)

$$

is also equinumerous to $B$ and therefore also to $A$.



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
