
## Lemma: A Superdense Null Set Contains at Most Countably Many Disjoint Compact Subsets with Multiple Accumulation Points

**Lemma.**  
Let $M \subset (0,1)$ be a superdense set of outer measure zero.  
Then there exist at most countably many pairwise disjoint compact subsets $K_n \subset M$ such that each $K_n$ contains at least two accumulation points.

---

**Proof.**  
We construct such compact sets recursively, using the structure of the interval $(0,1)$.  
Since $M$ is superdense, every nonempty open subinterval of $(0,1)$ contains uncountably many points of $M$.  
We also assume $\kappa(M) = 0$.

---

**Step 1: Find initial $K_1$**  
Because $M$ is superdense and of outer measure zero, there exists a compact subset
$$
K_1 \subset M
$$
with at least two distinct accumulation points:
- $k_{1,1} \in (1/5,\; 2/5)$,
- $k_{1,2} \in (3/5,\; 4/5)$,

so that both $k_{1,1}$ and $k_{1,2}$ belong to $K_1$ and are accumulation points of $K_1$.

After removing $K_1$, the largest remaining open subinterval $I \subset (0,1) \setminus K_1$ has length at most $0.4$.

---

**Step 2: Subdivide and recurse**  
Now consider the three open intervals that remain after removing $K_1$:
- $I_1 := (0,\; k_{1,1}) \setminus K_1$,
- $I_2 := (k_{1,1},\; k_{1,2}) \setminus K_1$,
- $I_3 := (k_{1,2},\; 1) \setminus K_1$.

Each of these is an open subset of $(0,1)$ disjoint from $K_1$.  
Since $M$ is superdense, each $I_i$ intersects $M$ in an uncountable set.  
Also, since $\kappa(M) = 0$, each such intersection has outer measure zero.

Within each $I_i$, we repeat the procedure:
- Find a compact set $K_n \subset M \cap I_i$,
- $K_n$ must have at least two accumulation points in $I_i$,
- $K_n$ must be disjoint from all previously chosen $K_j$.

At each stage of recursion, the largest remaining open interval after removing $K_1, \dots, K_n$ has length at most $0.4^n \to 0$ as $n \to \infty$.

---

**Step 3: Tree structure and countability**  
At each step, we subdivide the interval into at most **three** disjoint open subintervals.  
This defines a ternary tree of intervals, where in each interval at most **one** new compact set $K_n$ is constructed.  
Although the process can be continued indefinitely, it produces at most **countably many** disjoint compact sets.

---

**Conclusion:**  
We have constructed at most countably many pairwise disjoint compact subsets $K_n \subset M$, each with at least two accumulation points.  
Hence, any such family of compact subsets of $M$ must be countable.

$\blacksquare$
