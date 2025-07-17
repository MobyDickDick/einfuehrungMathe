**Title:** How to prove that inner and outer measure coincide for all subsets of $(0,1)$ using compact and open approximations?

---

I am studying a constructive variant of inner and outer measure on the interval $(0,1)$, defined purely via compact subsets and open supersets — without invoking $\sigma$-algebras, Carathéodory's criterion, or non-constructive principles.

---

### 1. Definitions

Let $M \subseteq (0,1)$. Define:

* $\mathbb{V}$: the set of all open supersets of $M$,
* $\mathbb{W}$: the set of all compact subsets of $M$.

We define:

* **Outer measure**:
  $\kappa(M) := \inf\{ \lambda(U) \mid U \in \mathbb{V} \}$

* **Inner measure**:
  $\nu(M) := \sup\{ \lambda(T) \mid T \in \mathbb{W} \}$

Here, $\lambda$ denotes Lebesgue length defined as follows:

* For open sets $U = \bigcup_{k \in \mathbb{N}} (a_k, b_k)$ (disjoint, bounded),
  $\lambda(U) := \sum_{k \in \mathbb{N}} (b_k - a_k)$.

* For compact sets $T \subseteq (0,1)$, we define:
  $\lambda(T) := \inf\{ \lambda(U) \mid T \subseteq U,\; U \text{ open} \}$
  which coincides with $1 - \lambda((0,1) \setminus T)$ when the complement is open.

---

### 2. Goals

We aim to prove, for all $M \subseteq [0,1]$:

1. **Complementarity**:
   $\kappa(M) + \kappa([0,1] \setminus M) = 1$

2. **Equality of inner and outer measure**:
   $\kappa(M) = \nu(M)$

3. **Additivity for disjoint sets**:
   If $M_1 \cap M_2 = \emptyset$, then
   $\kappa(M_1 \cup M_2) = \kappa(M_1) + \kappa(M_2)$

4. **Extension to $\mathbb{R}$**:
   For arbitrary $M \subseteq \mathbb{R}$, define
   $\kappa(M) := \sum_{z \in \mathbb{Z}} \kappa(M \cap (z, z+1))$

---

### 3. Preliminaries

#### 3.1. Correctness on open and compact sets

Let $U \subseteq (0,1)$ be open and $T \subseteq (0,1)$ compact. Then:
$\kappa(U) = \nu(U) = \lambda(U), \quad \kappa(T) = \nu(T) = \lambda(T)$

**Justification:**

* For open $U$, the infimum is achieved by $U$ itself, and compact subsets $K_n \subset U$ can approximate $U$ from below.
* For compact $T$, we use the definition of $\lambda(T)$ as the infimum over open supersets, and both inner and outer measures coincide with that.

---

### 4. Main Results

#### 4.1. Key contradiction argument for $\kappa(M) = \nu(M)$

Let $(T_k)_{k \in \mathbb{N}}$ be an increasing sequence of compact subsets of $M$ with
$\lambda(T_k) \nearrow \nu(M)$
and let $T := \bigcup_{k} T_k$. Suppose $\kappa(M \setminus T) > 0$. Then there exists a compact $T_W \subset M \setminus T$ with $\lambda(T_W) = \varepsilon > 0$.

Since $T_W$ is disjoint from all $T_k$, we can find $j$ such that:
$\lambda(T_j) > \nu(M) - \varepsilon$
Then:
$\lambda(T_j \cup T_W) = \lambda(T_j) + \lambda(T_W) > \nu(M)$
contradicting the maximality of $\nu(M)$. Hence:
$\kappa(M \setminus T) = 0,\quad \kappa(M) = \kappa(T) = \nu(M)$

---

#### 4.2. Symmetric approximation argument

For all $T \in \mathbb{W}$, $U \in \mathbb{V}$, we have:
$\lambda(U) - \lambda(T) \geq \kappa(M) - \nu(M)$
But the infimum of $\lambda(U) - \lambda(T)$ over such pairs is zero, because:
$\bigcap_{U \in \mathbb{V}} U = \bigcup_{T \in \mathbb{W}} T$
This yields:
$\kappa(M) = \nu(M)$

---

#### 4.3. Complementarity: $\kappa(M) + \kappa((0,1) \setminus M) = 1$

From previous result $\kappa = \nu$, for any $\varepsilon > 0$, we can find compact sets $T_M \subset M$, $T_{\complement} \subset (0,1) \setminus M$ with:
$\lambda(T_M) > \nu(M) - \varepsilon/2,\quad \lambda(T_{\complement}) > \nu((0,1) \setminus M) - \varepsilon/2$
Then:
$\nu(M) + \nu((0,1) \setminus M) < \lambda(T_M) + \lambda(T_{\complement}) + \varepsilon < 1 + \varepsilon$
Letting $\varepsilon \to 0$ yields:
$\kappa(M) + \kappa((0,1) \setminus M) = 1$

---

#### 4.4. Additivity for disjoint sets

Let $M_1 \cap M_2 = \emptyset$. For any $\varepsilon > 0$, choose compact sets $T_1 \subset M_1$, $T_2 \subset M_2$ with:
$\lambda(T_1) > \kappa(M_1) - \varepsilon/2,\quad \lambda(T_2) > \kappa(M_2) - \varepsilon/2$
Then $T_1 \cup T_2 \subset M_1 \cup M_2$, and:
$\kappa(M_1 \cup M_2) \geq \lambda(T_1) + \lambda(T_2) > \kappa(M_1) + \kappa(M_2) - \varepsilon$
Letting $\varepsilon \to 0$ gives:
$\kappa(M_1 \cup M_2) \geq \kappa(M_1) + \kappa(M_2)$
while subadditivity gives $\leq$, so equality holds.

---

#### 4.5. Generalization to $\mathbb{R}$

For arbitrary $M \subseteq \mathbb{R}$, define:
$\kappa(M) := \sum_{z \in \mathbb{Z}} \kappa(M \cap (z, z+1))$
This is well-defined (possibly infinite), and all previous results apply interval-wise.

---

### 5. Final Remarks

These results show that a robust and additive measure can be defined on arbitrary subsets of $\mathbb{R}$ using only open supersets and compact subsets, without invoking $\sigma$-algebras or Carathéodory's extension. The mutual approximation structure between open covers and compact inner sets enforces $\kappa(M) = \nu(M)$ constructively.

---

### My Question

Are these constructive arguments logically sound? Especially:

* Does the identity $\kappa(M) = \nu(M)$ follow rigorously from approximation arguments?
* Can this be accepted as a valid foundational approach to measure without $\sigma$-algebras?
* Could this be formalized in a proof assistant such as Lean?

---

**Tags**: `real-analysis`, `measure-theory`, `outer-measure`, `inner-measure`, `constructive-mathematics`, `formal-verification`
