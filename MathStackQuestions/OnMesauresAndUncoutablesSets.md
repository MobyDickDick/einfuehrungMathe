

# On Length Measurement (Version 1)

**Markus Demarmels**  
E-mail: markus.demarmels@bluewin.ch  
Date: last update: August 10, 2025  

---

## Summary

In this short document I attempt to show that for one-dimensional point sets a measure can be defined such that every set has both an inner and an outer measure, and that these two coincide. Furthermore, I would like to show that every subset of the real numbers with uncountably many elements has to be equinumerous to the real numbers.

## Preface

I emphasize that I have no intention of writing a plagiarism. I hope that you, the reader, will enjoy this document as much as I enjoyed writing it. It is a summary. After I posted my proposals online (and sent them to a former schoolmate), I was astonished and somewhat dismayed at the hostility they provoked. The reason given was simple: my ideas could “never work.” Nevertheless, I want to summarize them again.

---

## Chapter 1 On Length Measurement

Some preliminary remarks:

It is well known that according to the official view it is not possible to prove that every set M ⊂ (0,1) can consistently be assigned a number κ(M) such that

- κ((0,1)) = 1  
- κ(M) + κ((0,1)∖M) = 1  

Likewise, according to standard opinion it is not provable that every uncountable set of reals must be equinumerous with ℝ.  

However, I wish to argue: the existence of non-measurable sets is tied to the Axiom of Choice, and I simply choose not to invoke it. I allow myself that freedom.

It is also the standard view that the Continuum Hypothesis is undecidable. Yet I add extra assumptions coming from analysis. Under these, I believe one can reasonably assume that every subset of the reals with more than countably many elements must be equinumerous with ℝ.

I dislike concepts “pulled out of thin air.” So I attempt to define length measurement of sets directly. To my surprise, it seems sufficient to use only open subsets of ℝ. Thus I define κ: P(ℝ) → ℝ by:

For a,b ∈ ℝ, let ⟨a,b⟩ = (min{a,b}, max{a,b}). Then

κ(⟨a,b⟩) = max{a,b} − min{a,b}.

In particular, κ((0,1)) = 1.

Further, I want κ to satisfy:

- κ(M₁ ∪ M₂) = κ(M₁) + κ(M₂) − κ(M₁ ∩ M₂).  
  In particular, if M₁ ∩ M₂ = ∅ then κ(M₁ ∪ M₂) = κ(M₁) + κ(M₂).  
- If M₁ ∩ M₂ ≠ ∅ then κ(M₁ ∪ M₂) ≤ κ(M₁) + κ(M₂).  
- Translation invariance: κ(a + M) = κ(M) for all a ∈ ℝ.

---

## Definitions

**Definition 1.** Let I ⊂ ℝ be a nonempty open connected set (an interval). Then  
κ(I) = sup(I) − inf(I).

For open M ⊂ ℝ, write M = ⋃ₖ Iₖ with pairwise disjoint open intervals Iₖ. Define  
κ(M) = Σ κ(Iₖ) if the sum converges, else κ(M) = ∞. For the empty set, κ(∅) = 0.  

Let 𝒱 be the set of open subsets of ℝ. For M ⊂ ℝ, define 𝒱(M) = {U ∈ 𝒱 | M ⊂ U}.  

For M ⊂ (0,1), define  
κ(M) = inf{ κ(U) | U ∈ 𝒱(M) }.  

Let 𝒲(M) be the set of compact subsets of M.

Clearly κ((0,1)) = 1 and κ(∅) = 0.

---

## Results

**Theorem 2.** For M ⊂ (0,1):  
M = ⋂_{U ∈ 𝒱(M)} U.  

*Proof.* If M = ∅ this is trivial. If x ∈ M then x ∈ U for every U ∈ 𝒱(M), so x ∈ ⋂U. If x ∉ M then T = (0,x) ∪ (x,1) is an open set containing M but not x, hence x ∉ ⋂U. Thus the equality holds. ∎

**Theorem 3.** For M ⊂ ℝ:  
M = ⋃_{K ∈ 𝒲(M)} K.  

*Proof.* Every x ∈ M is contained in {x}, which is compact. Conversely, any compact K ⊂ M satisfies K ⊂ M, so ⋃K ⊂ M. ∎

From this it follows:  
⋂_{U ∈ 𝒱(M)} U ∖ ⋃_{K ∈ 𝒲(M)} K = ∅.  

Equivalently,  
⋂{ U∖K | K ⊂ M ⊂ U, K ∈ 𝒲(M), U ∈ 𝒱(M) } = ∅.  

This motivates the search for sequences (Uₙ), (Kₙ) with Kₙ ⊂ Kₙ₊₁ ⊂ M ⊂ Uₙ₊₁ ⊂ Uₙ and ⋂ (Uₙ∖Kₙ) = ∅.

---

## Towards Additivity

If such sequences exist, one can aim to prove:  
κ(M) + κ((0,1)∖M) = 1.  

I sketch the argument: for approximating compacts Kₙ ⊂ M and Lₙ ⊂ (0,1)∖M, their measures can be arranged so that Σ (κ(Kₙ)+κ(Lₙ)) = 1. Taking suprema λ_K = sup{κ(K) | K ⊂ M, K compact} and λ_L similarly for (0,1)∖M, one shows λ_K + λ_L = 1. Hence κ(M) + κ((0,1)∖M) = 1.

**Lemma 4.** If κ(M) = 1 then κ((0,1)∖M) = 0.  

*Proof.* Since (0,1)∖M = ⋃_{U ∈ 𝒱(M)} (0,1)∖U, each complement is compact and their union has measure 0. Thus κ((0,1)∖M) = 0. ∎

---

## Open Questions

I think the equality κ(M) + κ((0,1)∖M) = 1 can be proved.  
But the further question remains: can every set be written as a union of at most countably many compact subsets?

Another issue: given R = (0,1) ∖ ⋃ₙ (Kₙ ∪ Lₙ), can one say more than “R is a null set”?

---

## Superdense Null Sets

**Theorem 5.** Let M ⊂ (0,1) be superdense, uncountable, and with κ(M) = 0. Then there exist sequences of compacts Kₙ ⊂ M and opens Uₙ ⊃ M with Kₙ ⊂ Kₙ₊₁ ⊂ M ⊂ Uₙ₊₁ ⊂ Uₙ such that ⋂(Uₙ∖Kₙ) = ∅.  

Sketch of construction: iteratively build compacts with many accumulation points and shrinking open covers of small total length. This yields an “exhaustion” of M by compacts.

A second method is Cantor-like: construct nested families of open sets Uₙ removing subintervals while preserving points of M. The complement ⋂ (0,1)∖⋃Uₙ is compact, consists only of accumulation points, and hence is equinumerous with ℝ.

---

## Interim Conclusion

- The framework suggests that κ(M) + κ((0,1)∖M) = 1.  
- For κ(M) = 1 we indeed get κ((0,1)∖M) = 0.  
- For superdense null sets M we can construct Cantor-type exhaustions leading to compact subsets equinumerous with ℝ.

The remaining open problems: whether every set decomposes into at most countably many compacts, and what exactly can be said about the residual sets in these constructions.

---

## Comment on Logical Coherence

I do not see a blatant logical contradiction in your text. The steps follow the familiar outline of outer/inner measure via open covers and compact subsets. The weak points are where you *assert existence* of sequences (Kₙ), (Uₙ) with certain approximation properties. In standard measure theory this is justified using regularity theorems; in your constructive setting you would need to prove it directly. As long as you are aware this is the nontrivial step, the reasoning is coherent.
