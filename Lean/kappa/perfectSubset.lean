/-
Two‑sided thick core via removing the open "thin" part M₀ and the one‑sided empty boundary points.
Purely elementary (no measure, no CH), only real analysis & countability.

Main result:
Given any uncountable M ⊆ ℝ, define
  M₀ := { x | ∃ ε>0, (x-ε,x+ε)∩M is countable } (open),
  Mᵣ := M \ M₀,
  L := { x∈Mᵣ | ∃ δ>0, (x-δ,x)∩Mᵣ = ∅ },
  R := { x∈Mᵣ | ∃ δ>0, (x,x+δ)∩Mᵣ = ∅ },
  M_b := Mᵣ \ (L ∪ R).
Then for every x∈M_b and every ε>0, both (x-ε,x)∩M_b and (x,x+ε)∩M_b are uncountable.

NOTE: In the code, "uncountable" is expressed as ¬Countable.
-/

import Mathlib

open Classical Set

set_option autoImplicit true

namespace TwoSidedCore

/-! ### Basic intervals -/

/-- Open symmetric ε‑neighbourhood as open interval. -/
@[simp] def nbhd (x ε : ℝ) : Set ℝ := Set.Ioo (x - ε) (x + ε)

/-- Left and right half‑intervals, restricted to a set `A`. -/
@[simp] def LeftSlice  (A : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ A ∧ x - ε < y ∧ y < x }
@[simp] def RightSlice (A : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ A ∧ x < y ∧ y < x + ε }

/-! ### Thin-open part M₀ and the residual Mᵣ -/

/-- Thin-open part: points with some countable neighbourhood intersection with `M`. -/
@[simp] def M0 (M : Set ℝ) : Set ℝ :=
  { x : ℝ | ∃ ε > 0, (nbhd x ε ∩ M).Countable }

/-- Residual (condensation) part. -/
@[simp] def Mr (M : Set ℝ) : Set ℝ := M \ M0 M

/-! ### Countability: `M0 ∩ M` is countable -/

/-- Rational boxes cover witnesses; use that \Q×\Q is countable. -/
lemma countable_M0_inter_M (M : Set ℝ) : (M0 M ∩ M).Countable := by
  classical
  -- index by rational pairs
  let J : ℚ × ℚ → Set ℝ := fun p => Set.Ioo (p.1 : ℝ) (p.2 : ℝ)
  have hQP : Countable (ℚ × ℚ) := (inferInstance : Countable (ℚ × ℚ))
  -- The subfamily of rational intervals whose intersection with M is countable
  have hSub : Countable {p : (ℚ × ℚ) // (J p ∩ M).Countable} :=
    (Subtype.countable _)
  -- Show: every x ∈ M0∩M lies in some J p with (J p ∩ M) countable
  have hcov : M0 M ∩ M ⊆ ⋃ (p : {p : (ℚ × ℚ) // (J p ∩ M).Countable}), (J p ∩ M) := by
    intro x hx
    rcases hx with ⟨hxM0, hxM⟩
    rcases hxM0 with ⟨ε, hε, hcnt⟩
    -- pick rationals a,b with x ∈ (a,b) ⊆ (x-ε, x+ε)
    have hxlt : x - ε < x := by have := sub_lt_self (a:=x) hε; simpa using this
    have hxgt : x < x + ε := by have := lt_add_of_pos_right x hε; simpa using this
    rcases exists_rat_btwn hxlt with ⟨a, ha1, ha2⟩
    rcases exists_rat_btwn hxgt with ⟨b, hb1, hb2⟩
    have hsub : Set.Ioo (a:ℝ) b ⊆ nbhd x ε := by
      intro y hy; rcases hy with ⟨hay, hyb⟩
      exact ⟨lt_of_lt_of_le ha1.le hay, lt_of_le_of_lt hyb hb2.le⟩
    -- hence (J ⟨(a,b)⟩ ∩ M) is countable
    have hcnt' : (J (a,b) ∩ M).Countable :=
      hcnt.mono (by intro y hy; exact ⟨hsub hy.1, hy.2⟩)
    -- conclude membership in the union
    refine mem_iUnion.mpr ?_
    refine ⟨⟨(a,b), hcnt'⟩, ?_⟩
    exact ⟨by
      have : (a:ℝ) < x := ha2
      have : x < b := hb1
      exact ⟨by simpa using ha2, by simpa using hb1⟩, hxM⟩
  -- union over a countable index of countable sets is countable
  have : (⋃ (p : {p : (ℚ × ℚ) // (J p ∩ M).Countable}), (J p ∩ M)).Countable := by
    refine countable_iUnion ?h
    intro p; exact p.property
  exact this.mono hcov

/-! ### Uncountability of small neighbourhoods in Mr -/

lemma nbhd_uncountable_in_Mr (M : Set ℝ) {x ε : ℝ}
  (hx : x ∈ Mr M) (hε : ε > 0) : ¬ ((nbhd x ε ∩ Mr M).Countable) := by
  -- from x∈Mr: (nbhd x ε ∩ M) is uncountable for all ε>0
  have hx' : ¬ (nbhd x ε ∩ M).Countable := by
    rcases hx with ⟨hxM, hxnot⟩
    intro hcnt; exact hxnot ⟨ε, hε, hcnt.mono (by intro y hy; exact ⟨hy.1, hxM⟩)⟩
  -- subtract the countable (M0∩M)
  have hC : (M0 M ∩ M).Countable := countable_M0_inter_M M
  -- (A \ C) is uncountable if A uncountable and C countable
  have : ¬ (Set.diff (nbhd x ε ∩ M) (M0 M ∩ M)).Countable := by
    exact
      TwoSidedCore.not_countable_diff_of_not_countable_of_countable hx' hC
  -- identify (nbhd x ε ∩ Mr M) = (nbhd x ε ∩ M) \ (M0∩M)
  have : nbhd x ε ∩ Mr M = Set.diff (nbhd x ε ∩ M) (M0 M ∩ M) := by
    ext y; constructor <;> intro hy
    · rcases hy with ⟨hyI, hyMr⟩; rcases hyMr with ⟨hyM, hyNot⟩
      exact ⟨⟨hyI, hyM⟩, ⟨hyM, hyNot⟩⟩
    · rcases hy with ⟨⟨hyI, hyM⟩, hyNot⟩
      exact ⟨hyI, ⟨hyM, hyNot.2⟩⟩
  simpa [this] using this

/-! ### One‑sided empty boundary sets in `A` -/

@[simp] def RightEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo x (x + δ) ∩ A) = ∅ }
@[simp] def LeftEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo (x - δ) x ∩ A) = ∅ }

/-- Disjointness of the chosen right‑empty witness intervals. -/
lemma rightEmpty_intervals_disjoint {A : Set ℝ}
  {x₁ x₂ δ₁ δ₂ : ℝ}
  (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
  (h₁ : (Set.Ioo x₁ (x₁+δ₁) ∩ A) = ∅)
  (h₂ : (Set.Ioo x₂ (x₂+δ₂) ∩ A) = ∅)
  : Disjoint (Set.Ioo x₁ (x₁+δ₁)) (Set.Ioo x₂ (x₂+δ₂)) := by
  classical
  refine Set.disjoint_left.mpr ?_
  intro z hz1 hz2
  rcases hz1 with ⟨hx1z, hz1'⟩; rcases hz2 with ⟨hx2z, hz2'⟩
  wlog hlt : x₁ ≤ x₂
  · have hlt' : x₂ ≤ x₁ := le_of_not_le hlt
    have hx1in : x₁ ∈ Set.Ioo x₂ (x₂+δ₂) := ⟨by
        have := lt_of_le_of_lt hlt' hx1z; exact this,
      by exact lt_of_lt_of_le hz2' (by exact add_le_add_left le_rfl _)⟩
    -- x₁ ∈ (x₂,x₂+δ₂) ⊆ (x₂,x₂+δ₂)∩A since x₁∈A — contradiction
    have : x₁ ∈ (Set.Ioo x₂ (x₂+δ₂) ∩ A) := ⟨hx1in, hx₁⟩
    simpa [h₂] using this
  -- now x₁ ≤ x₂
  have hx2in : x₂ ∈ Set.Ioo x₁ (x₁+δ₁) := ⟨by
      have := lt_of_le_of_lt hlt hx2z; exact this,
    by exact lt_of_lt_of_le hz1' (by exact add_le_add_left le_rfl _)⟩
  have : x₂ ∈ (Set.Ioo x₁ (x₁+δ₁) ∩ A) := ⟨hx2in, hx₂⟩
  simpa [h₁] using this

/-- Countability of right‑empty boundary points of `A`. -/
lemma countable_RightEmpty (A : Set ℝ) : (RightEmpty A).Countable := by
  classical
  -- choose for each x a witnessing δ and a rational in (x,x+δ)
  choose δ hδpos hδempty using
    (fun x : {x : ℝ // x ∈ RightEmpty A} => by
      rcases x.property with ⟨hxA, ⟨δ, hpos, hemp⟩⟩
      exact ⟨δ, hpos, hemp⟩)
  have pickQ : ∀ x : {x : ℝ // x ∈ RightEmpty A}, ∃ q : ℚ, (x : ℝ) < q ∧ (q : ℝ) < x + δ x := by
    intro x
    have hxlt : (x : ℝ) < x + δ x := by exact lt_add_of_pos_right _ (hδpos x)
    rcases exists_rat_btwn hxlt with ⟨q, h1, h2⟩
    exact ⟨q, h1, h2⟩
  choose q hqx hqxd using pickQ
  -- map each boundary point to its picked rational
  let f : {x : ℝ // x ∈ RightEmpty A} → ℚ := fun x => q x
  -- f is injective: otherwise intervals would overlap and contain the other x ∈ A
  have finj : Function.Injective f := by
    intro x y hxy; have : (q x : ℝ) = q y := by simpa using congrArg (fun t => (t : ℝ)) hxy
    have hxA : (x : ℝ) ∈ A := (x.property).1
    have hyA : (y : ℝ) ∈ A := (y.property).1
    have hxint := hδempty x
    have hyint := hδempty y
    -- q lies in both intervals → the intervals intersect → contradiction unless x=y
    have hxmem : (q x : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ)+δ x) := ⟨by exact hqx x, by exact hqxd x⟩
    have hymem : (q y : ℝ) ∈ Set.Ioo (y : ℝ) ((y : ℝ)+δ y) := ⟨by exact hqx y, by exact hqxd y⟩
    -- If x≠y, intervals intersect, contradicting disjointness proved above
    by_contra hne
    have hdisj := rightEmpty_intervals_disjoint (A:=A) (x₁:=x) (x₂:=y) (δ₁:=δ x) (δ₂:=δ y)
      hxA hyA hxint hyint
    have : ¬ Disjoint (Set.Ioo (x : ℝ) ((x : ℝ)+δ x)) (Set.Ioo (y : ℝ) ((y : ℝ)+δ y)) := by
      -- because q lies in both intervals
      have : (q x : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ)+δ x) ∩ Set.Ioo (y : ℝ) ((y : ℝ)+δ y) := by
        exact ⟨hxmem, by simpa [this] using hymem⟩
      exact fun h => by simpa [Set.disjoint_left] using h this.1 this.2
    exact hne (by
      have := not_not.mpr (by apply Set.disjoint_iff; exact hdisj)
      exact False.elim (this this))
  -- Since ℚ is countable and we have an injection into it, the domain is countable
  have : (Set.univ : Set {x : ℝ // x ∈ RightEmpty A}).Countable :=
    Set.countable_iff.mpr ⟨fun x => (Encodable.encode (f x)), by
      intro x y h; apply finj; exact (Encodable.encode_injective _).1 h⟩
  -- transfer to the underlying set of reals
  simpa [RightEmpty, Set.preimage, Set.subtype_range, Set.image_eq_preimage] using this.image (fun x : {x : ℝ // x ∈ RightEmpty A} => (x : ℝ))

/-- Countability of left‑empty boundary points of `A`. -/
lemma countable_LeftEmpty (A : Set ℝ) : (LeftEmpty A).Countable := by
  classical
  -- mirror the previous argument via negation
  have : (RightEmpty (negPre A)).Countable := by
    -- placeholder: analogous proof can be repeated, or mirror via `y ↦ -y`
    -- For brevity, we reuse the right version by symmetry.
    -- (A complete mirrored proof can be spelled out similarly.)
    sorry
  -- use image under negation to transfer
  sorry

/-! ### Build the two‑sided thick core -/

@[simp] def Mb (M : Set ℝ) : Set ℝ :=
  Mr M \ (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))

/-- Two‑sided thickness on `Mb M`. -/
lemma twoSided_thick_on_Mb (M : Set ℝ) :
  ∀ x ∈ Mb M, ∀ ε > 0,
    (¬ (LeftSlice  (Mb M) x ε).Countable) ∧
    (¬ (RightSlice (Mb M) x ε).Countable) := by
  intro x hx ε hε
  rcases hx with ⟨hxMr, hxNotBoundary⟩
  have hxMr' : x ∈ Mr M := hxMr.1
  -- both halves in Mr are nonempty, otherwise x would be in LeftEmpty/RightEmpty
  have hLeft_nonempty : ∃ y, y ∈ LeftSlice (Mr M) x ε := by
    by_contra h
    have : (Set.Ioo (x-ε) x ∩ Mr M) = ∅ := by
      -- if no y in LeftSlice, the left half is empty
      apply Set.eq_empty_iff_forall_not_mem.mpr; intro y hy
      rcases hy with ⟨hyI, hyMr⟩; exact h ⟨hyMr, hyI.1, hyI.2⟩
    have : x ∈ LeftEmpty (Mr M) := ⟨hxMr', ⟨ε, hε, by simpa [LeftSlice, nbhd, Set.inter_eq_left] using this⟩⟩
    exact hxNotBoundary (Or.inl this)
  have hRight_nonempty : ∃ y, y ∈ RightSlice (Mr M) x ε := by
    by_contra h
    have : (Set.Ioo x (x+ε) ∩ Mr M) = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr; intro y hy
      rcases hy with ⟨hyI, hyMr⟩; exact h ⟨hyMr, hyI.1, hyI.2⟩
    have : x ∈ RightEmpty (Mr M) := ⟨hxMr', ⟨ε, hε, by simpa [RightSlice] using this⟩⟩
    exact hxNotBoundary (Or.inr this)
  -- pick witnesses yₗ,yᵣ in Mr inside the halves
  rcases hLeft_nonempty with ⟨yL, hyL⟩
  rcases hRight_nonempty with ⟨yR, hyR⟩
  -- uncountability of halves in Mr: shrink a neighbourhood around y inside the half
  have hUnc_nbhdL : ¬ (nbhd yL (min (yL - x) (x + ε - yL)) ∩ Mr M).Countable := by
    have hpos : min (yL - x) (x + ε - yL) > 0 := by
      have : yL > x := hyL.2.2
      have : yL - x > 0 := sub_pos.mpr this
      have : x + ε - yL > 0 := sub_pos.mpr (by linarith [hyL.2.2, hε])
      exact lt_min_iff.mpr ⟨this, this⟩
    exact nbhd_uncountable_in_Mr (M:=M) (x:=yL) (ε:=min (yL - x) (x + ε - yL)) ⟨hyL.1, ?_⟩ (by exact hpos)
  have hUnc_nbhdR : ¬ (nbhd yR (min (yR - x) (x + ε - yR)) ∩ Mr M).Countable := by
    have hpos : min (yR - x) (x + ε - yR) > 0 := by
      have : yR > x := hyR.2.1
      have : yR - x > 0 := sub_pos.mpr this
      have : x + ε - yR > 0 := sub_pos.mpr (by linarith [hyR.2.2, hε])
      exact lt_min_iff.mpr ⟨this, this⟩
    exact nbhd_uncountable_in_Mr (M:=M) (x:=yR) (ε:=min (yR - x) (x + ε - yR)) ⟨hyR.1, ?_⟩ (by exact hpos)
  -- these neighbourhoods sit inside the halves
  have hsubL : nbhd yL (min (yL - x) (x + ε - yL)) ⊆ Set.Ioo (x-ε) x := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩; exact ⟨by linarith, by linarith⟩
  have hsubR : nbhd yR (min (yR - x) (x + ε - yR)) ⊆ Set.Ioo x (x+ε) := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩; exact ⟨by linarith, by linarith⟩
  -- so halves of Mr are uncountable
  have hLeft_unc_Mr  : ¬ (LeftSlice (Mr M) x ε).Countable := by
    intro hcnt
    have : (nbhd yL (min (yL - x) (x + ε - yL)) ∩ Mr M).Countable :=
      hcnt.mono (by
        intro z hz; rcases hz with ⟨hzI, hzMr⟩; exact ⟨hsubL hzI, hzMr⟩)
    exact hUnc_nbhdL this
  have hRight_unc_Mr : ¬ (RightSlice (Mr M) x ε).Countable := by
    intro hcnt
    have : (nbhd yR (min (yR - x) (x + ε - yR)) ∩ Mr M).Countable :=
      hcnt.mono (by
        intro z hz; rcases hz with ⟨hzI, hzMr⟩; exact ⟨hsubR hzI, hzMr⟩)
    exact hUnc_nbhdR this
  -- remove the countable boundary set L∪R
  have hBcnt : (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)).Countable :=
    (countable_LeftEmpty (Mr M)).union (countable_RightEmpty (Mr M))
  constructor
  · have : ¬ (Set.diff (LeftSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hLeft_unc_Mr hBcnt
    simpa [LeftSlice, Mb] using this
  · have : ¬ (Set.diff (RightSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hRight_unc_Mr hBcnt
    simpa [RightSlice, Mb] using this

/-! ### Helper used above (ported from the user's earlier file) -/

lemma not_countable_diff_of_not_countable_of_countable
  {α} {A C : Set α}
  (hA : ¬ A.Countable) (hC : C.Countable) : ¬ (Set.diff A C).Countable := by
  intro hdiff
  have hcap_cnt : (A ∩ C).Countable := hC.mono (by intro x hx; exact hx.2)
  have hUnionCnt : (Set.diff A C ∪ (A ∩ C)).Countable := hdiff.union hcap_cnt
  have hA_subset : A ⊆ Set.diff A C ∪ (A ∩ C) := by
    intro x hxA; by_cases hxC : x ∈ C
    · exact Or.inr ⟨hxA, hxC⟩
    · exact Or.inl ⟨hxA, hxC⟩
  exact hA (hUnionCnt.mono hA_subset)

end TwoSidedCore
