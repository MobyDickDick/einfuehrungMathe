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

/-! ### Basic intervals and slices -/

/-- Open symmetric ε‑neighbourhood as an open interval. -/
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

/-! ### A general helper -/

/-- If `A` is uncountable and `C` countable, then `A \ C` is uncountable. -/
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

/-! ### Countability: `M0 ∩ M` is countable -/

/-- Use the countable rational basis to cover witnesses. -/
lemma countable_M0_inter_M (M : Set ℝ) : (M0 M ∩ M).Countable := by
  classical
  -- index by rational pairs
  let J : ℚ × ℚ → Set ℝ := fun p => Set.Ioo (p.1 : ℝ) (p.2 : ℝ)
  have hSub : Countable {p : (ℚ × ℚ) // (J p ∩ M).Countable} :=
    (Subtype.countable _)
  -- Every x ∈ M0∩M lies in some rational interval whose intersection with M is countable
  have hcov : M0 M ∩ M ⊆ ⋃ (p : {p : (ℚ × ℚ) // (J p ∩ M).Countable}), (J p ∩ M) := by
    intro x hx
    rcases hx with ⟨hxM0, hxM⟩
    rcases hxM0 with ⟨ε, hε, hcnt⟩
    have hxlt : x - ε < x := by simpa using sub_lt_self (a:=x) hε
    have hxgt : x < x + ε := by simpa using lt_add_of_pos_right x hε
    rcases exists_rat_btwn hxlt with ⟨a, ha1, ha2⟩
    rcases exists_rat_btwn hxgt with ⟨b, hb1, hb2⟩
    have hsub : Set.Ioo (a:ℝ) b ⊆ nbhd x ε := by
      intro y hy; exact ⟨lt_of_lt_of_le ha1.le hy.1, lt_of_le_of_lt hy.2 hb2.le⟩
    have hcnt' : (J (a,b) ∩ M).Countable :=
      hcnt.mono (by intro y hy; exact ⟨hsub hy.1, hy.2⟩)
    refine mem_iUnion.mpr ?_
    exact ⟨⟨(a,b), hcnt'⟩, ⟨by exact And.intro (by simpa using ha2) (by simpa using hb1), hxM⟩⟩
  -- union over a countable index of countable sets is countable
  have : (⋃ (p : {p : (ℚ × ℚ) // (J p ∩ M).Countable}), (J p ∩ M)).Countable := by
    refine countable_iUnion ?h
    intro p; exact p.property
  exact this.mono hcov

/-! ### Uncountability of small neighbourhoods in Mr -/

lemma nbhd_uncountable_in_Mr (M : Set ℝ) {x ε : ℝ}
  (hx : x ∈ Mr M) (hε : ε > 0) : ¬ ((nbhd x ε ∩ Mr M).Countable) := by
  classical
  -- from x∈Mr: (nbhd x ε ∩ M) is uncountable for all ε>0
  have hxM : x ∈ M := hx.1
  have hxnot : x ∉ M0 M := hx.2
  have hx' : ¬ (nbhd x ε ∩ M).Countable := by
    intro hcnt; exact hxnot ⟨ε, hε, hcnt.mono (by intro y hy; exact ⟨hy.1, hy.2.2⟩)⟩
  -- subtract the countable (M0∩M)
  have hC : (M0 M ∩ M).Countable := countable_M0_inter_M M
  -- identify (nbhd ∩ Mr) as a set difference
  have hEq : nbhd x ε ∩ Mr M = Set.diff (nbhd x ε ∩ M) (M0 M ∩ M) := by
    ext y; constructor <;> intro hy
    · rcases hy with ⟨hyI, hyMr⟩; exact ⟨⟨hyI, hyMr.1⟩, ⟨hyMr.1, hyMr.2⟩⟩
    · rcases hy with ⟨⟨hyI, hyM⟩, hyMem⟩; exact ⟨hyI, ⟨hyM, hyMem.2⟩⟩
  -- conclude
  have : ¬ (Set.diff (nbhd x ε ∩ M) (M0 M ∩ M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hx' hC
  simpa [hEq] using this

/-! ### One‑sided empty boundary sets in `A` and their countability -/

@[simp] def RightEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo x (x + δ) ∩ A) = ∅ }
@[simp] def LeftEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo (x - δ) x ∩ A) = ∅ }

/-- Countability of right‑empty boundary points of `A` via an injection into ℚ. -/
lemma countable_RightEmpty (A : Set ℝ) : (RightEmpty A).Countable := by
  classical
  -- For each x, pick a rational q with x < q < x+δ where (x,x+δ)∩A = ∅.
  have hxq : ∀ x : {x : ℝ // x ∈ RightEmpty A},
      ∃ q : ℚ, ∃ δ > 0, (x : ℝ) < q ∧ (q : ℝ) < (x : ℝ) + δ ∧ (Set.Ioo (x : ℝ) ((x : ℝ) + δ) ∩ A) = ∅ := by
    intro x; rcases x.property with ⟨hxA, ⟨δ, hpos, hemp⟩⟩
    have hxlt : (x : ℝ) < (x : ℝ) + δ := by simpa using lt_add_of_pos_right (x : ℝ) hpos
    rcases exists_rat_btwn hxlt with ⟨q, h1, h2⟩
    exact ⟨q, δ, hpos, h1, h2, hemp⟩
  noncomputable
  def f : {x : ℝ // x ∈ RightEmpty A} → ℚ := fun x => Classical.choose (hxq x)
  have f_spec : ∀ x, ∃ δ > 0,
      (x : ℝ) < f x ∧ (f x : ℝ) < (x : ℝ) + δ ∧ (Set.Ioo (x : ℝ) ((x : ℝ) + δ) ∩ A) = ∅ := by
    intro x
    rcases Classical.choose_spec (hxq x) with ⟨δ, hpos, h1, h2, hemp⟩
    exact ⟨δ, hpos, h1, h2, hemp⟩
  -- Injectivity: if f x = f y = q, then x=y (otherwise q lies in both empty intervals)
  have finj : Function.Injective f := by
    intro x y hxy
    have hxA : (x : ℝ) ∈ A := (x.property).1
    have hyA : (y : ℝ) ∈ A := (y.property).1
    rcases f_spec x with ⟨δx, hxpos, hxltq, hqltx, hxemp⟩
    rcases f_spec y with ⟨δy, hypos, hyltq, hqlty, hyemp⟩
    have : (f x : ℝ) = f y := by simpa using congrArg (fun t => (t : ℝ)) hxy
    have hxqmem : (f x : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ) + δx) := ⟨hxltq, hqltx⟩
    have hyqmem : (f y : ℝ) ∈ Set.Ioo (y : ℝ) ((y : ℝ) + δy) := ⟨hyltq, hqlty⟩
    by_contra hne
    wlog hxy' : (x : ℝ) ≤ (y : ℝ)
    · exact (this $ (le_total _ _).resolve_left hxy').elim
    have : (y : ℝ) < (x : ℝ) + δx := lt_of_le_of_lt hxy' hqltx
    have : (y : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ) + δx) := ⟨lt_of_le_of_lt hxy' hxltq, this⟩
    have : (y : ℝ) ∈ (Set.Ioo (x : ℝ) ((x : ℝ) + δx) ∩ A) := ⟨this, hyA⟩
    simpa [hxemp] using this
  -- Build an injection into ℕ via an injection ℚ → ℕ (since ℚ is countable)
  have : (RightEmpty A).Countable := by
    refine Set.countable_iff.mpr ?_
    refine ⟨fun x : {x : ℝ // x ∈ RightEmpty A} => Encodable.encode (f x), ?_⟩
    intro x y h
    have : f x = f y := by exact Encodable.encode_injective h
    exact finj this
  simpa using this

/-- Countability of left‑empty boundary points (mirror of the right version). -/
lemma countable_LeftEmpty (A : Set ℝ) : (LeftEmpty A).Countable := by
  classical
  have hxq : ∀ x : {x : ℝ // x ∈ LeftEmpty A},
      ∃ q : ℚ, ∃ δ > 0, (x : ℝ) - δ < q ∧ (q : ℝ) < (x : ℝ) ∧ (Set.Ioo ((x : ℝ) - δ) (x : ℝ) ∩ A) = ∅ := by
    intro x; rcases x.property with ⟨hxA, ⟨δ, hpos, hemp⟩⟩
    have hxlt : (x : ℝ) - δ < (x : ℝ) := by simpa using sub_lt_self (a:=(x:ℝ)) hpos
    rcases exists_rat_btwn hxlt with ⟨q, h1, h2⟩
    exact ⟨q, δ, hpos, h1, h2, hemp⟩
  noncomputable
  def f : {x : ℝ // x ∈ LeftEmpty A} → ℚ := fun x => Classical.choose (hxq x)
  have f_spec : ∀ x, ∃ δ > 0,
      (x : ℝ) - δ < f x ∧ (f x : ℝ) < (x : ℝ) ∧ (Set.Ioo ((x : ℝ) - δ) (x : ℝ) ∩ A) = ∅ := by
    intro x
    rcases Classical.choose_spec (hxq x) with ⟨δ, hpos, h1, h2, hemp⟩
    exact ⟨δ, hpos, h1, h2, hemp⟩
  have finj : Function.Injective f := by
    intro x y hxy
    have hxA : (x : ℝ) ∈ A := (x.property).1
    have hyA : (y : ℝ) ∈ A := (y.property).1
    rcases f_spec x with ⟨δx, hxpos, hqxlt, hltx, hxemp⟩
    rcases f_spec y with ⟨δy, hypos, hqylt, hlty, hyemp⟩
    have : (f x : ℝ) = f y := by simpa using congrArg (fun t => (t : ℝ)) hxy
    by_contra hne
    wlog hxy' : (y : ℝ) ≤ (x : ℝ)
    have : (x : ℝ) ∈ Set.Ioo ((y : ℝ) - δy) (y : ℝ) := ⟨lt_of_lt_of_le hqylt hxy', lt_of_le_of_lt hxy' hlty⟩
    have : (x : ℝ) ∈ (Set.Ioo ((y : ℝ) - δy) (y : ℝ) ∩ A) := ⟨this, hxA⟩
    simpa [hyemp] using this
  have : (LeftEmpty A).Countable := by
    refine Set.countable_iff.mpr ?_
    refine ⟨fun x : {x : ℝ // x ∈ LeftEmpty A} => Encodable.encode (f x), ?_⟩
    intro x y h
    have : f x = f y := by exact Encodable.encode_injective h
    exact finj this
  simpa using this

/-! ### Build the two‑sided thick core -/

@[simp] def Mb (M : Set ℝ) : Set ℝ :=
  Mr M \ (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))

/-- On `Mb M`, both left and right slices are uncountable at every scale. -/
lemma twoSided_thick_on_Mb (M : Set ℝ) :
  ∀ x ∈ Mb M, ∀ ε > 0,
    (¬ (LeftSlice  (Mb M) x ε).Countable) ∧
    (¬ (RightSlice (Mb M) x ε).Countable) := by
  classical
  intro x hx ε hε
  rcases hx with ⟨hxMr, hxNotB⟩
  have hxnotL : x ∉ LeftEmpty (Mr M) := by exact fun h => hxNotB (Or.inl h)
  have hxnotR : x ∉ RightEmpty (Mr M) := by exact fun h => hxNotB (Or.inr h)
  -- For all ε>0 the halves in Mr are nonempty (by definition of not in Left/RightEmpty)
  have exL : ∃ y, y ∈ Mr M ∧ x - ε < y ∧ y < x := by
    -- (Ioo (x-ε) x ∩ Mr M) ≠ ∅
    have : (Set.Ioo (x-ε) x ∩ Mr M) ≠ ∅ := by
      -- otherwise x∈LeftEmpty
      by_contra hempty
      have : x ∈ LeftEmpty (Mr M) := ⟨hxMr, ⟨ε, hε, by simpa [LeftEmpty, Set.eq_empty_iff_forall_notMem] using hempty⟩⟩
      exact hxnotL this
    rcases Set.nonempty_iff_ne_empty.mpr this with ⟨y, hy⟩
    rcases hy with ⟨hyI, hyMr⟩
    exact ⟨y, hyMr, hyI.1, hyI.2⟩
  have exR : ∃ y, y ∈ Mr M ∧ x < y ∧ y < x + ε := by
    have : (Set.Ioo x (x+ε) ∩ Mr M) ≠ ∅ := by
      by_contra hempty
      have : x ∈ RightEmpty (Mr M) := ⟨hxMr, ⟨ε, hε, by simpa [RightEmpty, Set.eq_empty_iff_forall_notMem] using hempty⟩⟩
      exact hxnotR this
    rcases Set.nonempty_iff_ne_empty.mpr this with ⟨y, hy⟩
    rcases hy with ⟨hyI, hyMr⟩
    exact ⟨y, hyMr, hyI.1, hyI.2⟩
  rcases exL with ⟨yL, hyL_Mr, hL1, hL2⟩
  rcases exR with ⟨yR, hyR_Mr, hR1, hR2⟩
  -- radii that sit inside the halves
  have dL1 : 0 < yL - (x - ε) := sub_pos.mpr (by linarith)
  have dL2 : 0 < x - yL := sub_pos.mpr hL2
  let ρL : ℝ := (min (yL - (x - ε)) (x - yL)) / 2
  have ρLpos : ρL > 0 := by
    have : 0 < min (yL - (x - ε)) (x - yL) := lt_min_iff.mpr ⟨dL1, dL2⟩
    exact (half_pos this)
  have subL : nbhd yL ρL ⊆ Set.Ioo (x-ε) x := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩
    have hle1 : ρL ≤ yL - (x - ε) := by
      dsimp [ρL]; exact div_le_iff.mpr (by have := min_le_left _ _; nlinarith)
    have hle2 : ρL ≤ x - yL := by
      dsimp [ρL]; exact div_le_iff.mpr (by have := min_le_right _ _; nlinarith)
    constructor
    · have : z > yL - ρL := hz1
      have : z > yL - (yL - (x - ε)) := lt_of_lt_of_le this (by nlinarith [hle1])
      simpa using this
    · have : z < yL + ρL := hz2
      have : z < yL + (x - yL) := lt_of_le_of_lt (by nlinarith [hle2]) this
      simpa using this
  have dR1 : 0 < yR - x := sub_pos.mpr hR1
  have dR2 : 0 < x + ε - yR := sub_pos.mpr (by linarith)
  let ρR : ℝ := (min (yR - x) (x + ε - yR)) / 2
  have ρRpos : ρR > 0 := by
    have : 0 < min (yR - x) (x + ε - yR) := lt_min_iff.mpr ⟨dR1, dR2⟩
    exact (half_pos this)
  have subR : nbhd yR ρR ⊆ Set.Ioo x (x+ε) := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩
    have hle1 : ρR ≤ yR - x := by dsimp [ρR]; exact div_le_iff.mpr (by have := min_le_left _ _; nlinarith)
    have hle2 : ρR ≤ x + ε - yR := by dsimp [ρR]; exact div_le_iff.mpr (by have := min_le_right _ _; nlinarith)
    constructor
    · have : z > yR - ρR := hz1
      have : z > yR - (yR - x) := lt_of_lt_of_le this (by nlinarith [hle1])
      simpa using this
    · have : z < yR + ρR := hz2
      have : z < yR + (x + ε - yR) := lt_of_le_of_lt (by nlinarith [hle2]) this
      simpa using this
  -- uncountability in Mr at those inner neighbourhoods
  have uncL : ¬ (nbhd yL ρL ∩ Mr M).Countable :=
    nbhd_uncountable_in_Mr (M:=M) (x:=yL) (ε:=ρL) ⟨hyL_Mr.1, hyL_Mr.2⟩ ρLpos
  have uncR : ¬ (nbhd yR ρR ∩ Mr M).Countable :=
    nbhd_uncountable_in_Mr (M:=M) (x:=yR) (ε:=ρR) ⟨hyR_Mr.1, hyR_Mr.2⟩ ρRpos
  -- deduce halves in Mr are uncountable via monotonicity
  have hLeft_unc_Mr  : ¬ (LeftSlice (Mr M) x ε).Countable := by
    intro hcnt
    have : (nbhd yL ρL ∩ Mr M).Countable :=
      hcnt.mono (by intro z hz; rcases hz with ⟨hzI, hzMr⟩; exact ⟨subL hzI, hzMr⟩)
    exact uncL this
  have hRight_unc_Mr : ¬ (RightSlice (Mr M) x ε).Countable := by
    intro hcnt
    have : (nbhd yR ρR ∩ Mr M).Countable :=
      hcnt.mono (by intro z hz; rcases hz with ⟨hzI, hzMr⟩; exact ⟨subR hzI, hzMr⟩)
    exact uncR this
  -- remove the countable boundary set L∪R to pass from Mr to Mb
  have hBcnt : (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)).Countable :=
    (countable_LeftEmpty (Mr M)).union (countable_RightEmpty (Mr M))
  constructor
  · have : ¬ (Set.diff (LeftSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hLeft_unc_Mr hBcnt
    -- identify LeftSlice on Mb as that diff
    have : LeftSlice (Mb M) x ε = Set.diff (LeftSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)) := by
      ext y; constructor <;> intro hy
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩; exact ⟨⟨hyMr, h1, h2⟩, hyNB⟩
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩; exact ⟨⟨hyMr, hyNB⟩, h1, h2⟩
    simpa [this, Mb]
  · have : ¬ (Set.diff (RightSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hRight_unc_Mr hBcnt
    have : RightSlice (Mb M) x ε = Set.diff (RightSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)) := by
      ext y; constructor <;> intro hy
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩; exact ⟨⟨hyMr, h1, h2⟩, hyNB⟩
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩; exact ⟨⟨hyMr, hyNB⟩, h1, h2⟩
    simpa [this, Mb]

end TwoSidedCore
