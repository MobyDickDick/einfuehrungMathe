/-
Two-sided thick core via removing the open "thin" part M₀ and the one-sided empty boundary points.
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

/-- Open symmetric ε-neighbourhood as an open interval. -/
@[simp] def nbhd (x ε : ℝ) : Set ℝ := Set.Ioo (x - ε) (x + ε)

/-- Left and right half-intervals, restricted to a set `A`. -/
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
  -- rational intervals as indices
  let J : ℚ × ℚ → Set ℝ := fun p => Set.Ioo (p.1 : ℝ) (p.2 : ℝ)

  -- cover: each x ∈ M0∩M lies in some rational (a,b)⊆nbhd x ε with (J(a,b) ∩ M) countable
  have hcov :
      M0 M ∩ M ⊆ ⋃ p : ℚ × ℚ,
        (if (J p ∩ M).Countable then (J p ∩ M) else (∅ : Set ℝ)) := by
    intro x hx
    rcases hx with ⟨hxM0, hxM⟩
    rcases hxM0 with ⟨ε, hε, hcnt⟩
    have hxlt : x - ε < x := by simpa using sub_lt_self (a := x) hε
    have hxgt : x < x + ε := by simpa using lt_add_of_pos_right x hε
    rcases exists_rat_btwn hxlt with ⟨a, ha1, ha2⟩
    rcases exists_rat_btwn hxgt with ⟨b, hb1, hb2⟩
    -- J(a,b) ⊆ nbhd x ε
    have hsub : J (a,b) ⊆ nbhd x ε := by
      intro y hy
      exact ⟨lt_trans ha1 hy.1, lt_trans hy.2 hb2⟩
    -- then (J(a,b) ∩ M) is countable
    have hcnt' : (J (a,b) ∩ M).Countable :=
      hcnt.mono (by intro y hy; exact ⟨hsub hy.1, hy.2⟩)
    -- x ∈ J(a,b) ∩ M
    have hxmem : x ∈ J (a,b) ∩ M := ⟨⟨by simpa using ha2, by simpa using hb1⟩, hxM⟩
    -- put into the union; the if-branch chooses J(a,b)∩M here
    refine mem_iUnion.mpr ?_
    refine ⟨(a,b), ?_⟩
    simpa [J, hcnt'] using hxmem

  -- union of countably many countable sets is countable
  have hUnionCnt :
      (⋃ p : ℚ × ℚ, (if (J p ∩ M).Countable then (J p ∩ M) else (∅ : Set ℝ))).Countable := by
    refine countable_iUnion (fun p => ?_)
    by_cases hp : (J p ∩ M).Countable
    · simpa [hp] using hp
    · simpa [hp] using (countable_empty : (∅ : Set ℝ).Countable)

  exact hUnionCnt.mono hcov

/-! ### Uncountability of small neighbourhoods in Mr -/

lemma nbhd_uncountable_in_Mr (M : Set ℝ) {x ε : ℝ}
  (hx : x ∈ Mr M) (hε : ε > 0) : ¬ ((nbhd x ε ∩ Mr M).Countable) := by
  classical
  have hxM : x ∈ M := hx.1
  have hxnot : x ∉ M0 M := hx.2
  -- if (nbhd x ε ∩ M) were countable, x ∈ M0 M
  have hx' : ¬ (nbhd x ε ∩ M).Countable := by
    intro hcnt
    exact hxnot ⟨ε, hε, hcnt⟩
  -- subtract the countable (M0∩M)
  have hC : (M0 M ∩ M).Countable := countable_M0_inter_M M
  -- identify (nbhd ∩ Mr) as a set difference
  have hEq : nbhd x ε ∩ Mr M = Set.diff (nbhd x ε ∩ M) (M0 M ∩ M) := by
    ext y; constructor <;> intro hy
    · -- → direction
      rcases hy with ⟨hyI, hyMr⟩
      exact ⟨⟨hyI, hyMr.1⟩, by
        intro hmem
        exact hyMr.2 hmem.1⟩
    · -- ← direction
      rcases hy with ⟨⟨hyI, hyM⟩, hyNot⟩
      exact ⟨hyI, ⟨hyM, by
        intro h0
        exact hyNot ⟨h0, hyM⟩⟩⟩
  -- conclude
  have : ¬ (Set.diff (nbhd x ε ∩ M) (M0 M ∩ M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hx' hC
  simpa [hEq] using this

/-! ### One-sided empty boundary sets in `A` and their countability -/

@[simp] def RightEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo x (x + δ) ∩ A) = ∅ }
@[simp] def LeftEmpty (A : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ A ∧ ∃ δ > 0, (Set.Ioo ((x) - δ) x ∩ A) = ∅ }

/-- Countability of right-empty boundary points of `A` via an injection into ℚ. -/
lemma countable_RightEmpty (A : Set ℝ) : (RightEmpty A).Countable := by
  classical
  -- For each x, pick a rational q with x < q < x+δ where (x,x+δ)∩A = ∅.
  have hxq : ∀ x : {x : ℝ // x ∈ RightEmpty A},
      ∃ q : ℚ, ∃ δ > 0, (x : ℝ) < q ∧ (q : ℝ) < (x : ℝ) + δ ∧ (Set.Ioo (x : ℝ) ((x : ℝ) + δ) ∩ A) = ∅ := by
    intro x; rcases x.property with ⟨hxA, ⟨δ, hpos, hemp⟩⟩
    have hxlt : (x : ℝ) < (x : ℝ) + δ := by simpa using lt_add_of_pos_right (x : ℝ) hpos
    rcases exists_rat_btwn hxlt with ⟨q, h1, h2⟩
    exact ⟨q, δ, hpos, h1, h2, hemp⟩
  -- local choice map to ℚ
  let f : {x : ℝ // x ∈ RightEmpty A} → ℚ := fun x => Classical.choose (hxq x)
  have f_spec : ∀ x, ∃ δ > 0,
      (x : ℝ) < f x ∧ (f x : ℝ) < (x : ℝ) + δ ∧ (Set.Ioo (x : ℝ) ((x : ℝ) + δ) ∩ A) = ∅ := by
    intro x; rcases Classical.choose_spec (hxq x) with ⟨δ, hpos, h1, h2, hemp⟩
    exact ⟨δ, hpos, h1, h2, hemp⟩

  -- Injectivity without wlog: order-separate using emptiness.
  have finj : Function.Injective f := by
    intro x y hxy
    have hxA : (x : ℝ) ∈ A := (x.property).1
    have hyA : (y : ℝ) ∈ A := (y.property).1
    rcases f_spec x with ⟨δx, hxpos, hxltq, hqltx, hxemp⟩
    rcases f_spec y with ⟨δy, hypos, hyltq, hqlty, hyemp⟩
    -- equality in ℝ
    have hxyℝ : (f x : ℝ) = (f y : ℝ) := by
      simpa using congrArg (fun t : ℚ => (t : ℝ)) hxy
    by_contra hne
    -- compare x and y on ℝ
    have hxy_ne : (x : ℝ) ≠ (y : ℝ) := by
      intro h
      apply hne
      apply Subtype.ext
      simpa using h
    cases lt_or_gt_of_ne hxy_ne with
    | inl hxylt =>
      -- From emptiness at x: since y ∈ A and x < y, we must have x+δx ≤ y.
      have sep_xy : (x : ℝ) + δx ≤ (y : ℝ) := by
        by_contra hylt
        -- then x < y < x+δx, contradiction
        have : (y : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ) + δx) := ⟨hxylt, lt_of_not_ge hylt⟩
        have : (y : ℝ) ∈ Set.Ioo (x : ℝ) ((x : ℝ) + δx) ∩ A := ⟨this, hyA⟩
        simpa [hxemp] using this
      have fx_lt_y : (f x : ℝ) < (y : ℝ) := lt_of_lt_of_le hqltx sep_xy
      have y_lt_fy : (y : ℝ) < (f y : ℝ) := hyltq
      exact (ne_of_lt (lt_trans fx_lt_y y_lt_fy)) hxyℝ
    | inr hyltx =>
      -- symmetric: use emptiness at y
      have sep_yx : (y : ℝ) + δy ≤ (x : ℝ) := by
        by_contra hxlt
        have : (x : ℝ) ∈ Set.Ioo (y : ℝ) ((y : ℝ) + δy) := ⟨hyltx, lt_of_not_ge hxlt⟩
        have : (x : ℝ) ∈ Set.Ioo (y : ℝ) ((y : ℝ) + δy) ∩ A := ⟨this, hxA⟩
        simpa [hyemp] using this
      have fy_lt_x : (f y : ℝ) < (x : ℝ) := lt_of_lt_of_le hqlty sep_yx
      have x_lt_fx : (x : ℝ) < (f x : ℝ) := hxltq
      exact (ne_of_lt (lt_trans fy_lt_x x_lt_fx)) (hxyℝ.symm)

  -- Countability from injectivity into ℚ (countable)
  refine Set.countable_iff.mpr ?_
  refine ⟨fun x : {x : ℝ // x ∈ RightEmpty A} => Encodable.encode (f x), ?_⟩
  intro x y h
  have : f x = f y := Encodable.encode_injective h
  exact finj this

/-- Countability of left-empty boundary points (mirror of the right version). -/
lemma countable_LeftEmpty (A : Set ℝ) : (LeftEmpty A).Countable := by
  classical
  have hxq : ∀ x : {x : ℝ // x ∈ LeftEmpty A},
      ∃ q : ℚ, ∃ δ > 0, (x : ℝ) - δ < q ∧ (q : ℝ) < (x : ℝ) ∧ (Set.Ioo ((x : ℝ) - δ) (x : ℝ) ∩ A) = ∅ := by
    intro x; rcases x.property with ⟨hxA, ⟨δ, hpos, hemp⟩⟩
    have hxlt : (x : ℝ) - δ < (x : ℝ) := by simpa using sub_lt_self (a:=(x:ℝ)) hpos
    rcases exists_rat_btwn hxlt with ⟨q, h1, h2⟩
    exact ⟨q, δ, hpos, h1, h2, hemp⟩
  let f : {x : ℝ // x ∈ LeftEmpty A} → ℚ := fun x => Classical.choose (hxq x)
  have f_spec : ∀ x, ∃ δ > 0,
      (x : ℝ) - δ < f x ∧ (f x : ℝ) < (x : ℝ) ∧ (Set.Ioo ((x : ℝ) - δ) (x : ℝ) ∩ A) = ∅ := by
    intro x; rcases Classical.choose_spec (hxq x) with ⟨δ, hpos, h1, h2, hemp⟩
    exact ⟨δ, hpos, h1, h2, hemp⟩

  -- Injectivity (left version), again without wlog
  have finj : Function.Injective f := by
    intro x y hxy
    have hxA : (x : ℝ) ∈ A := (x.property).1
    have hyA : (y : ℝ) ∈ A := (y.property).1
    rcases f_spec x with ⟨δx, hxpos, hqxlt, hltx, hxemp⟩
    rcases f_spec y with ⟨δy, hypos, hqylt, hlty, hyemp⟩
    have hxyℝ : (f x : ℝ) = (f y : ℝ) := by
      simpa using congrArg (fun t : ℚ => (t : ℝ)) hxy
    by_contra hne
    have hxy_ne : (x : ℝ) ≠ (y : ℝ) := by
      intro h
      apply hne
      apply Subtype.ext
      simpa using h
    cases lt_or_gt_of_ne hxy_ne with
    | inl hxylt =>
      -- y < x? nein: this case is x < y (since hxylt : (x:ℝ) < (y:ℝ)).
      -- Use emptiness at y on the left of y: since x ∈ A and x < y, we get x ≤ y - δy.
      have sep_xy : (x : ℝ) ≤ (y : ℝ) - δy := by
        by_contra hxgt
        have : (x : ℝ) ∈ Set.Ioo ((y : ℝ) - δy) (y : ℝ) := ⟨lt_of_not_ge hxgt, lt_of_le_of_lt le_rfl hxylt⟩
        have : (x : ℝ) ∈ Set.Ioo ((y : ℝ) - δy) (y : ℝ) ∩ A := ⟨this, hxA⟩
        simpa [hyemp] using this
      -- then (f x) < x ≤ y - δy < y, and (f y) < y; we will separate via the other side:
      -- Actually, stronger: from hqxlt: (x - δx) < f x, so f x ≤ y - δy does NOT hold a priori.
      -- Instead, use emptiness at x to place (f y) relative to x by symmetry.
      -- Better: we separate using the endpoint orders:
      have fx_lt_y : (f x : ℝ) < (y : ℝ) := lt_trans hltx (le_of_lt hxylt)
      have x_lt_fy : (x : ℝ) < (f y : ℝ) := lt_of_le_of_lt sep_xy hlty
      -- Now (f x) < y and x < (f y). This already rules out equality (two numbers on opposite sides unless x=y).
      -- Combine via trichotomy: from fx<y and x<fy and x<y, we still need a direct contradiction:
      -- Use: if fx = fy, then fx < y and y ≤ fx is impossible since hlty says y > fy = fx.
      have y_lt_fy : (y : ℝ) < (f y : ℝ) := hlty
      exact (ne_of_lt (lt_trans fx_lt_y y_lt_fy)) hxyℝ
    | inr hyltx =>
      -- case (y : ℝ) < (x : ℝ)
      -- Use emptiness at x (left): since y ∈ A and y < x, we must have y ≤ x - δx.
      have sep_yx : (y : ℝ) ≤ (x : ℝ) - δx := by
        by_contra hygt
        have : (y : ℝ) ∈ Set.Ioo ((x : ℝ) - δx) (x : ℝ) := ⟨lt_of_not_ge hygt, lt_of_le_of_lt le_rfl hyltx⟩
        have : (y : ℝ) ∈ Set.Ioo ((x : ℝ) - δx) (x : ℝ) ∩ A := ⟨this, hyA⟩
        simpa [hxemp] using this
      have fy_lt_x : (f y : ℝ) < (x : ℝ) := lt_of_lt_of_le hqylt (le_of_lt hyltx)
      have y_lt_fx : (y : ℝ) < (f x : ℝ) := by
        have : (x : ℝ) - δx < (f x : ℝ) := hqxlt
        exact lt_of_le_of_lt sep_yx this
      -- So (f y) < x and y < (f x). With (y<x), we get (f y) < (f x), contradicting equality.
      exact (ne_of_lt (lt_of_lt_of_le fy_lt_x (le_of_lt y_lt_fx))) (hxyℝ.symm)

  -- Countability from injectivity into ℚ
  refine Set.countable_iff.mpr ?_
  refine ⟨fun x : {x : ℝ // x ∈ LeftEmpty A} => Encodable.encode (f x), ?_⟩
  intro x y h
  have : f x = f y := Encodable.encode_injective h
  exact finj this

/-! ### Build the two-sided thick core -/

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
  have hxnotL : x ∉ LeftEmpty (Mr M) := fun h => hxNotB (Or.inl h)
  have hxnotR : x ∉ RightEmpty (Mr M) := fun h => hxNotB (Or.inr h)
  -- For all ε>0 the halves in Mr are nonempty (otherwise x ∈ Left/RightEmpty)
  have exL : ∃ y, y ∈ Mr M ∧ x - ε < y ∧ y < x := by
    have : (Set.Ioo (x-ε) x ∩ Mr M) ≠ ∅ := by
      by_contra hempty
      have : x ∈ LeftEmpty (Mr M) :=
        ⟨hxMr, ⟨ε, hε, by simpa [LeftEmpty, Set.eq_empty_iff_forall_notMem] using hempty⟩⟩
      exact hxnotL this
    rcases Set.nonempty_iff_ne_empty.mpr this with ⟨y, hy⟩
    rcases hy with ⟨hyI, hyMr⟩
    exact ⟨y, hyMr, hyI.1, hyI.2⟩
  have exR : ∃ y, y ∈ Mr M ∧ x < y ∧ y < x + ε := by
    have : (Set.Ioo x (x+ε) ∩ Mr M) ≠ ∅ := by
      by_contra hempty
      have : x ∈ RightEmpty (Mr M) :=
        ⟨hxMr, ⟨ε, hε, by simpa [RightEmpty, Set.eq_empty_iff_forall_notMem] using hempty⟩⟩
      exact hxnotR this
    rcases Set.nonempty_iff_ne_empty.mpr this with ⟨y, hy⟩
    rcases hy with ⟨hyI, hyMr⟩
    exact ⟨y, hyMr, hyI.1, hyI.2⟩
  rcases exL with ⟨yL, hyL_Mr, hL1, hL2⟩
  rcases exR with ⟨yR, hyR_Mr, hR1, hR2⟩

  -- radii that sit inside the halves (no division tricks)
  have dL1 : 0 < yL - (x - ε) := sub_pos.mpr (by linarith)
  have dL2 : 0 < x - yL := sub_pos.mpr hL2
  let ρL : ℝ := min (yL - (x - ε)) (x - yL)
  have ρLpos : ρL > 0 := lt_min_iff.mpr ⟨dL1, dL2⟩
  have subL : nbhd yL ρL ⊆ Set.Ioo (x-ε) x := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩
    have h1 : x - ε ≤ yL - ρL := by
      have : ρL ≤ yL - (x - ε) := min_le_left _ _
      linarith
    have h2 : yL + ρL ≤ x := by
      have : ρL ≤ x - yL := min_le_right _ _
      linarith
    exact ⟨lt_of_le_of_lt h1 hz1, lt_of_lt_of_le hz2 h2⟩

  have dR1 : 0 < yR - x := sub_pos.mpr hR1
  have dR2 : 0 < x + ε - yR := sub_pos.mpr (by linarith)
  let ρR : ℝ := min (yR - x) (x + ε - yR)
  have ρRpos : ρR > 0 := lt_min_iff.mpr ⟨dR1, dR2⟩
  have subR : nbhd yR ρR ⊆ Set.Ioo x (x+ε) := by
    intro z hz; rcases hz with ⟨hz1, hz2⟩
    have h1 : x ≤ yR - ρR := by
      have : ρR ≤ yR - x := min_le_left _ _
      linarith
    have h2 : yR + ρR ≤ x + ε := by
      have : ρR ≤ x + ε - yR := min_le_right _ _
      linarith
    exact ⟨lt_of_le_of_lt h1 hz1, lt_of_lt_of_le hz2 h2⟩

  -- uncountability in Mr at those inner neighbourhoods
  have uncL : ¬ (nbhd yL ρL ∩ Mr M).Countable :=
    nbhd_uncountable_in_Mr (M:=M) (x:=yL) (ε:=ρL) ⟨hyL_Mr.1, hyL_Mr.2⟩ ρLpos
  have uncR : ¬ (nbhd yR ρR ∩ Mr M).Countable :=
    nbhd_uncountable_in_Mr (M:=M) (x:=yR) (ε:=ρR) ⟨hyR_Mr.1, hyR_Mr.2⟩ ρRpos

  -- deduce halves in Mr are uncountable via monotonicity (subset-of-left/right slices)
  have hLeft_unc_Mr  : ¬ (LeftSlice (Mr M) x ε).Countable := by
    intro hcnt
    have sub_to_LeftSlice : (nbhd yL ρL ∩ Mr M) ⊆ LeftSlice (Mr M) x ε := by
      intro z hz
      rcases hz with ⟨hzI, hzMr⟩
      have hI := subL hzI
      exact ⟨hzMr, hI.1, hI.2⟩
    exact uncL (hcnt.mono sub_to_LeftSlice)
  have hRight_unc_Mr : ¬ (RightSlice (Mr M) x ε).Countable := by
    intro hcnt
    have sub_to_RightSlice : (nbhd yR ρR ∩ Mr M) ⊆ RightSlice (Mr M) x ε := by
      intro z hz
      rcases hz with ⟨hzI, hzMr⟩
      have hI := subR hzI
      exact ⟨hzMr, hI.1, hI.2⟩
    exact uncR (hcnt.mono sub_to_RightSlice)

  -- remove the countable boundary set L∪R to pass from Mr to Mb
  have hBcnt : (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)).Countable :=
    (countable_LeftEmpty (Mr M)).union (countable_RightEmpty (Mr M))
  constructor
  · -- left side on Mb
    have : ¬ (Set.diff (LeftSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hLeft_unc_Mr hBcnt
    have hEq :
        LeftSlice (Mb M) x ε
        = Set.diff (LeftSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)) := by
      ext y; constructor <;> intro hy
      · rcases hy with ⟨hyMb, h1, h2⟩
        rcases hyMb with ⟨hyMr, hyNB⟩
        exact ⟨⟨hyMr, h1, h2⟩, hyNB⟩
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩
        exact ⟨⟨hyMr, hyNB⟩, h1, h2⟩
    simpa [hEq, Mb]
  · -- right side on Mb
    have : ¬ (Set.diff (RightSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M))).Countable :=
      not_countable_diff_of_not_countable_of_countable hRight_unc_Mr hBcnt
    have hEq :
        RightSlice (Mb M) x ε
        = Set.diff (RightSlice (Mr M) x ε) (LeftEmpty (Mr M) ∪ RightEmpty (Mr M)) := by
      ext y; constructor <;> intro hy
      · rcases hy with ⟨hyMb, h1, h2⟩
        rcases hyMb with ⟨hyMr, hyNB⟩
        exact ⟨⟨hyMr, h1, h2⟩, hyNB⟩
      · rcases hy with ⟨⟨hyMr, h1, h2⟩, hyNB⟩
        exact ⟨⟨hyMr, hyNB⟩, h1, h2⟩
    simpa [hEq, Mb]

end TwoSidedCore
