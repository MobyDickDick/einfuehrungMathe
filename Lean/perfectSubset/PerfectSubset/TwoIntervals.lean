import Mathlib
open Set

noncomputable section

namespace PerfectSubset
namespace TwoIntervals

/-! # Two-interval reduction: clean, self-contained core + next steps

This file defines a tiny API around a two-interval restriction, plus a
compact "skeleton" iteration. No external project dependencies.
-/

/-- Data for the two-interval restriction with your side conditions.
`M` is a field (not a parameter at the head) for maximal robustness. -/
structure ThirdSplit where
  M : Set ℝ
  x00  : ℝ
  x01  : ℝ
  x10  : ℝ
  x11  : ℝ
  mem_x00 : x00 ∈ M
  mem_x01 : x01 ∈ M
  mem_x10 : x10 ∈ M
  mem_x11 : x11 ∈ M
  le_left  : x00 ≤ x01
  le_right : x10 ≤ x11
  -- side conditions: keep only the two "short" boundary pieces
  left_short  : x01 < x00 + (x11 - x00) / 3
  right_short : x11 - (x11 - x00) / 3 < x10

/-- One-third length of the outer span `[x00, x11]` (helper). -/
@[simp] def lambda0 (s : ThirdSplit) : ℝ := (s.x11 - s.x00) / 3

/-- The kept block set (union of two closed intervals). -/
@[simp] def blockSet (s : ThirdSplit) : Set ℝ :=
  Icc s.x00 s.x01 ∪ Icc s.x10 s.x11

/-- The restricted set `M₁ = M ∩ blockSet`. -/
@[simp] def M1 (s : ThirdSplit) : Set ℝ :=
  s.M ∩ blockSet s

/-- Membership expansion for `M1` (note the parentheses around the union!). -/
@[simp] theorem mem_M1 {s : ThirdSplit} {x : ℝ} :
  x ∈ M1 s ↔ x ∈ s.M ∧ x ∈ (Icc s.x00 s.x01 ∪ Icc s.x10 s.x11) := Iff.rfl

/-- Trivial inclusion `M₁ ⊆ M`. -/
@[simp] theorem M1_subset_M (s : ThirdSplit) : M1 s ⊆ s.M := by
  intro x hx; exact hx.1

/-- Trivial inclusion into the union hull. -/
@[simp] theorem M1_subset_union (s : ThirdSplit) :
  M1 s ⊆ (Icc s.x00 s.x01 ∪ Icc s.x10 s.x11) := by
  intro x hx; exact hx.2

/-- All four endpoints belong to `M₁`. -/
@[simp] theorem x00_mem_M1 (s : ThirdSplit) : s.x00 ∈ M1 s := by
  refine And.intro s.mem_x00 ?_
  exact Or.inl ⟨le_rfl, s.le_left⟩

@[simp] theorem x01_mem_M1 (s : ThirdSplit) : s.x01 ∈ M1 s := by
  refine And.intro s.mem_x01 ?_
  exact Or.inl ⟨s.le_left, le_rfl⟩

@[simp] theorem x10_mem_M1 (s : ThirdSplit) : s.x10 ∈ M1 s := by
  refine And.intro s.mem_x10 ?_
  exact Or.inr ⟨le_rfl, s.le_right⟩

@[simp] theorem x11_mem_M1 (s : ThirdSplit) : s.x11 ∈ M1 s := by
  refine And.intro s.mem_x11 ?_
  exact Or.inr ⟨s.le_right, le_rfl⟩

/-- If the middle gap is wide enough, the two `Icc` blocks are separated. -/
@[simp] theorem gap_left_right (s : ThirdSplit)
  (hmid : s.x00 + lambda0 s ≤ s.x11 - lambda0 s) :
  s.x01 < s.x10 := by
  have h' : s.x00 + lambda0 s < s.x10 := lt_of_le_of_lt hmid s.right_short
  exact lt_trans s.left_short h'

/-- Disjointness of the two closed blocks from a strict gap `x01 < x10`. -/
@[simp] theorem disjoint_Icc_of_gap (s : ThirdSplit) (h : s.x01 < s.x10) :
  Disjoint (Icc s.x00 s.x01) (Icc s.x10 s.x11) := by
  refine disjoint_left.mpr ?_
  intro x hx hx'
  rcases hx with ⟨hx0, hx1⟩
  rcases hx' with ⟨hx2, hx3⟩
  have : x < x := lt_of_lt_of_le (lt_of_le_of_lt hx1 h) hx2
  exact this.false

@[simp] theorem disjoint_blocks_of_midgap (s : ThirdSplit)
  (hmid : s.x00 + lambda0 s ≤ s.x11 - lambda0 s) :
  Disjoint (Icc s.x00 s.x01) (Icc s.x10 s.x11) :=
by exact disjoint_Icc_of_gap s (gap_left_right s hmid)

/-- `blockSet` is closed. -/
@[simp] lemma isClosed_block (s : ThirdSplit) : IsClosed (blockSet s) := by
  have h1 : IsClosed (Icc s.x00 s.x01) := isClosed_Icc
  have h2 : IsClosed (Icc s.x10 s.x11) := isClosed_Icc
  exact h1.union h2

/-- `blockSet` is compact. -/
@[simp] lemma isCompact_block (s : ThirdSplit) : IsCompact (blockSet s) := by
  have h1 : IsCompact (Icc s.x00 s.x01) := isCompact_Icc
  have h2 : IsCompact (Icc s.x10 s.x11) := isCompact_Icc
  exact h1.union h2

/-! ## Iteration: compact skeleton `Kₙ` -/

namespace Next

/-- A splitting scheme (sequence of two-interval restrictions). -/
structure Scheme where
  S : ℕ → ThirdSplit

/-- Compact skeleton: start with outer span of step 0, then intersect with blocks. -/
@[simp] def K (sch : Scheme) : ℕ → Set ℝ
  | 0     => Icc (sch.S 0).x00 (sch.S 0).x11
  | n+1   => K sch n ∩ blockSet (sch.S n)

@[simp] lemma K_succ_subset (sch : Scheme) (n : ℕ) :
  K sch (n+1) ⊆ K sch n := by intro x hx; exact hx.1

lemma isClosed_K (sch : Scheme) : ∀ n, IsClosed (K sch n)
  | 0     => by
      have h : IsClosed (Icc (sch.S 0).x00 (sch.S 0).x11) := isClosed_Icc
      exact h
  | n+1   => by
      have ih : IsClosed (K sch n) := isClosed_K sch n
      have hB : IsClosed (blockSet (sch.S n)) := isClosed_block (sch.S n)
      exact ih.inter hB

lemma isCompact_K (sch : Scheme) : ∀ n, IsCompact (K sch n)
  | 0     => by
      have h : IsCompact (Icc (sch.S 0).x00 (sch.S 0).x11) := isCompact_Icc
      exact h
  | n+1   => by
      have hK : IsCompact (K sch n) := isCompact_K sch n
      have hB : IsCompact (blockSet (sch.S n)) := isCompact_block (sch.S n)
      -- intersection of two compact sets is compact
      exact hK.inter hB

/-- Local uncountability on nondegenerate intervals. -/
@[simp] def LocallyUncountable (M : Set ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a < b → ¬ (M ∩ Icc a b).Countable

/-- If `M` is locally uncountable and both kept intervals are nondegenerate,
then `M₁` is uncountable. -/
lemma uncountable_M1_of_locally (s : ThirdSplit)
    (hL : s.x00 < s.x01) (hR : s.x10 < s.x11)
    (hLoc : LocallyUncountable s.M) :
    ¬ (M1 s).Countable := by
  -- left/right pieces
  let A : Set ℝ := s.M ∩ Icc s.x00 s.x01
  let B : Set ℝ := s.M ∩ Icc s.x10 s.x11
  have hA : ¬ A.Countable := by
    have : ¬ (s.M ∩ Icc s.x00 s.x01).Countable := hLoc hL
    simpa [A]
  have hB : ¬ B.Countable := by
    have : ¬ (s.M ∩ Icc s.x10 s.x11).Countable := hLoc hR
    simpa [B]
  intro hCnt
  have hA_sub : A ⊆ M1 s := by intro x hx; exact And.intro hx.1 (Or.inl hx.2)
  have hB_sub : B ⊆ M1 s := by intro x hx; exact And.intro hx.1 (Or.inr hx.2)
  have hAc : A.Countable := hCnt.mono hA_sub
  have hBc : B.Countable := hCnt.mono hB_sub
  exact hA hAc

end Next

end TwoIntervals
end PerfectSubset
