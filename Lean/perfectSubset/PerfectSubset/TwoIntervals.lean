/-
Self‑contained, minimal file for the two‑interval reduction.
No references to other project files; should compile with `import Mathlib`.
Save as `PerfectSubset/TwoIntervals.lean`.
-/

import Mathlib

open Set

namespace PerfectSubset
namespace TwoIntervals

/-- One‑third length of the outer span `[x00, x11]`. -/
noncomputable def lambda0 (x00 x11 : ℝ) : ℝ := (1 : ℝ) / 3 * (x11 - x00)

/-- Data for the two‑interval restriction with your side conditions. -/
structure ThirdSplit (M : Set ℝ) where
  x00 x01 x10 x11 : ℝ
  mem_x00 : x00 ∈ M
  mem_x01 : x01 ∈ M
  mem_x10 : x10 ∈ M
  mem_x11 : x11 ∈ M
  le_left  : x00 ≤ x01
  le_right : x10 ≤ x11
  left_short  : x01 < x00 + lambda0 x00 x11
  right_short : x11 - lambda0 x00 x11 < x10
deriving Repr

/-- The restricted set `M₁ = M ∩ ( [x00,x01] ∪ [x10,x11] )`. -/
 def M1 (M : Set ℝ) (s : ThirdSplit M) : Set ℝ :=
  M ∩ (Icc s.x00 s.x01 ∪ Icc s.x10 s.x11)

/-- Membership expansion for `M1`. -/
 theorem mem_M1 {M : Set ℝ} {s : ThirdSplit M} {x : ℝ} :
    x ∈ M1 M s ↔ x ∈ M ∧ x ∈ (Icc s.x00 s.x01 ∪ Icc s.x10 s.x11) := Iff.rfl

/-- Trivial inclusion `M₁ ⊆ M`. -/
 theorem M1_subset_M {M : Set ℝ} (s : ThirdSplit M) : M1 M s ⊆ M := by
  intro x hx; exact hx.1

/-- Trivial inclusion into the union hull. -/
 theorem M1_subset_union {M : Set ℝ} (s : ThirdSplit M) :
    M1 M s ⊆ (Icc s.x00 s.x01 ∪ Icc s.x10 s.x11) := by
  intro x hx; exact hx.2

/-- All four endpoints belong to `M₁`. -/
 theorem x00_mem_M1 {M : Set ℝ} (s : ThirdSplit M) : s.x00 ∈ M1 M s := by
  refine And.intro s.mem_x00 ?_
  exact Or.inl ⟨le_rfl, s.le_left⟩

 theorem x01_mem_M1 {M : Set ℝ} (s : ThirdSplit M) : s.x01 ∈ M1 M s := by
  refine And.intro s.mem_x01 ?_
  exact Or.inl ⟨s.le_left, le_rfl⟩

 theorem x10_mem_M1 {M : Set ℝ} (s : ThirdSplit M) : s.x10 ∈ M1 M s := by
  refine And.intro s.mem_x10 ?_
  exact Or.inr ⟨le_rfl, s.le_right⟩

 theorem x11_mem_M1 {M : Set ℝ} (s : ThirdSplit M) : s.x11 ∈ M1 M s := by
  refine And.intro s.mem_x11 ?_
  exact Or.inr ⟨s.le_right, le_rfl⟩

/-- If the middle gap is wide enough, the two `Icc` blocks are separated. -/
 theorem gap_left_right {M : Set ℝ} (s : ThirdSplit M)
    (hmid : s.x00 + lambda0 s.x00 s.x11 ≤ s.x11 - lambda0 s.x00 s.x11) :
    s.x01 < s.x10 := by
  have h' : s.x00 + lambda0 s.x00 s.x11 < s.x10 := lt_of_le_of_lt hmid s.right_short
  exact lt_trans s.left_short h'

/-! ## Next steps: blocks, iteration, compact `Kₙ`, and an uncountability helper -/

namespace Next
open Set

/-- The union of the two kept closed intervals. -/
@[simp] def blockSet (s : ThirdSplit) : Set ℝ :=
  Icc s.x00 s.x01 ∪ Icc s.x10 s.x11

/-- `blockSet` is closed. -/
lemma isClosed_block (s : ThirdSplit) : IsClosed (blockSet s) := by
  simpa [blockSet] using (isClosed_Icc.union isClosed_Icc)

/-- `blockSet` is compact (finite union of compacts). -/
lemma isCompact_block (s : ThirdSplit) : IsCompact (blockSet s) := by
  simpa [blockSet] using (isCompact_Icc.union isCompact_Icc)

/-- The outer span as a single closed interval. -/
@[simp] def outer (s : ThirdSplit) : Set ℝ := Icc s.x00 s.x11

/-- If the middle gap is wide enough (the same hypothesis as in `gap_left_right`),
then each kept interval sits inside the outer span. -/
lemma block_subset_outer (s : ThirdSplit)
    (hmid : s.x00 + lambda0 s ≤ s.x11 - lambda0 s) :
    blockSet s ⊆ outer s := by
  intro x hx
  rcases hx with hx | hx
  · -- left block inside outer
    have hgap : s.x01 < s.x10 := gap_left_right s hmid
    have hx01_le_x11 : s.x01 ≤ s.x11 := le_trans (le_of_lt hgap) s.le_right
    exact And.intro hx.1 (le_trans hx.2 hx01_le_x11)
  · -- right block insi
end PerfectSubset



end TwoIntervals
end PerfectSubset
