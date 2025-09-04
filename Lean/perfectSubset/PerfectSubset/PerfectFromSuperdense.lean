-- Superdense/Phase0.lean
import Mathlib

open Set

/-- Lokal *zweiseitig* superdicht in ℝ. -/
def TwoSidedSuperdense (M : Set ℝ) : Prop :=
  ¬ M.Countable ∧
  ∀ ⦃x ε : ℝ⦄, x ∈ M → 0 < ε →
    ((M ∩ Set.Ioo (x - ε) x).Infinite ∧
     (M ∩ Set.Ioo x (x + ε)).Infinite)
