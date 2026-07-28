import Mathlib

noncomputable section

namespace PerfectSubset
namespace SumNonNeg

variable {α : Type*}

/-- Supremum über alle endlichen Teilsummen von `f` auf `P` (Werte in `ENNReal`). -/
def g (f : α → ENNReal) (P : Set α) : ENNReal :=
  by
    classical
    exact
      ⨆ s : {s : Finset α // (↑s : Set α) ⊆ P},
        Finset.sum s.1 (fun e => f e)

/-- Charakterisierung: `g f P = 0` genau dann, wenn alle Summanden auf `P` Null sind. -/
theorem g_eq_zero_iff (f : α → ENNReal) (P : Set α) :
    g f P = 0 ↔ ∀ e ∈ P, f e = 0 := by
  classical
  constructor
  · -- (→)
    intro h0 e heP
    -- {e} ⊆ P
    have hsubset : (({e} : Finset α) : Set α) ⊆ P := by
      intro x hx
      have hx' : x = e := by simpa using (Finset.mem_singleton.mp hx)
      simpa [hx'] using heP
    -- f e ≤ g f P über die Einermenge
    have hle_sum :
        Finset.sum ({e} : Finset α) (fun x => f x) ≤ g f P :=
      le_iSup_of_le ⟨({e} : Finset α), hsubset⟩ (le_of_eq rfl)
    have hle_fe : f e ≤ g f P := by
      simpa [Finset.sum_singleton] using hle_sum
    -- mit h0 folgt f e ≤ 0, also Gleichheit
    have hle0 : f e ≤ 0 := by simpa [h0] using hle_fe
    exact le_antisymm hle0 bot_le
  · -- (←)
    intro h
    refine le_antisymm ?_ bot_le
    refine iSup_le ?_
    intro s
    -- punktweise Nullheit → Summe 0
    have hzero : ∀ x ∈ s.1, f x = 0 := by
      intro x hx
      have : x ∈ P := s.2 (by simpa using hx)
      exact h x this
    have hcongr :
        Finset.sum s.1 (fun x => f x)
          = Finset.sum s.1 (fun _ => (0 : ENNReal)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx; simp [hzero x hx]
    have hsum0 :
        Finset.sum s.1 (fun x => f x) = 0 := by
      -- hier 'simp' statt 'simpa'
      have : Finset.sum s.1 (fun _ => (0 : ENNReal)) = 0 := by
        simp
      simp [hcongr]
    simp [hsum0]

/-- Bequemer Wrapper für `f : α → NNReal`. -/
def gNN (f : α → NNReal) (P : Set α) : ENNReal :=
  g (fun a => (f a : ENNReal)) P

theorem gNN_eq_zero_iff (f : α → NNReal) (P : Set α) :
    gNN f P = 0 ↔ ∀ e ∈ P, f e = 0 := by
  classical
  simpa [gNN] using
    (g_eq_zero_iff (f := fun a => (f a : ENNReal)) P)

/-- Beispiel: α = Set ℝ. Dank lokaler `classical`-Nutzung brauchen wir hier
keine explizite `DecidableEq`-Instanz mehr. -/
example :
    ∀ (f : Set ℝ → NNReal) (P : Set (Set ℝ)),
      gNN f P = 0 ↔ ∀ e ∈ P, f e = 0 := by
  intro f P
  simpa using gNN_eq_zero_iff (α := Set ℝ) f P

end SumNonNeg
end PerfectSubset
