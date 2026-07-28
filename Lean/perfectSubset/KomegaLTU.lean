/-
  PerfectSubset/KomegaLTU.lean

  LTU ⇒ NoIsolated (ohne Konstruktion):
  Wir formalisieren die von dir gewünschte, rein existentielle Brücke.
  Aus "lokal zweiseitig überabzählbar" folgt direkt: keine isolierten Punkte.

  *Wir bauen nichts*, wir wählen nur (klassisch) einen Punkt aus einem
   unüberabzählbaren (also nichtleeren) linken ε‑Fenster.
-/

import Mathlib

import PerfectSubset.KomegaPerfect  -- liefert `Stage.NoIsolated`

open Set

namespace Stage

/-- "Lokal zweiseitig überabzählbar":
    an jedem Punkt und in jedem ε‑Fenster sind *beide* Halbintervalle
    gegen `M` unüberabzählbar. -/
def LocallyTwoSidedUncountable (M : Set ℝ) : Prop :=
  ∀ x ∈ M, ∀ ε > 0,
    ¬ ((Ioo (x - ε) x) ∩ M).Countable ∧
    ¬ ((Ioo x (x + ε)) ∩ M).Countable

/-- **Existenzielle Brücke (ohne Konstruktion):**
    Aus `LocallyTwoSidedUncountable M` folgt sofort `NoIsolated M`.
    Beweisidee: Nimm `y` aus dem linken ε‑Fenster; dann `|y-x|<ε` und `y≠x`. -/
theorem noIsolated_of_LTU {M : Set ℝ}
    (hLTU : LocallyTwoSidedUncountable M) :
    NoIsolated M := by
  intro x hx ε hε
  classical
  -- linkes Fenster unüberabzählbar ⇒ nichtleer
  have hLeftUncnt : ¬ ((Ioo (x - ε) x) ∩ M).Countable := (hLTU x hx ε hε).1
  have hLeftNonempty : ((Ioo (x - ε) x) ∩ M).Nonempty := by
    by_contra hempty
    have hEq : ((Ioo (x - ε) x) ∩ M) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    have hCnt : ((Ioo (x - ε) x) ∩ M).Countable := by
      simp [hEq] 
    exact hLeftUncnt hCnt
  rcases hLeftNonempty with ⟨y, hy⟩
  rcases hy with ⟨hyI, hyM⟩
  have x_minus_eps_lt_y : x - ε < y := hyI.1
  have hy_lt_x : y < x := hyI.2
  have hy_ne : y ≠ x := ne_of_lt hy_lt_x
  -- |y - x| < ε
  have lower : -ε < y - x := by
    have := sub_lt_sub_right x_minus_eps_lt_y x
    -- (x - ε) - x < y - x  ⇒  -ε < y - x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have upper : y - x < ε := by
    have upper' : y - x < 0 := sub_lt_zero.mpr hy_lt_x
    exact lt_trans upper' hε
  have habs : |y - x| < ε := by
    simpa using (abs_lt.mpr ⟨lower, upper⟩)
  exact ⟨y, hyM, hy_ne, habs⟩

/-- Variante mit expliziter Nichtleere: praktisch, wenn man die Annahme gern
    zusammen mit LTU gebündelt weiterreicht. -/
 def LTU (M : Set ℝ) : Prop :=
  M.Nonempty ∧ LocallyTwoSidedUncountable M

@[simp] lemma LTU_empty : ¬ LTU (∅ : Set ℝ) := by
  simp [LTU]

/-- Aus `LTU M` folgt sofort `M.Nonempty`. -/
 theorem nonempty_of_LTU {M : Set ℝ} (h : LTU M) : M.Nonempty := h.1

/-- Komfort‑Wrapper: `LTU M` (mit Nichtleere) ⇒ `NoIsolated M`.
    Nutzt intern die punktweise Version `noIsolated_of_LTU`. -/
 theorem noIsolated_of_LTU' {M : Set ℝ} (h : LTU M) : NoIsolated M :=
  noIsolated_of_LTU h.2

end Stage
