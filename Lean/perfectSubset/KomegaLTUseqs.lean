/-
  PerfectSubset/KomegaLTUSeqs.lean

  Aus der gebündelten Annahme `LTU M` (Nichtleere + lokal zweiseitig
  überabzählbar) gewinnen wir für **jedes** `x ∈ M` und **jedes**
  `n : ℕ` Punkte auf der linken bzw. rechten Seite, die in Abstand < 1/(n+1)
  von `x` liegen. Rein existentiell — wir *konstruieren* nichts, sondern
  wählen nur per klassischer Logik.
-/

import Mathlib

import PerfectSubset.KomegaLTU

open Set

namespace Stage

/-- Hilfsfunktion: Schrittweite `ε_n = 1/(n+1)`. -/
@[simp] noncomputable def eps (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma eps_pos : ∀ n, 0 < eps n := by
  intro n
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  simpa [eps] using inv_pos.mpr hpos

/-- **Links-Approximation:** Für `LTU M`, jeden Punkt `x ∈ M` und jedes `n` gibt es
    `y ∈ M` mit `y < x` und `|y - x| < eps n`. -/
lemma exists_left_approx_of_LTU {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) (n : ℕ) :
    ∃ y ∈ M, y ≠ x ∧ |y - x| < eps n ∧ y < x := by
  classical
  -- setze ε := 1/(n+1)
  let ε : ℝ := eps n
  have hε : ε > 0 := by simpa [ε, eps] using eps_pos n
  -- linkes Fenster ist unüberabzählbar ⇒ nichtleer ⇒ wähle y
  have hLeftUncnt : ¬ ((Ioo (x - ε) x) ∩ M).Countable := (h.2 x hx ε hε).1
  have hLeftNonempty : ((Ioo (x - ε) x) ∩ M).Nonempty := by
    by_contra hempty
    have hEq : ((Ioo (x - ε) x) ∩ M) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    have hCnt : ((Ioo (x - ε) x) ∩ M).Countable := by simp [hEq]
    exact hLeftUncnt hCnt
  rcases hLeftNonempty with ⟨y, hy⟩
  rcases hy with ⟨hyI, hyM⟩
  -- y ≠ x und |y-x| < ε
  have y_lt_x : y < x := hyI.2
  have y_ne_x : y ≠ x := ne_of_lt y_lt_x
  have lower : -ε < y - x := by
    -- (x - ε) < y ⇒ (x - ε) - x < y - x ⇒ -ε < y - x
    have := sub_lt_sub_right hyI.1 x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have upper : y - x < ε := by
    have : y - x < 0 := sub_lt_zero.mpr y_lt_x
    exact lt_trans this hε
  have hdist : |y - x| < ε := by simpa using (abs_lt.mpr ⟨lower, upper⟩)
  -- zurück in eps n
  simpa [ε] using ⟨y, hyM, y_ne_x, hdist, y_lt_x⟩

/-- **Rechts-Approximation:** Für `LTU M`, jeden Punkt `x ∈ M` und jedes `n` gibt es
    `y ∈ M` mit `x < y` und `|y - x| < eps n`. -/
lemma exists_right_approx_of_LTU {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) (n : ℕ) :
    ∃ y ∈ M, y ≠ x ∧ |y - x| < eps n ∧ x < y := by
  classical
  -- ε := 1/(n+1)
  let ε : ℝ := eps n
  have hε : ε > 0 := by simpa [ε, eps] using eps_pos n
  -- rechtes Fenster unüberabzählbar ⇒ nichtleer
  have hRightUncnt : ¬ ((Ioo x (x + ε)) ∩ M).Countable := (h.2 x hx ε hε).2
  have hRightNonempty : ((Ioo x (x + ε)) ∩ M).Nonempty := by
    by_contra hempty
    have hEq : ((Ioo x (x + ε)) ∩ M) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    have hCnt : ((Ioo x (x + ε)) ∩ M).Countable := by simp [hEq]
    exact hRightUncnt hCnt
  rcases hRightNonempty with ⟨y, hy⟩
  rcases hy with ⟨hyI, hyM⟩
  -- x ≠ y und |y-x| < ε
  have x_lt_y : x < y := hyI.1
  have y_ne_x : y ≠ x := ne_of_gt x_lt_y
  have lower : 0 < y - x := sub_pos.mpr x_lt_y
  have upper : y - x < ε := by
    have : y < x + ε := hyI.2
    have := sub_lt_iff_lt_add'.mpr this
    simpa using this
  have hdist : |y - x| < ε := by
    have : 0 ≤ y - x := le_of_lt lower
    simpa [abs_of_nonneg this] using upper
  simpa [ε] using ⟨y, hyM, y_ne_x, hdist, x_lt_y⟩

end Stage
