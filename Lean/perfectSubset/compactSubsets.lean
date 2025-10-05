/-
  PerfectSubset/compactSubsets.lean
  Neuaufbau: robuste Hilfslemmas und Utilities für kompakte Teilmengen,
  Filter-Argumente an atTop und reelle ε-Umformungen.

  Ziel: Beseitigt gemeldete Fehler:
   - ¬ s.Nonempty vs. ∀ x, x ∉ s  /  Set.eq_empty_iff_forall_notMem
   - Unknown constant Set.mem_setLike
   - ℝ vs. ℕ bei Folgen l n
   - Filter.Eventually.of_forall statt Filter.eventually_of_forall
   - exists_nat_one_div_lt  (ohne .mpr)
   - one_div_* Lemmas ohne .mpr / korrekte < / ≤ Handhabung
   - sub_lt_iff_lt_add', |l n - x| < ε via abs_lt.mpr

  Autor: Markus + ChatGPT (Skeleton)
-/

import Mathlib

open Set Filter
open scoped Topology BigOperators

namespace PerfectSubset

/-! # Abschnitt 1: Mengen-Utilities -/

section SetBasics

variable {α : Type*} {s : Set α}

/-- Klassische Form: `¬ s.Nonempty` ↔ `s = ∅`. -/
lemma not_nonempty_iff_eq_empty : ¬ s.Nonempty ↔ s = (∅ : Set α) := by
  simp [Set.not_nonempty_iff_eq_empty]

/-- Aus `¬ s.Nonempty` bekommt man bequem `s = ∅`. -/
lemma eq_empty_of_not_nonempty (h : ¬ s.Nonempty) : s = (∅ : Set α) := by
  simpa [Set.not_nonempty_iff_eq_empty] using h

/-- Aus `¬ s.Nonempty` folgt `∀ x, x ∉ s`. -/
lemma forall_not_mem_of_not_nonempty (h : ¬ s.Nonempty) : ∀ x, x ∉ s := by
  have h₀ : s = (∅ : Set α) := eq_empty_of_not_nonempty (s := s) h
  intro x; simp [h₀]

/-- Bequeme Variante: `s = ∅` ↔ `∀ x, x ∉ s`. -/
lemma eq_empty_iff_forall_notMem : s = (∅ : Set α) ↔ (∀ x, x ∉ s) := by
  simp [Set.eq_empty_iff_forall_notMem]

end SetBasics


/-! # Abschnitt 2: Nat-Cast und einfache Realklemmer -/

section NatCastReal

/-- Hilfslemma: Für jedes `N : ℕ` gilt `0 < (N : ℝ) + 1`. -/
lemma add_one_pos_of_nat (N : ℕ) : 0 < (N : ℝ) + 1 := by
  have h0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have h1 : 0 < (1 : ℝ) := by norm_num
  exact add_pos_of_nonneg_of_pos h0 h1

/-- Aus `N ≤ n` folgt `(N:ℝ)+1 ≤ (n:ℝ)+1`. -/
lemma nat_cast_add_one_mono {N n : ℕ} (h : N ≤ n) :
    (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
  have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  simpa using add_le_add_right this 1

/-- Monotonie von `x ↦ 1/x` auf `(0, ∞)` in der üblichen Form. -/
lemma one_div_le_one_div_of_le_nat {N n : ℕ} (h : N ≤ n) :
    1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
  have hpos : 0 < (N : ℝ) + 1 := add_one_pos_of_nat N
  have hle  : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := nat_cast_add_one_mono h
  exact one_div_le_one_div_of_le hpos hle

end NatCastReal


/-! # Abschnitt 3: Filter an `atTop` für `1/(n+1)` -/

section EventuallyOneDiv

/-- Standard: Für jedes `ε>0` gilt irgendwann `1/(n+1) < ε`. -/
lemma eventually_one_div_succ_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 / (n+1 : ℝ) < ε := by
  -- Mathlib-Lemma:
  -- `exists_nat_one_div_lt : 0 < ε → ∃ N, 1/(N+1) < ε`
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine (eventually_atTop.2 ?_)
  refine ⟨N, ?_⟩
  intro n hn
  -- Monotonie: 1/(n+1) ≤ 1/(N+1) < ε
  have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le_nat (N := N) (n := n) hn
  exact lt_of_le_of_lt hmono hN

/-- Auch als `≤ ε`-Variante (nützlich bei geschlossenen Schranken). -/
lemma eventually_one_div_succ_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 / (n+1 : ℝ) ≤ ε := by
  have : ∀ᶠ n : ℕ in atTop, 1 / (n+1 : ℝ) < ε := eventually_one_div_succ_lt (ε := ε) hε
  exact this.mono (by intro n hn; exact le_of_lt hn)

end EventuallyOneDiv


/-! # Abschnitt 4: Reelle `abs`-Umformungen ohne `.mpr` -/

section RealAbsTricks

variable {x y ε : ℝ}

/-- Aus `y < x` und `x - y < ε` folgt `|y - x| < ε`. -/
lemma abs_sub_of_right_lt (hyr : y < x) (h : x - y < ε) : |y - x| < ε := by
  have hx0 : 0 ≤ x - y := sub_nonneg.mpr (le_of_lt hyr)
  have : |x - y| = x - y := abs_of_nonneg hx0
  simpa [abs_sub_comm, this] using h

/-- Aus `x < y` und `y - x < ε` folgt `|y - x| < ε`. -/
lemma abs_sub_of_left_lt (hxl : x < y) (h : y - x < ε) : |y - x| < ε := by
  have hx0 : 0 ≤ y - x := sub_nonneg.mpr (le_of_lt hxl)
  have : |y - x| = y - x := abs_of_nonneg hx0
  simpa [this] using h

/-- Komfortform: Aus `x - ε < y` und `y < x + ε` folgt `|y - x| < ε`. -/
lemma abs_lt_of_between (h₁ : x - ε < y) (h₂ : y < x + ε) : |y - x| < ε := by
  -- rechte Seite: `y < x + ε` ⇒ `y - x < ε`
  have hr : y - x < ε := by
    have := sub_lt_iff_lt_add'.mpr h₂
    -- `sub_lt_iff_lt_add'` : `a - b < c ↔ a < c + b`
    -- Wir brauchen `y - x < ε` ; aus `y < x + ε` folgt direkt:
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- linke Seite: `x - ε < y` ⇒ `x - y < ε` ⇒ |y - x| < ε
  have hl : x - y < ε := by
    -- Umstellen: `x - ε < y` ↔ `x - y < ε` via `x < ε + y`
    have : x < ε + y := by simpa [add_comm] using sub_lt_iff_lt_add'.mp h₁
    -- daraus folgt `x - y < ε`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_lt_iff_lt_add'.mpr this
  -- Nun Fallunterscheidung `y ≤ x` oder `x ≤ y`
  by_cases hxy : y ≤ x
  · -- dann `y < x` oder `y = x`. In beiden Fällen reicht `x - y < ε`.
    have : |y - x| = x - y := by
      have : 0 ≤ x - y := sub_nonneg.mpr hxy
      simpa [abs_sub_comm] using (abs_of_nonneg this)
    -- Aus `hl : x - y < ε`
    simpa [this] using hl
  · -- `¬ y ≤ x` ⇒ `x < y`. Dann reicht `y - x < ε`.
    have hxl : x < y := lt_of_le_of_ne (le_of_not_ge hxy) (ne_comm.mp ?hne)
    · exact abs_sub_of_left_lt hxl hr
    · -- `hne : y ≠ x`
      intro hEq; exact hxy (le_of_eq hEq)

end RealAbsTricks


/-! # Abschnitt 5: Filter-Utility (Notation) -/

section FilterUtilities

/-- Stabile Variante von `Filter.Eventually.of_forall`. -/
lemma eventually_of_forall {α : Type*} {l : Filter α} {P : α → Prop}
    (h : ∀ x, P x) : ∀ᶠ x in l, P x :=
  Filter.Eventually.of_forall h

end FilterUtilities


/-! # Abschnitt 6: Kleine Helfer für Folgen `l : ℕ → ℝ` -/

section SequenceHelpers

variable {l : ℕ → ℝ} {x ε : ℝ} {n N : ℕ}

/-- Wenn `N ≤ n`, dann gilt `1/(n+1) ≤ 1/(N+1)` (bereits oben bewiesen, hier Alias). -/
lemma one_div_succ_mono_nat (h : N ≤ n) :
    1 / (n+1 : ℝ) ≤ 1 / (N+1 : ℝ) := by
  simpa using one_div_le_one_div_of_le_nat (N := N) (n := n) h

/-- Bequeme Umformung: aus `l n < x` und `x - l n < ε` folgt `|l n - x| < ε`. -/
lemma abs_of_right_gap_lt (hr : l n < x) (hgap : x - l n < ε) : |l n - x| < ε :=
  abs_sub_of_right_lt (y := l n) (x := x) hr hgap

/-- Bequeme Umformung: aus `x < l n` und `l n - x < ε` folgt `|l n - x| < ε`. -/
lemma abs_of_left_gap_lt (hl : x < l n) (hgap : l n - x < ε) : |l n - x| < ε :=
  abs_sub_of_left_lt (x := x) (y := l n) hl hgap

end SequenceHelpers

end PerfectSubset
