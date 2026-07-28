/-
  PerfectSubset/KomegaLTUTendsto.lean

  Aus `LTU M` (Nichtleere + lokal zweiseitig überabzählbar) gewinnen wir für
  jeden Punkt `x ∈ M` **kanonische (noncomputable) Folgen** von Punkten in `M`,
  die `x` von links bzw. rechts approximieren und gegen `x` konvergieren.

  Wir bauen nichts Konstruktives, sondern wählen nur per `Classical.choose`
  die in `KomegaLTUSeqs` bewiesenen Existenzpunkte.
-/

import Mathlib

import PerfectSubset.KomegaLTU
import PerfectSubset.KomegaLTUSeqs

open Set Filter Topology

namespace Stage

/-- `eps n = 1/(n+1)` kommt aus `KomegaLTUSeqs`.  Hier nur Monotonie-Hilfslemmas. -/
lemma eps_antitone : Antitone eps := by
  intro m n hmn
  -- 0 < m+1
  have hmpos : 0 < (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    linarith
  -- (m+1) ≤ (n+1)
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast add_le_add_right hmn 1
  -- Größerer Nenner ⇒ kleinerer Bruch
  have h : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le hmpos hle
  simpa [eps, one_div] using h

lemma exists_N_eps_lt {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, eps N < ε := by
  -- Wähle N mit (1/ε) < N (archimedisch)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hpos_inv : 0 < 1 / ε := by
    -- 0 < 1/ε
    have : 0 < ε := hε
    simpa [one_div] using inv_pos.mpr this
  have hNpos : 0 < (N : ℝ) := lt_trans hpos_inv hN
  -- Invertieren: aus (1/ε) < N folgt 1/N < ε
  have h_one_divN_lt_eps : (1 : ℝ) / (N : ℝ) < ε := by
    have h' : (1 : ℝ) / (N : ℝ) < (1 : ℝ) / (1 / ε) :=
      one_div_lt_one_div_of_lt hpos_inv hN
    simpa [one_div, inv_inv] using h'
  -- Und eps N = 1/(N+1) ≤ 1/N
  have h_cmp : eps N ≤ (1 : ℝ) / (N : ℝ) := by
    have hden : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have : (1 : ℝ) / ((N : ℝ) + 1) ≤ (1 : ℝ) / (N : ℝ) :=
      one_div_le_one_div_of_le hNpos hden
    simpa [eps, one_div] using this
  exact ⟨N, lt_of_le_of_lt h_cmp h_one_divN_lt_eps⟩

/-- Kanonische (noncomputable) **linke** Approximationsfolge aus `LTU`. -/
@[simp] noncomputable def leftSeq {M : Set ℝ}
    (h : LTU M) (x : ℝ) (hx : x ∈ M) (n : ℕ) : ℝ :=
  Classical.choose (exists_left_approx_of_LTU (M:=M) h hx n)

/-- Eigenschaften der linken Folge: Mitgliedschaft, Abstand, Richtung. -/
lemma leftSeq_spec {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) (n : ℕ) :
    leftSeq h x hx n ∈ M ∧ leftSeq h x hx n ≠ x ∧
      |leftSeq h x hx n - x| < eps n ∧ leftSeq h x hx n < x := by
  classical
  rcases Classical.choose_spec (exists_left_approx_of_LTU (M:=M) h hx n)
    with ⟨hM, hne, hdist, hlt⟩
  exact ⟨hM, hne, hdist, hlt⟩

/-- **Konvergenz** der linken Folge gegen `x`. -/
lemma tendsto_leftSeq {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) :
    Tendsto (fun n => leftSeq h x hx n) atTop (𝓝 x) := by
  classical
  -- Metrische ε‑Charakterisierung der Konvergenz in ℝ
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_N_eps_lt (hε := hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hspec := (leftSeq_spec (M:=M) h hx n)
  -- |seq n - x| < eps n ≤ eps N < ε
  have hmono : eps n ≤ eps N := eps_antitone (show N ≤ n from hn)
  have hlt_epsN : |leftSeq h x hx n - x| < eps N :=
    lt_of_lt_of_le hspec.2.2.1 hmono
  have hfinal : |leftSeq h x hx n - x| < ε := lt_trans hlt_epsN hN
  simpa [Real.dist_eq] using hfinal

/-- Kanonische (noncomputable) **rechte** Approximationsfolge aus `LTU`. -/
@[simp] noncomputable def rightSeq {M : Set ℝ}
    (h : LTU M) (x : ℝ) (hx : x ∈ M) (n : ℕ) : ℝ :=
  Classical.choose (exists_right_approx_of_LTU (M:=M) h hx n)

/-- Eigenschaften der rechten Folge. -/
lemma rightSeq_spec {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) (n : ℕ) :
    rightSeq h x hx n ∈ M ∧ rightSeq h x hx n ≠ x ∧
      |rightSeq h x hx n - x| < eps n ∧ x < rightSeq h x hx n := by
  classical
  rcases Classical.choose_spec (exists_right_approx_of_LTU (M:=M) h hx n)
    with ⟨hM, hne, hdist, hgt⟩
  exact ⟨hM, hne, hdist, hgt⟩

/-- **Konvergenz** der rechten Folge gegen `x`. -/
lemma tendsto_rightSeq {M : Set ℝ}
    (h : LTU M) {x : ℝ} (hx : x ∈ M) :
    Tendsto (fun n => rightSeq h x hx n) atTop (𝓝 x) := by
  classical
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_N_eps_lt (hε := hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hspec := (rightSeq_spec (M:=M) h hx n)
  have hmono : eps n ≤ eps N := eps_antitone (show N ≤ n from hn)
  have hlt_epsN : |rightSeq h x hx n - x| < eps N :=
    lt_of_lt_of_le hspec.2.2.1 hmono
  have hfinal : |rightSeq h x hx n - x| < ε := lt_trans hlt_epsN hN
  simpa [Real.dist_eq] using hfinal

end Stage
