/-
  SigmaCompactCover.lean – kompatibel mit älteren Mathlib4-Ständen

  (A) closure M ist abzählbare Vereinigung kompakter Mengen
  (B) Abgeschlossenes M ist abzählbare Vereinigung kompakter Mengen
  (C) Fσ-Darstellung ⇒ abzählbare Vereinigung kompakter Teilmengen innerhalb von M
-/

import Mathlib

open Set

section

variable (M : Set ℝ)

/-- Hilfslemma: ℝ ist durch die kompakten Intervalle [-n,n] abzudecken. -/
lemma mem_iUnion_Icc_cover (x : ℝ) :
    x ∈ ⋃ n : ℕ, (Icc (-(n : ℝ)) n) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  refine mem_iUnion.mpr ⟨n, ?_⟩
  have : |x| < (n : ℝ) := by exact_mod_cast hn
  have hlt : - (n : ℝ) < x ∧ x < (n : ℝ) := abs_lt.mp this
  exact ⟨hlt.1.le, hlt.2.le⟩

/-- (A) `closure M` ist abzählbare Vereinigung kompakter Mengen. -/
theorem closure_eq_iUnion_compact :
    closure M = ⋃ n : ℕ, (closure M ∩ Icc (-(n : ℝ)) n) := by
  classical
  ext x
  constructor
  · intro hx
    have hU := mem_iUnion_Icc_cover x
    rcases mem_iUnion.mp hU with ⟨n, hxI⟩
    exact mem_iUnion.mpr ⟨n, ⟨hx, hxI⟩⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨_, hx'⟩
    exact hx'.1

/-- Kompaktheit von `closure M ∩ Icc (−n) n`. -/
lemma isCompact_closure_inter_Icc (n : ℕ) :
    IsCompact (closure M ∩ Icc (-(n : ℝ)) n) := by
  -- Nutze: kompakt ∩ geschlossen ist kompakt
  have h := IsCompact.inter_right
              (isCompact_Icc : IsCompact (Icc (-(n : ℝ)) n))
              (isClosed_closure : IsClosed (closure M))
  -- Reihenfolge drehen:
  simpa [inter_comm] using h

/-- (B) Ist `M` abgeschlossen, dann ist `M` eine abzählbare Vereinigung kompakter Mengen. -/
theorem closed_eq_iUnion_compact (_hM : IsClosed M) :
    M = ⋃ n : ℕ, (M ∩ Icc (-(n : ℝ)) n) := by
  classical
  ext x
  constructor
  · intro hx
    have hU := mem_iUnion_Icc_cover x
    rcases mem_iUnion.mp hU with ⟨n, hxI⟩
    exact mem_iUnion.mpr ⟨n, ⟨hx, hxI⟩⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨_, hx'⟩
    exact hx'.1

/-- Kompaktheit von `M ∩ Icc (−n) n`, falls `M` abgeschlossen ist. -/
lemma isCompact_closed_inter_Icc (hM : IsClosed M) (n : ℕ) :
    IsCompact (M ∩ Icc (-(n : ℝ)) n) := by
  have h := IsCompact.inter_right
              (isCompact_Icc : IsCompact (Icc (-(n : ℝ)) n))
              (hM : IsClosed M)
  simpa [inter_comm] using h

end

/-
  (C) Aus Fσ-Darstellung: M = ⋃ₙ F n, mit `IsClosed (F n)`, folgt:
  M ist abzählbare Vereinigung kompakter TEILmengen von M.
-/
section

variable {M : Set ℝ}

/-- (C) Fσ ⇒ Vereinigung kompakter Teilmengen von `M`. -/
theorem fsigma_cover_by_compacts_inside
    (F : ℕ → Set ℝ)
    (hFclosed : ∀ n, IsClosed (F n))
    (hFsub : ∀ n, F n ⊆ M)
    (hFUnion : (⋃ n, F n) = M) :
    (⋃ n : ℕ, ⋃ m : ℕ, (F n ∩ Icc (-(m : ℝ)) m)) = M
    ∧ (∀ n m : ℕ, IsCompact (F n ∩ Icc (-(m : ℝ)) m))
    ∧ (∀ n m : ℕ, F n ∩ Icc (-(m : ℝ)) m ⊆ M) := by
  classical
  -- 1) Gleichheit der Vereinigungen
  have hUnion : (⋃ n : ℕ, ⋃ m : ℕ, (F n ∩ Icc (-(m : ℝ)) m)) = M := by
    ext x; constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hx⟩
      rcases mem_iUnion.mp hx with ⟨m, hx'⟩
      exact (hFsub n) hx'.1
    · intro hxM
      have : x ∈ ⋃ n : ℕ, F n := by simpa [hFUnion] using hxM
      rcases mem_iUnion.mp this with ⟨n, hxF⟩
      obtain ⟨m, hm⟩ := exists_nat_gt |x|
      have : |x| < (m : ℝ) := by exact_mod_cast hm
      have hlt : - (m : ℝ) < x ∧ x < (m : ℝ) := abs_lt.mp this
      have hxIcc : x ∈ Icc (-(m : ℝ)) m := ⟨hlt.1.le, hlt.2.le⟩
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨m, ⟨hxF, hxIcc⟩⟩⟩

  -- 2) Kompaktheit der Bausteine: kompakt ∩ geschlossen
  have hCompact : ∀ n m : ℕ, IsCompact (F n ∩ Icc (-(m : ℝ)) m) := by
    intro n m
    have h := IsCompact.inter_right
                (isCompact_Icc : IsCompact (Icc (-(m : ℝ)) m))
                (hFclosed n)
    simpa [inter_comm] using h

  -- 3) Teilmengen-Eigenschaft
  have hSubAll : ∀ n m : ℕ, F n ∩ Icc (-(m : ℝ)) m ⊆ M := by
    intro n m x hx
    exact (hFsub n) hx.1

  exact ⟨hUnion, hCompact, hSubAll⟩

end
