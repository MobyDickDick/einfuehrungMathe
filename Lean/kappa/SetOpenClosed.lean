/-
  SetOpenClosed.lean  (ℝ-Version ohne Metrik & ohne Div-Lemmas)

  Für jede Teilmenge M ⊆ ℝ gilt:

  (1) M = ⋂₀ { U | IsOpen U ∧ M ⊆ U }  (Schnitt aller offenen Obermengen von M)
      Beweis: Für x ∉ M definieren wir
        U_of M x = ⋃_{y∈M} (if y < x then Iio x else Ioi x),
      dann ist U_of M x offen, enthält M, aber nicht x.

  (2) M = ⋃₀ { K | IsCompact K ∧ K ⊆ M } (Vereinigung aller kompakten Teilmengen von M)
      Beweis: {x} ist kompakt und {x} ⊆ M für x ∈ M.

  Keine Maßtheorie, keine Metrik.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Set

namespace SetOpenClosed

/-- Die Familie aller offenen Obermengen von `M`. -/
def openSupersets (M : Set ℝ) : Set (Set ℝ) :=
  {U | IsOpen U ∧ M ⊆ U}

/-- Die Familie aller kompakten Teilmengen von `M`. -/
def compactSubsets (M : Set ℝ) : Set (Set ℝ) :=
  {K | IsCompact K ∧ K ⊆ M}

/-- Für gegebenes `M` und `x` eine offene Obermenge von `M`, die `x` ausschließt. -/
def U_of (M : Set ℝ) (x : ℝ) : Set ℝ :=
  ⋃ (y : ℝ) (_ : y ∈ M), (if y < x then Iio x else Ioi x)

/-- `U_of M x` ist offen. -/
lemma isOpen_U_of (M : Set ℝ) (x : ℝ) : IsOpen (U_of M x) := by
  classical
  refine isOpen_iUnion ?_
  intro y
  refine isOpen_iUnion ?_
  intro _
  by_cases h : y < x
  · simpa [U_of, h] using isOpen_Iio
  · simpa [U_of, h] using isOpen_Ioi

/-- Für `x ∉ M` gilt `M ⊆ U_of M x`. -/
lemma subset_U_of_of_not_mem {M : Set ℝ} {x : ℝ} (hx : x ∉ M) :
  M ⊆ U_of M x := by
  classical
  intro y hyM
  have hne : y ≠ x := fun h => hx (by simpa [h] using hyM)
  have hlt : y < x ∨ x < y := lt_or_gt_of_ne hne
  rcases hlt with h | h
  · -- (A) y < x ⇒ benutze "then"-Zweig
    refine mem_iUnion.mpr ?_
    refine ⟨y, mem_iUnion.mpr ?_⟩
    -- wähle die then-Branch explizit:
    have hyx : y < x := h
    have hyIio : y ∈ Iio x := by simpa [mem_Iio] using hyx
    have : y ∈ (if y < x then Iio x else Ioi x) := by
      simp [hyx]
    exact ⟨hyM, this⟩
  · -- (B) x < y ⇒ benutze "else"-Zweig (also ¬ y < x)
    refine mem_iUnion.mpr ?_
    refine ⟨y, mem_iUnion.mpr ?_⟩
    have hyx : ¬ y < x := not_lt.mpr (le_of_lt h)
    have hyIoi : y ∈ Ioi x := by simpa [mem_Ioi] using h
    have : y ∈ (if y < x then Iio x else Ioi x) := by
      simpa [hyx] using hyIoi
    exact ⟨hyM, this⟩

/-- `x ∉ U_of M x` (für jedes `x`). -/
lemma not_mem_U_of_self (M : Set ℝ) (x : ℝ) : x ∉ U_of M x := by
  classical
  intro hxU
  rcases mem_iUnion.mp hxU with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨_, hxIn⟩
  by_cases h : y < x
  · -- dann wäre `x ∈ Iio x` ⇒ `x < x` ⇒ Widerspruch
    have hxlt : x < x := by
      simp [ h, mem_Iio] at hxIn
    exact (lt_irrefl _) hxlt
  · -- sonst wäre `x ∈ Ioi x` ⇒ `x < x` ⇒ Widerspruch
    have hxlt : x < x := by
      simp [h, mem_Ioi] at hxIn
    exact (lt_irrefl _) hxlt

/-- (1) Für ℝ: M ist der Schnitt seiner offenen Obermengen. -/
theorem inter_all_open_supersets_real (M : Set ℝ) :
    (⋂₀ openSupersets M) = M := by
  classical
  apply le_antisymm
  · -- ⊆ : Wenn x in jeder offenen Obermenge liegt, dann x ∈ M.
    intro x hx
    by_contra hxNot
    have hUx_open : IsOpen (U_of M x) := isOpen_U_of M x
    have hUx_sup  : M ⊆ U_of M x :=
      subset_U_of_of_not_mem (M := M) (x := x) hxNot
    have hxU : x ∈ U_of M x :=
      (sInter_subset_of_mem
        (show U_of M x ∈ openSupersets M from ⟨hUx_open, hUx_sup⟩)) hx
    exact (not_mem_U_of_self M x) hxU
  · -- ⊇ : M liegt in jeder offenen Obermenge ⇒ M ⊆ ⋂₀ …
    refine subset_sInter ?_
    intro U hU
    exact hU.2

/-- (2) Für ℝ: M ist die Vereinigung seiner kompakten Teilmengen. -/
theorem union_all_compact_subsets_real (M : Set ℝ) :
    (⋃₀ compactSubsets M) = M := by
  classical
  apply le_antisymm
  · -- ⊆
    intro x hx
    rcases mem_sUnion.mp hx with ⟨K, hKmem, hxK⟩
    exact hKmem.2 hxK
  · -- ⊇ : für x∈M liegt {x} in der Familie
    intro x hxM
    have hKcompact : IsCompact ({x} : Set ℝ) := isCompact_singleton
    have hKsub : ({x} : Set ℝ) ⊆ M := by
      intro y hy
      have : y = x := by simpa using hy
      simpa [this] using hxM
    have hKmem : ({x} : Set ℝ) ∈ compactSubsets M := ⟨hKcompact, hKsub⟩
    have hxK : x ∈ ({x} : Set ℝ) := by simp
    exact mem_sUnion.mpr ⟨{x}, hKmem, hxK⟩

/-- Die Familie aller Differenzen `U \ K` mit `IsOpen U`, `IsCompact K`,
    `K ⊆ M` und `M ⊆ U`. -/
def gapFamily (M : Set ℝ) : Set (Set ℝ) :=
  {S | ∃ (U K : Set ℝ), IsOpen U ∧ IsCompact K ∧ K ⊆ M ∧ M ⊆ U ∧ S = U \ K}

/-- Hauptsatz: Der Schnitt aller `U \ K` (wie oben) ist leer. -/
theorem inter_all_gaps_empty (M : Set ℝ) :
    (⋂₀ gapFamily M) = (∅ : Set ℝ) := by
  classical
  apply le_antisymm
  · -- (⊆) Zeige: ⋂₀ gapFamily M ⊆ ∅
    intro x hx
    by_cases hxM : x ∈ M
    · -- Fall 1: x ∈ M. Wähle U = univ, K = {x}.
      have hUopen : IsOpen (Set.univ : Set ℝ) := isOpen_univ
      have hKcomp : IsCompact ({x} : Set ℝ) := isCompact_singleton
      have hKsub  : ({x} : Set ℝ) ⊆ M := by
        intro y hy
        -- aus y ∈ {x} folgt y = x
        have : y = x := by simpa using hy
        -- dann gilt y ∈ M per Umschreiben
        simpa [this] using hxM
      have hMsubU : M ⊆ (Set.univ : Set ℝ) := by intro _ _; trivial
      have hmem : (Set.univ \ ({x} : Set ℝ)) ∈ gapFamily M := by
        exact ⟨Set.univ, {x}, hUopen, hKcomp, hKsub, hMsubU, rfl⟩
      -- aus x ∈ ⋂₀ … folgt x ∈ U\K für dieses spezielle Paar
      have hxIn : x ∈ Set.univ \ ({x} : Set ℝ) :=
        (sInter_subset_of_mem hmem) hx
      -- aber x ∉ univ \ {x}
      have hxNot : x ∉ Set.univ \ ({x} : Set ℝ) := by
        -- x ∈ {x} ⇒ nicht in der Differenz
        simp
      exact hxNot hxIn
    · -- Fall 2: x ∉ M. Wähle U = U_of M x (offen, enthält M, aber nicht x), K = ∅.
      have hUopen : IsOpen (U_of M x) := isOpen_U_of M x
      have hKcomp : IsCompact (∅ : Set ℝ) := isCompact_empty
      have hKsub  : (∅ : Set ℝ) ⊆ M := by intro _ h; cases h
      have hMsubU : M ⊆ U_of M x := subset_U_of_of_not_mem (M := M) (x := x) hxM
      have hmem : (U_of M x \ (∅ : Set ℝ)) ∈ gapFamily M := by
        exact ⟨U_of M x, (∅ : Set ℝ), hUopen, hKcomp, hKsub, hMsubU, rfl⟩
      have hxIn : x ∈ U_of M x \ (∅ : Set ℝ) := (sInter_subset_of_mem hmem) hx
      -- also x ∈ U_of M x, Widerspruch zu not_mem_U_of_self
      exact (not_mem_U_of_self M x) hxIn.left
  · -- (⊇) Zeige: ∅ ⊆ ⋂₀ gapFamily M
    intro x hx
    cases hx


end SetOpenClosed
