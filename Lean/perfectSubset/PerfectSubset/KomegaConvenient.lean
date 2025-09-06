/-
  PerfectSubset/KomegaConvenience.lean
  Sammel- & Komfort-Lemmas rund um Kω.

  Ziel: Einfache, fehlerarme Anwendung der bereits bewiesenen Bausteine
  (Properties/Cantor/BW) über ein gebündeltes Setup.

  Diese Datei führt **keine** neuen mathematischen Abhängigkeiten ein,
  sondern verpackt vorhandene Resultate in bequeme Wrapper.
-/

import Mathlib

import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaCantor
import PerfectSubset.KomegaBW

open Set

namespace Stage

/-- Bündelt die Standardannahmen, die wir typischerweise für `Kω` verwenden. -/
structure KωSetup (M : Set ℝ) (a b : ℝ) where
  tsd : TwoSidedSuperdense M
  ha : a ∈ M
  hb : b ∈ M
  sel : Selector M a b
  s0 : State M a b
  antitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0))
  closed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0))
  subsetIcc: ∀ n : ℕ, core ((refineN tsd ha hb sel n) s0) ⊆ Icc a b
  nonempty : ∀ n : ℕ, (core ((refineN tsd ha hb sel n) s0)).Nonempty

namespace KωSetup

variable {M : Set ℝ} {a b : ℝ} (S : KωSetup M a b)

/-- Bequeme Abkürzung für den `n`‑ten Kern. -/
@[inline] def coreN (n : ℕ) : Set ℝ := core ((refineN S.tsd S.ha S.hb S.sel n) S.s0)

@[simp] theorem coreN_def (n : ℕ) : S.coreN n = core ((refineN S.tsd S.ha S.hb S.sel n) S.s0) := rfl

/-- Sofortige Folgerung: `Kω ⊆ Icc a b`. -/
theorem Kω_subset_Icc :
  Kω S.tsd S.ha S.hb S.sel S.s0 ⊆ Icc a b :=
  Stage.Kω_subset_of_cores_subset S.tsd S.ha S.hb S.sel S.s0 S.subsetIcc


/-- Nichtleerheit aus den Standardannahmen **plus** einer Instanz der BW‑Hypothese. -/
 theorem Kω_nonempty_of_BW (BW : BW_Icc a b) :
   (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty :=
  Kω_nonempty_of_closed_antitone_nonempty_in_Icc_of_BW
    S.tsd S.ha S.hb S.sel S.s0 S.antitone S.closed S.subsetIcc S.nonempty BW

/-- Praktischer Export der `mem_Kω`‑Charakterisierung als `simp`‑Form. -/
@[simp] theorem mem_Kω_iff_all_cores {x : ℝ} :
  x ∈ Kω S.tsd S.ha S.hb S.sel S.s0 ↔ ∀ n, x ∈ S.coreN n := by
  simpa [KωSetup.coreN, KωSetup.coreN_def] using
    (Stage.mem_Kω_iff_forall_core S.tsd S.ha S.hb S.sel S.s0 : _)

/-- Bequeme Richtung: aus `x ∈ Kω` folgt `x ∈ core_n` für jedes `n`. -/
 theorem mem_coreN_of_mem_Kω {x : ℝ} (hx : x ∈ Kω S.tsd S.ha S.hb S.sel S.s0) (n : ℕ) :
   x ∈ S.coreN n :=
  (mem_core_of_mem_Kω S.tsd S.ha S.hb S.sel S.s0 hx n)

/-- Umkehrung auf Mengenebene: `T ⊆ Kω` genau dann, wenn `T ⊆ core_n` für alle `n`. -/
@[simp] theorem subset_Kω_iff {T : Set ℝ} :
  T ⊆ Kω S.tsd S.ha S.hb S.sel S.s0 ↔ ∀ n, T ⊆ S.coreN n :=
  (subset_Kω_iff_forall_subset_core S.tsd S.ha S.hb S.sel S.s0)
end KωSetup

end Stage
