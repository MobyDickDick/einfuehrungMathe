/-
  PerfectSubset/KomegaPerfect.lean

  Abschluss-Baustein: Sobald wir **Nichtleere** und **keine isolierten Punkte**
  für `Kω` haben, folgt die Existenz einer **perfekten kompakten** Teilmenge von `M`.

  Dieses File führt keine schweren Beweise ein, sondern bündelt vorhandene
  Resultate aus den Convenience- /Closed- /Compact-Dateien in einer Endaussage.
-/

import Mathlib

import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaClosed
import PerfectSubset.KomegaCompact
import PerfectSubset.KomegaConvenient

open Set Topology

namespace Stage

/-- Einfache metrische Form von "keine isolierten Punkte". -/
def NoIsolated (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ ε > 0, ∃ y ∈ S, y ≠ x ∧ |y - x| < ε

/-- Schlussbaustein: Aus Standardannahmen + Nichtleere + keine isolierten Punkte
    folgt, dass `Kω` eine nichtleere, perfekte, kompakte Teilmenge von `M` ist. -/
 theorem Kω_perfect_subset_of_noIsolated
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     -- Standardannahmen über die Stufenkerne
     (hClosed : ∀ n, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     (_hIcc : ∀ n, core ((refineN tsd ha hb sel n) s0) ⊆ Icc a b)
     -- jede Stufe liegt bereits in `M`
     (hCoreM : ∀ n, core ((refineN tsd ha hb sel n) s0) ⊆ M)
     -- Endannahmen für `Kω`
     (hne : (Kω tsd ha hb sel s0).Nonempty)
     (hNoIso : NoIsolated (Kω tsd ha hb sel s0)) :
     (Kω tsd ha hb sel s0 ⊆ M) ∧ IsClosed (Kω tsd ha hb sel s0) ∧ IsCompact (Kω tsd ha hb sel s0) ∧
     (Kω tsd ha hb sel s0).Nonempty ∧ NoIsolated (Kω tsd ha hb sel s0) := by
   classical
   -- `Kω ⊆ M` aus der Kern-zu-M-Annahme
   have hSubM : Kω tsd ha hb sel s0 ⊆ M :=
     Kω_subset_of_cores_subset tsd ha hb sel s0 hCoreM
   -- Abgeschlossenheit und Kompaktheit von `Kω`
   have hClosedK : IsClosed (Kω tsd ha hb sel s0) :=
     isClosed_Kω_of_closed_cores tsd ha hb sel s0 hClosed
   have hCompK : IsCompact (Kω tsd ha hb sel s0) :=
     Stage.isCompact_Kω' tsd ha hb sel s0
   exact ⟨hSubM, hClosedK, hCompK, hne, hNoIso⟩

end Stage

namespace Stage.KωSetup

variable {M : Set ℝ} {a b : ℝ}

/-- Schlussbaustein im Setup-Stil: benötigt zusätzlich `hCoreM` (Kerne ⊆ M). -/
 theorem Kω_perfect_subset_of_noIsolated
     (S : KωSetup M a b)
     (hne : (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty)
     (hNoIso : Stage.NoIsolated (Kω S.tsd S.ha S.hb S.sel S.s0))
     (hCoreM : ∀ n, S.coreN n ⊆ M) :
     (Kω S.tsd S.ha S.hb S.sel S.s0 ⊆ M) ∧ IsClosed (Kω S.tsd S.ha S.hb S.sel S.s0) ∧
     IsCompact (Kω S.tsd S.ha S.hb S.sel S.s0) ∧ (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty ∧
     Stage.NoIsolated (Kω S.tsd S.ha S.hb S.sel S.s0) := by
   have hCoreM' : ∀ n, core ((refineN S.tsd S.ha S.hb S.sel n) S.s0) ⊆ M := by
     intro n; simpa [KωSetup.coreN, KωSetup.coreN_def] using hCoreM n
   exact
     Stage.Kω_perfect_subset_of_noIsolated
       S.tsd S.ha S.hb S.sel S.s0 S.closed S.subsetIcc hCoreM' hne hNoIso

end Stage.KωSetup
