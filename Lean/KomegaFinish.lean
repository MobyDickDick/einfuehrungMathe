/-
  PerfectSubset/KomegaFinish.lean

  Finale Verpackung: aus den bereits eingeführten Bausteinen folgt unmittelbar
  die Existenz einer **nichtleeren, kompakten, abgeschlossenen** und **ohne
  isolierte Punkte** liegenden Teilmenge von `M` — konkret `Kω`.

  Die Datei enthält zwei sehr dünne Wrapper, die nur bereits bewiesene Sätze
  kombinieren. Dadurch ist sie low‑risk.
-/

import Mathlib

import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaClosed
import PerfectSubset.KomegaCompact
import PerfectSubset.KomegaConvenient
import PerfectSubset.KomegaPerfect
import PerfectSubset.KomegaNoIsolated

open Set Topology

namespace Stage

/-- **Finale Aussage (direkt, ohne Setup‑Struct):**
    Unter den Standardannahmen an die Kerne (`closed`, `⊆ Icc`, `⊆ M`) sowie
    `Kω`‑Nichtleere und einer dichten Familie `Keep : ℝ → Set ℝ` um jeden Punkt
    in `Kω`, folgt, dass `Kω` die gesuchte perfekte kompakte Teilmenge von `M` ist. -/
 theorem perfect_subset_via_dense_family
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M) (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b) (s0 : State M a b)
     (hClosed : ∀ n, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     (hIcc : ∀ n, core ((refineN tsd ha hb sel n) s0) ⊆ Icc a b)
     (hCoreM : ∀ n, core ((refineN tsd ha hb sel n) s0) ⊆ M)
     (hne : (Kω tsd ha hb sel s0).Nonempty)
     (Keep : ℝ → Set ℝ)
     (subset_keep : ∀ x0, Keep x0 ⊆ Kω tsd ha hb sel s0)
     (dense_keep_at : ∀ {x0}, x0 ∈ Kω tsd ha hb sel s0 → ∀ ε > 0,
        ∃ y, y ∈ Keep x0 ∧ y ≠ x0 ∧ |y - x0| < ε) :
     (Kω tsd ha hb sel s0 ⊆ M) ∧ IsClosed (Kω tsd ha hb sel s0) ∧ IsCompact (Kω tsd ha hb sel s0) ∧
     (Kω tsd ha hb sel s0).Nonempty ∧ NoIsolated (Kω tsd ha hb sel s0) := by
   classical
   -- keine isolierten Punkte über die dichte Familie
   have hNoIso : NoIsolated (Kω tsd ha hb sel s0) :=
     noIsolated_of_dense_family tsd ha hb sel s0 Keep subset_keep (by intro x0; exact dense_keep_at)
   -- packe die übrigen Eigenschaften zusammen
   exact
     Kω_perfect_subset_of_noIsolated tsd ha hb sel s0 hClosed hIcc hCoreM hne hNoIso

/-- **Finale Aussage (Setup‑Variante):**
    Gleiche Aussage wie oben, aber mit gebündelten Annahmen in `KωSetup`.
    Nur `Keep` und dessen zwei Eigenschaften müssen noch gereicht werden. -/
 theorem perfect_subset_via_dense_family_setup
     {M : Set ℝ} {a b : ℝ}
     (S : KωSetup M a b)
     (hne : (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty)
     (Keep : ℝ → Set ℝ)
     (subset_keep : ∀ x0, Keep x0 ⊆ Kω S.tsd S.ha S.hb S.sel S.s0)
     (dense_keep_at : ∀ {x0}, x0 ∈ Kω S.tsd S.ha S.hb S.sel S.s0 → ∀ ε > 0,
        ∃ y, y ∈ Keep x0 ∧ y ≠ x0 ∧ |y - x0| < ε)
     (hCoreM : ∀ n, S.coreN n ⊆ M) :
     (Kω S.tsd S.ha S.hb S.sel S.s0 ⊆ M) ∧
        IsClosed (Kω S.tsd S.ha S.hb S.sel S.s0) ∧ IsCompact (Kω S.tsd S.ha S.hb S.sel S.s0) ∧
     (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty ∧ NoIsolated (Kω S.tsd S.ha S.hb S.sel S.s0) := by
   classical
   have hNoIso : NoIsolated (Kω S.tsd S.ha S.hb S.sel S.s0) :=
     noIsolated_of_dense_family_setup S Keep subset_keep (by intro x0; exact dense_keep_at)
   exact
     Stage.KωSetup.Kω_perfect_subset_of_noIsolated S hne hNoIso hCoreM

end Stage
