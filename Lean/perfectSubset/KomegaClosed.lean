/-
  PerfectSubset/KomegaClosed.lean
  Geschlossenheit von `Kω` als (beliebiger) Schnitt abgeschlossener Kerne.

  Low‑risk: benutzt nur `isClosed_iInter` aus Mathlib und unsere vorhandenen Bezeichner.
-/

import Mathlib
import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaConvenient

open Set Topology

namespace Stage

/-- `Kω` ist abgeschlossen, sobald alle Stufenkerne abgeschlossen sind. -/
 theorem isClosed_Kω_of_closed_cores
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0))) :
     IsClosed (Kω tsd ha hb sel s0) := by
   classical
   simpa [Kω] using isClosed_iInter (fun n => hClosed n)

namespace KωSetup

variable {M : Set ℝ} {a b : ℝ} (S : KωSetup M a b)

/-- Bequeme Ableitung: `Kω` ist abgeschlossen (aus dem Setup). -/
 theorem isClosed_Kω : IsClosed (Kω S.tsd S.ha S.hb S.sel S.s0) :=
   Stage.isClosed_Kω_of_closed_cores S.tsd S.ha S.hb S.sel S.s0 S.closed

end KωSetup
end Stage
