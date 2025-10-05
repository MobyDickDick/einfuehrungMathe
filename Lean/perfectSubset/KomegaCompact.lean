/-
  PerfectSubset/KomegaCompact.lean
  Kompaktheit von `Kω` — sichere Re-Exports aus der Basisdatei.

  Hinweis: Dein Projekt enthält bereits ein bewiesenes Lemma `isCompact_Kω`
  (siehe Grundmodul, dort via `Icc`-Einschluss). Um Versionsdifferenzen der
  Mathlib-Hilfslemmas zu vermeiden, re-exportieren wir hier nur bequem.
-/

import PerfectSubset.PerfectFromSuperdense
import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaClosed

open Set Topology

namespace Stage

/-- Bequemer Re-Export: Kompaktheit von `Kω` aus dem Grundmodul. -/
@[simp] theorem isCompact_Kω'
    {M : Set ℝ} {a b : ℝ}
    (tsd : TwoSidedSuperdense M)
    (ha : a ∈ M) (hb : b ∈ M)
    (sel : Selector M a b)
    (s0 : State M a b) :
    IsCompact (Kω tsd ha hb sel s0) :=
  -- Nutzt die bereits in deinem Projekt bewiesene Aussage.
  isCompact_Kω tsd ha hb sel s0

namespace KωSetup

variable {M : Set ℝ} {a b : ℝ} (S : KωSetup M a b)

/-- Komfort: Aus dem Setup sofort Kompaktheit. -/
 theorem isCompact_Kω : IsCompact (Kω S.tsd S.ha S.hb S.sel S.s0) :=
   Stage.isCompact_Kω' S.tsd S.ha S.hb S.sel S.s0

end KωSetup
end Stage
