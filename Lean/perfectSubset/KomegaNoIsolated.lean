/-
  PerfectSubset/KomegaNoIsolated.lean

  Ziel: eine **dünne Brücke** von einer beliebigen dichten "Keep"-Familie
  zu `NoIsolated (Kω …)`. Wir verweisen **nicht** mehr direkt auf `KωKeep`,
  damit das File ohne weitere Projekt-Abhängigkeiten kompiliert. Stattdessen
  parametrisieren wir eine Menge `Keep x0` und fordern zwei triviale Eigenschaften:
  (i) `Keep x0 ⊆ Kω` und (ii) für jedes `x0 ∈ Kω` liefert `Keep x0` zu jedem ε>0
  einen **anderen** Punkt im ε‑Ball. Das genügt, um `NoIsolated (Kω …)` zu folgern.
-/

import Mathlib

import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaConvenient
import PerfectSubset.KomegaPerfect  -- liefert `Stage.NoIsolated`

open Set Topology

namespace Stage

/-- Dünner Wrapper: Wenn eine Familie `Keep : ℝ → Set ℝ` für *jedes* Zentrum `x0`
    in `Kω` dicht ist (liefert andere Punkte im ε‑Ball) und außerdem `Keep x0 ⊆ Kω`,
    dann hat `Kω` **keine isolierten Punkte**. -/
 theorem noIsolated_of_dense_family
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (Keep : ℝ → Set ℝ)
     -- 1) Inklusions‑Brücke: alles aus `Keep x0` liegt in `Kω`.
     (subset_keep : ∀ x0 : ℝ, Keep x0 ⊆ Kω tsd ha hb sel s0)
     -- 2) Dichte‑Brücke: für jedes `x0 ∈ Kω` und jedes `ε>0` existiert
     --    **ein anderer** Punkt `y ∈ Keep x0` mit |y−x0|<ε.
     (dense_keep_at : ∀ {x0 : ℝ}, x0 ∈ Kω tsd ha hb sel s0 → ∀ ε > 0,
        ∃ y, y ∈ Keep x0 ∧ y ≠ x0 ∧ |y - x0| < ε) :
     NoIsolated (Kω tsd ha hb sel s0) := by
   intro x hx ε hε
   rcases dense_keep_at hx ε hε with ⟨y, hyKeep, hyNe, hyDist⟩
   have hyKω : y ∈ Kω tsd ha hb sel s0 := (subset_keep x) hyKeep
   exact ⟨y, hyKω, hyNe, hyDist⟩

/-- Setup‑Variante des vorherigen Lemmas (ohne Referenz auf projektspezifische `Keep`s). -/
 theorem noIsolated_of_dense_family_setup
     {M : Set ℝ} {a b : ℝ}
     (S : KωSetup M a b)
     (Keep : ℝ → Set ℝ)
     (subset_keep : ∀ x0 : ℝ, Keep x0 ⊆ Kω S.tsd S.ha S.hb S.sel S.s0)
     (dense_keep_at : ∀ {x0 : ℝ}, x0 ∈ Kω S.tsd S.ha S.hb S.sel S.s0 → ∀ ε > 0,
        ∃ y, y ∈ Keep x0 ∧ y ≠ x0 ∧ |y - x0| < ε) :
     NoIsolated (Kω S.tsd S.ha S.hb S.sel S.s0) := by
   simpa using
     (noIsolated_of_dense_family S.tsd S.ha S.hb S.sel S.s0 Keep
       subset_keep (by intro x0; exact dense_keep_at))

end Stage
