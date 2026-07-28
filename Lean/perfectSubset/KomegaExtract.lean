/-
  PerfectSubset/KomegaExtract.lean
  Kleine, absolut robuste Extraktions-Helfer für `Kω` auf Basis von `KωSetup`.

  Idee: Wir definieren eine kanonische Folge `seqCore S n ∈ core_n` über Choice
  und zeigen, dass sie (wegen Antitonie) zu jedem festen Kern schließlich gehört.
  Gepaart mit einer Konvergenzannahme liefert dies automatisch `x0 ∈ Kω` und
  `Kω ≠ ∅` über die Cantor-Brücke aus `KomegaCantor`.
-/

import Mathlib

import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaCantor
import PerfectSubset.KomegaConvenient

open Set Filter Topology

namespace Stage
namespace KωSetup

variable {M : Set ℝ} {a b : ℝ} (S : KωSetup M a b)

/-- Kanonische Auswahl einer Folge mit `seqCore S n ∈ core_n`. -/
@[inline] noncomputable def seqCore (n : ℕ) : ℝ :=
  Classical.choose (S.nonempty n)

/-- Mitgliedschaft der kanonischen Auswahl im jeweiligen `core_n`. -/
@[simp] theorem seqCore_mem_coreN (n : ℕ) :
  S.seqCore n ∈ S.coreN n := by
  classical
  simpa [seqCore, KωSetup.coreN, KωSetup.coreN_def] using Classical.choose_spec (S.nonempty n)

/-- Eventualität: Für jedes feste `n` liegt `seqCore S m` ab einem Index in `core_n`.
    (Antitonie + Kofinalität von `id`.) -/
 theorem eventually_seqCore_in_each_core :
   ∀ n : ℕ, ∀ᶠ m in atTop, S.seqCore m ∈ S.coreN n := by
  classical
  have hx : ∀ m, S.seqCore m ∈ S.coreN m := by intro m; simpa using S.seqCore_mem_coreN m
  -- Spezialisierung von `eventually_in_antitone_target`
  -- auf `C := S.coreN`, `y := seqCore`, `φ := id`.
  -- Kofinalität von `id` ist trivial: für gegebenes `n` wähle `m0 := n`.
  have hcofinal : ∀ n : ℕ, ∃ m0 : ℕ, ∀ m ≥ m0, n ≤ (id m) := by
    intro n; exact ⟨n, by intro m hm; exact hm⟩
  -- Anwenden des allgemeinen Lemmas
  simpa [KωSetup.coreN, KωSetup.coreN_def] using
    (Stage.eventually_in_antitone_target (C := fun n => S.coreN n) S.antitone hcofinal hx)

/-- **Konsequenz:** Konvergiert die kanonische Folge `seqCore S` gegen `x0`, dann
    `x0 ∈ Kω` und damit `Kω ≠ ∅`. -/
 theorem mem_Kω_of_tendsto_seqCore {x0 : ℝ}
     (hconv : Tendsto (fun m => S.seqCore m) atTop (nhds x0)) :
     x0 ∈ Kω S.tsd S.ha S.hb S.sel S.s0 := by
  classical
  -- Eventualität aus dem vorigen Lemma + Geschlossenheit der Kerne ⇒ Cantor-Bridge
  have hEv : ∀ n : ℕ, ∀ᶠ m in atTop, S.seqCore m ∈ S.coreN n := S.eventually_seqCore_in_each_core
  -- Verpacke `coreN` zurück in die ursprünglichen Parameter
  have hClosed : ∀ n, IsClosed (S.coreN n) := by
    intro n
    simpa [KωSetup.coreN, KωSetup.coreN_def] using S.closed n
  -- wende Cantor‑Brücke an
  simpa [KωSetup.coreN, KωSetup.coreN_def] using
    (Stage.mem_Kω_of_tendsto_eventually_in_each_core
      S.tsd S.ha S.hb S.sel S.s0 (by intro n; simpa using hClosed n)
      (by intro n; simpa using hEv n) hconv)

/-- **Nichtleere** aus Konvergenz der kanonischen Folge. -/
 theorem Kω_nonempty_of_tendsto_seqCore {x0 : ℝ}
     (hconv : Tendsto (fun m => S.seqCore m) atTop (nhds x0)) :
     (Kω S.tsd S.ha S.hb S.sel S.s0).Nonempty :=
  ⟨x0, S.mem_Kω_of_tendsto_seqCore hconv⟩

end KωSetup
end Stage
