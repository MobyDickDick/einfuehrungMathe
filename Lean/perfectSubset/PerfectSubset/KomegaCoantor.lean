/-
  PerfectSubset/KomegaCantor.lean
  Cantor-Schiene (verpackt in separater Datei):
  Brückensätze von (Teil-)Konvergenz zu `x0 ∈ Kω` und `Kω ≠ ∅`.

  Design-Ziel: robust & low-risk. Wir vermeiden harte Annahmen über
  bereits vorhandene Projektsätze; stattdessen geben wir flexible Wrapper,
  die mit `Antitone`/`IsClosed`/`Icc`/Kompaktheit kompatibel sind und
  auf Deinen bereits eingefügten Lemmas aus `KomegaProperties` aufsetzen.
-/

import PerfectSubset.PerfectFromSuperdense
import PerfectSubset.KomegaProperties

open Set Filter Topology

namespace Stage

/-- **Cantor-Brücke (generische Eventual-Form):**
    Wenn `y : ℕ → ℝ` gegen `x0` konvergiert und für **jedes** `n` gilt
    `y m ∈ core_n` für alle hinreichend großen `m`, dann liegt `x0 ∈ Kω`.
    Benötigt: Geschlossenheit der Kerne. -/
 theorem mem_Kω_of_tendsto_eventually_in_each_core
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {y : ℕ → ℝ} {x0 : ℝ}
     (hEv : ∀ n : ℕ, ∀ᶠ m in atTop, y m ∈ core ((refineN tsd ha hb sel n) s0))
     (hconv : Tendsto y atTop (nhds x0)) :
     x0 ∈ Kω tsd ha hb sel s0 := by
   classical
   have hx0_in_core : ∀ n : ℕ, x0 ∈ core ((refineN tsd ha hb sel n) s0) := by
     intro n
     exact (hClosed n).mem_of_tendsto hconv (hEv n)
   simpa [Kω] using Set.mem_iInter.mpr hx0_in_core

/-- **Nichtleere via Eventual-Form:** Existieren `y, x0` wie oben, so ist `Kω` nichtleer. -/
 theorem Kω_nonempty_of_tendsto_eventually_in_each_core
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {y : ℕ → ℝ} {x0 : ℝ}
     (hEv : ∀ n : ℕ, ∀ᶠ m in atTop, y m ∈ core ((refineN tsd ha hb sel n) s0))
     (hconv : Tendsto y atTop (nhds x0)) :
     (Kω tsd ha hb sel s0).Nonempty :=
   ⟨x0, mem_Kω_of_tendsto_eventually_in_each_core tsd ha hb sel s0 hClosed hEv hconv⟩

/-- **Hilfslemma (Antiton + kofinale Subsequenz-Indizes):**
    Antitone Familien `C : ℕ → Set ℝ` und eine Folge `y` mit `y m ∈ C (φ m)`.
    Ist `φ` kofinal, d. h. `∀ n, ∃ m₀, ∀ m ≥ m₀, n ≤ φ m`, dann gilt bereits
    `∀ n, ∀ᶠ m in atTop, y m ∈ C n`. -/
 theorem eventually_in_antitone_target
     {C : ℕ → Set ℝ}
     (hAntitone : Antitone C)
     {y : ℕ → ℝ} {φ : ℕ → ℕ}
     (cofinal : ∀ n : ℕ, ∃ m0 : ℕ, ∀ m ≥ m0, n ≤ φ m)
     (hy : ∀ m : ℕ, y m ∈ C (φ m)) :
     ∀ n : ℕ, ∀ᶠ m in atTop, y m ∈ C n := by
   intro n
   rcases cofinal n with ⟨m0, hφ⟩
   refine Filter.eventually_atTop.2 ?_
   refine ⟨m0, ?_⟩
   intro m hm
   have hle : n ≤ φ m := hφ m hm
   have hsub : C (φ m) ⊆ C n := hAntitone hle
   exact hsub (hy m)

/-- **Cantor-Brücke (Subsequenz‑Form unter Kofinalität):**
    Wir wählen `y m := x (φ m)`. Wenn `φ` kofinal ist, `core_n` geschlossen und antiton,
    und `y` gegen `x0` konvergiert, dann `x0 ∈ Kω`. -/
 theorem mem_Kω_of_tendsto_subseq_in_cores_of_cofinal
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hAntitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0)))
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {x : ℕ → ℝ} {φ : ℕ → ℕ} {x0 : ℝ}
     (cofinal : ∀ n : ℕ, ∃ m0 : ℕ, ∀ m ≥ m0, n ≤ φ m)
     (hx : ∀ m : ℕ, x m ∈ core ((refineN tsd ha hb sel m) s0))
     (hconv : Tendsto (fun m => x (φ m)) atTop (nhds x0)) :
     x0 ∈ Kω tsd ha hb sel s0 := by
   classical
   -- Setze y := x ∘ φ und nutze das Eventual-Lemma
   let y : ℕ → ℝ := fun m => x (φ m)
   have hy : ∀ m, y m ∈ core ((refineN tsd ha hb sel (φ m)) s0) := by
     intro m; dsimp [y]; exact hx (φ m)
   have hEv : ∀ n, ∀ᶠ m in atTop, y m ∈ core ((refineN tsd ha hb sel n) s0) := by
     -- Antitonie liefert `core_{φ m} ⊆ core_n`, sobald `n ≤ φ m` (kofinal ⇒ eventually)
     refine eventually_in_antitone_target
       (C := fun n => core ((refineN tsd ha hb sel n) s0)) hAntitone cofinal ?_
     exact hy
   -- wende Eventual-Form an
   exact mem_Kω_of_tendsto_eventually_in_each_core tsd ha hb sel s0 hClosed hEv hconv

/-- **Nichtleere via Subsequenz‑Form unter Kofinalität.** -/
 theorem Kω_nonempty_of_tendsto_subseq_in_cores_of_cofinal
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hAntitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0)))
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {x : ℕ → ℝ} {φ : ℕ → ℕ} {x0 : ℝ}
     (cofinal : ∀ n : ℕ, ∃ m0 : ℕ, ∀ m ≥ m0, n ≤ φ m)
     (hx : ∀ m : ℕ, x m ∈ core ((refineN tsd ha hb sel m) s0))
     (hconv : Tendsto (fun m => x (φ m)) atTop (nhds x0)) :
     (Kω tsd ha hb sel s0).Nonempty :=
   ⟨x0, mem_Kω_of_tendsto_subseq_in_cores_of_cofinal
      tsd ha hb sel s0 hAntitone hClosed cofinal hx hconv⟩

end Stage
