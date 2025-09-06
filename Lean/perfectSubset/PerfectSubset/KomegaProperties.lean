/-
  PerfectSubset/KomegaProperties.lean
  Nächste Iteration (bereinigt): erste sichere Folgerung für Kω.

  Änderungen ggü. der ersten Version:
  * Konflikt behoben: Der Name `Kω_subset_M` kollidierte bereits mit einer vorhandenen Deklaration.
    → Umbenannt zu `Kω_subset_M_of_cores`.
  * Wrapper‑Lemma zu `KωKeep` vorerst weggelassen (Signatur benötigt viele Parameter und
    führte zu Fehlertypisierungen). Kommt gerne wieder rein, sobald wir die exakte
    Signatur im aktuellen Projekt binden.
  * Linter‑Hinweis: kein globales `open Classical`; stattdessen `classical` im Beweis.
  * Anpassung an die tatsächliche Kurrierung von `refineN` **mit** Startzustand `s0`.
-/

import PerfectSubset.PerfectFromSuperdense

namespace Stage

/-- Wenn **jede** endliche Stufe des Kerns bereits in `M` liegt, dann liegt auch `Kω` in `M`.
    Nutzt nur die Definition von `Kω` als Schnitt der Kerne. -/
 theorem Kω_subset_M_of_cores
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (h : ∀ n : ℕ, core ((refineN tsd ha hb sel n) s0) ⊆ M) :
     Kω tsd ha hb sel s0 ⊆ M := by
   intro x hx
   classical
   -- hx : x ∈ ⋂ n, core ((refineN tsd ha hb sel n) s0)
   have hx_all : ∀ n : ℕ, x ∈ core ((refineN tsd ha hb sel n) s0) := by
     -- über die Definition von Kω als Schnitt
     simpa [Kω] using Set.mem_iInter.mp hx
   -- eine Stufe reicht, z. B. n = 0
   exact (h 0) (hx_all 0)

/-- Charakterisierung der Mitgliedschaft in `Kω` über alle Kerne der Stufen. -/
 theorem mem_Kω_iff_forall_core
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b) {x : ℝ} :
     x ∈ Kω tsd ha hb sel s0 ↔ ∀ n : ℕ, x ∈ core ((refineN tsd ha hb sel n) s0) := by
   -- direkte Entfaltung der Definition von `Kω` als Schnitt
   simp [Kω]

/-- Nichtleere von `Kω`, sobald ein Punkt in allen Stufen-Kernen liegt. -/
 theorem Kω_nonempty_of_point_mem_all_cores
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (x0 : ℝ)
     (hx : ∀ n : ℕ, x0 ∈ core ((refineN tsd ha hb sel n) s0)) :
     (Kω tsd ha hb sel s0).Nonempty := by
   refine ⟨x0, ?_⟩
   -- Mitgliedschaft in allen Stufen ⇒ Mitgliedschaft im Schnitt
   simpa [Kω] using Set.mem_iInter.mpr hx

/-- `Kω` liegt in **jeder** Stufen\-Kernmenge. -/
 theorem Kω_subset_core
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (n : ℕ) :
     Kω tsd ha hb sel s0 ⊆ core ((refineN tsd ha hb sel n) s0) := by
   intro x hx
   classical
   -- Entfalte `Kω` als Schnitt und picke die n-te Komponente.
   have hxAll : x ∈ ⋂ n, core ((refineN tsd ha hb sel n) s0) := by
     simpa [Kω] using hx
   exact (Set.mem_iInter.mp hxAll) n

/-- Allgemeine Verallgemeinerung von `Kω_subset_M_of_cores`:
    wenn jede Stufen\-Kernmenge in einer Menge `S` liegt, dann auch `Kω`. -/
 theorem Kω_subset_of_cores_subset
     {M : Set ℝ} {a b : ℝ} {S : Set ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (h : ∀ n : ℕ, core ((refineN tsd ha hb sel n) s0) ⊆ S) :
     Kω tsd ha hb sel s0 ⊆ S := by
   intro x hx
   classical
   have hxAll : ∀ n, x ∈ core ((refineN tsd ha hb sel n) s0) := by
     simpa [Kω] using Set.mem_iInter.mp hx
   exact (h 0) (hxAll 0)

/-- Bequeme Folgerung: Aus `x ∈ Kω` folgt bereits `x ∈ core ((refineN … 0) s0)`. -/
 theorem mem_core_zero_of_mem_Kω
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b) {x : ℝ}
     (hx : x ∈ Kω tsd ha hb sel s0) :
     x ∈ core ((refineN tsd ha hb sel 0) s0) :=
   (Kω_subset_core tsd ha hb sel s0 0) hx

end Stage
