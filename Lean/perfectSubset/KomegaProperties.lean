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

open Filter Topology

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

/-- Aus `x ∈ Kω` folgt für **jedes** `n` die Mitgliedschaft im `n`-ten Kern. -/
 theorem mem_core_of_mem_Kω
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b) {x : ℝ}
     (hx : x ∈ Kω tsd ha hb sel s0) (n : ℕ) :
     x ∈ core ((refineN tsd ha hb sel n) s0) :=
   (Kω_subset_core tsd ha hb sel s0 n) hx

/-- Wenn es **ein** `n0` gibt mit `core ((refineN … n0) s0) ⊆ S`, dann schon `Kω ⊆ S`.
    (Einfach: `Kω ⊆ core_n0 ⊆ S`.) -/
 theorem Kω_subset_of_core_subset_at
     {M : Set ℝ} {a b : ℝ} {S : Set ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (n0 : ℕ)
     (h : core ((refineN tsd ha hb sel n0) s0) ⊆ S) :
     Kω tsd ha hb sel s0 ⊆ S := by
   intro x hx
   exact h ((Kω_subset_core tsd ha hb sel s0 n0) hx)

/-- Charakterisierung auf Mengenebene: `S ⊆ Kω` genau dann,
    wenn `S` in **jede** Stufen\-Kernmenge fällt. -/
 theorem subset_Kω_iff_forall_subset_core
     {M : Set ℝ} {a b : ℝ} {S : Set ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b) :
     S ⊆ Kω tsd ha hb sel s0 ↔ ∀ n : ℕ, S ⊆ core ((refineN tsd ha hb sel n) s0) := by
   constructor
   · intro h n x hx
     exact (Kω_subset_core tsd ha hb sel s0 n) (h hx)
   · intro h x hx
     -- `x ∈ Kω` zeigen: in allen Stufen\-Kernen
     have hxAll : ∀ n, x ∈ core ((refineN tsd ha hb sel n) s0) := fun n => h n hx
     simpa [Kω] using Set.mem_iInter.mpr hxAll

/-- Korollar: Hat man `∀ n, S ⊆ core_n`, dann schon `S ⊆ Kω`. -/
 theorem subset_Kω_of_subset_all_cores
     {M : Set ℝ} {a b : ℝ} {S : Set ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (h : ∀ n : ℕ, S ⊆ core ((refineN tsd ha hb sel n) s0)) :
     S ⊆ Kω tsd ha hb sel s0 :=
   (subset_Kω_iff_forall_subset_core tsd ha hb sel s0).mpr h

/-- Korollar: Aus `S ⊆ Kω` folgt `S ⊆ core_n` für jedes `n`. -/
 theorem subset_core_of_subset_Kω
     {M : Set ℝ} {a b : ℝ} {S : Set ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (h : S ⊆ Kω tsd ha hb sel s0) (n : ℕ) :
     S ⊆ core ((refineN tsd ha hb sel n) s0) :=
   (subset_Kω_iff_forall_subset_core tsd ha hb sel s0).mp h n

/-- **Limitpunkt-Argument (Cantor-Schiene, Schritt 1):**
    Wenn eine Folge `x : ℕ → ℝ` so gewählt ist, dass `x n ∈ core ((refineN … n) s0)`
    für alle `n`, die Kerne antiton sind und alle Kerne geschlossen sind, und
    `x` gegen `x0` konvergiert, dann liegt `x0 ∈ Kω`.

    Idee: Für jedes feste `n` ist `core_{n}` geschlossen und (wegen Antitonie) gilt
    `x m ∈ core_{n}` für alle hinreichend großen `m`. Über `IsClosed.mem_of_tendsto`
    folgt `x0 ∈ core_{n}`. Also `x0 ∈ ⋂ n core_{n} = Kω`.
-/
 theorem mem_Kω_of_tendsto_in_cores
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hAntitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0)))
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {x : ℕ → ℝ} {x0 : ℝ}
     (hx  : ∀ n : ℕ, x n ∈ core ((refineN tsd ha hb sel n) s0))
     (hconv : Filter.Tendsto x Filter.atTop (nhds x0)) :
     x0 ∈ Kω tsd ha hb sel s0 := by
   classical
   -- Für jedes feste n liegt x0 in core_n (Abschlussargument über Konvergenz)
   have hx0_in_core : ∀ n : ℕ, x0 ∈ core ((refineN tsd ha hb sel n) s0) := by
     intro n
     -- ab irgendeinem Index m ≥ n gilt x m ∈ core_n, da core_m ⊆ core_n (Antitonie)
     have hEv : ∀ᶠ m in Filter.atTop, x m ∈ core ((refineN tsd ha hb sel n) s0) := by
       refine Filter.eventually_atTop.2 ?_
       refine ⟨n, ?_⟩
       intro m hm
       have hsub : core ((refineN tsd ha hb sel m) s0) ⊆ core ((refineN tsd ha hb sel n) s0) :=
         hAntitone hm
       exact hsub (hx m)
     -- Abschluss ist abgeschlossen: Grenzwert liegt drin
     exact (hClosed n).mem_of_tendsto hconv hEv
   -- Mitgliedschaft in allen Kernen ⇒ Mitgliedschaft im Schnitt = Kω
   simpa [Kω] using Set.mem_iInter.mpr hx0_in_core

/-- **Konsequenz:** Existiert eine konvergente Auswahl `x n ∈ core_n` mit Grenzwert `x0`,
    so ist `Kω` nichtleer. -/
 theorem Kω_nonempty_of_tendsto_in_cores
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hAntitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0)))
     (hClosed : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     {x : ℕ → ℝ} {x0 : ℝ}
     (hx  : ∀ n : ℕ, x n ∈ core ((refineN tsd ha hb sel n) s0))
     (hconv : Filter.Tendsto x Filter.atTop (nhds x0)) :
     (Kω tsd ha hb sel s0).Nonempty :=
   ⟨x0, mem_Kω_of_tendsto_in_cores tsd ha hb sel s0 hAntitone hClosed hx hconv⟩

end Stage
