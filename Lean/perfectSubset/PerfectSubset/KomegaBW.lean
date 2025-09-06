/-
  PerfectSubset/KomegaBW.lean
  "Bolzano–Weierstraß–Brücke" in separater Datei.

  Ziel: Aus Standardvoraussetzungen (Antitonie/Abgeschlossenheit/Einbettung der Kerne
  in ein kompaktes Intervall und Nichtleere jeder Stufe) folgt `Kω ≠ ∅` —
  vermittelt über die Existenz einer konvergenten Teilfolge in `Icc a b`.

  **Wichtig (modular & fehlertolerant):**
  Wir parametrisieren die eigentliche BW‑Aussage als Hypothese `BW_Icc`.
  So brauchst Du in diesem File *keine* konkreten Mathlib‑Lemma‑Namen; Du kannst
  `BW_Icc` beim Einsatz per `isCompact_Icc` belegen (z. B. über ein Lemma
  `exists_subseq_tendsto_of_forall_mem_Icc`, je nach Mathlib‑Stand).
-/
import PerfectSubset.PerfectFromSuperdense
import PerfectSubset.KomegaProperties
import PerfectSubset.KomegaCantor

open Set Filter Topology

namespace Stage

/-- **BW‑Hypothese für `Icc a b` (parametrisiert):**
    Für *jede* Folge in `Icc a b` existiert eine strikt wachsende Teilfolge
    und ein Grenzwert `x0`, so dass die Teilfolge gegen `x0` konvergiert. -/
@[simp, reducible]
def BW_Icc (a b : ℝ) : Prop :=
  ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Icc a b) →
    ∃ (φ : ℕ → ℕ) (x0 : ℝ), StrictMono φ ∧ Tendsto (fun m => x (φ m)) atTop (nhds x0)

/-- Kofinalität aus strikter Monotonie auf ℕ. -/
private lemma strictMono_nat_cofinal' {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : ∀ n : ℕ, ∃ m0 : ℕ, ∀ m ≥ m0, n ≤ φ m := by
  -- Schritt 1: Für alle m gilt m ≤ φ m (Induktion)
  have h_le_self : ∀ m, m ≤ φ m := by
    intro m; induction' m with m ih
    · exact Nat.zero_le _
    · have step : φ m + 1 ≤ φ (m+1) := by
        have : φ m < φ (m+1) := hφ (Nat.lt_succ_self m)
        exact Nat.succ_le_of_lt this
      exact le_trans (Nat.succ_le_succ ih) step
  -- Schritt 2: Kofinalität mit m0 := n
  intro n; refine ⟨n, ?_⟩
  intro m hm
  have hn_le_m : n ≤ m := hm
  have hm_le_phi : m ≤ φ m := h_le_self m
  exact le_trans hn_le_m hm_le_phi

/-- **Brückenlemma (kompakt, modular):**
    Unter Antitonie, Geschlossenheit, Nichtleere und Einbettung in `Icc a b`,
    plus einer Instanz der BW‑Hypothese für `Icc a b`, folgt `Kω ≠ ∅`. -/
 theorem Kω_nonempty_of_closed_antitone_nonempty_in_Icc_of_BW
     {M : Set ℝ} {a b : ℝ}
     (tsd : TwoSidedSuperdense M)
     (ha : a ∈ M) (hb : b ∈ M)
     (sel : Selector M a b)
     (s0 : State M a b)
     (hAntitone : Antitone (fun n : ℕ => core ((refineN tsd ha hb sel n) s0)))
     (hClosed   : ∀ n : ℕ, IsClosed (core ((refineN tsd ha hb sel n) s0)))
     (hIcc      : ∀ n : ℕ, core ((refineN tsd ha hb sel n) s0) ⊆ Icc a b)
     (hne       : ∀ n : ℕ, (core ((refineN tsd ha hb sel n) s0)).Nonempty)
     (BW        : BW_Icc a b) :
     (Kω tsd ha hb sel s0).Nonempty := by
   classical
   -- Wähle eine Folge x n ∈ core_n (aus Nichtleere)
   let x : ℕ → ℝ := fun n => Classical.choose (hne n)
   have hx_core : ∀ n, x n ∈ core ((refineN tsd ha hb sel n) s0) := by
     intro n; simpa [x] using Classical.choose_spec (hne n)
   have hx_Icc : ∀ n, x n ∈ Icc a b := fun n => hIcc n (hx_core n)
   -- Wende BW auf die Folge in Icc an
   rcases BW x hx_Icc with ⟨φ, x0, hStrict, hconv⟩
   -- Kofinalität der Indizes aus `StrictMono φ`
   have hCofinal : ∀ n, ∃ m0, ∀ m ≥ m0, n ≤ φ m := strictMono_nat_cofinal' hStrict
   -- Jetzt unsere Cantor‑Brücke anwenden
   exact
     Kω_nonempty_of_tendsto_subseq_in_cores_of_cofinal
       tsd ha hb sel s0 hAntitone hClosed hCofinal hx_core hconv

end Stage
