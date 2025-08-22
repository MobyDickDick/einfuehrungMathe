/-
  openSet.lean

  Reine Mengen- /Topologie-Aussagen über Folgen (U n), (K n) mit
    K n ⊆ M ⊆ U n
  und leerem Schnitt ⋂ n, (U n \ K n) = ∅.

  Zusätzlich: eine "naive κ" nur für OFFENE Mengen:
    - κ ∅ = 0
    - Monotonie auf offenen Mengen
    - endliche Subadditivität: κ(U ∪ V) ≤ κ U + κ V

  Keine Maßtheorie, keine Auswahlaxiome, keine BigOperators-Notation nötig.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Set

/-- Naive κ nur für offene Mengen. -/
structure NaiveKappa where
  kappa : Set ℝ → ℝ
  kappa_empty : kappa (∅ : Set ℝ) = 0
  kappa_mono_of_open :
    ∀ {A B : Set ℝ}, IsOpen A → IsOpen B → A ⊆ B → kappa A ≤ kappa B
  kappa_union_le :
    ∀ {A B : Set ℝ}, IsOpen A → IsOpen B → kappa (A ∪ B) ≤ kappa A + kappa B

namespace NaiveKappa

variable {M : Set ℝ} (κ : NaiveKappa)
variable (U K : ℕ → Set ℝ)

/-- Rahmenannahmen über die Folgen. (Für `K` genügt `IsClosed`, damit `U n \ K n` offen ist.) -/
structure CoverHypotheses (M : Set ℝ) (U K : ℕ → Set ℝ) : Prop where
  isOpenU    : ∀ n, IsOpen (U n)
  isClosedK  : ∀ n, IsClosed (K n)
  K_subset_M : ∀ n, K n ⊆ M
  M_subset_U : ∀ n, M ⊆ U n

/-- Reine Mengenlogik: Aus `⋂ n, (U n \ K n) = ∅` folgt `M ⊆ ⋃ n, K n`. -/
theorem cover_M_by_K
  (hcov : CoverHypotheses (U := U) (K := K) M)
  (hInterEmpty : (⋂ n, (U n \ K n)) = (∅ : Set ℝ)) :
  M ⊆ ⋃ n, K n := by
  classical
  intro x hxM
  by_contra hx
  have hxNotInUnion : x ∉ ⋃ n, K n := hx
  have hxNotK : ∀ n, x ∉ K n := by
    intro n hxIn; exact hxNotInUnion (mem_iUnion.mpr ⟨n, hxIn⟩)
  have hxInU : ∀ n, x ∈ U n := fun n => (hcov.M_subset_U n) hxM
  have hxInDiff : ∀ n, x ∈ U n \ K n := fun n => ⟨hxInU n, hxNotK n⟩
  have hxInInter : x ∈ ⋂ n, (U n \ K n) := by
    refine mem_iInter.mpr ?_
    intro n; exact hxInDiff n
  -- Ziel ist `False` (wegen `by_contra`). Nach Umschreiben ist `hxInInter : False`.
  simp [hInterEmpty] at hxInInter

/-- Reine Mengenlogik: Aus `⋂ n, (U n \ K n) = ∅` folgt `Mᶜ ⊆ ⋃ n, (U n)ᶜ`. -/
theorem cover_compM_by_compU
  (hcov : CoverHypotheses (U := U) (K := K) M)
  (hInterEmpty : (⋂ n, (U n \ K n)) = (∅ : Set ℝ)) :
  Mᶜ ⊆ ⋃ n, (U n)ᶜ := by
  classical
  intro x hxNotM
  -- Zeige: ¬ (∀ n, x ∈ U n) ⇒ ∃ n, x ∉ U n
  have hNotAll : ¬ (∀ n, x ∈ U n) := by
    intro hall
    have hxNotK : ∀ n, x ∉ K n := fun n hxInK => hxNotM ((hcov.K_subset_M n) hxInK)
    have hxInDiff : ∀ n, x ∈ U n \ K n := fun n => ⟨hall n, hxNotK n⟩
    have hxInInter : x ∈ ⋂ n, (U n \ K n) := by
      refine mem_iInter.mpr ?_
      intro n; exact hxInDiff n
    simp [hInterEmpty] at hxInInter
  -- daraus: ∃ n, x ∉ U n
  have : ∃ n, x ∉ U n := by
    by_contra h
    have hall : ∀ n, x ∈ U n := by
      intro n
      by_contra hx'
      exact h ⟨n, by simpa using hx'⟩
    exact hNotAll hall
  rcases this with ⟨n, hxNotU⟩
  exact mem_iUnion.mpr ⟨n, by simpa using hxNotU⟩

/-- Hilfslemma: Offenheit der „Lücken“ `U n \ K n` über `U ∩ Kᶜ`. -/
private theorem open_gap (hcov : CoverHypotheses (U := U) (K := K) M) :
  ∀ n, IsOpen (U n \ K n) := by
  intro n
  have hopenComp : IsOpen ((K n)ᶜ) := (hcov.isClosedK n).isOpen_compl
  have hopenInter : IsOpen (U n ∩ (K n)ᶜ) := (hcov.isOpenU n).inter hopenComp
  simpa [diff_eq] using hopenInter

/-- Rekursive endliche Schranke, um BigOperators zu vermeiden. -/
def Acc (bound : ℕ → ℝ) : ℕ → ℝ
| 0       => 0
| (N+1)   => Acc bound N + bound N

/-- Finitäre κ-Schranke ohne Summen-Notation:
    Angenommen für alle n gilt `κ (U n \ K n) ≤ bound n` (mit Offenheit der Differenzen).
    Dann gilt für jedes `N`:
      κ (⋃ n < N, (U n \ K n)) ≤ Acc bound N. -/
theorem kappa_union_bound_fin
  (hcov : CoverHypotheses (U := U) (K := K) M)
  (bound : ℕ → ℝ)
  (hκ : ∀ n, κ.kappa (U n \ K n) ≤ bound n) :
  ∀ N, κ.kappa (⋃ n < N, (U n \ K n)) ≤ Acc bound N := by
  classical
  -- Die Lücken sind offen:
  have hopen : ∀ n, IsOpen (U n \ K n) := open_gap (U := U) (K := K) (M := M) hcov
  -- Vereinigungen (auch zweifache iUnion) offener Mengen sind offen:
  have hopenUnion : ∀ N, IsOpen (⋃ n < N, (U n \ K n)) := by
    intro N
    exact isOpen_iUnion (fun n => isOpen_iUnion (fun _ => hopen n))

  -- Induktion über N
  intro N
  induction' N with N ih
  · -- Basis N=0
    simp [Acc, κ.kappa_empty]
  · -- Schritt N.succ
    let S : ℕ → Set ℝ := fun n => (U n \ K n)
    have split :
        (⋃ n < N.succ, S n) = (⋃ n < N, S n) ∪ S N := by
      ext x; constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨n, hx⟩
        rcases mem_iUnion.mp hx with ⟨hn, hxmem⟩
        have hlt : n < N ∨ n = N := lt_or_eq_of_le (Nat.le_of_lt_succ hn)
        cases hlt with
        | inl hlt' =>
            exact Or.inl (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hlt', hxmem⟩⟩)
        | inr heq =>
            subst heq
            exact Or.inr hxmem
      · intro hx
        rcases hx with hxL | hxR
        · rcases mem_iUnion.mp hxL with ⟨n, hx⟩
          rcases mem_iUnion.mp hx with ⟨hn, hxmem⟩
          exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Nat.lt_trans hn (Nat.lt_succ_self _), hxmem⟩⟩
        · exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨Nat.lt_succ_self _, hxR⟩⟩

    -- κ (A ∪ B) ≤ κ A + κ B
    have step_le :
        κ.kappa (⋃ n < N.succ, S n)
          ≤ κ.kappa (⋃ n < N, S n) + κ.kappa (S N) := by
      simpa [split] using
        κ.kappa_union_le (hopenUnion N) (hopen N)

    -- setze Induktionsvoraussetzung und Punkt-Bound ein
    have : κ.kappa (⋃ n < N.succ, S n)
          ≤ Acc bound N + bound N := by
      exact le_trans step_le (add_le_add ih (hκ N))

    -- Identität für Acc
    simpa [Acc] using this

end NaiveKappa
