import Mathlib
import Mathlib/MeasureTheory/Measure/Continuity
-- set_option diagnostics true

open Set MeasureTheory Topology Filter
open scoped Topology BigOperators

namespace Satz5

noncomputable section

/-- Kurzschreibweisen für (0,1) und [0,1]. -/
def Ioo01 : Set ℝ := Ioo 0 1
def Icc01 : Set ℝ := Icc 0 1

/-- Eine mögliche (optionale) Formulierung von „superdicht in (0,1)“. -/
def SuperdenseIn01 (M : Set ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 < a → a < b → b < 1 → Dense (M ∩ Ioo a b)

/-- κ als Lebesgue-Außenmaß (Typ `ENNReal`). -/
def kappa (S : Set ℝ) : ENNReal := volume.toOuterMeasure S

/-- **Satz 5 (programmative Form)** – konstruiert fallende offene `U n` und
wachsende abgeschlossene `K n` mit `⋂ n, (U n \ K n) = ∅`. -/
theorem satz5_construct_sequences
  (M : Set ℝ)
  (hM_subset : M ⊆ Ioo01)
  (_ : kappa M = 0)
  (_ : ¬ M.Countable)
  (_ : SuperdenseIn01 M)
  (hG : ∃ s : ℕ → Set ℝ, (∀ n, IsOpen (s n)) ∧ M = ⋂ n, s n)
  (hF : ∃ t : ℕ → Set ℝ, (∀ n, IsClosed (t n)) ∧ M = ⋃ n, t n) :
  ∃ (K U : ℕ → Set ℝ),
    (∀ n, IsClosed (K n) ∧ K n ⊆ M) ∧
    (∀ n, IsOpen (U n) ∧ M ⊆ U n) ∧
    (Antitone U) ∧ (Monotone K) ∧
    (⋂ n, (U n \ K n) = (∅ : Set ℝ)) := by
  classical
  rcases hG with ⟨s, hs_open, hM_iInter⟩
  rcases hF with ⟨t, ht_closed, hM_iUnion⟩

  -- U-Folge: endliche Schnitte von s
  let U : ℕ → Set ℝ :=
    fun n => Nat.rec (s 0) (fun n Un => Un ∩ s (n+1)) n
  have U_zero : U 0 = s 0 := by simp [U]
  have U_succ (n : ℕ) : U (n+1) = U n ∩ s (n+1) := by simp [U]

  have hU_open : ∀ n, IsOpen (U n) := by
    intro n
    refine Nat.rec (by simpa [U_zero] using hs_open 0)
      (fun n ih => by simpa [U_succ n] using ih.inter (hs_open (n+1))) n

  have hU_contains : ∀ n, M ⊆ U n := by
    have hM_sub_all : ∀ k, M ⊆ s k := by
      intro k x hx
      have : x ∈ ⋂ n, s n := by simpa [hM_iInter] using hx
      exact mem_iInter.mp this k
    intro n
    refine Nat.rec (by intro x hx; simpa [U_zero] using hM_sub_all 0 hx)
      (fun n ih x hx => And.intro (ih hx) (hM_sub_all (n+1) hx)) n

  have stepU : ∀ n, U (n+1) ⊆ U n := by
    intro n x hx
    have hx' : x ∈ U n ∩ s (n+1) := by simpa [U_succ n] using hx
    exact hx'.left

  have hU_antitone : Antitone U := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    refine Nat.rec (by simp) (fun k ih => ?_) k
    have hstep : U (m + k + 1) ⊆ U (m + k) := by
      simpa [Nat.add_assoc] using stepU (m + k)
    exact hstep.trans ih

  -- K-Folge: endliche Vereinigungen von Icc01 ∩ t k (nur Abgeschlossenheit benötigt)
  let Kpiece : ℕ → Set ℝ := fun k => Icc01 ∩ t k
  have hKpiece_closed : ∀ k, IsClosed (Kpiece k) := by
    intro k
    have hIcc_closed : IsClosed Icc01 := by
      simpa [Icc01] using (isClosed_Icc : IsClosed (Icc (0 : ℝ) 1))
    simpa [Kpiece] using hIcc_closed.inter (ht_closed k)

  let K : ℕ → Set ℝ :=
    fun n => Nat.rec (Kpiece 0) (fun n Kn => Kn ∪ Kpiece (n+1)) n
  have K_zero : K 0 = Kpiece 0 := by simp [K]
  have K_succ (n : ℕ) : K (n+1) = K n ∪ Kpiece (n+1) := by simp [K]

  have hK_closed : ∀ n, IsClosed (K n) := by
    intro n
    refine Nat.rec (by simpa [K_zero] using hKpiece_closed 0)
      (fun n ih => by
        have : IsClosed (Kpiece (n+1)) := hKpiece_closed (n+1)
        simpa [K_succ n] using ih.union this) n

  -- Aus M = ⋃ t n folgt: t k ⊆ M für alle k
  have ht_sub_M : ∀ k, t k ⊆ M := by
    intro k x hx
    have : x ∈ ⋃ n, t n := mem_iUnion.mpr ⟨k, hx⟩
    simpa [hM_iUnion] using this

  -- Daher Kpiece k ⊆ M und folglich K n ⊆ M
  have hKpiece_subset_M : ∀ k, Kpiece k ⊆ M := by
    intro k x hx; exact ht_sub_M k hx.right

  have hK_subset : ∀ n, K n ⊆ M := by
    intro n
    refine Nat.rec (by simpa [K_zero] using hKpiece_subset_M 0)
      (fun n ih => ?_) n
    intro x hx
    have hx' : x ∈ K n ∪ Kpiece (n+1) := by simpa [K_succ n] using hx
    cases hx' with
    | inl hxKn => exact ih hxKn
    | inr hxKp => exact hKpiece_subset_M (n+1) hxKp

  -- Monotonie von K
  have hK_mono : Monotone K := by
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    refine Nat.rec (by simp) (fun k ih => ?_) k
    intro x hx
    have hx' : x ∈ K (i + k) := ih hx
    have : x ∈ K (i + k) ∪ Kpiece (i + k + 1) := Or.inl hx'
    simpa [K_succ (i + k)] using this

  -- Leere des Schnitts ⋂ (U n \ K n)
  have h_inter_empty : (⋂ n, (U n \ K n)) = (∅ : Set ℝ) := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    -- aus hx: x ∈ U n und x ∉ K n für alle n
    have hxU : ∀ n, x ∈ U n := fun n => (mem_iInter.mp hx n).left
    have hx_notK : ∀ n, x ∉ K n := fun n => (mem_iInter.mp hx n).right

    -- aus x ∈ U n folgt x ∈ s n für alle n
    have hx_in_all_s : ∀ n, x ∈ s n := by
      intro n
      refine Nat.rec (by simpa [U_zero] using hxU 0)
        (fun n ih => ?_) n
      have hxUn1 : x ∈ U (n+1) := hxU (n+1)
      have : x ∈ U n ∩ s (n+1) := by simpa [U_succ n] using hxUn1
      exact this.right

    -- x ∈ M (da x ∈ ⋂ s n)
    have hxM : x ∈ M := by
      have : x ∈ ⋂ n, s n := mem_iInter.mpr (by intro n; exact hx_in_all_s n)
      simpa [hM_iInter] using this

    -- daraus x ∈ Icc01 (weil M ⊆ Ioo01 ⊆ Icc01)
    have hx_Icc : x ∈ Icc01 := by
      have hx_Ioo : x ∈ Ioo01 := hM_subset hxM
      exact ⟨le_of_lt hx_Ioo.1, le_of_lt hx_Ioo.2⟩

    -- aus M = ⋃ t n folgt ∃ k, x ∈ t k
    obtain ⟨k, hx_tk⟩ : ∃ k, x ∈ t k := by
      have : x ∈ ⋃ n, t n := by simpa [hM_iUnion] using hxM
      exact mem_iUnion.mp this

    -- dann x ∈ Kpiece k ⊆ K k, Widerspruch zu hx_notK k
    have hx_in_Kpiece : x ∈ Kpiece k := ⟨hx_Icc, hx_tk⟩
    have Kpiece_subset_K : ∀ n, Kpiece n ⊆ K n := by
      intro n
      induction' n with n ih
      · intro x hx; simpa [K_zero] using hx
      · intro x hx
        have : x ∈ K n ∪ Kpiece (n+1) := Or.inr hx
        simpa [K_succ n] using this
    have hx_in_Kk : x ∈ K k := Kpiece_subset_K k hx_in_Kpiece
    exact (hx_notK k) hx_in_Kk

  refine ⟨K, U, ?_, ?_, hU_antitone, hK_mono, h_inter_empty⟩
  · intro n; exact ⟨hK_closed n, hK_subset n⟩
  · intro n; exact ⟨hU_open n, hU_contains n⟩

/-- **Hilfssatz (Grenzwert der Lücken)**:
Für fallende offene `U`, wachsende abgeschlossene `K` und `⋂ n, (U n \ K n) = ∅`
gilt `volume ((U n ∩ [0,1]) \ K n) → 0`.
(Beweis ohne `tendsto_measure_iInter_of_measurableSet_decreasing`,
per `tendsto_atTop_iInf` + `measure_iInter_eq_iInf`.) -/
theorem tendsto_gap_length_to_zero
    (U K : ℕ → Set ℝ)
    (hU_open : ∀ n, IsOpen (U n))
    (hK_closed : ∀ n, IsClosed (K n))
    (hU_antitone : Antitone U)
    (hK_mono     : Monotone K)
    (hGap_empty  : (⋂ n, (U n \ K n)) = (∅ : Set ℝ)) :
    Tendsto (fun n => volume ((U n ∩ Icc01) \ K n)) atTop (𝓝 0) := by
  classical
  let A : ℕ → Set ℝ := fun n => (U n ∩ Icc01) \ K n

  -- Messbarkeit (offen / abgeschlossen ⇒ messbar)
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    have hcl_Icc : IsClosed Icc01 := by
      simpa [Icc01] using (isClosed_Icc : IsClosed (Icc (0:ℝ) 1))
    have hmeasU : MeasurableSet (U n) := (hU_open n).measurableSet
    have hmeasIcc : MeasurableSet Icc01 := hcl_Icc.measurableSet
    have hmeasK : MeasurableSet (K n) := (hK_closed n).measurableSet
    simpa [A] using (hmeasU.inter hmeasIcc).diff hmeasK

  -- Antitonie der Lücken
  have hA_antitone : Antitone A := by
    intro m n hmn x hx
    rcases hx with ⟨hxU, hxNotK⟩
    rcases hxU with ⟨hxUm, hxIcc⟩
    have hxUn : x ∈ U m := (hU_antitone hmn) hxUm
    have hxNotKm : x ∉ K m := by
      intro hxKm
      have : x ∈ K n := (hK_mono hmn) hxKm
      exact hxNotK this
    exact ⟨⟨hxUn, hxIcc⟩, hxNotKm⟩

  -- Leerer Schnitt (auch nach Schnitt mit [0,1])
  have hA_iInter_empty : (⋂ n, A n) = (∅ : Set ℝ) := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hx' : x ∈ ⋂ n, (U n \ K n) := by
      refine mem_iInter.mpr (by
        intro n
        have hsub : A n ⊆ U n \ K n := by
          intro y hy; exact ⟨hy.left.left, hy.right⟩
        exact hsub (mem_iInter.mp hx n))
    have : x ∈ (∅ : Set ℝ) := by
      simpa [hGap_empty] using hx'
    simpa using this

  -- μ([0,1]) endlich ⇒ μ(A 0) endlich (nur über explizite Formel)
  have hv : volume Icc01 = (1 : ENNReal) := by
    have : volume (Icc (0 : ℝ) 1) = ENNReal.ofReal (1 - 0) := by
      simpa using (volume_Icc (0 : ℝ) 1)
    simpa [Icc01, ENNReal.ofReal_one, sub_zero] using this
  have hIcc_finite : volume Icc01 < (⊤ : ENNReal) := by
    have : (1 : ENNReal) < (⊤ : ENNReal) := by simpa using ENNReal.one_lt_top
    simpa [hv] using this
  have hA0_subset_Icc : A 0 ⊆ Icc01 := by
    intro x hx; exact hx.left.right
  have hA0_finite : volume (A 0) < (⊤ : ENNReal) := by
    have hmono : volume (A 0) ≤ volume Icc01 := measure_mono hA0_subset_Icc
    exact lt_of_le_of_lt hmono hIcc_finite

  -- **Fallback ohne Speziallemma**:
  -- (1) Volumina sind antiton, weil A antiton und μ monoton in der Menge
  have hVol_antitone : Antitone (fun n => volume (A n)) := by
    intro m n hmn
    exact measure_mono (hA_antitone hmn)

  -- (2) Lim atTop einer antitonen Folge = iInf der Werte
  have h_tendsto_iInf :
      Tendsto (fun n => volume (A n)) atTop
              (𝓝 (iInf fun n => volume (A n))) :=
    tendsto_atTop_iInf hVol_antitone

  -- (3) Kontinuität von oben für Maß: μ(⋂ A n) = ⨅ μ(A n)
  have h_meas_iInf :
      volume (⋂ n, A n) = ⨅ n, volume (A n) :=
    measure_iInter (μ := volume) (s := A)
      hA_meas hA_antitone (ne_of_lt hA0_finite)

  -- (4) Umschreiben und Ziel „→ 0“
  have h_tendsto :
      Tendsto (fun n => volume (A n)) atTop (𝓝 (volume (⋂ n, A n))) := by
    simpa [h_meas_iInf] using h_tendsto_iInf

  -- Schließlich: ⋂ A n = ∅ ⇒ Maß = 0
  simpa [A, hA_iInter_empty] using h_tendsto

/-- **Korollar aus Satz 5**: Aus `satz5_construct_sequences` folgt
`volume ((U n ∩ [0,1]) \ K n) → 0`. -/
theorem tendsto_gap_from_satz5
  (M : Set ℝ)
  (hM_subset : M ⊆ Ioo01)
  (h_kappa0 : kappa M = 0)
  (h_uncount : ¬ M.Countable)
  (h_super : SuperdenseIn01 M)
  (hG : ∃ s : ℕ → Set ℝ, (∀ n, IsOpen (s n)) ∧ M = ⋂ n, s n)
  (hF : ∃ t : ℕ → Set ℝ, (∀ n, IsClosed (t n)) ∧ M = ⋃ n, t n) :
  ∃ (K U : ℕ → Set ℝ),
    (∀ n, IsClosed (K n) ∧ K n ⊆ M) ∧
    (∀ n, IsOpen (U n) ∧ M ⊆ U n) ∧
    (Antitone U) ∧ (Monotone K) ∧
    (⋂ n, (U n \ K n) = (∅ : Set ℝ)) ∧
    Tendsto (fun n => volume ((U n ∩ Icc01) \ K n)) atTop (𝓝 0) := by
  classical
  rcases satz5_construct_sequences M hM_subset h_kappa0 h_uncount h_super hG hF with
    ⟨K, U, hK, hU, hU_antitone, hK_mono, hGap⟩
  have hU_open : ∀ n, IsOpen (U n) := fun n => (hU n).1
  have hK_closed : ∀ n, IsClosed (K n) := fun n => (hK n).1
  have hT : Tendsto (fun n => volume ((U n ∩ Icc01) \ K n)) atTop (𝓝 0) :=
    tendsto_gap_length_to_zero U K hU_open hK_closed hU_antitone hK_mono hGap
  exact ⟨K, U, hK, hU, hU_antitone, hK_mono, hGap, hT⟩

end
end Satz5
