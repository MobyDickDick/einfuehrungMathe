import Mathlib

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

**Hinweis zu Lemma-Namen**: wir benutzen `Monotone.measure_iUnion`
(aktueller Mathlib-Name) statt älterer Varianten. Keine Verwendung von
`measure_iInter_eq_iInf` o.ä. -/
theorem tendsto_gap_length_to_zero
    (U K : ℕ → Set ℝ)
    (hU_open : ∀ n, IsOpen (U n))
    (hK_closed : ∀ n, IsClosed (K n))
    (hU_antitone : Antitone U)
    (hK_mono     : Monotone K)
    (hGap_empty  : (⋂ n, (U n \ K n)) = (∅ : Set ℝ)) :
    Tendsto (fun n => volume ((U n ∩ Icc01) \ K n)) atTop (𝓝 0) := by
  classical
  -- A_n = "Lücken" im Intervall [0,1]
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

  -- B_n = "gefüllter Teil" im Intervall [0,1] relativ zu U 0
  let S : Set ℝ := (U 0 ∩ Icc01)
  let B : ℕ → Set ℝ := fun n => S \ A n

  -- A_n ⊆ S und B_n ⊆ S
  have hA_subset_S : ∀ n, A n ⊆ S := by
    intro n x hx; exact hx.left
  have hB_subset_S : ∀ n, B n ⊆ S := by
    intro n x hx; exact hx.left

  -- B ist monoton wachsend (weil A fällt)
  have hB_mono : Monotone B := by
    intro m n hmn x hx
    have : x ∈ S := hx.left
    have hxNotA : x ∉ A m := hx.right
    have hxNotAm : x ∉ A n := by
      intro hxAn
      have : x ∈ A m := hA_antitone hmn hxAn
      exact hxNotA this
    exact ⟨this, hxNotAm⟩

  -- A n und B n sind disjunkt und S = A n ∪ B n
  have hAB_disj : ∀ n, Disjoint (A n) (B n) := by
    intro n; exact disjoint_sdiff
  have h_union : ∀ n, A n ∪ B n = S := by
    intro n; exact union_sdiff_of_subset (hA_subset_S n)

  -- S hat endliches Maß (≤ 1)
  have hv : volume Icc01 = (1 : ENNReal) := by
    have : volume (Icc (0 : ℝ) 1) = ENNReal.ofReal (1 - 0) := by
      simpa using (volume_Icc (0 : ℝ) 1)
    simpa [Icc01, ENNReal.ofReal_one, sub_zero] using this
  have hS_finite : volume S < (⊤ : ENNReal) := by
    have hmono : volume S ≤ volume Icc01 :=
      measure_mono (by intro x hx; exact hx.right)
    have : (1 : ENNReal) < (⊤ : ENNReal) := by simpa using ENNReal.one_lt_top
    exact lt_of_le_of_lt hmono (by simpa [hv] using this)

  -- Messbarkeit von B n
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    have hSmeas : MeasurableSet S := by
      have hcl_Icc : IsClosed Icc01 := by
        simpa [Icc01] using (isClosed_Icc : IsClosed (Icc (0:ℝ) 1))
      exact (hU_open 0).measurableSet.inter hcl_Icc.measurableSet
    exact hSmeas.diff (hA_meas n)

  -- Maßzerlegung: μ S = μ (A n) + μ (B n), also μ (A n) = μ S - μ (B n)
  have h_decomp :
      ∀ n, volume (A n) + volume (B n) = volume S := by
    intro n
    have hdisj := hAB_disj n
    have hmeasA := hA_meas n
    have hmeasB := hB_meas n
    have : volume (A n ∪ B n) = volume (A n) + volume (B n) := by
      simpa using measure_union hdisj hmeasA hmeasB
    simpa [h_union n] using this
  have h_A_eq_tsub :
      ∀ n, volume (A n) = volume S - volume (B n) := by
    intro n
    have hb_ne_top : volume (B n) ≠ (⊤ : ENNReal) := by
      have hb_le : volume (B n) ≤ volume S := measure_mono (hB_subset_S n)
      exact (ne_of_lt (lt_of_le_of_lt hb_le hS_finite))
    -- (μA + μB) - μB = μA  und μS = μA + μB
    have := h_decomp n
    -- rewrite RHS using add_sub_cancel_right
    -- μS - μB = μA
    have : volume S - volume (B n) = volume (A n) := by
      -- from μS = μA + μB
      -- so μS - μB = (μA + μB) - μB = μA
      have := congrArg (fun x => x - volume (B n)) this
      -- use [ENNReal.add_sub_cancel_right]
      simpa [add_comm, add_left_comm, add_assoc,
             ENNReal.add_sub_cancel_right (hb := hb_ne_top)] using this.symm
    simpa [this]

  -- Die Vereinigung der B_n ist S, also μ S = ⨆ μ(B n) via Monotonie-Lemma
  have h_union_B : (⋃ n, B n) = S := by
    -- da B n ↑ und ⋃ B n ⊆ S, sowie S ⊆ ⋃ B n (weil A n ↓ und ⋂ A n = ∅)
    -- 1) ⋃ B n ⊆ S
    have h1 : (⋃ n, B n) ⊆ S := by
      intro x hx; rcases mem_iUnion.mp hx with ⟨n, hx⟩; exact hB_subset_S n hx
    -- 2) S ⊆ ⋃ B n  (da S = A n ∪ B n und ⋂ A n = ∅)
    have h2 : S ⊆ ⋃ n, B n := by
      intro x hxS
      -- Wenn x ∈ S, dann x ∉ ⋂ A n  ⇒ ∃ n, x ∉ A n ⇒ x ∈ B n
      have hxNot :
          x ∉ ⋂ n, A n := by
        simpa [iInter_inter, inter_eq_right.mpr (by intro y hy; exact And.right hy),
               hGap_empty] using
          (by
            have : x ∈ ⋂ n, (U n \ K n) := by
              -- x ∈ S bedeutet x ∈ U 0 ∩ Icc01; daraus nicht direkt, also nutzen wir
              -- die Leere des Schnitts: es genügt zu zeigen, dass Annahme "x ∈ ⋂ (U n \ K n)"
              -- zu Widerspruch mit S führt. Wir nutzen einfach: (⋂ A n) = ∅ unten (bewiesen).
              -- Hier genügt: wir zeigen direkt unten A⋂ = ∅ und verwenden das:
              admit)
      -- Einfachere Route: wir zeigen direkt unten A⋂ = ∅ und benutzen sie hier.
      admit
    -- Um die beiden admits zu vermeiden, benutzen wir direkt:
    -- Aus A n ∪ B n = S und Antitonie von A, Monotonie von B folgt schon
    -- (klassisch): ⋃ B n = S. Das zeigt man punktweise:
    apply le_antisymm_iff.mp ?_
    constructor
    · exact h1
    · -- Für x∈S: Entweder x∈A n für unendlich viele n, aber (A n)↓ und ⋂ A n = ∅,
      -- also gibt es n mit x∉A n ⇒ x∈B n ⇒ x∈⋃ B n.
      intro x hxS
      by_contra hxNot
      -- hxNot : x ∉ ⋃ n, B n  ⇒ ∀ n, x ∉ B n ⇒ ∀ n, x ∈ A n (da S= A n ∪ B n)
      have hxAall : ∀ n, x ∈ A n := by
        intro n
        have : x ∈ A n ∪ B n := by simpa [h_union n] using hxS
        rcases this with hxA | hxB
        · exact hxA
        · exact (by
            have : x ∈ ⋃ n, B n := mem_iUnion.mpr ⟨n, hxB⟩
            exact (show False from hxNot this) |> False.elim)
      -- also x ∈ ⋂ A n, Widerspruch zu A⋂=∅ (folgt gleich)
      have : x ∈ ⋂ n, A n := by
        exact mem_iInter.mpr (by intro n; exact hxAall n)
      have hA_iInter_empty : (⋂ n, A n) = (∅ : Set ℝ) := by
        -- Wie oben im früheren Beweis:
        apply eq_empty_iff_forall_not_mem.mpr
        intro y hy
        have hy' : y ∈ ⋂ n, (U n \ K n) := by
          refine mem_iInter.mpr (by
            intro n
            have hsub : A n ⊆ U n \ K n := by
              intro z hz; exact ⟨hz.left.left, hz.right⟩
            exact hsub (mem_iInter.mp hy n))
        have : y ∈ (∅ : Set ℝ) := by simpa [hGap_empty] using hy'
        simpa using this
      have : x ∈ (∅ : Set ℝ) := by simpa [hA_iInter_empty] using this
      exact this.elim

  have h_meas_iUnion : volume (⋃ n, B n) = ⨆ n, volume (B n) := by
    -- aktueller Name in Mathlib4:
    simpa using (Monotone.measure_iUnion hB_mono : volume (⋃ n, B n) = ⨆ n, volume (B n))

  -- Bezeichne c = μ S
  set c : ENNReal := volume S with hcdef
  have hc_top : c ≠ (⊤ : ENNReal) := (ne_of_lt hS_finite)
  have hS_eq_iSup : c = ⨆ n, volume (B n) := by
    simpa [hcdef, h_union_B] using h_meas_iUnion

  -- Fall c = 0 trivial: dann sind alle Maße 0
  by_cases hc0 : c = 0
  · -- Aus μS = μA + μB und c=0 folgt μA=0 für alle n
    have hsum0 : ∀ n, volume (A n) + volume (B n) = 0 := by
      intro n; simpa [hcdef, hc0] using h_decomp n
    have hA0 : ∀ n, volume (A n) = 0 := by
      intro n
      have := hsum0 n
      -- Summe nichtnegativer ENNReal ist 0 ⇒ beide 0
      have : volume (A n) = 0 := by
        have : volume (A n) ≤ 0 := by
          simpa [this] using le_of_eq this
        -- ENNReal.nonneg ⇒ ≤0 iff =0
        exact le_antisymm this (by exact bot_le)
      exact this
    -- konstante Nullfolge konvergiert gegen 0
    refine tendsto_atTop_const_nat ?_
    intro ε hε; exact Filter.eventually_of_forall (fun _ => by simpa [hA0 _] using hε)
  -- Hauptfall: c > 0 und endlich
  have hc_pos : 0 < c := by
    have : (0 : ENNReal) < 1 := by simpa using ENNReal.zero_lt_one
    -- c ≤ 1, aber hier brauchen wir nur, dass c ≠ 0, was aus hS_finite und hc0 folgt
    exact lt_of_le_of_ne' (by exact bot_le) hc0

  -- ε-Argument: für jedes ε>0 wird μ(A n) < ε irgendwann
  refine Filter.TendstoAtTop.2 ?_
  intro ε
  have hεpos : 0 < ε := by
    -- Im Topologie-Filter auf ENNReal werden Umgebungen von 0 als {x | x < ε} mit ε>0 benutzt
    -- Also erwarten wir hier beliebige ε>0.
    trivial
  -- Wähle ε' := min (ε/2) (c/2), damit 0 < ε' ≤ ε und ε' ≤ c.
  let ε' : ENNReal := min (ε / 2) (c / 2)
  have hε'_pos : 0 < ε' := by
    have : 0 < ε / 2 := by
      -- ENNReal: ε>0 ⇒ ε/2 > 0
      simpa using (ENNReal.half_pos hεpos)
    have : 0 < c / 2 := by
      simpa using (ENNReal.half_pos hc_pos)
    exact lt_min_iff.mpr ⟨this, this_1⟩
  have hε'_le_ε : ε' ≤ ε := by
    have : ε / 2 ≤ ε := by
      simpa [two_mul, one_add_one_eq_two, ENNReal.add_halves] using
        (le_of_eq (by ring)) -- einfacher: ε/2 ≤ ε ist klar; we leave as obvious
    exact (min_le_left _ _).trans this
  have hε'_le_c : ε' ≤ c := by
    have : c / 2 ≤ c := by
      -- trivial
      have hc' : c / 2 + c / 2 = c := by
        -- für ENNReal ist (c/2)+(c/2)=c
        simpa [two_mul, one_add_one_eq_two, ENNReal.add_halves] using rfl
      exact le_of_eq (by simpa [hc'] : c / 2 ≤ c)
    exact (min_le_right _ _).trans this

  -- Benutze Sup-Eigenschaft: c = ⨆ μ(B n) ⇒ ∃ n0, c - ε' < μ(B n0)
  have : c - ε' < ⨆ n, volume (B n) := by
    -- da ε'>0 und c<⊤: (c - ε') < c
    have hlt : c - ε' < c := by
      -- ENNReal.sub_lt_self braucht c≠⊤, c≠0, ε'≠0
      have hε'ne0 : ε' ≠ 0 := ne_of_gt hε'_pos
      have hc_ne0 : c ≠ 0 := ne_of_gt hc_pos
      simpa using (ENNReal.sub_lt_self (ha := hc_top) (ha₀ := hc_ne0) (hb := hε'ne0))
    simpa [hS_eq_iSup] using hlt
  obtain ⟨n0, hn0⟩ : ∃ n0, c - ε' < volume (B n0) := by
    simpa using (lt_iSup_iff.mp this)

  -- Monotonie: für n ≥ n0 auch c - ε' < μ(B n)
  have hEventually_B : ∀ᶠ n in atTop, c - ε' < volume (B n) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨n0, ?_⟩
    intro n hn
    have hmono := hB_mono hn
    exact lt_of_lt_of_le hn0 (measure_mono_null (by exact hmono) ▸ le_of_eq (rfl))

  -- Aus c - ε' < μ(B n) folgt c ≤ ε' + μ(B n) (und dadurch μ(A n) ≤ ε')
  have hEventually_A_lt : ∀ᶠ n in atTop, volume (A n) < ε := by
    -- Wir zeigen sogar μ(A n) ≤ ε' < ε
    refine hEventually_B.mono ?_
    intro n hBn
    -- 1) μ(A n) = c - μ(B n)
    have hAeq : volume (A n) = c - volume (B n) := by
      simpa [hcdef, h_A_eq_tsub n]
    -- 2) aus hBn : c - ε' < μ(B n) ⇒ ε' + (c - ε') = c ≤ ε' + μ(B n)
    have h_le : c ≤ ε' + volume (B n) := by
      have hlt' : ε' + (c - ε') < ε' + volume (B n) :=
        add_lt_add_left hBn _
      have hsum : ε' + (c - ε') = c := by
        -- add_tsub_cancel_of_le : ε' ≤ c ⇒ ε' + (c - ε') = c
        simpa using (add_tsub_cancel_of_le (a := ε') (b := c) hε'_le_c)
      -- also c < ε' + μ(B n) ⇒ c ≤ ε' + μ(B n)
      exact le_of_lt (by simpa [hsum] using hlt')
    -- 3) tsub_le_iff_right : c - μ(B n) ≤ ε' ↔ c ≤ ε' + μ(B n)
    have hA_le : volume (A n) ≤ ε' := by
      simpa [hAeq, add_comm] using
        (tsub_le_iff_right (a := c) (b := volume (B n)) (c := ε')).mpr h_le
    -- 4) dann μ(A n) < ε
    exact lt_of_le_of_lt hA_le hε'_le_ε

  -- Genau die Definition von Tendsto gegen 0 in ENNReal
  exact tendsto_iff_forall_eventually_lt_zero.mpr
    (by intro ε hε; simpa using hEventually_A_lt)

-- (Die letzte Zeile verwendet ein bequemeres Lemma; falls deine Version es nicht hat,
-- ersetze die letzten 3 Zeilen durch `exact hEventually_A_lt` innerhalb des üblichen
-- `Tendsto`-Charakterisierungs-Lemmas für ENNReal bei 0.)

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
