import Mathlib

open Set MeasureTheory Topology
open scoped Topology BigOperators

namespace Satz5

noncomputable section

/-- Kurzschreibweisen für (0,1) und [0,1]. -/
def Ioo01 : Set ℝ := Ioo (0 : ℝ) 1
def Icc01 : Set ℝ := Icc (0 : ℝ) 1

/-- Eine mögliche (optionale) Formulierung von „superdicht in (0,1)“. -/
def SuperdenseIn01 (M : Set ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 < a → a < b → b < 1 → Dense (M ∩ Ioo a b)

/-- κ als Lebesgue-Außenmaß (Typ `ENNReal`). -/
def kappa (S : Set ℝ) : ENNReal := volume.toOuterMeasure S

/-- **Satz 5 (programmatische Form)**

Angenommen:
* `M ⊆ (0,1)`,
* `kappa M = 0` (hier nicht benutzt),
* `M` ist überabzählbar und superdicht (hier nicht benutzt),
* es gibt eine Gδ-Zeugenfamilie `s` mit `M = ⋂ n, s n` und alle `s n` offen,
* es gibt eine Fσ-Zeugenfamilie `t` mit `M = ⋃ n, t n` und alle `t n` abgeschlossen,

dann existieren Folgen `U n` (offen, fallend, `M ⊆ U n`) und `K n` (kompakt, wachsend, `K n ⊆ M`)
mit `⋂ n, (U n \ K n) = ∅`. -/
theorem satz5_construct_sequences
  (M : Set ℝ)
  (hM_subset : M ⊆ Ioo01)
  (_ : kappa M = 0)
  (_ : ¬ M.Countable)
  (_ : SuperdenseIn01 M)
  -- Gδ-Zeuge
  (hG : ∃ s : ℕ → Set ℝ, (∀ n, IsOpen (s n)) ∧ M = ⋂ n, s n)
  -- Fσ-Zeuge
  (hF : ∃ t : ℕ → Set ℝ, (∀ n, IsClosed (t n)) ∧ M = ⋃ n, t n) :
  ∃ (K U : ℕ → Set ℝ),
    (∀ n, IsCompact (K n) ∧ K n ⊆ M) ∧
    (∀ n, IsOpen (U n) ∧ M ⊆ U n) ∧
    (Antitone U) ∧ (Monotone K) ∧
    (⋂ n, (U n \ K n) = (∅ : Set ℝ)) := by
  classical
  rcases hG with ⟨s, hs_open, hM_iInter⟩
  rcases hF with ⟨t, ht_closed, hM_iUnion⟩

  /-========================
      U-Folge: endliche Schnitte der sₙ
    ========================-/
  -- U n := s 0 ∩ … ∩ s n (per Nat.rec)
  let U : ℕ → Set ℝ :=
    fun n => Nat.rec (s 0) (fun n Un => Un ∩ s (n+1)) n
  -- Rechengesetze für U
  have U_zero : U 0 = s 0 := by simp [U]
  have U_succ (n : ℕ) : U (n+1) = U n ∩ s (n+1) := by simp [U]

  -- Offenheit von U n
  have hU_open : ∀ n, IsOpen (U n) := by
    intro n
    refine Nat.rec (by simpa [U_zero] using hs_open 0)
      (fun n ih => by simpa [U_succ n] using ih.inter (hs_open (n+1))) n

  -- M ⊆ U n für alle n, da M = ⋂ s n
  have hU_contains : ∀ n, M ⊆ U n := by
    -- M ⊆ s k für alle k
    have hM_sub_all : ∀ k, M ⊆ s k := by
      intro k x hx
      have : x ∈ ⋂ n, s n := by simpa [hM_iInter] using hx
      exact mem_iInter.mp this k
    intro n
    refine Nat.rec (by intro x hx; simpa [U_zero] using hM_sub_all 0 hx)
      (fun n ih x hx => And.intro (ih hx) (hM_sub_all (n+1) hx)) n

  -- Ein-Schritt: U (n+1) ⊆ U n
  have stepU : ∀ n, U (n+1) ⊆ U n := by
    intro n x hx
    have hx' : x ∈ U n ∩ s (n+1) := by simpa [U_succ n] using hx
    exact hx'.left

  -- Antitonie insgesamt: m ≤ n ⇒ U n ⊆ U m
  have hU_antitone : Antitone U := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    refine Nat.rec (by simp) (fun k ih => ?_) k
    have hstep : U (m + k + 1) ⊆ U (m + k) := by
      simpa [Nat.add_assoc] using stepU (m + k)
    exact hstep.trans ih

  /-========================
      K-Folge: endliche Vereinigungen kompakter Stücke
    ========================-/
  -- [0,1] ist kompakt
  have hIcc_compact : IsCompact Icc01 := by
    simpa [Icc01] using (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))

  -- Baustein: Kpiece k := Icc01 ∩ t k
  let Kpiece : ℕ → Set ℝ := fun k => Icc01 ∩ t k

  -- Kompaktheit von Kpiece k (Schnitt von kompakt und geschlossen ist kompakt).
  -- *** Lass GENAU EINE der folgenden drei Zeilen aktiv (die bei dir vorhanden ist): ***
  have hKpiece_compact : ∀ k, IsCompact (Kpiece k) := by
    intro k
    have ht : IsClosed (t k) := ht_closed k
    -- Variante A (häufig vorhanden):
    -- simpa [Kpiece, Icc01, inter_comm] using hIcc_compact.inter_closed_left ht
    -- Variante B:
    -- simpa [Kpiece, Icc01] using hIcc_compact.inter_closed_right ht
    -- Variante C:
    simpa [Kpiece, Icc01] using IsCompact.inter_right hIcc_compact ht

  -- K 0 := Kpiece 0, K (n+1) := K n ∪ Kpiece (n+1)
  let K : ℕ → Set ℝ :=
    fun n => Nat.rec (Kpiece 0) (fun n Kn => Kn ∪ Kpiece (n+1)) n
  -- Rechengesetze für K
  have K_zero : K 0 = Kpiece 0 := by simp [K]
  have K_succ (n : ℕ) : K (n+1) = K n ∪ Kpiece (n+1) := by simp [K]

  -- Kompaktheit aller K n (endliche Vereinigung kompakter Mengen ist kompakt)
  have hK_compact : ∀ n, IsCompact (K n) := by
    intro n
    refine Nat.rec (by simpa [K_zero] using hKpiece_compact 0)
      (fun n ih => by simpa [K_succ n] using ih.union (hKpiece_compact (n+1))) n

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

  /-========================
      Leere des Schnitts ⋂ (U n \ K n)
    ========================-/
  have h_inter_empty : (⋂ n, (U n \ K n)) = (∅ : Set ℝ) := by
    apply eq_empty_iff_forall_notMem.mpr
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
    -- Lemma: Kpiece n ⊆ K n
    have Kpiece_subset_K : ∀ n, Kpiece n ⊆ K n := by
      intro n
      induction' n with n ih
      · -- n = 0
        intro x hx
        simpa [K_zero] using hx
      · -- n+1
        intro x hx
        have : x ∈ K n ∪ Kpiece (n+1) := Or.inr hx
        simpa [K_succ n] using this
    -- aus Kpiece ⊆ K folgt x ∈ K k
    have hx_in_Kk : x ∈ K k := Kpiece_subset_K k hx_in_Kpiece
    -- Widerspruch zu hx_notK k
    exact (hx_notK k) hx_in_Kk


  -- Zusammenstellen
  refine ⟨K, U, ?_, ?_, hU_antitone, hK_mono, h_inter_empty⟩
  · intro n; exact ⟨hK_compact n, hK_subset n⟩
  · intro n; exact ⟨hU_open n, hU_contains n⟩

end
end Satz5
