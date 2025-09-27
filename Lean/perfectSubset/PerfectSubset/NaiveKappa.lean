import Mathlib

open Set
open scoped BigOperators

noncomputable section
namespace PerfectSubset

/-
  Maßfreier Rahmen mit äußerer Größe kappa : Set ℝ → ENNReal.

  Axiome:
  * empty : kappa ∅ = 0
  * mono  : Monotonie
  * subadd_union : (binäre) Subadditivität  kappa(A ∪ B) ≤ kappa A + kappa B
  * add_disjoint_compact : endliche Additivität (Grundfall für zwei disjunkte Kompakte)
  * zero_of_noPosCompact : "kompakter Nullrest": enthält A keine kompakte Teilmenge mit kappa>0,
      dann kappa A = 0
  * cont_from_above : Stetigkeit von oben für absteigende Folgen (Antitone) von Mengen
-/
structure NaiveKappa (kappa : Set ℝ → ENNReal) : Prop where
  empty : kappa (∅ : Set ℝ) = 0
  mono  : ∀ {A B : Set ℝ}, A ⊆ B → kappa A ≤ kappa B
  subadd_union :
    ∀ A B : Set ℝ, kappa (A ∪ B) ≤ kappa A + kappa B
  add_disjoint_compact :
    ∀ {K L : Set ℝ}, IsCompact K → IsCompact L →
      Disjoint K L → kappa (K ∪ L) = kappa K + kappa L
  zero_of_noPosCompact :
    ∀ A : Set ℝ,
      (∀ K : Set ℝ, IsCompact K → K ⊆ A → kappa K = 0) →
      kappa A = 0
  cont_from_above :
    ∀ (B : ℕ → Set ℝ), Antitone B →
      kappa (⋂ n, B n) = iInf (fun n => kappa (B n))

namespace NaiveKappa

variable {kappa : Set ℝ → ENNReal}
variable (NK : NaiveKappa kappa)

/-- Inneres Kompaktmaß (maßfrei): Supremum der kappa-Werte über kompakte Teilmengen von `M`. -/
def nu (kappa : Set ℝ → ENNReal) (M : Set ℝ) : ENNReal :=
  iSup (fun (K : {S : Set ℝ // IsCompact S ∧ S ⊆ M}) => kappa (K : Set ℝ))

lemma nu_mono {A B : Set ℝ} (hAB : A ⊆ B) :
  nu (kappa := kappa) A ≤ nu (kappa := kappa) B := by
  refine iSup_le ?_
  intro K
  rcases K with ⟨S, hSc, hSsub⟩
  exact
    le_iSup_of_le ⟨S, ⟨hSc, hSsub.trans hAB⟩⟩ (le_of_eq rfl)

/-- Supremum der **endlichen** Block-Summen zur Zerlegung `K`. -/
def sumBlocks (kappa : Set ℝ → ENNReal) (K : ℕ → Set ℝ) : ENNReal :=
  iSup (fun (s : Finset ℕ) => Finset.sum s (fun n => kappa (K n)))

/-! ## Hilfslemmas über endliche Vereinigungen kompakter Mengen -/

lemma isCompact_iUnion_finset
    {K : ℕ → Set ℝ} (hKc : ∀ n, IsCompact (K n)) :
    ∀ s : Finset ℕ, IsCompact (⋃ n ∈ s, K n) := by
  classical
  intro s
  refine Finset.induction_on s ?base ?step
  · -- s = ∅
    have : (⋃ n ∈ (∅ : Finset ℕ), K n) = (∅ : Set ℝ) := by
      ext x; simp
    simp
  · intro a s ha hcomp
    have hsplit :
      (⋃ n ∈ insert a s, K n) = K a ∪ (⋃ n ∈ s, K n) := by
      ext x; constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hmem, hxKi⟩
        rcases Finset.mem_insert.mp hmem with hia | his
        · subst hia; exact Or.inl hxKi
        · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hxKi⟩⟩)
      · intro hx
        rcases hx with hx | hx
        · exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨by simp, hx⟩⟩
        · rcases mem_iUnion.mp hx with ⟨i, hi⟩
          rcases mem_iUnion.mp hi with ⟨his, hxKi⟩
          exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by
            simpa [Finset.mem_insert] using Or.inr his, hxKi⟩⟩
    have : IsCompact (K a ∪ (⋃ n ∈ s, K n)) :=
      (hKc a).union hcomp
    simpa [hsplit] using this

lemma disjoint_singleton_union_finset
    {K : ℕ → Set ℝ}
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∀ {a : ℕ} {s : Finset ℕ}, a ∉ s → Disjoint (K a) (⋃ n ∈ s, K n) := by
  classical
  intro a s ha
  refine disjoint_left.mpr ?_
  intro x hxKa hxUnion
  rcases mem_iUnion.mp hxUnion with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨his, hxKi⟩
  have hne : a ≠ i := by intro h; subst h; exact ha his
  exact (hdisj hne).le_bot ⟨hxKa, hxKi⟩

/-- Endliche Additivität auf Finsets:
    kappa(⋃_{n∈s} K n) = ∑_{n∈s} kappa(K n),
    wenn die `K n` kompakt und paarweise disjunkt sind. -/
lemma kappa_union_finset_eq_sum
    (NK : NaiveKappa kappa)
    {K : ℕ → Set ℝ}
    (hKc : ∀ n, IsCompact (K n))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∀ s : Finset ℕ,
    kappa (⋃ n ∈ s, K n) = Finset.sum s (fun n => kappa (K n)) := by
   classical
  intro s
  refine Finset.induction_on s ?base ?step
  · -- s = ∅
    have : (⋃ n ∈ (∅ : Finset ℕ), K n) = (∅ : Set ℝ) := by
      ext x; simp
    simp [NK.empty]
  · intro a s ha hIH
    have hdisj' : Disjoint (K a) (⋃ n ∈ s, K n) :=
      disjoint_singleton_union_finset (K := K) hdisj (a := a) (s := s) ha
    have hcomp_left : IsCompact (K a) := hKc a
    have hcomp_right : IsCompact (⋃ n ∈ s, K n) :=
      isCompact_iUnion_finset (K := K) hKc s
    have hsplit :
      (⋃ n ∈ insert a s, K n) = K a ∪ (⋃ n ∈ s, K n) := by
      ext x; constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hmem, hxKi⟩
        rcases Finset.mem_insert.mp hmem with hia | his
        · subst hia; exact Or.inl hxKi
        · exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨his, hxKi⟩⟩)
      · intro hx
        rcases hx with hx | hx
        · exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨by simp, hx⟩⟩
        · rcases mem_iUnion.mp hx with ⟨i, hi⟩
          rcases mem_iUnion.mp hi with ⟨his, hxKi⟩
          exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by
            simpa [Finset.mem_insert] using Or.inr his, hxKi⟩⟩
    calc
      kappa (⋃ n ∈ insert a s, K n)
          = kappa (K a ∪ (⋃ n ∈ s, K n)) := by simp
      _ = kappa (K a) + kappa (⋃ n ∈ s, K n) :=
          NK.add_disjoint_compact hcomp_left hcomp_right hdisj'
      _ = kappa (K a) + Finset.sum s (fun n => kappa (K n)) := by
          simp [hIH]
      _ = Finset.sum (insert a s) (fun n => kappa (K n)) := by
        classical
        exact
          (Finset.sum_insert
            (s := s) (a := a) (f := fun n => kappa (K n))
            (by simpa using ha)).symm

/-! ## Hauptsatz: kompakte Zerlegung mit Nullrest ⇒ Summe = inneres Kompaktmaß -/

/-- Hauptsatz (maßfrei).
    Zerlegung: `K : ℕ → Set ℝ` kompakt, paarweise disjunkt, in `M`;
    Rest `R := M \ ⋃ n, K n` hat keinen kompakten Positivteil.
    Dann gilt: `sumBlocks (kappa := kappa) K = nu (kappa := kappa) M`. -/
theorem sumBlocks_compactDecomp_eq_nu
    (NK : NaiveKappa kappa)
    {M : Set ℝ} (K : ℕ → Set ℝ)
    (hKc : ∀ n, IsCompact (K n))
    (hKsub : ∀ n, K n ⊆ M)
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hRest0 :
      ∀ L : Set ℝ, IsCompact L → L ⊆ M \ ⋃ n, K n → kappa L = 0) :
    sumBlocks (kappa := kappa) K = nu (kappa := kappa) M := by
  classical
  -- Restmenge
  set R : Set ℝ := M \ ⋃ n, K n

  -- (1) ≤-Richtung
  have h_le : sumBlocks (kappa := kappa) K ≤ nu (kappa := kappa) M := by
    refine iSup_le ?_
    intro s
    -- Kompaktheit der endlichen Vereinigung und Inklusion in M
    have hcomp := isCompact_iUnion_finset (K := K) hKc s
    have hsubM : (⋃ n ∈ s, K n) ⊆ M := by
      intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨_, hxKi⟩
      exact hKsub i hxKi
    -- κ(⋃_s K) ≤ ν(M)
    have h_to_nu :
        kappa (⋃ n ∈ s, K n) ≤ nu (kappa := kappa) M :=
      le_iSup_of_le ⟨(⋃ n ∈ s, K n), ⟨hcomp, hsubM⟩⟩ (le_of_eq rfl)
    -- κ(⋃_s K) = Summe ⇒ Summe ≤ ν(M)
    have h_eq := kappa_union_finset_eq_sum (NK := NK) (K := K) hKc hdisj s
    simpa [sumBlocks, h_eq] using h_to_nu

  -- (2) ≥-Richtung
  have h_ge : nu (kappa := kappa) M ≤ sumBlocks (kappa := kappa) K := by
    refine iSup_le ?_
    intro KL; rcases KL with ⟨L, hLc, hLsub⟩
    -- endliche Teilvereinigungen und Restmengen
    let U : ℕ → Set ℝ := fun N => ⋃ n ∈ Finset.range (N+1), K n
    let B : ℕ → Set ℝ := fun N => L \ U N

    -- B ist antiton
    have hB_antitone : Antitone B := by
      intro m n hmn x hx
      rcases hx with ⟨hxL, hxUm⟩
      refine ⟨hxL, ?_⟩
      intro hxUn
      have hUmono : U m ⊆ U n := by
        intro y hy
        rcases mem_iUnion.mp hy with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨him, hyKi⟩
        have : i < n + 1 := by
          have : i < m + 1 := by simpa [Finset.mem_range] using him
          exact lt_of_lt_of_le this (Nat.succ_le_succ hmn)
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨by
          simpa [Finset.mem_range] using this, hyKi⟩⟩
      exact hxUm (hUmono hxUn)

    -- ⋃ n, K n = ⋃ N, U N
    have hUnion_eq : (⋃ n, K n) = ⋃ N, U N := by
      ext x; constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨n, hxn⟩
        refine mem_iUnion.mpr ⟨n, ?_⟩
        exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨by
          simp [Finset.mem_range], hxn⟩⟩
      · intro hx
        rcases mem_iUnion.mp hx with ⟨N, hxUN⟩
        rcases mem_iUnion.mp hxUN with ⟨n, hxUN'⟩
        rcases mem_iUnion.mp hxUN' with ⟨hn, hxKn⟩
        exact mem_iUnion.mpr ⟨n, hxKn⟩

    -- ⋂N B N = L \ ⋃ n, K n
    have hInter_eq :
        (⋂ N, B N) = L \ ⋃ n, K n := by
      ext x; constructor
      · intro hx
        have hxL : x ∈ L := (mem_iInter.mp hx 0).1
        have hxNot : x ∉ ⋃ n, K n := by
          intro hxU
          have hxU' : x ∈ ⋃ N, U N := by simpa [hUnion_eq] using hxU
          rcases mem_iUnion.mp hxU' with ⟨N, hxUN⟩
          exact (mem_iInter.mp hx N).2 hxUN
        exact ⟨hxL, hxNot⟩
      · intro hx
        rcases hx with ⟨hxL, hxNotU⟩
        refine mem_iInter.mpr ?_
        intro N
        have hxNotUN : x ∉ U N := by
          intro hxUN
          exact hxNotU (by
            have : U N ⊆ ⋃ n, K n := by
              intro y hy
              rcases mem_iUnion.mp hy with ⟨i, hi⟩
              rcases mem_iUnion.mp hi with ⟨_, hyKi⟩
              exact mem_iUnion.mpr ⟨i, hyKi⟩
            exact this hxUN)
        exact ⟨hxL, hxNotUN⟩

    -- L \ ⋃ K  =  L ∩ R  (weil L ⊆ M)
    have Ldiff_eq : L \ (⋃ n, K n) = L ∩ R := by
      ext x; constructor
      · intro hx
        have hxM : x ∈ M := hLsub hx.1
        exact ⟨hx.1, ⟨hxM, hx.2⟩⟩
      · intro hx
        exact ⟨hx.1, hx.2.2⟩

    -- κ(L ∩ R) = 0 via "kompakter Nullrest" auf R
    have hLcapR_zero : kappa (L ∩ R) = 0 := by
      have hnoPos :
          ∀ C : Set ℝ, IsCompact C → C ⊆ L ∩ R → kappa C = 0 := by
        intro C hCc hCsub
        exact hRest0 C hCc (by intro x hxC; exact (hCsub hxC).2)
      simpa using NK.zero_of_noPosCompact (L ∩ R) hnoPos

    -- ⇒ κ(⋂N B N) = 0, also ⨅N κ(B N) = 0
    have hInter_zero : kappa (⋂ N, B N) = 0 := by
      simpa [R, hInter_eq, Ldiff_eq] using hLcapR_zero
    have hInf_zero : (iInf (fun N => kappa (B N))) = 0 := by
      have := NK.cont_from_above B hB_antitone
      simpa [this] using hInter_zero

    -- Überdeckung von L durch (⋃_{n≤N} L∩K n) ∪ B N
    have h_cover (N : ℕ) :
        L ⊆ (⋃ n ∈ Finset.range (N+1), L ∩ K n) ∪ B N := by
      intro x hxL
      by_cases hxU : x ∈ U N
      · rcases mem_iUnion.mp hxU with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨hir, hxKi⟩
        exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hir, ⟨hxL, hxKi⟩⟩⟩)
      · exact Or.inr ⟨hxL, hxU⟩

    -- κ(L) ≤ κ(⋃_{n≤N} L∩K n) + κ(B N)
    have h_upper (N : ℕ) :
        kappa L ≤ kappa (⋃ n ∈ Finset.range (N+1), L ∩ K n) + kappa (B N) := by
      have := NK.mono (A := L) (B := (⋃ n ∈ Finset.range (N+1), L ∩ K n) ∪ B N) (h_cover N)
      exact this.trans (NK.subadd_union _ _)

    -- Additivität auf disjunkten Schnitten → Summenformel
    have hU_eq_sum (N : ℕ) :
        kappa (⋃ n ∈ Finset.range (N+1), L ∩ K n)
          = Finset.sum (Finset.range (N+1)) (fun n => kappa (L ∩ K n)) := by
      have hKc' : ∀ n, IsCompact (L ∩ K n) := fun n => hLc.inter (hKc n)
      have hdisj' :
          Pairwise (fun i j => Disjoint (L ∩ K i) (L ∩ K j)) := by
        intro i j hij
        have : Disjoint (K i) (K j) := hdisj hij
        exact this.mono (by intro x hx; exact hx.2) (by intro x hx; exact hx.2)
      simpa using
        (kappa_union_finset_eq_sum
          (NK := NK)
          (K := fun n => L ∩ K n)
          hKc' hdisj' (Finset.range (N+1)))

    -- κ(⋃_{n≤N} L∩K n) ≤ ∑_{n≤N} κ(K n)
    have h_part_le (N : ℕ) :
        kappa (⋃ n ∈ Finset.range (N+1), L ∩ K n)
          ≤ Finset.sum (Finset.range (N+1)) (fun n => kappa (K n)) := by
      -- punktweise Monotonie → Summen-Ungleichung
      have hterm :
          ∀ n ∈ Finset.range (N+1),
            kappa (L ∩ K n) ≤ kappa (K n) := by
        intro n hn; exact NK.mono (by intro x hx; exact hx.2)
      have hsum :
          (Finset.sum (Finset.range (N+1)) (fun n => kappa (L ∩ K n)))
            ≤ (Finset.sum (Finset.range (N+1)) (fun n => kappa (K n))) :=
        Finset.sum_le_sum hterm
      -- Brücke zwischen zwei Schreibweisen der beschränkten Vereinigung
      have hRewr :
          (⋃ n, ⋃ (_ : n < N+1), L ∩ K n)
            = (⋃ n ∈ Finset.range (N+1), L ∩ K n) := by
        ext x; constructor
        · intro hx
          rcases mem_iUnion.mp hx with ⟨n, hx1⟩
          rcases mem_iUnion.mp hx1 with ⟨hn, hx2⟩
          have hn' : n ∈ Finset.range (N+1) := by simpa [Finset.mem_range] using hn
          exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn', hx2⟩⟩
        · intro hx
          rcases mem_iUnion.mp hx with ⟨n, hx1⟩
          rcases mem_iUnion.mp hx1 with ⟨hn', hx2⟩
          have hn : n < N+1 := by simpa [Finset.mem_range] using hn'
          exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hx2⟩⟩
      -- umschreiben und hsum anwenden
      have hEq := hU_eq_sum N
      calc
        kappa (⋃ n ∈ Finset.range (N+1), L ∩ K n)
            = kappa (⋃ n, ⋃ (_ : n < N+1), L ∩ K n) := by
                simp [hRewr]
        _ = Finset.sum (Finset.range (N+1)) (fun n => kappa (L ∩ K n)) := by
                simpa [hRewr] using hEq
        _ ≤ Finset.sum (Finset.range (N+1)) (fun n => kappa (K n)) := hsum

    -- ∀N, κ(L) ≤ (∑_{n≤N} κ(K n)) + κ(B N)
    have h_allN : ∀ N, kappa L ≤
        (Finset.sum (Finset.range (N+1)) (fun n => kappa (K n))) + kappa (B N) := by
      intro N
      exact (h_upper N).trans (add_le_add_right (h_part_le N) _)

    -- Aus ⨅N κ(BN)=0 folgt: ∀ε>0 ∃N, κ(BN) ≤ ε
    -- aus ⨅N κ(B N) = 0 folgt: ∀ ε>0 ∃N, κ(B N) ≤ ε
    have hB_to_zero :
        ∀ ε : ENNReal, 0 < ε → ∃ N, kappa (B N) ≤ ε := by
      intro ε hε
      classical
      -- Beweis durch Widerspruch
      by_contra h
      -- h : ¬ ∃ N, kappa (B N) ≤ ε  ⇒  ∀ N, ε < kappa (B N)
      have hforall_lt : ∀ N, ε < kappa (B N) := by
        intro N
        have hnotle : ¬ kappa (B N) ≤ ε := (not_exists.mp h) N
        exact lt_of_not_ge hnotle
      -- ⇒ ∀ N, ε ≤ kappa (B N)  ⇒  ε ≤ ⨅N κ(B N)
      have hge : ε ≤ ⨅ N, kappa (B N) :=
        (le_iInf_iff).2 (fun N => (le_of_lt (hforall_lt N)))
      -- aber ⨅N κ(B N) = 0
      have : ε ≤ 0 := by simpa [hInf_zero] using hge
      exact (not_lt_of_ge this) hε
    -- ε-Argument ⇒ κ(L) ≤ sumBlocks
    have hL_le_sumBlocks : kappa L ≤ sumBlocks (kappa := kappa) K := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      rcases hB_to_zero ε hε with ⟨N, hBN⟩
      have : kappa L ≤
          (Finset.sum (Finset.range (N+1)) (fun n => kappa (K n))) + kappa (B N) :=
        h_allN N
      have : kappa L ≤
          (Finset.sum (Finset.range (N+1)) (fun n => kappa (K n))) + ε :=
        this.trans (add_le_add_left hBN _)
      -- endliche Summe ≤ sumBlocks
      have hfin_le :
        (Finset.sum (Finset.range (N+1)) (fun n => kappa (K n)))
          ≤ sumBlocks (kappa := kappa) K :=
        le_iSup_of_le (Finset.range (N+1)) (le_of_eq rfl)
      exact this.trans (add_le_add_right hfin_le _)

    exact hL_le_sumBlocks

  -- Gleichheit
  exact le_antisymm h_le h_ge

end NaiveKappa
end PerfectSubset
