/-
  NaiveLength.lean — Dualität κ(U)+ν(K)=1 und äußere-Längen-Charakterisierung
  (stabile Version, ohne `introN`, robuste `simp`-Verwendung)
-/

import Mathlib
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- Grundintervall [0,1] als Menge auf ℝ. -/
def I01 : Set ℝ := Icc (0 : ℝ) 1

/-! ## Basishilfen -/

@[simp] lemma inter_I01_of_subset {K : Set ℝ} (h : K ⊆ I01) : K ∩ I01 = K := by
  ext x; constructor
  · intro hx; exact hx.1
  · intro hx; exact ⟨hx, h hx⟩

@[simp] lemma diff_diff_I01_of_subset {U : Set ℝ} (hU : U ⊆ I01) :
  I01 \ (I01 \ U) = U := by
  ext x; constructor
  · intro hx
    have : ¬ (x ∈ I01 ∧ x ∈ Uᶜ) := by
      have : x ∉ (I01 \ U) := hx.2
      simpa [mem_diff, mem_compl] using this
    by_cases hxI : x ∈ I01
    · have : ¬ x ∈ Uᶜ := by intro hxU; exact this ⟨hxI, hxU⟩
      simpa [mem_compl] using this
    · exact (hxI hx.1).elim
  · intro hxU
    exact ⟨hU hxU, by intro hxK; exact hxK.2 hxU⟩

lemma isCompact_compl_of_open_sub_I01
  {U : Set ℝ} (hUo : IsOpen U) (_hUsub : U ⊆ I01) :
  IsClosed (I01 \ U) ∧ IsCompact (I01 \ U) := by
  have hClosed : IsClosed (I01 ∩ Uᶜ) := isClosed_Icc.inter (hUo.isClosed_compl)
  have hComp   : IsCompact (I01 ∩ Uᶜ) := (isCompact_Icc).inter_right (hUo.isClosed_compl)
  simpa [Set.diff_eq] using And.intro hClosed hComp

lemma compact_of_closed_subset_I01 {K : Set ℝ}
  (hKclosed : IsClosed K) (hKsub : K ⊆ I01) : IsCompact K := by
  have : IsCompact (I01 ∩ K) := (isCompact_Icc).inter_right hKclosed
  simpa [inter_comm, inter_left_comm, inter_I01_of_subset hKsub] using this

/-! ## System κ mit benötigten Eigenschaften -/

structure KappaSystem where
  kappa : Set ℝ → ℝ
  mono_kappa : ∀ {A B : Set ℝ}, A ⊆ B → kappa A ≤ kappa B
  kappa_empty : kappa ∅ = 0
  kappa_I01  : kappa I01 = 1
  subadd : ∀ (A B : Set ℝ), kappa (A ∪ B) ≤ kappa A + kappa B
  inner_regular_on_compact :
    ∀ {K : Set ℝ}, IsCompact K → K ⊆ I01 →
      (sSup {κ : ℝ | ∃ (T : Set ℝ), IsCompact T ∧ T ⊆ K ∧ kappa T = κ}) = kappa K
  compl_compact :
    ∀ {K : Set ℝ}, IsCompact K → K ⊆ I01 → kappa (I01 \ K) = 1 - kappa K
  outer_open_sup :
    ∀ (S : Set ℝ), kappa S = sInf (kappa '' { U : Set ℝ | IsOpen U ∧ S ⊆ U })

namespace KappaSystem

variable (S : KappaSystem)
include S

/-- ν(A) := Sup über κ(T) für kompakte T ⊆ A ∩ [0,1]. -/
def nu (A : Set ℝ) : ℝ :=
  sSup {κ : ℝ | ∃ (T : Set ℝ), IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}

/-! ### Monotonie / Schranken -/

lemma mono_nu : ∀ {A B}, A ⊆ B → S.nu A ≤ S.nu B := by
  intro A B hAB
  classical
  have bddB :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ B ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _hTc, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
  have hneA :
    ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, ?_⟩
    · intro x hx; cases hx
    · simp [S.kappa_empty]

  apply csSup_le hneA
  intro x hx
  rcases hx with ⟨T, hTc, hTsub, rfl⟩
  have hTsub' : T ⊆ B ∩ I01 := by
    intro t ht; rcases hTsub ht with ⟨htA, htI⟩; exact ⟨hAB htA, htI⟩
  have hxB : S.kappa T ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ B ∩ I01 ∧ S.kappa T = κ} :=
    ⟨T, hTc, hTsub', rfl⟩
  exact le_csSup bddB hxB

lemma nu_eq_kappa_on_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.nu K = S.kappa K := by
  classical
  have hcap : K ∩ I01 = K := inter_I01_of_subset hKsub
  simpa [nu, hcap] using S.inner_regular_on_compact (K := K) hKc hKsub

lemma kappa_compl_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.kappa (I01 \ K) = 1 - S.kappa K := S.compl_compact hKc hKsub

lemma kappa_add_nu_of_closed_subset {K : Set ℝ}
  (hKclosed : IsClosed K) (hKsub : K ⊆ I01) :
  S.kappa (I01 \ K) + S.nu K = 1 := by
  classical
  have hKc : IsCompact K := compact_of_closed_subset_I01 hKclosed hKsub
  have hνκ : S.nu K = S.kappa K := S.nu_eq_kappa_on_compact hKc hKsub
  have hκ : S.kappa (I01 \ K) = 1 - S.kappa K := S.kappa_compl_compact hKc hKsub
  simp [hνκ, hκ, sub_eq_add_neg]

lemma kappa_add_nu_of_open_compl {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  let K := (I01 \ U)
  S.kappa U + S.nu K = 1 := by
  intro K
  classical
  obtain ⟨_, hKc⟩ := isCompact_compl_of_open_sub_I01 (U := U) hUo hUsub
  have hKsub : K ⊆ I01 := by intro x hx; exact hx.1
  have hνκ : S.nu K = S.kappa K := S.nu_eq_kappa_on_compact (K := K) hKc hKsub
  have hSet : I01 \ K = U := diff_diff_I01_of_subset hUsub
  have hκU : S.kappa U = 1 - S.kappa K := by
    have hcomp : S.kappa (I01 \ K) = 1 - S.kappa K :=
      S.kappa_compl_compact (K := K) hKc hKsub
    simpa [hSet] using hcomp
  have hsum : S.kappa U + S.nu K = (1 - S.kappa K) + S.kappa K := by
    simp [hνκ, hκU]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum

lemma kappa_add_nu_of_open_subset_I01 {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  S.kappa U + S.nu (I01 \ U) = 1 := by
  simp [kappa_add_nu_of_open_compl, hUo, hUsub]

/-! ### Schranken 0 ≤ κ,ν ≤ 1 (auf [0,1]) -/

lemma kappa_bounds_of_subset_I01 {A : Set ℝ} (hA : A ⊆ I01) :
  0 ≤ S.kappa A ∧ S.kappa A ≤ 1 := by
  have h1 : S.kappa A ≤ S.kappa I01 := S.mono_kappa hA
  have : S.kappa ∅ ≤ S.kappa A := S.mono_kappa (by intro x hx; cases hx)
  have hnonneg : 0 ≤ S.kappa A := by simp [S.kappa_empty] at this; exact this
  exact ⟨hnonneg, by simpa [S.kappa_I01] using h1⟩

lemma zero_le_nu (A : Set ℝ) : 0 ≤ S.nu A := by
  classical
  have idx0 :
    0 ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨∅, isCompact_empty, ?_, ?_⟩
    · intro x hx; cases hx
    · simp [S.kappa_empty]
  have bdd :
    BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _hTc, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
  have h0 : 0 ≤ sSup {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} :=
    le_csSup bdd idx0
  simpa [nu] using h0

lemma nu_le_one (A : Set ℝ) : S.nu A ≤ 1 := by
  classical
  have bdd :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
  have hne:
    ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, ?_⟩
    · intro x hx; cases hx
    · simp [S.kappa_empty]
  have h := csSup_le hne (by
    intro z hz; rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this)
  simpa [nu] using h

/-! ### Bequeme Korollare -/

lemma nu_eq_nu_inter_I01 (A : Set ℝ) : S.nu A = S.nu (A ∩ I01) := by
  have hsub : (A ∩ I01) ⊆ I01 := by intro x hx; exact hx.2
  have hcap : (A ∩ I01) ∩ I01 = (A ∩ I01) := by
    simp [inter_I01_of_subset, hsub]
  simp [nu, hcap]

@[simp] lemma kappa_empty' : S.kappa ∅ = 0 := S.kappa_empty

@[simp] lemma nu_empty : S.nu (∅ : Set ℝ) = 0 := by
  classical
  have hset : {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ (∅ : Set ℝ) ∩ I01 ∧ S.kappa T = κ}
        = {0} := by
    ext r; constructor
    · intro hr
      rcases hr with ⟨T, hTc, hTsub, rfl⟩
      have hTsubsetEmpty : T ⊆ (∅ : Set ℝ) := by
        intro x hx; exact (hTsub hx).1
      have hTempty : T = (∅ : Set ℝ) := by
        ext x; constructor
        · intro hx; exact hTsubsetEmpty hx
        · intro hx; cases hx
      subst hTempty
      simp [S.kappa_empty]
    · intro hr; rcases hr with rfl
      refine ⟨∅, isCompact_empty, ?_, ?_⟩
      · intro x hx; cases hx
      · simp [S.kappa_empty]
  simp [nu]

@[simp] lemma nu_I01 : S.nu I01 = 1 := by
  have h := S.nu_eq_kappa_on_compact (K := I01)
    (hKc := isCompact_Icc) (hKsub := by intro x hx; exact hx)
  simpa [S.kappa_I01] using h

/-! ### Familien: KFamily, κ(𝓤), ν(𝓚) -/

def KFamily (𝓤 : Set (Set ℝ)) : Set (Set ℝ) := {K | ∃ U ∈ 𝓤, K = I01 \ U}

def kappaInf (𝓤 : Set (Set ℝ)) : ℝ := sInf (S.kappa '' 𝓤)

def nuSup (𝓚 : Set (Set ℝ)) : ℝ := sSup (S.nu '' 𝓚)

def kappaSup (𝓚 : Set (Set ℝ)) : ℝ := sSup (S.kappa '' 𝓚)

lemma kappa_image_bdd
  (𝓤 : Set (Set ℝ))
  (hUsubI : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  BddBelow (S.kappa '' 𝓤) ∧ BddAbove (S.kappa '' 𝓤) := by
  refine ⟨?lb, ?ub⟩
  · refine ⟨0, ?_⟩
    intro y hy; rcases hy with ⟨U, _, rfl⟩
    have : S.kappa ∅ ≤ S.kappa U := S.mono_kappa (by intro x hx; cases hx)
    simpa [S.kappa_empty] using this
  · refine ⟨1, ?_⟩
    intro y hy; rcases hy with ⟨U, hU, rfl⟩
    have : S.kappa U ≤ S.kappa I01 := S.mono_kappa (hUsubI hU)
    simp [S.kappa_I01] at this; exact this

lemma nu_image_bdd
  {𝓚 : Set (Set ℝ)}
  (_hneK : 𝓚.Nonempty)
  (_hKsubI : ∀ {K}, K ∈ 𝓚 → K ⊆ I01) :
  BddBelow (S.nu '' 𝓚) ∧ BddAbove (S.nu '' 𝓚) := by
  refine ⟨⟨0, by intro y hy; rcases hy with ⟨K, _, rfl⟩; exact S.zero_le_nu K⟩,
          ⟨1, by intro y hy; rcases hy with ⟨K, _, rfl⟩; exact S.nu_le_one K⟩⟩

lemma kappaInf_le_of_mem {𝓤 : Set (Set ℝ)} {U : Set ℝ} (hU : U ∈ 𝓤) :
  S.kappaInf 𝓤 ≤ S.kappa U := by
  have hbb : BddBelow (S.kappa '' 𝓤) := ⟨0, by
    intro y hy; rcases hy with ⟨V, _, rfl⟩
    have : S.kappa ∅ ≤ S.kappa V := S.mono_kappa (by intro x hx; cases hx)
    simpa [S.kappa_empty] using this⟩
  have : S.kappa U ∈ (S.kappa '' 𝓤) := ⟨U, hU, rfl⟩
  simpa [kappaInf] using (csInf_le hbb this)

lemma le_nuSup_of_mem
  {𝓚 : Set (Set ℝ)} {K : Set ℝ}
  (hK : K ∈ 𝓚)
  (hb : BddAbove (S.nu '' 𝓚)) :
  S.nu K ≤ S.nuSup 𝓚 := by
  have : S.nu K ∈ (S.nu '' 𝓚) := ⟨K, hK, rfl⟩
  simpa [nuSup] using (le_csSup hb this)

/-! ### ν = κ auf der Komplementfamilie -/

lemma nu_eq_kappa_on_KFamily
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (_ : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  ∀ {K}, K ∈ KFamily 𝓤 → S.nu K = S.kappa K := by
  intro K hK
  rcases hK with ⟨U, hU, rfl⟩
  have hclosed : IsClosed (I01 \ U) := by
    have : IsClosed (I01 ∩ Uᶜ) := isClosed_Icc.inter (hUopen hU).isClosed_compl
    simpa [Set.diff_eq] using this
  have hsub : (I01 \ U) ⊆ I01 := by intro x hx; exact hx.1
  have hKc : IsCompact (I01 \ U) := compact_of_closed_subset_I01 hclosed hsub
  simpa using S.nu_eq_kappa_on_compact (K := I01 \ U) hKc hsub

lemma image_nu_eq_image_kappa_on_KFamily
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  (S.nu '' KFamily 𝓤) = (S.kappa '' KFamily 𝓤) := by
  ext r; constructor
  · intro hr; rcases hr with ⟨K, hK, rfl⟩
    have h := S.nu_eq_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub hK
    exact ⟨K, hK, h.symm⟩
  · intro hr; rcases hr with ⟨K, hK, rfl⟩
    have h := S.nu_eq_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub hK
    exact ⟨K, hK, h⟩

lemma nuSup_eq_kappaSup_on_KFamily
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  S.nuSup (KFamily 𝓤) = S.kappaSup (KFamily 𝓤) := by
  simpa [nuSup, kappaSup]
    using congrArg sSup (S.image_nu_eq_image_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub)

/-! ### Hauptsatz: κ(𝓤) + ν(𝓚) = 1 -/

theorem kappaInf_add_nuSup_eq_one
  (𝓤 : Set (Set ℝ))
  (hUopens : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsubI : ∀ {U}, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  let 𝓚 := KFamily 𝓤
  S.kappaInf 𝓤 + S.nuSup 𝓚 = 1 := by
  intro 𝓚
  classical
  -- Beschränktheiten
  have hBddκ := S.kappa_image_bdd 𝓤 hUsubI
  have hneK : 𝓚.Nonempty := by
    rcases hUnonempty with ⟨U0, hU0⟩
    exact ⟨I01 \ U0, ⟨U0, hU0, rfl⟩⟩
  have hKsubI : ∀ {K}, K ∈ 𝓚 → K ⊆ I01 := by
    intro K hK
    rcases hK with ⟨U, _, rfl⟩
    intro x hx; exact hx.1
  have hBddν := S.nu_image_bdd (𝓚 := 𝓚) hneK hKsubI
  rcases hBddκ with ⟨hκlb, hκub⟩
  rcases hBddν with ⟨_, hνub⟩

  -- Abkürzungen
  set α := S.kappaInf 𝓤
  set β := S.nuSup 𝓚
  have hαdef : α = sInf (S.kappa '' 𝓤) := rfl
  have hβdef : β = sSup (S.nu '' 𝓚)     := rfl

  -- (i) 1 - β ≤ α
  have h1 : 1 - β ≤ α := by
    have hUbound : ∀ {U}, U ∈ 𝓤 → 1 - β ≤ S.kappa U := by
      intro U hU
      have hKU : (I01 \ U) ∈ 𝓚 := ⟨U, hU, rfl⟩
      have hMem : S.nu (I01 \ U) ∈ (S.nu '' 𝓚) := ⟨I01 \ U, hKU, rfl⟩
      have hνleβ : S.nu (I01 \ U) ≤ β := by
        simpa [hβdef] using le_csSup hνub hMem
      have hsum : S.kappa U + S.nu (I01 \ U) = 1 :=
        S.kappa_add_nu_of_open_subset_I01 (U := U)
          (hUo := hUopens hU) (hUsub := hUsubI hU)
      have hκU : S.kappa U = 1 - S.nu (I01 \ U) := by
        have := congrArg (fun t => t - S.nu (I01 \ U)) hsum
        simpa [sub_eq_add_neg] using this
      have : 1 - β ≤ 1 - S.nu (I01 \ U) :=
        sub_le_sub_left hνleβ 1
      exact hκU ▸ this
    have hne : (S.kappa '' 𝓤).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.kappa U0, ⟨U0, hU0, rfl⟩⟩
    have hαraw : 1 - β ≤ sInf (S.kappa '' 𝓤) :=
      le_csInf hne (by
        intro y hy; rcases hy with ⟨U, hU, rfl⟩
        exact hUbound hU)
    simpa [hαdef] using hαraw

  -- (ii) β ≤ 1 - α
  have h2 : β ≤ 1 - α := by
    have hKbound : ∀ {K}, K ∈ 𝓚 → S.nu K ≤ 1 - α := by
      intro K hK
      rcases hK with ⟨U, hU, rfl⟩
      -- α ≤ κ(U)
      have hαleκU : α ≤ S.kappa U := by
        have hMem : S.kappa U ∈ (S.kappa '' 𝓤) := ⟨U, hU, rfl⟩
        simpa [hαdef] using (csInf_le hκlb hMem)
      -- ν(I01\U) = 1 - κ(U) ≤ 1 - α
      have hsum : S.kappa U + S.nu (I01 \ U) = 1 :=
        S.kappa_add_nu_of_open_subset_I01 (U := U)
          (hUo := hUopens hU) (hUsub := hUsubI hU)
      have hν : S.nu (I01 \ U) = 1 - S.kappa U :=
        eq_sub_of_add_eq (by simpa [add_comm] using hsum)
      have : 1 - S.kappa U ≤ 1 - α := sub_le_sub_left hαleκU (1 : ℝ)
      simpa [hν] using this
    have hne' : (S.nu '' 𝓚).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.nu (I01 \ U0), ⟨I01 \ U0, ⟨U0, hU0, rfl⟩, rfl⟩⟩
    have hβraw : sSup (S.nu '' 𝓚) ≤ 1 - α :=
      csSup_le hne' (by intro y hy; rcases hy with ⟨K, hK, rfl⟩; exact hKbound hK)
    simpa [hβdef] using hβraw

  -- aus (i) und (ii) folgt α + β = 1
  have hle : α + β ≤ 1 := by
    have := add_le_add_left h2 α
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hge : 1 ≤ α + β := by
    have := add_le_add_right h1 β
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact le_antisymm hle hge


/-! ## Familien auf [0,1]: strukturelle Gleichheiten -/
open Set

omit S

lemma interU_union_KFamily_eq_I01
  (𝓤 : Set (Set ℝ))
  (hUsub : ∀ ⦃U⦄, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  (sInter 𝓤) ∪ sUnion (KappaSystem.KFamily 𝓤) = I01 := by
  classical
  -- Richtung ⊆
  have hsubset :
      (sInter 𝓤) ∪ sUnion (KappaSystem.KFamily 𝓤) ⊆ I01 := by
    intro x hx
    rcases hx with hx | hx
    · rcases hUnonempty with ⟨U0, hU0⟩
      have hxU0 : x ∈ U0 := (mem_sInter.mp hx) U0 hU0
      exact hUsub hU0 hxU0
    · rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
      rcases hK with ⟨U, hU, rfl⟩
      exact hxK.1

  -- Richtung ⊇
  have hsupset :
      I01 ⊆ (sInter 𝓤) ∪ sUnion (KappaSystem.KFamily 𝓤) := by
    intro x hxI
    by_cases hAll : ∀ U ∈ 𝓤, x ∈ U
    · left; exact mem_sInter.mpr hAll
    · right
      have ⟨U, h⟩ := not_forall.mp hAll
      have ⟨hU, hxNot⟩ : U ∈ 𝓤 ∧ x ∉ U := Classical.not_imp.mp h
      refine mem_sUnion.mpr ?_
      refine ⟨I01 \ U, ⟨U, hU, rfl⟩, ?_⟩
      exact ⟨hxI, hxNot⟩

  exact le_antisymm hsubset hsupset


/-! ## Relativ offene Supersets in I01 -/

def VFamily (M : Set ℝ) : Set (Set ℝ) :=
  {U | ∃ V : Set ℝ, IsOpen V ∧ U = I01 ∩ V ∧ M ⊆ U}

lemma VFamily_inter_mem {M U₁ U₂ : Set ℝ}
  (h₁ : U₁ ∈ VFamily M) (h₂ : U₂ ∈ VFamily M) :
  (U₁ ∩ U₂) ∈ VFamily M := by
  rcases h₁ with ⟨V₁, hV₁open, rfl, hMsub₁⟩
  rcases h₂ with ⟨V₂, hV₂open, rfl, hMsub₂⟩
  refine ⟨V₁ ∩ V₂, hV₁open.inter hV₂open, ?_, ?_⟩
  · ext x; constructor
    · intro hx; rcases hx with ⟨⟨hxI, hxV₁⟩, ⟨_, hxV₂⟩⟩; exact ⟨hxI, ⟨hxV₁, hxV₂⟩⟩
    · intro hx; rcases hx with ⟨hxI, hxV⟩; exact ⟨⟨hxI, hxV.1⟩, ⟨hxI, hxV.2⟩⟩
  · intro x hxM; exact ⟨hMsub₁ hxM, hMsub₂ hxM⟩

omit S
/-- Kernlemma: `M` ist der Schnitt aller relativ offenen Supersets von `M` in `I01`. -/
lemma inter_VFamily_eq (M : Set ℝ) (hM : M ⊆ I01) :
  (⋂₀ VFamily M) = M := by
  classical
  -- Richtung ⊆
  have hsubset : (⋂₀ VFamily M) ⊆ M := by
    intro x hx
    by_contra hxM
    -- Wähle U := I01 ∩ {x}ᶜ ∈ VFamily M
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      intro y hyM
      have hyI : y ∈ I01 := hM hyM
      have hy_ne : y ≠ x := by
        intro hxy
        have hxM' : x ∈ M := by simpa [hxy] using hyM
        exact hxM hxM'
      exact ⟨hyI, by simpa [mem_compl] using hy_ne⟩
    -- x ∈ ⋂ VFamily M ⇒ x ∈ U, Widerspruch
    have hxU : x ∈ U := (mem_sInter.mp hx) U hUmem
    exact hxU.2 rfl

  -- Richtung ⊇
  have hsupset : M ⊆ (⋂₀ VFamily M) := by
    intro x hxM
    apply mem_sInter.mpr
    intro U hU
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    have : x ∈ U := hMsub hxM
    simpa [hUdef] using this

  exact le_antisymm hsubset hsupset

include S
namespace NaiveLength

/-- Zugehörige `K`-Familie: Komplemente der `V`-Mengen **innerhalb** von `I01`. -/
def KFamilyOf (M : Set ℝ) : Set (Set ℝ) :=
  {K | ∃ U ∈ VFamily M, K = I01 \ U}

omit S
/-- Komplementformel: `[0,1] \ M = ⋃₀ (KFamilyOf M)`. -/
lemma compl_eq_union_KFamilyOf (M : Set ℝ) (hM : M ⊆ I01) :
  I01 \ M = ⋃₀ (KFamilyOf M) := by
  classical
  -- Kernlemma: ⋂ VFamily M = M
  have hInt : (⋂₀ VFamily M) = M :=
    inter_VFamily_eq (M := M) hM
  ext x; constructor
  · -- → Richtung
    intro hx
    rcases hx with ⟨hxI, hxNotM⟩
    -- Wähle U := I01 ∩ {x}ᶜ ∈ VFamily M
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      intro y hyM
      have hyI : y ∈ I01 := hM hyM
      have hy_ne : y ≠ x := by
        intro h; have hxM' : x ∈ M := by simpa [h] using hyM
        exact hxNotM hxM'
      exact ⟨hyI, by simpa [mem_compl] using hy_ne⟩
    -- Zeige x ∈ ⋃ KFamilyOf M durch das konkrete K := I01 \ U
    refine mem_sUnion.mpr ?_
    refine ⟨I01 \ U, ?_, ?_⟩
    · exact ⟨U, hUmem, rfl⟩
    · exact ⟨hxI, by intro hxU; exact hxU.2 rfl⟩

  · -- ← Richtung
    intro hx
    rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
    rcases hK with ⟨U, hU, rfl⟩
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    rcases hxK with ⟨hxI, hxNotU⟩
    -- Aus x ∉ U folgt x ∉ ⋂ VFamily M ⇒ x ∉ M (per hInt)
    have hxNotInter : x ∉ ⋂₀ VFamily M := by
      intro hxInter
      have hxU : x ∈ U := (mem_sInter.mp hxInter) U ⟨V, _hVopen, hUdef, hMsub⟩
      exact hxNotU hxU
    have hxNotM : x ∉ M := by
      simpa [hInt] using hxNotInter
    exact ⟨hxI, hxNotM⟩

end NaiveLength

include S

/-!
###############################################################################
# Tail: Gleichungen/Abschätzungen für ν(A) und offene Supersets
###############################################################################
-/

omit S

lemma sUnion_KFamily_eq_compl_sInter (𝓤 : Set (Set ℝ)) :
  sUnion (KappaSystem.KFamily 𝓤) = I01 \ sInter 𝓤 := by
  classical
  ext x; constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
    rcases hK with ⟨U, hU, rfl⟩
    rcases hxK with ⟨hxI, hxNotU⟩
    exact ⟨hxI, by intro hxAll; exact hxNotU ((mem_sInter.mp hxAll) U hU)⟩
  · intro hx
    rcases hx with ⟨hxI, hxNotAll⟩
    have : ∃ U ∈ 𝓤, x ∉ U := by
      by_contra h; push_neg at h; exact hxNotAll (by intro U hU; exact h U hU)
    rcases this with ⟨U, hU, hxNotU⟩
    exact mem_sUnion.mpr ⟨I01 \ U, ⟨U, hU, rfl⟩, ⟨hxI, hxNotU⟩⟩

include S

/-- Grund-Ungleichung: Für `A ⊆ I01` gilt `ν(A) ≤ 1 - κ(I01 \ A)`. -/
lemma nu_le_one_sub_kappa_compl_of_subset_I01
  {A : Set ℝ} (_ : A ⊆ I01) :
  S.nu A ≤ 1 - S.kappa (I01 \ A) := by
  classical
  let I := {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}

  -- Nonempty-Zeuge für I
  have hsubset_empty : (∅ : Set ℝ) ⊆ A ∩ I01 := by
    intro x hx; cases hx
  have hkappa_empty : S.kappa (∅ : Set ℝ) = 0 := by
    simp [S.kappa_empty]
  have hne : I.Nonempty :=
    ⟨0, ⟨∅, isCompact_empty, ⟨hsubset_empty, hkappa_empty⟩⟩⟩
  have hbound : ∀ z ∈ I, z ≤ 1 - S.kappa (I01 \ A) := by
    intro z hz; rcases hz with ⟨T, hTc, hTsub, rfl⟩
    have hTsubA : T ⊆ A   := by intro t ht; exact (hTsub ht).1
    have hTsubI : T ⊆ I01 := by intro t ht; exact (hTsub ht).2
    have hcomp : I01 \ A ⊆ I01 \ T := by
      intro x hx; exact ⟨hx.1, by intro hxT; exact hx.2 (hTsubA hxT)⟩
    have hmono := S.mono_kappa hcomp
    have hcompl : S.kappa (I01 \ T) = 1 - S.kappa T :=
      S.compl_compact (K := T) hTc hTsubI
    have : S.kappa (I01 \ A) ≤ 1 - S.kappa T := by simpa [hcompl] using hmono
    linarith
  have bdd : BddAbove I := ⟨1, by
    intro z hz; rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this⟩
  have hfin : sSup I ≤ 1 - S.kappa (I01 \ A) := csSup_le hne (by intro z hz; exact hbound z hz)
  -- robust gegen Umschreibungen der Indexmenge
  simpa [KappaSystem.nu, I, subset_inter_iff] using hfin

/-- Aus der äußeren Offenheits-Charakterisierung:
Für `M ⊆ I01` und `ε>0` gibt es ein offenes `O ⊇ M` mit
`κ(O) ≤ κ(M) + ε`. -/
lemma exists_open_superset_kappa_within
  {M : Set ℝ} (_ : M ⊆ I01)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ O : Set ℝ, IsOpen O ∧ M ⊆ O ∧ S.kappa O ≤ S.kappa M + ε := by
  classical
  let A : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}
  have hEq : S.kappa M = sInf (S.kappa '' A) := by
    change S.kappa M = sInf (S.kappa '' {U | IsOpen U ∧ M ⊆ U})
    exact S.outer_open_sup (S := M)
  have hA_nonempty : (S.kappa '' A).Nonempty :=
    ⟨S.kappa (Set.univ), ⟨Set.univ, ⟨isOpen_univ, by intro _ _; trivial⟩, rfl⟩⟩
  have _hBBl : BddBelow (S.kappa '' A) := ⟨0, by
    intro y hy; rcases hy with ⟨U, _hU, rfl⟩
    have : S.kappa ∅ ≤ S.kappa U := S.mono_kappa (by intro x hx; cases hx)
    simpa [S.kappa_empty] using this⟩
  by_contra h
  have hforall : ∀ y ∈ (S.kappa '' A), S.kappa M + ε ≤ y := by
    intro y hy; rcases hy with ⟨U, hU, rfl⟩
    have hnot : ¬ S.kappa U ≤ S.kappa M + ε := by exact fun hle => h ⟨U, hU.1, hU.2, hle⟩
    exact le_of_lt (lt_of_not_ge hnot)
  have h_le_inf : S.kappa M + ε ≤ sInf (S.kappa '' A) := le_csInf hA_nonempty hforall
  have hcontra : S.kappa M + ε ≤ S.kappa M := by simpa [hEq] using h_le_inf
  exact ((not_lt_of_ge hcontra) (by linarith : S.kappa M < S.kappa M + ε)).elim

omit S
/-- **Hauptgleichung (Schnitt/Union):**
Für eine nichtleere Familie `𝓤` **offener** Mengen `U ⊆ I01` gilt
`κ(⋂₀ 𝓤) + ν(⋃₀ KFamily 𝓤) = 1`. -/
 theorem kappa_sInter_add_nu_sUnionK_eq_one
  (S : KappaSystem)
  (𝓤 : Set (Set ℝ))
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  S.kappa (sInter 𝓤) + S.nu (sUnion (KappaSystem.KFamily 𝓤)) = 1 := by
  classical
  set M : Set ℝ := sInter 𝓤
  have hMsub : M ⊆ I01 := by
    intro x hxM; rcases hUnonempty with ⟨U0, hU0⟩
    exact hUsub hU0 ((mem_sInter.mp hxM) U0 hU0)

  have hUnionEq : sUnion (KappaSystem.KFamily 𝓤) = I01 \ M :=
    (sUnion_KFamily_eq_compl_sInter (𝓤 := 𝓤))

  -- obere Schranke
  have hν_le : S.nu (sUnion (KappaSystem.KFamily 𝓤)) ≤ 1 - S.kappa M := by
    -- Grundlemma direkt anwenden (benannte Argumente, Subset-Beweis inline)
    have h0 :
        S.nu (I01 \ M) ≤ 1 - S.kappa (I01 \ (I01 \ M)) :=
      S.nu_le_one_sub_kappa_compl_of_subset_I01
        (A := I01 \ M)
        (by intro x hx; exact hx.1)
    -- Normalisierungen
    have hIcap : I01 ∩ M = M := by
      simpa [inter_comm] using inter_I01_of_subset (K := M) hMsub
    have hdd   : I01 \ (I01 \ M) = M :=
      diff_diff_I01_of_subset (U := M) hMsub
    have h1 : S.nu (I01 \ M) ≤ 1 - S.kappa M := by
      simpa [hIcap, hdd] using h0
    simpa [hUnionEq] using h1

  -- untere Schranke via ε > 0
  have hν_ge : 1 - S.kappa M ≤ S.nu (sUnion (KappaSystem.KFamily 𝓤)) := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- Open-Superset-Lemma sicher anwenden
    have hOpenSup :
      ∃ O : Set ℝ, IsOpen O ∧ M ⊆ O ∧ S.kappa O ≤ S.kappa M + ε := by
      exact S.exists_open_superset_kappa_within (M := M) hMsub ε hε
    rcases hOpenSup with ⟨O, hOopen, hMsubO, hκO⟩
    let U' : Set ℝ := I01 ∩ O
    let K' : Set ℝ := I01 \ U'
    have hK'closed : IsClosed K' := by
      have hc : IsClosed (I01 ∩ Oᶜ) := isClosed_Icc.inter (hOopen.isClosed_compl)
      simpa [K', U'] using hc
    have hK'sub   : K' ⊆ I01 := by intro x hx; exact hx.1
    have hK'comp  : IsCompact K' := compact_of_closed_subset_I01 hK'closed hK'sub
    have hU'subI  : U' ⊆ I01 := by intro x hx; exact hx.1
    have hMsubU'  : M ⊆ U' := by intro x hxM; exact ⟨hMsub hxM, hMsubO hxM⟩
    have hK'subCompl : K' ⊆ (I01 \ M) := by
      intro x hx; exact ⟨hx.1, by intro hxM; exact hx.2 (hMsubU' hxM)⟩
    have hK'subUnion : K' ⊆ sUnion (KappaSystem.KFamily 𝓤) := by
      intro x hx; simpa [hUnionEq] using hK'subCompl hx
    have hI01diffK' : I01 \ K' = U' := diff_diff_I01_of_subset (U := U') hU'subI
    have hκU' : S.kappa U' = 1 - S.kappa K' := by
      have hκ : S.kappa (I01 \ K') = 1 - S.kappa K' :=
        S.compl_compact (K := K') hK'comp hK'sub
      simpa [hI01diffK'] using hκ
    have hκU_leO : S.kappa U' ≤ S.kappa O :=
      S.mono_kappa (by intro x hx; exact hx.2)
    have hκK'_ge_one_sub_κO : S.kappa K' ≥ 1 - S.kappa O := by
      have : 1 - S.kappa K' ≤ S.kappa O := (hκU' ▸ hκU_leO)
      linarith
    have hκK'_ge : S.kappa K' ≥ 1 - S.kappa M - ε := by
      have : 1 - S.kappa M - ε ≤ 1 - S.kappa O := by linarith [hκO]
      exact le_trans this hκK'_ge_one_sub_κO
    have hν_ge' : S.kappa K' ≤ S.nu (sUnion (KappaSystem.KFamily 𝓤)) := by
      have hIn :
        S.kappa K' ∈ {κ : ℝ | ∃ T, IsCompact T ∧
                              T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ} := by
        refine ⟨K', hK'comp, ?_, rfl⟩
        intro x hx; exact ⟨hK'subUnion hx, hx.1⟩
      have bdd :
          BddAbove {κ : ℝ | ∃ T, IsCompact T ∧
                                T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ} :=
        ⟨1, by
          intro z hz; rcases hz with ⟨T, _hTc, hTsub, rfl⟩
          have : S.kappa T ≤ S.kappa I01 :=
            S.mono_kappa (by intro t ht; exact (hTsub ht).2)
          simpa [S.kappa_I01] using this⟩
      exact (le_csSup bdd hIn)
    have : 1 - S.kappa M ≤ S.kappa K' + ε := by linarith [hκK'_ge]
    exact le_trans this (add_le_add_right hν_ge' ε)

  -- Schluss
  have hEqν : S.nu (sUnion (KappaSystem.KFamily 𝓤)) = 1 - S.kappa M :=
    le_antisymm hν_le hν_ge
  calc
    S.kappa M + S.nu (sUnion (KappaSystem.KFamily 𝓤))
        = S.kappa M + (1 - S.kappa M) := by simp [hEqν]
    _   = 1 := by ring

end KappaSystem
