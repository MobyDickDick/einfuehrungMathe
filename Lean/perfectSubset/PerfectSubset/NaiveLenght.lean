/-
  NaiveLength.lean — Dualität κ(U)+ν(K)=1 und äußere-Längen-Charakterisierung
  (Version ohne sorry; + Korollare & Helfer; bereinigt)
-/

import Mathlib
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace NaiveLength

/-- Grundintervall [0,1] als Menge auf ℝ. -/
def I01 : Set ℝ := Icc (0 : ℝ) 1

/-! ## Hilfslemmas ohne `S : KappaSystem` -/

/-- (simp) Wenn `K ⊆ I01`, dann `K ∩ I01 = K`. -/
@[simp] lemma inter_I01_of_subset {K : Set ℝ} (h : K ⊆ I01) : K ∩ I01 = K := by
  ext x; constructor
  · intro hx; exact hx.1
  · intro hx; exact ⟨hx, h hx⟩

/-- (simp) Wenn `U ⊆ I01`, dann `I01 \ (I01 \ U) = U`. -/
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
    · have : False := hxI hx.1
      exact this.elim
  · intro hxU
    exact ⟨hU hxU, by intro hxK; exact hxK.2 hxU⟩

/-- Wenn `U` offen und `U ⊆ I01`, dann ist `I01 \ U` abgeschlossen und kompakt. -/
lemma isCompact_compl_of_open_sub_I01
  {U : Set ℝ} (hUo : IsOpen U) (_hUsub : U ⊆ I01) :
  IsClosed (I01 \ U) ∧ IsCompact (I01 \ U) := by
  classical
  have hClosed : IsClosed (I01 ∩ Uᶜ) := isClosed_Icc.inter (hUo.isClosed_compl)
  have hComp   : IsCompact (I01 ∩ Uᶜ) := (isCompact_Icc).inter_right (hUo.isClosed_compl)
  simpa [Set.diff_eq] using And.intro hClosed hComp

/-- Abgeschlossenes Teil von `[0,1]` ist kompakt. -/
lemma compact_of_closed_subset_I01 {K : Set ℝ}
  (hKclosed : IsClosed K) (hKsub : K ⊆ I01) : IsCompact K := by
  have : IsCompact (I01 ∩ K) := (isCompact_Icc).inter_right hKclosed
  simpa [inter_comm, inter_left_comm, inter_I01_of_subset hKsub] using this

/-- System für eine äußere "Länge" κ mit den Eigenschaften,
    die wir in den Beweisen benötigen. -/
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

/-- Monotonie von ν. -/
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
    simp [S.kappa_I01] at this
    exact this
  have hneA :
      ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    use 0
    use ∅
    constructor
    · exact isCompact_empty
    · constructor
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

/-- Für kompaktes `K ⊆ I01`: `ν(K) = κ(K)`. -/
lemma nu_eq_kappa_on_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.nu K = S.kappa K := by
  classical
  have hcap : K ∩ I01 = K := NaiveLength.inter_I01_of_subset hKsub
  simpa [nu, hcap] using S.inner_regular_on_compact (K := K) hKc hKsub

/-- Komplementformel für kompaktes `K ⊆ I01`: `κ(I01 \ K) = 1 - κ(K)`. -/
lemma kappa_compl_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.kappa (I01 \ K) = 1 - S.kappa K := by
  classical
  exact S.compl_compact hKc hKsub

/-- Komplementformel in Dualform: für kompaktes `K ⊆ I01` gilt `κ(I01 \ K) + ν(K) = 1`. -/
lemma kappa_add_nu_of_closed_subset {K : Set ℝ}
  (hKclosed : IsClosed K) (hKsub : K ⊆ I01) :
  S.kappa (I01 \ K) + S.nu K = 1 := by
  classical
  have hKc : IsCompact K := NaiveLength.compact_of_closed_subset_I01 hKclosed hKsub
  have hνκ : S.nu K = S.kappa K := S.nu_eq_kappa_on_compact hKc hKsub
  have hκ : S.kappa (I01 \ K) = 1 - S.kappa K := S.kappa_compl_compact hKc hKsub
  simp [hνκ, hκ, sub_eq_add_neg]

/-! ### Dualität: offenes U und K := I01 \ U -/

/-- Allgemeine Version (mit `let K := …`). -/
lemma kappa_add_nu_of_open_compl {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  let K := (I01 \ U)
  S.kappa U + S.nu K = 1 := by
  intro K
  classical
  obtain ⟨_, hKc⟩ := NaiveLength.isCompact_compl_of_open_sub_I01 (U := U) hUo hUsub
  have hKsub : K ⊆ I01 := by intro x hx; exact hx.1
  have hνκ : S.nu K = S.kappa K := S.nu_eq_kappa_on_compact (K := K) hKc hKsub
  have hSet : I01 \ K = U := NaiveLength.diff_diff_I01_of_subset hUsub
  have hκU : S.kappa U = 1 - S.kappa K := by
    have hcomp : S.kappa (I01 \ K) = 1 - S.kappa K :=
      S.kappa_compl_compact (K := K) hKc hKsub
    simpa [hSet] using hcomp
  have hsum : S.kappa U + S.nu K = (1 - S.kappa K) + S.kappa K := by
    simp [hνκ, hκU]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum

/-- Bequeme Version ohne `let`: für offenes `U ⊆ I01` gilt `κ(U)+ν(I01\U)=1`. -/
lemma kappa_add_nu_of_open_subset_I01 {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  S.kappa U + S.nu (I01 \ U) = 1 := by
  simp [kappa_add_nu_of_open_compl, hUo, hUsub]

/-! ### Schranken 0 ≤ κ,ν ≤ 1 (auf [0,1]) -/

/-- Untere/obere Schranke für κ(A), wenn A ⊆ [0,1]. -/
lemma kappa_bounds_of_subset_I01 {A : Set ℝ} (hA : A ⊆ I01) :
  0 ≤ S.kappa A ∧ S.kappa A ≤ 1 := by
  have h1 : S.kappa A ≤ S.kappa I01 := S.mono_kappa hA
  have : S.kappa ∅ ≤ S.kappa A := S.mono_kappa (by intro x hx; cases hx)
  have hnonneg : 0 ≤ S.kappa A := by
    rw [S.kappa_empty] at this
    exact this
  exact ⟨hnonneg, by simpa only [S.kappa_I01] using h1⟩

/-- Generelle untere Schranke `0 ≤ ν(A)` (weil `T=∅` im Index liegt). -/
lemma zero_le_nu (A : Set ℝ) : 0 ≤ S.nu A := by
  classical
  have idx0 :
    0 ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨∅, isCompact_empty, ?_, ?_⟩
    · -- ∅ ⊆ A ∩ I01
      intro x hx; cases hx
    · -- S.kappa ∅ = 0
      exact S.kappa_empty
  have bdd :
    BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simp [S.kappa_I01] at this
    exact this
  exact le_csSup bdd idx0

/-- Obere Schranke `ν(A) ≤ 1` (weil alle `κ(T) ≤ κ(I01) = 1`). -/
lemma nu_le_one (A : Set ℝ) : S.nu A ≤ 1 := by
  classical
  have bdd :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa only [S.kappa_I01] using this
  have hne :
    ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, ?_⟩
    · -- ⊆-Teil
      intro x hx; cases hx
    · -- Gleichheit κ(∅)=0
      simp [S.kappa_empty]
  have h := csSup_le hne (by
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this)
  simpa [nu] using h

/-! ### Bequeme Korollare -/

/-- ν “sieht” nur den Anteil in `[0,1]`. -/
lemma nu_eq_nu_inter_I01 (A : Set ℝ) : S.nu A = S.nu (A ∩ I01) := by
  have hsub : (A ∩ I01) ⊆ I01 := by intro x hx; exact hx.2
  have hcap : (A ∩ I01) ∩ I01 = (A ∩ I01) :=
    by simp [NaiveLength.inter_I01_of_subset (K := A ∩ I01) hsub]
  simp [nu, hcap]

/-- (simp) κ(∅) = 0. -/
@[simp] lemma kappa_empty' : S.kappa ∅ = 0 :=
  S.kappa_empty

/-- (simp) ν(∅) = 0. -/
@[simp] lemma nu_empty : S.nu (∅ : Set ℝ) = 0 := by
  classical
  have h :=
    S.inner_regular_on_compact (K := (∅ : Set ℝ))
      isCompact_empty (by intro x hx; cases hx)
  simp [nu, S.kappa_empty]

/-- (simp) ν([0,1]) = 1. -/
@[simp] lemma nu_I01 : S.nu I01 = 1 := by
  have h := S.nu_eq_kappa_on_compact (K := I01)
    (hKc := isCompact_Icc) (hKsub := by intro x hx; exact hx)
  simp [S.kappa_I01] at h
  exact h

/-! ### Familien-Ergebnis κ(𝓤)+ν(𝓚)=1 und Varianten -/

/-- Komplementfamilie zu 𝓤 in [0,1]. -/
def KFamily (𝓤 : Set (Set ℝ)) : Set (Set ℝ) := {K | ∃ U ∈ 𝓤, K = I01 \ U}

/-- κ(𝓤) := inf { κ(U) | U ∈ 𝓤 } -/
def kappaInf (𝓤 : Set (Set ℝ)) : ℝ := sInf (S.kappa '' 𝓤)
/-- ν(𝓚) := sup { ν(K) | K ∈ 𝓚 } -/
def nuSup (𝓚 : Set (Set ℝ)) : ℝ := sSup (S.nu '' 𝓚)
/-- (neu) κ(𝓚) := sup { κ(K) | K ∈ 𝓚 } -/
def kappaSup (𝓚 : Set (Set ℝ)) : ℝ := sSup (S.kappa '' 𝓚)

/-- Beschränktheit der κ-Bilder. -/
lemma kappa_image_bdd
  (𝓤 : Set (Set ℝ))
  (hUsubI : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  BddBelow (S.kappa '' 𝓤) ∧ BddAbove (S.kappa '' 𝓤) := by
  refine ⟨?lb, ?ub⟩
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    have : S.kappa ∅ ≤ S.kappa U := S.mono_kappa (by intro x hx; cases hx)
    rw [S.kappa_empty] at this
    exact this
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    have : S.kappa U ≤ S.kappa I01 := S.mono_kappa (hUsubI hU)
    simpa only [S.kappa_I01] using this

/-- Beschränktheit der ν-Bilder. -/
lemma nu_image_bdd
  {𝓚 : Set (Set ℝ)}
  (_hneK : 𝓚.Nonempty)
  (_hKsubI : ∀ {K}, K ∈ 𝓚 → K ⊆ I01) :
  BddBelow (S.nu '' 𝓚) ∧ BddAbove (S.nu '' 𝓚) := by
  classical
  refine ⟨?lb, ?ub⟩
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨K, hK, rfl⟩
    exact S.zero_le_nu K
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨K, hK, rfl⟩
    exact S.nu_le_one K

/-! ### Kleine Helfer für Infimum/Supremum -/

/-- `κ(U)` liegt in der Bildmenge, daher `inf ≤ κ(U)`. -/
lemma kappaInf_le_of_mem {𝓤 : Set (Set ℝ)} {U : Set ℝ} (hU : U ∈ 𝓤) :
  S.kappaInf 𝓤 ≤ S.kappa U := by
  have hbb : BddBelow (S.kappa '' 𝓤) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨V, hV, rfl⟩
    have : S.kappa ∅ ≤ S.kappa V := S.mono_kappa (by intro x hx; cases hx)
    simpa [S.kappa_empty] using this
  have : S.kappa U ∈ (S.kappa '' 𝓤) := ⟨U, hU, rfl⟩
  simpa [kappaInf] using (csInf_le hbb this)

/-- `ν(K)` liegt in der Bildmenge, daher `ν(K) ≤ sup`. -/
lemma le_nuSup_of_mem
  {𝓚 : Set (Set ℝ)} {K : Set ℝ}
  (hK : K ∈ 𝓚)
  (hb : BddAbove (S.nu '' 𝓚)) :
  S.nu K ≤ S.nuSup 𝓚 := by
  have : S.nu K ∈ (S.nu '' 𝓚) := ⟨K, hK, rfl⟩
  simpa [nuSup] using (le_csSup hb this)

/-! ### Gleichheit `ν(𝓚) = κ(𝓚)` für die Komplementfamilie -/

/-- Für die Komplementfamilie `𝓚 = KFamily 𝓤` gilt punktweise `ν(K) = κ(K)`. -/
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
  have hKc : IsCompact (I01 \ U) :=
    NaiveLength.compact_of_closed_subset_I01 hclosed hsub
  simpa using S.nu_eq_kappa_on_compact (K := I01 \ U) hKc hsub

/-- Damit sind auch die Bildmengen identisch: `{ν K | K∈𝓚} = {κ K | K∈𝓚}`. -/
lemma image_nu_eq_image_kappa_on_KFamily
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  (S.nu '' KFamily 𝓤) = (S.kappa '' KFamily 𝓤) := by
  ext r; constructor
  · intro hr
    rcases hr with ⟨K, hK, rfl⟩
    have h := S.nu_eq_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub hK
    exact ⟨K, hK, h.symm⟩
  · intro hr
    rcases hr with ⟨K, hK, rfl⟩
    have h := S.nu_eq_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub hK
    exact ⟨K, hK, h⟩

/-- Folglich stimmen die Supremumswerte über `𝓚` überein: `ν(𝓚) = κ(𝓚)`. -/
lemma nuSup_eq_kappaSup_on_KFamily
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01) :
  S.nuSup (KFamily 𝓤) = S.kappaSup (KFamily 𝓤) := by
  simpa [nuSup, kappaSup]
    using congrArg sSup (S.image_nu_eq_image_kappa_on_KFamily (𝓤 := 𝓤) hUopen hUsub)

/-! ### Hauptsatz: κ(𝓤) + ν(𝓚) = 1 -/

/-- Hauptsatz: κ(𝓤) + ν(𝓚) = 1 für 𝓚 = { [0,1]\U | U∈𝓤 }. -/
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
    intro K hK; rcases hK with ⟨U, hU, rfl⟩; intro x hx; exact hx.1
  have hBddν := S.nu_image_bdd (𝓚 := 𝓚) hneK hKsubI
  rcases hBddκ with ⟨hκlb, hκub⟩
  rcases hBddν with ⟨_, hνub⟩

  set α := S.kappaInf 𝓤
  set β := S.nuSup 𝓚
  have hαdef : α = sInf (S.kappa '' 𝓤) := rfl
  have hβdef : β = sSup (S.nu '' 𝓚) := rfl

  -- (i) 1 - β ≤ α
  have h1 : 1 - β ≤ α := by
    have hUbound : ∀ {U}, U ∈ 𝓤 → 1 - β ≤ S.kappa U := by
      intro U hU
      have hKU : (I01 \ U) ∈ 𝓚 := ⟨U, hU, rfl⟩
      have hMem : S.nu (I01 \ U) ∈ (S.nu '' 𝓚) := ⟨I01 \ U, hKU, rfl⟩
      have hνleβ : S.nu (I01 \ U) ≤ β := by
        simpa [hβdef] using le_csSup hνub hMem
      have hsum : S.kappa U + S.nu (I01 \ U) = 1 :=
        S.kappa_add_nu_of_open_subset_I01 (U := U) (hUo := hUopens hU) (hUsub := hUsubI hU)
      have hκU : S.kappa U = 1 - S.nu (I01 \ U) := by
        have := congrArg (fun t => t - S.nu (I01 \ U)) hsum
        simp [sub_eq_add_neg] at this
        exact this
      have : 1 - β ≤ 1 - S.nu (I01 \ U) := sub_le_sub_left hνleβ 1
      exact hκU ▸ this
    have hne : (S.kappa '' 𝓤).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.kappa U0, ⟨U0, hU0, rfl⟩⟩
    have hαraw : 1 - β ≤ sInf (S.kappa '' 𝓤) :=
      le_csInf hne (by intro y hy; rcases hy with ⟨U, hU, rfl⟩; exact hUbound hU)
    simpa [hαdef] using hαraw

  -- (ii) β ≤ 1 - α
  have h2 : β ≤ 1 - α := by
    have hKbound : ∀ {K}, K ∈ 𝓚 → S.nu K ≤ 1 - α := by
      intro K hK
      rcases hK with ⟨U, hU, rfl⟩
      -- α ≤ κ(U)
      have hMem : S.kappa U ∈ (S.kappa '' 𝓤) := ⟨U, hU, rfl⟩
      have hαleκU : α ≤ S.kappa U := by
        have := csInf_le hκlb hMem
        simp [] at this
        exact this
      -- ν(I01\U) = 1 - κ(U) ≤ 1 - α
      have hsum : S.kappa U + S.nu (I01 \ U) = 1 :=
        S.kappa_add_nu_of_open_subset_I01 (U := U) (hUo := hUopens hU) (hUsub := hUsubI hU)
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

  have hle : α + β ≤ 1 := by
    have h := add_le_add_left h2 α
    simp [sub_eq_add_neg] at h
    exact h
  have hge : 1 ≤ α + β := by
    have h := add_le_add_right h1 β
    simp [sub_eq_add_neg] at h
    exact h
  exact le_antisymm hle (le_of_eq_of_le (by simp) hge)

/-- Äußere-Längen-Charakterisierung als Theorem (direkt aus Feld). -/
@[simp] lemma kappa_outer_open_sup (A : Set ℝ) :
  S.kappa A = sInf (S.kappa '' { U : Set ℝ | IsOpen U ∧ A ⊆ U }) :=
  S.outer_open_sup A

lemma kappaInf_add_kappaSup_on_KFamily_eq_one
  (𝓤 : Set (Set ℝ))
  (hUopen : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  let 𝓚 := KFamily 𝓤
  S.kappaInf 𝓤 + S.kappaSup 𝓚 = 1 := by
  intro 𝓚
  have := S.kappaInf_add_nuSup_eq_one 𝓤 hUopen hUsub hUnonempty
  simpa [S.nuSup_eq_kappaSup_on_KFamily 𝓤 hUopen hUsub] using this

end KappaSystem

/-- Für eine Familie `𝓤` von Teilmengen von `[0,1]` (jeweils `U ⊆ I01`)
    und `𝓚 = { I01 \ U | U ∈ 𝓤 }` gilt:
    `(⋂₀ 𝓤) ∪ ⋃₀ 𝓚 = I01`.
    (Die Annahme `𝓤.Nonempty` sorgt dafür, dass `⋂₀ 𝓤 ⊆ I01`.) -/
lemma interU_union_KFamily_eq_I01
  (𝓤 : Set (Set ℝ))
  (hUsub : ∀ ⦃U⦄, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  (sInter 𝓤) ∪ sUnion (NaiveLength.KappaSystem.KFamily 𝓤) = I01 := by
  classical
  -- Inklusion "⊆"
  have hsubset : (sInter 𝓤) ∪ sUnion (NaiveLength.KappaSystem.KFamily 𝓤) ⊆ I01 := by
    intro x hx
    rcases hx with hx | hx
    · rcases hUnonempty with ⟨U0, hU0⟩
      have hxU0 : x ∈ U0 := (mem_sInter.mp hx) U0 hU0
      exact hUsub hU0 hxU0
    · rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
      rcases hK with ⟨U, hU, rfl⟩
      exact hxK.1
  -- Inklusion "⊇"
  have hsupset : I01 ⊆ (sInter 𝓤) ∪ sUnion (NaiveLength.KappaSystem.KFamily  𝓤) := by
    intro x hxI
    by_cases hAll : ∀ U ∈ 𝓤, x ∈ U
    · left; exact mem_sInter.mpr hAll
    · right
      push_neg at hAll
      rcases hAll with ⟨U, hU, hxNot⟩
      exact mem_sUnion.mpr ⟨I01 \ U, ⟨U, hU, rfl⟩, ⟨hxI, hxNot⟩⟩
  exact le_antisymm hsubset hsupset

open Set

/-- Die Familie aller *relativ offenen* Obermengen von `M` in `[0,1]`:
    Ein `U` gehört dazu genau dann, wenn es ein offenes `O ⊆ ℝ` gibt mit
    `U = I01 ∩ O` und `M ⊆ U`. -/
def relOpenSupersets (M : Set ℝ) : Set (Set ℝ) :=
  {U | ∃ O : Set ℝ, IsOpen O ∧ U = I01 ∩ O ∧ M ⊆ U}

/-- Die Familie `relOpenSupersets M` ist unter endlichen Schnitten abgeschlossen. -/
lemma relOpenSupersets_closed_under_inter (M : Set ℝ) :
    ∀ {U₁} (_ : U₁ ∈ relOpenSupersets M) {U₂} (_ : U₂ ∈ relOpenSupersets M),
      U₁ ∩ U₂ ∈ relOpenSupersets M := by
  intro U₁ h₁ U₂ h₂
  rcases h₁ with ⟨O₁, hO₁open, rfl, hM₁⟩
  rcases h₂ with ⟨O₂, hO₂open, rfl, hM₂⟩
  refine ⟨O₁ ∩ O₂, hO₁open.inter hO₂open, ?_, ?_⟩
  · ext x; constructor <;> intro hx
    · rcases hx with ⟨⟨hxI, hxO₁⟩, ⟨_, hxO₂⟩⟩
      exact ⟨hxI, ⟨hxO₁, hxO₂⟩⟩
    · rcases hx with ⟨hxI, hxO⟩
      exact ⟨⟨hxI, hxO.1⟩, ⟨hxI, hxO.2⟩⟩
  · intro x hxM
    exact ⟨hM₁ hxM, hM₂ hxM⟩

/-- **Kernlemma:** Für *jedes* `M ⊆ I01` ist der Schnitt aller relativ offenen
    Obermengen von `M` genau `M` selbst. -/
lemma sInter_relOpenSupersets_eq (M : Set ℝ) (hM : M ⊆ I01) :
    sInter (relOpenSupersets M) = M := by
  have h_right : M ⊆ sInter (relOpenSupersets M) := by
    intro x hxM
    refine mem_sInter.mpr ?_; intro U hU
    rcases hU with ⟨O, _hOopen, rfl, hMU⟩
    exact hMU hxM
  have h_left : sInter (relOpenSupersets M) ⊆ M := by
    intro x hxAll
    by_contra hxNot
    have hU0 : I01 ∩ ({x}ᶜ) ∈ relOpenSupersets M := by
      refine ⟨{x}ᶜ, isOpen_compl_singleton, rfl, ?_⟩
      intro y hyM; exact ⟨hM hyM, by simpa [mem_compl] using ne_of_mem_of_not_mem hyM hxNot⟩
    have hxU0 : x ∈ I01 ∩ ({x}ᶜ) := (mem_sInter.mp hxAll) _ hU0
    exact hxU0.2 (by simp)
  exact le_antisymm h_left h_right

/-- Familie der **relativ offenen** Supersets von `M` in `I01`. -/
def VFamily (M : Set ℝ) : Set (Set ℝ) :=
  {U | ∃ V : Set ℝ, IsOpen V ∧ U = I01 ∩ V ∧ M ⊆ U}

/-- `VFamily M` ist abgeschlossen unter endlichen Schnitten. -/
lemma VFamily_inter_mem {M U₁ U₂ : Set ℝ}
  (h₁ : U₁ ∈ VFamily M) (h₂ : U₂ ∈ VFamily M) :
  (U₁ ∩ U₂) ∈ VFamily M := by
  rcases h₁ with ⟨V₁, hV₁open, rfl, hMsub₁⟩
  rcases h₂ with ⟨V₂, hV₂open, rfl, hMsub₂⟩
  refine ⟨V₁ ∩ V₂, hV₁open.inter hV₂open, ?_, ?_⟩
  · ext x; constructor
    · intro hx
      rcases hx with ⟨⟨hxI, hxV₁⟩, ⟨_, hxV₂⟩⟩
      exact ⟨hxI, ⟨hxV₁, hxV₂⟩⟩
    · intro hx
      rcases hx with ⟨hxI, hxV⟩
      exact ⟨⟨hxI, hxV.1⟩, ⟨hxI, hxV.2⟩⟩
  · intro x hxM
    have hx₁ := hMsub₁ hxM
    have hx₂ := hMsub₂ hxM
    exact ⟨⟨hx₁.1, hx₁.2⟩, ⟨hx₂.1, hx₂.2⟩⟩

/-- **Kernlemma:** `M` ist der Schnitt aller relativ offenen Supersets von `M` in `I01`. -/
lemma inter_VFamily_eq (M : Set ℝ) (hM : M ⊆ I01) :
  (⋂₀ VFamily M) = M := by
  have hsubset : (⋂₀ VFamily M) ⊆ M := by
    intro x hx
    by_contra hxM
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      intro y hyM
      have : y ≠ x := by
        intro hxy; exact hxM (by simpa [hxy] using hyM)
      exact ⟨hM hyM, this⟩
    have hxU : x ∈ U := (mem_sInter.mp hx) U hUmem
    have hxNotU : x ∉ U := by
      intro hxU'
      exact (hxU'.2 rfl)
    exact hxNotU hxU
  have hsupset : M ⊆ (⋂₀ VFamily M) := by
    intro x hxM
    apply mem_sInter.mpr
    intro U hU
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    simpa [hUdef] using hMsub hxM
  exact le_antisymm hsubset hsupset

/-- Zugehörige `K`-Familie: Komplemente der `V`-Mengen **innerhalb** von `I01`. -/
def KFamilyOf (M : Set ℝ) : Set (Set ℝ) :=
  {K | ∃ U ∈ VFamily M, K = I01 \ U}

/-- Komplementformel: `[0,1] \ M = ⋃₀ (KFamilyOf M)`. -/
lemma compl_eq_union_KFamilyOf (M : Set ℝ) (hM : M ⊆ I01) :
  I01 \ M = ⋃₀ (KFamilyOf M) := by
  classical
  have hInt := inter_VFamily_eq (M := M) hM
  ext x; constructor
  · intro hx
    rcases hx with ⟨hxI, hxNotM⟩
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      intro y hyM
      have : y ≠ x := by
        intro h; exact hxNotM (by simpa [h] using hyM)
      exact ⟨hM hyM, this⟩
    refine mem_sUnion.mpr ?_
    refine ⟨I01 \ U, ⟨U, hUmem, rfl⟩, ⟨hxI, ?_⟩⟩
    intro hxU; exact hxU.2 rfl
  · intro hx
    rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
    rcases hK with ⟨U, hU, rfl⟩
    rcases hxK with ⟨hxI, hxNotU⟩
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    refine ⟨hxI, ?_⟩
    intro hxM
    have hxU' : x ∈ I01 ∩ V := by
      have hxU : x ∈ U := hMsub hxM
      simpa [hUdef] using hxU
    have hxV : x ∈ V := hxU'.2
    have : x ∈ U := by
      simpa [hUdef] using And.intro hxI hxV
    exact hxNotU this

/-!
###############################################################################
# NEUER TAIL: Schnitt/Union-Formel über Familien und robuste Hilfslemmata
###############################################################################
-/

namespace KappaSystem

open Set
open scoped Topology

/-- Für offenes `O` ist `I01 ∩ Oᶜ` abgeschlossen. -/
lemma closed_I01_inter_compl_open {O : Set ℝ} (hO : IsOpen O) :
  IsClosed (I01 ∩ Oᶜ) :=
  isClosed_Icc.inter hO.isClosed_compl

/-- Elementare Gleichheit: `I01 \ (I01 ∩ O) = I01 ∩ Oᶜ`. -/
lemma diff_I01_inter_open_eq {O : Set ℝ} :
  I01 \ (I01 ∩ O) = I01 ∩ Oᶜ := by
  ext x; constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro hxO
    exact hx.2 ⟨hx.1, hxO⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro hxU
    exact hx.2 hxU.2

/-- Elementare Gleichheit: `I01 \ (I01 ∩ Oᶜ) = I01 ∩ O`. -/
lemma diff_I01_inter_compl_eq {O : Set ℝ} :
  I01 \ (I01 ∩ Oᶜ) = I01 ∩ O := by
  ext x; constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    by_contra hxO
    exact hx.2 ⟨hx.1, by simpa [mem_compl] using hxO⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro hxK
    exact hxK.2 (by simpa [mem_compl] using hx.2)

/-- Ohne Offenheitsannahmen: `⋃₀ KFamily 𝓤 = I01 \ ⋂₀ 𝓤`. -/
lemma sUnion_KFamily_eq_compl_sInter (𝓤 : Set (Set ℝ)) :
  sUnion (KFamily 𝓤) = I01 \ sInter 𝓤 := by
  classical
  ext x; constructor
  · intro hx
    rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
    rcases hK with ⟨U, hU, rfl⟩
    rcases hxK with ⟨hxI, hxNotU⟩
    exact ⟨hxI, by
      intro hxAll
      exact hxNotU ((mem_sInter.mp hxAll) U hU)⟩
  · intro hx
    rcases hx with ⟨hxI, hxNotAll⟩
    have : ∃ U ∈ 𝓤, x ∉ U := by
      by_contra h; push_neg at h
      exact hxNotAll (by intro U hU; exact h U hU)
    rcases this with ⟨U, hU, hxNotU⟩
    exact mem_sUnion.mpr ⟨I01 \ U, ⟨U, hU, rfl⟩, ⟨hxI, hxNotU⟩⟩

/-- Grund-Ungleichung: Für `A ⊆ I01` gilt `ν(A) ≤ 1 - κ(I01 \ A)`. -/
lemma nu_le_one_sub_kappa_compl_of_subset_I01
  (S : KappaSystem) {A : Set ℝ} (_ : A ⊆ I01) :
  S.nu A ≤ 1 - S.kappa (I01 \ A) := by
  classical
  let I :=
    {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}
  have hne : I.Nonempty := by
    refine ⟨0, ⟨∅, isCompact_empty, ?_, ?_⟩⟩
    · -- ∅ ⊆ A ∩ I01
      intro x hx; cases hx
    · -- κ(∅) = 0
      exact S.kappa_empty
      -- alternativ:  by simpa using S.kappa_empty
  have hbound : ∀ z ∈ I, z ≤ 1 - S.kappa (I01 \ A) := by
    intro z hz
    rcases hz with ⟨T, hTc, hTsub, rfl⟩
    have hTsubA : T ⊆ A   := by intro t ht; exact (hTsub ht).1
    have hTsubI : T ⊆ I01 := by intro t ht; exact (hTsub ht).2
    have hcomp : I01 \ A ⊆ I01 \ T := by
      intro x hx; exact ⟨hx.1, by intro hxT; exact hx.2 (hTsubA hxT)⟩
    have hmono := S.mono_kappa hcomp
    have hcompl : S.kappa (I01 \ T) = 1 - S.kappa T :=
      S.kappa_compl_compact (K := T) hTc hTsubI
    have : S.kappa (I01 \ A) ≤ 1 - S.kappa T := by
      rw [hcompl] at hmono
      exact hmono
    linarith
  have bdd : BddAbove I := ⟨1, by
    intro z hz; rcases hz with ⟨T, _, hTsub, rfl⟩
    have hmono : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    have : S.kappa T ≤ 1 := by
      rw [S.kappa_I01] at hmono
      exact hmono
    exact this⟩
  have hfin : sSup I ≤ 1 - S.kappa (I01 \ A) :=
    csSup_le hne (by intro z hz; exact hbound z hz)
  have hnu_eq : S.nu A = sSup I := rfl
  rw [hnu_eq]
  exact hfin

/-- Aus der äußeren Offenheits-Charakterisierung:
Für `M ⊆ I01` und `ε>0` gibt es ein offenes `O ⊇ M` mit
`κ(O) ≤ κ(M) + ε`. -/
 lemma exists_open_superset_kappa_within
  (S : KappaSystem) {M : Set ℝ} (_ : M ⊆ I01)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ O : Set ℝ, IsOpen O ∧ M ⊆ O ∧ S.kappa O ≤ S.kappa M + ε := by

  -- Die Familie aller offenen Obermengen von M in ℝ:
  let A : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}
  -- A : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}
  have hEq : S.kappa M = sInf (S.kappa '' A) := by
    -- ersetze das Ziel explizit durch die expandierte Definition von A
    change S.kappa M =
      sInf (S.kappa '' {U : Set ℝ | IsOpen U ∧ M ⊆ U})
    exact S.kappa_outer_open_sup (A := M)

  -- Nichtleerheit der Bildmenge: `univ` ist offen und enthält M
  have hA_nonempty : (S.kappa '' A).Nonempty := by
    refine ⟨S.kappa (Set.univ), ?_⟩
    exact ⟨Set.univ, And.intro isOpen_univ (by intro x _; trivial), rfl⟩

  -- (optionale) untere Schranke der Bildmenge (hilft zwar hier nicht zwingend,
  -- ist aber oft nützlich; bewusst ohne `simp`-Loops)
  have _hBBl : BddBelow (S.kappa '' A) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    -- 0 ≤ κ(U) via Monotonie von ∅ ⊆ U
    have hmono : S.kappa ∅ ≤ S.kappa U :=
      S.mono_kappa (by intro x hx; cases hx)
    -- κ(∅)=0 in den Typ von `hmono` einsetzen, ergibt 0 ≤ κ(U)
    exact (S.kappa_empty ▸ hmono)

  -- Widerspruchsbeweis: falls es KEIN so gutes O gibt,
  -- folgt κ(M)+ε ≤ sInf(Bild) = κ(M), im Widerspruch zu ε>0.
  by_contra h
  -- h : ¬ ∃ O, IsOpen O ∧ M ⊆ O ∧ S.kappa O ≤ S.kappa M + ε

  -- Aus h folgt: für alle y in der Bildmenge gilt κ(M)+ε ≤ y
  have hforall : ∀ y ∈ (S.kappa '' A), S.kappa M + ε ≤ y := by
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    -- hU : IsOpen U ∧ M ⊆ U
    have hnot : ¬ S.kappa U ≤ S.kappa M + ε := by
      -- direkt aus der Negation-Behauptung h für dieses U
      exact fun hle => h ⟨U, hU.1, hU.2, hle⟩
    -- in einer linearen Ordnung ist ¬(a ≤ b) ↔ b < a
    have : S.kappa M + ε < S.kappa U := lt_of_not_ge hnot
    exact le_of_lt this

  -- daraus: κ(M)+ε ≤ sInf(Bild)
  have h_le_inf : S.kappa M + ε ≤ sInf (S.kappa '' A) :=
    le_csInf hA_nonempty hforall

  -- aber sInf(Bild) = κ(M)
  -- h_le_inf : S.kappa M + ε ≤ sInf (S.kappa '' A)
  -- hEq      : S.kappa M = sInf (S.kappa '' A)
  have hcontra : S.kappa M + ε ≤ S.kappa M := by
    have h := h_le_inf
    -- ersetze die rechte Seite via hEq.symm : sInf (S.kappa '' A) = S.kappa M
    rw [hEq.symm] at h
    exact h

  -- Widerspruch zu ε>0
  have : False := by exact not_lt_of_ge hcontra (by linarith : S.kappa M < S.kappa M + ε)
  exact this.elim

namespace NaiveLength


/-- Aus der äußeren Offenheits-Charakterisierung:
Für `M ⊆ I01` und `ε>0` gibt es ein offenes `O ⊇ M` mit `κ(O) ≤ κ(M) + ε`. -/
lemma exists_open_superset_kappa_within
  (S : KappaSystem) {M : Set ℝ} (_ : M ⊆ I01)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ O : Set ℝ, IsOpen O ∧ M ⊆ O ∧ S.kappa O ≤ S.kappa M + ε := by
  classical
  -- Familie aller offenen Obermengen von M
  let A : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}

  -- κ(M) = sInf (κ '' A)
  have hEq : S.kappa M = sInf (S.kappa '' A) := by
    change S.kappa M = sInf (S.kappa '' {U | IsOpen U ∧ M ⊆ U})
    exact S.kappa_outer_open_sup (A := M)

  -- Nichtleerheit der Bildmenge (univ ist offen und enthält M)
  have hA_nonempty : (S.kappa '' A).Nonempty := by
    refine ⟨S.kappa (Set.univ), ?_⟩
    refine ⟨Set.univ, And.intro isOpen_univ (by intro _ _; trivial), rfl⟩

  -- Untere Schranke: 0 ≤ κ(U) für alle U in A
  have _hBBl : BddBelow (S.kappa '' A) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨U, _hU, rfl⟩
    -- ∅ ⊆ U ⇒ κ(∅) ≤ κ(U); κ(∅)=0
    have hmono : S.kappa ∅ ≤ S.kappa U :=
      S.mono_kappa (by intro x hx; cases hx)
    exact (S.kappa_empty ▸ hmono)

  -- Widerspruchsbeweis: es gäbe kein gutes O
  by_contra h
  -- Dann gilt für alle y in der Bildmenge: κ(M)+ε ≤ y
  have hforall : ∀ y ∈ (S.kappa '' A), S.kappa M + ε ≤ y := by
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    have hnot : ¬ S.kappa U ≤ S.kappa M + ε := by
      exact fun hle => h ⟨U, hU.1, hU.2, hle⟩
    have : S.kappa M + ε < S.kappa U := lt_of_not_ge hnot
    exact le_of_lt this

  -- ⇒ κ(M)+ε ≤ sInf (κ '' A)
  have h_le_inf : S.kappa M + ε ≤ sInf (S.kappa '' A) :=
    le_csInf hA_nonempty hforall

  -- Aber sInf (κ '' A) = κ(M)
  have hcontra : S.kappa M + ε ≤ S.kappa M := by
    have hh : S.kappa M + ε ≤ sInf (S.kappa '' A) := h_le_inf
    -- `rw` ist hier völlig unproblematisch (nur 1 Umschreibung)
    rw [← hEq] at hh
    exact hh

  -- Widerspruch zu ε>0
  have : S.kappa M < S.kappa M + ε := by linarith
  exact (not_lt_of_ge hcontra) this


/-- **Hauptgleichung (Schnitt/Union):**
Für eine nichtleere Familie `𝓤` **offener** Mengen `U ⊆ I01` gilt
`κ(⋂₀ 𝓤) + ν(⋃₀ KFamily 𝓤) = 1`. -/
theorem kappa_sInter_add_nu_sUnionK_eq_one
  (S : KappaSystem)
  (𝓤 : Set (Set ℝ))
  (_ : ∀ {U}, U ∈ 𝓤 → IsOpen U)
  (hUsub : ∀ {U}, U ∈ 𝓤 → U ⊆ I01)
  (hUnonempty : 𝓤.Nonempty) :
  S.kappa (sInter 𝓤) + S.nu (sUnion (KappaSystem.KFamily 𝓤)) = 1 := by
  classical
  -- Bezeichner
  set M : Set ℝ := sInter 𝓤

  -- M ⊆ I01
  have hMsub : M ⊆ I01 := by
    intro x hxM
    rcases hUnonempty with ⟨U0, hU0⟩
    have hxU0 : x ∈ U0 := (mem_sInter.mp hxM) U0 hU0
    exact hUsub hU0 hxU0

  -- ⋃ KFamily 𝓤 = I01 \ M
  have hUnionEq :
      sUnion (KappaSystem.KFamily 𝓤) = I01 \ M :=
    (sUnion_KFamily_eq_compl_sInter (𝓤 := 𝓤))

  /- Obere Schranke: ν(⋃ K) ≤ 1 - κ(M) -/
  have hν_le : S.nu (sUnion (KappaSystem.KFamily 𝓤)) ≤ 1 - S.kappa M := by
    have hA : (I01 \ M) ⊆ I01 := by
      intro x hx; exact hx.1
    have hdd : I01 \ (I01 \ M) = M :=
      NaiveLength.diff_diff_I01_of_subset (U := M) hMsub
    -- Hilfslemma für ν(A) ≤ 1 - κ(I01 \ A) auf A := I01 \ M
    have h0 := nu_le_one_sub_kappa_compl_of_subset_I01 (S := S) (A := I01 \ M) hA
    -- h0 : S.nu (I01 \ M) ≤ 1 - S.kappa (I01 \ (I01 \ M))
    -- rechte Seite zu 1 - κ(M) umschreiben
    have hddκ : S.kappa (I01 \ (I01 \ M)) = S.kappa M :=
      congrArg S.kappa hdd
    have hddκ' : 1 - S.kappa (I01 \ (I01 \ M)) = 1 - S.kappa M :=
      congrArg (fun t => 1 - t) hddκ
    have h1 : S.nu (I01 \ M) ≤ 1 - S.kappa M := by
      have h0' := h0
      rw [hddκ'] at h0'
      exact h0'
    -- via ⋃ K = I01 \ M
    have hEqν : S.nu (sUnion (KappaSystem.KFamily 𝓤)) = S.nu (I01 \ M) :=
      congrArg S.nu hUnionEq
    have h1' := h1
    rw [← hEqν] at h1'
    exact h1'

  /- Untere Schranke via ε-Argument: 1 - κ(M) ≤ ν(⋃ K) -/
  have hν_ge : 1 - S.kappa M ≤ S.nu (sUnion (KappaSystem.KFamily 𝓤)) := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- Wähle offenes O ⊇ M mit κ(O) ≤ κ(M) + ε
    obtain ⟨O, hOopen, hMsubO, hκO⟩ :=
      NaiveLength.KappaSystem.exists_open_superset_kappa_within
        (S := S) (M := M) hMsub ε hε

    -- Relativ offen U' := I01 ∩ O, und K' := I01 \ U'
    let U' : Set ℝ := I01 ∩ O
    let K' : Set ℝ := I01 \ U'

    -- K' = I01 ∩ Oᶜ (elementares Mengenkalkül)
    have hK'def : K' = I01 ∩ Oᶜ := by
      -- I01 \ (I01 ∩ O) = I01 ∩ Oᶜ
      ext x; constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro hxO
        exact hx.2 ⟨hx.1, hxO⟩
      · intro hx
        rcases hx with ⟨hxI, hxNotO⟩
        exact ⟨hxI, by intro hxU; exact hxNotO hxU.2⟩

    -- K' ist abgeschlossen in ℝ (Schnitt von geschlossenem I01 mit abgeschlossenem Oᶜ)
    have hK'closed : IsClosed K' := by
      have hc : IsClosed (I01 ∩ Oᶜ) := isClosed_Icc.inter (hOopen.isClosed_compl)
      -- ersetze Ziel via hK'def ohne simp
      exact (hK'def ▸ hc)

    -- K' ⊆ I01, K' kompakt
    have hK'sub : K' ⊆ I01 := by
      intro x hx
      have hx' : x ∈ I01 ∩ Oᶜ := by
        -- benutze hK'def nur links (ohne simp-Loop)
        have : x ∈ I01 ∩ Oᶜ := by
          rcases hx with ⟨hxI, hxNotU⟩
          -- hxNotU : x ∉ U'  (also ¬ (x∈I01 ∧ x∈O))
          -- daraus folgt x∉O
          have hNotO : x ∉ O := by
            intro hxO
            exact hxNotU ⟨hxI, hxO⟩
          exact ⟨hxI, hNotO⟩
        exact this
      exact hx'.1

    have hK'comp : IsCompact K' :=
      NaiveLength.compact_of_closed_subset_I01 (K := K') hK'closed hK'sub

    -- U' ⊆ I01 und U' ⊆ O
    have hU'subI : U' ⊆ I01 := by intro x hx; exact hx.1
    have hU'subO : U' ⊆ O  := by intro x hx; exact hx.2

    -- M ⊆ U' (weil M ⊆ I01 und M ⊆ O)
    have hMsubU' : M ⊆ U' := by
      intro x hxM; exact ⟨hMsub hxM, hMsubO hxM⟩

    -- K' ⊆ I01 \ M ⇒ K' ⊆ ⋃ KFamily 𝓤 (via hUnionEq)
    have hK'subCompl : K' ⊆ (I01 \ M) := by
      intro x hx
      exact ⟨hx.1, by intro hxM; exact hx.2 (hMsubU' hxM)⟩

    have hK'subUnion : K' ⊆ sUnion (KappaSystem.KFamily 𝓤) := by
      -- benutze nur die Gleichheit hUnionEq gezielt
      have h := hK'subCompl
      intro x hx
      have hx' : x ∈ I01 \ M := h hx
      have hxUnion : x ∈ sUnion (KappaSystem.KFamily 𝓤) := by
        simpa [hUnionEq] using hx'
      exact hxUnion

    -- zuerst die Identität I01 \ K' = U' herstellen
    have hI01diffK' : I01 \ K' = U' := by
      change I01 \ K' = U'
      -- K' ⊆ I01, also die Standard-Identität aus deiner Datei
      exact NaiveLength.diff_diff_I01_of_subset (U := U') hU'subI

    -- Komplementformel auf K', danach linke Seite zu U' umschreiben
    have hκU' : S.kappa U' = 1 - S.kappa K' := by
      have hκ : S.kappa (I01 \ K') = 1 - S.kappa K' :=
        S.kappa_compl_compact (K := K') hK'comp hK'sub
      -- linke Seite per hI01diffK' ersetzen (ohne simp)
      exact (by
        have h' := hκ
        -- Ersetze (I01 \ K') durch U'
        -- also κ(U') = 1 - κ(K')
        -- mittels `rw`:
        -- (kein `simp`, nur gezieltes Umschreiben)
        have : S.kappa U' = 1 - S.kappa K' := by
          -- `hκ` ist bereits die Gleichheit, nach Umschreiben der linken Seite
          -- einfach: `rw [hI01diffK'] at h'` und `exact h'`
          -- in Term-Form:
          have htmp := hκ
          -- ersetze linke Seite
          -- (in Term-Mode nutzen wir `Eq.rec` durch `rw`-Äquivalent)
          -- einfacher:
          -- wir schreiben direkt:
          --   by simpa [hI01diffK'] using hκ
          -- um `simp` zu vermeiden, machen wir:
          --   (hI01diffK' ▸ hκ)
          -- `▸` ersetzt in der Aussage die linke Seite per Gleichheit
          exact (hI01diffK' ▸ hκ)
        exact this
      )

    -- Monotonie κ(U') ≤ κ(O)
    have hU_subO : U' ⊆ O := by intro x hx; exact hx.2
    have hκU_leO : S.kappa U' ≤ S.kappa O :=
      S.mono_kappa hU_subO

    -- daraus: κ(K') ≥ 1 - κ(O)
    have hκK'_ge_one_sub_κO : S.kappa K' ≥ 1 - S.kappa O := by
      -- ersetze in der Ungleichung links κ(U') durch 1 - κ(K')
      have h1' : 1 - S.kappa K' ≤ S.kappa O := (hκU' ▸ hκU_leO)
      linarith

    -- außerdem: κ(K') ≥ 1 - κ(M) - ε
    have hκK'_ge : S.kappa K' ≥ 1 - S.kappa M - ε := by
      have h1 : 1 - S.kappa M - ε ≤ 1 - S.kappa O := by
        -- aus κ(O) ≤ κ(M) + ε ⇒ 1 - κ(M) - ε ≤ 1 - κ(O)
        linarith [hκO]
      exact le_trans h1 hκK'_ge_one_sub_κO

    -- hebe κ(K') zu ν(⋃ K) an
    have hν_ge' : S.kappa K' ≤ S.nu (sUnion (KappaSystem.KFamily 𝓤)) := by
      -- 1) Element der Indexmenge in der ν-Definition
      have hIn :
        S.kappa K' ∈ {κ : ℝ | ∃ T, IsCompact T ∧
                              T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ} := by
        refine ⟨K', hK'comp, ?_, rfl⟩
        intro x hx
        exact ⟨hK'subUnion hx, hx.1⟩
      -- 2) Nach oben beschränkt
      have bdd :
          BddAbove {κ : ℝ | ∃ T, IsCompact T ∧
                                T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ} := by
        refine ⟨1, ?_⟩
        intro z hz
        rcases hz with ⟨T, _hTc, hTsub, rfl⟩
        have hmono : S.kappa T ≤ S.kappa I01 :=
          S.mono_kappa (by intro t ht; exact (hTsub ht).2)
        -- schreibe κ(I01)=1 ohne simp
        have hI : S.kappa I01 = 1 := S.kappa_I01
        have := hmono
        rw [hI] at this
        exact this
      -- 3) csSup-Schritt ⇒ κ(K') ≤ ν(⋃ K)
      have hcsup :
        S.kappa K' ≤
          sSup {κ : ℝ | ∃ T, IsCompact T ∧
                      T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ} :=
        le_csSup bdd hIn

      -- statt `simpa [KappaSystem.nu]` (führt zu simp-Loop):
      change
        S.kappa K' ≤
          sSup {κ : ℝ | ∃ T, IsCompact T ∧
                      T ⊆ (sUnion (KappaSystem.KFamily 𝓤)) ∩ I01 ∧ S.kappa T = κ}
      exact hcsup

    -- Klebeschritt: 1 - κ(M) ≤ ν(⋃ K) + ε
    have hstep1 : 1 - S.kappa M ≤ S.kappa K' + ε := by linarith [hκK'_ge]
    have hstep2 : S.kappa K' + ε ≤ S.nu (sUnion (KappaSystem.KFamily 𝓤)) + ε :=
      add_le_add_right hν_ge' ε
    exact le_trans hstep1 hstep2

  -- Gleichheit ν(⋃ K) = 1 - κ(M)
  have hEqν : S.nu (sUnion (KappaSystem.KFamily 𝓤)) = 1 - S.kappa M :=
    le_antisymm hν_le hν_ge

  -- Schlussrechnung
  calc
    S.kappa M + S.nu (sUnion (KappaSystem.KFamily 𝓤))
        = S.kappa M + (1 - S.kappa M) := by rw [hEqν]
    _   = 1 := by ring

end NaiveLength
end KappaSystem
end NaiveLength
