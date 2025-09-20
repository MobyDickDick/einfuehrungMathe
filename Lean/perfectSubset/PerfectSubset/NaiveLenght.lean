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
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; cases hx
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
  -- Jetzt stimmt der Index von `nu` mit dem aus `inner_regular_on_compact` überein
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
    simp [S.kappa_empty] at this
    exact this
  exact ⟨hnonneg, by simpa [S.kappa_I01] using h1⟩

/-- Generelle untere Schranke `0 ≤ ν(A)` (weil `T=∅` im Index liegt). -/
lemma zero_le_nu (A : Set ℝ) : 0 ≤ S.nu A := by
  classical
  have idx0 :
    0 ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; cases hx
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
  -- Indexmenge nach oben durch 1 beschränkt
  have bdd :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
  -- und nicht leer (T = ∅)
  have hne :
      ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; cases hx
  -- daraus csSup ≤ 1
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
    simp [S.kappa_empty] at this
    exact this
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    have : S.kappa U ≤ S.kappa I01 := S.mono_kappa (hUsubI hU)
    simpa [S.kappa_I01] using this

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
    have idx0 :
      0 ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ} := by
      refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
      intro x hx; cases hx
    have bddAboveIdx :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ} := by
      refine ⟨1, ?_⟩
      intro z hz
      rcases hz with ⟨T, _hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simp [S.kappa_I01] at this
      exact this
    exact le_csSup bddAboveIdx idx0
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨K, hK, rfl⟩
    have bddAboveIdx :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ} := by
      refine ⟨1, ?_⟩
      intro z hz
      rcases hz with ⟨T, _hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simp [S.kappa_I01] at this
      exact this
    have hneIdx :
      ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
      intro x hx; cases hx
    exact csSup_le hneIdx (by
      intro z hz
      rcases hz with ⟨T, _hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simp [S.kappa_I01] at this
      exact this)

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
  -- `K = I01 \ U` ist abgeschlossen in `[0,1]` und damit kompakt
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

  -- Kürzel
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
    -- inf ≤ alle κ(U) ⇒ 1 - β ≤ α
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
    -- csSup ≤ 1 - α
    have hne' : (S.nu '' 𝓚).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.nu (I01 \ U0), ⟨I01 \ U0, ⟨U0, hU0, rfl⟩, rfl⟩⟩
    have hβraw : sSup (S.nu '' 𝓚) ≤ 1 - α :=
      csSup_le hne' (by intro y hy; rcases hy with ⟨K, hK, rfl⟩; exact hKbound hK)
    simpa [hβdef] using hβraw

  -- Schluss: α + β = 1
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
  -- ersetze νSup durch κSup über der Komplementfamilie
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
    · -- x ∈ ⋂₀ 𝓤 ⇒ x ∈ U₀ ⊆ I01 für ein U₀ ∈ 𝓤
      rcases hUnonempty with ⟨U0, hU0⟩
      have hxU0 : x ∈ U0 := (mem_sInter.mp hx) U0 hU0
      exact hUsub hU0 hxU0
    · -- x ∈ ⋃₀ 𝓚 ⇒ ∃ U∈𝓤, x ∈ I01 \ U ⇒ x ∈ I01
      rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
      rcases hK with ⟨U, hU, rfl⟩
      exact hxK.1
  -- Inklusion "⊇"
  have hsupset : I01 ⊆ (sInter 𝓤) ∪ sUnion (NaiveLength.KappaSystem.KFamily  𝓤) := by
    intro x hxI
    by_cases hAll : ∀ U ∈ 𝓤, x ∈ U
    · -- x liegt in allen U ⇒ x ∈ ⋂₀ 𝓤
      left; exact mem_sInter.mpr hAll
    · -- sonst ∃ U∈𝓤 mit x ∉ U ⇒ x ∈ I01 \ U ⇒ x ∈ ⋃₀ 𝓚
      right
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
  -- `⊆`: jedes `U` der Familie enthält `M`
  have h_right : M ⊆ sInter (relOpenSupersets M) := by
    intro x hxM
    refine mem_sInter.mpr ?_; intro U hU
    rcases hU with ⟨O, _hOopen, rfl, hMU⟩
    exact hMU hxM
  -- `⊇`: Punkte außerhalb von `M` werden durch `U = I01 ∩ {x}ᶜ` ausgeschlossen
  have h_left : sInter (relOpenSupersets M) ⊆ M := by
    intro x hxAll
    by_contra hxNot
    -- Kandidat: relativ offene Obermenge `U0 := I01 ∩ {x}ᶜ` (kommt aus offenem `O0 := {x}ᶜ`)
    have hU0 : I01 ∩ ({x}ᶜ) ∈ relOpenSupersets M := by
      refine ⟨{x}ᶜ, isOpen_compl_singleton, rfl, ?_⟩
      intro y hyM; exact ⟨hM hyM, by simpa [mem_compl] using ne_of_mem_of_not_mem hyM hxNot⟩
    -- Da `x` in *allen* `U` der Familie liegt, insbesondere in `U0` — Widerspruch
    have hxU0 : x ∈ I01 ∩ ({x}ᶜ) := (mem_sInter.mp hxAll) _ hU0
    exact hxU0.2 (by simp)
  exact le_antisymm h_left h_right

/-- Familie der **relativ offenen** Supersets von `M` in `I01`:
`U ∈ VFamily M` bedeutet: Es gibt ein offenens `V` (in ℝ) mit `U = I01 ∩ V`
und `M ⊆ U`. (Dann ist automatisch `U ⊆ I01`.) -/
def VFamily (M : Set ℝ) : Set (Set ℝ) :=
  {U | ∃ V : Set ℝ, IsOpen V ∧ U = I01 ∩ V ∧ M ⊆ U}

/-- `VFamily M` ist abgeschlossen unter endlichen Schnitten. -/
lemma VFamily_inter_mem {M U₁ U₂ : Set ℝ}
  (h₁ : U₁ ∈ VFamily M) (h₂ : U₂ ∈ VFamily M) :
  (U₁ ∩ U₂) ∈ VFamily M := by
  rcases h₁ with ⟨V₁, hV₁open, rfl, hMsub₁⟩
  rcases h₂ with ⟨V₂, hV₂open, rfl, hMsub₂⟩
  refine ⟨V₁ ∩ V₂, hV₁open.inter hV₂open, ?_, ?_⟩
  · -- (I01 ∩ V₁) ∩ (I01 ∩ V₂) = I01 ∩ (V₁ ∩ V₂)
    ext x; constructor
    · intro hx
      rcases hx with ⟨⟨hxI, hxV₁⟩, ⟨_, hxV₂⟩⟩
      exact ⟨hxI, ⟨hxV₁, hxV₂⟩⟩
    · intro hx
      rcases hx with ⟨hxI, hxV⟩
      exact ⟨⟨hxI, hxV.1⟩, ⟨hxI, hxV.2⟩⟩
  · -- M ⊆ (I01 ∩ V₁) ∩ (I01 ∩ V₂)
    intro x hxM
    have hx₁ := hMsub₁ hxM  -- : x ∈ I01 ∩ V₁
    have hx₂ := hMsub₂ hxM  -- : x ∈ I01 ∩ V₂
    have hxI  : x ∈ I01 := hx₁.1
    have hxV₁ : x ∈ V₁  := hx₁.2
    have hxV₂ : x ∈ V₂  := hx₂.2
    exact ⟨⟨hxI, hxV₁⟩, ⟨hxI, hxV₂⟩⟩

/-- **Kernlemma:** `M` ist der Schnitt aller relativ offenen Supersets von `M` in `I01`. -/
lemma inter_VFamily_eq (M : Set ℝ) (hM : M ⊆ I01) :
  (⋂₀ VFamily M) = M := by
  -- Inklusion ⊆
  have hsubset : (⋂₀ VFamily M) ⊆ M := by
    intro x hx
    by_contra hxM
    -- Wähle `V := {x}ᶜ` offen in ℝ, setze `U := I01 ∩ V`.
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      -- M ⊆ U, da `x ∉ M`
      intro y hyM
      have : y ≠ x := by
        intro hxy; exact hxM (by simpa [hxy] using hyM)
      exact ⟨hM hyM, this⟩
    -- Aus `x ∈ ⋂₀ VFamily M` folgt `x ∈ U`, aber `x ∉ U` – Widerspruch.
    have hxU : x ∈ U := (mem_sInter.mp hx) U hUmem
    have hxNotU : x ∉ U := by
      intro hxU'
      exact (hxU'.2 rfl)
    exact hxNotU hxU
  -- Inklusion ⊇
  have hsupset : M ⊆ (⋂₀ VFamily M) := by
    intro x hxM
    apply mem_sInter.mpr
    intro U hU
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    -- `M ⊆ U` liefert `x ∈ U`.
    simpa [hUdef] using hMsub hxM
  exact le_antisymm hsubset hsupset

/-- Zugehörige `K`-Familie: Komplemente der `V`-Mengen **innerhalb** von `I01`. -/
def KFamilyOf (M : Set ℝ) : Set (Set ℝ) :=
  {K | ∃ U ∈ VFamily M, K = I01 \ U}

/-- Komplementformel: `[0,1] \ M = ⋃₀ (KFamilyOf M)`. -/
lemma compl_eq_union_KFamilyOf (M : Set ℝ) (hM : M ⊆ I01) :
  I01 \ M = ⋃₀ (KFamilyOf M) := by
  classical
  -- Nutze `⋂₀ VFamily M = M` und De-Morgan auf `I01`.
  have hInt := inter_VFamily_eq (M := M) hM
  -- Punktweise Argument: für `x ∈ I01`
  ext x; constructor
  · intro hx
    rcases hx with ⟨hxI, hxNotM⟩
    -- Wähle `U := I01 ∩ {x}ᶜ`
    have hVopen : IsOpen ({x}ᶜ : Set ℝ) :=
      (isClosed_singleton (x := x)).isOpen_compl
    let U : Set ℝ := I01 ∩ ({x}ᶜ)
    have hUmem : U ∈ VFamily M := by
      refine ⟨{x}ᶜ, hVopen, rfl, ?_⟩
      intro y hyM
      have : y ≠ x := by
        intro h; exact hxNotM (by simpa [h] using hyM)
      exact ⟨hM hyM, this⟩
    -- Dann liegt `x` in `I01 \ U`, also auch in der großen Vereinigung.
    refine mem_sUnion.mpr ?_
    refine ⟨I01 \ U, ?_, ?_⟩
    · exact ⟨U, hUmem, rfl⟩
    · exact ⟨hxI, fun hU => hU.2 rfl⟩

  · intro hx
    rcases mem_sUnion.mp hx with ⟨K, hK, hxK⟩
    rcases hK with ⟨U, hU, rfl⟩
    rcases hxK with ⟨hxI, hxNotU⟩
    -- Aus `U ∈ VFamily M` folgt `M ⊆ U`; also `x ∉ M`.
    rcases hU with ⟨V, _hVopen, hUdef, hMsub⟩
    refine ⟨hxI, ?_⟩
    intro hxM
    -- aus `x ∈ M ⊆ U` und `U = I01 ∩ V` folgt `x ∈ V`
    have hxU' : x ∈ I01 ∩ V := by
      have hxU : x ∈ U := hMsub hxM
      simpa [hUdef] using hxU
    have hxV : x ∈ V := hxU'.2
    -- damit `x ∈ U` (weil `U = I01 ∩ V`)
    have : x ∈ U := by
      simpa [hUdef] using And.intro hxI hxV
    exact hxNotU this

end NaiveLength
