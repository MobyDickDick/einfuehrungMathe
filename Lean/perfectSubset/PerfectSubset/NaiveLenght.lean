/-
  NaiveLength.lean — Dualität κ(U)+ν(K)=1 und äußere-Längen-Charakterisierung
  (Version ohne sorry; + Korollare & simp-Helfer; bereinigt ohne set_option/omit)
-/

import Mathlib
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace NaiveLength

/-- Grundintervall [0,1] als Menge auf ℝ. -/
def I01 : Set ℝ := Icc (0 : ℝ) 1

/-! ## Hilfslemmas, die kein `S : KappaSystem` benötigen -/

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
    · exact False.elim (hxI.elim (by exact hx.1))
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

/-! ### Monotonie / einfache Schranken -/

/-- Monotonie von ν (mit `csSup_le`/`le_csSup`). -/
lemma mono_nu : ∀ {A B}, A ⊆ B → S.nu A ≤ S.nu B := by
  intro A B hAB
  classical
  -- BddAbove der Indexmenge von ν(B)
  have bddB :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ B ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, hTc, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
  -- Nonempty der Indexmenge von ν(A)
  have hneA :
      ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; exact False.elim hx
  -- Ziel: csSup(Index A) ≤ csSup(Index B)
  apply csSup_le hneA
  intro x hx
  rcases hx with ⟨T, hTc, hTsub, rfl⟩
  -- T ⊆ A∩I01 ⇒ T ⊆ B∩I01
  have hTsub' : T ⊆ B ∩ I01 := by
    intro t ht
    rcases hTsub ht with ⟨htA, htI⟩
    exact ⟨hAB htA, htI⟩
  -- κ(T) ∈ Index B ⇒ κ(T) ≤ csSup(Index B)
  have hxB : S.kappa T ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ B ∩ I01 ∧ S.kappa T = κ} :=
    ⟨T, hTc, hTsub', rfl⟩
  exact le_csSup bddB hxB

/-- ν(K) = κ(K) auf kompakten K ⊆ [0,1]. -/
lemma nu_eq_kappa_on_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.nu K = S.kappa K := by
  classical
  have hcap : K ∩ I01 = K := NaiveLength.inter_I01_of_subset hKsub
  simp [nu, hcap, S.inner_regular_on_compact hKc hKsub]

/-- Komplementformel auf [0,1] für kompakte K. -/
lemma kappa_compl_compact {K : Set ℝ}
  (hKc : IsCompact K) (hKsub : K ⊆ I01) :
  S.kappa (I01 \ K) = 1 - S.kappa K :=
  S.compl_compact hKc hKsub

/-! ### Dualität für ein offenes U und sein Komplement K := I01 \ U -/

/-- Allgemeine Version (mit `let K := …`). -/
lemma kappa_add_nu_of_open_compl {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  let K := (I01 \ U)
  S.kappa U + S.nu K = 1 := by
  intro K
  classical
  -- K ist kompakt in I01
  obtain ⟨_, hKc⟩ := NaiveLength.isCompact_compl_of_open_sub_I01 (U := U) hUo hUsub
  have hKsub : K ⊆ I01 := by intro x hx; exact hx.1
  -- ν(K) = κ(K)
  have hνκ : S.nu K = S.kappa K := S.nu_eq_kappa_on_compact (K := K) hKc hKsub
  -- (I01 \ K) = U (weil K = I01 \ U und U ⊆ I01)
  have hSet : I01 \ K = U := NaiveLength.diff_diff_I01_of_subset hUsub
  -- κ(U) = 1 - κ(K)
  have hκU : S.kappa U = 1 - S.kappa K := by
    have hcomp : S.kappa (I01 \ K) = 1 - S.kappa K :=
      S.kappa_compl_compact (K := K) hKc hKsub
    simpa [hSet] using hcomp
  -- Schluss
  have : S.kappa U + S.nu K = (1 - S.kappa K) + S.kappa K := by
    simp [hνκ, hκU]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- Bequeme Version ohne `let`: für offenes `U ⊆ I01` gilt `κ(U)+ν(I01\U)=1`. -/
lemma kappa_add_nu_of_open_subset_I01 {U : Set ℝ}
  (hUo : IsOpen U) (hUsub : U ⊆ I01) :
  S.kappa U + S.nu (I01 \ U) = 1 := by
  simpa using (S.kappa_add_nu_of_open_compl (U := U) hUo hUsub)

/-! ### Schranken 0 ≤ κ,ν ≤ 1 (auf [0,1]) -/

/-- Untere/obere Schranke für κ(A), wenn A ⊆ [0,1]. -/
lemma kappa_bounds_of_subset_I01 {A : Set ℝ} (hA : A ⊆ I01) :
  0 ≤ S.kappa A ∧ S.kappa A ≤ 1 := by
  have h0 : 0 = S.kappa ∅ := by simp [S.kappa_empty]
  have h1 : S.kappa A ≤ S.kappa I01 := S.mono_kappa hA
  have : S.kappa ∅ ≤ S.kappa A := S.mono_kappa (by intro x hx; cases hx)
  have hnonneg : 0 ≤ S.kappa A := by simpa [h0] using this
  exact ⟨hnonneg, by simpa [S.kappa_I01] using h1⟩

/-- Generelle untere Schranke `0 ≤ ν(A)` (weil `T=∅` im Index liegt). -/
lemma zero_le_nu (A : Set ℝ) : 0 ≤ S.nu A := by
  classical
  have idx0 :
    0 ∈ {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; exact False.elim hx
  have bdd :
    BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ} := by
    refine ⟨1, ?_⟩
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this
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
    simpa [S.kappa_I01] using this
  have hne :
    ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ A ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
    intro x hx; exact False.elim hx
  have := csSup_le hne (by
    intro z hz
    rcases hz with ⟨T, _, hTsub, rfl⟩
    have : S.kappa T ≤ S.kappa I01 :=
      S.mono_kappa (by intro t ht; exact (hTsub ht).2)
    simpa [S.kappa_I01] using this)
  simpa [nu] using this

/-! ### Familien-Ergebnis κ(𝓤)+ν(𝓚)=1 -/

/-- Komplementfamilie zu 𝓤 in [0,1]. -/
def KFamily (𝓤 : Set (Set ℝ)) : Set (Set ℝ) := {K | ∃ U ∈ 𝓤, K = I01 \ U}

/-- κ(𝓤) := inf { κ(U) | U ∈ 𝓤 } -/
def kappaInf (𝓤 : Set (Set ℝ)) : ℝ := sInf (S.kappa '' 𝓤)
/-- ν(𝓚) := sup { ν(K) | K ∈ 𝓚 } -/
def nuSup (𝓚 : Set (Set ℝ)) : ℝ := sSup (S.nu '' 𝓚)

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
      intro x hx; exact False.elim hx
    have bddAboveIdx :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ} := by
      refine ⟨1, ?_⟩
      intro z hz
      rcases hz with ⟨T, hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simpa [S.kappa_I01] using this
    exact le_csSup bddAboveIdx idx0
  · refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨K, hK, rfl⟩
    have bddAboveIdx :
      BddAbove {κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ} := by
      refine ⟨1, ?_⟩
      intro z hz
      rcases hz with ⟨T, hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simpa [S.kappa_I01] using this
    have hneIdx :
      ({κ : ℝ | ∃ T, IsCompact T ∧ T ⊆ K ∩ I01 ∧ S.kappa T = κ}).Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨∅, isCompact_empty, ?_, by simp [S.kappa_empty]⟩
      intro x hx; exact False.elim hx
    exact csSup_le hneIdx (by
      intro z hz
      rcases hz with ⟨T, hTc, hTsub, rfl⟩
      have : S.kappa T ≤ S.kappa I01 :=
        S.mono_kappa (by intro t ht; exact (hTsub ht).2)
      simpa [S.kappa_I01] using this)

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
  have hBddκ := S.kappa_image_bdd 𝓤 hUsubI
  -- Nonempty- und Subset-Zeuge für 𝓚
  have hneK : 𝓚.Nonempty := by
    rcases hUnonempty with ⟨U0, hU0⟩
    exact ⟨I01 \ U0, ⟨U0, hU0, rfl⟩⟩
  have hKsubI : ∀ {K}, K ∈ 𝓚 → K ⊆ I01 := by
    intro K hK; rcases hK with ⟨U, hU, rfl⟩; intro x hx; exact hx.1
  have hBddν := S.nu_image_bdd (𝓚 := 𝓚) hneK hKsubI
  rcases hBddκ with ⟨hκlb, hκub⟩
  rcases hBddν with ⟨_, hνub⟩

  -- Abkürzungen
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
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have : 1 - β ≤ 1 - S.nu (I01 \ U) := sub_le_sub_left hνleβ 1
      exact hκU ▸ this
    -- inf-Bindung
    have hne : (S.kappa '' 𝓤).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.kappa U0, ⟨U0, hU0, rfl⟩⟩
    have := le_csInf hne (by intro y hy; rcases hy with ⟨U, hU, rfl⟩; exact hUbound hU)
    simpa [hαdef, hβdef] using this

  -- (ii) β ≤ 1 - α
  have h2 : β ≤ 1 - α := by
    have hKbound : ∀ {K}, K ∈ 𝓚 → S.nu K ≤ 1 - α := by
      intro K hK
      rcases hK with ⟨U, hU, rfl⟩
      -- α ≤ κ(U)
      have hMem : S.kappa U ∈ (S.kappa '' 𝓤) := ⟨U, hU, rfl⟩
      have hαleκU : α ≤ S.kappa U := by
        have := csInf_le hκlb hMem
        simpa [hαdef] using this
      -- ν(I01\U) = 1 - κ(U) ≤ 1 - α
      have hsum : S.kappa U + S.nu (I01 \ U) = 1 :=
        S.kappa_add_nu_of_open_subset_I01 (U := U) (hUo := hUopens hU) (hUsub := hUsubI hU)
      have hν : S.nu (I01 \ U) = 1 - S.kappa U := by
        have := congrArg (fun t => t - S.kappa U) hsum
        have : S.nu (I01 \ U) + S.kappa U = 1 := by simpa [add_comm] using hsum
        have := congrArg (fun t => t - S.kappa U) this
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have : 1 - S.kappa U ≤ 1 - α := by
        have := sub_le_sub_left hαleκU (1 : ℝ)
        simpa [sub_eq_add_neg] using this
      simpa [hν, sub_eq_add_neg] using this
    -- csSup ≤ 1 - α
    have hne' : (S.nu '' 𝓚).Nonempty := by
      rcases hUnonempty with ⟨U0, hU0⟩
      exact ⟨S.nu (I01 \ U0), ⟨I01 \ U0, ⟨U0, hU0, rfl⟩, rfl⟩⟩
    have := csSup_le hne' (by intro y hy; rcases hy with ⟨K, hK, rfl⟩; exact hKbound hK)
    simpa [hβdef, hαdef, sub_eq_add_neg] using this

  -- Schluss: α + β = 1
  have hle : α + β ≤ 1 := by
    have h := add_le_add_left h2 α
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hge : 1 ≤ α + β := by
    have h := add_le_add_right h1 β
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  exact le_antisymm hle (le_of_eq_of_le (by simp) hge)

/-- Äußere-Längen-Charakterisierung als Theorem (direkt aus Feld). -/
@[simp] lemma kappa_outer_open_sup (A : Set ℝ) :
  S.kappa A = sInf (S.kappa '' { U : Set ℝ | IsOpen U ∧ A ⊆ U }) :=
  S.outer_open_sup A

end KappaSystem

end NaiveLength
