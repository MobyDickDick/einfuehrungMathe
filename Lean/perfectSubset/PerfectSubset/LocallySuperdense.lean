/-
  Aus jeder überabzählbaren Teilmenge M₁ ⊆ ℝ gibt es M₂ ⊆ M₁,
  so dass für alle x ∈ M₂ und alle ε > 0 beide Mengen
    (x-ε, x) ∩ M₂  und  (x, x+ε) ∩ M₂
  überabzählbar sind.
-/

import Mathlib

open Set Topology

namespace LocallySuperdense

/-- überabzählbar minus zählbar bleibt überabzählbar -/
lemma not_countable_diff_of_not_countable_of_countable
  {α} {A C : Set α} (hA : ¬ A.Countable) (hC : C.Countable) :
  ¬ (A \ C).Countable := by
  intro hdiff
  have hcap_cnt : (A ∩ C).Countable := hC.mono (by intro x hx; exact hx.2)
  have hUnionCnt : (A \ C ∪ (A ∩ C)).Countable := hdiff.union hcap_cnt
  have hA_subset : A ⊆ A \ C ∪ (A ∩ C) := by
    intro x hxA; by_cases hxC : x ∈ C
    · exact Or.inr ⟨hxA, hxC⟩
    · exact Or.inl ⟨hxA, hxC⟩
  exact hA (hUnionCnt.mono hA_subset)

/-- Wenn `A ⊆ B` und `A` überabzählbar, dann ist `B` überabzählbar. -/
lemma not_countable_of_subset_of_not_countable {α} {A B : Set α}
    (hA : ¬ A.Countable) (hAB : A ⊆ B) : ¬ B.Countable := by
  intro hB; exact hA (hB.mono hAB)

/-! ### Schritt 1: Zweiseitig dünne Punkte sind zählbar -/

/-- Zweiseitig dünne Punkte relativ zu `M`. -/
def Thin (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo (x - ε) (x + ε)) ∩ M).Countable}

/-- `Thin M` ist zählbar. -/
lemma Thin_countable (M : Set ℝ) : (Thin M).Countable := by
  classical
  -- Summanden für (a,b)∈ℚ×ℚ: entweder (Ioo a b ∩ M) oder ∅
  let Summand : (ℚ × ℚ) → Set ℝ := fun p =>
    if h : ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M).Countable then
      ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M) else (∅ : Set ℝ)

  have hSummand_cnt : ∀ p, (Summand p).Countable := by
    intro p; classical
    by_cases h : ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M).Countable
    · simp [Summand, h]
    · simp [Summand, h]

  -- Cover: Thin M ⊆ ⋃_{(a,b)} Summand (a,b)
  have hcover : Thin M ⊆ ⋃ p : ℚ × ℚ, Summand p := by
    intro x hx
    rcases hx with ⟨hxM, ε, hε, hcnt⟩
    -- wähle a,b ∈ ℚ mit x-ε < a < x < b < x+ε
    have hxlt₁ : x - ε < x := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₁ with ⟨a, ha1, ha2⟩
    have hxlt₂ : x < x + ε := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₂ with ⟨b, hb1, hb2⟩
    have hsub : (Ioo (a : ℝ) b) ⊆ Ioo (x - ε) (x + ε) := by
      intro y hy; exact ⟨lt_trans ha1 hy.1, lt_trans hy.2 hb2⟩
    have hmono : ((Ioo (a : ℝ) b) ∩ M) ⊆ ((Ioo (x - ε) (x + ε)) ∩ M) := by
      intro y hy; exact ⟨hsub hy.1, hy.2⟩
    have hcnt_ab : ((Ioo (a : ℝ) b) ∩ M).Countable := hcnt.mono hmono
    refine mem_iUnion.mpr ?_
    refine ⟨(a, b), ?_⟩
    have hx_in : x ∈ ((Ioo (a : ℝ) b) ∩ M) := ⟨⟨ha2, hb1⟩, hxM⟩
    have : Summand (a, b) = ((Ioo (a : ℝ) b) ∩ M) := by
      classical
      have h : ((Ioo (a : ℝ) b) ∩ M).Countable := hcnt_ab
      simp [Summand, h]
    simpa [this] using hx_in

  -- ℚ×ℚ ist zählbar (Instanz automatisch)
  haveI : Countable (ℚ × ℚ) := by infer_instance

  have big : (⋃ p : ℚ × ℚ, Summand p).Countable :=
    countable_iUnion (fun p => hSummand_cnt p)
  exact big.mono hcover

/-! ### Schritt 2: Einseitig leere Punkte sind zählbar -/

/-- Punkte mit "links-leerer" Umgebung in `M`. -/
def LeftEmpty (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo (x - ε) x) ∩ M) = ∅}

/-- Punkte mit "rechts-leerer" Umgebung in `M`. -/
def RightEmpty (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo x (x + ε)) ∩ M) = ∅}

/-- Für rationale Fenster `(a,b)` tragen wir links-leere Punkte zusammen;
    pro Fenster höchstens ein Punkt ⇒ zählbar. -/
lemma LeftEmpty_countable (M : Set ℝ) : (LeftEmpty M).Countable := by
  classical
  -- Fixe Fenster über ℚ×ℚ
  let LE (a b : ℚ) : Set ℝ :=
    {x | x ∈ M ∧ (a : ℝ) < x ∧ x < (b : ℝ) ∧ ((Ioo (a : ℝ) x) ∩ M) = ∅}
  -- Jedes LE a b ist subsingleton ⇒ zählbar
  have hSub : ∀ a b, (LE a b).Subsingleton := by
    intro a b x hx y hy
    rcases hx with ⟨hxM, hax, hxb, hxE⟩
    rcases hy with ⟨hyM, hay, hyb, hyE⟩
    by_contra hxy
    cases lt_or_gt_of_ne hxy with
    | inl hxy' =>
        -- x∈(Ioo a y)∩M, Widerspruch zu hyE
        have hxIn : x ∈ (Ioo (a : ℝ) y) ∩ M := ⟨⟨hax, hxy'⟩, hxM⟩
        simp [hyE] at hxIn
    | inr hyx' =>
        -- y∈(Ioo a x)∩M, Widerspruch zu hxE
        have hyIn : y ∈ (Ioo (a : ℝ) x) ∩ M := ⟨⟨hay, hyx'⟩, hyM⟩
        simp [hxE] at hyIn
  have hLE_cnt : ∀ a b, (LE a b).Countable := fun a b => (hSub a b).countable

  -- Cover: LeftEmpty M ⊆ ⋃_{a,b} LE a b
  have hcover : LeftEmpty M ⊆ ⋃ a : ℚ, ⋃ b : ℚ, LE a b := by
    intro x hx
    rcases hx with ⟨hxM, ε, hε, hempty⟩
    -- wähle a ∈ ℚ mit x-ε < a < x und b ∈ ℚ mit x < b < x+ε
    have hxlt₁ : x - ε < x := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₁ with ⟨a, ha1, ha2⟩
    have hxlt₂ : x < x + ε := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₂ with ⟨b, hb1, hb2⟩
    -- (Ioo a x) ⊆ (Ioo (x-ε) x), also leer
    have subEmpty : ((Ioo (a : ℝ) x) ∩ M) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyI : y ∈ Ioo (x - ε) x := ⟨lt_trans ha1 hy.1.1, hy.1.2⟩
      have : y ∈ ((Ioo (x - ε) x) ∩ M) := ⟨hyI, hy.2⟩
      simp [hempty] at this
    -- Eintrag in die große Vereinigung
    refine mem_iUnion.mpr ?_
    refine ⟨a, ?_⟩
    refine mem_iUnion.mpr ?_
    refine ⟨b, ?_⟩
    exact ⟨hxM, ha2, by exact hb1, subEmpty⟩

  have : (⋃ a : ℚ, ⋃ b : ℚ, LE a b).Countable :=
    countable_iUnion (fun a => countable_iUnion (fun b => hLE_cnt a b))
  exact this.mono hcover

/-- Rechts-leere Punkte: symmetrisch. -/
lemma RightEmpty_countable (M : Set ℝ) : (RightEmpty M).Countable := by
  classical
  let RE (a b : ℚ) : Set ℝ :=
    {x | x ∈ M ∧ (a : ℝ) < x ∧ x < (b : ℝ) ∧ ((Ioo x (b : ℝ)) ∩ M) = ∅}
  have hSub : ∀ a b, (RE a b).Subsingleton := by
    intro a b x hx y hy
    rcases hx with ⟨hxM, hax, hxb, hxE⟩
    rcases hy with ⟨hyM, hay, hyb, hyE⟩
    by_contra hxy
    cases lt_or_gt_of_ne hxy with
    | inl hxy' =>
        -- y ∈ (Ioo x b) ∩ M, Widerspruch zu hxE
        have hyIn : y ∈ (Ioo x (b : ℝ)) ∩ M := ⟨⟨hxy', hyb⟩, hyM⟩
        simp [hxE] at hyIn
    | inr hyx' =>
        -- x ∈ (Ioo y b) ∩ M, Widerspruch zu hyE
        have hxIn : x ∈ (Ioo y (b : ℝ)) ∩ M := ⟨⟨hyx', hxb⟩, hxM⟩
        simp [hyE] at hxIn
  have hRE_cnt : ∀ a b, (RE a b).Countable := fun a b => (hSub a b).countable

  -- Cover: RightEmpty M ⊆ ⋃_{a,b} RE a b
  have hcover : RightEmpty M ⊆ ⋃ a : ℚ, ⋃ b : ℚ, RE a b := by
    intro x hx
    rcases hx with ⟨hxM, ε, hε, hempty⟩
    -- wähle a ∈ ℚ mit x-ε < a < x und b ∈ ℚ mit x < b < x+ε
    have hxlt₁ : x - ε < x := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₁ with ⟨a, ha1, ha2⟩
    have hxlt₂ : x < x + ε := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₂ with ⟨b, hb1, hb2⟩
    -- (Ioo x b) ⊆ (Ioo x (x+ε)), also leer
    have subEmpty : ((Ioo x (b : ℝ)) ∩ M) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyI : y ∈ Ioo x (x + ε) := ⟨hy.1.1, lt_trans hy.1.2 hb2⟩
      have : y ∈ ((Ioo x (x + ε)) ∩ M) := ⟨hyI, hy.2⟩
      simp [hempty] at this
    refine mem_iUnion.mpr ?_
    refine ⟨a, ?_⟩
    refine mem_iUnion.mpr ?_
    refine ⟨b, ?_⟩
    exact ⟨hxM, ha2, hb1, subEmpty⟩

  have : (⋃ a : ℚ, ⋃ b : ℚ, RE a b).Countable :=
    countable_iUnion (fun a => countable_iUnion (fun b => hRE_cnt a b))
  exact this.mono hcover

/-! ### Schritt 3: Hauptsatz -/

/-- Hauptsatz (lokal superdichte Teilmenge). -/
theorem exists_locally_superdense_subset
  {M1 : Set ℝ} (hM1 : ¬ M1.Countable) :
  ∃ M2 ⊆ M1, ¬ M2.Countable ∧
    (∀ x ∈ M2, ∀ ε > 0,
      ¬ ((Ioo (x - ε) x) ∩ M2).Countable ∧
      ¬ ((Ioo x (x + ε)) ∩ M2).Countable) := by
  classical
  -- entferne zweiseitig dünne Punkte
  let Mr := Thin M1
  have hMr_cnt : Mr.Countable := Thin_countable M1
  let M3 : Set ℝ := M1 \ Mr
  have hM3_unc : ¬ M3.Countable :=
    not_countable_diff_of_not_countable_of_countable hM1 hMr_cnt
  -- entferne einseitig leere Punkte in M3
  let L := LeftEmpty M3
  let R := RightEmpty M3
  have hL_cnt : L.Countable := LeftEmpty_countable M3
  have hR_cnt : R.Countable := RightEmpty_countable M3
  let M2 : Set ℝ := M3 \ (L ∪ R)
  have hM2_subset_M1 : M2 ⊆ M1 := by intro x hx; exact hx.1.1
  have hM2_unc : ¬ M2.Countable := by
    have hLR_cnt : (L ∪ R).Countable := hL_cnt.union hR_cnt
    exact not_countable_diff_of_not_countable_of_countable hM3_unc hLR_cnt

  -- Kern-Eigenschaft in M3: beidseitige Fenster sind überabzählbar
  have key_M3 :
      ∀ y ∈ M3, ∀ δ > 0, ¬ ((Ioo (y - δ) (y + δ)) ∩ M3).Countable := by
    intro y hy δ hδ
    have hyM1 : y ∈ M1 := hy.1
    have hyNotThin : y ∉ Mr := hy.2
    have bigM1 : ¬ ((Ioo (y - δ) (y + δ)) ∩ M1).Countable := by
      intro hcnt; exact hyNotThin ⟨hyM1, ⟨δ, hδ, hcnt⟩⟩
    -- (Ioo∩M3) = (Ioo∩M1) \ (Ioo∩Mr)
    have eq₀ :
      ((Ioo (y - δ) (y + δ)) ∩ M3)
        = ((Ioo (y - δ) (y + δ)) ∩ M1) \ ((Ioo (y - δ) (y + δ)) ∩ Mr) := by
      ext t; constructor
      · intro ht
        rcases ht with ⟨htI, htM3⟩
        rcases htM3 with ⟨htM1, htNotMr⟩
        -- wir brauchen: t ∉ (Ioo … ∩ Mr)
        have hnot : t ∉ ((Ioo (y - δ) (y + δ)) ∩ Mr) := by
          intro h
          exact htNotMr h.2
        exact ⟨⟨htI, htM1⟩, hnot⟩
      · intro ht
        rcases ht with ⟨⟨htI, htM1⟩, hnot⟩
        -- aus ¬ (t ∈ (Ioo … ∩ Mr)) folgt ¬ (t ∈ Mr)
        have htNotMr : t ∉ Mr := by
          intro hMr
          exact hnot ⟨htI, hMr⟩
        exact ⟨htI, ⟨htM1, htNotMr⟩⟩
    have hcntMr : ((Ioo (y - δ) (y + δ)) ∩ Mr).Countable :=
      hMr_cnt.mono (by intro t ht; exact ht.2)
    simpa [eq₀] using
      not_countable_diff_of_not_countable_of_countable bigM1 hcntMr

  -- Schluss: für x∈M2 sind Halbintervalle gegen M2 überabzählbar
  refine ⟨M2, hM2_subset_M1, hM2_unc, ?_⟩
  intro x hxM2 ε hε
  have hxM3 : x ∈ M3 := hxM2.1
  have hxNotL : x ∉ L := by exact fun h => hxM2.2 (Or.inl h)
  have hxNotR : x ∉ R := by exact fun h => hxM2.2 (Or.inr h)

  -- Links: (x-ε,x)∩M3 ist nicht leer (sonst x∈L)
  have left_nonempty : ((Ioo (x - ε) x) ∩ M3).Nonempty := by
    by_contra hempty
    have : ((Ioo (x - ε) x) ∩ M3) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    exact hxNotL ⟨hxM3, ⟨ε, hε, by simp [this]⟩⟩
  rcases left_nonempty with ⟨y, hyI, hyM3⟩

  -- δL := min (y-(x-ε)) (x-y) > 0, und Ioo(y-δL,y+δL) ⊆ Ioo(x-ε,x)
  let δL : ℝ := min (y - (x - ε)) (x - y)
  have hδL_pos : 0 < δL := by
    have : 0 < y - (x - ε) := sub_pos.mpr hyI.1
    have : 0 < x - y := sub_pos.mpr hyI.2
    exact lt_min (sub_pos.mpr hyI.1) (sub_pos.mpr hyI.2)
  have hsubL : Ioo (y - δL) (y + δL) ⊆ Ioo (x - ε) x := by
    intro z hz
    have h1 : x - ε ≤ y - δL := by
      have : δL ≤ y - (x - ε) := min_le_left _ _
      have := sub_le_sub_left this y
      -- y - (y - (x - ε)) = x - ε
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : y + δL ≤ x := by
      have : δL ≤ x - y := min_le_right _ _
      simpa using add_le_add_left this y
    exact ⟨lt_of_le_of_lt h1 hz.1, lt_of_lt_of_le hz.2 h2⟩
  have bigL : ¬ ((Ioo (y - δL) (y + δL)) ∩ M3).Countable :=
    key_M3 y hyM3 δL hδL_pos
  have left_unc_M3 : ¬ ((Ioo (x - ε) x) ∩ M3).Countable :=
    not_countable_of_subset_of_not_countable bigL
      (by intro z hz; exact ⟨hsubL hz.1, hz.2⟩)

  -- Rechts analog
  have right_nonempty : ((Ioo x (x + ε)) ∩ M3).Nonempty := by
    by_contra hempty
    have : ((Ioo x (x + ε)) ∩ M3) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    exact hxNotR ⟨hxM3, ⟨ε, hε, by simp [this]⟩⟩
  rcases right_nonempty with ⟨y', hyI', hyM3'⟩
  let δR : ℝ := min (y' - x) (x + ε - y')
  have hδR_pos : 0 < δR :=
    lt_min (sub_pos.mpr hyI'.1) (sub_pos.mpr hyI'.2)
  have hsubR : Ioo (y' - δR) (y' + δR) ⊆ Ioo x (x + ε) := by
    intro z hz
    have h1 : x ≤ y' - δR := by
      have : δR ≤ y' - x := min_le_left _ _
      have := sub_le_sub_left this y'
      -- y' - (y' - x) = x
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : y' + δR ≤ x + ε := by
      have : δR ≤ x + ε - y' := min_le_right _ _
      simpa using add_le_add_left this y'
    exact ⟨lt_of_le_of_lt h1 hz.1, lt_of_lt_of_le hz.2 h2⟩
  have bigR : ¬ ((Ioo (y' - δR) (y' + δR)) ∩ M3).Countable :=
    key_M3 y' hyM3' δR hδR_pos
  have right_unc_M3 : ¬ ((Ioo x (x + ε)) ∩ M3).Countable :=
    not_countable_of_subset_of_not_countable bigR
      (by intro z hz; exact ⟨hsubR hz.1, hz.2⟩)

  -- Von M3 zu M2: zählbare Menge (L ∪ R) abziehen
  have hLR_cnt : (L ∪ R).Countable := hL_cnt.union hR_cnt

  have left_unc_M2 :
      ¬ ((Ioo (x - ε) x) ∩ M2).Countable := by
    have eq₁ :
      ((Ioo (x - ε) x) ∩ M2)
        = (((Ioo (x - ε) x) ∩ M3) \ (L ∪ R)) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzI, hzM2⟩
        rcases hzM2 with ⟨hzM3, hzNot⟩
        exact ⟨⟨hzI, hzM3⟩, hzNot⟩
      · intro hz
        rcases hz with ⟨⟨hzI, hzM3⟩, hzNot⟩
        exact ⟨hzI, ⟨hzM3, hzNot⟩⟩
    simpa [eq₁] using
      (not_countable_diff_of_not_countable_of_countable left_unc_M3 hLR_cnt)

  have right_unc_M2 :
      ¬ ((Ioo x (x + ε)) ∩ M2).Countable := by
    have eq₂ :
      ((Ioo x (x + ε)) ∩ M2)
        = (((Ioo x (x + ε)) ∩ M3) \ (L ∪ R)) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzI, hzM2⟩
        rcases hzM2 with ⟨hzM3, hzNot⟩
        exact ⟨⟨hzI, hzM3⟩, hzNot⟩
      · intro hz
        rcases hz with ⟨⟨hzI, hzM3⟩, hzNot⟩
        exact ⟨hzI, ⟨hzM3, hzNot⟩⟩
    simpa [eq₂] using
      (not_countable_diff_of_not_countable_of_countable right_unc_M3 hLR_cnt)

  exact ⟨left_unc_M2, right_unc_M2⟩

end LocallySuperdense
