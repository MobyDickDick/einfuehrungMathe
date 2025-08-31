/-
  Aus jeder überabzählbaren Teilmenge M₁ ⊆ ℝ gibt es M₂ ⊆ M₁,
  so dass für alle x ∈ M₂ und alle ε > 0 beide Mengen
    (x-ε, x) ∩ M₂  und  (x, x+ε) ∩ M₂
  überabzählbar sind.

  Der Beweis geht so:
  1) "Zweiseitig dünne" Punkte (um die es ein beidseitiges Fenster mit zählbarem Schnitt mit M₁ gibt)
     bilden eine zählbare Menge `Mr`.
  2) Setze M₃ := M₁ \ Mr. Dann hat jeder Punkt in M₃ in *jedem* beidseitigen Fenster
     überabzählbar viele Punkte aus M₁; daraus folgt via Abziehen der zählbaren Mr:
     in jedem beidseitigen Fenster liegen auch überabzählbar viele Punkte aus M₃.
  3) "Einseitig leere" Punkte in M₃ (links- bzw. rechts-leer) bilden zählbare Mengen L bzw. R
     (jeweils über eine ℚ×ℚ-Parametrisierung; pro (a,b) ist der Summand sogar subsingleton).
  4) Setze M₂ := M₃ \ (L ∪ R). Dann ist M₂ ⊆ M₁ überabzählbar und beidseitig lokal überabzählbar.
-/

import Mathlib

open Set Topology

namespace LocallySuperdense

/-- Hilfslemma: überabzählbar minus zählbar bleibt überabzählbar. -/
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

/-- Hilfslemma: Ist `A` überabzählbar und `A ⊆ B`, dann ist `B` überabzählbar. -/
lemma not_countable_of_subset_of_not_countable {α} {A B : Set α}
    (hA : ¬ A.Countable) (hAB : A ⊆ B) : ¬ B.Countable := by
  intro hB; exact hA (hB.mono hAB)

/-! ### Schritt 1: Zweiseitig dünne Punkte sind zählbar -/

/-- Zweiseitig "dünne" Punkte relativ zu `M`:
    um `x` gibt es ein beidseitiges offenes Intervall, dessen Schnitt mit `M` zählbar ist. -/
def Thin (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo (x - ε) (x + ε)) ∩ M).Countable}

/-- `Thin M` ist zählbar. -/
lemma Thin_countable (M : Set ℝ) : (Thin M).Countable := by
  classical
  -- Für (a,b) ∈ ℚ×ℚ nehmen wir als Summand:
  --   falls (Ioo a b ∩ M) zählbar: genau diese Menge, sonst ∅.
  let Summand : (ℚ × ℚ) → Set ℝ := fun p =>
    if h : ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M).Countable then
      ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M)
    else (∅ : Set ℝ)
  have hSummand_cnt : ∀ p, (Summand p).Countable := by
    intro p; classical
    by_cases h : ((Ioo (p.1 : ℝ) (p.2 : ℝ)) ∩ M).Countable
    · simpa [Summand, h]
    · simpa [Summand, h] using (countable_empty : (∅ : Set ℝ).Countable)
  -- Cover: Thin M ⊆ ⋃_{(a,b)∈ℚ×ℚ} Summand (a,b)
  have hcover : Thin M ⊆ ⋃ p : ℚ × ℚ, Summand p := by
    intro x hx
    rcases hx with ⟨hxM, ⟨ε, hε, hcnt⟩⟩
    -- Wähle a,b ∈ ℚ mit x-ε < a < x < b < x+ε
    have hxlt₁ : x - ε < x := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₁ with ⟨a, ha1, ha2⟩
    have hxlt₂ : x < x + ε := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₂ with ⟨b, hb1, hb2⟩
    -- (Ioo a b) ⊆ (Ioo (x-ε) (x+ε))
    have hsub : (Ioo (a : ℝ) b) ⊆ Ioo (x - ε) (x + ε) := by
      intro y hy; exact ⟨lt_trans ha1 hy.1, lt_trans hy.2 hb2⟩
    have hmono : ((Ioo (a : ℝ) b) ∩ M) ⊆ ((Ioo (x - ε) (x + ε)) ∩ M) := by
      intro y hy; exact ⟨hsub hy.1, hy.2⟩
    -- (Ioo a b ∩ M) ist zählbar, als Teilmenge des zählbaren Fensters
    have hcnt_ab : ((Ioo (a : ℝ) b) ∩ M).Countable := hcnt.mono hmono
    -- Eintrag in die große Vereinigung, p = (a,b)
    refine mem_iUnion.mpr ?_
    refine ⟨(a, b), ?_⟩
    -- In diesem Summanden ist x enthalten:
    -- Summand (a,b) = (Ioo a b ∩ M) (weil hcnt_ab) und x ∈ Ioo a b ∩ M
    have hx_in : x ∈ ((Ioo (a : ℝ) b) ∩ M) := ⟨⟨ha2, hb1⟩, hxM⟩
    have : Summand (a, b) = ((Ioo (a : ℝ) b) ∩ M) := by
      classical
      have h : ((Ioo (a : ℝ) b) ∩ M).Countable := hcnt_ab
      simpa [Summand, h]
    simpa [this] using hx_in
  -- ℚ×ℚ ist zählbar ⇒ iUnion ist zählbar
  haveI : Countable (ℚ × ℚ) := countable_prod
  have big : (⋃ p : ℚ × ℚ, Summand p).Countable := countable_iUnion (fun p => hSummand_cnt p)
  exact big.mono hcover

/-! ### Schritt 2: Einseitig leere Punkte sind zählbar -/

/-- Punkte mit "links-leerer" Umgebung in `M`. -/
def LeftEmpty (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo (x - ε) x) ∩ M) = ∅}

/-- Punkte mit "rechts-leerer" Umgebung in `M`. -/
def RightEmpty (M : Set ℝ) : Set ℝ :=
  {x | x ∈ M ∧ ∃ ε > 0, ((Ioo x (x + ε)) ∩ M) = ∅}

/-- Für rationale Fenster `(a,b)` tragen wir links-leere Punkte zusammen; pro Fenster höchstens
    ein Punkt ⇒ zählbar. -/
lemma LeftEmpty_countable (M : Set ℝ) : (LeftEmpty M).Countable := by
  classical
  -- Fixe Fenster über ℚ×ℚ
  let LE (a b : ℚ) : Set ℝ :=
    {x | x ∈ M ∧ (a : ℝ) < x ∧ x < (b : ℝ) ∧ ((Ioo (a : ℝ) x) ∩ M) = ∅}
  -- Jedes LE a b ist subsingleton ⇒ zählbar
  have hSub : ∀ a b, (LE a b).Subsingleton := by
    intro a b
    intro x hx y hy
    by_contra hxy
    have hlt : x < y ∨ y < x := lt_or_gt_of_ne hxy
    cases hlt with
    | inl hxy' =>
        -- x ∈ (Ioo a y) ∩ M, aber das ist nach hy leer
        have hxIn : x ∈ (Ioo (a : ℝ) y) ∩ M := by
          refine ⟨⟨?_, ?_⟩, hx.1⟩
          · exact lt_trans hx.2.1 hxy'
          · exact hxy'
        have : ((Ioo (a : ℝ) y) ∩ M) = ∅ := hy.2.2.2
        simpa [this] using hxIn
    | inr hyx' =>
        -- y ∈ (Ioo a x) ∩ M, aber das ist nach hx leer
        have hyIn : y ∈ (Ioo (a : ℝ) x) ∩ M := by
          refine ⟨⟨?_, ?_⟩, hy.1⟩
          · exact lt_trans hy.2.1 hyx'
          · exact hyx'
        have : ((Ioo (a : ℝ) x) ∩ M) = ∅ := hx.2.2.2
        simpa [this] using hyIn
  have hLE_cnt : ∀ a b, (LE a b).Countable := fun a b => (hSub a b).countable
  -- Cover: LeftEmpty M ⊆ ⋃_{a,b} LE a b
  have hcover : LeftEmpty M ⊆ ⋃ a : ℚ, ⋃ b : ℚ, LE a b := by
    intro x hx
    rcases hx with ⟨hxM, ⟨ε, hε, hempty⟩⟩
    -- wähle a ∈ ℚ mit x-ε < a < x und b ∈ ℚ mit x < b
    have hxlt₁ : x - ε < x := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₁ with ⟨a, ha1, ha2⟩
    rcases exists_rat_btwn (lt_add_of_pos_right x hε) with ⟨b, hb1, _hb2⟩
    -- (Ioo a x) ⊆ (Ioo (x-ε) x), also leer
    have subEmpty : ((Ioo (a : ℝ) x) ∩ M) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyI : y ∈ Ioo (x - ε) x := ⟨lt_trans ha1 hy.1.1, hy.1.2⟩
      have : y ∈ ((Ioo (x - ε) x) ∩ M) := ⟨hyI, hy.2⟩
      simpa [hempty] using this
    -- Eintrag in die große Vereinigung
    refine mem_iUnion.mpr ?_
    refine ⟨a, ?_⟩
    refine mem_iUnion.mpr ?_
    refine ⟨b, ?_⟩
    exact ⟨hxM, ha2, by exact hb1, subEmpty⟩
  -- ℚ×ℚ ist zählbar ⇒ DoppeliUnion zählbar
  have : (⋃ a : ℚ, ⋃ b : ℚ, LE a b).Countable :=
    countable_iUnion (fun a => countable_iUnion (fun b => hLE_cnt a b))
  exact this.mono hcover

/-- Rechts-leere Punkte sind ebenso zählbar (symmetrischer Beweis wie links). -/
lemma RightEmpty_countable (M : Set ℝ) : (RightEmpty M).Countable := by
  classical
  -- Fixe Fenster über ℚ×ℚ
  let RE (a b : ℚ) : Set ℝ :=
    {x | x ∈ M ∧ (a : ℝ) < x ∧ x < (b : ℝ) ∧ ((Ioo x (b : ℝ)) ∩ M) = ∅}
  -- Jedes RE a b ist subsingleton ⇒ zählbar
  have hSub : ∀ a b, (RE a b).Subsingleton := by
    intro a b
    intro x hx y hy
    by_contra hxy
    have hlt : x < y ∨ y < x := lt_or_gt_of_ne hxy
    cases hlt with
    | inl hxy' =>
        -- y ∈ (Ioo x b) ∩ M, aber das ist nach hx leer
        have hyIn : y ∈ (Ioo x (b : ℝ)) ∩ M := by
          refine ⟨⟨?_, ?_⟩, hy.1⟩
          · exact hxy'
          · exact lt_trans hy.2.2.1 hx.2.2.1 -- y < b und x < y ⇒ x < b
        have : ((Ioo x (b : ℝ)) ∩ M) = ∅ := hx.2.2.2
        simpa [this] using hyIn
    | inr hyx' =>
        -- x ∈ (Ioo y b) ∩ M, aber das ist nach hy leer
        have hxIn : x ∈ (Ioo y (b : ℝ)) ∩ M := by
          refine ⟨⟨?_, ?_⟩, hx.1⟩
          · exact hyx'
          · exact lt_trans hx.2.2.1 hy.2.2.1
        have : ((Ioo y (b : ℝ)) ∩ M) = ∅ := hy.2.2.2
        simpa [this] using hxIn
  have hRE_cnt : ∀ a b, (RE a b).Countable := fun a b => (hSub a b).countable
  -- Cover: RightEmpty M ⊆ ⋃_{a,b} RE a b
  have hcover : RightEmpty M ⊆ ⋃ a : ℚ, ⋃ b : ℚ, RE a b := by
    intro x hx
    rcases hx with ⟨hxM, ⟨ε, hε, hempty⟩⟩
    -- wähle b ∈ ℚ mit x < b < x+ε und a ∈ ℚ mit a < x
    have hxlt₂ : x < x + ε := by have : (0 : ℝ) < ε := hε; linarith
    rcases exists_rat_btwn hxlt₂ with ⟨b, hb1, hb2⟩
    rcases exists_rat_btwn (sub_lt_self_iff x).mpr hε with ⟨a, _ha1, ha2⟩
    -- (Ioo x b) ⊆ (Ioo x (x+ε)), also leer
    have subEmpty : ((Ioo x (b : ℝ)) ∩ M) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hyI : y ∈ Ioo x (x + ε) := ⟨hy.1.1, lt_trans hy.1.2 hb2⟩
      have : y ∈ ((Ioo x (x + ε)) ∩ M) := ⟨hyI, hy.2⟩
      simpa [hempty] using this
    -- Eintrag in die große Vereinigung
    refine mem_iUnion.mpr ?_
    refine ⟨a, ?_⟩
    refine mem_iUnion.mpr ?_
    refine ⟨b, ?_⟩
    exact ⟨hxM, by exact ha2, hb1, subEmpty⟩
  -- ℚ×ℚ ist zählbar ⇒ DoppeliUnion zählbar
  have : (⋃ a : ℚ, ⋃ b : ℚ, RE a b).Countable :=
    countable_iUnion (fun a => countable_iUnion (fun b => hRE_cnt a b))
  exact this.mono hcover

/-! ### Schritt 3: Hauptsatz -/

/-- Hauptsatz (lokal superdichte Teilmenge): Aus `M₁` überabzählbar folgt
    `∃ M₂ ⊆ M₁`, überabzählbar, und für alle `x ∈ M₂, ε>0` sind
    beide Halbintervalle mit `M₂` überabzählbar. -/
theorem exists_locally_superdense_subset
  {M1 : Set ℝ} (hM1 : ¬ M1.Countable) :
  ∃ M2 ⊆ M1, ¬ M2.Countable ∧
    (∀ x ∈ M2, ∀ ε > 0,
      ¬ ((Ioo (x - ε) x) ∩ M2).Countable ∧
      ¬ ((Ioo x (x + ε)) ∩ M2).Countable) := by
  classical
  -- Schritt 1: entferne zweiseitig dünne Punkte
  let Mr := Thin M1
  have hMr_cnt : Mr.Countable := Thin_countable M1
  let M3 : Set ℝ := M1 \ Mr
  have hM3_unc : ¬ M3.Countable :=
    not_countable_diff_of_not_countable_of_countable hM1 hMr_cnt
  -- Schritt 2: entferne einseitig leere Punkte in M3
  let L := LeftEmpty M3
  let R := RightEmpty M3
  have hL_cnt : L.Countable := LeftEmpty_countable M3
  have hR_cnt : R.Countable := RightEmpty_countable M3
  let M2 : Set ℝ := M3 \ (L ∪ R)
  have hM2_subset_M1 : M2 ⊆ M1 := by
    intro x hx; exact hx.1.1
  have hM2_unc : ¬ M2.Countable := by
    have hLR_cnt : (L ∪ R).Countable := hL_cnt.union hR_cnt
    exact not_countable_diff_of_not_countable_of_countable hM3_unc hLR_cnt
  -- Kern-Eigenschaft in M3: um jeden y∈M3 und jedes δ>0 ist (Ioo (y-δ,y+δ) ∩ M3) überabzählbar.
  have key_M3 :
      ∀ y ∈ M3, ∀ δ > 0, ¬ ((Ioo (y - δ) (y + δ)) ∩ M3).Countable := by
    intro y hy δ hδ
    -- Aus y ∈ M3 folgt: y ∈ M1 und y ∉ Mr
    have hyM1 : y ∈ M1 := hy.1
    have hyNotThin : y ∉ Mr := hy.2
    -- Definition von Mr = Thin M1
    have : ¬ ((Ioo (y - δ) (y + δ)) ∩ M1).Countable := by
      intro hcnt; exact hyNotThin ⟨hyM1, ⟨δ, hδ, hcnt⟩⟩
    -- (Ioo∩M3) = (Ioo∩M1) \ (Ioo∩Mr)
    have eq₀ :
      ((Ioo (y - δ) (y + δ)) ∩ M3)
        = ((Ioo (y - δ) (y + δ)) ∩ M1) \ ((Ioo (y - δ) (y + δ)) ∩ Mr) := by
      ext t; constructor <;> intro ht
      · rcases ht with ⟨htI, ⟨htM1, htNotMr⟩⟩
        exact ⟨⟨htI, htM1⟩, ⟨htI, htNotMr⟩⟩
      · rcases ht with ⟨⟨htI, htM1⟩, ⟨_, htNotMr⟩⟩
        exact ⟨htI, ⟨htM1, htNotMr⟩⟩
    have hcntMr : ((Ioo (y - δ) (y + δ)) ∩ Mr).Countable :=
      hMr_cnt.mono (by intro t ht; exact ht.2)
    simpa [eq₀] using
      not_countable_diff_of_not_countable_of_countable this hcntMr
  -- Schluss: für x∈M2 sind Halbintervalle gegen M2 überabzählbar
  refine ⟨M2, hM2_subset_M1, hM2_unc, ?_⟩
  intro x hxM2 ε hε
  have hxM3 : x ∈ M3 := hxM2.1
  have hxNotL : x ∉ L := by exact fun h => hxM2.2 (Or.inl h)
  have hxNotR : x ∉ R := by exact fun h => hxM2.2 (Or.inr h)

  -- Links: (x-ε,x)∩M3 ist nicht leer (sonst x∈L); wähle y darin.
  have left_nonempty : ((Ioo (x - ε) x) ∩ M3).Nonempty := by
    by_contra hempty
    have : ((Ioo (x - ε) x) ∩ M3) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    exact hxNotL ⟨hxM3, ⟨ε, hε, by simpa [this]⟩⟩
  rcases left_nonempty with ⟨y, hyI, hyM3⟩
  -- kleines δ > 0 mit Ioo(y-δ,y+δ) ⊆ Ioo(x-ε,x):
  -- nimm δ := min (y - (x-ε)) (x - y)  (beides > 0, da y ∈ (x-ε,x))
  let δL : ℝ := min (y - (x - ε)) (x - y)
  have hδL_pos : 0 < δL := by
    have : 0 < y - (x - ε) := by exact sub_pos.mpr hyI.1
    have : 0 < min (y - (x - ε)) (x - y) := by
      have : 0 < x - y := sub_pos.mpr hyI.2
      exact lt_min (sub_pos.mpr hyI.1) this
    simpa [δL] using this
  have hsubL : Ioo (y - δL) (y + δL) ⊆ Ioo (x - ε) x := by
    intro z hz
    have h1 : x - ε ≤ y - δL := by
      have : δL ≤ y - (x - ε) := min_le_left _ _
      have : y - δL ≥ y - (y - (x - ε)) := by exact sub_le_sub_left this y
      -- y - (y - (x - ε)) = x - ε
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : y + δL ≤ x := by
      have : δL ≤ x - y := min_le_right _ _
      have := add_le_add_left this y
      simpa using this
    exact ⟨lt_of_le_of_lt h1 hz.1, lt_of_lt_of_le hz.2 h2⟩
  -- daraus: das große Intervall gegen M3 ist überabzählbar, also auch das linke Halbintervall
  have bigL : ¬ ((Ioo (y - δL) (y + δL)) ∩ M3).Countable := key_M3 y hyM3 δL hδL_pos
  have left_unc_M3 : ¬ ((Ioo (x - ε) x) ∩ M3).Countable :=
    not_countable_of_subset_of_not_countable bigL
      (by intro z hz; exact ⟨hsubL hz.1, hz.2⟩)

  -- Rechts analog:
  have right_nonempty : ((Ioo x (x + ε)) ∩ M3).Nonempty := by
    by_contra hempty
    have : ((Ioo x (x + ε)) ∩ M3) = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    exact hxNotR ⟨hxM3, ⟨ε, hε, by simpa [this]⟩⟩
  rcases right_nonempty with ⟨y', hyI', hyM3'⟩
  let δR : ℝ := min (y' - x) (x + ε - y')
  have hδR_pos : 0 < δR := by
    have : 0 < min (y' - x) (x + ε - y') := by
      exact lt_min (sub_pos.mpr hyI'.1) (sub_pos.mpr hyI'.2)
    simpa [δR] using this
  have hsubR : Ioo (y' - δR) (y' + δR) ⊆ Ioo x (x + ε) := by
    intro z hz
    have h1 : x ≤ y' - δR := by
      have : δR ≤ y' - x := min_le_left _ _
      have : y' - δR ≥ y' - (y' - x) := by exact sub_le_sub_left this y'
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : y' + δR ≤ x + ε := by
      have : δR ≤ x + ε - y' := min_le_right _ _
      have := add_le_add_left this y'
      simpa using this
    exact ⟨lt_of_le_of_lt h1 hz.1, lt_of_lt_of_le hz.2 h2⟩
  have bigR : ¬ ((Ioo (y' - δR) (y' + δR)) ∩ M3).Countable := key_M3 y' hyM3' δR hδR_pos
  have right_unc_M3 : ¬ ((Ioo x (x + ε)) ∩ M3).Countable :=
    not_countable_of_subset_of_not_countable bigR
      (by intro z hz; exact ⟨hsubR hz.1, hz.2⟩)

  -- Jetzt von M3 zu M2 (Abziehen der zählbaren Menge L ∪ R)
  have hLR_cnt : (L ∪ R).Countable := hL_cnt.union hR_cnt
  have left_unc_M2 :
      ¬ ((Ioo (x - ε) x) ∩ M2).Countable := by
    have : ((Ioo (x - ε) x) ∩ M2)
            = (((Ioo (x - ε) x) ∩ M3) \ (L ∪ R)) := by
      ext z; constructor
      · intro hz; exact ⟨⟨hz.1.1, hz.2.1⟩, hz.2.2⟩
      · intro hz; exact ⟨⟨hz.1.1, hz.2.1⟩, hz.1.2, hz.2.2⟩
    simpa [this] using
      (not_countable_diff_of_not_countable_of_countable left_unc_M3 hLR_cnt)
  have right_unc_M2 :
      ¬ ((Ioo x (x + ε)) ∩ M2).Countable := by
    have : ((Ioo x (x + ε)) ∩ M2)
            = (((Ioo x (x + ε)) ∩ M3) \ (L ∪ R)) := by
      ext z; constructor
      · intro hz; exact ⟨⟨hz.1.1, hz.2.1⟩, hz.2.2⟩
      · intro hz; exact ⟨⟨hz.1.1, hz.2.1⟩, hz.1.2, hz.2.2⟩
    simpa [this] using
      (not_countable_diff_of_not_countable_of_countable right_unc_M3 hLR_cnt)

  exact ⟨left_unc_M2, right_unc_M2⟩

end LocallySuperdense
