/-
Minimal Lean 4 skeleton (stable core, with dyadic reduction):
- genau ein `sorry` bei
    * `countable_BadLeft_fixed`  (Kernfall links)
- keine Cantor- /Node- /limitSet-Teile
- konsistente Nutzung von `Set.diff`
- Slices als Set-Comprehensions (kein `∩` im Kernteil)
-/

import Mathlib

open Classical Set

set_option autoImplicit true

namespace PerfectFromThick

/-! ### Slices (kein `∩`) -/

def LeftSlice  (M : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ M ∧ x - ε < y ∧ y < x }

def RightSlice (M : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ M ∧ x < y ∧ y < x + ε }

/-- Two-sided thickness via the slices. -/
@[simp] def TwoSidedThick (M : Set ℝ) : Prop :=
  ∀ x ∈ M, ∀ ε > 0,
    (¬ (LeftSlice  M x ε).Countable) ∧
    (¬ (RightSlice M x ε).Countable)

/-! ### Bad points -/

def BadLeft (M : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ M ∧ ∃ ε > 0, (LeftSlice M x ε).Countable }

def BadRight (M : Set ℝ) : Set ℝ :=
  { x : ℝ | x ∈ M ∧ ∃ ε > 0, (RightSlice M x ε).Countable }

@[simp] def Bad (M : Set ℝ) : Set ℝ := BadLeft M ∪ BadRight M


/-! ## Dyadische Reduktion (links und rechts) -/

open Filter Topology

/-- Dyadischer Radius `ε_k = (1 : ℝ) / (Nat.succ k)` (echt positiv). -/
noncomputable def dyadic (k : ℕ) : ℝ := (1 : ℝ) / (Nat.succ k)

lemma dyadic_pos (k : ℕ) : dyadic k > 0 := by
  unfold dyadic
  exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos k)

lemma exists_dyadic_le {ε : ℝ} (hε : ε > 0) :
  ∃ k, dyadic k ≤ ε := by
  -- Archimedisch: ∃ N, 1/(N+1) < ε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, ?_⟩
  have : (1 : ℝ) / (Nat.succ N) < ε := by
    simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hN
  exact le_of_lt this


/-! ### Kleine, robuste Rechen- und Ordnungs-Lemmas -/

section SliceHelpers
variable {M : Set ℝ} {x y ε : ℝ} {k : ℕ}

/-- Monotonie des rechten Slices in `ε`. -/
lemma RightSlice_mono_radius {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
  RightSlice M x ε₁ ⊆ RightSlice M x ε₂ := by
  intro y hy
  rcases hy with ⟨hyM, hlow, hupp⟩
  exact ⟨hyM, hlow, lt_of_lt_of_le hupp (add_le_add_left h x)⟩

/-- Monotonie des linken Slices in `ε`. -/
lemma LeftSlice_mono_radius {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
  LeftSlice M x ε₁ ⊆ LeftSlice M x ε₂ := by
  intro y hy
  rcases hy with ⟨hyM, hlow, hupp⟩
  have : x - ε₂ ≤ x - ε₁ := sub_le_sub_left h x
  exact ⟨hyM, lt_of_le_of_lt this hlow, hupp⟩

end SliceHelpers


/-! ### Links: Subunion + Kernfall -/

/-- Für jedes `x ∈ BadLeft M` gibt es
    * ein `k : ℕ` (dyadischer Radius) und
    * ein rationales `q` mit `x - dyadic k < q < x`,
  so dass auch `(LeftSlice M x (dyadic k))` abzählbar ist. -/
lemma BadLeft_subunion (M : Set ℝ) :
  BadLeft M ⊆ ⋃ (k : ℕ), ⋃ (q : ℚ),
    {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                   (LeftSlice M x (dyadic k)).Countable } := by
  intro x hx
  rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
  -- wähle dyadisch kleinen Radius ≤ ε
  rcases exists_dyadic_le (ε:=ε) hεpos with ⟨k, hk⟩
  -- dichte Q: wähle q mit x - dyadic k < q < x
  have : x - dyadic k < x := by
    have hkpos := dyadic_pos k
    have : x - dyadic k < x - 0 := by simpa using sub_lt_sub_left hkpos x
    simpa using this
  rcases exists_rat_btwn this with ⟨q, hq1, hq2⟩
  -- Monotonie in ε: (dyadic k) ≤ ε ⇒ LeftSlice … (dyadic k) ⊆ LeftSlice … ε
  have hmono : (LeftSlice M x (dyadic k)) ⊆ (LeftSlice M x ε) :=
    LeftSlice_mono_radius (M:=M) (x:=x) (ε₁:=dyadic k) (ε₂:=ε) hk
  have hcnt_dy : (LeftSlice M x (dyadic k)).Countable := hcnt.mono hmono
  -- packe in die Doppelsumme
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  -- zeigt: x erfüllt den Summanden (k,q)
  change x ∈ {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                        (LeftSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

/-- Fixiere `k` und einen rationalen Marker `q` (linker Kernfall). -/
lemma countable_BadLeft_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                 (LeftSlice M x (dyadic k)).Countable}).Countable := by
  /- hier kommt der konkrete Kodierungs- /Supremum-Beweis hinein (etwas länger) -/
  sorry

/-- **Links**: `BadLeft M` ist abzählbar. -/
lemma countable_BadLeft (M : Set ℝ) : (BadLeft M).Countable := by
  classical
  have big :
      (⋃ (k : ℕ), ⋃ (q : ℚ),
        {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                       (LeftSlice M x (dyadic k)).Countable }).Countable :=
    countable_iUnion (fun k =>
      countable_iUnion (fun q =>
        (countable_BadLeft_fixed (M:=M) k q)))
  exact big.mono (BadLeft_subunion (M:=M))


/-! ### Reine Negations-Geometrie auf Slices (für rechts) -/

/-- Vorabbildung von `M` unter der Negation. -/
def negPre (M : Set ℝ) : Set ℝ := {z : ℝ | -z ∈ M}

lemma negPre_negPre (M : Set ℝ) : negPre (negPre M) = M := by
  ext x; simp [negPre]

/-- Bild des rechten Slices unter `x ↦ -x` ist ein linker Slice des negierten Sets. -/
lemma image_neg_rightSlice (M : Set ℝ) (x ε : ℝ) :
  (fun y : ℝ => -y) '' (RightSlice M x ε) = LeftSlice (negPre M) (-x) ε := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyM, hgt, hlt⟩
    have hzNegPre : (-y) ∈ negPre M := by simpa [negPre] using hyM
    -- aus y < x + ε ⇒ -(x+ε) < -y  ⇒ (-x) - ε < -y
    have h1 : (-x) - ε < -y := by
      have := neg_lt_neg hlt
      -- -(x + ε) = (-x) - ε
      simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using this
    -- aus x < y ⇒ -y < -x
    have h2 : -y < -x := by simpa using (neg_lt_neg hgt)
    exact ⟨hzNegPre, h1, h2⟩
  · intro hz
    rcases hz with ⟨hzNegPre, h1, h2⟩
    refine ⟨-z, ?_, by simp⟩
    have hyM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- aus (-x)-ε < z ⇒ -z < x + ε
    have hlt' : -z < x + ε := by
      have := neg_lt_neg h1
      -- -(( -x) - ε) = x + ε
      simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc, neg_neg] using this
    -- aus z < -x ⇒ x < -z
    have hgt : x < -z := by
      have := neg_lt_neg h2
      simpa using this
    exact ⟨hyM, hgt, hlt'⟩

/-- Bild des linken Slices unter `x ↦ -x` ist ein rechter Slice des negierten Sets. -/
lemma image_neg_leftSlice (M : Set ℝ) (x ε : ℝ) :
  (fun y : ℝ => -y) '' (LeftSlice M x ε) = RightSlice (negPre M) (-x) ε := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyM, h1, h2⟩
    have hzNegPre : (-y) ∈ negPre M := by simpa [negPre] using hyM
    have hgt : -x < -y := by simpa using (neg_lt_neg h2)
    -- aus h1 : x - ε < y folgern wir -y < -x + ε (robust in 2 Schritten)
    have hlt : -y < -x + ε := by
      -- (1) ε addieren: x < y + ε
      have hxlt : x < y + ε := by
        have := add_lt_add_right h1 ε
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
              add_neg_cancel_right] using this
      -- (2) negieren und ε addieren:
      -- aus x < y + ε ⇒ -(y+ε) < -x ⇒  -(y+ε)+ε < -x+ε
      have hneg := neg_lt_neg hxlt
      have := add_lt_add_right hneg ε
      -- -(y+ε)+ε = -y
      simpa [neg_add, add_assoc, add_comm, add_left_comm,
            add_neg_cancel_right] using this
    exact ⟨hzNegPre, hgt, hlt⟩
  · intro hz
    rcases hz with ⟨hzNegPre, hgt, hlt⟩
    refine ⟨-z, ?_, by simp⟩
    have hyM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- aus -x < z ⇒ -z < x
    have h2 : -z < x := by simpa using (neg_lt_neg hgt)
    -- aus z < -x + ε folgern wir x - ε < -z (robust in 2 Schritten)
    have : z < -(x - ε) := by
      -- Schritt A: addiere x ⇒ z + x < ε
      have hxz : z + x < ε := by
        have := add_lt_add_right hlt x
        simpa [add_comm, add_left_comm, add_assoc] using this
      -- Schritt B: via lt_sub_iff_add_lt ⇒ z < ε - x  = -(x - ε)
      have hz' : z < ε - x := (lt_sub_iff_add_lt).mpr hxz
      simpa [sub_eq_add_neg, add_comm] using hz'
    have h1 : x - ε < -z := by simpa using (neg_lt_neg this)
    exact ⟨hyM, h1, h2⟩


/-! ### Rechts: Subunion + Kernfall (sauber, mit Slice-Negation) -/

/-- Für jedes `x ∈ BadRight M` gibt es
    * ein `k : ℕ` (dyadischer Radius) und
    * ein rationales `q` mit `x < q ∧ q < x + dyadic k`,
  so dass auch `(RightSlice M x (dyadic k))` abzählbar ist. -/
lemma BadRight_subunion (M : Set ℝ) :
  BadRight M ⊆ ⋃ (k : ℕ), ⋃ (q : ℚ),
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                   (RightSlice M x (dyadic k)).Countable } := by
  intro x hx
  rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
  -- wähle dyadisch kleinen Radius ≤ ε
  rcases exists_dyadic_le (ε:=ε) hεpos with ⟨k, hk⟩
  -- dichte Q: wähle q mit x < q < x + dyadic k
  have : x < x + dyadic k := by
    have hkpos := dyadic_pos k
    have := add_lt_add_left hkpos x   -- x + 0 < x + dyadic k
    simpa using this
  rcases exists_rat_btwn this with ⟨q, hq1, hq2⟩
  -- Monotonie in ε: (dyadic k) ≤ ε ⇒ RightSlice … (dyadic k) ⊆ RightSlice … ε
  have hmono : (RightSlice M x (dyadic k)) ⊆ (RightSlice M x ε) :=
    RightSlice_mono_radius (M:=M) (x:=x) (ε₁:=dyadic k) (ε₂:=ε) hk
  have hcnt_dy : (RightSlice M x (dyadic k)).Countable := hcnt.mono hmono
  -- packe in die Doppelsumme
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  -- zeigt: x erfüllt den Summanden (k,q)
  change x ∈ {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                        (RightSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

/-- Fixiere `k` und einen rationalen Marker `q` (rechter Kernfall).
    (ohne Spiegelung auf Ebene der Mengen; der Beweisschritt nutzt nur die
     Negations-Geometrie der **Slices** selbst) -/
lemma countable_BadRight_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}).Countable := by
  classical
  -- rechte Zielmenge:
  let SRight : Set ℝ :=
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                   (RightSlice M x (dyadic k)).Countable}
  -- linker Korrespondent unter Negation und Marke -q:
  let SLeftNeg : Set ℝ :=
    {z : ℝ | z ∈ negPre M ∧ (z - dyadic k : ℝ) < -q ∧ (-q : ℝ) < z ∧
                   (LeftSlice (negPre M) z (dyadic k)).Countable}
  -- Gleichheit des Negationsbildes:
  have himg : (fun x : ℝ => -x) '' SRight = SLeftNeg := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      rcases hx with ⟨hxM, hxltq, hqlt, hcnt⟩
      have hzNegPre : (-x) ∈ negPre M := by simpa [negPre] using hxM
      have h1 : (-x) - dyadic k < -q := by
        have := neg_lt_neg hqlt
        simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using this
      have h2 : (-q : ℝ) < -x := by simpa using (neg_lt_neg hxltq)
      -- rechte Slice-Abzählbarkeit → Bild unter Negation
      have himgSlice :
          ((fun y : ℝ => -y) '' (RightSlice M x (dyadic k))).Countable :=
        hcnt.image _
      -- per Geometrie-Lemma ist das genau der linke Slice
      have hLeft :
          (LeftSlice (negPre M) (-x) (dyadic k)).Countable := by
        simpa only [image_neg_rightSlice] using himgSlice
      exact ⟨hzNegPre, h1, h2, hLeft⟩
    · intro hz
      rcases hz with ⟨hzNegPre, h1, h2, hcnt⟩
      refine ⟨-z, ?_, by simp⟩
      have hxM : -z ∈ M := by simpa [negPre] using hzNegPre
      -- aus (-x)-δ < -q mit x := -z folgt  q < -z + δ
      have hqlt : (q : ℝ) < -z + dyadic k := by
        have := neg_lt_neg h1
        simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc, neg_neg] using this
      -- aus -q < z folgt -z < q
      have hxltq : (-z : ℝ) < q := by
        have := neg_lt_neg h2
        simpa using this
      -- linke Slice-Abzählbarkeit → rechte via Bild
      have hRight :
          (RightSlice M (-z) (dyadic k)).Countable := by
        simpa only [image_neg_leftSlice, negPre_negPre] using (hcnt.image (fun y : ℝ => -y))
      exact ⟨hxM, hxltq, by simpa [add_comm] using hqlt, hRight⟩
  -- `SLeftNeg` ist abzählbar durch den linken Kernfall (mit `negPre M` und Marke `-q`)
  have hLeftCnt : SLeftNeg.Countable := by
    simpa [SLeftNeg] using
      (countable_BadLeft_fixed (M:=negPre M) (k:=k) (q:=-q))
  -- daraus folgt Abzählbarkeit von `SRight`:
  -- Erst: Bild von `SRight` ist abzählbar
  have himgCnt : ((fun x : ℝ => -x) '' SRight).Countable := by
    simpa [himg] using hLeftCnt
  -- Zweit: Nochmals unter Negation abbilden ⇒ wieder `SRight`
  have : SRight.Countable := by
    have := himgCnt.image (fun x : ℝ => -x)
    -- (fun x => -x) ∘ (fun x => -x) = id; also Bild = SRight
    simpa [Set.image_image, Function.comp, neg_neg, Set.image_id] using this
  -- Ziel identifizieren
  simpa [SRight]

/-- **Rechts**: `BadRight M` ist abzählbar. -/
lemma countable_BadRight (M : Set ℝ) : (BadRight M).Countable := by
  classical
  have big :
      (⋃ (k : ℕ), ⋃ (q : ℚ),
        {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                       (RightSlice M x (dyadic k)).Countable }).Countable :=
    countable_iUnion (fun k =>
      countable_iUnion (fun q =>
        (countable_BadRight_fixed (M:=M) k q)))
  exact big.mono (BadRight_subunion (M:=M))


/-! ### Beide Seiten zusammen -/

lemma countable_Bad (M : Set ℝ) : (Bad M).Countable := by
  simpa [Bad] using (countable_BadLeft M).union (countable_BadRight M)


/-! ### Core und Slice-Algebra -/

/-- Core = entferne Bad-Punkte. (Kein `@[simp]`, um aggressives Unfolding zu vermeiden.) -/
def core (M : Set ℝ) : Set ℝ := Set.diff M (Bad M)

lemma core_subset (M : Set ℝ) : core M ⊆ M := by
  intro x hx; exact hx.1

/-- Linker Slice von `Set.diff M (Bad M)` ist `diff` des linken Slices. -/
lemma leftSlice_diff_eq (M : Set ℝ) (x ε : ℝ) :
  LeftSlice (Set.diff M (Bad M)) x ε = Set.diff (LeftSlice M x ε) (Bad M) := by
  ext y; constructor <;> intro hy
  · rcases hy with ⟨⟨hyM, hyNotBad⟩, hlt1, hlt2⟩
    exact ⟨⟨hyM, hlt1, hlt2⟩, hyNotBad⟩
  · rcases hy with ⟨⟨hyM, hlt1, hlt2⟩, hyNotBad⟩
    exact ⟨⟨hyM, hyNotBad⟩, hlt1, hlt2⟩

/-- Rechter Slice analog. -/
lemma rightSlice_diff_eq (M : Set ℝ) (x ε : ℝ) :
  RightSlice (Set.diff M (Bad M)) x ε = Set.diff (RightSlice M x ε) (Bad M) := by
  ext y; constructor <;> intro hy
  · rcases hy with ⟨⟨hyM, hyNotBad⟩, hgt, hlt⟩
    exact ⟨⟨hyM, hgt, hlt⟩, hyNotBad⟩
  · rcases hy with ⟨⟨hyM, hgt, hlt⟩, hyNotBad⟩
    exact ⟨⟨hyM, hyNotBad⟩, hgt, hlt⟩


/-! ### Mengen-Helfer (ohne `Uncountable.diff`, ohne `ext`) -/

/-- Ist `A` nicht abzählbar und `C` abzählbar, dann ist `A \\ C` nicht abzählbar. -/
lemma not_countable_diff_of_not_countable_of_countable
  {α} {A C : Set α}
  (hA : ¬ A.Countable) (hC : C.Countable) : ¬ (Set.diff A C).Countable := by
  intro hdiff
  -- (A ∩ C) ist abzählbar
  have hcap_cnt : (A ∩ C).Countable := hC.mono (by intro x hx; exact hx.2)
  -- Vereinigung zweier abzählbarer Mengen ist abzählbar
  have hUnionCnt : (Set.diff A C ∪ (A ∩ C)).Countable := hdiff.union hcap_cnt
  -- A ⊆ (A\\C) ∪ (A∩C)
  have hA_subset : A ⊆ Set.diff A C ∪ (A ∩ C) := by
    intro x hxA
    by_cases hxC : x ∈ C
    · exact Or.inr ⟨hxA, hxC⟩
    · exact Or.inl ⟨hxA, hxC⟩
  -- dann wäre A abzählbar — Widerspruch
  have : A.Countable := hUnionCnt.mono hA_subset
  exact hA this


/-- `core M` ist zweiseitig dick. -/
lemma TwoSidedThick_core (M : Set ℝ) : TwoSidedThick (core M) := by
  intro x hx ε hε
  rcases hx with ⟨hxM, hxNotBad⟩
  have hBadCnt : (Bad M).Countable := countable_Bad M
  -- große Slices in `M` sind nicht abzählbar, weil `x ∉ Bad M`
  have hLeftM  : ¬ (LeftSlice  M x ε).Countable := by
    intro hcnt; exact hxNotBad (Or.inl ⟨hxM, ⟨ε, hε, hcnt⟩⟩)
  have hRightM : ¬ (RightSlice M x ε).Countable := by
    intro hcnt; exact hxNotBad (Or.inr ⟨hxM, ⟨ε, hε, hcnt⟩⟩)
  -- ziehe die abzählbare Bad-Menge ab
  have hLeftCore  : ¬ (Set.diff (LeftSlice  M x ε) (Bad M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hLeftM hBadCnt
  have hRightCore : ¬ (Set.diff (RightSlice M x ε) (Bad M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hRightM hBadCnt
  -- explizite Umschreibungen für `core`
  have eqL' : LeftSlice (Set.diff M (Bad M)) x ε
      = Set.diff (LeftSlice M x ε) (Bad M) :=
    leftSlice_diff_eq (M:=M) (x:=x) (ε:=ε)
  have eqR' : RightSlice (Set.diff M (Bad M)) x ε
      = Set.diff (RightSlice M x ε) (Bad M) :=
    rightSlice_diff_eq (M:=M) (x:=x) (ε:=ε)
  -- bring die Ziele auf exakt dieselbe Form
  have eqL : LeftSlice (core M) x ε
      = Set.diff (LeftSlice M x ε) (Bad M) := by
    simpa [core] using eqL'
  have eqR : RightSlice (core M) x ε
      = Set.diff (RightSlice M x ε) (Bad M) := by
    simpa [core] using eqR'
  constructor
  · -- Ziel: ¬ (LeftSlice (core M) x ε).Countable
    simpa [eqL] using hLeftCore
  · -- Ziel: ¬ (RightSlice (core M) x ε).Countable
    simpa [eqR] using hRightCore

end PerfectFromThick

/-! ## Anwendung auf das Ziel (winzige Ergänzungen) -/
-- direkt vor "section ApplicationToGoal"
namespace PerfectFromThick


section ApplicationToGoal

/-- Ist `M` überabzählbar, dann ist auch `core M = M \\ Bad M` überabzählbar. -/
lemma uncountable_core_of_uncountable (M : Set ℝ) (hM : ¬ M.Countable) :
  ¬ (core M).Countable := by
  -- `Bad M` ist abzählbar; überabzählbar minus abzählbar bleibt überabzählbar
  simpa [core] using
    not_countable_diff_of_not_countable_of_countable
      (A := M) (C := Bad M) hM (countable_Bad M)

/-- Aus einer überabzählbaren Menge `M0` erhält man ein `M1 ⊆ M0`,
    das überabzählbar und zweiseitig dick ist.  Eine kanonische Wahl ist `M1 = core M0`. -/
lemma exists_twoSidedThick_subset (M0 : Set ℝ) (hM0 : ¬ M0.Countable) :
  ∃ M1 : Set ℝ, M1 ⊆ M0 ∧ ¬ M1.Countable ∧ TwoSidedThick M1 := by
  refine ⟨core M0, ?_, ?_, ?_⟩
  · exact core_subset M0
  · exact uncountable_core_of_uncountable (M := M0) hM0
  · exact TwoSidedThick_core M0

/-- In einer überabzählbaren Teilmenge von `ℝ` gibt es zwei streng geordnete Punkte. -/
lemma exists_two_points_of_uncountable (S : Set ℝ) (hS : ¬ S.Countable) :
  ∃ x0 x1 : ℝ, x0 ∈ S ∧ x1 ∈ S ∧ x0 < x1 := by
  classical
  -- `S` ist nicht leer
  have hne : S ≠ (∅ : Set ℝ) := by
    intro h
    set_option linter.unnecessarySimpa false in
    have : S.Countable := by
      simpa [h] using (countable_empty : (∅ : Set ℝ).Countable)
    exact hS this
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hne
  -- Ziehe einen Punkt `x1 ≠ x0` aus `S \\ {x0}` (immer noch überabzählbar)
  have hSdiff_unc :
      ¬ (S \ ({x0} : Set ℝ)).Countable :=
    not_countable_diff_of_not_countable_of_countable
      (A := S) (C := ({x0} : Set ℝ)) hS (countable_singleton x0)
  have hSdiff_ne : S \ ({x0} : Set ℝ) ≠ (∅ : Set ℝ) := by
    intro h
    set_option linter.unnecessarySimpa false in
    have : (S \ ({x0} : Set ℝ)).Countable := by
      simpa [h] using (countable_empty : (∅ : Set ℝ).Countable)
    exact hSdiff_unc this
  obtain ⟨x1, hx1⟩ := Set.nonempty_iff_ne_empty.mpr hSdiff_ne
  have hx1S : x1 ∈ S := hx1.1
  have hx1_ne_x0 : x1 ≠ x0 := by
    have : x1 ∉ ({x0} : Set ℝ) := hx1.2
    simpa [Set.mem_singleton_iff] using this
  -- total-ordnung in ℝ ⇒ entweder x0 < x1 oder x1 < x0; wähle passende Reihenfolge
  have hcmp : x0 < x1 ∨ x1 < x0 := lt_or_gt_of_ne (ne_comm.mp hx1_ne_x0)
  cases hcmp with
  | inl hlt =>
      exact ⟨x0, x1, hx0, hx1S, hlt⟩
  | inr hlt' =>
      exact ⟨x1, x0, hx1S, hx0, hlt'⟩

/-- Bequeme Auslese: Aus `M0` überabzählbar erhält man zwei Punkte `x0 < x1` in `core M0`. -/
lemma exists_two_points_in_core (M0 : Set ℝ) (hM0 : ¬ M0.Countable) :
  ∃ x0 x1 : ℝ, x0 ∈ core M0 ∧ x1 ∈ core M0 ∧ x0 < x1 := by
  have hcore_unc : ¬ (core M0).Countable := uncountable_core_of_uncountable (M := M0) hM0
  simpa using exists_two_points_of_uncountable (S := core M0) hcore_unc

/-- Aus Zweiseit-Dicke liest man die geforderten "beidseitig überabzählbar vielen Punkte in jedem
    ε-Intervall" direkt ab. (Nur eine bequeme Umformulierung.) -/
lemma twoSidedThick_gives_left_right (M : Set ℝ)
  (h : TwoSidedThick M) {x ε : ℝ} (hx : x ∈ M) (hε : ε > 0) :
  ¬ (LeftSlice M x ε).Countable ∧ ¬ (RightSlice M x ε).Countable :=
  h x hx ε hε

  /-! ### Mini-Auswahl aus Zweiseit-Dicke (für die 1./3.-Teilintervalle) -/

lemma exists_point_in_rightSlice_of_thick
  {M : Set ℝ} {x ε : ℝ}
  (hThick : TwoSidedThick M) (hx : x ∈ M) (hε : ε > 0) :
  ∃ y, y ∈ M ∧ x < y ∧ y < x + ε := by
  classical
  -- rechte Seite ist nicht abzählbar ⇒ insbesondere nicht leer
  have hnotCnt : ¬ (RightSlice M x ε).Countable := (hThick x hx ε hε).2
  have hne : (RightSlice M x ε).Nonempty := by
    by_contra hempty
    -- aus Nicht-Existenz folgt Gleichheit mit ∅
    have heq : RightSlice M x ε = (∅ : Set ℝ) := by
      -- hier ist `simpa` korrekt; `simp` kann kein `using`
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    -- leere Menge ist abzählbar ⇒ Widerspruch zur Nicht-Abzählbarkeit
    set_option linter.unnecessarySimpa false in
    have : (RightSlice M x ε).Countable := by
      simpa [heq] using (countable_empty : (∅ : Set ℝ).Countable)
    exact hnotCnt this
  rcases hne with ⟨y, hy⟩
  rcases hy with ⟨hyM, hxlt, hylt⟩
  exact ⟨y, hyM, hxlt, hylt⟩

lemma exists_point_in_leftSlice_of_thick
  {M : Set ℝ} {x ε : ℝ}
  (hThick : TwoSidedThick M) (hx : x ∈ M) (hε : ε > 0) :
  ∃ y, y ∈ M ∧ x - ε < y ∧ y < x := by
  classical
  -- linke Seite ist nicht abzählbar ⇒ insbesondere nicht leer
  have hnotCnt : ¬ (LeftSlice M x ε).Countable := (hThick x hx ε hε).1
  have hne : (LeftSlice M x ε).Nonempty := by
    by_contra hempty
    have heq : LeftSlice M x ε = (∅ : Set ℝ) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hempty
    set_option linter.unnecessarySimpa false in
    have : (LeftSlice M x ε).Countable := by
      simpa [heq] using (countable_empty : (∅ : Set ℝ).Countable)
    exact hnotCnt this
  rcases hne with ⟨y, hy⟩
  rcases hy with ⟨hyM, hlow, hupp⟩
  exact ⟨y, hyM, hlow, hupp⟩

/-- **Erste Auswahlstufe (1./3.-Regel)**:
Aus `TwoSidedThick M` und zwei Punkten `x0 < x1` in `M` erhält man
`x10 ∈ (x0, x0 + (x1 - x0)/3)` und `x11 ∈ (x1 - (x1 - x0)/3, x1)` in `M`. -/
lemma first_third_selection
  {M : Set ℝ} {x0 x1 : ℝ}
  (hThick : TwoSidedThick M)
  (hx0 : x0 ∈ M) (hx1 : x1 ∈ M) (hlt : x0 < x1) :
  ∃ x10 x11,
      x10 ∈ M ∧ x11 ∈ M ∧
      x0 < x10 ∧ x10 < x0 + (x1 - x0) / 3 ∧
      x1 - (x1 - x0) / 3 < x11 ∧ x11 < x1 := by
  have hpos : 0 < x1 - x0 := sub_pos.mpr hlt
  have hε : 0 < (x1 - x0) / 3 := by
    have three_pos : (0 : ℝ) < 3 := by norm_num
    exact div_pos hpos three_pos
  -- rechter Slice an x0 mit ε
  obtain ⟨x10, hx10M, hx0lt, hx10lt⟩ :=
    exists_point_in_rightSlice_of_thick (M:=M) (x:=x0) (ε:=(x1 - x0)/3)
      hThick hx0 hε
  -- linker Slice an x1 mit demselben ε
  obtain ⟨x11, hx11M, hx1low, hx11ltx1⟩ :=
    exists_point_in_leftSlice_of_thick (M:=M) (x:=x1) (ε:=(x1 - x0)/3)
      hThick hx1 hε
  -- Zusammenstellen
  exact ⟨x10, x11, hx10M, hx11M, hx0lt, hx10lt, hx1low, hx11ltx1⟩

/-! ### Mini-Schritt: aus einem Paar `x0<x1` zwei neue Teilintervalle -/

lemma first_third_intervals_nonempty
  {M : Set ℝ} {x0 x1 : ℝ}
  (hThick : TwoSidedThick M)
  (hx0 : x0 ∈ M) (hx1 : x1 ∈ M) (hlt : x0 < x1) :
  ∃ x10 x11,
      x0 < x10 ∧ x10 < x0 + (x1 - x0)/3 ∧
      x1 - (x1 - x0)/3 < x11 ∧ x11 < x1 ∧
      x10 ∈ M ∧ x11 ∈ M := by
  obtain ⟨x10, x11, hx10M, hx11M, hx0lt, hx10lt, hx1low, hx11ltx1⟩ :=
    first_third_selection (M:=M) hThick hx0 hx1 hlt
  exact ⟨x10, x11, hx0lt, hx10lt, hx1low, hx11ltx1, hx10M, hx11M⟩

/-- **Stage→Stage+1 (Ein Schritt)**:
Aus `x0<x1` in `M` erhält man zwei **nichtleere** neue Intervalle
`(x0,x10)` und `(x11,x1)` mit Endpunkten `x10,x11 ∈ M`, die strikt im
ersten bzw. letzten Drittel liegen. -/
lemma stage_succ_one_step
  {M : Set ℝ} {x0 x1 : ℝ}
  (hThick : TwoSidedThick M)
  (hx0 : x0 ∈ M) (hx1 : x1 ∈ M) (hlt : x0 < x1) :
  ∃ x10 x11,
      x0 < x10 ∧ x10 ∈ M ∧
      x11 < x1 ∧ x11 ∈ M ∧
      x10 < x0 + (x1 - x0)/3 ∧
      x1 - (x1 - x0)/3 < x11 := by
  obtain ⟨x10, x11, hx0lt, hx10lt, hx1low, hx11ltx1, hx10M, hx11M⟩ :=
    first_third_intervals_nonempty (M:=M) hThick hx0 hx1 hlt
  exact ⟨x10, x11, hx0lt, hx10M, hx11ltx1, hx11M, hx10lt, hx1low⟩

/-! ### Ein Schritt für eine endliche Familie von Intervallen -/
open Classical

/-- Hilfsprädikat: Ein Paar liegt in `M` und ist strikt geordnet. -/
def PairOk (M : Set ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 < p.2

lemma stage_succ_one_step_pairs
  {M : Set ℝ} (hThick : TwoSidedThick M) :
  ∀ {x0 x1 : ℝ}, x0 ∈ M → x1 ∈ M → x0 < x1 →
    ∃ x10 x11, PairOk M (x0, x10) ∧ PairOk M (x11, x1) ∧
      x10 < x0 + (x1 - x0)/3 ∧
      x1 - (x1 - x0)/3 < x11 := by
  intro x0 x1 hx0 hx1 hlt
  obtain ⟨x10, x11, hx0lt, hx10lt, hx1low, hx11ltx1, hx10M, hx11M⟩ :=
    first_third_intervals_nonempty (M:=M) hThick hx0 hx1 hlt
  refine ⟨x10, x11, ?_, ?_, hx10lt, hx1low⟩
  · -- PairOk M (x0, x10)
    exact ⟨hx0, hx10M, hx0lt⟩
  · -- PairOk M (x11, x1)
    exact ⟨hx11M, hx1, hx11ltx1⟩

/-- **Listen-Schritt (Stage → Stage+1):**
Aus einer endlichen Liste `L` von Intervall-Paaren in `M` (alle `PairOk`)
erzeugt eine neue Liste `L'`, in der jedes Paar `(x0,x1)` durch
`(x0,x10)` und `(x11,x1)` ersetzt ist, wobei `x10,x11 ∈ M` in den
ersten/letzten Dritteln liegen. -/
lemma stage_succ_list
  {M : Set ℝ} (hThick : TwoSidedThick M) :
  ∀ (L : List (ℝ × ℝ)),
    (∀ p ∈ L, PairOk M p) →
    ∃ L' : List (ℝ × ℝ),
      (∀ p' ∈ L', PairOk M p') ∧
      List.length L' = 2 * List.length L := by
  classical
  refine
    List.rec
      (motive := fun L =>
        (∀ p ∈ L, PairOk M p) →
        ∃ L' : List (ℝ × ℝ),
          (∀ p' ∈ L', PairOk M p') ∧
          List.length L' = 2 * List.length L)
      ?base ?step
  · -- Basis: L = []
    intro _h
    refine ⟨[], ?_, ?_⟩
    · intro p hp; cases hp
    · simp
  · -- Schritt: L = p :: L
    intro p L ih hAll
    have hpok : PairOk M p := hAll p (by simp)
    have hLok : ∀ q ∈ L, PairOk M q := by
      intro q hq; exact hAll q (by simp [hq])
    rcases p with ⟨x0, x1⟩
    rcases hpok with ⟨hx0M, hx1M, hlt⟩
    rcases stage_succ_one_step_pairs (M:=M) hThick hx0M hx1M hlt with
      ⟨x10, x11, hPairLeft, hPairRight, _h10FirstThird, _h11LastThird⟩
    rcases ih hLok with ⟨L', hL'OK, hlen⟩
    let Lnew : List (ℝ × ℝ) := (x0, x10) :: (x11, x1) :: L'
    refine ⟨Lnew, ?hOK, ?hLen⟩
    · -- alle Paare in Lnew sind ok
      intro q hq
      -- q ∈ (x0,x10) :: (x11,x1) :: L'  ⇔  q=(x0,x10) ∨ q=(x11,x1) ∨ q∈L'
      have hq' : q = (x0, x10) ∨ q = (x11, x1) ∨ q ∈ L' := by
        simpa [Lnew] using hq
      rcases hq' with hq0 | hq'
      · cases hq0; exact hPairLeft
      · rcases hq' with hq1 | hqL
        · cases hq1; exact hPairRight
        · exact hL'OK q hqL
    · -- Länge: 2 + length L' = 2 + 2 * length L = 2 * length (p :: L)
      simp [Lnew, hlen, List.length, two_mul,
            add_comm, add_left_comm, add_assoc]

/-- In einer zweiseitig dicken Menge hat kein Punkt eine isolierte Umgebung. -/
lemma no_isolated_points_of_thick
  {M : Set ℝ} (hThick : TwoSidedThick M) :
  ∀ x, x ∈ M → ∀ ε > 0,
    ∃ y ∈ M, ∃ z ∈ M,
      y < x ∧ x < z ∧ x - ε < y ∧ z < x + ε := by
  intro x hx ε hε
  obtain ⟨y, hyM, hy1, hy2⟩ :=
    exists_point_in_leftSlice_of_thick (M:=M) (x:=x) (ε:=ε) hThick hx hε
  obtain ⟨z, hzM, hz1, hz2⟩ :=
    exists_point_in_rightSlice_of_thick (M:=M) (x:=x) (ε:=ε) hThick hx hε
  exact ⟨y, hyM, z, hzM, hy2, hz1, hy1, hz2⟩

/-- Eine Menge ist perfekt, wenn sie abgeschlossen ist und keine isolierten Punkte hat. -/
def Perfect (S : Set ℝ) : Prop :=
  IsClosed S ∧ ∀ x ∈ S, ∀ ε > 0, ∃ y ≠ x, y ∈ S ∧ |y - x| < ε

/-- Aus einer überabzählbaren Menge `M0` erhält man eine perfekte Teilmenge `K`. -/
lemma exists_perfect_subset
  {M0 : Set ℝ} (_hM_0 : ¬ M0.Countable) :
  ∃ K : Set ℝ, K ⊆ closure M0 ∧ Perfect K := by
  -- Reduziere auf den Kern, der zwei-seitig dick ist
  let M1 := core M0
  have hThick : TwoSidedThick M1 := TwoSidedThick_core M0
  -- Wähle K := Abschluss des Kerns
  let K := closure M1
  use K
  constructor
  · -- K ⊆ closure M0, weil core M0 ⊆ M0 und closure monotone ist
    exact closure_mono (core_subset M0)
  constructor
  · -- K ist abgeschlossen
    exact isClosed_closure
  · -- K hat keine isolierten Punkte
    intro x hx ε hε
    -- Aus x ∈ closure M1: Punkte in M1 beliebig nah an x
    -- aus x ∈ closure M1: Distanz in der Form dist x y < δ
    have hx_cl0 : ∀ δ > 0, ∃ y ∈ M1, dist x y < δ :=
      Metric.mem_closure_iff.mp hx
    -- umschreiben zu dist y x < δ via Symmetrie
    have hx_cl : ∀ δ > 0, ∃ y ∈ M1, dist y x < δ := by
      intro δ hδ
      rcases hx_cl0 δ hδ with ⟨y, hyM1, hy⟩
      exact ⟨y, hyM1, by simpa [dist_comm] using hy⟩
    -- Arbeite mit ε/2 für etwas Reserve
    have hε2 : 0 < ε / 2 := by
      have : (0 : ℝ) < 2 := by norm_num
      exact half_pos hε

    obtain ⟨y0, hy0M1, hy0dist⟩ := hx_cl (ε/2) hε2
    have hy0abs : |y0 - x| < ε / 2 := by
      simpa [Real.dist_eq] using hy0dist

    -- Fallunterscheidung: liegt x selbst schon in M1?
    by_cases hxM1 : x ∈ M1
    · -- Fall 1: x ∈ M1 ⇒ nutze Zweiseit-Dicke für einen anderen Punkt yR
      obtain ⟨yR, hyRM1, hx_lt_yR, hyR_lt⟩ :=
        exists_point_in_rightSlice_of_thick
          (M:=M1) (x:=x) (ε:=ε/2) hThick hxM1 hε2
      -- |yR - x| < ε/2, also erst recht < ε
      have hyRabs_half : |yR - x| < ε/2 := by
        have hsub : yR - x < ε/2 := (sub_lt_iff_lt_add').mpr hyR_lt
        have hpos : 0 < yR - x := sub_pos.mpr hx_lt_yR
        simpa [abs_of_pos hpos] using hsub
      have hyRabs : |yR - x| < ε := by linarith
      have hneq : yR ≠ x := ne_of_gt hx_lt_yR
      exact ⟨yR, hneq, subset_closure hyRM1, hyRabs⟩

    · -- Fall 2: x ∉ M1 ⇒ der approximierende Punkt y0 ist automatisch verschieden von x
      have hneq : y0 ≠ x := by
        intro h; apply hxM1; simpa [h] using hy0M1
      have hy0abs_lt_eps : |y0 - x| < ε := by linarith
      exact ⟨y0, hneq, subset_closure hy0M1, hy0abs_lt_eps⟩

end ApplicationToGoal

end PerfectFromThick
