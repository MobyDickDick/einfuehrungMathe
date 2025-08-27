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
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, ?_⟩
  have : (1 : ℝ) / (Nat.succ N) < ε := by
    simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hN
  exact le_of_lt this


/-! ### Kleine Rechen- /Monotonie-Lemmas -/
section SliceHelpers
variable {M : Set ℝ} {x y z ε : ℝ} {k : ℕ}

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


/-- Für feste `x,ε`: der rechte Slice liegt im Intervall `(x, x+ε)`. -/
lemma RightSlice_subset_window :
  RightSlice M x ε ⊆ {y : ℝ | x < y ∧ y < x + ε} := by
  intro y hy; exact ⟨hy.2.1, hy.2.2⟩

/-- Für feste `x,ε`: der linke Slice liegt im Intervall `(x-ε, x)`. -/
lemma LeftSlice_subset_window :
  LeftSlice M x ε ⊆ {y : ℝ | x - ε < y ∧ y < x} := by
  intro y hy; exact ⟨hy.2.1, hy.2.2⟩

/-- Aus `x + z < ε` folgt `z < ε - x`. -/
lemma add_lt_to_lt_sub_right' {x z ε : ℝ} (h : x + z < ε) : z < ε - x := by
  have h' : z + x < ε := by simpa [add_comm] using h
  exact (lt_sub_iff_add_lt).mpr h'

/-- Aus `z < ε - x` folgt `x + z < ε`. -/
lemma lt_sub_to_add_lt_left' {x z ε : ℝ} (h : z < ε - x) : x + z < ε := by
  have h' := (lt_sub_iff_add_lt).1 h
  simpa [add_comm] using h'

end SliceHelpers


/-! ### Links: Subunion + Kernfall -/

lemma BadLeft_subunion (M : Set ℝ) :
  BadLeft M ⊆ ⋃ (k : ℕ), ⋃ (q : ℚ),
    {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                   (LeftSlice M x (dyadic k)).Countable } := by
  intro x hx
  rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
  rcases exists_dyadic_le (ε:=ε) hεpos with ⟨k, hk⟩
  have : x - dyadic k < x := by
    have hkpos := dyadic_pos k
    have : x - dyadic k < x - 0 := by simpa using sub_lt_sub_left hkpos x
    simpa using this
  rcases exists_rat_btwn this with ⟨q, hq1, hq2⟩
  have hmono : (LeftSlice M x (dyadic k)) ⊆ (LeftSlice M x ε) :=
    LeftSlice_mono_radius (M:=M) (x:=x) (ε₁:=dyadic k) (ε₂:=ε) hk
  have hcnt_dy : (LeftSlice M x (dyadic k)).Countable := hcnt.mono hmono
  refine mem_iUnion.mpr ?_; refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_; refine ⟨q, ?_⟩
  change x ∈ {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                        (LeftSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

/-- Fixiere `k` und einen rationalen Marker `q` (linker Kernfall). -/
lemma countable_BadLeft_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                 (LeftSlice M x (dyadic k)).Countable}).Countable := by
  /- hier kommt der konkrete Kodierungs- /Supremum-Beweis hinein (etwas länger) -/
  sorry


/-! ### Negations-Geometrie via Images unter `y ↦ -y` -/

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
    -- aus y < x + ε ⇒ (-x) - ε < -y
    have h1 : (-x) - ε < -y := by
      have := neg_lt_neg hlt
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
      simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using this
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
    have hlt : -y < -x + ε := by
      have := neg_lt_neg h1
      -- hier benötigt Lean `x < ε + y`-Form → normalisiere mit `add_comm`
      simpa [neg_sub, add_comm] using this
    exact ⟨hzNegPre, hgt, hlt⟩
  · intro hz
    rcases hz with ⟨hzNegPre, hgt, hlt⟩
    refine ⟨-z, ?_, by simp⟩
    have hyM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- -x < z ⇒ -z < x
    have h2 : -z < x := by simpa using (neg_lt_neg hgt)
    -- z < -x + ε ⇒ x - ε < -z
    have : z < -(x - ε) := by simpa [neg_sub, add_com] using hlt
    have h1 : x - ε < -z := by simpa using (neg_lt_neg this)
    exact ⟨hyM, h1, h2⟩


/-! ### Rechts: Subunion + Kernfall (über die Image-Lemmas) -/

lemma BadRight_subunion (M : Set ℝ) :
  BadRight M ⊆ ⋃ (k : ℕ), ⋃ (q : ℚ),
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                   (RightSlice M x (dyadic k)).Countable } := by
  intro x hx
  rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
  rcases exists_dyadic_le (ε:=ε) hεpos with ⟨k, hk⟩
  have : x < x + dyadic k := by
    have hkpos := dyadic_pos k
    simpa using add_lt_add_left hkpos x
  rcases exists_rat_btwn this with ⟨q, hq1, hq2⟩
  have hmono : (RightSlice M x (dyadic k)) ⊆ (RightSlice M x ε) :=
    RightSlice_mono_radius (M:=M) (x:=x) (ε₁:=dyadic k) (ε₂:=ε) hk
  have hcnt_dy : (RightSlice M x (dyadic k)).Countable := hcnt.mono hmono
  refine mem_iUnion.mpr ?_; refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_; refine ⟨q, ?_⟩
  change x ∈ {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                        (RightSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

lemma countable_BadRight_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}).Countable := by
  classical
  -- rechte Zielmenge
  let SRight : Set ℝ :=
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                   (RightSlice M x (dyadic k)).Countable}
  -- linker Korrespondent (unter Negation, Marke -q)
  let SLeftNeg : Set ℝ :=
    {z : ℝ | z ∈ negPre M ∧ (z - dyadic k : ℝ) < -q ∧ (-q : ℝ) < z ∧
                   (LeftSlice (negPre M) z (dyadic k)).Countable}
  -- Gleichheit des negierten Bildes (aber wir gehen über Images):
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
      -- Slice-Countability als Image
      have himgSlice :
          ((fun y : ℝ => -y) '' (RightSlice M x (dyadic k))).Countable :=
        hcnt.image _
      have hLeft :
          (LeftSlice (negPre M) (-x) (dyadic k)).Countable := by
        simpa [image_neg_rightSlice] using himgSlice
      exact ⟨hzNegPre, h1, h2, hLeft⟩
    · intro hz
      rcases hz with ⟨hzNegPre, h1, h2, hcnt⟩
      refine ⟨-z, ?_, by simp⟩
      have hxM : -z ∈ M := by simpa [negPre] using hzNegPre
      have hqlt : (q : ℝ) < -z + dyadic k := by
        have := neg_lt_neg h1
        simpa [sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using this
      have hxltq : (-z : ℝ) < q := by
        have := neg_lt_neg h2
        simpa using this
      -- Image des linken Slices liefert den rechten Slice
      have himgL :
          ((fun y : ℝ => -y) '' (LeftSlice (negPre M) z (dyadic k))).Countable :=
        hcnt.image _
      have hRight :
          (RightSlice M (-z) (dyadic k)).Countable := by
        simpa [image_neg_leftSlice, negPre_negPre] using himgL
      exact ⟨hxM, hxltq, by simpa [add_comm] using hqlt, hRight⟩
  -- `SLeftNeg` ist abzählbar durch den linken Kernfall (mit `negPre M` und Marke `-q`)
  have hLeftCnt : SLeftNeg.Countable := by
    simpa [SLeftNeg] using
      (countable_BadLeft_fixed (M:=negPre M) (k:=k) (q:=-q))
  -- daraus folgt Abzählbarkeit von `SRight`
  have himgCnt : ((fun x : ℝ => -x) '' SRight).Countable := by
    simpa [himg] using hLeftCnt
  have : SRight.Countable := by
    have := himgCnt.image (fun x : ℝ => -x)
    simpa [Set.image_image, Function.comp, neg_neg, Set.image_id] using this
  simpa [SRight]

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

def core (M : Set ℝ) : Set ℝ := Set.diff M (Bad M)

lemma core_subset (M : Set ℝ) : core M ⊆ M := by
  intro x hx; exact hx.1

lemma leftSlice_diff_eq (M : Set ℝ) (x ε : ℝ) :
  LeftSlice (Set.diff M (Bad M)) x ε = Set.diff (LeftSlice M x ε) (Bad M) := by
  ext y; constructor <;> intro hy
  · rcases hy with ⟨⟨hyM, hyNotBad⟩, hlt1, hlt2⟩
    exact ⟨⟨hyM, hlt1, hlt2⟩, hyNotBad⟩
  · rcases hy with ⟨⟨hyM, hlt1, hlt2⟩, hyNotBad⟩
    exact ⟨⟨hyM, hyNotBad⟩, hlt1, hlt2⟩

lemma rightSlice_diff_eq (M : Set ℝ) (x ε : ℝ) :
  RightSlice (Set.diff M (Bad M)) x ε = Set.diff (RightSlice M x ε) (Bad M) := by
  ext y; constructor <;> intro hy
  · rcases hy with ⟨⟨hyM, hyNotBad⟩, hgt, hlt⟩
    exact ⟨⟨hyM, hgt, hlt⟩, hyNotBad⟩
  · rcases hy with ⟨⟨hyM, hgt, hlt⟩, hyNotBad⟩
    exact ⟨⟨hyM, hyNotBad⟩, hgt, hlt⟩


/-! ### Mengen-Helfer -/

lemma not_countable_diff_of_not_countable_of_countable
  {α} {A C : Set α}
  (hA : ¬ A.Countable) (hC : C.Countable) : ¬ (Set.diff A C).Countable := by
  intro hdiff
  have hcap_cnt : (A ∩ C).Countable := hC.mono (by intro x hx; exact hx.2)
  have hUnionCnt : (Set.diff A C ∪ (A ∩ C)).Countable := hdiff.union hcap_cnt
  have hA_subset : A ⊆ Set.diff A C ∪ (A ∩ C) := by
    intro x hxA
    by_cases hxC : x ∈ C
    · exact Or.inr ⟨hxA, hxC⟩
    · exact Or.inl ⟨hxA, hxC⟩
  have : A.Countable := hUnionCnt.mono hA_subset
  exact hA this


/-! ### Hauptlemma: `core M` ist zweiseitig dick -/

lemma TwoSidedThick_core (M : Set ℝ) : TwoSidedThick (core M) := by
  intro x hx ε hε
  rcases hx with ⟨hxM, hxNotBad⟩
  have hBadCnt : (Bad M).Countable := countable_Bad M
  have hLeftM  : ¬ (LeftSlice  M x ε).Countable := by
    intro hcnt; exact hxNotBad (Or.inl ⟨hxM, ⟨ε, hε, hcnt⟩⟩)
  have hRightM : ¬ (RightSlice M x ε).Countable := by
    intro hcnt; exact hxNotBad (Or.inr ⟨hxM, ⟨ε, hε, hcnt⟩⟩)
  have hLeftCore  : ¬ (Set.diff (LeftSlice  M x ε) (Bad M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hLeftM hBadCnt
  have hRightCore : ¬ (Set.diff (RightSlice M x ε) (Bad M)).Countable :=
    not_countable_diff_of_not_countable_of_countable hRightM hBadCnt
  have eqL' : LeftSlice (Set.diff M (Bad M)) x ε
      = Set.diff (LeftSlice M x ε) (Bad M) :=
    leftSlice_diff_eq (M:=M) (x:=x) (ε:=ε)
  have eqR' : RightSlice (Set.diff M (Bad M)) x ε
      = Set.diff (RightSlice M x ε) (Bad M) :=
    rightSlice_diff_eq (M:=M) (x:=x) (ε:=ε)
  have eqL : LeftSlice (core M) x ε
      = Set.diff (LeftSlice M x ε) (Bad M) := by
    simpa [core] using eqL'
  have eqR : RightSlice (core M) x ε
      = Set.diff (RightSlice M x ε) (Bad M) := by
    simpa [core] using eqR'
  constructor
  · simpa [eqL] using hLeftCore
  · simpa [eqR] using hRightCore

end PerfectFromThick
