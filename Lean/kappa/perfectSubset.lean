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
  have hmono : (LeftSlice M x (dyadic k)) ⊆ (LeftSlice M x ε) := by
    intro y hy
    rcases hy with ⟨hyM, hylt1, hylt2⟩
    refine ⟨hyM, ?_, hylt2⟩
    have : x - ε ≤ x - dyadic k := sub_le_sub_left hk x
    exact lt_of_le_of_lt this hylt1
  have hcnt_dy : (LeftSlice M x (dyadic k)).Countable := hcnt.mono hmono
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
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


/-! ### Rechte Seite via Negation (Fix-Fall und Subunion separat) -/

-- Vorabbildung von `M` unter der Negation.
def negPre (M : Set ℝ) : Set ℝ := {z : ℝ | -z ∈ M}

lemma negPre_negPre (M : Set ℝ) : negPre (negPre M) = M := by
  ext x; simp [negPre]

/-- Bild des rechten Slices unter `y ↦ -y` ist ein linker Slice des negierten Sets. -/
lemma image_neg_rightSlice (M : Set ℝ) (x ε : ℝ) :
  (fun y : ℝ => -y) '' (RightSlice M x ε) = LeftSlice (negPre M) (-x) ε := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyM, hgt, hlt⟩
    have hzNegPre : (-y) ∈ negPre M := by
      simpa [negPre] using hyM
    -- aus y < x + ε ⇒ (-x) - ε < -y
    have h1 : (-x) - ε < -y := by
      have := neg_lt_neg hlt
      simpa [neg_add, sub_eq_add_neg] using this
    -- aus x < y ⇒ -y < -x
    have h2 : -y < -x := by
      have := neg_lt_neg hgt
      simpa using this
    exact ⟨hzNegPre, h1, h2⟩
  · intro hz
    rcases hz with ⟨hzNegPre, h1, h2⟩
    refine ⟨-z, ?_, by simp⟩
    have hyM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- aus (-x)-ε < z ⇒ -z < x + ε
    have hlt' : -z < x + ε := by
      have := neg_lt_neg h1
      simpa [sub_eq_add_neg, add_comm] using this
    -- aus z < -x ⇒ x < -z
    have hgt : x < -z := by
      have := neg_lt_neg h2
      simpa using this
    exact ⟨hyM, hgt, hlt'⟩

/-- Bild des linken Slices unter `y ↦ -y` ist ein rechter Slice des negierten Sets. -/
lemma image_neg_leftSlice (M : Set ℝ) (x ε : ℝ) :
  (fun y : ℝ => -y) '' (LeftSlice M x ε) = RightSlice (negPre M) (-x) ε := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyM, h1, h2⟩
    have hzNegPre : (-y) ∈ negPre M := by
      simpa [negPre] using hyM
    -- aus x - ε < y ⇒ -y < -x + ε
    have hlt : -y < -x + ε := by
      have : -y < -(x - ε) := by
        have := neg_lt_neg h1
        simpa using this
      simpa [neg_sub] using this
    -- aus y < x ⇒ -x < -y
    have hgt : -x < -y := by
      have := neg_lt_neg h2
      simpa using this
    exact ⟨hzNegPre, hgt, hlt⟩
  · intro hz
    rcases hz with ⟨hzNegPre, hgt, hlt⟩
    refine ⟨-z, ?_, by simp⟩
    have hyM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- aus -x < z ⇒ -z < x
    have h2 : -z < x := by
      have := neg_lt_neg hgt
      simpa using this
    -- aus z < -x + ε ⇒ x - ε < -z
    have h1 : x - ε < -z := by
      have := neg_lt_neg hlt
      simpa [neg_add, sub_eq_add_neg] using this
    exact ⟨hyM, h1, h2⟩

/-- Punktweise Negation von Slices (praktisch, wenn `image` zu `-S` vereinfacht). -/
@[simp] lemma neg_rightSlice_eq (M : Set ℝ) (x ε : ℝ) :
  -(RightSlice M x ε) = LeftSlice (negPre M) (-x) ε := by
  -- -(A) = {z | -z ∈ A}
  ext z; constructor
  · intro hz
    change -z ∈ RightSlice M x ε at hz
    rcases hz with ⟨hzM, hxlt, hlt⟩
    have hzNegPre : z ∈ negPre M := by simpa [negPre] using hzM
    -- x < -z ⇒ z < -x
    have h2 : z < -x := by
      have := neg_lt_neg hxlt
      simpa using this
    -- -z < x + ε ⇒ (-x) - ε < z
    have h1 : (-x) - ε < z := by
      have := neg_lt_neg hlt
      -- - (x + ε) = -x - ε = (-x) - ε
      simpa [neg_add, sub_eq_add_neg] using this
    exact ⟨hzNegPre, h1, h2⟩
  · intro hz
    rcases hz with ⟨hzNegPre, h1, h2⟩
    change -z ∈ RightSlice M x ε
    have hzM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- (-x) - ε < z ⇒ -z < x + ε
    have hlt' : -z < x + ε := by
      have := neg_lt_neg h1
      simpa [sub_eq_add_neg, add_comm] using this
    -- z < -x ⇒ x < -z
    have hgt : x < -z := by
      have := neg_lt_neg h2
      simpa using this
    exact ⟨hzM, hgt, hlt'⟩

@[simp] lemma neg_leftSlice_eq (M : Set ℝ) (z ε : ℝ) :
  -(LeftSlice (negPre M) z ε) = RightSlice M (-z) ε := by
  ext x; constructor
  · intro hx
    change -x ∈ LeftSlice (negPre M) z ε at hx
    rcases hx with ⟨hxNegPre, h1, h2⟩
    have hxM : x ∈ M := by simpa [negPre] using hxNegPre
    -- z - ε < -x ⇒ x < -z + ε
    have hlt : x < -z + ε := by
      have := neg_lt_neg h1
      simpa [neg_sub] using this
    -- -x < z ⇒ -z < x
    have hgt : -z < x := by
      have := neg_lt_neg h2
      simpa using this
    exact ⟨hxM, hgt, hlt⟩
  · intro hx
    rcases hx with ⟨hxM, hgt, hlt⟩
    change -x ∈ LeftSlice (negPre M) z ε
    have hxNegPre : -x ∈ negPre M := by simpa [negPre] using hxM
    -- -z < x ⇒ -x < z
    have h2 : -x < z := by
      have := neg_lt_neg hgt
      simpa using this
    -- x < -z + ε ⇒ z - ε < -x
    have h1 : z - ε < -x := by
      have := neg_lt_neg hlt
      -- -( -z + ε) = z - ε
      simpa [neg_add, sub_eq_add_neg] using this
    exact ⟨hxNegPre, h1, h2⟩

/-- Subunion auf der rechten Seite. -/
lemma BadRight_subunion (M : Set ℝ) :
  BadRight M ⊆ ⋃ (k : ℕ), ⋃ (q : ℚ),
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                   (RightSlice M x (dyadic k)).Countable } := by
  intro x hx
  rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
  rcases exists_dyadic_le (ε:=ε) hεpos with ⟨k, hk⟩
  have : x < x + dyadic k := by
    have hkpos := dyadic_pos k
    have := add_lt_add_left hkpos x
    simpa using this
  rcases exists_rat_btwn this with ⟨q, hq1, hq2⟩
  have hmono : (RightSlice M x (dyadic k)) ⊆ (RightSlice M x ε) := by
    intro y hy
    rcases hy with ⟨hyM, hxlt, hyub⟩
    refine ⟨hyM, hxlt, ?_⟩
    have : x + dyadic k ≤ x + ε := add_le_add_left hk x
    exact lt_of_lt_of_le hyub this
  have hcnt_dy : (RightSlice M x (dyadic k)).Countable := hcnt.mono hmono
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  change x ∈ {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                        (RightSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

/-- Bild der „Left-Fix“-Menge unter Negation ist die entsprechende „Right-Fix“-Menge. -/
lemma image_neg_leftFixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  (fun z : ℝ => -z) ''
      {z : ℝ | z ∈ negPre M ∧ (z - dyadic k : ℝ) < (-q) ∧ (-q : ℝ) < z ∧
                     (LeftSlice (negPre M) z (dyadic k)).Countable}
  =
      {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                     (RightSlice M x (dyadic k)).Countable} := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨z, hz, rfl⟩
    rcases hz with ⟨hzNegPre, h1, h2, hcntL⟩
    have hxM : -z ∈ M := by simpa [negPre] using hzNegPre
    have hxlt : (-z) < q := by
      have := neg_lt_neg h2
      simpa using this
    have hxub : q < (-z) + dyadic k := by
      have := neg_lt_neg h1
      simpa [sub_eq_add_neg, add_comm] using this
    have himgL :
        ((fun y : ℝ => -y) '' (LeftSlice (negPre M) z (dyadic k))).Countable :=
      hcntL.image (fun y : ℝ => -y)
    have hR :
        (RightSlice M (-z) (dyadic k)).Countable := by
      -- falls in deinem Build `image` zu `-S` vereinfacht, helfen beide Simpas:
      simpa [image_neg_leftSlice, neg_leftSlice_eq] using himgL
    exact ⟨hxM, hxlt, hxub, hR⟩
  · intro hx
    rcases hx with ⟨hxM, hxlt, hxub, hcntR⟩
    refine ⟨-x, ?_, by simp⟩
    have hzNegPre : -x ∈ negPre M := by simpa [negPre] using hxM
    have h2 : -q < -x := by
      have := neg_lt_neg hxlt
      simpa using this
    have h1 : (-x) - dyadic k < -q := by
      have := neg_lt_neg hxub
      simpa [neg_add, sub_eq_add_neg] using this
    have himg :
        ((fun y : ℝ => -y) '' (RightSlice M x (dyadic k))).Countable :=
      hcntR.image (fun y : ℝ => -y)
    have hL :
        (LeftSlice (negPre M) (-x) (dyadic k)).Countable := by
      -- dito: Bild → left-slice, egal ob es zu `-S` vereinfacht
      simpa [image_neg_rightSlice, neg_rightSlice_eq] using himg
    exact ⟨hzNegPre, h1, h2, hL⟩

/-- Fix-Fall rechts ist abzählbar (als Negationsbild des linken Fix-Falls). -/
lemma countable_BadRight_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}).Countable := by
  classical
  have hLeft :
      ({z : ℝ | z ∈ negPre M ∧ (z - dyadic k : ℝ) < (-q) ∧ (-q : ℝ) < z ∧
                     (LeftSlice (negPre M) z (dyadic k)).Countable}).Countable := by
    simpa using countable_BadLeft_fixed (M:=negPre M) (k:=k) (q:=-q)
  -- Bild einer abzählbaren Menge ist abzählbar; nutze die Gleichheit der Bilder
  have hImgCnt :
      ((fun z : ℝ => -z) ''
        {z : ℝ | z ∈ negPre M ∧ (z - dyadic k : ℝ) < (-q) ∧ (-q : ℝ) < z ∧
                       (LeftSlice (negPre M) z (dyadic k)).Countable}).Countable :=
    hLeft.image (fun z : ℝ => -z)
  -- Gleichheit des Bildes mit der rechten Fix-Menge
  simpa [image_neg_leftFixed] using hImgCnt

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


/-! ### Mengen-Helfer (ohne `Uncountable.diff`, ohne `ext`) -/

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
