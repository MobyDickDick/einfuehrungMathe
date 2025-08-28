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
    -- aus h1 : x - ε < y folgern wir -y < -x + ε, aber in zwei Schritte
      -- aus h1 : x - ε < y folgern wir -y < -x + ε, in zwei Schritten
    have hlt : -y < -x + ε := by
      -- (1) ε addieren
      have hxlt : x < y + ε := by
        have := add_lt_add_right h1 ε
        -- (x - ε) + ε = x
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
              add_neg_cancel_right] using this
      -- (2) negieren und wieder ε addieren
      have hneg := neg_lt_neg hxlt                -- -(y+ε) < -x
      have := add_lt_add_right hneg ε             -- -(y+ε)+ε < -x+ε
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
    -- aus z < -x + ε ⇒ x - ε < -z
    have : z < -(x - ε) := by
      -- aus x + z < ε folgt z + x < ε
      have hxz : z + x < ε := by simpa [add_comm] using hlt
      -- und damit z < ε - x
      have hz : z < ε - x := (lt_sub_iff_add_lt).mpr hxz
      -- -(x - ε) = ε - x
      simpa [sub_eq_add_neg, add_comm] using hz
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
      -- rechte Slice-Abzählbarkeit nach links „spiegeln“ (nur auf Slice-Ebene):
      have hLeft :
          (LeftSlice (negPre M) (-x) (dyadic k)).Countable := by
        simpa [image_neg_rightSlice] using
          (hcnt.image (fun y : ℝ => -y))
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
        simpa [image_neg_leftSlice] using
          (hcnt.image (fun y : ℝ => -y))
      exact ⟨hxM, hxltq, by simpa [add_comm] using hqlt, hRight⟩
  -- `SLeftNeg` ist abzählbar durch den linken Kernfall (mit `negPre M` und Marke `-q`)
  have hLeftCnt : SLeftNeg.Countable := by
    simpa [SLeftNeg] using
      (countable_BadLeft_fixed (M:=negPre M) (k:=k) (q:=-q))
  -- daraus folgt Abzählbarkeit von `SRight`:
  -- Erst: Bild von `SRight` ist abzählbar
  have himgCnt : ((fun x : ℝ => -x) '' SRight).Countable := by
    simpa [himg] using hLeftCnt
  -- Zweit: Image noch einmal unter Negation ist wieder `SRight`
  have : SRight.Countable := by
    -- Bild eines abzählbaren Sets unter einer Funktion ist abzählbar
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
