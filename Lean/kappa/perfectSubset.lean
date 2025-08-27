/-
Minimal Lean 4 skeleton (stable core, with dyadic reduction):
- genau zwei `sorry` bei
    * `countable_BadLeft_fixed`  (Kernfall links)
    * `countable_BadRight_fixed` (Kernfall rechts)
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


/-! ### Kleine, robuste Rechen- und Ordnungs-Lemmas (links & rechts symmetrisch) -/

section SliceHelpers
variable {M : Set ℝ} {x y q ε : ℝ} {k : ℕ}

-- Fenster-Lemmas (bewusst mit offenen/abgeschlossenen Intervallen formuliert)

lemma x_in_window_left
    (hL : x - dyadic k < q) (hR : q < x) :
    x ∈ Ioo q (q + dyadic k) := by
  -- aus x - dyadic k < q folgt x < q + dyadic k
  have hxlt : x < q + dyadic k := by
    have := add_lt_add_right hL (dyadic k)
    -- x - dyadic k + dyadic k = x
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact ⟨hR, hxlt⟩

lemma x_in_window_right
    (hL : x < q) (hR : q < x + dyadic k) :
    x ∈ Icc (q - dyadic k) q := by
  -- aus q < x + dyadic k folgt q - dyadic k < x
  have hxgt : q - dyadic k < x := by
    -- erst auf `dyadic k + x`, dann Subtraktionslemma
    have : q < dyadic k + x := by simpa [add_comm] using hR
    exact (sub_lt_iff_lt_add').mpr (by simpa [add_comm] using this)
  exact ⟨le_of_lt hxgt, le_of_lt hL⟩

-- Monotonie in ε für LeftSlice/RightSlice

lemma LeftSlice_mono_radius {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    LeftSlice M x ε₁ ⊆ LeftSlice M x ε₂ := by
  intro y hy; rcases hy with ⟨hyM, hlow, hupp⟩
  refine ⟨hyM, ?_, hupp⟩
  -- x - ε₂ ≤ x - ε₁ < y
  have : x - ε₂ ≤ x - ε₁ := sub_le_sub_left h x
  exact lt_of_le_of_lt this hlow

lemma RightSlice_mono_radius {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    RightSlice M x ε₁ ⊆ RightSlice M x ε₂ := by
  intro y hy; rcases hy with ⟨hyM, hlow, hupp⟩
  refine ⟨hyM, hlow, ?_⟩
  -- y < x + ε₁ ≤ x + ε₂
  exact lt_of_lt_of_le hupp (add_le_add_left h x)

-- „Slice liegt im Intervall“

lemma LeftSlice_subset_Ioo :
    LeftSlice M x ε ⊆ {y : ℝ | x - ε < y ∧ y < x} := by
  intro y hy; exact ⟨hy.2.1, hy.2.2⟩

lemma RightSlice_subset_Ioo :
    RightSlice M x ε ⊆ {y : ℝ | x < y ∧ y < x + ε} := by
  intro y hy; exact ⟨hy.2.1, hy.2.2⟩

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
  -- packe in die Doppelsumme über k und q
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  -- zeigt: x erfüllt die Bedingung im Summanden (k,q)
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
  -- große Doppelsumme ist abzählbar
  have big :
      (⋃ (k : ℕ), ⋃ (q : ℚ),
        {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                       (LeftSlice M x (dyadic k)).Countable }).Countable :=
    countable_iUnion (fun k =>
      countable_iUnion (fun q =>
        (countable_BadLeft_fixed (M:=M) k q)))
  -- und `BadLeft` liegt darin (BadLeft_subunion)
  exact big.mono (BadLeft_subunion (M:=M))


/-! ### Rechts: Subunion + Kernfall (komplett unabhängig, ohne Symmetrie) -/

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
  -- packe in die Doppelsumme über k und q
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  -- zeigt: x erfüllt die Bedingung im Summanden (k,q)
  change x ∈ {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                        (RightSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

/-- Fixiere `k` und einen rationalen Marker `q` (rechter Kernfall). -/
lemma countable_BadRight_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}).Countable := by
  /- analog zum linken Kernfall, aber rechts von x:
     * Aus x < q < x + dyadic k folgt ein „Fenster“ für x in Icc(q - dyadic k, q).
     * Wähle kanonisch eine rationale Marke r mit x < r < min q (x + dyadic k),
       und einen minimalen Index n aus einer Aufzählung des rechten Slices.
     * Konstruiere eine Injektion in ℚ × ℕ (bzw. ℚ × ℚ × ℕ), um Abzählbarkeit zu zeigen.
     (Technische Details wie beim linken Kernfall; hier ausgelassen.)
  -/
  sorry

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


/-! ### Hauptlemma: `core M` ist zweiseitig dick -/

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
