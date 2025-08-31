/-
Minimal Lean 4 skeleton (stable core, with dyadic reduction):
- keine Cantor- /Node- /limitSet-Teile
- konsistente Nutzung von `Set.diff`
- Slices als Set-Comprehensions (kein `∩` im Kernteil)
-/
import Mathlib
import Mathlib.Topology.Separation

open Classical Set Topology Filter

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


/-! ### Negations-Bild der schlechten rechten Punkte -/

/-- Bild von `BadRight` unter Negation ist `BadLeft` des negierten Sets. -/
lemma image_neg_BadRight (M : Set ℝ) :
  (fun x : ℝ => -x) '' (BadRight M) = BadLeft (negPre M) := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hx with ⟨hxM, ⟨ε, hεpos, hcnt⟩⟩
    have hxNeg : (-x) ∈ negPre M := by simpa [negPre] using hxM
    -- Bild des rechten Slices ist der linke Slice

    -- 1) Vorwärtsrichtung
    have himgSlice :
        ((fun y : ℝ => -y) '' (RightSlice M x ε)).Countable :=
      hcnt.image _
    have : (LeftSlice (negPre M) (-x) ε).Countable :=
      (image_neg_rightSlice (M:=M) (x:=x) (ε:=ε)) ▸ himgSlice
    exact ⟨hxNeg, ⟨ε, hεpos, this⟩⟩

  · intro hz
    rcases hz with ⟨hzNeg, ⟨ε, hεpos, hcnt⟩⟩
    refine ⟨-z, ?_, by simp⟩
    have hxM : -z ∈ M := by simpa [negPre] using hzNeg
    -- 2) Rückrichtung
    have himgSlice :
        ((fun y : ℝ => -y) '' (LeftSlice (negPre M) z ε)).Countable :=
      hcnt.image _
    have : (RightSlice M (-z) ε).Countable := by
      -- erst zu RightSlice (negPre (negPre M)) umschreiben …
      have eq1 := image_neg_leftSlice (M:=negPre M) (x:=z) (ε:=ε)
      -- … und dann negPre ∘ negPre = id
      have eq2 :
          (fun y : ℝ => -y) '' (LeftSlice (negPre M) z ε)
            = RightSlice M (-z) ε := by
        simpa [negPre_negPre] using eq1
      exact eq2 ▸ himgSlice
    exact ⟨hxM, ⟨ε, hεpos, this⟩⟩



/-! ### Linker/ Rechter Fix-Fall – Brücke per Negation -/

open Classical

/-- Linker Fix-Set für (M,k,q). -/
def SLeftFix (M : Set ℝ) (k : ℕ) (q : ℚ) : Set ℝ :=
  {x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                 (LeftSlice M x (dyadic k)).Countable}

/-- Rechter Fix-Set für (M,k,q). -/
def SRightFix (M : Set ℝ) (k : ℕ) (q : ℚ) : Set ℝ :=
  {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}

/-- Negationsbild des linken Fix-Sets ist das rechte Fix-Set des negierten Sets. -/
lemma image_neg_SLeftFix (M : Set ℝ) (k : ℕ) (q : ℚ) :
  (fun x : ℝ => -x) '' (SLeftFix M k q)
    = SRightFix (negPre M) k (-q) := by
  ext z; constructor
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hx with ⟨hxM, hxsub, hqx, hcnt⟩
    have hzNegPre : (-x) ∈ negPre M := by simpa [negPre] using hxM
    -- aus q < x ⇒ -x < -q
    have h2 : ((fun t : ℝ => -t) x) < ((-q : ℚ) : ℝ) := by
      simpa using (neg_lt_neg hqx)
    -- aus (x - δ) < q ⇒ -q < -x + δ
    have h1 : ((-q : ℚ) : ℝ) < ((fun t : ℝ => -t) x) + dyadic k := by
      have := neg_lt_neg hxsub
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add, neg_neg] using this
    -- Bild des linken Slices = rechter Slice des negierten Sets
    have himgSlice :
      ((fun y : ℝ => -y) '' (LeftSlice M x (dyadic k))).Countable := hcnt.image _
    have hRightSlice :
      (RightSlice (negPre M) (-x) (dyadic k)).Countable :=
      (image_neg_leftSlice (M:=M) (x:=x) (ε:=dyadic k)) ▸ himgSlice
    exact ⟨hzNegPre, h2, h1, hRightSlice⟩
  · intro hz
    rcases hz with ⟨hzNegPre, hxltq', hqlt', hcnt'⟩
    refine ⟨-z, ?_, by simp⟩
    have hxM : -z ∈ M := by simpa [negPre] using hzNegPre
    -- aus z < -q ⇒ q < -z
    have hqx : (q : ℝ) < (-z : ℝ) := by
      have := neg_lt_neg hxltq'
      simpa using this
    -- aus (-q) < z + δ ⇒ (-z) - δ < q
    have hxsub : ((-z : ℝ) - dyadic k) < (q : ℝ) := by
      have := neg_lt_neg hqlt'
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add, neg_neg] using this
    -- Bild des rechten Slices = linker Slice (doppelte Negation)
    have himgSlice :
      ((fun y : ℝ => -y) '' (RightSlice (negPre M) z (dyadic k))).Countable :=
      hcnt'.image _
    have hLeftSlice :
      (LeftSlice M (-z) (dyadic k)).Countable := by
      have eq1 := image_neg_rightSlice (M := negPre M) (x := z) (ε := dyadic k)
      have eq2 :
        (fun y : ℝ => -y) '' (RightSlice (negPre M) z (dyadic k))
          = LeftSlice M (-z) (dyadic k) := by
        simpa [negPre_negPre] using eq1
      exact eq2 ▸ himgSlice
    exact ⟨hxM, hxsub, hqx, hLeftSlice⟩

open Topology

/-- Punkte von `M`, an denen es **irgendeine** Umgebung gibt,
in der `M` nur zählbar viele Punkte hat, bilden *in `M`* eine zählbare Menge.
(In ℝ folgt das aus der Cantor–Bendixson-Zerlegung von Teilmengen von ℝ.) -/
lemma countable_nonCondensation_in_M (M : Set ℝ) :
  (M \ condensationPoints M).Countable := by
  -- Mathlib: In polnischen Räumen ist `M \ condensationPoints M` zählbar.
  -- (ℝ ist polnisch; das Lemma befindet sich in `Topology/Separation.lean`.)
  simpa [Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
    using condensationPoints_countable_compl (s := M)

/-- Rechtsseitig "dünn" (es gibt `ε>0` mit zählbarem Schnitt rechts)
impliziert: Es gibt *eine* Nachbarschaft mit zählbarem Schnitt; also
kein Kondensationspunkt. -/
lemma rightThin_in_M_is_nonCondensation (M : Set ℝ) :
  {x : ℝ | x ∈ M ∧ ∃ ε > 0, (M ∩ Set.Ioc x (x + ε)).Countable}
    ⊆ (M \ condensationPoints M) := by
  intro x hx
  rcases hx with ⟨hxM, ε, hεpos, hCntIoc⟩
  -- Nimm eine *offene* Umgebung `U := (x-ε, x+ε)` um `x`.
  let U : Set ℝ := Set.Ioo (x - ε) (x + ε)
  have hU_mem : U ∈ 𝓝 x := by
    have : (0 : ℝ) < ε := hεpos
    -- Standard: jedes `(x-ε, x+ε)` ist eine Umgebung von `x`
    have hxlt : x - ε < x := by linarith
    have hxlt' : x < x + ε := by linarith
    simpa [U, sub_eq_add_neg] using Ioo_mem_nhds hxlt hxlt'
  -- Rechtsintervall `Ioc x (x+ε)` liegt in `U`.
  have hIncl : Set.Ioc x (x + ε) ⊆ U := by
    intro y hy
    rcases hy with ⟨hyx, hy_le⟩
    exact ⟨by linarith, by linarith⟩
  -- Damit ist auch `M ∩ U` zählbar (Monotonie).
  have hCntU : (M ∩ U).Countable := hCntIoc.mono (by
    intro y hy; rcases hy with ⟨hyM, hyI⟩; exact ⟨hyM, hIncl hyI⟩)
  -- Folgt: `x` ist in `M` und hat eine Umgebung mit zählbarem Schnitt ⇒ nicht-Kondensationspunkt.
  exact ⟨hxM, by
    -- Def. Nicht-Kondensationspunkt: ∃ U ∈ 𝓝 x, (M ∩ U).Countable
    change x ∈ {x | ∃ U ∈ 𝓝 x, (M ∩ U).Countable}ᶜᶜ
    have : x ∈ {x | ∃ U ∈ 𝓝 x, (M ∩ U).Countable} := ⟨U, hU_mem, hCntU⟩
    simpa using this⟩

/-- **Rechts**: Fixmenge ist abzählbar. -/
lemma countable_BadRight_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                 (RightSlice M x (dyadic k)).Countable}).Countable := by
  classical
  -- Schreibe das Fix-Set als Teilmenge der "rechts dünnen Punkte" in M.
  have hSub :
    {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                  (RightSlice M x (dyadic k)).Countable}
      ⊆ {x : ℝ | x ∈ M ∧ ∃ ε > 0, (M ∩ Set.Ioc x (x + ε)).Countable} := by
    intro x hx; rcases hx with ⟨hxM, hxltq, hqlt, hCntSlice⟩
    have hεpos : 0 < dyadic k := dyadic_pos k
    -- `RightSlice M x ε` ist genau `M ∩ (x, x+ε]`.
    have hEq :
        RightSlice M x (dyadic k) = (M ∩ Set.Ioc x (x + dyadic k)) := by
      ext y; constructor <;> intro hy
      · rcases hy with ⟨hyM, hxlt, hylt⟩
        exact ⟨hyM, ⟨by simpa using hxlt, (le_of_lt hylt)⟩⟩
      · rcases hy with ⟨hyM, ⟨hxlt, hyle⟩⟩
        -- aus `y ≤ x+ε` und `ε>0` folgt `y < x+ε` oder `y = x+ε`;
        -- beides reicht für den Slice, weil wir `y < x+ε` wollen.
        have : y < x + dyadic k ∨ y = x + dyadic k := lt_or_eq_of_le hyle
        have hylt : y < x + dyadic k := by
          cases this with
          | inl hlt => exact hlt
          | inr heq => simpa [heq, hεpos] using (lt_of_le_of_lt (le_of_eq heq) (by
              have : 0 < dyadic k := hεpos; linarith))
        exact ⟨hyM, by simpa using hxlt, hylt⟩
    -- Monotonie der Zählbarkeit (Bild via Gleichheit)
    have : (M ∩ Set.Ioc x (x + dyadic k)).Countable := by
      simpa [hEq] using hCntSlice
    exact ⟨hxM, ⟨dyadic k, hεpos, this⟩⟩
  -- Diese "rechts dünnen" Punkte in `M` sind zählbar (Nicht-Kondensationspunkte in `M`).
  have hThinCnt :
    ({x : ℝ | x ∈ M ∧ ∃ ε > 0, (M ∩ Set.Ioc x (x + ε)).Countable}).Countable := by
    -- Teilmenge von `M \ condensationPoints M`
    exact (countable_nonCondensation_in_M M).mono (by
      intro x hx; exact rightThin_in_M_is_nonCondensation (M:=M) hx)
  -- Also ist auch unser Fix-Set zählbar.
  exact hThinCnt.mono hSub


/-- **Links via Negations-Brücke**: Fixmenge ist abzählbar. -/
lemma countable_BadLeft_fixed_via_neg (M : Set ℝ) (k : ℕ) (q : ℚ) :
  (SLeftFix M k q).Countable := by
  classical
  -- Bild unter Negation ist die rechte Fix-Menge des negierten Sets
  have himg : (fun x : ℝ => -x) '' (SLeftFix M k q)
                = SRightFix (negPre M) k (-q) :=
    image_neg_SLeftFix (M:=M) (k:=k) (q:=q)
  -- Rechts-Fix ist abzählbar (benutze das vorige Lemma)
  have hRightCnt :
    (SRightFix (negPre M) k (-q)).Countable := by
    simpa [SRightFix] using
      (countable_BadRight_fixed (M := negPre M) (k := k) (q := -q))
  -- also ist auch das Bild abzählbar
  have himgCnt : ((fun x : ℝ => -x) '' (SLeftFix M k q)).Countable := by
    simpa [himg] using hRightCnt
  -- Abbilden unter Negation liefert wieder die Ursprungsmenge
  have : (SLeftFix M k q).Countable := by
    have := himgCnt.image (fun x : ℝ => -x)
    simpa [Set.image_image, Function.comp, neg_neg, Set.image_id] using this
  exact this

/-- **Links (Wrapper)**: Fixmenge ist abzählbar. -/
lemma countable_BadLeft_fixed (M : Set ℝ) (k : ℕ) (q : ℚ) :
  ({x : ℝ | x ∈ M ∧ (x - dyadic k : ℝ) < q ∧ (q : ℝ) < x ∧
                 (LeftSlice M x (dyadic k)).Countable}).Countable := by
  -- Das ist genau SLeftFix:
  have : (SLeftFix M k q).Countable :=
    countable_BadLeft_fixed_via_neg (M:=M) (k:=k) (q:=q)
  simpa [SLeftFix]

/-! ### Globale Zählbarkeit von BadLeft / BadRight / Bad -/

/-- **Links**: `BadLeft M` ist abzählbar (Subunion + Fixfall). -/
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

/-- **Rechts**: `BadRight M` ist abzählbar (per iUnion + Rechts-Fix). -/
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
  have hmono : (RightSlice M x (dyadic k)) ⊆ (RightSlice M x ε) :=
    RightSlice_mono_radius (M:=M) (x:=x) (ε₁:=dyadic k) (ε₂:=ε) hk
  have hcnt_dy : (RightSlice M x (dyadic k)).Countable := hcnt.mono hmono
  refine mem_iUnion.mpr ?_
  refine ⟨k, ?_⟩
  refine mem_iUnion.mpr ?_
  refine ⟨q, ?_⟩
  change x ∈ {x : ℝ | x ∈ M ∧ (x : ℝ) < q ∧ (q : ℝ) < x + dyadic k ∧
                        (RightSlice M x (dyadic k)).Countable}
  exact And.intro hxM (And.intro hq1 (And.intro hq2 hcnt_dy))

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

/-- **Erste Auswahlstufe (1./3.-Regel)**: … -/
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
  obtain ⟨x10, hx10M, hx0lt, hx10lt⟩ :=
    exists_point_in_rightSlice_of_thick (M:=M) (x:=x0) (ε:=(x1 - x0)/3)
      hThick hx0 hε
  obtain ⟨x11, hx11M, hx1low, hx11ltx1⟩ :=
    exists_point_in_leftSlice_of_thick (M:=M) (x:=x1) (ε:=(x1 - x0)/3)
      hThick hx1 hε
  exact ⟨x10, x11, hx10M, hx11M, hx0lt, hx10lt, hx1low, hx11ltx1⟩

/-! ### Mini-Schritt usw. (unverändert zur vorherigen Version) -/

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

def PairOk (M : Set ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 < p.2

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
  · exact ⟨hx0, hx10M, hx0lt⟩
  · exact ⟨hx11M, hx1, hx11ltx1⟩

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
  · intro _h
    refine ⟨[], ?_, ?_⟩
    · intro p hp; cases hp
    · simp
  · intro p L ih hAll
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
    · intro q hq
      have hq' : q = (x0, x10) ∨ q = (x11, x1) ∨ q ∈ L' := by
        simpa [Lnew] using hq
      rcases hq' with hq0 | hq'
      · cases hq0; exact hPairLeft
      · rcases hq' with hq1 | hqL
        · cases hq1; exact hPairRight
        · exact hL'OK q hqL
    · simp [Lnew, hlen, List.length, two_mul,
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
  let M1 := core M0
  have hThick : TwoSidedThick M1 := TwoSidedThick_core M0
  let K := closure M1
  use K
  constructor
  · exact closure_mono (core_subset M0)
  constructor
  · exact isClosed_closure
  · intro x hx ε hε
    have hx_cl0 : ∀ δ > 0, ∃ y ∈ M1, dist x y < δ :=
      Metric.mem_closure_iff.mp hx
    have hx_cl : ∀ δ > 0, ∃ y ∈ M1, dist y x < δ := by
      intro δ hδ
      rcases hx_cl0 δ hδ with ⟨y, hyM1, hy⟩
      exact ⟨y, hyM1, by simpa [dist_comm] using hy⟩
    have hε2 : 0 < ε / 2 := by
      have : (0 : ℝ) < 2 := by norm_num
      exact half_pos hε
    obtain ⟨y0, hy0M1, hy0dist⟩ := hx_cl (ε/2) hε2
    have hy0abs : |y0 - x| < ε / 2 := by
      simpa [Real.dist_eq] using hy0dist
    by_cases hxM1 : x ∈ M1
    · obtain ⟨yR, hyRM1, hx_lt_yR, hyR_lt⟩ :=
        exists_point_in_rightSlice_of_thick
          (M:=M1) (x:=x) (ε:=ε/2) hThick hxM1 hε2
      have hyRabs_half : |yR - x| < ε/2 := by
        have hsub : yR - x < ε/2 := (sub_lt_iff_lt_add').mpr hyR_lt
        have hpos : 0 < yR - x := sub_pos.mpr hx_lt_yR
        simpa [abs_of_pos hpos] using hsub
      have hyRabs : |yR - x| < ε := by linarith
      have hneq : yR ≠ x := ne_of_gt hx_lt_yR
      exact ⟨yR, hneq, subset_closure hyRM1, hyRabs⟩
    · have hneq : y0 ≠ x := by
        intro h; apply hxM1; simpa [h] using hy0M1
      have hy0abs_lt_eps : |y0 - x| < ε := by linarith
      exact ⟨y0, hneq, subset_closure hy0M1, hy0abs_lt_eps⟩

/-- Wenn `A` überabzählbar ist und `A ⊆ B`, dann ist auch `B` überabzählbar. -/
lemma not_countable_of_subset_of_not_countable {α} {A B : Set α}
    (hA : ¬ A.Countable) (hAB : A ⊆ B) : ¬ B.Countable := by
  intro hB
  exact hA (hB.mono hAB)

/-- Perfekte **und überabzählbare** Teilmenge im Abschluss. -/
lemma exists_perfect_uncountable_subset
  {M0 : Set ℝ} (_hM0 : ¬ M0.Countable) :
  ∃ K : Set ℝ, K ⊆ closure M0 ∧ Perfect K ∧ ¬ K.Countable := by
  classical
  let M1 := core M0
  have hThick : TwoSidedThick M1 := TwoSidedThick_core M0
  have hM1 : ¬ M1.Countable := uncountable_core_of_uncountable (M := M0) _hM0
  let K := closure M1
  refine ⟨K, ?subset, ?perfect, ?uncountableK⟩
  · exact closure_mono (core_subset M0)
  · constructor
    · exact isClosed_closure
    · intro x hx ε hε
      have hx_cl0 : ∀ δ > 0, ∃ y ∈ M1, dist x y < δ :=
        Metric.mem_closure_iff.mp hx
      have hx_cl : ∀ δ > 0, ∃ y ∈ M1, dist y x < δ := by
        intro δ hδ
        rcases hx_cl0 δ hδ with ⟨y, hyM1, hy⟩
        exact ⟨y, hyM1, by simpa [dist_comm] using hy⟩
      have hε2 : 0 < ε / 2 := by
        have : (0 : ℝ) < 2 := by norm_num
        exact half_pos hε
      rcases hx_cl (ε/2) hε2 with ⟨y0, hy0M1, hy0dist⟩
      have hy0abs : |y0 - x| < ε / 2 := by
        simpa [Real.dist_eq] using hy0dist
      by_cases hxM1 : x ∈ M1
      · obtain ⟨yR, hyRM1, hx_lt_yR, hyR_lt⟩ :=
          exists_point_in_rightSlice_of_thick
            (M:=M1) (x:=x) (ε:=ε/2) hThick hxM1 hε2
        have hyRabs_half : |yR - x| < ε/2 := by
          have hsub : yR - x < ε/2 := (sub_lt_iff_lt_add').mpr hyR_lt
          have hpos : 0 < yR - x := sub_pos.mpr hx_lt_yR
          simpa [abs_of_pos hpos] using hsub
        have hyRabs : |yR - x| < ε := by linarith
        have hneq : yR ≠ x := ne_of_gt hx_lt_yR
        exact ⟨yR, hneq, subset_closure hyRM1, hyRabs⟩
      · have hneq : y0 ≠ x := by
          intro h; apply hxM1; simpa [h] using hy0M1
        have hy0abs_lt_eps : |y0 - x| < ε := by linarith
        exact ⟨y0, hneq, subset_closure hy0M1, hy0abs_lt_eps⟩
  · have hsubset : M1 ⊆ K := subset_closure
    exact not_countable_of_subset_of_not_countable hM1 hsubset

/-- Kurzer Alias. -/
lemma exists_perfect_and_uncountable_in_closure
  {M0 : Set ℝ} (hM0 : ¬ M0.Countable) :
  ∃ K : Set ℝ, K ⊆ closure M0 ∧ Perfect K ∧ ¬ K.Countable :=
  exists_perfect_uncountable_subset (M0 := M0) hM0

end ApplicationToGoal


/-! ### Kleine Enumerations- und Auswahl-Helfer für zählbare Teilmengen von ℝ -/
section CountableHelpers
  open Classical

  /-- Eine *feste* Aufzählung der rationalen Zahlen. -/
  noncomputable def enumQ : ℕ → ℚ :=
    Classical.choose (exists_surjective_nat ℚ)

  lemma enumQ_surj : Function.Surjective enumQ :=
    Classical.choose_spec (exists_surjective_nat ℚ)

  /-- Feste Aufzählung der **rationalen Zahlen in einem offenen Intervall** `(a,b)`:
      Wir nehmen `enumQ` und filtern. -/
  noncomputable def enumQin (a b : ℝ) : ℕ → ℚ :=
    fun n =>
      let q := enumQ n
      if (a : ℝ) < q ∧ (q : ℝ) < b then q else (0 : ℚ)

  lemma enumQin_mem {a b : ℝ} {n : ℕ}
    (h : (a : ℝ) < enumQin a b n ∧ (enumQin a b n : ℝ) < b) :
    (enumQin a b n : ℝ) ∈ Set.Ioo a b := by
    exact ⟨h.1, h.2⟩

  /-- Dichte von `ℚ`: Für `a < b` gibt es einen Index `n` mit
      `a < enumQin a b n < b`. -/
  lemma exists_index_enumQin_between {a b : ℝ} (h : a < b) :
    ∃ n, (a : ℝ) < enumQin a b n ∧ (enumQin a b n : ℝ) < b := by
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn h
    rcases enumQ_surj q with ⟨n, rfl⟩
    refine ⟨n, ?_, ?_⟩
    all_goals
      simp [enumQin, hqa, hqb]

  /-- Aus einer zählbaren *und nichtleeren* Menge `S` extrahieren wir eine surjektive
      Aufzählung `e : ℕ → S`. -/
  noncomputable def someEnum {α} {S : Set α} (hS : S.Countable) (hne : S.Nonempty) :
    { e : ℕ → S // Function.Surjective e } := by
    classical
    haveI : Countable S := hS.to_subtype
    haveI : Nonempty S := by
      rcases hne with ⟨x, hx⟩
      exact ⟨⟨x, hx⟩⟩
    -- statt `rcases exists_surjective_nat S with ⟨e, he⟩`
    let e : ℕ → S := Classical.choose (exists_surjective_nat S)
    have he : Function.Surjective e :=
      Classical.choose_spec (exists_surjective_nat S)
    exact ⟨e, he⟩


  /-- Wenn `S` zählbar ist und es irgendein Element `> t` gibt, dann gibt es
      den *kleinsten Index* in einer festen Aufzählung von `S`, dessen Bild `> t` liegt. -/
  lemma exists_min_index_above
    {S : Set ℝ} (hS : S.Countable) {t : ℝ}
    (hex : ∃ y ∈ S, t < y) :
    ∃ n, (t < (someEnum hS (by rcases hex with ⟨y, hyS, _⟩; exact ⟨y, hyS⟩)).1 n) ∧
          ∀ m, m < n → ¬ (t < (someEnum hS (by rcases hex with ⟨y, hyS, _⟩; exact ⟨y, hyS⟩)).1 m) := by
    classical
    -- Nicht-Leere von `S` aus `hex`
    have hne : S.Nonempty := by
      rcases hex with ⟨y, hyS, _⟩
      exact ⟨y, hyS⟩
    let e := (someEnum hS hne).1
    have esurj : Function.Surjective e := (someEnum hS hne).2
    -- Es gibt einen Treffer
    have hex' : ∃ n, t < e n := by
      rcases hex with ⟨y, hyS, hty⟩
      rcases esurj ⟨y, hyS⟩ with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      -- bringe hn auf Ebene der Werte (ℝ):
      have hnval : ((e n : S) : ℝ) = y := by
        simpa using congrArg (fun s : S => (s : ℝ)) hn
      -- jetzt einfach umschreiben
      simpa [hnval] using hty
    -- Menge der Indizes mit Treffer
    let I : Set ℕ := {n | t < e n}
    have hI : ∃ n, n ∈ I := hex'
    -- kleinstes Element per `Nat.find`
    let n := Nat.find hI
    have hnI : n ∈ I := Nat.find_spec hI
    refine ⟨n, hnI, ?_⟩
    intro m hm
    -- Minimalität von `n`: aus `m ∈ I` folgt `n ≤ m`
    have hmin : ∀ k, k ∈ I → n ≤ k := by
      intro k hk; exact Nat.find_min' hI hk
    exact fun hmI => (not_lt_of_ge (hmin m hmI)) hm

  /-- Eine *erste* Position in einer festen Aufzählung von `S`, deren Bild *oberhalb* `t` liegt. -/
  noncomputable def firstIdxAbove
    {S : Set ℝ} (hS : S.Countable) (hne : S.Nonempty) (t : ℝ) : Option ℕ :=
  by
    classical
    let e := (someEnum hS hne).1
    by_cases hex : ∃ n, t < e n
    · exact some (Nat.find hex)
    · exact none

  lemma firstIdxAbove_spec
    {S : Set ℝ} (hS : S.Countable) (hne : S.Nonempty) {t : ℝ} {n : ℕ}
    (h : firstIdxAbove hS hne t = some n) :
    let e := (someEnum hS hne).1
    t < e n ∧ ∀ m, m < n → ¬ t < e m := by
    classical
    set e := (someEnum hS hne).1 with he
    by_cases hex : ∃ k, t < e k
    · -- Definitorische Gleichheit der linken Seite
      have hdef : firstIdxAbove hS hne t = some (Nat.find hex) := by
        simpa [firstIdxAbove, he, hex]
      -- Aus hdef und h folgt Gleichheit der Indizes
      have hsome : some n = some (Nat.find hex) := by
        simpa [h] using hdef
      have hn : n = Nat.find hex := Option.some.inj hsome
      subst hn
      refine ⟨Nat.find_spec hex, ?_⟩
      intro m hm htm
      have : Nat.find hex ≤ m := Nat.find_min' hex htm
      exact (not_lt_of_ge this) hm
    · -- ¬ ∃ k, t < e k  ⇒  ∀ x, e x ≤ t
      have e_le_t : ∀ x, (e x : ℝ) ≤ t := by
        intro x
        have : ¬ t < e x := (not_exists.mp hex) x
        exact le_of_not_gt this
      -- damit entfaltet sich firstIdxAbove zum none-Zweig
      have hnone : firstIdxAbove hS hne t = none := by
        simpa [firstIdxAbove, he, e_le_t]
      -- Widerspruch zu `h : = some n`
      -- Widerspruch zu `h : = some n`
      have : some n = none := h.symm.trans hnone
      cases this

  end CountableHelpers
end PerfectFromThick
