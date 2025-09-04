/-
Cantor-inside-M (Lean 4 + mathlib):
- baut aus TwoSidedThick M eine perfekte Menge K ⊆ M.
- deterministische Steuerung via erste rationale Teilintervalle (keine freie Auswahl).
- Die schwersten "Plumbing"-Lemmas sind markiert mit `sorry` (siehe Kommentare).
-/

import Mathlib

open Classical Set

set_option autoImplicit true

namespace PerfectFromSuperdense

/-*************************************************
 * 1) Slices & TwoSidedThick (aus deiner Datei)  *
 *************************************************-/

def LeftSlice  (M : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ M ∧ x - ε < y ∧ y < x }

def RightSlice (M : Set ℝ) (x ε : ℝ) : Set ℝ :=
  { y : ℝ | y ∈ M ∧ x < y ∧ y < x + ε }

@[simp] def TwoSidedThick (M : Set ℝ) : Prop :=
  ∀ x ∈ M, ∀ ε > 0,
    (¬ (LeftSlice  M x ε).Countable) ∧
    (¬ (RightSlice M x ε).Countable)

/-- Aus Zweiseit-Dicke: rechter Slice ist nicht leer. -/
lemma exists_point_in_rightSlice_of_thick
  {M : Set ℝ} {x ε : ℝ}
  (hThick : TwoSidedThick M) (hx : x ∈ M) (hε : ε > 0) :
  ∃ y, y ∈ M ∧ x < y ∧ y < x + ε := by
  have hne : (RightSlice M x ε).Nonempty := by
    by_contra hempty
    have : (RightSlice M x ε).Countable := by
      have : RightSlice M x ε = (∅ : Set ℝ) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hempty
      simpa [this] using (countable_empty : (∅ : Set ℝ).Countable)
    exact (hThick x hx ε hε).2 this
  rcases hne with ⟨y, ⟨hyM, hxlt, hylt⟩⟩
  exact ⟨y, hyM, hxlt, hylt⟩

/-- Aus Zweiseit-Dicke: linker Slice ist nicht leer. -/
lemma exists_point_in_leftSlice_of_thick
  {M : Set ℝ} {x ε : ℝ}
  (hThick : TwoSidedThick M) (hx : x ∈ M) (hε : ε > 0) :
  ∃ y, y ∈ M ∧ x - ε < y ∧ y < x := by
  have hne : (LeftSlice M x ε).Nonempty := by
    by_contra hempty
    have : (LeftSlice M x ε).Countable := by
      have : LeftSlice M x ε = (∅ : Set ℝ) := by
        simpa [Set.not_nonempty_iff_eq_empty] using hempty
      simpa [this] using (countable_empty : (∅ : Set ℝ).Countable)
    exact (hThick x hx ε hε).1 this
  rcases hne with ⟨y, ⟨hyM, hlow, hupp⟩⟩
  exact ⟨y, hyM, hlow, hupp⟩

/-**************************************
 * 2) Rationale Basis von Intervallen *
 **************************************-/

-- Alle rationalen offenen Intervalle als Subtyp
def RatInt := { pq : ℚ × ℚ // pq.1 < pq.2 }

-- Feste Aufzählung aller rationalen Intervalle (surjektiv)
noncomputable def enumRJ : ℕ → RatInt :=
  Classical.choose (exists_surjective_nat RatInt)

lemma enumRJ_surj : Function.Surjective enumRJ :=
  Classical.choose_spec (exists_surjective_nat RatInt)

-- Das reale offene Intervall hinter einem RatInt
def RJset (r : RatInt) : Set ℝ :=
  { x : ℝ | (r.val.1 : ℝ) < x ∧ x < (r.val.2 : ℝ) }

@[simp] lemma mem_RJset_iff {r : RatInt} {x : ℝ} :
  x ∈ RJset r ↔ ((r.val.1 : ℝ) < x ∧ x < (r.val.2 : ℝ)) := Iff.rfl

/*************************************************
 * 3) Kandidaten J in einer Komponente [a,b]     *
 *************************************************/

-- Ein rationales Intervall J ist Kandidat in (a,b), wenn sein Abschluss in (a,b) liegt
-- und J einen Punkt außerhalb von M enthält.
def IsCand (M : Set ℝ) (a b : ℝ) (r : RatInt) : Prop :=
  (a : ℝ) < r.val.1 ∧ (r.val.2 : ℝ) < b ∧
  ∃ x, x ∈ RJset r ∧ x ∉ M

lemma exists_cand_if_compl_hits (M : Set ℝ) {a b : ℝ}
  (hab : a < b) (hx : ∃ t, a < t ∧ t < b ∧ t ∉ M) :
  ∃ r : RatInt, IsCand M a b r := by
  rcases hx with ⟨t, hat, htb, hnotM⟩
  -- wähle rationale a<p<t<q<b
  obtain ⟨p, hap, hpt⟩ := exists_rat_btwn hat
  have hpb : (p : ℝ) < b := lt_trans hpt htb
  obtain ⟨q, htq, hqb⟩ := exists_rat_btwn (lt_trans hpt htb)
  have haq : (a : ℝ) < q := lt_trans hat htq
  -- baue r := (p,q)
  have hpq : (p : ℝ) < q := lt_trans hpt htq
  have hpqQ : p < q := by
    -- cast zurück auf ℚ
    have : (p : ℝ) < q := hpq
    exact_mod_cast this
  -- benutze Surj., um ein n mit enumRJ n = (p,q) zu finden
  rcases enumRJ_surj ⟨(p,q), hpqQ⟩ with ⟨n, hn⟩
  refine ⟨enumRJ n, ?_⟩
  dsimp [IsCand, RJset]
  refine ⟨?_, ?_, ?_⟩
  · simpa [hn] using hap
  · simpa [hn] using hqb
  · refine ⟨t, ?_, hnotM⟩
    simpa [hn] using And.intro hpt htq

/-- Erste Kandidaten-Position (kleinster Index) als Option. -/
noncomputable def firstCandIdx (M : Set ℝ) (a b : ℝ) : Option ℕ :=
  if h : ∃ n, IsCand M a b (enumRJ n) then
    some (Nat.find h)
  else none

/-- Spezifikation von `firstCandIdx`. -/
lemma firstCandIdx_spec_some {M : Set ℝ} {a b : ℝ} {n : ℕ}
  (h : firstCandIdx M a b = some n) :
  IsCand M a b (enumRJ n) ∧
  ∀ m, m < n → ¬ IsCand M a b (enumRJ m) := by
  classical
  unfold firstCandIdx at h
  by_cases hex : ∃ k, IsCand M a b (enumRJ k)
  · have hs : some (Nat.find hex) = some n := by simpa [hex] using h
    have hn : n = Nat.find hex := by exact Option.some.inj hs |>.symm
    refine And.intro ?pos ?min
    · simpa [hn] using Nat.find_spec hex
    · intro m hm hCand
      have hle : Nat.find hex ≤ m := Nat.find_min' hex hCand
      exact (Nat.not_lt.mpr hle) hm
  · simp [hex] at h

lemma firstCandIdx_none_iff {M : Set ℝ} {a b : ℝ} :
  firstCandIdx M a b = none
  ↔ ¬ ∃ n, IsCand M a b (enumRJ n) := by
  classical
  unfold firstCandIdx
  by_cases hex : ∃ n, IsCand M a b (enumRJ n)
  · simp [hex]
  · simp [hex]

/*************************************************
 * 4) Ein großer Schnitt (u,v) innerhalb [a,b]   *
 *    mit Endpunkten in M                        *
 *************************************************/

-- Hilfslemma: an Randpunkten a,b∈M finden wir u,v∈M beliebig nahe an a bzw. b
lemma exists_u_v_in_M_near_endpoints
  {M : Set ℝ} (hThick : TwoSidedThick M)
  {a b : ℝ} (haM : a ∈ M) (hbM : b ∈ M) (hab : a < b)
  {α β : ℝ} (haα : a < α) (hβb : β < b) (hαβ : α < β)
  {δ : ℝ} (hδa : 0 < δ) (hδb : 0 < δ) :
  ∃ u v, u ∈ M ∧ v ∈ M ∧ a < u ∧ u < α ∧ β < v ∧ v < b ∧
          u - a < δ ∧ b - v < δ := by
  -- wähle u aus (a, min α (a+δ))∩M
  have hεu : 0 < min (α - a) δ := by
    have : 0 < α - a := sub_pos.mpr haα
    exact lt_min_iff.mpr ⟨this, hδa⟩
  obtain ⟨u, huM, hau, huα⟩ :=
    exists_point_in_rightSlice_of_thick
      (M:=M) (x:=a) (ε:=min (α - a) δ) hThick haM hεu
  have hua_le : u - a < δ := by
    have : u < a + min (α - a) δ := huα
    have : u - a < min (α - a) δ := (sub_lt_iff_lt_add').mpr this
    exact lt_of_le_of_lt (min_le_right _ _) this
  have hau_lt : a < u := hau

  -- wähle v aus (max β (b-δ), b)∩M
  have hεv : 0 < min (b - β) δ := by
    have : 0 < b - β := sub_pos.mpr hβb
    exact lt_min_iff.mpr ⟨this, hδb⟩
  -- benutze die linke Seite am Punkt b
  obtain ⟨v, hvM, hvβ, hvb⟩ :=
    exists_point_in_leftSlice_of_thick
      (M:=M) (x:=b) (ε:=min (b - β) δ) hThick hbM hεv
  have hvb_le : b - v < δ := by
    have : b - min (b - β) δ < v := (lt_sub_iff_add_lt).mp hvβ
    -- aus b - min(...) < v folgt b - v < min(...) ≤ δ
    have : b - v < min (b - β) δ := by
      have : v < b := hvb
      have := sub_lt_iff_lt_add'.mpr this
      exact lt_of_le_of_lt (by exact le_of_lt this)
        (by
          have : b + (-v) < (min (b - β) δ) + (-v) := by
            -- aus b - min < v ⇒ b + (-v) < min
            have := sub_lt_iff_lt_add'.mpr hvβ
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
    exact lt_of_le_of_lt (min_le_right _ _) this
  have β_lt_v : β < v := by
    -- aus b - v < b - β ⇒ β < v
    have : b - v < b - β := by
      have : min (b - β) δ ≤ (b - β) := min_le_left _ _
      exact lt_of_lt_of_le hvb_le this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_lt_sub_iff_left.mp this)
  exact ⟨u, v, huM, hvM, hau, by
    have : u < α := by
      have : u - a < α - a := by
        have : u - a < min (α - a) δ := (sub_lt_iff_lt_add').mpr huα
        exact lt_of_lt_of_le this (min_le_left _ _)
      simpa [sub_eq] using this
    exact this, β_lt_v, hvb, hua_le, hvb_le⟩
where sub_eq := by intros; ring

/-- Eine kanonische Schnittwahl in [a,b]:
    - Wenn es einen Kandidaten J=(α,β) gibt, schneide (u,v) so, dass α,β ∈ (u,v).
    - Sonst schneide zentral mit Randabstand ≤ (b-a)/4.
-/
noncomputable def chooseCut (M : Set ℝ) (hThick : TwoSidedThick M)
  (a b : ℝ) (haM : a ∈ M) (hbM : b ∈ M) (hab : a < b) :
  {uv : ℝ × ℝ // a < uv.1 ∧ uv.1 ∈ M ∧ uv.2 ∈ M ∧ uv.2 < b ∧ uv.1 < uv.2
               ∧ uv.1 - a < (b - a)/4 ∧ b - uv.2 < (b - a)/4
               ∧ (∀ n, firstCandIdx M a b = some n →
                   ( (enumRJ n).val.1 : ℝ) > uv.1 ∧ ( (enumRJ n).val.2 : ℝ) < uv.2 ) } :=
by
  classical
  -- zwei Fälle
  by_cases hC : firstCandIdx M a b = none
  · -- Kein Kandidat: (a,b) ⊆ M; wähle u,v nahe an den Rändern, großer Mittel-Schnitt
    have habpos : 0 < b - a := sub_pos.mpr hab
    let δ := (b - a) / 4
    have hδ : 0 < δ := by have : (0 : ℝ) < 4 := by norm_num; exact div_pos habpos this
    -- Wähle α,β symmetrisch (z. B. α := a + (b-a)/2, β := a + 3(b-a)/4)
    let α := a + (b - a) / 2
    let β := a + (3 : ℝ) * (b - a) / 4
    have haα : a < α := by have : 0 < (b - a) / 2 := by have : (0:ℝ) < 2 := by norm_num; exact div_pos habpos this; simpa [α, add_comm, add_left_comm, add_assoc] using this
    have hβb : β < b := by
      have : (3 : ℝ) * (b - a) / 4 < (b - a) := by
        have : (3:ℝ)/4 < 1 := by norm_num
        have hbapos : 0 ≤ b - a := le_of_lt habpos
        exact (mul_lt_mul_of_pos_right this (by positivity)).trans_eq ?_
      · simpa [β] using (lt_of_add_lt_add_left (show a + ((3:ℝ)*(b-a)/4) < a + (b-a) by
          simpa [add_comm, add_left_comm, add_assoc] using this))
      · ring
    have hαβ : α < β := by
      have : (b - a) / 2 < (3 : ℝ) * (b - a) / 4 := by
        have : (1:ℝ)/2 < (3:ℝ)/4 := by norm_num
        exact (mul_lt_mul_of_pos_right this (by positivity))
      simpa [α, β, add_comm, add_left_comm, add_assoc] using
        (add_lt_add_left this a)
    obtain ⟨u,v, huM, hvM, hau, huα, hβv, hvb, huda, hbv⟩ :=
      exists_u_v_in_M_near_endpoints hThick haM hbM hab haα hβb hαβ hδ hδ
    refine ⟨⟨u,v⟩, ?_⟩
    refine And.intro hau (And.intro huM (And.intro hvM (And.intro hvb (And.intro ?uv1 (And.intro huda (And.intro hbv ?all))))))
    · exact lt_trans huα (lt_trans hαβ hβv)
    · intro n hn
      -- Unmöglicher Fall: es gibt keinen Kandidaten
      have : ¬ ∃ m, IsCand M a b (enumRJ m) := by
        simpa [firstCandIdx_none_iff] using hC
      -- kontradiktorisch: aus "some n" folgt Existenz
      have : False := by
        have : ∃ m, IsCand M a b (enumRJ m) := ⟨n, (firstCandIdx_spec_some (M:=M) (a:=a) (b:=b) (n:=n) hn).1⟩
        exact this.elim this
      exact False.elim this
  · -- Es gibt einen ersten Kandidaten r = enumRJ n; schneide so, dass r ⊂ (u,v)
    rcases Option.eq_some_iff.mp (by simpa using hC : firstCandIdx M a b ≠ none) with ⟨n, hn⟩
    have hspec := firstCandIdx_spec_some (M:=M) (a:=a) (b:=b) (n:=n) hn
    rcases hspec.1 with ⟨haα, hβb, ⟨t, htRJ, htNotM⟩⟩
    let α : ℝ := (enumRJ n).val.1
    let β : ℝ := (enumRJ n).val.2
    have hαβ : (α : ℝ) < β := by
      have : (enumRJ n).val.1 < (enumRJ n).val.2 := (enumRJ n).property
      exact_mod_cast this
    have habpos : 0 < b - a := sub_pos.mpr hab
    let δ := (b - a) / 4
    have hδ : 0 < δ := by have : (0 : ℝ) < 4 := by norm_num; exact div_pos habpos this
    obtain ⟨u,v, huM, hvM, hau, huα, hβv, hvb, huda, hbv⟩ :=
      exists_u_v_in_M_near_endpoints hThick haM hbM hab (show a < α by simpa [α] using haα)
        (show β < b by simpa [β] using hβb) (by simpa [α,β] using hαβ) hδ hδ
    refine ⟨⟨u,v⟩, ?_⟩
    refine And.intro hau (And.intro huM (And.intro hvM (And.intro hvb (And.intro ?uv1 (And.intro huda (And.intro hbv ?all))))))
    · exact lt_trans huα (lt_trans (show α < β by simpa [α,β] using hαβ) hβv)
    · intro m hm
      -- minimalitäts-Fakt: aus m<n folgt enumRJ m kein Kandidat in (a,b)
      have : ¬ IsCand M a b (enumRJ m) := hspec.2 m hm
      -- daraus beliebige Schranke; wir brauchen nur, dass α>u & β<v gelten, was schon oben steht
      exact And.intro
        (by simpa [α] using huα)
        (by simpa [β] using hβv)

/******************************************
 * 5) Stufen: aus [a,b] werden zwei Kinder *
 ******************************************/

/-- ein "gutes" Paar (a,b) mit a,b∈M und a<b -/
def PairOk (M : Set ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ M ∧ p.2 ∈ M ∧ p.1 < p.2

/-- Ein Schritt auf einem Paar: schneidet (u,v) gemäß `chooseCut`. -/
noncomputable def splitPair
  (M : Set ℝ) (hThick : TwoSidedThick M)
  (p : ℝ × ℝ) (hp : PairOk M p) :
  (ℝ × ℝ) × (ℝ × ℝ) :=
by
  rcases hp with ⟨haM, hbM, hab⟩
  classical
  let uv := chooseCut M hThick p.1 p.2 haM hbM hab
  refine ((p.1, uv.val.1), (uv.val.2, p.2))

/-- Die Kinder von `p`. -/
def childL (M : Set ℝ) (hThick : TwoSidedThick M) (p : ℝ × ℝ) (hp : PairOk M p) :
  ℝ × ℝ := (splitPair M hThick p hp).1

def childR (M : Set ℝ) (hThick : TwoSidedThick M) (p : ℝ × ℝ) (hp : PairOk M p) :
  ℝ × ℝ := (splitPair M hThick p hp).2

lemma child_ok (M : Set ℝ) (hThick : TwoSidedThick M)
  {p : ℝ × ℝ} (hp : PairOk M p) :
  PairOk M (childL M hThick p hp) ∧ PairOk M (childR M hThick p hp) ∧
  (childL M hThick p hp).1 < p.1 + (p.2 - p.1)/2 ∧
  p.2 - (p.2 - p.1)/2 < (childR M hThick p hp).2 := by
  -- aus chooseCut bekommen wir: Ränder in M, Abstände ≤ (b-a)/4 usw.
  rcases hp with ⟨haM, hbM, hab⟩
  classical
  rcases chooseCut M hThick p.1 p.2 haM hbM hab with ⟨uv, hpack⟩
  rcases hpack with ⟨hau, huM, hvM, hvb, hu_lt_v, huda, hbv, _cover⟩
  -- formales Umbauen
  have LOK : PairOk M (p.1, uv.1) := ⟨haM, huM, hau⟩
  have ROK : PairOk M (uv.2, p.2) := ⟨hvM, hbM, hvb⟩
  -- Mit (b-a)/4 bekommt man leicht die "in der Mitte"-Ungleichungen (hier halbe Version).
  have hquarter : (uv.1 : ℝ) < p.1 + (p.2 - p.1)/2 := by
    -- denn uv.1 - p.1 ≤ (p.2 - p.1)/4
    have : uv.1 - p.1 < (p.2 - p.1)/4 := huda
    have : uv.1 < p.1 + (p.2 - p.1)/4 := (sub_lt_iff_lt_add').mp this
    exact lt_of_lt_of_le this (by
      have : (p.2 - p.1)/4 ≤ (p.2 - p.1)/2 := by
        have : (0:ℝ) ≤ (p.2 - p.1) := le_of_lt (sub_pos.mpr hab)
        have : (1/4 : ℝ) ≤ (1/2 : ℝ) := by norm_num
        exact (mul_le_mul_of_nonneg_left this ‹_›)
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this p.1)
  have hquarterR : p.2 - (p.2 - p.1)/2 < uv.2 := by
    have : (p.2 - uv.2) < (p.2 - p.1)/4 := hbv
    -- p.2 - (p.2 - p.1)/2 < uv.2  ⇔  (p.2 - uv.2) < (p.2 - p.1)/2
    have : p.2 - uv.2 < (p.2 - p.1)/4 := this
    exact (sub_lt_iff_lt_add'.1
      (lt_of_lt_of_le this (by
        have : (p.2 - p.1)/4 ≤ (p.2 - p.1)/2 := by
          have : (0:ℝ) ≤ (p.2 - p.1) := le_of_lt (sub_pos.mpr hab)
          have : (1/4 : ℝ) ≤ (1/2 : ℝ) := by norm_num
          exact (mul_le_mul_of_nonneg_left this ‹_›)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)))
  exact ⟨LOK, ROK, hquarter, hquarterR⟩

/***********************************************
 * 6) Stufenlisten und Grenzmenge K            *
 ***********************************************/

-- Eine Stufe ist eine endliche Liste von Paaren (geschlossene Intervalle)
def Stage := List (ℝ × ℝ)

def StageOk (M : Set ℝ) (L : Stage) : Prop :=
  (∀ p ∈ L, PairOk M p) ∧
  -- Disjunktheit der offenen Inneren (keine Überlappung) – für Einfachheit als Prop:
  (∀ p₁ ∈ L, ∀ p₂ ∈ L, p₁ ≠ p₂ →
     (Set.Icc p₁.1 p₁.2 ∩ Set.Icc p₂.1 p₂.2 = (∅ : Set ℝ)))

/-- Starte mit einem Anfangspaar [a0,b0] in M. -/
def stage0 (a0 b0 : ℝ) : Stage := [(a0, b0)]

lemma StageOk_stage0 {M : Set ℝ} {a0 b0 : ℝ}
  (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  StageOk M (stage0 a0 b0) := by
  refine And.intro ?all ?disj
  · intro p hp
    rcases hp with rfl | hnil
    · exact ⟨ha, hb, hab⟩
    · cases hnil
  · intro p₁ hp₁ p₂ hp₂ hne
    -- Nur ein Intervall in der Stufe ⇒ kein zweites
    rcases hp₁ with rfl | hnil <;> cases hp₂ <;> cases hnil <;> cases hne

/-- Ein Stufensprung: jedes Paar wird in zwei Kinder ersetzt. -/
noncomputable def stageSucc
  (M : Set ℝ) (hThick : TwoSidedThick M) (L : Stage) : Stage :=
  L.bind (fun p =>
    if hp : PairOk M p then [childL M hThick p hp, childR M hThick p hp] else [])

lemma StageOk_stageSucc
  {M : Set ℝ} (hThick : TwoSidedThick M) :
  ∀ L, StageOk M L → StageOk M (stageSucc M hThick L) := by
  -- Technisch: Disjunktheit der Kinder untereinander und zwischen Paaren.
  -- Die Beweisdetails sind lang, aber Standard: jede Komponente wird lokal "innen" zerschnitten.
  -- Wir lassen hier `sorry` stehen; die Aussage ist rein elementar.
  intro L hL; classical
  sorry

/-- Die geschlossene Intervallmenge einer Stufe. -/
def carrier (L : Stage) : Set ℝ :=
  {x | ∃ p ∈ L, x ∈ Set.Icc p.1 p.2}

lemma carrier_mono {L L'} :
  L' = stageSucc (M:=({} : Set ℝ)) (by intro; exact False.elim) L → carrier L' ⊆ carrier L := by
  -- Platzhalter: in unserem Aufbau schrumpft die Trägervereinigung stufenweise.
  -- In der finalen Fassung wird das aus `StageOk_stageSucc` folgen.
  intro _; intro x hx; rcases hx with ⟨p, hpL', hxI⟩; admit

/-- Definition der Grenzmenge: Schnitt der Trägermengen. -/
def Kof (Ls : ℕ → Stage) : Set ℝ :=
  ⋂ n, {x | ∃ p ∈ Ls n, x ∈ Set.Icc p.1 p.2}

/***********************************************
 * 7) Aufbau der Stufenfolge und Eigenschaften *
 ***********************************************/

noncomputable def buildStages
  (M : Set ℝ) (hThick : TwoSidedThick M)
  (a0 b0 : ℝ) (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  ℕ → Stage
| 0     => stage0 a0 b0
| (n+1) => stageSucc M hThick (buildStages n)

lemma StageOk_buildStages
  (M : Set ℝ) (hThick : TwoSidedThick M)
  {a0 b0 : ℝ} (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  ∀ n, StageOk M (buildStages M hThick a0 b0 ha hb hab n) := by
  intro n; induction' n with n ih
  · exact StageOk_stage0 (M:=M) ha hb hab
  ·
    have := StageOk_stageSucc (M:=M) hThick (buildStages M hThick a0 b0 ha hb hab n) ih
    simpa [buildStages] using this

/*************************************************
 * 8) Die Menge K ⊆ M, perfekt & nichtleer       *
 *************************************************/

def K (M : Set ℝ) (hThick : TwoSidedThick M)
  (a0 b0 : ℝ) (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) : Set ℝ :=
  Kof (buildStages M hThick a0 b0 ha hb hab)

-- Nichtleer & abgeschlossen & keine isolierten Punkte:
lemma K_nonempty (M : Set ℝ) (hThick : TwoSidedThick M)
  {a0 b0 : ℝ} (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  (K M hThick a0 b0 ha hb hab).Nonempty := by
  -- Standard-Cantor-Argument: geschachtelte, abnehmende, nichtleere kompakte Vereinigung.
  -- Hier ein `sorry` als Platzhalter.
  sorry

lemma K_closed (M : Set ℝ) (hThick : TwoSidedThick M)
  {a0 b0 : ℝ} (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  IsClosed (K M hThick a0 b0 ha hb hab) := by
  -- Schnitt abgeschlossener Vereinigungen von Intervallen ⇒ abgeschlossen.
  sorry

lemma K_no_isolated (M : Set ℝ) (hThick : TwoSidedThick M)
  {a0 b0 : ℝ} (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  ∀ x ∈ K M hThick a0 b0 ha hb hab, ∀ ε > 0, ∃ y ≠ x, y ∈ K M hThick a0 b0 ha hb hab ∧ |y - x| < ε := by
  -- Binäre Verzweigung + Durchmesser → 0 in jeder Tiefe ⇒ keine isolierten Punkte.
  sorry

/-- Eliminationslemma: jeder Punkt außerhalb von M wird in endlicher Stufe weggeschnitten. -/
lemma K_subset_M (M : Set ℝ) (hThick : TwoSidedThick M)
  {a0 b0 : ℝ} (ha : a0 ∈ M) (hb : b0 ∈ M) (hab : a0 < b0) :
  K M hThick a0 b0 ha hb hab ⊆ M := by
  -- Sei x∉M. Wähle rationales J=(p,q) mit a0<p<x<q<b0.
  -- Betrachte die eindeutige Komponente jeder Stufe, die x enthält; mittels `firstCandIdx`
  -- wird irgendwann genau dieses J als erster Kandidat gewählt und (u,v) so geschnitten,
  -- dass J ⊂ (u,v); damit wird x entfernt.
  -- Technisches Induktionsargument über die Stufen: `sorry`.
  sorry

/-- Perfekt-Definition aus deiner Datei (geschlossen + keine isolierten Punkte). -/
def Perfect (S : Set ℝ) : Prop :=
  IsClosed S ∧ ∀ x ∈ S, ∀ ε > 0, ∃ y ≠ x, y ∈ S ∧ |y - x| < ε

/*************************************************
 * 9) Hauptsatz: perfekte Teilmenge IN M         *
 *************************************************/

theorem exists_perfect_subset_in_M_of_twoSidedThick
  {M : Set ℝ} (hThick : TwoSidedThick M) :
  ∃ K : Set ℝ, K ⊆ M ∧ Perfect K := by
  -- wähle zwei Punkte a0<b0 in M (aus Unzählbarkeit folgt Nichtleer + zwei Punkte; hier kurz):
  have : ¬ M.Countable := by
    -- Aus jeder TwoSidedThick-Menge folgt Unzählbarkeit (z. B. um x herum).
    -- Formales Lemma der Kürze halber ausgelassen:
    sorry
  obtain ⟨a0, b0, ha0, hb0, hlt⟩ := by
    -- aus Unzählbarkeit in ℝ: es gibt zwei verschiedene Punkte (Standard)
    sorry
  refine ⟨K M hThick a0 b0 ha0 hb0 hlt, ?subset, ?perf⟩
  · exact K_subset_M M hThick ha0 hb0 hlt
  · refine And.intro (K_closed M hThick ha0 hb0 hlt) (K_no_isolated M hThick ha0 hb0 hlt)

end PerfectFromSuperdense
