/-
  Kappa.lean — ASCII-safe baseline without MeasureTheory.
  Clean compile: definitions + two lemmas with full proofs (no `simpa`).

  Provided (ASCII identifiers only):
    • iLen     : Real -> Real -> ENNReal
    • iLenFin  : (Nat -> Real) -> (Nat -> Real) -> Finset Nat -> ENNReal
    • IooCover : existential countable open-interval cover of U : Set Real
    • coverCost: iSup over finite partial sums of iLen
    • kappaOpen: sInf of cover costs over all covers of an open set U
    • OpenSupersets
    • kappa    : sInf of kappaOpen over open supersets of M

  Proved:
    • kappa_le_kappaOpen
    • kappa_empty = 0

  Notes:
    • All ASCII: Real, Nat, ENNReal, ->, Set.
    • No unicode sums/unions in structure field types.
-/

import Mathlib

open Set

namespace Kappa01

noncomputable section

/-- Closed unit interval `[0,1]` as a set. -/
@[simp] def Icc01 : Set Real := Icc (0 : Real) 1

/-- Length of an open interval `(a,b)` as an extended nonnegative real (`ENNReal`). -/
@[simp] def iLen (a b : Real) : ENNReal := ENNReal.ofReal (b - a)

/-- Finite partial sum of lengths for indices in a finite set `s`. -/
@[simp] def iLenFin (a b : Nat -> Real) (s : Finset Nat) : ENNReal :=
  s.sum (fun i => iLen (a i) (b i))

/-- A countable cover of an open set `U` by open intervals. We store the cover
    in existential form to avoid binder-inference pitfalls in structure fields. -/
structure IooCover (U : Set Real) where
  aSeq : Nat -> Real
  bSeq : Nat -> Real
  hcover : ∀ x, x ∈ U -> ∃ n : Nat, x ∈ Ioo (aSeq n) (bSeq n)
  hopen : IsOpen U

/-- Cost of a cover: `iSup` of finite partial sums of interval lengths. -/
@[simp] def coverCost {U : Set Real} (C : IooCover U) : ENNReal :=
  iSup (fun s : Finset Nat => iLenFin C.aSeq C.bSeq s)

/-- Outer content for **open** sets via interval covers. -/
@[simp] def kappaOpen (U : Set Real) : ENNReal :=
  sInf ((fun C : IooCover U => coverCost C) '' (Set.univ : Set (IooCover U)))

/-- Admissible open supersets of `M`. -/
@[simp] def OpenSupersets (M : Set Real) : Set (Set Real) := {U | IsOpen U ∧ M ⊆ U}

/-- κ on arbitrary sets via open supersets. -/
@[simp] def kappa (M : Set Real) : ENNReal :=
  sInf ((fun U : Set Real => kappaOpen U) '' OpenSupersets M)

/-- Helper: a canonical zero-cost cover of the empty set. -/
def emptyCover : IooCover (∅ : Set Real) where
  aSeq := fun _ => (0 : Real)
  bSeq := fun _ => (0 : Real)
  hcover := by intro x hx; cases hx
  hopen := isOpen_empty

/-- `κ(M) ≤ κ₀(U)` for any open `U ⊇ M`. -/
lemma kappa_le_kappaOpen {M U : Set Real} (hU : IsOpen U) (hsub : M ⊆ U) :
    kappa M ≤ kappaOpen U := by
  have hx : kappaOpen U ∈ ((fun V : Set Real => kappaOpen V) '' OpenSupersets M) := by
    exact ⟨U, ⟨hU, hsub⟩, rfl⟩
  dsimp [kappa]
  exact sInf_le hx

/-- `κ(∅) = 0`. -/
lemma kappa_empty : kappa (∅ : Set Real) = 0 := by
  -- 1) κ(∅) ≤ κ₀(∅)
  have hxU :
      kappaOpen (∅ : Set Real)
        ∈ ((fun V : Set Real => kappaOpen V) '' OpenSupersets (∅ : Set Real)) :=
    ⟨(∅ : Set Real), ⟨isOpen_empty, by intro x hx; cases hx⟩, rfl⟩
  have h1 : kappa (∅ : Set Real) ≤ kappaOpen (∅ : Set Real) := by
    dsimp [kappa]
    exact sInf_le hxU

  -- 2) Concrete zero-cost cover C of the empty set
  let C : IooCover (∅ : Set Real) := emptyCover

  -- Every finite partial sum is 0 (induction on the finite set)
  have hsum_zero : ∀ s : Finset Nat, iLenFin C.aSeq C.bSeq s = 0 := by
    intro s; classical
    refine Finset.induction_on s ?base ?step
    · -- base
      simp [iLenFin]
    · -- step
      intro a s ha ih
      simp [iLenFin, C, emptyCover, iLen]

  -- coverCost C ≤ 0  (since every partial sum is 0)
  have hcost_le_zero : coverCost C ≤ 0 := by
    -- unfold and use `iSup_le`
    dsimp [coverCost]
    refine iSup_le ?H
    intro s
    have hz : iLenFin C.aSeq C.bSeq s = 0 := hsum_zero s
    exact le_of_eq hz

  -- therefore coverCost C = 0 (as 0 ≤ coverCost C always holds)
  have hcost_eq_zero : coverCost C = 0 := by
    apply le_antisymm
    · exact hcost_le_zero
    · exact bot_le

  -- 3) κ₀(∅) ≤ 0 via the defining infimum and the chosen cover
  have hxC :
      coverCost C
        ∈ (fun C : IooCover (∅ : Set Real) => coverCost C)
             '' (Set.univ : Set (IooCover (∅ : Set Real))) :=
    ⟨C, trivial, rfl⟩
  have h2' : kappaOpen (∅ : Set Real) ≤ coverCost C := by
    dsimp [kappaOpen]
    exact sInf_le hxC
  have h2 : kappaOpen (∅ : Set Real) ≤ 0 := by
    -- rewrite with hcost_eq_zero and chain the inequalities
    have : coverCost C = 0 := hcost_eq_zero
    have : kappaOpen (∅ : Set Real) ≤ 0 := by
      exact le_trans h2' (le_of_eq hcost_eq_zero)
    exact this

  -- 4) Combine and conclude by antisymmetry
  have hle : kappa (∅ : Set Real) ≤ 0 := le_trans h1 h2
  exact le_antisymm hle bot_le

end

/-- Monotonicity: if A ⊆ B then kappa A ≤ kappa B. -/
lemma kappa_mono {A B : Set Real} (hAB : A ⊆ B) : kappa A ≤ kappa B := by
  classical
  -- Image inclusion: (kappaOpen '' OpenSupersets B) ⊆ (kappaOpen '' OpenSupersets A)
  have himg :
      (fun U : Set Real => kappaOpen U) '' OpenSupersets B
        ⊆ (fun U : Set Real => kappaOpen U) '' OpenSupersets A := by
    intro y hy
    rcases hy with ⟨U, hU, rfl⟩
    rcases hU with ⟨hUopen, hBsubU⟩
    -- since A ⊆ B and B ⊆ U, we get A ⊆ U
    have hAsubU : A ⊆ U := by
      intro x hxA
      exact hBsubU (hAB hxA)
    exact ⟨U, ⟨hUopen, hAsubU⟩, rfl⟩
  -- Now: sInf over a larger set ≤ sInf over a smaller set (antitone).
  -- We show: for all y ∈ (image over B), sInf(image over A) ≤ y
  -- hence sInf(image over A) ≤ sInf(image over B).
  dsimp [kappa]
  refine le_sInf ?H
  intro y hyB
  have hyA : y ∈ (fun U : Set Real => kappaOpen U) '' OpenSupersets A := himg hyB
  exact sInf_le hyA

/-- Subadditivity on open sets: `kappaOpen (U ∪ V) ≤ kappaOpen U + kappaOpen V`.
    (Der technische Beweis – Mischen zweier Intervallcovers und Kostenschranke –
    kommt als separater Inkrement-Schritt.) -/
lemma kappaOpen_union_le {U V : Set Real} (hU : IsOpen U) (hV : IsOpen V) :
  kappaOpen (U ∪ V) ≤ kappaOpen U + kappaOpen V := by
sorry

/-- Subadditivity with chosen open supersets:
    Für beliebige `A ⊆ U` und `B ⊆ V` mit offenen `U,V` gilt:
    `kappa (A ∪ B) ≤ kappaOpen U + kappaOpen V`. -/
lemma kappa_union_le_of_open
    {A B U V : Set Real} (hU : IsOpen U) (hV : IsOpen V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) :
    kappa (A ∪ B) ≤ kappaOpen U + kappaOpen V := by
  -- A ∪ B ⊆ U ∪ V
  have hIncl : A ∪ B ⊆ U ∪ V := by
    intro x hx
    cases hx with
    | inl hxA => exact Or.inl (hAU hxA)
    | inr hxB => exact Or.inr (hBV hxB)
  -- Außenapproximation auf U ∪ V
  have h1 : kappa (A ∪ B) ≤ kappaOpen (U ∪ V) :=
    kappa_le_kappaOpen (M := A ∪ B) (U := U ∪ V) (hU.union hV) hIncl
  -- Offene Subadditivität als Blackbox (Lemma oben)
  have h2 : kappaOpen (U ∪ V) ≤ kappaOpen U + kappaOpen V :=
    kappaOpen_union_le hU hV
  exact le_trans h1 h2


end Kappa01
