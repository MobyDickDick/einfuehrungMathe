/-
  Kappa.lean — ASCII‑safe, minimal, and free of MeasureTheory.

  What this file provides (all ASCII identifiers, no unicode):
    • iLen     : Real → Real → ENNReal
    • iLenFin  : (Nat → Real) → (Nat → Real) → Finset Nat → ENNReal
    • IooCover : structure for countable open‑interval covers (existential form)
    • coverCost: cost of a cover as iSup of finite partial sums
    • kappaOpen: outer content for open sets via interval covers
    • kappa    : outer content for arbitrary sets via open supersets

  Proven simple lemmas:
    • kappa_le_kappaOpen (monotonicity toward an open superset)
    • kappa_empty = 0

  Notes:
    • Everything is ASCII: Real/Nat/ENNReal, no ℝ/ℕ/→/∞/⋃/∑ symbols.
    • Heavy results (e.g. kappa on [0,1] equals 1) are intentionally omitted here.
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
@[simp] def iLenFin (a b : Nat → Real) (s : Finset Nat) : ENNReal :=
  s.sum (fun i => iLen (a i) (b i))

/-- A countable cover of an open set `U` by open intervals. We store the cover
    in existential form to avoid binder‑inference pitfalls in structure fields. -/
structure IooCover (U : Set Real) where
  aSeq : Nat → Real
  bSeq : Nat → Real
  hcover : ∀ x, x ∈ U → ∃ n : Nat, x ∈ Ioo (aSeq n) (bSeq n)
  hopen  : IsOpen U

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

/-- `κ(M) ≤ κ₀(U)` for any open `U ⊇ M`. -/
lemma kappa_le_kappaOpen {M U : Set Real} (hU : IsOpen U) (hsub : M ⊆ U) :
    kappa M ≤ kappaOpen U := by
  have hmem : U ∈ OpenSupersets M := And.intro hU hsub
  -- `sInf_le` on images
  simpa [kappa] using sInf_le (Exists.intro U (And.intro hmem rfl))

/-- `κ(∅) = 0`. -/
lemma kappa_empty : kappa (∅ : Set Real) = 0 := by
  -- Upper bound: choose `U = ∅`.
  have hU : (∅ : Set Real) ∈ OpenSupersets (∅ : Set Real) := by
    refine And.intro isOpen_empty ?subset
    intro x hx; cases hx
  have h₁ : kappa (∅ : Set Real) ≤ kappaOpen (∅ : Set Real) := by
    simpa [kappa] using sInf_le (Exists.intro (∅ : Set Real) (And.intro hU rfl))
  -- Build a zero‑cost cover of `∅`.
  let C : IooCover (∅ : Set Real) :=
    { aSeq := fun _ => 0
      , bSeq := fun _ => 0
      , hcover := by intro x hx; cases hx
      , hopen  := isOpen_empty }
  have hsum_zero : ∀ s : Finset Nat, iLenFin C.aSeq C.bSeq s = 0 := by
    intro s; simp [iLenFin, C, iLen]
  -- `coverCost C = iSup (fun _ => 0) = 0`
  have hcost : coverCost C = 0 := by
    have hfun : (fun s : Finset Nat => iLenFin C.aSeq C.bSeq s) = (fun _ : Finset Nat => (0 : ENNReal)) := by
      funext s; simpa [hsum_zero]
    -- iSup over a constant 0 is 0
    have hsup : iSup (fun _ : Finset Nat => (0 : ENNReal)) = 0 := by simpa using (iSup_const : iSup (fun _ : Finset Nat => (0 : ENNReal)) = (0 : ENNReal))
    simpa [coverCost, hfun] using hsup
  -- Since the infimum set contains 0, we get `kappaOpen ∅ ≤ 0`; antisymmetry gives equality.
  have : kappaOpen (∅ : Set Real) ≤ 0 := by
    simpa [kappaOpen, hcost] using sInf_le (Exists.intro C (And.intro trivial rfl))
  exact le_antisymm h₁ (by simpa [kappa] : 0 ≤ kappa (∅ : Set Real))

end

end Kappa01
