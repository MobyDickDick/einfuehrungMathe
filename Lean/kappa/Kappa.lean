/-
  κ on subsets of [0,1], WITHOUT measure theory.
  Clean, minimal, and compiles on a fresh Mathlib setup.

  What you get in this file:
  • `iLen` — length of an open interval as `ℝ≥0∞`.
  • `iLenFin` — finite partial sums over a `Finset`.
  • `iLenSum` — countable sum defined as `⨆` of finite partial sums (no `tsum`).
  • `IooCover`, `coverCost`, `kappaOpen` — outer content for open sets via interval covers.
  • `OpenSupersets`, `kappa` — outer content for arbitrary sets via open supersets.
  • Lemmas: `kappa_le_kappaOpen`, `kappa_empty` (proved). Others left as `sorry`.
-/

import Mathlib

open Set Classical Topology
open scoped BigOperators

namespace Kappa01

noncomputable section

/-- Closed unit interval `[0,1]` as a set. -/
@[simp] def Icc01 : Set ℝ := Icc (0 : ℝ) 1

/-- Length of an open interval `(a,b)` as an extended nonnegative real. -/
@[simp] def iLen (a b : ℝ) : ENNReal := ENNReal.ofReal (b - a)

lemma iLen_of_lt {a b : ℝ} (hab : a < b) :
    iLen a b = ENNReal.ofReal (b - a) := by rfl

/-- Finite partial sum of lengths for indices in a finite set `s`. -/
@[simp] def iLenFin (a b : ℕ → ℝ) (s : Finset ℕ) : ENNReal :=
  s.sum (fun i => iLen (a i) (b i))

/-- Countable sum of lengths as `⨆` over all finite partial sums. -/
@[simp] def iLenSum (a b : ℕ → ℝ) : ENNReal := ⨆ s : Finset ℕ, iLenFin a b s

/-- A countable cover of an open set `U` by open intervals. -/
structure IooCover (U : Set ℝ) where
  a b : ℕ → ℝ
  hcover : U ⊆ ⋃ n, Ioo (a n) (b n)
  hopen : IsOpen U

/-- Cost of a cover: the (countable) sum of interval lengths as `⨆` of finite sums. -/
@[simp] def coverCost {U : Set ℝ} (C : IooCover U) : ℝ≥0∞ := iLenSum C.a C.b

/-- Length (outer content) of an **open** set using interval covers. -/
@[simp] def kappaOpen (U : Set ℝ) : ℝ≥0∞ :=
  sInf ((fun C : IooCover U => coverCost C) '' (Set.univ : Set (IooCover U)))

/-- Admissible open supersets of `M`. -/
@[simp] def OpenSupersets (M : Set ℝ) : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}

/-- κ on arbitrary sets via open supersets. -/
@[simp] def kappa (M : Set ℝ) : ℝ≥0∞ :=
  sInf ((fun U : Set ℝ => kappaOpen U) '' OpenSupersets M)

/-- Generic helper: `κ(M) ≤ κ₀(U)` when `U` is open and `M ⊆ U`. -/
lemma kappa_le_kappaOpen {M U : Set ℝ} (hU : IsOpen U) (hsub : M ⊆ U) :
    kappa M ≤ kappaOpen U := by
  have : U ∈ OpenSupersets M := ⟨hU, hsub⟩
  simpa [kappa] using sInf_le ⟨U, this, rfl⟩

/-- Basic: `κ(∅) = 0`. -/
lemma kappa_empty : kappa (∅ : Set ℝ) = 0 := by
  -- Upper bound: take `U = ∅`.
  have hU : (∅ : Set ℝ) ∈ OpenSupersets (∅ : Set ℝ) := ⟨isOpen_empty, by intro x hx; cases hx⟩
  have h₁ : kappa (∅ : Set ℝ) ≤ kappaOpen (∅ : Set ℝ) := by
    simpa [kappa] using sInf_le ⟨(∅ : Set ℝ), hU, rfl⟩
  -- Show `kappaOpen ∅ = 0` using a zero-cost cover (all intervals degenerate).
  have hzero : kappaOpen (∅ : Set ℝ) = 0 := by
    let C : IooCover (∅ : Set ℝ) :=
      { a := fun _ => 0, b := fun _ => 0
        , hcover := by intro x hx; cases hx
        , hopen := isOpen_empty }
    have hsum_zero : ∀ s : Finset ℕ, iLenFin C.a C.b s = 0 := by
      intro s
      -- rewrite the summand to a constant 0 function, then use `sum_const_zero`
      have : (fun i => iLen (C.a i) (C.b i)) = (fun _ : ℕ => (0 : ℝ≥0∞)) := by
        funext i; simp [C, iLen]
      simpa [iLenFin, this] using (Finset.sum_const_zero : ∀ (s : Finset ℕ), _)
    have hcost : coverCost C = 0 := by
      -- `iSup` over a constant-zero family is zero
      have : (fun s : Finset ℕ => iLenFin C.a C.b s) = (fun _ : Finset ℕ => (0 : ℝ≥0∞)) := by
        funext s; simpa [hsum_zero]
      simpa [coverCost, iLenSum, this]
    -- Infimum over a set containing `0` is ≤ 0; antisymmetry gives equality.
    refine le_antisymm ?h bot_le
    have : kappaOpen (∅ : Set ℝ) ≤ 0 := by
      simpa [kappaOpen, hcost] using sInf_le ⟨C, trivial, rfl⟩
    exact this
  exact le_antisymm h₁ (by simpa [hzero] : 0 ≤ kappa (∅ : Set ℝ))

/-- Upper bound for intervals: `κ((a,b)) ≤ b - a`. -/
lemma kappa_Ioo_le {a b : ℝ} (h0 : 0 < a) (hab : a < b) (h1 : b < 1) :
    kappa (Ioo a b) ≤ ENNReal.ofReal (b - a) := by
  -- Cover `(a,b)` by itself.
  let C : IooCover (Ioo a b) :=
    { a := fun _ => a, b := fun _ => b
      , hcover := by intro x hx; refine mem_iUnion.mpr ?_; exact ⟨0, by simpa⟩
      , hopen := isOpen_Ioo }
  have hkU : kappaOpen (Ioo a b) ≤ coverCost C := sInf_le ⟨C, trivial, rfl⟩
  have hk : kappa (Ioo a b) ≤ kappaOpen (Ioo a b) :=
    kappa_le_kappaOpen (M := Ioo a b) (U := Ioo a b) isOpen_Ioo (by intro x hx; exact hx)
  have : kappa (Ioo a b) ≤ coverCost C := hk.trans hkU
  simpa [coverCost, iLenSum, iLenFin, iLen_of_lt hab] using this

/-- The remaining classical facts are left as `sorry` to keep the file compiling. -/
lemma length_le_sum_of_finite_cover
    {ι : Type} [Fintype ι]
    {x y : ℝ} (hxy : x ≤ y)
    (a b : ι → ℝ) (hcover : Icc x y ⊆ ⋃ i, Ioo (a i) (b i)) :
    (ENNReal.ofReal (y - x)) ≤ ∑ i, iLen (a i) (b i) := by
  sorry

lemma Ioo_le_kappa {a b : ℝ} (hab : a < b) :
    ENNReal.ofReal (b - a) ≤ kappa (Ioo a b) := by
  sorry

lemma kappa_Ioo_eq {a b : ℝ} (h0 : 0 < a) (hab : a < b) (h1 : b < 1) :
    kappa (Ioo a b) = ENNReal.ofReal (b - a) := by
  exact le_antisymm (kappa_Ioo_le h0 hab h1) (Ioo_le_kappa hab)

lemma kappa_Icc01_le_one : kappa Icc01 ≤ (1 : ℝ≥0∞) := by
  sorry

lemma kappa_Icc01_ge_one : (1 : ℝ≥0∞) ≤ kappa Icc01 := by
  sorry

lemma kappa_Icc01 : kappa Icc01 = (1 : ℝ≥0∞) := by
  exact le_antisymm kappa_Icc01_le_one kappa_Icc01_ge_one

lemma kappa_open_disjoint_iUnion
    (a b : ℕ → ℝ)
    (hpairwise : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hinside : ∀ n, 0 < a n ∧ a n < b n ∧ b n < 1) :
    kappa (⋃ n, Ioo (a n) (b n)) = iLenSum a b := by
  sorry

end

end Kappa01
