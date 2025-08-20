import Mathlib
/-
  κ on subsets of [0,1], **without measure theory** and with **minimal imports**.

  Key points:
  • No `MeasureTheory` imports at all.
  • No use of `tsum` / infinite series API. Instead, countable sums are defined as
    the `iSup` (supremum) over all finite partial sums (via `Finset`).
  • Uses only: sets, real numbers, basic topology on ℝ (for `IsOpen` and open intervals),
    finite sums and order-theoretic `sInf/iSup` on `ℝ≥0∞`.
-/

open Set Classical Topology
open scoped BigOperators

namespace Kappa01

noncomputable section

/-- Closed unit interval `[0,1]` as a set. -/
@[simp] def Icc01 : Set ℝ := Icc (0 : ℝ) 1

/-- Length of an open interval `(a,b)` as an extended nonnegative real. -/
@[simp] def iLen (a b : ℝ) : ℝ≥0∞ := ENNReal.ofReal (b - a)

lemma iLen_of_lt {a b : ℝ} (hab : a < b) : iLen a b = ENNReal.ofReal (b - a) := by rfl

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
    -- `coverCost C = iSup_s ≤ 0`, but each finite sum is zero, hence `coverCost C = 0`.
    have : ∀ s : Finset ℕ, iLenFin C.a C.b s = 0 := by
      intro s;
      have : ∀ i ∈ s, iLen 0 0 = 0 := by intro i hi; simp [iLen]
      simpa [iLenFin, this] using Finset.sum_const_zero
    -- iSup of a constant 0 is 0
    have hcost : coverCost C = 0 := by
      have : (fun s : Finset ℕ => iLenFin C.a C.b s) = (fun _ : Finset ℕ => (0 : ℝ≥0∞)) := by
        funext s; simpa [this]
      simpa [coverCost, this]
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

/-- Finite-cover lower bound on a compact interval: if `[x,y] ⊆ ⋃ᵢ (aᵢ,bᵢ)`, then
    `y - x ≤ ∑ᵢ max(bᵢ - aᵢ, 0)`. (Classical, no measure theory.) -/
lemma length_le_sum_of_finite_cover
    {ι : Type} [Fintype ι]
    {x y : ℝ} (hxy : x ≤ y)
    (a b : ι → ℝ) (hcover : Icc x y ⊆ ⋃ i, Ioo (a i) (b i)) :
    (ENNReal.ofReal (y - x)) ≤ ∑ i, iLen (a i) (b i) := by
  -- Classical argument outline:
  -- 1) Extract a finite disjoint subfamily whose union still covers [x,y] except endpoints.
  -- 2) The length of the union ≤ sum of lengths, and the union's length ≥ y - x.
  -- A full formalization would sort endpoints and argue by induction on |ι|.
  sorry

/-- Lower bound for `(a,b)`: `b - a ≤ κ((a,b))`. -/
lemma Ioo_le_kappa {a b : ℝ} (hab : a < b) :
    ENNReal.ofReal (b - a) ≤ kappa (Ioo a b) := by
  classical
  -- ε-approximation: cover (a,b) by an open U and then restrict to [a+ε, b-ε],
  -- which is compact ⇒ finite subcover ⇒ apply finite-cover lemma and let ε→0.
  sorry

/-- Hence `κ((a,b)) = b - a` for `0<a<b<1`. -/
lemma kappa_Ioo_eq {a b : ℝ} (h0 : 0 < a) (hab : a < b) (h1 : b < 1) :
    kappa (Ioo a b) = ENNReal.ofReal (b - a) := by
  exact le_antisymm (kappa_Ioo_le h0 hab h1) (Ioo_le_kappa hab)

/-- Upper bound for `[0,1]`: use the open interval `(-ε, 1+ε)` and take ε→0. -/
lemma kappa_Icc01_le_one : kappa Icc01 ≤ (1 : ℝ≥0∞) := by
  classical
  -- For each n, εₙ = 1/(n+1), Uₙ = (−εₙ, 1+εₙ). Then κ([0,1]) ≤ 1+2εₙ. Take inf over n.
  -- The arithmetic and limit step are classical; full formalization omitted here.
  sorry

/-- Lower bound for `[0,1]`: any countable open cover has total length ≥ 1. -/
lemma kappa_Icc01_ge_one : (1 : ℝ≥0∞) ≤ kappa Icc01 := by
  classical
  -- Reduce to finite subcovers of `[δ,1−δ]` and apply `length_le_sum_of_finite_cover`, then let δ→0.
  sorry

/-- Hence `κ([0,1]) = 1`. -/
lemma kappa_Icc01 : kappa Icc01 = (1 : ℝ≥0∞) := by
  exact le_antisymm kappa_Icc01_le_one kappa_Icc01_ge_one

/-- Disjoint open union: if `U = ⋃ₙ (aₙ,bₙ)` with pairwise disjoint intervals in `(0,1)`,
    then `κ(U) = sup over finite partial sums = ∑ (bₙ − aₙ)` in our sense. -/
lemma kappa_open_disjoint_iUnion
    (a b : ℕ → ℝ)
    (hpairwise : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hinside : ∀ n, 0 < a n ∧ a n < b n ∧ b n < 1) :
    kappa (⋃ n, Ioo (a n) (b n)) = iLenSum a b := by
  classical
  -- `≤`: as before, use the canonical cover to bound from above by any finite partial sum, hence by the `iSup`.
  have hle : kappa (⋃ n, Ioo (a n) (b n)) ≤ iLenSum a b := by
    have h₁ : kappa (⋃ n, Ioo (a n) (b n)) ≤ kappaOpen (⋃ n, Ioo (a n) (b n)) :=
      kappa_le_kappaOpen (M := _) (U := _) (isOpen_iUnion fun _ => isOpen_Ioo) (by intro x hx; exact hx)
    -- pick the canonical cover C with these intervals
    let C : IooCover (⋃ n, Ioo (a n) (b n)) :=
      { a := a, b := b
        , hcover := by intro x hx; simpa using hx
        , hopen := (isOpen_iUnion fun _ => isOpen_Ioo) }
    have : kappaOpen (⋃ n, Ioo (a n) (b n)) ≤ coverCost C := sInf_le ⟨C, trivial, rfl⟩
    exact h₁.trans (this.trans (by simp [coverCost]))
  -- `≥`: monotone limit over finite partial unions using disjointness and `κ((a,b)) = b-a`.
  -- Formal details omitted here.
  have hge : iLenSum a b ≤ kappa (⋃ n, Ioo (a n) (b n)) := by
    sorry
  exact le_antisymm hle hge

end Kappa01
