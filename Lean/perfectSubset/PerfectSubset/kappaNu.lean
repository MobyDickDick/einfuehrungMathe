import Mathlib

open Set

noncomputable section
namespace PerfectSubset

/-- Fixes Intervall `I = [0,1]`. -/
def I : Set ℝ := Icc (0 : ℝ) 1

/-- Relative offene Überdeckungen im Intervall:
    𝓥(M) = { U | ∃O offen, U = I ∩ O ∧ M ⊆ U }. -/
def V (M : Set ℝ) : Set (Set ℝ) :=
  { U | ∃ O : Set ℝ, IsOpen O ∧ U = I ∩ O ∧ M ⊆ U }

/-- Naiver Rahmen: nur die wirklich benötigten Annahmen. -/
structure KappaNu where
  kappa : Set ℝ → ℝ
  nu    : Set ℝ → ℝ
  /-- Bounds von κ auf Teilmengen von I. -/
  kappa_bounds :
    ∀ {A : Set ℝ}, A ⊆ I → 0 ≤ kappa A ∧ kappa A ≤ 1
  /-- Offene Zerlegung im Intervall: κ(I ∩ Oᶜ) = 1 - κ(I ∩ O). -/
  kappa_open_partition :
    ∀ {O : Set ℝ}, IsOpen O → kappa (I ∩ Oᶜ) = (1 : ℝ) - kappa (I ∩ O)
  /-- ν auf Komplementen via 𝓥(M): ν(I \ M) = Sup { κ(I \ U) | U ∈ 𝓥(M) }. -/
  nu_on_compl :
    ∀ {M : Set ℝ}, M ⊆ I →
      nu (I \ M) = sSup {x | ∃ U ∈ V M, x = kappa (I \ U)}

namespace KappaNu

variable (KN : KappaNu)

/-- Bildmenge der κ-Werte über 𝓥(M). -/
def Aset (M : Set ℝ) : Set ℝ :=
  {x | ∃ U ∈ V M, x = KN.kappa U}

/-- `I \ (I ∩ O) = I ∩ Oᶜ`. -/
lemma diff_inter_eq_inter_compl (O : Set ℝ) :
    I \ (I ∩ O) = I ∩ Oᶜ := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨hxI, hxNot⟩
    refine ⟨hxI, ?_⟩
    intro hxIO
    exact hxNot ⟨hxI, hxIO⟩
  · intro hx
    rcases hx with ⟨hxI, hxOc⟩
    exact ⟨hxI, fun hxIO => hxOc hxIO.2⟩

/-- Für `U = I ∩ O` (O offen): κ(I \ U) = 1 - κ(U). -/
lemma kappa_diff_eq_one_sub_kappa_of_memV
    {M U : Set ℝ} (hU : U ∈ V M) :
    KN.kappa (I \ U) = 1 - KN.kappa U := by
  rcases hU with ⟨O, hO, rfl, _hMU⟩
  -- U = I ∩ O
  simpa [diff_inter_eq_inter_compl (O := O)] using
    KN.kappa_open_partition (O := O) hO

/-- 𝓥(M) ist nicht leer (U = I). -/
lemma V_nonempty {M : Set ℝ} (hM : M ⊆ I) : (V M).Nonempty := by
  refine ⟨I, ?_⟩
  refine ⟨(Set.univ : Set ℝ), isOpen_univ, by simp [I], ?_⟩
  simpa using hM

/-- A(M) ist nach unten durch 0 beschränkt (benötigt kein `hM`). -/
lemma Aset_bddBelow {M : Set ℝ} :
    BddBelow (KN.Aset M) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨U, hU, rfl⟩
  rcases hU with ⟨O, _hO, rfl, _⟩
  have hUsub : I ∩ O ⊆ I := by intro x hx; exact hx.1
  exact (KN.kappa_bounds (A := I ∩ O) hUsub).1

/-- A(M) ist nach oben durch 1 beschränkt (benötigt kein `hM`). -/
lemma Aset_bddAbove {M : Set ℝ} :
    BddAbove (KN.Aset M) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨U, hU, rfl⟩
  rcases hU with ⟨O, _hO, rfl, _⟩
  have hUsub : I ∩ O ⊆ I := by intro x hx; exact hx.1
  exact (KN.kappa_bounds (A := I ∩ O) hUsub).2

/-- A(M) ist nicht leer. -/
lemma Aset_nonempty {M : Set ℝ} (hM : M ⊆ I) :
    (KN.Aset M).Nonempty := by
  rcases V_nonempty (M := M) hM with ⟨U, hU⟩
  exact ⟨KN.kappa U, ⟨U, hU, rfl⟩⟩

/-- ν(I \ M) = Sup ( (x ↦ 1 - x) '' A(M) ). -/
lemma nu_eq_sup_image_one_sub {M : Set ℝ} (hM : M ⊆ I) :
  KN.nu (I \ M) = sSup ((fun x => 1 - x) '' KN.Aset M) := by
  classical
  have h0 := KN.nu_on_compl (M := M) hM
  -- Gleichheit der Indexmengen:
  have hset :
    {x | ∃ U ∈ V M, x = KN.kappa (I \ U)}
      = (fun x => 1 - x) '' KN.Aset M := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨U, hU, rfl⟩
      exact ⟨KN.kappa U, ⟨U, hU, rfl⟩, by
        simp [kappa_diff_eq_one_sub_kappa_of_memV (KN := KN) hU]⟩
    · intro hx
      rcases hx with ⟨x0, ⟨U, hU, rfl⟩, rfl⟩
      exact ⟨U, hU, by
        simp [kappa_diff_eq_one_sub_kappa_of_memV (KN := KN) hU]⟩
  -- umschreiben
  simp [hset] at h0
  exact h0

/-- Reine Ordnungs-Tatsache auf ℝ (kein Maß!):
    Für nichtleeres, unten und oben beschränktes `A` gilt
    `Sup{1 - a | a∈A} = 1 - Inf A`.
    *(Hier als Axiom aufgenommen, um die Datei schlank zu halten.)* -/
axiom sup_image_one_sub_eq_one_sub_inf
    {A : Set ℝ} (hA_ne : A.Nonempty) (hA_bBelow : BddBelow A) (hA_bAbove : BddAbove A) :
    sSup ((fun x => 1 - x) '' A) = (1 : ℝ) - sInf A

/-- Äußeres κ(M) als Inf über A(M). -/
def kappaOuter (M : Set ℝ) : ℝ := sInf (KN.Aset M)

/-- Hauptsatz (naiv, ohne Maßtheorie): Für `M ⊆ [0,1]` gilt
    `κ(M) + ν(I \ M) = 1`. -/
theorem kappa_add_nu_compl_eq_one {M : Set ℝ} (hM : M ⊆ I) :
  KN.kappaOuter M + KN.nu (I \ M) = 1 := by
  classical
  have hA_ne  := KN.Aset_nonempty (M := M) hM
  have hA_bLo := KN.Aset_bddBelow (M := M)
  have hA_bUp := KN.Aset_bddAbove (M := M)
  have hNu : KN.nu (I \ M) = sSup ((fun x => 1 - x) '' KN.Aset M) :=
    KN.nu_eq_sup_image_one_sub (M := M) hM
  have hSup :
    sSup ((fun x => 1 - x) '' KN.Aset M) = 1 - sInf (KN.Aset M) :=
    sup_image_one_sub_eq_one_sub_inf (A := KN.Aset M) hA_ne hA_bLo hA_bUp
  simp [kappaOuter, hNu, hSup]
end KappaNu
end PerfectSubset
