/-
  Aus jeder überabzählbaren Teilmenge S ⊆ ℝ gibt es eine nichtleere
  perfekte Teilmenge K ⊆ closure S. Außerdem gilt für jede
  nichtleere perfekte K ⊆ ℝ die Gleichmächtigkeit #K = #ℝ.
-/

import Mathlib

open Set Topology Cardinal

namespace PerfectFromUncountable

/-- Wenn `S` überabzählbar ist, dann ist auch `closure S` überabzählbar. -/
lemma uncountable_closure {S : Set ℝ} (hS : ¬ S.Countable) :
    ¬ (closure S).Countable := by
  intro hcl
  exact hS (hcl.mono subset_closure)

/-- In ℝ (Polish, zweitabzählbar): Jede überabzählbare abgeschlossene Menge enthält
    eine **nichtleere perfekte** Teilmenge. Wir wenden dies auf `closure S` an. -/
theorem exists_perfect_nonempty_in_closure
    {S : Set ℝ} (hS : ¬ S.Countable) :
    ∃ K : Set ℝ, K ⊆ closure S ∧ Perfect K ∧ K.Nonempty := by
  -- closure S ist abgeschlossen und überabzählbar
  have hcl_unc : ¬ (closure S).Countable := uncountable_closure hS
  have hcl_closed : IsClosed (closure S) := isClosed_closure
  -- Mathlib: überabzählbare abgeschlossene Teilmenge eines Polish-Raums
  -- enthält eine perfekte, nichtleere Teilmenge.
  obtain ⟨K, hKperf, hKne, hKsubset⟩ :=
    exists_perfect_nonempty_of_isClosed_of_not_countable
      (C := closure S) hcl_closed hcl_unc
  exact ⟨K, hKsubset, hKperf, hKne⟩

/-- Jede **nichtleere perfekte** Teilmenge von ℝ hat Kardinalität des Kontinuums. -/
theorem card_eq_real_of_perfect_nonempty
    {K : Set ℝ} (hK : Perfect K) (hKne : K.Nonempty) :
    (#↥K : Cardinal) = (#ℝ : Cardinal) := by
  classical
  -- In einem vollständigen metrischen Raum gibt es für perfekte nichtleere K
  -- eine stetige Injektion des Cantor-Raums (ℕ → Bool) nach ℝ mit Bild in K.
  obtain ⟨f, hfrange, _hfcont, hfinj⟩ :=
    Perfect.exists_nat_bool_injection (α := ℝ) hK hKne
  -- Daraus eine Injektion (ℕ → Bool) ↪ ↥K konstruieren:
  have hCantorIntoK : (#(ℕ → Bool) : Cardinal) ≤ #↥K := by
    refine Cardinal.mk_le_of_injective
      (f := fun a : (ℕ → Bool) => (⟨f a, hfrange ⟨a, rfl⟩⟩ : K)) ?_
    intro a b h
    have : f a = f b := congrArg Subtype.val h
    exact hfinj this
  -- Subtyp-Kardinalität ist ≤ Obertyp
  have hK_le_R : (#↥K : Cardinal) ≤ (#ℝ : Cardinal) :=
    (Cardinal.mk_subtype_le K)

  -- #(ℕ → Bool) = 2^ℵ₀ = 𝔠 (ohne `simpa`)
  have hCantorCard : (#(ℕ → Bool) : Cardinal) = 𝔠 := by
    have h1 : (#(ℕ → Bool) : Cardinal) = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := by
      calc
        (#(ℕ → Bool) : Cardinal)
            = Cardinal.lift (#Bool : Cardinal) ^ Cardinal.lift (#ℕ : Cardinal) :=
              Cardinal.mk_arrow (α := ℕ) (β := Bool)
        _   = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := by
              simp [Cardinal.lift_id]
    calc
      (#(ℕ → Bool) : Cardinal)
          = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := h1
      _   = (2 : Cardinal) ^ ℵ₀ := by simp
      _   = 𝔠 := rfl
  -- #ℝ = 𝔠
  have hRCard : (#ℝ : Cardinal) = 𝔠 := Cardinal.mk_real

  -- 𝔠 ≤ #K aus hCantorIntoK, ganz ohne `simpa`
 -- rewrite #(ℕ → Bool) to 𝔠 in the inequality
  have hC : 𝔠 ≤ #↥K := (hCantorCard ▸ hCantorIntoK)
  -- rewrite 𝔠 to #ℝ in the inequality
  have hR_le_K : (#ℝ : Cardinal) ≤ #↥K := (hRCard.symm ▸ hC)

   -- (#ℝ) ≤ #K via #ℝ = 𝔠
  have hC : 𝔠 ≤ #↥K := (hCantorCard ▸ hCantorIntoK)
  have hR_le_K : (#ℝ : Cardinal) ≤ #↥K := (hRCard.symm ▸ hC)

  exact le_antisymm hK_le_R hR_le_K

/-- Kombiniertes Ergebnis: Aus `S` überabzählbar folgt
    `∃ K ⊆ closure S, Perfect K ∧ K.Nonempty ∧ #K = #ℝ`. -/
theorem exists_perfect_in_closure_with_card
    {S : Set ℝ} (hS : ¬ S.Countable) :
    ∃ K : Set ℝ, K ⊆ closure S ∧ Perfect K ∧ K.Nonempty ∧ (#↥K : Cardinal) = #ℝ := by
  obtain ⟨K, hKsubset, hKperf, hKne⟩ := exists_perfect_nonempty_in_closure (S := S) hS
  have hcard : (#↥K : Cardinal) = #ℝ := card_eq_real_of_perfect_nonempty hKperf hKne
  exact ⟨K, hKsubset, hKperf, hKne, hcard⟩

/-- Bonus: Enthält `S` selbst eine nichtleere perfekte Teilmenge `K`, so gilt `#S = #ℝ`. -/
theorem card_eq_real_of_contains_perfect_subset
    {S K : Set ℝ} (hKS : K ⊆ S) (hK : Perfect K) (hKne : K.Nonempty) :
    (#↥S : Cardinal) = (#ℝ : Cardinal) := by
  classical
  -- Injektion Cantor ↪ K (wie oben)
  obtain ⟨f, hfrange, _hfcont, hfinj⟩ :=
    Perfect.exists_nat_bool_injection (α := ℝ) hK hKne
  have hCantorIntoK : (#(ℕ → Bool) : Cardinal) ≤ #↥K := by
    refine Cardinal.mk_le_of_injective
      (f := fun a : (ℕ → Bool) => (⟨f a, hfrange ⟨a, rfl⟩⟩ : K)) ?_
    intro a b h
    have : f a = f b := congrArg Subtype.val h
    exact hfinj this
  -- Injektion K ↪ S via Inklusion
  have hKIntoS : (#↥K : Cardinal) ≤ #↥S := by
    refine Cardinal.mk_le_of_injective
      (f := fun x : K => (⟨(x : ℝ), hKS x.property⟩ : S)) ?_
    intro x y h
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  -- Cantor ↪ S
  have hCantorIntoS : (#(ℕ → Bool) : Cardinal) ≤ #↥S :=
    le_trans hCantorIntoK hKIntoS

  -- #(ℕ → Bool) = 𝔠 ohne `simpa`
  have hCantorCard : (#(ℕ → Bool) : Cardinal) = 𝔠 := by
    have h1 : (#(ℕ → Bool) : Cardinal) = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := by
      calc
        (#(ℕ → Bool) : Cardinal)
            = Cardinal.lift (#Bool : Cardinal) ^ Cardinal.lift (#ℕ : Cardinal) :=
              Cardinal.mk_arrow (α := ℕ) (β := Bool)
        _   = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := by
              simp [Cardinal.lift_id]
    calc
      (#(ℕ → Bool) : Cardinal)
          = (#Bool : Cardinal) ^ (#ℕ : Cardinal) := h1
      _   = (2 : Cardinal) ^ ℵ₀ := by simp
      _   = 𝔠 := rfl
  have hRCard : (#ℝ : Cardinal) = 𝔠 := Cardinal.mk_real

  -- 𝔠 ≤ #S aus hCantorIntoS, per simple rewrite statt `Eq.substr`
  have hC_le_S : 𝔠 ≤ #↥S := (hCantorCard ▸ hCantorIntoS)
  -- #ℝ ≤ #S via #ℝ = 𝔠
  have hR_le_S : (#ℝ : Cardinal) ≤ #↥S := (hRCard.symm ▸ hC_le_S)

  -- #ℝ ≤ #S via #ℝ = 𝔠
  have hR_le_S : (#ℝ : Cardinal) ≤ #↥S := (hRCard.symm ▸ hC_le_S)
  -- #S ≤ #ℝ via Subtyp S ↪ ℝ
  have hS_le_R : (#↥S : Cardinal) ≤ (#ℝ : Cardinal) := Cardinal.mk_subtype_le S
  exact le_antisymm hS_le_R hR_le_S

end PerfectFromUncountable
