import Mathlib
open Set

noncomputable section

namespace ExchangeSupInf

/-- Allgemein für `a : ℝ`:
`sInf ((fun x => a - x) '' M) = a - sSup M`,
wenn `M` nichtleer und nach oben beschränkt ist. -/
theorem sInf_image_const_sub_eq_const_sub_sSup
    {M : Set ℝ} (hMn : M.Nonempty) (hBdd : BddAbove M) (a : ℝ) :
    sInf ((fun x : ℝ => a - x) '' M) = a - sSup M := by
  classical
  set T : Set ℝ := (fun x : ℝ => a - x) '' M with hT
  -- T ist nichtleer
  have hTne : T.Nonempty := by
    rcases hMn with ⟨x, hx⟩
    exact ⟨a - x, ⟨x, hx, rfl⟩⟩
  -- Extrahiere eine konkrete obere Schranke B für M
  obtain ⟨B, hB⟩ := hBdd
  -- T ist nach unten beschränkt: untere Schranke (a - B)
  have hTbb : BddBelow T := ⟨a - B, by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le_B : x ≤ B := hB hx
    have : x + (a - B) ≤ a := by
      have := add_le_add_right hx_le_B (a - B)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact (le_sub_iff_add_le).mpr (by
      simpa [add_comm, add_left_comm, add_assoc] using this)⟩
  -- (a - sSup M) ist GLB von T
  have hLB_T : (a - sSup M) ∈ lowerBounds T := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    -- hier benutzen wir die konkrete BddAbove-Zeugenschaft ⟨B, hB⟩
    have hx_le_sSup : x ≤ sSup M := le_csSup ⟨B, hB⟩ hx
    have : x + (a - sSup M) ≤ a := by
      have := add_le_add_right hx_le_sSup (a - sSup M)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact (le_sub_iff_add_le).mpr (by
      simpa [add_comm, add_left_comm, add_assoc] using this)
  have hGLB_T : IsGLB T (a - sSup M) := by
    refine ⟨hLB_T, ?_⟩
    intro z hz
    -- Aus z ≤ a - x (für alle x∈M) folgt x ≤ a - z ⇒ a - z ist obere Schranke von M
    have hUpper' : ∀ x ∈ M, x ≤ a - z := by
      intro x hx
      have hz' : z ≤ a - x := hz ⟨x, hx, rfl⟩
      have : x + z ≤ a := by
        have := add_le_add_left hz' x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact (le_sub_iff_add_le).mpr (by simpa [add_comm] using this)
    -- WICHTIG: Hier `csSup_le hMn ...` statt `⟨B, hB⟩`
    have hsSup_le : sSup M ≤ a - z := csSup_le hMn hUpper'
    have : sSup M + z ≤ a := by
      have := add_le_add_right hsSup_le z
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    exact (le_sub_iff_add_le).mpr (by simpa [add_comm] using this)
  -- Eindeutigkeit des GLB
  have hglb_ci : IsGLB T (sInf T) := isGLB_csInf hTne hTbb
  have hEq : sInf T = a - sSup M := hglb_ci.unique hGLB_T
  simpa [hT] using hEq

/-- Bequeme Spezialform für `a = 1` und `M ⊆ [0,1]`. -/
theorem sInf_image_one_sub_eq_one_sub_sSup_of_subset_Icc
    {M : Set ℝ} (hM : M ⊆ Icc (0 : ℝ) 1) (hMn : M.Nonempty) :
    sInf ((fun x : ℝ => 1 - x) '' M) = 1 - sSup M := by
  have hBdd : BddAbove M := ⟨(1 : ℝ), by intro x hx; exact (hM hx).2⟩
  simpa using
    sInf_image_const_sub_eq_const_sub_sSup (M := M) (a := 1) hMn hBdd

end ExchangeSupInf
