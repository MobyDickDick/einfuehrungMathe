import Mathlib
import PerfectSubset.PreservingRefine

noncomputable section
open Set

namespace Stage

/-
  Zusatz: Monotonie & Einbettung für die „Keep“-Iteration
  -------------------------------------------------------
  1) core_refineOneKeep_subset_core:
        Ein Keep-Schritt kann den Kern nur verkleinern.
  2) mem_KωKeep_of_core:
        Aus x0 ∈ core s folgt x0 ∈ KωKeep … s.
  3) KωKeep_subset_Icc:
        Die ω-Kernmenge liegt im Grundintervall [xu, xo].
-/

/-- Ein Keep-Schritt kann den Kern nur verkleinern. -/
lemma core_refineOneKeep_subset_core
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  core (M := M) (xu := xu) (xo := xo)
        (refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo)
           hxu hxo x0 s J hJmem hHit)
    ⊆ core (M := M) (xu := xu) (xo := xo) s := by
  classical
  intro x hx
  -- Neuer Zustand
  let s' :=
    refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit
  -- Zerlege `hx : x ∈ core s'` in die Konjunktionsform der `core`-Def.
  have hxParts :
      (xu ≤ x ∧ x ≤ xo) ∧ x ∉ U0' M xu xo ∧ ∀ U ∈ s'.mids, x ∉ U := by
    simpa [core] using hx
  -- Schreibe die neue Mid-Liste als `U0 :: s.mids`
  obtain ⟨U0, hMids, _hNotInU0⟩ :=
    exists_cons_mids_refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo)
      hxu hxo x0 s J hJmem hHit
  -- Aus „für alle U in s'.mids“ folgt insbesondere „für alle U in s.mids“
  have hforallOld : ∀ U ∈ s.mids, x ∉ U := by
    intro U hU
    -- U ∈ s.mids  ⇒  (U = U0 ∨ U ∈ s.mids)  ⇒  U ∈ s'.mids
    have hU' : U ∈ s'.mids := by
      rw [hMids, List.mem_cons]
      exact Or.inr hU
    -- falls du vorher `hxParts : (xu ≤ x ∧ x ≤ xo) ∧ x ∉ U0' … ∧ ∀ U ∈ s'.mids, x ∉ U` hast:
    exact hxParts.2.2 U hU'
  -- andernfalls, wenn dein Beweisobjekt `hx` heißt:  exact hx.2.2 U hU'

  -- Ziel: wieder die `core`-Konjunktionsform des *alten* Zustands
  simpa [core] using And.intro hxParts.1 (And.intro hxParts.2.1 hforallOld)

/-- Direkt: aus `x0 ∈ core s` folgt `x0 ∈ KωKeep … s`. -/
lemma mem_KωKeep_of_core
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo)
    (s : State M xu xo)
    (hx0Core : x0 ∈ core (M := M) (xu := xu) (xo := xo) s) :
  x0 ∈ KωKeep (M := M) (xu := xu) (xo := xo)
         hM hxu hxo x0 sel s := by
  have hx_all :=
    mem_core_refineNKeep_of_core (M:=M) (xu:=xu) (xo:=xo)
      hM hxu hxo x0 sel s hx0Core
  simpa [KωKeep] using Set.mem_iInter.mpr hx_all

/-- `KωKeep … s ⊆ Icc xu xo`. -/
lemma KωKeep_subset_Icc
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo)
    (s : State M xu xo) :
  KωKeep (M := M) (xu := xu) (xo := xo) hM hxu hxo x0 sel s ⊆ Set.Icc xu xo := by
  intro x hx
  -- Aus ∩-Mitgliedschaft folgt speziell Mitgliedschaft bei n=0
  have hx0' : x ∈ core (M := M) (xu := xu) (xo := xo)
                 (refineNKeep (M := M) (xu := xu) (xo := xo)
                    hM hxu hxo x0 sel 0 s) := by
    have hx_all : ∀ n,
        x ∈ core (M := M) (xu := xu) (xo := xo)
               (refineNKeep (M := M) (xu := xu) (xo := xo)
                  hM hxu hxo x0 sel n s) := by
      simpa [KωKeep] using Set.mem_iInter.mp hx
    simpa [refineNKeep] using hx_all 0
  -- Kern liegt stets in `Icc`
  have : x ∈ Set.Icc xu xo :=
    (core_subset_Icc (s := (refineNKeep (M:=M) (xu:=xu) (xo:=xo)
                              hM hxu hxo x0 sel 0 s))) hx0'
  simpa [refineNKeep] using this

end Stage
