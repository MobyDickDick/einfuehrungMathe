-- Superdense/Phase0A.lean
import Mathlib

open Set

/-- Komplement von `M` im Grundintervall `[x_u,x_o]`. -/
def S (M : Set ℝ) (xu xo : ℝ) : Set ℝ :=
  Set.Icc xu xo \ M

/-- Kleiner Radius um `y`, der die Endpunkte schont. -/
def rad (xu xo y : ℝ) : ℝ :=
  min (|y - xu|) (|xo - y|) / 4

/-- Offene Hülle des Komplements: Vereinigung kleiner offener Intervalle. -/
def U0' (M : Set ℝ) (xu xo : ℝ) : Set ℝ :=
  ⋃ (y : ℝ), ⋃ (_hy : y ∈ S M xu xo),
    Set.Ioo (y - rad xu xo y) (y + rad xu xo y)

/-- `U0'` ist offen. -/
lemma U0'_isOpen (M : Set ℝ) (xu xo : ℝ) : IsOpen (U0' M xu xo) := by
  classical
  unfold U0'
  refine isOpen_iUnion ?_
  intro y
  refine isOpen_iUnion ?_
  intro hy
  exact isOpen_Ioo

/-- Für `y ∈ S` ist der Radius positiv, wenn `x_u,x_o ∈ M`. -/
lemma rad_pos_of_mem_S
    {M : Set ℝ} {xu xo y : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M)
    (hyI : y ∈ Set.Icc xu xo) (hyM : y ∉ M) :
    0 < rad xu xo y := by
  have hy_ne_xu : y ≠ xu := by
    intro h; exact hyM (by simpa [h] using hxu)
  have hy_ne_xo : y ≠ xo := by
    intro h; exact hyM (by simpa [h] using hxo)
  have h1 : 0 < |y - xu| := by
    have : y - xu ≠ 0 := sub_ne_zero.mpr hy_ne_xu
    simpa [abs_pos_iff] using this
  have h2 : 0 < |xo - y| := by
    have : xo - y ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hy_ne_xo)
    simpa [abs_pos_iff] using this
  have hmin : 0 < min (|y - xu|) (|xo - y|) := lt_min h1 h2
  have : 0 < min (|y - xu|) (|xo - y|) / 4 := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    exact div_pos hmin h4
  simpa [rad] using this

/-- `S ⊆ U0'` (die offene Hülle deckt das Komplement im Intervall). -/
lemma S_subset_U0'
    {M : Set ℝ} {xu xo : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M) :
    S M xu xo ⊆ U0' M xu xo := by
  classical
  intro y hyS
  rcases hyS with ⟨hyIcc, hyNotM⟩
  have hr : 0 < rad xu xo y := rad_pos_of_mem_S (M:=M) hxu hxo hyIcc hyNotM
  have hy_in : y ∈ Set.Ioo (y - rad xu xo y) (y + rad xu xo y) := by
    refine ⟨?L, ?R⟩
    · simpa using sub_lt_self y hr
    · simpa using lt_add_of_pos_right y hr
  unfold U0'
  refine mem_iUnion.mpr ?_
  refine ⟨y, mem_iUnion.mpr ?_⟩
  exact ⟨⟨hyIcc, hyNotM⟩, by simpa using hy_in⟩

/-- Startmenge nach Phase 0. -/
def K0 (M : Set ℝ) (xu xo : ℝ) : Set ℝ :=
  Set.Icc xu xo ∩ (U0' M xu xo)ᶜ

lemma K0_subset_Icc (M : Set ℝ) (xu xo : ℝ) :
    K0 M xu xo ⊆ Set.Icc xu xo := by
  intro x hx; exact hx.1

lemma isClosed_K0 (M : Set ℝ) (xu xo : ℝ) :
    IsClosed (K0 M xu xo) := by
  classical
  have : IsClosed (U0' M xu xo)ᶜ := (U0'_isOpen M xu xo).isClosed_compl
  simpa [K0] using isClosed_Icc.inter this

/-- Phase 0-Kern: `K0 ⊆ M`. -/
lemma K0_subset_M
    {M : Set ℝ} {xu xo : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M) :
    K0 M xu xo ⊆ M := by
  intro x hx
  rcases hx with ⟨hxIcc, hxNotU⟩
  by_contra hxNotM
  have hxS : x ∈ S M xu xo := ⟨hxIcc, hxNotM⟩
  have hxU : x ∈ U0' M xu xo := S_subset_U0' (M:=M) (xu:=xu) (xo:=xo) hxu hxo hxS
  exact hxNotU hxU
