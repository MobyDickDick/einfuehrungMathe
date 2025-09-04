-- Superdense/Phase 2.3
import Mathlib

noncomputable section
open Set

-- Lokal *zweiseitig* superdicht in ℝ.
def TwoSidedSuperdense (M : Set ℝ) : Prop :=
  ¬ M.Countable ∧
  ∀ ⦃x ε : ℝ⦄, x ∈ M → 0 < ε →
    ((M ∩ Set.Ioo (x - ε) x).Infinite ∧
     (M ∩ Set.Ioo x (x + ε)).Infinite)

-- Komplement von `M` im Grundintervall `[x_u, x_o]`.
def S (M : Set ℝ) (xu xo : ℝ) : Set ℝ :=
  Set.Icc xu xo \ M

-- Kleiner Radius um `y`, der die Endpunkte schont (nur |y - ...|).
def rad (xu xo y : ℝ) : ℝ :=
  min (|y - xu|) (|y - xo|) / 4

-- Offene Hülle des Komplements: Vereinigung kleiner offener Intervalle.
def U0' (M : Set ℝ) (xu xo : ℝ) : Set ℝ :=
  ⋃ (y : ℝ), ⋃ (_hy : y ∈ S M xu xo),
    Set.Ioo (y - rad xu xo y) (y + rad xu xo y)

-- U0' ist offen.
lemma U0'_isOpen (M : Set ℝ) (xu xo : ℝ) : IsOpen (U0' M xu xo) := by
  classical
  unfold U0'
  refine isOpen_iUnion ?_
  intro y
  refine isOpen_iUnion ?_
  intro _hy
  exact isOpen_Ioo

-- Für y ∈ S ist der Radius positiv, wenn x_u,x_o ∈ M.
lemma rad_pos_of_mem_S
    {M : Set ℝ} {xu xo y : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M)
    (hyM : y ∉ M) :
    0 < rad xu xo y := by
  have hy_ne_xu : y ≠ xu := by
    intro h; exact hyM (by simpa [h] using hxu)
  have hy_ne_xo : y ≠ xo := by
    intro h; exact hyM (by simpa [h] using hxo)
  have h1 : 0 < |y - xu| := abs_pos.mpr (sub_ne_zero.mpr hy_ne_xu)
  have h2 : 0 < |y - xo| := abs_pos.mpr (sub_ne_zero.mpr hy_ne_xo)
  have hmin : 0 < min (|y - xu|) (|y - xo|) := lt_min h1 h2
  have h4 : (0 : ℝ) < 4 := by norm_num
  have : 0 < min (|y - xu|) (|y - xo|) / 4 := by exact div_pos hmin h4
  simpa [rad] using this

-- S ⊆ U0' (die offene Hülle deckt das Komplement im Intervall).
lemma S_subset_U0'
    {M : Set ℝ} {xu xo : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M) :
    S M xu xo ⊆ U0' M xu xo := by
  classical
  intro y hyS
  rcases hyS with ⟨hyIcc, hyNotM⟩
  have hr : 0 < rad xu xo y := rad_pos_of_mem_S (M:=M) hxu hxo hyNotM
  have hy_in : y ∈ Set.Ioo (y - rad xu xo y) (y + rad xu xo y) := by
    refine ⟨?L, ?R⟩
    · simpa using sub_lt_self y hr
    · simpa using lt_add_of_pos_right y hr
  unfold U0'
  refine mem_iUnion.mpr ?_
  refine ⟨y, mem_iUnion.mpr ?_⟩
  exact ⟨⟨hyIcc, hyNotM⟩, by simpa using hy_in⟩

-- Startmenge nach Phase 0.
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

-- Phase 0-Kern: K0 ⊆ M.
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

-- Links/Rechts-Nachbarn aus der lokalen zweiseitigen Superdichte
lemma exists_left_right_near
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {x ε : ℝ} (hx : x ∈ M) (hε : 0 < ε) :
  ∃ a b, a ∈ M ∧ b ∈ M ∧ x - ε < a ∧ a < x ∧ x < b ∧ b < x + ε := by
  classical
  rcases (hM.2 hx hε).1.nonempty with ⟨a, ha⟩
  rcases (hM.2 hx hε).2.nonempty with ⟨b, hb⟩
  rcases ha with ⟨haM, ⟨haL, haR⟩⟩
  rcases hb with ⟨hbM, ⟨hbL, hbR⟩⟩
  exact ⟨a, b, haM, hbM, haL, haR, hbL, hbR⟩

-- Ein "geschlossenes Segment" mit a < b
structure ClosedSeg where
  a : ℝ
  b : ℝ
  hlt : a < b

-- Die dazugehörige Menge
def segSet (J : ClosedSeg) : Set ℝ := Set.Icc J.a J.b

lemma segSet_closed (J : ClosedSeg) : IsClosed (segSet J) :=
  isClosed_Icc

lemma seg_len (J : ClosedSeg) : 0 < J.b - J.a :=
  sub_pos.mpr J.hlt

-- Mittelpunkt eines echten Segments liegt im offenen Inneren
lemma mid_mem_Ioo {a b : ℝ} (h : a < b) :
  (a + b) / 2 ∈ Set.Ioo a b := by
  -- Zuerst: 0 < (b - a)/2
  have hpos : 0 < (b - a) / 2 := by
    have hbma : 0 < b - a := sub_pos.mpr h
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact div_pos hbma h2
  -- Links: a < (a + b)/2  ⇔  0 < (a + b)/2 - a = (b - a)/2
  have hleft' : 0 < (a + b) / 2 - a := by
    have : (a + b) / 2 - a = (b - a) / 2 := by ring
    simpa [this] using hpos
  have hleft : a < (a + b) / 2 := sub_pos.mp hleft'
  -- Rechts: (a + b)/2 < b  ⇔  0 < b - (a + b)/2 = (b - a)/2
  have hright' : 0 < b - (a + b) / 2 := by
    have : b - (a + b) / 2 = (b - a) / 2 := by ring
    simpa [this] using hpos
  have hright : (a + b) / 2 < b := sub_pos.mp hright'
  exact ⟨hleft, hright⟩

-- Ein kleineres beidseitiges Intervall liegt im größeren (δ ≤ ε)
lemma Ioo_subset_of_radius_le {x ε δ : ℝ} (hδε : 0 < δ ∧ δ ≤ ε) :
  Set.Ioo (x - δ) (x + δ) ⊆ Set.Ioo (x - ε) (x + ε) := by
  intro y hy
  rcases hy with ⟨hyL, hyR⟩
  have h1 : x - ε ≤ x - δ := by linarith
  have h2 : x + δ ≤ x + ε := by linarith
  constructor
  · exact lt_of_le_of_lt h1 hyL
  · exact lt_of_lt_of_le hyR h2

-- kleine Rechenhilfen für Mittelpunkts-Umschreibungen
lemma aux_add_sub_div_two (x y : ℝ) : x + (y - x) / 2 = (x + y) / 2 := by ring
lemma aux_sub_sub_div_two (x y : ℝ) : y - (y - x) / 2 = (x + y) / 2 := by ring

/-- Trifft ein echtes Segment `J` die Menge `K0 M xu xo`, dann enthält `J`
    einen **inneren** Punkt aus `M`. -/
lemma exists_M_interior_of_seg_intersects_K0
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (J : ClosedSeg) (_ : segSet J ⊆ Set.Icc xu xo)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  ∃ z, z ∈ M ∧ z ∈ Set.Ioo J.a J.b := by
  classical
  rcases hHit with ⟨x0, hx0J, hx0K0⟩
  -- x0 ∈ M
  have hx0M : x0 ∈ M := (K0_subset_M (M:=M) (xu:=xu) (xo:=xo) hxu hxo) hx0K0
  -- x0 ∈ Icc J.a J.b
  rcases hx0J with ⟨hJleft, hJright⟩

  -- Fall 1: x0 = linker Rand
  by_cases hL : x0 = J.a
  · have hbgt : x0 < J.b := by simpa [hL] using J.hlt
    -- ε = halbe Distanz zur rechten Kante
    have hεpos : 0 < (J.b - x0) / 2 := by
      have : 0 < J.b - x0 := sub_pos.mpr hbgt
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact div_pos this h2
    set ε := (J.b - x0) / 2 with hεdef
    rcases exists_left_right_near (M:=M) hM (x:=x0) (ε:=ε) hx0M hεpos
      with ⟨a', b', haM, hbM, hLa, haLt, hLb, hbLt⟩
    -- x0 + ε = (x0 + J.b)/2  ⇒  x0 + ε < J.b
    have hx0eps_lt_b : x0 + ε < J.b := by
      have hx0_plus_eps_eq_mid : x0 + ε = (x0 + J.b) / 2 := by
        simp [hεdef, aux_add_sub_div_two]
      simpa [hx0_plus_eps_eq_mid] using
        (mid_mem_Ioo (a:=x0) (b:=J.b) hbgt).2
    refine ⟨b', hbM, ?_⟩
    constructor
    · -- J.a < b' aus x0 < b' und x0 = J.a
      simpa [hL] using hLb
    · -- b' < J.b aus b' < x0 + ε < J.b
      exact lt_trans hbLt hx0eps_lt_b

  -- Fall 2: x0 = rechter Rand
  by_cases hR : x0 = J.b
  · have halt : J.a < x0 := by simpa [hR] using J.hlt
    -- ε = halbe Distanz zur linken Kante
    have hεpos : 0 < (x0 - J.a) / 2 := by
      have : 0 < x0 - J.a := sub_pos.mpr halt
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact div_pos this h2
    set ε := (x0 - J.a) / 2 with hεdef
    rcases exists_left_right_near (M:=M) hM (x:=x0) (ε:=ε) hx0M hεpos
      with ⟨a', b', h_aM, h_bM, hLa, haLt, hLb, hbLt⟩
    -- J.a < x0 - ε  via Mittelpunktsformel
    have ha_lt_x0minus : J.a < x0 - ε := by
      have hx0_minus_eps_eq_mid : x0 - ε = (J.a + x0) / 2 := by
        have := aux_sub_sub_div_two (x:=J.a) (y:=x0)
        simpa [hεdef, add_comm] using this
      have : J.a < (J.a + x0) / 2 := (mid_mem_Ioo (a:=J.a) (b:=x0) halt).1
      simpa [hx0_minus_eps_eq_mid] using this
    refine ⟨a', h_aM, ?_⟩
    constructor
    · -- J.a < a' aus J.a < x0 - ε und x0 - ε < a'
      exact lt_trans ha_lt_x0minus hLa
    · -- a' < J.b aus a' < x0 und x0 = J.b
      simpa [hR] using haLt

  -- Fall 3: x0 echt innen
    -- Fall 3: x0 echt innen
  have hLeft  : J.a < x0 := lt_of_le_of_ne hJleft (ne_comm.mp hL)
  have hRight : x0 < J.b := lt_of_le_of_ne hJright hR
  exact ⟨x0, hx0M, ⟨hLeft, hRight⟩⟩

-- ------------------------------------------------------------
-- Erster Split-Schritt: zwei disjunkte Kinder + offenes Mittelstück
-- ------------------------------------------------------------

-- Hilfslemma: aus a ≤ b folgt a/2 ≤ b/2 (für ℝ)
-- Hilfslemma: aus a ≤ b folgt a/2 ≤ b/2 (für ℝ)
-- Aus a ≤ b folgt a/2 ≤ b/2 (auf ℝ)

-- a ≤ b ⇒ a/2 ≤ b/2  (ohne Mul-/simp-Gymnastik)
-- Aus a ≤ b folgt a/2 ≤ b/2  (auf ℝ), ohne Mul-/simp-Gymnastik
lemma half_le_half_of_le {a b : ℝ} (h : a ≤ b) :
  a / 2 ≤ b / 2 := by
  -- Standard: Division mit nichtnegativem Nenner erhält ≤
  simpa using
    (div_le_div_of_nonneg_right h (show (0 : ℝ) ≤ (2 : ℝ) by norm_num))

-- 0 < t ⇒ t/2 < t  (stabil, ohne div/ring/simp-Gymnastik)
lemma half_lt_self_of_pos {t : ℝ} (ht : 0 < t) : t / 2 < t := by
  -- (2)⁻¹ < 1  (weil 1/2 < 1)
  have inv2_lt_one : (2 : ℝ)⁻¹ < 1 := by
    have : (1/2 : ℝ) < 1 := by norm_num
    simpa [one_div] using this
  -- Schreibe t/2 als t * (2)⁻¹, dann multipliziere mit t>0
  calc
    t / 2 = t * (2 : ℝ)⁻¹ := by
      simp [div_eq_mul_inv]
    _     < t * 1         := by
      simpa [one_mul] using mul_lt_mul_of_pos_left inv2_lt_one ht
    _     = t             := by
      simp
-- Erster Split-Schritt: zwei disjunkte Kinder + offenes Mittelstück
-- Erster Split-Schritt: zwei disjunkte Kinder + offenes Mittelstück
lemma split_once
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (J : ClosedSeg) (hJsub : segSet J ⊆ Set.Icc xu xo)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  ∃ (J0 J1 : ClosedSeg) (Mid : Set ℝ),
    segSet J0 ⊆ segSet J ∧
    segSet J1 ⊆ segSet J ∧
    Disjoint (segSet J0) (segSet J1) ∧
    IsOpen Mid ∧
    Mid ⊆ Set.Ioo J.a J.b ∧
    segSet J ⊆ segSet J0 ∪ Mid ∪ segSet J1 ∧
    (segSet J0 ∩ M).Nonempty ∧
    (segSet J1 ∩ M).Nonempty := by
  classical
  -- innerer M-Punkt z in J
  obtain ⟨z, hzM, hzI⟩ :=
    exists_M_interior_of_seg_intersects_K0 (M:=M) hM (xu:=xu) (xo:=xo)
      hxu hxo J hJsub hHit
  rcases hzI with ⟨hzL, hzR⟩  -- J.a < z < J.b

  -- ε := Hälfte der minimalen Randdistanz
  let ε : ℝ := (min (z - J.a) (J.b - z)) / 2
  have hεpos : 0 < ε := by
    have h1 : 0 < z - J.a := sub_pos.mpr hzL
    have h2 : 0 < J.b - z := sub_pos.mpr hzR
    have hmin : 0 < min (z - J.a) (J.b - z) := lt_min h1 h2
    have h2pos : (0 : ℝ) < 2 := by norm_num
    exact div_pos hmin h2pos

  -- Nachbarn um z: ℓ links, r rechts (beide in M)
  obtain ⟨ℓ, r, hℓM, hrM, hleftL, hleftR, hrightL, hrightR⟩ :=
    exists_left_right_near (M:=M) hM (x:=z) (ε:=ε) hzM hεpos
  -- hleftL : z - ε < ℓ ,  hleftR : ℓ < z
  -- hrightL : z < r      ,  hrightR : r < z + ε

  -- (1) J.a < ℓ
  have hz_a_pos : 0 < z - J.a := sub_pos.mpr hzL
  have hε_le_half_left : ε ≤ (z - J.a) / 2 := by
    have h0 : min (z - J.a) (J.b - z) / 2 ≤ (z - J.a) / 2 :=
      half_le_half_of_le (min_le_left (z - J.a) (J.b - z))
    simpa [ε] using h0
  have half_lt_left : (z - J.a) / 2 < (z - J.a) :=
    half_lt_self_of_pos hz_a_pos
  have hJa_plus_eps_lt_z : J.a + ε < z := by
    have hεlt : ε < z - J.a := lt_of_le_of_lt hε_le_half_left half_lt_left
    have h' : J.a + ε < J.a + (z - J.a) := add_lt_add_left hεlt J.a
    have hz_sum : J.a + (z - J.a) = z := by ring
    simpa [hz_sum] using h'
  have hJa_lt_z_minus_eps : J.a < z - ε :=
    (lt_sub_iff_add_lt).mpr hJa_plus_eps_lt_z
  have hJa_lt_ell : J.a < ℓ := lt_trans hJa_lt_z_minus_eps hleftL

  -- (2) r < J.b
  have hz_b_pos : 0 < J.b - z := sub_pos.mpr hzR
  have hε_le_half_right : ε ≤ (J.b - z) / 2 := by
    have h0 : min (z - J.a) (J.b - z) / 2 ≤ (J.b - z) / 2 :=
      half_le_half_of_le (min_le_right (z - J.a) (J.b - z))
    simpa [ε] using h0
  have half_lt_right : (J.b - z) / 2 < (J.b - z) :=
    half_lt_self_of_pos hz_b_pos
  have hz_plus_eps_lt_b : z + ε < J.b := by
    have hεlt : ε < J.b - z := lt_of_le_of_lt hε_le_half_right half_lt_right
    have h' : ε + z < (J.b - z) + z := add_lt_add_right hεlt z
    have h'' : z + ε < (J.b - z) + z := by simpa [add_comm] using h'
    have hz_sum' : (J.b - z) + z = J.b := by ring
    simpa [hz_sum'] using h''
  have h_r_lt_Jb : r < J.b := lt_trans hrightR hz_plus_eps_lt_b

  -- Kinder & Mittelstück
  let J0 : ClosedSeg := { a := J.a, b := ℓ, hlt := hJa_lt_ell }
  let J1 : ClosedSeg := { a := r, b := J.b, hlt := h_r_lt_Jb }
  let Mid : Set ℝ := Set.Ioo ℓ r

  -- Inklusionen der Kinder in J
  have sub0 : segSet J0 ⊆ segSet J := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    have hℓ_le_Jb : ℓ ≤ J.b := le_of_lt (lt_trans hleftR hzR)
    exact ⟨hxL, le_trans hxR hℓ_le_Jb⟩
  have sub1 : segSet J1 ⊆ segSet J := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    have hz_le_x : z ≤ x := le_trans (le_of_lt hrightL) hxL
    have hJa_lt_x : J.a < x := lt_of_lt_of_le hzL hz_le_x
    exact ⟨le_of_lt hJa_lt_x, hxR⟩

  -- Disjunktheit der Kinder
  have disj : Disjoint (segSet J0) (segSet J1) := by
    have hsep : ℓ < r := lt_trans hleftR hrightL
    refine disjoint_left.mpr ?_
    intro x hx0 hx1
    rcases hx0 with ⟨hx0L, hx0R⟩
    rcases hx1 with ⟨hx1L, hx1R⟩
    have : r ≤ ℓ := le_trans hx1L hx0R
    exact (not_le_of_gt hsep) this

  -- Mid ist offen und liegt im Inneren von J
  have openMid : IsOpen Mid := isOpen_Ioo
  have midSub : Mid ⊆ Set.Ioo J.a J.b := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    exact ⟨lt_trans hJa_lt_ell hxL, lt_trans hxR h_r_lt_Jb⟩

  -- Überdeckung: [J.a,J.b] ⊆ [J.a,ℓ] ∪ (ℓ,r) ∪ [r,J.b]
  -- Achtung: `∪` ist linksassoziativ: (A ∪ B) ∪ C.
  have cover : segSet J ⊆ segSet J0 ∪ Mid ∪ segSet J1 := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    by_cases hxl : x ≤ ℓ
    · -- x ∈ segSet J0 ⇒ Mitglied im linken Summanden (A ∪ B) des großen ∪
      have hxJ0 : x ∈ segSet J0 := ⟨hxL, hxl⟩
      exact Or.inl (Or.inl hxJ0)
    · have hℓlt : ℓ < x := lt_of_not_ge hxl
      by_cases hxr : x < r
      · -- x ∈ Mid ⇒ Mitglied im rechten Summanden von (A ∪ B)
        have hxMid : x ∈ Mid := ⟨hℓlt, hxr⟩
        exact Or.inl (Or.inr hxMid)
      · -- sonst r ≤ x ⇒ x ∈ segSet J1 ⇒ rechter äußerer Summand
        have hx_ge_r : r ≤ x := le_of_not_gt hxr
        have hxJ1 : x ∈ segSet J1 := ⟨hx_ge_r, hxR⟩
        exact Or.inr hxJ1

  -- Beide Kinder schneiden M (weil ℓ,r ∈ M)
  have touch0 : (segSet J0 ∩ M).Nonempty := by
    refine ⟨ℓ, ?_⟩; constructor
    · exact ⟨le_of_lt hJa_lt_ell, le_rfl⟩
    · exact hℓM
  have touch1 : (segSet J1 ∩ M).Nonempty := by
    refine ⟨r, ?_⟩; constructor
    · exact ⟨le_rfl, le_of_lt h_r_lt_Jb⟩
    · exact hrM

  exact ⟨J0, J1, Mid, sub0, sub1, disj, openMid, midSub, cover, touch0, touch1⟩

end

/-
  -------------------------
  Phase 2: Iteration scaffold
  -------------------------
-/
noncomputable section

namespace Stage

-- Endliche Vereinigungen als Listen-Unions
def segUnion (L : List ClosedSeg) : Set ℝ :=
  {x | ∃ J ∈ L, x ∈ segSet J}

def midUnion (L : List (Set ℝ)) : Set ℝ :=
  {x | ∃ U ∈ L, x ∈ U}

@[simp] lemma mem_segUnion {L : List ClosedSeg} {x : ℝ} :
  x ∈ segUnion L ↔ ∃ J ∈ L, x ∈ segSet J := Iff.rfl

@[simp] lemma mem_midUnion {L : List (Set ℝ)} {x : ℝ} :
  x ∈ midUnion L ↔ ∃ U ∈ L, x ∈ U := Iff.rfl

@[simp] lemma segUnion_nil : segUnion [] = (∅ : Set ℝ) := by
  ext x; simp [segUnion]

@[simp] lemma midUnion_nil : midUnion [] = (∅ : Set ℝ) := by
  ext x; simp [midUnion]

@[simp] lemma segUnion_cons (J : ClosedSeg) (L : List ClosedSeg) :
  segUnion (J :: L) = segSet J ∪ segUnion L := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨K, hKmem, hxK⟩
    rcases (List.mem_cons).1 hKmem with hK | hK
    · subst hK; exact Or.inl hxK
    · exact Or.inr ⟨K, hK, hxK⟩
  · intro hx
    rcases hx with hxJ | hxRest
    · exact ⟨J, by simp, hxJ⟩
    · rcases hxRest with ⟨K, hKmem, hxK⟩
      exact ⟨K, List.mem_cons_of_mem _ hKmem, hxK⟩

@[simp] lemma midUnion_cons (U : Set ℝ) (L : List (Set ℝ)) :
  midUnion (U :: L) = U ∪ midUnion L := by
  ext x; constructor
  · -- → Richtung
    intro hx
    rcases hx with ⟨V, hVmem, hxV⟩
    rcases (List.mem_cons).1 hVmem with hV | hV
    · subst hV
      exact Or.inl hxV
    · exact Or.inr ⟨V, hV, hxV⟩
  · -- ← Richtung
    intro hx
    rcases hx with hxU | hxRest
    · exact ⟨U, by simp, hxU⟩
    · rcases hxRest with ⟨V, hVmem, hxV⟩
      exact ⟨V, List.mem_cons_of_mem _ hVmem, hxV⟩

-- Endliche Vereinigung geschlossener Segmente ist geschlossen
lemma segUnion_closed : ∀ L : List ClosedSeg, IsClosed (segUnion L)
| []      => by simp [segUnion_nil]           -- ← statt: simpa … using …
| (J::L)  => by
    have hJ : IsClosed (segSet J) := segSet_closed J
    have hL : IsClosed (segUnion L) := segUnion_closed L
    simpa [segUnion_cons] using hJ.union hL

-- Wenn alle U in L offen sind, ist die endliche Vereinigung offen.
lemma midUnion_open_of_all_open
    (L : List (Set ℝ))
    (h : ∀ U ∈ L, IsOpen U) :
  IsOpen (midUnion L) := by
  induction L with
  | nil =>
      simp [midUnion_nil]                     -- ← statt: simpa … using …
  | cons U L ih =>
      have hU : IsOpen U := h U (by simp)
      have hL : IsOpen (midUnion L) := ih (by
        intro V hV; exact h V (by simp [hV]))
      simpa [midUnion_cons] using hU.union hL

-- Wenn jedes Segment in Icc xu xo liegt, liegt auch die Vereinigung darin.
lemma segUnion_subset_Icc
    (L : List ClosedSeg) {xu xo : ℝ}
    (h : ∀ J ∈ L, segSet J ⊆ Set.Icc xu xo) :
  segUnion L ⊆ Set.Icc xu xo := by
  intro x hx
  rcases hx with ⟨J, hJmem, hxJ⟩
  exact h J hJmem hxJ

/-- Zustand für die endliche Iteration (fixiert `M`, `xu`, `xo`). -/
structure State (M : Set ℝ) (xu xo : ℝ) where
  segs : List ClosedSeg
  mids : List (Set ℝ)
  -- Invarianten:
  invSegs : ∀ {J}, J ∈ segs → segSet J ⊆ Set.Icc xu xo
  invMids : ∀ {U}, U ∈ mids → IsOpen U

/-- Anfangszustand aus einem Startsegment `J ⊆ [xu,xo]`. -/
def init {M : Set ℝ} {xu xo : ℝ}
    (J : ClosedSeg) (hJsub : segSet J ⊆ Set.Icc xu xo)
  : State M xu xo :=
{ segs := [J],
  mids := [],
  invSegs := by
    intro J' hJ'
    have h' : J' = J := by simpa using hJ'
    simpa [h'] using hJsub,
  invMids := by
    intro U hU
    -- U ∈ [] ist unmöglich
    cases hU
}

/-- Bequeme Folgerungen aus den Invarianten des Zustands. -/
lemma segUnion_subset_Icc_of_state
    {M : Set ℝ} {xu xo : ℝ} (s : State M xu xo) :
  segUnion s.segs ⊆ Set.Icc xu xo :=
  segUnion_subset_Icc s.segs (by
    intro J hJ; exact s.invSegs hJ)

lemma midUnion_open_of_state
    {M : Set ℝ} {xu xo : ℝ} (s : State M xu xo) :
  IsOpen (midUnion s.mids) :=
  midUnion_open_of_all_open s.mids (by
    intro U hU; exact s.invMids hU)

/-- Ein einzelner Verfeinerungsschritt:
    wähle `J ∈ s.segs`, der `K0` trifft, und füge die beiden Kinder sowie das
    Mittelstück hinzu. (Wir lassen `J` in `s.segs` drin – einfach & robust.) -/
def refineOne
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty)
  : State M xu xo := by
  classical
  -- 1) J ⊆ [xu,xo] aus der Invariante
  have hJsub : segSet J ⊆ Set.Icc xu xo := s.invSegs hJmem

  -- 2) split_once liefert ∃ J0 J1 Mid, …  (in Prop)
  --    => wir entpacken mit Classical.choose in Typdaten
  let h := split_once (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo J hJsub hHit
  -- h : ∃ J0, ∃ J1, ∃ Mid, P J0 J1 Mid

  -- Stufe 1: wähle J0
  let J0 : ClosedSeg := Classical.choose h
  let h1 := Classical.choose_spec h
  -- h1 : ∃ J1, ∃ Mid, P J0 J1 Mid

  -- Stufe 2: wähle J1
  let J1 : ClosedSeg := Classical.choose h1
  let h2 := Classical.choose_spec h1
  -- h2 : ∃ Mid, P J0 J1 Mid

  -- Stufe 3: wähle Mid
  let Mid : Set ℝ := Classical.choose h2
  let hprops := Classical.choose_spec h2
  -- hprops :  segSet J0 ⊆ segSet J
  --        ∧  segSet J1 ⊆ segSet J
  --        ∧  Disjoint (segSet J0) (segSet J1)
  --        ∧  IsOpen Mid
  --        ∧  Mid ⊆ Ioo J.a J.b
  --        ∧  segSet J ⊆ segSet J0 ∪ Mid ∪ segSet J1
  --        ∧  (segSet J0 ∩ M).Nonempty
  --        ∧  (segSet J1 ∩ M).Nonempty

  -- 3) einzelne Eigenschaften herausziehen
  have sub0 : segSet J0 ⊆ segSet J := hprops.1
  have sub1 : segSet J1 ⊆ segSet J := hprops.2.1
  have _disj : Disjoint (segSet J0) (segSet J1) := hprops.2.2.1
  have openMid : IsOpen Mid := hprops.2.2.2.1
  have _midSub : Mid ⊆ Set.Ioo J.a J.b := hprops.2.2.2.2.1
  have _cover  : segSet J ⊆ segSet J0 ∪ Mid ∪ segSet J1 := hprops.2.2.2.2.2.1
  have _t0 : (segSet J0 ∩ M).Nonempty := hprops.2.2.2.2.2.2.1
  have _t1 : (segSet J1 ∩ M).Nonempty := hprops.2.2.2.2.2.2.2

  -- 4) neue Listen (wir lassen J in s.segs stehen – einfach & robust)
  let segs' := J0 :: J1 :: s.segs
  let mids' := Mid :: s.mids

  -- 5) Invarianten für neue Segmente (via sub0/sub1 + hJsub)
  have invJ0 : segSet J0 ⊆ Set.Icc xu xo := by
    intro x hx; exact hJsub (sub0 hx)
  have invJ1 : segSet J1 ⊆ Set.Icc xu xo := by
    intro x hx; exact hJsub (sub1 hx)

  -- 6) neuen State bauen
  refine
  { segs := segs',
    mids := mids',
    invSegs := ?_ ,
    invMids := ?_ }

  · -- invSegs' für jedes J' in J0 :: J1 :: s.segs
    intro J' hJ'
    have : J' = J0 ∨ J' = J1 ∨ J' ∈ s.segs := by
      -- Mitgliedschaft in der cons-Liste
      simpa [segs'] using hJ'
    rcases this with h0 | h
    · -- J' = J0
      simpa [h0] using invJ0
    rcases h with h1 | hIn
    · -- J' = J1
      simpa [h1] using invJ1
    · -- J' stammt aus s.segs
      exact s.invSegs hIn

  · -- invMids' für jedes U in Mid :: s.mids
    intro U hU
    have : U = Mid ∨ U ∈ s.mids := by
      simpa [mids'] using hU
    rcases this with hEq | hOld
    · -- U = Mid
      simpa [hEq] using openMid
    · -- U ∈ alte mids
      exact s.invMids hOld
/-
  -------------------------
  Phase 2.1: aktueller Kern des Baus
  --------------------------/

/-- *Kern* des aktuellen Zustands `s`: Punkte im Grundintervall,
    die weder in der anfänglichen offenen Hülle `U0'` noch in einem
    der bisher gesammelten offenen Mittelstücke liegen. -/
def core {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) : Set ℝ :=
  Set.Icc xu xo ∩ (U0' M xu xo ∪ Stage.midUnion s.mids)ᶜ

/-- Zerlegt den *Kern* als Schnitt von `K0` mit dem Komplement der bereits
    gesammelten offenen Mittelstücke.  Äquivalent zu De-Morgan + Assoziativität. -/
lemma core_eq_K0_inter
    {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) :
  core s = K0 M xu xo ∩ (Stage.midUnion s.mids)ᶜ := by
  ext x; constructor
  · intro hx
    -- `simp` entfaltet `core` und `K0` und benutzt De-Morgan sowie
    -- Assoziativität/Kommutativität von `∩`.
    simpa [core, K0, Set.compl_union,
           Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using hx
  · intro hx
    simpa [core, K0, Set.compl_union,
           Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using hx


/-- `core` ist abgeschlossen. -/
lemma isClosed_core'
    {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) :
  IsClosed (core s) := by
  classical
  have hIcc : IsClosed (Set.Icc xu xo) := isClosed_Icc
  have hU0 : IsOpen (U0' M xu xo) := U0'_isOpen M xu xo
  have hMid : IsOpen (Stage.midUnion s.mids) :=
    Stage.midUnion_open_of_state s
  have hopen : IsOpen (U0' M xu xo ∪ Stage.midUnion s.mids) :=
    hU0.union hMid
  have hCompl : IsClosed (U0' M xu xo ∪ Stage.midUnion s.mids)ᶜ :=
    hopen.isClosed_compl
  -- `core s = Icc ∩ (U0' ∪ midUnion)ᶜ`
  simpa [core, Set.inter_assoc, Set.inter_left_comm, Set.inter_right_comm] using
    hIcc.inter hCompl

/-- `core ⊆ Icc`. -/
lemma core_subset_Icc
    {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) :
  core (M := M) (xu := xu) (xo := xo) s ⊆ Set.Icc xu xo := by
  intro x hx
  -- hx : x ∈ Icc xu xo ∩ …
  rcases (by simpa [core] using hx) with ⟨hxIcc, _⟩
  exact hxIcc

/-- `core = K0 ∩ (midUnion)ᶜ` liefert `core ⊆ K0`. -/
lemma core_subset_K0
    {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) :
  core (M := M) (xu := xu) (xo := xo) s ⊆ K0 M xu xo := by
  intro x hx
  have hx' : x ∈ K0 M xu xo ∩ (Stage.midUnion s.mids)ᶜ := by
    simpa [core_eq_K0_inter] using hx
  exact hx'.1


  -- Andernfalls (ohne `core_eq_K0_inter`) ersetze den obigen Block durch:
  -- have hxIcc : x ∈ Set.Icc xu xo := (show x ∈ _ from hx).1
  -- have hxCompl : x ∉ U0' M xu xo ∪ Stage.midUnion s.mids := by
  --   have : x ∈ (U0' M xu xo ∪ Stage.midUnion s.mids)ᶜ := (show x ∈ _ from hx).2
  --   simpa using this
  -- have hxNotU0' : x ∉ U0' M xu xo := by
  --   intro hxU; exact hxCompl (Or.inl hxU)
  -- exact ⟨hxIcc, by simpa using hxNotU0'⟩

-- Hauptlemma: core ⊆ M (benötigt Endpunkte in M, wegen K0 ⊆ M)
lemma core_subset_M
    {M : Set ℝ} {xu xo : ℝ}
    (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : Stage.State M xu xo) :
  core (M := M) (xu := xu) (xo := xo) s ⊆ M := by
  intro x hx
  -- zuerst in K0 fallen …
  have hxK0 : x ∈ K0 M xu xo := (core_subset_K0 (s := s)) hx
  -- … und dann K0 ⊆ M benutzen
  exact (K0_subset_M (M := M) (xu := xu) (xo := xo) hxu hxo) hxK0

end Stage

namespace Stage

/-- `midUnion` wächst, wenn man vorne ein weiteres offenes Stück dazupackt. -/
lemma midUnion_subset_cons (U : Set ℝ) (L : List (Set ℝ)) :
  midUnion L ⊆ midUnion (U :: L) := by
  intro x hx
  have : x ∈ U ∪ midUnion L := Or.inr hx
  simpa [midUnion_cons] using this

/-- Antitonie des *Kerns* in der zweiten Komponente:
    Je größer die offene Vereinigung rechts im Komplement, desto kleiner der Kern. -/
lemma core_antitone_union
    {M : Set ℝ} {xu xo : ℝ} {A B : Set ℝ}
    (hAB : A ⊆ B) :
  (Set.Icc xu xo ∩ (U0' M xu xo ∪ B)ᶜ)
    ⊆ (Set.Icc xu xo ∩ (U0' M xu xo ∪ A)ᶜ) := by
  intro x hx
  rcases hx with ⟨hxIcc, hxCompl⟩
  have hsubset : (U0' M xu xo ∪ A) ⊆ (U0' M xu xo ∪ B) := by
    intro y hy
    rcases hy with hyU0 | hyA
    · exact Or.inl hyU0
    · exact Or.inr (hAB hyA)
  have hcompl := Set.compl_subset_compl.mpr hsubset
  exact ⟨hxIcc, hcompl hxCompl⟩

/-- Spezialfall für Listen: *Kern* nach Kons eines neuen offenen Stücks
    ist Teilmenge des alten *Kerns*. -/
lemma core_mids_cons_subset_noState
    {M : Set ℝ} {xu xo : ℝ} (s : Stage.State M xu xo) (U : Set ℝ) :
  (Set.Icc xu xo ∩ (U0' M xu xo ∪ Stage.midUnion (U :: s.mids))ᶜ)
    ⊆ (Set.Icc xu xo ∩ (U0' M xu xo ∪ Stage.midUnion s.mids)ᶜ) := by
  intro x hx
  have hgrow : Stage.midUnion s.mids ⊆ Stage.midUnion (U :: s.mids) :=
    Stage.midUnion_subset_cons U s.mids
  exact Stage.core_antitone_union (M:=M) (xu:=xu) (xo:=xo) hgrow hx

/-- Im Startzustand ist der *Kern* genau `K0`. -/
@[simp] lemma core_init_eq_K0
    {M : Set ℝ} {xu xo : ℝ}
    (J : ClosedSeg) (hJsub : segSet J ⊆ Set.Icc xu xo) :
  core (M := M) (xu := xu) (xo := xo) (init (M:=M) (xu:=xu) (xo:=xo) J hJsub)
    = K0 M xu xo := by
  simp [core, init, K0, midUnion_nil]

/-- Es gibt in `s` ein Segment, das `K0` trifft. -/
def Hits (M : Set ℝ) (xu xo : ℝ) (s : State M xu xo) : Prop :=
  ∃ J ∈ s.segs, (segSet J ∩ K0 M xu xo).Nonempty

/-- Wie `refineOne`, aber wählt das zu verfeinernde Segment automatisch
    aus einem Existenzzeugnis. -/
noncomputable def refineOnceAuto
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (hSel : Hits M xu xo s)
  : State M xu xo :=
by
  classical
  -- Wähle ein J und die beiden Beweise nicht-konstruktiv aus hSel
  let J : ClosedSeg := Classical.choose hSel
  have hJmem : J ∈ s.segs := (Classical.choose_spec hSel).1
  have hHit  : (segSet J ∩ K0 M xu xo).Nonempty :=
    (Classical.choose_spec hSel).2
  -- Jetzt einfach den einen Schritt ausführen
  exact refineOne (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s J hJmem hHit

/-- Beim einen Schritt `refineOne` wird **genau ein** neues offenes Mittelstück
    vorne an die `mids`-Liste angehängt. Wir brauchen nur die Existenz. -/
lemma exists_cons_mids_refineOne
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  ∃ U, (refineOne (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s J hJmem hHit).mids
        = U :: s.mids := by
  classical
  -- In der Definition von `refineOne` wird `mids' := Mid :: s.mids` gesetzt.
  -- Das gewünschte `U` ist genau dieses `Mid`.
  -- `simp` entfaltet die Definition bis zur gewünschten Gleichheit.
  refine ⟨
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (split_once (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo J (s.invSegs hJmem) hHit))),
    ?_⟩
  -- Jetzt folgt die Gleichheit der Listen rein definitorisch:
  simp [refineOne]

/-- Der Kern wird durch einen `refineOne`-Schritt nur **kleiner**. -/
lemma core_refineOne_subset
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  core (M:=M) (xu:=xu) (xo:=xo)
    (refineOne (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s J hJmem hHit)
    ⊆ core (M:=M) (xu:=xu) (xo:=xo) s := by
  classical
  -- Schreibe die neue `mids`-Liste als `U :: s.mids`
  rcases exists_cons_mids_refineOne (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s J hJmem hHit
    with ⟨U, hU⟩
  -- Reduziere auf die „noState“-Version der Antitonie (reiner Mengenbeweis)
  intro x hx
  have hx' :
      x ∈ (Set.Icc xu xo ∩ (U0' M xu xo ∪ midUnion (U :: s.mids))ᶜ) := by
    simpa [core, hU] using hx
  have hx'' :=
    core_mids_cons_subset_noState (M:=M) (xu:=xu) (xo:=xo) (s:=s) (U:=U) hx'
  simpa [core] using hx''

/-- Der Kern wird auch beim „automatischen“ Schritt nur **kleiner**. -/
lemma core_refineOnceAuto_subset
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo) (hSel : Hits M xu xo s) :
  core (refineOnceAuto (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s hSel) ⊆ core s := by
  classical
  -- Variante A: dsimp + exact
  dsimp [refineOnceAuto]
  exact core_refineOne_subset (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo s
    (Classical.choose hSel)
    ((Classical.choose_spec hSel).1)
    ((Classical.choose_spec hSel).2)

noncomputable def refineTwiceAuto
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (h1 : Hits M xu xo s)
    (h2 : Hits M xu xo (refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1)) :
  State M xu xo :=
  refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo
    (refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1) h2

lemma core_refineTwiceAuto_subset
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (s : State M xu xo)
    (h1 : Hits M xu xo s)
    (h2 : Hits M xu xo (refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1)) :
  core (M := M) (xu := xu) (xo := xo)
       (refineTwiceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1 h2)
    ⊆ core (M := M) (xu := xu) (xo := xo) s := by
  classical
  -- Zustand nach dem ersten Auto-Schritt
  let s1 := refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1
  -- Schritt 2 schrumpft den Kern: core(new) ⊆ core(s1)
  have step2 :
    core (M := M) (xu := xu) (xo := xo)
      (refineOnceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s1 h2)
      ⊆ core (M := M) (xu := xu) (xo := xo) s1 :=
    core_refineOnceAuto_subset (M := M) hM (xu := xu) (xo := xo) hxu hxo s1 h2
  -- Schritt 1 schrumpft den Kern: core(s1) ⊆ core(s)
  have step1 :
    core (M := M) (xu := xu) (xo := xo) s1
      ⊆ core (M := M) (xu := xu) (xo := xo) s :=
    core_refineOnceAuto_subset (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1
  -- Zusammensetzen
  have step2' :
    core (M := M) (xu := xu) (xo := xo)
      (refineTwiceAuto (M := M) hM (xu := xu) (xo := xo) hxu hxo s h1 h2)
      ⊆ core (M := M) (xu := xu) (xo := xo) s1 := by
    simpa [refineTwiceAuto, s1] using step2
  exact subset_trans step2' step1

end  Stage
end
