import Mathlib
import PerfectSubset.PerfectFromSuperdense

noncomputable section
open Set

namespace Stage

/-
  Punkt-schonender Split: Das neue offene Zwischenstück `Mid` enthält `x0` nicht.
-/
lemma split_once_avoiding_point
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ)
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
    (segSet J1 ∩ M).Nonempty ∧
    x0 ∉ Mid := by
  classical
  -- innerer M-Punkt in J
  obtain ⟨z₁, hz₁M, hz₁I⟩ :=
    exists_M_interior_of_seg_intersects_K0 (M:=M) hM (xu:=xu) (xo:=xo)
      hxu hxo J hJsub hHit
  rcases hz₁I with ⟨hz₁L, hz₁R⟩

  -- Falls z₁ = x0, rücke minimal weg
  have hz_exists : ∃ z, z ∈ M ∧ z ∈ Set.Ioo J.a J.b ∧ z ≠ x0 := by
    by_cases hneq : z₁ ≠ x0
    · exact ⟨z₁, hz₁M, ⟨hz₁L, hz₁R⟩, hneq⟩
    · have hposL : 0 < z₁ - J.a := sub_pos.mpr hz₁L
      have hposR : 0 < J.b - z₁ := sub_pos.mpr hz₁R
      let ε₁ : ℝ := min (z₁ - J.a) (J.b - z₁) / 4
      have hε₁pos : 0 < ε₁ := by
        have hminpos : 0 < min (z₁ - J.a) (J.b - z₁) := lt_min hposL hposR
        have : (0 : ℝ) < 4 := by norm_num
        simpa [ε₁] using (div_pos hminpos this)
      rcases exists_left_right_near (M:=M) hM (x:=z₁) (ε:=ε₁) hz₁M hε₁pos with
        ⟨ℓ₁, r₁, hℓ₁M, hr₁M, hℓ₁L, hℓ₁R, hr₁L, hr₁R⟩
      -- J.a < ℓ₁
      have hε₁_le_left_quarter :
          ε₁ ≤ (z₁ - J.a) / 4 := by
        have hmin_le : min (z₁ - J.a) (J.b - z₁) ≤ (z₁ - J.a) :=
          min_le_left _ _
        have h4 : (0 : ℝ) ≤ 4 := by norm_num
        have := div_le_div_of_nonneg_right hmin_le h4
        simpa [ε₁] using this
      have hquarter_left_lt :
          (z₁ - J.a) / 4 < (z₁ - J.a) := by
        have hpos : 0 < z₁ - J.a := sub_pos.mpr hz₁L
        have one_lt_four : (1 : ℝ) < 4 := by norm_num
        simpa using (div_lt_self hpos one_lt_four)
      have hε₁_lt_left : ε₁ < z₁ - J.a :=
        lt_of_le_of_lt hε₁_le_left_quarter hquarter_left_lt
      have hstep : J.a + ε₁ < J.a + (z₁ - J.a) :=
        add_lt_add_left hε₁_lt_left J.a
      have hz_sum : J.a + (z₁ - J.a) = z₁ := by ring
      have hJa_eps_lt_z : J.a + ε₁ < z₁ := by simpa [hz_sum] using hstep
      have hJa_lt_z_minus_eps : J.a < z₁ - ε₁ :=
        (lt_sub_iff_add_lt).mpr hJa_eps_lt_z
      have hJa_lt_ℓ₁ : J.a < ℓ₁ := lt_trans hJa_lt_z_minus_eps hℓ₁L
      -- r₁ < J.b
      have hε₁_le_right_quarter :
          ε₁ ≤ (J.b - z₁) / 4 := by
        have hmin_le : min (z₁ - J.a) (J.b - z₁) ≤ (J.b - z₁) :=
          min_le_right _ _
        have h4 : (0 : ℝ) ≤ 4 := by norm_num
        have := div_le_div_of_nonneg_right hmin_le h4
        simpa [ε₁] using this
      have hquarter_right_lt :
          (J.b - z₁) / 4 < (J.b - z₁) := by
        have hpos : 0 < J.b - z₁ := sub_pos.mpr hz₁R
        have one_lt_four : (1 : ℝ) < 4 := by norm_num
        simpa using (div_lt_self hpos one_lt_four)
      have hε₁_lt_right : ε₁ < J.b - z₁ :=
        lt_of_le_of_lt hε₁_le_right_quarter hquarter_right_lt
      have hstep' : z₁ + ε₁ < (J.b - z₁) + z₁ :=
        by simpa [add_comm] using add_lt_add_right hε₁_lt_right z₁
      have hz_sum' : (J.b - z₁) + z₁ = J.b := by ring
      have hz_plus_eps_lt_b : z₁ + ε₁ < J.b := by simpa [hz_sum'] using hstep'
      have _hr₁_lt_Jb : r₁ < J.b := lt_trans hr₁R hz_plus_eps_lt_b
      -- ℓ₁ ≠ x0 (weil ℓ₁ < z₁ = x0)
      have hEq : z₁ = x0 := by
        classical
        by_contra hne; exact hneq hne
      have hz_ne_x0' : ℓ₁ ≠ x0 := by
        have : ℓ₁ < x0 := by simpa [hEq] using hℓ₁R
        exact ne_of_lt this
      -- und ℓ₁ < J.b via z₁:
      have hℓ₁_lt_Jb : ℓ₁ < J.b := lt_trans hℓ₁R hz₁R
      exact ⟨ℓ₁, hℓ₁M, ⟨hJa_lt_ℓ₁, hℓ₁_lt_Jb⟩, hz_ne_x0'⟩

  rcases hz_exists with ⟨z, hzM, ⟨hzL, hzR⟩, hz_ne_x0⟩

  -- wähle ε ≤ min( Rand/2, |z-x0|/2 )
  let ε₀ : ℝ := (min (z - J.a) (J.b - z)) / 2
  have hε₀pos : 0 < ε₀ := by
    have h1 : 0 < z - J.a := sub_pos.mpr hzL
    have h2 : 0 < J.b - z := sub_pos.mpr hzR
    have hmin : 0 < min (z - J.a) (J.b - z) := lt_min h1 h2
    have : (0 : ℝ) < 2 := by norm_num
    exact div_pos hmin this
  let ε : ℝ := min ε₀ (|z - x0| / 2)
  have hεpos : 0 < ε := by
    have hz_x0_ne : z - x0 ≠ 0 := sub_ne_zero.mpr hz_ne_x0
    have hz_x0_abs_pos : 0 < |z - x0| := abs_pos.mpr hz_x0_ne
    have two_pos : (0 : ℝ) < 2 := by norm_num
    have hpos2 : 0 < |z - x0| / 2 := by
      simpa using (div_pos hz_x0_abs_pos two_pos)
    exact lt_min hε₀pos hpos2
  have hε_le_half_left' : ε ≤ (z - J.a) / 2 := by
    have h1 : ε ≤ ε₀ := min_le_left _ _
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hmin_le : min (z - J.a) (J.b - z) ≤ (z - J.a) := min_le_left _ _
    have hε0_le : ε₀ ≤ (z - J.a) / 2 :=
      (div_le_div_of_nonneg_right hmin_le h2nonneg)
    exact le_trans h1 hε0_le
  have hε_le_half_right : ε ≤ (J.b - z) / 2 := by
    have h1 : ε ≤ ε₀ := min_le_left _ _
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hmin_le : min (z - J.a) (J.b - z) ≤ (J.b - z) := min_le_right _ _
    have hε0_le : ε₀ ≤ (J.b - z) / 2 :=
      (div_le_div_of_nonneg_right hmin_le h2nonneg)
    exact le_trans h1 hε0_le
  have hε_le_half_to_x0 : ε ≤ |z - x0| / 2 := min_le_right _ _
  have hε_le_half_to_x0' : ε ≤ |x0 - z| / 2 := by
    simpa [abs_sub_comm] using hε_le_half_to_x0

  -- Nachbarn um z mit Radius ε
  rcases exists_left_right_near (M:=M) hM (x:=z) (ε:=ε) hzM hεpos with
    ⟨ℓ, r, hℓM, hrM, hℓL, hℓR, hrL, hrR⟩

  -- J.a < ℓ
  have hJa_lt_ℓ : J.a < ℓ := by
    have half_lt_left : (z - J.a) / 2 < (z - J.a) := by
      have hpos : 0 < z - J.a := sub_pos.mpr hzL
      have one_lt_two : (1 : ℝ) < 2 := by norm_num
      simpa using (div_lt_self hpos one_lt_two)
    have hε_lt_left : ε < z - J.a := lt_of_le_of_lt hε_le_half_left' half_lt_left
    have hstep : J.a + ε < J.a + (z - J.a) := add_lt_add_left hε_lt_left J.a
    have hz_sum : J.a + (z - J.a) = z := by ring
    have hJa_eps_lt_z : J.a + ε < z := by simpa [hz_sum] using hstep
    have hJa_lt_z_minus_eps : J.a < z - ε :=
      (lt_sub_iff_add_lt).mpr hJa_eps_lt_z
    exact lt_trans hJa_lt_z_minus_eps hℓL

  -- r < J.b
  have hr_lt_Jb : r < J.b := by
    have half_lt_right : (J.b - z) / 2 < (J.b - z) := by
      have hpos : 0 < J.b - z := sub_pos.mpr hzR
      have one_lt_two : (1 : ℝ) < 2 := by norm_num
      simpa using (div_lt_self hpos one_lt_two)
    have hε_lt_right : ε < J.b - z :=
      lt_of_le_of_lt hε_le_half_right half_lt_right
    have hstep : z + ε < (J.b - z) + z := by
      simpa [add_comm] using add_lt_add_right hε_lt_right z
    have hz_sum' : (J.b - z) + z = J.b := by ring
    have hz_plus_eps_lt_b : z + ε < J.b := by simpa [hz_sum'] using hstep
    exact lt_trans hrR hz_plus_eps_lt_b

  -- Kinder & Mittelstück
  let J0 : ClosedSeg := { a := J.a, b := ℓ, hlt := hJa_lt_ℓ }
  let J1 : ClosedSeg := { a := r, b := J.b, hlt := hr_lt_Jb }
  let Mid : Set ℝ := Set.Ioo ℓ r

  -- Standard-Eigenschaften
  have sub0 : segSet J0 ⊆ segSet J := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    have hℓ_le_Jb : ℓ ≤ J.b := le_of_lt (lt_trans hℓR hzR)
    exact ⟨hxL, le_trans hxR hℓ_le_Jb⟩
  have sub1 : segSet J1 ⊆ segSet J := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    have hz_le_x : z ≤ x := le_trans (le_of_lt hrL) hxL
    have hJa_lt_x : J.a < x := lt_of_lt_of_le hzL hz_le_x
    exact ⟨le_of_lt hJa_lt_x, hxR⟩
  have disj : Disjoint (segSet J0) (segSet J1) := by
    have hsep : ℓ < r := lt_trans hℓR hrL
    refine disjoint_left.mpr ?_
    intro x hx0 hx1
    rcases hx0 with ⟨hx0L, hx0R⟩
    rcases hx1 with ⟨hx1L, hx1R⟩
    have : r ≤ ℓ := le_trans hx1L hx0R
    exact (not_le_of_gt hsep) this
  have openMid : IsOpen Mid := isOpen_Ioo
  have midSub : Mid ⊆ Set.Ioo J.a J.b := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    exact ⟨lt_trans hJa_lt_ℓ hxL, lt_trans hxR hr_lt_Jb⟩
  have cover : segSet J ⊆ segSet J0 ∪ Mid ∪ segSet J1 := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    by_cases hxl : x ≤ ℓ
    · exact Or.inl (Or.inl ⟨hxL, hxl⟩)
    · have hℓlt : ℓ < x := lt_of_not_ge hxl
      by_cases hxr : x < r
      · exact Or.inl (Or.inr ⟨hℓlt, hxr⟩)
      · have hx_ge_r : r ≤ x := le_of_not_gt hxr
        exact Or.inr ⟨hx_ge_r, hxR⟩
  have touch0 : (segSet J0 ∩ M).Nonempty := by
    refine ⟨ℓ, ?_⟩; constructor
    · exact ⟨le_of_lt hJa_lt_ℓ, le_rfl⟩
    · exact hℓM
  have touch1 : (segSet J1 ∩ M).Nonempty := by
    refine ⟨r, ?_⟩; constructor
    · exact ⟨le_rfl, le_of_lt hr_lt_Jb⟩
    · exact hrM

  -- x0 ∉ Mid über Fensterabschätzung
  have Mid_subset_window : Mid ⊆ Set.Ioo (z - ε) (z + ε) := by
    intro x hx; rcases hx with ⟨hxL, hxR⟩
    exact ⟨lt_trans hℓL hxL, lt_trans hxR hrR⟩
  have x0_not_window : x0 ∉ Set.Ioo (z - ε) (z + ε) := by
    intro hx
    have h1 : -ε < x0 - z := by
      have : -ε + z < x0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx.1
      exact (lt_sub_iff_add_lt).mpr this
    have h2 : x0 - z < ε := by
      have : x0 < ε + z := by simpa [add_comm] using hx.2
      exact (sub_lt_iff_lt_add).mpr this
    have habs : |x0 - z| < ε := abs_lt.mpr ⟨h1, h2⟩
    have hlt : |x0 - z| < |x0 - z| / 2 :=
      lt_of_lt_of_le habs hε_le_half_to_x0'
    have hle : |x0 - z| / 2 ≤ |x0 - z| := by
      have hnn : 0 ≤ |x0 - z| := abs_nonneg _
      have : (1 : ℝ) ≤ 2 := by norm_num
      exact div_le_self hnn this
    have habsFalse : ¬ |x0 - z| < |x0 - z| := lt_irrefl _
    exact habsFalse (lt_of_lt_of_le hlt hle)
  have notin : x0 ∉ Mid := fun hx => x0_not_window (Mid_subset_window hx)

  exact ⟨J0, J1, Mid, sub0, sub1, disj, openMid, midSub, cover, touch0, touch1, notin⟩


/-!
  Ein Schritt der Verfeinerung, der `Mid` so wählt, dass `x0` nicht hinein fällt.
  (mit `Classical.choose` statt `rcases`, um Large-Elim zu vermeiden)
-/
def refineOneKeep
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty)
  : State M xu xo := by
  classical
  have hJsub : segSet J ⊆ Set.Icc xu xo := s.invSegs hJmem
  let h := split_once_avoiding_point (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 J hJsub hHit
  let J0 : ClosedSeg := Classical.choose h
  let h1 := Classical.choose_spec h
  let J1 : ClosedSeg := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let Mid : Set ℝ := Classical.choose h2
  let hprops := Classical.choose_spec h2
  have sub0 : segSet J0 ⊆ segSet J := hprops.1
  have sub1 : segSet J1 ⊆ segSet J := hprops.2.1
  have openMid : IsOpen Mid := hprops.2.2.2.1
  let segs' := J0 :: J1 :: s.segs
  let mids' := Mid :: s.mids
  have invJ0 : segSet J0 ⊆ Set.Icc xu xo := by intro x hx; exact hJsub (sub0 hx)
  have invJ1 : segSet J1 ⊆ Set.Icc xu xo := by intro x hx; exact hJsub (sub1 hx)
  refine { segs := segs', mids := mids', invSegs := ?_, invMids := ?_ }
  · intro J' hJ'
    have : J' = J0 ∨ J' = J1 ∨ J' ∈ s.segs := by simpa [segs'] using hJ'
    rcases this with h0 | h
    · simpa [h0] using invJ0
    rcases h with h1' | hIn
    · simpa [h1'] using invJ1
    · exact s.invSegs hIn
  · intro U hU
    have : U = Mid ∨ U ∈ s.mids := by simpa [mids'] using hU
    rcases this with hEq | hOld
    · simpa [hEq] using openMid
    · exact s.invMids hOld


/-- Hilfslemma: Die neue `mids`-Liste beginnt mit dem frisch gewählten `Mid`. -/
lemma exists_cons_mids_refineOneKeep
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty) :
  ∃ U,
    (refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit).mids
      = U :: s.mids
    ∧ x0 ∉ U := by
  classical
  -- einmalig wählen (wie oben)
  have hJsub : segSet J ⊆ Set.Icc xu xo := s.invSegs hJmem
  let h := split_once_avoiding_point (M:=M) hM (xu:=xu) (xo:=xo)
              hxu hxo x0 J hJsub hHit
  let J0 : ClosedSeg := Classical.choose h
  let h1 := Classical.choose_spec h
  let J1 : ClosedSeg := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let Mid : Set ℝ := Classical.choose h2
  rcases (Classical.choose_spec h2) with
    ⟨_sub0, _sub1, _disj, _openMid, _midSub, _cover, _t0, _t1, notin⟩
  have mids_eq :
      (refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit).mids
        = Mid :: s.mids := by
    simp [refineOneKeep, Mid]
  exact ⟨Mid, mids_eq, notin⟩


/-- `x0` bleibt im Kern nach einem `refineOneKeep`-Schritt. -/
lemma core_preserved_refineOneKeep
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ)
    (s : State M xu xo)
    (J : ClosedSeg) (hJmem : J ∈ s.segs)
    (hHit : (segSet J ∩ K0 M xu xo).Nonempty)
    (hx0Core : x0 ∈ core (M := M) (xu := xu) (xo := xo) s) :
  x0 ∈ core (M := M) (xu := xu) (xo := xo)
        (refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit) := by
  classical
  -- Zerlege `hx0Core` explizit in Konjunktionsbestandteile
  have hxParts :
      (xu ≤ x0 ∧ x0 ≤ xo) ∧ x0 ∉ U0' M xu xo ∧ ∀ U ∈ s.mids, x0 ∉ U := by
    simpa [core] using hx0Core
  have hxNotU0   : x0 ∉ U0' M xu xo := hxParts.2.1
  have hxNotAll  : ∀ U ∈ s.mids, x0 ∉ U := hxParts.2.2

  -- Nimm das erste neue Mid aus `refineOneKeep` als `U0`
  rcases exists_cons_mids_refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo)
      hxu hxo x0 s J hJmem hHit with ⟨U0, hMids, hNotInU0⟩

  -- Baue die ∀-Aussage über die *neue* Mid-Liste ohne `refineOneKeep` zu entfalten
  have hforallNew :
      ∀ U ∈ (refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit).mids,
        x0 ∉ U := by
    intro U hU
    -- durch `hMids : new.mids = U0 :: s.mids`
    have : U = U0 ∨ U ∈ s.mids := by
      simpa [hMids] using hU
    cases this with
    | inl h => simpa [h] using hNotInU0
    | inr h => exact hxNotAll U h

  -- Ziel hat genau die `core`-Form; wichtig: *nicht* `refineOneKeep` entfalten
  simpa [core] using
    And.intro hxParts.1 (And.intro hxNotU0 hforallNew)

/-- Automatischer Schritt mit Schonungspunkt `x0`. -/
noncomputable def refineOnceAutoKeep
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ)
    (s : State M xu xo)
    (hSel : Hits M xu xo s) :
  State M xu xo := by
  classical
  let J : ClosedSeg := Classical.choose hSel
  have hJmem : J ∈ s.segs := (Classical.choose_spec hSel).1
  have hHit  : (segSet J ∩ K0 M xu xo).Nonempty :=
    (Classical.choose_spec hSel).2
  exact refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s J hJmem hHit


/-- Der Kern wird vom schonenden Auto-Schritt bzgl. `x0` bewahrt. -/
lemma core_refineOnceAutoKeep_preserves
    {M : Set ℝ} (hM : TwoSidedSuperdense M)
    {xu xo : ℝ} (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (s : State M xu xo) (hSel : Hits M xu xo s)
    (hx0Core : x0 ∈ core (M := M) (xu := xu) (xo := xo) s) :
  x0 ∈ core (M := M) (xu := xu) (xo := xo)
        (refineOnceAutoKeep (M:=M) hM (xu:=xu) (xo:=xo) hxu hxo x0 s hSel) := by
  classical
  dsimp [refineOnceAutoKeep]
  exact core_preserved_refineOneKeep (M:=M) hM (xu:=xu) (xo:=xo)
    hxu hxo x0 s
    (Classical.choose hSel) ((Classical.choose_spec hSel).1)
    ((Classical.choose_spec hSel).2) hx0Core


/-- n-fache Verfeinerung mit Schonungspunkt `x0`. -/
def refineNKeep
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo) :
    Nat → State M xu xo → State M xu xo
  | 0,     s => s
  | n+1,   s =>
      let s' := refineNKeep hM hxu hxo x0 sel n s
      refineOnceAutoKeep hM hxu hxo x0 s' (sel s')

/-- Die ω-stufige Kernmenge der schonenden Iteration. -/
def KωKeep
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo)
    (s : State M xu xo) : Set ℝ :=
  ⋂ n : ℕ,
    core (M := M) (xu := xu) (xo := xo)
         (refineNKeep (M := M) (xu := xu) (xo := xo)
            hM hxu hxo x0 sel n s)

/-- Persistenz: Ist `x0 ∈ core s`, so bleibt `x0` in allen
    `core (refineNKeep … n s)`. -/
lemma mem_core_refineNKeep_of_core
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo)
    (s : State M xu xo)
    (hx0Core : x0 ∈ core (M := M) (xu := xu) (xo := xo) s) :
  ∀ n, x0 ∈ core (M := M) (xu := xu) (xo := xo)
         (refineNKeep (M := M) (xu := xu) (xo := xo)
            hM hxu hxo x0 sel n s) := by
  refine Nat.rec ?base ?step
  · simpa [refineNKeep] using hx0Core
  · intro n ih
    have hx_core_n := ih
    have hx_core_succ :
        x0 ∈ core (M := M) (xu := xu) (xo := xo)
               (refineOnceAutoKeep (M := M) (xu := xu) (xo := xo)
                 hM hxu hxo x0
                 (refineNKeep (M := M) (xu := xu) (xo := xo)
                   hM hxu hxo x0 sel n s)
                 (sel (refineNKeep (M := M) (xu := xu) (xo := xo)
                   hM hxu hxo x0 sel n s))) := by
      exact core_refineOnceAutoKeep_preserves (M := M) (xu := xu) (xo := xo)
        hM hxu hxo x0
        (refineNKeep (M := M) (xu := xu) (xo := xo)
          hM hxu hxo x0 sel n s)
        (sel (refineNKeep (M := M) (xu := xu) (xo := xo)
          hM hxu hxo x0 sel n s))
        hx_core_n
    simpa [refineNKeep] using hx_core_succ

/-- **Nicht-Leerheit** der `KωKeep`-Menge (aus einem Startsegment). -/
lemma KωKeep_nonempty_of_preserved_point_from_init
    {M : Set ℝ} {xu xo : ℝ}
    (hM : TwoSidedSuperdense M) (hxu : xu ∈ M) (hxo : xo ∈ M)
    (x0 : ℝ) (sel : Selector M xu xo)
    (J : ClosedSeg) (hJsub : segSet J ⊆ Set.Icc xu xo)
    (hx0K0 : x0 ∈ K0 M xu xo) :
  (KωKeep (M := M) (xu := xu) (xo := xo) hM hxu hxo x0 sel
      (init (M := M) (xu := xu) (xo := xo) J hJsub)).Nonempty := by
  classical
  let s0 := init (M := M) (xu := xu) (xo := xo) J hJsub
  have hcore_eq : core (M := M) (xu := xu) (xo := xo) s0 = K0 M xu xo := by
    simp [s0, core_init_eq_K0 (M := M) (xu := xu) (xo := xo) (J := J) hJsub]
  have hx0_core : x0 ∈ core (M := M) (xu := xu) (xo := xo) s0 := by
    simpa [← hcore_eq] using hx0K0
  have hx_all :
      ∀ n,
        x0 ∈ core (M := M) (xu := xu) (xo := xo)
          (refineNKeep (M := M) (xu := xu) (xo := xo)
            hM hxu hxo x0 sel n s0) := by
    intro n
    exact mem_core_refineNKeep_of_core (M := M) (xu := xu) (xo := xo)
      hM hxu hxo x0 sel s0 hx0_core n
  refine ⟨x0, ?_⟩
  simpa [KωKeep] using Set.mem_iInter.mpr hx_all

end Stage
