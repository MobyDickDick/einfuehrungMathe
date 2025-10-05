import Mathlib

open Set Metric

noncomputable section
namespace SumKappa

/-- Grundintervall. -/
def I : Set ℝ := Icc (0 : ℝ) 1

/-- Kugel relativ zu `I`. -/
def ballI (x r : ℝ) : Set ℝ := ball x r ∩ I

/-
  Naive Axiome für ein "Längen-κ" auf `I`:
  * Monotonie, Subadditivität, Nichtnegativität
  * κ(I) = 1
  * jede relative Kugel hat positives Maß
  * Zerlegung von I entlang einer relativen Kugel auf Wertebene
-/
class KappaOnI (κ : Set ℝ → ℝ) : Prop where
  mono     : ∀ {A B}, A ⊆ B → κ A ≤ κ B
  subadd   : ∀ {A B}, κ (A ∪ B) ≤ κ A + κ B
  nonneg   : ∀ {A}, 0 ≤ κ A
  I_one    : κ I = 1
  ball_pos : ∀ {x r}, 0 < r → 0 < κ (ballI x r)
  split_I  : ∀ {x r}, 0 < r → κ (I \ ballI x r) = 1 - κ (ballI x r)

variable {κ : Set ℝ → ℝ} [KappaOnI κ]

/-- Deine fünf Mengen (nur M₂, M₄ und M₅ werden gleich aktiv genutzt). -/
def M1 (M : Set ℝ) : Set ℝ :=
  {x | ∃ ε > 0, κ (ballI x ε ∩ M) = 0}

def M2 (M : Set ℝ) : Set ℝ :=
  {x | ∀ ε > 0, 0 < κ (ballI x ε ∩ M)}

def M3 (M : Set ℝ) : Set ℝ :=
  {x | ∃ ε > 0, κ (ballI x ε ∩ (I \ M)) = 0}

def M4 (M : Set ℝ) : Set ℝ :=
  {x | ∀ ε > 0, 0 < κ (ballI x ε ∩ (I \ M))}

def M5 (M : Set ℝ) : Set ℝ := M2 (κ := κ) M ∩ M4 (κ := κ) M

/-- (Hilfs-)Zerlegungsinklusion: für `A ⊆ I`
    deckt `(ballI ∩ A) ∪ (A ∩ (I \ ballI))` die Menge `A`. -/
lemma subset_split_ballI {A : Set ℝ} (hA : A ⊆ I) (x r : ℝ) :
    A ⊆ (ballI x r ∩ A) ∪ (A ∩ (I \ ballI x r)) := by
  intro y hyA
  by_cases hyB : y ∈ ballI x r
  · exact Or.inl ⟨hyB, hyA⟩
  · have hyI : y ∈ I := hA hyA
    exact Or.inr ⟨hyA, ⟨hyI, hyB⟩⟩

/-- `M1` ist offen. -/
lemma isOpen_M1 (M : Set ℝ) : IsOpen (M1 (κ := κ) M) := by
  classical
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  rcases hx with ⟨ε, hεpos, hzero⟩
  refine ⟨ball x (ε/2), ?subset, isOpen_ball, ?mem⟩
  · -- subset: ball x (ε/2) ⊆ M1 M
    intro y hy
    -- Inclusion: ballI y (ε/2) ⊆ ballI x ε
    have hsub : ballI y (ε/2) ⊆ ballI x ε := by
      intro z hz
      rcases hz with ⟨hzy, hzI⟩
      have hyx : dist y x < ε/2 := by simpa [dist_comm] using hy
      have hzx : dist z x < ε := by
        have tri : dist z x ≤ dist z y + dist y x := by
          simpa [dist_comm] using dist_triangle z y x
        have : dist z x < (ε/2) + (ε/2) :=
          lt_of_le_of_lt tri (add_lt_add hzy hyx)
        simpa using this
      exact ⟨hzx, hzI⟩
    -- Monotonie + hzero ⇒ κ(ballI y (ε/2) ∩ M) = 0
    have hsubsetInt : ballI y (ε/2) ∩ M ⊆ ballI x ε ∩ M := by
      intro z hz; exact ⟨hsub hz.1, hz.2⟩
    have hle' : κ (ballI y (ε/2) ∩ M) ≤ κ (ballI x ε ∩ M) :=
      KappaOnI.mono (κ := κ) hsubsetInt
    have hle0 : κ (ballI y (ε/2) ∩ M) ≤ 0 := by
      simpa [hzero] using hle'
    have hnn : 0 ≤ κ (ballI y (ε/2) ∩ M) :=
      KappaOnI.nonneg (κ := κ) (A := ballI y (ε/2) ∩ M)
    have hzero' : κ (ballI y (ε/2) ∩ M) = 0 := le_antisymm hle0 hnn
    exact ⟨ε/2, by simpa using half_pos hεpos, by simp [hzero']⟩
  · -- x ∈ ball x (ε/2)
    exact mem_ball_self (half_pos hεpos)



/-- `M2` ist abgeschlossen (Komplement von `M1`). -/
lemma isClosed_M2 (M : Set ℝ) : IsClosed (M2 (κ := κ) M) := by
  classical
  -- (M2)ᶜ = M1
  have hcompl : (M2 (κ := κ) M)ᶜ = M1 (κ := κ) M := by
    ext x; constructor
    · intro hx
      have : ∃ ε > 0, ¬ 0 < κ (ballI x ε ∩ M) := by
        simpa [M2] using (Classical.not_forall.mp hx)
      rcases this with ⟨ε, hεpos, hnotpos⟩
      have hle : κ (ballI x ε ∩ M) ≤ 0 := le_of_not_gt hnotpos
      have hnn : 0 ≤ κ (ballI x ε ∩ M) :=
        KappaOnI.nonneg (κ := κ) (A := ballI x ε ∩ M)
      have hzero : κ (ballI x ε ∩ M) = 0 := le_antisymm hle hnn
      exact ⟨ε, hεpos, hzero⟩
    · intro hx
      rcases hx with ⟨ε, hεpos, hzero⟩
      have : ¬ 0 < κ (ballI x ε ∩ M) := by simp [hzero]
      have : ¬ (∀ ε > 0, 0 < κ (ballI x ε ∩ M)) := by
        intro hall; exact this (hall ε hεpos)
      simpa [M2] using this
  -- daraus: M2 = (M1)ᶜ
  have hEq : M2 (κ := κ) M = (M1 (κ := κ) M)ᶜ := by
    have := congrArg compl hcompl
    simpa [compl_compl] using this
  simpa [hEq] using (isOpen_M1 (κ := κ) M).isClosed_compl

/-- Analog: `M3` ist offen. -/
lemma isOpen_M3 (M : Set ℝ) : IsOpen (M3 (κ := κ) M) := by
  classical
  simpa [M3, inter_left_comm, inter_assoc] using
    isOpen_M1 (κ := κ) (I \ M)

/-- Analog: `M4` ist geschlossen. -/
lemma isClosed_M4 (M : Set ℝ) : IsClosed (M4 (κ := κ) M) := by
  classical
  -- (M4)ᶜ = M3
  have hcompl : (M4 (κ := κ) M)ᶜ = M3 (κ := κ) M := by
    ext x; constructor
    · intro hx
      have : ∃ ε > 0, ¬ 0 < κ (ballI x ε ∩ (I \ M)) := by
        simpa [M4] using (Classical.not_forall.mp hx)
      rcases this with ⟨ε, hεpos, hnotpos⟩
      have hle : κ (ballI x ε ∩ (I \ M)) ≤ 0 := le_of_not_gt hnotpos
      have hnn : 0 ≤ κ (ballI x ε ∩ (I \ M)) :=
        KappaOnI.nonneg (κ := κ) (A := ballI x ε ∩ (I \ M))
      have hzero : κ (ballI x ε ∩ (I \ M)) = 0 := le_antisymm hle hnn
      exact ⟨ε, hεpos, hzero⟩
    · intro hx
      rcases hx with ⟨ε, hεpos, hzero⟩
      have : ¬ 0 < κ (ballI x ε ∩ (I \ M)) := by simp [hzero]
      have : ¬ (∀ ε > 0, 0 < κ (ballI x ε ∩ (I \ M))) := by
        intro hall; exact this (hall ε hεpos)
      simpa [M4] using this
  have hEq : M4 (κ := κ) M = (M3 (κ := κ) M)ᶜ := by
    have := congrArg compl hcompl
    simpa [compl_compl] using this
  simpa [hEq] using (isOpen_M3 (κ := κ) M).isClosed_compl

/-- Aus `κ(M)=1` und `M⊆I` folgt: `I ⊆ M2(M)` (jede Nachbarschaft trifft M mit positivem κ). -/
lemma subset_M2_of_full (M : Set ℝ) (hMsub : M ⊆ I) (hM : κ M = 1) :
    I ⊆ M2 (κ := κ) M := by
  intro x hxI ε hε
  by_contra hpos
  have hle : κ (ballI x ε ∩ M) ≤ 0 := le_of_not_gt hpos
  have hnn : 0 ≤ κ (ballI x ε ∩ M) := KappaOnI.nonneg (κ := κ)
  have hzero : κ (ballI x ε ∩ M) = 0 := le_antisymm hle hnn
  -- Decke M mit (ballI∩M) ∪ (M ∩ (I \ ballI))
  have hcover : M ⊆ (ballI x ε ∩ M) ∪ (M ∩ (I \ ballI x ε)) :=
    subset_split_ballI hMsub x ε
  have hκcover :
      κ M ≤ κ ((ballI x ε ∩ M) ∪ (M ∩ (I \ ballI x ε))) :=
    KappaOnI.mono (κ := κ) hcover
  have hsubadd :
      κ ((ballI x ε ∩ M) ∪ (M ∩ (I \ ballI x ε)))
        ≤ κ (ballI x ε ∩ M) + κ (M ∩ (I \ ballI x ε)) :=
    KappaOnI.subadd (κ := κ)
  have h1 := hκcover.trans hsubadd
  have h2 : κ (M ∩ (I \ ballI x ε)) ≤ κ (I \ ballI x ε) :=
    KappaOnI.mono (κ := κ) (by intro y hy; exact hy.2)
  have hsumLe : κ M ≤ 0 + κ (I \ ballI x ε) := by
    simpa [hzero, zero_add] using (le_trans h1 (add_le_add le_rfl h2))
  -- Schritt zu κ(ballI) ≤ 0
  have h1' : 1 ≤ κ (I \ ballI x ε) := by simpa [hM] using hsumLe
  have h2' : 1 ≤ 1 - κ (ballI x ε) := by
    simpa [KappaOnI.split_I (κ := κ) (x := x) (r := ε) hε] using h1'
  have : κ (ballI x ε) ≤ 0 := by linarith
  have hposBall := KappaOnI.ball_pos (κ := κ) (x := x) (r := ε) hε
  exact (not_lt_of_ge this) hposBall

/-- Aus `κ(I\M)=1` folgt: `I ⊆ M4(M)`. -/
lemma subset_M4_of_full_compl (M : Set ℝ) (_hMsub : M ⊆ I) (hMc : κ (I \ M) = 1) :
    I ⊆ M4 (κ := κ) M := by
  intro x hxI ε hε
  by_contra hpos
  have hle : κ (ballI x ε ∩ (I \ M)) ≤ 0 := le_of_not_gt hpos
  have hnn : 0 ≤ κ (ballI x ε ∩ (I \ M)) := KappaOnI.nonneg (κ := κ)
  have hzero : κ (ballI x ε ∩ (I \ M)) = 0 := le_antisymm hle hnn
  have hA : (I \ M) ⊆ I := by intro y hy; exact hy.1
  have hcover : (I \ M)
      ⊆ (ballI x ε ∩ (I \ M)) ∪ ((I \ M) ∩ (I \ ballI x ε)) :=
    subset_split_ballI hA x ε
  have hκcover :
      κ (I \ M)
        ≤ κ ((ballI x ε ∩ (I \ M)) ∪ ((I \ M) ∩ (I \ ballI x ε))) :=
    KappaOnI.mono (κ := κ) hcover
  have hsubadd :
      κ ((ballI x ε ∩ (I \ M)) ∪ ((I \ M) ∩ (I \ ballI x ε)))
        ≤ κ (ballI x ε ∩ (I \ M)) + κ ((I \ M) ∩ (I \ ballI x ε)) :=
    KappaOnI.subadd (κ := κ)
  have h1 := hκcover.trans hsubadd
  have h2 : κ ((I \ M) ∩ (I \ ballI x ε)) ≤ κ (I \ ballI x ε) :=
    KappaOnI.mono (κ := κ) (by intro y hy; exact hy.2)
  have hsumLe : κ (I \ M) ≤ 0 + κ (I \ ballI x ε) := by
    simpa [hzero, zero_add] using (le_trans h1 (add_le_add le_rfl h2))
  -- Schritt zu κ(ballI) ≤ 0
  have h1' : 1 ≤ κ (I \ ballI x ε) := by simpa [hMc] using hsumLe
  have h2' : 1 ≤ 1 - κ (ballI x ε) := by
    simpa [KappaOnI.split_I (κ := κ) (x := x) (r := ε) hε] using h1'
  have : κ (ballI x ε) ≤ 0 := by linarith
  have hposBall := KappaOnI.ball_pos (κ := κ) (x := x) (r := ε) hε
  exact (not_lt_of_ge this) hposBall

/-- Aus `κ(M) + κ(I\M) = 2` und Monotonie folgt `κ(M)=1` und `κ(I\M)=1`. -/
lemma both_full_of_sum_two (M : Set ℝ) (hMsub : M ⊆ I)
    (hsum : κ M + κ (I \ M) = 2) :
    κ M = 1 ∧ κ (I \ M) = 1 := by
  have hM_le : κ M ≤ 1 := by
    simpa [KappaOnI.I_one (κ := κ)]
      using (KappaOnI.mono (κ := κ) (A := M) (B := I) hMsub)
  have hMc_le : κ (I \ M) ≤ 1 := by
    simpa [KappaOnI.I_one (κ := κ)]
      using (KappaOnI.mono (κ := κ) (A := I \ M) (B := I) (by intro x hx; exact hx.1))
  have hM1 : κ M = 1 := by linarith [hM_le, hMc_le, hsum]
  have hMc1 : κ (I \ M) = 1 := by linarith [hM_le, hMc_le, hsum, hM1]
  exact ⟨hM1, hMc1⟩

/-- Zentraler Schritt: aus der Summenannahme folgt `I ⊆ M5(M)`. -/
lemma I_subset_M5_of_sum_two (M : Set ℝ) (hMsub : M ⊆ I)
    (hsum : κ M + κ (I \ M) = 2) :
    I ⊆ M5 (κ := κ) M := by
  obtain ⟨hM, hMc⟩ := both_full_of_sum_two (κ := κ) M hMsub hsum
  intro x hxI
  exact ⟨subset_M2_of_full (κ := κ) M hMsub hM hxI,
         subset_M4_of_full_compl (κ := κ) M hMsub hMc hxI⟩

/-- `M2` und `M4` sind abgeschlossen ⇒ `M5` ist abgeschlossen ⇒ `I ∩ M5` kompakt. -/
lemma isCompact_I_inter_M5 (M : Set ℝ) :
    IsCompact (I ∩ M5 (κ := κ) M) := by
  have hIc : IsCompact I := isCompact_Icc
  have hM2closed : IsClosed (M2 (κ := κ) M) := isClosed_M2 (κ := κ) M
  have hM4closed : IsClosed (M4 (κ := κ) M) := isClosed_M4 (κ := κ) M
  have hM5closed : IsClosed (M5 (κ := κ) M) := hM2closed.inter hM4closed
  simpa [inter_assoc, inter_left_comm] using hIc.inter_right hM5closed

/-- Konsequenz deiner Summenannahme: relativ zu `I` gilt `I ∩ M5 = I`. -/
lemma I_inter_M5_eq_I_of_sum_two (M : Set ℝ) (hMsub : M ⊆ I)
    (hsum : κ M + κ (I \ M) = 2) :
    I ∩ M5 (κ := κ) M = I := by
  apply le_antisymm
  · exact inter_subset_left
  · intro x hxI
    exact ⟨hxI, I_subset_M5_of_sum_two (κ := κ) M hMsub hsum hxI⟩


/-- Aus `κ(M)+κ(I \ M)=2` folgt sogar `(0,1) ⊆ M5(M)` (weil schon `I ⊆ M5(M)`). -/
lemma Ioo_subset_M5_of_sum_two
    (M : Set ℝ) (hMsub : M ⊆ I)
    (hsum : κ M + κ (I \ M) = 2) :
    Ioo (0:ℝ) 1 ⊆ M5 (κ := κ) M := by
  -- wir hatten bereits: `I ⊆ M5`
  have hI : I ⊆ M5 (κ := κ) M :=
    I_subset_M5_of_sum_two (κ := κ) M hMsub hsum
  -- also auch `(0,1) ⊆ I ⊆ M5`
  exact fun x hx => hI (Ioo_subset_Icc_self hx)

/-- **Kontraposition**: existiert ein Punkt im Inneren, der nicht in `M5` liegt,
    dann ist die Summe echt kleiner als 2. -/
lemma sum_lt_two_of_exists_notin_M5_interior
    (M : Set ℝ) (hMsub : M ⊆ I)
    (hx : ∃ x, x ∈ Ioo (0 : ℝ) 1 ∧ x ∉ M5 (κ := κ) M) :
    κ M + κ (I \ M) < 2 := by
  -- obere Schranke: jede der beiden Massen ≤ 1
  have hM_le : κ M ≤ 1 := by
    simpa [KappaOnI.I_one (κ := κ)]
      using (KappaOnI.mono (κ := κ) (A := M) (B := I) hMsub)
  have hMc_le : κ (I \ M) ≤ 1 := by
    simpa [KappaOnI.I_one (κ := κ)]
      using (KappaOnI.mono (κ := κ) (A := I \ M) (B := I) (by intro x hx; exact hx.1))
  have hsum_le' : κ M + κ (I \ M) ≤ (1 : ℝ) + 1 :=
    add_le_add hM_le hMc_le
  have hsum_le : κ M + κ (I \ M) ≤ 2 := by
    have h : (1 : ℝ) + 1 = 2 := by norm_num
    simpa [h] using hsum_le'
  -- zeige: Summe ist nicht = 2 (sonst Widerspruch zu `hx`)
  have hne : κ M + κ (I \ M) ≠ 2 := by
    intro hEq
    -- aus Summe=2 folgt `I ⊆ M5`
    have hI : I ⊆ M5 (κ := κ) M :=
      I_subset_M5_of_sum_two (κ := κ) M hMsub hEq
    rcases hx with ⟨x, hxIoo, hxnot⟩
    have hxI : x ∈ I := Ioo_subset_Icc_self hxIoo
    have : x ∈ M5 (κ := κ) M := hI hxI
    exact hxnot this
  -- aus `≤` und `≠` folgt `<`
  exact lt_of_le_of_ne hsum_le hne
/-- Aus den Axiomen folgt bereits: κ(∅) = 0. -/
lemma kappa_empty : κ (∅ : Set ℝ) = 0 := by
  classical
  -- Wir zeigen: Es gibt δ>0 mit ball (-1) δ ⊆ Iᶜ ⇒ ballI (-1) δ = ∅.
  have hxI : (-1 : ℝ) ∈ Iᶜ := by
    -- (-1) ∉ I = [0,1]
    simp [I]
  have hopen : IsOpen (Iᶜ) := isClosed_Icc.isOpen_compl
  have hnhds : Iᶜ ∈ nhds (-1) := hopen.mem_nhds hxI
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
  -- dann ist die relative Kugel leer
  have hBIempty : ballI (-1) δ = (∅ : Set ℝ) := by
    ext z; constructor
    · intro hz
      have hzBall : z ∈ ball (-1) δ := hz.1
      have hzI    : z ∈ I := hz.2
      have hzCompl : z ∈ Iᶜ := hball hzBall
      have : z ∉ I := by simpa using hzCompl
      exact (this hzI).elim
    · intro hz; cases hz
  -- Split-Identität auf I: κ(I \ ballI) = 1 - κ(ballI)
  have hsplit := KappaOnI.split_I (κ := κ) (x := (-1)) (r := δ) hδpos
  have : 1 = 1 - κ (∅ : Set ℝ) := by
    simpa [KappaOnI.I_one (κ := κ), hBIempty] using hsplit
  linarith

/-- Punkte von `M2 M` liegen notwendigerweise in `I = [0,1]`. -/
lemma M2_subset_I (M : Set ℝ) : M2 (κ := κ) M ⊆ I := by
  classical
  intro x hxM2
  by_contra hxI
  have hxI' : x ∈ Iᶜ := by simpa using hxI
  have hopen : IsOpen (Iᶜ) := isClosed_Icc.isOpen_compl
  have hnhds : Iᶜ ∈ nhds x := hopen.mem_nhds hxI'
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
  -- dann ist ballI x δ = ∅
  have hBIempty : ballI x δ = (∅ : Set ℝ) := by
    ext z; constructor
    · intro hz
      have hzBall : z ∈ ball x δ := hz.1
      have hzI    : z ∈ I := hz.2
      have hzCompl : z ∈ Iᶜ := hball hzBall
      have : z ∉ I := by simpa using hzCompl
      exact (this hzI).elim
    · intro hz; cases hz
  -- Positivität aus M2 bei ε = δ; gleichzeitig ist der Schnitt leer ⇒ Widerspruch.
  have hpos : 0 < κ (ballI x δ ∩ M) := hxM2 δ hδpos
  have hzero : κ (ballI x δ ∩ M) = 0 := by simp [hBIempty, kappa_empty]
  -- 0 < 0 ist falsch
  simp [hzero] at hpos

/-- Analog: Punkte von `M4 M` liegen in `I`. -/
lemma M4_subset_I (M : Set ℝ) : M4 (κ := κ) M ⊆ I := by
  classical
  intro x hxM4
  by_contra hxI
  have hxI' : x ∈ Iᶜ := by simpa using hxI
  have hopen : IsOpen (Iᶜ) := isClosed_Icc.isOpen_compl
  have hnhds : Iᶜ ∈ nhds x := hopen.mem_nhds hxI'
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδpos, hball⟩
  have hBIempty : ballI x δ = (∅ : Set ℝ) := by
    ext z; constructor
    · intro hz
      have hzBall : z ∈ ball x δ := hz.1
      have hzI    : z ∈ I := hz.2
      have hzCompl : z ∈ Iᶜ := hball hzBall
      have : z ∉ I := by simpa using hzCompl
      exact (this hzI).elim
    · intro hz; cases hz
  have hpos : 0 < κ (ballI x δ ∩ (I \ M)) := hxM4 δ hδpos
  have hzero : κ (ballI x δ ∩ (I \ M)) = 0 := by simp [hBIempty, kappa_empty]
  simp [hzero] at hpos


/-- `M2` ist kompakt (abgeschlossen und in `[0,1]` gelegen). -/
lemma isCompact_M2 (M : Set ℝ) : IsCompact (M2 (κ := κ) M) := by
  have hIc : IsCompact I := isCompact_Icc
  have hcl : IsClosed (M2 (κ := κ) M) := isClosed_M2 (κ := κ) M
  have hsub : M2 (κ := κ) M ⊆ I := M2_subset_I (κ := κ) M
  have : IsCompact (I ∩ M2 (κ := κ) M) := hIc.inter_right hcl
  have hEq : I ∩ M2 (κ := κ) M = M2 (κ := κ) M := by
    ext x; constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hsub hx, hx⟩
  simpa [hEq]

/-- `M4` ist kompakt (abgeschlossen und in `[0,1]` gelegen). -/
lemma isCompact_M4 (M : Set ℝ) : IsCompact (M4 (κ := κ) M) := by
  have hIc : IsCompact I := isCompact_Icc
  have hcl : IsClosed (M4 (κ := κ) M) := isClosed_M4 (κ := κ) M
  have hsub : M4 (κ := κ) M ⊆ I := M4_subset_I (κ := κ) M
  have : IsCompact (I ∩ M4 (κ := κ) M) := hIc.inter_right hcl
  have hEq : I ∩ M4 (κ := κ) M = M4 (κ := κ) M := by
    ext x; constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hsub hx, hx⟩
  simpa [hEq]

end SumKappa
