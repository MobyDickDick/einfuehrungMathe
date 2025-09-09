/-
  Aus einer überabzählbaren Menge M ⊆ ℝ erzeugen wir eine kompakte Teilmenge K ⊆ M
  mit zwei verschiedenen Häufungspunkten. Wir benutzen
  `LocallySuperdense.exists_locally_superdense_subset`.

  In diesem File: zwei kleine Hilfslemmata zur Unabzählbarkeit und
  ein topologisches Lemma über eine Folge (l n) mit l n ∈ (x - 1/(n+1), x).
-/

import Mathlib
import PerfectSubset.LocallySuperdense

open Set Topology Filter
open scoped Topology

namespace PerfectSubset.CompactSubsets

/-- Aus `¬ s.Countable` folgt `s.Nonempty`. -/
lemma nonempty_of_not_countable {α} {s : Set α} (hs : ¬ s.Countable) :
  s.Nonempty := by
  classical
  by_contra h
  have : s = (∅ : Set α) := by simpa [Set.not_nonempty_iff_eq_empty] using h
  have : s.Countable := by simp [this]
  exact hs this

/-- Wenn `A` unabzählbar ist und `x ∈ A`, dann ist `A \\ {x}` unabzählbar. -/
lemma not_countable_diff_singleton_of_mem {α} {A : Set α} (hA : ¬ A.Countable)
    {x : α} (hx : x ∈ A) : ¬ (A \ {x}).Countable := by
  classical
  intro h
  have h' : (insert x (A \ {x})).Countable := h.insert x
  have hEq : insert x (A \ {x}) = A := by
    ext y; constructor
    · intro hy
      rcases hy with rfl | hy
      · exact hx
      · exact hy.1
    · intro hyA
      by_cases hxy : y = x
      · subst hxy; exact Or.inl rfl
      · exact Or.inr ⟨hyA, by simpa [mem_singleton_iff] using hxy⟩
  have : A.Countable := by simpa [hEq] using h'
  exact hA this

/-- Reine Konvergenz: aus `l n ∈ (x - 1/(n+1), x)` folgt `l ⟶ x`. -/
lemma tendsto_to_x (l : ℕ → ℝ) (x : ℝ)
    (hl : ∀ n : ℕ, l n ∈ Ioo (x - (1 : ℝ) / (n + 1)) x) :
    Tendsto l atTop (𝓝 x) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hεpos : 0 < ε := hε
  -- Wähle N mit (N+1)⁻¹ < ε
  obtain ⟨N, hNgt⟩ :
      ∃ N : ℕ, (1 : ℝ) / ε < (N : ℝ) + 1 := by
    rcases exists_nat_gt ((1 : ℝ) / ε) with ⟨N, hN⟩
    have : (1 : ℝ) / ε < (N : ℝ) := by exact_mod_cast hN
    exact ⟨N, by linarith⟩
  have hNlt : (1 : ℝ) / ((N : ℝ) + 1) < ε := by
    -- 0 < 1/ε < N+1 ⇒ 1/(N+1) < 1/(1/ε) = ε
    have h := one_div_lt_one_div_of_lt (one_div_pos.mpr hεpos) hNgt
    simpa [one_div, inv_inv] using h
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hxnonneg : 0 ≤ x - l n := by
    have : l n < x := (hl n).2; linarith
  -- x - l n < 1/(n+1)
  have hxln' : x - l n < (1 : ℝ) / (n + 1) := by
    have : x < l n + (1 : ℝ) / (n + 1) := by
      simpa [add_comm] using (sub_lt_iff_lt_add).mp ((hl n).1)
    simpa [add_comm, sub_lt_iff_lt_add'] using this
  -- |l n - x| < 1/(n+1)
  have habs_lt : |l n - x| < (1 : ℝ) / (n + 1) := by
    have : |l n - x| = |x - l n| := by simp [abs_sub_comm]
    have hxabs : |x - l n| = x - l n := abs_of_nonneg hxnonneg
    have := lt_of_le_of_lt (le_of_eq hxabs) hxln'
    simpa [abs_sub_comm] using this
  -- Monotonie: n ≥ N ⇒ 1/(n+1) ≤ 1/(N+1)
  have hmono : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (N + 1) := by
    have hle : (N : ℝ) + 1 ≤ (n : ℝ) + 1 :=
      add_le_add_right (by exact_mod_cast hn : (N : ℝ) ≤ n) 1
    have hposN : 0 < (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      linarith
    simpa [one_div] using (one_div_le_one_div_of_le hposN hle)
  -- Kettenabschluss
  have : dist (l n) x < ε := by
    have : |l n - x| < (1 : ℝ) / (N + 1) := lt_of_lt_of_le habs_lt hmono
    exact lt_of_lt_of_le this (le_of_lt hNlt)
  simpa [Real.dist_eq] using this

/-- Linksseitiger Limes: aus `l ⟶ x` und `l n < x` folgt `l ⟶ 𝓝[<] x`. -/
lemma tendsto_left (l : ℕ → ℝ) (x : ℝ)
    (hl : ∀ n : ℕ, l n ∈ Ioo (x - (1 : ℝ) / (n + 1)) x) :
    Tendsto l atTop (𝓝[<] x) := by
  have h_tend : Tendsto l atTop (𝓝 x) := tendsto_to_x l x hl
  have h_in : ∀ᶠ n in atTop, l n ∈ Iio x :=
    Filter.Eventually.of_forall (fun n => (hl n).2)
  have h_pr : Tendsto l atTop (𝓟 (Iio x)) :=
    tendsto_principal.2 h_in
  have : Tendsto l atTop ((𝓝 x) ⊓ 𝓟 (Iio x)) :=
    (tendsto_inf.2 ⟨h_tend, h_pr⟩)
  simpa [nhdsWithin] using this

/--
Wenn `l n ∈ (x - 1/(n+1), x)` für alle `n`, dann gilt:
Alle Häufungsstellen der Bildmenge `range l` sind entweder `x` selbst
oder bereits in `range l`.
-/
lemma closure_range_subset_insert
    (l : ℕ → ℝ) (x : ℝ)
    (hl : ∀ n : ℕ, l n ∈ Ioo (x - (1 : ℝ) / (n + 1)) x) :
    closure (Set.range l) ⊆ ({x} : Set ℝ) ∪ Set.range l := by
  classical
  intro y hy
  by_cases hyx : y = x
  · exact Or.inl (by simp [hyx])

  -- y ≤ x, da range l ⊆ Iio x
  have hy_le_x : y ≤ x := by
    have : Set.range l ⊆ Iio x := by
      intro t ht; rcases ht with ⟨n, rfl⟩; exact (hl n).2
    have : closure (Set.range l) ⊆ closure (Iio x) := closure_mono this
    have hy' : y ∈ closure (Iio x) := this hy
    simp [closure_Iio] at hy'
    exact hy'
  have hy_lt_x : y < x := lt_of_le_of_ne hy_le_x hyx

  -- ε := (x - y)/3 > 0
  set ε : ℝ := (x - y) / 3
  have hεpos : 0 < ε := by
    have hxmy_pos : 0 < x - y := sub_pos.mpr hy_lt_x
    exact div_pos hxmy_pos (by norm_num)

  -- l → x ⇒ schließlich dist(l n, x) < ε
  have h_tend : Tendsto l atTop (𝓝 x) := tendsto_to_x l x hl
  have hN1 : ∀ᶠ n in atTop, dist (l n) x < ε :=
    (Metric.tendsto_nhds.mp h_tend) _ hεpos

  -- Dreiecksungleichung ⇒ schließlich dist(l n, y) ≥ 2ε
  have hfar : ∀ᶠ n in atTop, dist (l n) y ≥ 2 * ε := by
    filter_upwards [hN1] with n hn
    have tri : dist x y ≤ dist (l n) y + dist (l n) x := by
      simpa [dist_comm, add_comm] using dist_triangle x (l n) y
    have tri' : dist x y - dist (l n) x ≤ dist (l n) y :=
      by simpa [sub_le_iff_le_add] using tri
    have hlower : dist x y - ε ≤ dist (l n) y :=
      le_trans (sub_le_sub_left (le_of_lt hn) _) tri'
    have hxysimp : dist x y = x - y := by
      simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_le_x)]
    have : 2 * ε ≤ dist (l n) y := by
      have : x - y - ε = 2 * ε := by
        have : ε = (x - y) / 3 := rfl; ring
      simpa [hxysimp, this] using hlower
    exact this

  -- Wähle einen Zeugen im Ball(y, ε) ∩ range l
  have hopen : IsOpen (Metric.ball (α := ℝ) y ε) := by
    simpa using Metric.isOpen_ball (x := y) (r := ε)
  have hyball : y ∈ Metric.ball y ε := by
    simp [Metric.mem_ball, dist_self, hεpos]
  have hnonempty : (Metric.ball y ε ∩ Set.range l).Nonempty :=
    (mem_closure_iff.1 hy) _ hopen hyball
  rcases hnonempty with ⟨z, hz⟩
  rcases hz.2 with ⟨n, rfl⟩

  -- Entweder n groß ⇒ Widerspruch, oder n klein ⇒ y ist Wert der endlichen Anfangsmenge
  rcases (Filter.eventually_atTop.1 hfar) with ⟨N0, hN0⟩
  by_cases hge : N0 ≤ n
  · -- großer Index: 2ε ≤ dist(l n, y), aber l n ∈ Ball(y, ε) — Widerspruch
    have hbig : 2 * ε ≤ dist (l n) y := hN0 n hge
    have hzBall : dist (l n) y < ε := by
      have : l n ∈ Metric.ball y ε := hz.1
      simpa [Metric.mem_ball, Real.dist_eq, dist_comm] using this
    have hεle : ε ≤ 2 * ε := by
      have : (0 : ℝ) ≤ ε := le_of_lt hεpos; nlinarith
    exact (not_lt_of_ge (le_trans hεle hbig)) hzBall |> False.elim
  · -- kleiner Index: n < N0.
    -- Zwei Fälle: entweder y = l m für ein m < N0 (fertig),
    -- oder y ist von allen {l m | m<N0} positiv entfernt; dann kleinerer Ball.
    set T : Finset ℕ := Finset.range N0
    by_cases hy_in_T : ∃ m ∈ T, y = l m
    · rcases hy_in_T with ⟨m, hmT, hym⟩
      exact Or.inr ⟨m, hym.symm⟩
    ·
      -- y ≠ l m für alle m < N0 ⇒ min. Abstand δ' > 0
      let D : Finset ℝ := T.image (fun m => dist (l m) y)
      have hDmem : ∀ m ∈ T, dist (l m) y ∈ D := by
        intro m hm; exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
      have hDpos : ∀ m ∈ T, 0 < dist (l m) y := by
        intro m hm
        have hne_ym : y ≠ l m := by
          intro h; exact hy_in_T ⟨m, hm, h⟩
        have hne_my : l m ≠ y := by simpa [eq_comm] using hne_ym
        exact dist_pos.mpr hne_my

      -- Splitte Fälle: T leer oder nicht leer
      by_cases hT : T.Nonempty
      · -- **Fall 1: T ≠ ∅**
        have hDne : D.Nonempty := by
          rcases hT with ⟨m0, hm0⟩
          exact ⟨dist (l m0) y, hDmem m0 hm0⟩
        -- alle D-Elemente sind > 0
        have hDpos' : ∀ d ∈ D, 0 < d := by
          intro d hd
          rcases Finset.mem_image.mp hd with ⟨m, hm, rfl⟩
          exact hDpos m hm
        -- δ' = Minimum von D
        let δ' : ℝ := D.min' hDne
        have hδ'pos : 0 < δ' := by
          have hmem : δ' ∈ D := Finset.min'_mem _ hDne
          exact hDpos' δ' hmem

        -- δ₀ := min ε (δ'/2)
        set δ₀ : ℝ := min ε (δ' / 2)
        have hδ₀pos : 0 < δ₀ := lt_min_iff.mpr ⟨hεpos, half_pos hδ'pos⟩

        -- (Ball(y, δ₀) ∩ range l) = ∅
        have hEmpty : (Metric.ball y δ₀ ∩ Set.range l) = (∅ : Set ℝ) := by
          apply Set.eq_empty_iff_forall_not_mem.mpr
          intro z hz
          rcases hz with ⟨hzBall, ⟨m, rfl⟩⟩
          by_cases hm' : m < N0
          · -- m < N0 ⇒ dist(l m, y) ≥ δ' ≥ 2*(δ'/2) ≥ 2*δ₀ ⇒ nicht im Ball
            have hmT : m ∈ T := by simpa [T, Finset.mem_range] using hm'
            -- min' ≤ jedes Element der Bildmenge
            have hmin_le : D.min' hDne ≤ dist (l m) y :=
              Finset.min'_le (s := D) (x := dist (l m) y) (H2 := hDmem m hmT)
            have hδ'le : δ' ≤ dist (l m) y := by
              simpa [δ'] using hmin_le
            -- δ₀ ≤ δ'/2 ⇒ 2 δ₀ ≤ 2 (δ'/2) = δ'
            have hδ₀le : δ₀ ≤ δ' / 2 := min_le_right _ _
            have hle2' : 2 * δ₀ ≤ 2 * (δ' / 2) :=
              mul_le_mul_of_nonneg_left hδ₀le (by norm_num : 0 ≤ (2:ℝ))
            have hge : 2 * δ₀ ≤ dist (l m) y :=
              le_trans hle2' (by simpa using (le_trans (le_of_eq (by ring)) hδ'le))
            -- Widerspruch mit Ball-Bedingung
            have hzlt : dist (l m) y < δ₀ := by
              simpa [Metric.mem_ball, dist_comm, Real.dist_eq] using hzBall
            -- elementar: δ₀ ≤ 2 δ₀
            have hle2 : δ₀ ≤ 2 * δ₀ := by
              have hnonneg : 0 ≤ δ₀ := le_of_lt hδ₀pos
              have : (1 : ℝ) ≤ 2 := by norm_num
              simpa [one_mul] using (mul_le_mul_of_nonneg_right this hnonneg)
            exact (not_lt_of_ge (le_trans hle2 hge)) hzlt
          · -- m ≥ N0 ⇒ dist(l m, y) ≥ 2ε ≥ ε ≥ δ₀ ⇒ nicht im Ball
            have hge' : N0 ≤ m := le_of_not_lt hm'
            have hbig : 2 * ε ≤ dist (l m) y := hN0 m hge'
            have hεδ : δ₀ ≤ ε := min_le_left _ _
            have : δ₀ ≤ dist (l m) y :=
              le_trans hεδ (le_trans (by
                have : (0 : ℝ) ≤ ε := le_of_lt hεpos; nlinarith) hbig)
            exact (not_lt_of_ge this) (by
              simpa [Metric.mem_ball, dist_comm, Real.dist_eq] using hzBall)

        -- Widerspruch zur Abschluss-Charakterisierung
        have : (Metric.ball y δ₀ ∩ Set.range l).Nonempty :=
          (mem_closure_iff.1 hy) _
            (by simpa using Metric.isOpen_ball (x := y) (r := δ₀))
            (by simp [Metric.mem_ball, dist_self, hδ₀pos])
        simpa [hEmpty] using this

      · -- **Fall 2: T = ∅** ⇒ daraus folgt N0 = 0, also ∀ m, N0 ≤ m
        have hTempty : T = (∅ : Finset ℕ) := by
          -- ¬T.Nonempty ↔ T = ∅
          simpa [Finset.nonempty_iff_ne_empty] using hT
          -- range N0 = ∅  ↔  N0 = 0
          -- aus T = ∅ folgt N0 = 0 (sonst wäre 0 ∈ range N0)
        have hN0zero : N0 = 0 := by
          by_contra hne
          have hpos : 0 < N0 := Nat.pos_of_ne_zero hne
          have : 0 ∈ T := by
            -- 0 < N0  ↔  0 ∈ range N0
            simpa [T, Finset.mem_range] using hpos
          -- Widerspruch zu T = ∅
          simpa [hTempty] using this

        -- wähle δ₀ := min ε (1/2)
        set δ₀ : ℝ := min ε ((1 : ℝ) / 2)
        have hδ₀pos : 0 < δ₀ := lt_min_iff.mpr ⟨hεpos, by norm_num⟩
        have hEmpty : (Metric.ball y δ₀ ∩ Set.range l) = (∅ : Set ℝ) := by
          apply Set.eq_empty_iff_forall_not_mem.mpr
          intro z hz
          rcases hz with ⟨hzBall, ⟨m, rfl⟩⟩
          -- aus N0=0 folgt N0 ≤ m
          have hge' : N0 ≤ m := by simpa [hN0zero]
          have hbig : 2 * ε ≤ dist (l m) y := hN0 m hge'
          have hεδ : δ₀ ≤ ε := min_le_left _ _
          have : δ₀ ≤ dist (l m) y :=
            le_trans hεδ (le_trans (by
              have : (0 : ℝ) ≤ ε := le_of_lt hεpos; nlinarith) hbig)
          exact (not_lt_of_ge this) (by
            simpa [Metric.mem_ball, dist_comm, Real.dist_eq] using hzBall)
        -- Widerspruch
        have : (Metric.ball y δ₀ ∩ Set.range l).Nonempty :=
          (mem_closure_iff.1 hy) _
            (by simpa using Metric.isOpen_ball (x := y) (r := δ₀))
            (by simp [Metric.mem_ball, dist_self, hδ₀pos])
        simpa [hEmpty] using this


end PerfectSubset.CompactSubsets
