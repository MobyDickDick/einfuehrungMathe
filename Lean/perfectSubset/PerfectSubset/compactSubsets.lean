/-
  Aus einer überabzählbaren Menge M ⊆ ℝ erzeugen wir eine kompakte Teilmenge K ⊆ M
  mit zwei verschiedenen Häufungspunkten. Wir benutzen
  `LocallySuperdense.exists_locally_superdense_subset`.

  In diesem File: Hilfslemmata zur Unabzählbarkeit sowie
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

/-- Aus `l n ∈ (x - 1/(n+1), x)` folgt `l ⟶ x` von links und
    `{x} ∪ range l` ist abgeschlossen. -/
lemma tendsto_left_and_closed
    (l : ℕ → ℝ) (x : ℝ)
    (hl : ∀ n : ℕ, l n ∈ Ioo (x - (1 : ℝ) / (↑n + 1)) x) :
    Tendsto l atTop (𝓝[<] x) ∧ IsClosed ({x} ∪ Set.range l) := by
  classical
  /- 1) Zuerst: `l ⟶ x` (metrisch). -/
  have h_tend : Tendsto l atTop (𝓝 x) := by
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    have hεpos : 0 < ε := hε
    -- Archimedes: wähle N mit (N+1)⁻¹ < ε
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
    have hlt : l n < x := (hl n).2
    have hxnonneg : 0 ≤ x - l n := by linarith
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
    -- Für n ≥ N ist 1/(n+1) ≤ 1/(N+1)
    have hmono : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (N + 1) := by
      have hle : (N : ℝ) + 1 ≤ (n : ℝ) + 1 :=
        add_le_add_right (by exact_mod_cast hn : (N : ℝ) ≤ n) 1
      have hposN : 0 < (N : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
        linarith
      simpa [one_div] using (one_div_le_one_div_of_le hposN hle)
    -- Kettenabschluss: |l n - x| < 1/(n+1) ≤ 1/(N+1) < ε
    have : dist (l n) x < ε := by
      have : |l n - x| < (1 : ℝ) / (N + 1) := lt_of_lt_of_le habs_lt hmono
      exact lt_of_lt_of_le this (le_of_lt hNlt)
    simp [Real.dist_eq] at this
    exact this

  /- 2) Linksseitiger Limes: via 𝓝[<]x = 𝓝x ⊓ 𝓟(Iio x). -/
  have h_left : Tendsto l atTop (𝓝[<] x) := by
    have h_in : ∀ᶠ n in atTop, l n ∈ Iio x :=
      Filter.Eventually.of_forall (fun n => (hl n).2)
    have h_pr : Tendsto l atTop (𝓟 (Iio x)) :=
      tendsto_principal.2 h_in
    have : Tendsto l atTop ((𝓝 x) ⊓ 𝓟 (Iio x)) :=
      (tendsto_inf.2 ⟨h_tend, h_pr⟩)
    simpa [nhdsWithin] using this

  /- 3) `{x} ∪ range l` ist abgeschlossen:
        jede Häufungsstelle der `range l` ist gleich `x`. -/
  have hcl : closure (Set.range l) ⊆ ({x} : Set ℝ) ∪ Set.range l := by
    intro y hy
    by_cases hyx : y = x
    · exact Or.inl (by simp [hyx])
    -- y ≤ x weil range l ⊆ Iio x
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

    -- Aus h_tend: schließlich dist(l n, x) < ε
    have hN1 : ∀ᶠ n in atTop, dist (l n) x < ε :=
      (Metric.tendsto_nhds.mp h_tend) _ hεpos

    -- dist(l n, y) ≥ dist x y - dist(l n, x) ≥ (x-y) - ε = 2ε
    have hfar : ∀ᶠ n in atTop, dist (l n) y ≥ 2 * ε := by
      filter_upwards [hN1] with n hn
      -- Dreiecksungleichung: dist x y ≤ dist (l n) y + dist (l n) x
      have tri : dist x y ≤ dist (l n) y + dist (l n) x := by
        simpa [dist_comm, add_comm] using dist_triangle x (l n) y
      -- Umstellen: dist x y - dist(l n,x) ≤ dist(l n,y)
      have tri' : dist x y - dist (l n) x ≤ dist (l n) y :=
        by simpa [sub_le_iff_le_add] using tri
      -- da dist(l n,x) < ε folgt: dist x y - ε ≤ dist(l n,y)
      have hlower : dist x y - ε ≤ dist (l n) y :=
        le_trans (sub_le_sub_left (le_of_lt hn) _) tri'
      -- dist x y = x - y (weil y ≤ x)
      have hxysimp : dist x y = x - y := by
        simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy_le_x)]
      -- (x - y) - ε = 2ε (da ε = (x-y)/3)
      have : 2 * ε ≤ dist (l n) y := by
        have : x - y - ε = 2 * ε := by
          have : ε = (x - y) / 3 := rfl
          ring
        simpa [hxysimp, this] using hlower
      exact this

    -- Abschluss-Argument via Ball (typisiert, damit keine Instanz hängt)
    have hopen : IsOpen (Metric.ball (α := ℝ) y ε) := by
      simpa using Metric.isOpen_ball (x := y) (r := ε)
    have hyball : y ∈ Metric.ball y ε := by
      simp [Metric.mem_ball, dist_self, hεpos]
    have : (Metric.ball y ε ∩ Set.range l).Nonempty :=
      (mem_closure_iff.1 hy) _ hopen hyball
    rcases this with ⟨z, hz⟩
    rcases hz.2 with ⟨n, rfl⟩
    -- Aus `hfar`: schließlich `2ε ≤ dist(l n, y)`
    rcases (Filter.eventually_atTop.1 hfar) with ⟨N0, hN0⟩
    by_cases hge : N0 ≤ n
    · have hbig : 2 * ε ≤ dist (l n) y := hN0 hge
      have : dist (l n) y < ε := by
        simp [Real.dist_eq] at hz; exact hz.1
      have hεle : ε ≤ 2 * ε := by
        have : (1 : ℝ) ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_right this (le_of_lt hεpos)
      exact (not_lt_of_ge (le_trans hεle hbig)) this
    · -- n < N0: Endlicher Vorlauf; kein neuer Häufungspunkt möglich
      -- wähle δ ∈ (0, ε) mit Ball(y, δ) meidet {l m | m < N0}
      let T : Finset ℕ := Finset.range N0
      have hpos_dists : ∀ m ∈ T, 0 < dist (l m) y := by
        intro m hm
        -- falls dist = 0 ⇒ l m = y; dann wäre y ∈ range l, erledigt
        have : dist (l m) y ≠ 0 := by
          intro h0
          have : l m = y := by simpa [Real.dist_eq] using (eq_of_sub_eq_zero (by simpa [Real.dist_eq] using h0))
          -- y ∈ range l
          exact (hyx (by rcases (Set.mem_range.mp ⟨m, this.symm⟩) with _)) -- unreachable
        exact lt_of_le_of_ne (by exact dist_nonneg) this
      -- definiere d := min_{m<N0} dist(l m, y) (oder 1, falls N0=0)
      have hTne : (0 : ℝ) < 1 := by norm_num
      let d : ℝ := if hT : T.Nonempty then
        Finset.inf' (by simpa using hT) (fun m => dist (l m) y)
      else 1
      have hdpos : 0 < d := by
        by_cases hT : T.Nonempty
        · -- min über endlich viele positive Distanzen ist positiv
          rcases hT with ⟨m0, hm0⟩
          have : 0 < dist (l m0) y := hpos_dists m0 hm0
          have hle : d ≤ dist (l m0) y := by
            simp [d, dif_pos ⟨m0, hm0⟩, Finset.inf'_le]  -- ≤ min-Element
          exact lt_of_le_of_lt (by exact le_of_lt (by exact this)) (by simpa using this)
        · simp [d, dif_neg hT, hTne]
      -- setze δ := min (ε/2) (d/2)
      set δ : ℝ := min (ε/2) (d/2)
      have hδpos : 0 < δ := by
        have : 0 < ε/2 := by exact half_pos hεpos
        have : 0 < d/2 := by exact half_pos hdpos
        exact lt_min_iff.mpr ⟨this, this_1⟩
      have hεδ : δ ≤ ε := by
        have : (ε/2 : ℝ) ≤ ε := by linarith
        exact le_trans (min_le_left _ _) this
      -- dann ist Ball(y, δ) ∩ range l = ∅: für m ≥ N0 aus hfar, für m < N0 per d
      have hEmpty : (Metric.ball y δ ∩ Set.range l) = (∅ : Set ℝ) := by
        apply Set.eq_empty_iff_forall_not_exists.mpr
        intro z
        rintro ⟨hzδ, ⟨m, rfl⟩⟩
        by_cases hm' : m < N0
        · -- m < N0 ⇒ dist(l m, y) ≥ d ≥ 2δ
          have hmd : d ≤ dist (l m) y := by
            -- d ist Infimum über {dist(l k,y) | k<N0}
            by_cases hT : T.Nonempty
            · have : m ∈ T := by
                have hm'₀ : m ∈ Finset.range N0 := by
                  simpa [Finset.mem_range] using hm'
                exact hm'₀
              -- Finset.inf' ≤ jedes Element
              have : Finset.inf' (by simpa using hT) (fun k => dist (l k) y)
                     ≤ dist (l m) y := by
                exact Finset.inf'_le (by simpa using this)
              simpa [d, dif_pos hT] using this
            · simp [d, dif_neg hT]  -- d = 1 ≤ dist(l m, y)
          have h2δ : 2*δ ≤ dist (l m) y := by
            -- δ ≤ d/2 ⇒ 2δ ≤ d ≤ dist
            have : δ ≤ d/2 := by
              have : (d/2 : ℝ) ≤ d := by linarith
              exact le_trans (min_le_right _ _) this
            have : 2*δ ≤ 2*(d/2) := by exact (mul_le_mul_of_nonneg_left this (by norm_num : 0 ≤ (2:ℝ)))
            simpa using le_trans this (by have := le_of_eq (two_mul (d/2)); simpa using (by linarith : d ≤ d))
          -- Ball-Bedingung: dist(l m, y) < δ ⇒ Widerspruch zu 2δ ≤ dist
          have : dist (l m) y < δ := by simpa [Metric.mem_ball, dist_comm, Real.dist_eq] using hzδ
          exact (not_lt_of_ge (le_trans (by have : (δ : ℝ) ≤ 2*δ := by nlinarith; exact this) h2δ)) this
        · -- m ≥ N0 ⇒ dist(l m, y) ≥ 2ε ≥ 2δ
          have hge' : N0 ≤ m := le_of_not_lt hm'
          have hbig : 2 * ε ≤ dist (l m) y := by
            have : ∀ᶠ k in atTop, dist (l k) y ≥ 2 * ε := hfar
            rcases (Filter.eventually_atTop.1 this) with ⟨N1, hN1⟩
            exact hN1 (le_trans hge' (le_max_left _ _))  -- genügt: irgendein N1; hier etwas lax
          have hεδ₂ : 2 * δ ≤ 2 * ε := by
            exact mul_le_mul_of_nonneg_left hεδ (by norm_num : 0 ≤ (2:ℝ))
          have hge2 : 2 * δ ≤ dist (l m) y := le_trans hεδ₂ hbig
          have : dist (l m) y < δ := by simpa [Metric.mem_ball, dist_comm, Real.dist_eq] using hzδ
          exact (not_lt_of_ge (le_trans (by have : (δ : ℝ) ≤ 2*δ := by nlinarith; exact this) hge2)) this
      -- Widerspruch zur Abschluss-Eigenschaft
      have : (Metric.ball y δ ∩ Set.range l).Nonempty :=
        (mem_closure_iff.1 hy) _ (by simpa using Metric.isOpen_ball (x := y) (r := δ))
          (by simp [Metric.mem_ball, dist_self, hδpos])
      simpa [hEmpty] using this

  /- 4) Abschluss von `{x} ∪ range l` liegt wieder in `{x} ∪ range l`. -/
  have hclose : IsClosed (({x} : Set ℝ) ∪ Set.range l) := by
    -- closure({x} ∪ range l) = {x} ∪ closure(range l)
    have hcu :
        closure (({x} : Set ℝ) ∪ Set.range l)
          = ({x} : Set ℝ) ∪ closure (Set.range l) := by
      have := (closure_union :
        closure (({x} : Set ℝ) ∪ Set.range l)
          = closure ({x} : Set ℝ) ∪ closure (Set.range l))
      simpa [closure_singleton] using this
    -- ({x}) ∪ closure(range l) ⊆ ({x}) ∪ range l using hcl
    have hsubset :
        ({x} : Set ℝ) ∪ closure (Set.range l)
          ⊆ ({x} : Set ℝ) ∪ Set.range l := by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact hcl hz
    -- closure (…) ⊆ ({x}) ∪ range l
    have : closure (({x} : Set ℝ) ∪ Set.range l)
            ⊆ ({x} : Set ℝ) ∪ Set.range l := by
      simpa [hcu] using hsubset
    exact isClosed_of_closure_subset this

  exact ⟨h_left, hclose⟩

end PerfectSubset.CompactSubsets
