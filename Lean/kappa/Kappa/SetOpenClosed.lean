import Mathlib

/-!
# Lean-Beweis: Schnitt-Aussage

Ziel: Für jede Teilmenge `M` eines T₁-Raums (insbesondere `ℝ`) gilt
```
⋂₀ {U | IsOpen U ∧ M ⊆ U} = M.
```

Die Beweisidee: `M ⊆ ⋂₀ …` ist klar. Für `⋂₀ … ⊆ M`: Sei `x ∉ M`. Dann ist `({x})ᶜ` offen und enthält `M`, also darf `x` nicht in der Schnittmenge liegen.

Die Datei enthält:
* eine Hilfsdefinition `openSupersets M`,
* den allgemeinen Satz in T₁-Räumen,
* die Spezialisierung auf `ℝ`,
* zwei Mini‑Tests.

Zusätzlich sind unten Hinweise zur früheren `hyIoi`‑Stelle und zum `end SetOpenClosed`‑Fehler.
-/

open Set

namespace SetOpenClosed

/-- Offene Obermengen `𝒱(M)` und abgeschlossene Teilmengen `𝒲(M)` (ℝ‑Version). -/
def V (M : Set ℝ) : Set (Set ℝ) := {U | IsOpen U ∧ M ⊆ U}

def W (M : Set ℝ) : Set (Set ℝ) := {K | IsClosed K ∧ K ⊆ M}

variable {α : Type*} [TopologicalSpace α]

/-- Die Menge aller offenen Obermengen von `M`. -/
def openSupersets (M : Set α) : Set (Set α) := {U | IsOpen U ∧ M ⊆ U}

/-- Richtung `⊆`: Die Schnittmenge aller offenen Obermengen enthält `M`. -/
lemma subset_sInter_openSupersets (M : Set α) :
    M ⊆ ⋂₀ (openSupersets (α:=α) M) := by
  intro x hx
  classical
  refine mem_sInter.mpr ?_
  intro U hU
  exact hU.2 hx

/-- Richtung `⊇`: In T₁-Räumen ist `⋂₀ (openSupersets M) ⊆ M`. -/
lemma sInter_openSupersets_subset (M : Set α) [T1Space α] :
    ⋂₀ (openSupersets (α:=α) M) ⊆ M := by
  intro x hx
  classical
  by_contra hxM
  -- `({x})ᶜ` ist offen und enthält `M` (da `x ∉ M`).
  have hUopen : IsOpen (({x} : Set α)ᶜ) := (isClosed_singleton (x:=x)).isOpen_compl
  have hMU : M ⊆ ({x} : Set α)ᶜ := by
    intro y hy
    have : y ≠ x := by
      intro h; subst h; exact hxM hy
    -- `y ≠ x` ist gleichbedeutend mit `y ∈ ({x})ᶜ`.
    simpa [Set.mem_singleton_iff] using this
  -- `x` liegt *nicht* in `({x})ᶜ`.
  have hxnot : x ∉ ({x} : Set α)ᶜ := by simp
  -- Da `({x})ᶜ` in `openSupersets M` liegt, müsste `x` darin liegen — Widerspruch.
  have hXinU : x ∈ ({x} : Set α)ᶜ := by
    have hUmem : ({x} : Set α)ᶜ ∈ openSupersets (α:=α) M := ⟨hUopen, hMU⟩
    exact (mem_sInter.mp hx) _ hUmem
  exact hxnot hXinU

/-- Hauptsatz: In T₁-Räumen ist der Schnitt aller offenen Obermengen gleich `M`. -/
 theorem sInter_openSupersets_eq (M : Set α) [T1Space α] :
    ⋂₀ (openSupersets (α:=α) M) = M := by
  apply le_antisymm
  · exact sInter_openSupersets_subset (α:=α) M
  · exact subset_sInter_openSupersets (α:=α) M

/-- Spezialisierung auf `ℝ`. -/
example (M : Set ℝ) : ⋂₀ (openSupersets (α:=ℝ) M) = M := by
  simpa using (sInter_openSupersets_eq (α:=ℝ) M)

/-- Mini‑Test 1: Einzelpunkt. -/
example (x : ℝ) : ⋂₀ (openSupersets (α:=ℝ) ({x} : Set ℝ)) = {x} := by
  simpa using (sInter_openSupersets_eq (α:=ℝ) ({x} : Set ℝ))

/-- Mini‑Test 2: Beliebiges Intervall (hier: offen) als Sanity‑Check. -/
example (a b : ℝ) : ⋂₀ (openSupersets (α:=ℝ) (Ioo a b)) = Ioo a b := by
  simpa using (sInter_openSupersets_eq (α:=ℝ) (Ioo a b))

/-!
## Hinweis zu `hyIoi`

Wenn man (für ein fixes `x`) ein offenes `U` baut über
```
U := ⋃ y ∈ M, (if y < x then Iio x else Ioi x),
```
dann reicht aus `¬ (y < x)` allein **nicht** `x < y`; man bekommt nur `x ≤ y`.
Für die Rechtsseite benötigt man `x < y`. Das erhält man mit `lt_or_gt_of_ne` aus `y ≠ x`.
Und `y ≠ x` folgt hier aus `x ∉ M` und `y ∈ M`.

Kurzmuster:
```
  have hne : y ≠ x := by
    intro h; subst h; exact hxM hy
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · -- `hyx : y < x`, dann `by simpa [hyx]` zeigt `y ∈ Iio x`.
  · -- `hxy : x < y`, dann `by simpa [hyx, hxy]` zeigt `y ∈ Ioi x`.
```

Mit der hier gewählten Singleton‑Komplement‑Konstruktion ist all das überflüssig
und die Fehlermeldung „term `hyIoi` has type `True` …" tritt nicht auf.

## Hinweis zu `end SetOpenClosed`

Nutze konsequent `namespace …`/`end …` (wie in dieser Datei). Falls du nur
lokale Variablen binden willst, nimm zusätzlich **unnamed** `section …`/`end`.
Ein `end SetOpenClosed` beendet ausschließlich ein zuvor geöffnetes
`namespace SetOpenClosed`.
-/

/-- Für gegebenes `M` und `x` eine offene Obermenge von `M`, die `x` ausschließt. -/
def U_of (M : Set ℝ) (x : ℝ) : Set ℝ :=
  ⋃ (y : ℝ) (_ : y ∈ M), (if y < x then Iio x else Ioi x)

/-- `U_of M x` ist offen. -/
lemma isOpen_U_of (M : Set ℝ) (x : ℝ) : IsOpen (U_of M x) := by
  classical
  refine isOpen_iUnion ?_
  intro y; refine isOpen_iUnion ?_
  intro _; by_cases h : y < x
  · simpa [U_of, h] using isOpen_Iio
  · simpa [U_of, h] using isOpen_Ioi

/-- Für `x ∉ M` gilt `M ⊆ U_of M x`. -/
lemma subset_U_of_of_not_mem {M : Set ℝ} {x : ℝ} (hx : x ∉ M) :
  M ⊆ U_of M x := by
  classical
  intro y hyM
  have hne : y ≠ x := fun h => hx (by simpa [h] using hyM)
  have hlt : y < x ∨ x < y := lt_or_gt_of_ne hne
  rcases hlt with h | h
  · refine mem_iUnion.mpr ?_
    refine ⟨y, mem_iUnion.mpr ?_⟩
    have hyx : y < x := h
    have : y ∈ (if y < x then Iio x else Ioi x) := by simp [hyx]
    exact ⟨hyM, this⟩
  · refine mem_iUnion.mpr ?_
    refine ⟨y, mem_iUnion.mpr ?_⟩
    have hyx : ¬ y < x := not_lt.mpr (le_of_lt h)
    have : y ∈ (if y < x then Iio x else Ioi x) := by
      have : y ∈ Ioi x := by simpa using h
      simpa [hyx] using this
    exact ⟨hyM, this⟩

/-- `x ∉ U_of M x` (für jedes `x`). -/
lemma not_mem_U_of_self (M : Set ℝ) (x : ℝ) : x ∉ U_of M x := by
  classical
  intro hxU
  rcases mem_iUnion.mp hxU with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨_, hxIn⟩
  by_cases h : y < x
  · have : x < x := by simp [h] at hxIn
    exact (lt_irrefl _) this
  · have : x < x := by simp [h] at hxIn
    exact (lt_irrefl _) this


/-- Variante mit *abgeschlossenen* $K$ wie in deiner Notation: `U ∈ 𝒱(M)`, `K ∈ 𝒲(M)`. -/
def gapFamily' (M : Set ℝ) : Set (Set ℝ) :=
  {S | ∃ U ∈ V M, ∃ K ∈ W M, S = U \ K}

/-- **Auch für `gapFamily'` (mit `K` abgeschlossen) ist der Schnitt leer.** -/
 theorem inter_all_gaps'_empty (M : Set ℝ) : (⋂₀ gapFamily' M) = (∅ : Set ℝ) := by
  classical
  apply le_antisymm
  · -- (⋂₀ …) ⊆ ∅
    intro x hx
    by_cases hxM : x ∈ M
    · -- Fall 1: x ∈ M. Nimm U = univ, K = {x}.
      have hUopen : IsOpen (Set.univ : Set ℝ) := isOpen_univ
      have hKclosed : IsClosed ({x} : Set ℝ) := isClosed_singleton
      have hKsub  : ({x} : Set ℝ) ⊆ M := by
        intro y hy
        rcases mem_singleton_iff.mp hy with rfl
        simpa using hxM
      have hMsubU : M ⊆ (Set.univ : Set ℝ) := by intro _ _; trivial
      have hmem : (Set.univ \ ({x} : Set ℝ)) ∈ gapFamily' M := by
        exact ⟨Set.univ, ⟨hUopen, hMsubU⟩, {x}, ⟨hKclosed, hKsub⟩, rfl⟩
      have hxIn : x ∈ Set.univ \ ({x} : Set ℝ) := (sInter_subset_of_mem hmem) hx
      -- Widerspruch
      have : False := by
        have hxNot : x ∉ Set.univ \ ({x} : Set ℝ) := by simp
        exact hxNot hxIn
      exact False.elim this
    · -- Fall 2: x ∉ M. Nimm U = U_of M x, K = ∅.
      have hUopen : IsOpen (U_of M x) := isOpen_U_of M x
      have hKclosed : IsClosed (∅ : Set ℝ) := isClosed_empty
      have hKsub  : (∅ : Set ℝ) ⊆ M := by intro _ h; cases h
      have hMsubU : M ⊆ U_of M x := subset_U_of_of_not_mem (M := M) (x := x) hxM
      have hmem : (U_of M x \ (∅ : Set ℝ)) ∈ gapFamily' M := by
        exact ⟨U_of M x, ⟨hUopen, hMsubU⟩, ∅, ⟨hKclosed, hKsub⟩, rfl⟩
      have hxIn : x ∈ U_of M x \ (∅ : Set ℝ) := (sInter_subset_of_mem hmem) hx
      have hxU : x ∈ U_of M x := by simpa using hxIn.left
      have : False := (not_mem_U_of_self M x) hxU
      exact this.elim
  · -- ∅ ⊆ (⋂₀ …)
    intro x hx; cases hx

/-- **Abstrakte Dyaden-Folge aus einer ε-Approximation.**
Falls eine Größe `κ : Set ℝ → ℝ` gegeben ist und wir *für jedes* `ε>0`
`U ∈ 𝒱(M)` und `K ∈ 𝒲(M)` mit `κ (U \ K) < ε` finden, dann gibt es für *jedes*
`n : ℕ` solche `Uₙ, Kₙ` mit `κ (Uₙ \ Kₙ) < (1/2)^n`.

> Diese Aussage extrahiert nur die **Folgenkonstruktion** aus der ε‑Version und
> ist unabhängig davon, wie `κ` konkret definiert ist.
-/
lemma exists_dyadic_gap_sequence
    (κ : Set ℝ → ℝ)
    (M : Set ℝ)
    (hε : ∀ ε > 0, ∃ U ∈ V M, ∃ K ∈ W M, κ (U \ K) < ε) :
    ∀ n : ℕ, ∃ U ∈ V M, ∃ K ∈ W M, κ (U \ K) < ((1:ℝ)/2) ^ n := by
  intro n
  have hpos : 0 < ((1:ℝ)/2) ^ n := by
    have : 0 < (1:ℝ)/2 := by norm_num
    exact pow_pos this n
  simpa using hε (((1:ℝ)/2) ^ n) hpos

/-!
### Hinweis zur konkreten Instanziierung von `κ` (z. B. Lebesgue‑Maß)

Für `κ = fun S => (MeasureTheory.Measure.restrict MeasureTheory.volume Set.univ) S`
(also das Lebesgue‑Maß auf `ℝ`) liefert die Regularität des Maßes die benötigte
ε‑Version: Für jede messbare Menge `M` und jedes `ε>0` gibt es `K ⊆ M` kompakt
(also abgeschlossen) und `U ⊇ M` offen mit `volume (U \ K) < ε`.

Dann kann obiges Lemma direkt angewandt werden, um die Folge `(Uₙ, Kₙ)` und die
Dyaden‑Schranke `volume (Uₙ \ Kₙ) < (1/2)^n` zu erhalten.

Die Implementierung dieser Regularitäts‑Brücke in Lean ist möglich, benötigt aber
Importe aus der Maßtheorie (`MeasureTheory.Measure.Regular`/`Lebesgue`) und setzt
`MeasurableSet M` (und ggf. `volume M < ⊤`) voraus. Wenn du möchtest, bauen wir
sie als eigenes Lemma `exists_open_closed_gap_lt (M) (hM : MeasurableSet M)`.
-/

end SetOpenClosed


/-!  κ als Infimum über offene Obermengen – rein abstrakt über eine Basisgröße ℓ : Set ℝ → ℝ. -/
section Kappa

open Set

/-- Äußere Größe `κ(M) := inf { ℓ(U) | U offen, M ⊆ U }`. -/
noncomputable def kappa (ℓ : Set ℝ → ℝ) (M : Set ℝ) : ℝ :=
  sInf ((fun U : Set ℝ => ℓ U) '' {U : Set ℝ | IsOpen U ∧ M ⊆ U})

/-- `κ(∅) = 0`, sofern `ℓ ∅ = 0` und `ℓ` nichtnegativ ist. -/
lemma kappa_empty
    (ℓ : Set ℝ → ℝ)
    (hℓ_empty : ℓ (∅ : Set ℝ) = 0)
    (hℓ_nonneg : ∀ U : Set ℝ, 0 ≤ ℓ U) :
    kappa ℓ (∅ : Set ℝ) = 0 := by
  classical
  set S := ((fun U : Set ℝ => ℓ U) '' {U : Set ℝ | IsOpen U ∧ (∅ : Set ℝ) ⊆ U}) with hS
  -- S ist nichtleer (U = ∅ ist Kandidat)
  have hS_ne : S.Nonempty := by
    refine ⟨ℓ (∅ : Set ℝ), ?_⟩
    exact ⟨(∅ : Set ℝ), ⟨isOpen_empty, by intro _ h; cases h⟩, rfl⟩
  -- 0 ist untere Schranke von S (Nichtnegativität von ℓ)
  have hLower : ∀ z ∈ S, 0 ≤ z := by
    intro z hz; rcases hz with ⟨U, -, rfl⟩; exact hℓ_nonneg U
  have hBdd : BddBelow S := ⟨0, hLower⟩
  -- ℓ(∅) ∈ S ⇒ sInf S ≤ ℓ(∅) = 0
  have hz : ℓ (∅ : Set ℝ) ∈ S := ⟨(∅ : Set ℝ), ⟨isOpen_empty, by intro _ h; cases h⟩, rfl⟩
  have h_le : sInf S ≤ ℓ (∅ : Set ℝ) := csInf_le hBdd hz
  -- 0 ≤ sInf S
  have h_ge : 0 ≤ sInf S := le_csInf hS_ne hLower
  -- von S zurück zu κ
  have h1 : kappa ℓ (∅ : Set ℝ) ≤ 0 := by simpa [kappa, hS, hℓ_empty] using h_le
  have h2 : 0 ≤ kappa ℓ (∅ : Set ℝ) := by simpa [kappa, hS] using h_ge
  exact le_antisymm h1 h2

/-- Allgemein: ist ein Schnitt leer, so ist sein κ-Wert 0. -/
lemma kappa_of_sInter_empty
    (ℓ : Set ℝ → ℝ)
    (hℓ_empty : ℓ (∅ : Set ℝ) = 0)
    (hℓ_nonneg : ∀ U : Set ℝ, 0 ≤ ℓ U)
    {G : Set (Set ℝ)} (h : ⋂₀ G = (∅ : Set ℝ)) :
    kappa ℓ (⋂₀ G) = 0 := by
  have h0 : kappa ℓ (∅ : Set ℝ) = 0 := kappa_empty ℓ hℓ_empty hℓ_nonneg
  simpa [h] using h0

/-- **Existenz offener Überdeckungen mit beliebig kleinem κ**
Falls `κ M = 0`, gibt es für jedes `n` eine offene Menge `U ⊇ M`
mit `κ(U) < 1 / 2 ^ n`. -/
lemma exists_open_superset_with_small_kappa_dyadic
    (ℓ : Set ℝ → ℝ)
    (hℓ_nonneg : ∀ U : Set ℝ, 0 ≤ ℓ U)
    {M : Set ℝ}
    (hκ0 : kappa ℓ M = 0) :
    ∀ n : ℕ, ∃ U, IsOpen U ∧ M ⊆ U ∧ kappa ℓ U < (1 / 2 : ℝ) ^ n := by
  intro n
  classical
  -- Kandidaten: offene Obermengen von M
  let Cand : Set (Set ℝ) := {U : Set ℝ | IsOpen U ∧ M ⊆ U}
  have hCand_ne : Cand.Nonempty := ⟨Set.univ, ⟨isOpen_univ, subset_univ M⟩⟩
  -- ε = (1/2)^n > 0
  set ε : ℝ := (1 / 2 : ℝ) ^ n with hε
  have hεpos : 0 < ε := by
    rw [hε]; have hhalf : 0 < (1 : ℝ) / 2 := by norm_num
    exact pow_pos hhalf n

  -- 1) Aus κ M = 0 folgt: Es gibt U ∈ Cand mit ℓ U < ε.
  have exists_open_with_small_ell :
      ∃ U ∈ Cand, ℓ U < ε := by
    -- Widerspruchsbeweis gegen die Existenz
    by_contra h
    -- h : ¬ (∃ U ∈ Cand, ℓ U < ε)
    push_neg at h
    -- zeige ε ≤ sInf (ℓ '' Cand)
    have h_lower : ε ≤ sInf ((fun U : Set ℝ => ℓ U) '' Cand) := by
      -- Nichtleerheit des Bildes
      have hne : ((fun U : Set ℝ => ℓ U) '' Cand).Nonempty := by
        rcases hCand_ne with ⟨U0, hU0⟩
        exact ⟨ℓ U0, ⟨U0, hU0, rfl⟩⟩
      -- ε ist untere Schranke von (ℓ '' Cand)
      have hbound : ∀ z ∈ ((fun U : Set ℝ => ℓ U) '' Cand), ε ≤ z := by
        intro z hz
        rcases hz with ⟨U, hU, rfl⟩
        -- aus h U hU : ¬ (ℓ U < ε) folgt ε ≤ ℓ U
        have : ¬ (ε > ℓ U) := by
          -- ¬(ε > ℓ U) ist gleich ¬(ℓ U < ε)
          simpa [gt_iff_lt] using (h U hU)
        exact le_of_not_gt this
      -- jetzt über le_csInf
      exact le_csInf hne hbound
    -- Aber sInf (ℓ '' Cand) = κ M = 0 ⇒ ε ≤ 0, Widerspruch zu ε>0.
    have : sInf ((fun U : Set ℝ => ℓ U) '' Cand) = kappa ℓ M := rfl
    have hε_le_zero : ε ≤ 0 := by simpa [this, hκ0] using h_lower
    exact (hεpos.not_ge hε_le_zero)
  rcases exists_open_with_small_ell with ⟨U, hUin, hℓUlt⟩
  rcases hUin with ⟨hUopen, hMsubU⟩

  -- 2) Aus ℓ U < ε folgt κ U ≤ ℓ U < ε ⇒ κ U < ε.
  --    (weil U selbst in der Indexmenge von κ U liegt)
  have hκU_le_ℓU : kappa ℓ U ≤ ℓ U := by
    -- Indexmenge für κ U
    let S' : Set ℝ :=
      ((fun V : Set ℝ => ℓ V) '' {V : Set ℝ | IsOpen V ∧ U ⊆ V})
    -- ℓ U ∈ S' (mit V=U)
    have hUmem : ℓ U ∈ S' := ⟨U, ⟨hUopen, subset_rfl⟩, rfl⟩
    -- 0 ist untere Schranke von S' (Nichtnegativität von ℓ)
    have hBdd : BddBelow S' := ⟨0, by
      intro z hz; rcases hz with ⟨V, -, rfl⟩; exact hℓ_nonneg V⟩
    -- sInf S' ≤ ℓ U
    simpa [kappa, S'] using (csInf_le hBdd hUmem)
  have hκUlt : kappa ℓ U < ε := lt_of_le_of_lt hκU_le_ℓU hℓUlt
  exact ⟨U, hUopen, hMsubU, by simpa [hε] using hκUlt⟩


end Kappa
