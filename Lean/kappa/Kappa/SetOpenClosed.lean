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

end SetOpenClosed

