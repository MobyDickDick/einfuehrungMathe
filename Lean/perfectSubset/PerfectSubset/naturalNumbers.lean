/-
  naturalNumbers.lean
  "n A" als n-fache Wiederholung von A (Wörter als Listen).
-/
namespace MetaSymbol

universe u
abbrev Word (α : Type u) := List α
variable {α : Type u}

/-- Rechtsrekursion:
    0 Kopien = leeres Wort, (n+1) Kopien = (n Kopien) ++ [a]. -/
def repRight (a : α) : Nat → Word α
| 0     => []
| n+1   => repRight a n ++ [a]

@[simp] theorem repRight_zero (a : α) : repRight a 0 = ([] : Word α) := rfl
@[simp] theorem repRight_one  (a : α) : repRight a 1 = [a] := rfl
@[simp] theorem repRight_succ (a : α) (n : Nat) :
  repRight a (n+1) = repRight a n ++ [a] := rfl

/-- `replicate n a ++ [a] = replicate (n+1) a`. -/
theorem replicate_append_singleton (n : Nat) (a : α) :
  List.replicate n a ++ [a] = List.replicate (n+1) a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, ih]

/-- Gleichheit zur Standardfunktion `List.replicate`. -/
theorem repRight_eq_replicate (a : α) (n : Nat) :
  repRight a n = List.replicate n a := by
  induction n with
  | zero => simp [repRight]
  | succ n ih => simp [repRight, ih, replicate_append_singleton]

/-- Länge ist `n`. -/
theorem length_repRight (a : α) (n : Nat) :
  (repRight a n).length = n := by
  induction n with
  | zero => simp [repRight]
  | succ n ih => simp [repRight, ih]

end MetaSymbol

open MetaSymbol

/-- N-fache Wiederholung eines Zeichens als String. -/
def repChar (c : Char) (n : Nat) : String :=
  String.mk (repRight c n)

/-- Notation: `(n ✶ 'A')` ergibt direkt den String `"AAAAA"`. -/
notation:73 n " ✶ " c => repChar c n

-- Beispiele (zeigen Strings, nicht Listen):
#eval (1+1+1+1+1) ✶ 'A'   -- "AAAAA"
#eval (3+2) ✶ 'B'         -- "BBBBB"
#eval 0 ✶ 'Z'             -- ""
