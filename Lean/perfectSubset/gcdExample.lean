import Mathlib

namespace DemoGCD

/-- Euklidischer Algorithmus, Rekursion auf dem zweiten Argument. -/
def gcd' : Nat → Nat → Nat
| a, 0     => a
| a, b+1   => gcd' (b+1) (a % (b+1))
termination_by _ b => b
decreasing_by
  -- Im rekursiven Fall: a % (b+1) < b+1
  simpa using Nat.mod_lt a (Nat.succ_pos b)

/-- Korrektheit: `gcd'` stimmt mit `Nat.gcd` überein. -/
theorem gcd'_eq_gcd (a b : Nat) : gcd' a b = Nat.gcd a b := by
  revert a
  refine Nat.strong_induction_on b ?_
  intro b IH a
  cases b with
  | zero =>
      -- Basisfall
      simp [gcd', Nat.gcd_zero_right]
  | succ b =>
      -- Induktionsschritt: IH auf (a % (b+1), b+1)
      have ih' := IH (a % (b+1)) (Nat.mod_lt _ (Nat.succ_pos _)) (b+1)
      calc
        gcd' a (b+1)
            = gcd' (b+1) (a % (b+1)) := by
              simp only [gcd']
        _   = Nat.gcd (b+1) (a % (b+1)) := ih'
        _   = Nat.gcd (a % (b+1)) (b+1) := by
              -- commutiere gcd-Argumente
              exact Nat.gcd_comm _ _
        _   = Nat.gcd (b+1) a := by
              -- benutze Orientierung von `gcd_rec`: gcd (b+1) a = gcd (a % (b+1)) (b+1)
              exact (Nat.gcd_rec (b+1) a).symm
        _   = Nat.gcd a (b+1) := by
              -- wieder zurückkommutieren
              exact Nat.gcd_comm _ _

/-! Beispiele (nur Ausgaben) -/
#eval gcd' 48 18     -- 6
#eval gcd' 1071 462  -- 21
#eval gcd' 0 0       -- 0
#eval gcd' 7 0       -- 7

end DemoGCD
