module

import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

namespace GardenCanopy.M1Ordinal

/-- The normal-form notation for the ordinal omega. -/
def omegaNote : NONote :=
  NONote.oadd (NONote.ofNat 1) 1 0 (by
    exact ONote.NFBelow.zero
  )

/-- The least-prime-factor exponent used by the author's CNF recursion. -/
def sourceExponent (k : Nat) : Nat :=
  k.factorization k.minFac

/-- The quotient remaining after removing the full least-prime power. -/
def sourceQuotient (k : Nat) : Nat :=
  k / (k.minFac ^ sourceExponent k)

/--
The author's prime-factor CNF map, with values represented in Mathlib's
normal Cantor notation below epsilon-zero.
-/
noncomputable def sourceCNF : Nat → NONote
  | 0 => 0
  | n + 1 => by
      let k := n + 2
      let p := k.minFac
      let v := sourceExponent k
      let j := sourceQuotient k
      have hk : 2 ≤ k := by omega
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hp2 : 2 ≤ p := hp.two_le
      have hvpos : 0 < v := by
        dsimp [v, sourceExponent]
        exact hp.factorization_pos_of_dvd (by omega) k.minFac_dvd
      have hvbound : p * v ≤ k := by
        dsimp [v, sourceExponent]
        exact Nat.mul_factorization_le
      have hvlt : v - 1 < n + 1 := by omega
      have hpPow : 1 < p ^ v := by
        exact (Nat.one_lt_pow_iff hvpos.ne').2 hp.one_lt
      have hjlt : j - 1 < n + 1 := by
        have hdiv : k / p ^ v < k := Nat.div_lt_self (by omega) hpPow
        dsimp [j, sourceQuotient]
        exact Nat.sub_lt_sub_right hdiv 1
      exact NONote.opow omegaNote (sourceCNF (v - 1)) +
        sourceCNF (j - 1)
termination_by n => n
decreasing_by
  all_goals
    simp_wf
    assumption

@[simp] theorem sourceCNF_zero : sourceCNF 0 = 0 := rfl

end GardenCanopy.M1Ordinal
