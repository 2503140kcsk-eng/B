import Std

namespace GardenCanopy

/-- Apply g exactly k times to n. -/
def iterate (g : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate g k (g n)

/--
Knuth's up-arrow hierarchy in the convention:
level 0 = multiplication, level 1 = exponentiation,
and each higher level iterates the previous-level operation.
-/
def knuthArrow : Nat → Nat → Nat → Nat
  | 0, a, b => a * b
  | 1, a, b => a ^ b
  | r + 2, a, b => iterate (knuthArrow (r + 1) a) b 1

/-- The common starting value 10 ↑^10 10. -/
def lngnSeed : Nat := knuthArrow 10 10 10

/-- The finite maximum of f(0), ..., f(n). -/
def prefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (prefixMax f n) (f (n + 1))

/--
A one-step envelope. It exceeds n, exceeds f(n), and is at least 2^(n+1).
-/
def amplification (f : Nat → Nat) (n : Nat) : Nat :=
  max (n + 1) (max (2 ^ (n + 1)) (prefixMax f n + 1))

/-- The LNGN expression, parameterized by its intended total function f. -/
def lngnValue (f : Nat → Nat) : Nat :=
  iterate f 10 lngnSeed

/--
Garden Canopy Number: iterate the envelope LNGN(f)+1 times,
starting at LNGN(f).
-/
def gardenCanopyNumber (f : Nat → Nat) : Nat :=
  iterate (amplification f) (lngnValue f + 1) (lngnValue f)

theorem self_le_prefixMax (f : Nat → Nat) :
    ∀ n, f n ≤ prefixMax f n := by
  intro n
  induction n with
  | zero =>
      simp [prefixMax]
  | succ n ih =>
      simpa [prefixMax] using
        (Nat.le_max_right (prefixMax f n) (f (n + 1)))

theorem amplification_gt_self (f : Nat → Nat) (n : Nat) :
    n < amplification f n := by
  unfold amplification
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_left _ _)

theorem function_value_lt_amplification (f : Nat → Nat) (n : Nat) :
    f n < amplification f n := by
  unfold amplification
  have hmem : f n ≤ prefixMax f n := self_le_prefixMax f n
  have hsucc : prefixMax f n < prefixMax f n + 1 := by
    simp
  have hinner :
      prefixMax f n + 1 ≤
        max (2 ^ (n + 1)) (prefixMax f n + 1) :=
    Nat.le_max_right _ _
  have houter :
      max (2 ^ (n + 1)) (prefixMax f n + 1) ≤
        max (n + 1) (max (2 ^ (n + 1)) (prefixMax f n + 1)) :=
    Nat.le_max_right _ _
  exact Nat.lt_of_le_of_lt hmem
    (Nat.lt_of_lt_of_le hsucc (Nat.le_trans hinner houter))


theorem amplification_ge_power (f : Nat → Nat) (n : Nat) :
    2 ^ (n + 1) ≤ amplification f n := by
  unfold amplification
  exact Nat.le_trans
    (Nat.le_max_left (2 ^ (n + 1)) (prefixMax f n + 1))
    (Nat.le_max_right (n + 1)
      (max (2 ^ (n + 1)) (prefixMax f n + 1)))

theorem iterate_ge_of_expansive
    (g : Nat → Nat) (hg : ∀ n, n < g n) :
    ∀ k n, n ≤ iterate g k n := by
  intro k
  induction k with
  | zero =>
      intro n
      exact Nat.le_refl n
  | succ k ih =>
      intro n
      change n ≤ iterate g k (g n)
      exact Nat.le_trans (Nat.le_of_lt (hg n)) (ih (g n))

theorem iterate_gt_of_expansive
    (g : Nat → Nat) (hg : ∀ n, n < g n) (k n : Nat) :
    n < iterate g (k + 1) n := by
  have hstep : n < g n := hg n
  have hrest : g n ≤ iterate g k (g n) :=
    iterate_ge_of_expansive g hg k (g n)
  exact Nat.lt_of_lt_of_le hstep (by
    simpa [iterate] using hrest)

/-- The GCN is strictly greater than the LNGN expression under the same f. -/
theorem gardenCanopy_gt_lngn (f : Nat → Nat) :
    lngnValue f < gardenCanopyNumber f := by
  unfold gardenCanopyNumber
  exact iterate_gt_of_expansive
    (amplification f) (amplification_gt_self f)
    (lngnValue f) (lngnValue f)

/-- The GCN also strictly exceeds the next f-value after the LNGN input. -/
theorem gardenCanopy_gt_next_f_value (f : Nat → Nat) :
    f (lngnValue f) < gardenCanopyNumber f := by
  unfold gardenCanopyNumber
  have hfirst :
      f (lngnValue f) < amplification f (lngnValue f) :=
    function_value_lt_amplification f (lngnValue f)
  have hrest :
      amplification f (lngnValue f) ≤
        iterate (amplification f) (lngnValue f + 1) (lngnValue f) := by
    simpa [iterate] using
      (iterate_ge_of_expansive
        (amplification f)
        (amplification_gt_self f)
        (lngnValue f)
        (amplification f (lngnValue f)))
  exact Nat.lt_of_lt_of_le hfirst hrest


/-- GCN is at least 2^(LNGN(f)+1), an explicit exponential lower bound. -/
theorem gardenCanopy_ge_power_of_lngn (f : Nat → Nat) :
    2 ^ (lngnValue f + 1) ≤ gardenCanopyNumber f := by
  unfold gardenCanopyNumber
  have hfirst :
      2 ^ (lngnValue f + 1) ≤ amplification f (lngnValue f) :=
    amplification_ge_power f (lngnValue f)
  have hrest :
      amplification f (lngnValue f) ≤
        iterate (amplification f) (lngnValue f + 1) (lngnValue f) := by
    simpa [iterate] using
      (iterate_ge_of_expansive
        (amplification f)
        (amplification_gt_self f)
        (lngnValue f)
        (amplification f (lngnValue f)))
  exact Nat.le_trans hfirst hrest

/-- Every component of the definition is a natural number by construction. -/
theorem gardenCanopy_is_finite (f : Nat → Nat) :
    ∃ n : Nat, n = gardenCanopyNumber f := by
  exact ⟨gardenCanopyNumber f, rfl⟩

end GardenCanopy
