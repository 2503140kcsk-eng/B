module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic

public section

open scoped BigOperators

namespace GardenCanopy.M1Syntax

/-- The source's zero-indexed prime sequence: p₀ = 2, p₁ = 3, ... . -/
noncomputable def sourcePrime (i : Nat) : Nat :=
  Nat.nth Nat.Prime i

theorem sourcePrime_prime (i : Nat) : (sourcePrime i).Prime := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i

theorem sourcePrime_strictMono : StrictMono sourcePrime := by
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime

@[simp] theorem sourcePrime_zero : sourcePrime 0 = 2 := by
  simp [sourcePrime]

@[simp] theorem sourcePrime_one : sourcePrime 1 = 3 := by
  simp [sourcePrime]

@[simp] theorem sourcePrime_two : sourcePrime 2 = 5 := by
  simp [sourcePrime]

@[simp] theorem sourcePrime_three : sourcePrime 3 = 7 := by
  simp [sourcePrime]

/-- Auxiliary structural recursion for the prime-power payload. -/
noncomputable def sequencePayloadAux (i : Nat) : List Nat → Nat
  | [] => 1
  | a :: xs => sourcePrime (i + 1) ^ a * sequencePayloadAux (i + 1) xs

/-- Product of the prime powers in the source's finite-sequence code. -/
noncomputable def sequencePayload (xs : List Nat) : Nat :=
  sequencePayloadAux 0 xs

/--
The exact finite-sequence Gödel code from the primary source:
2^(length xs) * product_{i < length xs} p_(i+1)^(xs[i]) - 1.
The first prime p₀ = 2 is reserved for the length.
-/
noncomputable def encodeSequence (xs : List Nat) : Nat :=
  2 ^ xs.length * sequencePayload xs - 1

/-- A candidate decoder obtained from the prime valuations of n+1. -/
noncomputable def sequenceCandidate (n : Nat) : List Nat :=
  let code := n + 1
  let len := code.factorization 2
  (List.range len).map fun i => code.factorization (sourcePrime (i + 1))

/--
The source-code decoder is partial. It accepts the factorization-derived candidate
only when re-encoding it returns the original code; all malformed codes return none.
This equality check rejects any residual cofactor not represented by the source list.
-/
noncomputable def decodeSequence (n : Nat) : Option (List Nat) :=
  if encodeSequence (sequenceCandidate n) = n
  then some (sequenceCandidate n)
  else none

theorem decodeSequence_sound {n : Nat} {xs : List Nat}
    (h : decodeSequence n = some xs) :
    encodeSequence xs = n := by
  by_cases hEq : encodeSequence (sequenceCandidate n) = n
  · have hxs : sequenceCandidate n = xs := by
      simpa [decodeSequence, hEq] using h
    simpa [hxs] using hEq
  · simp [decodeSequence, hEq] at h

theorem decodeSequence_value {n : Nat} :
    decodeSequence n =
      if encodeSequence (sequenceCandidate n) = n
      then some (sequenceCandidate n) else none := by
  rfl

/-- The source's four-coordinate symbol tuple. -/
abbrev SymbolTuple := Nat × Nat × Nat × Nat

/--
Primitive and extended-language symbols from the source.
The coordinates are ordered as (a₀,a₁,a₂,a₃), corresponding to
a₀ + ω*a₁ + ω²*a₂ + ω³*a₃ before natural Gödel coding.
-/
inductive Symbol where
  | falsum
  | implication
  | negation
  | existsQuantifier
  | leftParen
  | rightParen
  | constant (i : Nat)
  | variable (i : Nat)
  | unaryU
  | theta
  | function (arity index : Nat)
  | membership
  | relation (arity index : Nat)
  deriving DecidableEq, Repr

/-- The exact source coordinate assignment for every symbol constructor. -/
def symbolTuple : Symbol → SymbolTuple
  | .falsum => (0, 0, 0, 0)
  | .implication => (1, 0, 0, 0)
  | .negation => (2, 0, 0, 0)
  | .existsQuantifier => (3, 0, 0, 0)
  | .leftParen => (4, 0, 0, 0)
  | .rightParen => (5, 0, 0, 0)
  | .constant i => (6, 0, i, 0)
  | .variable i => (7, 1, i, 0)
  | .unaryU => (8, 2, 0, 1)
  | .theta => (8, 3, 0, 1)
  | .function arity index => (8, 4, index, arity)
  | .membership => (9, 5, 0, 2)
  | .relation arity index => (9, 6, index, arity)

/-- Apply the source's sequence code to the four coordinates of a symbol. -/
noncomputable def symbolCode (s : Symbol) : Nat :=
  let (a₀, a₁, a₂, a₃) := symbolTuple s
  encodeSequence [a₀, a₁, a₂, a₃]

/-- Function symbols; the arity function gives their argument count. -/
inductive FunctionSymbol where
  | unaryU
  | theta
  | generic (arity index : Nat)

def FunctionSymbol.arity : FunctionSymbol → Nat
  | .unaryU => 1
  | .theta => 1
  | .generic arity _ => arity

/-- Relation symbols; membership is binary and generic relations carry an arity. -/
inductive RelationSymbol where
  | membership
  | generic (arity index : Nat)

def RelationSymbol.arity : RelationSymbol → Nat
  | .membership => 2
  | .generic arity _ => arity

/-- First-order terms over named variables and parameter constants. -/
inductive Term where
  | variable (index : Nat)
  | constant (index : Nat)
  | app (f : FunctionSymbol) (args : List Term)

/-- First-order formulas with the source's primitive connectives and quantifier. -/
inductive Formula where
  | falsum
  | implication (left right : Formula)
  | negation (body : Formula)
  | existsQuantifier (index : Nat) (body : Formula)
  | relation (r : RelationSymbol) (args : List Term)

/-- Arity-correctness at the root of terms. -/
def Term.hasCorrectRootArity : Term → Prop
  | .variable _ => True
  | .constant _ => True
  | .app f args => args.length = f.arity

/-- Arity-correctness at the root of atomic relation formulae. -/
def Formula.hasCorrectRootArity : Formula → Prop
  | .falsum => True
  | .implication _ _ => True
  | .negation _ => True
  | .existsQuantifier _ _ => True
  | .relation r args => args.length = r.arity

/--
Inductive detection of Θ in a term. This avoids a non-structural recursive
traversal through a nested List inside the term datatype.
-/
inductive Term.HasTheta : Term → Prop where
  | root {args : List Term} : Term.HasTheta (.app .theta args)
  | argument {f : FunctionSymbol} {args : List Term} {t : Term}
      (ht : t ∈ args) (h : Term.HasTheta t) : Term.HasTheta (.app f args)

/-- Inductive detection of Θ in a formula. -/
inductive Formula.HasTheta : Formula → Prop where
  | implicationLeft {A B : Formula} (h : Formula.HasTheta A) :
      Formula.HasTheta (.implication A B)
  | implicationRight {A B : Formula} (h : Formula.HasTheta B) :
      Formula.HasTheta (.implication A B)
  | negation {A : Formula} (h : Formula.HasTheta A) :
      Formula.HasTheta (.negation A)
  | existsQuantifier {i : Nat} {A : Formula} (h : Formula.HasTheta A) :
      Formula.HasTheta (.existsQuantifier i A)
  | relationArgument {r : RelationSymbol} {args : List Term} {t : Term}
      (ht : t ∈ args) (h : Term.HasTheta t) :
      Formula.HasTheta (.relation r args)

/-- The source's Henkin-scheme fragment: formulas not containing Θ. -/
def FormulaWithoutTheta (P : Formula) : Prop :=
  ¬ Formula.HasTheta P

/-! ## Hand-checkable code vectors from the source definition -/

example : encodeSequence [] = 0 := by
  simp [encodeSequence, sequencePayload, sequencePayloadAux]

example : encodeSequence [0] = 1 := by
  norm_num [encodeSequence, sequencePayload, sequencePayloadAux, sourcePrime]

example : encodeSequence [1] = 5 := by
  norm_num [encodeSequence, sequencePayload, sequencePayloadAux, sourcePrime,
    Nat.nth_prime_one_eq_three]

example : encodeSequence [0, 1] = 19 := by
  norm_num [encodeSequence, sequencePayload, sequencePayloadAux, sourcePrime,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

example : encodeSequence [3, 2, 5] =
    2 ^ 3 * 3 ^ 3 * 5 ^ 2 * 7 ^ 5 - 1 := by
  norm_num [encodeSequence, sequencePayload, sequencePayloadAux, sourcePrime,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven]


/-! ## Prime-factorization proof of the sequence-code round trip -/

/-- The Finsupp exponent vector encoded by the tail of a source sequence. -/
noncomputable def sequenceFactorization (i : Nat) : List Nat → (Nat →₀ Nat)
  | [] => 0
  | a :: xs =>
      Finsupp.single (sourcePrime (i + 1)) a +
        sequenceFactorization (i + 1) xs

theorem sequencePayloadAux_pos (i : Nat) :
    ∀ xs : List Nat, 0 < sequencePayloadAux i xs := by
  intro xs
  induction xs generalizing i with
  | nil =>
      simp [sequencePayloadAux]
  | cons a xs ih =>
      have hp : 0 < sourcePrime (i + 1) :=
        (sourcePrime_prime (i + 1)).pos
      simp only [sequencePayloadAux]
      exact Nat.mul_pos (pow_pos hp a) (ih (i + 1))

theorem sequencePayload_pos (xs : List Nat) :
    0 < sequencePayload xs := by
  exact sequencePayloadAux_pos 0 xs

theorem sequencePayloadAux_factorization (i : Nat) :
    ∀ xs : List Nat,
      (sequencePayloadAux i xs).factorization = sequenceFactorization i xs := by
  intro xs
  induction xs generalizing i with
  | nil =>
      simp [sequencePayloadAux, sequenceFactorization]
  | cons a xs ih =>
      have hp : (sourcePrime (i + 1)).Prime := sourcePrime_prime (i + 1)
      have hpow : sourcePrime (i + 1) ^ a ≠ 0 :=
        pow_ne_zero _ hp.ne_zero
      have htail : sequencePayloadAux (i + 1) xs ≠ 0 :=
        (sequencePayloadAux_pos (i + 1) xs).ne'
      change
        (sourcePrime (i + 1) ^ a * sequencePayloadAux (i + 1) xs).factorization =
          Finsupp.single (sourcePrime (i + 1)) a +
            sequenceFactorization (i + 1) xs
      rw [Nat.factorization_mul hpow htail, hp.factorization_pow, ih (i + 1)]

theorem sequencePayload_factorization (xs : List Nat) :
    (sequencePayload xs).factorization = sequenceFactorization 0 xs := by
  exact sequencePayloadAux_factorization 0 xs

theorem sequenceFactorization_apply_below_start
    (i : Nat) (xs : List Nat) (q : Nat)
    (hq : q ≤ sourcePrime i) :
    sequenceFactorization i xs q = 0 := by
  induction xs generalizing i q with
  | nil =>
      simp [sequenceFactorization]
  | cons a xs ih =>
      have hlt : sourcePrime i < sourcePrime (i + 1) :=
        sourcePrime_strictMono (Nat.lt_succ_self i)
      have hne : q ≠ sourcePrime (i + 1) :=
        ne_of_lt (lt_of_le_of_lt hq hlt)
      have hq' : q ≤ sourcePrime (i + 1) :=
        le_trans hq hlt.le
      simp [sequenceFactorization, hne, ih (i + 1) q hq']

theorem sequenceFactorization_apply_index
    (i : Nat) (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    sequenceFactorization i xs (sourcePrime (i + j + 1)) = xs[j] := by
  induction xs generalizing i j with
  | nil =>
      simp at hj
  | cons a xs ih =>
      cases j with
      | zero =>
          have htail :
              sequenceFactorization (i + 1) xs (sourcePrime (i + 1)) = 0 :=
            sequenceFactorization_apply_below_start
              (i + 1) xs (sourcePrime (i + 1)) le_rfl
          simp [sequenceFactorization, htail]
      | succ j =>
          have hj' : j < xs.length := by simpa using hj
          have htail : sequenceFactorization (i + 1) xs
              (sourcePrime ((i + 1) + j + 1)) = xs[j] := ih (i + 1) j hj'
          have hne : sourcePrime (i + 1) ≠ sourcePrime ((i + 1) + j + 1) := by
            apply ne_of_lt
            apply sourcePrime_strictMono
            omega
          have hindex : i + (j + 1) + 1 = (i + 1) + j + 1 := by omega
          rw [hindex]
          simp [sequenceFactorization, hne, htail]

theorem encodeSequence_add_one (xs : List Nat) :
    encodeSequence xs + 1 = 2 ^ xs.length * sequencePayload xs := by
  unfold encodeSequence
  have hp2 : 0 < 2 := by omega
  have hprod : 0 < 2 ^ xs.length * sequencePayload xs :=
    Nat.mul_pos (pow_pos hp2 xs.length) (sequencePayload_pos xs)
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hprod)

theorem encodeSequence_factorization (xs : List Nat) :
    (encodeSequence xs + 1).factorization =
      Finsupp.single 2 xs.length + sequenceFactorization 0 xs := by
  rw [encodeSequence_add_one xs]
  have hpow : 2 ^ xs.length ≠ 0 := by positivity
  have hpayload : sequencePayload xs ≠ 0 :=
    (sequencePayload_pos xs).ne'
  rw [Nat.factorization_mul hpow hpayload]
  rw [Nat.Prime.factorization_pow (by norm_num : Nat.Prime 2)]
  rw [sequencePayload_factorization]

theorem encodeSequence_factorization_two (xs : List Nat) :
    (encodeSequence xs + 1).factorization 2 = xs.length := by
  rw [encodeSequence_factorization]
  have hbelow :
      sequenceFactorization 0 xs 2 = 0 := by
    apply sequenceFactorization_apply_below_start
    simp [sourcePrime_zero]
  simp [Finsupp.add_apply, hbelow]

theorem encodeSequence_factorization_prime
    (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    (encodeSequence xs + 1).factorization (sourcePrime (j + 1)) = xs[j] := by
  rw [encodeSequence_factorization]
  have hprime_ne_two : sourcePrime (j + 1) ≠ 2 := by
    have hlt : sourcePrime 0 < sourcePrime (j + 1) :=
      sourcePrime_strictMono (by omega)
    simpa [sourcePrime_zero] using (ne_of_gt hlt)
  have hvalue :
      sequenceFactorization 0 xs (sourcePrime (j + 1)) = xs[j] := by
    simpa using sequenceFactorization_apply_index 0 xs j hj
  simp [Finsupp.add_apply, hprime_ne_two, hvalue]

/-- Encoding followed by candidate decoding recovers the original list. -/
theorem sequenceCandidate_encode (xs : List Nat) :
    sequenceCandidate (encodeSequence xs) = xs := by
  change
    (List.range ((encodeSequence xs + 1).factorization 2)).map
      (fun i => (encodeSequence xs + 1).factorization (sourcePrime (i + 1))) = xs
  rw [encodeSequence_factorization_two]
  apply List.ext_getElem
  · simp
  · intro i hiRange hiXs
    simp only [List.getElem_map, List.getElem_range]
    exact encodeSequence_factorization_prime xs i hiXs

/-- Universal source sequence-code round trip. -/
theorem decodeSequence_encodeSequence (xs : List Nat) :
    decodeSequence (encodeSequence xs) = some xs := by
  simp [decodeSequence, sequenceCandidate_encode]

/-- The source sequence encoder is injective. -/
theorem encodeSequence_injective : Function.Injective encodeSequence := by
  intro xs ys h
  have h' := congrArg decodeSequence h
  simpa [decodeSequence_encodeSequence] using h'

/-- A natural code is invalid exactly when no finite sequence encodes it. -/
theorem decodeSequence_eq_none_iff (n : Nat) :
    decodeSequence n = none ↔ ¬ ∃ xs : List Nat, encodeSequence xs = n := by
  constructor
  · intro h hExists
    obtain ⟨xs, hxs⟩ := hExists
    subst n
    rw [decodeSequence_encodeSequence] at h
    contradiction
  · intro h
    cases hd : decodeSequence n with
    | none => rfl
    | some xs =>
        exact (h ⟨xs, decodeSequence_sound hd⟩).elim


end GardenCanopy.M1Syntax
