module

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

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

/-- Product of the prime powers in the source's finite-sequence code. -/
noncomputable def sequencePayload (xs : List Nat) : Nat :=
  ∏ i ∈ Finset.range xs.length, sourcePrime (i + 1) ^ xs.getD i 0

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

def Term.containsTheta : Term → Bool
  | .variable _ => false
  | .constant _ => false
  | .app .theta _ => true
  | .app .unaryU args => args.any Term.containsTheta
  | .app (.generic _ _) args => args.any Term.containsTheta

def Formula.containsTheta : Formula → Bool
  | .falsum => false
  | .implication A B => Formula.containsTheta A || Formula.containsTheta B
  | .negation A => Formula.containsTheta A
  | .existsQuantifier _ A => Formula.containsTheta A
  | .relation _ args => args.any Term.containsTheta

/-- The source's Henkin-scheme fragment: formulas not containing Θ. -/
def FormulaWithoutTheta (P : Formula) : Prop :=
  Formula.containsTheta P = false

/-! ## Hand-checkable code vectors from the source definition -/

example : encodeSequence [] = 0 := by
  simp [encodeSequence, sequencePayload]

example : encodeSequence [0] = 1 := by
  norm_num [encodeSequence, sequencePayload, sourcePrime]

example : encodeSequence [1] = 5 := by
  norm_num [encodeSequence, sequencePayload, sourcePrime,
    Nat.nth_prime_one_eq_three]

example : encodeSequence [0, 1] = 19 := by
  norm_num [encodeSequence, sequencePayload, sourcePrime,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

example : encodeSequence [3, 2, 5] =
    2 ^ 3 * 3 ^ 3 * 5 ^ 2 * 7 ^ 5 - 1 := by
  norm_num [encodeSequence, sequencePayload, sourcePrime,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven]

end GardenCanopy.M1Syntax
