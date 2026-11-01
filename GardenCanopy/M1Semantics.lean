module

import GardenCanopy.M1Syntax
import Mathlib.Data.Set.Finite

namespace GardenCanopy.M1Semantics

universe u

/--
An expansion of the source language on a carrier D.

The fields constants, genericFunction, and genericRelation interpret c_i,
f_(a,i), and r_(a,i), respectively. No injectivity, distinctness,
definability, or invariance condition is imposed on these maps.
Membership, U, and Θ are interpreted separately.
-/
structure Expansion (D : Type u) where
  defaultElement : D
  constants : Nat → D
  genericFunction : Nat → Nat → List D → D
  genericRelation : Nat → Nat → List D → Prop
  membership : D → D → Prop
  unaryU : D → D
  theta : D → D

open GardenCanopy.M1Syntax

def functionInterpretation {D : Type u} (M : Expansion D) :
    FunctionSymbol → List D → D
  | .unaryU, [x] => M.unaryU x
  | .theta, [x] => M.theta x
  | .generic arity index, args => M.genericFunction arity index args
  | _, _ => M.defaultElement

def relationInterpretation {D : Type u} (M : Expansion D) :
    RelationSymbol → List D → Prop
  | .membership, [x, y] => M.membership x y
  | .generic arity index, args => M.genericRelation arity index args
  | _, _ => False

mutual
  /-- A term evaluates relative to a structure and a variable assignment. -/
  inductive TermEval {D : Type u} (M : Expansion D) (σ : Nat → D) :
      Term → D → Prop where
    | variable (i : Nat) : TermEval M σ (.variable i) (σ i)
    | constant (i : Nat) : TermEval M σ (.constant i) (M.constants i)
    | app {f : FunctionSymbol} {args : List Term} {values : List D}
        (h : TermsEval M σ args values) :
        TermEval M σ (.app f args) (functionInterpretation M f values)

  /-- Pointwise evaluation of an argument list. -/
  inductive TermsEval {D : Type u} (M : Expansion D) (σ : Nat → D) :
      List Term → List D → Prop where
    | nil : TermsEval M σ [] []
    | cons {t : Term} {ts : List Term} {x : D} {xs : List D}
        (ht : TermEval M σ t x) (hs : TermsEval M σ ts xs) :
        TermsEval M σ (t :: ts) (x :: xs)
end

/-- Tarskian satisfaction for the source's primitive formula constructors. -/
inductive Satisfies {D : Type u} (M : Expansion D) :
    (Nat → D) → Formula → Prop where
  | implication {σ : Nat → D} {A B : Formula}
      (h : Satisfies M σ A → Satisfies M σ B) :
      Satisfies M σ (.implication A B)
  | negation {σ : Nat → D} {A : Formula}
      (h : Satisfies M σ A → False) :
      Satisfies M σ (.negation A)
  | existsQuantifier {σ : Nat → D} {i : Nat} {A : Formula}
      (h : ∃ d : D, Satisfies M (Function.update σ i d) A) :
      Satisfies M σ (.existsQuantifier i A)
  | relation {σ : Nat → D} {r : RelationSymbol}
      {args : List Term} {values : List D}
      (heval : TermsEval M σ args values)
      (hrel : relationInterpretation M r values) :
      Satisfies M σ (.relation r args)

/-- The source-language atomic formula r_(1,0)(x₀). -/
def r10Formula : Formula :=
  .relation (.generic 1 0) [.variable 0]

theorem satisfies_r10_iff {D : Type u} (M : Expansion D)
    (σ : Nat → D) :
    Satisfies M σ r10Formula ↔ M.genericRelation 1 0 [σ 0] := by
  constructor
  · intro hs
    cases hs with
    | relation heval hrel =>
      cases heval with
      | cons hhead htail =>
        cases hhead
        cases htail
        exact hrel
  · intro hrel
    exact Satisfies.relation
      (TermsEval.cons (TermEval.variable 0) TermsEval.nil) hrel

/--
A legal arbitrary interpretation in which every parameter constant c_i denotes d,
every generic function is the constant function d, and r_(1,0) denotes the
singleton predicate {d}. All other generic relations are empty.
-/
def collapsedExpansion {D : Type u} [Nonempty D] (d : D) : Expansion D where
  defaultElement := d
  constants := fun _ => d
  genericFunction := fun _ _ _ => d
  genericRelation := fun arity index args =>
    arity = 1 ∧ index = 0 ∧ args = [d]
  membership := fun _ _ => False
  unaryU := fun _ => d
  theta := fun _ => d

theorem collapsed_r10_iff {D : Type u} [Nonempty D] (d x : D) :
    (collapsedExpansion d).genericRelation 1 0 [x] ↔ x = d := by
  simp [collapsedExpansion]

theorem collapsed_satisfies_r10_iff {D : Type u} [Nonempty D] (d : D)
    (σ : Nat → D) :
    Satisfies (collapsedExpansion d) σ r10Formula ↔ σ 0 = d := by
  rw [satisfies_r10_iff, collapsed_r10_iff]

/--
DefinesExactly M P means P has exactly one satisfying value of x₀,
independently of the values assigned to the other variables.
-/
def DefinesExactly {D : Type u} (M : Expansion D) (P : Formula) : Prop :=
  ∃! d : D, ∀ σ : Nat → D, Satisfies M σ P ↔ σ 0 = d

/--
A value m is defined by the formula r_(1,0)(x₀) when that formula defines
exactly one object and the parameter constant c_m denotes that object.
This is the semantic core of Definable(m,i,P), with i=0 and one fixed P.
-/
def ParameterDefinable {D : Type u} (M : Expansion D) (m : Nat) : Prop :=
  DefinesExactly M r10Formula ∧
    ∀ σ : Nat → D, Satisfies M σ r10Formula ↔ σ 0 = M.constants m

theorem collapsed_defines_exactly {D : Type u} [Nonempty D] (d : D) :
    DefinesExactly (collapsedExpansion d) r10Formula := by
  refine ⟨d, ?_, ?_⟩
  · intro σ
    exact collapsed_satisfies_r10_iff d σ
  · intro y hy
    have hsat : Satisfies (collapsedExpansion d) (fun _ => d) r10Formula := by
      exact (collapsed_satisfies_r10_iff d (fun _ => d)).2 rfl
    have hEq := (hy (fun _ => d)).1 hsat
    exact hEq.symm

theorem collapsed_all_parameters_definable {D : Type u} [Nonempty D] (d : D) :
    ∀ m : Nat, ParameterDefinable (collapsedExpansion d) m := by
  intro m
  constructor
  · exact collapsed_defines_exactly d
  · intro σ
    rw [collapsed_satisfies_r10_iff]
    simp [collapsedExpansion]

/-- The values m witnessed by this one fixed (i,P) pair. -/
def fixedWitnessValues {D : Type u} (M : Expansion D) : Set Nat :=
  {m | ParameterDefinable M m}

theorem collapsed_fixedWitnessValues_eq_univ {D : Type u} [Nonempty D] (d : D) :
    fixedWitnessValues (collapsedExpansion d) = Set.univ := by
  ext m
  simp [fixedWitnessValues, collapsed_all_parameters_definable d]

theorem collapsed_fixedWitnessValues_infinite {D : Type u} [Nonempty D] (d : D) :
    (fixedWitnessValues (collapsedExpansion d)).Infinite := by
  rw [collapsed_fixedWitnessValues_eq_univ]
  exact Set.infinite_univ

/--
If the natural-code bound q and index i=0 are admitted, the same single
witness pair already contributes every m to the source's candidate set.
The set is infinite, so it cannot be the finite domain of a natural-number sum.
-/
def boundedFixedWitnessValues {D : Type u} (M : Expansion D)
    (n q : Nat) : Set Nat :=
  {m | 0 < n ∧ q < n ∧ ParameterDefinable M m}

theorem collapsed_boundedFixedWitnessValues_eq_univ
    {D : Type u} [Nonempty D] (d : D) {n q : Nat}
    (hn : 0 < n) (hq : q < n) :
    boundedFixedWitnessValues (collapsedExpansion d) n q = Set.univ := by
  ext m
  simp [boundedFixedWitnessValues, hn, hq,
    collapsed_all_parameters_definable d]

theorem collapsed_boundedFixedWitnessValues_infinite
    {D : Type u} [Nonempty D] (d : D) {n q : Nat}
    (hn : 0 < n) (hq : q < n) :
    (boundedFixedWitnessValues (collapsedExpansion d) n q).Infinite := by
  rw [collapsed_boundedFixedWitnessValues_eq_univ d hn hq]
  exact Set.infinite_univ

/--
A necessary condition for the source finite-sum argument:
if a single formula uniquely defines d, then the preimage of d under the
parameter-constant map must be finite. Injectivity of constants is sufficient.
-/
theorem parameterFiber_finite_of_injective {D : Type u}
    (constants : Nat → D) (hInjective : Function.Injective constants)
    (d : D) :
    {m : Nat | constants m = d}.Finite := by
  by_cases h : ∃ m, constants m = d
  · obtain ⟨m₀, hm₀⟩ := h
    have heq : {m : Nat | constants m = d} = {m₀} := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hm
        exact hInjective (hm.trans hm₀.symm)
      · rintro rfl
        exact hm₀
    rw [heq]
    exact Set.finite_singleton m₀
  · have heq : {m : Nat | constants m = d} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => h ⟨m, hm⟩
    rw [heq]
    exact Set.finite_empty

end GardenCanopy.M1Semantics
