module

public import GardenCanopy.M1Syntax
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic

public section

namespace GardenCanopy.M1Semantics

universe u

open GardenCanopy.M1Syntax

/--
An expansion of the source language on a carrier D. The interpretations of
c_i, f_(a,i), and r_(a,i) are independent functions with no injectivity
or invariance hypotheses.
-/
structure Expansion (D : Type u) where
  defaultElement : D
  constants : Nat → D
  genericFunction : Nat → Nat → List D → D
  genericRelation : Nat → Nat → List D → Prop
  membership : D → D → Prop
  unaryU : D → D
  theta : D → D

/-- Update one variable while leaving all other variables unchanged. -/
def assignmentUpdate {D : Type u} (σ : Nat → D) (i : Nat) (d : D) : Nat → D :=
  fun j => if j = i then d else σ j

@[simp] theorem assignmentUpdate_same {D : Type u} [DecidableEq Nat]
    (σ : Nat → D) (i : Nat) (d : D) :
    assignmentUpdate σ i d i = d := by
  simp [assignmentUpdate]

@[simp] theorem assignmentUpdate_other {D : Type u} [DecidableEq Nat]
    (σ : Nat → D) (i j : Nat) (d : D) (h : j ≠ i) :
    assignmentUpdate σ i d j = σ j := by
  simp [assignmentUpdate, h]

def functionInterpretation {D : Type u} (M : Expansion D) :
    GardenCanopy.M1Syntax.FunctionSymbol → List D → D
  | .unaryU, [x] => M.unaryU x
  | .theta, [x] => M.theta x
  | .generic arity index, args =>
      M.genericFunction arity index args
  | _, _ => M.defaultElement

def relationInterpretation {D : Type u} (M : Expansion D) :
    GardenCanopy.M1Syntax.RelationSymbol → List D → Prop
  | .membership, [x, y] => M.membership x y
  | .generic arity index, args =>
      M.genericRelation arity index args
  | _, _ => False

mutual
  inductive TermEval {D : Type u} (M : Expansion D) (σ : Nat → D) :
      GardenCanopy.M1Syntax.Term → D → Prop where
    | variable (i : Nat) :
        TermEval M σ (GardenCanopy.M1Syntax.Term.variable i) (σ i)
    | constant (i : Nat) :
        TermEval M σ (GardenCanopy.M1Syntax.Term.constant i) (M.constants i)
    | app {f : GardenCanopy.M1Syntax.FunctionSymbol}
        {args : List GardenCanopy.M1Syntax.Term} {values : List D}
        (h : TermsEval M σ args values) :
        TermEval M σ (GardenCanopy.M1Syntax.Term.app f args)
          (functionInterpretation M f values)

  inductive TermsEval {D : Type u} (M : Expansion D) (σ : Nat → D) :
      List GardenCanopy.M1Syntax.Term → List D → Prop where
    | nil : TermsEval M σ [] []
    | cons {t : GardenCanopy.M1Syntax.Term}
        {ts : List GardenCanopy.M1Syntax.Term} {x : D} {xs : List D}
        (ht : TermEval M σ t x) (hs : TermsEval M σ ts xs) :
        TermsEval M σ (t :: ts) (x :: xs)
end

/-- Tarskian satisfaction, relative to an expansion and variable assignment. -/
inductive Satisfies {D : Type u} (M : Expansion D) :
    (Nat → D) → GardenCanopy.M1Syntax.Formula → Prop where
  | implication {σ : Nat → D} {A B : GardenCanopy.M1Syntax.Formula}
      (h : Satisfies M σ A → Satisfies M σ B) :
      Satisfies M σ (GardenCanopy.M1Syntax.Formula.implication A B)
  | negation {σ : Nat → D} {A : GardenCanopy.M1Syntax.Formula}
      (h : Satisfies M σ A → False) :
      Satisfies M σ (GardenCanopy.M1Syntax.Formula.negation A)
  | existsQuantifier {σ : Nat → D} {i : Nat}
      {A : GardenCanopy.M1Syntax.Formula} (d : D)
      (h : Satisfies M (assignmentUpdate σ i d) A) :
      Satisfies M σ (GardenCanopy.M1Syntax.Formula.existsQuantifier i A)
  | relation {σ : Nat → D} {r : GardenCanopy.M1Syntax.RelationSymbol}
      {args : List GardenCanopy.M1Syntax.Term} {values : List D}
      (heval : TermsEval M σ args values)
      (hrel : relationInterpretation M r values) :
      Satisfies M σ (GardenCanopy.M1Syntax.Formula.relation r args)

/-- The source-language atomic formula r_(1,0)(x₀). -/
def r10Formula : GardenCanopy.M1Syntax.Formula :=
  GardenCanopy.M1Syntax.Formula.relation
    (.generic 1 0)
    [GardenCanopy.M1Syntax.Term.variable 0]

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
A permitted arbitrary expansion in which every parameter c_i denotes d,
every generic function returns d, and r_(1,0) has extension {d}.
All other generic relations are empty.
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

/-- A formula uniquely defines d if every assignment satisfies it exactly at d. -/
def DefinesExactly {D : Type u} (M : Expansion D)
    (P : GardenCanopy.M1Syntax.Formula) : Prop :=
  ExistsUnique (fun d : D =>
    ∀ σ : Nat → D, Satisfies M σ P ↔ σ 0 = d)

/--
The m-th parameter c_m denotes the unique object defined by r_(1,0)(x₀).
This is the semantic core of Definable for i=0 and this fixed formula.
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
    change Satisfies (collapsedExpansion d) σ r10Formula ↔ σ 0 = d
    exact collapsed_satisfies_r10_iff d σ

/-- Natural indices witnessed by this one fixed formula and model. -/
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
If n and q satisfy the source's finite code bounds, the same fixed witness
still makes every natural m definable in this arbitrary expansion.
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

/-- Injectivity of the parameter map makes every parameter fiber finite. -/
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
