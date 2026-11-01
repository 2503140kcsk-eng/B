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

/--
Tarskian satisfaction, defined by structural recursion on formulas.
The Boolean connectives are represented by their ordinary propositions.
-/
def Satisfies {D : Type u} (M : Expansion D) (σ : Nat → D) :
    GardenCanopy.M1Syntax.Formula → Prop
  | .falsum => False
  | .implication A B => Satisfies M σ A → Satisfies M σ B
  | .negation A => ¬ Satisfies M σ A
  | .existsQuantifier i A =>
      ∃ d : D, Satisfies M (assignmentUpdate σ i d) A
  | .relation r args =>
      ∃ values : List D,
        TermsEval M σ args values ∧ relationInterpretation M r values

theorem termsEval_variable_zero_iff {D : Type u} (M : Expansion D)
    (σ : Nat → D) (values : List D) :
    TermsEval M σ [GardenCanopy.M1Syntax.Term.variable 0] values
      ↔ values = [σ 0] := by
  constructor
  · intro h
    cases h with
    | cons hHead hTail =>
      cases hHead
      cases hTail
      rfl
  · intro h
    subst values
    exact TermsEval.cons (TermEval.variable 0) TermsEval.nil

/-- The source-language atomic formula r_(1,0)(x₀). -/
def r10Formula : GardenCanopy.M1Syntax.Formula :=
  GardenCanopy.M1Syntax.Formula.relation
    (.generic 1 0)
    [GardenCanopy.M1Syntax.Term.variable 0]

theorem satisfies_r10_iff {D : Type u} (M : Expansion D)
    (σ : Nat → D) :
    Satisfies M σ r10Formula ↔ M.genericRelation 1 0 [σ 0] := by
  unfold Satisfies r10Formula
  constructor
  · rintro ⟨values, hEval, hRel⟩
    have hValues := (termsEval_variable_zero_iff M σ values).1 hEval
    subst values
    simpa [relationInterpretation] using hRel
  · intro hRel
    refine ⟨[σ 0], ?_, ?_⟩
    · exact (termsEval_variable_zero_iff M σ [σ 0]).2 rfl
    · simpa [relationInterpretation] using hRel

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
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hm
        exact hInjective (hm.trans hm₀.symm)
      · rintro rfl
        exact hm₀
    rw [heq]
    exact Set.finite_singleton m₀
  · have heq : {m : Nat | constants m = d} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => h ⟨m, hm⟩
    rw [heq]
    exact Set.finite_empty


/-!
## Sensitivity to arbitrary interpretations of the extra relation symbols

The parameter map is kept fixed below. Only the interpretation of r_(1,0)
changes. This separates dependence on generic relation symbols from any
possible collision among the parameter constants.
-/

/-- An expansion which interprets every generic relation as empty. -/
def emptyGenericRelations {D : Type u} (M : Expansion D) : Expansion D :=
  { M with genericRelation := fun _ _ _ => False }

/-- An expansion in which r_(1,0) denotes the singleton predicate x = d. -/
def singletonR10Relation {D : Type u} (M : Expansion D) (d : D) : Expansion D :=
  { M with genericRelation := fun arity index args =>
      arity = 1 ∧ index = 0 ∧ args = [d] }

/-- The fixed formula r_(1,0)(x₀) is false in the empty-relation expansion. -/
theorem emptyR10_never_satisfied {D : Type u} (M : Expansion D)
    (σ : Nat → D) :
    ¬ Satisfies (emptyGenericRelations M) σ r10Formula := by
  rw [satisfies_r10_iff]
  simp [emptyGenericRelations]

/-- In the singleton expansion, r_(1,0)(x₀) holds exactly when x₀ = d. -/
theorem singletonR10_satisfies_iff {D : Type u} (M : Expansion D) (d : D)
    (σ : Nat → D) :
    Satisfies (singletonR10Relation M d) σ r10Formula ↔ σ 0 = d := by
  rw [satisfies_r10_iff]
  simp [singletonR10Relation]

/-- The singleton interpretation makes r_(1,0)(x₀) uniquely define d. -/
theorem singletonR10_defines_exactly {D : Type u} (M : Expansion D) (d : D) :
    DefinesExactly (singletonR10Relation M d) r10Formula := by
  refine ⟨d, ?_, ?_⟩
  · intro σ
    exact singletonR10_satisfies_iff M d σ
  · intro y hy
    have hs : Satisfies (singletonR10Relation M d) (fun _ => d) r10Formula := by
      exact (singletonR10_satisfies_iff M d (fun _ => d)).2 rfl
    have hEq : d = y := (hy (fun _ => d)).1 hs
    exact hEq.symm

/-- An empty interpretation cannot make r_(1,0)(x₀) uniquely define anything. -/
theorem emptyR10_not_defines {D : Type u} (M : Expansion D) :
    ¬ DefinesExactly (emptyGenericRelations M) r10Formula := by
  rintro ⟨d, hd, _⟩
  have hSat : Satisfies (emptyGenericRelations M) (fun _ => d) r10Formula :=
    (hd (fun _ => d)).2 rfl
  exact emptyR10_never_satisfied M (fun _ => d) hSat

/-- With a fixed parameter map, the singleton relation makes the chosen m definable. -/
theorem singletonR10_parameter_definable {D : Type u} (M : Expansion D)
    (m : Nat) (d : D) (hParam : M.constants m = d) :
    ParameterDefinable (singletonR10Relation M d) m := by
  constructor
  · exact singletonR10_defines_exactly M d
  · intro σ
    rw [singletonR10_satisfies_iff]
    simp [singletonR10Relation, hParam]

/-- With the same fixed parameter map, the empty relation makes no m definable by this P. -/
theorem emptyR10_not_parameter_definable {D : Type u} (M : Expansion D)
    (m : Nat) :
    ¬ ParameterDefinable (emptyGenericRelations M) m := by
  intro h
  exact emptyR10_not_defines M h.1

/--
A precise local non-invariance theorem: changing only r_(1,0) from empty to
the singleton {M.constants m} changes whether the same formula and parameter
satisfy the source-style unique-definability predicate.
-/
theorem arbitrary_relation_interpretation_changes_Definable
    {D : Type u} (M : Expansion D) (m : Nat) :
    ParameterDefinable
        (singletonR10Relation M (M.constants m)) m ∧
      ¬ ParameterDefinable (emptyGenericRelations M) m := by
  constructor
  · exact singletonR10_parameter_definable M m (M.constants m) rfl
  · exact emptyR10_not_parameter_definable M m

end GardenCanopy.M1Semantics
