module

public import GardenCanopy.M1Syntax
public import Mathlib.Data.Finset.Lattice.Fold

public section

namespace GardenCanopy.M1Substitution

open GardenCanopy.M1Syntax

/-- The least natural variable index not occurring in a finite set. -/
theorem newVarExists (s : Finset Nat) : ∃ n : Nat, n ∉ s := by
  refine ⟨s.sup id + 1, ?_⟩
  intro hmem
  have hbound : s.sup id + 1 ≤ s.sup id := by
    simpa using (Finset.le_sup (f := id) hmem)
  omega

noncomputable def newVar (s : Finset Nat) : Nat :=
  Nat.find (newVarExists s)

theorem newVar_not_mem (s : Finset Nat) : newVar s ∉ s :=
  Nat.find_spec (newVarExists s)

theorem newVar_minimal (s : Finset Nat) (n : Nat) (hn : n ∉ s) :
    newVar s ≤ n :=
  Nat.find_min' (newVarExists s) hn

/- Every variable index occurring in a term, including indices in nested arguments. -/
mutual
  def termVars (t : Term) : Finset Nat :=
    match t with
    | .variable i => {i}
    | .constant _ => ∅
    | .app _ args => termsVars args
  termination_by sizeOf t
  decreasing_by
    simp_wf
    omega

  def termsVars (ts : List Term) : Finset Nat :=
    match ts with
    | [] => ∅
    | t :: rest => termVars t ∪ termsVars rest
  termination_by sizeOf ts
  decreasing_by
    simp_wf
end

/- Shape-only size of a term, ignoring the numerical values of variable names. -/
mutual
  def termNodes (t : Term) : Nat :=
    match t with
    | .variable _ => 1
    | .constant _ => 1
    | .app _ args => 1 + termsNodes args
  termination_by sizeOf t
  decreasing_by
    simp_wf

  def termsNodes (ts : List Term) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => termNodes t + termsNodes rest
  termination_by sizeOf ts
  decreasing_by
    simp_wf
end

/-- Every variable index occurring in a formula, including bound indices. -/
def formulaVars : Formula → Finset Nat
  | .falsum => ∅
  | .implication A B => formulaVars A ∪ formulaVars B
  | .negation A => formulaVars A
  | .existsQuantifier i A => insert i (formulaVars A)
  | .relation _ args => termsVars args

/-- Shape-only formula size, independent of variable names. -/
def formulaNodes : Formula → Nat
  | .falsum => 1
  | .implication A B => 1 + formulaNodes A + formulaNodes B
  | .negation A => 1 + formulaNodes A
  | .existsQuantifier _ A => 1 + formulaNodes A
  | .relation _ args => 1 + termsNodes args

/- Capture-safe renaming/substitution of one variable in a term. -/
mutual
  def substituteTermAux (x : Nat) (replacement : Term)
      (rho : Nat → Nat) (active : Bool) (t : Term) : Term :=
    match t with
    | .variable i =>
        if active && decide (i = x) then replacement else .variable (rho i)
    | .constant i => .constant i
    | .app f args => .app f (substituteTermsAux x replacement rho active args)
  termination_by sizeOf t
  decreasing_by
    simp_wf

  def substituteTermsAux (x : Nat) (replacement : Term)
      (rho : Nat → Nat) (active : Bool) (ts : List Term) : List Term :=
    match ts with
    | [] => []
    | t :: rest =>
        substituteTermAux x replacement rho active t ::
          substituteTermsAux x replacement rho active rest
  termination_by sizeOf ts
  decreasing_by
    simp_wf
end

/--
Capture-avoiding substitution of the term replacement for free occurrences of x.
The renaming environment records alpha-renamings of binders already traversed.
The freshness index is exactly the least index absent from the current formula,
the replacement term, and the target variable, as prescribed by the source.
-/
noncomputable def substituteFormulaAux (x : Nat) (replacement : Term)
    (rho : Nat → Nat) (active : Bool) (P : Formula) : Formula :=
  match P with
  | .falsum => .falsum
  | .implication A B =>
      .implication
        (substituteFormulaAux x replacement rho active A)
        (substituteFormulaAux x replacement rho active B)
  | .negation A =>
      .negation (substituteFormulaAux x replacement rho active A)
  | .existsQuantifier i A =>
      if active then
        if i = x then
          .existsQuantifier i
            (substituteFormulaAux x replacement (Function.update rho i i) false A)
        else if i ∈ termVars replacement then
          let z := newVar (formulaVars P ∪ termVars replacement ∪ {x})
          .existsQuantifier z
            (substituteFormulaAux x replacement (Function.update rho i z) true A)
        else
          .existsQuantifier i
            (substituteFormulaAux x replacement (Function.update rho i i) true A)
      else
        .existsQuantifier i
          (substituteFormulaAux x replacement (Function.update rho i i) false A)
  | .relation r args =>
      .relation r (substituteTermsAux x replacement rho active args)
termination_by formulaNodes P
decreasing_by
  all_goals
    simp [formulaNodes] <;> omega

/-- Source-style one-variable capture-avoiding substitution. -/
noncomputable def substituteFormula (P : Formula) (replacement : Term) (x : Nat) : Formula :=
  substituteFormulaAux x replacement id true P

/-- The least fresh variable for a formula is absent from its variable indices. -/
theorem newVar_avoids_formula (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ formulaVars P := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  intro hv
  apply h
  simp only [Finset.mem_union, Finset.mem_singleton]
  exact Or.inl (Or.inl hv)

/-- The least fresh variable for a formula is absent from the replacement term. -/
theorem newVar_avoids_term (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ termVars t := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  intro hv
  apply h
  simp only [Finset.mem_union, Finset.mem_singleton]
  exact Or.inl (Or.inr hv)

/-- The least fresh variable for a formula differs from the substitution target. -/
theorem newVar_ne_target (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ≠ x := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  intro heq
  have hmem : newVar (formulaVars P ∪ termVars t ∪ {x}) ∈
      formulaVars P ∪ termVars t ∪ {x} := by
    rw [heq]
    simp
  exact h hmem


end GardenCanopy.M1Substitution
