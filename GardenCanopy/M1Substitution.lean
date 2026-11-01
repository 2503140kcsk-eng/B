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
  termination_by t => sizeOf t
  decreasing_by
    simp_wf
    omega

  def termsVars (ts : List Term) : Finset Nat :=
    match ts with
    | [] => ∅
    | t :: rest => termVars t ∪ termsVars rest
  termination_by ts => sizeOf ts
  decreasing_by
    simp_wf
    omega
end

/- Shape-only size of a term, ignoring the numerical values of variable names. -/
mutual
  def termNodes (t : Term) : Nat :=
    match t with
    | .variable _ => 1
    | .constant _ => 1
    | .app _ args => 1 + termsNodes args
  termination_by t => sizeOf t
  decreasing_by
    simp_wf
    omega

  def termsNodes (ts : List Term) : Nat :=
    match ts with
    | [] => 0
    | t :: rest => termNodes t + termsNodes rest
  termination_by ts => sizeOf ts
  decreasing_by
    simp_wf
    omega
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
  termination_by t => sizeOf t

  def substituteTermsAux (x : Nat) (replacement : Term)
      (rho : Nat → Nat) (active : Bool) (ts : List Term) : List Term :=
    match ts with
    | [] => []
    | t :: rest =>
        substituteTermAux x replacement rho active t ::
          substituteTermsAux x replacement rho active rest
  termination_by ts => sizeOf ts
end
termination_by
  substituteTermAux _ _ _ _ t => sizeOf t
  substituteTermsAux _ _ _ _ ts => sizeOf ts
decreasing_by
  all_goals
    simp_wf
    omega

/--
Capture-avoiding substitution of the term replacement for free occurrences of x.
rho records alpha-renamings of binders already traversed. When active=false,
the target variable is bound and substitution is suspended, while outer alpha
renamings are still propagated.
-/
noncomputable def substituteFormulaAux (x : Nat) (replacement : Term)
    (rho : Nat → Nat) (active : Bool) (used : Finset Nat) :
    Formula → Formula
  | .falsum => .falsum
  | .implication A B =>
      .implication
        (substituteFormulaAux x replacement rho active used A)
        (substituteFormulaAux x replacement rho active used B)
  | .negation A =>
      .negation (substituteFormulaAux x replacement rho active used A)
  | .existsQuantifier i A =>
      if active then
        if i = x then
          .existsQuantifier i
            (substituteFormulaAux x replacement (Function.update rho i i) false used A)
        else if i ∈ termVars replacement then
          let z := newVar used
          .existsQuantifier z
            (substituteFormulaAux x replacement (Function.update rho i z) true
              (insert z used) A)
        else
          .existsQuantifier i
            (substituteFormulaAux x replacement (Function.update rho i i) true used A)
      else
        .existsQuantifier i
          (substituteFormulaAux x replacement (Function.update rho i i) false used A)
  | .relation r args =>
      .relation r (substituteTermsAux x replacement rho active args)
termination_by P => formulaNodes P
decreasing_by
  all_goals
    simp [formulaNodes]

/-- Source-style one-variable capture-avoiding substitution. -/
noncomputable def substituteFormula (P : Formula) (replacement : Term) (x : Nat) : Formula :=
  substituteFormulaAux x replacement id true
    (formulaVars P ∪ termVars replacement ∪ {x}) P

/-- The initial fresh-name set contains every variable in the formula. -/
theorem initialNew_avoids_formula (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ formulaVars P := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  have hp : formulaVars P ⊆ formulaVars P ∪ termVars t ∪ {x} := by
    simp
  exact fun hmem => h (hp hmem)

/-- The initial fresh-name set contains every variable in the substituting term. -/
theorem initialNew_avoids_term (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ termVars t := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  have ht : termVars t ⊆ formulaVars P ∪ termVars t ∪ {x} := by
    simp
  exact fun hmem => h (ht hmem)

/-- The chosen new variable differs from the substitution target. -/
theorem initialNew_ne_target (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ≠ x := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  intro heq
  apply h
  rw [heq]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self x)

end GardenCanopy.M1Substitution
