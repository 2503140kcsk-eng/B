module

public import GardenCanopy.M1Syntax
public import Mathlib.Data.Finset.Lattice.Fold

public section

namespace GardenCanopy.M1Substitution

open GardenCanopy.M1Syntax

/-- Map a dependent function over a list while retaining membership evidence
for each recursive element. This is useful for the nested list of terms. -/
def mapTermsWith : (xs : List Term) → (∀ t, t ∈ xs → Term) → List Term
  | [], _ => []
  | t :: ts, f =>
      f t (by simp) :: mapTermsWith ts (fun u hu => f u (by simp [hu]))

/-- Fold the subterms of a term, retaining the membership evidence supplied by Term.rec. -/
def foldTermVars : (xs : List Term) → (∀ t, t ∈ xs → Finset Nat) → Finset Nat
  | [], _ => ∅
  | t :: ts, f =>
      f t (by simp) ∪ foldTermVars ts (fun u hu => f u (by simp [hu]))

/-- Fold the node counts of nested subterms. -/
def foldTermNodes : (xs : List Term) → (∀ t, t ∈ xs → Nat) → Nat
  | [], _ => 0
  | t :: ts, f =>
      f t (by simp) + foldTermNodes ts (fun u hu => f u (by simp [hu]))

/-- Every variable index occurring in a term, irrespective of binding context. -/
def termVars (t : Term) : Finset Nat :=
  Term.rec (motive := fun _ => Finset Nat)
    (fun i => {i})
    (fun _ => ∅)
    (fun _ args ih => foldTermVars args ih)
    t

/-- Every variable index occurring in a formula, including bound indices. -/
def formulaVars : Formula → Finset Nat
  | .falsum => ∅
  | .implication A B => formulaVars A ∪ formulaVars B
  | .negation A => formulaVars A
  | .existsQuantifier i A => insert i (formulaVars A)
  | .relation _ args => foldTermVars args (fun t _ => termVars t)

/-- A shape-only size, ignoring the numerical values used as variable names. -/
def termNodes (t : Term) : Nat :=
  Term.rec (motive := fun _ => Nat)
    (fun _ => 1)
    (fun _ => 1)
    (fun _ args ih => 1 + foldTermNodes args ih)
    t

/-- Shape-only formula size; renaming a variable cannot change this measure. -/
def formulaNodes : Formula → Nat
  | .falsum => 1
  | .implication A B => 1 + formulaNodes A + formulaNodes B
  | .negation A => 1 + formulaNodes A
  | .existsQuantifier _ A => 1 + formulaNodes A
  | .relation _ args => 1 + foldTermNodes args (fun t _ => termNodes t)

/--
The least natural variable index not occurring in a finite set of variable
indices. This is New(S) from the source, not an arbitrary fresh upper bound.
-/
noncomputable def newVar (s : Finset Nat) : Nat :=
  Nat.find (show ∃ n : Nat, n ∉ s from by
    refine ⟨s.sup id + 1, ?_⟩
    intro hmem
    have hbound : id (s.sup id + 1) ≤ s.sup id :=
      Finset.le_sup (f := id) hmem
    omega)

theorem newVar_not_mem (s : Finset Nat) : newVar s ∉ s :=
  Nat.find_spec _

theorem newVar_minimal (s : Finset Nat) (n : Nat) (hn : n ∉ s) :
    newVar s ≤ n :=
  Nat.find_min' _ hn

/-- Capture-safe renaming/substitution of one variable in a term.
rho records alpha-renamings of binders already traversed; when active=false,
the target variable is bound and substitution is suspended, but outer alpha
renamings are still propagated. -/
def substituteTermAux (x : Nat) (replacement : Term)
    (rho : Nat → Nat) (active : Bool) (t : Term) : Term :=
  Term.rec (motive := fun _ => Term)
    (fun i =>
      if active && decide (i = x) then replacement else .variable (rho i))
    (fun i => .constant i)
    (fun f args ih => .app f (mapTermsWith args ih))
    t

/-- A helper showing that term substitution preserves the syntax-tree shape. -/
theorem substituteTermAux_nodes (x : Nat) (replacement : Term)
    (rho : Nat → Nat) (active : Bool) (t : Term) :
    termNodes (substituteTermAux x replacement rho active t) = termNodes t := by
  induction t using Term.rec with
  | variable i =>
      simp [substituteTermAux, termNodes]
  | constant i =>
      simp [substituteTermAux, termNodes]
  | app f args ih =>
      simp [substituteTermAux, termNodes, foldTermNodes, ih]

/--
Capture-avoiding substitution of the term replacement for free occurrences
of variable x. It follows the source New convention: when a binder would
capture a variable of replacement, rename that binder to the least variable
not occurring in the whole input formula, replacement term, target variable,
or any fresh name already introduced during this traversal.
-/
def substituteFormulaAux (x : Nat) (replacement : Term)
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
      .relation r
        (mapTermsWith args (fun t _ => substituteTermAux x replacement rho active t))
termination_by P => formulaNodes P
decreasing_by
  all_goals
    simp [formulaNodes]
    omega

/-- Source-style one-variable capture-avoiding substitution. -/
def substituteFormula (P : Formula) (replacement : Term) (x : Nat) : Formula :=
  substituteFormulaAux x replacement id true
    (formulaVars P ∪ termVars replacement ∪ {x}) P

/-- The initial fresh-name set contains every variable in the formula. -/
theorem initialNew_avoids_formula (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ formulaVars P := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
  intro hp
  exact h (Or.inl (Or.inl hp))

/-- The initial fresh-name set contains every variable in the substituting term. -/
theorem initialNew_avoids_term (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ∉ termVars t := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
  intro ht
  exact h (Or.inl (Or.inr ht))

/-- The chosen new variable differs from the substitution target. -/
theorem initialNew_ne_target (P : Formula) (t : Term) (x : Nat) :
    newVar (formulaVars P ∪ termVars t ∪ {x}) ≠ x := by
  have h := newVar_not_mem (formulaVars P ∪ termVars t ∪ {x})
  simp only [Finset.mem_union, Finset.mem_singleton] at h
  intro heq
  subst x
  exact h (Or.inr rfl)

end GardenCanopy.M1Substitution
