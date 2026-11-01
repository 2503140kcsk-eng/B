module

public import GardenCanopy.M1Semantics
public import GardenCanopy.M1Substitution

public section

namespace GardenCanopy.M1SubstitutionSemantics

open GardenCanopy.M1Syntax
open GardenCanopy.M1Semantics
open GardenCanopy.M1Substitution

universe u

/--
Every source term has a semantic value in every expansion and under every
assignment. This is proved from the inductive evaluation relation itself.
-/
mutual
  theorem termEval_exists {D : Type u} (M : Expansion D) (σ : Nat → D) :
      ∀ t : Term, ∃ d : D, TermEval M σ t d
    | .variable i => ⟨σ i, TermEval.variable i⟩
    | .constant i => ⟨M.constants i, TermEval.constant i⟩
    | .app f args => by
        obtain ⟨values, hValues⟩ := termsEval_exists M σ args
        exact ⟨functionInterpretation M f values, TermEval.app hValues⟩
    termination_by t => sizeOf t
    decreasing_by all_goals simp_wf

  theorem termsEval_exists {D : Type u} (M : Expansion D) (σ : Nat → D) :
      ∀ ts : List Term, ∃ values : List D, TermsEval M σ ts values
    | [] => ⟨[], TermsEval.nil⟩
    | t :: ts => by
        obtain ⟨value, hValue⟩ := termEval_exists M σ t
        obtain ⟨values, hValues⟩ := termsEval_exists M σ ts
        exact ⟨value :: values, TermsEval.cons hValue hValues⟩
    termination_by ts => sizeOf ts
    decreasing_by all_goals simp_wf
end

/-- The evaluation relation assigns at most one value to a term. -/
mutual
  theorem termEval_deterministic {D : Type u} (M : Expansion D) (σ : Nat → D)
      {t : Term} {v w : D} (h₁ : TermEval M σ t v) (h₂ : TermEval M σ t w) :
      v = w := by
    cases h₁ with
    | variable i =>
        cases h₂
        rfl
    | constant i =>
        cases h₂
        rfl
    | app hValues₁ =>
        cases h₂ with
        | app hValues₂ =>
            have hValues := termsEval_deterministic M σ hValues₁ hValues₂
            cases hValues
            rfl

  theorem termsEval_deterministic {D : Type u} (M : Expansion D) (σ : Nat → D)
      {ts : List Term} {vs ws : List D}
      (h₁ : TermsEval M σ ts vs) (h₂ : TermsEval M σ ts ws) :
      vs = ws := by
    cases h₁ with
    | nil =>
        cases h₂
        rfl
    | cons hHead₁ hTail₁ =>
        cases h₂ with
        | cons hHead₂ hTail₂ =>
            have hHead := termEval_deterministic M σ hHead₁ hHead₂
            have hTail := termsEval_deterministic M σ hTail₁ hTail₂
            cases hHead
            cases hTail
            rfl
end

/-- A total, function-valued denotation for terms, selected from TermEval. -/
noncomputable def evalTerm {D : Type u} (M : Expansion D) (σ : Nat → D)
    (t : Term) : D :=
  Classical.choose (termEval_exists M σ t)

/-- The chosen denotation is certified by the source evaluation relation. -/
theorem evalTerm_spec {D : Type u} (M : Expansion D) (σ : Nat → D)
    (t : Term) : TermEval M σ t (evalTerm M σ t) :=
  Classical.choose_spec (termEval_exists M σ t)

/-- Every relational evaluation agrees with the chosen denotation. -/
theorem termEval_eq_evalTerm {D : Type u} (M : Expansion D) (σ : Nat → D)
    {t : Term} {d : D} (h : TermEval M σ t d) :
    d = evalTerm M σ t :=
  termEval_deterministic M σ h (evalTerm_spec M σ t)

end GardenCanopy.M1SubstitutionSemantics
