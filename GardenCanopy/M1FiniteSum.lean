module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

open scoped BigOperators

namespace GardenCanopy.M1FiniteSum

universe u v

variable {D : Nat → Type u} {P : Type v}

/--
The natural indices witnessed by a pair (i,p), but only when (i,p) uniquely
defines some element of the model at index i. The domain may vary with i,
matching the source family U(CNF(i)).
-/
def pairParameterFiber
    (parameter : (i : Nat) → Nat → D i)
    (defines : (i : Nat) → P → D i → Prop)
    (i : Nat) (p : P) : Set Nat :=
  {m | (∃! d : D i, defines i p d) ∧
    ∃ d : D i, defines i p d ∧ parameter i m = d}

/--
For a fixed pair (i,p), all qualifying natural indices lie in the one
parameter fiber of the uniquely defined element in the i-th model.
-/
theorem pairParameterFiber_finite
    (parameter : (i : Nat) → Nat → D i)
    (defines : (i : Nat) → P → D i → Prop)
    (hFiber : ∀ i (d : D i),
      ({m : Nat | parameter i m = d} : Set Nat).Finite)
    (i : Nat) (p : P) :
    (pairParameterFiber parameter defines i p).Finite := by
  by_cases hNonempty : ∃ m, m ∈ pairParameterFiber parameter defines i p
  · obtain ⟨m₀, hm₀⟩ := hNonempty
    rcases hm₀ with ⟨⟨d₀, hd₀, hUnique₀⟩, _d₁, _hd₁, _hParam₀⟩
    apply (hFiber i d₀).subset
    intro m hm
    rcases hm with ⟨⟨d, hd, hUnique⟩, d', hd', hParam⟩
    have h₂ : d' = d := hUnique d' hd'
    have h₃ : d = d₀ := hUnique₀ d hd
    exact hParam.trans (h₂.trans h₃)
  · have hEmpty : pairParameterFiber parameter defines i p = ∅ := by
      ext m
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hm => hNonempty ⟨m, hm⟩
    rw [hEmpty]
    exact Set.finite_empty

/--
The set of all natural parameter indices witnessed by finitely many indices i<n
and by formulae in the finite code set codes.
-/
def boundedCandidateSet
    (parameter : (i : Nat) → Nat → D i)
    (defines : (i : Nat) → P → D i → Prop)
    (n : Nat) (codes : Finset P) : Set Nat :=
  ⋃ i ∈ (Finset.range n : Set Nat),
    ⋃ p ∈ (codes : Set P), pairParameterFiber parameter defines i p

/--
Finite-sum support theorem: a finite range of model indices and a finite set
of formula codes, together with finite parameter fibers in each model, imply
that the set of qualifying natural indices is finite. Non-unique formulas
contribute no indices.
-/
theorem boundedCandidateSet_finite
    (parameter : (i : Nat) → Nat → D i)
    (defines : (i : Nat) → P → D i → Prop)
    (hFiber : ∀ i (d : D i),
      ({m : Nat | parameter i m = d} : Set Nat).Finite)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  unfold boundedCandidateSet
  apply Set.Finite.biUnion (Finset.finite_toSet (Finset.range n))
  intro i hi
  apply Set.Finite.biUnion (Finset.finite_toSet codes)
  intro p hp
  exact pairParameterFiber_finite parameter defines hFiber i p

/-- Injectivity of each model's parameter map makes all its fibers finite. -/
theorem parameterFiber_finite_of_injective
    (parameter : (i : Nat) → Nat → D i)
    (hInjective : ∀ i, Function.Injective (parameter i))
    (i : Nat) (d : D i) :
    {m : Nat | parameter i m = d}.Finite := by
  by_cases h : ∃ m, parameter i m = d
  · obtain ⟨m₀, hm₀⟩ := h
    have heq : {m : Nat | parameter i m = d} = {m₀} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hm
        exact hInjective i (hm.trans hm₀.symm)
      · rintro rfl
        exact hm₀
    rw [heq]
    exact Set.finite_singleton m₀
  · have heq : {m : Nat | parameter i m = d} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => h ⟨m, hm⟩
    rw [heq]
    exact Set.finite_empty

/--
Injective parameter interpretations in every model are sufficient, but not
necessary, for the bounded candidate-set finiteness theorem.
-/
theorem boundedCandidateSet_finite_of_injective
    (parameter : (i : Nat) → Nat → D i)
    (hInjective : ∀ i, Function.Injective (parameter i))
    (defines : (i : Nat) → P → D i → Prop)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  apply boundedCandidateSet_finite parameter defines
  intro i d
  exact parameterFiber_finite_of_injective parameter hInjective i d

/--
A finite sum over a set is implemented through its canonical Finset.
Because the summation domain is a set, each natural number is counted once,
regardless of how many witnesses produced its membership.
-/
noncomputable def finiteNaturalSum (s : Set Nat) (hs : s.Finite) : Nat :=
  ∑ m in hs.toFinset, m

/-- Conditional model-relative finite sum over the qualifying parameter indices. -/
noncomputable def boundedCandidateSum
    (parameter : (i : Nat) → Nat → D i)
    (defines : (i : Nat) → P → D i → Prop)
    (hFiber : ∀ i (d : D i),
      ({m : Nat | parameter i m = d} : Set Nat).Finite)
    (n : Nat) (codes : Finset P) : Nat :=
  finiteNaturalSum
    (boundedCandidateSet parameter defines n codes)
    (boundedCandidateSet_finite parameter defines hFiber n codes)

end GardenCanopy.M1FiniteSum
