module

public import Mathlib.Data.Set.Finite.Lattice

public section

namespace GardenCanopy.M1FiniteSum

universe u v

variable {D : Type u} {P : Type v}

/--
The natural indices witnessed by a pair (i,p), but only when (i,p) uniquely
defines some domain element. The outer existential unique condition mirrors
the source's IsDefinition(P); if uniqueness fails, this set is empty.
-/
def pairParameterFiber
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (i : Nat) (p : P) : Set Nat :=
  {m | (∃! d : D, defines i p d) ∧
    ∃ d : D, defines i p d ∧ parameter m = d}

/--
For a fixed pair (i,p), all qualifying natural indices lie in the one
parameter fiber of the uniquely defined domain element.
-/
theorem pairParameterFiber_finite
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (hFiber : ∀ d : D, ({m : Nat | parameter m = d} : Set Nat).Finite)
    (i : Nat) (p : P) :
    (pairParameterFiber parameter defines i p).Finite := by
  by_cases hNonempty : ∃ m, m ∈ pairParameterFiber parameter defines i p
  · obtain ⟨m₀, hm₀⟩ := hNonempty
    rcases hm₀ with ⟨⟨d₀, hd₀, hUnique₀⟩, d₁, hd₁, hParam₀⟩
    have h₁ : d₁ = d₀ := hUnique₀ d₁ hd₁
    have hParam₀' : parameter m₀ = d₀ := hParam₀.trans h₁
    apply (hFiber d₀).subset
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
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (n : Nat) (codes : Finset P) : Set Nat :=
  ⋃ i ∈ (Finset.range n : Set Nat),
    ⋃ p ∈ (codes : Set P), pairParameterFiber parameter defines i p

/--
Finite-sum support theorem: a finite range of indices and a finite set of
formula codes, together with finite parameter fibers, imply that the set of
qualifying natural indices is finite. Uniqueness is already part of
pairParameterFiber; formulas that do not uniquely define an element add no m.
-/
theorem boundedCandidateSet_finite
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (hFiber : ∀ d : D, ({m : Nat | parameter m = d} : Set Nat).Finite)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  unfold boundedCandidateSet
  apply Set.Finite.biUnion (Finset.finite_toSet (Finset.range n))
  intro i hi
  apply Set.Finite.biUnion (Finset.finite_toSet codes)
  intro p hp
  exact pairParameterFiber_finite parameter defines hFiber i p

/-- Injectivity of the natural parameter map makes all parameter fibers finite. -/
theorem parameterFiber_finite_of_injective
    (parameter : Nat → D) (hInjective : Function.Injective parameter)
    (d : D) :
    {m : Nat | parameter m = d}.Finite := by
  by_cases h : ∃ m, parameter m = d
  · obtain ⟨m₀, hm₀⟩ := h
    have heq : {m : Nat | parameter m = d} = {m₀} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hm
        exact hInjective (hm.trans hm₀.symm)
      · rintro rfl
        exact hm₀
    rw [heq]
    exact Set.finite_singleton m₀
  · have heq : {m : Nat | parameter m = d} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => h ⟨m, hm⟩
    rw [heq]
    exact Set.finite_empty

/--
Injective parameter interpretations are a sufficient, but not necessary,
condition for the finite candidate-set theorem.
-/
theorem boundedCandidateSet_finite_of_injective
    (parameter : Nat → D) (hInjective : Function.Injective parameter)
    (defines : Nat → P → D → Prop)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  apply boundedCandidateSet_finite parameter defines
  intro d
  exact parameterFiber_finite_of_injective parameter hInjective d

/--
A finite sum over a set is implemented through its canonical Finset.
Because the summation domain is a set, each natural number is counted once,
regardless of how many witnesses produced its membership.
-/
noncomputable def finiteNaturalSum (s : Set Nat) (hs : s.Finite) : Nat :=
  ∑ m in hs.toFinset, m

/-- Conditional model-relative finite sum over the qualifying parameter indices. -/
noncomputable def boundedCandidateSum
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (hFiber : ∀ d : D, ({m : Nat | parameter m = d} : Set Nat).Finite)
    (n : Nat) (codes : Finset P) : Nat :=
  finiteNaturalSum
    (boundedCandidateSet parameter defines n codes)
    (boundedCandidateSet_finite parameter defines hFiber n codes)

end GardenCanopy.M1FiniteSum
