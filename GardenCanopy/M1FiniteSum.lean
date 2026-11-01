module

public import Mathlib.Data.Set.Finite.Lattice

public section

namespace GardenCanopy.M1FiniteSum

universe u v

variable {D : Type u} {P : Type v}

/-- The natural indices whose parameter constants denote the unique object defined by (i,p). -/
def pairParameterFiber
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (i : Nat) (p : P) : Set Nat :=
  {m | ∃ d : D, defines i p d ∧ parameter m = d}

/--
If (i,p) defines exactly one object and every parameter fiber is finite,
then the natural indices witnessed by this pair form a finite set.
-/
theorem pairParameterFiber_finite
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (hUnique : ∀ i p, ∃! d : D, defines i p d)
    (hFiber : ∀ d : D, ({m : Nat | parameter m = d} : Set Nat).Finite)
    (i : Nat) (p : P) :
    (pairParameterFiber parameter defines i p).Finite := by
  obtain ⟨d, hd, hUniqueD⟩ := hUnique i p
  apply (hFiber d).subset
  intro m hm
  rcases hm with ⟨d', hd', hParam⟩
  have hEq : d' = d := hUniqueD d' hd'
  simpa [pairParameterFiber, hEq] using hParam

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
Finite-sum theorem: finitely many (i,p) pairs, unique definability of one
model element for each pair, and finite parameter fibers imply that the
union of qualifying natural indices is finite.
-/
theorem boundedCandidateSet_finite
    (parameter : Nat → D) (defines : Nat → P → D → Prop)
    (hUnique : ∀ i p, ∃! d : D, defines i p d)
    (hFiber : ∀ d : D, ({m : Nat | parameter m = d} : Set Nat).Finite)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  unfold boundedCandidateSet
  apply Set.Finite.biUnion (Finset.finite_toSet (Finset.range n))
  intro i hi
  apply Set.Finite.biUnion (Finset.finite_toSet codes)
  intro p hp
  exact pairParameterFiber_finite parameter defines hUnique hFiber i p

/-- Injectivity of a map from Nat makes each point-preimage finite. -/
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
Injectivity of the natural parameter map is a sufficient condition for the
finite-fiber hypothesis, and hence for the bounded candidate set to be finite.
-/
theorem boundedCandidateSet_finite_of_injective
    (parameter : Nat → D) (hInjective : Function.Injective parameter)
    (defines : Nat → P → D → Prop)
    (hUnique : ∀ i p, ∃! d : D, defines i p d)
    (n : Nat) (codes : Finset P) :
    (boundedCandidateSet parameter defines n codes).Finite := by
  apply boundedCandidateSet_finite parameter defines hUnique
  intro d
  exact parameterFiber_finite_of_injective parameter hInjective d

end GardenCanopy.M1FiniteSum
