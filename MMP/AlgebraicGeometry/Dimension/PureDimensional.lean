module

public import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Pure-dimensional schemes, with an integer dimension

A scheme `X` is *pure-dimensional of dimension `k`* (Fulton, Appendix B.1) if every irreducible
component of `X`, with its reduced structure, has dimension `k`. The dimension is an integer, so
that expected dimensions such as `dim X + dim Y - dim P` can be stated before they are known to be
nonnegative; an empty scheme is pure-dimensional of every dimension.
`MMP.Intersection.IsPureDimensional X n` is the version with a natural number `n`.

## Main definitions

* `MMP.IsPureDimensional X k`.

## Main results

* `MMP.IsPureDimensional.hasDim_of_nonempty`: a nonempty pure-dimensional scheme has dimension
  `k`, so `0 ≤ k` (`MMP.IsPureDimensional.nonneg`).
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace MMP

open MMP.Intersection (HasDim)

/-- A scheme `X` is *pure-dimensional of dimension `k`* (Fulton, Appendix B.1) if every
irreducible component of `X`, with its reduced structure, has dimension `k`. -/
def IsPureDimensional (X : Scheme.{u}) (k : ℤ) : Prop :=
  ∀ Z ∈ irreducibleComponents X, HasDim Z k

variable {X : Scheme.{u}} {k : ℤ}

/-- Every irreducible component of a pure-dimensional scheme of dimension `k` has dimension
`k`. -/
theorem IsPureDimensional.hasDim (h : IsPureDimensional X k) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) : HasDim Z k :=
  h Z hZ

/-- An empty scheme is pure-dimensional of every dimension `k`. -/
theorem isPureDimensional_of_isEmpty [IsEmpty X] (k : ℤ) : IsPureDimensional X k :=
  fun _ hZ ↦ (IsEmpty.false hZ.1.nonempty.some).elim

/-- The height of an irreducible closed subset `C` of a quasi-sober space, in the poset of
irreducible closed subsets, is the Krull dimension of the subspace `C`. -/
theorem height_irreducibleCloseds_eq {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (C : IrreducibleCloseds α) :
    (Order.height C : WithBot ℕ∞) = topologicalKrullDim (C : Set α) := by
  rw [Order.height_eq_krullDim_Iic,
    Order.krullDim_eq_of_orderIso (MMP.Intersection.Scheme.irreducibleClosedsIicOrderIso C)]
  rfl

/-- A pure-dimensional scheme of dimension `k` that is nonempty has dimension `k`. -/
theorem IsPureDimensional.hasDim_of_nonempty [Nonempty X] (h : IsPureDimensional X k) :
    HasDim X k := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, rfl, hn⟩ := h _ (irreducibleComponent_mem_irreducibleComponents x)
  refine ⟨n, rfl, le_antisymm ?_ ?_⟩
  · unfold topologicalKrullDim
    rw [Order.krullDim_eq_iSup_height]
    refine iSup_le fun T ↦ ?_
    obtain ⟨Z, hZ, hTZ⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible (T : Set X) T.isIrreducible
    let C : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
    obtain ⟨m, hm, hm'⟩ := h Z hZ
    obtain rfl : m = n := by exact_mod_cast hm
    calc (Order.height T : WithBot ℕ∞) ≤ Order.height C := by
          exact_mod_cast Order.height_mono (show T ≤ C from hTZ)
      _ = topologicalKrullDim Z := height_irreducibleCloseds_eq C
      _ = m := hm'
  · rw [← hn]
    exact topologicalKrullDim_subspace_le X _

/-- A nonempty pure-dimensional scheme of dimension `k` has `0 ≤ k`. -/
theorem IsPureDimensional.nonneg [Nonempty X] (h : IsPureDimensional X k) : 0 ≤ k :=
  h.hasDim_of_nonempty.nonneg

end MMP
