module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence

/-!
# Ordered divisor tuples

An *ordered divisor tuple* `(V, (I_1, …, I_m), E)` over a field `k` of characteristic zero is a
smooth variety `V` over `k`, a finite ordered list `(I_1, …, I_m)` of nonzero invertible ideal
sheaves on `V` and an ordered simple normal crossing divisor `E` on `V`. Its *snc locus* is the
set of points `x ∈ V` at which the `I_j` with `x ∈ cosupp I_j` are distinct coordinate ideals
of multiplicity one and the entries of `E` through `x` are further, distinct coordinate
hyperplanes: there is a regular system of parameters `z_1, …, z_n` of `𝒪_{V,x}` with
`I_j·𝒪_{V,x} = (z_{c(j)})` and `E^i·𝒪_{V,x} = (z_{c(i)})`, all these coordinates being
distinct.

This follows the explicit ordered-ideal construction of Kollár's semi-log resolutions,
Proposition 6.

## Main definitions

* `MMP.Resolution.OrderedDivisorTuple`: the data `((I_1, …, I_m), E)` on a scheme `V`.
* `MMP.Resolution.IsOrderedDivisorTuple`: `(V, (I_j), E)`, `V` over `k`, is an ordered divisor
  tuple.
* `MMP.Resolution.OrderedDivisorTuple.divisors`: the family `(I_1, …, I_m, E^1, …, E^s)`.
* `MMP.Resolution.OrderedDivisorTuple.indicesAt`: the `I_j` and `E^i` whose cosupport contains
  a point.
* `MMP.Resolution.OrderedDivisorTuple.sncLocus`: the snc locus.

## Main results

* `MMP.Resolution.OrderedDivisorTuple.sncLocus_eq_univ_of_isSNCFamily`: if `∑ I_j + ∑ E^i` is
  an snc family, the snc locus is everything.
* `MMP.Resolution.OrderedDivisorTuple.mem_sncLocus_of_notMem_support`: a point with a regular
  system of parameters lying in no cosupport and on no boundary entry is in the snc locus.

## Implementation notes

The tuple is unbundled: `OrderedDivisorTuple V` carries the ideals and the boundary, and `V` is
over `k` by an explicit `s_V : V ⟶ Spec k`, as for `MMP.Resolution.IsTriple`. A blow-up
`π : Bl_C V → V` is then over `k` by `π ≫ s_V`, and a transform of the tuple is an
`OrderedDivisorTuple (blowUp C)`.

An invertible ideal sheaf is `Stacks.Divisors.IsEffectiveCartierDivisor`. Cosupports are
`Scheme.IdealSheafData.support`; `x ∈ cosupp I_j` is the condition `I_j·𝒪_{V,x} ≠ 𝒪_{V,x}`,
the source's "`I_j` is a nonunit at `x`".

The entries `E^i` of an ordered snc divisor may be reducible, but each is smooth, so its stalk
at a point `x ∈ E^i` is the ideal of the unique irreducible component of `E^i` through `x`;
the components of `E` through `x` are thus the entries `E^i` with `x ∈ E^i`, each counted
once, and these are the ones asked to be coordinate hyperplanes. Multiplicity one is the
stalk being exactly `(z_{c(j)})`, not a power of it.

The coordinate assignment `c` is defined only on the indices whose cosupport contains `x`
(`OrderedDivisorTuple.indicesAt`), so a point lying on none of them is in the snc locus even
when `𝒪_{V,x}` has no parameters at all.

## References

* [J. Kollár, *Semi log resolutions*, arXiv:0812.3592, Proposition 6]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Resolution

/-- The data of an ordered divisor tuple on a scheme `V`: a finite ordered list
`(I_1, …, I_m)` of ideal sheaves and an ordered divisor `E = (E^1, …, E^s)`. It is an ordered
divisor tuple when `IsOrderedDivisorTuple` holds. -/
@[mmp "def_mmp_ordered_divisor_tuple"]
structure OrderedDivisorTuple (V : Scheme.{u}) where
  /-- The number `m` of ideals. -/
  m : ℕ
  /-- The ideals `I_1, …, I_m`. -/
  I : Fin m → V.IdealSheafData
  /-- The boundary `E`. -/
  E : OrderedDivisor V

section Defs

variable {k : Type u} [Field k] {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))

/-- `(V, (I_1, …, I_m), E)`, `V` over `k` by `s_V`, is an *ordered divisor tuple*: `k` has
characteristic zero, `V` is a smooth variety over `k`, every `I_j` is a nonzero invertible ideal
sheaf and `E` is an ordered snc divisor. -/
@[mmp "def_mmp_ordered_divisor_tuple"]
def IsOrderedDivisorTuple (T : OrderedDivisorTuple V) : Prop :=
  CharZero k ∧ MMP.Mori.IsVariety k sV ∧ MMP.Mori.IsSmoothScheme sV ∧
    (∀ j, T.I j ≠ ⊥ ∧ Stacks.Divisors.IsEffectiveCartierDivisor (T.I j)) ∧ T.E.IsOrderedSNC sV

end Defs

namespace OrderedDivisorTuple

variable {V : Scheme.{u}} (T : OrderedDivisorTuple V)

/-- The family `(I_1, …, I_m, E^1, …, E^s)` of the ideals and the boundary entries of a tuple,
indexed by `Fin m ⊕ Fin s`. -/
def divisors : Fin T.m ⊕ Fin T.E.s → V.IdealSheafData :=
  Sum.elim T.I T.E.E

/-- The entry of `divisors` at the index of the ideal `I_j` is `I_j`. -/
@[simp]
theorem divisors_inl (j : Fin T.m) : T.divisors (.inl j) = T.I j := rfl

/-- The entry of `divisors` at the index of the boundary entry `E^i` is `E^i`. -/
@[simp]
theorem divisors_inr (i : Fin T.E.s) : T.divisors (.inr i) = T.E.E i := rfl

/-- The indices `p` of the ideals and boundary entries whose cosupport contains `x`: the `I_j`
that are nonunits at `x` and the `E^i` through `x`. -/
def indicesAt (x : V) : Type :=
  {p : Fin T.m ⊕ Fin T.E.s // x ∈ (T.divisors p).support}

/-- The *snc locus* of an ordered divisor tuple: the points `x` with a regular system of
parameters `z_1, …, z_n` of `𝒪_{V,x}` and an injective assignment `c` of coordinates to the
ideals `I_j` with `x ∈ cosupp I_j` and the boundary entries `E^i` through `x` such that
`I_j·𝒪_{V,x} = (z_{c(j)})` and `E^i·𝒪_{V,x} = (z_{c(i)})`. -/
@[mmp "def_mmp_ordered_divisor_tuple"]
def sncLocus : Set V :=
  {x | ∃ (n : ℕ) (z : Fin n → V.presheaf.stalk x) (c : T.indicesAt x → Fin n),
    MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective c ∧
      ∀ p, IdealSheafData.stalk (T.divisors p.1) x = Ideal.span {z (c p)}}

/-- If `∑ I_j + ∑ E^i` is a simple normal crossing family, the snc locus is all of `V`. -/
theorem sncLocus_eq_univ_of_isSNCFamily {k : Type u} [Field k] {sV : V ⟶ Spec (.of k)}
    (h : IsSNCFamily sV T.divisors) : T.sncLocus = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h.2 x
  exact ⟨n, z, c, hz, hinj, hc⟩

/-- A point at which `𝒪_{V,x}` has a regular system of parameters and which lies in no
cosupport `cosupp I_j` and on no boundary entry is in the snc locus. -/
theorem mem_sncLocus_of_notMem_support {x : V} {n : ℕ} {z : Fin n → V.presheaf.stalk x}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) (hx : ∀ p, x ∉ (T.divisors p).support) :
    x ∈ T.sncLocus :=
  ⟨n, z, fun p => (hx _ p.2).elim, hz, fun p => (hx _ p.2).elim, fun p => (hx _ p.2).elim⟩

end OrderedDivisorTuple

end MMP.Resolution
