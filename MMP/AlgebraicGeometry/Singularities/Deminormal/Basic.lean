/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoCriteria
public import StacksFrontier.RingTheory.Derivation.Regularity

/-!
# The locus `X°` of regular and double-crossing points

FA Remark 2.6 (`def_fa2_discrepancy_nonnormal`) uses, for `X` satisfying (2.6.1), "the open set
`X° ⊆ X` of points that are regular or of the form in (2.6.1)", whose complement has codimension
`≥ 2`. This file defines that locus for all points of `X` and proves the parts of the claim that
need no theory beyond the source.

## The locus

At a codimension-one point the form of (2.6.1) is `𝒪̂_{X,P} ≅ κ(P)[[u, v]]/(uv)`. Read literally
at every point, that form only occurs at points of codimension one, and then the set of regular
points and such points is not open in general (for `X = {xy = 0} ⊆ 𝔸³` it contains the generic
point of the double line but none of its closed points). The form meant at a point `x` of any
codimension is the product of the transversal crossing with a regular germ,
`𝒪̂_{X,x} ≅ κ(x)[[x₀, …, x_{m+1}]]/(x₀x₁)` (`IsDoubleCrossingPoint`), which for `m = 0` is the
form of (2.6.1) and at a closed point of an `n`-fold over an algebraically closed `k` is FA
12.2.1(1)'s double normal crossing point (as rings rather than `k`-algebras).
`doubleCrossingLocus X` is the set of regular points and double-crossing points.

## Main results

* `MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType`: the regular locus of a scheme locally
  of finite type over a field is open (Stacks 07R5, from StacksDraft's J-2 theory).
* `MMP.Flips.mem_doubleCrossingLocus_of_coheight_le_one`: under (2.6.1) every point of
  codimension `≤ 1` lies in `X°`.
* `MMP.Flips.two_le_closedsCodimension_compl`: an open set containing every point of codimension
  `≤ 1` has closed complement of codimension `≥ 2`.
* `MMP.Flips.two_le_closedsCodimension_compl_doubleCrossingLocus`: hence, if `X°` is open, its
  complement has codimension `≥ 2`.

The openness of `X°` itself is not proved here: the double-crossing condition is a condition on
completions, and spreading it from a point to an open neighbourhood needs Artin approximation or
a formal Morse lemma with parameters, neither of which is available.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

namespace MMP.Flips

open MMP.Mori

variable {X : Scheme.{u}}

/-- `x` is a *double-crossing point* of `X`: `𝒪̂_{X,x} ≅ κ(x)[[x₀, …, x_{m+1}]]/(x₀x₁)` as rings
for some `m`, i.e. two regular branches meeting transversally, times a regular germ. For `m = 0`
this is the form `κ(P)[[u, v]]/(uv)` of (2.6.1). -/
def IsDoubleCrossingPoint (x : X) : Prop :=
  ∃ m : ℕ, Nonempty (CompletedLocalRing X x ≃+*
    MvPowerSeries (Fin (m + 2)) (X.residueField x) ⧸
      Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin (m + 2)) (X.residueField x))})

variable (X) in
/-- The locus `X°` of FA Remark 2.6: the points of `X` that are regular or double-crossing
points. -/
def doubleCrossingLocus : Set X :=
  {x | IsRegularLocalRing (X.presheaf.stalk x) ∨ IsDoubleCrossingPoint x}

@[simp]
theorem mem_doubleCrossingLocus_iff {x : X} :
    x ∈ doubleCrossingLocus X ↔ IsRegularLocalRing (X.presheaf.stalk x) ∨ IsDoubleCrossingPoint x :=
  Iff.rfl

/-- Every regular point of `X` lies in `X°`. -/
theorem regularLocus_subset_doubleCrossingLocus : regularLocus X ⊆ doubleCrossingLocus X :=
  fun _ hx ↦ Or.inl hx

/-- **Stacks 07R5.** The regular locus of a scheme locally of finite type over a field is
open. -/
theorem isOpen_regularLocus_of_locallyOfFiniteType {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] : IsOpen (regularLocus X) :=
  Scheme.IsJ2.isOpen_regularLocus
    ((Scheme.isJ2_Spec_iff k).mpr ((isJ2_of_standard_classes_and_finiteType.{u, u}).1 k)) sX

/-- A Noetherian local ring which is a field is regular. -/
theorem isRegularLocalRing_of_isField {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (h : IsField A) : IsRegularLocalRing A := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp h]
  simpa using ringKrullDim_nonneg_of_nontrivial (R := A)

/-- On a reduced locally Noetherian scheme the local ring at a point of codimension zero (a
generic point of an irreducible component) is regular. -/
theorem isRegularLocalRing_stalk_of_coheight_eq_zero [IsReduced X] [IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 0) : IsRegularLocalRing (X.presheaf.stalk x) := by
  have hdim : ringKrullDim (X.presheaf.stalk x) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]; rfl
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact isRegularLocalRing_of_isField Ring.KrullDimLE.isField_of_isReduced

/-- Under (2.6.1) every point of codimension `≤ 1` lies in `X°`: a point of codimension zero is
regular (`X` is reduced), and a point of codimension one is regular or has completion
`κ(P)[[u, v]]/(uv)`. -/
theorem mem_doubleCrossingLocus_of_coheight_le_one {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : SatisfiesFA261 sX) {x : X} (hx : Order.coheight x ≤ 1) :
    x ∈ doubleCrossingLocus X := by
  obtain ⟨hft, -, hred, -, h1⟩ := hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rcases (lt_or_eq_of_le hx).imp Order.lt_one_iff.mp id with h0 | h1'
  · exact Or.inl (isRegularLocalRing_stalk_of_coheight_eq_zero h0)
  · rcases h1 x h1' with hreg | ⟨e⟩
    · exact Or.inl hreg
    · exact Or.inr ⟨0, e⟩

/-- The codimension of an irreducible closed subset is the codimension of its generic point. -/
theorem codimension_eq_coheight_genericPoint (W : IrreducibleCloseds X) :
    codimension W = Order.coheight W.isIrreducible.genericPoint := by
  rw [codimension_eq_coheight]
  exact (Order.coheight_orderIso (irreducibleSetEquivPoints (α := X)) W).symm

/-- An open set containing every point of codimension `≤ 1` has complement of codimension
`≥ 2`. -/
theorem two_le_closedsCodimension_compl {U : Set X} (hU : IsOpen U)
    (hcodim : ∀ x : X, Order.coheight x ≤ 1 → x ∈ U) :
    2 ≤ closedsCodimension (⟨Uᶜ, hU.isClosed_compl⟩ : Closeds X) := by
  refine le_closedsCodimension_iff.mpr fun W hW ↦ ?_
  rw [codimension_eq_coheight_genericPoint]
  by_contra hlt
  have hle : Order.coheight W.isIrreducible.genericPoint ≤ 1 := by
    rw [not_le, ← one_add_one_eq_two] at hlt
    exact ENat.lt_add_one_iff (by simp) |>.mp hlt
  exact hW (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem (hcodim _ hle)

/-- **FA Remark 2.6, codimension of `X ∖ X°`.** If `X` satisfies (2.6.1) and `X°` is open, then
`X ∖ X°` has codimension `≥ 2`. -/
theorem two_le_closedsCodimension_compl_doubleCrossingLocus {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : SatisfiesFA261 sX) (hopen : IsOpen (doubleCrossingLocus X)) :
    2 ≤ closedsCodimension (⟨(doubleCrossingLocus X)ᶜ, hopen.isClosed_compl⟩ : Closeds X) :=
  two_le_closedsCodimension_compl hopen fun _ hx ↦ mem_doubleCrossingLocus_of_coheight_le_one hX hx

end MMP.Flips
