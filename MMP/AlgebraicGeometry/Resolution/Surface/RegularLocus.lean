/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The regular locus of a scheme of finite type over a field

The singular locus of a scheme locally of finite type over a field, and of the spectrum of one of
its local rings, is closed (such schemes are J-2, and their local rings are excellent); a curve
over a field has finitely many singular points.

## Main results

* `MMP.Resolution.isClosed_setOf_not_isRegularLocalRing`,
  `MMP.Resolution.isClosed_setOf_not_isRegularLocalRing_spec_stalk`
* `MMP.Resolution.finite_singular_closedPoints`

## References

* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5)
* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.19
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution

/-- The structure map `C ⟶ 𝒪_{Y, y}` of a scheme `Y` locally of finite type over `Spec C` is
essentially of finite type: a localization followed by a stalk map of a morphism locally of
finite type. -/
private theorem essFiniteType_stalkStructureMap {C : Type u} [CommRing C] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of C)) [LocallyOfFiniteType f] (y : Y) :
    ((f.stalkMap y).hom.comp ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom).EssFiniteType := by
  have := (f.base y).isPrime
  have h0 : (algebraMap C (Localization.AtPrime (f.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (f.base y).asIdeal.primeCompl
  have h1 : ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of C) (x := f.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of C) (f.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  exact h1.comp (LocallyOfFiniteType.stalkMap f y)

/-- **The regular locus of a scheme of finite type over a field is open.** For a scheme `X` locally
of finite type over a field `k`, the singular locus `Sing X = {x | 𝒪_{X,x} is not regular}` is
closed in `X`. -/
@[mmp "lem_mmp_foundation_excellent_regular_locus_open"]
theorem isClosed_setOf_not_isRegularLocalRing {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    IsClosed {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  exact (Scheme.isJ2_of_locallyOfFiniteType_over_field k sX |>.isOpen_regularLocus
    (𝟙 X)).isClosed_compl

/-- **The regular locus of a local ring of a scheme of finite type over a field is open.** For a
point `x` of a scheme `X` locally of finite type over a field, the singular locus of
`Spec 𝒪_{X,x}` is closed. -/
@[mmp "lem_mmp_foundation_excellent_regular_locus_open"]
theorem isClosed_setOf_not_isRegularLocalRing_spec_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (x : X) :
    IsClosed {y : Spec (X.presheaf.stalk x) |
      ¬ IsRegularLocalRing ((Spec (X.presheaf.stalk x)).presheaf.stalk y)} := by
  have hE : IsExcellent (X.presheaf.stalk x) := by
    let : Algebra k (X.presheaf.stalk x) := ((sX.stalkMap x).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ (sX.base x) (by simp)).hom).toAlgebra
    have : Algebra.EssFiniteType k (X.presheaf.stalk x) := essFiniteType_stalkStructureMap sX x
    exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k)
  exact ((Scheme.isOpen_regularLocus_spec_iff (X.presheaf.stalk x)).mpr
    (hE.1.2.2 _)).isClosed_compl

/-- **An integral algebraic curve has finitely many singular points.** For a curve `C` over a field
`k`, the set of singular closed points `p` (those with `𝒪_{C,p}` not a regular local ring) is
finite. -/
@[mmp "lem_mmp_foundation_curve_singular_points_finite"]
theorem finite_singular_closedPoints {k : Type u} [Field k] {C : Scheme.{u}}
    (sC : C ⟶ Spec (.of k)) [MMP.Mori.IsCurve k sC] :
    {p : C | IsClosed ({p} : Set C) ∧ ¬ IsRegularLocalRing (C.presheaf.stalk p)}.Finite := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have : AlgebraicGeometry.IsNoetherian C := AlgebraicGeometry.IsNoetherian.mk
  exact (Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset
    (AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one (k := k) (f := sC)).le
    (isClosed_setOf_not_isRegularLocalRing sC) fun _ hC ↦
      not_subset_singularLocus_of_mem_irreducibleComponents C hC).subset fun _ hp ↦ hp.2

end MMP.Resolution
