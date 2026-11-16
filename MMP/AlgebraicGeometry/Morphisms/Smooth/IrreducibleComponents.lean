/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct

/-!
# Irreducible components of a scheme smooth over a field

A scheme smooth over a field is normal, hence locally irreducible: every point has an
irreducible open neighbourhood. Consequently its irreducible components are open, and two
distinct irreducible components are disjoint.

## Main results

* `MMP.Flips.ResolutionInputs.isOpen_of_mem_irreducibleComponents_of_smooth`: on a scheme
  smooth over a field every irreducible component is open.
* `MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth`: distinct
  irreducible components of a scheme smooth over a field are disjoint.

## Implementation notes

The remaining permanence properties of smooth and étale morphisms used alongside these
(isomorphisms and open immersions are étale, étale morphisms are smooth, stability under
composition and base change, smoothness of `𝔸^n` and of `𝔾_m = Spec R[t, t⁻¹]`, reduced and
normal ascent along smooth morphisms) are `AlgebraicGeometry.Etale.instOfIsOpenImmersion`,
`AlgebraicGeometry.Etale.instSmooth`, `AlgebraicGeometry.smooth_comp`,
`AlgebraicGeometry.smooth_isStableUnderBaseChange`, `AlgebraicGeometry.smooth_affineSpace_over`,
`AlgebraicGeometry.smooth_multiplicativeGroupBaseChange`, `AlgebraicGeometry.isReduced_of_smooth`
and `AlgebraicGeometry.isNormal_of_smooth`, among others.

## References

* [J. Kollár, *Lectures on resolution of singularities*]
* [Stacks Project, Tag 033B, Tag 033C, Tag 033M]
-/
@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips.ResolutionInputs

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]

include f in
/-- A scheme smooth over a field is locally irreducible: every point has an irreducible open
neighbourhood, namely an integral piece of the decomposition of a normal Noetherian affine open
neighbourhood into integral schemes. -/
private theorem exists_isOpen_isIrreducible_of_smooth (z : X) :
    ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ IsIrreducible U := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hzV⟩ : ∃ V : X.affineOpens, z ∈ V.1 := by
    rw [← TopologicalSpace.Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  have : IsAffine V.1.toScheme := V.2
  have : IsNoetherian V.1.toScheme := ⟨⟩
  have : IsNormal V.1.toScheme := isNormal_of_smooth (V.1.ι ≫ f)
  obtain ⟨ι, _, W, _, hint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal V.1.toScheme).mp inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk W).surjective (e.hom ⟨z, hzV⟩)
  rw [sigmaMk_mk] at hw
  let j : W i ⟶ X := Limits.Sigma.ι W i ≫ e.inv ≫ V.1.ι
  have := hint i
  refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, ⟨w, ?_⟩, ?_⟩
  · change V.1.ι (e.inv (Limits.Sigma.ι W i w)) = z
    rw [hw]
    change (e.hom ≫ e.inv ≫ V.1.ι) ⟨z, hzV⟩ = z
    rw [e.hom_inv_id_assoc]
    rfl
  · rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (W i)).image j j.continuous.continuousOn

include f in
/-- On a scheme smooth over a field, two irreducible components through a common point are
equal. -/
theorem eq_of_mem_irreducibleComponents_of_smooth {C C' : Set X}
    (hC : C ∈ irreducibleComponents X) (hC' : C' ∈ irreducibleComponents X) {x : X}
    (hx : x ∈ C) (hx' : x ∈ C') : C = C' := by
  obtain ⟨V, hVo, hxV, hVirr⟩ := exists_isOpen_isIrreducible_of_smooth f x
  exact component_eq_of_open_irreducible_nhd C C' hC hC' V hVo hVirr ⟨x, hx, hxV⟩ ⟨x, hx', hxV⟩

include f in
/-- **The irreducible components of a scheme smooth over a field are open**: such a scheme is
normal, hence every point has an irreducible open neighbourhood. -/
@[mmp "lem_mmp_foundation_kr_smooth_etale_permanence"]
theorem isOpen_of_mem_irreducibleComponents_of_smooth {C : Set X}
    (hC : C ∈ irreducibleComponents X) : IsOpen C := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hVo, hxV, hVirr⟩ := exists_isOpen_isIrreducible_of_smooth f x
  obtain ⟨C', hC', hVC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hVirr
  obtain rfl := eq_of_mem_irreducibleComponents_of_smooth f hC hC' hx (hVC' hxV)
  exact ⟨V, hVC', hVo, hxV⟩

include f in
/-- **Distinct irreducible components of a scheme smooth over a field are disjoint.** -/
@[mmp "lem_mmp_foundation_kr_smooth_etale_permanence"]
theorem disjoint_of_mem_irreducibleComponents_of_smooth {C C' : Set X}
    (hC : C ∈ irreducibleComponents X) (hC' : C' ∈ irreducibleComponents X) (hne : C ≠ C') :
    Disjoint C C' :=
  Set.disjoint_left.mpr fun _ hx hx' =>
    hne (eq_of_mem_irreducibleComponents_of_smooth f hC hC' hx hx')

end MMP.Flips.ResolutionInputs

end
