module

public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing

/-!
# Relatively ample line bundles are positive on exceptional curves

Let `g : X ⟶ Y` be a morphism from a variety and `L` a `g`-ample invertible sheaf. Then
`(L · C) = deg_C L > 0` for every proper curve `C ⊆ X` with `g(C)` a point: over an affine
neighbourhood `V` of the point, `L|_{g⁻¹(V)}` is ample, `C` is a closed subscheme of `g⁻¹(V)`, and
an ample line bundle on a proper curve has positive degree.

## Main results

* `MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori RingedSpaceModuleAdjunction

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Resolution

variable {k : Type u} [Field k]

/-- **A relatively ample line bundle is positive on contracted curves.** Let `X` be a variety,
`g : X ⟶ Y` a morphism, `L` a `g`-ample invertible sheaf and `C ⊆ X` a proper curve with `g(C)`
a point. Then `deg_C L > 0`. -/
theorem degreeOn_pos_of_isRelativelyAmple {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (hX : Mori.IsVariety k sX) (g : X ⟶ Y) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hamp : Mori.IsRelativelyAmple g L) (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < Mori.degreeOn k sX C.ι C.dim_le L := by
  haveI : IsIntegral C.scheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI := hX.toIsSeparated
  haveI := hX.toLocallyOfFiniteType
  haveI := hX.toQuasiCompact
  haveI : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  obtain ⟨V, -, hyV, hampV⟩ := hamp (g C.point)
  have hrange : Set.range C.ι ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hc : C.ι c ∈ closure ({C.point} : Set X) := by
      have : C.ι c ∈ Set.range C.ι := ⟨c, rfl⟩
      unfold ProperCurve.ι curveSubschemeAtι at this
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    show g (C.ι c) ∈ V
    rw [hC _ hc]
    exact hyV
  set j := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι C.ι hrange with hjdef
  have hj : j ≫ (g ⁻¹ᵁ V).ι = C.ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ (g ⁻¹ᵁ V).ι) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j (g ⁻¹ᵁ V).ι
  set M := (modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L with hM
  haveI hMinv : SheafOfModules.IsInvertible (g ⁻¹ᵁ V).toScheme.presheaf
      (g ⁻¹ᵁ V).toScheme.ringCatSheaf.2 M :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (g ⁻¹ᵁ V).ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple (g ⁻¹ᵁ V).toScheme M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hampV
  have h2 := isAmple_pullback_of_isFinite j M h1
  haveI := MMP.Mori.isInvertible_pullback_obj j M
  have h3 := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (C.ι ≫ sX) C.dim_le _ h2
  let e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback C.ι).obj L :=
    (Scheme.Modules.pullback j).mapIso
        ((AlgebraicGeometry.modulePullbackIsoSchemePullback
          (g ⁻¹ᵁ V).ι).app L) ≪≫
      (Scheme.Modules.pullbackComp j (g ⁻¹ᵁ V).ι).app L ≪≫ eqToIso (by rw [hj])
  rw [Mori.degreeOn_eq_invertibleCurveDegree, ← invertibleCurveDegree_eq_of_iso k _ _ e]
  exact h3

end MMP.Threefold.Resolution
