module

public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Curves.DegreeEuler
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing

/-!
# Relatively ample line bundles are positive on contracted curves, for any `k`-scheme

Let `g : X ⟶ Y` be a morphism of schemes, `X` a scheme over a field `k`, `L` a `g`-ample
invertible sheaf and `C ⊆ X` a proper curve with `g(C)` a point. Over an affine neighbourhood
`V` of the point, `L|_{g⁻¹(V)}` is ample, `C` is a closed subscheme of `g⁻¹(V)`, so `L|_C` is
ample, and an ample line bundle on a proper curve has positive degree `χ(C, L|_C) - χ(C, 𝒪_C)`.
Nothing about `X` is used beyond its structure morphism: `C` is integral of dimension one and
proper over `k`, which makes it a curve.

## Main results

* `MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy`: the degree
  `deg_C L = χ(C, L|_C) - χ(C, 𝒪_C)` is positive, with no hypothesis on `X`.
* `MMP.Threefold.Resolution.lineBundleCurveIntersection_pos_of_isRelativelyAmple`: the
  intersection number `(L · C)`, computed with Kollár's degree of 1.20, is positive on every
  projective curve contracted by `f` (Kollár 2.9–2.11).

## Implementation notes

The intersection number `(L · C)` of `MMP.Resolution.lineBundleCurveIntersection` is Kollár's
degree `MMP.Resolution.degree`, a sum of multiplicities of a rational section, while ampleness
gives positivity of the Euler characteristic degree `MMP.Mori.degreeOn`. The two agree on
invertible sheaves on an integral projective curve by Riemann–Roch
(`MMP.Resolution.degree_eq_invertibleCurveDegree`), which the main result applies to the
projective curve `C`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.20, 2.9
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori RingedSpaceModuleAdjunction

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Resolution

variable {k : Type u} [Field k]

/-- **A relatively ample line bundle is positive on contracted curves.** Let `X` be a scheme over
`k`, `g : X ⟶ Y` a morphism, `L` a `g`-ample invertible sheaf and `C ⊆ X` a proper curve with
`g(C)` a point. Then `0 < deg_C L`. -/
theorem degreeOn_pos_of_isRelativelyAmple_of_isContractedBy {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (g : X ⟶ Y) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hamp : Mori.IsRelativelyAmple g L) (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < Mori.degreeOn k sX C.ι C.dim_le L := by
  have : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) :=
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
    change g (C.ι c) ∈ V
    rw [hC _ hc]
    exact hyV
  set j := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι C.ι hrange
  have hj : j ≫ (g ⁻¹ᵁ V).ι = C.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (j ≫ (g ⁻¹ᵁ V).ι) := by rw [hj]; infer_instance
  have : IsClosedImmersion j := IsClosedImmersion.of_comp j (g ⁻¹ᵁ V).ι
  set M := (modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L
  have hMinv : SheafOfModules.IsInvertible (g ⁻¹ᵁ V).toScheme.presheaf
      (g ⁻¹ᵁ V).toScheme.ringCatSheaf.2 M :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (g ⁻¹ᵁ V).ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple (g ⁻¹ᵁ V).toScheme M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hampV
  have := MMP.Mori.isInvertible_pullback_obj j M
  let e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback C.ι).obj L :=
    (Scheme.Modules.pullback j).mapIso
        ((AlgebraicGeometry.modulePullbackIsoSchemePullback
          (g ⁻¹ᵁ V).ι).app L) ≪≫
      (Scheme.Modules.pullbackComp j (g ⁻¹ᵁ V).ι).app L ≪≫ eqToIso (by rw [hj])
  rw [Mori.degreeOn_eq_invertibleCurveDegree, ← invertibleCurveDegree_eq_of_iso k _ _ e]
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (C.ι ≫ sX) C.dim_le _
    (isAmple_pullback_of_isFinite j M h1)

/-- **A relatively ample line bundle is positive on exceptional curves** (Kollár 2.9–2.11). Let
`X` be a scheme over `k`, `f : X ⟶ Y` a morphism, `L` an `f`-ample invertible sheaf and `C` a
projective curve contracted by `f`. Then `0 < (L · C)`. -/
@[mmp "lem_kr2a_relatively_ample_positive_on_exceptional_curves"]
theorem lineBundleCurveIntersection_pos_of_isRelativelyAmple {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (f : X ⟶ Y) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hamp : Mori.IsRelativelyAmple f L) (C : ProperCurve sX)
    (hC : MMP.Resolution.IsContractedProjectiveCurve sX f C) :
    0 < MMP.Resolution.lineBundleCurveIntersection L C := by
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sX) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC.1 }
  have := MMP.Mori.isInvertible_pullback_obj C.ι L
  unfold MMP.Resolution.lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sX) _ C.dim_le,
    ← Mori.degreeOn_eq_invertibleCurveDegree]
  exact degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f L hamp C hC.2

end MMP.Threefold.Resolution
