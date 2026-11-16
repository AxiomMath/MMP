module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.HomotopyPointGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyInfra
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksAgreesSubmanifoldScheme

/-!
# The orientation class of a point of a smooth complex curve, for Stacks vector bundles

Let `T` be a smooth complex curve and `t ∈ T(ℂ)`. The point `t : Spec ℂ → T` is a regular closed
immersion of codimension one (`MMP.UnderlyingSpace.isRegularClosedImmersionOfCodim_toHom`), and
its orientation class `u_{t,T} ∈ H²(T, T - t)` (Fulton §19.2, orientation data on the vector bundle
`𝐕(ℰ)` of a quasi-coherent `𝒪_T`-module, `MMP.Modules.IsRegularImbeddingOrientationClass`) is the
local orientation class of the complex manifold `T(ℂ)` at `t`: the disc criterion
(`MMP.Modules.IsRegularImbeddingOrientationClass.eval_comp_affineSimplex_eq_one`) gives the disc
values of a local orientation class
(`MMP.UnderlyingSpace.isLocalOrientationClass_forget_of_eval_comp_affineSimplex_eq_one`).

## Main results

* `MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set

namespace MMP.Modules

open UnderlyingSpace

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]

/-- **The orientation class of a point of a curve is its local orientation class.** For a
smooth complex curve `T` and `t ∈ T(ℂ)`, the orientation class `u` of the regular closed immersion
`t : Spec ℂ → T` (`MMP.Modules.IsRegularImbeddingOrientationClass`), viewed in `H²(T, T - t)`, is
the local orientation class of the complex manifold `T(ℂ)` at `t` for its complex orientation
(`MMP.UnderlyingSpace.curveOrientationBasis`). -/
theorem isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass (R : Type)
    [CommRing R] (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (t : UnderlyingSpace ℂ T)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R t.toHom 1 u) :
    IsLocalOrientationClass R curveOrientationBasis t
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom u) :=
  isLocalOrientationClass_forget_of_eval_comp_affineSimplex_eq_one R hT t
    fun hα hrep B hB0 hBM _ hB hinj hc hl _ hv ↦
      hu.eval_comp_affineSimplex_eq_one R
        (isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one hT t)
        (isNonsingularPair_toHom (n := 1) t) (exists_tangentConeAt_chartAt_range_map_toHom hT t)
        hα hrep (mem_range_map_toHom_self t) B hB0 hBM hB hinj ⊥
        (tangentConeAt_chartAt_range_map_toHom hT t) hc hl hv

end MMP.Modules
