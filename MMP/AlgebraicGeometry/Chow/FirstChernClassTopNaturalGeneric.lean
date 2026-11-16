module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksEulerClass
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksThomClass
public import MMP.AlgebraicGeometry.Chow.CycleClassFirstChernGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksBaseChangeChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationGeneric
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationThom
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPullback
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicTopology.SingularCohomology.Relative

/-!
# Naturality of `c₁ᵗᵒᵖ` under base change

Let `f : X' ⟶ X` be a morphism of schemes over `ℂ`. For `ℰ` quasi-coherent and locally free of
rank one on `X`, the bundle map `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` of the base change is a fibrewise isomorphism
carrying the zero section to the zero section, so it pulls the Thom class back to the Thom class
and `f^* c₁ᵗᵒᵖ(ℰ) = c₁ᵗᵒᵖ(f^*ℰ)`.

## Main results

* `MMP.Modules.pullback_topFirstChernClass_of_fibrewise`: naturality of `c₁ᵗᵒᵖ` under fibrewise
  isomorphic bundle maps.
* `MMP.Modules.pullback_topFirstChernClass`: `f^* c₁ᵗᵒᵖ(ℰ) = c₁ᵗᵒᵖ(f^*ℰ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite
open MMP.UnderlyingSpace

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

/-! ### Naturality under fibrewise isomorphic bundle maps -/

section Fibrewise

variable (R : Type) [CommRing R] {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] {E : X.Modules} [E.IsQuasicoherent]
  [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
  {E' : X'.Modules} [E'.IsQuasicoherent] [IsFiniteLocallyFreeOfRank.{0, 0, 0} E' 1]
  {f : X' ⟶ X} [f.IsOver (Spec (.of ℂ))] {F : totalSpace E' ⟶ totalSpace E}
  [F.IsOver (Spec (.of ℂ))]

/-- **`c₁ᵗᵒᵖ` is natural under fibrewise isomorphic bundle maps**: for a bundle map
`F : 𝐕(ℰ') ⟶ 𝐕(ℰ)` over `f : X' ⟶ X`, linear and invertible on each fibre and carrying the zero
section to the zero section, `f^* c₁ᵗᵒᵖ(ℰ) = c₁ᵗᵒᵖ(ℰ')`. -/
theorem pullback_topFirstChernClass_of_fibrewise (hπ : F ≫ proj E = proj E' ≫ f)
    (hF : IsFibrewiseIso 1 f F) (h0 : zeroSection E' ≫ F = f ≫ zeroSection E) :
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) univ ((2 * 1 : ℕ) : ℤ)).hom
        (topFirstChernClass R E) :
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X')) univ
        ((2 * 1 : ℕ) : ℤ)) = topFirstChernClass R E' := by
  rw [topFirstChernClass, topFirstChernClass, thomClass_eq_map_of_fibrewise R hπ hF]
  refine (relativeSingularCohomology.map_hom_comp_apply R _ _ _ _
    (fun x hx ↦ (hx (mem_univ _)).elim) _ _).symm.trans
    (Eq.trans ?_ (relativeSingularCohomology.map_hom_comp_apply R _ _ _ _
      (fun x hx ↦ (hx (mem_univ _)).elim) _ _))
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ _)
    (relativeSingularCohomology.map_eq_map_of_hom_eq R (ConcreteCategory.hom_ext _ _ fun p ↦
      (mapFun_mapFun_of_comp (zeroSection E) (zeroSection E') h0 p).symm) _ _ _)

end Fibrewise

/-! ### Naturality of `c₁ᵗᵒᵖ` -/

section Naturality

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

variable (R : Type) [CommRing R] {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] (f : X' ⟶ X) [f.IsOver (Spec (.of ℂ))]

/-- **Naturality of the topological first Chern class** (Fulton, §19.1): for a morphism
`f : X' ⟶ X` of schemes over `ℂ` and `ℰ` quasi-coherent, locally free of rank one on `X`,
`f^* c₁ᵗᵒᵖ(ℰ) = c₁ᵗᵒᵖ(f^*ℰ)` in `H²(X'(ℂ); R)`. -/
theorem pullback_topFirstChernClass (E : X.Modules) [E.IsQuasicoherent]
    [IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1] :
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f)) univ ((2 * 1 : ℕ) : ℤ)).hom
        (topFirstChernClass R E) :
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X')) univ
        ((2 * 1 : ℕ) : ℤ)) = topFirstChernClass R ((Scheme.Modules.pullback f).obj E) :=
  pullback_topFirstChernClass_of_fibrewise R (baseChangeMap_proj f E)
    (isFibrewiseIso_baseChangeMap f E 1) (zeroSection_comp_baseChangeMap E f)

end Naturality

end MMP.Modules
