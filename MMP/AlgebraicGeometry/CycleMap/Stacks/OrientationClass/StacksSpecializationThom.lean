module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.AlgebraicEquivalence.PointSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksHomotopyPoint
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksLineSectionZero

/-!
# The orientation class of a point of a curve as a localized first Chern class, for Stacks bundles

Let `T` be a smooth complex curve, `t ∈ T(ℂ)`, `ℰ` a quasi-coherent `𝒪_T`-module, finite locally
free of rank one, and `σ : T ⟶ 𝐕(ℰ)` a section whose zero scheme `Z(σ)` is the reduced point `t`
(for instance the section `σ_s : T ⟶ 𝐕(𝒩^∨)` of a global section `s` of an invertible module `𝒩`
with `Z(s) = t`, `MMP.Modules.globalSectionMap`). Then the orientation class `u_{t,T}` of the
regular closed immersion `t : Spec ℂ → T` (Fulton §19.2) is the pull-back `σ^*(u_ℰ)` of the Thom
class, both in `H²(T, T - t)` (Fulton, proof of Lemma 19.1.3: "`s_t` has a simple zero, so it is
transversal to the zero section and `u_{t,T} = s_t^*(u_L)`").

**Proof.** Both classes are the local orientation class of the complex manifold `T(ℂ)` at `t`:
`u_{t,T}` by the disc criterion
(`MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass`), `σ^*(u_ℰ)`
because `σ` has a simple zero at `t` (`MMP.Modules.injective_chartDeriv_chartLocalCoord`,
`MMP.Modules.isLocalOrientationClass_forget_pullback_thomClass`); and a local orientation class is
unique (`MMP.IsLocalOrientationClass.eq`).

## Main results

* `MMP.Modules.forget_eq_forget_pullback_thomClass_of_isRegularImbeddingOrientationClass`:
  `u_{t,T} = σ^*(u_ℰ)` for a section `σ` of a rank-one bundle with `Z(σ) = t`.
* `MMP.Modules.isLocalOrientationClass_forget_pullback_thomClass_globalSectionMap`,
  `MMP.Modules.forget_eq_forget_pullback_thomClass_globalSectionMap`: the same for the section
  `σ_s` of a global section `s` of an invertible module.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

namespace MMP.Modules

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]
  (t : UnderlyingSpace ℂ T)

/-- **`u_{t,T} = σ^*(u_ℰ)`** (Fulton, proof of Lemma 19.1.3). For a smooth complex curve `T`,
`t ∈ T(ℂ)` and a section `σ` of a rank-one bundle `𝐕(ℰ) ⟶ T` whose zero scheme is the point `t`,
the orientation class `u` of the regular closed immersion `t : Spec ℂ → T` (Fulton §19.2) is
`σ^*(u_ℰ)`, both viewed in `H²(T, T - t)`. -/
theorem forget_eq_forget_pullback_thomClass_of_isRegularImbeddingOrientationClass (R : Type)
    [CommRing R] (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) {E : T.Modules}
    [E.IsQuasicoherent] [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E 1]
    {σ : T ⟶ totalSpace E} [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 T)
    (hz : zeroLocus E σ = t.toHom.ker)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R t.toHom 1 u) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
        (preimage_ofHom_range_zeroSection_subset_singleton σ t hz) (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection E))) (2 * 1 : ℕ)).hom
            (thomClass R E 1)) :=
  IsLocalOrientationClass.eq (by norm_num)
    (isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R hT t hu)
    (isLocalOrientationClass_forget_pullback_thomClass t R hT hσ hz)

section GlobalSection

variable {N : T.Modules} [(Scheme.Modules.dual N).IsQuasicoherent]
  [Stacks.Ample.IsInvertibleModule T N] (s : Γ(N, ⊤))

/-- **The pull-back of the Thom class by the section of a global section cutting out a point is
the local orientation class.** For a global section `s` of an invertible module `𝒩` on a smooth
complex curve `T` whose section `σ_s : T ⟶ 𝐕(𝒩^∨)` has zero scheme the point `t`,
`σ_s^*(u_{𝒩^∨})`, viewed in `H²(T, T - t)`, is the local orientation class of `T(ℂ)` at `t`. -/
theorem isLocalOrientationClass_forget_pullback_thomClass_globalSectionMap (R : Type)
    [CommRing R] (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ)))
    (hs : zeroLocus (Scheme.Modules.dual N) (globalSectionMap N s) = t.toHom.ker) :
    IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ T)) R curveOrientationBasis t
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
        (preimage_ofHom_range_zeroSection_subset_singleton (globalSectionMap N s) t hs)
        (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (globalSectionMap N s)))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection (Scheme.Modules.dual N))))
          (2 * 1 : ℕ)).hom (thomClass R (Scheme.Modules.dual N) 1))) :=
  isLocalOrientationClass_forget_pullback_thomClass t R hT (globalSectionMap_proj N s) hs

/-- **`u_{t,T} = σ_s^*(u_{𝒩^∨})`** (Fulton, proof of Lemma 19.1.3). For a global section `s` of an
invertible module `𝒩` on a smooth complex curve `T` whose section `σ_s : T ⟶ 𝐕(𝒩^∨)` has zero
scheme the point `t`, the orientation class `u` of the regular closed immersion `t : Spec ℂ → T`
is `σ_s^*(u_{𝒩^∨})`, both viewed in `H²(T, T - t)`. -/
theorem forget_eq_forget_pullback_thomClass_globalSectionMap (R : Type) [CommRing R]
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ)))
    (hs : zeroLocus (Scheme.Modules.dual N) (globalSectionMap N s) = t.toHom.ker)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R t.toHom 1 u) :
    (cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom u =
      (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
        (preimage_ofHom_range_zeroSection_subset_singleton (globalSectionMap N s) t hs)
        (2 * 1 : ℕ)).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (globalSectionMap N s)))
          (range (UnderlyingSpace.map (K := ℂ) (zeroSection (Scheme.Modules.dual N))))
          (2 * 1 : ℕ)).hom (thomClass R (Scheme.Modules.dual N) 1)) :=
  forget_eq_forget_pullback_thomClass_of_isRegularImbeddingOrientationClass t R hT
    (globalSectionMap_proj N s) hs hu

end GlobalSection

end MMP.Modules
