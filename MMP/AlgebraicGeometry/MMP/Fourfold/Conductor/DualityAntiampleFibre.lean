module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup
public import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.AlgebraicGeometry.Dimension.SmoothOfRelativeDimension
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularOpensSmooth
public import MMP.AlgebraicGeometry.CycleMap.Stacks.FundamentalClassGenericPoint
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicTopology.OrientationClass.CapCodimZero
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Product
public import MMP.Topology.Manifold.NeighbourhoodRetract.Basic
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
import MMP.AlgebraicGeometry.ProjectiveSpace.ZeroLocusFactorization
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisorSupport

/-!
# Conductor calculations: supported duality and an antiample snc fibre

Two inputs to the conductor calculations on a dominating smooth model.

**Supported duality.** Let `M` be a smooth quasi-projective complex variety of dimension `d` with
fundamental class `μ_M ∈ H_{2d} M(ℂ)`, and `D ⊆ M` Zariski closed and proper over `ℂ`. Capping
with `μ_M` gives an isomorphism `H^{2d-k}(M(ℂ), M(ℂ) - D(ℂ); ℚ) ≅ H_k(D(ℂ); ℚ)` for every `k`,
and likewise on every open neighbourhood `U` of `D(ℂ)` with the restricted class `μ_M|_U`. Since
`M` is non-singular, `M(ℂ)` is a real `2d`-manifold whose fundamental class is `μ_M`; Alexander
duality on it and on `U`, transported along the homeomorphisms with the regular parts, gives both.

**An antiample snc fibre.** Let `f₀ : W₀ ⟶ S` be a projective resolution of a normal
quasi-projective complex threefold, and `x ∈ S` a singular point with an open neighbourhood `U`
such that `Sing(S) ∩ U = {x}` and `f₀` is an isomorphism over `U ∖ {x}`. Then `f₀` is dominated by
a projective resolution `f = r ≫ f₀ : W ⟶ S` with `W` quasi-projective, again an isomorphism over
`U ∖ {x}`, whose reduced fibre over `x` is an snc divisor `E = ∑ Eᵢ` of smooth projective
surfaces, together with `D = ∑ mᵢ Eᵢ`, `mᵢ > 0`, such that `-D` is Cartier and ample over `U`.
One blows up `S` along `C·𝔪_x`, for `C` the colon ideal of the coordinate ratios of
`W₀ ⊆ ℙⁿ_S`, which dominates `W₀`; principalizes the pulled-back ideal on `W₀`; and corrects
Kollár's `π`-antiample divisor (Lemma 2.9) by a multiple of the divisor of the ideal, using
[Stacks, Tag 0C4K] for the composite.

## Main results

* `MMP.Analytic.supportedDuality_of_isQuasiProjectiveVariety`: the duality map `c ↦ c ∩ μ_M` is
  bijective, natural in the support, carries the orientation class of a closed complex submanifold
  `D(ℂ) ∩ V` of an open `V` (the normal disks) to its fundamental class, and on every open
  neighbourhood `U` of `D(ℂ)` the duality with `μ_M|_U` is bijective and commutes with restriction.
* `MMP.Analytic.bijective_dualityMap_of_isQuasiProjectiveVariety`: the bijectivity, on `M(ℂ)` and
  on every open neighbourhood of `D(ℂ)`.
* `MMP.Threefold.exists_isResolution_comp_isSNC_isAmpleOver_neg`: the dominating model with an
  antiample snc fibre.
* `MMP.Mori.IsRelativelyAmple.to_stacks`, `MMP.Mori.IsRelativelyAmple.of_iso`,
  `MMP.Mori.modulePullbackIsoRestrict`: `f`-ampleness of an invertible sheaf is Stacks'
  relative ampleness for quasi-compact `f`, and is invariant under isomorphism.
* `MMP.Mori.Divisor.IsRelativelyAmple.isAmpleOver`,
  `MMP.Mori.Divisor.IsRelativelyAmple.isAmpleOver_of_coeff_eq`: an `f`-ample Cartier divisor is
  ample over every open `U` of the base, and so is any Cartier divisor agreeing with it over `U`.

## Implementation notes

* `M(ℂ)` is `MMP.UnderlyingSpace ℂ M` and `D(ℂ)` is
  `MMP.UnderlyingSpace.pointsOver D`; supported cohomology is
  `MMP.cohomologyWithSupports`, and the map is
  `MMP.borelMooreHomology.dualityMap`, the cap product with the cycle class
  `MMP.Chow.pointCycleClass` of the generic point of `M` (the fundamental class of `M`).
  Homology is Borel–Moore homology, ordinary
  homology for the compact `D(ℂ)`. The degree is written `H^{2d-k}_D → H_k D`. The source
  compactifies `M` and excises the boundary; Alexander duality needs no compactness, so it is
  applied on `M(ℂ)` and on `U` directly.
* The resolutions `f₀` and `f` are `MMP.Intersection.IsResolution`; "`f₀` is an isomorphism over
  `U ∖ {x}`" is `U ∖ {x} ⊆ MMP.Mori.biregularLocus f₀`, and `Sing(S)` is `MMP.Mori.singularLocus`.
  "`-D` is ample over `U`" is `MMP.Mori.Divisor.IsAmpleOver`.
* The auxiliary lemmas live in the namespaces `Proof_<tag>` of the two cards.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1
* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], 2.9, 3.16, 3.72
* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
-/

@[expose] public section

universe u

namespace Proof_lem_mmp_conductor_quasiprojective_supported_duality

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP MMP.UnderlyingSpace MMP.FundamentalClass
open MMP.borelMooreHomology

/-- **Pullback along an inverse homeomorphism is onto.** For `φ : M ≃ₜ M'` and `A ⊆ M`, the
pullback `(φ⁻¹)^* : H^j(M, M - A) → H^j(M', M' - φ(A))` is surjective: `φ^*` followed by `(φ⁻¹)^*`
is the identity of `H^j(M', M' - φ(A))`. -/
private lemma surjective_pullback_homeomorph_symm {R : Type} [CommRing R] (N : ModuleCat.{0} R)
    {M M' : TopCat.{0}} (φ : M ≃ₜ M') (A : Set M) (j : ℤ) :
    Function.Surjective
      (cohomologyWithSupports.pullback R N (TopCat.ofHom (φ.symm : C(M', M))) A j).hom := by
  rw [show A = φ ⁻¹' (φ.symm ⁻¹' A) by ext; simp]
  have key : ∀ h : M' ⟶ M', h = 𝟙 M' →
      Function.Surjective (cohomologyWithSupports.pullback R N h (φ.symm ⁻¹' A) j).hom := by
    rintro _ rfl
    rw [cohomologyWithSupports.pullback_id]
    exact Function.surjective_id
  have h := key _ (by ext; simp :
    TopCat.ofHom (φ.symm : C(M', M)) ≫ TopCat.ofHom (φ : C(M, M')) = 𝟙 M')
  rw [cohomologyWithSupports.pullback_comp, ModuleCat.hom_comp, LinearMap.coe_comp] at h
  exact h.of_comp

/-- **Duality maps transported along a homeomorphism.** For `φ : M ≃ₜ M'` and closed `A ⊆ M`, if
the duality map `c ↦ c ∩ μ` on `H^{n-k}(M, M - A)` is bijective, then so is the duality map of
`φ(A)` with `φ_* μ`. -/
private lemma bijective_dualityMap_pushforward_homeomorph {R : Type} [CommRing R]
    {M M' : TopCat.{0}} (φ : M ≃ₜ M') {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (φ.symm ⁻¹' A)) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ)
    (h : Function.Bijective (dualityMap R hA hAd μ k)) :
    Function.Bijective (dualityMap R (hA.preimage φ.symm.continuous) hA'd
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n).hom μ)
      k) := by
  have hQ := bijective_pushforward_homeomorph R (Y := TopCat.of (φ.symm ⁻¹' A)) (Y' := TopCat.of A)
    (preimageHomeomorph φ.symm A) k
  rw [show ⇑(dualityMap R hA hAd μ k) = _ ∘ _ ∘ _ from
    funext fun c ↦ (pushforward_dualityMap_pullback_symm R φ hA hAd hA'd μ k c).symm] at h
  replace h := (hQ.of_comp_iff' _).1 h
  exact (Function.Bijective.of_comp_iff _
    ⟨.of_comp h.1, surjective_pullback_homeomorph_symm _ φ A _⟩).1 h

end Proof_lem_mmp_conductor_quasiprojective_supported_duality

namespace MMP.Analytic

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
  MMP.UnderlyingSpace MMP.FundamentalClass
  MMP.borelMooreHomology Proof_lem_mmp_conductor_quasiprojective_supported_duality

/-- **Supported duality near a proper algebraic subset of a smooth quasi-projective complex
variety.** Let `M` be a non-singular quasi-projective complex variety of dimension `d` with
fundamental class `μ ∈ H_{2d} M(ℂ)` (the complex orientation), and `D ⊆ M` Zariski closed and
proper over `ℂ`. For every `k`, the cap product with `μ`,
`H^{2d-k}(M(ℂ), M(ℂ) - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is bijective; and for every open neighbourhood
`U` of `D(ℂ)` in `M(ℂ)` in which `D(ℂ)` has arbitrarily small proper neighbourhood deformations,
the cap product with `μ|_U`,
`H^{2d-k}(U, U - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is bijective. -/
public theorem bijective_dualityMap_of_isQuasiProjectiveVariety
    {M : Scheme.{0}} [M.Over (Spec (.of ℂ))] [IsComplexScheme M] [IsIntegral M]
    (hM : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ))) {d : ℕ}
    [SmoothOfRelativeDimension d (M ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ M)) (2 * d : ℕ)}
    (hμ : Chow.pointCycleClass ℚ (genericPoint M)
      (Chow.relativeDimension_genericPoint_eq ℂ (M ↘ Spec (.of ℂ))
        (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d).symm) = μ)
    (D : Closeds M)
    (hD : IsProper ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫ (M ↘ Spec (.of ℂ))))
    (k : ℤ) :
    Function.Bijective
        (borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ M))
          (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver M D)
          μ k) ∧
      ∀ (U : Opens (TopCat.of (UnderlyingSpace ℂ M)))
        (_hDU : pointsOver (K := ℂ) (D : Set M) ⊆ U)
        (hUd : HasProperNeighbourhoodDeformations
          ((borelMooreHomology.inclHom U).hom ⁻¹' pointsOver (K := ℂ) (D : Set M))),
        Function.Bijective
          (borelMooreHomology.dualityMap ℚ (M := TopCat.of U)
            ((isClosed_pointsOver D.isClosed).preimage
              (borelMooreHomology.inclHom U).hom.continuous) hUd
            ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U (2 * d : ℕ)).hom μ) k) := by
  letI := regularChartedSpace (𝕜 := ℂ)
    (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d)
  have hμ' : IsFundamentalClass ℚ (euclideanComplexOrientationBasis d)
      ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
        (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M))) (2 * d : ℕ)).hom μ) :=
    hμ ▸ Chow.isFundamentalClass_restrict_pointCycleClass_genericPoint ℚ
      (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d) _
  have hW := MMP.regularOpens_eq_top_of_smoothOfRelativeDimension (X := M) d
  let W : Opens (TopCat.of (UnderlyingSpace ℂ M)) := regularOpens ℂ M
  let M' : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ M)
  let μr := (restrict ℚ (ModuleCat.of ℚ ℚ) W (2 * d : ℕ)).hom μ
  refine ⟨?_, fun U _ hUd ↦ ?_⟩
  · -- `φ : M_reg(ℂ) ≃ₜ M(ℂ)`, the inclusion of the regular part, which is everything.
    let φ : (W : Opens (UnderlyingSpace ℂ M)) ≃ₜ UnderlyingSpace ℂ M :=
      (Homeomorph.setCongr (congrArg SetLike.coe hW)).trans (Homeomorph.Set.univ _)
    let X : Set M' := pointsOver D
    have hXd : HasProperNeighbourhoodDeformations X :=
      hasProperNeighbourhoodDeformations_pointsOver M D
    have hA : IsClosed (φ ⁻¹' X) := (isClosed_pointsOver D.isClosed).preimage φ.continuous
    have hpush : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(TopCat.of W, M')))
        φ.isProperMap
        (2 * d : ℕ)).hom μr = μ :=
      pushforward_inclHom_restrict_of_eq_top ℚ hW _ _ μ
    rw [← hpush]
    exact bijective_dualityMap_pushforward_homeomorph (M := TopCat.of W) (M' := M') φ hA _ hXd μr
      k (bijective_dualityMap_of_isFundamentalClass (M := (W : Opens (UnderlyingSpace ℂ M)))
        (euclideanComplexOrientationBasis d) μr hμ' hA (hXd.preimage_homeomorph φ) k)
  · have hUW : U ≤ W := le_top.trans_eq hW.symm
    -- `ψ : V ≃ₜ U`, for `V ⊆ M_reg(ℂ)` the open subset corresponding to `U`.
    let V : Opens (TopCat.of W) := subOpens W U
    let ψ : V ≃ₜ U := (subOpensHomeo W hUW).symm
    let X : Set (TopCat.of U) := (inclHom U).hom ⁻¹' pointsOver (K := ℂ) (D : Set M)
    have hA : IsClosed (ψ ⁻¹' X) :=
      ((isClosed_pointsOver D.isClosed).preimage (inclHom U).hom.continuous).preimage
        ψ.continuous
    let ν := (restrict ℚ (ModuleCat.of ℚ ℚ) V (2 * d : ℕ)).hom μr
    have hν : IsFundamentalClass ℚ (euclideanComplexOrientationBasis d) ν := hμ'.restrict V
    have hpush : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (ψ : C(TopCat.of V, TopCat.of U)))
        ψ.isProperMap (2 * d : ℕ)).hom ν = (restrict ℚ (ModuleCat.of ℚ ℚ) U (2 * d : ℕ)).hom μ := by
      have h1 := restrict_restrict_apply ℚ (ModuleCat.of ℚ ℚ) W hUW (2 * d : ℕ) μ
      change (pushforward ℚ (ModuleCat.of ℚ ℚ) (subOpensInv W hUW) _ _).hom
        ((restrict ℚ (ModuleCat.of ℚ ℚ) (subOpens W U) (2 * d : ℕ)).hom
          ((restrict ℚ (ModuleCat.of ℚ ℚ) W (2 * d : ℕ)).hom μ)) = _
      erw [h1]
      refine (pushforward_comp_apply ℚ (subOpensMap W hUW) (subOpensInv W hUW) _ _
        isProperMap_id _ _).trans ?_
      change (pushforward ℚ (ModuleCat.of ℚ ℚ) (𝟙 _) isProperMap_id _).hom _ = _
      rw [pushforward_id]
      rfl
    rw [← hpush]
    exact bijective_dualityMap_pushforward_homeomorph (M := TopCat.of V) (M' := TopCat.of U) ψ hA
      _ hUd ν k (bijective_dualityMap_of_isFundamentalClass (M := V)
        (euclideanComplexOrientationBasis d) ν hν hA (hUd.preimage_homeomorph ψ) k)

end MMP.Analytic

namespace MMP.Analytic

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set Filter MMP
  MMP.UnderlyingSpace MMP.FundamentalClass
  MMP.borelMooreHomology MMP.BorelMooreCross
  MMP.ThomClass Proof_lem_mmp_conductor_quasiprojective_supported_duality
open scoped Manifold ContDiff

/-- **Proper neighbourhood deformations restrict to an open neighbourhood.** If `X` has
arbitrarily small proper neighbourhood deformations in `Y` and `U ⊇ X` is open, then `X`, read
inside `U`, has arbitrarily small proper neighbourhood deformations in `U`. -/
public theorem hasProperNeighbourhoodDeformations_subtypeVal_preimage_of_subset {Y : Type*}
    [TopologicalSpace Y] {U : Set Y} (hU : IsOpen U) {X : Set Y} (hXU : X ⊆ U)
    (hX : HasProperNeighbourhoodDeformations X) :
    HasProperNeighbourhoodDeformations ((Subtype.val : U → Y) ⁻¹' X) := by
  intro Mu hMu
  have hM' : (Subtype.val '' Mu : Set Y) ∈ 𝓝ˢ X := by
    rw [mem_nhdsSet_iff_forall] at hMu ⊢
    intro x hx
    exact hU.isOpenEmbedding_subtypeVal.image_mem_nhds.2 (hMu ⟨x, hXU hx⟩ hx)
  obtain ⟨N, hN, hXN, hNM, r, hr, hrX, G, hG, hG0, hG1, hGX, hGM⟩ := hX _ hM'
  have hNU : N ⊆ U := fun y hy ↦ by
    obtain ⟨z, -, rfl⟩ := hNM hy
    exact z.2
  let eN : ((Subtype.val : U → Y) ⁻¹' N) ≃ₜ N :=
    { toFun := fun y ↦ ⟨y.1.1, y.2⟩
      invFun := fun z ↦ ⟨⟨z.1, hNU z.2⟩, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let eX : ((Subtype.val : U → Y) ⁻¹' X) ≃ₜ X :=
    { toFun := fun y ↦ ⟨y.1.1, y.2⟩
      invFun := fun z ↦ ⟨⟨z.1, hXU z.2⟩, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have hGU : ∀ q, G q ∈ U := fun q ↦ Subtype.coe_image_subset U Mu (hGM q)
  let ru : C((Subtype.val : U → Y) ⁻¹' N, (Subtype.val : U → Y) ⁻¹' X) :=
    ⟨fun y ↦ eX.symm (r (eN y)), eX.symm.continuous.comp (r.continuous.comp eN.continuous)⟩
  let eNI := eN.prodCongr (Homeomorph.refl unitInterval)
  let Gu : C((Subtype.val : U → Y) ⁻¹' N × unitInterval, U) :=
    ⟨fun q ↦ ⟨G (eNI q), hGU _⟩, (G.continuous.comp eNI.continuous).subtype_mk _⟩
  refine ⟨_, hN.preimage continuous_subtype_val,
    fun y hy ↦ preimage_interior_subset_interior_preimage continuous_subtype_val (hXN hy),
    fun y hy ↦ ?_, ru, ?_, fun y hy ↦ Subtype.ext (hrX (eN y) hy), Gu, ?_,
    fun y ↦ Subtype.ext (hG0 (eN y)), fun y ↦ Subtype.ext (hG1 (eN y)),
    fun y t hy ↦ Subtype.ext (hGX (eN y) t hy), fun q ↦ ?_⟩
  · obtain ⟨z, hz, hzy⟩ := hNM hy
    rwa [← Subtype.ext hzy]
  · exact eX.symm.isProperMap.comp (hr.comp eN.isProperMap)
  · exact isProperMap_of_comp_of_inj Gu.continuous continuous_subtype_val
      (hG.comp eNI.isProperMap) Subtype.val_injective
  · obtain ⟨z, hz, hzq⟩ := hGM (eNI q)
    have hz' : z = Gu q := Subtype.ext hzq
    rwa [← hz']

/-- `hasProperNeighbourhoodDeformations_subtypeVal_preimage_of_subset` for an open `U` of a space
`Y`, with `X` read in `U` through the inclusion `inclHom U`. -/
public theorem hasProperNeighbourhoodDeformations_inclHom_preimage_of_subset {Y : TopCat.{0}}
    (U : Opens Y) {X : Set Y} (hXU : X ⊆ U) (hX : HasProperNeighbourhoodDeformations X) :
    HasProperNeighbourhoodDeformations ((inclHom U).hom ⁻¹' X) :=
  hasProperNeighbourhoodDeformations_subtypeVal_preimage_of_subset U.isOpen hXU hX

/-- Bases of open contractible neighbourhoods pull back along open embeddings. -/
private theorem hasOpenContractibleBasis_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : HasOpenContractibleBasis X) {e : Y → X} (he : IsOpenEmbedding e) :
    HasOpenContractibleBasis Y := by
  intro y
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨V, ⟨hV, hyV, _⟩, hVt⟩ ↦ mem_of_superset (hV.mem_nhds hyV)
    hVt⟩⟩
  obtain ⟨V, ⟨hV, hyV, hc⟩, hVt⟩ := (h (e y)).mem_iff.1 (he.image_mem_nhds.2 ht)
  have hVr : V ⊆ range e := hVt.trans (image_subset_range _ _)
  refine ⟨e ⁻¹' V, ⟨hV.preimage he.continuous, hyV, ?_⟩, fun z hz ↦ ?_⟩
  · exact ((he.isEmbedding.homeomorphImage (e ⁻¹' V)).trans
      (Homeomorph.setCongr (image_preimage_eq_of_subset hVr))).contractibleSpace
  · obtain ⟨w, hw, hwz⟩ := hVt hz
    rwa [← he.injective hwz]

/-- A closed subset with bases of open contractible neighbourhoods of a Hausdorff,
second-countable manifold modelled on `ℂⁿ` has arbitrarily small proper neighbourhood
deformations. -/
private theorem hasProperNeighbourhoodDeformations_of_complexChartedSpace {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] (n : ℕ)
    (c : ChartedSpace (EuclideanSpace ℂ (Fin n)) Y) {X : Set Y} (hX : IsClosed X)
    (hXc : HasOpenContractibleBasis X) : HasProperNeighbourhoodDeformations X := by
  let e : EuclideanSpace ℂ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin (2 * n)) :=
    ((euclideanComplexOrientationBasis n).equivFun.trans
      (WithLp.linearEquiv 2 ℝ (Fin (2 * n) → ℝ)).symm).toContinuousLinearEquiv.toHomeomorph
  let c₀ : ChartedSpace (EuclideanSpace ℝ (Fin (2 * n))) (EuclideanSpace ℂ (Fin n)) :=
    e.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  exact @hasProperNeighbourhoodDeformations_of_chartedSpace (2 * n) Y _ _ _
    (@ChartedSpace.comp _ _ _ _ Y _ c₀ c) X hX hXc

/-- The points of an open `V ⊆ W` of an open `W ⊆ M(ℂ)` lying over a subset `D` of `M`. -/
public abbrev pointsOverIn {M : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    {W : Opens (TopCat.of (UnderlyingSpace ℂ M))} (V : Opens (TopCat.of W)) (D : Set M) :
    Set (TopCat.of V) :=
  (fun x : V ↦ ((x : W) : UnderlyingSpace ℂ M)) ⁻¹' pointsOver (K := ℂ) D

/-- `D(ℂ) ∩ V` is closed in `V` for `D` closed. -/
public theorem isClosed_pointsOverIn {M : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    {W : Opens (TopCat.of (UnderlyingSpace ℂ M))} (V : Opens (TopCat.of W)) {D : Set M}
    (hD : IsClosed D) : IsClosed (pointsOverIn V D) :=
  (isClosed_pointsOver hD).preimage (continuous_subtype_val.comp continuous_subtype_val)

/-- `D(ℂ) ∩ V`, for `V` open in an open `W ⊆ M(ℂ)`, has bases of open contractible
neighbourhoods. -/
private theorem hasOpenContractibleBasis_pointsOverIn {M : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] {W : Opens (TopCat.of (UnderlyingSpace ℂ M))} (V : Opens (TopCat.of W))
    (D : Closeds M) : HasOpenContractibleBasis (pointsOverIn V (D : Set M)) := by
  let g : pointsOverIn V (D : Set M) → pointsOver (K := ℂ) (D : Set M) := fun z ↦ ⟨z.1.1.1, z.2⟩
  have hg : Continuous g :=
    ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  have hemb : IsEmbedding g := by
    refine (IsEmbedding.subtypeVal.of_comp_iff).1 ?_
    exact (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal
  have hS : IsOpen (Subtype.val '' (V : Set (TopCat.of W)) : Set (UnderlyingSpace ℂ M)) :=
    W.isOpen.isOpenMap_subtype_val _ V.isOpen
  have hrange : range g = Subtype.val ⁻¹' (Subtype.val '' (V : Set (TopCat.of W))) := by
    ext p
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1.1, z.1.2, rfl⟩
    · rintro ⟨w, hw, hwp⟩
      refine ⟨⟨⟨w, hw⟩, ?_⟩, Subtype.ext hwp⟩
      change (w : UnderlyingSpace ℂ M) ∈ pointsOver (K := ℂ) (D : Set M)
      rw [hwp]
      exact p.2
  have hge : IsOpenEmbedding g := ⟨hemb, hrange ▸ hS.preimage continuous_subtype_val⟩
  exact hasOpenContractibleBasis_of_isOpenEmbedding (hasOpenContractibleBasis_pointsOver M D) hge

/-- For an open `V` of the regular part `M_reg(ℂ)` of a complex variety, the points of `V` over a
closed subset `D` have arbitrarily small proper neighbourhood deformations in `V`. -/
public theorem hasProperNeighbourhoodDeformations_pointsOverIn {M : Scheme.{0}}
    [M.Over (Spec (.of ℂ))] [IsComplexScheme M] [IsIntegral M] {n : ℕ}
    (hn : (n : WithBot ℕ∞) = topologicalKrullDim M)
    (V : Opens (TopCat.of (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M)))))
    (D : Closeds M) : HasProperNeighbourhoodDeformations (pointsOverIn V (D : Set M)) := by
  let := regularChartedSpace (𝕜 := ℂ) hn
  exact hasProperNeighbourhoodDeformations_of_complexChartedSpace n inferInstance
    (isClosed_pointsOverIn V D.isClosed) (hasOpenContractibleBasis_pointsOverIn V D)

/-- A fundamental class for the orientation of a basis `b` is one for every basis `b'` of the
same orientation. -/
private theorem isFundamentalClass_of_det_pos {R : Type} [CommRing R] {H : Type*} [AddCommGroup H]
    [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace H M] {n : ℕ} {b b' : Module.Basis (Fin n) ℝ H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n} (hμ : IsFundamentalClass R b μ)
    (h : 0 < b'.det b) : IsFundamentalClass R b' μ := by
  have h' : 0 < b.det b' := by
    have h1 := b.det_mul_det b' b
    rw [Module.Basis.det_self] at h1
    by_contra hneg
    nlinarith [not_lt.1 hneg]
  intro e he x v hv hvt
  refine hμ e he x v ⟨hv.1, ?_⟩ hvt
  have hm := congrArg Matrix.det (b.toMatrix_mul_toMatrix b' fun k ↦ v k.succ - e x - (v 0 - e x))
  rw [Matrix.det_mul, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    ← Module.Basis.det_apply] at hm
  rw [← hm]
  exact mul_pos h' hv.2

/-- Reindexing the coordinates of `ℂʳ` along `r = d` carries `complexOrientationBasis r` to
`complexOrientationBasis d`. -/
private lemma complexOrientationBasis_comp_finCongr (r d : ℕ) (hr : r = d) (h : 2 * r = 2 * d)
    (i : Fin (2 * r)) :
    complexOrientationBasis r i ∘ finCongr hr.symm = complexOrientationBasis d (finCongr h i) := by
  subst hr
  rfl

/-- `euclideanComplexOrientationBasis d` and `complexOrientationBasisOf ℂᵈ` define the same
orientation. -/
private theorem det_complexOrientationBasisOf_euclideanComplexOrientationBasis_pos (d : ℕ)
    (h : 2 * d = 2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d))) :
    0 < (complexOrientationBasisOf (EuclideanSpace ℂ (Fin d))).det
      ((euclideanComplexOrientationBasis d).reindex (finCongr h)) := by
  have hr : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = d := finrank_euclideanSpace_fin
  let L : (Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin d))) → ℂ) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (finCongr hr.symm)).trans
      (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm
  have hpos := complexOrientationBasisOf_det_pos (E := EuclideanSpace ℂ (Fin d))
    (L := L.toLinearMap) L.injective
  convert hpos using 2
  funext i
  rw [Module.Basis.reindex_apply, euclideanComplexOrientationBasis_apply, finCongr_symm]
  change _ = WithLp.toLp 2 ((complexOrientationBasis _ i) ∘ (finCongr hr.symm))
  rw [complexOrientationBasis_comp_finCongr _ d hr h.symm]

/-- **Supported duality near a proper algebraic subset of a smooth quasi-projective complex
variety.** Let `M` be a non-singular quasi-projective complex variety of dimension `d` with
fundamental class `μ ∈ H_{2d} M(ℂ)` (the complex orientation), and `D ⊆ M` Zariski closed and
proper over `ℂ`, with trace `D(ℂ) ⊆ M(ℂ)`. Then:
1. for every `k`, the cap product with `μ`, `H^{2d-k}(M(ℂ), M(ℂ) - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is
  bijective;
2. it is natural in the support: for Zariski-closed `D ⊆ D'` it commutes with the forgetful map
  `H^*_D → H^*_{D'}` and the push-forward `H_* D(ℂ) → H_* D'(ℂ)`;
3. it has the normal-disk orientation normalization: on every open `V ⊆ M(ℂ) = M_reg(ℂ)` where
  `D(ℂ) ∩ V` is a closed complex submanifold `Z` with a tubular (normal disk) neighbourhood, the
  cap product with `μ|_V` carries the orientation class `u_{Z,V}` to the fundamental class of `Z`;
4. it is compatible with restriction to every open neighbourhood `U` of `D(ℂ)`: the cap product
  with `μ|_U`, `H^{2d-k}(U, U - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is bijective, and it commutes with the
  restrictions `c ↦ c|_U` and `H_* D(ℂ) → H_*(D(ℂ) ∩ U) = H_* D(ℂ)`. -/
@[mmp "lem_mmp_conductor_quasiprojective_supported_duality"]
public theorem supportedDuality_of_isQuasiProjectiveVariety
    {M : Scheme.{0}} [M.Over (Spec (.of ℂ))] [IsComplexScheme M] [IsIntegral M]
    (hM : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ))) {d : ℕ}
    [SmoothOfRelativeDimension d (M ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ M)) (2 * d : ℕ)}
    (hμ : Chow.pointCycleClass ℚ (genericPoint M)
      (Chow.relativeDimension_genericPoint_eq ℂ (M ↘ Spec (.of ℂ))
        (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d).symm) = μ)
    (D : Closeds M)
    (hD : IsProper ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫ (M ↘ Spec (.of ℂ)))) :
    (∀ k : ℤ, Function.Bijective (dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ M))
        (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver M D)
        μ k)) ∧
    (∀ (D' : Closeds M) (hDD' : (D : Set M) ⊆ D') (k : ℤ)
        (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ M))
          (pointsOver (K := ℂ) (D : Set M)) ((2 * d : ℕ) - k)),
        (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (pointsOver_mono hDD'))
            (isProperMap_subsetInclusionOfSubset (isClosed_pointsOver D.isClosed)
              (pointsOver_mono hDD')) k).hom
          (dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ M)) (isClosed_pointsOver D.isClosed)
            (hasProperNeighbourhoodDeformations_pointsOver M D) μ k c) =
        dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ M)) (isClosed_pointsOver D'.isClosed)
            (hasProperNeighbourhoodDeformations_pointsOver M D') μ k
          ((cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) _ (pointsOver_mono hDD') _).hom
            c)) ∧
    (letI := regularChartedSpace (𝕜 := ℂ)
        (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d)
      ∀ (V : Opens (TopCat.of (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M)))))
        (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
        [ChartedSpace E' (pointsOverIn V (D : Set M))],
        IsComplexSubmanifold (EuclideanSpace ℂ (Fin d)) E' (pointsOverIn V (D : Set M)) →
        ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
          (N : pointsOverIn V (D : Set M) → Type) [∀ x, AddCommGroup (N x)]
          [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
          [TopologicalSpace (Bundle.TotalSpace F N)] [FiberBundle F N] [VectorBundle ℂ F N]
          (φ : TubularNeighbourhood F N)
          (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of V)
            (pointsOverIn V (D : Set M)) (2 * Module.finrank ℂ F : ℕ)),
          IsOrientationClass (EuclideanSpace ℂ (Fin d)) ℚ φ u →
          ∀ (hdeg : ((2 * d : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) =
            (2 * Module.finrank ℂ E' : ℕ)),
          IsFundamentalClass (M := pointsOverIn V (D : Set M)) ℚ (complexOrientationBasisOf E')
            (congrDegree ℚ (TopCat.of (pointsOverIn V (D : Set M))) hdeg
              (capProductSupport ℚ (TopCat.of V) (isClosed_pointsOverIn V D.isClosed)
                (hasProperNeighbourhoodDeformations_pointsOverIn
                  (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d)
                  V D) _ _ u
                ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
                    (Y := TopCat.of (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M))))
                    V (2 * d : ℕ)).hom
                  ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
                    (Y := TopCat.of (UnderlyingSpace ℂ M))
                    (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M)))
                    (2 * d : ℕ)).hom μ))))) ∧
    (∀ (U : Opens (TopCat.of (UnderlyingSpace ℂ M)))
        (hDU : pointsOver (K := ℂ) (D : Set M) ⊆ U) (k : ℤ),
      Function.Bijective (dualityMap ℚ (M := TopCat.of U)
          ((isClosed_pointsOver D.isClosed).preimage (inclHom U).hom.continuous)
          (hasProperNeighbourhoodDeformations_inclHom_preimage_of_subset U hDU
            (hasProperNeighbourhoodDeformations_pointsOver M D))
          ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U (2 * d : ℕ)).hom μ) k) ∧
      ∀ c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ M))
          (pointsOver (K := ℂ) (D : Set M)) ((2 * d : ℕ) - k),
        dualityMap ℚ (M := TopCat.of U)
            ((isClosed_pointsOver D.isClosed).preimage (inclHom U).hom.continuous)
            (hasProperNeighbourhoodDeformations_inclHom_preimage_of_subset U hDU
              (hasProperNeighbourhoodDeformations_pointsOver M D))
            ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U (2 * d : ℕ)).hom μ) k
            ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (inclHom U)
              (pointsOver (K := ℂ) (D : Set M)) ((2 * d : ℕ) - k)).hom c) =
          (pushforward ℚ (ModuleCat.of ℚ ℚ) (opensInterMap U (pointsOver (K := ℂ) (D : Set M)))
              (isProperMap_opensInterMap U _) k).hom
            ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
              (opensInter U (pointsOver (K := ℂ) (D : Set M))) k).hom
              (dualityMap ℚ (isClosed_pointsOver D.isClosed)
                (hasProperNeighbourhoodDeformations_pointsOver M D) μ k c))) := by
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hM.toIsSeparated
  have hn := natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M d
  refine ⟨fun k ↦ (bijective_dualityMap_of_isQuasiProjectiveVariety hM hμ D hD k).1,
    fun D' hDD' k c ↦ ?_, ?_,
    fun U hDU k ↦ ⟨(bijective_dualityMap_of_isQuasiProjectiveVariety hM hμ D hD k).2 U hDU _,
      fun c ↦ ?_⟩⟩
  · rw [dualityMap_apply, dualityMap_apply, borelMooreHomology.pushforward_congrDegree,
      pushforward_subsetInclusionOfSubset_capProductSupport]
  · let := regularChartedSpace (𝕜 := ℂ) hn
    have hμ' : IsFundamentalClass ℚ (euclideanComplexOrientationBasis d)
        ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
          (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M))) (2 * d : ℕ)).hom μ) :=
      hμ ▸ Chow.isFundamentalClass_restrict_pointCycleClass_genericPoint ℚ hn _
    intro V E' _ _ _ _ hZ F _ _ _ N _ _ _ _ _ _ φ u hu hdeg
    have := isManifold_regularOpens (𝕜 := ℂ) hn
    have : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 1 (regularOpens ℂ M) :=
      IsManifold.of_le (n := ω) le_top
    set ν := (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
        (Y := TopCat.of (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M)))) V
        (2 * d : ℕ)).hom
      ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ M))
        (regularOpens ℂ M : Opens (TopCat.of (UnderlyingSpace ℂ M))) (2 * d : ℕ)).hom μ)
    have hν : IsFundamentalClass ℚ (euclideanComplexOrientationBasis d) ν :=
      IsFundamentalClass.restrict hμ' V
    have h2 : 2 * d = 2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]
    have hν' := isFundamentalClass_of_det_pos (hν.congrDegree_reindex h2)
      (det_complexOrientationBasisOf_euclideanComplexOrientationBasis_pos d h2)
    have hdeg' : ((2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℤ) -
        (2 * Module.finrank ℂ F : ℕ) = (2 * Module.finrank ℂ E' : ℕ) := by
      rw [← h2]
      exact hdeg
    have key := hu.isFundamentalClass_capProductSupport ℚ hZ (isClosed_pointsOverIn V D.isClosed)
      (hasProperNeighbourhoodDeformations_pointsOverIn hn V D) hν' hdeg'
    rw [MMP.capProductSupport_congrDegree ℚ (TopCat.of V) (isClosed_pointsOverIn V D.isClosed)
      (hasProperNeighbourhoodDeformations_pointsOverIn hn V D) _ (congrArg Nat.cast h2) hdeg hdeg'
      u ν] at key
    exact key
  · rw [dualityMap_apply (μ := μ), borelMooreHomology.restrict_congrDegree,
      borelMooreHomology.pushforward_congrDegree,
      pushforward_opensInterMap_restrict_capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ M)) U
        (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver M D)
        (hasProperNeighbourhoodDeformations_inclHom_preimage_of_subset U hDU
          (hasProperNeighbourhoodDeformations_pointsOver M D)) _ _ c μ]
    rfl

end MMP.Analytic

namespace MMP.Mori

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open: it is
ampleness relative to `f` in the sense of [Stacks, Tag 01VH]. -/
public theorem IsRelativelyAmple.to_stacks {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- The restriction of a module to an open subscheme, in the ringed-space spelling
`modulePullback` of the pull-back, is the restriction `Scheme.Modules.restrict`. -/
public noncomputable def modulePullbackIsoRestrict {Z : Scheme.{u}} (U : Z.Opens)
    (F : Z.Modules) : (modulePullback U.ι.toLRSHom.toShHom).obj F ≅ F.restrict U.ι :=
  (Adjunction.leftAdjointUniq
      (modulePullbackPushforwardAdjunction U.ι.toLRSHom.toShHom)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).app F ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

/-- Relative ampleness is invariant under isomorphism of invertible sheaves. -/
public theorem IsRelativelyAmple.of_iso {X Y : Scheme.{u}} {f : X ⟶ Y} {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f L' := fun y ↦ by
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp⟩

/-- **Ampleness over an open from global relative ampleness.** If the Cartier divisor `L` is
`f`-ample and `L'` has the same coefficients as `L` along every prime divisor meeting `f⁻¹(U)`,
then `L'` is ample over `U`. -/
public theorem Divisor.IsRelativelyAmple.isAmpleOver_of_coeff_eq {X Y : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f]
    {L L' : Divisor X} {hL : L.IsCartier} (hamp : L.IsRelativelyAmple f hL) (hL' : L'.IsCartier)
    (U : Y.Opens)
    (heq : ∀ P : PrimeDivisor X, (P.support ∩ (f ⁻¹ᵁ U : Set X)).Nonempty →
      L'.coeff P = L.coeff P) :
    L'.IsAmpleOver f hL' U := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := hL'.isInvertibleModule_divisorialSheaf
  have h : MMP.Mori.IsRelativelyAmple (f ∣_ U)
      ((modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj L.divisorialSheaf) :=
    .of_stacks _ _ (Stacks.AmplePullbackDatum.isRelativelyAmple_morphismRestrict f _
      (MMP.Mori.IsRelativelyAmple.to_stacks hamp) U)
  exact h.of_iso (modulePullbackIsoRestrict _ _ ≪≫
    Divisor.restrictDivisorialSheafIsoOfEqOn (fun E hE => (heq E hE).symm) ≪≫
    (modulePullbackIsoRestrict _ _).symm)

/-- An `f`-ample Cartier divisor is ample over every open of the base. -/
public theorem Divisor.IsRelativelyAmple.isAmpleOver {X Y : Scheme.{u}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f] {L : Divisor X}
    {hL : L.IsCartier} (hamp : L.IsRelativelyAmple f hL) (U : Y.Opens) :
    L.IsAmpleOver f hL U :=
  hamp.isAmpleOver_of_coeff_eq hL U fun _ _ ↦ rfl

end MMP.Mori

namespace Proof_lem_mmp_conductor_threefold_antiample_fibre

open CategoryTheory AlgebraicGeometry TopologicalSpace

open MMP.Mori MMP.Resolution Limits Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.ProjectiveSpaceChartRatio

/-! ### Colon ideals -/

section Colon

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {ι : Type*} (f : ι → K)

/-- The multipliers `(R : M)` of the fractional ideal `M` generated by the `f k`. -/
private def colonSet : Set K := {c | ∀ k, c * f k ∈ (algebraMap R K).range}

/-- The fractional ideal `M·(R : M)`, which lies in `R`. -/
private def colonSubmodule : Submodule R K :=
  Submodule.span R {x | ∃ c ∈ colonSet R f, ∃ k, x = c * f k}

/-- The colon ideal `M·(R : M)`, as an ideal of `R`. -/
private def colonIdeal : Ideal R := (colonSubmodule R f).comap (Algebra.linearMap R K)

variable {R f}

private theorem mem_colonIdeal {a : R} :
    a ∈ colonIdeal R f ↔ algebraMap R K a ∈ colonSubmodule R f :=
  Iff.rfl

private theorem colonSubmodule_le_range :
    colonSubmodule R f ≤ LinearMap.range (Algebra.linearMap R K) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨c, hc, k, rfl⟩
  obtain ⟨a, ha⟩ := hc k
  exact ⟨a, ha⟩

private theorem map_colonIdeal [Finite ι] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization M S] [Algebra S K] [IsScalarTower R S K]
    (hS : Function.Injective (algebraMap S K)) :
    (colonIdeal R f).map (algebraMap R S) = colonIdeal S f := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap S K (algebraMap R S a) ∈ colonSubmodule S f
    rw [← IsScalarTower.algebraMap_apply]
    have hle : (colonSubmodule R f).restrictScalars R ≤ (colonSubmodule S f).restrictScalars R := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hc, k, rfl⟩
      refine Submodule.subset_span ⟨c, fun k' => ?_, k, rfl⟩
      obtain ⟨b, hb⟩ := hc k'
      exact ⟨algebraMap R S b, by rw [← hb, ← IsScalarTower.algebraMap_apply]⟩
    exact hle ha
  · intro a ha
    have key : ∀ v ∈ colonSubmodule S f, ∃ m ∈ M, (m : R) • v ∈ colonSubmodule R f := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, k, rfl⟩ := hx
        have : ∀ k', ∃ m ∈ M, ((m : R) • c) * f k' ∈ (algebraMap R K).range := by
          intro k'
          obtain ⟨s, hs⟩ := hc k'
          obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.surj M s
          refine ⟨m, m.2, x, ?_⟩
          rw [smul_mul_assoc, ← hs, Algebra.smul_def, IsScalarTower.algebraMap_apply R S K,
            IsScalarTower.algebraMap_apply R S K, ← map_mul, mul_comm, ← hxm]
        choose m hm hm' using this
        cases nonempty_fintype ι
        refine ⟨∏ k', m k', prod_mem fun k' _ => hm k', Submodule.subset_span
          ⟨(∏ k', m k' : R) • c, fun k' => ?_, k, by rw [smul_mul_assoc]⟩⟩
        obtain ⟨y, hy⟩ := hm' k'
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k'), mul_smul, smul_mul_assoc, ← hy]
        exact ⟨_ * y, by rw [map_mul, Algebra.smul_def]⟩
      | zero => exact ⟨1, one_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨m', hm', hmy⟩ := hy
        refine ⟨m * m', mul_mem hm hm', ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmx
        · rw [mul_smul]; exact Submodule.smul_mem _ _ hmy
      | smul s x _ hx =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨⟨y, m'⟩, hym⟩ := IsLocalization.surj M s
        refine ⟨m' * m, mul_mem m'.2 hm, ?_⟩
        have : ((m' * m : R)) • (s • x) = y • ((m : R) • x) := by
          rw [← algebraMap_smul (A := S) (R := R), smul_smul, ← algebraMap_smul (A := S) (R := R) y,
            ← algebraMap_smul (A := S) (R := R) (m : R), smul_smul]
          congr 1
          simp only at hym
          rw [map_mul]
          linear_combination (algebraMap R S m) * hym
        rw [this]
        exact Submodule.smul_mem _ _ hmx
    obtain ⟨m, hm, hmv⟩ := key _ ha
    obtain ⟨x, hx⟩ := colonSubmodule_le_range hmv
    have hx' : algebraMap R S x = algebraMap R S m * a := by
      apply hS
      rw [← IsScalarTower.algebraMap_apply, map_mul, ← IsScalarTower.algebraMap_apply]
      simpa [Algebra.smul_def] using hx
    have hxI : x ∈ colonIdeal R f := by
      rw [mem_colonIdeal]
      have : algebraMap R K x = (m : R) • algebraMap S K a := by simpa using hx
      rw [this]; exact hmv
    have hu : IsUnit (algebraMap R S m) := IsLocalization.map_units S ⟨m, hm⟩
    have : a = hu.unit⁻¹ * algebraMap R S x := by
      rw [hx', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hxI)

end Colon

/-! ### The colon ideal sheaf -/

section Sheaf

variable {Y : Scheme.{u}} [IsIntegral Y] {ι : Type} [Finite ι] (f : ι → Y.functionField)

open Classical in
/-- The colon ideal sheaf `M·(𝒪 : M)` of the fractional ideal generated by the `f k`. -/
private noncomputable def colonIdealSheaf : Y.IdealSheafData where
  ideal U := if h : Nonempty U.1 then (haveI := h; colonIdeal Γ(Y, U.1) f) else ⊤
  map_ideal_basicOpen U g := by
    by_cases hU : Nonempty U.1
    · by_cases hg : Nonempty (Y.basicOpen g)
      · have hg' : Nonempty (Y.affineBasicOpen g).1 := hg
        rw [dif_pos hU, dif_pos hg']
        have hloc := U.2.isLocalization_basicOpen g
        refine @map_colonIdeal Γ(Y, U.1) Y.functionField _ _ _ ι f _ (Submonoid.powers g)
          Γ(Y, Y.basicOpen g) _ _ hloc _ ?_ (Y.germToFunctionField_injective _)
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le g)) _ _ a).symm
      · have hbot : Y.basicOpen g = ⊥ := by
          ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hg ⟨⟨x, hx⟩⟩
        haveI : Subsingleton Γ(Y, Y.basicOpen g) := hbot ▸ inferInstance
        exact Subsingleton.elim _ _
    · have : ¬ Nonempty (Y.affineBasicOpen g).1 := fun ⟨x⟩ => hU ⟨⟨x.1, Y.basicOpen_le g x.2⟩⟩
      rw [dif_neg hU, dif_neg this]
      exact Ideal.map_top _

private theorem colonIdealSheaf_ideal (U : Y.affineOpens) [h : Nonempty U.1] :
    (colonIdealSheaf f).ideal U = colonIdeal Γ(Y, U.1) f := by
  classical
  exact dif_pos h

private theorem stalk_colonIdealSheaf (y : Y) :
    IdealSheafData.stalk (colonIdealSheaf f) y = colonIdeal (Y.presheaf.stalk y) f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU]
  rw [colonIdealSheaf_ideal]
  have hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  letI := Y.presheaf.algebra_section_stalk ⟨y, hyU⟩
  exact @map_colonIdeal Γ(Y, U) Y.functionField _ _ _ ι f _
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (Y.presheaf.stalk y) _ _ hloc _
    (functionField_isScalarTower Y U ⟨y, hyU⟩) (IsFractionRing.injective _ _)

end Sheaf

/-! ### The standard charts of `ℙⁿ_ℤ` -/

attribute [local instance] MvPolynomial.gradedAlgebra

section Charts

variable {n : ℕ}

/-- The integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`. -/
private noncomputable abbrev PZ (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n)

/-- The standard chart `D₊(T_j)`. -/
private noncomputable abbrev chartOpen (n : ℕ) (j : Fin (n + 1)) : (PZ.{u} n).Opens :=
  Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j)

/-- The ratio `T_k / T_j` as a germ at a point of the chart `D₊(T_j)`. -/
private noncomputable def ratio {x : PZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (PZ.{u} n).presheaf.stalk x :=
  (PZ.{u} n).presheaf.germ _ x hx
    (Proj.awayToSection _ _ (coordFracAt (ULift.{u} ℤ) n j k))

private theorem val_stalkIso'_ratio {x : PZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x (ratio hx k)).val =
      Localization.mk (MvPolynomial.X k)
        ⟨MvPolynomial.X j, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hx)⟩ := by
  rw [ratio]
  erw [Proj.stalkIso'_germ]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [coordFracAt, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  simp

private theorem ratio_mul {x : PZ.{u} n} {j m : Fin (n + 1)} (hj : x ∈ chartOpen n j)
    (hm : x ∈ chartOpen n m) (k : Fin (n + 1)) :
    ratio hm k = ratio hj k * ratio hm j := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [map_mul, HomogeneousLocalization.val_mul, val_stalkIso'_ratio, val_stalkIso'_ratio,
    val_stalkIso'_ratio]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]; ring⟩

private theorem ratio_self {x : PZ.{u} n} {j : Fin (n + 1)} (hj : x ∈ chartOpen n j) :
    ratio hj j = 1 := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [(Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x).map_one, HomogeneousLocalization.val_one,
    val_stalkIso'_ratio]
  exact Localization.mk_self ⟨_, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hj)⟩

private theorem germ_mem_closure_ratio {x : PZ.{u} n} {j : Fin (n + 1)} (hx : x ∈ chartOpen n j)
    (b : Γ(PZ.{u} n, chartOpen n j)) :
    (PZ.{u} n).presheaf.germ _ x hx b ∈ Subring.closure (Set.range (ratio hx)) := by
  obtain ⟨s, rfl⟩ : ∃ s, Proj.awayToSection _ _ s = b :=
    ⟨(Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv b, by
      rw [← CommRingCat.comp_apply]
      exact congrArg (fun φ => φ b)
        (congrArg CommRingCat.Hom.hom
          (Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv_hom_id)⟩
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) n j s
  set ψ : HomogeneousLocalization.Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j) →+*
      (PZ.{u} n).presheaf.stalk x :=
    ((PZ.{u} n).presheaf.germ _ x hx).hom.comp (Proj.awayToSection _ _).hom
  change ψ (chartHom _ n j p) ∈ _
  have : ψ.comp (chartHom (ULift.{u} ℤ) n j) =
      MvPolynomial.eval₂Hom (ψ.comp (coeffToAway _ n j)) (fun k => ψ (chartCoord _ n j k)) := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  rw [← RingHom.comp_apply, this]
  have hc : ∀ c : ULift.{u} ℤ, (ψ.comp (coeffToAway _ n j)) c ∈
      Subring.closure (Set.range (ratio hx)) := fun c => by
    rw [show c = ((c.down : ℤ) : ULift.{u} ℤ) from by ext; simp, map_intCast]
    exact intCast_mem _ _
  exact MvPolynomial.eval₂_mem (fun c _ => hc _) (fun k => Subring.subset_closure ⟨k.1, rfl⟩)

end Charts

/-! ### The coordinate ratios on a closed subscheme of `ℙⁿ_Y` -/

section Ratios

variable {Y Z : Scheme.{u}} {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y)

/-- The projection of `Z ⊆ ℙⁿ_Y` to the integral model `ℙⁿ_ℤ`. -/
private noncomputable abbrev toPZ : Z ⟶ PZ.{u} n :=
  i ≫ (pullback.snd (terminal.from Y) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
    projectiveSpaceOver n Y ⟶ PZ.{u} n)

/-- The germ at `z` of the pulled-back ratio `T_k / T_j`, for `z` on the chart `T_j ≠ 0`. -/
private noncomputable def gRatio (z : Z) {j : Fin (n + 1)} (hz : toPZ i z ∈ chartOpen n j)
    (k : Fin (n + 1)) : Z.presheaf.stalk z :=
  (toPZ i).stalkMap z (ratio hz k)

private theorem gRatio_mul (z : Z) {j m : Fin (n + 1)} (hj : toPZ i z ∈ chartOpen n j)
    (hm : toPZ i z ∈ chartOpen n m) (k : Fin (n + 1)) :
    gRatio i z hm k = gRatio i z hj k * gRatio i z hm j := by
  rw [gRatio, gRatio, gRatio, ratio_mul hj hm k, map_mul]

private theorem gRatio_self (z : Z) {j : Fin (n + 1)} (hj : toPZ i z ∈ chartOpen n j) :
    gRatio i z hj j = 1 := by
  rw [gRatio, ratio_self, map_one]

private theorem algebraMap_gRatio [IsIntegral Z] (z : Z) {j : Fin (n + 1)}
    (hz : toPZ i z ∈ chartOpen n j) (hη : toPZ i (genericPoint Z) ∈ chartOpen n j)
    (k : Fin (n + 1)) :
    algebraMap (Z.presheaf.stalk z) Z.functionField (gRatio i z hz k) =
      gRatio i (genericPoint Z) hη k := by
  have h : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  change (Z.presheaf.stalkSpecializes h).hom ((toPZ i).stalkMap z (ratio hz k)) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, gRatio, ratio, ratio]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply (PZ.{u} n).presheaf hz _ _

end Ratios

/-! ### The ideal sheaf -/

section Core

/-- If `ρ(b_k) = g_k ρ(b_j)` for all `k`, the image of the ideal generated by the `b_k` is
generated by `ρ(b_j)`. -/
private theorem map_span_range_eq_span_singleton {A B : Type*} [CommRing A] [CommRing B]
    {ι : Type*} (ρ : A →+* B) (b : ι → A) (g : ι → B) (j : ι)
    (h : ∀ k, ρ (b k) = g k * ρ (b j)) :
    (Ideal.span (Set.range b)).map ρ = Ideal.span {ρ (b j)} := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Function.comp_apply, h k]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨j, rfl⟩)

/-- If `ρ(b_k) = g_k ρ(b_j)` with `ρ(b_j) ≠ 0`, `ρ` local into a domain, and the `b_k` generate a
principal ideal, then every `g_k` lies in the image of `ρ`. -/
private theorem mem_range_of_span_singleton_eq {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    {ι : Type*} (ρ : A →+* B) [IsLocalHom ρ] (b : ι → A) (g : ι → B) (j : ι) (t : A)
    (ht : Ideal.span {t} = Ideal.span (Set.range b)) (h : ∀ k, ρ (b k) = g k * ρ (b j))
    (hne : ρ (b j) ≠ 0) (k : ι) : g k ∈ Set.range ρ := by
  have hspan := map_span_range_eq_span_singleton ρ b g j h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1
    (show b j ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨j, rfl⟩)
  have htm : ρ t ∈ Ideal.span {ρ (b j)} :=
    hspan ▸ Ideal.mem_map_of_mem ρ (ht ▸ Ideal.mem_span_singleton_self t)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 htm
  have hav : ρ a * v = 1 :=
    mul_right_cancel₀ hne (by rw [one_mul, mul_assoc, hv, ← map_mul, ha])
  have hau : IsUnit a := (isUnit_map_iff ρ a).1 (isUnit_iff_exists_inv.2 ⟨v, hav⟩)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (show b k ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨c * ↑hau.unit⁻¹, mul_right_cancel₀ hne ?_⟩
  have hinv : ρ ↑hau.unit⁻¹ * ρ a = 1 := by
    rw [← map_mul, hau.val_inv_mul, map_one]
  rw [← h k, ← hc, ← ha, map_mul, map_mul, map_mul]
  linear_combination (ρ c * ρ t) * hinv

/-- The stalk of an effective Cartier divisor is principal. -/
private theorem exists_stalk_eq_span_singleton {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ t, IdealSheafData.stalk J x = Ideal.span {t} := by
  obtain ⟨U, hU, hxU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hf, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- **The stalks of `ℙⁿ_Y` on a standard chart.** At a point `x` of `ℙⁿ_Y = Y ×_ℤ ℙⁿ_ℤ` on the
chart `T_j ≠ 0`, a subring of the stalk which contains the functions from `Y`, the ratios
`T_k / T_j` and the inverses of its units is the whole stalk. -/
private theorem eq_top_of_subring_stalk_pullback {Y : Scheme.{u}} {n : ℕ} (f : Y ⟶ ⊤_ Scheme)
    (g : PZ.{u} n ⟶ ⊤_ Scheme) (x : ↥(pullback f g)) {j : Fin (n + 1)}
    (hx : pullback.snd f g x ∈ chartOpen n j) (T : Subring ((pullback f g).presheaf.stalk x))
    (h1 : ∀ a, (pullback.fst f g).stalkMap x a ∈ T)
    (h2 : ∀ k, (pullback.snd f g).stalkMap x (ratio hx k) ∈ T)
    (h3 : ∀ v : ((pullback f g).presheaf.stalk x)ˣ, v.1 ∈ T → (v⁻¹).1 ∈ T) :
    T = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pullback.fst f g x)) isOpen_univ
  have hV : IsAffineOpen (chartOpen n j) :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos
  have hW := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf f g hU hV
  have hxW : x ∈ pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j := ⟨hyU, hx⟩
  have hgerm : ∀ s, ((pullback f g).presheaf.germ _ x hxW).hom s ∈ T := by
    have htop := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf f g hU hV rfl
      inf_le_left inf_le_right (T.comap ((pullback f g).presheaf.germ _ x hxW).hom)
      (fun a => ?_) (fun b => ?_)
    · exact fun s => htop.ge (Subring.mem_top s)
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.fst f g) U x hyU a
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      exact h1 _
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.snd f g) (chartOpen n j) x hx b
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      have hle : Subring.closure (Set.range (ratio hx)) ≤
          T.comap ((pullback.snd f g).stalkMap x).hom :=
        Subring.closure_le.2 (Set.range_subset_iff.2 h2)
      exact hle (germ_mem_closure_ratio hx b)
  letI := (pullback f g).presheaf.algebra_section_stalk (U := pullback.fst f g ⁻¹ᵁ U ⊓
    pullback.snd f g ⁻¹ᵁ chartOpen n j) ⟨x, hxW⟩
  haveI := hW.isLocalization_stalk ⟨x, hxW⟩
  refine top_unique fun s _ => ?_
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl s
  dsimp only
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  have hu := IsLocalization.map_units ((pullback f g).presheaf.stalk x) t
  have hinv : IsLocalization.mk' ((pullback f g).presheaf.stalk x)
      (1 : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j)) t =
      (hu.unit⁻¹).1 := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [IsUnit.unit_spec, mul_comm, IsLocalization.mk'_spec, map_one]
  rw [hinv]
  exact T.mul_mem (hgerm a) (h3 _ (hgerm t))

/-- A valuation subring dominating the image of a local ring `A` in its fraction field sends the
maximal ideal of `A` to nonunits. -/
private theorem algebraMap_mem_nonunits_of_le {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] {V : ValuationSubring K}
    (hV : LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : algebraMap A K a ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hV.1 ⟨a, rfl⟩, (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_⟩
  haveI := hV.2
  have hu' := isUnit_of_map_unit (Subring.inclusion hV.1) ⟨_, ⟨a, rfl⟩⟩ hu
  obtain ⟨⟨b, ⟨a', rfl⟩⟩, hb⟩ := isUnit_iff_exists_inv.1 hu'
  have hb' : algebraMap A K (a * a') = algebraMap A K 1 := by
    rw [map_mul, map_one]
    exact congrArg Subtype.val hb
  exact (IsLocalRing.mem_maximalIdeal _).1 ha
    (isUnit_iff_exists_inv.2 ⟨a', IsFractionRing.injective _ _ hb'⟩)

/-- The codomain restriction of `algebraMap A K` to a valuation subring sending the maximal ideal
of `A` to nonunits is a local homomorphism. -/
private theorem isLocalHom_codRestrict_algebraMap {A K : Type*} [CommRing A] [IsLocalRing A]
    [Field K] [Algebra A K] {V : ValuationSubring K} (h₁ : ∀ a : A, algebraMap A K a ∈ V)
    (h₂ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A K a ∈ V.nonunits) :
    IsLocalHom ((algebraMap A K).codRestrict V h₁) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨_, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1
    (h₂ a ((IsLocalRing.mem_maximalIdeal _).2 hna))
  exact (IsLocalRing.mem_maximalIdeal _).1 hm ha

/-- **Valuative uniqueness for points.** Let `φ : Z ⟶ X` be a separated dominant morphism of
integral schemes all of whose maps on local rings are surjective. Then `φ` is injective: two
points over the same point of `X` have the same local ring inside the function field of `Z`, so
a valuation ring dominating it gives two lifts in one valuative square for `φ`. -/
private theorem injective_of_surjective_stalkMap {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (φ : Z ⟶ X) [IsSeparated φ] [IsDominant φ]
    (hsurj : ∀ z, Function.Surjective (φ.stalkMap z)) : Function.Injective φ := by
  intro z z' hzz
  obtain ⟨V, hV⟩ :=
    (LocalSubring.range
      (algebraMap (Z.presheaf.stalk z) Z.functionField)).exists_le_valuationSubring
  -- domination of the local rings of `X`, read in the function field of `Z`
  let HX : X → Prop := fun w => ∀ c : X.presheaf.stalk w,
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V
  let HX' : X → Prop := fun w => ∀ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w),
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V.nonunits
  let D : Z → Prop := fun p => (∀ a : Z.presheaf.stalk p, algebraMap _ Z.functionField a ∈ V) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk p), algebraMap _ Z.functionField a ∈ V.nonunits
  have hDX : ∀ p, D p → HX (φ p) ∧ HX' (φ p) := by
    intro p hp
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact hp.1 _
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine hp.2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 hc (isUnit_of_map_unit _ _ hu)
  have hXD : ∀ p, HX (φ p) → HX' (φ p) → D p := by
    intro p h1 h2
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact h1 c
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine h2 c ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (hu.map _)
  have hDz : D z := ⟨fun a => hV.1 ⟨a, rfl⟩, fun _ => algebraMap_mem_nonunits_of_le hV⟩
  have hDz' : D z' := by
    obtain ⟨h1, h2⟩ := hDX z hDz
    exact hXD z' (hzz ▸ h1) (hzz ▸ h2)
  -- the lift `Spec V ⟶ Z` through a dominated point
  let ψ : ∀ p, D p → Z.presheaf.stalk p →+* V := fun p hp =>
    (algebraMap _ Z.functionField).codRestrict V hp.1
  have hψloc : ∀ p (hp : D p), IsLocalHom (ψ p hp) := fun _ hp =>
    isLocalHom_codRestrict_algebraMap hp.1 hp.2
  let l : ∀ p, D p → (Spec (.of V) ⟶ Z) := fun p hp =>
    Spec.map (CommRingCat.ofHom (ψ p hp)) ≫ Z.fromSpecStalk p
  have hl : ∀ p (hp : D p),
      Spec.map (CommRingCat.ofHom (algebraMap V Z.functionField)) ≫ l p hp =
        Z.fromSpecStalk (genericPoint Z) := by
    intro p hp
    have hy : genericPoint Z ⤳ p := (genericPoint_spec Z).specializes trivial
    have hc : CommRingCat.ofHom (ψ p hp) ≫ CommRingCat.ofHom (algebraMap V Z.functionField) =
        Z.presheaf.stalkSpecializes hy := by
      ext a
      rfl
    simp only [l]
    rw [← Spec.map_comp_assoc, hc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hlp : ∀ p (hp : D p), l p hp (IsLocalRing.closedPoint V) = p := by
    intro p hp
    haveI : IsLocalHom (CommRingCat.ofHom (ψ p hp)).hom := hψloc p hp
    change Z.fromSpecStalk p (Spec.map (CommRingCat.ofHom (ψ p hp))
      (IsLocalRing.closedPoint V)) = p
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  -- the composite `Spec V ⟶ X` only depends on the image point
  let χ : ∀ w, HX w → X.presheaf.stalk w →+* V := fun w hw =>
    ((functionFieldMap φ).comp (algebraMap _ X.functionField)).codRestrict V hw
  have hlφ : ∀ p (hp : D p), l p hp ≫ φ =
      Spec.map (CommRingCat.ofHom (χ (φ p) (hDX p hp).1)) ≫ X.fromSpecStalk (φ p) := by
    intro p hp
    simp only [l]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext c
    change algebraMap _ Z.functionField ((φ.stalkMap p).hom c) =
      functionFieldMap φ (algebraMap _ X.functionField c)
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hχ : ∀ w w' (_ : w = w') (hw : HX w) (hw' : HX w'),
      Spec.map (CommRingCat.ofHom (χ w hw)) ≫ X.fromSpecStalk w =
        Spec.map (CommRingCat.ofHom (χ w' hw')) ≫ X.fromSpecStalk w' := by
    rintro w _ rfl hw hw'
    rfl
  let S : ValuativeCommSq φ :=
    { R := V
      K := Z.functionField
      i₁ := Z.fromSpecStalk (genericPoint Z)
      i₂ := l z hDz ≫ φ
      commSq := ⟨by rw [← hl z hDz, Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion φ S
  let L : S.commSq.LiftStruct := ⟨l z hDz, hl z hDz, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨l z' hDz', hl z' hDz',
    (hlφ z' hDz').trans ((hχ _ _ hzz.symm _ _).trans (hlφ z hDz).symm)⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  rw [← hlp z hDz, ← hlp z' hDz']
  exact congrArg (fun m : Spec (.of V) ⟶ Z => m (IsLocalRing.closedPoint V)) hLL

/-- A morphism `φ : Z ⟶ Bl_I Y` whose composite to `Y` is dominant sends the generic point to the
generic point, when `I` does not vanish at the generic point of `Y`. -/
private theorem map_genericPoint_eq_genericPoint_blowUp {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y] {I : Y.IdealSheafData} [IsIntegral (blowUp I)]
    (hgenY : genericPoint Y ∉ I.support) (φ : Z ⟶ blowUp I) [IsDominant (φ ≫ blowUpToBase I)] :
    φ (genericPoint Z) = genericPoint (blowUp I) := by
  have h1 : blowUpToBase I (φ (genericPoint Z)) = genericPoint Y :=
    map_genericPoint_of_isDominant (φ ≫ blowUpToBase I)
  have hV : φ (genericPoint Z) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
    change blowUpToBase I (φ _) ∈ I.support.compl
    rw [h1]
    exact hgenY
  have hV' : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl :=
    ((genericPoint_spec _).mem_open_set_iff (blowUpToBase I ⁻¹ᵁ _).isOpen).2 ⟨_, trivial, hV⟩
  have h2 : blowUpToBase I (genericPoint (blowUp I)) = genericPoint Y := by
    have hs : genericPoint (blowUp I) ⤳ φ (genericPoint Z) :=
      (genericPoint_spec _).specializes trivial
    have := hs.map (blowUpToBase I).base.hom.continuous
    rw [h1] at this
    exact (this.antisymm ((genericPoint_spec Y).specializes trivial)).eq
  have := (blowUpToBase I ∣_ I.support.compl).homeomorph.injective
    (a₁ := ⟨_, hV⟩) (a₂ := ⟨_, hV'⟩) (Subtype.ext
      (((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV⟩).trans h1).trans
        ((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV'⟩).trans h2).symm))
  exact congrArg Subtype.val this

/-- Under the chart data of `isIso_of_comp_blowUpToBase`, the stalk maps of `φ : Z ⟶ Bl_I Y` are
surjective. -/
private theorem surjective_stalkMap_of_comp_blowUpToBase {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r) (I : Y.IdealSheafData)
    (φ : Z ⟶ blowUp I) (hφ : φ ≫ blowUpToBase I = r) (z : Z)
    (hloc : ∃ (j : Fin (n + 1)) (hz : toPZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0) :
    Function.Surjective (φ.stalkMap z) := by
  subst hφ
  obtain ⟨j, hz, b, hspan, hrel, hne⟩ := hloc
  have hcomp : ∀ a, (φ ≫ blowUpToBase I).stalkMap z a =
      φ.stalkMap z ((blowUpToBase I).stalkMap (φ z) a) := fun a => by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  -- the inverse image of `I` is principal at `φ z`
  obtain ⟨t, ht⟩ := exists_stalk_eq_span_singleton (I.comap (blowUpToBase I))
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) (φ z)
  have ht' : Ideal.span {t} =
      Ideal.span (Set.range fun k => (blowUpToBase I).stalkMap (φ z) (b k)) := by
    rw [← ht, idealStalk_comap_eq_map]
    exact ((congrArg (Ideal.map ((blowUpToBase I).stalkMap (φ z)).hom) hspan).trans
      (Ideal.map_span _ _)).trans (congrArg Ideal.span (Set.range_comp _ _).symm)
  -- the coordinate ratios come from the blow-up
  have hg : ∀ k, gRatio i z hz k ∈ Set.range (φ.stalkMap z) :=
    mem_range_of_span_singleton_eq (φ.stalkMap z).hom
      (fun k => (blowUpToBase I).stalkMap (φ z) (b k)) (gRatio i z hz) j t ht'
      (fun k => by rw [← hcomp, ← hcomp]; exact hrel k) (by rw [← hcomp]; exact hne)
  -- the functions from `Y` come from the blow-up
  have hY : ∀ a, ∃ c, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a = φ.stalkMap z c := by
    intro a
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hir z, CommRingCat.comp_apply, hcomp]
    exact ⟨_, rfl⟩
  have e1 : ∀ a, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a =
      i.stalkMap z ((pullback.fst (terminal.from Y)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))).stalkMap (i z) a) := by
    intro a; rw [Scheme.Hom.stalkMap_comp]; rfl
  have e2 : ∀ k, gRatio i z hz k = i.stalkMap z ((pullback.snd (terminal.from Y)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
        projectiveSpaceOver n Y ⟶ PZ.{u} n).stalkMap (i z) (ratio hz k)) := by
    intro k; rw [gRatio]; erw [Scheme.Hom.stalkMap_comp]; rfl
  -- the image of `φ` pulled back to the stalk of `ℙⁿ_Y` is everything
  have hT := eq_top_of_subring_stalk_pullback (terminal.from Y) (terminal.from (PZ.{u} n))
    (i z) hz (((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom) (fun a => ?_) (fun k => ?_)
    (fun v hv => ?_)
  · intro a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z a
    have : c ∈ ((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom := hT ▸ Subring.mem_top c
    exact this
  · obtain ⟨c, hc⟩ := hY a
    exact ⟨c, hc.symm.trans (e1 a)⟩
  · obtain ⟨c, hc⟩ := hg k
    exact ⟨c, hc.trans (e2 k)⟩
  · obtain ⟨c, hc⟩ := hv
    have hcu : IsUnit c := isUnit_of_map_unit (φ.stalkMap z).hom c (hc ▸ v.isUnit.map _)
    refine ⟨↑hcu.unit⁻¹, ?_⟩
    have h1 : (i.stalkMap z) v.1 * (i.stalkMap z) (v⁻¹).1 = 1 :=
      (map_mul (i.stalkMap z).hom v.1 (v⁻¹).1).symm.trans
        ((congrArg (i.stalkMap z).hom v.mul_inv).trans (map_one _))
    have h2 : (φ.stalkMap z) c * (φ.stalkMap z) ↑hcu.unit⁻¹ = 1 :=
      (map_mul (φ.stalkMap z).hom c _).symm.trans
        ((congrArg (φ.stalkMap z).hom hcu.mul_val_inv).trans (map_one _))
    change (φ.stalkMap z) ↑hcu.unit⁻¹ = (i.stalkMap z) (v⁻¹).1
    change (φ.stalkMap z) c = (i.stalkMap z) v.1 at hc
    linear_combination (-(φ.stalkMap z) ↑hcu.unit⁻¹) * h1 -
      ((φ.stalkMap z) ↑hcu.unit⁻¹ * (i.stalkMap z) (v⁻¹).1) * hc +
      (i.stalkMap z) (v⁻¹).1 * h2

/-- **The comparison morphism is an isomorphism.** Let `Z ⊆ ℙⁿ_Y` be closed and integral over an
integral `Y`, `I` an ideal sheaf on `Y` vanishing nowhere near the generic point, and
`φ : Z ⟶ Bl_I Y` a morphism over `Y`. Suppose that at every `z`, on a chart `T_j ≠ 0`, the stalk of
`I` at the image of `z` is generated by elements `b_k` with `r^♯ b_k = (T_k / T_j) · r^♯ b_j` and
`r^♯ b_j ≠ 0`. Then `φ` is an isomorphism. -/
private theorem isIso_of_comp_blowUpToBase {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r) [IsDominant r]
    (I : Y.IdealSheafData) (hI : I ≠ ⊥) (hgenY : genericPoint Y ∉ I.support)
    (φ : Z ⟶ blowUp I) (hφ : φ ≫ blowUpToBase I = r)
    (hloc : ∀ z : Z, ∃ (j : Fin (n + 1)) (hz : toPZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0) :
    IsIso φ := by
  have hsurj z := surjective_stalkMap_of_comp_blowUpToBase r i hir I φ hφ z (hloc z)
  subst hφ
  haveI : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  have hgen := map_genericPoint_eq_genericPoint_blowUp hgenY φ
  haveI : IsDominant φ := ⟨by
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec (blowUp I)).def]
    exact closure_mono (by rintro _ rfl; exact ⟨_, hgen⟩)⟩
  -- the stalk maps are injective
  have hinj : ∀ z, Function.Injective (φ.stalkMap z) := fun z => by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h := MMP.Mori.functionFieldMap_algebraMap_stalk φ z a
    rw [ha, map_zero] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1
      ((map_eq_zero_iff _ (functionFieldMap φ).injective).1 h)
  -- `φ` is closed and separated
  haveI : IsProper (φ ≫ blowUpToBase I) := by
    rw [← hir]
    haveI := isProper_projectiveSpaceOver n Y
    infer_instance
  haveI : IsSeparated φ := IsSeparated.of_comp φ (blowUpToBase I)
  haveI : UniversallyClosed φ := UniversallyClosed.of_comp_of_isSeparated φ (blowUpToBase I)
  -- `φ` is injective
  have hφinj : Function.Injective φ := injective_of_surjective_stalkMap φ hsurj
  have hclosed : IsClosedMap φ := φ.isClosedMap
  have hφsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← hclosed.isClosed_range.closure_eq]
    exact (IsDominant.denseRange (f := φ)).closure_range
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨TopCat.isIso_of_bijective_of_isClosedMap _ ⟨hφinj, hφsurj⟩ hclosed, fun z => ?_⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj z, hsurj z⟩

end Core

/-! ### Generators of colon ideals, and principal ideals in local domains -/

section ColonGenerators

variable {R : Type*} {K : Type*} [CommRing R] [Field K] [Algebra R K] {ι : Type*} {f : ι → K}

/-- The colon ideal `M·(R : M) ∩ R` is generated by the elements of `R` whose image in `K` is a
product `c f_k` of a multiplier `c ∈ (R : M)` with a generator `f_k` of `M`. -/
private theorem colonIdeal_eq_span (hinj : Function.Injective (algebraMap R K)) :
    colonIdeal R f = Ideal.span {a | ∃ c ∈ colonSet R f, ∃ k, algebraMap R K a = c * f k} := by
  have h : colonSubmodule R f = Submodule.map (Algebra.linearMap R K)
      (Submodule.span R {a | ∃ c ∈ colonSet R f, ∃ k, algebraMap R K a = c * f k}) := by
    rw [Submodule.map_span]
    unfold colonSubmodule
    congr 1
    ext x
    constructor
    · rintro ⟨c, hc, k, rfl⟩
      obtain ⟨a, ha⟩ := hc k
      exact ⟨a, ⟨c, hc, k, ha⟩, ha⟩
    · rintro ⟨a, ⟨c, hc, k, ha⟩, rfl⟩
      exact ⟨c, hc, k, ha⟩
  change (colonSubmodule R f).comap (Algebra.linearMap R K) = _
  rw [h, Submodule.comap_map_eq_of_injective (f := Algebra.linearMap R K) hinj]

/-- If some `f_j` is nonzero and every ratio `f_k / f_j` comes from `R`, the colon ideal is the
unit ideal: `f_j⁻¹` is a multiplier and `f_j⁻¹ f_j = 1`. -/
private theorem colonIdeal_eq_top {j : ι} (hj : f j ≠ 0)
    (h : ∀ k, f k / f j ∈ (algebraMap R K).range) : colonIdeal R f = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_colonIdeal, map_one]
  refine Submodule.subset_span ⟨(f j)⁻¹, fun k => ?_, j, (inv_mul_cancel₀ hj).symm⟩
  rw [inv_mul_eq_div]
  exact h k

end ColonGenerators

/-- In a local ring, if a set `G` generates a nonzero principal ideal, then one element of `G`
already generates it. -/
private theorem exists_mem_span_eq_span_singleton {A : Type*} [CommRing A] [IsLocalRing A]
    {G : Set A} {t : A} (ht : t ≠ 0) (h : Ideal.span G = Ideal.span {t}) :
    ∃ g ∈ G, Ideal.span G = Ideal.span {g} := by
  by_contra hne
  push Not at hne
  have hG : G ⊆ (IsLocalRing.maximalIdeal A * Ideal.span {t} : Ideal A) := by
    intro g hg
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span hg : g ∈ Ideal.span {t})
    by_cases hs : IsUnit s
    · exact absurd (h.trans (Ideal.span_singleton_mul_left_unit hs t).symm) (hne _ hg)
    · exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 hs)
        (Ideal.mem_span_singleton_self t)
  have hle : Ideal.span {t} ≤ IsLocalRing.maximalIdeal A * Ideal.span {t} :=
    h.symm.le.trans (Ideal.span_le.2 hG)
  obtain ⟨z, hz, hzt⟩ := (Ideal.mem_mul_span_singleton).1 (hle (Ideal.mem_span_singleton_self t))
  have hu : IsUnit (1 - z) := by
    by_contra hnu
    have h1 : (1 - z) + z ∈ IsLocalRing.maximalIdeal A :=
      add_mem ((IsLocalRing.mem_maximalIdeal _).2 hnu) hz
    rw [sub_add_cancel] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
  have h0 : (1 - z) * t = 0 := by rw [sub_mul, one_mul, hzt, sub_self]
  exact ht ((hu.mul_right_eq_zero).1 h0)

/-! ### Blow-ups of integral schemes -/

section BlowUp

variable {S : Scheme.{u}} [IsIntegral S]

/-- The blow-up of an ideal sheaf whose cosupport misses the generic point is dominant: it is an
isomorphism over the dense open complement of the cosupport. -/
private theorem isDominant_blowUpToBase (I : S.IdealSheafData)
    (hgen : genericPoint S ∉ I.support) : IsDominant (blowUpToBase I) := by
  haveI := isIso_blowUp_restrict_compl_support I
  have hsub : (I.support.compl : Set S) ⊆ Set.range (blowUpToBase I) := by
    intro y hy
    obtain ⟨z, hz⟩ := (blowUpToBase I ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
    exact ⟨(blowUpToBase I ⁻¹ᵁ I.support.compl).ι z,
      (morphismRestrict_base_coe (blowUpToBase I) I.support.compl z).symm.trans
        (congrArg Subtype.val hz)⟩
  exact ⟨Dense.mono hsub (I.support.compl.isOpen.dense ⟨_, hgen⟩)⟩

/-- On the blow-up of an ideal sheaf whose cosupport misses the generic point, the only point over
the generic point is the generic point. -/
private theorem eq_genericPoint_of_blowUpToBase_eq (I : S.IdealSheafData)
    (hgen : genericPoint S ∉ I.support) [IsIntegral (blowUp I)] (t : blowUp I)
    (ht : blowUpToBase I t = genericPoint S) : t = genericPoint (blowUp I) := by
  haveI := isDominant_blowUpToBase I hgen
  haveI := isIso_blowUp_restrict_compl_support I
  have h1 : blowUpToBase I (genericPoint (blowUp I)) = genericPoint S :=
    map_genericPoint_of_isDominant (blowUpToBase I)
  have hV : t ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
    change blowUpToBase I t ∈ I.support.compl
    rw [ht]; exact hgen
  have hV' : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
    change blowUpToBase I _ ∈ I.support.compl
    rw [h1]; exact hgen
  have := (blowUpToBase I ∣_ I.support.compl).homeomorph.injective
    (a₁ := ⟨_, hV⟩) (a₂ := ⟨_, hV'⟩) (Subtype.ext
      (((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV⟩).trans ht).trans
        ((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV'⟩).trans h1).symm))
  exact congrArg Subtype.val this

end BlowUp

/-! ### The coordinate ratios are regular on the blow-up of the colon ideal -/

section RatioData

open scoped Pointwise

variable {S : Scheme.{u}} [IsIntegral S] {ι : Type} [Finite ι] (f : ι → S.functionField)
  (K : S.IdealSheafData)

/-- **The cofactor chart.** Let `I = C·K` with `C` the colon ideal sheaf of `f`. At every point
`t` of the blow-up `Bl_I S` the invertible ideal `I·𝒪_{T,t}` is generated by one of the
products `c f_{k₀} κ`, hence every ratio `f_l / f_{k₀}` is a regular function at `t`. -/
private theorem exists_ratio_data (I : S.IdealSheafData)
    (hIstalk : ∀ s, IdealSheafData.stalk I s =
      colonIdeal (S.presheaf.stalk s) f * IdealSheafData.stalk K s)
    (hI : genericPoint S ∉ I.support) [IsIntegral (blowUp I)] (t : blowUp I) :
    haveI := isDominant_blowUpToBase _ hI
    ∃ (k₀ : ι) (β : ι → (blowUp I).presheaf.stalk t),
      β k₀ = 1 ∧ functionFieldMap (blowUpToBase I) (f k₀) ≠ 0 ∧
      ∀ l, algebraMap _ (blowUp I).functionField (β l) =
        functionFieldMap (blowUpToBase I) (f l) / functionFieldMap (blowUpToBase I) (f k₀) := by
  classical
  haveI : IsDominant (blowUpToBase I) := isDominant_blowUpToBase _ hI
  -- a regular generator of `I·𝒪_T` at `t`
  obtain ⟨U, hU, htU, g₀, hg₀reg, hg₀⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      (I.comap (blowUpToBase I)) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) t
  haveI : Nonempty U := ⟨⟨t, htU⟩⟩
  have ht₀ : (blowUp I).presheaf.germ U t htU g₀ ≠ 0 := by
    intro h0
    have := germ_injective_of_isIntegral (blowUp I) t htU (h0.trans (map_zero _).symm)
    exact hg₀reg.ne_zero this
  have hstalkT : IdealSheafData.stalk (I.comap (blowUpToBase I)) t =
      Ideal.span {(blowUp I).presheaf.germ U t htU g₀} := by
    rw [IdealSheafData.stalk_eq_map_germ _ t ⟨U, hU⟩ htU, hg₀, Ideal.map_span,
      Set.image_singleton]
  -- generators of `I` at the image point
  have hinj : Function.Injective
      (algebraMap (S.presheaf.stalk (blowUpToBase I t)) S.functionField) :=
    IsFractionRing.injective _ _
  have hspan : Ideal.span ((blowUpToBase I).stalkMap t ''
      ({a | ∃ c ∈ colonSet (S.presheaf.stalk (blowUpToBase I t)) f, ∃ k,
          algebraMap _ S.functionField a = c * f k} *
        (IdealSheafData.stalk K (blowUpToBase I t) : Set _))) =
      Ideal.span {(blowUp I).presheaf.germ U t htU g₀} := by
    have e : ∀ (G : Set (S.presheaf.stalk (blowUpToBase I t))),
        Ideal.span G * IdealSheafData.stalk K (blowUpToBase I t) =
          Ideal.span (G * (IdealSheafData.stalk K (blowUpToBase I t) : Set _)) := fun G => by
      conv_lhs => rw [← Ideal.span_eq (IdealSheafData.stalk K (blowUpToBase I t))]
      exact Ideal.span_mul_span' _ _
    rw [← hstalkT, idealStalk_comap_eq_map, hIstalk, colonIdeal_eq_span hinj, e, Ideal.map_span]
  obtain ⟨g, hgmem, hgspan⟩ := exists_mem_span_eq_span_singleton ht₀ hspan
  obtain ⟨y, ⟨a, ha, κ, hκ, rfl⟩, rfl⟩ := hgmem
  obtain ⟨c₀, hc₀, k₀, hak₀⟩ := ha
  have hg0 : (blowUpToBase I).stalkMap t (a * κ) ≠ 0 := by
    intro h0
    have h := hspan.symm.trans hgspan
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h
    exact ht₀ (Ideal.span_singleton_eq_bot.1 h)
  choose a' ha' using fun l => hc₀ l
  have hmem : ∀ l, (blowUpToBase I).stalkMap t (a' l * κ) ∈
      Ideal.span {(blowUpToBase I).stalkMap t (a * κ)} := fun l => by
    rw [← hgspan]
    exact Ideal.subset_span ⟨_, ⟨a' l, ⟨c₀, hc₀, l, ha' l⟩, κ, hκ, rfl⟩, rfl⟩
  choose β hβ using fun l => Ideal.mem_span_singleton'.1 (hmem l)
  -- the images in the function field
  have himg : ∀ x, algebraMap _ (blowUp I).functionField ((blowUpToBase I).stalkMap t x) =
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField x) := fun x =>
    (MMP.Mori.functionFieldMap_algebraMap_stalk (blowUpToBase I) t x).symm
  have hden : functionFieldMap (blowUpToBase I) c₀ * functionFieldMap (blowUpToBase I) (f k₀) *
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField κ) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← hak₀, ← map_mul, ← himg]
    exact fun h => hg0 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have hc₀κ : functionFieldMap (blowUpToBase I) c₀ *
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField κ) ≠ 0 := fun h =>
    hden (by rw [mul_right_comm, h, zero_mul])
  have hfk₀ : functionFieldMap (blowUpToBase I) (f k₀) ≠ 0 := fun h =>
    hden (by rw [h, mul_zero, zero_mul])
  have hβK : ∀ l, algebraMap _ (blowUp I).functionField (β l) =
      functionFieldMap (blowUpToBase I) (f l) / functionFieldMap (blowUpToBase I) (f k₀) := by
    intro l
    have h1 := congrArg (algebraMap _ (blowUp I).functionField) (hβ l)
    simp only [map_mul, himg, ha', hak₀] at h1
    rw [eq_div_iff hfk₀]
    apply mul_right_cancel₀ hc₀κ
    linear_combination h1
  refine ⟨k₀, β, ?_, hfk₀, hβK⟩
  have h1 := hβK k₀
  rw [div_self hfk₀] at h1
  exact IsFractionRing.injective _ (blowUp I).functionField (h1.trans (map_one _).symm)

end RatioData

/-! ### Coordinate ratios along a morphism -/

/-- Germs of the pull-back of a section along equal morphisms agree. -/
private theorem germ_app_congr {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (x : X)
    (hφ : φ x ∈ U) (hψ : ψ x ∈ U) (s : Γ(Y, U)) :
    X.presheaf.germ (φ ⁻¹ᵁ U) x hφ (φ.app U s) = X.presheaf.germ (ψ ⁻¹ᵁ U) x hψ (ψ.app U s) := by
  subst h
  rfl

/-- If `Z' ⊆ ℙⁿ_{Y'}` maps to `ℙⁿ_ℤ` through `q : Z' ⟶ Z` and `Z ⊆ ℙⁿ_Y`, the coordinate ratios
of `Z'` are the pull-backs along `q` of those of `Z`. -/
private theorem gRatio_eq_stalkMap {Y Y' Z Z' : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ projectiveSpaceOver n Y) (i' : Z' ⟶ projectiveSpaceOver n Y') (q : Z' ⟶ Z)
    (hq : toPZ i' = q ≫ toPZ i) (z : Z') {j : Fin (n + 1)} (hz : toPZ i' z ∈ chartOpen n j)
    (hz' : toPZ i (q z) ∈ chartOpen n j) (k : Fin (n + 1)) :
    gRatio i' z hz k = q.stalkMap z (gRatio i (q z) hz' k) := by
  simp only [gRatio, ratio, Scheme.Hom.germ_stalkMap_apply]
  rw [germ_app_congr hq _ z hz hz']
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- The base change of a closed subscheme `W₀ ⊆ ℙⁿ_S` along `b : T ⟶ S` is a closed subscheme of
`ℙⁿ_T`, compatibly with the projections to `T` and to `ℙⁿ_ℤ`. -/
private theorem exists_isClosedImmersion_projectiveSpaceOver {S T W₀ Γ : Scheme.{u}} {n : ℕ}
    (b : T ⟶ S) (i : W₀ ⟶ projectiveSpaceOver n S) [IsClosedImmersion i]
    (g : Γ ⟶ pullback b (i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)))) (hg : IsClosedImmersion g) :
    ∃ iΓ : Γ ⟶ projectiveSpaceOver n T, IsClosedImmersion iΓ ∧
      iΓ ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ∧
      iΓ ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ ≫ i ≫ pullback.snd _ _ := by
  let e₁ := pullbackLeftPullbackSndIso b
    (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))) i
  let e₂ := pullbackRightPullbackFstIso (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n)) b
  let e₃ : pullback (b ≫ terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≅ projectiveSpaceOver n T :=
    pullback.congrHom (Subsingleton.elim _ _) rfl
  refine ⟨g ≫ e₁.inv ≫ pullback.fst _ _ ≫ e₂.hom ≫ e₃.hom, inferInstance, ?_, ?_⟩
  · simp only [e₃, e₂, e₁, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
      Category.comp_id, pullbackRightPullbackFstIso_hom_fst, pullbackLeftPullbackSndIso_inv_fst]
  · simp only [e₃, e₂, e₁, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc]

/-! ### The blow-up of the colon ideal dominates `W₀` -/

section Domination

variable {S W₀ : Scheme.{u}}

/-- Over its biregular locus a morphism has a point over every point, with bijective map on
local rings. -/
private theorem exists_bijective_stalkMap_of_mem_biregularLocus (f₀ : W₀ ⟶ S) {y : S}
    (hy : y ∈ MMP.Mori.biregularLocus f₀) :
    ∃ w, f₀ w = y ∧ Function.Bijective (f₀.stalkMap w) := by
  haveI : IsIso (f₀ ∣_ MMP.Mori.biregularLocus f₀) := MMP.Mori.isBiregular_biregularLocus f₀
  obtain ⟨x₀, hx₀⟩ := (f₀ ∣_ MMP.Mori.biregularLocus f₀).homeomorph.surjective ⟨y, hy⟩
  have hw : f₀ ((f₀ ⁻¹ᵁ MMP.Mori.biregularLocus f₀).ι x₀) = y :=
    (morphismRestrict_base_coe f₀ _ x₀).symm.trans (congrArg Subtype.val hx₀)
  refine ⟨_, hw, ?_⟩
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus f₀ (x := (f₀ ⁻¹ᵁ _).ι x₀) (hw ▸ hy)
  exact ConcreteCategory.bijective_of_isIso _

variable [IsIntegral S] [IsIntegral W₀] [IsLocallyNoetherian S]

/-- **A blow-up of `S` dominating `W₀`.** Let `f₀ : W₀ ⟶ S` be a projective birational morphism
of integral schemes, isomorphic over the generic point, and `K` an ideal sheaf on `S` nonzero at
the generic point. There is an ideal sheaf `I`, whose cosupport contains that of `K` and misses
the points of the biregular locus of `f₀` outside the cosupport of `K`, such that `Bl_I S ⟶ S`
factors through `f₀`. The ideal is `C·K`, with `C = M·(𝒪_S : M)` the colon ideal of the fractional
ideal `M` generated by the coordinate ratios of the generic point of `W₀ ⊆ ℙⁿ_S`. -/
private theorem exists_blowUp_dominating (f₀ : W₀ ⟶ S) (hf₀ : IsProjectiveMorphism f₀)
    (hb : MMP.Mori.IsBirationalMorphism f₀)
    (hgenbir : genericPoint S ∈ MMP.Mori.biregularLocus f₀) (K : S.IdealSheafData)
    (hK : genericPoint S ∉ K.support) :
    ∃ I : S.IdealSheafData, genericPoint S ∉ I.support ∧ K.support ≤ I.support ∧
      (∀ y ∈ MMP.Mori.biregularLocus f₀, y ∉ K.support → y ∉ I.support) ∧
      ∃ r : blowUp I ⟶ W₀, r ≫ f₀ = blowUpToBase I := by
  classical
  haveI : IsDominant f₀ := MMP.Mori.IsBirationalMorphism.isDominant hb
  obtain ⟨n, i, hi, rfl⟩ := hf₀
  set f₀ := i ≫ (projectiveSpaceOver n S ↘ S) with hf₀def
  -- the chart of the generic point and the coordinate ratios there
  have hcover : ∀ x : PZ.{u} n, ∃ j, x ∈ chartOpen n j := fun x => by
    have hx : x ∈ (⊤ : (PZ.{u} n).Opens) := trivial
    rw [← iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hgen : ∀ (z : W₀) {j : Fin (n + 1)}, toPZ i z ∈ chartOpen n j →
      toPZ i (genericPoint W₀) ∈ chartOpen n j := fun z j hz =>
    ((genericPoint_spec W₀).mem_open_set_iff (toPZ i ⁻¹ᵁ chartOpen n j).isOpen).2 ⟨z, trivial, hz⟩
  obtain ⟨j₀, hj₀⟩ := hcover (toPZ i (genericPoint W₀))
  set c : Fin (n + 1) → W₀.functionField := fun k => gRatio i (genericPoint W₀) hj₀ k with hcdef
  have hc₀ : c j₀ = 1 := gRatio_self i _ hj₀
  have hcrel : ∀ (z : W₀) {j : Fin (n + 1)} (hz : toPZ i z ∈ chartOpen n j) (k : Fin (n + 1)),
      c k = algebraMap _ W₀.functionField (gRatio i z hz k) * c j := by
    intro z j hz k
    rw [algebraMap_gRatio i z hz (hgen z hz)]
    exact gRatio_mul i _ (hgen z hz) hj₀ k
  have hcj : ∀ (z : W₀) {j : Fin (n + 1)} (_ : toPZ i z ∈ chartOpen n j), c j ≠ 0 := by
    intro z j hz h
    have := hcrel z hz j₀
    rw [h, mul_zero, hc₀] at this
    exact one_ne_zero this
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hb
  set f : Fin (n + 1) → S.functionField := fun k => Function.surjInv hbij.2 (c k) with hfdef
  have hf : ∀ k, functionFieldMap f₀ (f k) = c k := fun k => Function.surjInv_eq hbij.2 _
  have hfj : ∀ (z : W₀) {j : Fin (n + 1)} (_ : toPZ i z ∈ chartOpen n j), f j ≠ 0 := by
    intro z j hz h
    apply hcj z hz
    rw [← hf, h, map_zero]
  -- the colon ideal is the unit ideal on the biregular locus
  have hCbir : ∀ y ∈ MMP.Mori.biregularLocus f₀, y ∉ (colonIdealSheaf f).support := by
    intro y hy
    obtain ⟨w, rfl, hwbij⟩ := exists_bijective_stalkMap_of_mem_biregularLocus f₀ hy
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, stalk_colonIdealSheaf]
    obtain ⟨j, hz⟩ := hcover (toPZ i w)
    refine colonIdeal_eq_top (hfj w hz) fun k => ?_
    obtain ⟨a, ha⟩ := hwbij.2 (gRatio i w hz k)
    refine ⟨a, (functionFieldMap f₀).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, map_div₀, hf, hf, eq_div_iff (hcj w hz)]
    exact ((congrArg (algebraMap _ W₀.functionField) ha).trans rfl) ▸ (hcrel w hz k).symm
  set I := colonIdealSheaf f * K with hIdef
  have hIsupp : I.support = (colonIdealSheaf f).support ⊔ K.support :=
    Scheme.IdealSheafData.support_mul _ _
  have hIgen : genericPoint S ∉ I.support := by
    rw [hIsupp]
    rintro (h | h)
    · exact hCbir _ hgenbir h
    · exact hK h
  refine ⟨I, hIgen, hIsupp ▸ le_sup_right, fun y hy hyK => ?_, ?_⟩
  · rw [hIsupp]
    rintro (h | h)
    · exact hCbir y hy h
    · exact hyK h
  -- the blow-ups `T = Bl_I S` and `Γ = Bl_{I 𝒪_{W₀}} W₀`
  have hI0 : I ≠ ⊥ := by
    rintro h
    apply hIgen
    rw [h, Scheme.IdealSheafData.support_bot]
    trivial
  haveI : IsIntegral (blowUp I) := isIntegral_blowUp I hI0
  haveI : IsLocallyNoetherian (blowUp I) :=
    TwoStepTower.isLocallyNoetherian_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI : IsDominant (blowUpToBase I) := isDominant_blowUpToBase I hIgen
  have hJgen : genericPoint W₀ ∉ (I.comap f₀).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change f₀ (genericPoint W₀) ∉ I.support
    rw [map_genericPoint_of_isDominant f₀]
    exact hIgen
  have hJ0 : I.comap f₀ ≠ ⊥ := fun h =>
    hJgen (by rw [h, Scheme.IdealSheafData.support_bot]; trivial)
  haveI : IsIntegral (blowUp (I.comap f₀)) := isIntegral_blowUp _ hJ0
  haveI : IsDominant (blowUpToBase (I.comap f₀)) := isDominant_blowUpToBase _ hJgen
  have hlamb : canonicalLift f₀ I ≫ blowUpToBase I = blowUpToBase (I.comap f₀) ≫ f₀ :=
    canonicalLift_comp_blowUpToBase f₀ I
  have hlamgen : canonicalLift f₀ I (genericPoint (blowUp (I.comap f₀))) =
      genericPoint (blowUp I) := by
    apply eq_genericPoint_of_blowUpToBase_eq I hIgen
    have h1 : (blowUpToBase (I.comap f₀) ≫ f₀) (genericPoint (blowUp (I.comap f₀))) =
        genericPoint S := map_genericPoint_of_isDominant _
    rw [← hlamb] at h1
    exact h1
  haveI : IsDominant (canonicalLift f₀ I) := ⟨by
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec (blowUp I)).def]
    exact closure_mono (by rintro _ rfl; exact ⟨_, hlamgen⟩)⟩
  -- `Γ` is a closed subscheme of `ℙⁿ_T`
  obtain ⟨g, hg, hgsnd, hgfst⟩ := exists_isClosedImmersion_canonicalLift_factor f₀ I
  haveI := hg
  obtain ⟨iΓ, hiΓ, hiΓfst, hiΓsnd⟩ := exists_isClosedImmersion_projectiveSpaceOver
    (blowUpToBase I) i g hg
  haveI := hiΓ
  have hiΓ1 : iΓ ≫ (projectiveSpaceOver n (blowUp I) ↘ blowUp I) = canonicalLift f₀ I :=
    hiΓfst.trans hgfst
  have hiΓ2 : toPZ iΓ = blowUpToBase (I.comap f₀) ≫ toPZ i := by
    have h := congrArg (fun φ => φ ≫ i ≫ pullback.snd (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) hgsnd
    simp only [Category.assoc] at h
    exact hiΓsnd.trans h
  -- the local data on `Γ`
  have hloc : ∀ z : blowUp (I.comap f₀), ∃ (j : Fin (n + 1)) (hz : toPZ iΓ z ∈ chartOpen n j)
      (b : Fin (n + 1) → (blowUp I).presheaf.stalk (canonicalLift f₀ I z)),
      IdealSheafData.stalk (⊤ : (blowUp I).IdealSheafData) (canonicalLift f₀ I z) =
          Ideal.span (Set.range b) ∧
        (∀ k, (canonicalLift f₀ I).stalkMap z (b k) =
          gRatio iΓ z hz k * (canonicalLift f₀ I).stalkMap z (b j)) ∧
        (canonicalLift f₀ I).stalkMap z (b j) ≠ 0 := by
    intro z
    obtain ⟨j, hz⟩ := hcover (toPZ iΓ z)
    have hz' : toPZ i (blowUpToBase (I.comap f₀) z) ∈ chartOpen n j := by
      have := congrArg (fun φ => φ z) hiΓ2
      simp only [Scheme.Hom.comp_apply] at this
      exact this ▸ hz
    obtain ⟨k₀, β, hβ1, hfk₀, hβ⟩ := exists_ratio_data f K I
      (fun s => by rw [MMP.Resolution.Aux.stalk_mul, stalk_colonIdealSheaf]) hIgen (canonicalLift f₀ I z)
    have hΨ : ∀ t : S.functionField, functionFieldMap (canonicalLift f₀ I)
        (functionFieldMap (blowUpToBase I) t) =
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ t) := fun t => by
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hlamb]
    have hfj0 : f j ≠ 0 := hfj _ hz'
    have himgΓ : ∀ x, algebraMap _ (blowUp (I.comap f₀)).functionField
        ((canonicalLift f₀ I).stalkMap z x) =
        functionFieldMap (canonicalLift f₀ I) (algebraMap _ (blowUp I).functionField x) :=
      fun x => (MMP.Mori.functionFieldMap_algebraMap_stalk _ z x).symm
    have hgR : ∀ k, algebraMap _ (blowUp (I.comap f₀)).functionField (gRatio iΓ z hz k) =
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ (f k / f j)) := by
      intro k
      rw [gRatio_eq_stalkMap i iΓ _ hiΓ2 z hz hz' k,
        ← MMP.Mori.functionFieldMap_algebraMap_stalk, map_div₀, hf, hf]
      congr 1
      rw [eq_div_iff (hcj _ hz')]
      exact (hcrel _ hz' k).symm
    have hA : ∀ l, f l ≠ 0 →
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ (f l)) ≠ 0 :=
      fun l hl h => hl ((map_eq_zero_iff _ (functionFieldMap f₀).injective).1
        ((map_eq_zero_iff _ (functionFieldMap (blowUpToBase (I.comap f₀))).injective).1 h))
    have hfk₀' : f k₀ ≠ 0 := fun h => hfk₀ (by rw [h, map_zero])
    refine ⟨j, hz, β, ?_, fun k => ?_, ?_⟩
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 (by
        rw [Scheme.IdealSheafData.support_top]; exact id)]
      exact (Ideal.eq_top_of_isUnit_mem (Ideal.span (Set.range β))
        (Ideal.subset_span (⟨k₀, hβ1⟩ : (1 : _) ∈ Set.range β)) isUnit_one).symm
    · apply IsFractionRing.injective ((blowUp (I.comap f₀)).presheaf.stalk z)
        (blowUp (I.comap f₀)).functionField
      rw [map_mul, himgΓ, himgΓ, hβ, hβ, hgR]
      simp only [map_div₀, hΨ]
      have h1 := hA j hfj0
      have h2 := hA k₀ hfk₀'
      field_simp
    · intro h0
      have h1 := congrArg (algebraMap _ (blowUp (I.comap f₀)).functionField) h0
      rw [himgΓ, hβ, map_zero, map_div₀, hΨ, hΨ] at h1
      exact div_ne_zero (hA j hfj0) (hA k₀ hfk₀') h1
  -- `Γ ⟶ T` is an isomorphism
  haveI := ClosedBlowupSequence.isIso_blowUpToBase_top (blowUp I)
  have htop : (⊤ : (blowUp I).IdealSheafData) ≠ ⊥ := by
    intro h
    have hmem : genericPoint (blowUp I) ∈ ((⊥ : (blowUp I).IdealSheafData).support : Set _) := by
      rw [Scheme.IdealSheafData.support_bot]; trivial
    rw [← h, Scheme.IdealSheafData.support_top] at hmem
    exact hmem
  have hgentop : genericPoint (blowUp I) ∉ (⊤ : (blowUp I).IdealSheafData).support := by
    rw [Scheme.IdealSheafData.support_top]; exact id
  haveI := isIso_of_comp_blowUpToBase (canonicalLift f₀ I) iΓ hiΓ1 ⊤ htop hgentop
    (canonicalLift f₀ I ≫ inv (blowUpToBase ⊤)) (by simp) hloc
  haveI : IsIso (canonicalLift f₀ I) := by
    have e : canonicalLift f₀ I = (canonicalLift f₀ I ≫ inv (blowUpToBase ⊤)) ≫ blowUpToBase ⊤ := by
      simp
    rw [e]
    infer_instance
  refine ⟨inv (canonicalLift f₀ I) ≫ blowUpToBase (I.comap f₀), ?_⟩
  rw [Category.assoc, ← hlamb, IsIso.inv_hom_id_assoc]

end Domination

/-! ### A relatively antiample divisor supported over the exceptional locus -/

section Exceptional

/-- **Coefficients of a pull-back where the morphism is a local isomorphism.** If the stalk map
of `f` at the generic point of `H` is an isomorphism and `f(η_H) = η_P`, then
`coeff_H(f^*C) = coeff_P(C)`. -/
private theorem coeff_isPullback_eq_of_isIso {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (hHP : f H.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap H.genericPoint)] : C'.coeff H = C.coeff P := by
  obtain ⟨V, hV, φ, hφ⟩ := hCc (f H.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV P.component,
    MMP.Positivity.ord_functionFieldMap_of_isIso f H P hHP,
    ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    hφ P ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, hHP ▸ hV⟩]

variable {X Y : Scheme.{u}}

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_mem_biregularLocus (π : X ⟶ Y) {a b : X}
    (ha : π a ∈ MMP.Mori.biregularLocus π) (hab : π a = π b) : a = b := by
  set V := MMP.Mori.biregularLocus π
  haveI : IsIso (π ∣_ V) := MMP.Mori.isBiregular_biregularLocus π
  have hb : π b ∈ V := hab ▸ ha
  have := (π ∣_ V).homeomorph.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext
    (((morphismRestrict_base_coe π V ⟨a, ha⟩).trans hab).trans
      (morphismRestrict_base_coe π V ⟨b, hb⟩).symm))
  exact congrArg Subtype.val this

/-- The prime divisor of `Y` through the image of the generic point of a prime divisor `P` of `X`,
when that image lies in the biregular locus. -/
private noncomputable def imagePrimeDivisor (π : X ⟶ Y) (P : MMP.Mori.PrimeDivisor X)
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π) : MMP.Mori.PrimeDivisor Y :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π P.genericPoint)
    ((MMP.Positivity.coheight_map_of_mem_biregularLocus π h).trans
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P))

private theorem genericPoint_imagePrimeDivisor (π : X ⟶ Y) (P : MMP.Mori.PrimeDivisor X)
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π) :
    (imagePrimeDivisor π P h).genericPoint = π P.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

private theorem imagePrimeDivisor_injective (π : X ⟶ Y) {P P' : MMP.Mori.PrimeDivisor X}
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π)
    (h' : π P'.genericPoint ∈ MMP.Mori.biregularLocus π)
    (e : imagePrimeDivisor π P h = imagePrimeDivisor π P' h') : P = P' := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  apply eq_of_mem_biregularLocus π h
  rw [← genericPoint_imagePrimeDivisor π P h, ← genericPoint_imagePrimeDivisor π P' h', e]

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- **A relatively antiample divisor supported over the exceptional locus.** Let `π : X ⟶ Y` be
a projective morphism of varieties over `k` which is an isomorphism over a nonempty open `O`,
with `Y` smooth and quasi-projective. There is a divisor `G` on `X`, with `-G` Cartier and
`π`-ample, all of whose components lie over the complement of `O`: Kollár's divisor `W`
(Lemma 2.9), minus the pull-back of its image on `Y`, which is Cartier because `Y` is smooth. -/
private theorem exists_isRelativelyAmple_neg_of_isIso {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} (π : X ⟶ Y) (hX : MMP.Mori.IsVariety k (π ≫ sY))
    (hY : MMP.Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    (hYsm : IsSmoothScheme sY) (hπ : IsProjectiveMorphism π) [IsDominant π] (O : Y.Opens)
    [IsIso (π ∣_ O)] (hO : (O : Set Y).Nonempty) :
    ∃ G : Divisor X, ∃ hGc : (-G).IsCartier, (-G).IsRelativelyAmple π hGc ∧
      ∀ P : MMP.Mori.PrimeDivisor X, G.coeff P ≠ 0 → π P.genericPoint ∉ O := by
  classical
  haveI : QuasiCompact sY := hY.toQuasiCompact
  have hOb : O ≤ MMP.Mori.biregularLocus π :=
    MMP.Mori.le_biregularLocus (show MMP.Mori.IsBiregular π O from ‹IsIso (π ∣_ O)›)
  have hOr : ((O : Set Y) ∩ Set.range π).Nonempty := by
    obtain ⟨y, hy⟩ := hO
    obtain ⟨z, hz⟩ := (π ∣_ O).surjective ⟨y, hy⟩
    exact ⟨y, hy, (π ⁻¹ᵁ O).ι z,
      (morphismRestrict_base_coe π O z).symm.trans (congrArg Subtype.val hz)⟩
  -- Kollár's divisor
  obtain ⟨W, -, hWc, hWamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism hX
      hY hYqp hπ ⟨O, hOr, inferInstance⟩
  -- the image of `W` on `Y`
  let B : Divisor Y := ∑ P ∈ W.support,
    if h : π P.genericPoint ∈ O then W.coeff P • Finsupp.single (imagePrimeDivisor π P (hOb h)) 1
    else 0
  have hBcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (h : π P.genericPoint ∈ O),
      B.coeff (imagePrimeDivisor π P (hOb h)) = W.coeff P := by
    intro P h
    change B (imagePrimeDivisor π P (hOb h)) = W P
    rw [Finsupp.finset_sum_apply]
    by_cases hPW : P ∈ W.support
    · rw [Finset.sum_eq_single P]
      · rw [dif_pos h, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
        rfl
      · intro P' _ hP'
        split_ifs with h'
        · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
          exact fun e => hP' (imagePrimeDivisor_injective π _ _ e)
        · rfl
      · exact fun hP => absurd hPW hP
    · rw [Finsupp.notMem_support_iff.1 hPW]
      refine Finset.sum_eq_zero fun P' hP' => ?_
      split_ifs with h'
      · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        rintro e
        exact hPW (imagePrimeDivisor_injective π _ _ e ▸ hP')
      · rfl
  have hBc : B.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm B
  have hBgen : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ B.supp := by
    intro Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp B
  obtain ⟨B', hB'⟩ : ∃ B' : Divisor X, B.IsPullback π hBgen B' :=
    hBc.exists_isPullback (f := π) hBgen
  have hB'c : B'.IsCartier := Divisor.IsPullback.isCartier hB' hBc
  refine ⟨W - B', ?_, ?_, fun P hP hPO => hP ?_⟩
  · rw [neg_sub]
    exact hB'c.sub hWc
  · have :=
      MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback π hWc.neg hWamp hBc hB' hB'c
    convert this using 1
    rw [neg_sub, sub_eq_neg_add]
  · rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    haveI : IsIso (π.stalkMap P.genericPoint) :=
      MMP.isIso_stalkMap_of_mem_biregularLocus π (hOb hPO)
    rw [coeff_isPullback_eq_of_isIso hBc hB' P (imagePrimeDivisor π P (hOb hPO))
      (genericPoint_imagePrimeDivisor π P (hOb hPO)).symm, hBcoeff P hPO]

end Exceptional

/-! ### The divisor of a monomial ideal -/

section MonomialDivisor

open MMP.Intersection

variable {X : Scheme.{u}}

/-- The closed subscheme of the zero Cartier divisor is empty. -/
private theorem subscheme_zero :
    MMP.CartierDivisor.subscheme (0 : X.CartierDivisor)
      MMP.CartierDivisor.isEffective_zero = ⊤ := by
  have h1 : ∀ U : X.Opens, MMP.CartierDivisor.IsRegularLocalEquation
      (0 : X.CartierDivisor) (1 : Γ(X, U)) := by
    intro U
    have hu : IsUnit (MMP.CartierDivisorSheaf.toK U (1 : Γ(X, U))) := by
      rw [map_one]; exact isUnit_one
    refine ⟨hu, ?_⟩
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, map_one]; rfl)
    rw [this, IsLocalEquationOn, cartierClass_one, restrictDivisor, map_zero]
  refine ((MMP.CartierDivisor.eq_subscheme_iff _ ⊤).2 fun U g hg => ?_).symm
  obtain ⟨u, hu⟩ := hg.exists_unit_mul (h1 U)
  rw [mul_one] at hu
  rw [hu, Ideal.span_singleton_eq_top.2 u.isUnit]
  rfl

variable [IsIntegral X] [IsLocallyNoetherian X] {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))

/-- Multiples of an effective Cartier divisor cutting out a prime divisor `E` cut out the powers
of the ideal of `E`, and have Weil divisor the multiples of `E`. -/
private theorem exists_nsmul (A : X.CartierDivisor)
    (E : MMP.Mori.PrimeDivisor X) (hA : MMP.Intersection.IsEffective A)
    (hAs : MMP.CartierDivisor.subscheme A hA = E.idealSheaf)
    (hAw : IsWeilDivisorOfCartier A (Finsupp.single E 1)) (n : ℕ) :
    ∃ hn : MMP.Intersection.IsEffective (n • A),
      MMP.CartierDivisor.subscheme (n • A) hn = E.idealSheaf ^ n ∧
      IsWeilDivisorOfCartier (n • A) ((n : ℤ) • Finsupp.single E 1) := by
  induction n with
  | zero =>
    refine ⟨by rw [zero_smul]; exact MMP.CartierDivisor.isEffective_zero, ?_, ?_⟩
    · simp only [zero_smul, pow_zero, Scheme.IdealSheafData.one_eq_top]
      exact subscheme_zero
    · intro P
      simp only [zero_smul, Nat.cast_zero, DivisorWithCoeffs.coeff_zero]
      exact isOrderAlong_zero _
  | succ n ih =>
    obtain ⟨hn, hns, hnw⟩ := ih
    have hn' : MMP.Intersection.IsEffective (n • A + A) := hn.add hA
    refine ⟨by rw [succ_nsmul]; exact hn', ?_, ?_⟩
    · have e := MMP.CartierDivisor.subscheme_add hn hA hn'
      simp only [succ_nsmul, pow_succ]
      rw [e, hns, hAs]
    · intro P
      have := (hnw P).add (hAw P)
      simpa only [succ_nsmul, Nat.cast_succ, add_smul, one_smul, DivisorWithCoeffs.coeff_add]
        using this

/-- **The divisor of a monomial ideal.** On a smooth variety, the ideal `∏_E I_E^{c_E}` over a
finite set of prime divisors is the ideal sheaf of an effective Cartier divisor whose Weil divisor
is `∑ c_E E`. -/
private theorem exists_isWeilDivisorOfCartier_prod [AlgebraicGeometry.IsVariety k sX]
    (hsm : IsSmoothScheme sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℕ) :
    ∃ (A : X.CartierDivisor)
      (hA : MMP.Intersection.IsEffective A),
      MMP.CartierDivisor.subscheme A hA = ∏ E ∈ s, E.idealSheaf ^ c E ∧
      IsWeilDivisorOfCartier A (∑ E ∈ s, (c E : ℤ) • Finsupp.single E 1) := by
  classical
  have hreg : IsRegular X := MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, MMP.CartierDivisor.isEffective_zero, ?_, fun P => ?_⟩
    · rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
      exact subscheme_zero
    · rw [Finset.sum_empty, DivisorWithCoeffs.coeff_zero]
      exact isOrderAlong_zero _
  | insert E s hE ih =>
    obtain ⟨A, hA, hAs, hAw⟩ := ih
    obtain ⟨AE, hAEw⟩ :=
      (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2 X hreg
        (Finsupp.single E 1)
    obtain ⟨hAEe, hAEs⟩ :=
      IsWeilDivisorOfCartier.isEffective_and_subscheme_eq_of_isSmoothScheme sX hsm hAEw
    obtain ⟨hn, hns, hnw⟩ := exists_nsmul AE E hAEe hAEs hAEw (c E)
    refine ⟨c E • AE + A, hn.add hA, ?_, fun P => ?_⟩
    · rw [MMP.CartierDivisor.subscheme_add hn hA (hn.add hA), hns, hAs,
        Finset.prod_insert hE]
    · rw [Finset.sum_insert hE, DivisorWithCoeffs.coeff_add]
      exact (hnw P).add (hAw P)

end MonomialDivisor

/-! ### Composing with the blow-up of `S` -/

section Compose

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple MMP.Intersection

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- The Weil divisor of `-A` is minus the Weil divisor of `A`. -/
private theorem isWeilDivisorOfCartier_neg {X : Scheme.{u}} {A : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier A w) :
    IsWeilDivisorOfCartier (-A) (-w) := by
  intro P
  obtain ⟨a, b, ha, hb, ⟨g, ⟨U, hxU, g', hg', hgg⟩, hbu, hbg⟩, la, lb, hla, hlb, hN⟩ := h P
  have hgu : IsUnit g := hgg ▸ g'.isUnit.map _
  refine ⟨b, a, hb, ha, ⟨_, ⟨U, hxU, g'⁻¹, hg'.inv, rfl⟩, ?_, ?_⟩, lb, la, hlb, hla, ?_⟩
  · rw [← hbg]; exact hbu.mul hgu
  · rw [← hbg, ← hgg, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rw [DivisorWithCoeffs.coeff_neg, hN]; ring

/-- **[Stacks, Tag 0C4K] against a module on the target.** Let `h : W ⟶ T`, `b : T ⟶ S` be
quasi-compact, `S` quasi-compact, `L` an `h`-ample Cartier divisor on the normal scheme `W` and
`M` a `b`-ample invertible sheaf on `T` whose pull-back is `𝒪_W(N)`. Then `L + nN` is
`(h ≫ b)`-ample for all large `n`. -/
private theorem exists_isRelativelyAmple_add_nsmul_of_iso {W T S : Scheme.{u}}
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace S]
    (h : W ⟶ T) (b : T ⟶ S) [QuasiCompact h] [QuasiCompact b] (M : T.Modules)
    [IsInvertibleModule T M] (hM : MMP.Mori.IsRelativelyAmple b M)
    {L : Divisor W} (hLc : L.IsCartier) (hL : L.IsRelativelyAmple h hLc)
    {N : Divisor W} (hNc : N.IsCartier)
    (eN : (modulePullback h.toLRSHom.toShHom).obj M ≅ N.divisorialSheaf) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (L + n • N).IsRelativelyAmple (h ≫ b) (hLc.add (hNc.nsmul n)) := by
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hNc.isInvertibleModule_divisorialSheaf
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp h b _ _
    (MMP.Mori.IsRelativelyAmple.to_stacks hL) hM.to_stacks
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := (hLc.add (hNc.nsmul n)).isInvertibleModule_divisorialSheaf
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule h L.divisorialSheaf M n ≅
      (L + n • N).divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso W (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso h _ n ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso W _ _ eN n ≪≫
          (divisorialSheafNsmulIso hNc n).symm) ≪≫
      hLc.divisorialSheafTensorIso (hNc.nsmul n)
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ n hn))

/-- **The pull-back of the exceptional ideal.** If `h : W ⟶ Bl_I S` pulls `I` back to the closed
subscheme of an effective Cartier divisor `A` on the normal scheme `W` with Weil divisor `K`, the
pull-back of the exceptional ideal sheaf `I·𝒪_{Bl}` is `𝒪_W(-K)`. -/
private theorem nonempty_modulePullback_exceptionalIdealModule_iso {W S : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (I : S.IdealSheafData)
    (h : W ⟶ blowUp I) (A : W.CartierDivisor)
    (hA : MMP.Intersection.IsEffective A)
    (hAs : MMP.CartierDivisor.subscheme A hA = I.comap (h ≫ blowUpToBase I))
    {K : Divisor W} (hAw : IsWeilDivisorOfCartier A K) :
    Nonempty ((modulePullback h.toLRSHom.toShHom).obj (exceptionalIdealModule I) ≅
      (-K).divisorialSheaf) := by
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdeal I) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  have heq : (exceptionalIdeal I).comap h = MMP.CartierDivisor.subscheme A hA := by
    rw [hAs, Scheme.IdealSheafData.comap_comp]
  have hdef : Stacks.Divisors.IsPullbackDefined h (exceptionalIdeal I) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor ((exceptionalIdeal I).comap h)
    rw [heq]
    exact MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hA
  exact ⟨Stacks.Divisors.pullbackIdealSheafComapIso h (exceptionalIdeal I) hdef ≪≫
    eqToIso (congrArg (fun J : W.IdealSheafData =>
      Stacks.ClosedImmersion.idealSheaf J.subschemeι.toLRSHom.toShHom) heq) ≪≫
    MMP.CartierDivisor.idealSheafIsoSheafNeg A hA ≪≫
      (isWeilDivisorOfCartier_neg hAw).sheafIsoDivisorialSheaf⟩

end Compose

/-! ### Cosupports of monomial ideals -/

section MonomialSupport

/-- The cosupport of a product of positive powers is the union of the cosupports. -/
private theorem coe_support_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (n : ι → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) :
    ((∏ i ∈ s, I i ^ n i).support : Set X) = ⋃ i ∈ s, ((I i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul,
      Scheme.IdealSheafData.support_pow _ _ (hn i (Finset.mem_insert_self i s)),
      Finset.set_biUnion_insert,
      ← ih fun j hj => hn j (Finset.mem_insert_of_mem hj)]
    rfl

/-- For `J = ∏_{E ∈ Supp D} I_E^{D E}`, a prime divisor is a component of `D` exactly when its
generic point lies in the cosupport of `J`. -/
private theorem mem_support_iff_genericPoint_mem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : DivisorWithCoeffs ℕ X) {J : X.IdealSheafData}
    (hJ : J = ∏ E ∈ D.support, E.idealSheaf ^ D E) (P : MMP.Mori.PrimeDivisor X) :
    P ∈ D.support ↔ P.genericPoint ∈ J.support := by
  subst hJ
  change P ∈ D.support ↔
    P.genericPoint ∈ ((∏ E ∈ D.support, E.idealSheaf ^ D E).support : Set X)
  rw [coe_support_prod_pow _ _ _ fun E hE => Finsupp.mem_support_iff.1 hE]
  refine ⟨fun hP => Set.mem_biUnion hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P),
    fun hP => ?_⟩
  obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.1 hP
  by_contra hne
  exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne
    (fun (h : P = E) => hne (h ▸ hE)) hPE

/-- A divisor whose components form a simple normal crossing family is an snc divisor. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (D : DivisorWithCoeffs ℕ X)
    (h : IsSNCFamily sX fun E : D.support => E.1.idealSheaf) : D.IsSNC sX := by
  refine ⟨fun E hE => (h.1 ⟨E, hE⟩).2.2, fun x => ?_⟩
  obtain ⟨n, z, c, hz, hstalk, hinj⟩ := h.2 x
  refine ⟨n, z, fun E => c ⟨⟨E.1, E.2.1⟩, E.2.2⟩, hz, fun E E' hEE' => ?_,
    fun E => hstalk ⟨⟨E.1, E.2.1⟩, E.2.2⟩⟩
  have := hinj hEE'
  simp only [Subtype.mk.injEq] at this
  exact Subtype.ext this

end MonomialSupport

/-! ### The components of the fibre over a closed point -/

section FibreComponents

/-- **Components of a fibre are projective varieties of one dimension less.** Let `f : W ⟶ S` be
proper, with `W` a quasi-projective variety of dimension `d + 1` over `k`, and `P` a prime divisor
of `W` whose generic point maps to a closed point `x`. Then `P` is a projective variety of
dimension `d`: it is proper over `Spec κ(x)`, which is finite over `k`. -/
private theorem isProjectiveVariety_and_topologicalKrullDim_of_map_eq {k : Type u} [Field k]
    {W S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [LocallyOfFiniteType sS] (f : W ⟶ S) [IsProper f]
    (sW : W ⟶ Spec (.of k)) (hsW : f ≫ sS = sW) (hW : IsQuasiProjectiveVariety k sW) {d : ℕ}
    (hWdim : topologicalKrullDim W = ((d + 1 : ℕ) : WithBot ℕ∞)) (x : S)
    (hxc : IsClosed ({x} : Set S)) (P : MMP.Mori.PrimeDivisor W)
    (hP : f P.genericPoint = x) :
    MMP.Mori.IsProjectiveVariety k (P.idealSheaf.subschemeι ≫ sW) ∧
      topologicalKrullDim P.idealSheaf.subscheme = d := by
  haveI : IsIntegral W := hW.toIsIntegral
  haveI : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  haveI : IsSeparated sW := hW.toIsSeparated
  haveI : QuasiCompact sW := hW.toQuasiCompact
  haveI : IsIntegral P.idealSheaf.subscheme := P.integral
  -- the dimension
  have hdim : topologicalKrullDim P.idealSheaf.subscheme = d := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW P.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hWdim] at h
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    change topologicalKrullDim (P.support : Set W) = d
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact ENat.WithBot.add_one_cancel.mp (by exact_mod_cast h)
  -- `P` maps into the closed point `x`
  have hPx : ∀ w ∈ (P.support : Set W), f w = x := by
    intro w hw
    have := (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hw).map
      f.base.hom.continuous
    rw [hP] at this
    exact (this.mem_closed hxc rfl)
  -- properness, through `Spec κ(x)`
  have : IsClosedImmersion (S.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hxc
  set h := P.idealSheaf.subschemeι ≫ f with hh
  have H : (S.fromSpecResidueField x).ker ≤ h.ker := by
    have h1 : h.ker = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (h.base '' (⊤ : Closeds P.idealSheaf.subscheme))) := by
      rw [← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
    rintro _ ⟨z, -, rfl⟩
    refine (S.fromSpecResidueField x).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    have hz : P.idealSheaf.subschemeι z ∈ (P.idealSheaf.support : Set W) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hPx _ hz
  let l := IsClosedImmersion.lift (S.fromSpecResidueField x) h H
  have hl : l ≫ S.fromSpecResidueField x = h := IsClosedImmersion.lift_fac _ _ H
  have : IsProper (l ≫ S.fromSpecResidueField x) := hl ▸ inferInstance
  have : IsProper l := IsProper.of_comp l (S.fromSpecResidueField x)
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  have : IsFinite (S.fromSpecResidueField x ≫ sS) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hprop : IsProper (P.idealSheaf.subschemeι ≫ sW) := by
    rw [← hsW, ← Category.assoc, ← hh, ← hl, Category.assoc]
    infer_instance
  -- quasi-projectivity, hence projectivity
  haveI hvar : AlgebraicGeometry.IsVariety k (P.idealSheaf.subschemeι ≫ sW) := {}
  have hunit : ∃ (M : (Spec (.of k)).Modules) (hM : Stacks.Ample.IsInvertibleModule _ M),
      letI : Stacks.Ample.IsInvertibleModule _ M := hM
      Stacks.Ample.IsAmple _ M :=
    ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  haveI hqp : IsQuasiProjectiveVariety k (P.idealSheaf.subschemeι ≫ sW) :=
    (isQuasiProjectiveVariety_iff k _).2 ⟨hvar, isQuasiProjective_comp_of_exists_isAmple _ _
      hunit (isQuasiProjective_of_isImmersion _) hW.isQuasiProjective⟩
  haveI : AlgebraicGeometry.IsVariety k (𝟙 (Spec (.of k))) := {}
  have hH := MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
    (P.idealSheaf.subschemeι ≫ sW) (𝟙 (Spec (.of k))) (P.idealSheaf.subschemeι ≫ sW)
    (Category.comp_id _)
  exact ⟨(AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hvar, hH⟩, hdim⟩

end FibreComponents

/-! ### The main construction -/

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rw [hfac, ← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- Two morphisms into `W₀` which agree after `f₀ : W₀ ⟶ S` agree on the preimage of the
biregular locus of `f₀`, hence everywhere when the source is reduced and `f₀` separated. -/
private theorem eq_of_comp_eq_of_isSeparated {X W₀ S : Scheme.{u}} [IsReduced X]
    [IrreducibleSpace X] (f₀ : W₀ ⟶ S) [IsSeparated f₀] {a b : X ⟶ W₀} (h : a ≫ f₀ = b ≫ f₀)
    (hne : ((a ≫ f₀) ⁻¹ᵁ MMP.Mori.biregularLocus f₀ : Set X).Nonempty) : a = b := by
  set V := MMP.Mori.biregularLocus f₀
  haveI : IsIso (f₀ ∣_ V) := MMP.Mori.isBiregular_biregularLocus f₀
  set O := (a ≫ f₀) ⁻¹ᵁ V
  haveI : IsDominant O.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact O.isOpen.dense hne⟩
  refine ext_of_isDominant_of_isSeparated f₀ h O.ι ?_
  have hra : Set.range (O.ι ≫ a) ⊆ Set.range (f₀ ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2
  have hrb : Set.range (O.ι ≫ b) ⊆ Set.range (f₀ ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (b ≫ f₀) z.1 ∈ V
    rw [← h]
    exact z.2
  haveI : Mono ((f₀ ⁻¹ᵁ V).ι ≫ f₀) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hab : IsOpenImmersion.lift _ _ hra = IsOpenImmersion.lift _ _ hrb := by
    rw [← cancel_mono ((f₀ ⁻¹ᵁ V).ι ≫ f₀), ← Category.assoc, ← Category.assoc,
      IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, h]
  rw [← IsOpenImmersion.lift_fac _ _ hra, ← IsOpenImmersion.lift_fac _ _ hrb, hab]

/-- A blow-up sequence truncated at its length is itself. -/
private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

/-- The empty ordered divisor has no irreducible components. -/
private theorem pairwise_disjoint_componentsOf_empty {X : Scheme.{u}} :
    (componentsOf (OrderedDivisor.empty X).support).Pairwise Disjoint := by
  intro C hC
  obtain ⟨x, hx⟩ := hC.1.1.nonempty
  obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hC.1.2 hx)
  exact i.elim0

end Proof_lem_mmp_conductor_threefold_antiample_fibre

namespace MMP.Threefold

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution Limits
  Stacks.AlgebraicGeometry.ProjPolyChart Stacks.ProjectiveSpaceChartRatio
  Proof_lem_mmp_conductor_threefold_antiample_fibre

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coefficient of `P` in `∑ E ∈ s, c E • single E 1` is `c P` if `P ∈ s`, and `0`
otherwise. -/
public theorem finset_sum_smul_single_one_apply {α : Type*} [DecidableEq α] (s : Finset α)
    (c : α → ℤ) (P : α) :
    (∑ E ∈ s, c E • Finsupp.single E (1 : ℤ)) P = if P ∈ s then c P else 0 := by
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- If `f` is an isomorphism over `V` and `g` is one over `f⁻¹(V)`, then `g ≫ f` is one over
`V`. -/
public theorem le_biregularLocus_comp {X Y Z : Scheme.{u}} {g : X ⟶ Y} {f : Y ⟶ Z} {V : Z.Opens}
    (hV : V ≤ biregularLocus f) (hVg : f ⁻¹ᵁ V ≤ biregularLocus g) :
    V ≤ biregularLocus (g ≫ f) := by
  have h₁ : IsIso (f ∣_ V) := isBiregular_iff_le_biregularLocus.2 hV
  have h₂ : IsIso (g ∣_ f ⁻¹ᵁ V) := isBiregular_iff_le_biregularLocus.2 hVg
  have : IsBiregular (g ≫ f) V := by
    change IsIso ((g ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' h₂ h₁
  exact le_biregularLocus this

/-- The reduced fibre over a closed point `x` of a morphism `φ : W ⟶ S` on which `I·𝒪_W` is
the monomial ideal of an snc family, when `x` is the only point of `I.support` in an open `U`, is
a reduced snc divisor whose components are the prime divisors mapping to `x`. -/
public theorem exists_isReducedEffective_isSNC_supp_eq_preimage {S W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (φ : W ⟶ S) (sW : W ⟶ Spec (.of ℂ))
    (DJ : DivisorWithCoeffs ℕ W) (hDJsnc : IsSNCFamily sW fun E : DJ.support => E.1.idealSheaf)
    (I : S.IdealSheafData) (hDJprod : I.comap φ = ∏ E ∈ DJ.support, E.idealSheaf ^ DJ E)
    (hDJmem : ∀ P : MMP.Mori.PrimeDivisor W, P ∈ DJ.support ↔ φ P.genericPoint ∈ I.support)
    {x : S} (hxc : IsClosed ({x} : Set S)) (hxI : x ∈ I.support) (U : S.Opens) (hxU : x ∈ U)
    (hIU : ∀ y ∈ U, y ∈ I.support → y = x) :
    ∃ E : Divisor W, MMP.Intersection.IsReducedEffective E ∧ DivisorWithCoeffs.IsSNC sW E ∧
      (E.supp : Set W) = φ.base ⁻¹' {x} ∧
      ∀ P : MMP.Mori.PrimeDivisor W, P ∈ E.support ↔ φ P.genericPoint = x := by
  classical
  set F := DJ.support.filter fun P => φ P.genericPoint = x with hFdef
  have hEcoeff : ∀ P, (∑ Q ∈ F, Finsupp.single Q (1 : ℤ) : Divisor W).coeff P =
      if P ∈ F then 1 else 0 := by
    intro P
    change (∑ Q ∈ F, Finsupp.single Q (1 : ℤ)) P = _
    simpa using finset_sum_smul_single_one_apply F (fun _ => 1) P
  have hEmem : ∀ P, P ∈ (∑ Q ∈ F, Finsupp.single Q (1 : ℤ) : Divisor W).support ↔
      P ∈ F := fun P => by
    rw [Finsupp.mem_support_iff]
    change (∑ Q ∈ F, Finsupp.single Q (1 : ℤ) : Divisor W).coeff P ≠ 0 ↔ _
    rw [hEcoeff]
    split_ifs with hP <;> simp [hP]
  have hFmem : ∀ P, P ∈ F ↔ φ P.genericPoint = x := fun P => by
    rw [hFdef, Finset.mem_filter, hDJmem]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hxI, h⟩⟩
  refine ⟨∑ Q ∈ F, Finsupp.single Q (1 : ℤ), fun P => ?_, ?_, ?_, fun P => ?_⟩
  · rw [hEcoeff]
    split_ifs <;> simp
  · refine DivisorWithCoeffs.IsSNC.of_support_subset (isSNC_of_isSNCFamily sW DJ hDJsnc) ?_
    intro P hP
    rw [hEmem] at hP
    exact (Finset.mem_filter.1 hP).1
  · ext w
    rw [DivisorWithCoeffs.coe_supp, Set.mem_iUnion₂, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, hP, hwP⟩
      rw [hEmem, hFmem] at hP
      have := (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hwP).map
        φ.base.hom.continuous
      rw [hP] at this
      exact (this.mem_closed hxc rfl).symm ▸ rfl
    · intro hw
      have hwJ : w ∈ ((I.comap φ).support : Set W) := by
        rw [Scheme.IdealSheafData.support_comap]
        change φ w ∈ I.support
        rw [hw]
        exact hxI
      rw [hDJprod, coe_support_prod_pow _ _ _ fun E hE => Finsupp.mem_support_iff.1 hE]
        at hwJ
      obtain ⟨P, hP, hwP⟩ := Set.mem_iUnion₂.1 hwJ
      have hsp' := (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hwP).map
        φ.base.hom.continuous
      rw [hw] at hsp'
      have hU' : φ P.genericPoint ∈ U := hsp'.mem_open U.isOpen hxU
      refine ⟨P, ?_, hwP⟩
      rw [hEmem, hFmem]
      exact hIU _ hU' ((hDJmem P).1 hP)
  · rw [hEmem, hFmem]

/-- **An antiample snc fibre over an isolated threefold singularity.** Let `f₀ : W₀ ⟶ S` be a
projective resolution of a normal quasi-projective complex threefold, `x ∈ S` and `U ∋ x` an open
with `Sing(S) ∩ U = {x}` over whose complement of `x` the map `f₀` is an isomorphism. There is a
morphism `r : W ⟶ W₀` such that `f = r ≫ f₀` is a projective resolution of `S` with `W`
quasi-projective which is an isomorphism over `U ∖ {x}`, the reduced fibre `f⁻¹(x)` is the
support of a reduced snc divisor `E` whose components are smooth projective surfaces, and some
`D = ∑ mᵢ Eᵢ` with all `mᵢ > 0` has `-D` Cartier and ample over `U`. -/
public theorem exists_isResolution_comp_isSNC_isAmpleOver_neg_and_subset_biregularLocus
    {S W₀ : Scheme.{0}} [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : IsQuasiProjectiveVariety ℂ sS) (hSdim : topologicalKrullDim S = 3)
    {f₀ : W₀ ⟶ S} (hf₀ : MMP.Intersection.IsResolution sS f₀)
    (x : S) (U : S.Opens) (hxU : x ∈ U)
    (hx : (singularLocus sS : Set S) ∩ U = {x})
    (hU : (U : Set S) \ {x} ⊆ biregularLocus f₀) :
    ∃ (W : Scheme.{0}) (_ : IsLocallyNoetherian W) (_ : IsNormal W) (_ : CompactSpace W)
      (r : W ⟶ W₀),
      MMP.Intersection.IsResolution sS (r ≫ f₀) ∧
      IsQuasiProjectiveVariety ℂ (r ≫ f₀ ≫ sS) ∧
      (U : Set S) \ {x} ⊆ biregularLocus (r ≫ f₀) ∧
      ∃ E : Divisor W, MMP.Intersection.IsReducedEffective E ∧
        DivisorWithCoeffs.IsSNC (r ≫ f₀ ≫ sS) E ∧
        (E.supp : Set W) = (r ≫ f₀).base ⁻¹' {x} ∧
        (∀ P ∈ E.support,
          MMP.Mori.IsProjectiveVariety ℂ (P.idealSheaf.subschemeι ≫ r ≫ f₀ ≫ sS) ∧
          topologicalKrullDim P.idealSheaf.subscheme = 2) ∧
        ∃ D : Divisor W, (∀ P ∈ E.support, 0 < D.coeff P) ∧ (∀ P ∉ E.support, D.coeff P = 0) ∧
          ∃ h : (-D).IsCartier, (-D).IsAmpleOver (r ≫ f₀) h U := by
  obtain ⟨hSv, hWv, hWs, hproj, hbir⟩ := hf₀
  haveI : IsIntegral S := hSv.toIsIntegral
  haveI : IsIntegral W₀ := hWv.toIsIntegral
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : LocallyOfFiniteType (f₀ ≫ sS) := hWv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (f₀ ≫ sS)
  -- `x` is a closed point, distinct from the generic point
  have hxc : IsClosed ({x} : Set S) := by
    haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
    apply isClosed_singleton_of_isLocallyClosed_singleton
    refine ⟨U, singularLocus sS, U.isOpen, (singularLocus sS).isClosed, ?_⟩
    rw [← hx, Set.inter_comm]
  have hxgen : x ≠ genericPoint S := by
    rintro rfl
    have huniv : (Set.univ : Set S) = {genericPoint S} := by
      rw [← (genericPoint_spec S).def, hxc.closure_eq]
    haveI : Subsingleton S :=
      Set.subsingleton_univ_iff.1 (huniv ▸ Set.subsingleton_singleton)
    haveI : DiscreteTopology S := Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology S
    rw [hSdim] at h0
    exact absurd h0 (by decide)
  have hgenbir : genericPoint S ∈ biregularLocus f₀ := by
    refine hU ⟨?_, fun h => hxgen (Set.mem_singleton_iff.1 h).symm⟩
    exact ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hxU⟩
  -- the ideal of `x`, and the dominating blow-up
  set m : S.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hxc⟩ with hmdef
  have hmsupp : (m.support : Set S) = {x} := by
    rw [hmdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hmgen : genericPoint S ∉ m.support := by
    rw [← SetLike.mem_coe, hmsupp]
    exact fun h => hxgen (Set.mem_singleton_iff.1 h).symm
  obtain ⟨I, hIgen, hmI, hIbir, r, hr⟩ :=
    exists_blowUp_dominating f₀ hproj hbir hgenbir m hmgen
  have hxI : x ∈ I.support := hmI (by rw [← SetLike.mem_coe, hmsupp]; rfl)
  have hIU : ∀ y ∈ U, y ∈ I.support → y = x := by
    intro y hyU hyI
    by_contra hyx
    exact hIbir y (hU ⟨hyU, hyx⟩) (by rw [← SetLike.mem_coe, hmsupp]; exact hyx) hyI
  -- principalization of `J = I·𝒪_{W₀}` on the smooth variety `W₀`
  haveI : IsDominant f₀ := hbir.isDominant
  have hJgen : genericPoint W₀ ∉ (I.comap f₀).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change f₀ (genericPoint W₀) ∉ I.support
    rw [map_genericPoint_of_isDominant f₀]
    exact hIgen
  have hJ0 : I.comap f₀ ≠ ⊥ := fun h =>
    hJgen (by rw [h, Scheme.IdealSheafData.support_bot]; trivial)
  obtain ⟨ht, hvar⟩ := isVariety_and_isProjective_toBase_truncate_canonicalPrincipalization
    (f₀ ≫ sS) hWv hWs (I.comap f₀) hJ0
  obtain ⟨-, hmono, hiso3, -⟩ := canonicalPrincipalization_properties.{0, 0, 0}
  set B := canonicalPrincipalization _ (triples_subset_sncTriples ht) with hBdef
  obtain ⟨hWvar, hπproj, hπbir, hWsm⟩ := hvar B.length
  rw [truncate_length] at hWvar hπproj hπbir hWsm
  have hJmono : IsMonomialIdeal ((I.comap f₀).comap B.toBase) := hmono _ ht
  haveI hπiso : IsIso (B.toBase ∣_ (I.comap f₀).support.compl) :=
    (hiso3 _ ht pairwise_disjoint_componentsOf_empty).2
  -- instances on `W = B.target`
  haveI : IsIntegral B.target := hWvar.toIsIntegral
  haveI : LocallyOfFiniteType (B.toBase ≫ f₀ ≫ sS) := hWvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian B.target :=
    LocallyOfFiniteType.isLocallyNoetherian (B.toBase ≫ f₀ ≫ sS)
  haveI : QuasiCompact (B.toBase ≫ f₀ ≫ sS) := hWvar.toQuasiCompact
  haveI : CompactSpace B.target := QuasiCompact.compactSpace_of_compactSpace (B.toBase ≫ f₀ ≫ sS)
  haveI : Smooth (B.toBase ≫ f₀ ≫ sS) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWsm
  haveI : IsNormal B.target := isNormal_of_smooth_over_field (B.toBase ≫ f₀ ≫ sS)
  -- projectivity
  haveI : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace (f₀ ≫ sS)
  haveI : QuasiSeparatedSpace W₀ := quasiSeparatedSpace_of_quasiSeparated (f₀ ≫ sS)
  have hunit : ∃ (M : (Spec (.of ℂ)).Modules) (hM : Stacks.Ample.IsInvertibleModule _ M),
      letI : Stacks.Ample.IsInvertibleModule _ M := hM
      Stacks.Ample.IsAmple _ M :=
    ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  have hW₀qp : IsQuasiProjective (f₀ ≫ sS) :=
    isQuasiProjective_comp_of_exists_isAmple f₀ sS hunit
      (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f₀ hproj.isHQuasiProjective)
      hS.isQuasiProjective
  have hWqp : IsQuasiProjectiveVariety ℂ (B.toBase ≫ f₀ ≫ sS) :=
    (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hWvar, isQuasiProjective_comp_of_exists_isAmple
      B.toBase (f₀ ≫ sS) hunit (isQuasiProjective_of_isProjective hπproj) hW₀qp⟩
  haveI := hπproj.isProper
  have hπH : IsProjectiveMorphism B.toBase :=
    haveI := hWqp
    haveI := hWv
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
      (B.toBase ≫ f₀ ≫ sS) (f₀ ≫ sS) B.toBase rfl
  have hfbir : IsBirationalMorphism (B.toBase ≫ f₀) := isBirationalMorphism_comp hπbir hbir
  -- the lift to `T = Bl_I S`
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (B.toBase ≫ f₀)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (exists_divisorWithCoeffs_of_isMonomialIdeal (B.toBase ≫ f₀ ≫ sS) hWsm _
      hJmono).choose_spec.2.1
  set h := blowUpLift I (B.toBase ≫ f₀) hcart with hhdef
  have hh : h ≫ blowUpToBase I = B.toBase ≫ f₀ := blowUpLift_comp _ _ _
  haveI : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI : IsProper f₀ := isProper_of_isProjectiveMorphism f₀ hproj
  haveI : QuasiCompact (h ≫ blowUpToBase I) := by rw [hh]; infer_instance
  haveI : QuasiCompact h := QuasiCompact.of_comp h (blowUpToBase I)
  have hπr : h ≫ r = B.toBase := by
    haveI : IsSeparated f₀ := (isProper_of_isProjectiveMorphism f₀ hproj).toIsSeparated
    refine eq_of_comp_eq_of_isSeparated f₀ (by rw [Category.assoc, hr, hh]) ?_
    refine ⟨genericPoint B.target, ?_⟩
    change ((h ≫ r) ≫ f₀) (genericPoint _) ∈ biregularLocus f₀
    rw [Category.assoc, hr, hh]
    haveI : IsDominant (B.toBase ≫ f₀) := hfbir.isDominant
    rw [map_genericPoint_of_isDominant]
    exact hgenbir
  -- a `π`-exceptional divisor whose negative is relatively ample
  obtain ⟨G, hGc, hGamp, hGsupp⟩ : ∃ G : Divisor B.target, ∃ hGc : (-G).IsCartier,
      (-G).IsRelativelyAmple h hGc ∧
        ∀ P : MMP.Mori.PrimeDivisor B.target, G.coeff P ≠ 0 →
          B.toBase P.genericPoint ∈ (I.comap f₀).support := by
    haveI : IsDominant B.toBase := hπbir.isDominant
    haveI : Smooth (f₀ ≫ sS) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWs
    haveI : IsNormal W₀ := isNormal_of_smooth_over_field (f₀ ≫ sS)
    have hW₀qpv : IsQuasiProjectiveVariety ℂ (f₀ ≫ sS) :=
      (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hWv, hW₀qp⟩
    have hW₀H : Stacks.HProjective.IsHQuasiProjective (f₀ ≫ sS) :=
      ((isQuasiProjectiveVariety_iff_isHQuasiProjective ℂ _).1 hW₀qpv).2
    obtain ⟨G, hGc, hGπ, hGs⟩ := exists_isRelativelyAmple_neg_of_isIso B.toBase hWvar hWv hW₀H
      hWs hπH (I.comap f₀).support.compl ⟨_, hJgen⟩
    refine ⟨G, hGc, ?_, fun P hP => ?_⟩
    · haveI := hGc.isInvertibleModule_divisorialSheaf
      have h1 := MMP.Mori.IsRelativelyAmple.to_stacks hGπ
      rw [← hπr] at h1
      exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
        (Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp h r _ h1
          inferInstance)
    · exact of_not_not (hGs P hP)
  -- the monomial divisor of `J·𝒪_W`
  obtain ⟨DJ, hDJsnc, -, hDJprod⟩ :=
    exists_divisorWithCoeffs_of_isMonomialIdeal (B.toBase ≫ f₀ ≫ sS) hWsm _ hJmono
  have hDJmem : ∀ P : MMP.Mori.PrimeDivisor B.target,
      P ∈ DJ.support ↔ (B.toBase ≫ f₀) P.genericPoint ∈ I.support := by
    intro P
    rw [mem_support_iff_genericPoint_mem DJ hDJprod P, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap]
    rfl
  -- composition with the blow-up `T ⟶ S`
  obtain ⟨K, hK0, hKpos, n₀, hn₀⟩ : ∃ K : Divisor B.target, (∀ P, 0 ≤ K.coeff P) ∧
      (∀ P : MMP.Mori.PrimeDivisor B.target,
        0 < K.coeff P ↔ (B.toBase ≫ f₀) P.genericPoint ∈ I.support) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ hc : (-(G + n • K)).IsCartier,
        (-(G + n • K)).IsRelativelyAmple (B.toBase ≫ f₀) hc := by
    classical
    obtain ⟨A, hA, hAs, hAw⟩ :=
      exists_isWeilDivisorOfCartier_prod (B.toBase ≫ f₀ ≫ sS) hWsm DJ.support DJ
    have hKcoeff : ∀ P, (∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ) :
        Divisor B.target).coeff P = DJ P := by
      intro P
      change (∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ)) P = _
      rw [finset_sum_smul_single_one_apply]
      split_ifs with hP
      · rfl
      · rw [Finsupp.notMem_support_iff.1 hP, Nat.cast_zero]
    have hJ' : I.comap (h ≫ blowUpToBase I) = ∏ E ∈ DJ.support, E.idealSheaf ^ DJ E := by
      rw [hh, Scheme.IdealSheafData.comap_comp]
      exact hDJprod
    obtain ⟨eK⟩ := nonempty_modulePullback_exceptionalIdealModule_iso I h A hA
      (hAs.trans hJ'.symm) hAw
    haveI : QuasiCompact sS := hSv.toQuasiCompact
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
    haveI : AlgebraicGeometry.IsNoetherian S := ⟨⟩
    obtain ⟨-, hMinv, hMamp, -⟩ := MMP.Foundations.isRelativelyAmple_exceptionalIdealModule I
      (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
    haveI := hMinv
    have hKc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm
      (∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ))
    obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul_of_iso h (blowUpToBase I) _ hMamp
      hGc hGamp hKc.neg eK
    refine ⟨_, fun P => by rw [hKcoeff]; positivity, fun P => ?_, n₀, fun n hn =>
      ⟨MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm _, ?_⟩⟩
    · rw [hKcoeff, Nat.cast_pos, Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, hDJmem]
    · have := hn₀ n hn
      rw [hh] at this
      convert this using 2
      rw [neg_add, smul_neg]
  obtain ⟨E, hEred, hEsnc, hEsupp, hEcomp⟩ :=
    exists_isReducedEffective_isSNC_supp_eq_preimage (B.toBase ≫ f₀) (B.toBase ≫ f₀ ≫ sS) DJ
      hDJsnc I (by rw [Scheme.IdealSheafData.comap_comp]; exact hDJprod) hDJmem hxc hxI U hxU hIU
  -- the components of `E`
  have hEproj : ∀ P ∈ E.support,
      MMP.Mori.IsProjectiveVariety ℂ (P.idealSheaf.subschemeι ≫ B.toBase ≫ f₀ ≫ sS) ∧
        topologicalKrullDim P.idealSheaf.subscheme = 2 := by
    have hWdim : topologicalKrullDim B.target = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
      haveI : MMP.Mori.IsVariety ℂ sS := hSv
      haveI : MMP.Mori.IsVariety ℂ (B.toBase ≫ f₀ ≫ sS) := hWvar
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS
        (B.toBase ≫ f₀ ≫ sS) hfbir, hSdim]
      rfl
    intro P hP
    exact isProjectiveVariety_and_topologicalKrullDim_of_map_eq (B.toBase ≫ f₀)
      (B.toBase ≫ f₀ ≫ sS) (Category.assoc _ _ _) hWqp hWdim x hxc P ((hEcomp P).1 hP)
  -- the divisor `D`
  classical
  set N : ℕ := n₀ + ∑ P ∈ E.support, (G.coeff P).natAbs + 1 with hNdef
  obtain ⟨hNc, hNamp⟩ := hn₀ N (by omega)
  set D : Divisor B.target := (G + N • K).filter (· ∈ E.support) with hDdef
  have hDcoeff : ∀ P, D.coeff P = if P ∈ E.support then G.coeff P + N * K.coeff P else 0 := by
    intro P
    change ((G + N • K).filter (· ∈ E.support)) P = _
    split_ifs with hP
    · rw [Finsupp.filter_apply_pos _ _ hP]
      change (G + N • K) P = G P + N * K P
      rw [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
    · exact Finsupp.filter_apply_neg _ _ hP
  have hDpos : ∀ P ∈ E.support, 0 < D.coeff P := by
    intro P hP
    rw [hDcoeff, if_pos hP]
    have hK1 : 1 ≤ K.coeff P := (hKpos P).2 (((hEcomp P).1 hP) ▸ hxI)
    have hGle : (G.coeff P).natAbs ≤ ∑ Q ∈ E.support, (G.coeff Q).natAbs :=
      Finset.single_le_sum (f := fun Q => (G.coeff Q).natAbs) (fun _ _ => Nat.zero_le _) hP
    have hG1 : -((G.coeff P).natAbs : ℤ) ≤ G.coeff P := by simpa using neg_abs_le (G.coeff P)
    have hN : ((G.coeff P).natAbs : ℤ) + 1 ≤ N := by omega
    nlinarith
  have hDzero : ∀ P ∉ E.support, D.coeff P = 0 := fun P hP => by
    rw [hDcoeff, if_neg hP]
  have hDc : (-D).IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm _
  have hDamp : (-D).IsAmpleOver (B.toBase ≫ f₀) hDc U := by
    refine hNamp.isAmpleOver_of_coeff_eq hDc U fun P hP => ?_
    have hPU : (B.toBase ≫ f₀) P.genericPoint ∈ U := by
      obtain ⟨w, hwP, hwU⟩ := hP
      exact ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support P hwP).map
        (B.toBase ≫ f₀).base.hom.continuous).mem_open U.isOpen hwU
    rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_neg, hDcoeff]
    split_ifs with hPE
    · change -(G.coeff P + N * K.coeff P) = -((G + N • K) P)
      rw [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
      rfl
    · have hx' : (B.toBase ≫ f₀) P.genericPoint ≠ x := fun h => hPE ((hEcomp P).2 h)
      have hG0 : G.coeff P = 0 := by
        by_contra hG
        have h1 := hGsupp P hG
        rw [Scheme.IdealSheafData.support_comap] at h1
        exact hx' (hIU _ hPU h1)
      have hK0' : K.coeff P = 0 := by
        by_contra hK
        exact hx' (hIU _ hPU ((hKpos P).1 (lt_of_le_of_ne (hK0 P) (Ne.symm hK))))
      change (0 : ℤ) = -((G + N • K) P)
      rw [Finsupp.add_apply, Finsupp.smul_apply]
      change (0 : ℤ) = -(G.coeff P + N • K.coeff P)
      rw [hG0, hK0', smul_zero, add_zero, neg_zero]
  -- `f` is an isomorphism over `U ∖ {x}`, which `I` misses
  have hbir' : (U : Set S) \ {x} ⊆ biregularLocus (B.toBase ≫ f₀) := by
    let V : S.Opens := U ⊓ ⟨{x}ᶜ, hxc.isOpen_compl⟩
    have hV : V ≤ biregularLocus f₀ := fun y hy => hU ⟨hy.1, hy.2⟩
    have hVI : f₀ ⁻¹ᵁ V ≤ biregularLocus B.toBase := by
      refine le_trans (fun w hw => ?_) (le_biregularLocus hπiso)
      change w ∉ (I.comap f₀).support
      rw [Scheme.IdealSheafData.support_comap]
      exact fun h => hw.2 (hIU _ hw.1 h)
    exact fun y hy => le_biregularLocus_comp hV hVI ⟨hy.1, hy.2⟩
  exact ⟨B.target, inferInstance, inferInstance, inferInstance, B.toBase,
    ⟨hSv, hWvar, hWsm, hπH.comp hproj, hfbir⟩, hWqp, hbir', E, hEred, hEsnc, hEsupp, hEproj,
    D, hDpos, hDzero, hDc, hDamp⟩

/-- **An antiample snc fibre over an isolated threefold singularity.** Let `f₀ : W₀ ⟶ S` be a
projective resolution of a normal quasi-projective complex threefold, `x ∈ S` and `U ∋ x` an open
with `Sing(S) ∩ U = {x}` over whose complement of `x` the map `f₀` is an isomorphism. There is a
morphism `r : W ⟶ W₀` such that `f = r ≫ f₀` is a projective resolution of `S` with `W`
quasi-projective, the reduced fibre `f⁻¹(x)` is the support of a reduced snc divisor `E` whose
components are smooth projective surfaces, and some `D = ∑ mᵢ Eᵢ` with all `mᵢ > 0` has `-D`
Cartier and ample over `U`. -/
@[mmp "lem_mmp_conductor_threefold_antiample_fibre"]
public theorem exists_isResolution_comp_isSNC_isAmpleOver_neg
    {S W₀ : Scheme.{0}} [IsNormal S] {sS : S ⟶ Spec (.of ℂ)}
    (hS : IsQuasiProjectiveVariety ℂ sS) (hSdim : topologicalKrullDim S = 3)
    {f₀ : W₀ ⟶ S} (hf₀ : MMP.Intersection.IsResolution sS f₀)
    (x : S) (U : S.Opens) (hxU : x ∈ U)
    (hx : (singularLocus sS : Set S) ∩ U = {x})
    (hU : (U : Set S) \ {x} ⊆ biregularLocus f₀) :
    ∃ (W : Scheme.{0}) (_ : IsLocallyNoetherian W) (_ : IsNormal W) (_ : CompactSpace W)
      (r : W ⟶ W₀),
      MMP.Intersection.IsResolution sS (r ≫ f₀) ∧
      IsQuasiProjectiveVariety ℂ (r ≫ f₀ ≫ sS) ∧
      ∃ E : Divisor W, MMP.Intersection.IsReducedEffective E ∧
        DivisorWithCoeffs.IsSNC (r ≫ f₀ ≫ sS) E ∧
        (E.supp : Set W) = (r ≫ f₀).base ⁻¹' {x} ∧
        (∀ P ∈ E.support,
          MMP.Mori.IsProjectiveVariety ℂ (P.idealSheaf.subschemeι ≫ r ≫ f₀ ≫ sS) ∧
          topologicalKrullDim P.idealSheaf.subscheme = 2) ∧
        ∃ D : Divisor W, (∀ P ∈ E.support, 0 < D.coeff P) ∧ (∀ P ∉ E.support, D.coeff P = 0) ∧
          ∃ h : (-D).IsCartier, (-D).IsAmpleOver (r ≫ f₀) h U := by
  obtain ⟨W, h₁, h₂, h₃, r, hres, hqp, -, hrest⟩ :=
    exists_isResolution_comp_isSNC_isAmpleOver_neg_and_subset_biregularLocus
      hS hSdim hf₀ x U hxU hx hU
  exact ⟨W, h₁, h₂, h₃, r, hres, hqp, hrest⟩

end MMP.Threefold
