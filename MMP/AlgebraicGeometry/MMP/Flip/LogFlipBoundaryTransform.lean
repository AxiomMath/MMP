module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve

/-!
# Reduced boundaries and discrepancies across log flips

In a sequence of log flips, the contraction `φ_i : X_i ⟶ Z_i` and its flip `φ_i⁺` agree off the
exceptional loci (`MMP.Flips.SequenceOfLogFlips.exists_iso_compl_exceptionalLocus_flipMap`), so
`θ_{i*}` is a bijection between the components of `⌊B_i⌋` and of `⌊B_{i+1}⌋`, each component
and its transform having the same surface as image in `Z_i`.
If moreover `X_i` is `ℚ`-factorial and a `ℚ`-divisor `G` satisfies
`G · C = μ (K_{X_i} + B_i) · C` on a flipping curve `C`, then
`m (θ_{i*} G - μ (K_{X_{i+1}} + B_{i+1})) ∼ φ_i⁺^* M` for some `m > 0` and some Cartier divisor
`M` on `Z_i`: since `ρ(X_i/Z_i) = 1`, `G - μ (K_{X_i} + B_i)` is numerically trivial over `Z_i`
and descends, and `θ_i`, an isomorphism in codimension one over `Z_i`, carries principal divisors
to principal divisors, `φ_i^* M` to `φ_i⁺^* M` and `θ_{i*} K_{X_i}` to a canonical divisor.

Finally, if `W ⊆ X` is an irreducible closed subset of codimension two of a normal variety, with
`𝒪_{X,η_W}` regular, and `D ≥ 0` is a `ℚ`-divisor with `K_X + D` `ℚ`-Cartier and
`mult_W(D) ≤ 1`, every divisor `E` over `X` with centre `W` has `a(E, X, D) ≥ 1 - mult_W(D)`.
Restricting to a neighbourhood of `η_W` on which `X` and `W` are smooth, this is proved by
induction on `a(E, X, 0) ∈ ℕ`: either `E` is the exceptional divisor of `Bl_W X`, where the
blow-up formula gives the bound, or the boundary on `Bl_W X` is `π⁻¹_* D - N'` with `N' ≥ 0`, the
centre of `E` there is again of codimension two with no larger multiplicity, and `a(E, ·, 0)`
drops by the order of `E` along the exceptional divisor.

## Main results

* `MMP.Flips.ker_subschemeι_comp`: the scheme-theoretic image of a prime divisor `Γ` is the
  reduced closure of the image of its generic point.
* `MMP.Flips.isBirationalMorphism_toImage_subschemeι_comp`: a proper morphism which is an
  isomorphism over a neighbourhood of `f(η_Γ)` is birational from `Γ` onto its image.
* `MMP.Flips.SequenceOfLogFlips.boundaryComponentEquiv`: `Γ ↦ θ_{i*}Γ` on the components of
  `⌊B_i⌋`; `MMP.Flips.SequenceOfLogFlips.boundaryComponentEquiv_spec`: its properties.
* `MMP.Flips.SequenceOfLogFlips.exists_smul_transformDivisor_sub_linearEquiv_pullback`: if
  `G · C = μ (K_{X_i} + B_i) · C` on a flipping curve, then
  `m (θ_{i*} G - μ (K_{X_{i+1}} + B_{i+1})) ∼ φ_i⁺^* M` for some `m > 0` and Cartier `M`.
* `MMP.Flips.IsDiscrepancy.one_sub_le_of_isRegularLocalRing`: `a(E, X, D) ≥ 1 - mult_W(D)`.

## Implementation notes

The components of `⌊B_i⌋` are the prime divisors in the support of
`DivisorWithCoeffs.roundDown B_i`; the image `φ_i(Γ)` is the scheme-theoretic image, and the
equality `φ_i(Γ) = φ_i⁺(θ_{i*}Γ)` is the equality of the kernels `Scheme.Hom.ker`.

A linear equivalence `D ∼ φ_i⁺^* M` of a Weil divisor with the pull-back of a Cartier divisor is
recorded, as in `MMP.Flips.IsExtremalRayContraction`, as an isomorphism
`𝒪_{X_{i+1}}(D) ≅ φ_i⁺^* 𝒪_{Z_i}(M)`.

The discrepancy `a(E, X, D)` of `IsDiscrepancy.one_sub_le_of_isRegularLocalRing` is the general
one, `MMP.Flips.IsDiscrepancy`; it agrees with the Kollár–Mori discrepancy
`MMP.Mori.IsDiscrepancy` on any model of the valuation, since both are the log discrepancy minus
one, and the induction runs on the latter.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (4.13), 4.15,
  7.1, 7.3–7.7, Exercise 4.9.1
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace MMP.Flips

open MMP.Mori

/-! ### The reduced boundaries of a log flip have the same images -/

/-- The scheme-theoretic image of a prime divisor `Γ` under `f` is the reduced closure of the
image of the generic point of `Γ`. -/
theorem ker_subschemeι_comp {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (Γ : AlgebraicGeometry.PrimeDivisor Y) :
    (Γ.idealSheaf.subschemeι ≫ f).ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {f Γ.genericPoint}) := by
  have := Γ.integral
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ← MMP.Positivity.vanishingIdeal_support_of_isReduced Γ.idealSheaf,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  rw [Closeds.coe_closure, Closeds.coe_closure]
  change closure (f '' Γ.support) = _
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, closure_image_closure f.continuous,
    Set.image_singleton]

/-- If `f` is proper and an isomorphism over an open `W` containing the image of the generic
point of a prime divisor `Γ`, then `f|_Γ` is birational onto its scheme-theoretic image. -/
theorem isBirationalMorphism_toImage_subschemeι_comp {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsProper f]
    (W : Z.Opens) [IsIso (f ∣_ W)] (Γ : AlgebraicGeometry.PrimeDivisor Y)
    (hΓ : f Γ.genericPoint ∈ W) :
    IsBirationalMorphism (Γ.idealSheaf.subschemeι ≫ f).toImage := by
  have := Γ.integral
  set h := Γ.idealSheaf.subschemeι ≫ f with hh
  let V := h.imageι ⁻¹ᵁ W
  have hgen : h.toImage (genericPoint Γ.idealSheaf.subscheme) ∈ V := by
    show h.imageι (h.toImage _) ∈ W
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
    exact hΓ
  refine isBirationalMorphism_of_isIso_resLE h.toImage (h.toImage ⁻¹ᵁ V) V ⟨_, hgen⟩ ⟨_, hgen⟩
    le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  haveI : IsClosedImmersion (f ∣_ W) := inferInstance
  haveI : IsClosedImmersion (h ∣_ W) := by
    rw [hh, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ (IsZariskiLocalAtTarget.restrict
      (inferInstanceAs (IsClosedImmersion Γ.idealSheaf.subschemeι)) _) ‹_›
  have h1 : IsClosedImmersion ((h.toImage ≫ h.imageι) ∣_ W) := by
    rw [Scheme.Hom.toImage_imageι]; infer_instance
  rw [morphismRestrict_comp] at h1
  haveI : IsClosedImmersion (h.toImage ∣_ V) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (h.imageι ∣_ W) _ h1
  haveI : IsProper (h.toImage ≫ h.imageι) := by
    rw [Scheme.Hom.toImage_imageι]; infer_instance
  haveI : IsProper h.toImage := IsProper.of_comp h.toImage h.imageι
  haveI : Surjective h.toImage := by
    refine ⟨fun x ↦ ?_⟩
    have hr : Set.range h.toImage = Set.univ := by
      rw [← h.toImage.isClosedMap.isClosed_range.closure_eq]
      exact h.toImage.denseRange.closure_range
    exact hr.ge (Set.mem_univ x)
  haveI : Surjective (h.toImage ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
  exact isIso_of_isClosedImmersion_of_surjective _

/-- If `f` is an isomorphism over an open `W` of a threefold `Z` containing the image of the
generic point of a prime divisor `Γ`, the scheme-theoretic image of `Γ` is a surface. -/
private theorem topologicalKrullDim_image_eq_two {k : Type u} [Field k] {Y Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
    (W : Z.Opens) [IsIso (f ∣_ W)] (Γ : AlgebraicGeometry.PrimeDivisor Y)
    (hΓ : f Γ.genericPoint ∈ W) (hZ : topologicalKrullDim Z = 3) :
    topologicalKrullDim (Γ.idealSheaf.subschemeι ≫ f).image = 2 := by
  set h := Γ.idealSheaf.subschemeι ≫ f
  have hr : Set.range h.imageι = closure {f Γ.genericPoint} := by
    change Set.range h.ker.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, ker_subschemeι_comp,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hdim : topologicalKrullDim h.image =
      topologicalKrullDim (closure {f Γ.genericPoint} : Set Z) := by
    rw [← hr]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (h.imageι.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph
  have hη : Γ.genericPoint ∈ f ⁻¹ᵁ W := hΓ
  have e1 : (f ∣_ W) ⟨Γ.genericPoint, hη⟩ = ⟨f Γ.genericPoint, hΓ⟩ :=
    Subtype.ext (morphismRestrict_base_coe f W ⟨Γ.genericPoint, hη⟩)
  have hcoh : Order.coheight (f Γ.genericPoint) = 1 := by
    have c1 := coheight_eq_of_isOpenImmersion (x := (⟨f Γ.genericPoint, hΓ⟩ : W.toScheme)) W.ι
    have c2 := coheight_eq_of_isOpenImmersion
      (x := (⟨Γ.genericPoint, hη⟩ : (f ⁻¹ᵁ W).toScheme)) (f ∣_ W)
    have c3 := coheight_eq_of_isOpenImmersion
      (x := (⟨Γ.genericPoint, hη⟩ : (f ⁻¹ᵁ W).toScheme)) (f ⁻¹ᵁ W).ι
    rw [e1] at c2
    exact c1.trans (c2.trans (c3.symm.trans Γ.coheight_genericPoint))
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ (f Γ.genericPoint)
  rw [hcoh, hZ] at hsum
  rw [hdim]
  generalize topologicalKrullDim (closure {f Γ.genericPoint} : Set Z) = d at hsum ⊢
  induction d using WithBot.recBotCoe with
  | bot => simp at hsum
  | coe m =>
    have h3 : m + 1 = 3 := WithBot.coe_injective (by push_cast; exact hsum)
    induction m using ENat.recTopCoe with
    | top => simp at h3
    | coe m =>
      have : m = 2 := by norm_cast at h3; omega
      subst this; rfl

section RoundDownSupport

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]
  {X Y : Scheme.{u}} {ψ : AlgebraicGeometry.PrimeDivisor X → AlgebraicGeometry.PrimeDivisor Y}

/-- Pushing forward along an injective `ψ` commutes with rounding down at `ψ D`. -/
private theorem roundDown_mapDomain_apply (hψ : Function.Injective ψ) (B : DivisorWithCoeffs R X)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    DivisorWithCoeffs.roundDown (Finsupp.mapDomain ψ B) (ψ D) =
      DivisorWithCoeffs.roundDown B D := by
  simp only [DivisorWithCoeffs.roundDown, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply,
    Finsupp.mapDomain_apply_of_injective hψ]

/-- An injective `ψ` carries a component of `⌊B⌋` to a component of `⌊ψ_* B⌋`. -/
theorem map_mem_support_roundDown_mapDomain (hψ : Function.Injective ψ)
    {B : DivisorWithCoeffs R X} {B' : DivisorWithCoeffs R Y} (hB : B' = Finsupp.mapDomain ψ B)
    {Γ : AlgebraicGeometry.PrimeDivisor X} (hΓ : Γ ∈ (DivisorWithCoeffs.roundDown B).support) :
    ψ Γ ∈ (DivisorWithCoeffs.roundDown B').support := by
  subst hB
  rw [Finsupp.mem_support_iff, roundDown_mapDomain_apply hψ]
  exact Finsupp.mem_support_iff.mp hΓ

/-- An injective `ψ` restricts to a bijection from the components of `⌊B⌋` to those of
`⌊ψ_* B⌋`. -/
theorem bijective_restrict_support_roundDown_mapDomain (hψ : Function.Injective ψ)
    (B : DivisorWithCoeffs R X) {B' : DivisorWithCoeffs R Y} (hB : B' = Finsupp.mapDomain ψ B) :
    Function.Bijective (fun Γ : (DivisorWithCoeffs.roundDown B).support ↦
      (⟨ψ Γ.1, map_mem_support_roundDown_mapDomain hψ hB Γ.2⟩ :
        (DivisorWithCoeffs.roundDown B').support)) := by
  refine ⟨fun a b hab ↦ Subtype.ext (hψ (congrArg Subtype.val hab)), fun E ↦ ?_⟩
  subst hB
  have hE := Finsupp.mem_support_iff.mp E.2
  by_cases hr : E.1 ∈ Set.range ψ
  · obtain ⟨D, hD⟩ := hr
    exact ⟨⟨D, Finsupp.mem_support_iff.mpr (by rw [← roundDown_mapDomain_apply hψ, hD]; exact hE)⟩,
      Subtype.ext hD⟩
  · refine absurd ?_ hE
    simp only [DivisorWithCoeffs.roundDown, DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply,
      Finsupp.mapDomain_of_notMem_range _ _ hr, Int.floor_zero]

/-- An injective map `ψ` of prime divisors, as a bijection from the components of `⌊B⌋` to those
of `⌊B'⌋` when `B' = ψ_* B`. -/
noncomputable def roundDownSupportEquivOfMapDomain (hψ : Function.Injective ψ)
    (B : DivisorWithCoeffs R X) {B' : DivisorWithCoeffs R Y} (hB : B' = Finsupp.mapDomain ψ B) :
    (DivisorWithCoeffs.roundDown B).support ≃ (DivisorWithCoeffs.roundDown B').support :=
  Equiv.ofBijective _ (bijective_restrict_support_roundDown_mapDomain hψ B hB)

/-- The bijection `roundDownSupportEquivOfMapDomain hψ B hB` sends a component `Γ` of `⌊B⌋` to
`ψ Γ`. -/
@[simp]
theorem coe_roundDownSupportEquivOfMapDomain_apply (hψ : Function.Injective ψ)
    (B : DivisorWithCoeffs R X) {B' : DivisorWithCoeffs R Y} (hB : B' = Finsupp.mapDomain ψ B)
    (Γ : (DivisorWithCoeffs.roundDown B).support) :
    (roundDownSupportEquivOfMapDomain hψ B hB Γ).1 = ψ Γ.1 :=
  rfl

end RoundDownSupport

section BoundaryComponents

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X}
  {B : QDivisor X}

/-- In a sequence of log flips, the transform under `θ_i` is defined on every prime divisor of
`X_i`, injective, and carries generic points to points with the same image in `Z_i`. -/
private theorem SequenceOfLogFlips.exists_injective_transformPrimeDivisor_flipMap
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    ∃ ψ : AlgebraicGeometry.PrimeDivisor (S.model i).1 →
        AlgebraicGeometry.PrimeDivisor (S.model (i + 1)).1,
      Function.Injective ψ ∧ ∀ D, RationalMap.transformPrimeDivisor (S.flipMap i) D = some (ψ D) ∧
        S.flip i (ψ D).genericPoint = S.contraction i D.genericPoint := by
  obtain ⟨hV, hpre, -, hd, e, he, hrep⟩ := S.exists_iso_compl_exceptionalLocus_flipMap i hi
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := (S.isNormalVariety_model i hi').1.toIsIntegral
  have := (S.isNormalVariety_model (i + 1) hi).1.toIsSeparated
  have := isSeparated_terminal (S.model (i + 1)).2.1
  have hsmall := S.isSmall i hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hsmall' := (S.isFlip i hi).isSmall
  have := hsmall.isProper
  have := hsmall'.isProper
  have := hsmall.isVariety_target.toIsIntegral
  have := hsmall.isVariety_target.toLocallyOfFiniteType
  obtain ⟨V₀, W₀, hV₀, -, h₀, hiso⟩ := hsmall.exists_isIso
  let g' := Scheme.PartialMap.mk (S.contraction i ⁻¹ᵁ ⟨_, hV⟩) hd
    (e.hom ≫ (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι)
  have : IsOpenImmersion g'.hom := inferInstanceAs (IsOpenImmersion (e.hom ≫ _))
  have hdom (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) : D.genericPoint ∈ g'.domain :=
    (Set.ext_iff.mp hpre D.genericPoint).mpr fun ⟨_, _, _, hdim⟩ ↦ by
      have := subsingleton_preimage_genericPoint _ V₀ W₀ hV₀ h₀ hiso D
      exact hdim.not_ge (topologicalKrullDim_zero_of_discreteTopology _)
  obtain ⟨ψ, hψinj, hψ⟩ := exists_injective_transformPrimeDivisor g' hrep hdom
  have key : e.hom ≫ (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι ≫ S.flip i =
      (S.contraction i ⁻¹ᵁ ⟨_, hV⟩).ι ≫ S.contraction i := by
    rw [← morphismRestrict_ι, ← Category.assoc, he, morphismRestrict_ι]
  refine ⟨ψ, hψinj, fun D ↦ ⟨(hψ D).1, ?_⟩⟩
  rw [(hψ D).2]
  exact congrArg (fun g : (S.contraction i ⁻¹ᵁ ⟨_, hV⟩).toScheme ⟶ S.base i ↦
    g ⟨D.genericPoint, hdom D⟩) key

/-- The birational transform `θ_{i*} D` of a prime divisor `D` of `X_i` under the flip map
`θ_i = S.flipMap i`, the value of `RationalMap.transformPrimeDivisor`, which is defined on every
prime divisor of `X_i`. -/
noncomputable def SequenceOfLogFlips.flipMapTransformPrimeDivisor (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) :
    AlgebraicGeometry.PrimeDivisor (S.model (i + 1)).1 :=
  (RationalMap.transformPrimeDivisor (S.flipMap i) D).get <| by
    obtain ⟨ψ, -, hψ⟩ := S.exists_injective_transformPrimeDivisor_flipMap i hi
    rw [(hψ D).1]
    rfl

/-- The birational transform of a prime divisor `D` of `X_i` under `θ_i` is defined and equals
`θ_{i*} D`. -/
theorem SequenceOfLogFlips.transformPrimeDivisor_flipMap_eq_some (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) :
    RationalMap.transformPrimeDivisor (S.flipMap i) D =
      some (S.flipMapTransformPrimeDivisor i hi D) :=
  (Option.some_get _).symm

/-- `θ_{i*}` is injective on prime divisors. -/
theorem SequenceOfLogFlips.flipMapTransformPrimeDivisor_injective (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    Function.Injective (S.flipMapTransformPrimeDivisor i hi) := by
  obtain ⟨ψ, hψinj, hψ⟩ := S.exists_injective_transformPrimeDivisor_flipMap i hi
  have h (D) : S.flipMapTransformPrimeDivisor i hi D = ψ D :=
    Option.some_injective _ ((S.transformPrimeDivisor_flipMap_eq_some i hi D).symm.trans (hψ D).1)
  intro D₁ D₂ h₁₂
  rw [h, h] at h₁₂
  exact hψinj h₁₂

/-- `φ_i⁺` maps the generic point of `θ_{i*} D` to the image under `φ_i` of the generic point
of `D`. -/
theorem SequenceOfLogFlips.flip_genericPoint_flipMapTransformPrimeDivisor
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) :
    S.flip i (S.flipMapTransformPrimeDivisor i hi D).genericPoint =
      S.contraction i D.genericPoint := by
  obtain ⟨ψ, -, hψ⟩ := S.exists_injective_transformPrimeDivisor_flipMap i hi
  have h : S.flipMapTransformPrimeDivisor i hi D = ψ D :=
    Option.some_injective _ ((S.transformPrimeDivisor_flipMap_eq_some i hi D).symm.trans (hψ D).1)
  rw [h]
  exact (hψ D).2

/-- The boundary `B_{i+1}` is the push-forward of `B_i` along `θ_{i*}`. -/
theorem SequenceOfLogFlips.boundary_succ_eq_mapDomain_flipMapTransformPrimeDivisor
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    (S.model (i + 1)).2.2.2 = Finsupp.mapDomain (S.flipMapTransformPrimeDivisor i hi)
      (S.model i).2.2.2 :=
  (S.transform_eq i hi).trans
    (mapPrimeDivisors_eq_mapDomain (S.transformPrimeDivisor_flipMap_eq_some i hi) _)

/-- `Γ ↦ θ_{i*} Γ`, as a bijection from the components of `⌊B_i⌋` to those of `⌊B_{i+1}⌋`. -/
noncomputable def SequenceOfLogFlips.boundaryComponentEquiv (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    (DivisorWithCoeffs.roundDown (S.model i).2.2.2).support ≃
      (DivisorWithCoeffs.roundDown (S.model (i + 1)).2.2.2).support :=
  roundDownSupportEquivOfMapDomain (S.flipMapTransformPrimeDivisor_injective i hi)
    (S.model i).2.2.2 (S.boundary_succ_eq_mapDomain_flipMapTransformPrimeDivisor i hi)

/-- The bijection `S.boundaryComponentEquiv i hi` sends a component `Γ` of `⌊B_i⌋` to
`θ_{i*} Γ`. -/
@[simp]
theorem SequenceOfLogFlips.coe_boundaryComponentEquiv_apply (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (Γ : (DivisorWithCoeffs.roundDown (S.model i).2.2.2).support) :
    (S.boundaryComponentEquiv i hi Γ).1 = S.flipMapTransformPrimeDivisor i hi Γ.1 :=
  rfl

/-- The bijection `S.boundaryComponentEquiv i hi` is the birational transform under `θ_i`. -/
theorem SequenceOfLogFlips.transformPrimeDivisor_eq_boundaryComponentEquiv
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (Γ : (DivisorWithCoeffs.roundDown (S.model i).2.2.2).support) :
    RationalMap.transformPrimeDivisor (S.flipMap i) Γ.1 =
      some (S.boundaryComponentEquiv i hi Γ).1 :=
  S.transformPrimeDivisor_flipMap_eq_some i hi Γ.1

/-- A component `Γ` of `⌊B_i⌋` and its transform `θ_{i*}Γ` have the same scheme-theoretic image
in `Z_i`, under `φ_i` and `φ_i⁺` respectively. -/
theorem SequenceOfLogFlips.ker_contraction_eq_ker_flip_boundaryComponentEquiv
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (Γ : (DivisorWithCoeffs.roundDown (S.model i).2.2.2).support) :
    (Γ.1.idealSheaf.subschemeι ≫ S.contraction i).ker =
      ((S.boundaryComponentEquiv i hi Γ).1.idealSheaf.subschemeι ≫ S.flip i).ker := by
  rw [coe_boundaryComponentEquiv_apply, ker_subschemeι_comp, ker_subschemeι_comp,
    flip_genericPoint_flipMapTransformPrimeDivisor]

/-- The scheme-theoretic image under `φ_i` of a prime divisor of `X_i` is a surface. -/
theorem SequenceOfLogFlips.topologicalKrullDim_image_contraction_eq_two
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) :
    topologicalKrullDim (D.idealSheaf.subschemeι ≫ S.contraction i).image = 2 := by
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := (S.isNormalVariety_model i hi').1.toIsIntegral
  have := (S.isNormalVariety_model (i + 1) hi).1.toIsSeparated
  have := isSeparated_terminal (S.model (i + 1)).2.1
  have hsmall := S.isSmall i hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hsmall' := (S.isFlip i hi).isSmall
  have := hsmall.isProper
  have := hsmall'.isProper
  have := hsmall.isVariety_target.toIsIntegral
  have := hsmall.isVariety_target.toLocallyOfFiniteType
  obtain ⟨W, hWiso, hW, -⟩ := exists_isIso_morphismRestrict_of_isSmall hsmall
  exact topologicalKrullDim_image_eq_two (S.baseStr i) (S.contraction i) W D (hW D)
    (hsmall.dim_eq.symm.trans (S.dim_model i hi'))

/-- `φ_i` restricted to a prime divisor of `X_i` is birational onto its scheme-theoretic image. -/
theorem SequenceOfLogFlips.isBirationalMorphism_toImage_contraction
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) :
    IsBirationalMorphism (D.idealSheaf.subschemeι ≫ S.contraction i).toImage := by
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := (S.isNormalVariety_model i hi').1.toIsIntegral
  have := (S.isNormalVariety_model (i + 1) hi).1.toIsSeparated
  have := isSeparated_terminal (S.model (i + 1)).2.1
  have hsmall := S.isSmall i hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hsmall' := (S.isFlip i hi).isSmall
  have := hsmall.isProper
  have := hsmall'.isProper
  have := hsmall.isVariety_target.toIsIntegral
  have := hsmall.isVariety_target.toLocallyOfFiniteType
  obtain ⟨W, hWiso, hW, -⟩ := exists_isIso_morphismRestrict_of_isSmall hsmall
  exact isBirationalMorphism_toImage_subschemeι_comp (S.contraction i) W D (hW D)

/-- `φ_i⁺` restricted to a prime divisor of `X_{i+1}` is birational onto its scheme-theoretic
image. -/
theorem SequenceOfLogFlips.isBirationalMorphism_toImage_flip
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (D : AlgebraicGeometry.PrimeDivisor (S.model (i + 1)).1) :
    IsBirationalMorphism (D.idealSheaf.subschemeι ≫ S.flip i).toImage := by
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := (S.isNormalVariety_model i hi').1.toIsIntegral
  have := (S.isNormalVariety_model (i + 1) hi).1.toIsSeparated
  have := isSeparated_terminal (S.model (i + 1)).2.1
  have hsmall := S.isSmall i hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hsmall' := (S.isFlip i hi).isSmall
  have := hsmall.isProper
  have := hsmall'.isProper
  have := hsmall.isVariety_target.toIsIntegral
  have := hsmall.isVariety_target.toLocallyOfFiniteType
  obtain ⟨W', hWiso', hW', -⟩ := exists_isIso_morphismRestrict_of_isSmall hsmall'
  exact isBirationalMorphism_toImage_subschemeι_comp (S.flip i) W' D (hW' D)

/-- In a sequence of log flips `S`, for every `i` with `i + 1 < L`, the bijection
`e = S.boundaryComponentEquiv i hi` from the components of `⌊B_i⌋` to those of `⌊B_{i+1}⌋` is
the birational transform under `θ_i = S.flipMap i`, and for every component `Γ` the restrictions
of `φ_i = S.contraction i` to `Γ` and of `φ_i⁺ = S.flip i` to `e Γ` have the same
scheme-theoretic image, a surface in `Z_i`, onto which both are birational morphisms. -/
@[mmp "lem_fa7_boundary_images_agree"]
public theorem SequenceOfLogFlips.boundaryComponentEquiv_spec (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (Γ : (DivisorWithCoeffs.roundDown (S.model i).2.2.2).support) :
    RationalMap.transformPrimeDivisor (S.flipMap i) Γ.1 =
        some (S.boundaryComponentEquiv i hi Γ).1 ∧
      (Γ.1.idealSheaf.subschemeι ≫ S.contraction i).ker =
        ((S.boundaryComponentEquiv i hi Γ).1.idealSheaf.subschemeι ≫ S.flip i).ker ∧
      topologicalKrullDim (Γ.1.idealSheaf.subschemeι ≫ S.contraction i).image = 2 ∧
      IsBirationalMorphism (Γ.1.idealSheaf.subschemeι ≫ S.contraction i).toImage ∧
      IsBirationalMorphism
        ((S.boundaryComponentEquiv i hi Γ).1.idealSheaf.subschemeι ≫ S.flip i).toImage :=
  ⟨S.transformPrimeDivisor_eq_boundaryComponentEquiv i hi Γ,
    S.ker_contraction_eq_ker_flip_boundaryComponentEquiv i hi Γ,
    S.topologicalKrullDim_image_contraction_eq_two i hi Γ.1,
    S.isBirationalMorphism_toImage_contraction i hi Γ.1,
    S.isBirationalMorphism_toImage_flip i hi _⟩

end BoundaryComponents

/-! ### Discrepancies over a regular codimension-two point -/

section DiscrepancyBound

open scoped WithZero

/-! For an irreducible closed subset `Z` of the scheme `Y` in context: its reduced ideal sheaf
`𝓘[Z]`, the blow-up `Bl[Z]` along it and the blow-down `Blπ[Z]`. -/

local macro "𝓘[" Z:term "]" : term =>
  `(Scheme.IdealSheafData.vanishingIdeal
    (⟨$Z, ($Z).isClosed⟩ : TopologicalSpace.Closeds $(Lean.mkIdent `Y)))
local notation "Bl[" Z "]" => Stacks.Blowup.blowUp 𝓘[Z]
local notation "Blπ[" Z "]" => Stacks.Blowup.blowUpToBase 𝓘[Z]

/-- An FA discrepancy `a(F, D_X)` is computed on a proper divisor `(Y, f, E)` over `X` with
`ord_E = F`, and `1 + a` is the log discrepancy of that divisor. -/
private theorem exists_isLogDiscrepancy {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X}
    {D_X : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : IsDiscrepancy sX n K D_X F a) :
    ∃ E : ProperDivisorOver k sX, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sX n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, rfl, hX, -, hω0, hLc, hL, L', hLpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r, L,
    L', hLc, fun Γ => ?_, hLpb, by ring⟩
  have := congrArg (fun G : RDivisor X => G.coeff Γ) hL
  simp only [coeff_sum_smul_toRDivisor] at this
  rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]

/-- The image of the generic point of `E` is the generic point of the center of `E`. -/
private theorem map_genericPoint_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX)
    {W : IrreducibleCloseds X} (hE : E.center = W) :
    E.f E.E.genericPoint = W.isIrreducible.genericPoint := by
  have h1 : (W : Set X) = closure {E.f E.E.genericPoint} := by
    rw [← hE, ← E.toDivisorOver.center_eq_closure_genericPoint, DivisorOver.coe_center,
      ProperDivisorOver.coe_center, E.isClosed_image_support.closure_eq]
  exact ((isGenericPoint_def.mpr h1.symm).eq
    (W.isIrreducible.isGenericPoint_genericPoint W.isClosed))

/-- A *stage* of the blow-up induction, with bound `μ`, discrepancy `q` and measure `m`: a regular
variety `Y` with canonical divisor `K`, a boundary `P - N` with `P, N ≥ 0`, a codimension-two
irreducible closed subset `Z` with `mult_Z(P) ≤ μ`, and a divisor `E` over `Y` with centre `Z`,
such that `q = a(E, Y, P - N)` and `m = a(E, Y, 0)`. -/
private def Stage (k : Type u) [Field k] (μ q : ℚ) (m : ℕ) : Prop :=
  ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (_ : IsNormalVariety k sY)
    (_ : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (n : ℕ) (K : Divisor Y) (P N : QDivisor Y) (_ : 0 ≤ P) (_ : 0 ≤ N)
    (Z : IrreducibleCloseds Y) (_ : codimension Z = 2)
    (_ : (P.sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ μ)
    (E : DivisorOver k sY) (_ : E.f E.E.genericPoint = Z.isIrreducible.genericPoint),
    MMP.Mori.IsDiscrepancy sY n K (P - N) E q ∧ MMP.Mori.IsDiscrepancy sY n K 0 E m

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- Over a perfect field, a scheme all of whose local rings are regular is smooth. -/
private theorem isSmoothScheme_of_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme sY :=
  eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing sY y).mpr (hYreg y)

/-- At a point with regular local ring of a scheme locally of finite type over a perfect field,
the local ring is formally smooth and essentially of finite type over `k`. -/
private theorem formallySmooth_stalk {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (x : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    letI := stalkAlgebra sX x
    Algebra.FormallySmooth k (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let := stalkAlgebra sX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x' : U := ⟨x, hxU⟩
  let := sectionAlgebra sX U
  have := finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have := isScalarTower_section_stalk sX U x'
  have := hU'.isLocalization_stalk x'
  set q := (hU'.primeIdealOf x').asIdeal
  have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
  have hs : Algebra.IsSmoothAt k q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q (X.presheaf.stalk x)).mpr hreg
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) := .of_isLocalization _ q.primeCompl
  refine ⟨?_, .comp k Γ(X, U) (X.presheaf.stalk x)⟩
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)).restrictScalars k)

/-- **A generator of the top forms at a regular point.** -/
private theorem exists_topForms_generator_stalk {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    ∃ σ : ⋀[X.presheaf.stalk x]^d Ω[X.presheaf.stalk x⁄k],
      Submodule.span (X.presheaf.stalk x) {σ} = ⊤ ∧
      topFormsMap k (X.presheaf.stalk x) X.functionField d σ ≠ 0 := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  obtain ⟨_, _⟩ := formallySmooth_stalk (sX := sX) x hreg
  have : Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    Module.free_of_flat_of_isLocalRing
  have := essFiniteType_functionField (sX := sX)
  refine exists_topForms_generator_of_free (K := X.functionField) ?_
  rw [← finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField),
    finrank_kaehlerDifferential_eq_trdeg, hd]

variable {k : Type*} [CommRing k] in
private theorem kaehler_map_map {A A' K : Type*} [CommRing A] [CommRing A'] [CommRing K]
    [Algebra k A] [Algebra k A'] [Algebra k K] [Algebra A A'] [Algebra A' K] [Algebra A K]
    [IsScalarTower k A A'] [IsScalarTower k A' K] [IsScalarTower k A K] [IsScalarTower A A' K]
    (w : Ω[A⁄k]) :
    KaehlerDifferential.map k k A' K (KaehlerDifferential.map k k A A' w) =
      KaehlerDifferential.map k k A K w := by
  have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp only [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul a x _ hx =>
    calc KaehlerDifferential.map k k A' K (KaehlerDifferential.map k k A A' (a • x))
        = KaehlerDifferential.map k k A' K (a • KaehlerDifferential.map k k A A' x) := by
          rw [LinearMap.map_smul]
      _ = KaehlerDifferential.map k k A' K
            (algebraMap A A' a • KaehlerDifferential.map k k A A' x) := by
          rw [algebraMap_smul]
      _ = algebraMap A A' a •
            KaehlerDifferential.map k k A' K (KaehlerDifferential.map k k A A' x) :=
          LinearMap.map_smul _ _ _
      _ = a • KaehlerDifferential.map k k A K x := by rw [algebraMap_smul, hx]
      _ = _ := (LinearMap.map_smul _ _ _).symm

variable {k : Type*} [CommRing k] in
private theorem topFormsMap_topFormsMap {A A' K : Type*} [CommRing A] [CommRing A'] [CommRing K]
    [Algebra k A] [Algebra k A'] [Algebra k K] [Algebra A A'] [Algebra A' K] [Algebra A K]
    [IsScalarTower k A A'] [IsScalarTower k A' K] [IsScalarTower k A K] [IsScalarTower A A' K]
    {d : ℕ} (ρ : ⋀[A]^d Ω[A⁄k]) :
    topFormsMap k A' K d (topFormsMap k A A' d ρ) = topFormsMap k A K d ρ := by
  have hρ : ρ ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hρ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    simp only [topFormsMap_ιMulti, kaehler_map_map]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul a x _ hx =>
    calc topFormsMap k A' K d (topFormsMap k A A' d (a • x))
        = topFormsMap k A' K d (a • topFormsMap k A A' d x) := by rw [LinearMap.map_smul]
      _ = topFormsMap k A' K d (algebraMap A A' a • topFormsMap k A A' d x) := by
          rw [algebraMap_smul]
      _ = algebraMap A A' a • topFormsMap k A' K d (topFormsMap k A A' d x) :=
          LinearMap.map_smul _ _ _
      _ = a • topFormsMap k A K d x := by rw [algebraMap_smul, hx]
      _ = _ := (LinearMap.map_smul _ _ _).symm

variable {k : Type*} [CommRing k] in
private theorem ordAt_basis_nonneg {A K : Type*} [CommRing A] [Field K] [Algebra k A]
    [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {v : K → ℤ} (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hpos : ∀ a : A, algebraMap A K a ≠ 0 → 0 ≤ v (algebraMap A K a))
    (ρ : ⋀[A]^d Ω[A⁄k]) (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k]))
    (hb : b () = topFormsMap k A K d ρ) :
    0 ≤ ordAt A v (ZTensorPower.basis b 1 ()) := by
  by_cases hgen : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  swap
  · simp [ordAt, hgen]
  obtain ⟨σ, hσ, hσ0⟩ := hgen
  rw [ordAt_eq hmul hunit hσ hσ0]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := ρ))
  have hb' : b () = algebraMap A K a • topFormsBasis A hσ hσ0 () := by
    rw [hb, topFormsBasis_apply, ← ha, map_smul, algebraMap_smul]
  have hc : algebraMap A K a ≠ 0 := by
    rintro hz
    rw [hz, zero_smul] at hb'
    exact b.ne_zero () hb'
  have : formCoeff A hσ hσ0 (ZTensorPower.basis b 1 ()) = algebraMap A K a := by
    rw [formCoeff, ZTensorPower.basis_apply_of_eq_smul hb', zpow_one, LinearEquiv.map_smul]
    simp [Algebra.smul_def]
  rw [this]
  exact hpos a hc

/-- **The form of a generator at a regular point has order zero along the prime divisors
through that point.** -/
private theorem ordForm_eq_zero_of_generator {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] (x : X) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (σ : letI := stalkAlgebra sX x; ⋀[X.presheaf.stalk x]^d Ω[X.presheaf.stalk x⁄k])
    (hσ : letI := stalkAlgebra sX x; Submodule.span (X.presheaf.stalk x) {σ} = ⊤)
    (hb : letI := stalkAlgebra sX x
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX x
      b () = topFormsMap k (X.presheaf.stalk x) X.functionField d σ)
    (Γ : MMP.Mori.PrimeDivisor X) (hΓ : x ∈ Γ.support) :
    Γ.ordForm (sX := sX) (d := d) (m := 1) (ZTensorPower.basis b 1 ()) = 0 := by
  let := stalkAlgebra sX x
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hsp : Γ.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hΓ
  let : Algebra (X.presheaf.stalk x) Γ.localRing := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have hloc := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hsp
  have : IsScalarTower k (X.presheaf.stalk x) Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ Γ.genericPoint (Opens.mem_top _)).hom = ((Scheme.ΓSpecIso (.of k)).inv ≫
      sX.appTop ≫ X.presheaf.germ ⊤ x (Opens.mem_top _) ≫ X.presheaf.stalkSpecializes hsp).hom
    simp
  have : IsScalarTower (X.presheaf.stalk x) Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun t =>
      (AlgebraicGeometry.algebraMap_stalkSpecializes hsp t).symm
  set σΓ := topFormsMap k (X.presheaf.stalk x) Γ.localRing d σ
  have hσΓ : Submodule.span Γ.localRing {σΓ} = ⊤ :=
    span_singleton_topFormsMap
      ((IsLocalRing.maximalIdeal Γ.localRing).under (X.presheaf.stalk x)).primeCompl hσ
  have hcomp : topFormsMap k Γ.localRing X.functionField d σΓ = b () := by
    rw [hb]; exact topFormsMap_topFormsMap σ
  have h0 : topFormsMap k Γ.localRing X.functionField d σΓ ≠ 0 := by
    rw [hcomp]; exact b.ne_zero ()
  refine (Γ.ordForm_eq _ hσΓ h0).trans ?_
  rw [formCoeff]
  have hbb : topFormsBasis Γ.localRing hσΓ h0 () = (1 : X.functionField) • b () := by
    rw [topFormsBasis_apply, hcomp, one_smul]
  rw [ZTensorPower.basis_repr_of_eq_smul hbb]
  simp only [one_zpow, inv_one, one_mul, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [← map_one (algebraMap Γ.localRing X.functionField)]
  exact Γ.ord_algebraMap_of_isUnit isUnit_one

/-- Elements of the local ring along a prime divisor have nonnegative order. -/
private theorem ord_algebraMap_localRing_nonneg {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y) (a : P.localRing) :
    0 ≤ Y.ord (algebraMap P.localRing Y.functionField a) P.genericPoint := by
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]; rfl
  have h := (P.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- **The pull-back of a regular top form has nonnegative order** along every prime divisor `E`
of `Y`, for a dominant `f : Y ⟶ X` inducing an isomorphism of function fields: if `b ()` is the
image of a form `σ` of `Ω^d_{𝒪_{X,f(η_E)}/k}`, then `f^*b ()` is the image of the form `f^*σ`
of `Ω^d_{𝒪_{Y,E}/k}`. -/
private theorem ordForm_pullback_basis_nonneg {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (E : MMP.Mori.PrimeDivisor Y)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (σ : letI := stalkAlgebra sX (f E.genericPoint)
      ⋀[X.presheaf.stalk (f E.genericPoint)]^d Ω[X.presheaf.stalk (f E.genericPoint)⁄k])
    (hb : letI := stalkAlgebra sX (f E.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (f E.genericPoint)
      b () = topFormsMap k (X.presheaf.stalk (f E.genericPoint)) X.functionField d σ) :
    0 ≤ E.ordForm (sX := f ≫ sX) (d := d) (m := 1)
      (pullbackRationalPluriForms sX f (ZTensorPower.basis b 1 ())) := by
  let := stalkAlgebra sX (f E.genericPoint)
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  let := stalkAlgebra (f ≫ sX) E.genericPoint
  have := isScalarTower_stalk_functionField sX (f E.genericPoint)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_stalk_functionField (f ≫ sX) E.genericPoint
  -- `b ()` is a pull-back generator
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hω₀.1 ▸ Submodule.mem_top (x := b ()))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact b.ne_zero () (by rw [← hc, zero_smul])
  have hω : IsPullbackGenerator Y.functionField (b ()) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hc, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0), hω₀.1]
    · rw [← hc, map_smul, ← algebraMap_smul Y.functionField,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ ((map_ne_zero _).mpr hc0)), hω₀.2.1]
    · rw [← hc, map_smul, ← algebraMap_smul Y.functionField]
      exact smul_ne_zero ((map_ne_zero _).mpr hc0) hω₀.2.2
  -- the pull-back
  have hpull : pullbackRationalPluriForms (d := d) (m := 1) sX f (ZTensorPower.basis b 1 ()) =
      (ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1 () :
        RationalPluriForms (f ≫ sX) d 1) := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 _ = _
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    have h1 : basisOfSpanSingleton hω.1 hω.ne_zero () = (1 : X.functionField) • b () := by
      rw [basisOfSpanSingleton_apply, one_smul]
    rw [ZTensorPower.basis_repr_of_eq_smul h1]
    simp
  rw [hpull]
  -- the local ring of `E` over that of `x`
  let : Algebra (X.presheaf.stalk (f E.genericPoint)) E.localRing :=
    (f.stalkMap E.genericPoint).hom.toAlgebra
  let : Algebra (X.presheaf.stalk (f E.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (f E.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (f E.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (X.presheaf.stalk (f E.genericPoint)) E.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun t =>
      functionFieldMap_algebraMap_stalk f E.genericPoint t
  have : IsScalarTower k (X.presheaf.stalk (f E.genericPoint)) E.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
      Y.presheaf.germ ⊤ E.genericPoint (Opens.mem_top _)).hom = ((Scheme.ΓSpecIso (.of k)).inv ≫
      sX.appTop ≫ X.presheaf.germ ⊤ (f E.genericPoint) (Opens.mem_top _) ≫
        f.stalkMap E.genericPoint).hom
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.Hom.germ_stalkMap]
    rfl
  have : IsScalarTower k (X.presheaf.stalk (f E.genericPoint)) Y.functionField :=
    IsScalarTower.to₁₂₄ k (X.presheaf.stalk (f E.genericPoint)) X.functionField Y.functionField
  have hb'' : basisOfSpanSingleton hω.2.1 hω.2.2 () = topFormsMap k E.localRing Y.functionField d
      (topFormsMap k (X.presheaf.stalk (f E.genericPoint)) E.localRing d σ) := by
    rw [basisOfSpanSingleton_apply, topFormsMap_topFormsMap, hb, topFormsMap_topFormsMap]
  exact ordAt_basis_nonneg (k := k) E.ord_mul_of_ne_zero
    (fun _ ha => E.ord_algebraMap_of_isUnit ha)
    (fun a _ => ord_algebraMap_localRing_nonneg E a) _ _ hb''

/-- **The measure.** On a regular normal variety `Y`, every divisor `E` over `Y` has a
discrepancy `a(E, Y, 0)` which is a natural number: `K_Y` is Cartier, a generator `σ` of
`Ω^n_{𝒪_{Y,y}/k}` at the centre `y` of `E` is a local generator of `ω_Y` near `y`, and its
pull-back is the image of the form `f^*σ` of `Ω^n_{𝒪_{E}/k}`, hence of nonnegative order along
`E`. -/
private theorem exists_natCast_isDiscrepancy_zero {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) (E : DivisorOver k sY) :
    ∃ m : ℕ, MMP.Mori.IsDiscrepancy sY n K 0 E m := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hn
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have hbij := E.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨σ, hσ, h0⟩ :=
    exists_topForms_generator_stalk (sX := sY) (E.f E.E.genericPoint) (hYreg _) hd
  let := stalkAlgebra sY (E.f E.E.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (E.f E.E.genericPoint)
  have hs := span_singleton_topFormsMap (K := Y.functionField)
    (nonZeroDivisors (Y.presheaf.stalk (E.f E.E.genericPoint))) hσ
  set b := basisOfSpanSingleton hs h0 with hbdef
  have hb : b () = topFormsMap k (Y.presheaf.stalk (E.f E.E.genericPoint)) Y.functionField n σ :=
    basisOfSpanSingleton_apply _ _ _
  set τ : RationalPluriForms sY n 1 := ZTensorPower.basis b 1 () with hτdef
  have hτ0 : τ ≠ 0 := (ZTensorPower.basis b 1).ne_zero ()
  have hΓ : ∀ Γ : MMP.Mori.PrimeDivisor Y, E.f E.E.genericPoint ∈ Γ.support →
      Γ.ordForm τ = 0 := fun Γ hΓ =>
    ordForm_eq_zero_of_generator (sX := sY) _ hd b σ hσ hb Γ hΓ
  -- an open neighbourhood `W` of the centre on which `τ` generates
  let F := (finite_ordForm_ne_zero τ).toFinset
  have hFc : IsClosed (⋃ Γ ∈ F, (Γ.support : Set Y)) :=
    F.finite_toSet.isClosed_biUnion fun Γ _ => Γ.idealSheaf.support.isClosed
  let W : Y.Opens := ⟨_, hFc.isOpen_compl⟩
  have hxW : E.f E.E.genericPoint ∈ W := by
    change E.f E.E.genericPoint ∉ ⋃ Γ ∈ F, (Γ.support : Set Y)
    simp only [Set.mem_iUnion, not_exists]
    intro Γ hΓF hxΓ
    exact ((Set.Finite.mem_toFinset _).mp hΓF) (hΓ Γ hxΓ)
  have hgen : GeneratesOn (0 : QDivisor Y) 1 W τ := by
    refine ⟨hτ0, fun Γ ⟨y, hyΓ, hyW⟩ => ?_⟩
    have : Γ.ordForm τ = 0 := by
      by_contra hne
      exact hyW (Set.mem_biUnion ((Set.Finite.mem_toFinset _).mpr hne) hyΓ)
    simp [this]
  -- `K` is Cartier
  have hsm : IsSmoothScheme sY :=
    isSmoothScheme_of_isRegularLocalRing sY hYreg
  have hKc := MMP.Fourfold.isCartier_of_isSmoothScheme hsm K
  -- the order of the pull-back is nonnegative
  have hpos : 0 ≤ E.ordPullback τ :=
    ordForm_pullback_basis_nonneg (sX := sY) E.f hbij hd E.E b σ hb
  refine ⟨(E.ordPullback τ).toNat, hY, hK, 1, one_pos, ?_, W, hxW, τ, hgen, ?_⟩
  · simpa using QDivisor.isCartierDivisor_toQDivisor.mpr hKc
  · push_cast
    rw [one_mul]
    exact_mod_cast Int.toNat_of_nonneg hpos

/-- **The first stage**: restricted to the smooth locus, a neighbourhood of `η_W`, the data of the
statement form a stage with `N = 0` and `μ = mult_W(D)`. -/
private theorem exists_stage {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X} (hD : 0 ≤ D)
    (hKD : (Divisor.toQDivisor K + D).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (E : DivisorOver k sX) (hE : E.f E.E.genericPoint = W.isIrreducible.genericPoint) {q : ℚ}
    (hq : MMP.Mori.IsDiscrepancy sX n K D E q) :
    ∃ m : ℕ, Stage k (D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ)) q m := by
  have hP : IsPairWith sX n K D := ⟨hX, hK, hKD⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  set U := smoothLocus sX
  have hU : W.isIrreducible.genericPoint ∈ U :=
    (mem_smoothLocus_iff_isRegularLocalRing sX _).mpr hreg
  have hη : E.f E.E.genericPoint ∈ U := hE ▸ hU
  have hUc : ((E.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [E.center_eq_closure_genericPoint]; exact subset_closure rfl, hη⟩
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hP E U hUc
  have hqU := (hiff q).mp hq
  have hKU := hqU.2.1
  have hUv := isNormalVariety_ι hX U
  have : IsIntegral U.toScheme := hUv.1.toIsIntegral
  have : IsLocallyNoetherian U.toScheme := hUv.1.toLocallyOfFiniteType.isLocallyNoetherian
  have : IsNormal U.toScheme := hUv.2
  have hUreg : ∀ y : U.toScheme, IsRegularLocalRing (U.toScheme.presheaf.stalk y) := fun y =>
    isRegularLocalRing_of_isOpenImmersion U.ι y
      ((mem_smoothLocus_iff_isRegularLocalRing sX (U.ι y)).mp y.2)
  obtain ⟨W', hW', hW'η, hW'c, hsum⟩ := exists_irreducibleCloseds_restrict D W U hU
  have hE'' : (E.f ∣_ U) E'.genericPoint = W'.isIrreducible.genericPoint := by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hW'η, ← hE, ← hE',
      ← OpenWeilRestriction.genericPoint_primeDivisorMap]
  obtain ⟨m, hm⟩ := exists_natCast_isDiscrepancy_zero (U.ι ≫ sX) hUv hUreg hKU
    (⟨_, E.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX))
  refine ⟨m, U.toScheme, U.ι ≫ sX, inferInstance, inferInstance, inferInstance, hUv, hUreg, n,
    K.restrictOpen U, D.restrictOpen U, 0, ?_, le_rfl, W', hW'c.trans hW, hsum.le,
    ⟨_, E.f ∣_ U, hY, hf, E'⟩, hE'', by simpa using hqU, hm⟩
  exact fun Γ => hD (OpenWeilRestriction.primeDivisorMap U.ι Γ)

/-- `mult_Z` is additive: `mult_Z(P - N) = mult_Z(P) - mult_Z(N)`. -/
private theorem sum_mult_sub {Y : Scheme.{u}} (c : MMP.Mori.PrimeDivisor Y → ℚ) (P N : QDivisor Y) :
    ((P - N).sum fun Γ d => d * c Γ) = (P.sum fun Γ d => d * c Γ) - N.sum fun Γ d => d * c Γ :=
  Finsupp.sum_sub_index fun _ _ _ => sub_mul _ _ _

/-- `mult_Z(N) ≥ 0` for `N ≥ 0`. -/
private theorem sum_mult_nonneg {Y : Scheme.{u}} {W : IrreducibleCloseds Y} {N : QDivisor Y}
    (hN : 0 ≤ N) : 0 ≤ N.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ) :=
  Finsupp.sum_nonneg fun Γ _ => mul_nonneg (hN Γ) (Nat.cast_nonneg _)

/-- **The last step**: if `E` has the valuation of the exceptional divisor of the blow-up of its
centre `Z` (of codimension two, regular at its generic point), then
`a(E, Y, P - N) = 1 - mult_Z(P - N) ≥ 1 - mult_Z(P)`. -/
private theorem one_sub_le_of_valuation_eq_blowUp {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY) {n : ℕ} {K : Divisor Y} {P N : QDivisor Y}
    (hN : 0 ≤ N) {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk Z.isIrreducible.genericPoint)) {μ q : ℚ}
    (hmult : (P.sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ μ)
    (E : DivisorOver k sY) (hE : E.f E.E.genericPoint = Z.isIrreducible.genericPoint)
    (hq : MMP.Mori.IsDiscrepancy sY n K (P - N) E q) (D : DivisorOver k sY)
    (j : D.Y ⟶ Bl[Z])
    [IsOpenImmersion j] (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hD : D.f D.E.genericPoint = Z.isIrreducible.genericPoint)
    (hv : D.valuation = E.valuation) : 1 - μ ≤ q := by
  obtain ⟨-, hK, m, hm, hC, -⟩ := id hq
  have hKB : (Divisor.toQDivisor K + (P - N)).IsQCartier :=
    ⟨m, by exact_mod_cast hm.ne', hC⟩
  have hD' := isDiscrepancy_blowUp_of_isRegularLocalRing sY hY hK (P - N) hKB Z (c := 2)
    (by rw [hZ]; rfl) le_rfl hreg D j hj hD
  have heq := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (hD.trans hE.symm) hD' hq
  rw [← heq, sum_mult_sub]
  have := sum_mult_nonneg (W := Z) hN
  push_cast
  linarith

/-- The inverse transform of an effective divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {X Y : Scheme.{u}} (g : Y ⟶ X) {D : QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  classical
  rw [inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply,
    Finsupp.sum]
  refine Finset.sum_nonneg fun P _ => ?_
  cases inverseTransformPrimeDivisor g P with
  | none => exact le_rfl
  | some E => exact Finsupp.single_nonneg.mpr (hD P)

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
private noncomputable def compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by rw [Category.assoc]; exact E.isNormalVariety
    isBirationalMorphism := MMP.Mori.IsPair.isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

private theorem valuation_compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- For a birational morphism `f : Y ⟶ X`, a valuation `ξ` of `k(Y)` restricting on `k(X)` to the
valuation of a divisor `(W, g, F)` over `X` is a divisor of `k(Y)`: it is `ord_F` on `W`,
transported along `k(Y) ≅ k(X) ≅ k(W)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (hf : IsBirationalMorphism f) (D : DivisorOver k sX)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap f) = D.valuation) :
    MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  let eP := MMP.Mori.functionFieldAlgEquiv sX f hf.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hf.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
  change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
  rw [h1, hs]
  rfl

/-- **The center on a proper model.** For a proper dominant morphism `f : Y ⟶ X` of integral
schemes and a divisor `D` over `X`, a valuation `ξ` of `k(Y)` restricting on `k(X)` to `ord_D`
dominates the local ring of some point of `Y`: the valuation ring of `ξ` dominates
`𝒪_{X, c_X(D)}`, and the valuative criterion for `f` lifts `Spec 𝒪_ξ ⟶ X` to `Y`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] [IsProper f] (D : DivisorOver k sX)
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap f) = D.valuation) :
    ∃ y : Y, (∀ a : Y.presheaf.stalk y, ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
        ξ (algebraMap _ Y.functionField a) < 1 := by
  set z := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk z,
      ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ X.functionField b)) h
    simpa only [Valuation.comap_apply] using this
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk z →+* R :=
    ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
  have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence f := by
    have h : @IsProper _ _ f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq f :=
    { R := R
      K := Y.functionField
      i₁ := Y.fromSpecStalk (genericPoint Y)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk f,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
      Y.fromSpecStalk (genericPoint Y) := hl₁
  set y := l (IsLocalRing.closedPoint R)
  have hy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
      Y.presheaf.stalkSpecializes hy := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk y)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : Y.presheaf.stalk y,
      algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨y, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]; exact (g.hom a).2
  · rw [hga]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- **A divisor over `X` lives on a proper model** (Kollár–Mori, proof of 2.32). For a proper
birational morphism `f : Y ⟶ X` of normal varieties, every divisor `(W, g, F)` over `X` has the
valuation of a divisor over `Y`: `f⁻¹ ∘ g` is defined on an open `W' ∋ η_F`, and `(W', f⁻¹ ∘ g,
F ∩ W')` is a divisor over `Y` with the valuation of `F`. -/
private theorem exists_divisorOver_comap_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    [IsProper f] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (D : DivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ D' : DivisorOver k (f ≫ sX), D'.valuation.comap (functionFieldMap f) = D.valuation := by
  haveI : IsDominant f := hf.isDominant
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  let e := RingEquiv.ofBijective (functionFieldMap f) hf.functionFieldMap_bijective
  let ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) :=
    D.valuation.comap e.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    change D.valuation (e.symm (e t)) = D.valuation t
    rw [e.symm_apply_apply]
  obtain ⟨y, h1, h2⟩ := exists_dominated_point_of_comap_eq f D ξ hξ
  obtain ⟨D', -, hv, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX)
    (isDivisorOfFunctionField_of_comap_eq f hf D ξ hξ) y h1 h2
  exact ⟨D'.toDivisorOver, by rw [← hξ]; exact congrArg (·.comap (functionFieldMap f)) hv⟩

/-- The blow-up of a regular scheme over a perfect field along a regular irreducible closed
subset `Z` (with its reduced structure) is a smooth blow-up. -/
private theorem isSmoothBlowup_vanishingIdeal {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (Z : IrreducibleCloseds Y)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w)) :
    MMP.Resolution.IsSmoothBlowup sY 𝓘[Z] := by
  set I := 𝓘[Z]
  have hIsupp : (I.support : Set Y) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  refine ⟨isSmoothScheme_of_isRegularLocalRing sY hYreg,
    eq_top_iff.mpr fun z _ => (mem_smoothLocus_iff_isRegularLocalRing _ z).mpr ?_⟩
  have hz : I.subschemeι z ∈ (Z : Set Y) := by
    rw [← hIsupp, ← I.range_subschemeι]; exact ⟨z, rfl⟩
  have h := hZreg _ hz
  rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk] at h
  exact IsRegularLocalRing.of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I z)

private theorem isIrreducible_support_vanishingIdeal {Y : Scheme.{u}} (Z : IrreducibleCloseds Y) :
    IsIrreducible (𝓘[Z].support : Set Y) := by
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact Z.isIrreducible

/-- The support of the vanishing ideal of `Z`, as an irreducible closed subset, is `Z`. -/
private theorem mk_support_vanishingIdeal {Y : Scheme.{u}} (Z : IrreducibleCloseds Y) :
    (⟨_, isIrreducible_support_vanishingIdeal Z, 𝓘[Z].support.isClosed⟩ : IrreducibleCloseds Y) =
      Z :=
  IrreducibleCloseds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

private theorem one_le_codimension_support_vanishingIdeal {Y : Scheme.{u}}
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2) :
    1 ≤ codimension (⟨_, isIrreducible_support_vanishingIdeal Z, 𝓘[Z].support.isClosed⟩ :
      IrreducibleCloseds Y) := by
  rw [mk_support_vanishingIdeal, hZ]; exact_mod_cast (by norm_num : 1 ≤ 2)

/-- **The blow-up of a smooth codimension-two centre** is a regular normal variety of the same
dimension, and the blow-down `π` is proper and birational. -/
private theorem blowUp_basic {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    {n : ℕ} (hn : topologicalKrullDim Y = n) :
    IsNormalVariety k (Blπ[Z] ≫ sY) ∧
      (∀ b, IsRegularLocalRing (Bl[Z].presheaf.stalk b)) ∧
      IsBirationalMorphism Blπ[Z] ∧ IsProper Blπ[Z] ∧
      topologicalKrullDim Bl[Z] = topologicalKrullDim Y := by
  classical
  set I := 𝓘[Z] with hI
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hsb := isSmoothBlowup_vanishingIdeal sY hYreg Z hZreg
  have hirr := isIrreducible_support_vanishingIdeal Z
  have hc : ((2 : ℕ) : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ :
      IrreducibleCloseds Y) := by rw [mk_support_vanishingIdeal, hZ]; rfl
  obtain ⟨hvar, hsm, -, hbir, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      sY hY.1 hn I hsb hirr hc le_rfl
  have hc1 := one_le_codimension_support_vanishingIdeal hZ
  have : IsIntegral (AlgebraicGeometry.blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have : IsLocallyNoetherian Y := inferInstance
  have hft := TwoStepTower.isFiniteType_of_isLocallyNoetherian I
  have : IsProper (AlgebraicGeometry.blowUpToBase I) := TwoStepTower.isProper_blowUpToBase hft
  set e := Stacks.Blowup.blowUpIso I with he
  have hπe : Stacks.Blowup.blowUpToBase I = e.hom ≫ AlgebraicGeometry.blowUpToBase I :=
    (Stacks.Blowup.blowUpIso_hom_comp I).symm
  have : Nonempty (Stacks.Blowup.blowUp I) := ⟨e.inv (genericPoint _)⟩
  have : IsIntegral (Stacks.Blowup.blowUp I) := isIntegral_of_isOpenImmersion e.hom
  have : Smooth (AlgebraicGeometry.blowUpToBase I ≫ sY) := hsm
  have : AlgebraicGeometry.IsVariety k (AlgebraicGeometry.blowUpToBase I ≫ sY) := hvar
  have : Smooth (Stacks.Blowup.blowUpToBase I ≫ sY) := by
    rw [hπe, Category.assoc]; infer_instance
  have hvarS : AlgebraicGeometry.IsVariety k (Stacks.Blowup.blowUpToBase I ≫ sY) := by
    rw [hπe, Category.assoc]
    constructor <;> infer_instance
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have hnorm : IsNormal (Stacks.Blowup.blowUp I) :=
    AlgebraicGeometry.isNormal_of_smooth (Stacks.Blowup.blowUpToBase I ≫ sY)
  have hbirS : IsBirationalMorphism (Stacks.Blowup.blowUpToBase I) := by
    rw [hπe]
    exact MMP.Mori.IsPair.isBirationalMorphism_comp (isBirationalMorphism_of_isIso e.hom) hbir
  refine ⟨⟨hvarS, hnorm⟩, fun b => ?_, hbirS, by rw [hπe]; infer_instance, ?_⟩
  · exact (mem_smoothLocus_iff_isRegularLocalRing _ b).mp <| by
      rw [show smoothLocus (Stacks.Blowup.blowUpToBase I ≫ sY) = ⊤ from
        MMP.Resolution.isSmoothScheme_of_smooth _]
      trivial
  · have : IsDominant (Stacks.Blowup.blowUpToBase I) := hbirS.isDominant
    have : LocallyOfFiniteType (Stacks.Blowup.blowUpToBase I ≫ sY) := hvarS.toLocallyOfFiniteType
    rw [← MMP.Mori.toENat_trdeg_functionField (sX := Stacks.Blowup.blowUpToBase I ≫ sY),
      ← MMP.Mori.toENat_trdeg_functionField (sX := sY),
      MMP.Mori.trdeg_functionField_eq_of_bijective sY _ hbirS.functionFieldMap_bijective]

/-- **The points of codimension one of a smooth blow-up lying over points of codimension `≥ 2`**
map to the generic point of the centre: they lie on the exceptional prime divisor `F`, so they
are its generic point, and `π(F) = Z`. -/
private theorem map_eq_genericPoint_of_coheight_eq_one {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] (I : Y.IdealSheafData)
    (hsb : MMP.Resolution.IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (Z : IrreducibleCloseds Y) (hZI : (Z : Set Y) = I.support)
    (x : AlgebraicGeometry.blowUp I) (hx : Order.coheight x = 1)
    (h2 : 2 ≤ Order.coheight (AlgebraicGeometry.blowUpToBase I x)) :
    AlgebraicGeometry.blowUpToBase I x = Z.isIrreducible.genericPoint := by
  obtain ⟨-, F, hF, -, himg⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY I hsb hirr hc1
  -- `x` lies over the centre
  have hxI : AlgebraicGeometry.blowUpToBase I x ∈ (I.support : Set Y) := by
    by_contra hn
    set W : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    have := isIso_blowUp_restrict_compl_support I
    let x' : (AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ W).toScheme := ⟨x, hn⟩
    have e1 := coheight_eq_of_isOpenImmersion (x := x') (AlgebraicGeometry.blowUpToBase I ∣_ W)
    have e2 :=
      coheight_eq_of_isOpenImmersion (x := ((AlgebraicGeometry.blowUpToBase I ∣_ W) x')) W.ι
    have e3 := coheight_eq_of_isOpenImmersion (x := x') (AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ W).ι
    have e4 : W.ι ((AlgebraicGeometry.blowUpToBase I ∣_ W) x') =
        AlgebraicGeometry.blowUpToBase I x := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]; rfl
    have e5 : (AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ W).ι x' = x := rfl
    rw [e4] at e2
    rw [e5] at e3
    rw [e2, e1, ← e3, hx] at h2
    exact absurd h2 (by decide)
  -- so it lies on `F`
  have hxF : x ∈ F.support := by
    change x ∈ (F.idealSheaf.support : Set _)
    rw [hF, Scheme.IdealSheafData.support_comap]
    exact hxI
  have hsp : F.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxF
  have hxη : x = F.genericPoint := by
    by_contra hne
    have hlt : x < F.genericPoint := lt_of_le_not_ge (show x ≤ F.genericPoint from hsp)
      fun h => hne ((show x ⤳ F.genericPoint from h).antisymm hsp).eq
    have := Order.coheight_add_one_le hlt
    rw [F.coheight_genericPoint, hx] at this
    exact absurd this (by decide)
  -- and `π(F) = Z`
  have : IsProper (AlgebraicGeometry.blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  rw [hxη]
  have hcl : closure {AlgebraicGeometry.blowUpToBase I F.genericPoint} = (Z : Set Y) := by
    rw [hZI, ← himg, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← (AlgebraicGeometry.blowUpToBase I).isClosedMap.closure_image_eq_of_continuous
        (AlgebraicGeometry.blowUpToBase I).continuous, Set.image_singleton]
  exact (isGenericPoint_def.mpr hcl).eq (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)

/-- **The exceptional prime divisors of the blow-up lie over the generic point of the centre**:
a prime divisor `G` of the blow-up whose image has codimension `≥ 2` is the exceptional divisor,
whose generic point maps to `η_Z`. -/
private theorem blowUp_map_genericPoint_of_two_le_coheight {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    (hB : IsNormalVariety k (Blπ[Z] ≫ sY))
    [IsIntegral Bl[Z]] [IsLocallyNoetherian Bl[Z]] [IsNormal Bl[Z]]
    (hπ : IsBirationalMorphism Blπ[Z])
    (G : MMP.Mori.PrimeDivisor Bl[Z])
    (hG : 2 ≤ Order.coheight (Blπ[Z] G.genericPoint)) :
    Blπ[Z] G.genericPoint = Z.isIrreducible.genericPoint := by
  classical
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hIsupp : (𝓘[Z].support : Set Y) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hsb := isSmoothBlowup_vanishingIdeal sY hYreg Z hZreg
  have hirr := isIrreducible_support_vanishingIdeal Z
  have hc1 := one_le_codimension_support_vanishingIdeal hZ
  have he := Stacks.Blowup.blowUpIso_hom_comp 𝓘[Z]
  have hx : Order.coheight ((Stacks.Blowup.blowUpIso _).hom G.genericPoint) = 1 := by
    rw [coheight_eq_of_isOpenImmersion, G.coheight_genericPoint]
  have hmap : AlgebraicGeometry.blowUpToBase _ ((Stacks.Blowup.blowUpIso
      𝓘[Z]).hom G.genericPoint) =
      Stacks.Blowup.blowUpToBase _ G.genericPoint := by
    rw [← Scheme.Hom.comp_apply, he]
  rw [← hmap] at hG ⊢
  exact map_eq_genericPoint_of_coheight_eq_one sY _ hsb hirr hc1 Z hIsupp.symm _ hx hG

/-- **Dimension count.** For a morphism `π : B ⟶ Y` of varieties of the same dimension `n`, a point
`b` of `B` whose image has codimension two has codimension at most two:
`n = trdeg κ(b) + codim b` and `n = trdeg κ(π b) + 2`, with `κ(π b) ⊆ κ(b)`. -/
private theorem coheight_le_two_of_map {k : Type u} [Field k] {B Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsIntegral B] (hY : IsNormalVariety k sY)
    (π : B ⟶ Y) (hB : IsNormalVariety k (π ≫ sY)) {n : ℕ} (hn : topologicalKrullDim Y = n)
    (hdim : topologicalKrullDim B = n) (b : B) (hb : Order.coheight (π b) = 2) :
    Order.coheight b ≤ 2 := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (π ≫ sY) := hB.1.toLocallyOfFiniteType
  have hY' := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y sY (π b)
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k Y sY (π b), hn,
    ringKrullDim_stalk_eq_coheight, hb] at hY'
  have hB' := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k B (π ≫ sY) b
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k B (π ≫ sY) b, hdim,
    ringKrullDim_stalk_eq_coheight] at hB'
  have htr := MMP.Flips.trdeg_residueField_add (π ≫ sY) sY π rfl b
  letI : Algebra k (Y.residueField (π b)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (π b)).hom.toAlgebra
  letI : Algebra k (B.residueField b) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (π ≫ sY).appTop ≫ B.Γevaluation b).hom.toAlgebra
  have hle : Cardinal.toENat (Algebra.trdeg k (Y.residueField (π b))) ≤
      Cardinal.toENat (Algebra.trdeg k (B.residueField b)) := by
    rw [← htr, map_add]; exact le_self_add
  revert hle hY' hB'
  generalize Cardinal.toENat (Algebra.trdeg k (Y.residueField (π b))) = t
  generalize Cardinal.toENat (Algebra.trdeg k (B.residueField b)) = s
  generalize Order.coheight b = c
  intro hY' hB' hle
  have e1' : t + 2 = n := by exact_mod_cast hY'.symm
  have e2' : s + c = n := by exact_mod_cast hB'.symm
  have ht : t ≠ ⊤ := fun h => by rw [h, top_add] at e1'; exact ENat.top_ne_coe n e1'
  have hs : s ≠ ⊤ := fun h => by rw [h, top_add] at e2'; exact ENat.top_ne_coe n e2'
  have hc : c ≠ ⊤ := fun h => by rw [h, add_top] at e2'; exact ENat.top_ne_coe n e2'
  obtain ⟨t', rfl⟩ := ENat.ne_top_iff_exists.mp ht
  obtain ⟨s', rfl⟩ := ENat.ne_top_iff_exists.mp hs
  obtain ⟨c', rfl⟩ := ENat.ne_top_iff_exists.mp hc
  have h1 : t' + 2 = n := by exact_mod_cast e1'
  have h2 : s' + c' = n := by exact_mod_cast e2'
  have h3 : t' ≤ s' := by exact_mod_cast hle
  exact_mod_cast (by omega : c' ≤ 2)

/-- **Points over `η_Z` have codimension at most two** on the blow-up (dimension count:
`codim b = dim - trdeg κ(b) ≤ dim - trdeg κ(η_Z) = 2`). -/
private theorem blowUp_coheight_le_two {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    (hB : IsNormalVariety k (Blπ[Z] ≫ sY))
    [IsIntegral Bl[Z]] [IsLocallyNoetherian Bl[Z]] [IsNormal Bl[Z]]
    (hπ : IsBirationalMorphism Blπ[Z])
    {n : ℕ} (hn : topologicalKrullDim Y = n)
    (b : Bl[Z]) (hb : Blπ[Z] b = Z.isIrreducible.genericPoint) :
    Order.coheight b ≤ 2 := by
  refine coheight_le_two_of_map hY _ hB hn
    ((blowUp_basic sY hY hYreg hZ hZreg hn).2.2.2.2.trans hn) b ?_
  rw [hb, ← MMP.Flips.codimension_eq_coheight_genericPoint, hZ]

/-- A prime divisor `F` of `Y` is exceptional for a morphism `f : Y ⟶ X` exactly when `f(η_F)`
has codimension at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsSeparated (X ↘ Limits.terminal Scheme)]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap F ↔
      2 ≤ Order.coheight (f F.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hη : F.genericPoint ∈ (F.idealSheaf.support : Set Y) := by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  refine ⟨fun h ↦ h _ (subset_closure ⟨_, hη, rfl⟩), fun h x hx ↦ ?_⟩
  have hsub : closure (f '' (F.idealSheaf.support : Set Y)) ⊆ closure {f F.genericPoint} := by
    refine closure_minimal ?_ isClosed_closure
    change f '' (F.support : Set Y) ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have := image_closure_subset_closure_image (f := f) (s := {F.genericPoint}) f.continuous
    rwa [Set.image_singleton] at this
  have hsp : f F.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (hsub hx)
  exact h.trans (Order.coheight_anti (show x ≤ f F.genericPoint from hsp))

/-- **The crepant boundary on the blow-up.** For `P, N ≥ 0` with `mult_Z(P - N) ≤ 1`, the crepant
boundary of `(Y, P - N)` on the blow-up is `π⁻¹_* P - N'` with `N' ≥ 0`, and discrepancies of
divisors with corresponding valuations agree. -/
private theorem blowUp_crepant {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    (hB : IsNormalVariety k (Blπ[Z] ≫ sY))
    [IsIntegral Bl[Z]] [IsLocallyNoetherian Bl[Z]] [IsNormal Bl[Z]]
    (hπ : IsBirationalMorphism Blπ[Z])
    {n : ℕ} {K : Divisor Y} {P N : QDivisor Y} (hP : 0 ≤ P) (hN : 0 ≤ N)
    (hmult1 : ((P - N).sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ 1)
    (E : DivisorOver k sY) {q : ℚ} (hq : MMP.Mori.IsDiscrepancy sY n K (P - N) E q)
    (K' : Divisor Bl[Z]) (hK' : K'.IsCanonicalDivisor (Blπ[Z] ≫ sY) n)
    (E' : DivisorOver k (Blπ[Z] ≫ sY))
    (hv : haveI : IsDominant Blπ[Z] := hπ.isDominant
      E.valuation = E'.valuation.comap (functionFieldMap Blπ[Z])) :
    ∃ N' : QDivisor Bl[Z], 0 ≤ N' ∧
      MMP.Mori.IsDiscrepancy _ n K' (inverseTransformDivisor Blπ[Z] P - N') E' q := by
  classical
  have hn := hq.2.1.topologicalKrullDim_eq
  have : IsProper Blπ[Z] :=
    (blowUp_basic sY hY hYreg hZ hZreg hn).2.2.2.1
  have : IsDominant Blπ[Z] := hπ.isDominant
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal sY
  have hP' : IsPair sY (P - N) := hq.isPair
  have hK := hq.2.1
  obtain ⟨-, hK0, m₀, hm₀, hC₀, -⟩ := id hq
  have hKB : (Divisor.toQDivisor K + (P - N)).IsQCartier :=
    ⟨m₀, by exact_mod_cast hm₀.ne', hC₀⟩
  obtain ⟨ΔB, hΔB, -⟩ := (MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP' hK _ hB hπ).1
  obtain ⟨hdec, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP' hΔB
  set μ := (P - N).sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ) with hμ
  have hexc : ∀ G : MMP.Mori.PrimeDivisor _,
      MMP.Mori.RationalMap.IsExceptional Blπ[Z].toRationalMap G →
      ΔB G = μ - 1 := by
    intro G hG
    have h2 := (isExceptional_toRationalMap_iff_two_le_coheight _ G).mp hG
    have hη := blowUp_map_genericPoint_of_two_le_coheight sY hY hYreg hZ hZreg hB hπ G h2
    have ha := isDiscrepancy_blowUp_of_isRegularLocalRing sY hY hK (P - N) hKB Z (c := 2)
      (by rw [hZ]; rfl) le_rfl (hYreg _) ⟨_, _, hB, hπ, G⟩ (𝟙 _) (Category.id_comp _) hη
    have := ha.eq (hΔB G)
    change ΔB.coeff G = μ - 1
    push_cast at this
    linarith
  set N' := inverseTransformDivisor Blπ[Z] N -
    Finsupp.filter (fun G => MMP.Mori.RationalMap.IsExceptional Blπ[Z].toRationalMap G) ΔB
    with hN'
  refine ⟨N', fun G => ?_, ?_⟩
  · have h1 : (0 : ℚ) ≤ inverseTransformDivisor Blπ[Z] N G :=
      inverseTransformDivisor_nonneg _ hN G
    rw [hN']
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.filter_apply, Finsupp.coe_zero,
      Pi.zero_apply]
    split_ifs with hG
    · rw [hexc G hG]; linarith
    · simpa using h1
  · have : inverseTransformDivisor Blπ[Z] P - N' = ΔB := by
      rw [hN']
      conv_rhs => rw [hdec]
      rw [map_sub]; abel
    rw [this]
    exact ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP' _ hB hπ hK hK'
      (Or.inl hΔB)).2 E' E hv q).2 hq

/-- **Pull-backs of effective Cartier divisors are positive over their support.** If `D ≥ 0` is
Cartier with `coeff_G(D) > 0` and `f(η_E) ∈ G`, then `coeff_E(f^*D) > 0`: a local equation of `D`
near `f(η_E)` is regular there (Hartogs) and not a unit (it vanishes along `G`), so its pull-back
lies in the maximal ideal of `𝒪_{Y,E}`. -/
private theorem coeff_isPullback_pos {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    {D : Divisor X} (hDc : D.IsCartier) (hDnn : ∀ G, 0 ≤ D.coeff G)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D') (E : MMP.Mori.PrimeDivisor Y)
    (G : MMP.Mori.PrimeDivisor X) (hG : 0 < D.coeff G) (hEG : f E.genericPoint ∈ G.support) :
    0 < D'.coeff E := by
  classical
  have hsub := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)
  obtain ⟨U, hyU, φ, hφ⟩ := hDc (f E.genericPoint)
  have hWc := mem_pointComponent (f E.genericPoint)
  obtain ⟨ϖ, hϖ⟩ := exists_stalk_eq_of_forall_zero_le_ord hWc φ fun E' hE' => by
    rw [← hφ E' ⟨_, hE', hyU⟩]; exact hDnn E'
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f E.genericPoint)) := by
    by_contra hnm
    have hu : IsUnit ϖ := (IsLocalRing.notMem_maximalIdeal.mp hnm)
    have hsp : G.genericPoint ⤳ f E.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hEG
    have hyG : f E.genericPoint ∈ G.component.1 := by
      rw [Subsingleton.elim G.component (pointComponent (f E.genericPoint))]; exact hWc
    have hcomp : G.component = pointComponent (f E.genericPoint) := Subsingleton.elim _ _
    have hval : G.toComponent.hom ((X.presheaf.stalkSpecializes hsp).hom ϖ) =
        ((Units.map (RationalFunctions.component X G.component).toMonoidHom φ :
          (X.presheaf.stalk (componentGenericPoint X G.component))ˣ) :
          X.presheaf.stalk (componentGenericPoint X G.component)) := by
      rw [G.toComponent_stalkSpecializes hsp hyG]
      change _ = (φ : RationalFunctions X) G.component
      revert hyG
      rw [hcomp]
      intro hyG
      exact hϖ
    have h0 := G.ordUnit_eq_zero_of_isUnit (hu.map _) hval
    have hc := hφ G ⟨_, hEG, hyU⟩
    rw [G.ord_eq_ordUnit, h0] at hc
    omega
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff _).mp hyU
  rw [hD' U φ hφ E hEU]
  have h1 := MMP.Fourfold.pullbackComponent_val_eq_stalkMap f hB hφ hWc ϖ hϖ.symm
    E.genericPoint_mem_component (E.map_componentGenericPoint_mem f hEU)
  exact MMP.Fourfold.PrimeDivisor.ordUnit_pos_of_mem_maximalIdeal E
    (map_nonunit (f.stalkMap E.genericPoint).hom ϖ hϖm) h1.symm

/-- **The points over `η_Z` lie on an exceptional divisor** of the blow-up: the exceptional
divisor `F` of the smooth blow-up is `π⁻¹(Z)`. -/
private theorem exists_isExceptional_mem_support {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    [IsIntegral Bl[Z]]
    [IsLocallyNoetherian Bl[Z]]
    [IsNormal Bl[Z]]
    (z : Bl[Z])
    (hz : Blπ[Z] z = Z.isIrreducible.genericPoint) :
    ∃ G : MMP.Mori.PrimeDivisor Bl[Z],
      2 ≤ Order.coheight (Blπ[Z] G.genericPoint) ∧ z ∈ G.support := by
  classical
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have hIsupp : (𝓘[Z].support : Set Y) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hsb := isSmoothBlowup_vanishingIdeal sY hYreg Z hZreg
  have hirr := isIrreducible_support_vanishingIdeal Z
  have hc1 := one_le_codimension_support_vanishingIdeal hZ
  obtain ⟨-, F, hF, -, -⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY _
      hsb hirr hc1
  set e := Stacks.Blowup.blowUpIso
    𝓘[Z] with he
  have hπ : e.inv ≫ Stacks.Blowup.blowUpToBase _ = AlgebraicGeometry.blowUpToBase
      𝓘[Z] := by
    rw [he, ← Stacks.Blowup.blowUpIso_hom_comp, Iso.inv_hom_id_assoc]
  have hxz : e.inv (e.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  have h2 : AlgebraicGeometry.blowUpToBase _ (e.hom z) = Z.isIrreducible.genericPoint := by
    rw [← hπ, Scheme.Hom.comp_apply, hxz, hz]
  have hxF : e.hom z ∈ F.support := by
    change e.hom z ∈ (F.idealSheaf.support : Set _)
    rw [hF, Scheme.IdealSheafData.support_comap]
    show AlgebraicGeometry.blowUpToBase _ (e.hom z) ∈ (𝓘[Z].support : Set Y)
    rw [h2]
    exact (Set.ext_iff.mp hIsupp _).mpr
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hsp : F.genericPoint ⤳ e.hom z := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxF
  have hFc : Order.coheight F.genericPoint = 1 := F.coheight_genericPoint
  have hFmap : AlgebraicGeometry.blowUpToBase _ F.genericPoint = Z.isIrreducible.genericPoint := by
    refine map_eq_genericPoint_of_coheight_eq_one sY _ hsb hirr hc1 Z hIsupp.symm _ hFc ?_
    have h1 := hsp.map (AlgebraicGeometry.blowUpToBase
      𝓘[Z]).continuous
    rw [h2] at h1
    -- `π(η_F)` generalizes `η_Z` and lies in `Z`, so equals `η_Z`
    have hmem : AlgebraicGeometry.blowUpToBase _ F.genericPoint ∈ (Z : Set Y) := by
      refine (Set.ext_iff.mp hIsupp _).mp ?_
      have : F.genericPoint ∈ F.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      change F.genericPoint ∈ (F.idealSheaf.support : Set _) at this
      rw [hF, Scheme.IdealSheafData.support_comap] at this
      exact this
    have h3 : Z.isIrreducible.genericPoint ⤳ AlgebraicGeometry.blowUpToBase _ F.genericPoint :=
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hmem
    rw [(h1.antisymm h3).eq, ← MMP.Flips.codimension_eq_coheight_genericPoint, hZ]
  refine ⟨AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap e.inv F, ?_, ?_⟩
  · show 2 ≤ Order.coheight (Stacks.Blowup.blowUpToBase _
      (AlgebraicGeometry.PrimeDivisor.genericPoint
        (AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap e.inv F)))
    rw [AlgebraicGeometry.OpenWeilRestriction.genericPoint_primeDivisorMap]
    change 2 ≤ Order.coheight ((e.inv ≫ Stacks.Blowup.blowUpToBase _) F.genericPoint)
    rw [hπ, hFmap, ← MMP.Flips.codimension_eq_coheight_genericPoint, hZ]
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    show z ∈ closure {(AlgebraicGeometry.PrimeDivisor.genericPoint
        (AlgebraicGeometry.OpenWeilRestriction.primeDivisorMap e.inv F))}
    rw [AlgebraicGeometry.OpenWeilRestriction.genericPoint_primeDivisorMap, ← hxz]
    exact specializes_iff_mem_closure.mp (hsp.map e.inv.continuous)

/-- **The measure drops**: `a(E, Y, 0) = a(E, Y', 0) + ord_E(F)` with `ord_E(F) ≥ 1`, for the
exceptional divisor `F`, since the centre of `E` on `Y'` lies on `F`. -/
private theorem blowUp_measure_lt {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    (hB : IsNormalVariety k (Blπ[Z] ≫ sY))
    [IsIntegral Bl[Z]] [IsLocallyNoetherian Bl[Z]] [IsNormal Bl[Z]]
    (hπ : IsBirationalMorphism Blπ[Z])
    {n : ℕ} {K : Divisor Y} (E : DivisorOver k sY) {m : ℕ}
    (hm : MMP.Mori.IsDiscrepancy sY n K 0 E m)
    (K' : Divisor Bl[Z]) (hK' : K'.IsCanonicalDivisor (Blπ[Z] ≫ sY) n)
    (E' : DivisorOver k (Blπ[Z] ≫ sY))
    (hv : haveI : IsDominant Blπ[Z] := hπ.isDominant
      E.valuation = E'.valuation.comap (functionFieldMap Blπ[Z]))
    (hE' : Blπ[Z] (E'.f E'.E.genericPoint) = Z.isIrreducible.genericPoint) {m' : ℕ}
    (hm' : MMP.Mori.IsDiscrepancy _ n K' 0 E' m') : m' < m := by
  classical
  have hn := hm.2.1.topologicalKrullDim_eq
  obtain ⟨-, hBreg, -, hπp, -⟩ := blowUp_basic sY hY hYreg hZ hZreg hn
  have : IsProper Blπ[Z] := hπp
  have : IsDominant Blπ[Z] := hπ.isDominant
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal sY
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (Blπ[Z] ≫ sY) :=
    hB.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme sY :=
    isSmoothScheme_of_isRegularLocalRing sY hYreg
  have hsmB : IsSmoothScheme (Blπ[Z] ≫ sY) :=
    isSmoothScheme_of_isRegularLocalRing _ hBreg
  have hP0 : IsPair sY (0 : QDivisor Y) := hm.isPair
  have hK := hm.2.1
  have hKc := MMP.Fourfold.isCartier_of_isSmoothScheme hsmY K
  have hKB : (Divisor.toQDivisor K + 0).IsQCartier :=
    ⟨1, one_ne_zero, by simpa using QDivisor.isCartierDivisor_toQDivisor.mpr hKc⟩
  obtain ⟨⟨ΔB, hΔB, -⟩, hint⟩ :=
    MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP0 hK _ hB hπ
  obtain ⟨D0, hD0⟩ := hint ΔB hΔB 1 (by simpa using QDivisor.isCartierDivisor_toQDivisor.mpr hKc)
  rw [one_smul] at hD0
  obtain ⟨hdec, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP0 hΔB
  have hexc : ∀ G : MMP.Mori.PrimeDivisor _,
      MMP.Mori.RationalMap.IsExceptional Blπ[Z].toRationalMap G →
      ΔB G = -1 := by
    intro G hG
    have h2 := (isExceptional_toRationalMap_iff_two_le_coheight _ G).mp hG
    have hη := blowUp_map_genericPoint_of_two_le_coheight sY hY hYreg hZ hZreg hB hπ G h2
    have ha := isDiscrepancy_blowUp_of_isRegularLocalRing sY hY hK 0 hKB Z (c := 2)
      (by rw [hZ]; rfl) le_rfl (hYreg _) ⟨_, _, hB, hπ, G⟩ (𝟙 _) (Category.id_comp _) hη
    have := ha.eq (hΔB G)
    change ΔB.coeff G = -1
    simp only [Finsupp.sum_zero_index] at this
    push_cast at this
    linarith
  have hnon : ∀ G : MMP.Mori.PrimeDivisor _,
      ¬ MMP.Mori.RationalMap.IsExceptional Blπ[Z].toRationalMap G →
      ΔB G = 0 := by
    intro G hG
    have := congrArg (fun Δ : QDivisor _ => Δ G) hdec
    simp only [map_zero, Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply, if_neg hG,
      Finsupp.coe_zero, Pi.zero_apply, add_zero] at this
    exact this
  -- the divisor `D = -Δ_B`, the sum of the exceptional prime divisors
  set D : Divisor _ := -D0 with hDdef
  have hDq : Divisor.toQDivisor D = -ΔB := by rw [hDdef, map_neg, hD0]
  have hDcoeff : ∀ G, (D.coeff G : ℚ) = -ΔB G := fun G => by
    have := congrArg (fun Δ : QDivisor _ => Δ.coeff G) hDq
    rw [Divisor.coeff_toQDivisor] at this
    exact this
  have hDnn : ∀ G, 0 ≤ D.coeff G := fun G => by
    have h := hDcoeff G
    have : (0 : ℚ) ≤ D.coeff G := by
      by_cases hG : MMP.Mori.RationalMap.IsExceptional Blπ[Z].toRationalMap G
      · rw [h, hexc G hG]; norm_num
      · rw [h, hnon G hG]; norm_num
    exact_mod_cast this
  have hDc : D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmB D
  -- the pair on the blow-up and `a(E', Y', Δ_B) = m`
  have hPB : IsPairWith _ n K' ΔB :=
    ⟨hB, hK', MMP.Fourfold.isQCartier_of_isSmoothScheme hsmB _⟩
  have hmB : MMP.Mori.IsDiscrepancy _ n K' ΔB E' m :=
    ((MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP0 _ hB hπ hK hK'
      (Or.inl hΔB)).2 E' E hv m).2 hm
  obtain ⟨-, hBs, hiff⟩ := MMP.Mori.IsPairWith.isDiscrepancy_add_smul_iff hPB
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsmB (Divisor.toQDivisor D)) E'
  have := E'.isIntegral
  have := E'.isLocallyNoetherian
  have := E'.isNormal
  have : CompactSpace Bl[Z] := by
    have : QuasiCompact (Blπ[Z] ≫ sY) :=
      hB.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (Blπ[Z] ≫ sY)
  have : CompactSpace E'.Y := by
    have := E'.isNormalVariety.1
    have : QuasiCompact (E'.f ≫ Blπ[Z] ≫ sY) :=
      E'.isNormalVariety.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (E'.f ≫ Blπ[Z] ≫ sY)
  have hBD : ∀ Z' : irreducibleComponents E'.Y, E'.f (componentGenericPoint E'.Y Z') ∉ D.supp :=
    fun Z' hZ' => hBs Z' (by rwa [Divisor.supp_toQDivisor])
  set D' := D.pullback hDc hBD with hD'def
  have hD' := Divisor.isPullback_pullback (f := E'.f) hDc hBD
  have hBQ := QDivisor.isPullback_toQDivisor hDc hBs hD'
  have h1 := ((hiff _ hBQ).1 m).2 hmB
  have h0 : ΔB + Divisor.toQDivisor D = 0 := by rw [hDq, add_neg_cancel]
  rw [h0] at h1
  have heq := hm'.eq h1
  -- the coefficient is positive
  obtain ⟨G, hG2, hzG⟩ := exists_isExceptional_mem_support sY hY hYreg hZ hZreg _ hE'
  have hGexc := (isExceptional_toRationalMap_iff_two_le_coheight _ G).mpr hG2
  have hGpos : 0 < D.coeff G := by
    have h := hDcoeff G
    rw [hexc G hGexc] at h
    exact_mod_cast (show (0 : ℚ) < D.coeff G by rw [h]; norm_num)
  have hpos := coeff_isPullback_pos E'.f hDc hDnn hD' E'.E G hGpos hzG
  have hc : (Divisor.toQDivisor D').coeff E'.E = (D'.coeff E'.E : ℚ) :=
    Divisor.coeff_toQDivisor _ _
  rw [hc] at heq
  have : ((m' : ℤ) : ℚ) < ((m : ℤ) : ℚ) := by
    push_cast
    have : (0 : ℚ) < D'.coeff E'.E := by exact_mod_cast hpos
    linarith
  exact_mod_cast this

/-- **The geometry of the blow-up step.** Let `π : Y' = Bl_Z Y ⟶ Y` be the blow-up of a smooth
centre `Z` of codimension two in a regular variety, with exceptional divisor `F`, and let `E` be a
divisor over `Y` with centre `Z` which is not `F`. Then `Y'` is a regular normal variety, the
centre `Z'` of `E` on `Y'` has codimension two, lies over `Z` and dominates it, and, for a
canonical divisor `K'` of `Y'`, the crepant boundary of `(Y, P - N)` on `Y'` is `π⁻¹_* P - N'`
with `N' = π⁻¹_* N + (1 - mult_Z(P - N)) F ≥ 0` (here `mult_Z(P - N) ≤ mult_Z(P) ≤ 1` is used),
so that `q = a(E, Y', π⁻¹_* P - N')`; and `a(E, Y, 0) = a(E, Y', 0) + ord_E(F)` with
`ord_E(F) ≥ 1`. -/
private theorem exists_blowUp_data {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {n : ℕ} {K : Divisor Y} {P N : QDivisor Y} (hP : 0 ≤ P)
    (hN : 0 ≤ N) {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    {μ q : ℚ} (hμ : μ ≤ 1)
    (hmult : (P.sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ μ)
    (E : DivisorOver k sY) (hE : E.f E.E.genericPoint = Z.isIrreducible.genericPoint)
    (hq : MMP.Mori.IsDiscrepancy sY n K (P - N) E q) {m : ℕ}
    (hm : MMP.Mori.IsDiscrepancy sY n K 0 E m)
    (hb : ¬ ∃ (D : DivisorOver k sY) (j : D.Y ⟶ Bl[Z]),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
        D.f D.E.genericPoint = Z.isIrreducible.genericPoint ∧ D.valuation = E.valuation) :
    ∃ (_ : IsIntegral Bl[Z])
      (_ : IsLocallyNoetherian Bl[Z])
      (_ : IsNormal Bl[Z])
      (_ : IsNormalVariety k (Blπ[Z] ≫ sY))
      (_ : ∀ y, IsRegularLocalRing (Bl[Z].presheaf.stalk y))
      (K' : Divisor Bl[Z])
      (N' : QDivisor Bl[Z]) (_ : 0 ≤ N')
      (Z' : IrreducibleCloseds Bl[Z])
      (_ : codimension Z' = 2)
      (_ : ∀ z ∈ (Z' : Set _), Blπ[Z] z ∈ (Z : Set Y))
      (_ : Blπ[Z]
        Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint)
      (E' : DivisorOver k (Blπ[Z] ≫ sY))
      (_ : E'.f E'.E.genericPoint = Z'.isIrreducible.genericPoint) (m' : ℕ) (_ : m' < m),
      MMP.Mori.IsDiscrepancy _ n K' (inverseTransformDivisor Blπ[Z] P - N') E' q ∧
      MMP.Mori.IsDiscrepancy _ n K' 0 E' m' := by
  classical
  set I := 𝓘[Z] with hI
  set π := Stacks.Blowup.blowUpToBase I with hπdef
  obtain ⟨hB, hBreg, hπ, hπp, hdim⟩ :=
    blowUp_basic sY hY hYreg hZ hZreg hq.2.1.topologicalKrullDim_eq
  have : IsIntegral (Stacks.Blowup.blowUp I) := hB.1.toIsIntegral
  have : LocallyOfFiniteType (π ≫ sY) := hB.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  have : IsNormal (Stacks.Blowup.blowUp I) := hB.2
  have : IsDominant π := hπ.isDominant
  have : IsProper π := hπp
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : QuasiCompact (π ≫ sY) := hB.1.toQuasiCompact
  have : CompactSpace (Stacks.Blowup.blowUp I) := QuasiCompact.compactSpace_of_compactSpace (π ≫ sY)
  have hK := hq.2.1
  -- a canonical divisor of the blow-up
  have hsmB : IsSmoothScheme (π ≫ sY) :=
    isSmoothScheme_of_isRegularLocalRing _ hBreg
  have hnB : topologicalKrullDim (Stacks.Blowup.blowUp I) = n :=
    hdim.trans hK.topologicalKrullDim_eq
  have := hB.1
  obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sY) hsmB hnB
  -- the lift of `E`
  obtain ⟨E', hvE'⟩ := exists_divisorOver_comap_valuation_eq hY hB hπ E
  have hv : E.valuation = E'.valuation.comap (functionFieldMap π) := hvE'.symm
  have hcen : π (E'.f E'.E.genericPoint) = Z.isIrreducible.genericPoint := by
    have h1 := (valuation_compDivisorOver π hB hπ E').trans hvE'
    have h2 := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hY h1
    change (E'.f ≫ π) E'.E.genericPoint = _ at h2
    rw [Scheme.Hom.comp_apply] at h2
    exact h2.trans hE
  set z' := E'.f E'.E.genericPoint with hz'
  set Z' := IrreducibleCloseds.closureSingleton z' with hZ'def
  have hZ'gen : Z'.isIrreducible.genericPoint = z' :=
    (Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed).eq (isGenericPoint_closure (x := z'))
  have hZcl : (Z : Set Y) = closure {Z.isIrreducible.genericPoint} :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).symm
  -- `Z'` has codimension two
  have hcod : Order.coheight z' = 2 := by
    have hle :=
      blowUp_coheight_le_two sY hY hYreg hZ hZreg hB hπ hq.2.1.topologicalKrullDim_eq z' hcen
    have hηZ : Order.coheight Z.isIrreducible.genericPoint = 2 := by
      rw [← MMP.Flips.codimension_eq_coheight_genericPoint, hZ]
    have h0 : Order.coheight z' ≠ 0 := by
      intro h0
      have hle : z' ≤ genericPoint (Stacks.Blowup.blowUp I) :=
        (genericPoint_spec _).specializes trivial
      have h2 := (Order.coheight_eq_zero.mp h0) hle
      have hzg : z' = genericPoint (Stacks.Blowup.blowUp I) :=
        (show z' ⤳ genericPoint (Stacks.Blowup.blowUp I) from h2).antisymm
          (show genericPoint (Stacks.Blowup.blowUp I) ⤳ z' from hle) |>.eq
      have hgY : Z.isIrreducible.genericPoint = genericPoint Y := by
        rw [← hcen, hzg, map_genericPoint_of_isDominant]
      have : Order.coheight (genericPoint Y) = 0 :=
        Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec Y).specializes trivial
      rw [← hgY, hηZ] at this
      exact absurd this (by decide)
    have h1 : Order.coheight z' ≠ 1 := by
      intro h1
      set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z' h1
      have hG : G.genericPoint = z' :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
      apply hb
      refine ⟨⟨_, π, hB, hπ, G⟩, 𝟙 _, inferInstance, Category.id_comp _, ?_, ?_⟩
      · change π G.genericPoint = _
        rw [hG, hcen]
      · have h3 := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hB E' G hG.symm
        rw [hv, h3]
        ext t
        change MMP.Mori.PrimeDivisor.divisorialValuation G (functionFieldMap π t) =
          MMP.Mori.PrimeDivisor.divisorialValuation G
            (functionFieldMap (𝟙 _) (functionFieldMap π t))
        rw [MMP.Mori.functionFieldMap_id_apply]
    have hne : Order.coheight z' ≠ ⊤ := ne_top_of_le_ne_top (by decide) hle
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hc] at hle h0 h1 ⊢
    have hc2 : c ≤ 2 := by exact_mod_cast hle
    have hc0 : c ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have hc1 : c ≠ 1 := fun h => h1 (by rw [h]; rfl)
    obtain rfl : c = 2 := by omega
    rfl
  have hZ'c : codimension Z' = 2 := by
    rw [hZ'def, MMP.Flips.codimension_closureSingleton, hcod]
  have hZF : ∀ z ∈ (Z' : Set _), π z ∈ (Z : Set Y) := by
    intro z hz
    rw [hZcl, ← hcen]
    exact (specializes_iff_mem_closure.mpr hz).map π.continuous |>.mem_closure
  have hZW : π Z'.isIrreducible.genericPoint = Z.isIrreducible.genericPoint := by
    rw [hZ'gen, hcen]
  -- the measure
  obtain ⟨m', hm'⟩ := exists_natCast_isDiscrepancy_zero (π ≫ sY) hB hBreg hK' E'
  have hlt := blowUp_measure_lt sY hY hYreg hZ hZreg hB hπ E hm K' hK' E' hv hcen hm'
  -- the boundary
  have hmult1 : ((P - N).sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ 1 := by
    rw [sum_mult_sub]
    have := sum_mult_nonneg (W := Z) hN
    linarith
  obtain ⟨N', hN', hq'⟩ := blowUp_crepant sY hY hYreg hZ hZreg hB hπ hP hN hmult1 E hq K' hK' E' hv
  exact ⟨inferInstance, inferInstance, inferInstance, hB, hBreg, K', N', hN', Z', hZ'c, hZF, hZW,
    E', by rw [hZ'gen], m', hlt, hq', hm'⟩

/-- **Blowing up the centre.** If `E` is not the exceptional divisor of the blow-up of its
centre `Z`, then the blow-up gives a stage of smaller measure; the bound
`mult_{Z'}(π⁻¹_* P) ≤ mult_Z(P) ≤ μ` on the new centre is
`multiplicityAlong_inverseTransformDivisor_blowUpToBase_le`. -/
private theorem exists_stage_blowUp {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY)
    (hYreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    {n : ℕ} {K : Divisor Y} {P N : QDivisor Y} (hP : 0 ≤ P)
    (hN : 0 ≤ N) {Z : IrreducibleCloseds Y} (hZ : codimension Z = 2)
    (hZreg : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    {μ q : ℚ} (hμ : μ ≤ 1)
    (hmult : (P.sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ μ)
    (E : DivisorOver k sY) (hE : E.f E.E.genericPoint = Z.isIrreducible.genericPoint)
    (hq : MMP.Mori.IsDiscrepancy sY n K (P - N) E q) {m : ℕ}
    (hm : MMP.Mori.IsDiscrepancy sY n K 0 E m)
    (hb : ¬ ∃ (D : DivisorOver k sY) (j : D.Y ⟶ Bl[Z]),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
        D.f D.E.genericPoint = Z.isIrreducible.genericPoint ∧ D.valuation = E.valuation) :
    ∃ m' < m, Stage k μ q m' := by
  obtain ⟨_, _, _, hY', hY'reg, K', N', hN', Z', hZ', hZF, hZW, E', hE', m', hm', hq', hm''⟩ :=
    exists_blowUp_data sY hY hYreg hP hN hZ hZreg hμ hmult E hE hq hm hb
  refine ⟨m', hm', _, _, inferInstance, inferInstance, inferInstance, hY', hY'reg, n, K', _, N',
    inverseTransformDivisor_nonneg _ hP, hN', Z', hZ', ?_, E', hE', hq', hm''⟩
  exact (multiplicityAlong_inverseTransformDivisor_blowUpToBase_le sY hY.1 hYreg Z hZ hZreg Z'
    hZ' hZF hZW P hP).trans hmult

/-- The *smooth* stages: those whose centre `Z` is regular (`𝒪_{Z,w}` regular for `w ∈ Z`). -/
private def SmoothStage (k : Type u) [Field k] (μ q : ℚ) (m : ℕ) : Prop :=
  ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
    (_ : IsNormal Y) (_ : IsNormalVariety k sY)
    (_ : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (n : ℕ) (K : Divisor Y) (P N : QDivisor Y) (_ : 0 ≤ P) (_ : 0 ≤ N)
    (Z : IrreducibleCloseds Y) (_ : codimension Z = 2)
    (_ : ∀ w ∈ (Z : Set Y), IsRegularLocalRing (Y.presheaf.stalk w ⧸
      𝓘[Z].stalkIdeal w))
    (_ : (P.sum fun Γ d => d * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤ μ)
    (E : DivisorOver k sY) (_ : E.f E.E.genericPoint = Z.isIrreducible.genericPoint),
    MMP.Mori.IsDiscrepancy sY n K (P - N) E q ∧ MMP.Mori.IsDiscrepancy sY n K 0 E m

/-- **Generic smoothness of the centre.** An irreducible closed subset `Z` of a variety over an
algebraically closed field of characteristic zero is regular on an open neighbourhood `V` of its
generic point: `𝒪_{Z ∩ V, w}` is regular for every `w ∈ Z ∩ V`. -/
private theorem exists_open_isRegularLocalRing_quotient {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    (hY : IsNormalVariety k sY) (Z : IrreducibleCloseds Y) :
    ∃ V : Y.Opens, Z.isIrreducible.genericPoint ∈ V ∧
      ∀ Z' : IrreducibleCloseds V.toScheme, (Z' : Set V.toScheme) = V.ι ⁻¹' (Z : Set Y) →
        ∀ w ∈ (Z' : Set V.toScheme), IsRegularLocalRing (V.toScheme.presheaf.stalk w ⧸
          (Scheme.IdealSheafData.vanishingIdeal (⟨Z', Z'.isClosed⟩ : Closeds V.toScheme)).stalkIdeal
            w) := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  set I := 𝓘[Z] with hI
  have hIsupp : (I.support : Set Y) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ Z.isIrreducible
  set ζ := genericPoint I.subscheme with hζ
  have hζx : I.subschemeι ζ = Z.isIrreducible.genericPoint := by
    have h1 : IsGenericPoint (I.subschemeι ζ) (Z : Set Y) := by
      change closure _ = _
      rw [MMP.Resolution.closure_subschemeι_genericPoint, hIsupp]
    exact h1.eq (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)
  set S := smoothLocus (I.subschemeι ≫ sY) with hS
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr inferInstance
  set T : Set Y := I.subschemeι '' (S : Set I.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    I.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : Z.isIrreducible.genericPoint ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (I.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  let V : Y.Opens := ⟨Tᶜ, hTc.isOpen_compl⟩
  refine ⟨V, hxT, fun Z' hZ' w hw => ?_⟩
  let J := I.comap V.ι
  have hJZ : J =
      Scheme.IdealSheafData.vanishingIdeal (⟨Z', Z'.isClosed⟩ : Closeds V.toScheme) := by
    have : IsReduced J.subscheme :=
      isReduced_of_isOpenImmersion ((I.comapIso V.ι).hom ≫ Limits.pullback.snd V.ι I.subschemeι)
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    rw [Scheme.IdealSheafData.support_comap]
    apply Closeds.ext
    rw [Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hZ'.symm
  rw [← hJZ, Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  have e : J.subschemeι ≫ V.ι = (I.comapIso V.ι).hom ≫
      Limits.pullback.snd V.ι I.subschemeι ≫ I.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  have hJsm : MMP.Mori.IsSmoothScheme (J.subschemeι ≫ V.ι ≫ sY) := by
    refine eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing _ y).mpr ?_
    set j := (I.comapIso V.ι).hom ≫ Limits.pullback.snd V.ι I.subschemeι with hj
    have hjy : I.subschemeι (j y) = V.ι (J.subschemeι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
    refine isRegularLocalRing_of_isOpenImmersion j y
      ((mem_smoothLocus_iff_isRegularLocalRing (I.subschemeι ≫ sY) _).mp ?_)
    by_contra hns
    exact (J.subschemeι y).2 ⟨j y, hns, hjy⟩
  have hwJ : w ∈ J.support := by
    rw [hJZ]
    change w ∈ ((Scheme.IdealSheafData.vanishingIdeal
      (⟨Z', Z'.isClosed⟩ : Closeds V.toScheme)).support : Set V.toScheme)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hw
  exact MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk (V.ι ≫ sY) J hJsm hwJ

/-- Restriction of `ℚ`-divisors to an open subscheme commutes with subtraction. -/
private theorem restrictOpen_sub {Y : Scheme.{u}} (V : Y.Opens) (P N : QDivisor Y) :
    (P - N).restrictOpen V = P.restrictOpen V - N.restrictOpen V :=
  Finsupp.ext fun _ => rfl

/-- Restriction of the zero divisor. -/
private theorem restrictOpen_zero {Y : Scheme.{u}} (V : Y.Opens) :
    (0 : QDivisor Y).restrictOpen V = 0 :=
  Finsupp.ext fun _ => rfl

/-- **Every stage restricts to a smooth stage**, on an open neighbourhood of `η_Z` on which `Z` is
regular; discrepancies and multiplicities are local. -/
private theorem Stage.smoothStage {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {μ q : ℚ} {m : ℕ} (h : Stage k μ q m) : SmoothStage k μ q m := by
  obtain ⟨Y, sY, _, _, _, hY, hYreg, n, K, P, N, hP, hN, Z, hZ, hmult, E, hE, hq, hm⟩ := h
  obtain ⟨V, hV, hVreg⟩ := exists_open_isRegularLocalRing_quotient sY hY Z
  have hη : E.f E.E.genericPoint ∈ V := hE ▸ hV
  have hVc : ((E.center : Set Y) ∩ V).Nonempty :=
    ⟨_, by rw [E.center_eq_closure_genericPoint]; exact subset_closure rfl, hη⟩
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  have hpair : ∀ {B : QDivisor Y} {a : ℚ}, MMP.Mori.IsDiscrepancy sY n K B E a →
      IsPairWith sY n K B := by
    rintro B a ⟨hX, hK, m₀, hm₀, hC, -⟩
    exact ⟨hX, hK, m₀, by exact_mod_cast hm₀.ne', hC⟩
  obtain ⟨hY₁, hf₁, E₁, hE₁, -, hiff₁⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff (hpair hq) E V hVc
  obtain ⟨hY₂, hf₂, E₂, hE₂, -, hiff₂⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff (hpair hm) E V hVc
  obtain rfl : E₁ = E₂ :=
    OpenWeilRestriction.primeDivisorMap_injective _ (hE₁.trans hE₂.symm)
  have hqV := (hiff₁ q).mp hq
  have hmV := (hiff₂ m).mp hm
  rw [restrictOpen_sub] at hqV
  rw [restrictOpen_zero] at hmV
  have hVv := isNormalVariety_ι hY V
  have : IsIntegral V.toScheme := hVv.1.toIsIntegral
  have : IsLocallyNoetherian V.toScheme := hVv.1.toLocallyOfFiniteType.isLocallyNoetherian
  have : IsNormal V.toScheme := hVv.2
  have hVreg' : ∀ y : V.toScheme, IsRegularLocalRing (V.toScheme.presheaf.stalk y) := fun y =>
    isRegularLocalRing_of_isOpenImmersion V.ι y (hYreg _)
  obtain ⟨Z', hZ', hZ'η, hZ'c, hsum⟩ := exists_irreducibleCloseds_restrict P Z V hV
  have hE' : (E.f ∣_ V) E₁.genericPoint = Z'.isIrreducible.genericPoint := by
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hZ'η, ← hE, ← hE₁,
      ← OpenWeilRestriction.genericPoint_primeDivisorMap]
  exact ⟨V.toScheme, V.ι ≫ sY, inferInstance, inferInstance, inferInstance, hVv, hVreg', n,
    K.restrictOpen V, P.restrictOpen V, N.restrictOpen V, fun Γ => hP _, fun Γ => hN _, Z',
    hZ'c.trans hZ, hVreg Z' hZ', hsum.le.trans hmult, ⟨_, E.f ∣_ V, hY₁, hf₁, E₁⟩, hE', hqV, hmV⟩

/-- **One blow-up step**: either the divisor `E` of a smooth stage is the exceptional divisor of
the blow-up of its centre, and then `1 - μ ≤ q`, or blowing up the centre gives a stage of smaller
measure. -/
private theorem SmoothStage.step {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {μ q : ℚ}
    {m : ℕ} (h : SmoothStage k μ q m) (hμ : μ ≤ 1) : 1 - μ ≤ q ∨ ∃ m' < m, Stage k μ q m' := by
  obtain ⟨Y, sY, _, _, _, hY, hYreg, n, K, P, N, hP, hN, Z, hZ, hZreg, hmult, E, hE, hq, hm⟩ := h
  by_cases hb : ∃ (D : DivisorOver k sY) (j : D.Y ⟶ Bl[Z]),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
        D.f D.E.genericPoint = Z.isIrreducible.genericPoint ∧ D.valuation = E.valuation
  · obtain ⟨D, j, hj, hjD, hD, hv⟩ := hb
    exact Or.inl (one_sub_le_of_valuation_eq_blowUp sY hY hN hZ (hYreg _) hmult E hE hq D j
      hjD hD hv)
  · exact Or.inr (exists_stage_blowUp sY hY hYreg hP hN hZ hZreg hμ hmult E hE hq hm hb)

/-- Every stage with `μ ≤ 1` has `1 - μ ≤ q`, by induction on the measure. -/
private theorem Stage.one_sub_le {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {μ q : ℚ} (hμ : μ ≤ 1) : ∀ {m : ℕ}, Stage k μ q m → 1 - μ ≤ q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    rcases h.smoothStage.step hμ with h' | ⟨m', hm', h'⟩
    · exact h'
    · exact ih m' hm' h'

/-- **The bound for the Kollár–Mori discrepancy.** -/
private theorem one_sub_mult_le_of_isDiscrepancy {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X} (hD : 0 ≤ D)
    (hKD : (Divisor.toQDivisor K + D).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (hmult : (D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ)) ≤ 1)
    (E : DivisorOver k sX) (hE : E.f E.E.genericPoint = W.isIrreducible.genericPoint) {q : ℚ}
    (hq : MMP.Mori.IsDiscrepancy sX n K D E q) :
    (1 - D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ)) ≤ q := by
  obtain ⟨m, hm⟩ := exists_stage hX hK hD hKD hW hreg E hE hq
  exact Stage.one_sub_le hmult hm

/-- **Discrepancies over a regular codimension-two point** (FA Exercise 4.9.1). Let `X` be a normal
variety of dimension `n` over an algebraically closed field `k` of characteristic zero, `K` a
canonical divisor, `D` an effective `ℚ`-divisor with `K + D` `ℚ`-Cartier, and `W ⊆ X` an
irreducible closed subset of codimension `2`
with `𝒪_{X,η_W}` regular and `mult_W(D) = ∑_Γ coeff_Γ(D) · mult_W Γ ≤ 1`. If `E` is a divisor over
`X` with center `W` and `a = a(E, X, D)`, then `1 - mult_W(D) ≤ a`. -/
@[mmp "lem_fa4_smooth_codim_two_discrepancy_bound"]
public theorem IsDiscrepancy.one_sub_le_of_isRegularLocalRing {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} {D : QDivisor X} (hD : 0 ≤ D)
    (hKD : (Divisor.toQDivisor K + D).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (hmult : (D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ)) ≤ 1)
    {E : ProperDivisorOver k sX} (hE : E.center = W) {a : ℝ}
    (h : IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a) :
    ((1 - D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ) : ℚ) : ℝ) ≤ a := by
  have hK : K.IsCanonicalDivisor sX n := h.1
  obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
    (⟨hX, n, K, hK, hKD⟩ : IsPair sX D) hK E.toDivisorOver
  obtain ⟨E₁, hE₁, hlog₁⟩ := exists_isLogDiscrepancy h
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hq E.isProper
  have heq : 1 + a = 1 + (q : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hlog hE₁
  have hb := one_sub_mult_le_of_isDiscrepancy hX hK hD hKD hW hreg hmult E.toDivisorOver
    (map_genericPoint_eq E hE) hq
  rw [show a = q by linarith]
  exact_mod_cast hb

end DiscrepancyBound

/-! ### Transport of a numerically trivial class across a log flip -/

section TransformRelation

open MMP.Fourfold

/-! ### Canonical divisors pushed forward to the base -/

section Forms

open MMP.Positivity

/-- **The push-forward of a canonical divisor is the divisor of a rational top form.** Let
`q : M ⟶ V` be a proper birational morphism of normal varieties of dimension `n` over a perfect
field and `K_M` a canonical divisor of `M`. Then `q_* K_M = div(τ)` for a nonzero rational
`n`-form `τ` on `V`. -/
private theorem exists_ordForm_eq_transformDivisor {k : Type u} [Field k] [PerfectField k]
    {M V : Scheme.{u}} [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {q : M ⟶ V}
    (hM : IsNormalVariety k (q ≫ sV)) [IsProper q] (hq : IsBirationalMorphism q)
    {n : ℕ} (hn : topologicalKrullDim V = n) {KM : Divisor M}
    (hKM : KM.IsCanonicalDivisor (q ≫ sV) n) :
    ∃ τ : RationalPluriForms sV n 1, τ ≠ 0 ∧ ∀ P : MMP.Mori.PrimeDivisor V,
      P.ordForm τ = (MMP.Mori.RationalMap.transformDivisor (X := M) q.toRationalMap KM :
        Divisor V) P := by
  have : IsDominant q := hq.isDominant
  have hbij := hq.functionFieldMap_bijective
  have : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q ≫ sV) := hM.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) hn
  let := functionFieldAlgebra sV
  let := functionFieldAlgebra (q ≫ sV)
  let := functionFieldMapAlgebra q
  have := isScalarTower_functionFieldMap sV q
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hM hKM
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sV q hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sV _ 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sV q τ = ω₁ := by
    change pullbackForms (K := V.functionField) (K' := M.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap q g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  have hτ0 : τ ≠ 0 := fun h0 => hω₁0 (by
    rw [← hpull, h0]
    change pullbackForms (K := V.functionField) (K' := M.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp)
  refine ⟨τ, hτ0, fun P => ?_⟩
  obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hV hM hq P
  rw [htr, ← ordForm_pullbackRationalPluriForms_of_isIso q hbij hd E P heq τ, hpull, hω₁]
  rfl

/-- **Divisors of rational top forms are linearly equivalent.** On a normal variety `V` of
dimension `n` over a perfect field, if `A = div(τ)` and `B = div(ω)` for nonzero rational
`n`-forms `τ`, `ω`, then `A ∼ B`: the forms differ by a rational function. -/
private theorem linearlyEquivalent_of_ordForm_eq {k : Type u} [Field k] [PerfectField k]
    {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV) {n : ℕ}
    (hn : topologicalKrullDim V = n) {A B : Divisor V} {τ ω : RationalPluriForms sV n 1}
    (hτ0 : τ ≠ 0) (hω0 : ω ≠ 0) (hτ : ∀ P : MMP.Mori.PrimeDivisor V, P.ordForm τ = A P)
    (hω : ∀ P : MMP.Mori.PrimeDivisor V, P.ordForm ω = B P) :
    A.LinearlyEquivalent B := by
  have : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sV) hn
  let := functionFieldAlgebra sV
  obtain ⟨b⟩ := exists_basis_topForms hV hn
  set c := (ZTensorPower.basis b 1).repr τ () with hc_def
  set cV := (ZTensorPower.basis b 1).repr ω () with hcV_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ0
  have hcV : cV ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hωeq : ω = (cV / c) • τ := by
    have h1 := basis_unit_repr_smul (ZTensorPower.basis b 1) ω
    have h2 := basis_unit_repr_smul (ZTensorPower.basis b 1) τ
    rw [← hc_def] at h2
    rw [← hcV_def] at h1
    conv_lhs => rw [← h1]
    conv_rhs => rw [← h2]
    erw [smul_smul, div_mul_cancel₀ _ hc]
    rfl
  obtain ⟨φ, hφ⟩ := exists_units_of_ne_zero (div_ne_zero hcV hc)
  refine ⟨φ⁻¹, Finsupp.ext fun P => ?_⟩
  have h1 := P.ordForm_smul hd (div_ne_zero hcV hc) hτ0
  rw [← hωeq, hω, hτ P, ← hφ P] at h1
  change _ = DivisorWithCoeffs.coeff (MMP.Mori.principalDivisor φ⁻¹) P
  rw [coeff_principalDivisor, PrimeDivisor.ord_inv, Finsupp.coe_sub, Pi.sub_apply]
  change _ = P.ord φ + _ at h1
  change A P - B P = _
  omega

end Forms

/-- The transform `θ_{i*} K_{X_i}` of the canonical divisor of `X_i` is linearly equivalent to
the chosen canonical divisor `K_{X_{i+1}}`. Both push forward to `Z_i` as divisors of rational top
forms, hence to linearly equivalent divisors, and `φ_i⁺` identifies the prime divisors of
`X_{i+1}` with those of `Z_i`. -/
private theorem linearlyEquivalent_transformDivisor_canonicalDivisor
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    Divisor.LinearlyEquivalent
      (MMP.Mori.RationalMap.transformDivisor (S.flipMap i) (S.model i).2.2.1)
      (S.model (i + 1)).2.2.1 := by
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  obtain ⟨hZ, hX, hX', hsm, hsm', hθ, hdim⟩ := flip_data S i hi
  have : IsIntegral (S.model i).1 := hX.1.toIsIntegral
  have : IsIntegral (S.model (i + 1)).1 := hX'.1.toIsIntegral
  have : IsIntegral (S.base i) := hZ.1.toIsIntegral
  have : CompactSpace (S.base i) := by
    have := hZ.1
    exact QuasiCompact.compactSpace_of_compactSpace (S.baseStr i)
  have : IsProper (S.contraction i) := hsm.isProper
  have : IsProper (S.flip i) := hsm'.isProper
  have hb := hsm.isBirationalMorphism
  have hb' := hsm'.isBirationalMorphism
  have : IsDominant (S.flip i) := hb'.isDominant
  have hYφ : IsNormalVariety k (S.contraction i ≫ S.baseStr i) := by rw [hsm.comp_eq]; exact hX
  have hYφp : IsNormalVariety k (S.flip i ≫ S.baseStr i) := by rw [hsm'.comp_eq]; exact hX'
  have hK : (S.model i).2.2.1.IsCanonicalDivisor (S.contraction i ≫ S.baseStr i) 3 := by
    rw [hsm.comp_eq]; exact S.isCanonicalDivisor_model i hi'
  have hK' : (S.model (i + 1)).2.2.1.IsCanonicalDivisor (S.flip i ≫ S.baseStr i) 3 := by
    rw [hsm'.comp_eq]; exact S.isCanonicalDivisor_model (i + 1) hi
  obtain ⟨τ, hτ0, hτ⟩ := exists_ordForm_eq_transformDivisor hZ hYφ hb hdim hK
  obtain ⟨τ', hτ'0, hτ'⟩ := exists_ordForm_eq_transformDivisor hZ hYφp hb' hdim hK'
  obtain ⟨c, hc⟩ := linearlyEquivalent_of_ordForm_eq hZ hdim hτ0 hτ'0 hτ hτ'
  have hc' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (S.flip i)
    (MMP.Mori.principalDivisor c)
  refine ⟨MMP.Mori.pullbackRationalFunction (S.flip i) c hc', Finsupp.ext fun P' => ?_⟩
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hsm' P'
  have hcQ := congrArg (fun D : Divisor (S.base i) => D Q) hc
  simp only [Finsupp.coe_sub, Pi.sub_apply] at hcQ ⊢
  rw [transformDivisor_apply_of_isOver hZ hX hX' hsm hsm' hθ hQ,
    ← transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hb' hQ (S.model (i + 1)).2.2.1,
    ← transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hb' hQ,
    MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hYφp hb' c hc']
  exact hcQ

/-- Transport across the flip: if `𝒪_{X_i}(L) ≅ φ_i^* 𝒪_{Z_i}(M)` with `M` Cartier, then for
every integer `c` the integral divisor `θ_{i*} L + c (θ_{i*} K_{X_i} - K_{X_{i+1}})` has
divisorial sheaf isomorphic to `φ_i⁺^* 𝒪_{Z_i}(M)`. -/
private theorem exists_transformDivisor_linearEquiv_pullback_flip
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (c : ℤ)
    (L : Divisor (S.model i).1) (M : Divisor (S.base i))
    (hM : haveI := S.isLocallyNoetherian_base i
      haveI := S.isNormal_base i
      M.IsCartier)
    (e : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.isLocallyNoetherian_base i
      haveI := S.isNormal_base i
      Nonempty (L.divisorialSheaf ≅
        (Scheme.Modules.pullback (S.contraction i)).obj M.divisorialSheaf)) :
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.isLocallyNoetherian_base i
    haveI := S.isNormal_base i
    ∃ D : Divisor (S.model (i + 1)).1,
      Divisor.toQDivisor D = MMP.Mori.RationalMap.transformDivisor (S.flipMap i)
          (Divisor.toQDivisor L) + (c : ℚ) • (MMP.Mori.RationalMap.transformDivisor (S.flipMap i)
          (Divisor.toQDivisor (S.model i).2.2.1) - Divisor.toQDivisor (S.model (i + 1)).2.2.1) ∧
      Nonempty (D.divisorialSheaf ≅
        (Scheme.Modules.pullback (S.flip i)).obj M.divisorialSheaf) := by
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  set θ := S.flipMap i
  set N := MMP.Mori.RationalMap.transformDivisor θ (S.model i).2.2.1 - (S.model (i + 1)).2.2.1
  have hlin : Divisor.LinearlyEquivalent (MMP.Mori.RationalMap.transformDivisor θ L + c • N)
      (MMP.Mori.RationalMap.transformDivisor θ L) := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range, add_sub_cancel_left]
    exact AddSubgroup.zsmul_mem _
      ((Divisor.linearlyEquivalent_iff_sub_mem_range).1
        (linearlyEquivalent_transformDivisor_canonicalDivisor S i hi)) c
  obtain ⟨e'⟩ := nonempty_divisorialSheaf_transformDivisor_iso_pullback_flip S i hi L M hM e
  refine ⟨_ + c • N, ?_, ⟨hlin.divisorialSheafIso ≪≫ e'⟩⟩
  simp only [N, map_add, map_zsmul, map_sub, transformDivisor_toQDivisor, Int.cast_smul_eq_zsmul]

/-- In a sequence of log flips `S`, let `i + 1 < L` with `X_i` `ℚ`-factorial, `G` a `ℚ`-divisor on
`X_i`, `C` a flipping curve of `φ_i = S.contraction i` and `μ ∈ ℚ` with
`G · C = μ (K_{X_i} + B_i) · C`. Then there are `m > 0`, a Weil divisor `D` on `X_{i+1}` with
`D = m (θ_{i*} G - μ (K_{X_{i+1}} + B_{i+1}))`, `θ_i = S.flipMap i`, and a Cartier divisor `M` on
`Z_i` with `𝒪_{X_{i+1}}(D) ≅ φ_i⁺^* 𝒪_{Z_i}(M)` for `φ_i⁺ = S.flip i`. -/
@[mmp "lem_fa7_flip_transform_relation"]
public theorem SequenceOfLogFlips.exists_smul_transformDivisor_sub_linearEquiv_pullback
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (hQ : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      MMP.Fourfold.IsQFactorial (S.model i).2.1)
    (G : QDivisor (S.model i).1) (C : ProperCurve (S.model i).2.1)
    (hC : IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i)
      (closure {C.point})) (μ : ℚ)
    (hGC : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
      ∃ (hG : G.IsQCartier)
        (hKB : (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).IsQCartier),
        G.intersectionNumber k (S.model i).2.1 C.ι C.dim_le hG =
          μ * (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).intersectionNumber
            k (S.model i).2.1 C.ι C.dim_le hKB) :
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.isLocallyNoetherian_base i
    haveI := S.isNormal_base i
    ∃ m : ℕ, 0 < m ∧ ∃ (D : Divisor (S.model (i + 1)).1) (M : Divisor (S.base i)),
      M.IsCartier ∧
      Divisor.toQDivisor D = (m : ℚ) • (Mori.RationalMap.transformDivisor (S.flipMap i) G -
        μ • (Divisor.toQDivisor (S.model (i + 1)).2.2.1 + (S.model (i + 1)).2.2.2)) ∧
      Nonempty (D.divisorialSheaf ≅
        (Scheme.Modules.pullback (S.flip i)).obj M.divisorialSheaf) := by
  have : PerfectField k := PerfectField.ofCharZero
  obtain ⟨m, hm, ⟨a, ha⟩, L, M, hM, hL, e⟩ :=
    exists_smul_sub_linearEquiv_pullback_contraction S i hi hQ G C hC μ hGC
  obtain ⟨D, hD, e'⟩ := exists_transformDivisor_linearEquiv_pullback_flip S i hi a L M hM e
  refine ⟨m, hm, D, M, hM, ?_, e'⟩
  have hT (E : QDivisor (S.model i).1) : MMP.Mori.RationalMap.transformDivisor (S.flipMap i) E =
      MMP.Mori.RationalMap.transformDivisorₗ ℚ (S.flipMap i) E := rfl
  rw [hD, hL, S.transform_eq i hi, ← ha]
  simp only [hT, map_smul, map_sub, map_add, smul_sub, smul_add, mul_smul]
  abel

end TransformRelation

end MMP.Flips

end
