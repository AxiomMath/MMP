module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcVerticalNegativeRay
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Projective crepant dlt modifications from the floor-program inputs

Assume the projective floor-program inputs `P(n)` (`MMP.Fourfold.ProjectiveFloorProgramInputs`)
for some `n ≥ 3`. Let `(X, Δ)` be a rational log canonical pair
(`MMP.Intersection.IsLogCanonicalPair`) on a normal projective complex `n`-fold `X`. Then there is
a projective birational morphism `p : V ⟶ X` from a `ℚ`-factorial variety `V` and an effective
rational dlt boundary `Δ_V` (`MMP.Intersection.IsDltPair`) with `K_V + Δ_V = p^*(K_X + Δ)`, such
that every `p`-exceptional prime divisor `E` of `V` has log discrepancy `a(E; X, Δ) = 0` and
coefficient one in `Δ_V`.

On a projective log resolution `g : Y ⟶ X`, the boundary `Γ` given by the strict transform of `Δ`
plus every exceptional prime with coefficient one is snc and dlt, and
`K_Y + Γ = g^*(K_X + Δ) + F` with `F = ∑ a(E; X, Δ) E` over the exceptional primes; `F` is
effective because `(X, Δ)` is log canonical, and every prime in its positive support has
coefficient one in `Γ`. The dlt program of `K_Y + Γ` over `X` runs: at a non-nef stage the
remainder `F` is negative on the extremal ray, so some reduced component of `Γ` in its positive
support is; the resulting floor flips are supplied and terminated by `P(n)`, and a divisorial
contraction contracts only primes of the positive support of `F`, by the negativity lemma, so that
the number of exceptional valuations drops. On the final model `F` is effective, exceptional and
nef over `X`, hence zero: the model is crepant, and each surviving exceptional prime has log
discrepancy zero and coefficient one.

## Main results

* `MMP.Fourfold.ProjectiveFloorProgramInputs.exists_crepant_dltModification`: the modification.

## Implementation notes

* `K_V + Δ_V = p^*(K_X + Δ)` is `MMP.Mori.IsCrepantBoundary`, asserted for every canonical
  divisor `K_X` of `X`. Effectivity of `Δ_V` is part of `MMP.Intersection.IsDltPair`.
* A `p`-exceptional prime divisor of `V` is one that `p` contracts
  (`MMP.Mori.RationalMap.IsExceptional`), and its log discrepancy is that of the divisor
  `(V, p, E)` over `X`.
* The models of the program prescribe their coefficients relative to a finite set `𝓔` of
  exceptional valuations, which receive coefficient `1 - a(E; X, Δ)` instead of `1`; this is the
  program of the specified extraction. Here it runs with `𝓔 = ∅`, so that every exceptional prime
  of a model has coefficient one. Termination of divisorial steps is measured by the number of
  exceptional valuations realised on the model, which a divisorial contraction lowers.

## References

* [OAI4] the fourfold source, *Projective crepant dlt modification*.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.Fourfold

section Program

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of ℂ)) (Δ : QDivisor X)
  (𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))

/-- The coefficient `c` prescribed at a divisor `D` over `X`: the coefficient of `Δ` at the
image when `D` is not exceptional over `X`; `1 - a(D; X, Δ)` when `D` is exceptional with
valuation in `𝓔`; and `1` otherwise. -/
private def IsPrescribedCoeff (D : DivisorOver ℂ sX) (c : ℚ) : Prop :=
  (∃ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint = Q.genericPoint ∧ c = Δ.coeff Q) ∨
    ((∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint) ∧
      ((D.valuation ∈ 𝓔 ∧ IsValuationLogDiscrepancy sX Δ D.valuation (1 - c)) ∨
        (D.valuation ∉ 𝓔 ∧ c = 1)))

/-- A *model* of the program over `X`: a projective `ℚ`-factorial dlt pair `(U, Γ)` of
dimension `n`, projective and birational over `X`, whose coefficients are the prescribed ones,
on which every valuation of `𝓔` is a prime divisor, and whose exceptional prime divisors have
valuations in the finite set `S₀`. -/
private structure Model (n : ℕ)
    (S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))
    where
  U : Scheme.{0}
  [isIntegral : IsIntegral U]
  [compactSpace : CompactSpace U]
  [isLocallyNoetherian : IsLocallyNoetherian U]
  [isNormal : IsNormal U]
  π : U ⟶ X
  K : Divisor U
  Γ : QDivisor U
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ (π ≫ sX)
  dim_eq : topologicalKrullDim U = n
  isQFactorial : IsQFactorial (π ≫ sX)
  isCanonicalDivisor : K.IsCanonicalDivisor (π ≫ sX) n
  isDltPair : MMP.Intersection.IsDltPair (π ≫ sX) Γ
  isProjectiveMorphism : IsProjectiveMorphism π
  isBirationalMorphism : IsBirationalMorphism π
  coeff_spec : ∀ F : MMP.Mori.PrimeDivisor U,
    IsPrescribedCoeff sX Δ 𝓔 ⟨U, π, isQFactorial.1, isBirationalMorphism, F⟩ (Γ.coeff F)
  surv : ∀ s ∈ 𝓔, ∃ F : MMP.Mori.PrimeDivisor U,
    (⟨U, π, isQFactorial.1, isBirationalMorphism, F⟩ : DivisorOver ℂ sX).valuation = s
  exc_mem : ∀ F : MMP.Mori.PrimeDivisor U, (∀ Q : MMP.Mori.PrimeDivisor X,
    π F.genericPoint ≠ Q.genericPoint) →
    (⟨U, π, isQFactorial.1, isBirationalMorphism, F⟩ : DivisorOver ℂ sX).valuation ∈ S₀

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

variable {sX Δ 𝓔} {n : ℕ} {S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The valuations of `S₀` realised by exceptional prime divisors of a model. -/
private noncomputable def Model.excVals (M : Model sX Δ 𝓔 n S₀) :
    Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))) := by
  classical
  exact S₀.filter fun v => ∃ F : MMP.Mori.PrimeDivisor M.U,
    (∀ Q : MMP.Mori.PrimeDivisor X, M.π F.genericPoint ≠ Q.genericPoint) ∧
      (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, F⟩ : DivisorOver ℂ sX).valuation = v

/-- The adjoint `K_U + Γ` of a model is nef over `X`. -/
private def Model.IsNef (M : Model sX Δ 𝓔 n S₀) : Prop :=
  QDivisor.IsRelativelyNef (M.π ≫ sX) M.π (Divisor.toQDivisor M.K + M.Γ)

/-- `M'` is obtained from `M` by a flip of a floor flipping contraction, in the form of the
termination clause of `P(n)`. -/
private def Model.IsFlipStep (M M' : Model sX Δ 𝓔 n S₀) : Prop :=
  ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses (M.π ≫ sX)))
    (f : M.U ⟶ Z) (fp : M'.U ⟶ Z),
    IsFloorFlippingContraction (M.π ≫ sX) sZ M.K M.Γ R f ∧
      MMP.Mori.IsFlip (M.π ≫ sX) sZ (M'.π ≫ sX) M.K M.Γ f fp ∧
      M'.K = flipTransform f fp M.K ∧ M'.Γ = flipTransform f fp M.Γ

end Program

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

/- ### Tools for the steps -/

section StepTools

/-- The identity of a normal variety is a small morphism. -/
private theorem isSmallMorphism_id {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) : IsSmallMorphism sZ sZ (𝟙 Z) where
  isNormalVariety_source := hZ
  isNormalVariety_target := hZ
  comp_eq := Category.id_comp _
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso _
  two_le_codimension := by
    rw [(exceptionalSet_eq_bot_iff (𝟙 Z)).mpr inferInstance, le_closedsCodimension_iff]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hW hx) (by simp)

/-- Divisors over `X` through `Z` with the same valuation over `Z` have the same valuation over
`X`. -/
private theorem valuation_eq_of_valuationOver_eq {X U U' Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U']
    [IsNormal U'] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} (f : U ⟶ Z) (fp : U' ⟶ Z) (g : Z ⟶ X)
    [IsDominant f] [IsDominant fp] [IsDominant g] {π : U ⟶ X} {π' : U' ⟶ X} (hπ : f ≫ g = π)
    (hπ' : fp ≫ g = π') (hU : IsNormalVariety ℂ (π ≫ sX)) (hU' : IsNormalVariety ℂ (π' ≫ sX))
    (hb : IsBirationalMorphism π) (hb' : IsBirationalMorphism π')
    {F : MMP.Mori.PrimeDivisor U} {F' : MMP.Mori.PrimeDivisor U'}
    (h : F.valuationOver f = F'.valuationOver fp) :
    (⟨U, π, hU, hb, F⟩ : DivisorOver ℂ sX).valuation =
      (⟨U', π', hU', hb', F'⟩ : DivisorOver ℂ sX).valuation := by
  subst hπ hπ'
  haveI : IsDominant (f ≫ g) := hb.isDominant
  haveI : IsDominant (fp ≫ g) := hb'.isDominant
  ext t
  have h' := congrArg (fun v => v (functionFieldMap g t)) h
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply] at h'
  change F.divisorialValuation (functionFieldMap (f ≫ g) t) =
    F'.divisorialValuation (functionFieldMap (fp ≫ g) t)
  rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply f g,
    ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply fp g]
  exact h'

/-- **Prime divisors across a step.** For `f : U ⟶ Z` proper birational and `f⁺ : U' ⟶ Z`
small, every prime divisor `F'` of `U'` is the strict transform of a prime divisor `F` of `U`
with the same valuation over `X`, and `coeff_{F'} (f⁺)⁻¹_* f_* D = coeff_F D`. -/
private theorem exists_primeDivisor_of_step {X U U' Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U']
    [IsNormal U'] {sX : X ⟶ Spec (.of ℂ)} {sU' : U' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (f : U ⟶ Z) [IsProper f] (hf : IsBirationalMorphism f) {fp : U' ⟶ Z}
    (hfp : IsSmallMorphism sU' sZ fp) (g : Z ⟶ X) {π : U ⟶ X} {π' : U' ⟶ X}
    (hπ : f ≫ g = π) (hπ' : fp ≫ g = π') (hU : IsNormalVariety ℂ (π ≫ sX))
    (hU' : IsNormalVariety ℂ (π' ≫ sX)) (hb : IsBirationalMorphism π)
    (hb' : IsBirationalMorphism π') (F' : MMP.Mori.PrimeDivisor U') :
    ∃ (F : MMP.Mori.PrimeDivisor U) (Q : MMP.Mori.PrimeDivisor Z),
      (⟨U, π, hU, hb, F⟩ : DivisorOver ℂ sX).valuation =
        (⟨U', π', hU', hb', F'⟩ : DivisorOver ℂ sX).valuation ∧
      f F.genericPoint = Q.genericPoint ∧ fp F'.genericPoint = Q.genericPoint ∧
      ∀ (D : QDivisor U), flipTransform f fp D F' = D F := by
  have hZ := hfp.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI := hf.isDominant
  haveI := hfp.isBirationalMorphism.isDominant
  haveI : IsDominant g := by
    have : IsDominant (f ≫ g) := by rw [hπ]; exact hb.isDominant
    exact IsDominant.of_comp f g
  obtain ⟨Pm, Q, hv, hPm, hF'⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hf
    hfp F'
  have h1 := map_genericPoint_eq_of_image_eq Pm Q hPm
  have h2 := map_genericPoint_eq_of_image_eq F' Q hF'
  obtain ⟨Pm', hx, hcoeff⟩ := exists_eq_genericPoint_flipTransform_apply hf hfp F'
    Pm.genericPoint (h1.trans h2.symm)
  have : Pm' = Pm := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hx.symm
  subst this
  exact ⟨Pm', Q, valuation_eq_of_valuationOver_eq f fp g hπ hπ' hU hU' hb hb' hv, h1, h2, hcoeff⟩

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : X ⟶ Y` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `Y`. -/
private theorem exists_primeDivisor_isIso_stalkMap {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- **A prime divisor over a prime divisor of `Z`.** If `f(η_F) = η_Q` for a prime divisor `Q`
of `Z`, then `f⁺ : U' ⟶ Z` (proper birational) has a prime divisor `F'` over `Q`, with the same
valuation over `X` as `F`. -/
private theorem exists_primeDivisor_of_map_genericPoint {X U U' Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U']
    [IsNormal U'] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of ℂ)} (f : U ⟶ Z) (hf : IsBirationalMorphism f) (fp : U' ⟶ Z) [IsProper fp]
    (hfp : IsBirationalMorphism fp) (g : Z ⟶ X) {π : U ⟶ X} {π' : U' ⟶ X}
    (hπ : f ≫ g = π) (hπ' : fp ≫ g = π') (hU : IsNormalVariety ℂ (π ≫ sX))
    (hU' : IsNormalVariety ℂ (π' ≫ sX)) (hb : IsBirationalMorphism π)
    (hb' : IsBirationalMorphism π') (F : MMP.Mori.PrimeDivisor U) (Q : MMP.Mori.PrimeDivisor Z)
    (hQ : f F.genericPoint = Q.genericPoint) :
    ∃ F' : MMP.Mori.PrimeDivisor U', fp F'.genericPoint = Q.genericPoint ∧
      (⟨U, π, hU, hb, F⟩ : DivisorOver ℂ sX).valuation =
        (⟨U', π', hU', hb', F'⟩ : DivisorOver ℂ sX).valuation := by
  haveI := hf.isDominant
  haveI := hfp.isDominant
  haveI : IsDominant g := by
    have : IsDominant (f ≫ g) := by rw [hπ]; exact hb.isDominant
    exact IsDominant.of_comp f g
  obtain ⟨F', hF', hiso'⟩ := exists_primeDivisor_isIso_stalkMap fp hfp Q
  haveI := hiso'
  haveI := isIso_stalkMap_of_map_eq_genericPoint hf hQ
  refine ⟨F', hF', valuation_eq_of_valuationOver_eq f fp g hπ hπ' hU hU' hb hb' ?_⟩
  rw [MMP.Fourfold.Oai4C1.valuationOver_eq_of_isIso f F Q hQ,
    MMP.Fourfold.Oai4C1.valuationOver_eq_of_isIso fp F' Q hF']

/-- **The strict transform of a canonical divisor across a small morphism is canonical.** For
`f : U ⟶ Z` proper birational and `f⁺ : U' ⟶ Z` small, `(f⁺)⁻¹_* f_* K` is a canonical divisor
of `U'`: `f_* K` is a canonical divisor of `Z`, which is `f⁺_* K'` for a canonical divisor `K'`,
and `f⁺` identifies the prime divisors of `U'` and `Z`. -/
private theorem isCanonicalDivisor_flipTransform {U U' Z : Scheme.{0}}
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U'] [IsNormal U']
    {sU : U ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sU' : U' ⟶ Spec (.of ℂ)}
    (hU : IsNormalVariety ℂ sU) {f : U ⟶ Z} [IsProper f] (hf : IsBirationalMorphism f)
    (hfs : f ≫ sZ = sU) {fp : U' ⟶ Z} (hfp : IsSmallMorphism sU' sZ fp) {n : ℕ}
    {K : Divisor U} (hK : K.IsCanonicalDivisor sU n) :
    Divisor.IsCanonicalDivisor sU' n (flipTransform f fp K) := by
  have hZ := hfp.isNormalVariety_target
  have hU' := hfp.isNormalVariety_source
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isBirationalMorphism.isDominant
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ sU := hU.1
  haveI : MMP.Mori.IsVariety ℂ sU' := hU'.1
  have hdimZ : topologicalKrullDim Z = n := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sU hf]; exact hK.1
  have hdimU' : topologicalKrullDim U' = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sU'
      hfp.isBirationalMorphism]
    exact hdimZ
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sZ hZ hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sU' hU' hdimU'
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rwa [hfs]
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rwa [hfp.comp_eq]
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sZ) n := by rwa [hfs]
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sZ) n := by rwa [hfp.comp_eq]
  have h1 := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZ hXn hf hKZ hK1
  obtain ⟨KY, hKY, hKYeq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hZ hX'n
      hfp.isBirationalMorphism h1 hK₀'
  have heq : flipTransform f fp K = flipTransform fp fp KY := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, hKYeq]
  have hid : flipTransform fp fp KY = KY := by
    ext P
    obtain ⟨Pm, hx, hc⟩ := exists_eq_genericPoint_flipTransform_apply
      hfp.isBirationalMorphism hfp P P.genericPoint rfl
    have : Pm = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hx.symm
    subst this
    exact hc KY
  rw [heq, hid]
  rw [hfp.comp_eq] at hKY
  exact hKY

end StepTools

/- ### The final model -/

section Conclusion

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X}
  {𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))} {n : ℕ}
  {S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- A pair on an `n`-dimensional variety has a canonical divisor of dimension `n`. -/
private theorem exists_isCanonicalDivisor_of_isPair (hP : MMP.Mori.IsPair sX Δ)
    (hdim : topologicalKrullDim X = n) : ∃ K : Divisor X, K.IsCanonicalDivisor sX n := by
  obtain ⟨-, n₀, K, hK, -⟩ := hP
  obtain rfl : n₀ = n := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hdim
  exact ⟨K, hK⟩

/-- A pair is a pair with every canonical divisor: canonical divisors of a normal variety are
linearly equivalent. -/
private theorem isPairWith_of_isPair [CompactSpace X] (hP : MMP.Mori.IsPair sX Δ)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) : IsPairWith sX n K Δ := by
  obtain ⟨hX, n₀, K₀, hK₀, hQ⟩ := hP
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn : n₀ = n := by
    have := hK₀.topologicalKrullDim_eq.symm.trans hK.topologicalKrullDim_eq
    exact_mod_cast this
  subst hn
  obtain ⟨ω, hω, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω₀, hω₀, hωK₀⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK₀
  have e1 : divisorOfForm ω = K := Finsupp.ext hωK
  have e0 : divisorOfForm ω₀ = K₀ := Finsupp.ext hωK₀
  have hlin : K₀.LinearlyEquivalent K := by
    rw [← e1, ← e0]
    exact Divisor.linearlyEquivalent_divisorOfForm hX hK.1 hω₀ hω
  exact ⟨hX, hK, hQ.add_of_linearlyEquivalent hlin⟩

/-- **The coefficient of `Γ - Δ_Y` at a prescribed divisor.** For a divisor `D` over `X`, with
`D.f` proper, carrying the prescribed coefficient `c` and with discrepancy `a = a(D; X, Δ)`,
`c + a` (the coefficient of `Γ - Δ_Y`, `Δ_Y` the crepant boundary) is zero unless `D` is
exceptional with valuation outside `𝓔`, where it is the log discrepancy, non-negative since
`(X, Δ)` is log canonical. -/
private theorem add_eq_zero_or_nonneg_of_isPrescribedCoeff [CompactSpace X]
    (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) {c a : ℚ}
    (hc : IsPrescribedCoeff sX Δ 𝓔 D c) (ha : IsDiscrepancy sX n K Δ D a) :
    (c + a = 0 ∧ ¬ ((∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint) ∧
        D.valuation ∉ 𝓔)) ∨
      (0 ≤ c + a ∧ (∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint) ∧
        D.valuation ∉ 𝓔) := by
  have hP : MMP.Mori.IsPair sX Δ := hΔ.1
  have hX : IsNormalVariety ℂ sX := hP.1
  rcases hc with ⟨Q, hQ, rfl⟩ | ⟨hexc, ⟨hs, hlog⟩ | ⟨hs, rfl⟩⟩
  · left
    refine ⟨?_, fun h => h.1 Q hQ⟩
    rw [IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq hQ ha]
    ring
  · left
    refine ⟨?_, fun h => h.2 hs⟩
    obtain ⟨n', D', hD', hv, hlog⟩ := hlog
    have hn : n' = n := by
      obtain ⟨-, -, -, -, ⟨K', hK', -⟩, -⟩ := hlog
      have := hK'.topologicalKrullDim_eq.symm.trans hK.topologicalKrullDim_eq
      exact_mod_cast this
    subst hn
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D'
    have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hlog
    have h2 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq (isPairWith_of_isPair hP hK)
      hv ha' ha
    have h3 : ((c + a : ℚ) : ℝ) = 0 := by push_cast; rw [← h2]; linarith
    exact_mod_cast h3
  · right
    refine ⟨?_, hexc, hs⟩
    have hlog := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha
      (1 + (a : ℝ))).mpr ⟨hD, rfl⟩
    have := hΔ.2.2 n D _ hlog
    have h3 : (0 : ℝ) ≤ ((1 + a : ℚ) : ℝ) := by push_cast; exact this
    exact_mod_cast h3

/-- **The final model is crepant.** On a model whose adjoint is nef over `X`, `Γ - Δ_U` (with
`Δ_U` the crepant boundary of `(X, Δ)`) is effective, exceptional and nef over `X`, hence zero by
the negativity lemma: `Γ` is the crepant boundary. -/
private theorem Model.isCrepantBoundary_of_isNef (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) (hM : M.IsNef) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    IsCrepantBoundary sX n K Δ M.π M.isQFactorial.1 M.isBirationalMorphism M.Γ := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1
  have hX : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set U := M.U
  set πU := M.π
  have hUnv : IsNormalVariety ℂ (πU ≫ sX) := M.isQFactorial.1
  have hbirU := M.isBirationalMorphism
  have : IsProper πU := isProper_of_isProjectiveMorphism πU M.isProjectiveMorphism
  obtain ⟨ΔU, hΔU, -⟩ := (hPB.existsUnique_isCrepantBoundary hK πU hUnv hbirU).1
  -- the crepant boundary of `(U, Γ)` on itself is `Γ`
  have hPU : MMP.Mori.IsPair (πU ≫ sX) M.Γ := M.isDltPair.1.1
  have hUnv' : IsNormalVariety ℂ (𝟙 U ≫ πU ≫ sX) := by simpa using hUnv
  obtain ⟨ΔZ', hΔZ', -⟩ := (hPU.existsUnique_isCrepantBoundary M.isCanonicalDivisor (𝟙 U) hUnv'
    (isBirationalMorphism_of_isIso _)).1
  have hΔZ'eq : ΔZ' = M.Γ := by
    ext F
    have := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq (P := F)
      (D := ⟨U, 𝟙 U, hUnv', isBirationalMorphism_of_isIso _, F⟩) (by simp) (hΔZ' F)
    change ΔZ'.coeff F = M.Γ.coeff F
    linarith
  haveI : QuasiCompact (πU ≫ sX) := hUnv.1.toQuasiCompact
  have hN : QDivisor.IsRelativelyNef sX (𝟙 X) (-(Divisor.toQDivisor K + Δ)) :=
    ⟨QDivisor.IsQCartier.neg (isPairWith_of_isPair hPB hK).2.2,
      fun C hC => absurd hC (ProperCurve.not_isContractedBy_id C)⟩
  have hnefG := IsCrepantBoundary.isRelativelyNef_sub (X := X) (X' := U) (Y := X) (Z := U)
    hX hUnv hX (f := 𝟙 X) (f' := πU) (Category.id_comp _) rfl
    (isBirationalMorphism_of_isIso _) hbirU hK M.isCanonicalDivisor hN hM (g := πU) (g' := 𝟙 U)
    hUnv hUnv' hbirU (isBirationalMorphism_of_isIso _) (by simp) hΔU hΔZ'
  rw [hΔZ'eq, Category.comp_id] at hnefG
  -- the coefficients of `Γ - Δ_U`
  have hcoeff := fun F : MMP.Mori.PrimeDivisor U =>
    add_eq_zero_or_nonneg_of_isPrescribedCoeff hΔ hK ⟨U, πU, hUnv, hbirU, F⟩ ‹_› (M.coeff_spec F)
      (hΔU F)
  set G : QDivisor U := M.Γ - ΔU with hGdef
  have hGF : ∀ F, G.coeff F = M.Γ.coeff F + -ΔU.coeff F := fun F => by
    change M.Γ.coeff F - ΔU.coeff F = _; ring
  have hGeff : G.IsEffective := by
    intro F
    rw [hGF]
    rcases hcoeff F with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.ge
    · exact h
  have hGexc : ∀ F : MMP.Mori.PrimeDivisor U,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor sX πU F → G.coeff F = 0 := by
    intro F hF'
    have hnot : ¬ (MMP.Flips.ProperDivisorOver.mk ⟨U, πU, hUnv, hbirU, F⟩ inferInstance :
        MMP.Flips.ProperDivisorOver ℂ sX).IsExceptional :=
      fun h => hF' ⟨hUnv, hbirU, inferInstance, h⟩
    obtain ⟨Q, -, hQ, -⟩ := MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional
      hX _ hnot
    rw [hGF]
    rcases hcoeff F with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd hQ (h Q)
  have hG0 : G = 0 :=
    MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef ℂ sX (πU ≫ sX) hX hUnv πU rfl
      hbirU (MMP.Fourfold.isQCartier_of_isQFactorial _ M.isQFactorial G) hGexc hGeff hnefG
  have hΓΔ : M.Γ = ΔU := sub_eq_zero.mp hG0
  exact hΓΔ ▸ hΔU

/-- A divisor over a normal variety is exceptional exactly when its centre is not a prime
divisor. -/
private theorem isExceptional_iff_forall_ne (hX : IsNormalVariety ℂ sX) (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ ∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint := by
  rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D]
  have := D.isIntegral
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ (D.f ≫ sX) := D.isNormalVariety.1
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (D.f ≫ sX)
    D.isBirationalMorphism
  have h1 : 1 ≤ Order.coheight (D.f D.E.genericPoint) := by
    have := MMP.Flips.coheight_le_coheight_map sX (D.f ≫ sX) hX.1 D.isNormalVariety.1 D.f rfl
      hdim.symm D.E.genericPoint
    rwa [D.E.coheight_genericPoint] at this
  refine ⟨fun h Q hQ => ?_, fun h => ?_⟩
  · rw [hQ, Q.coheight_genericPoint] at h
    exact absurd h (by decide)
  · by_contra hlt
    have h2 : Order.coheight (D.f D.E.genericPoint) = 1 :=
      le_antisymm (not_lt.mp fun h3 => hlt (Order.add_one_le_of_lt h3)) h1
    exact h (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h2)
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm

/-- Two prime divisors of one birational model with the same valuation are equal. -/
private theorem eq_of_valuation_eq {U : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U]
    [IsNormal U] (π : U ⟶ X) (hU : IsNormalVariety ℂ (π ≫ sX)) (hb : IsBirationalMorphism π)
    {F F' : MMP.Mori.PrimeDivisor U}
    (h : (⟨U, π, hU, hb, F⟩ : DivisorOver ℂ sX).valuation =
      (⟨U, π, hU, hb, F'⟩ : DivisorOver ℂ sX).valuation) : F = F' := by
  haveI := hb.isDominant
  have hU' : IsNormalVariety ℂ (𝟙 U ≫ π ≫ sX) := by simpa using hU
  have hv : (⟨U, 𝟙 U, hU', isBirationalMorphism_of_isIso _, F⟩ :
        DivisorOver ℂ (π ≫ sX)).valuation =
      (⟨U, 𝟙 U, hU', isBirationalMorphism_of_isIso _, F'⟩ : DivisorOver ℂ (π ≫ sX)).valuation := by
    ext t
    obtain ⟨s, rfl⟩ := hb.functionFieldMap_bijective.2 t
    have h' := congrArg (fun v => v s) h
    change F.divisorialValuation (functionFieldMap (𝟙 U) (functionFieldMap π s)) =
      F'.divisorialValuation (functionFieldMap (𝟙 U) (functionFieldMap π s))
    simp only [functionFieldMap_id_apply]
    exact h'
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hU.1 hv
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

end Conclusion

/- ### The remainder `Γ - Δ_U` -/

section Remainder

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X}
  {𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))} {n : ℕ}
  {S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- **`K_U + Δ_U` is numerically trivial over `X`.** If `Δ_U` is the crepant boundary of
`(X, Δ)` on `U` and `K_U` is a canonical divisor of `U`, then `((K_U + Δ_U) · C) = 0` for every
curve `C` contracted by `π`: `K_U + Δ_U` is linearly equivalent to `π^*(K_X + Δ)`. -/
private theorem intersectionNumber_eq_zero_of_isCrepantBoundary [CompactSpace X]
    {U : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    (hX : IsNormalVariety ℂ sX) (π : U ⟶ X) [IsProper π] (hU : IsNormalVariety ℂ (π ≫ sX))
    (hb : IsBirationalMorphism π) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hQ : (Divisor.toQDivisor K + Δ).IsQCartier) {ΔU : QDivisor U}
    (hΔU : IsCrepantBoundary sX n K Δ π hU hb ΔU) {KU : Divisor U}
    (hKU : KU.IsCanonicalDivisor (π ≫ sX) n) (hQU : (Divisor.toQDivisor KU + ΔU).IsQCartier)
    (C : ProperCurve (π ≫ sX)) (hC : C.IsContractedBy π) :
    (Divisor.toQDivisor KU + ΔU).intersectionNumber ℂ (π ≫ sX) C.ι C.dim_le hQU = 0 := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (π ≫ sX) := hU.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : QuasiCompact (π ≫ sX) := hU.1.toQuasiCompact
  haveI : IsDominant π := hb.isDominant
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : AlgebraicGeometry.IsVariety ℂ (π ≫ sX) := hU.1
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hLB : ∀ W : irreducibleComponents U, π (componentGenericPoint U W) ∉
      (Divisor.toQDivisor K + Δ).supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hpb := IsCrepantBoundary.isPullback_divisorOfForm_add hX hU hb hK hΔU hω0 hωK hLB
  have hB := hpb.isQCartier hQ
  have hzero : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) +
      ΔU).intersectionNumber ℂ (π ≫ sX) C.ι C.dim_le hB = 0 := by
    rcases QDivisor.intersectionNumber_pullback_eq_zero_or π rfl (𝟙 X) hQ hpb hB C
        (by rw [Category.comp_id]; exact hC) with h0 | ⟨d, -, C'', hC'', -⟩
    · exact h0
    · exact absurd hC'' (ProperCurve.not_isContractedBy_id C'')
  have hne : pullbackRationalPluriForms sX π ω ≠ 0 :=
    MMP.Mori.pullbackRationalPluriForms_ne_zero hX hb hK.1 hω0
  obtain ⟨τ, hτ0, hτK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hU hKU
  have hτ : divisorOfForm τ = KU := Finsupp.ext hτK
  have hlin : KU.LinearlyEquivalent (divisorOfForm (pullbackRationalPluriForms sX π ω)) := by
    rw [← hτ]; exact Divisor.linearlyEquivalent_divisorOfForm hU hKU.1 hτ0 hne
  rw [QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (π ≫ sX) C.ι C.dim_le hlin ΔU hQU hB]
  exact hzero

/-- A prime divisor of a model is *unwanted* if it is exceptional over `X` with valuation outside
`𝓔`. -/
private def Model.IsUnwanted (M : Model sX Δ 𝓔 n S₀) (F : MMP.Mori.PrimeDivisor M.U) : Prop :=
  (∀ Q : MMP.Mori.PrimeDivisor X, M.π F.genericPoint ≠ Q.genericPoint) ∧
    (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, F⟩ : DivisorOver ℂ sX).valuation ∉ 𝓔

/-- **The remainder.** On a model, `G = Γ - Δ_U` (with `Δ_U` the crepant boundary of `(X, Δ)`)
vanishes away from the unwanted primes, is non-negative on them, and has the intersection numbers
of `K_U + Γ` on the curves contracted over `X`. -/
private theorem Model.exists_remainder (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) :
    ∃ G : QDivisor M.U,
      (∀ F, (G.coeff F = 0 ∧ ¬ M.IsUnwanted F) ∨ (0 ≤ G.coeff F ∧ M.IsUnwanted F)) ∧
      ∀ C : ProperCurve (M.π ≫ sX), C.IsContractedBy M.π →
        G.intersectionNumber ℂ (M.π ≫ sX) C.ι C.dim_le
            (isQCartier_of_isQFactorial _ M.isQFactorial G) =
          (Divisor.toQDivisor M.K + M.Γ).intersectionNumber ℂ (M.π ≫ sX) C.ι C.dim_le
            (isQCartier_of_isQFactorial _ M.isQFactorial _) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1
  have hX : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hUnv : IsNormalVariety ℂ (M.π ≫ sX) := M.isQFactorial.1
  haveI : QuasiCompact (M.π ≫ sX) := hUnv.1.toQuasiCompact
  have : IsProper M.π := isProper_of_isProjectiveMorphism M.π M.isProjectiveMorphism
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ (M.π ≫ sX) := hUnv.1
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isPair hPB
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (M.π ≫ sX)
      M.isBirationalMorphism).trans M.dim_eq)
  obtain ⟨ΔU, hΔU, -⟩ :=
    (hΔ.1.existsUnique_isCrepantBoundary hK M.π hUnv M.isBirationalMorphism).1
  have hQ := isQCartier_of_isQFactorial _ M.isQFactorial
  refine ⟨M.Γ - ΔU, fun F => ?_, fun C hC => ?_⟩
  · have h := add_eq_zero_or_nonneg_of_isPrescribedCoeff hΔ hK
      ⟨M.U, M.π, hUnv, M.isBirationalMorphism, F⟩ ‹_› (M.coeff_spec F) (hΔU F)
    have hGF : (M.Γ - ΔU).coeff F = M.Γ.coeff F + -ΔU.coeff F := by
      change M.Γ.coeff F - ΔU.coeff F = _; ring
    rw [hGF]; exact h
  · have h0 := intersectionNumber_eq_zero_of_isCrepantBoundary hX M.π hUnv
      M.isBirationalMorphism hK (isPairWith_of_isPair hΔ.1 hK).2.2 hΔU
      M.isCanonicalDivisor (hQ _) C hC
    have heq : M.Γ - ΔU =
        (Divisor.toQDivisor M.K + M.Γ) + -(Divisor.toQDivisor M.K + ΔU) := by abel
    rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le (hQ _)
        ((hQ _).add (QDivisor.IsQCartier.neg (hQ _))) heq,
      QDivisor.intersectionNumber_add' ℂ _ C.ι C.dim_le _ _ (hQ _) (QDivisor.IsQCartier.neg (hQ _)),
      QDivisor.intersectionNumber_neg ℂ _ C.ι C.dim_le (hQ _) (QDivisor.IsQCartier.neg (hQ _)), h0]
    ring

/-- The birational transform of an effective divisor is effective: it keeps or drops each
coefficient. -/
private theorem isEffective_transformDivisor {X Y : Scheme.{0}} {f : RationalMap X Y}
    {D : QDivisor X} (hD : D.IsEffective) :
    (RationalMap.transformDivisor (X := X) f D).IsEffective := by
  classical
  rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  refine Finset.sum_induction _ DivisorWithCoeffs.IsEffective
    (fun _ _ => DivisorWithCoeffs.IsEffective.add) DivisorWithCoeffs.isEffective_zero
    fun P _ => ?_
  rw [RationalMap.transformDivisor_single]
  rcases f.transformPrimeDivisor P with _ | E
  · exact DivisorWithCoeffs.isEffective_zero
  · intro E'
    simp only [Option.elim_some]
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_rfl

/-- Intersection numbers are additive over finite sums of divisors on a `ℚ`-factorial variety. -/
private theorem intersectionNumber_finset_sum {U : Scheme.{0}} [IsLocallyNoetherian U]
    [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} [QuasiCompact sU] (hU : IsQFactorial sU)
    (C : ProperCurve sU) {ι : Type*} (s : Finset ι) (D : ι → QDivisor U) :
    (∑ i ∈ s, D i).intersectionNumber ℂ sU C.ι C.dim_le (isQCartier_of_isQFactorial _ hU _) =
      ∑ i ∈ s, (D i).intersectionNumber ℂ sU C.ι C.dim_le (isQCartier_of_isQFactorial _ hU _) := by
  classical
  have hQ := isQCartier_of_isQFactorial _ hU
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := QDivisor.intersectionNumber_add' ℂ sU C.ι C.dim_le (0 : QDivisor U) 0
      (hQ _) (hQ _) (by simpa using hQ 0)
    rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le _ (hQ _) (add_zero 0)] at this
    linarith
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      QDivisor.intersectionNumber_add' ℂ sU C.ι C.dim_le _ _ (hQ _) (hQ _), ih]

/-- The intersection number of a divisor is the sum of those of its components. -/
private theorem intersectionNumber_eq_sum_coeff {U : Scheme.{0}} [IsLocallyNoetherian U]
    [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} [QuasiCompact sU] (hU : IsQFactorial sU)
    (C : ProperCurve sU) (G : QDivisor U) :
    G.intersectionNumber ℂ sU C.ι C.dim_le (isQCartier_of_isQFactorial _ hU _) =
      ∑ P ∈ G.support, G.coeff P *
        QDivisor.intersectionNumber ℂ sU C.ι C.dim_le (Finsupp.single P (1 : ℚ))
          (isQCartier_of_isQFactorial _ hU _) := by
  classical
  have hQ := isQCartier_of_isQFactorial _ hU
  conv_lhs => rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le _ (hQ _)
    (Finsupp.sum_single G).symm]
  rw [Finsupp.sum, intersectionNumber_finset_sum hU C]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le _ (hQ _)
      (Finsupp.smul_single_one P (G P)).symm,
    MMP.Fourfold.intersectionNumber_smul sU C.ι C.dim_le _ (hQ _) (G P) (hQ _)]
  rfl

/-- **Contracted primes lie in the remainder.** Let `f : U ⟶ Z` be a proper birational morphism
from a `ℚ`-factorial variety onto a normal variety all of whose contracted curves have classes on
the ray `ℝ_{≥0} [C₀]`, and `G` an effective divisor with `(G · C₀) < 0`. Then every prime
divisor `F` contracted by `f` has positive coefficient in `G`. -/
private theorem coeff_pos_of_forall_ne {U Z : Scheme.{0}} [IsIntegral U] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hU : IsQFactorial sU) (hZ : IsNormalVariety ℂ sZ) (f : U ⟶ Z) [IsProper f]
    (hf : IsBirationalMorphism f) (hfs : f ≫ sZ = sU) (C₀ : ProperCurve sU)
    (hray : ∀ C : ProperCurve sU, C.IsContractedBy f → ∃ c : ℝ, 0 ≤ c ∧
      c • OneCycle.numericalClass sU (C₀.cycle ℝ) = OneCycle.numericalClass sU (C.cycle ℝ))
    {G : QDivisor U} (hG : G.IsEffective)
    (hGC : haveI : QuasiCompact sU := hU.1.1.toQuasiCompact
      G.intersectionNumber ℂ sU C₀.ι C₀.dim_le (isQCartier_of_isQFactorial _ hU G) < 0)
    (F : MMP.Mori.PrimeDivisor U) (hF : ∀ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint ≠ Q.genericPoint) : 0 < G.coeff F := by
  classical
  haveI : QuasiCompact sU := hU.1.1.toQuasiCompact
  have hQ := isQCartier_of_isQFactorial _ hU
  set a := G.intersectionNumber ℂ sU C₀.ι C₀.dim_le (hQ G) with ha
  set E : QDivisor U := Finsupp.single F (1 : ℚ) with hE
  set e := E.intersectionNumber ℂ sU C₀.ι C₀.dim_le (hQ E) with he
  obtain ⟨t, ht0, hte⟩ : ∃ t : ℚ, 0 < t ∧ a ≤ t * e := by
    by_cases h : 0 ≤ e
    · exact ⟨1, one_pos, by linarith⟩
    · push Not at h
      refine ⟨a / e, div_pos_of_neg_of_neg hGC h, ?_⟩
      rw [div_mul_cancel₀ _ h.ne]
  set B : QDivisor U := G - Finsupp.single F t with hB
  have hBeq : -B = -G + t • E := by
    rw [hB, hE, Finsupp.smul_single, smul_eq_mul, mul_one]; abel
  have hBC : (-B).intersectionNumber ℂ sU C₀.ι C₀.dim_le (hQ _) = -a + t * e := by
    rw [MMP.Fourfold.intersectionNumber_congr _ C₀.ι C₀.dim_le _ ((hQ _).add (hQ _)) hBeq,
      QDivisor.intersectionNumber_add' ℂ _ C₀.ι C₀.dim_le _ _ (QDivisor.IsQCartier.neg (hQ G))
        (hQ _),
      QDivisor.intersectionNumber_neg ℂ _ C₀.ι C₀.dim_le (hQ G) (QDivisor.IsQCartier.neg (hQ G)),
      MMP.Fourfold.intersectionNumber_smul sU C₀.ι C₀.dim_le E (hQ E) t (hQ _)]
  have hnef : (-B).IsRelativelyNef sU f :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sU (hQ _) fun C hC => by
      obtain ⟨c, hc, hcC⟩ := hray C hC
      have h1 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sU (-B) (hQ _) C
      have h2 := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sU (-B) (hQ _) C₀
      rw [← hcC, map_smul, smul_eq_mul, h2, hBC] at h1
      have h3 : (0 : ℝ) ≤ (((-B).intersectionNumber ℂ sU C.ι C.dim_le (hQ _) : ℚ) : ℝ) := by
        rw [← h1]
        exact mul_nonneg hc (by exact_mod_cast (show (0 : ℚ) ≤ -a + t * e by linarith))
      exact_mod_cast h3
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  have hnone : RationalMap.transformPrimeDivisor (X := U) f.toRationalMap F = none := by
    rcases h : RationalMap.transformPrimeDivisor (X := U) f.toRationalMap F with _ | Q
    · rfl
    · exact absurd ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f F Q).mp h)
        (hF Q)
  have heff : (RationalMap.transformDivisor (X := U) f.toRationalMap B).IsEffective := by
    rw [hB, map_sub, RationalMap.transformDivisor_single_of_eq_none hnone, sub_zero]
    exact isEffective_transformDivisor hG
  have hBeff := QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sZ
    sU hZ hU.1 f hfs hf (hQ B) hnef heff
  have := hBeff F
  simp only [hB, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_eq_same] at this
  rw [Finsupp.sub_apply, Finsupp.single_eq_same] at this
  rw [DivisorWithCoeffs.coeff_apply]
  linarith

end Remainder

/- ### Building the next model -/

section NextModel

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X}
  {𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))} {n : ℕ}
  {S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The prescribed coefficient depends only on the valuation. -/
private theorem isPrescribedCoeff_iff_of_valuation_eq (hX : IsNormalVariety ℂ sX)
    {D D' : DivisorOver ℂ sX} (hv : D.valuation = D'.valuation) {c : ℚ} :
    IsPrescribedCoeff sX Δ 𝓔 D c ↔ IsPrescribedCoeff sX Δ 𝓔 D' c := by
  have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  unfold IsPrescribedCoeff
  rw [h, hv]

/-- **The next model.** The data of a step `U --f--> Z <--f⁺-- U'` over `X`, with `f⁺` small,
`(U', (f⁺)⁻¹_* f_* Γ)` a projective `ℚ`-factorial dlt pair, projective and birational over `X`,
and every prime divisor of `U` which is not unwanted mapped onto a prime divisor of `Z`, define
the next model. -/
private noncomputable def Model.ofStep (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀)
    {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (f : M.U ⟶ Z) (g : Z ⟶ X) (hfg : f ≫ g = M.π) (hfb : IsBirationalMorphism f) [IsProper f]
    (U' : Scheme.{0}) [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U'] [IsNormal U']
    (fp : U' ⟶ Z) (π' : U' ⟶ X) (hπ' : fp ≫ g = π')
    (hfp : IsSmallMorphism (π' ≫ sX) (g ≫ sX) fp)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (π' ≫ sX)) (hQ' : IsQFactorial (π' ≫ sX))
    (hdlt' : MMP.Intersection.IsDltPair (π' ≫ sX) (flipTransform f fp M.Γ))
    (hπ'p : IsProjectiveMorphism π') (hπ'b : IsBirationalMorphism π')
    (hsurv : ∀ F, ¬ M.IsUnwanted F → ∃ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint = Q.genericPoint) : Model sX Δ 𝓔 n S₀ where
  U := U'
  π := π'
  K := flipTransform f fp M.K
  Γ := flipTransform f fp M.Γ
  isProjectiveVariety := hproj
  dim_eq := by
    have hX : IsNormalVariety ℂ sX := hΔ.1.1
    haveI : MMP.Mori.IsVariety ℂ sX := hX.1
    haveI : MMP.Mori.IsVariety ℂ (π' ≫ sX) := hQ'.1.1
    haveI : MMP.Mori.IsVariety ℂ (M.π ≫ sX) := M.isQFactorial.1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π' ≫ sX) hπ'b,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (M.π ≫ sX)
        M.isBirationalMorphism]
    exact M.dim_eq
  isQFactorial := hQ'
  isCanonicalDivisor := isCanonicalDivisor_flipTransform M.isQFactorial.1 hfb
    (by rw [← Category.assoc, hfg]) hfp M.isCanonicalDivisor
  isDltPair := hdlt'
  isProjectiveMorphism := hπ'p
  isBirationalMorphism := hπ'b
  coeff_spec := fun F' => by
    have hX : IsNormalVariety ℂ sX := hΔ.1.1
    obtain ⟨F, -, hv, -, -, hc⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
      M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
    rw [DivisorWithCoeffs.coeff_apply, hc]
    exact (isPrescribedCoeff_iff_of_valuation_eq hX hv).mp (M.coeff_spec F)
  surv := fun s hs => by
    have : IsProper fp := hfp.isProper
    obtain ⟨F, hF⟩ := M.surv s hs
    obtain ⟨Q, hQ⟩ := hsurv F (fun h => h.2 (hF ▸ hs))
    obtain ⟨F', -, hv⟩ := exists_primeDivisor_of_map_genericPoint f hfb fp
      hfp.isBirationalMorphism g hfg hπ' M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F Q hQ
    exact ⟨F', hv.symm.trans hF⟩
  exc_mem := fun F' hF' => by
    have hX : IsNormalVariety ℂ sX := hΔ.1.1
    obtain ⟨F, -, hv, -, -, -⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
      M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
    have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
    rw [← hv]
    exact M.exc_mem F fun Q hQ => hF' Q (h.symm.trans hQ)

/-- The exceptional valuations of the next model are among those of the model. -/
private theorem Model.excVals_ofStep_subset (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀)
    {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (f : M.U ⟶ Z) (g : Z ⟶ X) (hfg : f ≫ g = M.π) (hfb : IsBirationalMorphism f) [IsProper f]
    (U' : Scheme.{0}) [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U'] [IsNormal U']
    (fp : U' ⟶ Z) (π' : U' ⟶ X) (hπ' : fp ≫ g = π')
    (hfp : IsSmallMorphism (π' ≫ sX) (g ≫ sX) fp)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (π' ≫ sX)) (hQ' : IsQFactorial (π' ≫ sX))
    (hdlt' : MMP.Intersection.IsDltPair (π' ≫ sX) (flipTransform f fp M.Γ))
    (hπ'p : IsProjectiveMorphism π') (hπ'b : IsBirationalMorphism π')
    (hsurv : ∀ F, ¬ M.IsUnwanted F → ∃ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint = Q.genericPoint) :
    (M.ofStep hΔ f g hfg hfb U' fp π' hπ' hfp hproj hQ' hdlt' hπ'p hπ'b hsurv).excVals ⊆
      M.excVals := by
  classical
  have hX : IsNormalVariety ℂ sX := hΔ.1.1
  intro v hv
  simp only [Model.excVals, Finset.mem_filter] at hv ⊢
  obtain ⟨hv0, F', hF', rfl⟩ := hv
  obtain ⟨F, -, hvF, -, -, -⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
    M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
  have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hvF
  exact ⟨hv0, F, fun Q hQ => hF' Q (h.symm.trans hQ), hvF⟩

/-- A prime divisor contracted by `f` leaves the exceptional valuations of the next model. -/
private theorem Model.valuation_notMem_excVals_ofStep
    (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀)
    {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    (f : M.U ⟶ Z) (g : Z ⟶ X) (hfg : f ≫ g = M.π) (hfb : IsBirationalMorphism f) [IsProper f]
    (U' : Scheme.{0}) [IsIntegral U'] [CompactSpace U'] [IsLocallyNoetherian U'] [IsNormal U']
    (fp : U' ⟶ Z) (π' : U' ⟶ X) (hπ' : fp ≫ g = π')
    (hfp : IsSmallMorphism (π' ≫ sX) (g ≫ sX) fp)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (π' ≫ sX)) (hQ' : IsQFactorial (π' ≫ sX))
    (hdlt' : MMP.Intersection.IsDltPair (π' ≫ sX) (flipTransform f fp M.Γ))
    (hπ'p : IsProjectiveMorphism π') (hπ'b : IsBirationalMorphism π')
    (hsurv : ∀ F, ¬ M.IsUnwanted F → ∃ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint = Q.genericPoint)
    (E : MMP.Mori.PrimeDivisor M.U)
    (hE : ∀ Q : MMP.Mori.PrimeDivisor Z, f E.genericPoint ≠ Q.genericPoint) :
    (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, E⟩ : DivisorOver ℂ sX).valuation ∉
      (M.ofStep hΔ f g hfg hfb U' fp π' hπ' hfp hproj hQ' hdlt' hπ'p hπ'b hsurv).excVals := by
  classical
  intro hv
  simp only [Model.excVals, Finset.mem_filter] at hv
  obtain ⟨-, F', -, hvF'⟩ := hv
  obtain ⟨F, Q, hvF, hFQ, -, -⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
    M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
  have hFE : F = E := eq_of_valuation_eq M.π M.isQFactorial.1 M.isBirationalMorphism
    (hvF.trans hvF')
  subst hFE
  exact hE Q hFQ

end NextModel

/- ### Flips and contractions -/

section FlipTools

/-- Regarding a divisor as a `ℚ`-divisor commutes with moving its prime divisors. -/
private theorem toQDivisor_mapPrimeDivisors {X Y : Scheme}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single E n =>
    have h1 : ∀ {Z : Scheme} (F : MMP.Mori.PrimeDivisor Z) (m : ℤ),
        Divisor.toQDivisor (Finsupp.single F m) = Finsupp.single F (m : ℚ) := fun F m => by
      simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
        DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, Int.coe_castAddHom]
    rw [h1, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [h1]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem toQDivisor_flipTransform {X Y X' : Scheme} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    Divisor.toQDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toQDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, toQDivisor_mapPrimeDivisors]

/-- The strict transform of `K + D` is the sum of the strict transforms of `K` and of `D`. -/
private theorem flipTransform_add {X Y X' : Scheme} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (K : Divisor X) (D : QDivisor X) :
    flipTransform f fp (Divisor.toQDivisor K + D) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D := by
  rw [map_add, toQDivisor_flipTransform]

/-- A projective `(K + D)`-flip in the sense of `MMP.Mori.IsFlip` of the small contraction of an
extremal ray is a `(K + D)`-flip in the sense of `MMP.Fourfold.IsFlipOf`. -/
private theorem isFlipOf_of_isFlip {X W X' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {K : Divisor X} {D : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    {fp : X' ⟶ W} (hf : IsContractionOfRay sX sW R f)
    (hsmall : IsSmallMorphism sX sW f) (h : MMP.Mori.IsFlip sX sW sX' K D f fp)
    (hproj : IsProjectiveMorphism fp) :
    IsFlipOf sX sW sX' (Divisor.toQDivisor K + D) f fp where
  isQCartier := h.isFlippingContraction.isQCartier
  isContraction := hf.toIsContraction
  isSmallMorphism := hsmall
  hasRelativelyAmpleMultiple := h.isFlippingContraction.hasRelativelyAmpleMultiple
  isSmallMorphism_flip :=
    { isNormalVariety_source := h.isNormalVariety
      isNormalVariety_target := hsmall.isNormalVariety_target
      comp_eq := h.comp_eq
      isProper := h.isProper
      isBirationalMorphism := h.isBirationalMorphism
      two_le_codimension := h.two_le_codimension }
  isProjectiveMorphism_flip := hproj
  isQCartier_flip := by rw [flipTransform_add]; exact h.isQCartier
  hasRelativelyAmpleMultiple_flip := by rw [flipTransform_add]; exact h.hasRelativelyAmpleMultiple

/-- **A non-small birational morphism contracts a prime divisor.** If a proper birational
morphism `f : U ⟶ Z` of normal varieties is not small, some prime divisor of `U` is not mapped
onto a prime divisor of `Z`. -/
private theorem exists_primeDivisor_of_not_isSmallMorphism {U Z : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hU : IsNormalVariety ℂ sU) (hZ : IsNormalVariety ℂ sZ) (f : U ⟶ Z) [IsProper f]
    (hfb : IsBirationalMorphism f) (hfs : f ≫ sZ = sU) (h : ¬ IsSmallMorphism sU sZ f) :
    ∃ E : MMP.Mori.PrimeDivisor U, ∀ Q : MMP.Mori.PrimeDivisor Z,
      f E.genericPoint ≠ Q.genericPoint := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsDominant f := hfb.isDominant
  have hUv : MMP.Mori.IsVariety ℂ (f ≫ sZ) := by rw [hfs]; exact hU.1
  by_contra hcon
  push Not at hcon
  refine h ⟨hU, hZ, hfs, inferInstance, hfb,
    MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : ∀ y : U, f y ∈ biregularLocus f → y ∉ (exceptionalSet f : Set U) := fun y hy hy' =>
    hy' hy
  obtain h0 | h1 : Order.coheight x = 0 ∨ Order.coheight x = 1 := by
    generalize Order.coheight x = c at hlt ⊢
    induction c using ENat.recTopCoe with
    | top => exact absurd hlt (by simp)
    | coe c => norm_cast at hlt ⊢; omega
  · have hmax := Order.coheight_eq_zero.mp h0
    have hle : x ≤ genericPoint U :=
      Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
    have hx' : x = genericPoint U :=
      ((Scheme.le_iff_specializes.mp (hmax hle)).antisymm (genericPoint_specializes x)).eq
    subst hx'
    haveI : ValuationRing (Z.presheaf.stalk (genericPoint Z)) :=
      inferInstanceAs (ValuationRing Z.functionField)
    have := MMP.Flips.mem_biregularLocus_of_valuationRing hZ hUv hfb (genericPoint Z)
    rw [← map_genericPoint_of_isDominant f] at this
    exact hmem _ this hx
  · set E : MMP.Mori.PrimeDivisor U := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1
    have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1
    obtain ⟨Q, hQ⟩ := hcon E
    have := Q.isDiscreteValuationRing_localRing
    have hQb := MMP.Flips.mem_biregularLocus_of_valuationRing hZ hUv hfb Q.genericPoint
    rw [← hQ, hE] at hQb
    exact hmem _ hQb hx

end FlipTools

/- ### Contractions of negative extremal rays -/

section RayContraction

/-- A projective variety carries an ample invertible sheaf. -/
private theorem exists_isAmple {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- A proper morphism between projective varieties is projective. -/
private theorem isProjectiveMorphism_of_isProper {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) [IsProper p] :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 5 2
  exact h.mp ⟨inferInstance, exists_isAmple hV⟩

section IsoApp

variable {X Z : Scheme.{0}} (ψ : X ⟶ Z) (hψ : ∀ V : Z.Opens, IsIso (ψ.app V))

include hψ

/-- If every `ψ.app V` is an isomorphism, nonempty opens have nonempty preimages. -/
private theorem nonempty_preimage_of_isIso_app (V : Z.Opens) [Nonempty V] :
    Nonempty (ψ ⁻¹ᵁ V) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hbot : ψ ⁻¹ᵁ V = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne.false ⟨x, hx⟩
  haveI := Scheme.component_nontrivial Z V
  haveI := hψ V
  haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
  exact hab ((ConcreteCategory.bijective_of_isIso (ψ.app V)).1 (Subsingleton.elim _ _))

/-- The target of a morphism from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is integral. -/
private theorem isIntegral_of_isIso_app [IsIntegral X] : IsIntegral Z where
  nonempty := ⟨ψ (Nonempty.some inferInstance)⟩
  component_integral V _ := by
    haveI := nonempty_preimage_of_isIso_app ψ hψ V
    haveI := hψ V
    exact Function.Injective.isDomain (ψ.app V).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app V)).1

/-- A morphism with `ψ_* 𝒪_X = 𝒪_Z` is dominant. -/
private theorem isDominant_of_isIso_app : IsDominant ψ := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨z, hz⟩ => ?_⟩
  haveI : Nonempty (⟨V, hV⟩ : Z.Opens) := ⟨⟨z, hz⟩⟩
  obtain ⟨⟨x, hx⟩⟩ := nonempty_preimage_of_isIso_app ψ hψ ⟨V, hV⟩
  exact ⟨ψ x, hx, x, rfl⟩

end IsoApp

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- A nonzero element of a ray `ℝ_{≥0} v` spans it. -/
private theorem eq_setOf_smul_of_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {v w : V}
    {R : Set V} (hR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u}) (hw : w ∈ R) (hw0 : w ≠ 0) :
    R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u} := by
  obtain ⟨c₁, hc₁, rfl⟩ := hR ▸ hw
  have hc : 0 < c₁ := hc₁.lt_of_ne (by rintro rfl; exact hw0 (zero_smul _ _))
  rw [hR]
  ext u
  constructor
  · rintro ⟨c, hc0, rfl⟩
    exact ⟨c / c₁, div_nonneg hc0 hc₁, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩
  · rintro ⟨c, hc0, rfl⟩
    exact ⟨c * c₁, mul_nonneg hc0 hc₁, by rw [smul_smul]⟩

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}

/-- The point `Spec ℂ` is a projective variety over itself. -/
private theorem isProjectiveVariety_id_spec :
    AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
  (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
    ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      MMP.isProjectiveMorphism_of_isClosedImmersion _⟩

omit [IsIntegral X] in
/-- An extremal ray of `NE̅(X)` is the preimage of an extremal ray of `NE̅(X / Spec ℂ)` under the
natural bijection. -/
private theorem isExtremalRay_preimage (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R) :
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _)
      (relativeToAbsolute sX sX ⁻¹' R) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
  haveI := isProjectiveVariety_id_spec
  have hbij := relativeToAbsolute_bijective sX
  let e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij
  have hcone : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    have h := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of ℂ))) sX
      (Category.comp_id sX)
    rw [hbij.2.range_eq, Set.inter_univ] at h
    rw [← h]; exact e.symm_image_image _
  change IsExtremalRay ℝ _ (e ⁻¹' R)
  rw [← e.image_symm_eq_preimage, ← hcone]
  exact MMP.ProgramBaseChange.isExtremalRay_image e.symm hR

/-- **The dlt contraction theorem over the base point.** A `(K + B)`-negative extremal ray `R` of
a projective `ℚ`-factorial dlt complex pair `(X, B)` has a contraction `ψ : X ⟶ Z` onto a
projective variety. The ray is moved to `N₁(X / Spec ℂ)` along the bijection
`relativeToAbsolute`, where the relative dlt contraction theorem applies. -/
private theorem exists_isContractionOfRay_isProjectiveVariety
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hdlt : MMP.Intersection.IsDltPair sX B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hXn : IsNormalVariety ℂ sX) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (ψ : X ⟶ Z),
      MMP.Mori.IsProjectiveVariety ℂ sZ ∧ IsContractionOfRay sX sZ R ψ := by
  obtain ⟨m, hKm⟩ := hK
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
  haveI := isProjectiveVariety_id_spec
  have hFray := isExtremalRay_preimage hXp hR.2.1
  obtain ⟨Z, ψ, g, hψ⟩ := MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace
    (𝟙 (Spec (.of ℂ))) sX (Category.comp_id sX)
    ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKm B).mp hdlt) hQ hFray.1
    hFray.1.2.2.1 fun z hz hz0 => by
      rw [QDivisor.relativeCurveForm_eq_comp]
      exact hR.2.2 _ hz fun h =>
        hz0 ((relativeToAbsolute_bijective sX).1 (by rw [h, map_zero]))
  have happ := hψ.isIso_app
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hψ.isProjectiveMorphism
  have hZv : MMP.Mori.IsVariety ℂ g := (MMP.Mori.isVariety_iff ℂ g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety ℂ g :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ g).mpr ⟨hZv, hψ.isProjectiveMorphism⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  haveI : IsProper (ψ ≫ g) := by rw [hψ.comp_eq]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  refine ⟨Z, g, ψ, hZp,
    { isNormalVariety_source := hXn
      isNormalVariety_target := ⟨hZv, MMP.Mori.isNormal_of_isIso_c g ψ hZv
        (by rw [hψ.comp_eq]; exact hXp.toIsVariety)⟩
      comp_eq := hψ.comp_eq
      isProjectiveMorphism := isProjectiveMorphism_of_isProper hXp hZp ψ
      surjective := ψ.surjective
      isIso_app := happ
      isContractedBy_iff := fun C => ?_ }⟩
  rw [hψ.isContractedBy_iff C (isContractedBy_structure C)]
  exact Iff.of_eq (congrArg (· ∈ R) (isNaturalRelativeMap_relativeToAbsolute sX sX _))

/-- **A negative extremal ray is spanned by a curve.** By the cone theorem for the dlt pair
`(X, B)`, a `(K + B)`-negative extremal ray `R` of `NE̅(X)` is `ℝ_{≥0} [C₀]` for a proper curve
`C₀`: a generator of `R` lies in `NE̅_{K+B ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`, the first summand vanishes on
the face `R`, and some `[Cⱼ]` with nonzero class lies in `R`. -/
private theorem exists_properCurve_eq_ray (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX) {m : ℕ} (hKm : K.IsCanonicalDivisor sX m)
    (hdlt : MMP.Intersection.IsDltPair sX B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ C₀ : ProperCurve sX,
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = w} := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
  haveI := isProjectiveVariety_id_spec
  set e := relativeToAbsolute sX sX with he
  have hinj : Function.Injective e := (relativeToAbsolute_bijective sX).1
  have hΔ := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKm B).mp hdlt
  obtain ⟨ι, -, C, hC, -, -, hdec⟩ :=
    MMP.Mori.IsDltPair.exists_relativeClosedConeOfCurves_eq_add_hull
    (𝟙 (Spec (.of ℂ))) sX (Category.comp_id sX) hΔ hQ
  obtain ⟨⟨hFA, ⟨-, hFs⟩, -, hFext⟩, v, hv0, hFv⟩ := isExtremalRay_preimage hXp hR.2.1
  have hneg : ∀ z ∈ e ⁻¹' R, z ≠ 0 → QDivisor.relativeCurveForm sX sX
      (Divisor.toQDivisor K + B) hΔ.1.2.2 z < 0 := fun z hz hz0 => by
    rw [QDivisor.relativeCurveForm_eq_comp]
    exact hR.2.2 _ hz fun h => hz0 (hinj (by rw [h, map_zero]))
  set H := PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass sX (hC j))
  have hHN : ∀ y ∈ H, y ∈ (relativeClosedConeOfCurves sX sX : Set _) := fun y hy => by
    change y ∈ (relativeClosedConeOfCurves sX sX : Set _)
    rw [hdec]
    exact ⟨0, ⟨(relativeClosedConeOfCurves sX sX).zero_mem, by simp⟩, y, hy, zero_add y⟩
  have hvF : v ∈ e ⁻¹' R := hFv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hvN : v ∈ (relativeClosedConeOfCurves sX sX : Set _) := hFA hvF
  rw [hdec] at hvN
  obtain ⟨a, ⟨haN, ha0⟩, h, hh, hah⟩ := hvN
  replace hah : a + h = v := hah
  obtain ⟨haF, hhF⟩ := hFext a haN h (hHN h hh) (hah ▸ hvF)
  have ha : a = 0 := by
    by_contra ha
    exact absurd ha0 (not_le.mpr (hneg a haF ha))
  have key : ∀ y ∈ H, y ∈ e ⁻¹' R → y = 0 ∨ ∃ j, (C j).relativeClass sX (hC j) ∈ e ⁻¹' R ∧
      (C j).relativeClass sX (hC j) ≠ 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro hj
      by_cases h0 : (C j).relativeClass sX (hC j) = 0
      · exact Or.inl h0
      · exact Or.inr ⟨j, hj, h0⟩
    | zero => exact fun _ => Or.inl rfl
    | add x y hx hy ihx ihy =>
      intro hxy
      obtain ⟨hxF, hyF⟩ := hFext x (hHN x hx) y (hHN y hy) hxy
      rcases ihx hxF with h1 | h1
      · rcases ihy hyF with h2 | h2
        · exact Or.inl (by rw [h1, h2, add_zero])
        · exact Or.inr h2
      · exact Or.inr h1
    | smul c x hx ihx =>
      intro hcx
      by_cases hc : c = 0
      · exact Or.inl (by rw [hc, zero_smul])
      · have hxF : x ∈ e ⁻¹' R := by
          have hc' : (0 : ℝ) < c := lt_of_le_of_ne c.2 fun h => hc (Subtype.ext h.symm)
          have h1 := hFs _ hcx ((c : ℝ)⁻¹) (inv_pos.mpr hc')
          have h2 : ((c : ℝ)⁻¹) • (c • x) = x := by
            rw [show c • x = (c : ℝ) • x from rfl, smul_smul, inv_mul_cancel₀ hc'.ne', one_smul]
          rwa [h2] at h1
        rcases ihx hxF with h1 | h1
        · exact Or.inl (by rw [h1, smul_zero])
        · exact Or.inr h1
  rcases key h hh hhF with h0 | ⟨j, hjF, hj0⟩
  · exact absurd (by rw [← hah, ha, h0, add_zero]) hv0
  refine ⟨C j, ?_⟩
  have hw : e ((C j).relativeClass sX (hC j)) = OneCycle.numericalClass sX ((C j).cycle ℝ) :=
    isNaturalRelativeMap_relativeToAbsolute sX sX _
  obtain ⟨-, v', -, hRv'⟩ := hR.2.1
  refine eq_setOf_smul_of_mem hRv' (hw ▸ hjF) fun h0 => hj0 (hinj ?_)
  rw [hw, h0, map_zero]

end RayContraction

/- ### The steps of the program -/

section Steps

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X}
  {𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))} {n : ℕ}
  {S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- A model is a floor pair of `P(n)`. -/
private theorem Model.isFloorPair (M : Model sX Δ 𝓔 n S₀) :
    IsFloorPair (M.π ≫ sX) n M.K M.Γ :=
  ⟨M.isProjectiveVariety, M.dim_eq, M.isQFactorial, ⟨n, M.isCanonicalDivisor⟩, M.isDltPair⟩

/-- **The contraction of a negative extremal ray over `X`.** If the adjoint of a model is not
nef over `X`, then `NE̅(U)` has a `(K_U + Γ)`-negative extremal ray `R = ℝ_{≥0} [C₀]`, spanned by
a curve contracted over `X`, whose contraction `f : U ⟶ Z` is a birational morphism over `X`
onto a normal projective variety, with `-(K_U + Γ)` relatively ample. -/
private theorem Model.exists_contraction (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ) (M : Model sX Δ 𝓔 n S₀) (hM : ¬ M.IsNef) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (_ : CompactSpace Z) (f : M.U ⟶ Z) (g : Z ⟶ X)
      (R : Set (NumericalCurveClasses (M.π ≫ sX))) (C₀ : ProperCurve (M.π ≫ sX)),
      f ≫ g = M.π ∧ IsProper f ∧ IsProjectiveMorphism g ∧ IsBirationalMorphism f ∧
      IsBirationalMorphism g ∧ IsNormalVariety ℂ (g ≫ sX) ∧
      MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX) ∧
      IsNegativeExtremalRayOf (M.π ≫ sX) (Divisor.toQDivisor M.K + M.Γ) R ∧
      R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) = w} ∧
      C₀.IsContractedBy M.π ∧
      IsContractionOfRay (M.π ≫ sX) (g ≫ sX) R f ∧
      (-(Divisor.toQDivisor M.K + M.Γ)).HasRelativelyAmpleMultiple f := by
  classical
  have hUn : IsNormalVariety ℂ (M.π ≫ sX) := M.isQFactorial.1
  have hUp := M.isProjectiveVariety
  obtain ⟨R, hR, hRπ⟩ := exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef hUp
    hX ⟨n, M.isCanonicalDivisor⟩ M.isDltPair.1 M.isProjectiveMorphism rfl hM
  obtain ⟨Z, sZ, ψ, hZp, hψ⟩ := exists_isContractionOfRay_isProjectiveVariety hUp M.isQFactorial
    ⟨n, M.isCanonicalDivisor⟩ M.isDltPair hR hUn
  obtain ⟨g, hg, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hUp M.isProjectiveMorphism rfl
    hR.2.1 hRπ hψ
  have hψb := isBirationalMorphism_of_isContractionOfRay hUp M.isProjectiveMorphism
    M.isBirationalMorphism rfl hR.2.1 hRπ hψ
  have hZn := hψ.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZn.2
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI hψp : IsProper ψ := isProper_of_isProjectiveMorphism _ hψ.isProjectiveMorphism
  have hgs : g ≫ sX = sZ := by
    haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U =>
      hψ.isIso_app U.unop
    exact (MMP.existsUnique_comp_eq_of_isIso_c ψ (M.π ≫ sX) fun _ _ _ =>
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _).unique
      (by rw [← Category.assoc, hg]) hψ.comp_eq
  subst hgs
  have hXn : IsNormalVariety ℂ sX := hΔ.1.1
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsProper (g ≫ sX) := isProper_of_isProjectiveMorphism _ hZp.isProjective
  haveI : IsProper g := IsProper.of_comp g sX
  have hgp : IsProjectiveMorphism g := isProjectiveMorphism_of_isProper hZp hX g
  haveI : IsProper M.π := isProper_of_isProjectiveMorphism _ M.isProjectiveMorphism
  have hBg : IsBirational g :=
    MMP.Mori.isBirational_of_comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hψb)
      (hg ▸ MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism M.isBirationalMorphism)
  have hgb : IsBirationalMorphism g := by
    have := isBirationalMorphism_comp_of_isBirational g (𝟙 _) hBg
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        (isBirationalMorphism_of_isIso _))
    simpa using this
  obtain ⟨C₀, hRC⟩ := exists_properCurve_eq_ray hUp M.isQFactorial M.isCanonicalDivisor
    M.isDltPair hR
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance, ψ, g, R, C₀, hg,
    hψp, hgp, hψb, hgb, hZn, hZp, hR, hRC, hRπ C₀ (hRC ▸ ⟨1, zero_le_one, one_smul _ _⟩), hψ,
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay (M.π ≫ sX) (g ≫ sX) hUn hUp hZp
      ⟨n, M.isCanonicalDivisor⟩ hR.1 hR.2.1 (fun v hv hv0 => by
        simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hR.2.2 v hv hv0)
      ψ hψ.comp_eq fun C hC => (hψ.isContractedBy_iff C).mp hC⟩

/-- The adjoint is negative on the spanning curve of a negative extremal ray, and so is the
remainder `G`. -/
private theorem Model.intersectionNumber_neg_of_ray (M : Model sX Δ 𝓔 n S₀)
    {R : Set (NumericalCurveClasses (M.π ≫ sX))} {C₀ : ProperCurve (M.π ≫ sX)}
    (hR : IsNegativeExtremalRayOf (M.π ≫ sX) (Divisor.toQDivisor M.K + M.Γ) R)
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) = w}) :
    haveI : QuasiCompact (M.π ≫ sX) := M.isQFactorial.1.1.toQuasiCompact
    (Divisor.toQDivisor M.K + M.Γ).intersectionNumber ℂ (M.π ≫ sX) C₀.ι C₀.dim_le
      (isQCartier_of_isQFactorial _ M.isQFactorial _) < 0 := by
  haveI : QuasiCompact (M.π ≫ sX) := M.isQFactorial.1.1.toQuasiCompact
  obtain ⟨hQ', hray, hneg⟩ := hR
  obtain ⟨v, hv0, hRv⟩ := hray.2
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hC₀R : OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) ∈ R :=
    hRC ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hC₀0 : OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) ≠ 0 := by
    intro h0
    obtain ⟨c, -, hc⟩ := (hRC ▸ hvR : v ∈ {w | ∃ c : ℝ, 0 ≤ c ∧
      c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) = w})
    rw [h0, smul_zero] at hc
    exact hv0 hc.symm
  have h := hneg _ hC₀R hC₀0
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at h
  exact_mod_cast h

/-- **The flip step.** If the contraction of the ray is small, its flip, supplied by `P(n)`, is
the next model. -/
private theorem Model.exists_flip (hP : ProjectiveFloorProgramInputs n)
    (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] (f : M.U ⟶ Z) (g : Z ⟶ X) (R : Set (NumericalCurveClasses (M.π ≫ sX)))
    (C₀ : ProperCurve (M.π ≫ sX)) (hfg : f ≫ g = M.π) [IsProper f]
    (hg : IsProjectiveMorphism g) (hfb : IsBirationalMorphism f) (hgb : IsBirationalMorphism g)
    (hZn : IsNormalVariety ℂ (g ≫ sX)) (hZp : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX))
    (hR : IsNegativeExtremalRayOf (M.π ≫ sX) (Divisor.toQDivisor M.K + M.Γ) R)
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) = w})
    (hC₀ : C₀.IsContractedBy M.π) (hcon : IsContractionOfRay (M.π ≫ sX) (g ≫ sX) R f)
    (hamp : (-(Divisor.toQDivisor M.K + M.Γ)).HasRelativelyAmpleMultiple f)
    (hsmall : IsSmallMorphism (M.π ≫ sX) (g ≫ sX) f) :
    ∃ M' : Model sX Δ 𝓔 n S₀, M'.excVals.card ≤ M.excVals.card ∧ M.IsFlipStep M' := by
  classical
  haveI : QuasiCompact (M.π ≫ sX) := M.isQFactorial.1.1.toQuasiCompact
  have hQ := isQCartier_of_isQFactorial _ M.isQFactorial
  obtain ⟨G, hGspec, hGnum⟩ := M.exists_remainder hΔ
  have hGC := (hGnum C₀ hC₀).symm ▸ M.intersectionNumber_neg_of_ray hR hRC
  -- a component of the reduced boundary negative on the ray
  rw [intersectionNumber_eq_sum_coeff M.isQFactorial C₀ G] at hGC
  obtain ⟨P, hPG, hPneg⟩ : ∃ P ∈ G.support, G.coeff P *
      QDivisor.intersectionNumber ℂ (M.π ≫ sX) C₀.ι C₀.dim_le (Finsupp.single P (1 : ℚ))
        (hQ _) < 0 := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.sum_nonneg hcon) (not_le.mpr hGC)
  have hGP0 : G.coeff P ≠ 0 := by
    rw [DivisorWithCoeffs.coeff_apply]; exact Finsupp.mem_support_iff.mp hPG
  have hGP : 0 < G.coeff P ∧ M.IsUnwanted P := by
    rcases hGspec P with ⟨h0, -⟩ | h
    · exact absurd h0 hGP0
    · exact ⟨h.1.lt_of_ne hGP0.symm, h.2⟩
  have hPC : QDivisor.intersectionNumber ℂ (M.π ≫ sX) C₀.ι C₀.dim_le
      (Finsupp.single P (1 : ℚ)) (hQ _) < 0 := by
    by_contra h0
    push Not at h0
    exact absurd (mul_nonneg hGP.1.le h0) (not_le.mpr hPneg)
  have hΓP : M.Γ.coeff P = 1 := by
    rcases M.coeff_spec P with ⟨Q, hQP, -⟩ | ⟨-, ⟨hs, -⟩ | ⟨-, h1⟩⟩
    · exact absurd hQP (hGP.2.1 Q)
    · exact absurd hs hGP.2.2
    · exact h1
  have hsingle : Divisor.toQDivisor (Finsupp.single P (1 : ℤ)) = Finsupp.single P (1 : ℚ) := by
    simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
      DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, Int.coe_castAddHom, Int.cast_one]
  have hcomp : IsComponentNegative (M.π ≫ sX) M.Γ R := by
    refine ⟨P, hΓP, hQ _, fun u hu hu0 => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hRC ▸ hu
    have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
    rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      MMP.Fourfold.intersectionNumber_congr _ C₀.ι C₀.dim_le _ (hQ _) hsingle]
    exact mul_neg_of_pos_of_neg hc0 (by exact_mod_cast hPC)
  have hfloor : IsFloorFlippingContraction (M.π ≫ sX) (g ≫ sX) M.K M.Γ R f :=
    ⟨hR, hcon, hsmall, hZp, hamp, hcomp⟩
  obtain ⟨X', _, _, _, sX', fp, hX'p, hflip⟩ :=
    hP.2.1 M.U (M.π ≫ sX) M.K M.Γ M.isFloorPair Z (g ≫ sX) R f hfloor
  haveI : IsIntegral X' := hflip.isNormalVariety.1.toIsIntegral
  have hsX' : (fp ≫ g) ≫ sX = sX' := by rw [Category.assoc]; exact hflip.comp_eq
  subst hsX'
  haveI : IsProper fp := hflip.isProper
  have hfpS : IsSmallMorphism ((fp ≫ g) ≫ sX) (g ≫ sX) fp :=
    ⟨hflip.isNormalVariety, hZn, hflip.comp_eq, hflip.isProper, hflip.isBirationalMorphism,
      hflip.two_le_codimension⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ ((fp ≫ g) ≫ sX) := hX'p
  haveI := AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ ((fp ≫ g) ≫ sX)
  haveI : MMP.Mori.IsVariety ℂ (g ≫ sX) := hZn.1
  have hfpp : IsProjectiveMorphism fp :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety ((fp ≫ g) ≫ sX)
      (g ≫ sX) fp hflip.comp_eq
  have hstep : IsProjectiveElementaryDltStep (M.π ≫ sX) (g ≫ sX) ((fp ≫ g) ≫ sX) M.K M.Γ R f fp
      (flipTransform f fp M.Γ) :=
    { isProjectiveQFactorialDltPair :=
        ⟨M.isProjectiveVariety, M.isQFactorial, ⟨n, M.isCanonicalDivisor⟩, M.isDltPair⟩
      isNegativeExtremalRayOf := hR
      isContractionOfRay := hcon
      isBirationalMorphism := hfb
      comp_eq := hflip.comp_eq
      eq_flipTransform := rfl
      flip_or_divisorial := Or.inl ⟨hsmall, isFlipOf_of_isFlip hcon hsmall hflip hfpp⟩ }
  obtain ⟨hQ', hdlt'⟩ := hstep.isQFactorial_and_isDltPair
  have hZ := hsmall.isNormalVariety_target
  have hsurv : ∀ F, ¬ M.IsUnwanted F → ∃ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint = Q.genericPoint := by
    intro F _
    obtain ⟨-, Q, -, -, hFQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ
      (isBirationalMorphism_of_isIso (𝟙 Z)) hsmall F
    exact ⟨Q, map_genericPoint_eq_of_image_eq F Q hFQ⟩
  have hπp : IsProjectiveMorphism (fp ≫ g) := hfpp.comp hg
  have hπb : IsBirationalMorphism (fp ≫ g) :=
    MMP.Mori.isBirationalMorphism_comp hflip.isBirationalMorphism hgb
  refine ⟨M.ofStep hΔ f g hfg hfb X' fp (fp ≫ g) rfl hfpS hX'p hQ' hdlt' hπp hπb hsurv,
    Finset.card_le_card (M.excVals_ofStep_subset hΔ f g hfg hfb X' fp (fp ≫ g) rfl hfpS hX'p hQ'
      hdlt' hπp hπb hsurv), Z, g ≫ sX, R, f, fp, hfloor, hflip, rfl, rfl⟩

/-- **The divisorial step.** If the contraction of the ray is not small, its target is the next
model: it contracts only unwanted primes, so the number of exceptional valuations drops. -/
private theorem Model.exists_divisorial (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] (f : M.U ⟶ Z) (g : Z ⟶ X) (R : Set (NumericalCurveClasses (M.π ≫ sX)))
    (C₀ : ProperCurve (M.π ≫ sX)) (hfg : f ≫ g = M.π) [IsProper f]
    (hg : IsProjectiveMorphism g) (hfb : IsBirationalMorphism f) (hgb : IsBirationalMorphism g)
    (hZn : IsNormalVariety ℂ (g ≫ sX)) (hZp : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX))
    (hR : IsNegativeExtremalRayOf (M.π ≫ sX) (Divisor.toQDivisor M.K + M.Γ) R)
    (hRC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) = w})
    (hC₀ : C₀.IsContractedBy M.π) (hcon : IsContractionOfRay (M.π ≫ sX) (g ≫ sX) R f)
    (hsmall : ¬ IsSmallMorphism (M.π ≫ sX) (g ≫ sX) f) :
    ∃ M' : Model sX Δ 𝓔 n S₀, M'.excVals.card < M.excVals.card := by
  classical
  haveI : QuasiCompact (M.π ≫ sX) := M.isQFactorial.1.1.toQuasiCompact
  obtain ⟨G, hGspec, hGnum⟩ := M.exists_remainder hΔ
  have hGC := (hGnum C₀ hC₀).symm ▸ M.intersectionNumber_neg_of_ray hR hRC
  have hGeff : G.IsEffective := fun F => by
    rcases hGspec F with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.ge
    · exact h
  have hfs : f ≫ g ≫ sX = M.π ≫ sX := by rw [← Category.assoc, hfg]
  have hray : ∀ C : ProperCurve (M.π ≫ sX), C.IsContractedBy f → ∃ c : ℝ, 0 ≤ c ∧
      c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) =
        OneCycle.numericalClass (M.π ≫ sX) (C.cycle ℝ) := fun C hC => by
    have := (hcon.isContractedBy_iff C).mp hC
    rw [hRC] at this
    exact this
  have hpos := coeff_pos_of_forall_ne M.isQFactorial hZn f hfb hfs C₀ hray hGeff hGC
  have hsurv : ∀ F, ¬ M.IsUnwanted F → ∃ Q : MMP.Mori.PrimeDivisor Z,
      f F.genericPoint = Q.genericPoint := by
    intro F hF
    by_contra hcon
    push Not at hcon
    rcases hGspec F with ⟨h0, -⟩ | ⟨-, h⟩
    · exact absurd h0 (hpos F hcon).ne'
    · exact hF h
  have hstep : IsProjectiveElementaryDltStep (M.π ≫ sX) (g ≫ sX) (g ≫ sX) M.K M.Γ R f (𝟙 Z)
      (flipTransform f (𝟙 Z) M.Γ) :=
    { isProjectiveQFactorialDltPair :=
        ⟨M.isProjectiveVariety, M.isQFactorial, ⟨n, M.isCanonicalDivisor⟩, M.isDltPair⟩
      isNegativeExtremalRayOf := hR
      isContractionOfRay := hcon
      isBirationalMorphism := hfb
      comp_eq := Category.id_comp _
      eq_flipTransform := rfl
      flip_or_divisorial := Or.inr ⟨hsmall, inferInstance⟩ }
  obtain ⟨hQ', hdlt'⟩ := hstep.isQFactorial_and_isDltPair
  obtain ⟨E, hE⟩ := exists_primeDivisor_of_not_isSmallMorphism M.isQFactorial.1 hZn f hfb hfs
    hsmall
  have hEunw : M.IsUnwanted E := by
    rcases hGspec E with ⟨h0, -⟩ | ⟨-, h⟩
    · exact absurd h0 (hpos E hE).ne'
    · exact h
  have hEmem : (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, E⟩ :
      DivisorOver ℂ sX).valuation ∈ M.excVals := by
    simp only [Model.excVals, Finset.mem_filter]
    exact ⟨M.exc_mem E hEunw.1, E, hEunw.1, rfl⟩
  set M' := M.ofStep hΔ f g hfg hfb Z (𝟙 Z) g (Category.id_comp g) (isSmallMorphism_id hZn) hZp
    hQ' hdlt' hg hgb hsurv
  refine ⟨M', Finset.card_lt_card ⟨M.excVals_ofStep_subset hΔ f g hfg hfb Z (𝟙 Z) g
    (Category.id_comp g) (isSmallMorphism_id hZn) hZp hQ' hdlt' hg hgb hsurv, fun h => ?_⟩⟩
  exact M.valuation_notMem_excVals_ofStep hΔ f g hfg hfb Z (𝟙 Z) g (Category.id_comp g)
    (isSmallMorphism_id hZn) hZp hQ' hdlt' hg hgb hsurv E hE (h hEmem)

/-- **A step of the program.** A model whose adjoint is not nef over `X` has a divisorial
contraction, which lowers the number of exceptional valuations, or a floor flip. -/
private theorem Model.exists_step (hP : ProjectiveFloorProgramInputs n)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) (hM : ¬ M.IsNef) :
    ∃ M' : Model sX Δ 𝓔 n S₀, M'.excVals.card < M.excVals.card ∨
      (M'.excVals.card ≤ M.excVals.card ∧ M.IsFlipStep M') := by
  obtain ⟨Z, _, _, _, _, f, g, R, C₀, hfg, _, hg, hfb, hgb, hZn, hZp, hR, hRC, hC₀, hcon, hamp⟩ :=
    M.exists_contraction hX hΔ hM
  by_cases hsmall : IsSmallMorphism (M.π ≫ sX) (g ≫ sX) f
  · obtain ⟨M', h⟩ := M.exists_flip hP hΔ f g R C₀ hfg hg hfb hgb hZn hZp hR hRC hC₀ hcon hamp
      hsmall
    exact ⟨M', Or.inr h⟩
  · obtain ⟨M', h⟩ := M.exists_divisorial hΔ f g R C₀ hfg hg hfb hgb hZn hZp hR hRC hC₀ hcon
      hsmall
    exact ⟨M', Or.inl h⟩

/-- **No infinite sequence of floor flips.** Under `P(n)`, no sequence of models has each
obtained from the previous one by a floor flip. -/
private theorem not_forall_isFlipStep (hP : ProjectiveFloorProgramInputs n)
    (Ms : ℕ → Model sX Δ 𝓔 n S₀) : ¬ ∀ i, (Ms i).IsFlipStep (Ms (i + 1)) := by
  intro h
  choose Z sZ R f fp hf using h
  refine hP.2.2 (Ms 0).U ((Ms 0).π ≫ sX) (Ms 0).K (Ms 0).Γ (Ms 0).isFloorPair
    ⟨fun i => (Ms (i + 1)).U, fun i => (Ms (i + 1)).π ≫ sX, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
      fun i => (Ms (i + 1)).K, fun i => (Ms (i + 1)).Γ, Z, sZ,
      fun i => match i with
        | 0 => R 0
        | j + 1 => R (j + 1),
      fun i => match i with
        | 0 => f 0
        | j + 1 => f (j + 1),
      fp, fun i => ?_⟩
  rcases i with _ | j
  · exact ⟨(Ms 1).isProjectiveVariety, hf 0⟩
  · exact ⟨(Ms (j + 2)).isProjectiveVariety, hf (j + 1)⟩

/-- **Termination.** Some model has nef adjoint over `X`. Among all models take one with the
fewest exceptional valuations; from it every step is a flip keeping that number, so a failure
of termination would give an infinite sequence of floor flips. -/
private theorem exists_isNef (hP : ProjectiveFloorProgramInputs n)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (M₀ : Model sX Δ 𝓔 n S₀) : ∃ M : Model sX Δ 𝓔 n S₀, M.IsNef := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ k, ∃ M : Model sX Δ 𝓔 n S₀, M.excVals.card = k := ⟨_, M₀, rfl⟩
  set m := Nat.find hex with hm
  have hmin : ∀ M : Model sX Δ 𝓔 n S₀, m ≤ M.excVals.card := fun M =>
    Nat.find_min' hex ⟨M, rfl⟩
  have key : ∀ M : Model sX Δ 𝓔 n S₀, M.excVals.card = m →
      ∃ M' : Model sX Δ 𝓔 n S₀, M'.excVals.card = m ∧ M.IsFlipStep M' := by
    intro M hM
    obtain ⟨M', hM'⟩ := M.exists_step hP hX hΔ (hcon M)
    rcases hM' with hlt | ⟨hle, hflip⟩
    · exact absurd (hmin M') (by omega)
    · exact ⟨M', le_antisymm (hM ▸ hle) (hmin M'), hflip⟩
  obtain ⟨M₁, hM₁⟩ := Nat.find_spec hex
  let seq : ℕ → {M : Model sX Δ 𝓔 n S₀ // M.excVals.card = m} := fun i =>
    Nat.rec ⟨M₁, hM₁⟩ (fun _ M => ⟨(key M.1 M.2).choose, (key M.1 M.2).choose_spec.1⟩) i
  exact not_forall_isFlipStep hP (fun i => (seq i).1) fun i =>
    (key (seq i).1 (seq i).2).choose_spec.2

end Steps

/- ### The initial model -/

section Initial

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} {n : ℕ}

/-- A Stacks-projective morphism to a projective variety is projective in the sense of
`IsProjectiveMorphism`. -/
private theorem isProjectiveMorphism_of_isProjective {V Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z)
    (hp : IsProjective p) : IsProjectiveMorphism p :=
  ((isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 1 2).mp hp

/-- **Lifting a prime divisor along a proper birational morphism.** A prime divisor `F` of a
normal model `N` of `X` is the image of a prime divisor `F'` of any normal model `N'` mapping
properly and birationally to `N`, with the same valuation over `X`. -/
private theorem exists_primeDivisor_valuation_eq_of_isProper {N N' : Scheme.{0}}
    [IsIntegral N] [IsLocallyNoetherian N] [IsNormal N] [IsIntegral N'] [IsLocallyNoetherian N']
    [IsNormal N'] (p : N ⟶ X) (q : N' ⟶ N) [IsProper q] (hq : IsBirationalMorphism q)
    (hN : IsNormalVariety ℂ (p ≫ sX)) (hN' : IsNormalVariety ℂ ((q ≫ p) ≫ sX))
    (hp : IsBirationalMorphism p) (hqp : IsBirationalMorphism (q ≫ p))
    (F : MMP.Mori.PrimeDivisor N) :
    ∃ F' : MMP.Mori.PrimeDivisor N',
      (⟨N', q ≫ p, hN', hqp, F'⟩ : DivisorOver ℂ sX).valuation =
        (⟨N, p, hN, hp, F⟩ : DivisorOver ℂ sX).valuation := by
  haveI := hq.isDominant
  haveI := hp.isDominant
  obtain ⟨F', hF', hiso⟩ := exists_primeDivisor_isIso_stalkMap q hq F
  haveI := hiso
  refine ⟨F', valuation_eq_of_valuationOver_eq q (𝟙 N) p rfl (Category.id_comp p) hN' hN hqp hp ?_⟩
  rw [MMP.Fourfold.Oai4C1.valuationOver_eq_of_isIso q F' F hF',
    MMP.Fourfold.Oai4C1.valuationOver_eq_of_isIso (𝟙 N) F F rfl]

/-- **A normal projective model carrying given divisors.** For finitely many divisorial
valuations of `k(X)`, each the valuation of a proper divisor over the projective normal variety
`X`, there is a projective birational morphism `p : N ⟶ X` from a normal variety on which each of
them is the valuation of a prime divisor. The model is built one valuation at a time: the
valuation has a centre on the current model by the valuative criterion, and is realized on a
projective model over it (`MMP.Flips.exists_properDivisorOver_isProjective_of_dominates`). -/
private theorem exists_normalModel (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXn : IsNormalVariety ℂ sX)
    (T : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))
    (hT : ∀ s ∈ T, ∃ D : DivisorOver ℂ sX, IsProper D.f ∧ D.valuation = s) :
    ∃ (N : Scheme.{0}) (p : N ⟶ X) (hN : IsNormalVariety ℂ (p ≫ sX))
      (hp : IsBirationalMorphism p), IsProjectiveMorphism p ∧
      ∀ s ∈ T, ∃ F : MMP.Mori.PrimeDivisor N,
        (⟨N, p, hN, hp, F⟩ : DivisorOver ℂ sX).valuation = s := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨X, 𝟙 X, by simpa using hXn, isBirationalMorphism_of_isIso _,
      MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X),
      fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert s T hs ih =>
    obtain ⟨N, p, hN, hp, hpp, hF⟩ := ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
    obtain ⟨D, hDp, hDs⟩ := hT s (Finset.mem_insert_self s T)
    haveI : IsIntegral N := hN.1.toIsIntegral
    haveI : IsNormal N := hN.2
    haveI : LocallyOfFiniteType (p ≫ sX) := hN.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
    haveI : IsDominant p := hp.isDominant
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
    haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hN.1
    have hNp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
      (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hN.1, hpp.comp hX.isProjective⟩
    haveI := D.isIntegral
    haveI := D.isDominant
    -- the valuation `s` on `k(N)`
    let e : X.functionField ≃+* N.functionField :=
      RingEquiv.ofBijective (functionFieldMap p) hp.functionFieldMap_bijective
    set v : Valuation N.functionField (WithZero (Multiplicative ℤ)) :=
      s.comap (e.symm : N.functionField →+* X.functionField) with hvdef
    have hvs : v.comap (functionFieldMap p) = s := by
      ext a
      change s (e.symm (e a)) = s a
      rw [RingEquiv.symm_apply_apply]
    -- `v` is a divisor of `k(N)`
    have hv : MMP.Flips.IsDivisorOfFunctionField ℂ (p ≫ sX) v := by
      letI := functionFieldAlgebra sX
      letI := functionFieldAlgebra (p ≫ sX)
      letI := functionFieldAlgebra (D.f ≫ sX)
      letI := functionFieldMapAlgebra p
      letI := functionFieldMapAlgebra D.f
      haveI := isScalarTower_functionFieldMap sX p
      haveI := isScalarTower_functionFieldMap sX D.f
      let ep : X.functionField ≃ₐ[ℂ] N.functionField :=
        AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℂ X.functionField N.functionField)
          hp.functionFieldMap_bijective
      let eD : X.functionField ≃ₐ[ℂ] D.Y.functionField :=
        AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℂ X.functionField D.Y.functionField)
          D.isBirationalMorphism.functionFieldMap_bijective
      refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ep.symm.trans eD, ?_⟩
      rw [hvdef, ← hDs]
      ext a
      rfl
    -- its centre on `N`
    have hdom := MMP.Fourfold.SNCWeight.Restriction.dominates_divisorOver D
    rw [hDs, ← hvs] at hdom
    obtain ⟨y, hy, -⟩ := MMP.Fourfold.SNCWeight.SNCModel.exists_dominates_of_isProper p v _ hdom
    obtain ⟨D', hD'p, hD'v, -⟩ :=
      MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (p ≫ sX) hv y hy.1 hy.2
    haveI := D'.isIntegral
    haveI := D'.isNormal
    haveI := D'.isLocallyNoetherian
    haveI : IsProper D'.f := D'.isProper
    have hN' : IsNormalVariety ℂ ((D'.f ≫ p) ≫ sX) := by
      rw [Category.assoc]; exact D'.isNormalVariety
    have hp' : IsBirationalMorphism (D'.f ≫ p) :=
      MMP.Mori.isBirationalMorphism_comp D'.isBirationalMorphism hp
    refine ⟨D'.Y, D'.f ≫ p, hN', hp',
      (isProjectiveMorphism_of_isProjective hNp D'.f hD'p).comp hpp, fun t ht => ?_⟩
    rcases Finset.mem_insert.mp ht with rfl | ht
    · refine ⟨D'.E, ?_⟩
      have h := MMP.Mori.valuation_compDivisorOver p hN hp D'.toDivisorOver
      change _ = D'.valuation.comap (functionFieldMap p) at h
      exact h.trans (by rw [hD'v, hvs])
    · obtain ⟨F, hFt⟩ := hF t ht
      obtain ⟨F', hF'⟩ := exists_primeDivisor_valuation_eq_of_isProper p D'.f
        D'.isBirationalMorphism hN hN' hp hp' F
      exact ⟨F', hF'.trans hFt⟩

/-- A prime divisor lies in a closed set as soon as its generic point does. -/
private theorem support_subset_of_genericPoint_mem {Y : Scheme.{0}} {P : MMP.Mori.PrimeDivisor Y}
    {C : Set Y} (hC : IsClosed C) (hP : P.genericPoint ∈ C) : P.support ⊆ C := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact hC.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)

/-- Over a normal variety, a prime divisor of a proper birational model lies in the exceptional
locus exactly when its generic point maps to no generic point of a prime divisor. -/
private theorem subset_exceptionalLocus_iff_forall_ne (hX : IsNormalVariety ℂ sX)
    {Y : Scheme.{0}} {π : Y ⟶ X} [IsProper π] (hY : MMP.Mori.IsVariety ℂ (π ≫ sX))
    (hπ : IsBirationalMorphism π) (F : MMP.Mori.PrimeDivisor Y) :
    F.support ⊆ MMP.Intersection.exceptionalLocus π ↔
      ∀ Q : MMP.Mori.PrimeDivisor X, π F.genericPoint ≠ Q.genericPoint := by
  refine ⟨fun hF => MMP.Flips.map_genericPoint_ne_of_subset_exceptionalLocus hX hY hπ hF,
    fun hF => ?_⟩
  by_contra h1
  obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset h1
  exact hF Q hQ.symm

/-- **The initial model.** A projective log resolution of `(X, Δ)` on which every valuation of
`𝓔` is a prime divisor, with the boundary `Γ` of prescribed coefficients, is a model. -/
private theorem exists_initialModel (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = n) (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ)
    (𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))
    (h𝓔 : ∀ s ∈ 𝓔, MMP.Intersection.IsExceptionalValuation ℂ sX s ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sX Δ s a ∧ 0 < a ∧ a ≤ 1) :
    ∃ S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))),
      Nonempty (Model sX Δ 𝓔 n S₀) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1
  have hXn : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  obtain ⟨N, p, hN, hp, hpp, hNF⟩ := exists_normalModel hX hXn 𝓔 fun s hs => by
    obtain ⟨D, hD, hv, -⟩ := (h𝓔 s hs).1
    exact ⟨D, hD, hv.symm⟩
  haveI : IsIntegral N := hN.1.toIsIntegral
  haveI : IsNormal N := hN.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hN.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : QuasiCompact (p ≫ sX) := hN.1.toQuasiCompact
  haveI : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hN.1
  have hNp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hN.1, hpp.comp hX.isProjective⟩
  obtain ⟨EN, hEN⟩ := MMP.Intersection.exists_isExceptionalDivisorSum hp
  set BN : QDivisor N := MMP.Flips.birationalInverseTransform p hp Δ + Divisor.toQDivisor EN
    with hBN
  obtain ⟨Y, _, _, _, _, h, hlog, hhp, hYn₀, hYp₀, hdimY, hQY₀⟩ :=
    MMP.Mori.exists_isLogResolution_isQFactorial_isProjectiveVariety (p ≫ sX) hNp hN BN
  have hbh : IsBirationalMorphism h := hlog.isBirationalMorphism
  haveI : IsProper h := hlog.isProper
  have hsY : (h ≫ p) ≫ sX = h ≫ p ≫ sX := Category.assoc _ _ _
  have hYn : IsNormalVariety ℂ ((h ≫ p) ≫ sX) := by rwa [hsY]
  have hYp : MMP.Mori.IsProjectiveVariety ℂ ((h ≫ p) ≫ sX) := by rwa [hsY]
  have hQY : IsQFactorial ((h ≫ p) ≫ sX) := by rwa [hsY]
  have hπb : IsBirationalMorphism (h ≫ p) := MMP.Mori.isBirationalMorphism_comp hbh hp
  have hπp : IsProjectiveMorphism (h ≫ p) := hhp.comp hpp
  haveI : IsProper (h ≫ p) := isProper_of_isProjectiveMorphism _ hπp
  haveI : AlgebraicGeometry.IsVariety ℂ ((h ≫ p) ≫ sX) := hYn.1
  haveI : LocallyOfFiniteType ((h ≫ p) ≫ sX) := hYn.1.toLocallyOfFiniteType
  have hdimY' : topologicalKrullDim Y = n := by
    rw [hdimY, ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp,
      hdim]
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isPair hPB hdim
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme ((h ≫ p) ≫ sX)
    (by rw [hsY]; exact hlog.isSmoothScheme) (n := n) hdimY'
  obtain ⟨ΔY, hΔY, -⟩ := (hΔ.1.existsUnique_isCrepantBoundary hK (h ≫ p) hYn hπb).1
  obtain ⟨Eπ, hEπ⟩ := MMP.Intersection.exists_isExceptionalDivisorSum hπb
  set val : MMP.Mori.PrimeDivisor Y → Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
    fun F => (⟨Y, h ≫ p, hYn, hπb, F⟩ : DivisorOver ℂ sX).valuation with hval
  set c : MMP.Mori.PrimeDivisor Y → ℚ := fun F =>
    if F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) then
      (if val F ∈ 𝓔 then ΔY.coeff F else 1)
    else (MMP.Flips.birationalInverseTransform (h ≫ p) hπb Δ).coeff F with hc
  have hcfin : (Function.support c).Finite := by
    refine (MMP.Flips.birationalInverseTransform (h ≫ p) hπb Δ +
      Divisor.toQDivisor Eπ).support.finite_toSet.subset fun F hF => ?_
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
      MMP.Flips.coeff_birationalInverseTransform_add_exceptionalDivisorSum hXn hYn.1 hπb Δ hEπ F]
    by_cases h1 : F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p)
    · rw [if_pos h1]
      exact one_ne_zero
    · rw [if_neg h1]
      have : c F = (MMP.Flips.birationalInverseTransform (h ≫ p) hπb Δ).coeff F := by
        rw [hc]
        exact if_neg h1
      rwa [← this]
  set Γ : QDivisor Y := Finsupp.ofSupportFinite c hcfin with hΓ
  have hΓc : ∀ F, Γ.coeff F = c F := fun F => by
    rw [DivisorWithCoeffs.coeff_apply, hΓ, Finsupp.ofSupportFinite_coe]
  have hexc : ∀ F : MMP.Mori.PrimeDivisor Y,
      F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) ↔
        ∀ Q : MMP.Mori.PrimeDivisor X, (h ≫ p) F.genericPoint ≠ Q.genericPoint :=
    fun F => subset_exceptionalLocus_iff_forall_ne hXn hYn.1 hπb F
  have hnexc : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) →
        ∃ Q : MMP.Mori.PrimeDivisor X, (h ≫ p) F.genericPoint = Q.genericPoint ∧
          Γ.coeff F = Δ.coeff Q ∧ Γ.coeff F = ΔY.coeff F := by
    intro F hF
    obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
    have e1 : Γ.coeff F = (MMP.Flips.birationalInverseTransform (h ≫ p) hπb Δ).coeff F := by
      rw [hΓc, hc]; exact if_neg hF
    refine ⟨Q, hQ.symm, ?_, ?_⟩
    · rw [e1]
      exact MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hXn (h ≫ p) hYn.1 hπb Δ
        hQ.symm
    · rw [e1, ← MMP.Flips.coeff_eq_of_not_subset_of_isCrepantBoundary hΔY F hF]
  have hlogF : ∀ F : MMP.Mori.PrimeDivisor Y,
      IsValuationLogDiscrepancy sX Δ (val F) (1 - (ΔY.coeff F : ℝ)) := fun F =>
    ⟨n, ⟨Y, h ≫ p, hYn, hπb, F⟩, inferInstance, rfl,
      (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hΔY F) _).mpr
        ⟨inferInstance, by push_cast; ring⟩⟩
  have hle : ∀ F : MMP.Mori.PrimeDivisor Y, ΔY.coeff F ≤ 1 := by
    intro F
    obtain ⟨n', D, -, -, hl⟩ := hlogF F
    have := hΔ.2.2 n' D _ hl
    have h3 : ((ΔY.coeff F : ℚ) : ℝ) ≤ 1 := by linarith
    exact_mod_cast h3
  have hexcE : ∀ F : MMP.Mori.PrimeDivisor Y,
      F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) → val F ∈ 𝓔 →
        Γ.coeff F = ΔY.coeff F ∧ 0 ≤ ΔY.coeff F := by
    intro F hF hs
    refine ⟨by rw [hΓc, hc]; simp only [if_pos hF, if_pos hs], ?_⟩
    obtain ⟨a, ha, -, ha1⟩ := (h𝓔 _ hs).2
    obtain ⟨n₁, D₁, -, hv₁, hl₁⟩ := hlogF F
    obtain ⟨n₂, D₂, -, hv₂, hl₂⟩ := ha
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hΔ.1
      hl₁ hl₂ (hv₁.trans hv₂.symm)
    have h' : ((ΔY.coeff F : ℚ) : ℝ) ≥ 0 := by linarith
    exact_mod_cast h'
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor Y, 0 ≤ Γ.coeff F ∧ Γ.coeff F ≤ 1 := by
    intro F
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p)
    · by_cases hs : val F ∈ 𝓔
      · obtain ⟨e1, e2⟩ := hexcE F hF hs
        rw [e1]; exact ⟨e2, hle F⟩
      · have : Γ.coeff F = 1 := by rw [hΓc, hc]; simp only [if_pos hF, if_neg hs]
        rw [this]; norm_num
    · obtain ⟨Q, -, e1, e2⟩ := hnexc F hF
      exact ⟨e1 ▸ hΔ.2.1 Q, e2 ▸ hle F⟩
  have hsupp : ∀ P ∈ Γ.support, P.support ⊆
      ((exceptionalSet h ⊔ (QDivisor.toRDivisor BN).supp.preimage h.continuous :
        TopologicalSpace.Closeds Y) : Set Y) := by
    intro P hP
    by_cases hPh : P.support ⊆ MMP.Intersection.exceptionalLocus h
    · exact (hPh.trans (MMP.Flips.exceptionalLocus_subset_exceptionalSet h)).trans fun x hx =>
        Or.inl hx
    obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hPh
    have hBQ : BN.coeff Q ≠ 0 := by
      rw [hBN,
        MMP.Flips.coeff_birationalInverseTransform_add_exceptionalDivisorSum hXn hN.1 hp Δ hEN Q]
      split_ifs with hQe
      · exact one_ne_zero
      · obtain ⟨R, hR, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hQe
        have hPR : (h ≫ p) P.genericPoint = R.genericPoint := by
          rw [Scheme.Hom.comp_apply, ← hQ, hR]
        have hPe : ¬ P.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) :=
          fun hPe => (hexc P).mp hPe R hPR
        obtain ⟨R', hR', e1, -⟩ := hnexc P hPe
        have hRR' : R' = R := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (hR'.symm.trans hPR)
        subst hRR'
        change (MMP.Flips.birationalInverseTransform p hp Δ) Q ≠ 0
        rw [MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq hXn p hN.1 hp Δ hR.symm]
        change Δ.coeff R' ≠ 0
        rw [← e1, DivisorWithCoeffs.coeff_apply]
        exact Finsupp.mem_support_iff.mp hP
    have hBQ' : (QDivisor.toRDivisor BN).coeff Q ≠ 0 := by
      simpa [QDivisor.toRDivisor] using hBQ
    have hclosed : IsClosed (((QDivisor.toRDivisor BN).supp.preimage h.continuous :
        TopologicalSpace.Closeds Y) : Set Y) := TopologicalSpace.Closeds.isClosed _
    have hηP : P.genericPoint ∈
        ((QDivisor.toRDivisor BN).supp.preimage h.continuous : TopologicalSpace.Closeds Y) := by
      change h P.genericPoint ∈ ((QDivisor.toRDivisor BN).supp : Set N)
      rw [← hQ]
      refine DivisorWithCoeffs.support_subset_supp hBQ' ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    exact (support_subset_of_genericPoint_mem hclosed hηP).trans fun x hx => Or.inr hx
  have hsnc : Γ.IsSNC (h ≫ p ≫ sX) := hlog.isSNC_of_support_subset Γ hsupp
  have hKY₀ : KY.IsCanonicalDivisor (h ≫ p ≫ sX) n := by rwa [← hsY]
  have hdlt : MMP.Mori.IsDltPair (h ≫ p ≫ sX) n KY Γ := by
    refine ⟨⟨hYn₀, hKY₀, MMP.Fourfold.isQCartier_of_isQFactorial _ hQY₀ _⟩, hcoeff, ⊤, ?_, ?_, ?_⟩
    · exact hlog.isSmoothScheme.ge
    · exact hsnc.restrictOpen ⊤
    · intro D a hD _
      exfalso
      obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
      exact hD hx (by simp)
  have hdlt' : MMP.Intersection.IsDltPair ((h ≫ p) ≫ sX) Γ := by
    rw [hsY]
    exact (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (h ≫ p ≫ sX) hKY₀ Γ).mpr hdlt
  refine ⟨Eπ.support.image val, ⟨
    { U := Y
      π := h ≫ p
      K := KY
      Γ := Γ
      isProjectiveVariety := hYp
      dim_eq := hdimY'
      isQFactorial := hQY
      isCanonicalDivisor := hKY
      isDltPair := hdlt'
      isProjectiveMorphism := hπp
      isBirationalMorphism := hπb
      coeff_spec := fun F => ?_
      surv := fun s hs => ?_
      exc_mem := fun F hF => ?_ }⟩⟩
  · by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p)
    · refine Or.inr ⟨(hexc F).mp hF, ?_⟩
      by_cases hs : val F ∈ 𝓔
      · refine Or.inl ⟨hs, ?_⟩
        rw [(hexcE F hF hs).1]
        exact hlogF F
      · refine Or.inr ⟨hs, ?_⟩
        rw [hΓc, hc]; simp only [if_pos hF, if_neg hs]
    · obtain ⟨Q, hQ, e1, -⟩ := hnexc F hF
      exact Or.inl ⟨Q, hQ, e1⟩
  · obtain ⟨F, hF⟩ := hNF s hs
    obtain ⟨F', hF'⟩ := exists_primeDivisor_valuation_eq_of_isProper p h hbh hN hYn hp hπb F
    exact ⟨F', hF'.trans hF⟩
  · refine Finset.mem_image.mpr ⟨F, ?_, rfl⟩
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hEπ F, if_pos ((hexc F).mpr hF)]
    exact one_ne_zero

end Initial

/-- **Projective crepant dlt modification.** Assume `P(n)`. Let `(X, Δ)` be a log canonical pair
with `Δ` a `ℚ`-divisor on a normal projective complex `n`-fold `X`. Then there is a projective
birational `p : V ⟶ X` from a `ℚ`-factorial variety `V` (over `ℂ` through `p`) and a dlt boundary
`Δ_V` on `V` (effective, with rational coefficients) such that `K_V + Δ_V = p^*(K_X + Δ)` for
every canonical divisor `K_X`, and every `p`-exceptional prime divisor `E` of `V` has log
discrepancy `a(E; X, Δ) = 0` and coefficient one in `Δ_V`. -/
@[mmp "thm_fourfold_projective_dlt_modification_from_floor_inputs"]
public theorem ProjectiveFloorProgramInputs.exists_crepant_dltModification {n : ℕ}
    (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = n) {Δ : QDivisor X}
    (hΔ : MMP.Intersection.IsLogCanonicalPair sX Δ) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (hp : IsBirationalMorphism p) (hV : IsQFactorial (p ≫ sX))
      (ΔV : QDivisor V),
      IsProjectiveMorphism p ∧
      MMP.Intersection.IsDltPair (p ≫ sX) ΔV ∧
      (∀ K : Divisor X, K.IsCanonicalDivisor sX n →
        IsCrepantBoundary sX n K Δ p hV.1 hp ΔV) ∧
      ∀ E : MMP.Mori.PrimeDivisor V, RationalMap.IsExceptional (X := V) p.toRationalMap E →
        MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ)
          (⟨V, p, hV.1, hp, E⟩ : DivisorOver ℂ sX) 0 ∧
        ΔV.coeff E = 1 := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1
  have hXn : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨S₀, ⟨M₀⟩⟩ := exists_initialModel hX hdim hΔ ∅ fun s hs =>
    absurd hs (Finset.notMem_empty s)
  obtain ⟨M, hM⟩ := exists_isNef hP hX hΔ M₀
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isPair hPB hdim
  have hfin := M.isCrepantBoundary_of_isNef hΔ hM hK₀
  have hUnv : IsNormalVariety ℂ (M.π ≫ sX) := M.isQFactorial.1
  have : IsProper M.π := isProper_of_isProjectiveMorphism M.π M.isProjectiveMorphism
  refine ⟨M.U, inferInstance, inferInstance, inferInstance, M.π, M.isBirationalMorphism,
    M.isQFactorial, M.Γ, M.isProjectiveMorphism, M.isDltPair,
    fun K hK => M.isCrepantBoundary_of_isNef hΔ hM hK, fun E hE => ?_⟩
  have hEexc : ∀ Q : MMP.Mori.PrimeDivisor X, M.π E.genericPoint ≠ Q.genericPoint :=
    (isExceptional_iff_forall_ne hXn ⟨M.U, M.π, hUnv, M.isBirationalMorphism, E⟩).mp hE
  have hE1 : M.Γ.coeff E = 1 := by
    rcases M.coeff_spec E with ⟨Q, hQ, -⟩ | ⟨-, ⟨hs, -⟩ | ⟨-, h1⟩⟩
    · exact absurd hQ (hEexc Q)
    · exact absurd hs (Finset.notMem_empty _)
    · exact h1
  refine ⟨?_, hE1⟩
  exact (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hfin E) 0).mpr
    ⟨inferInstance, by rw [hE1]; norm_num⟩

end MMP.Fourfold
