module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
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
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus

/-!
# Crepant `ℚ`-factorial dlt models of lower-dimensional projective dlt pairs

Assume the lower-dimensional projective log minimal model program `P₃`
(`MMP.Fourfold.ProjectiveLowerLogMMP 3`). Then every projective complex dlt pair `(S, B)` with
rational boundary and `dim S ≤ 3` has a crepant `ℚ`-factorial dlt model. Take a projective log
resolution `p : Y ⟶ S` and let `Γ` be the strict transform of `B` plus the reduced exceptional
divisor, so that `K_Y + Γ = p^*(K_S + B) + E` with `E` effective and `p`-exceptional. The
projective MMP of the snc pair `(Y, Γ)` over `S` ends with a nef model `Y' ⟶ S` (not a Mori fibre
space, since every model is birational over `S`), and the push-forward of `E` to `Y'` is
effective, exceptional and nef over `S`, hence zero.

## Main results

* `MMP.Fourfold.ProjectiveLowerLogMMP.exists_isCrepantDltLift`: under `P₃`, a projective dlt pair
  of dimension at most three has a projective crepant `ℚ`-factorial dlt model.
* `MMP.Flips.birationalInverseTransform_apply_of_genericPoint_eq`: for a proper birational
  morphism `f : Y ⟶ X` of varieties with `X` normal and `f(η_E) = η_P`, `(f⁻¹_* D)_E = D_P`.
* `MMP.Flips.coeff_birationalInverseTransform_eq_zero_of_subset`,
  `MMP.Flips.coeff_birationalInverseTransform_add_exceptionalDivisorSum`: `μ⁻¹_* D` has no
  exceptional component, and `μ⁻¹_* D + Exc(μ)_red` has coefficient `1` on each.
* `MMP.Flips.coeff_eq_of_not_subset_of_isCrepantBoundary`: off the exceptional locus, the crepant
  boundary of `(X, B)` on `Y` agrees with `μ⁻¹_* B`.
* `MMP.Flips.isRIntersectionNumber_sum`, `MMP.Flips.forall_isRIntersectionNumber_eq_zero_iff`: a
  presentation `D = ∑ rⱼ Lⱼ` by Cartier divisors computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`, via
  `MMP.Flips.IsCartierIntersectionNumber.eq_degreeOn`.
* `MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor`: a `ℚ`-Cartier `ℚ`-divisor
  whose real divisor is `f`-nef is `f`-nef.
* `MMP.Mori.IsCrepantBoundary.isRelativelyNef_sub`: if `(X, Δ)` is anti-nef and `(X', Δ')` nef
  over `Y`, their crepant boundaries `Δ_Z`, `Δ'_Z` on a common model `Z` have `Δ'_Z - Δ_Z` nef
  over `Y`.
* `MMP.Fourfold.exists_primeDivisor_of_isOver`,
  `MMP.Mori.DivisorOver.valuation_eq_of_isIso_morphismRestrict`: along a map `φ : X ⤏ X'` over
  `Z` of proper birational models, a prime divisor of `X'` over a prime divisor of `Z` comes from a
  prime divisor of `X` with the same coefficients in `φ_* D` and the same valuation.
* `MMP.Flips.IsSmall.isBirationalMorphism_and_exists_primeDivisor`: a small contraction is
  birational and sends prime divisors to prime divisors.
* `MMP.Fourfold.RelativeDltProgram.exists_step`: the data of a step of a relative dlt program.
* `MMP.Mori.exists_isLogResolution_isQFactorial_isProjectiveVariety`: a projective complex normal
  variety with a `ℚ`-divisor has a projective log resolution from a projective `ℚ`-factorial
  variety of the same dimension; `MMP.Mori.IsLogResolution.isSNC_of_support_subset`: a divisor
  supported on `Ex(p) ∪ p⁻¹(Supp D)` is snc.
* `MMP.Intersection.exists_isExceptionalDivisorSum`: a birational morphism from an integral
  Noetherian scheme has a reduced exceptional divisor `Exc(μ)_red`.
* `MMP.Mori.isBirational_iff_of_isIntegral`, `MMP.Mori.isBirational_of_comp`: birationality at
  the generic point for integral schemes, and its cancellation on the left.
* `MMP.Mori.IsCrepantBoundary.coeff_isPullback_eq`: for the crepant boundary `Δ` of `(X, B)` on
  `U` and `K = div(ω)`, the coefficients of `div(p^*ω) + Δ` and `p^*(K + B)` agree.
* `MMP.Mori.Divisor.linearlyEquivalent_divisorOfForm`: the divisors of two nonzero rational top
  forms are linearly equivalent; `MMP.Mori.pullbackRationalPluriForms_ne_zero`.
* `MMP.Mori.QDivisor.intersectionNumber_eq_of_iso_comp`: intersection numbers along a curve
  depend on the curve only up to isomorphism over `X`.
* `MMP.Mori.IsVariety.isSeparated_terminal`: a variety is separated over `⊤_ Scheme`.

## Implementation notes

The model is stated as a crepant dlt lift (`MMP.Fourfold.IsCrepantDltLift`), which fixes its
boundary to be `p⁻¹_* B + Exc(p)_red`; the model is moreover a projective variety, with compact
underlying space, so that `P₃` applies to it. The auxiliary lemmas of the proof live in the
namespace `Proof_lem_mmp_projective_lower_dlt_model`; the instance
`AlgebraicGeometry.IsVariety.toIsIntegral` is switched off only for the main statement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips

open TopologicalSpace MMP.Mori

/-! ### Strict transforms under the inverse of a birational morphism -/

variable {X Y : Scheme.{u}}

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    have hs : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
    rw [hs, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- Let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If
`f` sends the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`,
then the strict transform of `P` under `f⁻¹` is `E`. -/
theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal sX
  have := isSeparated_terminal (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal sX
  have := isSeparated_terminal (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
theorem _root_.MMP.Mori.IsVariety.isSeparated_terminal {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) :=
  have : IsSeparated sX := hX.toIsSeparated
  MMP.Flips.isSeparated_terminal sX

/-- The coefficient of `μ⁻¹_* D` along a prime divisor `E` lying over no prime divisor of `X`
vanishes. -/
theorem coeff_birationalInverseTransform_eq_zero {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {μ : Y ⟶ X} (hY : MMP.Mori.IsVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, μ E.genericPoint ≠ P.genericPoint) :
    MMP.Flips.birationalInverseTransform μ hμ D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have := hX.isSeparated_terminal
  have := hY.isSeparated_terminal
  exact mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hμ hP)) D

/-- The exceptional locus of a morphism lies in its exceptional set. -/
theorem exceptionalLocus_subset_exceptionalSet {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MMP.Intersection.exceptionalLocus f ⊆ (Mori.exceptionalSet f : Set X) := by
  intro x hx
  by_contra h
  have hU : x ∈ f ⁻¹ᵁ biregularLocus f := by
    simpa [Mori.exceptionalSet] using h
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine MMP.Intersection.mem_exceptionalLocus_iff.mp hx _ hU ?_
  rw [← morphismRestrict_ι]
  infer_instance

/-- A proper birational morphism `μ : Y ⟶ X` of varieties onto a normal variety is an isomorphism
over a neighbourhood of every point `x` of `X` whose local ring is a valuation ring (the generic
point, and the generic points of the prime divisors). -/
theorem mem_biregularLocus_of_valuationRing {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (x : X)
    [ValuationRing (X.presheaf.stalk x)] : x ∈ biregularLocus μ := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : IsDominant μ := hμ.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have : IsSeparated μ := IsSeparated.of_comp μ sX
  have hbij := hμ.functionFieldMap_bijective
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ)).1 inferInstance
  refine le_biregularLocus (f := μ) (V := ⟨_, hU⟩) hiso ?_
  change (μ ⁻¹' {x}).Finite
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  have ha' : μ a = x := ha
  have hb' : μ b = x := hb
  have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
  have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
  exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)

/-- A prime divisor `F` of `Y` contained in the exceptional locus of a proper birational morphism
`μ : Y ⟶ X` of varieties onto a normal variety does not lie over a prime divisor `P` of `X`. -/
theorem map_genericPoint_ne_of_subset_exceptionalLocus {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    {F : MMP.Mori.PrimeDivisor Y} (hF : F.support ⊆ MMP.Intersection.exceptionalLocus μ)
    (P : MMP.Mori.PrimeDivisor X) : μ F.genericPoint ≠ P.genericPoint := by
  intro h
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsNormal X := hX.2
  have := P.isDiscreteValuationRing_localRing
  have hη : F.genericPoint ∈ F.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hexc := exceptionalLocus_subset_exceptionalSet μ (hF hη)
  exact (by simpa [Mori.exceptionalSet, h] using hexc : P.genericPoint ∉ biregularLocus μ)
    (mem_biregularLocus_of_valuationRing hX hY hμ _)

/-- The birational transform `μ⁻¹_* D` of a divisor under the inverse of a birational morphism
`μ` has no `μ`-exceptional component. -/
theorem coeff_birationalInverseTransform_eq_zero_of_subset {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (D : QDivisor X) (F : MMP.Mori.PrimeDivisor Y)
    (hF : F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    (MMP.Flips.birationalInverseTransform μ hμ D).coeff F = 0 :=
  coeff_birationalInverseTransform_eq_zero hX.1 hY hμ D
    (map_genericPoint_ne_of_subset_exceptionalLocus hX hY hμ hF)

open Classical in
/-- The coefficients of `μ⁻¹_* D + Exc(μ)_red`: `1` along a prime divisor in the exceptional locus
of `μ`, and the coefficient of `μ⁻¹_* D` elsewhere. -/
theorem coeff_birationalInverseTransform_add_exceptionalDivisorSum {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (D : QDivisor X) {E : Divisor Y} (hE : MMP.Intersection.IsExceptionalDivisorSum μ E)
    (F : MMP.Mori.PrimeDivisor Y) :
    (MMP.Flips.birationalInverseTransform μ hμ D + Divisor.toQDivisor E).coeff F =
      if F.support ⊆ MMP.Intersection.exceptionalLocus μ then 1 else
        (MMP.Flips.birationalInverseTransform μ hμ D).coeff F := by
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hE F]
  split_ifs with hF
  · rw [coeff_birationalInverseTransform_eq_zero_of_subset hX hY hμ D F hF]
    simp
  · simp

/-- The coefficient of `μ⁻¹_* D + Exc(μ)_red` along a prime divisor in the exceptional locus of
`μ` is `1`. -/
theorem coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_subset {Y X : Scheme.{0}}
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (D : QDivisor X) {E : Divisor Y} (hE : MMP.Intersection.IsExceptionalDivisorSum μ E)
    {F : MMP.Mori.PrimeDivisor Y} (hF : F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    (MMP.Flips.birationalInverseTransform μ hμ D + Divisor.toQDivisor E).coeff F = 1 := by
  classical
  rw [coeff_birationalInverseTransform_add_exceptionalDivisorSum hX hY hμ D hE F, if_pos hF]

/-- The coefficient of `μ⁻¹_* D + Exc(μ)_red` along a prime divisor `F` with `μ(η_F) = η_Q` is
the coefficient of `D` along `Q`. -/
theorem coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_genericPoint_eq
    {Y X : Scheme.{0}} [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X} [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : QDivisor X) {E : Divisor Y}
    (hE : MMP.Intersection.IsExceptionalDivisorSum μ E) {F : MMP.Mori.PrimeDivisor Y}
    {Q : MMP.Mori.PrimeDivisor X} (h : μ F.genericPoint = Q.genericPoint) :
    (MMP.Flips.birationalInverseTransform μ hμ D + Divisor.toQDivisor E).coeff F = D.coeff Q := by
  classical
  rw [coeff_birationalInverseTransform_add_exceptionalDivisorSum hX hY hμ D hE F,
    if_neg fun hF => map_genericPoint_ne_of_subset_exceptionalLocus hX hY hμ hF Q h]
  exact birationalInverseTransform_apply_of_genericPoint_eq hX μ hY hμ D h

/-- On a prime divisor `F` of `Y` not contained in the exceptional locus of `μ`, the crepant
boundary `Δ_Y` has the same coefficient as `μ⁻¹_* B`. -/
theorem coeff_eq_of_not_subset_of_isCrepantBoundary {Y X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {μ : Y ⟶ X} [IsProper μ] {hY : IsNormalVariety ℂ (μ ≫ sX)}
    {hμ : IsBirationalMorphism μ} {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K B μ hY hμ ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    ΔY.coeff F = (MMP.Flips.birationalInverseTransform μ hμ B).coeff F := by
  obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
  have hX : IsNormalVariety ℂ sX := (h F).1
  have e := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
    (D := ⟨Y, μ, hY, hμ, F⟩) hQ.symm (h F)
  have e2 := birationalInverseTransform_apply_of_genericPoint_eq hX μ hY.1 hμ B hQ.symm
  change _ = (MMP.Flips.birationalInverseTransform μ hμ B) F
  rw [e2]
  change ΔY.coeff F = B.coeff Q
  linarith

/-! ### `ℝ`-intersection numbers as degrees along proper curves -/

section RIntersectionDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  exact ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => by rw [(hd j).eq_degreeOn]⟩

/-- `D · C = 0` for every presentation of `D` if and only if one presentation gives
`∑ rⱼ deg_C 𝒪_X(Lⱼ) = 0`. -/
theorem forall_isRIntersectionNumber_eq_zero_iff (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    (∀ (m' : ℕ) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (x : ℝ),
        IsRIntersectionNumber k sX D r' L' C x → x = 0) ↔
      ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) = 0 := by
  refine ⟨fun h => h _ r L _ (isRIntersectionNumber_sum C r L hL hD), fun h m' r' L' x hx => ?_⟩
  rw [← h]
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 D r' L' r L x _ hx
    (isRIntersectionNumber_sum C r L hL hD)

end RIntersectionDegree

end MMP.Flips

namespace Proof_lem_mmp_projective_lower_dlt_model

open TopologicalSpace MMP.Mori MMP.Fourfold
open MMP.Flips (genericPoint_eq_of_transformPrimeDivisor_eq_some
  exceptionalLocus_subset_exceptionalSet mem_biregularLocus_of_valuationRing
  map_genericPoint_ne_of_subset_exceptionalLocus
  coeff_birationalInverseTransform_add_exceptionalDivisorSum
  coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_subset
  coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_genericPoint_eq
  coeff_eq_of_not_subset_of_isCrepantBoundary isRIntersectionNumber_sum)

/-- A birational morphism `μ : Y ⟶ X` from an integral Noetherian scheme has an exceptional
divisor `Exc(μ)_red`. -/
theorem _root_.MMP.Intersection.exists_isExceptionalDivisorSum {Y X : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] {μ : Y ⟶ X} (hμ : IsBirationalMorphism μ) :
    ∃ E : Divisor Y, MMP.Intersection.IsExceptionalDivisorSum μ E := by
  classical
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  obtain ⟨e, he⟩ := hμ
  obtain ⟨W, hW, hWe, hWr, hWeq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWe' : W ≤ e.source := hWe
  have hWι : IsOpenImmersion (W.ι ≫ μ) := by
    have h : W.ι ≫ μ = Y.homOfLE hWe' ≫ e.iso.hom ≫ e.target.ι := by
      have h := hWeq.symm
      simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom] at h
      rw [Scheme.topIso_hom] at h
      change Y.homOfLE (le_top : W ≤ ⊤) ≫ (⊤ : Y.Opens).ι ≫ μ =
        Y.homOfLE hWe' ≫ e.iso.hom ≫ e.target.ι at h
      rw [← Category.assoc, Scheme.homOfLE_ι] at h
      exact h
    rw [h]; infer_instance
  have hη : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by
      obtain ⟨y, hy⟩ := hW.nonempty; exact ⟨y, trivial, hy⟩)
  have hsub : ∀ P : MMP.Mori.PrimeDivisor Y,
      P.support ⊆ MMP.Intersection.exceptionalLocus μ → P.genericPoint ∉ W := by
    intro P hP hmem
    exact MMP.Intersection.mem_exceptionalLocus_iff.mp
      (hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl))
      W hmem hWι
  have hfin : {P : MMP.Mori.PrimeDivisor Y |
      P.support ⊆ MMP.Intersection.exceptionalLocus μ}.Finite := by
    refine Set.Finite.of_finite_image
      ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) W hη).subset ?_)
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    rintro - ⟨P, hP, rfl⟩
    exact ⟨by rw [(genericPoint_spec Y).def]; trivial, hsub P hP, P.coheight_genericPoint⟩
  refine ⟨Finsupp.ofSupportFinite
    (fun P => if P.support ⊆ MMP.Intersection.exceptionalLocus μ then (1 : ℤ) else 0)
    (hfin.subset fun P hP => by by_contra h; exact hP (if_neg h)), fun _ => rfl⟩

/-! ### Birationality at the generic point -/

/-- For integral schemes, `f` is birational if and only if it maps the generic point to the generic
point and its stalk map there is an isomorphism. -/
theorem _root_.MMP.Mori.isBirational_iff_of_isIntegral {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) :
    IsBirational f ↔
      f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  unfold IsBirational
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  simp

/-- If `f` and `f ≫ g` are birational at the generic point, so is `g`. -/
theorem _root_.MMP.Mori.isBirational_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirational f) (hfg : IsBirational (f ≫ g)) :
    IsBirational g := by
  rw [isBirational_iff_of_isIntegral] at *
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hfg1, hfg2⟩ := hfg
  refine ⟨by rw [← hf1, ← Scheme.Hom.comp_apply, hfg1], ?_⟩
  rw [Scheme.Hom.stalkMap_comp] at hfg2
  have : IsIso (g.stalkMap (f (genericPoint X))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hf2 hfg2
  exact hf1 ▸ this

/-! ### Crepant dlt lifts -/

/-- **Recognizing a crepant dlt lift.** Let `p : U ⟶ S` be a projective birational morphism from
a `ℚ`-factorial variety, `Δ` the crepant boundary of the projective lc pair `(S, B)` on `U`, with
`(U, Δ)` dlt and `coeff_F Δ = 1` on every prime divisor `F` in the exceptional locus of `p`. Then
`Δ = p⁻¹_* B + Exc(p)_red` and `p` is a crepant dlt lift of `(S, B)`. -/
private theorem isCrepantDltLift_of_isCrepantBoundary
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {K : Divisor S} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sS n)
    {B : QDivisor S} (hB : MMP.Intersection.IsDltPair sS B)
    {U : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {p : U ⟶ S} (hp : IsProjectiveMorphism p) (hbir : IsBirationalMorphism p)
    (hQ : IsQFactorial (p ≫ sS)) {Δ : QDivisor U}
    (hΔ : MMP.Intersection.IsDltPair (p ≫ sS) Δ)
    (hcrep : ∃ n : ℕ, IsCrepantBoundary sS n K B p hQ.1 hbir Δ)
    (hexc : ∀ F : MMP.Mori.PrimeDivisor U,
      F.support ⊆ MMP.Intersection.exceptionalLocus p → Δ.coeff F = 1) :
    IsCrepantDltLift sS K B p Δ := by
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have hX : IsNormalVariety ℂ sS := hB.1.1.1
  refine ⟨hS, hB.1, hK, hp, hbir, hQ, ?_, hΔ, hcrep⟩
  obtain ⟨n, hn⟩ := hcrep
  obtain ⟨E, hE⟩ := MMP.Intersection.exists_isExceptionalDivisorSum hbir
  refine ⟨E, hE, DivisorWithCoeffs.ext' fun F => ?_⟩
  rw [coeff_birationalInverseTransform_add_exceptionalDivisorSum hX hQ.1.1 hbir B hE F]
  split_ifs with hF
  · exact hexc F hF
  · exact coeff_eq_of_not_subset_of_isCrepantBoundary (μ := p) hn F hF

/-! ### The log resolution -/

/-- A projective complex normal variety `S`, with a `ℚ`-divisor `B`,
has a projective log resolution `p : Y ⟶ S` of `(S, B)` with `Y` a projective `ℚ`-factorial
normal variety of the dimension of `S`. -/
theorem _root_.MMP.Mori.exists_isLogResolution_isQFactorial_isProjectiveVariety
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hX : IsNormalVariety ℂ sS) (B : QDivisor S) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (p : Y ⟶ S),
      IsLogResolution sS (QDivisor.toRDivisor B) p ∧ IsProjectiveMorphism p ∧
      IsNormalVariety ℂ (p ≫ sS) ∧ MMP.Mori.IsProjectiveVariety ℂ (p ≫ sS) ∧
      topologicalKrullDim Y = topologicalKrullDim S ∧ IsQFactorial (p ≫ sS) := by
  obtain ⟨Y, p, hlog, hproj⟩ :=
    MMP.Mori.exists_isLogResolution_isProjectiveMorphism sS hX (QDivisor.toRDivisor B)
  obtain ⟨hW, hdimW, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral Y := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sS) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sS)
  haveI : IsNormal Y := hW.2
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sS) := hW.1
  haveI : AlgebraicGeometry.IsVariety ℂ sS := hS.toIsVariety
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (p ≫ sS)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, p, hlog, hproj, hW,
    ⟨hproj.comp hS.isProjective⟩, hdimW, hW, fun D => ⟨1, one_pos, ?_⟩⟩
  simpa using MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hlog.isSmoothScheme D

/-! ### The boundary of the log resolution -/

/-- A divisor on the source of a log resolution of `(S, D)` all of whose components lie in
`Ex(p) ∪ p⁻¹(Supp D)` is snc. -/
theorem _root_.MMP.Mori.IsLogResolution.isSNC_of_support_subset {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {D : RDivisor S} {p : Y ⟶ S}
    (hlog : IsLogResolution sS D p) [LocallyOfFinitePresentation (p ≫ sS)] {R : Type*} [Zero R]
    (Γ : DivisorWithCoeffs R Y)
    (hΓ : ∀ P ∈ Γ.support,
      P.support ⊆ ((exceptionalSet p ⊔ D.supp.preimage p.continuous : Closeds Y) : Set Y)) :
    Γ.IsSNC (p ≫ sS) := by
  classical
  have hη : ∀ P : MMP.Mori.PrimeDivisor Y, P.genericPoint ∈ P.support := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := R) (p ≫ sS)
      hlog.isSmoothScheme).of_support_subset fun P hP => ?_
    have := hΓ P hP (hη P)
    simp [h] at this
  · refine hsnc.of_support_subset fun P hP => ?_
    have hP' := hΓ P hP (hη P)
    rw [← hs] at hP'
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hP'
    have hEP := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
    subst hEP
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE]

/-- **The log resolution model.** A projective dlt pair `(S, B)` of dimension at most three has a
projective log resolution `p : Y ⟶ S` with `Y` a projective `ℚ`-factorial variety of the same
dimension, such that `Γ = p⁻¹_* B + Exc(p)_red` makes `(Y, Γ)` dlt and `K_Y + Γ - p^*(K + B)`
is effective: `Γ_F + a(F, S, B) ≥ 0` for every prime divisor `F` of `Y`. -/
private theorem exists_resolution_model
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S ≤ 3) (K : Divisor S) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sS n)
    (B : QDivisor S) (hB : MMP.Intersection.IsDltPair sS B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (p : Y ⟶ S) (KY : Divisor Y) (Γ : QDivisor Y)
      (hbir : IsBirationalMorphism p),
      IsProjectiveMorphism p ∧ MMP.Mori.IsProjectiveVariety ℂ (p ≫ sS) ∧
      topologicalKrullDim Y ≤ 3 ∧ IsQFactorial (p ≫ sS) ∧
      (∃ m : ℕ, KY.IsCanonicalDivisor (p ≫ sS) m) ∧ MMP.Intersection.IsDltPair (p ≫ sS) Γ ∧
      (∃ E : Divisor Y, MMP.Intersection.IsExceptionalDivisorSum p E ∧
        Γ = MMP.Flips.birationalInverseTransform p hbir B + Divisor.toQDivisor E) ∧
      ∃ (n : ℕ) (hY : IsNormalVariety ℂ (p ≫ sS)), K.IsCanonicalDivisor sS n ∧
        ∀ F : MMP.Mori.PrimeDivisor Y, ∃ a : ℚ,
          IsDiscrepancy sS n K B ⟨Y, p, hY, hbir, F⟩ a ∧ 0 ≤ Γ.coeff F + a := by
  classical
  have hX : IsNormalVariety ℂ sS := hB.1.1.1
  have hPB : MMP.Mori.IsPair sS B := hB.1.1
  obtain ⟨Y, _, _, _, _, p, hlog, hproj, hW, hYproj, hdimY, hQ⟩ :=
    exists_isLogResolution_isQFactorial_isProjectiveVariety sS hS hX B
  have hbir : IsBirationalMorphism p := hlog.isBirationalMorphism
  have : IsProper p := hlog.isProper
  haveI : LocallyOfFiniteType (p ≫ sS) := hW.1.toLocallyOfFiniteType
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sS)
    hlog.isSmoothScheme (n := n) (hdimY.trans hKn.topologicalKrullDim_eq)
  obtain ⟨E, hE⟩ := MMP.Intersection.exists_isExceptionalDivisorSum hbir
  set Γ : QDivisor Y := MMP.Flips.birationalInverseTransform p hbir B + Divisor.toQDivisor E
    with hΓdef
  obtain ⟨ΔY, hΔY, -⟩ := (hPB.existsUnique_isCrepantBoundary hKn p hW hbir).1
  -- coefficients of `Γ`
  have hΓexc : ∀ F : MMP.Mori.PrimeDivisor Y,
      F.support ⊆ MMP.Intersection.exceptionalLocus p → Γ.coeff F = 1 := fun _ hF =>
    coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_subset hX hW.1 hbir B hE hF
  have hΓne : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ F.support ⊆ MMP.Intersection.exceptionalLocus p →
        Γ.coeff F = (MMP.Flips.birationalInverseTransform p hbir B).coeff F := by
    intro F hF
    rw [hΓdef, coeff_birationalInverseTransform_add_exceptionalDivisorSum hX hW.1 hbir B hE F,
      if_neg hF]
  have hΓB : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ F.support ⊆ MMP.Intersection.exceptionalLocus p →
        ∃ Q : MMP.Mori.PrimeDivisor S, p F.genericPoint = Q.genericPoint ∧
          Γ.coeff F = B.coeff Q := by
    intro F hF
    obtain ⟨Q, hQF, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
    exact ⟨Q, hQF.symm,
      coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_genericPoint_eq hX hW.1 hbir B
        hE hQF.symm⟩
  -- the discrepancy comparison
  have hdisc : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ a : ℚ,
      IsDiscrepancy sS n K B ⟨Y, p, hW, hbir, F⟩ a ∧ 0 ≤ Γ.coeff F + a := by
    intro F
    refine ⟨-ΔY.coeff F, hΔY F, ?_⟩
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus p
    · have hlogd := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hΔY F)
        (1 + ((-ΔY.coeff F : ℚ) : ℝ))).mpr ⟨hlog.isProper, rfl⟩
      have h0 := hB.1.2.2 n _ _ hlogd
      rw [hΓexc F hF]
      have : (0 : ℝ) ≤ ((1 + -ΔY.coeff F : ℚ) : ℝ) := by push_cast at h0 ⊢; exact h0
      exact_mod_cast this
    · rw [hΓne F hF, ← coeff_eq_of_not_subset_of_isCrepantBoundary (μ := p) hΔY F hF]
      simp
  -- the coefficients of `Γ` lie in `[0, 1]`
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor Y, 0 ≤ Γ.coeff F ∧ Γ.coeff F ≤ 1 := by
    intro F
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus p
    · rw [hΓexc F hF]; norm_num
    · obtain ⟨Q, -, hQ⟩ := hΓB F hF
      rw [hQ]
      exact ⟨hB.1.2.1 Q, hB.2.1 Q⟩
  -- the components of `Γ` lie in `Ex(p) ∪ p⁻¹(Supp B)`
  have hsupp : ∀ P ∈ Γ.support, P.support ⊆
      ((exceptionalSet p ⊔ (QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) :
        Set Y) := by
    intro P hP
    by_cases hF : P.support ⊆ MMP.Intersection.exceptionalLocus p
    · exact (hF.trans (exceptionalLocus_subset_exceptionalSet p)).trans
        (fun x hx => Or.inl hx)
    · obtain ⟨Q, hPQ, hQ⟩ := hΓB P hF
      have hBQ : B.coeff Q ≠ 0 := hQ ▸ Finsupp.mem_support_iff.mp hP
      have hBQ' : (QDivisor.toRDivisor B).coeff Q ≠ 0 := by
        simpa [QDivisor.toRDivisor] using hBQ
      have hclosed : IsClosed (((QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) :
          Set Y) := Closeds.isClosed _
      have hηP : P.genericPoint ∈
          ((QDivisor.toRDivisor B).supp.preimage p.continuous : Closeds Y) := by
        change p P.genericPoint ∈ ((QDivisor.toRDivisor B).supp : Set S)
        rw [hPQ]
        refine DivisorWithCoeffs.support_subset_supp hBQ' ?_
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      intro x hx
      right
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
      exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηP) hx
  have hsnc : Γ.IsSNC (p ≫ sS) := hlog.isSNC_of_support_subset Γ hsupp
  -- `(Y, Γ)` is dlt
  have hdlt : MMP.Mori.IsDltPair (p ≫ sS) n KY Γ := by
    refine ⟨⟨hW, hKY, MMP.Fourfold.isQCartier_of_isQFactorial _ hQ _⟩, hcoeff, ⊤, ?_, ?_, ?_⟩
    · exact hlog.isSmoothScheme.ge
    · exact hsnc.restrictOpen ⊤
    · intro D a hD _
      exfalso
      obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
      exact hD hx (by simp)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, p, KY, Γ, hbir, hproj,
    hYproj, hdimY ▸ hdim, hQ, ⟨n, hKY⟩,
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (p ≫ sS) hKY Γ).mpr hdlt, ⟨E, hE, rfl⟩,
    n, hW, hKn, hdisc⟩

/-! ### Intersection numbers along proper curves -/

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- **The two notions of relative nefness agree.** A `ℚ`-Cartier `ℚ`-divisor `D` whose real
divisor is `f`-nef, with intersection numbers computed from a presentation by Cartier divisors, is
`f`-nef in the `ℚ`-Cartier sense: both compute `D · C` as the degree of `D` along `C`. -/
theorem _root_.MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor [IsIntegral X]
    {Y : Scheme.{u}} {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D)) :
    QDivisor.IsRelativelyNef sX f D := by
  obtain ⟨m, r, L, hL, hDeq, hnn⟩ := h
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD fun C hC => ?_
  set c := D.cartierIndex hD
  have hc : (0 : ℚ) < c := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set M : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hM : M.IsCartier := (D.cartierIndexSMul hD).2
  have hMD := QDivisor.toQDivisor_cartierIndexSMul D hD
  have hDR : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 : ℝ) / c) • Divisor.toRDivisor M := by
    ext P
    have hP := congrArg (fun E => DivisorWithCoeffs.coeff E P) hMD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hP
    simp only [QDivisor.coeff_toRDivisor, Finset.univ_unique, Finset.sum_singleton,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have : ((M.coeff P : ℚ) : ℝ) = (c : ℝ) * (D.coeff P : ℝ) := by
      rw [hP]; push_cast; ring
    rw [show ((M.coeff P : ℤ) : ℝ) = ((M.coeff P : ℚ) : ℝ) by push_cast; rfl, this]
    field_simp
  have hx := isRIntersectionNumber_sum C r L hL hDeq
  have hy := isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ) / c) (fun _ => M)
    (fun _ => hM) hDR
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ _ _ hx hy
  have h0 := hnn C hC _ hx
  rw [heq] at h0
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD M hM hMD]
  simp only [Finset.univ_unique, Finset.sum_singleton] at h0
  have : (0 : ℝ) ≤ ((M.degreeOn k sX C.ι C.dim_le hM : ℚ) / c : ℚ) := by
    push_cast
    rw [div_eq_mul_one_div, mul_comm]
    exact h0
  exact_mod_cast this

end RIntersection

/-! ### Relative nefness of a difference of crepant boundaries -/

section CommonModel

open AlgebraicGeometry hiding PrimeDivisor

section Crepancy

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] in
/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
theorem _root_.MMP.Mori.IsCrepantBoundary.coeff_isPullback_eq {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK Γ, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
  have hCq : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hE
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgen : GeneratesOn B m V τ := by
    refine ⟨hτ0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, h1, h2⟩ := hKcoeff Γ
    have h3 := hgord Γ hΓ
    qify at h1 h2 h3
    linear_combination h2 - hCq Γ - h3 - (m : ℚ) * h1
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, h]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ, hgen, ?_⟩
    qify at hordτ hKY hcoeff
    rw [hordτ, hKY, hcoeff]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
theorem _root_.MMP.Mori.pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end Crepancy

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Intersection numbers are unchanged by an isomorphism of curves over `X`. -/
theorem _root_.MMP.Mori.QDivisor.intersectionNumber_eq_of_iso_comp [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{u}}
    (i : C ⟶ X) (i' : C' ⟶ X) [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C')
    (he : e.hom ≫ i' = i) (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

end Curves

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
theorem _root_.MMP.Mori.Divisor.linearlyEquivalent_divisorOfForm {k : Type u} [Field k]
    [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hω : ω ≠ 0) : Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- If `-(K_X + Δ)` is `f`-nef and `K_{X'} + Δ'` is `f'`-nef, the crepant boundaries `Δ_Z`, `Δ'_Z`
on a common model `Z` satisfy: `Δ'_Z - Δ_Z` is `(g ≫ f)`-nef. -/
theorem _root_.MMP.Mori.IsCrepantBoundary.isRelativelyNef_sub {k : Type u} [Field k]
    [PerfectField k] {n : ℕ} {X X' Y Z : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [QuasiCompact sX] [QuasiCompact sX']
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {f' : X' ⟶ Y} [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX)
    (hfs' : f' ≫ sY = sX') (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f')
    {KX : Divisor X} {KX' : Divisor X'} (hK : KX.IsCanonicalDivisor sX n)
    (hK' : KX'.IsCanonicalDivisor sX' n) {Δ : QDivisor X} {Δ' : QDivisor X'}
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hN' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor KX' + Δ'))
    {g : Z ⟶ X} {g' : Z ⟶ X'} [IsProper g] [IsProper g'] (hZ : IsNormalVariety k (g ≫ sX))
    (hZ' : IsNormalVariety k (g' ≫ sX'))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ f = g' ≫ f')
    {ΔZ ΔZ' : QDivisor Z} (hΔZ : IsCrepantBoundary sX n KX Δ g hZ hg ΔZ)
    (hΔZ' : IsCrepantBoundary sX' n KX' Δ' g' hZ' hg' ΔZ') :
    QDivisor.IsRelativelyNef (g ≫ sX) (g ≫ f) (ΔZ' - ΔZ) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g ≫ sX) := hZ.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (g' ≫ sX') := hZ'.1.toLocallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace sX'
  have : QuasiCompact (g ≫ sX) := hZ.1.toQuasiCompact
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsDominant g := hg.isDominant
  have : IsDominant g' := hg'.isDominant
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sX' := hX'.1
  have : AlgebraicGeometry.IsVariety k (g ≫ sX) := hZ.1
  have hsZ : g' ≫ sX' = g ≫ sX := by
    rw [← hfs', ← Category.assoc, ← hcomm, Category.assoc, hfs]
  have hnZ : topologicalKrullDim Z = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hg, hK.1]
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ω', hω0', hωK'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX' hK'
  have hLB : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX + Δ).supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hLB' : ∀ W : irreducibleComponents Z, g' (componentGenericPoint Z W) ∉
      (Divisor.toQDivisor KX' + Δ').supp := fun W => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω)
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω')
  have hpb := IsCrepantBoundary.isPullback_divisorOfForm_add hX hZ hg hK hΔZ hω0 hωK hLB
  have hpb' := IsCrepantBoundary.isPullback_divisorOfForm_add hX' hZ' hg' hK' hΔZ' hω0' hωK' hLB'
  have hQ : (Divisor.toQDivisor KX + Δ).IsQCartier := by
    simpa using hN.1.neg
  have hQ' : (Divisor.toQDivisor KX' + Δ').IsQCartier := hN'.1
  have hB := hpb.isQCartier hQ
  have hA := hpb'.isQCartier hQ'
  have hne : pullbackRationalPluriForms sX g ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hg hK.1 hω0
  have hne' : pullbackRationalPluriForms sX' g' ω' ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX' hg' hK'.1 hω0'
  have hlin : KZ'.LinearlyEquivalent KZ := by
    have key : ∀ (s : Z ⟶ Spec (.of k)) (_ : s = g ≫ sX) [LocallyOfFiniteType s]
        (τ : RationalPluriForms s n 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent KZ := by
      rintro s rfl _ τ hτ
      exact Divisor.linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ hne'
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ)).IsQCartier := hB.neg
  have hH : ΔZ' - ΔZ = (Divisor.toQDivisor KZ + ΔZ') + -(Divisor.toQDivisor KZ + ΔZ) := by abel
  have hHq : (ΔZ' - ΔZ).IsQCartier := hH ▸ hA2.add hBn
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sX) hHq
    fun C hC => ?_
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hA2.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hA2 hBn,
    QDivisor.intersectionNumber_neg k _ C.ι C.dim_le hB hBn,
    ← QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin ΔZ' hA
      hA2]
  have h1 : 0 ≤ (Divisor.toQDivisor KZ' + ΔZ').intersectionNumber k (g ≫ sX) C.ι C.dim_le hA := by
    rcases QDivisor.intersectionNumber_pullback_eq_zero_or g' hsZ f' hQ' hpb' hA C
        (by rw [← hcomm]; exact hC) with h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonneg hd
        (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX' hN' hQ' C'' hC'')
  have h2 : (Divisor.toQDivisor KZ + ΔZ).intersectionNumber k (g ≫ sX) C.ι C.dim_le hB ≤ 0 := by
    rcases QDivisor.intersectionNumber_pullback_eq_zero_or g rfl f hQ hpb hB C hC with
        h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      have := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hN hN.1 C'' hC''
      rw [QDivisor.intersectionNumber_neg k sX C''.ι C''.dim_le hQ hN.1] at this
      nlinarith
  linarith

end CommonModel

/-! ### Prime divisors along a step of the program -/

/-- A map `φ : X ⤏ X'` over `Z` (for `f : X ⟶ Z`, `f⁺ : X' ⟶ Z`) satisfies `f⁺ ∘ φ = f` at every
point of its domain of definition, `Z` being separated. -/
private theorem apply_toPartialMap_hom {X X' Z : Scheme.{u}} [IsIntegral X] [X'.IsSeparated]
    [Z.IsSeparated] (f : X ⟶ Z) (fp : X' ⟶ Z) (φ : X.RationalMap X')
    (hφ : φ.compHom fp = f.toRationalMap) (x : X) (hx : x ∈ φ.domain) :
    fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x := by
  have he : (φ.toPartialMap.compHom fp).toRationalMap = f.toPartialMap.toRationalMap := by
    change _ = f.toRationalMap
    rw [← hφ]
    conv_rhs => rw [← φ.toRationalMap_toPartialMap]
    rfl
  obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWl' : W ≤ φ.toPartialMap.domain := hWl
  have : IsDominant (X.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
  have hEq' : X.homOfLE hWl' ≫ φ.toPartialMap.hom ≫ fp = X.homOfLE hWr ≫ X.topIso.hom ≫ f := by
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    exact hEq
  have key : φ.toPartialMap.hom ≫ fp = φ.toPartialMap.domain.ι ≫ f := by
    refine ext_of_isDominant (X.homOfLE hWl') ?_
    refine hEq'.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc X hWr f
  exact congrArg (fun g : φ.toPartialMap.domain.toScheme ⟶ Z => g ⟨x, hx⟩) key

/-- A morphism restricting to an isomorphism over `V` is injective on the preimage of `V`. -/
private theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] {a b : X} (ha : g a ∈ V) (h : g a = g b) : a = b := by
  have hb : g b ∈ V := h ▸ ha
  have hopen : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  exact congrArg Subtype.val (((g ⁻¹ᵁ V).ι ≫ g).isOpenEmbedding.injective
    (a₁ := (⟨a, ha⟩ : g ⁻¹ᵁ V)) (a₂ := ⟨b, hb⟩) h)

/-- **Prime divisors along a step.** Let `f : X ⟶ Z` and `f⁺ : X' ⟶ Z` be proper birational
morphisms of varieties onto a normal variety and `φ : X ⤏ X'` a map over `Z`. If a prime divisor
`F'` of `X'` lies over a prime divisor `Q` of `Z`, then `f` and `f⁺` are isomorphisms over a
neighbourhood `V₀` of `η_Q`, there is a prime divisor `F` of `X` over `Q`, and every `ℚ`-divisor
`D` on `X` has `coeff_{F'} φ_* D = coeff_F D`. -/
theorem _root_.MMP.Fourfold.exists_primeDivisor_of_isOver {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral Z]
    [IsLocallyNoetherian Z] {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    (f : X ⟶ Z) (fp : X' ⟶ Z) [IsProper f] [IsProper fp] (hXv : MMP.Mori.IsVariety ℂ (f ≫ sZ))
    (hX'v : MMP.Mori.IsVariety ℂ (fp ≫ sZ)) (hf : IsBirationalMorphism f)
    (hfp : IsBirationalMorphism fp) (φ : X.RationalMap X') (hφ : φ.compHom fp = f.toRationalMap)
    (F' : MMP.Mori.PrimeDivisor X') (Q : MMP.Mori.PrimeDivisor Z)
    (hQ : fp F'.genericPoint = Q.genericPoint) :
    ∃ (F : MMP.Mori.PrimeDivisor X) (V₀ : Z.Opens) (hV : Q.genericPoint ∈ V₀),
      IsIso (f ∣_ V₀) ∧ IsIso (fp ∣_ V₀) ∧ f F.genericPoint = Q.genericPoint ∧
      ∀ D : QDivisor X, (MMP.Mori.RationalMap.transformDivisor φ D).coeff F' = D.coeff F := by
  classical
  have : IsNormal Z := hZ.2
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  have : IsSeparated (fp ≫ sZ) := hX'v.toIsSeparated
  have : X'.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (fp ≫ sZ)]; infer_instance⟩
  have hsep := hX'v.isSeparated_terminal
  have := Q.isDiscreteValuationRing_localRing
  set V₀ : Z.Opens := biregularLocus f ⊓ biregularLocus fp
  have hQV : Q.genericPoint ∈ V₀ :=
    ⟨mem_biregularLocus_of_valuationRing hZ hXv hf _,
      mem_biregularLocus_of_valuationRing hZ hX'v hfp _⟩
  have hfV : IsIso (f ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hfpV : IsIso (fp ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  -- the point of `X` over `η_Q`
  set U : X.Opens := f ⁻¹ᵁ V₀
  have hUopen : IsOpenImmersion (U.ι ≫ f) := by rw [← morphismRestrict_ι]; infer_instance
  set y : U := (inv (f ∣_ V₀)) ⟨Q.genericPoint, hQV⟩
  have hfy : f (U.ι y) = Q.genericPoint := by
    have h1 : (f ∣_ V₀) y = ⟨Q.genericPoint, hQV⟩ := by
      change ((inv (f ∣_ V₀)) ≫ (f ∣_ V₀)) _ = _
      rw [IsIso.inv_hom_id]; rfl
    have h2 := congrArg (fun g : U.toScheme ⟶ Z => g y) (morphismRestrict_ι f V₀)
    change V₀.ι ((f ∣_ V₀) y) = f (U.ι y) at h2
    rw [← h2, h1]; rfl
  have hcoh : Order.coheight (U.ι y) = 1 := by
    rw [coheight_eq_of_isOpenImmersion U.ι, ← coheight_eq_of_isOpenImmersion (U.ι ≫ f)]
    change Order.coheight (f (U.ι y)) = 1
    rw [hfy, Q.coheight_genericPoint]
  set F : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hFη : F.genericPoint = U.ι y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hfF : f F.genericPoint = Q.genericPoint := by rw [hFη, hfy]
  refine ⟨F, V₀, hQV, hfV, hfpV, hfF, fun D => ?_⟩
  -- the strict transform of `F` is `F'`, and only `F` maps to `F'`
  have hdom : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ φ.domain := fun P =>
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f fp φ hφ (by rw [P.coheight_genericPoint])
  have hg' : φ.toPartialMap.toRationalMap = φ := φ.toRationalMap_toPartialMap
  have hF' : F'.genericPoint = φ.toPartialMap.hom ⟨F.genericPoint, hdom F⟩ := by
    refine eq_of_isIso_morphismRestrict fp V₀ (hQ ▸ hQV) ?_
    rw [hQ, apply_toPartialMap_hom f fp φ hφ _ (hdom F), hfF]
  have hE :=
    MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap hg' (hdom F) hF'
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hE (fun P hP => ?_) D
  have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hP φ.toPartialMap hg' (hdom P)
  have h2 : f P.genericPoint = f F.genericPoint := by
    rw [← apply_toPartialMap_hom f fp φ hφ _ (hdom P), ← h1, hQ, hfF]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_isIso_morphismRestrict f V₀ (h2 ▸ hfF ▸ hQV) h2)

/-- **Valuations along a step.** With `f : X ⟶ Z`, `f⁺ : X' ⟶ Z` isomorphisms over `V₀ ∋ η_Q` and
prime divisors `F ⊆ X`, `F' ⊆ X'` over `Q`, the divisors `F` and `F'` over `S` (via
`π = g ∘ f` and `π' = g ∘ f⁺`) define the same valuation of `k(S)`. -/
theorem _root_.MMP.Mori.DivisorOver.valuation_eq_of_isIso_morphismRestrict
    {X X' Z S : Scheme.{0}} [IsIntegral S] {sS : S ⟶ Spec (.of ℂ)} (f : X ⟶ Z) (fp : X' ⟶ Z)
    (g : Z ⟶ S) {π : X ⟶ S} {π' : X' ⟶ S}
    (hπ : f ≫ g = π) (hπ' : fp ≫ g = π') (hX : IsNormalVariety ℂ (π ≫ sS))
    (hX' : IsNormalVariety ℂ (π' ≫ sS)) (hb : IsBirationalMorphism π)
    (hb' : IsBirationalMorphism π') (V₀ : Z.Opens) [IsIso (f ∣_ V₀)] [IsIso (fp ∣_ V₀)]
    (F : MMP.Mori.PrimeDivisor X) (F' : MMP.Mori.PrimeDivisor X') (hV : f F.genericPoint ∈ V₀)
    (h : fp F'.genericPoint = f F.genericPoint) :
    (⟨X', π', hX', hb', F'⟩ : DivisorOver ℂ sS).valuation =
      (⟨X, π, hX, hb, F⟩ : DivisorOver ℂ sS).valuation := by
  have hV' : fp F'.genericPoint ∈ V₀ := h ▸ hV
  let e : (fp ⁻¹ᵁ V₀).toScheme ≅ (f ⁻¹ᵁ V₀).toScheme := asIso (fp ∣_ V₀) ≪≫ (asIso (f ∣_ V₀)).symm
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso _ _ (fp ⁻¹ᵁ V₀) (f ⁻¹ᵁ V₀) hV' hV e ?_ ?_
  · change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀)) ≫ (f ⁻¹ᵁ V₀).ι ≫ π = (fp ⁻¹ᵁ V₀).ι ≫ π'
    rw [← hπ, ← hπ', ← Category.assoc (f ⁻¹ᵁ V₀).ι, ← morphismRestrict_ι, ← Category.assoc,
      Category.assoc _ (inv _), IsIso.inv_hom_id_assoc, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  · apply (f ∣_ V₀).isOpenEmbedding.injective
    change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀) ≫ (f ∣_ V₀)) _ = _
    rw [IsIso.inv_hom_id, Category.comp_id]
    apply Subtype.ext
    have h1 := congrArg (fun k : (fp ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F'.genericPoint, hV'⟩)
      (morphismRestrict_ι fp V₀)
    have h2 := congrArg (fun k : (f ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F.genericPoint, hV⟩)
      (morphismRestrict_ι f V₀)
    change V₀.ι _ = fp F'.genericPoint at h1
    change V₀.ι _ = f F.genericPoint at h2
    exact h1.trans (h.trans h2.symm)

/-- A small contraction `f : X ⟶ Z` of integral schemes is birational, and maps the generic point
of every prime divisor of `X` to the generic point of a prime divisor of `Z`. -/
theorem _root_.MMP.Flips.IsSmall.isBirationalMorphism_and_exists_primeDivisor {k : Type u}
    [Field k] {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} (h : MMP.Flips.IsSmall k sZ sX f) :
    IsBirationalMorphism f ∧ ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ Q : MMP.Mori.PrimeDivisor Z, f F.genericPoint = Q.genericPoint := by
  obtain ⟨-, V, W, hV, hW, hle, hiso⟩ := h
  refine ⟨MMP.Flips.isBirationalMorphism_of_isIso_resLE f V.compl W.compl
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V hV)
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W hW) hle hiso, fun F => ?_⟩
  have hFV : F.genericPoint ∈ (V.compl : X.Opens) := by
    intro hmem
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) _ hmem
    rw [F.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hopen : IsOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hle]; infer_instance
  have hcoh : Order.coheight (f F.genericPoint) = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    have h2 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    change Order.coheight (f F.genericPoint) = _ at h1
    change Order.coheight F.genericPoint = _ at h2
    rw [h1, ← h2, F.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

/-- **The data of a step of a program.** The `i`-th step `X_i → Z_i ← X_{i+1}` of a relative
elementary dlt program consists of proper birational morphisms onto a normal variety `Z_i` over
`S`, with `φ_i : X_i ⤏ X_{i+1}` a map over `Z_i`, and every prime divisor of `X_{i+1}` lies over a
prime divisor of `Z_i` (for a divisorial step `X_{i+1} ≅ Z_i`; for a flip, `f⁺` is small). -/
theorem _root_.MMP.Fourfold.RelativeDltProgram.exists_step {X S : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X} {B : QDivisor X}
    (P : RelativeDltProgram sX sS π K B) (i : ℕ) (hi : (i : ℕ∞) < P.n) :
    ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i)),
      IsNormalVariety ℂ (P.sZ i) ∧ IsProper (P.f i) ∧ IsProper (P.fp i) ∧
      MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) ∧ MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) ∧
      IsBirationalMorphism (P.f i) ∧ IsBirationalMorphism (P.fp i) ∧
      P.f i ≫ P.gZ i = modelMap π P.πY i ∧ P.fp i ≫ P.gZ i = P.πY i ∧
      (P.φ i).compHom (P.fp i) = (P.f i).toRationalMap ∧
      ∀ F' : MMP.Mori.PrimeDivisor (P.Y i), ∃ Q : MMP.Mori.PrimeDivisor (P.Z i),
        P.fp i F'.genericPoint = Q.genericPoint := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  have hcon := hctr.isContraction
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsSeparated (P.sZ i) := hZ.1.toIsSeparated
  haveI : QuasiCompact (P.sZ i) := hZ.1.toQuasiCompact
  have hf : IsProper (P.f i) := hcon.isProper
  have hfv : MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) := hcon.comp_eq ▸ hcon.isVariety_source
  have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, hmod⟩ | hflip
  · have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
        toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    refine ⟨inferInstance, inferInstance, hZ, hf, inferInstance, hfv, hfpv, hfb,
      isBirationalMorphism_of_isIso _, hfg, hstep.comp_eq, hmod.2, fun F' => ?_⟩
    have hcoh : Order.coheight (P.fp i F'.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (P.fp i), F'.coheight_genericPoint]
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩
  · obtain ⟨hfb, -⟩ := hflip.isSmall_source.isBirationalMorphism_and_exists_primeDivisor
    obtain ⟨hfpb, hQ⟩ := hflip.isSmall.isBirationalMorphism_and_exists_primeDivisor
    have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      hflip.isSmall.comp_eq ▸ hflip.isSmall.isVariety_source
    exact ⟨inferInstance, inferInstance, hZ, hf, hflip.isProper, hfv, hfpv, hfb, hfpb, hfg,
      hstep.comp_eq, hflip.isModificationOf.2, hQ⟩

/-- **The models of a program over `S`.** Let `P` be a relative elementary dlt program over `S`
starting from a birational morphism `p : Y ⟶ S`. Every model `π_i : X_i ⟶ S`, `i ≤ n`, is
birational, and every prime divisor `F'` of `X_i` is the transform of a prime divisor `F` of `Y`:
they define the same valuation of `k(S)`, and `coeff_{F'} B_i = coeff_F B_0`. -/
private theorem isBirationalMorphism_and_exists_primeDivisor {S Y : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ S) {KY : Divisor Y} {Γ : QDivisor Y}
    (hbir : IsBirationalMorphism p) (hYn : IsNormalVariety ℂ (p ≫ sS))
    (P : RelativeDltProgram (p ≫ sS) sS p KY Γ) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ hbi : IsBirationalMorphism (modelMap p P.πY i),
      ∀ (hni : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS))
        (F' : MMP.Mori.PrimeDivisor (modelSeq Y P.Y i)), ∃ F : MMP.Mori.PrimeDivisor Y,
        (⟨_, modelMap p P.πY i, hni, hbi, F'⟩ : DivisorOver ℂ sS).valuation =
          (⟨Y, p, hYn, hbir, F⟩ : DivisorOver ℂ sS).valuation ∧
        (divisorSeq Γ P.BY i).coeff F' = Γ.coeff F := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hbir, fun hni F' => ⟨F', rfl, rfl⟩⟩
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    obtain ⟨hbi, hti⟩ := ih hi'.le
    obtain ⟨_, _, hZ, hf, hfp, hfv, hfpv, hfb, hfpb, hfg, hfpg, hφ, hQ⟩ := P.exists_step i hi'
    have hmi := P.isRelativeDltModel i hi'.le
    have hmi1 := P.isRelativeDltModel (i + 1) hi
    have : IsProper (P.πY i) := isProper_of_isProjectiveMorphism _ hmi1.isProjectiveMorphism
    -- the next model is birational over `S`
    have hBi := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbi
    have hBf := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
    have hBfp := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfpb
    have hBg : IsBirational (P.gZ i) := isBirational_of_comp hBf (hfg ▸ hBi)
    have hB' : IsBirational (P.πY i) := hfpg ▸ hBfp.comp hBg
    have hbi' : IsBirationalMorphism (P.πY i) := by
      simpa using isBirationalMorphism_comp_of_isBirational (P.πY i) (𝟙 _) hB'
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso _))
    refine ⟨hbi', fun hni F' => ?_⟩
    obtain ⟨Q, hQF⟩ := hQ F'
    obtain ⟨F, V₀, hV, hfV, hfpV, hfF, hcoeff⟩ := exists_primeDivisor_of_isOver hZ (P.f i)
      (P.fp i) hfv hfpv hfb hfpb (P.φ i) hφ F' Q hQF
    have hni_i : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS) :=
      hmi.comp_eq ▸ hmi.isQFactorial.1
    obtain ⟨F₀, hv0, hc0⟩ := hti hni_i F
    refine ⟨F₀, ?_, ?_⟩
    · exact (DivisorOver.valuation_eq_of_isIso_morphismRestrict (P.f i) (P.fp i) (P.gZ i) hfg
        hfpg hni_i hni hbi hbi' V₀ F F' (hfF ▸ hV) (hQF.trans hfF.symm)).trans hv0
    · change (P.BY i).coeff F' = _
      rw [P.BY_eq i hi', hcoeff, hc0]

/-- A birational proper morphism `π : U ⟶ S` onto a normal variety does not factor through a
scheme `T` of smaller dimension. -/
private theorem topologicalKrullDim_le_of_comp_eq {U T S : Scheme.{0}} [IsIntegral U]
    [IsIntegral S] [IsLocallyNoetherian S] {sS : S ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sS)
    {πU : U ⟶ S} [IsProper πU] (hUv : MMP.Mori.IsVariety ℂ (πU ≫ sS))
    (hb : IsBirationalMorphism πU) (g : U ⟶ T) (gT : T ⟶ S) (h : g ≫ gT = πU) :
    topologicalKrullDim U ≤ topologicalKrullDim T := by
  haveI : ValuationRing (S.presheaf.stalk (genericPoint S)) :=
    inferInstanceAs (ValuationRing S.functionField)
  have hA := mem_biregularLocus_of_valuationRing hX hUv hb (genericPoint S)
  have hiso : IsIso (πU ∣_ biregularLocus πU) := isBiregular_biregularLocus πU
  haveI : IsDominant πU := hb.isDominant
  set W : U.Opens := πU ⁻¹ᵁ biregularLocus πU
  have hWne : (W : Set U).Nonempty := ⟨genericPoint U, by
    change πU (genericPoint U) ∈ biregularLocus πU
    rw [map_genericPoint_of_isDominant]; exact hA⟩
  have hopen : IsOpenImmersion (W.ι ≫ πU) := by rw [← morphismRestrict_ι]; infer_instance
  have hind : Topology.IsInducing (W.ι ≫ g).base := by
    refine Topology.IsInducing.of_comp (W.ι ≫ g).base.hom.continuous gT.base.hom.continuous ?_
    have : (W.ι ≫ πU).base = (W.ι ≫ g).base ≫ gT.base := by
      rw [← h, ← Category.assoc, Scheme.Hom.comp_base]
    have h2 := (W.ι ≫ πU).isOpenEmbedding.isInducing
    rw [this] at h2
    exact h2
  haveI : AlgebraicGeometry.IsVariety ℂ (πU ≫ sS) := hUv
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ U (πU ≫ sS) _ W.isOpen hWne]
  exact hind.topologicalKrullDim_le

/-! ### The output of the program -/

/-- **The output of the program is a crepant dlt lift.** Let `p : Y ⟶ S` be the log resolution
model of `exists_resolution_model` and `P` a finite projective program of `(Y, Γ)` over `S`
ending with a relatively nef adjoint or a Mori fibre space. The program does not end with a Mori
fibre space, every model is birational over `S`, and on the last model `Y'` the push-forward `E'`
of `K_Y + Γ - p^*(K + B)` is effective, exceptional and nef over `S`, hence zero
(`MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef`); so `Y' ⟶ S` is a crepant dlt
lift. -/
private theorem isCrepantDltLift_of_program
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (K : Divisor S) (B : QDivisor S) (hB : MMP.Intersection.IsDltPair sS B)
    {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ S) (KY : Divisor Y) (Γ : QDivisor Y) (hbir : IsBirationalMorphism p)
    (hp : IsProjectiveMorphism p)
    (hΓeq : ∃ E : Divisor Y, MMP.Intersection.IsExceptionalDivisorSum p E ∧
        Γ = MMP.Flips.birationalInverseTransform p hbir B + Divisor.toQDivisor E)
    (hdisc : ∃ (n : ℕ) (hY : IsNormalVariety ℂ (p ≫ sS)), K.IsCanonicalDivisor sS n ∧
        ∀ F : MMP.Mori.PrimeDivisor Y, ∃ a : ℚ,
          IsDiscrepancy sS n K B ⟨Y, p, hY, hbir, F⟩ a ∧ 0 ≤ Γ.coeff F + a)
    (P : RelativeDltProgram (p ≫ sS) sS p KY Γ) (hPproj : P.IsProjective)
    (hPend : MMP.Flips.IsRelativelyNef ℂ (modelStr (p ≫ sS) P.sY P.n.toNat)
          (modelMap p P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq KY P.KY P.n.toNat) +
            divisorSeq Γ P.BY P.n.toNat)) ∨ P.hasFinal) :
    ∃ (U : Scheme.{0}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U) (_ : IsNormal U)
      (_ : CompactSpace U) (p : U ⟶ S) (Δ : QDivisor U),
      IsCrepantDltLift sS K B p Δ ∧ MMP.Mori.IsProjectiveVariety ℂ (p ≫ sS) := by
  classical
  obtain ⟨n, hYn, hKn, hd⟩ := hdisc
  obtain ⟨E, hE, hΓE⟩ := hΓeq
  have hX : IsNormalVariety ℂ sS := hB.1.1.1
  have hPB : MMP.Mori.IsPair sS B := hB.1.1
  have hPBw : IsPairWith sS n K B :=
    ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sS hKn B).mp hB).1
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  set m := P.n.toNat
  have hm : (m : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  have hmod := P.isRelativeDltModel m hm
  set U := modelSeq Y P.Y m
  set πU : U ⟶ S := modelMap p P.πY m
  have hcomp : πU ≫ sS = modelStr (p ≫ sS) P.sY m := hmod.comp_eq
  have hQU : IsQFactorial (πU ≫ sS) := hcomp ▸ hmod.isQFactorial
  have hUnv : IsNormalVariety ℂ (πU ≫ sS) := hQU.1
  have hprojU : IsProjectiveMorphism πU := hmod.isProjectiveMorphism
  have : IsProper πU := isProper_of_isProjectiveMorphism πU hprojU
  -- T1: the final model is birational over `S`
  obtain ⟨hbirU, htrack0⟩ := isBirationalMorphism_and_exists_primeDivisor p hbir hYn P m hm
  -- T2: the program does not end with a Mori fibre space
  have hnotFinal : ¬ P.hasFinal := by
    intro hfin
    obtain ⟨-, hctr, hlt⟩ := P.final_spec hfin
    have hle := topologicalKrullDim_le_of_comp_eq hX hUnv.1 hbirU P.g P.gT
      hctr.isRelativeContractionOfFace.comp_eq
    exact absurd hlt (not_lt.mpr hle)
  -- T3: every prime divisor of the final model is the transform of one on `Y`
  have htrack := htrack0 hUnv
  set ΓU : QDivisor U := divisorSeq Γ P.BY m
  set KU : Divisor U := divisorSeq KY P.KY m
  have hdltU : MMP.Intersection.IsDltPair (πU ≫ sS) ΓU := hcomp ▸ hmod.isDltPair
  -- the canonical divisor of the final model has the dimension index `n`
  have hKU : KU.IsCanonicalDivisor (πU ≫ sS) n := by
    obtain ⟨n', hn'⟩ := hmod.isCanonicalDivisor
    rw [← hcomp] at hn'
    have hXv : MMP.Mori.IsVariety ℂ sS := hX.1
    have hUv : MMP.Mori.IsVariety ℂ (πU ≫ sS) := hUnv.1
    have h1 := hn'.topologicalKrullDim_eq
    have h2 := hKn.topologicalKrullDim_eq
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (πU ≫ sS) hbirU,
      h2] at h1
    exact (show n' = n by exact_mod_cast h1.symm) ▸ hn'
  -- the crepant boundary `Δ_U` of `(S, B)` on `U`
  obtain ⟨ΔU, hΔU, -⟩ := (hPB.existsUnique_isCrepantBoundary hKn πU hUnv hbirU).1
  -- the crepant boundary of `(U, Γ_U)` on itself is `Γ_U`
  have hPU : MMP.Mori.IsPair (πU ≫ sS) ΓU := hdltU.1.1
  have hUnv' : IsNormalVariety ℂ (𝟙 U ≫ πU ≫ sS) := by simpa using hUnv
  obtain ⟨ΔZ', hΔZ', -⟩ := (hPU.existsUnique_isCrepantBoundary hKU (𝟙 U) hUnv'
    (isBirationalMorphism_of_isIso _)).1
  have hΔZ'eq : ΔZ' = ΓU := by
    ext F
    have := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq (P := F)
      (D := ⟨U, 𝟙 U, hUnv', isBirationalMorphism_of_isIso _, F⟩) (by simp) (hΔZ' F)
    change ΔZ'.coeff F = ΓU.coeff F
    linarith
  -- T4: the adjoint of the final model is nef over `S` in the `ℚ`-Cartier sense
  haveI : QuasiCompact sS := hX.1.toQuasiCompact
  haveI : QuasiCompact (πU ≫ sS) := hUnv.1.toQuasiCompact
  have hN' : QDivisor.IsRelativelyNef (πU ≫ sS) πU (Divisor.toQDivisor KU + ΓU) := by
    have h := hPend.resolve_right hnotFinal
    rw [← hcomp] at h
    exact QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor (sX := πU ≫ sS)
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hQU _) h
  -- the identity contracts no curve, so `-(K + B)` is nef over `S` for `𝟙`
  have hN : QDivisor.IsRelativelyNef sS (𝟙 S) (-(Divisor.toQDivisor K + B)) :=
    ⟨hPBw.2.2.neg, fun C hC => absurd hC C.not_isContractedBy_id⟩
  have hnefG := IsCrepantBoundary.isRelativelyNef_sub (X := S) (X' := U) (Y := S) (Z := U)
    hX hUnv hX (f := 𝟙 S) (f' := πU) (Category.id_comp _) rfl
    (isBirationalMorphism_of_isIso _) hbirU hKn hKU hN hN' (g := πU) (g' := 𝟙 U) hUnv hUnv'
    hbirU (isBirationalMorphism_of_isIso _) (by simp) hΔU hΔZ'
  rw [hΔZ'eq, Category.comp_id] at hnefG
  -- comparing a prime divisor of `U` with its strict transform on `Y`
  have hcmp : ∀ (F' : MMP.Mori.PrimeDivisor U) (F : MMP.Mori.PrimeDivisor Y),
      (⟨U, πU, hUnv, hbirU, F'⟩ : DivisorOver ℂ sS).valuation =
        (⟨Y, p, hYn, hbir, F⟩ : DivisorOver ℂ sS).valuation →
      ∀ a : ℚ, IsDiscrepancy sS n K B ⟨Y, p, hYn, hbir, F⟩ a → -ΔU.coeff F' = a :=
    fun F' F hv a ha =>
      MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPBw hv (hΔU F') ha
  set G : QDivisor U := ΓU - ΔU
  have hGeff : G.IsEffective := by
    intro F'
    obtain ⟨F, hv, hc⟩ := htrack F'
    obtain ⟨a, ha, ha0⟩ := hd F
    have := hcmp F' F hv a ha
    change 0 ≤ ΓU.coeff F' - ΔU.coeff F'
    rw [hc]
    linarith
  have hGexc : ∀ F' : MMP.Mori.PrimeDivisor U,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor sS πU F' → G.coeff F' = 0 := by
    intro F' hF'
    have hnot : ¬ (MMP.Flips.ProperDivisorOver.mk ⟨U, πU, hUnv, hbirU, F'⟩ inferInstance :
        MMP.Flips.ProperDivisorOver ℂ sS).IsExceptional :=
      fun h => hF' ⟨hUnv, hbirU, inferInstance, h⟩
    obtain ⟨Q, -, hQ, -⟩ := MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional
      hX _ hnot
    obtain ⟨F, hv, hc⟩ := htrack F'
    obtain ⟨a, ha, -⟩ := hd F
    have hpQ : p F.genericPoint = Q.genericPoint :=
      (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv).symm.trans hQ
    have haQ := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
      (D := ⟨Y, p, hYn, hbir, F⟩) hpQ ha
    have := hcmp F' F hv a ha
    change ΓU.coeff F' - ΔU.coeff F' = 0
    rw [hc, hΓE,
      coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_genericPoint_eq hX hYn.1 hbir B
        hE hpQ]
    linarith
  have hexc1 : ∀ F' : MMP.Mori.PrimeDivisor U,
      F'.support ⊆ MMP.Intersection.exceptionalLocus πU → ΓU.coeff F' = 1 := by
    intro F' hF'
    obtain ⟨F, hv, hc⟩ := htrack F'
    rw [hc]
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus p
    · rw [hΓE]
      exact coeff_birationalInverseTransform_add_exceptionalDivisorSum_of_subset hX hYn.1 hbir B hE
        hF
    · exfalso
      obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
      exact map_genericPoint_ne_of_subset_exceptionalLocus hX hUnv.1 hbirU hF' Q
        ((MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv).trans hQ.symm)
  have hG0 : G = 0 :=
    MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef ℂ sS (πU ≫ sS) hX hUnv πU rfl
      hbirU (MMP.Fourfold.isQCartier_of_isQFactorial _ hQU G) hGexc hGeff hnefG
  have hΓΔ : ΓU = ΔU := sub_eq_zero.mp hG0
  have hprojV : MMP.Mori.IsProjectiveVariety ℂ (πU ≫ sS) := hcomp ▸ hPproj.2 m hm
  exact ⟨U, inferInstance, inferInstance, inferInstance, inferInstance, πU, ΓU,
    isCrepantDltLift_of_isCrepantBoundary hS ⟨n, hKn⟩ hB hprojU hbirU hQU hdltU
      ⟨n, hΓΔ ▸ hΔU⟩ hexc1, hprojV⟩

end Proof_lem_mmp_projective_lower_dlt_model

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori Proof_lem_mmp_projective_lower_dlt_model

/-- **Crepant `ℚ`-factorial dlt models from `P₃`.** Assume `P₃`. If `(S, B)` is a projective
complex dlt pair with rational boundary `B`, `dim S ≤ 3` and canonical divisor `K`, there is a
projective birational morphism `p : U ⟶ S` from a projective `ℚ`-factorial variety `U` such that,
with `Δ = p⁻¹_* B + Exc(p)_red`, the pair `(U, Δ)` is dlt and `K_U + Δ = p^*(K + B)`. -/
@[mmp "lem_mmp_projective_lower_dlt_model"]
public theorem ProjectiveLowerLogMMP.exists_isCrepantDltLift (hP : ProjectiveLowerLogMMP 3)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hdim : topologicalKrullDim S ≤ 3) (K : Divisor S) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sS n)
    (B : QDivisor S) (hB : MMP.Intersection.IsDltPair sS B) :
    ∃ (U : Scheme.{0}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U) (_ : IsNormal U)
      (_ : CompactSpace U) (p : U ⟶ S) (Δ : QDivisor U),
      IsCrepantDltLift sS K B p Δ ∧ MMP.Mori.IsProjectiveVariety ℂ (p ≫ sS) := by
  obtain ⟨Y, _, _, _, _, p, KY, Γ, hbir, hp, hY, hdimY, hQ, hKY, hΓ, hΓeq, hdisc⟩ :=
    exists_resolution_model sS hS hdim K hK B hB
  obtain ⟨-, -, P, hPproj, -, hPend⟩ :=
    hP.2 Y S (p ≫ sS) sS p KY Γ hY hS rfl (by exact_mod_cast hdimY) hQ hKY hΓ
  exact isCrepantDltLift_of_program sS hS K B hB p KY Γ hbir hp hΓeq hdisc P hPproj hPend

end MMP.Fourfold
