module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
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
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcVerticalNegativeRay
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Projective extraction of specified low-discrepancy valuations

Assume the projective floor-program inputs `P(n)` (`MMP.Fourfold.ProjectiveFloorProgramInputs`)
for some `n ≥ 3`. Let `(X, Δ)` be a rational klt pair (`MMP.Fourfold.IsKltPair`) on a normal
projective complex `n`-fold `X`, not necessarily `ℚ`-factorial, and let `𝓔` be a finite set of
normalized divisorial valuations of `k(X)`, exceptional over `X`, with log discrepancies
`0 < a(E; X, Δ) ≤ 1`. Then there is a projective birational morphism `p : V ⟶ X` from a
`ℚ`-factorial variety `V` whose exceptional prime divisors are exactly the centres of the
valuations in `𝓔`, each extracted once, and an effective rational klt boundary `Δ_V` on `V` with
`K_V + Δ_V = p^*(K_X + Δ)` and coefficient `1 - a(E; X, Δ)` at each extracted prime. For
`𝓔 = ∅` this is a small `ℚ`-factorialization.

## Main results

* `MMP.Fourfold.ProjectiveFloorProgramInputs.exists_crepant_extraction`: the extraction.

## Implementation notes

* The extracted prime `E_s = c_V(s)` of `s ∈ 𝓔` is recorded by `ord_{E_s} = s`, as valuations of
  `k(X)`, and "the exceptional primes are exactly `𝓔`" by: `s ↦ E_s` is injective and its range
  is the set of `p`-exceptional prime divisors of `V`; this is the convention of
  `MMP.Fourfold.CrepantJunction`.
* `K_V + Δ_V = p^*(K_X + Δ)` is `MMP.Mori.IsCrepantBoundary`, for every canonical divisor `K_X`
  of `X`. Effectivity of `Δ_V` is part of `MMP.Fourfold.IsKltPair`.

## References

* [OAI4] the fourfold source, *Projective extraction of specified low-discrepancy valuations*.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

open MMP.Mori

section Helpers

open TopologicalSpace MMP.Mori MMP.Fourfold

/- ### Strict transforms under the inverse of a birational morphism -/

section InverseTransform

open MMP MMP.Flips

variable {X Y : Scheme.{u}}

private theorem isSeparated_terminal_from {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Flips.transformPrimeDivisor_inverse_of_map_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((MMP.Flips.map_genericPoint_eq_of_transformPrimeDivisor_inverse hf hP').symm.trans h)) D

end InverseTransform

/-- A birational morphism `μ : Y ⟶ X` from an integral Noetherian scheme has an exceptional
divisor `Exc(μ)_red`: only finitely many prime divisors of `Y` lie in the exceptional locus, a
proper closed subset, each being one of its irreducible components. -/
private theorem exists_isExceptionalDivisorSum {Y X : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] {μ : Y ⟶ X} (hμ : IsBirationalMorphism μ) :
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
    rw [h]
    infer_instance
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
  exact ⟨Finsupp.ofSupportFinite
    (fun P => if P.support ⊆ MMP.Intersection.exceptionalLocus μ then (1 : ℤ) else 0)
    (hfin.subset fun P hP => by by_contra h; exact hP (if_neg h)), fun P => rfl⟩

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
private theorem isSeparated_terminal_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) :=
  have : IsSeparated sX := hX.toIsSeparated
  isSeparated_terminal_from sX

/-- The coefficient of `μ⁻¹_* D` along a prime divisor `E` lying over no prime divisor of `X`
vanishes. -/
private theorem coeff_birationalInverseTransform_eq_zero {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {μ : Y ⟶ X} (hY : MMP.Mori.IsVariety k (μ ≫ sX))
    (hμ : IsBirationalMorphism μ) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, μ E.genericPoint ≠ P.genericPoint) :
    MMP.Flips.birationalInverseTransform μ hμ D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have := isSeparated_terminal_of_isVariety hX
  have := isSeparated_terminal_of_isVariety hY
  exact MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (MMP.Flips.map_genericPoint_eq_of_transformPrimeDivisor_inverse hμ hP)) D

/-- The exceptional locus of a morphism lies in its exceptional set: over the biregular locus the
morphism is an isomorphism, hence an open immersion on its preimage. -/
private theorem exceptionalLocus_subset_exceptionalSet {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MMP.Intersection.exceptionalLocus f ⊆ (exceptionalSet f : Set X) := by
  intro x hx
  by_contra h
  have hU : x ∈ f ⁻¹ᵁ biregularLocus f := by
    simpa [exceptionalSet] using h
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine MMP.Intersection.mem_exceptionalLocus_iff.mp hx _ hU ?_
  rw [← morphismRestrict_ι]
  infer_instance

/-- A proper birational morphism `μ : Y ⟶ X` of varieties onto a normal variety is an isomorphism
over a neighbourhood of every point `x` of `X` whose local ring is a valuation ring (the generic
point, and the generic points of the prime divisors): the fibre over `x` is a single point, so
`x` lies in the finite-fibre locus, over which `μ` is an isomorphism. -/
private theorem mem_biregularLocus_of_valuationRing {Y X : Scheme.{0}} [IsIntegral X]
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
  let V : X.Opens := ⟨_, hU⟩
  have hxV : x ∈ V := by
    change (μ ⁻¹' {x}).Finite
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : μ a = x := ha
    have hb' : μ b = x := hb
    have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
    have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)
  exact le_biregularLocus (f := μ) (V := V) hiso hxV

/-- A prime divisor `F` of `Y` contained in the exceptional locus of a proper birational morphism
`μ : Y ⟶ X` of varieties onto a normal variety does not lie over a prime divisor `P` of `X`:
`μ` is an isomorphism over a neighbourhood of `η_P` (`mem_biregularLocus_of_valuationRing`). -/
private theorem map_genericPoint_ne_of_subset_exceptionalLocus {Y X : Scheme.{0}}
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
  exact (by simpa [exceptionalSet, h] using hexc : P.genericPoint ∉ biregularLocus μ)
    (mem_biregularLocus_of_valuationRing hX hY hμ _)

/-- The birational transform `μ⁻¹_* D` of a divisor under the inverse of a birational morphism
`μ` has no `μ`-exceptional component. -/
private theorem coeff_birationalInverseTransform_eq_zero_of_subset {Y X : Scheme.{0}}
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
private theorem coeff_birationalInverseTransform_add_exceptionalDivisorSum {Y X : Scheme.{0}}
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

/-- Pushing forward the crepant identity `K_Y + Δ_Y = μ^*(K_X + B)`: on a prime divisor `F` of
`Y` not contained in the exceptional locus of `μ`, the crepant boundary `Δ_Y` has the coefficient
of `B` along the image of `F`, i.e. `coeff_F Δ_Y = coeff_F (μ⁻¹_* B)`. -/
private theorem coeff_eq_of_not_subset_of_isCrepantBoundary {Y X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {μ : Y ⟶ X} [IsProper μ] {hY : IsNormalVariety ℂ (μ ≫ sX)}
    {hμ : IsBirationalMorphism μ} {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K B μ hY hμ ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hF : ¬ F.support ⊆ MMP.Intersection.exceptionalLocus μ) :
    ΔY.coeff F = (MMP.Flips.birationalInverseTransform μ hμ B).coeff F := by
  obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
  have hX : IsNormalVariety ℂ sX := (h F).1
  have e := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq
    (D := ⟨Y, μ, hY, hμ, F⟩) hQ.symm (h F)
  have e2 := birationalInverseTransform_apply_of_genericPoint_eq hX μ hY.1 hμ B hQ.symm
  change _ = (MMP.Flips.birationalInverseTransform μ hμ B) F
  rw [e2]
  change ΔY.coeff F = B.coeff Q
  linarith

/- ### Birationality at the generic point -/

/-- For integral schemes, a morphism is birational at the generic point when it maps the generic
point to the generic point and is an isomorphism on the stalks there. -/
private theorem isBirational_iff_of_isIntegral {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) : IsBirational f ↔
      f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  unfold IsBirational
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  simp

/-- If `f` and `f ≫ g` are birational at the generic point, so is `g`. -/
private theorem isBirational_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
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

/- ### The log resolution -/

/-- A projective complex normal variety `S`, with a `ℚ`-divisor `B`,
has a projective log resolution `p : Y ⟶ S` of `(S, B)` with `Y` a projective `ℚ`-factorial
normal variety of the dimension of `S`. -/
private theorem exists_projective_log_resolution
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hX : IsNormalVariety ℂ sS) (B : QDivisor S) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (p : Y ⟶ S),
      MMP.Mori.IsLogResolution sS (QDivisor.toRDivisor B) p ∧ IsProjectiveMorphism p ∧
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

/- ### The boundary of the log resolution -/

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- A divisor on the source of a log resolution of `(S, D)` all of whose components lie in
`Ex(p) ∪ p⁻¹(Supp D)` is snc. -/
private theorem isSNC_of_isLogResolution {k : Type u} [Field k] {S Y : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} {D : RDivisor S} {p : Y ⟶ S}
    (hlog : MMP.Mori.IsLogResolution sS D p)
    [LocallyOfFinitePresentation (p ≫ sS)] {R : Type*} [Zero R] (Γ : DivisorWithCoeffs R Y)
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

/- ### Relative nefness of a difference of crepant boundaries -/

section CommonModel

open AlgebraicGeometry hiding PrimeDivisor

section Crepancy

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace U]
    [IsLocallyNoetherian U] [IsNormal U] in
/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
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

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
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

/-- **`Δ'_Z - Δ_Z` is `(g ≫ f)`-nef.** With `K_X = div(ω)`, `K_{X'} = div(ω')`, crepancy says
`K_Z + Δ_Z = g^*(K_X + Δ)` and `K'_Z + Δ'_Z = g'^*(K_{X'} + Δ')` for `K_Z = div(g^*ω)`,
`K'_Z = div(g'^*ω')`, and `K'_Z ∼ K_Z`. So `Δ'_Z - Δ_Z = (K_Z + Δ'_Z) - (K_Z + Δ_Z)` is
`ℚ`-Cartier, and on a curve `C` contracted by `g ≫ f` its degree is
`(g'^*(K_{X'} + Δ') · C) - (g^*(K_X + Δ) · C)`; by the projection formula each term is `0` or a
non-negative multiple of the degree on the image curve, which is contracted by `f'`, resp. `f`. -/
private theorem isRelativelyNef_sub_of_isCrepantBoundary {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} {X X' Y Z : Scheme.{u}}
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
  set KZ := divisorOfForm (pullbackRationalPluriForms sX g ω) with hKZ
  set KZ' := divisorOfForm (pullbackRationalPluriForms sX' g' ω') with hKZ'
  have hpb := MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hX hZ hg hK hΔZ hω0 hωK hLB
  have hpb' := MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hX' hZ' hg' hK' hΔZ' hω0'
    hωK' hLB'
  have hQ : (Divisor.toQDivisor KX + Δ).IsQCartier := by
    simpa using MMP.Fourfold.Oai4C1.isQCartier_neg hN.1
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
      exact linearlyEquivalent_divisorOfForm hZ hnZ hτ hne
    exact key _ hsZ _ hne'
  have hA2 : (Divisor.toQDivisor KZ + ΔZ').IsQCartier := hA.add_of_linearlyEquivalent hlin
  have hBn : (-(Divisor.toQDivisor KZ + ΔZ)).IsQCartier := MMP.Fourfold.Oai4C1.isQCartier_neg hB
  have hH : ΔZ' - ΔZ = (Divisor.toQDivisor KZ + ΔZ') + -(Divisor.toQDivisor KZ + ΔZ) := by abel
  have hHq : (ΔZ' - ΔZ).IsQCartier := hH ▸ hA2.add hBn
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sX) hHq
    fun C hC => ?_
  rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le hHq (hA2.add hBn) hH,
    QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hA2 hBn,
    MMP.Mori.QDivisor.intersectionNumber_neg k _ C.ι C.dim_le hB hBn,
    ← MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (g ≫ sX) C.ι C.dim_le hlin
      ΔZ' hA hA2]
  have h1 : 0 ≤ (Divisor.toQDivisor KZ' + ΔZ').intersectionNumber k (g ≫ sX) C.ι C.dim_le hA := by
    rcases MMP.Mori.QDivisor.intersectionNumber_pullback_eq_zero_or g' hsZ f' hQ' hpb' hA C
        (by rw [← hcomm]; exact hC) with h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      exact mul_nonneg hd
        (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX' hN' hQ' C'' hC'')
  have h2 : (Divisor.toQDivisor KZ + ΔZ).intersectionNumber k (g ≫ sX) C.ι C.dim_le hB ≤ 0 := by
    rcases MMP.Mori.QDivisor.intersectionNumber_pullback_eq_zero_or g rfl f hQ hpb hB C hC with
        h0 | ⟨d, hd, C'', hC'', heq⟩
    · rw [h0]
    · rw [heq]
      have := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hN hN.1 C'' hC''
      rw [MMP.Mori.QDivisor.intersectionNumber_neg k sX C''.ι C''.dim_le hQ hN.1] at this
      nlinarith
  linarith

end CommonModel

end Helpers

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
    (S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))) where
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
  exact ⟨Pm', Q, valuation_eq_of_valuationOver_eq f fp g hπ hπ' hU hU' hb hb' hv, h1, h2,
    hcoeff⟩

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
  obtain ⟨F', hF', hiso'⟩ := MMP.Flips.exists_primeDivisor_isIso_stalkMap fp hfp Q
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
      hfp.isBirationalMorphism]; exact hdimZ
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sZ hZ hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sU' hU' hdimU'
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [hfs]; exact hU
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfp.comp_eq]; exact hU'
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sZ) n := by rw [hfs]; exact hK
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sZ) n := by rw [hfp.comp_eq]; exact hK₀
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
    exact linearlyEquivalent_divisorOfForm hX hK.1 hω₀ hω
  exact ⟨hX, hK, hQ.add_of_linearlyEquivalent hlin⟩

/-- **The coefficient of `Γ - Δ_Y` at a prescribed divisor.** For a divisor `D` over `X`, with
`D.f` proper, carrying the prescribed coefficient `c` and with discrepancy `a = a(D; X, Δ)`,
`c + a` (the coefficient of `Γ - Δ_Y`, `Δ_Y` the crepant boundary) is zero unless `D` is
exceptional with valuation outside `𝓔`, where it is the log discrepancy, positive by klt. -/
private theorem add_eq_zero_or_pos_of_isPrescribedCoeff [CompactSpace X]
    (hΔ : IsKltPair sX Δ) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver ℂ sX) (hD : IsProper D.f) {c a : ℚ}
    (hc : IsPrescribedCoeff sX Δ 𝓔 D c) (ha : IsDiscrepancy sX n K Δ D a) :
    (c + a = 0 ∧ ¬ ((∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint) ∧
        D.valuation ∉ 𝓔)) ∨
      (0 < c + a ∧ (∀ Q : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ≠ Q.genericPoint) ∧
        D.valuation ∉ 𝓔) := by
  have hP : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
  have hX : IsNormalVariety ℂ sX := hP.1
  rcases hc with ⟨Q, hQ, rfl⟩ | ⟨hexc, ⟨hs, hlog⟩ | ⟨hs, rfl⟩⟩
  · left
    refine ⟨?_, fun h => h.1 Q hQ⟩
    rw [MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq hQ ha]
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
    have := hΔ.2 n D _ hlog
    have h3 : (0 : ℝ) < ((1 + a : ℚ) : ℝ) := by push_cast; exact this
    exact_mod_cast h3

/-- **The final model is crepant.** On a model whose adjoint is nef over `X`, `Γ - Δ_U` (with
`Δ_U` the crepant boundary of `(X, Δ)`) is effective, exceptional and nef over `X`, hence zero by
the negativity lemma: `Γ` is the crepant boundary, and no prime divisor is exceptional with
valuation outside `𝓔`. -/
private theorem Model.isCrepantBoundary_of_isNef (hΔ : IsKltPair sX Δ)
    (M : Model sX Δ 𝓔 n S₀) (hM : M.IsNef) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    IsCrepantBoundary sX n K Δ M.π M.isQFactorial.1 M.isBirationalMorphism M.Γ ∧
      ∀ F : MMP.Mori.PrimeDivisor M.U,
        ¬ ((∀ Q : MMP.Mori.PrimeDivisor X, M.π F.genericPoint ≠ Q.genericPoint) ∧
          (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, F⟩ :
            DivisorOver ℂ sX).valuation ∉ 𝓔) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
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
    have := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq (P := F)
      (D := ⟨U, 𝟙 U, hUnv', isBirationalMorphism_of_isIso _, F⟩) (by simp) (hΔZ' F)
    change ΔZ'.coeff F = M.Γ.coeff F
    linarith
  haveI : QuasiCompact (πU ≫ sX) := hUnv.1.toQuasiCompact
  have hN : QDivisor.IsRelativelyNef sX (𝟙 X) (-(Divisor.toQDivisor K + Δ)) :=
    ⟨MMP.Fourfold.Oai4C1.isQCartier_neg (isPairWith_of_isPair hPB hK).2.2,
      fun C hC => absurd hC (MMP.Mori.ProperCurve.not_isContractedBy_id C)⟩
  have hnefG := isRelativelyNef_sub_of_isCrepantBoundary (X := X) (X' := U) (Y := X) (Z := U)
    hX hUnv hX (f := 𝟙 X) (f' := πU) (Category.id_comp _) rfl
    (isBirationalMorphism_of_isIso _) hbirU hK M.isCanonicalDivisor hN hM (g := πU) (g' := 𝟙 U)
    hUnv hUnv' hbirU (isBirationalMorphism_of_isIso _) (by simp) hΔU hΔZ'
  rw [hΔZ'eq, Category.comp_id] at hnefG
  -- the coefficients of `Γ - Δ_U`
  have hcoeff := fun F : MMP.Mori.PrimeDivisor U =>
    add_eq_zero_or_pos_of_isPrescribedCoeff hΔ hK ⟨U, πU, hUnv, hbirU, F⟩ ‹_› (M.coeff_spec F)
      (hΔU F)
  set G : QDivisor U := M.Γ - ΔU with hGdef
  have hGF : ∀ F, G.coeff F = M.Γ.coeff F + -ΔU.coeff F := fun F => by
    change M.Γ.coeff F - ΔU.coeff F = _; ring
  have hGeff : G.IsEffective := by
    intro F
    rw [hGF]
    rcases hcoeff F with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.ge
    · exact h.le
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
  refine ⟨hΓΔ ▸ hΔU, fun F hF => ?_⟩
  rcases hcoeff F with ⟨-, h⟩ | ⟨h, -⟩
  · exact h hF
  · have : G.coeff F = 0 := by rw [hG0]; rfl
    rw [hGF] at this
    linarith

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
  constructor
  · rintro h Q hQ
    rw [hQ, Q.coheight_genericPoint] at h
    exact absurd h (by decide)
  · intro h
    by_contra hlt
    have h2 : Order.coheight (D.f D.E.genericPoint) = 1 := by
      refine le_antisymm ?_ h1
      by_contra h3
      push Not at h3
      exact hlt (Order.add_one_le_of_lt h3)
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

/-- **Crepant pull-backs of klt pairs are klt.** If `Δ_V` is the crepant boundary of the klt pair
`(X, Δ)` on a proper birational model `V`, effective with `K_V + Δ_V` `ℚ`-Cartier, then
`(V, Δ_V)` is klt: every log discrepancy over `V` is one over `X`. -/
private theorem isKltPair_of_isCrepantBoundary [CompactSpace X] (hΔ : IsKltPair sX Δ)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {V : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (p : V ⟶ X) [IsProper p]
    (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) {KV : Divisor V}
    (hKV : KV.IsCanonicalDivisor (p ≫ sX) n) {ΔV : QDivisor V}
    (hcrep : IsCrepantBoundary sX n K Δ p hV hp ΔV)
    (hQ : (Divisor.toQDivisor KV + ΔV).IsQCartier) (hnn : ∀ P, 0 ≤ ΔV.coeff P) :
    IsKltPair (p ≫ sX) ΔV := by
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
  have hPV : MMP.Mori.IsPair (p ≫ sX) ΔV := ⟨hV, n, KV, hKV, hQ⟩
  refine ⟨⟨inferInstance, inferInstance, hPV, hnn⟩, fun n' D a ha => ?_⟩
  have hn : n' = n := by
    obtain ⟨-, -, -, -, ⟨K', hK', -⟩, -⟩ := ha
    have := hK'.topologicalKrullDim_eq.symm.trans hKV.topologicalKrullDim_eq
    exact_mod_cast this
  subst hn
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPV hKV D
  have hab := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hb ha
  have hDp : IsProper D.f := ha.2.1
  have hinv := (hPB.isDiscrepancy_iff_of_crepant p hV hp hK hKV (Or.inl hcrep)).2 D
    (MMP.Mori.compDivisorOver p hV hp D) (MMP.Mori.valuation_compDivisorOver p hV hp D) b
  have hb' := hinv.mp hb
  have hprop : IsProper (MMP.Mori.compDivisorOver p hV hp D).f := by
    change IsProper (D.f ≫ p); infer_instance
  have hlog := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hb'
    (1 + (b : ℝ))).mpr ⟨hprop, rfl⟩
  rw [hab]
  exact hΔ.2 _ _ _ hlog

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
  have hpb := MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hX hU hb hK hΔU hω0 hωK hLB
  have hB := hpb.isQCartier hQ
  have hzero : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) +
      ΔU).intersectionNumber ℂ (π ≫ sX) C.ι C.dim_le hB = 0 := by
    rcases MMP.Mori.QDivisor.intersectionNumber_pullback_eq_zero_or π rfl (𝟙 X) hQ hpb hB C
        (by rw [Category.comp_id]; exact hC) with h0 | ⟨d, -, C'', hC'', -⟩
    · exact h0
    · exact absurd hC'' (MMP.Mori.ProperCurve.not_isContractedBy_id C'')
  have hne : pullbackRationalPluriForms sX π ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hX hb hK.1 hω0
  obtain ⟨τ, hτ0, hτK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hU hKU
  have hτ : divisorOfForm τ = KU := Finsupp.ext hτK
  have hlin : KU.LinearlyEquivalent (divisorOfForm (pullbackRationalPluriForms sX π ω)) := by
    rw [← hτ]; exact linearlyEquivalent_divisorOfForm hU hKU.1 hτ0 hne
  rw [MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (π ≫ sX) C.ι C.dim_le hlin
    ΔU hQU hB]
  exact hzero

/-- A prime divisor of a model is *unwanted* if it is exceptional over `X` with valuation outside
`𝓔`. -/
private def Model.IsUnwanted (M : Model sX Δ 𝓔 n S₀) (F : MMP.Mori.PrimeDivisor M.U) : Prop :=
  (∀ Q : MMP.Mori.PrimeDivisor X, M.π F.genericPoint ≠ Q.genericPoint) ∧
    (⟨M.U, M.π, M.isQFactorial.1, M.isBirationalMorphism, F⟩ : DivisorOver ℂ sX).valuation ∉ 𝓔

/-- **The remainder.** On a model, `G = Γ - Δ_U` (with `Δ_U` the crepant boundary of `(X, Δ)`)
vanishes away from the unwanted primes, is positive on them, and has the intersection numbers of
`K_U + Γ` on the curves contracted over `X`. -/
private theorem Model.exists_remainder (hΔ : IsKltPair sX Δ) (M : Model sX Δ 𝓔 n S₀) :
    ∃ G : QDivisor M.U,
      (∀ F, (G.coeff F = 0 ∧ ¬ M.IsUnwanted F) ∨ (0 < G.coeff F ∧ M.IsUnwanted F)) ∧
      ∀ C : ProperCurve (M.π ≫ sX), C.IsContractedBy M.π →
        G.intersectionNumber ℂ (M.π ≫ sX) C.ι C.dim_le
            (isQCartier_of_isQFactorial _ M.isQFactorial G) =
          (Divisor.toQDivisor M.K + M.Γ).intersectionNumber ℂ (M.π ≫ sX) C.ι C.dim_le
            (isQCartier_of_isQFactorial _ M.isQFactorial _) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
  have hX : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hUnv : IsNormalVariety ℂ (M.π ≫ sX) := M.isQFactorial.1
  haveI : QuasiCompact (M.π ≫ sX) := hUnv.1.toQuasiCompact
  have : IsProper M.π := isProper_of_isProjectiveMorphism M.π M.isProjectiveMorphism
  obtain ⟨-, n₀, K, hK₀, -⟩ := hPB
  have hK : K.IsCanonicalDivisor sX n := by
    have hn : n₀ = n := by
      haveI : MMP.Mori.IsVariety ℂ sX := hX.1
      haveI : MMP.Mori.IsVariety ℂ (M.π ≫ sX) := hUnv.1
      have := hK₀.topologicalKrullDim_eq.symm.trans
        ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (M.π ≫ sX)
          M.isBirationalMorphism).trans M.dim_eq)
      exact_mod_cast this
    exact hn ▸ hK₀
  obtain ⟨ΔU, hΔU, -⟩ :=
    (hΔ.1.isPair.existsUnique_isCrepantBoundary hK M.π hUnv M.isBirationalMorphism).1
  have hQ := isQCartier_of_isQFactorial _ M.isQFactorial
  refine ⟨M.Γ - ΔU, fun F => ?_, fun C hC => ?_⟩
  · have h := add_eq_zero_or_pos_of_isPrescribedCoeff hΔ hK
      ⟨M.U, M.π, hUnv, M.isBirationalMorphism, F⟩ ‹_› (M.coeff_spec F) (hΔU F)
    have hGF : (M.Γ - ΔU).coeff F = M.Γ.coeff F + -ΔU.coeff F := by
      change M.Γ.coeff F - ΔU.coeff F = _; ring
    rw [hGF]; exact h
  · have h0 := intersectionNumber_eq_zero_of_isCrepantBoundary hX M.π hUnv
      M.isBirationalMorphism hK (isPairWith_of_isPair hΔ.1.isPair hK).2.2 hΔU
      M.isCanonicalDivisor (hQ _) C hC
    have heq : M.Γ - ΔU =
        (Divisor.toQDivisor M.K + M.Γ) + -(Divisor.toQDivisor M.K + ΔU) := by abel
    rw [MMP.Fourfold.intersectionNumber_congr _ C.ι C.dim_le (hQ _)
        ((hQ _).add (MMP.Fourfold.Oai4C1.isQCartier_neg (hQ _))) heq,
      QDivisor.intersectionNumber_add' ℂ _ C.ι C.dim_le _ _ (hQ _)
        (MMP.Fourfold.Oai4C1.isQCartier_neg (hQ _)),
      MMP.Mori.QDivisor.intersectionNumber_neg ℂ _ C.ι C.dim_le (hQ _)
        (MMP.Fourfold.Oai4C1.isQCartier_neg (hQ _)), h0]
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
divisor `F` contracted by `f` has positive coefficient in `G`: by the negativity lemma,
`G - t F` is effective for small `t > 0`, since `-(G - t F)` is nonnegative on `C₀`. -/
private theorem pos_coeff_of_forall_ne {U Z : Scheme.{0}} [IsIntegral U] [CompactSpace U]
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
      QDivisor.intersectionNumber_add' ℂ _ C₀.ι C₀.dim_le _ _
        (MMP.Fourfold.Oai4C1.isQCartier_neg (hQ G)) (hQ _),
      MMP.Mori.QDivisor.intersectionNumber_neg ℂ _ C₀.ι C₀.dim_le (hQ G)
        (MMP.Fourfold.Oai4C1.isQCartier_neg (hQ G)),
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
private noncomputable def Model.ofStep (hΔ : IsKltPair sX Δ) (M : Model sX Δ 𝓔 n S₀)
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
    have hX : IsNormalVariety ℂ sX := hΔ.1.isPair.1
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
    have hX : IsNormalVariety ℂ sX := hΔ.1.isPair.1
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
    have hX : IsNormalVariety ℂ sX := hΔ.1.isPair.1
    obtain ⟨F, -, hv, -, -, -⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
      M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
    have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
    rw [← hv]
    exact M.exc_mem F fun Q hQ => hF' Q (h.symm.trans hQ)

/-- The exceptional valuations of the next model are among those of the model. -/
private theorem Model.excVals_ofStep_subset (hΔ : IsKltPair sX Δ) (M : Model sX Δ 𝓔 n S₀)
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
  have hX : IsNormalVariety ℂ sX := hΔ.1.isPair.1
  intro v hv
  simp only [Model.excVals, Finset.mem_filter] at hv ⊢
  obtain ⟨hv0, F', hF', rfl⟩ := hv
  obtain ⟨F, -, hvF, -, -, -⟩ := exists_primeDivisor_of_step f hfb hfp g hfg hπ'
    M.isQFactorial.1 hQ'.1 M.isBirationalMorphism hπ'b F'
  have h := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hvF
  exact ⟨hv0, F, fun Q hQ => hF' Q (h.symm.trans hQ), hvF⟩

/-- A prime divisor contracted by `f` leaves the exceptional valuations of the next model. -/
private theorem Model.valuation_notMem_excVals_ofStep (hΔ : IsKltPair sX Δ)
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

/-- The strict transform of a log canonical divisor `K + D`. -/
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
    have := mem_biregularLocus_of_valuationRing hZ hUv hfb (genericPoint Z)
    rw [← map_genericPoint_of_isDominant f] at this
    exact hmem _ this hx
  · set E : MMP.Mori.PrimeDivisor U := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1
    have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1
    obtain ⟨Q, hQ⟩ := hcon E
    have := Q.isDiscreteValuationRing_localRing
    have hQb := mem_biregularLocus_of_valuationRing hZ hUv hfb Q.genericPoint
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

omit [IsIntegral X] in
/-- An extremal ray of `NE̅(X)` is the preimage of an extremal ray of `NE̅(X / Spec ℂ)` under the
natural bijection. -/
private theorem isExtremalRay_preimage (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R) :
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _)
      (relativeToAbsolute sX sX ⁻¹' R) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr
          ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
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
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr
          ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
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
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr
          ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
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
    (hΔ : IsKltPair sX Δ) (M : Model sX Δ 𝓔 n S₀) (hM : ¬ M.IsNef) :
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
  have hXn : IsNormalVariety ℂ sX := hΔ.1.isPair.1
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsProper (g ≫ sX) := isProper_of_isProjectiveMorphism _ hZp.isProjective
  haveI : IsProper g := IsProper.of_comp g sX
  have hgp : IsProjectiveMorphism g := isProjectiveMorphism_of_isProper hZp hX g
  haveI : IsProper M.π := isProper_of_isProjectiveMorphism _ M.isProjectiveMorphism
  have hBg : IsBirational g :=
    isBirational_of_comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hψb)
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
private theorem Model.exists_flip (hP : ProjectiveFloorProgramInputs n) (hΔ : IsKltPair sX Δ)
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
  have hGP : 0 < G.coeff P ∧ M.IsUnwanted P := by
    rcases hGspec P with ⟨h0, -⟩ | h
    · exact absurd (by rw [DivisorWithCoeffs.coeff_apply] at h0; exact h0)
        (Finsupp.mem_support_iff.mp hPG)
    · exact h
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
private theorem Model.exists_divisorial (hΔ : IsKltPair sX Δ)
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
    · exact h.le
  have hfs : f ≫ g ≫ sX = M.π ≫ sX := by rw [← Category.assoc, hfg]
  have hray : ∀ C : ProperCurve (M.π ≫ sX), C.IsContractedBy f → ∃ c : ℝ, 0 ≤ c ∧
      c • OneCycle.numericalClass (M.π ≫ sX) (C₀.cycle ℝ) =
        OneCycle.numericalClass (M.π ≫ sX) (C.cycle ℝ) := fun C hC => by
    have := (hcon.isContractedBy_iff C).mp hC
    rw [hRC] at this
    exact this
  have hpos := pos_coeff_of_forall_ne M.isQFactorial hZn f hfb hfs C₀ hray hGeff hGC
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
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hΔ : IsKltPair sX Δ)
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

/-- **No infinite sequence of floor flips.** By the termination clause of `P(n)`, applied to
the first model of the sequence. -/
private theorem not_forall_isFlipStep (hP : ProjectiveFloorProgramInputs n)
    (Ms : ℕ → Model sX Δ 𝓔 n S₀) (h : ∀ i, (Ms i).IsFlipStep (Ms (i + 1))) : False := by
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
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hΔ : IsKltPair sX Δ)
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
  obtain ⟨F', hF', hiso⟩ := MMP.Flips.exists_primeDivisor_isIso_stalkMap q hq F
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
      MMP.isProjectiveMorphism_of_isClosedImmersion _,
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
      s.comap (e.symm : N.functionField →+* X.functionField)
      with hvdef
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

/-- **The initial model.** A projective log resolution of `(X, Δ)` on which every valuation of
`𝓔` is a prime divisor, with the boundary `Γ` of prescribed coefficients, is a model. -/
private theorem exists_initialModel (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = n) (hΔ : IsKltPair sX Δ)
    (𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))
    (h𝓔 : ∀ s ∈ 𝓔, MMP.Intersection.IsExceptionalValuation ℂ sX s ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sX Δ s a ∧ 0 < a ∧ a ≤ 1) :
    ∃ S₀ : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))),
      Nonempty (Model sX Δ 𝓔 n S₀) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
  have hXn : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  -- a normal projective model carrying the valuations of `𝓔`
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
  -- the boundary `B_N = p⁻¹_* Δ + Exc(p)_red` and a log resolution of `(N, B_N)`
  obtain ⟨EN, hEN⟩ := exists_isExceptionalDivisorSum hp
  set BN : QDivisor N := MMP.Flips.birationalInverseTransform p hp Δ + Divisor.toQDivisor EN
    with hBN
  obtain ⟨Y, _, _, _, _, h, hlog, hhp, hYn₀, hYp₀, hdimY, hQY₀⟩ :=
    exists_projective_log_resolution (p ≫ sX) hNp hN BN
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
  -- canonical divisors
  obtain ⟨-, n₀, K, hK₀, -⟩ := hPB
  have hK : K.IsCanonicalDivisor sX n := by
    have hn : n₀ = n := by exact_mod_cast hK₀.topologicalKrullDim_eq.symm.trans hdim
    exact hn ▸ hK₀
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme ((h ≫ p) ≫ sX)
    (by rw [hsY]; exact hlog.isSmoothScheme) (n := n) hdimY'
  -- the crepant boundary and the exceptional divisor of `π = h ≫ p`
  obtain ⟨ΔY, hΔY, -⟩ := (hΔ.1.isPair.existsUnique_isCrepantBoundary hK (h ≫ p) hYn hπb).1
  obtain ⟨Eπ, hEπ⟩ := exists_isExceptionalDivisorSum hπb
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
      coeff_birationalInverseTransform_add_exceptionalDivisorSum hXn hYn.1 hπb Δ hEπ F]
    by_cases h1 : F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p)
    · rw [if_pos h1]; exact one_ne_zero
    · rw [if_neg h1]
      have : c F = (MMP.Flips.birationalInverseTransform (h ≫ p) hπb Δ).coeff F := by
        rw [hc]; exact if_neg h1
      rw [← this]; exact hF
  set Γ : QDivisor Y := Finsupp.ofSupportFinite c hcfin with hΓ
  have hΓc : ∀ F, Γ.coeff F = c F := fun F => by
    rw [DivisorWithCoeffs.coeff_apply, hΓ, Finsupp.ofSupportFinite_coe]
  -- exceptional primes
  have hexc : ∀ F : MMP.Mori.PrimeDivisor Y,
      F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) ↔
        ∀ Q : MMP.Mori.PrimeDivisor X, (h ≫ p) F.genericPoint ≠ Q.genericPoint := by
    intro F
    refine ⟨fun hF => map_genericPoint_ne_of_subset_exceptionalLocus hXn hYn.1 hπb hF, fun hF => ?_⟩
    by_contra h1
    obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset h1
    exact hF Q hQ.symm
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
      exact birationalInverseTransform_apply_of_genericPoint_eq hXn (h ≫ p) hYn.1 hπb Δ hQ.symm
    · rw [e1, ← coeff_eq_of_not_subset_of_isCrepantBoundary hΔY F hF]
  -- log discrepancies over `X`
  have hlogF : ∀ F : MMP.Mori.PrimeDivisor Y,
      IsValuationLogDiscrepancy sX Δ (val F) (1 - (ΔY.coeff F : ℝ)) := fun F =>
    ⟨n, ⟨Y, h ≫ p, hYn, hπb, F⟩, inferInstance, rfl,
      (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hΔY F) _).mpr
        ⟨inferInstance, by push_cast; ring⟩⟩
  have hlt : ∀ F : MMP.Mori.PrimeDivisor Y, ΔY.coeff F < 1 := by
    intro F
    obtain ⟨n', D, -, -, hl⟩ := hlogF F
    have := hΔ.2 n' D _ hl
    have h3 : ((ΔY.coeff F : ℚ) : ℝ) < 1 := by linarith
    exact_mod_cast h3
  have hexcE : ∀ F : MMP.Mori.PrimeDivisor Y,
      F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p) → val F ∈ 𝓔 →
        Γ.coeff F = ΔY.coeff F ∧ 0 ≤ ΔY.coeff F := by
    intro F hF hs
    refine ⟨by rw [hΓc, hc]; simp only [if_pos hF, if_pos hs], ?_⟩
    obtain ⟨a, ha, -, ha1⟩ := (h𝓔 _ hs).2
    obtain ⟨n₁, D₁, -, hv₁, hl₁⟩ := hlogF F
    obtain ⟨n₂, D₂, -, hv₂, hl₂⟩ := ha
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hΔ.1.isPair
      hl₁ hl₂ (hv₁.trans hv₂.symm)
    have h' : ((ΔY.coeff F : ℚ) : ℝ) ≥ 0 := by linarith
    exact_mod_cast h'
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor Y, 0 ≤ Γ.coeff F ∧ Γ.coeff F ≤ 1 := by
    intro F
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus (h ≫ p)
    · by_cases hs : val F ∈ 𝓔
      · obtain ⟨e1, e2⟩ := hexcE F hF hs
        rw [e1]; exact ⟨e2, (hlt F).le⟩
      · have : Γ.coeff F = 1 := by rw [hΓc, hc]; simp only [if_pos hF, if_neg hs]
        rw [this]; norm_num
    · obtain ⟨Q, -, e1, e2⟩ := hnexc F hF
      exact ⟨e1 ▸ hΔ.1.nonneg Q, e2 ▸ (hlt F).le⟩
  -- the components of `Γ` lie in `Ex(h) ∪ h⁻¹(Supp B_N)`
  have hsupp : ∀ P ∈ Γ.support, P.support ⊆
      ((exceptionalSet h ⊔ (QDivisor.toRDivisor BN).supp.preimage h.continuous :
        TopologicalSpace.Closeds Y) : Set Y) := by
    intro P hP
    by_cases hPh : P.support ⊆ MMP.Intersection.exceptionalLocus h
    · exact (hPh.trans (exceptionalLocus_subset_exceptionalSet h)).trans fun x hx => Or.inl hx
    obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hPh
    have hBQ : BN.coeff Q ≠ 0 := by
      rw [hBN, coeff_birationalInverseTransform_add_exceptionalDivisorSum hXn hN.1 hp Δ hEN Q]
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
        rw [birationalInverseTransform_apply_of_genericPoint_eq hXn p hN.1 hp Δ hR.symm]
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
    intro x hx
    right
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηP) hx
  have hsnc : Γ.IsSNC (h ≫ p ≫ sX) := isSNC_of_isLogResolution hlog Γ hsupp
  -- `(Y, Γ)` is dlt
  have hKY₀ : KY.IsCanonicalDivisor (h ≫ p ≫ sX) n := by rw [← hsY]; exact hKY
  have hdlt : MMP.Mori.IsDltPair (h ≫ p ≫ sX) n KY Γ := by
    refine ⟨⟨hYn₀, hKY₀, MMP.Fourfold.isQCartier_of_isQFactorial _ hQY₀ _⟩, hcoeff, ⊤, ?_, ?_, ?_⟩
    · exact hlog.isSmoothScheme.ge
    · exact isSNC_restrictOpen (h ≫ p ≫ sX) hsnc ⊤
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

/-- **Projective extraction of specified low-discrepancy valuations.** Assume `P(n)`. Let `(X, Δ)`
be a klt pair on a normal projective complex `n`-fold and `𝓔` a finite set of valuations of
`k(X)`, exceptional over `X`, with log discrepancies `0 < a(s; X, Δ) ≤ 1`. Then there is a
projective birational `p : V ⟶ X` from a `ℚ`-factorial variety `V` (over `ℂ` through `p`) with
prime divisors `E_s`, `s ∈ 𝓔`, such that `ord_{E_s} = s`, `s ↦ E_s` is a bijection onto the
`p`-exceptional prime divisors of `V`, and a klt boundary `Δ_V` (effective) on `V` with
`K_V + Δ_V = p^*(K_X + Δ)` for every canonical divisor `K_X`, whose coefficient at `E_s` is
`1 - a(s; X, Δ)`. -/
@[mmp "thm_fourfold_projective_specified_extraction"]
public theorem ProjectiveFloorProgramInputs.exists_crepant_extraction {n : ℕ}
    (hP : ProjectiveFloorProgramInputs n)
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = n) {Δ : QDivisor X} (hΔ : IsKltPair sX Δ)
    (𝓔 : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ))))
    (h𝓔 : ∀ s ∈ 𝓔, MMP.Intersection.IsExceptionalValuation ℂ sX s ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sX Δ s a ∧ 0 < a ∧ a ≤ 1) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (p : V ⟶ X) (hp : IsBirationalMorphism p) (hV : IsQFactorial (p ≫ sX))
      (E : 𝓔 → MMP.Mori.PrimeDivisor V) (ΔV : QDivisor V),
      IsProjectiveMorphism p ∧
      (∀ s : 𝓔, (⟨V, p, hV.1, hp, E s⟩ : DivisorOver ℂ sX).valuation = s) ∧
      Function.Injective E ∧
      (∀ P : MMP.Mori.PrimeDivisor V,
        RationalMap.IsExceptional (X := V) p.toRationalMap P ↔ P ∈ Set.range E) ∧
      IsKltPair (p ≫ sX) ΔV ∧
      (∀ K : Divisor X, K.IsCanonicalDivisor sX n →
        IsCrepantBoundary sX n K Δ p hV.1 hp ΔV) ∧
      ∀ s : 𝓔, IsValuationLogDiscrepancy sX Δ s (1 - (ΔV.coeff (E s) : ℝ)) := by
  classical
  have hPB : MMP.Mori.IsPair sX Δ := hΔ.1.isPair
  have hXn : IsNormalVariety ℂ sX := hPB.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨S₀, ⟨M₀⟩⟩ := exists_initialModel hX hdim hΔ 𝓔 h𝓔
  obtain ⟨M, hM⟩ := exists_isNef hP hX hΔ M₀
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := hPB
  have hn₀ : n₀ = n := by
    have := hK₀.topologicalKrullDim_eq.symm.trans hdim
    exact_mod_cast this
  subst hn₀
  have hfin := M.isCrepantBoundary_of_isNef hΔ hM hK₀
  have hUnv : IsNormalVariety ℂ (M.π ≫ sX) := M.isQFactorial.1
  have : IsProper M.π := isProper_of_isProjectiveMorphism M.π M.isProjectiveMorphism
  set D : MMP.Mori.PrimeDivisor M.U → DivisorOver ℂ sX :=
    fun F => ⟨M.U, M.π, hUnv, M.isBirationalMorphism, F⟩ with hD
  choose E hE using fun s : 𝓔 => M.surv s.1 s.2
  -- the extracted primes are exceptional
  have hEexc : ∀ s : 𝓔, ∀ Q : MMP.Mori.PrimeDivisor X,
      M.π (E s).genericPoint ≠ Q.genericPoint := by
    intro s Q hQ
    obtain ⟨D', hD', hv, hcod⟩ := (h𝓔 s.1 s.2).1
    have hc := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hXn.1
      ((hE s).trans hv)
    have h1 := MMP.Positivity.DivisorOver.codimension_center (D (E s))
    have h2 := MMP.Positivity.DivisorOver.codimension_center D'
    change codimension (D (E s)).center = Order.coheight (M.π (E s).genericPoint) at h1
    rw [hc] at h1
    rw [h1, hQ, Q.coheight_genericPoint] at hcod
    exact absurd hcod (by decide)
  -- the log discrepancy of an extracted prime
  have hElog : ∀ s : 𝓔, IsValuationLogDiscrepancy sX Δ s (1 - (M.Γ.coeff (E s) : ℝ)) := by
    intro s
    rcases M.coeff_spec (E s) with ⟨Q, hQ, -⟩ | ⟨-, ⟨-, hlog⟩ | ⟨hs, -⟩⟩
    · exact absurd hQ (hEexc s Q)
    · rw [← hE s]; exact hlog
    · exact absurd ((hE s).symm ▸ s.2) hs
  have hnn : ∀ P : MMP.Mori.PrimeDivisor M.U, 0 ≤ M.Γ.coeff P := by
    intro P
    rcases M.coeff_spec P with ⟨Q, -, hQ⟩ | ⟨hexc, ⟨hs, hlog⟩ | ⟨hs, -⟩⟩
    · rw [hQ]; exact hΔ.1.nonneg Q
    · obtain ⟨a, ha, -, ha1⟩ := (h𝓔 _ hs).2
      obtain ⟨n₁, D₁, -, hv₁, hl₁⟩ := hlog
      obtain ⟨n₂, D₂, -, hv₂, hl₂⟩ := ha
      have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hΔ.1.isPair
        hl₁ hl₂ (hv₁.trans hv₂.symm)
      have h' : ((M.Γ.coeff P : ℚ) : ℝ) ≥ 0 := by linarith
      exact_mod_cast h'
    · exact absurd ⟨hexc, hs⟩ (hfin.2 P)
  refine ⟨M.U, inferInstance, inferInstance, inferInstance, M.π, M.isBirationalMorphism,
    M.isQFactorial, E, M.Γ, M.isProjectiveMorphism, hE, ?_, ?_, ?_,
    fun K hK => (M.isCrepantBoundary_of_isNef hΔ hM hK).1, hElog⟩
  · intro s t h
    apply Subtype.ext
    rw [← hE s, ← hE t, h]
  · intro P
    have hiff := isExceptional_iff_forall_ne hXn (D P)
    change (D P).IsExceptional ↔ _
    rw [hiff]
    constructor
    · intro hP
      rcases M.coeff_spec P with ⟨Q, hQ, -⟩ | ⟨-, ⟨hs, -⟩ | ⟨hs, -⟩⟩
      · exact absurd hQ (hP Q)
      · exact ⟨⟨_, hs⟩, eq_of_valuation_eq M.π hUnv M.isBirationalMorphism (hE ⟨_, hs⟩)⟩
      · exact absurd ⟨hP, hs⟩ (hfin.2 P)
    · rintro ⟨s, rfl⟩
      exact hEexc s
  · exact isKltPair_of_isCrepantBoundary hΔ hK₀ M.π hUnv M.isBirationalMorphism
      M.isCanonicalDivisor hfin.1
      (MMP.Fourfold.isQCartier_of_isQFactorial _ M.isQFactorial _) hnn

end MMP.Fourfold

end
