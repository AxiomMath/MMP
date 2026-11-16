module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGermTypes
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.MarkedChainContraction
import MMP.RingTheory.PowerSeries.CompleteLocalRing
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.RingTheory.RegularLocalRing.LeadingTerm
import MMP.AlgebraicGeometry.Divisor.Cartier
import MMP.AlgebraicGeometry.Resolution.Blowup.PointBlowupIsoOff
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.CoordinateBlowupChart
import MMP.AlgebraicGeometry.Resolution.LinearBlowupCharts
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.PointBlowupComposites
import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
import StacksFrontier.AlgebraicGeometry.Blowup.ReesChartFraction
import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.ChartImage
import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Jacobian
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions
import MMP.AlgebraicGeometry.Resolution.OrderReduction.EmptyEntriesInert
import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.MarkedChainFormalRigidity
import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The boundary ideal of a chain germ of type (3) or (9)

Let `(Y, y; C)` be a surface germ with reduced boundary `C` over an algebraically closed field
`K` of characteristic `0`, of type (3) (`MMP.Flips.IsFig3Type3`) or type (9)
(`MMP.Flips.IsFig3Type9`) of FA Fig. 3, whose minimal resolution has at least one exceptional
curve. Then for some `m ≥ 2` and `q` prime to `m` there is a `K`-isomorphism
`K[[u, v]]^{μ_m} ≃ 𝒪̂_{Y,y}`, `μ_m` acting with weights `(1, q)`
(`MMP.Flips.cyclicInvariants`), carrying the invariants in `(u)` (type (3)), resp. in
`(u) ∩ (v) = (uv)` (type (9)), onto the completed ideal `I_{C,y} 𝒪̂_{Y,y}` of `C`. In particular
`(Spec 𝒪̂_{Y,y}, C) ≅ (T_{m,q}, C^{(1)}_{m,q})`, resp. `(T_{m,q}, C^{(2)}_{m,q})`
(`MMP.Flips.cyclicQuotientCurveOne`, `MMP.Flips.cyclicQuotientCurveTwo`).

## Main results

* `MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isFig3Type3_or_isFig3Type9_of_pos`

## Implementation notes

The two types are one statement indexed by the power series `g` cut out upstairs: `g = u` for
type (3) and `g = uv` for type (9); in `K[[u, v]]` one has `(u) ∩ (v) = (uv)`, so the
invariants in `(u) ∩ (v)` are the invariants in `(g)`, the contraction of `(g)` to
`K[[u, v]]^{μ_m}`. The isomorphism of pairs of affine schemes over `K` is a ring isomorphism of
the rings of global sections compatible with the embeddings of `K`; the ideal of
`C^{(i)}_{m,q}` is that of global sections of the vanishing ideal of
`MMP.Flips.cyclicQuotientImage` of `g`. The ideal sheaf of the reduced boundary `C = ∑ Cᵢ` is
the infimum of the ideal sheaves of its components. "The minimal resolution has a nonempty
exceptional chain" is: some minimal resolution of `(Y, y)` has `n ≥ 1` exceptional curves (the
minimal resolution being unique, this is a property of the germ).

The minimal resolution in the type data and the one with a nonempty chain are compared through
`MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq`: if the former had no exceptional
curves it would be an isomorphism, and the latter, dominated by it, would be one too.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6.1.2,
  16.6.3, Fig. 3
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.Flips

open MMP.Mori

/-! ### The model side -/

private theorem X_dvd_iff_rescale_eq_zero {K : Type v} [Field K] (i : Fin 2)
    (φ : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.X i ∣ φ ↔ MvPowerSeries.rescale (Function.update 1 i 0) φ = 0 := by
  rw [MvPowerSeries.X_dvd_iff]
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_rescale, map_zero]
    by_cases he : e i = 0
    · rw [h e he, mul_zero]
    · rw [Finsupp.prod, Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr he)
        (by simp [he]), zero_mul]
  · intro h e he
    have := congrArg (MvPowerSeries.coeff e) h
    rw [MvPowerSeries.coeff_rescale, map_zero] at this
    have hp : e.prod (fun j n => (Function.update (1 : Fin 2 → K) i 0) j ^ n) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have : j ≠ i := fun hji => (Finsupp.mem_support_iff.mp hj) (hji ▸ he)
      simp [this]
    rwa [hp, one_mul] at this

private theorem prime_X {K : Type v} [Field K] (i : Fin 2) :
    Prime (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
  refine ⟨fun h => by simpa using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h,
    fun hu => ?_, fun a b hab => ?_⟩
  · simpa using MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  · simp only [X_dvd_iff_rescale_eq_zero, map_mul] at hab ⊢
    exact mul_eq_zero.mp hab

private theorem radical_span_X {K : Type v} [Field K] (i : Fin 2) :
    (Ideal.span {MvPowerSeries.X i} : Ideal (MvPowerSeries (Fin 2) K)).radical =
      Ideal.span {MvPowerSeries.X i} :=
  ((Ideal.span_singleton_prime (prime_X i).ne_zero).mpr (prime_X i)).radical

private theorem span_X_inf_span_X {K : Type v} [Field K] :
    (Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1} :
        Ideal (MvPowerSeries (Fin 2) K)) =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} := by
  refine le_antisymm (fun f hf => ?_) (le_inf ?_ ?_)
  · rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hf
    obtain ⟨a, rfl⟩ := hf.1
    rw [Ideal.mem_span_singleton]
    refine mul_dvd_mul_left _ (((prime_X 1).dvd_or_dvd hf.2).resolve_left fun h => ?_)
    simpa using MvPowerSeries.X_dvd_iff.mp h (Finsupp.single 0 1) (by simp)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

/-- The global sections of the vanishing ideal of a closed subset `Z` of `Spec R`, read in `R`
through `Γ(Spec R, ⊤) ≅ R`, form the vanishing ideal of `Z`. -/
private theorem comap_ΓSpecIso_vanishingIdeal (R : CommRingCat.{v})
    (Z : TopologicalSpace.Closeds (Spec R)) :
    Ideal.comap (Scheme.ΓSpecIso R).inv.hom
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨⊤, isAffineOpen_top (Spec R)⟩) =
      PrimeSpectrum.vanishingIdeal (R := R) (Z : Set (Spec R)) := by
  ext x
  refine Iff.trans ?_ (PrimeSpectrum.mem_vanishingIdeal _ _).symm
  rw [Ideal.mem_comap, Scheme.IdealSheafData.vanishingIdeal_ideal,
    PrimeSpectrum.mem_vanishingIdeal]
  simp only [Set.mem_preimage]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  constructor
  · intro h (p : Spec R) hp
    have hp' : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) = p := by
      rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
      rfl
    have hmem : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) ∈
        (Z : Set (Spec R)) := by rwa [hp']
    have := h (Spec.map (Scheme.ΓSpecIso R).hom p) hmem
    change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) ∈ p.asIdeal at this
    simpa using this
  · intro h p hp
    exact h _ hp

/-- The vanishing ideal of the image of a set under `Spec` of a ring map is the preimage of its
vanishing ideal. -/
private theorem vanishingIdeal_image_comap {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (S : Set (PrimeSpectrum B)) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap f '' S) =
      Ideal.comap f (PrimeSpectrum.vanishingIdeal S) := by
  ext a
  simp only [PrimeSpectrum.mem_vanishingIdeal, Set.forall_mem_image, Ideal.mem_comap]
  rfl

/-- The ideal of global sections of the reduced image of `(g = 0)` in `T_{m,q}`, read in
`K[[u, v]]^{μ_m}`, consists of the invariants in the radical of `(g)`. -/
private theorem comap_vanishingIdeal_cyclicQuotientImage {K : Type v} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (g : MvPowerSeries (Fin 2) K) :
    Ideal.comap (Scheme.ΓSpecIso (.of (cyclicInvariants K m q))).inv.hom
        ((Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h g)).ideal
          ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g}).radical := by
  rw [comap_ΓSpecIso_vanishingIdeal]
  exact (PrimeSpectrum.vanishingIdeal_closure (R := cyclicInvariants K m q) _).trans <|
    (vanishingIdeal_image_comap (cyclicInvariants K m q).subtype _).trans <| by
      rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

/-! ### The smooth case: the germ, its completion and a smooth boundary -/

private theorem coheight_ne_zero {Y : Scheme.{v}} [IrreducibleSpace Y] {x : Y}
    (hx : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x ≠ 0 := by
  intro h0
  have hgx : genericPoint Y ≤ x :=
    Order.coheight_eq_zero.mp h0 ((genericPoint_spec Y).specializes (Set.mem_univ x))
  refine hx (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact isClosed_closure.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hgx))

private theorem coheight_eq_one_of_not_isClosed {k : Type v} [Field k] {Y : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hYd : topologicalKrullDim Y = 2) {x : Y} (hx : ¬ IsClosed ({x} : Set Y))
    (hx' : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x = 1 := by
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ closure ({x} : Set Y), z ≠ x := by
    by_contra! h
    exact hx (isClosed_of_closure_subset h)
  have hz2 : Order.coheight z ≤ 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY z
    rw [hYd] at h
    generalize topologicalKrullDim (closure ({z} : Set Y)) = d at h
    induction d using WithBot.recBotCoe with
    | bot => simp at h
    | coe d => exact le_add_self.trans_eq (WithBot.coe_inj.mp (by push_cast; exact h))
  have h := (Order.coheight_add_one_le (lt_of_le_not_ge (α := Y)
    (specializes_iff_mem_closure.mpr hz) fun h' =>
      hzx ((specializes_iff_mem_closure.mpr hz).antisymm h').eq.symm)).trans hz2
  rw [← one_add_one_eq_two, ENat.add_le_add_iff_right ENat.one_ne_top] at h
  exact h.antisymm (Order.one_le_iff_ne_zero.mpr (coheight_ne_zero hx'))

private theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{v}} [IrreducibleSpace Y]
    {ξ η : Y} (hη : Order.coheight η = 1) (h : ξ ⤳ η)
    (hξ : closure ({ξ} : Set Y) ≠ Set.univ) : ξ = η := by
  by_contra hne
  have h1 := Order.coheight_add_one_le (lt_of_le_not_ge (α := Y) h fun h' =>
    hne (h.antisymm h').eq)
  rw [hη] at h1
  exact coheight_ne_zero hξ
    (nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using h1)))

/-- A non-closed point of the fibre of a resolution over the point lies on an exceptional curve.
-/
private theorem exists_mem_support_of_not_isClosed {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g) {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) {η : Y}
    (hηF : η ∈ g.base ⁻¹' {P}) (hη : ¬ IsClosed ({η} : Set Y)) : ∃ j, η ∈ (E j).support := by
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have hYd := hg.topologicalKrullDim_eq
  obtain ⟨hFcl, hFne⟩ := hg.isClosed_preimage_and_ne_univ
  have hne : closure ({η} : Set Y) ≠ Set.univ := fun h =>
    hFne (Set.eq_univ_of_univ_subset
      (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηF)))
  have hη1 := coheight_eq_one_of_not_isClosed (g ≫ sX) hYd hη hne
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hη1
  have hsupp : D.support = closure {η} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  have hD : IsGermExceptionalCurve g P D := by
    refine ⟨⟨⟨?_, ?_⟩, fun Z ⟨hZirr, hZF⟩ hle => ?_⟩,
      isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd _⟩
    · rw [hsupp]; exact isIrreducible_singleton.closure
    · rw [hsupp]; exact hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηF)
    · rw [hsupp] at hle ⊢
      have hgen := hZirr.isGenericPoint_genericPoint_closure
      have hξF : hZirr.genericPoint ∈ g.base ⁻¹' {P} :=
        hFcl.closure_subset_iff.mpr hZF hgen.mem
      have hξ := eq_of_specializes_of_coheight_eq_one hη1
        (hgen.specializes (subset_closure (hle (subset_closure rfl))))
        (fun h => hFne (Set.eq_univ_of_univ_subset
          (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξF))))
      rw [← hξ, hgen.def]
      exact subset_closure
  obtain ⟨j, hj⟩ := hE.exists_eq D hD
  refine ⟨j, ?_⟩
  rw [hj, hsupp]
  exact subset_closure rfl

/-- A resolution of a surface germ without exceptional curves has finite fibre over the point. -/
private theorem finite_preimage_of_isExceptionalCurveEnumeration_zero {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g)
    {E : Fin 0 → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) :
    (g.base ⁻¹' {P}).Finite := by
  have : IsIntegral Y := hg.isVariety.toIsIntegral
  obtain ⟨hFcl, -⟩ := hg.isClosed_preimage_and_ne_univ
  have hcl : ∀ η ∈ g.base ⁻¹' {P}, IsClosed ({η} : Set Y) := fun η hηF => by
    by_contra hη
    exact (exists_mem_support_of_not_isClosed hg hE hηF hη).choose.elim0
  -- a closed subset of a Noetherian space all of whose points are closed is finite
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨S, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨g.base ⁻¹' {P}, hFcl⟩
  have hS' : g.base ⁻¹' {P} = ⋃ (K : TopologicalSpace.Closeds Y) (_ : K ∈ S), (K : Set Y) := by
    have := congrArg (fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hS
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
    simpa [Set.iSup_eq_iUnion] using this
  rw [hS']
  refine Set.Finite.biUnion S.finite_toSet fun K hK => ?_
  have hKirr : IsIrreducible (K : Set Y) := hSirr ⟨K, hK⟩
  have hgen := hKirr.isGenericPoint_genericPoint_closure
  rw [K.isClosed.closure_eq] at hgen
  have hKF : (K : Set Y) ⊆ g.base ⁻¹' {P} := by
    rw [hS']; exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds Y =>
      (K : Set Y)) hK
  have := hcl _ (hKF hgen.mem)
  rw [← hgen.def, this.closure_eq]
  exact Set.finite_singleton _

/-- A subset of Krull dimension one is not a single point. -/
private theorem ne_singleton_of_topologicalKrullDim_eq_one {Y : Type*} [TopologicalSpace Y]
    {S : Set Y} (hS : topologicalKrullDim S = 1) (x : Y) : S ≠ {x} := by
  rintro rfl
  have : DiscreteTopology ({x} : Set Y) := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology ({x} : Set Y)
  rw [hS] at h0
  exact absurd h0 (by decide)

/-- At a closed point `y` of a prime divisor `C` of a surface, the ideal of `C` in `𝒪_{Y,y}` is
neither `0` nor the maximal ideal. -/
private theorem stalk_idealSheaf_ne_bot_and_ne_maximalIdeal {k : Type v} [Field k]
    {Y : Scheme.{v}} {sY : Y ⟶ Spec (.of k)} (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ C.support)
    (hycl : IsClosed ({y} : Set Y)) :
    IdealSheafData.stalk C.idealSheaf y ≠ ⊥ ∧
      IdealSheafData.stalk C.idealSheaf y ≠ maximalIdeal (Y.presheaf.stalk y) := by
  have : IsIntegral Y := hY.toIsIntegral
  have hC := isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY hYd C
  have hdimC : topologicalKrullDim (C.support : Set Y) = 1 := by
    rw [← topologicalKrullDim_subscheme]; exact hC.2
  have hsupp := MMP.Resolution.Aux.support_eq_closure_genericPoint C
  constructor
  · intro h0
    have hξ : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
    have hmem : genericPoint Y ∈ C.support :=
      (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C.idealSheaf hξ).2
        (by rw [h0]; exact bot_le)
    have huniv : (C.support : Set Y) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec Y).def]
      exact C.idealSheaf.support.isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hmem)
    rw [huniv, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq, hYd] at hdimC
    exact absurd hdimC (by decide)
  · intro hm
    have hη : AlgebraicGeometry.PrimeDivisor.genericPoint C ⤳ y := by
      rwa [specializes_iff_mem_closure, ← hsupp]
    have hle := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C.idealSheaf hη).1
      (by
        change _ ∈ (C.support : Set Y)
        rw [hsupp]; exact subset_closure rfl)
    have hrefl : MMP.Intersection.primeOfSpecializes (specializes_refl y) ≤
        MMP.Intersection.primeOfSpecializes hη := by
      intro a ha
      apply hle
      rw [hm]
      change (Y.presheaf.stalkSpecializes (specializes_refl y)).hom a ∈ maximalIdeal _ at ha
      rwa [TopCat.Presheaf.stalkSpecializes_refl] at ha
    have hyη := MMP.Intersection.specializes_of_primeOfSpecializes_le _ _ hrefl
    have hηy : AlgebraicGeometry.PrimeDivisor.genericPoint C = y := by
      have := hyη.mem_closure
      rwa [hycl.closure_eq] at this
    exact ne_singleton_of_topologicalKrullDim_eq_one hdimC y
      (by rw [hsupp, hηy, hycl.closure_eq])

/-! ### The completed local ring at a closed point -/

/-- **The completed local ring at a closed point is `K[[x₁, …, xₙ]]` over `K`**, the variables
going to any generators `z₁, …, zₙ` of the maximal ideal, `n = dim 𝒪_{X,p}`. -/
private theorem exists_ringEquiv_mvPowerSeries_of_span_eq {K : Type v}
    [Field K] [IsAlgClosed K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType sX] [IsLocallyNoetherian X] (p : X) (hp : IsClosed ({p} : Set X))
    {n : ℕ} (hdim : ringKrullDim (X.presheaf.stalk p) = n)
    {z : Fin n → AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)}
    (hz : Ideal.span (Set.range z) =
      maximalIdeal (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) :
    letI := Mori.stalkAlgebra sX p
    ∃ Φ : MvPowerSeries (Fin n) K ≃+*
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      (∀ c : K, Φ (MvPowerSeries.C c) = algebraMap (X.presheaf.stalk p)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
          (algebraMap K (X.presheaf.stalk p) c)) ∧
      ∀ i, Φ (MvPowerSeries.X i) = z i := by
  letI := Mori.stalkAlgebra sX p
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)))).comp
        ((algebraMap (X.presheaf.stalk p) _).comp (algebraMap K (X.presheaf.stalk p)))) := by
    intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := AdicCompletion.residueField_map_bijective (X.presheaf.stalk p) |>.2
      (residue _ w)
    obtain ⟨r, rfl⟩ := residue_surjective r
    obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sX p hp r
    refine ⟨c, ?_⟩
    change residue _ (algebraMap (X.presheaf.stalk p) _ (algebraMap K (X.presheaf.stalk p) c)) =
      residue _ w
    rw [← hr, ← ResidueField.map_residue]
    exact congrArg _ hc
  obtain ⟨F, hFs, hFX, hFC⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom (maximalIdeal
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) z hz _ hsurj
  have hinj := MMP.Flips.ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F hFs
    (MvPowerSeries.ringKrullDim_le K n)
    (by rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hdim])
  exact ⟨RingEquiv.ofBijective F ⟨hinj, hFs⟩, hFC, hFX⟩

/-! ### Birational transforms and the local equation of a reduced boundary -/

/-- In a local ring of dimension two the maximal ideal has height two. -/
private theorem height_maximalIdeal_eq_two {R : Type*} [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) : (maximalIdeal R).height = 2 := by
  have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hdim] at h
  exact WithBot.coe_injective (h.trans rfl)

/-- In a two-dimensional regular local ring a prime ideal other than `0` and `𝔪` is generated by
a prime element. -/
private theorem exists_prime_eq_span_of_ne {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (P : Ideal R) [hP : P.IsPrime] (h0 : P ≠ ⊥)
    (hm : P ≠ maximalIdeal R) : ∃ π : R, Prime π ∧ P = Ideal.span {π} := by
  have : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid R
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hbot : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h0)
  have hlt : P < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hm
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hP1 : P.height = 1 := by
    rw [height_maximalIdeal_eq_two hdim] at h2
    have h1' : (1 : ℕ∞) ≤ P.height := le_trans le_add_self h1
    generalize P.height = h at h1' h2 ⊢
    induction h using ENat.recTopCoe with
    | top => simp at h2
    | coe n =>
      have h1'' : 1 ≤ n := by exact_mod_cast h1'
      have h2' : n + 1 ≤ 2 := by exact_mod_cast h2
      obtain rfl : n = 1 := by omega
      rfl
  obtain ⟨π, hπP, hπ⟩ := hP.exists_mem_prime_of_ne_bot h0
  exact ⟨π, hπ, Ideal.eq_span_singleton_of_height_eq_one hP1 hπP hπ⟩

/-- The ideal of a prime divisor in a local ring at a point of its support is prime. -/
private theorem isPrime_stalk_idealSheaf {Y : Scheme} (C : Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ C.support) : (IdealSheafData.stalk C.idealSheaf y).IsPrime := by
  obtain ⟨y', rfl⟩ : y ∈ Set.range C.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have := C.integral
  rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
  exact RingHom.ker_isPrime _

/-- At a closed point of a prime divisor on a regular surface, the ideal of the divisor in the
local ring is principal. -/
private theorem exists_stalk_idealSheaf_eq_span_singleton {k : Type v} [Field k] [IsAlgClosed k]
    {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX)
    (hXd : topologicalKrullDim X = 2) (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    {x : X} (hx : IsClosed ({x} : Set X)) (D : Mori.PrimeDivisor X) (hD : x ∈ D.support) :
    ∃ π, IdealSheafData.stalk D.idealSheaf x = Ideal.span {π} := by
  have := hreg x
  have := isPrime_stalk_idealSheaf D hD
  obtain ⟨h0, hm⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hX hXd D hD hx
  obtain ⟨π, -, he⟩ := exists_prime_eq_span_of_ne
    (MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sX hX hXd x hx) _ h0 hm
  exact ⟨π, he⟩

/-- On a surface, the generic point of a prime divisor is not a closed point. -/
private theorem genericPoint_ne_of_isClosed {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) (hXd : topologicalKrullDim X = 2)
    (C : Mori.PrimeDivisor X) {x : X} (hx : IsClosed ({x} : Set X)) : C.genericPoint ≠ x := by
  intro hgen
  have hdimC : topologicalKrullDim (C.support : Set X) = 1 := by
    rw [← topologicalKrullDim_subscheme]
    exact (isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hX hXd C).2
  refine ne_singleton_of_topologicalKrullDim_eq_one hdimC x ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  change closure {C.genericPoint} = _
  rw [hgen, hx.closure_eq]

/-! ### Curvilinear markings at a point -/

section Markings

section

open Polynomial

section MarkAlg

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {M : Ideal R} {h w : R}

private theorem span_pair_pow_le (h w : R) (j : ℕ) :
    Ideal.span {h, w} ^ j ≤ Ideal.span {h} ⊔ Ideal.span {w ^ j} := by
  induction j with
  | zero => simp
  | succ j ihj =>
    rw [pow_succ]
    calc Ideal.span {h, w} ^ j * Ideal.span {h, w}
        ≤ (Ideal.span {h} ⊔ Ideal.span {w ^ j}) * Ideal.span {h, w} :=
          Ideal.mul_mono_left ihj
      _ ≤ Ideal.span {h} ⊔ Ideal.span {w ^ (j + 1)} := by
          rw [Ideal.sup_mul, Ideal.span_insert, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · exact le_sup_of_le_left Ideal.mul_le_right
          · exact le_sup_of_le_left Ideal.mul_le_left
          · exact le_sup_of_le_left Ideal.mul_le_right
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_right

/-- Modulo `(h) + 𝔪 ^ j`, every element is a polynomial in `w`, for `𝔪 = (h, w)` with residue
field `K`. -/
private theorem exists_sub_aeval_mem (hM : Ideal.span {h, w} = M)
    (hres : ∀ g : R, ∃ c : K, g - algebraMap K R c ∈ M) (j : ℕ) (g : R) :
    ∃ P : K[X], g - aeval w P ∈ Ideal.span {h} ⊔ M ^ j := by
  induction j generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih g
    obtain ⟨a, ha, r, hr, hra⟩ := Submodule.mem_sup.mp hP
    rw [← hM] at hr
    obtain ⟨a', ha', r', hr', hr'a⟩ := Submodule.mem_sup.mp (span_pair_pow_le h w j hr)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hr'
    obtain ⟨c, hc⟩ := hres b
    refine ⟨P + Polynomial.C c * Polynomial.X ^ j, ?_⟩
    have : g - aeval w (P + Polynomial.C c * Polynomial.X ^ j) =
        (a + a') + (b - algebraMap K R c) * w ^ j := by
      rw [map_add, map_mul, aeval_C, map_pow, aeval_X]
      linear_combination -hra - hr'a
    rw [this]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ ha ha')) ?_
    refine Submodule.mem_sup_right ?_
    rw [pow_succ']
    have hw : w ∈ M := by rw [← hM]; exact Ideal.subset_span (by simp)
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hw j)

/-- Elements of `(X₀, X₁ ^ (n + 1))` have no monomials `X₁ ^ j`, `j ≤ n`. -/
private theorem coeff_single_one_eq_zero_of_mem {n : ℕ} {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 1 ^ (n + 1)}) {j : ℕ}
    (hj : j ≤ n) : MvPowerSeries.coeff (Finsupp.single 1 j) f = 0 := by
  rw [Ideal.mem_span_pair] at hf
  obtain ⟨a, b, rfl⟩ := hf
  rw [map_add, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [MvPowerSeries.coeff_X_pow]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg (fun e => e 1) hp
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, h] at this
    omega
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [MvPowerSeries.coeff_X]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg (fun e => e 0) hp
    simp [h] at this

variable (K) in
/-- Evaluation of a polynomial at `X₁`. -/
private theorem coeff_eval₂_X_one (P : K[X]) (j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j)
      (P.eval₂ MvPowerSeries.C (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = P.coeff j := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.coeff_add]
  | monomial d c =>
    rw [Polynomial.eval₂_monomial, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow,
      Polynomial.coeff_monomial]
    by_cases hd : d = j
    · subst hd; simp
    · rw [if_neg (fun h => hd (Finsupp.single_injective 1 h).symm), if_neg hd,
        mul_zero]

/-- **The kernel of `K[X] → R/(h, w ^ (n + 1))`**, read off a coordinate system
`R → K[[x₀, x₁]]` with `h ↦ x₀`, `w ↦ x₁`. -/
private theorem X_pow_dvd_of_aeval_mem (Q : R →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (algebraMap K R c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) {n : ℕ} {P : K[X]}
    (hP : aeval w P ∈ Ideal.span {h, w ^ (n + 1)}) : Polynomial.X ^ (n + 1) ∣ P := by
  have hmem : Q (aeval w P) ∈ Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 1 ^ (n + 1)} := by
    have := Ideal.mem_map_of_mem Q hP
    rwa [Ideal.map_span, Set.image_pair, map_pow, hQh, hQw] at this
  have hQP : Q (aeval w P) = P.eval₂ MvPowerSeries.C (MvPowerSeries.X 1) := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hQw]
    congr 1
    ext c : 1
    exact hQc c
  rw [Polynomial.X_pow_dvd_iff]
  intro j hj
  rw [hQP] at hmem
  rw [← coeff_eval₂_X_one K P j]
  exact coeff_single_one_eq_zero_of_mem (n := n) (j := j) hmem (by omega)

/-- **A curvilinear quotient.** For `𝔪 = (h, w)` with residue field `K`, and a coordinate system
`h ↦ x₀`, `w ↦ x₁`, the quotient `R/(h, w ^ (n + 1))` is `K[X]/(X ^ (n + 1))`, `w ↦ X`. -/
private theorem exists_ringHom_ker_eq (hM : Ideal.span {h, w} = M)
    (hres : ∀ g : R, ∃ c : K, g - algebraMap K R c ∈ M) (Q : R →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (algebraMap K R c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) (n : ℕ) :
    ∃ φ : R →+* K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}, Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span {h, w ^ (n + 1)} ∧
      (∀ c : K, φ (algebraMap K R c) = algebraMap K _ c) ∧
      φ w = Ideal.Quotient.mk _ Polynomial.X := by
  set 𝔞 := Ideal.span {h, w ^ (n + 1)}
  let ψ : K[X] →+* R ⧸ 𝔞 := (Ideal.Quotient.mk 𝔞).comp (aeval w).toRingHom
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hP⟩ := exists_sub_aeval_mem hM hres (n + 1) g
    refine ⟨P, ?_⟩
    change Ideal.Quotient.mk 𝔞 (aeval w P) = _
    rw [Ideal.Quotient.eq]
    have hle : Ideal.span {h} ⊔ M ^ (n + 1) ≤ 𝔞 := by
      rw [← hM]
      refine sup_le ?_ ((span_pair_pow_le h w (n + 1)).trans ?_)
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.subset_span (by simp)
      · refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff] <;>
          exact Ideal.subset_span (by simp)
    have := hle hP
    rw [← neg_sub]
    exact neg_mem this
  have hker : RingHom.ker ψ = Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)} := by
    ext P
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change Ideal.Quotient.mk 𝔞 (aeval w P) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · exact X_pow_dvd_of_aeval_mem Q hQc hQh hQw
    · rintro ⟨P', rfl⟩
      rw [map_mul, map_pow, aeval_X]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  let e : (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) ≃+* R ⧸ 𝔞 :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ P : K[X], e (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk 𝔞 (aeval w P) := fun P => rfl
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔞), ?_, ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp Ideal.Quotient.mk_surjective
  · ext g
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq, IsScalarTower.algebraMap_apply K K[X] (K[X] ⧸ _) c,
      Ideal.Quotient.algebraMap_eq, ← Polynomial.C_eq_algebraMap, he, aeval_C]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq, he, aeval_X]

end MarkAlg

end

section PointImmersion

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{v}} (p : X) {A : CommRingCat.{v}} [IsLocalRing A]
  (φ : X.presheaf.stalk p ⟶ A) [IsLocalHom φ.hom]

private theorem pointι_closedPoint :
    (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint A) = p := by
  rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem range_pointι (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A) :
    Set.range (Spec.map φ ≫ X.fromSpecStalk p) = {p} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [hA z, pointι_closedPoint]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨_, pointι_closedPoint x φ⟩

private theorem isClosedImmersion_pointι (hp : IsClosed ({p} : Set X)) (hφ : Function.Surjective φ)
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A) :
    IsClosedImmersion (Spec.map φ ≫ X.fromSpecStalk p) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective _ hφ
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [range_pointι p φ hA]
  exact hp

private theorem ker_pointι_ideal (U : X.affineOpens) (hU : p ∈ U.1)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    (Spec.map φ ≫ X.fromSpecStalk p).ker.ideal U =
      Ideal.comap (X.presheaf.germ U.1 p hU).hom (RingHom.ker φ.hom) := by
  rw [Scheme.Hom.ker_apply]
  have hU' : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint A) ∈ U.1 := by
    rw [pointι_closedPoint]; exact hU
  have key := Scheme.germ_stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk p) U.1 hU'
  rw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk] at key
  ext s
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
  have := congrArg (fun g => g.hom s) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this]
  exact (map_eq_zero_iff _ (ConcreteCategory.injective_of_mono_of_preservesPullback _)).symm

private theorem stalk_ker_pointι [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    IdealSheafData.stalk (Spec.map φ ≫ X.fromSpecStalk p).ker p = RingHom.ker φ.hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ p ⟨U, hU⟩ hpU, ker_pointι_ideal p φ ⟨U, hU⟩ hpU]
  letI := X.presheaf.algebra_section_stalk ⟨p, hpU⟩
  haveI := hU.isLocalization_stalk ⟨p, hpU⟩
  exact IsLocalization.map_comap (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl _ _

private theorem support_ker_pointι (hp : IsClosed ({p} : Set X))
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    ((Spec.map φ ≫ X.fromSpecStalk p).ker.support : Set X) = {p} := by
  rw [Scheme.Hom.support_ker, range_pointι p φ hA, hp.closure_eq]

private theorem stalk_ker_pointι_of_ne (hp : IsClosed ({p} : Set X))
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] {x : X} (hx : x ≠ p) :
    IdealSheafData.stalk (Spec.map φ ≫ X.fromSpecStalk p).ker x = ⊤ := by
  rw [Stacks.Divisors.stalk_eq_top_iff_notMem_support]
  intro h
  have : x ∈ ((Spec.map φ ≫ X.fromSpecStalk p).ker.support : Set X) := h
  rw [support_ker_pointι p φ hp hA] at this
  exact hx this

private theorem fromSpecStalk_comp_eq {K : Type v} [Field K] (sX : X ⟶ Spec (.of K)) :
    X.fromSpecStalk p ≫ sX = Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)) := by
  have h1 : sX = X.toSpecΓ ≫ Spec.map sX.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [h1]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

private theorem exists_iso_subscheme_ker_pointι {K : Type v} [Field K] (sX : X ⟶ Spec (.of K))
    [Algebra K A] (hφK : ∀ c : K, φ.hom (((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c) = algebraMap K A c)
    [IsClosedImmersion (Spec.map φ ≫ X.fromSpecStalk p)] :
    ∃ e : (Spec.map φ ≫ X.fromSpecStalk p).ker.subscheme ≅ Spec A,
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        (Spec.map φ ≫ X.fromSpecStalk p).ker.subschemeι ≫ sX := by
  set ι := Spec.map φ ≫ X.fromSpecStalk p
  refine ⟨(asIso ι.toImage).symm, ?_⟩
  have h1 : (asIso ι.toImage).symm.hom ≫ ι = ι.ker.subschemeι := by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  have h2 : ι ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    change Spec.map φ ≫ X.fromSpecStalk p ≫ sX = _
    rw [fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext c
    exact hφK c
  rw [← h2, ← Category.assoc, h1]

end PointImmersion

section Marking

open Polynomial

set_option backward.isDefEq.respectTransparency false

private theorem eq_closedPoint_of_finite {K : Type v} [Field K] {A : CommRingCat.{v}}
    [IsLocalRing A]
    [Algebra K A] [Module.Finite K A] (z : Spec A) : z = IsLocalRing.closedPoint A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hz : z.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime z.asIdeal
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hz)

/-- **Curvilinear point markings.** At a closed point `p` with `𝔪_p = (h, w)`, residue field
`K` and a coordinate system `h ↦ x₀`, `w ↦ x₁`, the ideal sheaves `Zₙ` with stalk
`(h, w ^ (n + 1))` at `p` and trivial elsewhere exist, and `Zₙ ≅ Spec K[X]/(X ^ (n + 1))` over
`K`. -/
private theorem exists_marking {K : Type v} [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
    (p : X)
    (hp : IsClosed ({p} : Set X)) {h w : X.presheaf.stalk p}
    (hhw : Ideal.span {h, w} = IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (hres : ∀ g : X.presheaf.stalk p, ∃ c : K, g - ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (Q : X.presheaf.stalk p →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) :
    ∃ Z : ℕ → X.IdealSheafData,
      (∀ n, ((Z n).support : Set X) = {p}) ∧
      (∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)}) ∧
      (∀ n x, x ≠ p → IdealSheafData.stalk (Z n) x = ⊤) ∧
      (∀ n, ∃ e : (Z n).subscheme ≅
        Spec (.of (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (Z n).subschemeι ≫ sX) := by
  letI : Algebra K (X.presheaf.stalk p) := ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom.toAlgebra
  have hφ : ∀ n : ℕ,
      ∃ φ : X.presheaf.stalk p →+* K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)},
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span {h, w ^ (n + 1)} ∧
      (∀ c : K, φ (algebraMap K _ c) = algebraMap K _ c) ∧
      φ w = Ideal.Quotient.mk _ Polynomial.X :=
    fun n => exists_ringHom_ker_eq hhw hres Q hQc hQh hQw n
  choose φ hsurj hker hK hφw using hφ
  refine ⟨fun n => (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p).ker, ?_⟩
  have hfin : ∀ n : ℕ, Module.Finite K (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
    fun n => (AdjoinRoot.powerBasis' (monic_X_pow (R := K) (n + 1))).finite
  have hloc : ∀ n : ℕ,
      IsLocalRing (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
    fun n => by
      haveI : Nontrivial (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by
          rw [Ne, Ideal.span_singleton_eq_top]
          exact (isUnit_pow_iff (Nat.succ_ne_zero n)).not.mpr Polynomial.not_isUnit_X)
      exact IsLocalRing.of_surjective' (φ n) (hsurj n)
  have hlh : ∀ n, IsLocalHom (φ n) := fun n => IsLocalHom.of_surjective _ (hsurj n)
  have hA : ∀ n (z : Spec (.of (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}))),
      z = IsLocalRing.closedPoint _ := fun n z => by
    haveI := hfin n; haveI := hloc n
    exact eq_closedPoint_of_finite (K := K) (A := .of (K[X] ⧸ _)) z
  have hci : ∀ n, IsClosedImmersion (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p) :=
    fun n => by
      haveI := hloc n; haveI := hlh n
      exact isClosedImmersion_pointι p (CommRingCat.ofHom (φ n)) hp (hsurj n) (hA n)
  have hqc : ∀ n, QuasiCompact (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p) :=
    fun n => by
      haveI := hci n
      haveI := IsClosedImmersion.instIsAffineHom
        (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p)
      exact instQuasiCompactOfIsAffineHom _
  refine ⟨fun n => ?_, fun n => ?_, fun n x hx => ?_, fun n => ?_⟩ <;>
    haveI := hloc n <;> haveI := hlh n <;> haveI := hci n <;> haveI := hqc n
  · exact support_ker_pointι p (CommRingCat.ofHom (φ n)) hp (hA n)
  · rw [stalk_ker_pointι p (CommRingCat.ofHom (φ n))]
    exact hker n
  · exact stalk_ker_pointι_of_ne p (CommRingCat.ofHom (φ n)) hp (hA n) hx
  · exact exists_iso_subscheme_ker_pointι p (CommRingCat.ofHom (φ n)) sX (hK n)

end Marking

section MarkingProps

private theorem stalk_sup' {X : Scheme.{v}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  simp only [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Ideal.map_sup]

/-- The markings are compatible with the thickenings of a curve with local equation `w`. -/
private theorem marking_le_and_eq_sup {X : Scheme.{v}} {p : X} {h w : X.presheaf.stalk p}
    (I : X.IdealSheafData) (hI : IdealSheafData.stalk I p = Ideal.span {w})
    (Z : ℕ → X.IdealSheafData)
    (hZp : ∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)})
    (hZx : ∀ n x, x ≠ p → IdealSheafData.stalk (Z n) x = ⊤) :
    (∀ n, I ^ (n + 1) ≤ Z n) ∧ (∀ n, Z n = Z (n + 1) ⊔ I ^ (n + 1)) := by
  refine ⟨fun n => IdealSheafData.le_of_stalk_le _ _ fun x => ?_,
    fun n => IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_⟩
  · by_cases hx : x = p
    · subst hx
      rw [MMP.Resolution.Aux.stalk_pow, hI, hZp, Ideal.span_singleton_pow, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    · rw [hZx n x hx]; exact le_top
  · rw [stalk_sup']
    by_cases hx : x = p
    · subst hx
      rw [MMP.Resolution.Aux.stalk_pow, hI, hZp, hZp, Ideal.span_singleton_pow]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro z (rfl | rfl)
        · exact Ideal.mem_sup_left (Ideal.subset_span (by simp))
        · exact Ideal.mem_sup_right (Ideal.subset_span rfl)
      · refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
        · rintro z (rfl | rfl)
          · exact Ideal.subset_span (by simp)
          · rw [pow_succ w (n + 1)]
            exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
        · rintro z rfl
          exact Ideal.subset_span (by simp)
    · rw [hZx n x hx, hZx (n + 1) x hx, top_sup_eq]

end MarkingProps

section Vanishing

set_option backward.isDefEq.respectTransparency false

private theorem germ_mem_stalk_congr {X : Scheme.{v}} (Z : X.IdealSheafData) {V : X.Opens}
    (a : Γ(X, V))
    {q q' : X} (h : q = q') (hq : q ∈ V) (hq' : q' ∈ V) :
    (X.presheaf.germ V q hq).hom a ∈ IdealSheafData.stalk Z q ↔
      (X.presheaf.germ V q' hq').hom a ∈ IdealSheafData.stalk Z q' := by
  subst h; rfl

/-- **Vanishing on a subscheme supported at one point** is membership of the germ in the stalk
of its ideal. -/
private theorem appLE_subschemeι_eq_zero_iff {X : Scheme.{v}} (Z : X.IdealSheafData) {p : X}
    (hZ : (Z.support : Set X) = {p}) {V : X.Opens} (hpV : p ∈ V)
    (hle : ⊤ ≤ Z.subschemeι ⁻¹ᵁ V) (a : Γ(X, V)) :
    (Z.subschemeι.appLE V ⊤ hle).hom a = 0 ↔
      (X.presheaf.germ V p hpV).hom a ∈ IdealSheafData.stalk Z p := by
  have hpt : ∀ t : Z.subscheme, Z.subschemeι t = p := fun t => by
    have : Z.subschemeι t ∈ (Z.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
    rwa [hZ] at this
  have hgerm : ∀ (t : Z.subscheme), Z.subscheme.presheaf.germ ⊤ t trivial
      ((Z.subschemeι.appLE V ⊤ hle).hom a) =
        Z.subschemeι.stalkMap t (X.presheaf.germ V (Z.subschemeι t) (hle trivial) a) := by
    intro t
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
    rw [CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hker : ∀ t : Z.subscheme, ∀ b : X.presheaf.stalk (Z.subschemeι t),
      Z.subschemeι.stalkMap t b = 0 ↔ b ∈ IdealSheafData.stalk Z (Z.subschemeι t) := by
    intro t b
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, RingHom.mem_ker]
  obtain ⟨t₀, ht₀⟩ : ∃ t : Z.subscheme, Z.subschemeι t = p := by
    have : p ∈ (Z.support : Set X) := by rw [hZ]; rfl
    rwa [← Scheme.IdealSheafData.range_subschemeι] at this
  constructor
  · intro h0
    have := hgerm t₀
    rw [h0, map_zero, eq_comm, hker] at this
    exact (germ_mem_stalk_congr Z a ht₀ _ hpV).mp this
  · intro hmem
    refine TopCat.Presheaf.section_ext Z.subscheme.sheaf ⊤ _ _ fun t _ => ?_
    change Z.subscheme.presheaf.germ ⊤ t trivial _ = Z.subscheme.presheaf.germ ⊤ t trivial 0
    rw [map_zero, hgerm, hker]
    exact (germ_mem_stalk_congr Z a (hpt t) _ hpV).mpr hmem

end Vanishing

end Markings

/-! ### The completed boundary ideal, read on markings -/

section BoundaryIdeal

open Scheme.IdealSheafData in
/-- The formal function of a germ `s` at `y` vanishes on a marking `Z` supported at a point `p`
over `y` exactly when the germ of `f^♯ s` at `p` lies in the stalk of `Z`. -/
private theorem appTop_inclusion_completionToFormalNeighborhood_eq_zero_iff
    {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y) (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) {p : X} (hp : f.base p = y)
    (Z : X.IdealSheafData) (hZs : (Z.support : Set X) = {p}) (n : ℕ) (hZ : D ^ (n + 1) ≤ Z)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)) :
    (inclusion hZ).appTop.hom ((D.completionToFormalNeighborhood f y hmaps
        (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) (Y.presheaf.germ U y hy s))).1 n) = 0 ↔
      X.presheaf.germ (f ⁻¹ᵁ U) p (show f.base p ∈ U from hp ▸ hy) (f.app U s) ∈
        IdealSheafData.stalk Z p := by
  have hpU : p ∈ f ⁻¹ᵁ U := show f.base p ∈ U from hp ▸ hy
  have hle : (⊤ : Z.subscheme.Opens) ≤ Z.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro t _
    have ht : Z.subschemeι t ∈ (Z.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
    rw [hZs, Set.mem_singleton_iff] at ht
    change f.base (Z.subschemeι t) ∈ U
    rwa [ht, hp]
  rw [← appLE_subschemeι_eq_zero_iff Z hZs hpU hle]
  have h1 : (D.completionToFormalNeighborhood f y hmaps
        (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) (Y.presheaf.germ U y hy s))).1 n =
      (((D ^ (n + 1)).subschemeι ≫ f).appLE U ⊤
        (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y (base_thickening_eq D f y hmaps n) U
          hy)).hom s := by
    change (D.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ _)).1 n = _
    rw [completionToFormalNeighborhood_of]
    exact Scheme.Hom.stalkToΓ_germ _ _ _ _ _ _
  have hcomp : inclusion hZ ≫ (D ^ (n + 1)).subschemeι ≫ f = Z.subschemeι ≫ f := by
    rw [← Category.assoc, inclusion_subschemeι]
  have key : ((D ^ (n + 1)).subschemeι ≫ f).appLE U ⊤
        (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y (base_thickening_eq D f y hmaps n) U
          hy) ≫ (inclusion hZ).appTop =
      f.app U ≫ Z.subschemeι.appLE (f ⁻¹ᵁ U) ⊤ hle := by
    rw [← Stacks.FormalFunctions.appLE_top_eq_appTop _
      (Stacks.FormalFunctions.top_le_preimage_top _), Scheme.Hom.appLE_comp_appLE,
      Stacks.FormalFunctions.appLE_congr_hom hcomp, Scheme.Hom.comp_appLE]
    all_goals first | rfl | exact hle
  rw [h1, ← CommRingCat.comp_apply, key]
  rfl

/-- An element of the `I`-adic completion whose image in `R ⧸ I ^ k` vanishes lies in the `k`-th
power of the extended ideal, for `I` finitely generated. -/
private theorem mem_map_pow_of_evalₐ_eq_zero {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    {k : ℕ} {x : AdicCompletion I R} (hx : AdicCompletion.evalₐ I k x = 0) :
    x ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ k := by
  have h0 : AdicCompletion.eval I R k x = 0 := by
    have h' := hx
    simp only [AdicCompletion.evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply] at h'
    exact (map_eq_zero_iff _ (AlgEquiv.injective _)).mp h'
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hI] at h0
  rw [← Ideal.map_pow]
  exact Submodule.smul_induction_on h0
    (fun r hr z _ => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr))
    (fun z z' hz hz' => Ideal.add_mem _ hz hz')

/-- A ring map out of the completion of a Noetherian local ring is determined by its values on
the ring, provided it agrees there with a map killing the kernel of `R̂ → R ⧸ 𝔪 ^ (n + 1)`. -/
private theorem ringHom_eq_of_algebraMap_eq {R S : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing S]
    (ψ χ : AdicCompletion (maximalIdeal R) R →+* S) (n : ℕ)
    (hχ : ∀ x, AdicCompletion.evalₐ (maximalIdeal R) (n + 1) x = 0 → χ x = 0)
    (h : ∀ r, ψ (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      χ (algebraMap R (AdicCompletion (maximalIdeal R) R) r))
    (t : AdicCompletion (maximalIdeal R) R) : ψ t = χ t := by
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hker : ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ^
      (n + 1) ≤ RingHom.ker ψ := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, h]
    apply hχ
    change AdicCompletion.evalₐ _ _ (AdicCompletion.of _ _ x) = 0
    rw [AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal R) (n + 1) t)
  have hev : AdicCompletion.evalₐ (maximalIdeal R) (n + 1)
      (t - algebraMap R (AdicCompletion (maximalIdeal R) R) g) = 0 := by
    rw [map_sub, show algebraMap R (AdicCompletion (maximalIdeal R) R) g =
      AdicCompletion.of _ _ g from rfl, AdicCompletion.evalₐ_of, hg, sub_self]
  have h2 : ψ (t - algebraMap R _ g) = 0 := hker (mem_map_pow_of_evalₐ_eq_zero hfg hev)
  have h3 : χ (t - algebraMap R _ g) = 0 := hχ _ hev
  rw [map_sub, sub_eq_zero] at h2 h3
  rw [h2, h3, h]

/-- **Krull's intersection theorem**, for an ideal of a Noetherian local ring: an element lying
in `I + 𝔪 ^ N` for every `N` lies in `I`. -/
private theorem mem_of_forall_mem_sup_maximalIdeal_pow {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (I : Ideal A) {t : A}
    (h : ∀ N : ℕ, t ∈ I ⊔ maximalIdeal A ^ N) : t ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A)
    (maximalIdeal.isMaximal A).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot A, ← hbot]
  refine Submodule.mem_iInf _ |>.mpr fun N => ?_
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp (h N)
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add,
    ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem_smul hm Submodule.mem_top

open Scheme.IdealSheafData in
/-- **The completed boundary ideal, read on markings.** Let `f : X ⟶ Y` carry the reduced curve
`D` to `y`, and let `Z a n` be markings supported at points `p a` over `y`, with
`D ^ (n + 1) ≤ Z a n`. If the germs of `J` pull back into the markings, and conversely a germ
pulling back into the markings of high level lies in `J + 𝔪 ^ N`, then an element of `𝒪̂_{Y,y}`
lies in `J 𝒪̂_{Y,y}` exactly when its formal function vanishes on all the markings. -/
private theorem mem_map_iff_forall_appTop_inclusion_eq_zero
    {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) {ι : Type*} (p : ι → X)
    (hp : ∀ a, f.base (p a) = y) (Z : ι → ℕ → X.IdealSheafData)
    (hZs : ∀ a n, ((Z a n).support : Set X) = {p a}) (hZ : ∀ a n, D ^ (n + 1) ≤ Z a n)
    (J : Ideal (Y.presheaf.stalk y))
    (h1 : ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)), Y.presheaf.germ U y hy s ∈ J →
      ∀ a n, X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f.base (p a) ∈ U from (hp a) ▸ hy)
        (f.app U s) ∈ IdealSheafData.stalk (Z a n) (p a))
    (h3 : ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
      (∀ a, X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f.base (p a) ∈ U from (hp a) ▸ hy)
        (f.app U s) ∈ IdealSheafData.stalk (Z a n) (p a)) →
      Y.presheaf.germ U y hy s ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N)
    (t : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    t ∈ Ideal.map (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))) J ↔
      ∀ a n, (inclusion (hZ a n)).appTop.hom
        ((D.completionToFormalNeighborhood f y hmaps t).1 n) = 0 := by
  have hkey := fun a n U hy s =>
    appTop_inclusion_completionToFormalNeighborhood_eq_zero_iff f y D hmaps (hp a) (Z a n)
      (hZs a n) n (hZ a n) U hy s
  let ev : ∀ a n, AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y) →+*
      Γ((Z a n).subscheme, ⊤) := fun a n =>
    (inclusion (hZ a n)).appTop.hom.comp (((Pi.evalRingHom _ n).comp
      (D.formalNeighborhoodRing).subtype).comp (D.completionToFormalNeighborhood f y hmaps))
  have hev : ∀ a n x, ev a n x = (inclusion (hZ a n)).appTop.hom
      ((D.completionToFormalNeighborhood f y hmaps x).1 n) := fun _ _ _ => rfl
  constructor
  · intro ht a n
    have hle : Ideal.map (algebraMap _ (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y))) J ≤
        RingHom.ker (ev a n) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.germ_exist g
      rw [Ideal.mem_comap, RingHom.mem_ker, hev]
      exact (hkey a n U hy s).mpr (h1 U hy s hg a n)
    have := hle ht
    rwa [RingHom.mem_ker, hev] at this
  · intro ht
    have : IsNoetherianRing
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :=
      AdicCompletion.isNoetherianRing _
    refine mem_of_forall_mem_sup_maximalIdeal_pow _ fun N => ?_
    have hfg : (maximalIdeal (Y.presheaf.stalk y)).FG := IsNoetherian.noetherian _
    obtain ⟨n₀, hn₀⟩ := h3 N
    set n := max n₀ N
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t)
    obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.germ_exist g
    have hevₐ : AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
        (algebraMap _ (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y))
          (Y.presheaf.germ U y hy s)) =
        AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t := by
      rw [← hg]; exact AdicCompletion.evalₐ_of _ _ _
    have hcomp : ∀ x x' : AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y),
        AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) x =
          AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) x' →
        (D.completionToFormalNeighborhood f y hmaps x).1 n =
          (D.completionToFormalNeighborhood f y hmaps x').1 n := by
      intro x x' h
      change (thickeningToStalkQuotient D f y hmaps n).hom
          (AdicCompletion.evalₐ _ (n + 1) x) =
        (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) x')
      rw [h]
    have hgerm := hn₀ n (le_max_left _ _) U hy s fun a =>
      (hkey a n U hy s).mp (by rw [hcomp _ _ hevₐ]; exact ht a n)
    have h2 : algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
        (Y.presheaf.germ U y hy s) ∈
        Ideal.map (algebraMap _ (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y))) J ⊔
          maximalIdeal (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y)) ^ N := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Ideal.map_sup]
      exact Ideal.mem_map_of_mem _ hgerm
    have h3' : t - algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
        (Y.presheaf.germ U y hy s) ∈
        maximalIdeal (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y)) ^ N := by
      have h0 : AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
          (t - algebraMap _ (AdicCompletion (maximalIdeal _) (Y.presheaf.stalk y))
            (Y.presheaf.germ U y hy s)) = 0 := by
        rw [map_sub, hevₐ, sub_self]
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.pow_le_pow_right (by omega) (mem_map_pow_of_evalₐ_eq_zero hfg h0)
    simpa using Submodule.add_mem _ h2 (Ideal.mem_sup_right h3')

end BoundaryIdeal

/-! ### Finite curves over the point -/

section FiniteBoundary

/-- A section lies in the prime of a point of an affine open exactly when its germ there is not a
unit. -/
private theorem mem_primeIdealOf_iff {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (r : Γ(X, U)) :
    r ∈ (hU.primeIdealOf x).asIdeal ↔ (X.presheaf.germ U x x.2).hom r ∈ maximalIdeal _ := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk x)
    (hU.primeIdealOf x).asIdeal]
  rfl

private theorem primeIdealOf_injective {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun x x' h => Subtype.ext (by
  rw [← hU.fromSpec_primeIdealOf x, ← hU.fromSpec_primeIdealOf x', h])

private theorem exists_primeIdealOf_eq {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = P := by
  have hx : hU.fromSpec P ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨P, rfl⟩
  refine ⟨⟨_, hx⟩, hU.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hU.fromSpec_primeIdealOf]

/-- A local homomorphism reflects the maximal ideal. -/
private theorem map_mem_maximalIdeal_iff {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] (a : A) :
    ψ a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A :=
  map_mem_nonunits_iff ψ a

/-- The prime of a point of the preimage of an affine open pulls back to the prime of its
image. -/
private theorem comap_app_primeIdealOf {X Y : Scheme.{v}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U)) (x : g ⁻¹ᵁ U) (hx : g x.1 ∈ U) :
    (hV.primeIdealOf x).asIdeal.comap (g.app U).hom = (hU.primeIdealOf ⟨g x.1, hx⟩).asIdeal := by
  ext r
  rw [Ideal.mem_comap, mem_primeIdealOf_iff, mem_primeIdealOf_iff,
    ← map_mem_maximalIdeal_iff (g.stalkMap x.1).hom ((Y.presheaf.germ U (g x.1) hx).hom r),
    Scheme.Hom.germ_stalkMap_apply]

/-- A function on the base whose pullback lies in `(h, w ^ (n + 1))` at a point of a closed
subscheme `Z` containing `h` lies in the `(n + 1)`-st power of the prime of that point on an affine
open of `Z`. -/
private theorem app_mem_primeIdealOf_pow {X Y : Scheme.{v}} (f : X ⟶ Y) (Z : X.IdealSheafData)
    {U : Y.Opens} (hV : IsAffineOpen ((Z.subschemeι ≫ f) ⁻¹ᵁ U))
    (t : (Z.subschemeι ≫ f) ⁻¹ᵁ U) {q : X} (hq : Z.subschemeι t.1 = q)
    (hmax : (hV.primeIdealOf t).asIdeal.IsMaximal)
    {h w : X.presheaf.stalk q} (hh : h ∈ IdealSheafData.stalk Z q) (hw : w ∈ maximalIdeal _)
    (n : ℕ) (r : Γ(Y, U)) (hfq : f q ∈ U)
    (hr : (f.stalkMap q).hom ((Y.presheaf.germ U (f q) hfq).hom r) ∈
      Ideal.span {h, w ^ (n + 1)}) :
    ((Z.subschemeι ≫ f).app U).hom r ∈ (hV.primeIdealOf t).asIdeal ^ (n + 1) := by
  subst hq
  set 𝔫 := (hV.primeIdealOf t).asIdeal
  letI := Z.subscheme.presheaf.algebra_section_stalk t
  haveI := hV.isLocalization_stalk t
  have hprim : (𝔫 ^ (n + 1)).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by
    rw [Ideal.radical_pow _ (Nat.succ_ne_zero n), hmax.isPrime.radical]; exact hmax)
  have hdisj : Disjoint (𝔫.primeCompl : Set Γ(Z.subscheme, (Z.subschemeι ≫ f) ⁻¹ᵁ U))
      ((𝔫 ^ (n + 1) : Ideal _) : Set Γ(Z.subscheme, (Z.subschemeι ≫ f) ⁻¹ᵁ U)) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hx')
  rw [← IsLocalization.comap_map_of_isPrimary_disjoint 𝔫.primeCompl
    (Z.subscheme.presheaf.stalk t) hprim hdisj, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.under, Ideal.mem_comap]
  change (Z.subscheme.presheaf.germ _ t t.2).hom (((Z.subschemeι ≫ f).app U).hom r) ∈
    maximalIdeal (Z.subscheme.presheaf.stalk t) ^ (n + 1)
  rw [← Scheme.Hom.germ_stalkMap_apply (Z.subschemeι ≫ f) U t.1 t.2 r, Scheme.Hom.stalkMap_comp]
  change (Z.subschemeι.stalkMap t.1).hom ((f.stalkMap (Z.subschemeι t.1)).hom
    ((Y.presheaf.germ U (f (Z.subschemeι t.1)) hfq).hom r)) ∈
      maximalIdeal (Z.subscheme.presheaf.stalk t) ^ (n + 1)
  have hπh : (Z.subschemeι.stalkMap t).hom h = 0 := by
    rwa [← RingHom.mem_ker, Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
  have hπw : (Z.subschemeι.stalkMap t).hom w ∈ maximalIdeal _ :=
    (map_mem_maximalIdeal_iff _ _).mpr hw
  have := Ideal.mem_map_of_mem (Z.subschemeι.stalkMap t).hom hr
  rw [Ideal.map_span, Set.image_pair, hπh, map_pow] at this
  refine Ideal.span_le.mpr ?_ this
  rintro _ (rfl | rfl)
  · exact zero_mem _
  · exact Ideal.pow_mem_pow hπw _

/-- **Artin–Rees for a finite extension with finitely many points over a maximal ideal.** Let
`φ : R → B` be finite, `R` Noetherian and `𝔮 ⊂ R` maximal, and let `𝔫_a` be the distinct primes of
`B` lying over `𝔮`. If `φ r` lies in `𝔫_a ^ (n + 1)` for every `a`, with `n` large, then `φ r` is
the image of an element of `𝔮 ^ N`. -/
private theorem exists_mem_pow_eq_of_forall_mem_pow {R B : Type*} [CommRing R] [CommRing B]
    [IsNoetherianRing R] (φ : R →+* B) (hφ : φ.Finite) (𝔮 : Ideal R) [h𝔮 : 𝔮.IsMaximal]
    {ι : Type*} [Fintype ι] (𝔫 : ι → Ideal B) [h𝔫p : ∀ a, (𝔫 a).IsPrime]
    (h𝔫 : ∀ a, (𝔫 a).comap φ = 𝔮) (hinj : Function.Injective 𝔫)
    (hall : ∀ P : Ideal B, P.IsPrime → P.comap φ = 𝔮 → ∃ a, 𝔫 a = P) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ r : R, (∀ a, φ r ∈ 𝔫 a ^ (n + 1)) →
      ∃ r' ∈ 𝔮 ^ N, φ r = φ r' := by
  classical
  letI := φ.toAlgebra
  have : Module.Finite R B := hφ
  have : IsNoetherianRing B := isNoetherian_of_tower R inferInstance
  have hmax : ∀ a, (𝔫 a).IsMaximal := fun a =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ (by
      change (Ideal.comap φ (𝔫 a)).IsMaximal; rw [h𝔫 a]; exact h𝔮)
  have hrad : (⨅ a, 𝔫 a) ≤ (𝔮.map φ).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hP, hPp⟩ => ?_
    have hc : P.comap φ = 𝔮 := by
      have h1 : 𝔮 ≤ P.comap φ := Ideal.map_le_iff_le_comap.mp hP
      exact (h𝔮.eq_of_le (Ideal.comap_ne_top φ hPp.ne_top) h1).symm
    obtain ⟨a, rfl⟩ := hall P hPp hc
    exact iInf_le _ a
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔮 (R ∙ (1 : B))
  refine ⟨e * (N + k₀), fun n hn r hr => ?_⟩
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun IsCoprime
      fun a => 𝔫 a ^ (n + 1)) := fun a _ b _ hab =>
    (Ideal.isCoprime_iff_sup_eq.mpr ((hmax a).coprime_of_ne (hmax b) (hinj.ne hab))).pow
  have h1 : φ r ∈ ∏ a ∈ Finset.univ, 𝔫 a ^ (n + 1) := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
    simp only [Finset.mem_univ, iInf_pos]
    exact Ideal.mem_iInf.mpr hr
  have h2 : (∏ a ∈ Finset.univ, 𝔫 a ^ (n + 1)) ≤ (𝔮 ^ (N + k₀)).map φ := by
    rw [Finset.prod_pow, Ideal.map_pow]
    calc (∏ a ∈ Finset.univ, 𝔫 a) ^ (n + 1) ≤ (⨅ a, 𝔫 a) ^ (n + 1) :=
          Ideal.pow_right_mono (le_iInf fun a =>
            Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ a))) _
      _ ≤ (⨅ a, 𝔫 a) ^ (e * (N + k₀)) := Ideal.pow_le_pow_right (by omega)
      _ = ((⨅ a, 𝔫 a) ^ e) ^ (N + k₀) := pow_mul _ _ _
      _ ≤ (𝔮.map φ) ^ (N + k₀) := Ideal.pow_right_mono he _
  have h3 : φ r ∈ (𝔮 ^ (N + k₀) • ⊤ : Submodule R B) ⊓ (R ∙ (1 : B)) := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.smul_top_eq_map]; exact h2 h1
    · exact Submodule.mem_span_singleton.mpr ⟨r, by rw [Algebra.smul_def, mul_one]; rfl⟩
  rw [hk₀ (N + k₀) (by omega), Nat.add_sub_cancel] at h3
  have h4 : φ r ∈ 𝔮 ^ N • (R ∙ (1 : B)) := Submodule.smul_mono le_rfl inf_le_right h3
  obtain ⟨r', hr', hrr'⟩ := Submodule.mem_smul_span_singleton.mp h4
  refine ⟨r', hr', ?_⟩
  rw [← hrr', Algebra.smul_def, mul_one]
  rfl

/-- **Germs vanishing to high order on a finite curve.** Let `f : X ⟶ Y` carry a closed
subscheme `Z` finitely to `Y`, with points `p a` exactly the points of `Z` over the closed point
`y`. Suppose `h a` lies in the ideal of `Z` at `p a` and `w a ∈ 𝔪_{p a}`, and that a function on
an affine neighbourhood of `y` vanishing on `Z` has germ in `J`. If the germ of `s` at `y` pulls
back into `(h a, w a ^ (n + 1))` at every `p a`, for `n` large, then it lies in `J + 𝔪 ^ N`. -/
private theorem mem_sup_pow_of_forall_mem_span {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y)
    (hycl : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] (Z : X.IdealSheafData)
    [IsFinite (Z.subschemeι ≫ f)] {ι : Type*} [Fintype ι] (p : ι → X)
    (hpinj : Function.Injective p) (hpy : ∀ a, f (p a) = y) (hpZ : ∀ a, p a ∈ Z.support)
    (hall : ∀ z ∈ Z.support, f z = y → ∃ a, p a = z) (h w : ∀ a, X.presheaf.stalk (p a))
    (hh : ∀ a, h a ∈ IdealSheafData.stalk Z (p a)) (hw : ∀ a, w a ∈ maximalIdeal _)
    (J : Ideal (Y.presheaf.stalk y))
    (hker : ∀ (U : Y.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ r : Γ(Y, U),
      ((Z.subschemeι ≫ f).app U).hom r = 0 → (Y.presheaf.germ U y hy).hom r ∈ J) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
      (∀ a, (X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f (p a) ∈ U from (hpy a) ▸ hy)).hom
        ((f.app U).hom s) ∈ Ideal.span {h a, w a ^ (n + 1)}) →
      (Y.presheaf.germ U y hy).hom s ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N := by
  classical
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  set g := Z.subschemeι ≫ f with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U₀) := hU₀.preimage g
  have hφ : (g.app U₀).hom.Finite := IsFinite.finite_app g U₀ hU₀
  have : IsNoetherianRing Γ(Y, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  set 𝔮 := (hU₀.primeIdealOf ⟨y, hyU₀⟩).asIdeal with h𝔮def
  have h𝔮 : 𝔮.IsMaximal := hU₀.primeIdealOf_isMaximal_of_isClosed ⟨y, hyU₀⟩ hycl
  have ht : ∀ a, ∃ t : g ⁻¹ᵁ U₀, Z.subschemeι t.1 = p a := fun a => by
    obtain ⟨t, ht⟩ : p a ∈ Set.range Z.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hpZ a
    exact ⟨⟨t, show f (Z.subschemeι t) ∈ U₀ by rw [ht, hpy a]; exact hyU₀⟩, ht⟩
  choose t ht using ht
  have hgt : ∀ a, g (t a).1 = y := fun a => by
    change f (Z.subschemeι (t a).1) = y; rw [ht a, hpy a]
  have hcomap : ∀ x : g ⁻¹ᵁ U₀, g x.1 = y →
      (hV.primeIdealOf x).asIdeal.comap (g.app U₀).hom = 𝔮 := fun x hx => by
    rw [comap_app_primeIdealOf g hU₀ hV x (hx ▸ hyU₀)]
    exact congrArg (fun z => (hU₀.primeIdealOf z).asIdeal) (Subtype.ext hx)
  have hιinj : Function.Injective Z.subschemeι := Z.subschemeι.isClosedEmbedding.injective
  have hinj : Function.Injective fun a => (hV.primeIdealOf (t a)).asIdeal := by
    intro a b hab
    have h1 := primeIdealOf_injective hV (PrimeSpectrum.ext hab)
    apply hpinj
    rw [← ht a, ← ht b, h1]
  have hmax : ∀ a, (hV.primeIdealOf (t a)).asIdeal.IsMaximal := by
    intro a
    letI := (g.app U₀).hom.toAlgebra
    haveI : Module.Finite Γ(Y, U₀) Γ(Z.subscheme, g ⁻¹ᵁ U₀) := hφ
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ (by
      change (Ideal.comap (g.app U₀).hom _).IsMaximal
      rw [hcomap _ (hgt a)]; exact h𝔮)
  have hallP : ∀ P : Ideal Γ(Z.subscheme, g ⁻¹ᵁ U₀), P.IsPrime → P.comap (g.app U₀).hom = 𝔮 →
      ∃ a, (hV.primeIdealOf (t a)).asIdeal = P := by
    intro P hP hPc
    obtain ⟨x, hx⟩ := exists_primeIdealOf_eq hV ⟨P, hP⟩
    have hgx : g x.1 = y := by
      have h1 := comap_app_primeIdealOf g hU₀ hV x x.2
      rw [hx] at h1
      change P.comap _ = _ at h1
      rw [hPc] at h1
      exact congrArg Subtype.val (primeIdealOf_injective hU₀ (PrimeSpectrum.ext h1)).symm
    obtain ⟨a, ha⟩ := hall (Z.subschemeι x.1) (show Z.subschemeι x.1 ∈ (Z.support : Set X) by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x.1, rfl⟩) hgx
    refine ⟨a, ?_⟩
    have : t a = x := Subtype.ext (hιinj ((ht a).trans ha))
    rw [this, hx]
  obtain ⟨n₀, hn₀⟩ := exists_mem_pow_eq_of_forall_mem_pow (g.app U₀).hom hφ 𝔮
    (fun a => (hV.primeIdealOf (t a)).asIdeal) (fun a => hcomap _ (hgt a)) hinj hallP N
  refine ⟨n₀, fun n hn U hy s hs => ?_⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hyU₀⟩ : U₀)
  haveI := hU₀.isLocalization_stalk ⟨y, hyU₀⟩
  obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl
    ((Y.presheaf.germ U y hy).hom s)
  have hrd' : (Y.presheaf.germ U y hy).hom s * (Y.presheaf.germ U₀ y hyU₀).hom d =
      (Y.presheaf.germ U₀ y hyU₀).hom r := by
    rw [← hrd]; exact IsLocalization.mk'_spec _ r d
  -- the conditions at the points `p a`
  have hθ : ∀ a, (g.app U₀).hom r ∈ (hV.primeIdealOf (t a)).asIdeal ^ (n + 1) := by
    intro a
    have hsp : f (p a) ⤳ y := hpy a ▸ specializes_rfl
    refine app_mem_primeIdealOf_pow f Z hV (t a) (ht a) (hmax a) (hh a) (hw a) n r
      ((hpy a).symm ▸ hyU₀) ?_
    have e : ∀ (V : Y.Opens) (hV : y ∈ V) (σ : Γ(Y, V)),
        (Y.presheaf.germ V (f (p a)) (hsp.mem_open V.isOpen hV)).hom σ =
          (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V y hV).hom σ) :=
      fun V hV σ => (TopCat.Presheaf.germ_stalkSpecializes_apply _ hV hsp σ).symm
    rw [e U₀ hyU₀, ← hrd', map_mul, map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← e U hy, Scheme.Hom.germ_stalkMap_apply]
    exact hs a
  obtain ⟨r', hr', hrr'⟩ := hn₀ n hn r hθ
  have h0 : ((Z.subschemeι ≫ f).app U₀).hom (r - r') = 0 := by
    rw [map_sub, hrr', sub_self]
  have hJ := hker U₀ hyU₀ hU₀ (r - r') h0
  have hm : (Y.presheaf.germ U₀ y hyU₀).hom r' ∈ maximalIdeal (Y.presheaf.stalk y) ^ N := by
    have hle : Ideal.map (Y.presheaf.germ U₀ y hyU₀).hom 𝔮 ≤ maximalIdeal _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (mem_primeIdealOf_iff hU₀ ⟨y, hyU₀⟩ z).mp hz
    have := Ideal.mem_map_of_mem (Y.presheaf.germ U₀ y hyU₀).hom hr'
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle N this
  have hr : (Y.presheaf.germ U₀ y hyU₀).hom r ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N := by
    have := Ideal.add_mem _ (Ideal.mem_sup_left hJ) (Ideal.mem_sup_right hm)
    rwa [map_sub, sub_add_cancel] at this
  have hu : IsUnit ((Y.presheaf.germ U₀ y hyU₀).hom (d : Γ(Y, U₀))) :=
    IsLocalization.map_units (Y.presheaf.stalk y) d
  obtain ⟨u, hu⟩ := hu
  have : (Y.presheaf.germ U y hy).hom s =
      (Y.presheaf.germ U₀ y hyU₀).hom r * ↑u⁻¹ := by
    rw [← hrd', ← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hr

/-- **Curvilinear markings transverse to a curve.** At a closed point `p` of a surface over an
algebraically closed field `K`, with `𝔪_p = (h, w)` and `w` a local equation of the ideal sheaf
`I` at `p`, there are ideal sheaves `Zₙ` supported at `p`, with stalk `(h, w ^ (n + 1))` there,
containing `I ^ (n + 1)` and compatible with the thickenings, each `Zₙ ≅ Spec K[X]/(X ^ (n + 1))`
over `K`. -/
private theorem exists_marking_of_span_eq {K : Type v} [Field K] [IsAlgClosed K]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X]
    (p : X) (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (I : X.IdealSheafData) {h w : X.presheaf.stalk p}
    (hI : IdealSheafData.stalk I p = Ideal.span {w})
    (hhw : Ideal.span {h, w} = maximalIdeal (X.presheaf.stalk p)) :
    ∃ (Z : ℕ → X.IdealSheafData) (hZ : ∀ n, I ^ (n + 1) ≤ Z n),
      (∀ n, Z n = Z (n + 1) ⊔ I ^ (n + 1)) ∧ (∀ n, ((Z n).support : Set X) = {p}) ∧
      (∀ n, ∃ e : (Z n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (Z n).subschemeι ≫ sX) ∧
      ∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)} := by
  letI := Mori.stalkAlgebra sX p
  set c := algebraMap (X.presheaf.stalk p)
    (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) with hc
  have hz : Ideal.span (Set.range ![c h, c w]) =
      maximalIdeal (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) := by
    have h1 : Ideal.map c (Ideal.span {h, w}) = Ideal.span (Set.range ![c h, c w]) := by
      rw [Ideal.map_span, Set.image_pair]
      congr 1
      ext g
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [AdicCompletion.maximalIdeal_eq_map, ← h1]
    exact congrArg (Ideal.map c) hhw
  obtain ⟨Φ, hΦc, hΦX⟩ := exists_ringEquiv_mvPowerSeries_of_span_eq sX p hp (n := 2)
    (by rw [hdim]; rfl) hz
  have hres : ∀ g : X.presheaf.stalk p, ∃ c' : K, g - ((Scheme.ΓSpecIso (.of K)).inv ≫
      sX.appTop ≫ X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c' ∈
        maximalIdeal (X.presheaf.stalk p) := by
    intro g
    obtain ⟨c', hc'⟩ := MMP.Mori.SurfaceAux.residue_surjective sX p hp (Ideal.Quotient.mk _ g)
    refine ⟨c', Ideal.Quotient.eq.mp ?_⟩
    rw [← hc', IsScalarTower.algebraMap_apply K (X.presheaf.stalk p)
      (X.presheaf.stalk p ⧸ maximalIdeal (X.presheaf.stalk p)), Ideal.Quotient.algebraMap_eq]
    rfl
  obtain ⟨Z, hZs, hZp, hZx, hZe⟩ := exists_marking sX p hp hhw hres (Φ.symm.toRingHom.comp c)
    (fun c' => (RingEquiv.symm_apply_eq Φ).mpr (hΦc c').symm)
    ((RingEquiv.symm_apply_eq Φ).mpr (by rw [hΦX]; rfl))
    ((RingEquiv.symm_apply_eq Φ).mpr (by rw [hΦX]; rfl))
  obtain ⟨hle, hsucc⟩ := marking_le_and_eq_sup I hI Z hZp hZx
  exact ⟨Z, hle, hsucc, hZs, hZe, hZp⟩

end FiniteBoundary

/-! ### Boundary curves and their germs -/

section BoundaryCurves

/-- A germ at a point of a prime divisor lies in the ideal of the divisor exactly when its image at
the generic point of the divisor is not a unit. -/
private theorem germ_mem_stalk_iff {X : Scheme.{v}} (D : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ D.support) {U : X.Opens} (hU : x ∈ U) (s : Γ(X, U)) :
    (X.presheaf.germ U x hU).hom s ∈ IdealSheafData.stalk D.idealSheaf x ↔
      (X.presheaf.germ U D.genericPoint
        ((show D.genericPoint ⤳ x by
          rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact hx).mem_open U.isOpen hU)).hom s ∈
        maximalIdeal (X.presheaf.stalk D.genericPoint) := by
  have hη : D.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  obtain ⟨q, hq, hqE, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support D hx
  have hsp : X.fromSpecStalk x q ⤳ x := MMP.Resolution.specializes_fromSpecStalk x q
  have h1 : IdealSheafData.stalk D.idealSheaf x = MMP.Intersection.primeOfSpecializes hη := by
    rw [hqE, ← MMP.Resolution.primeOfSpecializes_fromSpecStalk x q hsp,
      MMP.Resolution.primeOfSpecializes_congr hq hsp hη]
  rw [h1]
  change (X.presheaf.stalkSpecializes hη).hom ((X.presheaf.germ U x hU).hom s) ∈
    maximalIdeal (X.presheaf.stalk D.genericPoint) ↔ _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The germ of a pullback `f^♯ s` at `ξ` is a unit exactly when the germ of `s` at `f ξ` is. -/
private theorem germ_app_mem_maximalIdeal_iff {X Y : Scheme.{v}} (f : X ⟶ Y) {ξ : X} {η : Y}
    (hξ : f ξ = η) {U : Y.Opens} (hU : η ∈ U) (s : Γ(Y, U)) :
    (X.presheaf.germ (f ⁻¹ᵁ U) ξ (show f ξ ∈ U from hξ ▸ hU)).hom ((f.app U).hom s) ∈
        maximalIdeal (X.presheaf.stalk ξ) ↔
      (Y.presheaf.germ U η hU).hom s ∈ maximalIdeal (Y.presheaf.stalk η) := by
  subst hξ
  rw [← Scheme.Hom.germ_stalkMap_apply]
  exact map_mem_maximalIdeal_iff (f.stalkMap ξ).hom _

/-- The local intersection number is symmetric. -/
private theorem localIntersectionNumber_comm {K : Type v} [Field K] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of K)) (q : X) (C C' : Mori.Divisor X) :
    localIntersectionNumber sX q C C' = localIntersectionNumber sX q C' C := by
  simp only [localIntersectionNumber]
  rw [sup_comm]

/-- Prime divisors with local intersection number one at `q` have ideals generating `𝔪_q`. -/
private theorem stalk_sup_eq_maximalIdeal_of_localIntersectionNumber_eq_one {K : Type v}
    [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K)) (q : X) (C C' : Mori.PrimeDivisor X)
    (h1 : localIntersectionNumber sX q (Finsupp.single C 1) (Finsupp.single C' 1) = 1) :
    IdealSheafData.stalk C.idealSheaf q ⊔ IdealSheafData.stalk C'.idealSheaf q =
      maximalIdeal (X.presheaf.stalk q) := by
  letI := Mori.stalkAlgebra sX q
  have hloc : ∀ E : Mori.PrimeDivisor X,
      localIdeal q (Finsupp.single E 1) = IdealSheafData.stalk E.idealSheaf q := fun E => by
    rw [localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, Int.toNat_one, pow_one]
  rw [localIntersectionNumber, hloc, hloc] at h1
  set J := IdealSheafData.stalk C.idealSheaf q ⊔ IdealSheafData.stalk C'.idealSheaf q
  have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K)
    (E := X.presheaf.stalk q ⧸ J)).mp h1
  exact IsLocalRing.eq_maximalIdeal <| Ideal.Quotient.maximal_of_isField J
    ((RingEquiv.ofBijective _ hb).symm.toMulEquiv.isField (Field.toIsField K))

/-- A prime divisor with nonzero coefficient in the birational transform of `B` is the transform
of a component of `B`. -/
private theorem exists_mem_support_of_inverseTransformDivisor_ne_zero {X Y : Scheme.{v}}
    (f : X ⟶ Y) (B : QDivisor Y) {D : Mori.PrimeDivisor X}
    (hD : inverseTransformDivisor f B D ≠ 0) :
    ∃ C ∈ B.support, inverseTransformPrimeDivisor f C = some D := by
  classical
  by_contra! h
  apply hD
  conv_lhs => rw [← Finsupp.sum_single B]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [inverseTransformDivisor_single]
  rcases hφ : inverseTransformPrimeDivisor f C with _ | D'
  · rfl
  · have : D' ≠ D := fun he => h C hC (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' this

/-- **A normal curve through a regular point is cut out by a parameter.** At a point `p` of a
prime divisor `E` with normal subscheme, on a scheme whose local ring at `p` is regular of
dimension two, a local equation `w` of `E` is part of a system of generators `h, w` of `𝔪_p`. -/
private theorem exists_span_pair_eq_maximalIdeal {X : Scheme.{v}} [IsLocallyNoetherian X]
    (E : Mori.PrimeDivisor X) [IsNormal E.idealSheaf.subscheme] {p : X} (hp : p ∈ E.support)
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    {w : X.presheaf.stalk p} (hw : IdealSheafData.stalk E.idealSheaf p = Ideal.span {w})
    (h0 : IdealSheafData.stalk E.idealSheaf p ≠ ⊥)
    (hm : IdealSheafData.stalk E.idealSheaf p ≠ maximalIdeal (X.presheaf.stalk p)) :
    ∃ h : X.presheaf.stalk p, Ideal.span {h, w} = maximalIdeal (X.presheaf.stalk p) := by
  have hPw : (Ideal.span {w}).IsPrime := hw ▸ isPrime_stalk_idealSheaf E hp
  obtain ⟨t, rfl⟩ : p ∈ Set.range E.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hp
  set π := (E.idealSheaf.subschemeι.stalkMap t).hom with hπ
  have hsurj : Function.Surjective π := E.idealSheaf.subschemeι.stalkMap_surjective t
  have hker : RingHom.ker π = Ideal.span {w} := by
    rw [hπ, Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, hw]
  have : IsDomain (X.presheaf.stalk (E.idealSheaf.subschemeι t)) :=
    IsRegularLocalRing.isDomain _
  have : IsNoetherianRing (E.idealSheaf.subscheme.presheaf.stalk t) :=
    isNoetherianRing_of_surjective _ _ π hsurj
  have hwm : Ideal.span {w} ≤ maximalIdeal _ := le_maximalIdeal hPw.ne_top
  obtain ⟨a, ha, haw⟩ : ∃ a ∈ maximalIdeal (X.presheaf.stalk (E.idealSheaf.subschemeι t)),
      a ∉ Ideal.span {w} := by
    by_contra! h
    exact hm (hw.trans (le_antisymm hwm h))
  have hπa : π a ≠ 0 := fun h => haw (hker ▸ RingHom.mem_ker.mpr h)
  have hπm : ∀ m, π m ∈ maximalIdeal (E.idealSheaf.subscheme.presheaf.stalk t) ↔
      m ∈ maximalIdeal _ := fun m => map_mem_maximalIdeal_iff π m
  have hnf : ¬ IsField (E.idealSheaf.subscheme.presheaf.stalk t) := by
    intro hF
    letI := hF.toField
    exact (IsLocalRing.mem_maximalIdeal _).mp ((hπm a).mpr ha) (isUnit_iff_ne_zero.mpr hπa)
  have hm2 := height_maximalIdeal_eq_two hdim
  have hbot : (⊥ : Ideal (X.presheaf.stalk (E.idealSheaf.subschemeι t))).IsPrime :=
    Ideal.isPrime_bot
  have huniq : ∀ P : Ideal (E.idealSheaf.subscheme.presheaf.stalk t), P ≠ ⊥ → P.IsPrime →
      P = maximalIdeal _ := by
    intro P hP0 hPp
    have hQp : (P.comap π).IsPrime := Ideal.IsPrime.comap π
    have hwQ : Ideal.span {w} ≤ P.comap π := by
      rw [← hker]; exact Ideal.comap_mono bot_le
    have hwQ' : Ideal.span {w} ≠ P.comap π := by
      intro h
      apply hP0
      rw [← Ideal.map_comap_of_surjective π hsurj P, ← h, ← hker]
      refine eq_bot_iff.mpr (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
      rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact (⊥ : Ideal _).zero_mem
    have hQm : P.comap π = maximalIdeal _ := by
      by_contra hQm
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr (hw ▸ h0))
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hwQ hwQ')
      have e3 := Ideal.height_add_one_le_of_lt_of_isPrime
        (lt_of_le_of_ne (le_maximalIdeal hQp.ne_top) hQm)
      rw [hm2] at e3
      have e1' : (1 : ℕ∞) ≤ (Ideal.span {w}).height := le_trans le_add_self e1
      have e4 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
        (add_le_add ((add_le_add e1' le_rfl).trans e2) le_rfl).trans e3
      exact absurd e4 (by decide)
    refine le_antisymm (le_maximalIdeal hPp.ne_top) fun b hb => ?_
    obtain ⟨m, rfl⟩ := hsurj b
    exact show m ∈ P.comap π from hQm ▸ (hπm m).mp hb
  have hP3 : IsIntegrallyClosed (E.idealSheaf.subscheme.presheaf.stalk t) ∧
      ∃! P : Ideal (E.idealSheaf.subscheme.presheaf.stalk t), P ≠ ⊥ ∧ P.IsPrime :=
    ⟨IsNormal.stalk_normal t, ⟨maximalIdeal _,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩,
      fun P hP => huniq P hP.1 hP.2⟩⟩
  have hdvr := ((IsDiscreteValuationRing.TFAE _ hnf).out 4 5).mp hP3
  obtain ⟨b, hb⟩ := hdvr.principal
  obtain ⟨h, rfl⟩ := hsurj b
  refine ⟨h, le_antisymm ?_ fun m hm' => ?_⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨(hπm h).mp ?_, hwm (Ideal.mem_span_singleton_self w)⟩
    rw [hb]; exact Submodule.mem_span_singleton_self _
  · have h1 : π m ∈ Ideal.span {π h} := by
      have := (hπm m).mpr hm'
      rwa [hb] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨c', rfl⟩ := hsurj c
    have h2 : m - c' * h ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
    rw [hker] at h2
    have h4 : Ideal.span {w} ≤ Ideal.span {h, w} := Ideal.span_mono (Set.subset_insert h {w})
    have h5 : h ∈ Ideal.span {h, w} := Ideal.subset_span (Set.mem_insert h {w})
    have h3 := Ideal.add_mem (Ideal.span {h, w}) (Ideal.mul_mem_left _ c' h5) (h4 h2)
    rwa [add_sub_cancel] at h3

end BoundaryCurves

/-! ### The chain of exceptional curves -/

/-- A curve of arithmetic genus zero over an algebraically closed field is a smooth rational
curve. -/
private theorem isSmoothRationalCurve_of_isArithmeticGenusOf_zero {k : Type v} [Field k]
    [IsAlgClosed k] {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) (C : Mori.PrimeDivisor X)
    (hC : IsCurveIn C.idealSheaf) (h0 : IsArithmeticGenusOf sX C 0) :
    IsSmoothRationalCurve sX C.idealSheaf := by
  obtain ⟨hprop, hcoh, hpa⟩ := h0
  have : IsIntegral C.idealSheaf.subscheme := C.integral
  obtain ⟨-, hiff⟩ := MMP.Mori.arithmeticGenus_nonneg_and_eq_zero_iff
    (C.idealSheaf.subschemeι ≫ sX) hC.2
  obtain ⟨eC, heC⟩ := hiff.mp hpa.symm
  exact ⟨⟨hC, hprop, eC.hom, heC, inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _⟩, eC,
    heC⟩

/-- Two distinct prime divisors on a smooth surface, the first proper, with intersection number
`0` are disjoint. -/
private theorem disjoint_support_of_isIntersectionNumber_zero {k : Type v} [Field k]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (hX : Mori.IsVariety k sX) (hsm : Mori.IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 2) {C D : Mori.PrimeDivisor X} (hCD : C ≠ D)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sX))
    (h0 : IsIntersectionNumber sX (Finsupp.single D 1) C.idealSheaf 0) :
    Disjoint C.support D.support := by
  obtain ⟨hfin, hnum, hpos⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne sX hX hsm hdim hCD hC
  have h := hnum.unique h0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hle := Finset.single_le_sum (f := fun w =>
    (localIntersectionNumber sX w (Finsupp.single C 1) (Finsupp.single D 1) : ℚ))
    (fun w _ => by positivity) (hfin.mem_toFinset.mpr hz)
  rw [h] at hle
  have : (0 : ℚ) < localIntersectionNumber sX z (Finsupp.single C 1) (Finsupp.single D 1) := by
    exact_mod_cast hpos z hz
  linarith

/-- For a resolution of a surface germ with connected fibre over the point and at least one
exceptional curve, the fibre over the point is contained in the union of the exceptional
curves. -/
private theorem preimage_subset_iUnion_support {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g) {n : ℕ} (hn : 1 ≤ n)
    {E : Fin n → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E)
    (hconn : _root_.IsConnected (g.base ⁻¹' {P})) :
    g.base ⁻¹' {P} ⊆ ⋃ j, ((E j).support : Set Y) := by
  classical
  have hYv := hg.isVariety
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨hFcl, -⟩ := hg.isClosed_preimage_and_ne_univ
  set U := ⋃ j, ((E j).support : Set Y) with hU
  have hUcl : IsClosed U := isClosed_iUnion_of_finite fun j => (E j).idealSheaf.support.isClosed
  have hUF : U ⊆ g.base ⁻¹' {P} :=
    Set.iUnion_subset fun j => (hE.isGermExceptionalCurve j).1.prop.2
  intro z hz
  by_contra hzU
  obtain ⟨S, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨g.base ⁻¹' {P}, hFcl⟩
  have hS' : g.base ⁻¹' {P} = ⋃ (K : TopologicalSpace.Closeds Y) (_ : K ∈ S), (K : Set Y) := by
    have := congrArg (fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hS
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
    simpa [Set.iSup_eq_iUnion] using this
  -- a component not inside `U` is a closed point
  have hK : ∀ K ∈ S, ¬ (K : Set Y) ⊆ U → ∃ w, IsClosed ({w} : Set Y) ∧ (K : Set Y) = {w} := by
    intro K hKS hKU
    have hKirr : IsIrreducible (K : Set Y) := hSirr ⟨K, hKS⟩
    have hgen := hKirr.isGenericPoint_genericPoint_closure
    rw [K.isClosed.closure_eq] at hgen
    have hKF : (K : Set Y) ⊆ g.base ⁻¹' {P} := by
      rw [hS']
      exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hKS
    by_cases hcl : IsClosed ({hKirr.genericPoint} : Set Y)
    · exact ⟨_, hcl, hgen.def.symm.trans hcl.closure_eq⟩
    · exfalso
      obtain ⟨j, hj⟩ := exists_mem_support_of_not_isClosed hg hE (hKF hgen.mem) hcl
      apply hKU
      rw [← hgen.def]
      exact hUcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨j, hj⟩))
  -- every point of the fibre off `U` is a closed point forming a component
  have hoff : ∀ w ∈ g.base ⁻¹' {P}, w ∉ U →
      ∃ K ∈ S, (K : Set Y) = {w} ∧ IsClosed ({w} : Set Y) := by
    intro w hw hwU
    rw [hS'] at hw
    obtain ⟨K, hKS, hwK⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨w', hw'cl, hKw'⟩ := hK K hKS fun h => hwU (h hwK)
    rw [hKw', Set.mem_singleton_iff] at hwK
    subst hwK
    exact ⟨K, hKS, hKw', hw'cl⟩
  obtain ⟨-, -, -, hzcl⟩ := hoff z hz hzU
  set W := U ∪ ⋃ K ∈ S.filter (fun K : TopologicalSpace.Closeds Y => z ∉ (K : Set Y)),
    (K : Set Y) with hW
  have hWcl : IsClosed W :=
    hUcl.union (Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun K _ => K.isClosed)
  have hzW : z ∉ W := by
    rintro (h | h)
    · exact hzU h
    · obtain ⟨K, hK', hzK⟩ := Set.mem_iUnion₂.mp h
      exact (Finset.mem_filter.mp hK').2 hzK
  have hFW : ∀ w ∈ g.base ⁻¹' {P}, w ≠ z → w ∈ W := by
    intro w hw hwz
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · obtain ⟨K, hKS, hKw, -⟩ := hoff w hw hwU
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKS, ?_⟩, ?_⟩)
      · rw [hKw]; exact fun h => hwz (Set.mem_singleton_iff.mp h).symm
      · rw [hKw]; rfl
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn.isPreconnected Wᶜ {z}ᶜ
      hWcl.isOpen_compl hzcl.isOpen_compl
      (fun w hw => by
        by_cases hwz : w = z
        · exact Or.inl (hwz ▸ hzW)
        · exact Or.inr hwz)
      (by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and, not_not]
        intro hw hwW
        by_contra hwz
        exact hwW (hFW w hw hwz)) with h | h
  · have hgen : (E ⟨0, hn⟩).genericPoint ∈ U :=
      Set.mem_iUnion.mpr ⟨⟨0, hn⟩, primeDivisor_genericPoint_mem_support _⟩
    exact h (hUF hgen) (Or.inl hgen)
  · exact h hz rfl

/-- The support of a finite product of ideal sheaves is the union of their supports. -/
private theorem coe_support_prod {X : Scheme.{v}} {ι : Type*} (s : Finset ι)
    (F : ι → X.IdealSheafData) :
    ((∏ i ∈ s, F i).support : Set X) = ⋃ i ∈ s, ((F i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, ih, Finset.set_biUnion_insert]

/-- On a scheme with regular local rings, the product of the ideal sheaves of distinct prime
divisors is their intersection. -/
private theorem prod_idealSheaf_eq_finsetInf {X : Scheme.{v}} [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {r : ℕ}
    (E : Fin r → Mori.PrimeDivisor X) (hinj : Function.Injective E) :
    ∏ i, (E i).idealSheaf = Finset.univ.inf fun i => (E i).idealSheaf := by
  classical
  refine IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  have := hreg x
  have : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  have hπ : ∀ i, ∃ π : X.presheaf.stalk x, IdealSheafData.stalk (E i).idealSheaf x =
      Ideal.span {π} ∧ (x ∈ (E i).support → Prime π) ∧ (x ∉ (E i).support → π = 1) := by
    intro i
    by_cases hx : x ∈ (E i).support
    · obtain ⟨q, -, hq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support (E i) hx
      have hq0 : q.asIdeal ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.height_bot] at hq1
        exact zero_ne_one hq1
      obtain ⟨π, hπq, hπ⟩ := q.isPrime.exists_mem_prime_of_ne_bot hq0
      exact ⟨π, hq.trans (Ideal.eq_span_singleton_of_height_eq_one hq1 hπq hπ),
        fun _ => hπ, fun h => absurd hx h⟩
    · exact ⟨1, by rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ hx,
        Ideal.span_singleton_one], fun h => absurd h hx, fun _ => rfl⟩
  choose π hπ using hπ
  set T := Finset.univ.filter fun i => x ∈ (E i).support
  have hprod : ∏ i, π i = ∏ i ∈ T, π i := by
    rw [Finset.prod_filter_of_ne]
    intro i _ hi
    by_contra hx
    exact hi ((hπ i).2.2 hx)
  rw [MMP.Resolution.Aux.stalk_prod, MMP.Intersection.stalk_finsetInf]
  simp_rw [fun i => (hπ i).1]
  rw [Ideal.prod_span_singleton, hprod,
    ← MMP.Intersection.finsetInf_span_singleton_eq_span_prod T π
      (fun i hi => (hπ i).2.1 (Finset.mem_filter.mp hi).2)
      (fun i hi j hj hass => hinj (MMP.Intersection.eq_of_stalk_idealSheaf_eq
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (by rw [(hπ i).1, (hπ j).1]; exact Ideal.span_singleton_eq_span_singleton.mpr hass)))]
  refine le_antisymm (Finset.le_inf fun i _ => ?_)
    (Finset.le_inf fun i hi => Finset.inf_le (Finset.mem_univ i))
  by_cases hx : x ∈ (E i).support
  · exact Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)
  · rw [(hπ i).2.2 hx, Ideal.span_singleton_one]
    exact le_top

/-- A finite intersection of ideal sheaves of prime divisors is the ideal of the union of their
supports. -/
private theorem finsetInf_idealSheaf_eq_vanishingIdeal {X : Scheme.{v}} {ι : Type*}
    (s : Finset ι) (E : ι → Mori.PrimeDivisor X) :
    (s.inf fun i => (E i).idealSheaf) =
      Scheme.IdealSheafData.vanishingIdeal (s.sup fun i => (E i).idealSheaf.support) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup, ih,
      MMP.Intersection.vanishingIdeal_support_idealSheaf (E a)]

/-! ### A minimal resolution over a regular germ has no exceptional curves -/

/-- A resolution of a surface germ without exceptional curves is an isomorphism. -/
private theorem isIso_of_isExceptionalCurveEnumeration_zero {k : Type v} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g)
    {E : Fin 0 → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) : IsIso g := by
  have hXv : IsNormalVariety k sX := hg.isSurfaceGerm.1
  have : IsIntegral X := hXv.1.toIsIntegral
  have : IsNormal X := hXv.2
  have : IsIntegral Y := hg.isIntegral sX
  have : IsProper g := hg.isSmoothResolution.isProper
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hg.isSmoothResolution.isBirationalMorphism
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g hb).1 this
  set V : X.Opens := ⟨_, hU⟩
  have hPV : P ∈ V := finite_preimage_of_isExceptionalCurveEnumeration_zero hg hE
  obtain ⟨U, hU', hisoU⟩ := hg.isIso_away
  have key : MorphismProperty.isomorphisms Scheme g := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun b : Bool => if b then V else U) ?_ ?_
    · refine eq_top_iff.mpr fun x _ => ?_
      rw [TopologicalSpace.Opens.mem_iSup]
      by_cases hx : x = P
      · exact ⟨true, by subst hx; exact hPV⟩
      · refine ⟨false, ?_⟩
        change x ∈ (U : Set X)
        rw [hU']
        exact hx
    · intro b
      cases b
      · exact hisoU
      · exact hiso
  exact key

/-- If some minimal resolution of a germ has no exceptional curves, then no minimal resolution
of it has an exceptional curve. -/
private theorem false_of_isExceptionalCurveEnumeration_zero {k : Type v} [Field k]
    [IsAlgClosed k] {X Y Y₂ : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hg : IsMinimalGermResolution sX P g) {E : Fin 0 → Mori.PrimeDivisor Y}
    (hE : IsExceptionalCurveEnumeration g P E) {f : Y₂ ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y₂] [IsNormal Y₂] (hf : IsMinimalGermResolution sX P f) {n : ℕ}
    {E₂ : Fin n → Mori.PrimeDivisor Y₂} (hE₂ : IsExceptionalCurveEnumeration f P E₂)
    (hn : 1 ≤ n) : False := by
  have : IsIso g := isIso_of_isExceptionalCurveEnumeration_zero hg.1 hE
  have hX := hf.1.isSurfaceGerm
  obtain ⟨huniv, -⟩ := MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f hX.1
    hX.2.1 hf.isMinimalSurfaceResolution
  obtain ⟨a, ha, -⟩ := huniv _ g hg.1.isSmoothResolution
  have hs : (inv g ≫ a) ≫ f = 𝟙 X := by rw [Category.assoc, ha, IsIso.inv_hom_id]
  have hfs : f ≫ (inv g ≫ a) = 𝟙 Y₂ :=
    (huniv _ f hf.1.isSmoothResolution).unique
      (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp f)
  have : IsIso f := ⟨⟨inv g ≫ a, hfs, hs⟩⟩
  have : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  have hinj : Function.Injective f.base := f.isOpenEmbedding.injective
  -- the first exceptional curve of `f` would be a point
  set D := E₂ ⟨0, hn⟩
  have hD := hE₂.isGermExceptionalCurve ⟨0, hn⟩
  have hsub : (D.support : Set Y₂) ⊆ f.base ⁻¹' {P} := hD.1.prop.2
  have hgen := primeDivisor_genericPoint_mem_support D
  have hsing : (D.support : Set Y₂) = {D.genericPoint} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hgen, fun w hw => hinj ?_⟩
    have h1 : f.base w = P := hsub hw
    have h2 : f.base D.genericPoint = P := hsub hgen
    rw [h1, h2]
  exact ne_singleton_of_topologicalKrullDim_eq_one
    (by rw [← topologicalKrullDim_subscheme]; exact hD.2.2) _ hsing

/-- The inverse transform of a reduced boundary has nonzero coefficient along the transform of
each of its components. -/
theorem inverseTransformDivisor_ne_zero_of_isReducedBoundary {X Y : Scheme.{v}} (f : X ⟶ Y)
    {B : QDivisor Y} (hB : IsReducedBoundary B) {C : Mori.PrimeDivisor Y} (hC : C ∈ B.support)
    {D : Mori.PrimeDivisor X} (hD : inverseTransformPrimeDivisor f C = some D) :
    inverseTransformDivisor f B D ≠ 0 := by
  classical
  have hsum : inverseTransformDivisor f B D = ∑ C' ∈ B.support,
      ((inverseTransformPrimeDivisor f C').elim 0 (Finsupp.single · (B C'))) D := by
    conv_lhs => rw [← Finsupp.sum_single B]
    rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun C' _ => ?_
    rw [inverseTransformDivisor_single]
  rw [hsum]
  refine (Finset.sum_pos' (fun C' hC' => ?_) ⟨C, hC, ?_⟩).ne'
  · rcases inverseTransformPrimeDivisor f C' with _ | D'
    · exact le_rfl
    · change (0 : ℚ) ≤ Finsupp.single D' (B C') D
      rw [Finsupp.single_apply]
      split_ifs
      · rw [hB C' hC']
        exact zero_le_one
      · exact le_rfl
  · rw [hD]
    change (0 : ℚ) < Finsupp.single D (B C) D
    rw [Finsupp.single_eq_same, hB C hC]
    exact zero_lt_one

/-- On a locally Noetherian scheme a point lies in the support of a finite intersection of ideal
sheaves iff it lies in the support of one of them. -/
theorem mem_support_finsetInf_iff {X : Scheme.{v}} [IsLocallyNoetherian X] {ι : Type*}
    (s : Finset ι) (I : ι → X.IdealSheafData) (x : X) :
    x ∈ (s.inf I).support ↔ ∃ i ∈ s, x ∈ (I i).support := by
  rw [← not_iff_not, ← Stacks.Divisors.stalk_eq_top_iff_notMem_support,
    MMP.Intersection.stalk_finsetInf, Finset.inf_eq_top_iff]
  simp only [not_exists, not_and, Stacks.Divisors.stalk_eq_top_iff_notMem_support]

open Scheme.IdealSheafData in
/-- A ring map `𝒪̂_{Y,y} → Γ((n + 1)D, 𝒪)` agreeing with the pullback of germs is the `n`-th
component of the comparison map to formal functions. -/
private theorem eq_completionToFormalNeighborhood_of_germ {X Y : Scheme.{v}} (f : X ⟶ Y)
    (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] (D : X.IdealSheafData)
    [IsReduced D.subscheme] (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) (n : ℕ)
    (ψ : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) →+*
      Γ((D ^ (n + 1)).subscheme, ⊤))
    (hψ : ∀ (U : Y.Opens) (hyU : y ∈ U) (hU : ⊤ ≤ ((D ^ (n + 1)).subschemeι ≫ f) ⁻¹ᵁ U)
      (s : Γ(Y, U)), ψ (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
        (Y.presheaf.germ U y hyU s)) = (((D ^ (n + 1)).subschemeι ≫ f).appLE U ⊤ hU).hom s)
    (t : AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) :
    ψ t = (D.completionToFormalNeighborhood f y hmaps t).1 n := by
  refine ringHom_eq_of_algebraMap_eq ψ (((Pi.evalRingHom _ n).comp
    D.formalNeighborhoodRing.subtype).comp (D.completionToFormalNeighborhood f y hmaps)) n
    (fun x hx => ?_) (fun r => ?_) t
  · change (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) x) = 0
    rw [hx, map_zero]
  · obtain ⟨U, hyU, s, rfl⟩ := Y.presheaf.germ_exist r
    rw [hψ U hyU (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y
      (base_thickening_eq D f y hmaps n) U hyU) s]
    symm
    change (D.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ _)).1 n = _
    rw [completionToFormalNeighborhood_of]
    exact Scheme.Hom.stalkToΓ_germ _ _ _ _ _ _

/-- If a section vanishes on a closed subscheme `Z` through `x`, its germ at `f x` is not a
unit. -/
private theorem germ_mem_maximalIdeal_of_app_subschemeι_comp_eq_zero {X Y : Scheme.{v}}
    (f : X ⟶ Y) (Z : X.IdealSheafData) {x : X} (hx : x ∈ Z.support) {η : Y} (hxη : f.base x = η)
    {U : Y.Opens} (hU : η ∈ U) (r : Γ(Y, U)) (hr : ((Z.subschemeι ≫ f).app U).hom r = 0) :
    (Y.presheaf.germ U η hU).hom r ∈ maximalIdeal (Y.presheaf.stalk η) := by
  obtain ⟨t, rfl⟩ : x ∈ Set.range Z.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  have hfU : f.base (Z.subschemeι t) ∈ U := by
    rw [hxη]
    exact hU
  have htU : (Z.subschemeι ≫ f).base t ∈ U := hfU
  have h0 := congrArg (Z.subscheme.presheaf.germ ((Z.subschemeι ≫ f) ⁻¹ᵁ U) t htU).hom hr
  rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.stalkMap_comp] at h0
  change (Z.subschemeι.stalkMap t).hom ((f.stalkMap (Z.subschemeι t)).hom
    ((Y.presheaf.germ U (f.base (Z.subschemeι t)) hfU).hom r)) = 0 at h0
  have h1 : (f.stalkMap (Z.subschemeι t)).hom
      ((Y.presheaf.germ U (f.base (Z.subschemeι t)) hfU).hom r) ∈ maximalIdeal _ := by
    have h2 := RingHom.mem_ker.mpr h0
    rw [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk] at h2
    exact (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support Z _).mpr hx h2
  rw [Scheme.Hom.germ_stalkMap_apply] at h1
  exact (germ_app_mem_maximalIdeal_iff f hxη hU r).mp h1

/-- If the fibre of `f` over `y` lies in the union of the prime divisors `E i`, all of which map
to `y`, then the fibre is that union. -/
private theorem preimage_singleton_eq_iUnion_support {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y)
    {r : ℕ} (E : Fin r → Mori.PrimeDivisor X)
    (hfib : f.base ⁻¹' {y} ⊆ ((∏ i, (E i).idealSheaf).support : Set X))
    (hmaps : ∀ x ∈ ((∏ i, (E i).idealSheaf).support : Set X), f.base x = y) :
    f.base ⁻¹' {y} = ⋃ i, ((E i).support : Set X) := by
  have h := coe_support_prod Finset.univ fun i => (E i).idealSheaf
  simp only [Finset.mem_univ, Set.iUnion_true] at h
  exact le_antisymm (h ▸ hfib) fun z hz => hmaps z (h ▸ hz)

/-- An isomorphism `φ : S ≃+* R` carries the contraction of `P` onto `J` when membership in `J`
is a predicate which, along `φ`, is membership in `P`. -/
private theorem map_comap_eq_of_forall_mem_iff {S A R F : Type*} [CommRing S] [CommRing A]
    [CommRing R] [FunLike F S A] [RingHomClass F S A] (ι : F) (φ : S ≃+* R) {P : Ideal A}
    {J : Ideal R} {Q : R → Prop} (hJ : ∀ t, t ∈ J ↔ Q t) (hQ : ∀ a, Q (φ a) ↔ ι a ∈ P) :
    Ideal.map φ (Ideal.comap ι P) = J := by
  ext t
  rw [Ideal.mem_map_of_equiv, hJ]
  refine ⟨fun ⟨a, ha, h⟩ => h ▸ (hQ a).mpr ha, fun ht => ⟨φ.symm t, (hQ _).mp ?_,
    φ.apply_symm_apply t⟩⟩
  rwa [φ.apply_symm_apply]

section Cases

variable {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{v}}
  (sY : Y ⟶ Spec (.of K)) (y : Y) (B : QDivisor Y)

/-- **Types (3) and (9), nonempty chain.** The completed germ is the cyclic quotient
`K[[u, v]]^{μ_m}` given by the formal plumbing of the chain, with the boundary ideal the
invariants in `(u)` (one boundary point, `l = 1`) or in `(u) ∩ (v)` (two, `l = 2`). -/
private theorem exists_ringEquiv_of_chain (hS : IsSurfaceGermWithBoundary sY y B)
    (hB : IsReducedBoundary B)
    {Y' : Scheme.{v}} (f : Y' ⟶ Y) [QuasiCompact (f ≫ sY)] [IsLocallyNoetherian Y']
    [IsNormal Y'] {n : ℕ} (E : Fin n → Mori.PrimeDivisor Y') (hf : IsMinimalGermResolution sY y f)
    (hE : IsExceptionalCurveEnumeration f y E) (hn : 1 ≤ n) {l : ℕ}
    (pt : Fin l → Mori.PrimeDivisor Y' × Y') (Γ : ExtendedWeightedGraph (Fin n) (Fin l))
    (e : Fin n ≃ Fin n) (hΓ : IsExtendedDualGraph sY y B f E pt Γ)
    (hchain : Γ.toWeightedGraph.IsChainOrder e) (hw : ∀ j, 2 ≤ Γ.toWeightedGraph.weight j)
    (hl : l = 1 ∨ l = 2) (hpt : ∀ (a b : Fin l), a ≠ b → (pt a).2 ≠ (pt b).2)
    (hbd : ∀ (a : Fin l) j, Γ.boundaryEdgeWeight j a =
      if j = e (if (a : ℕ) = 0 then ⟨0, hn⟩ else ⟨n - 1, by omega⟩) then 1 else 0) :
    letI := Mori.stalkAlgebra sY y
    ∃ (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)),
      2 ≤ m ∧
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype
          (if l = 1 then Ideal.span {MvPowerSeries.X 0}
            else Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1})) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨⟨⟨hYv, hYn⟩, hYd, hycl, -⟩, hBy, -⟩ := hS
  have hg := hf.1
  have : IsIntegral Y' := hg.isIntegral sY
  have : IsProper f := hg.isSmoothResolution.isProper
  have hY'v : Mori.IsVariety K (f ≫ sY) := hg.isVariety
  have hY'd := hg.topologicalKrullDim_eq
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := hYv.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (f ≫ sY)
  have : IsNoetherian Y' := ⟨⟩
  have : IsIntegral Y := hYv.toIsIntegral
  have : Smooth (f ≫ sY) := (isSmoothScheme_iff _).mp hsm
  have : Mori.IsVariety K (f ≫ sY) := hY'v
  have : SmoothOfRelativeDimension 2 (f ≫ sY) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 2 (by exact_mod_cast hY'd)
  have hfc : IsIso f.c := by
    have h := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (f ≫ sY)
      sY hY'v ⟨hYv, hYn⟩ f hg.isSmoothResolution.isBirationalMorphism).1
    have : ∀ U, IsIso (f.c.app U) := fun U => h U.unop
    exact NatIso.isIso_of_isIso_app _
  -- the chain, from left to right
  set E' : Fin n → Mori.PrimeDivisor Y' := fun i => E (e i) with hE'
  set b : Fin n → ℕ := fun i => (Γ.toWeightedGraph.weight (e i)).toNat with hbdef
  have hb : ∀ i, 2 ≤ b i := fun i => by
    have := hw (e i)
    simp only [hbdef]
    omega
  have hinj : Function.Injective E' := hE.injective.comp e.injective
  have hexc : ∀ i, IsGermExceptionalCurve f y (E' i) := fun i => hE.isGermExceptionalCurve _
  have hprop : ∀ i, IsProper ((E' i).idealSheaf.subschemeι ≫ f ≫ sY) := fun i =>
    ((hexc i).isProper sY hg).2
  have hrat : ∀ i, IsSmoothRationalCurve (f ≫ sY) (E' i).idealSheaf := fun i => by
    have h := hΓ.isWeightedDualGraph.genus (e i)
    rw [hchain.genus_eq_zero i] at h
    exact isSmoothRationalCurve_of_isArithmeticGenusOf_zero _ _ (hexc i).2 (by exact_mod_cast h)
  have hself : ∀ i, IsIntersectionNumber (f ≫ sY) (Finsupp.single (E' i) 1) (E' i).idealSheaf
      (-(b i : ℤ)) := fun i => by
    have h := hΓ.isWeightedDualGraph.weight (e i)
    have hnn : (0 : ℤ) ≤ Γ.toWeightedGraph.weight (e i) := by have := hw (e i); omega
    have hbi : ((b i : ℕ) : ℤ) = Γ.toWeightedGraph.weight (e i) := Int.toNat_of_nonneg hnn
    rw [hbi]
    push_cast
    exact h
  have hne : ∀ i j : Fin n, i.val ≠ j.val → e i ≠ e j := fun i j h he =>
    h (congrArg Fin.val (e.injective he))
  have hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      IsIntersectionNumber (f ≫ sY) (Finsupp.single (E' i) 1) (E' j).idealSheaf 1 := by
    intro i j hij
    have h := hΓ.isWeightedDualGraph.edgeWeight (e i) (e j) (hne i j (by omega))
    rw [hchain.edgeWeight_eq i j, if_pos (Or.inl hij)] at h
    exact_mod_cast h
  have hfar : ∀ i j : Fin n, i.val + 1 < j.val →
      Disjoint (E' i).support (E' j).support := by
    intro i j hij
    have h := hΓ.isWeightedDualGraph.edgeWeight (e i) (e j) (hne i j (by omega))
    rw [hchain.edgeWeight_eq i j, if_neg (by omega)] at h
    refine (disjoint_support_of_isIntersectionNumber_zero (f ≫ sY) hY'v hsm hY'd
      (fun h' => hne j i (by omega) (hE.injective h')) (hprop j) (by exact_mod_cast h)).symm
  -- the exceptional curve
  set I := ∏ i, (E' i).idealSheaf with hI
  have hreg' : ∀ x : Y', IsRegularLocalRing (Y'.presheaf.stalk x) :=
    ((isRegular_iff_regular_stalks Y').1
      (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme (f ≫ sY) hsm)).2
  have hred : IsReduced I.subscheme := by
    rw [hI, prod_idealSheaf_eq_finsetInf hreg' E' hinj, finsetInf_idealSheaf_eq_vanishingIdeal]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hmaps : ∀ x ∈ (I.support : Set Y'), f.base x = y := by
    intro x hx
    rw [hI, coe_support_prod] at hx
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hx
    exact (hexc i).1.prop.2 hi
  have hfib : f.base ⁻¹' {y} ⊆ (I.support : Set Y') := by
    have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sY) sY hY'v ⟨hYv, hYn⟩ f hg.isSmoothResolution.isBirationalMorphism).2 y
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (preimage_subset_iUnion_support hg hn hE hconn hz)
    rw [hI, coe_support_prod]
    refine Set.mem_iUnion₂.mpr ⟨e.symm j, Finset.mem_univ _, ?_⟩
    simp only [hE', Equiv.apply_symm_apply]
    exact hj
  -- the two marked points and their markings
  obtain ⟨pL, pR, hpLR, hpL, hpL', hpR, hpR', ZL, ZR, hZL, hZR, hZL_succ, hZR_succ, hZLs, hZRs,
    hZLc, hZRc, hJ⟩ : ∃ (pL pR : Y') (_ : pL ≠ pR) (_ : pL ∈ (E' ⟨0, hn⟩).support)
      (_ : ∀ i, i ≠ ⟨0, hn⟩ → pL ∉ (E' i).support) (_ : pR ∈ (E' ⟨n - 1, by omega⟩).support)
      (_ : ∀ i, i ≠ ⟨n - 1, by omega⟩ → pR ∉ (E' i).support)
      (ZL ZR : ℕ → Y'.IdealSheafData) (hZL : ∀ n, I ^ (n + 1) ≤ ZL n)
      (hZR : ∀ n, I ^ (n + 1) ≤ ZR n) (_ : ∀ n, ZL n = ZL (n + 1) ⊔ I ^ (n + 1))
      (_ : ∀ n, ZR n = ZR (n + 1) ⊔ I ^ (n + 1))
      (_ : ∀ n, ((ZL n).support : Set Y') = {pL}) (_ : ∀ n, ((ZR n).support : Set Y') = {pR})
      (_ : ∀ n, ∃ e : (ZL n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ f ≫ sY)
      (_ : ∀ n, ∃ e : (ZR n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ f ≫ sY),
      ∀ t, t ∈ Ideal.map (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) ↔
        if l = 1 then
          (∀ n, (Scheme.IdealSheafData.inclusion (hZL n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0)
        else
          (∀ n, (Scheme.IdealSheafData.inclusion (hZL n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0) ∧
          (∀ n, (Scheme.IdealSheafData.inclusion (hZR n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0) := by
    classical
    have : LocallyOfFiniteType (f ≫ sY) := hY'v.toLocallyOfFiniteType
    obtain ⟨hFcl, hFne⟩ := hg.isClosed_preimage_and_ne_univ
    -- the components of the boundary and their transforms
    have hbir : ∀ x : Y, x ≠ y → x ∈ biregularLocus f := by
      obtain ⟨U, hU, hiso⟩ := hg.isIso_away
      intro x hx
      exact le_biregularLocus hiso (show x ∈ (U : Set Y) by rw [hU]; exact hx)
    have hgenC : ∀ C ∈ B.support, C.genericPoint ≠ y := fun C _ =>
      genericPoint_ne_of_isClosed hYv hYd C hycl
    have htr : ∀ C ∈ B.support, ∃ D : Mori.PrimeDivisor Y',
        inverseTransformPrimeDivisor f C = some D ∧ f.base D.genericPoint = C.genericPoint :=
      fun C hC => exists_inverseTransformPrimeDivisor_eq_some C (hbir _ (hgenC C hC))
    have hDC : ∀ a, ∃ C ∈ B.support, f.base (pt a).1.genericPoint = C.genericPoint := by
      intro a
      obtain ⟨C, hC, hτ⟩ := exists_mem_support_of_inverseTransformDivisor_ne_zero f B
        (hΓ.isGermBoundaryPoint a).1
      obtain ⟨D, hD, hgen⟩ := htr C hC
      rw [hD] at hτ
      obtain rfl := Option.some.inj hτ
      exact ⟨C, hC, hgen⟩
    have hCD : ∀ C ∈ B.support, ∃ a, f.base (pt a).1.genericPoint = C.genericPoint := by
      intro C hC
      obtain ⟨D, hD, hgen⟩ := htr C hC
      have hcl : IsClosed (f.base '' (D.support : Set Y')) :=
        f.isClosedMap _ D.idealSheaf.support.isClosed
      have h1 : C.genericPoint ∈ f.base '' (D.support : Set Y') :=
        ⟨_, primeDivisor_genericPoint_mem_support D, hgen⟩
      have h2 : (C.support : Set Y) ⊆ f.base '' D.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h1)
      obtain ⟨z, hz, hfz⟩ := h2 (hBy C hC)
      obtain ⟨a, ha⟩ := hΓ.exists_eq D z
        ⟨inverseTransformDivisor_ne_zero_of_isReducedBoundary f hB hC hD, hz, hfz⟩
      exact ⟨a, by rwa [ha]⟩
    have hptinj : Function.Injective fun a => (pt a).2 := fun a b h =>
      by_contra fun hab => hpt a b hab h
    have hDfib : ∀ a, f.base (pt a).1.genericPoint ≠ y := fun a => by
      obtain ⟨C, hC, hgen⟩ := hDC a
      rw [hgen]
      exact hgenC C hC
    have hDE : ∀ a i, (pt a).1 ≠ E i := by
      intro a i h
      apply hDfib a
      rw [h]
      exact (hE.isGermExceptionalCurve i).1.prop.2 (primeDivisor_genericPoint_mem_support (E i))
    have hDb : ∀ a b, (pt a).2 ∈ (pt b).1.support → (pt b).1 = (pt a).1 := by
      intro a b hab
      obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 (pt a).2
        ⟨(hΓ.isGermBoundaryPoint b).1, hab, (hΓ.isGermBoundaryPoint a).2.2⟩
      have hca : c = a := hptinj (show (pt c).2 = (pt a).2 by rw [hc])
      subst hca
      exact (congrArg Prod.fst hc).symm
    -- the boundary points on the chain
    obtain ⟨eend, heend⟩ : ∃ g : Fin l → Fin n,
        ∀ a, g a = e (if (a : ℕ) = 0 then ⟨0, hn⟩ else ⟨n - 1, by omega⟩) := ⟨_, fun _ => rfl⟩
    have hpos : ∀ a j, (pt a).2 ∈ (E j).support → 0 < localIntersectionNumber (f ≫ sY)
        (pt a).2 (Finsupp.single (pt a).1 1) (Finsupp.single (E j) 1) := by
      intro a j hj
      have h := (MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne (f ≫ sY)
        hY'v hsm hY'd (fun h => hDE a j h.symm)
        ((hE.isGermExceptionalCurve j).isProper sY hg).2).2.2 _
        ⟨hj, (hΓ.isGermBoundaryPoint a).2.1⟩
      rwa [localIntersectionNumber_comm] at h
    have hqE : ∀ a j, (pt a).2 ∈ (E j).support ↔ j = eend a := by
      intro a j
      have h := (hbd a j).symm.trans (hΓ.boundaryEdgeWeight_eq j a)
      rw [← heend a] at h
      constructor
      · intro hj
        by_contra hne
        rw [if_neg hne, if_pos hj] at h
        exact (hpos a j hj).ne h
      · rintro rfl
        rw [if_pos rfl] at h
        by_contra hj'
        rw [if_neg hj'] at h
        exact one_ne_zero h
    have hqlin : ∀ a, localIntersectionNumber (f ≫ sY) (pt a).2
        (Finsupp.single (pt a).1 1) (Finsupp.single (E (eend a)) 1) = 1 := by
      intro a
      have h := (hbd a (eend a)).symm.trans (hΓ.boundaryEdgeWeight_eq (eend a) a)
      rw [← heend a, if_pos rfl, if_pos ((hqE a _).mpr rfl)] at h
      exact h.symm
    have hqcl : ∀ a, IsClosed ({(pt a).2} : Set Y') := by
      intro a
      by_contra hcl
      have hqF : (pt a).2 ∈ f.base ⁻¹' {y} := (hΓ.isGermBoundaryPoint a).2.2
      have hne : closure ({(pt a).2} : Set Y') ≠ Set.univ := fun h =>
        hFne (Set.eq_univ_of_univ_subset
          (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hqF)))
      have h1 := coheight_eq_one_of_not_isClosed (f ≫ sY) hY'd hcl hne
      have hsp : (E (eend a)).genericPoint ⤳ (pt a).2 := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact (hqE a _).mpr rfl
      have hneE : closure ({(E (eend a)).genericPoint} : Set Y') ≠ Set.univ := by
        rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        intro h
        exact hFne <| Set.eq_univ_of_univ_subset (h ▸ (hE.isGermExceptionalCurve (eend a)).1.prop.2)
      have h2 := eq_of_specializes_of_coheight_eq_one h1 hsp hneE
      apply hDE a (eend a)
      refine (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support ?_).symm
      rw [h2]
      exact (hΓ.isGermBoundaryPoint a).2.1
    have hdimq : ∀ a, ringKrullDim (Y'.presheaf.stalk (pt a).2) = 2 := fun a =>
      MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (f ≫ sY) hY'v hY'd (pt a).2 (hqcl a)
    have hprin := fun (x : Y') (hx : IsClosed ({x} : Set Y')) =>
      exists_stalk_idealSheaf_eq_span_singleton hY'v hY'd hreg' hx
    have hloc : ∀ a, ∃ h w : Y'.presheaf.stalk (pt a).2,
        IdealSheafData.stalk (pt a).1.idealSheaf (pt a).2 = Ideal.span {h} ∧
        IdealSheafData.stalk (E (eend a)).idealSheaf (pt a).2 = Ideal.span {w} ∧
        Ideal.span {h, w} = maximalIdeal (Y'.presheaf.stalk (pt a).2) := by
      intro a
      obtain ⟨h, hh⟩ := hprin _ (hqcl a) _ (hΓ.isGermBoundaryPoint a).2.1
      obtain ⟨w, hw⟩ := hprin _ (hqcl a) _ ((hqE a _).mpr rfl)
      refine ⟨h, w, hh, hw, ?_⟩
      have := stalk_sup_eq_maximalIdeal_of_localIntersectionNumber_eq_one (f ≫ sY) _ _ _
        (hqlin a)
      rwa [hh, hw, ← Ideal.span_union, Set.singleton_union] at this
    choose hh hw hhD hwE hhw using hloc
    -- the ideal of the exceptional curve near a point of a single component
    have hIstalk : ∀ (x : Y') (i₀ : Fin n), (∀ i, i ≠ i₀ → x ∉ (E' i).support) →
        IdealSheafData.stalk I x = IdealSheafData.stalk (E' i₀).idealSheaf x := by
      intro x i₀ hx
      rw [hI, MMP.Resolution.Aux.stalk_prod, Finset.prod_eq_single i₀]
      · intro i _ hi
        rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ (hx i hi),
          Ideal.one_eq_top]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hIq : ∀ a, IdealSheafData.stalk I (pt a).2 = Ideal.span {hw a} := by
      intro a
      rw [hIstalk (pt a).2 (e.symm (eend a)) fun i hi hmem => hi ?_]
      · simp only [hE', Equiv.apply_symm_apply]; exact hwE a
      · rw [← e.symm_apply_apply i, (hqE a (e i)).mp hmem]
    -- the markings at the boundary points
    have hmark := fun a => exists_marking_of_span_eq (f ≫ sY) (pt a).2 (hqcl a) (hdimq a) I
      (hIq a) (hhw a)
    choose Zm hZm hZm_succ hZms hZmc hZmp using hmark
    -- the boundary curve, finite over `Y`
    set Zb : Y'.IdealSheafData := Finset.univ.inf fun a => (pt a).1.idealSheaf with hZbdef
    have hZbmem : ∀ z : Y', z ∈ Zb.support ↔ ∃ a, z ∈ (pt a).1.support := fun z => by
      rw [hZbdef, mem_support_finsetInf_iff]
      exact ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, Finset.mem_univ a, ha⟩⟩
    have hιZ : Function.Injective Zb.subschemeι := Zb.subschemeι.isClosedEmbedding.injective
    have hZbfin : IsFinite (Zb.subschemeι ≫ f) := by
      refine (IsFinite.iff_isProper_and_locallyQuasiFinite _).mpr ⟨inferInstance,
        LocallyQuasiFinite.of_finite_preimage_singleton _ fun x => ?_⟩
      refine Set.Finite.of_finite_image ?_ hιZ.injOn
      by_cases hx : x = y
      · refine (Set.finite_range fun a => (pt a).2).subset ?_
        rintro _ ⟨t, ht, rfl⟩
        have hz : Zb.subschemeι t ∈ Zb.support := by
          change _ ∈ (Zb.support : Set Y')
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
        obtain ⟨b, hb⟩ := (hZbmem _).mp hz
        obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 (Zb.subschemeι t)
          ⟨(hΓ.isGermBoundaryPoint b).1, hb, by rw [← hx]; exact ht⟩
        exact ⟨c, show (pt c).2 = _ by rw [hc]⟩
      · obtain ⟨U, hU, hiso⟩ := hg.isIso_away
        have : IsIso (f ∣_ U) := hiso
        refine (MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict f U
          (show x ∈ (U : Set Y) by rw [hU]; exact hx)).finite.subset ?_
        rintro _ ⟨t, ht, rfl⟩
        exact ht
    -- germs vanishing on the boundary
    have hJmem : ∀ z : Y.presheaf.stalk y,
        z ∈ IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y ↔
          ∀ C ∈ B.support, z ∈ IdealSheafData.stalk C.idealSheaf y := by
      intro z
      rw [← Finset.inf_eq_iInf, MMP.Intersection.stalk_finsetInf, Submodule.mem_finsetInf]
    have hspC : ∀ C ∈ B.support, AlgebraicGeometry.PrimeDivisor.genericPoint C ⤳ y :=
      fun C hC => by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hBy C hC
    have hkerZ : ∀ (U : Y.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ r : Γ(Y, U),
        ((Zb.subschemeι ≫ f).app U).hom r = 0 →
        (Y.presheaf.germ U y hy).hom r ∈
          IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y := by
      intro U hy _ r hr
      rw [hJmem]
      intro C hC
      rw [germ_mem_stalk_iff C (hBy C hC) hy r]
      obtain ⟨a, ha⟩ := hCD C hC
      exact germ_mem_maximalIdeal_of_app_subschemeι_comp_eq_zero f Zb
        ((hZbmem _).mpr ⟨a, primeDivisor_genericPoint_mem_support _⟩) ha
        ((hspC C hC).mem_open U.isOpen hy) r hr
    have hpy : ∀ a, f.base (pt a).2 = y := fun a => (hΓ.isGermBoundaryPoint a).2.2
    have hpull : ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
        (Y.presheaf.germ U y hy).hom s ∈ IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y →
        ∀ a n, (Y'.presheaf.germ (f ⁻¹ᵁ U) (pt a).2
          (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy)).hom ((f.app U).hom s) ∈
            IdealSheafData.stalk (Zm a n) (pt a).2 := by
      intro U hy s hs a n
      rw [hZmp a n]
      refine Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) ?_
      rw [← hhD a]
      obtain ⟨C, hC, hgen⟩ := hDC a
      have hCU : AlgebraicGeometry.PrimeDivisor.genericPoint C ∈ U :=
        (hspC C hC).mem_open U.isOpen hy
      refine (germ_mem_stalk_iff (pt a).1 (hΓ.isGermBoundaryPoint a).2.1 (U := f ⁻¹ᵁ U)
        (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy) ((f.app U).hom s)).mpr ?_
      refine (germ_app_mem_maximalIdeal_iff f hgen hCU s).mpr ?_
      exact (germ_mem_stalk_iff C (hBy C hC) hy s).mp ((hJmem _).mp hs C hC)
    have hpZ : ∀ a, (pt a).2 ∈ Zb.support := fun a =>
      (hZbmem _).mpr ⟨a, (hΓ.isGermBoundaryPoint a).2.1⟩
    have hallZ : ∀ z ∈ Zb.support, f.base z = y → ∃ a, (pt a).2 = z := by
      intro z hz hfz
      obtain ⟨b, hb⟩ := (hZbmem z).mp hz
      obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 z ⟨(hΓ.isGermBoundaryPoint b).1, hb, hfz⟩
      exact ⟨c, show (pt c).2 = _ by rw [hc]⟩
    have hhZ : ∀ a, hh a ∈ IdealSheafData.stalk Zb (pt a).2 := by
      intro a
      rw [hZbdef, MMP.Intersection.stalk_finsetInf, Submodule.mem_finsetInf]
      intro b _
      by_cases hab : (pt a).2 ∈ (pt b).1.support
      · rw [hDb a b hab, hhD a]; exact Ideal.mem_span_singleton_self _
      · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ hab]; trivial
    have hwm : ∀ a, hw a ∈ maximalIdeal (Y'.presheaf.stalk (pt a).2) := fun a => by
      rw [← hhw a]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hdeep : ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
        (∀ a, (Y'.presheaf.germ (f ⁻¹ᵁ U) (pt a).2
          (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy)).hom ((f.app U).hom s) ∈
            IdealSheafData.stalk (Zm a n) (pt a).2) →
        (Y.presheaf.germ U y hy).hom s ∈
          IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y ⊔
            maximalIdeal (Y.presheaf.stalk y) ^ N := by
      intro N
      obtain ⟨n₀, hn₀⟩ := mem_sup_pow_of_forall_mem_span f y hycl Zb (fun a => (pt a).2)
        hptinj hpy hpZ hallZ hh hw hhZ hwm _ hkerZ N
      refine ⟨n₀, fun n hn U hy s hs => hn₀ n hn U hy s fun a => ?_⟩
      rw [← hZmp a n]; exact hs a
    have hJgen := mem_map_iff_forall_appTop_inclusion_eq_zero f y I hmaps (fun a => (pt a).2)
      hpy Zm hZms hZm _ hpull hdeep
    rcases hl with rfl | rfl
    · -- type (3): the boundary point, and an auxiliary marking at the other end
      have he0 : eend 0 = e ⟨0, hn⟩ := by rw [heend]; simp
      set iR : Fin n := ⟨n - 1, by omega⟩ with hiR
      have hEnormal : IsNormal (E' iR).idealSheaf.subscheme := by
        obtain ⟨-, eiso, -⟩ := hrat iR
        exact Stacks.ResolutionOfSurfaces.isNormal_of_iso_projectiveLineProj K
          ((projectiveLineIsoProj K).symm ≪≫ eiso)
      have : JacobsonSpace Y' := LocallyOfFiniteType.jacobsonSpace (f ≫ sY)
      set W : Set Y' := ((E' iR).support : Set Y') ∩
        ((⋃ i ∈ {i | i ≠ iR}, ((E' i).support : Set Y')) ∪ {(pt 0).2})ᶜ with hW
      have hWlc : IsLocallyClosed W :=
        (E' iR).idealSheaf.support.isClosed.isLocallyClosed.inter (IsOpen.isLocallyClosed
          (isOpen_compl_iff.mpr ((Set.Finite.isClosed_biUnion (Set.toFinite _)
            fun i _ => (E' i).idealSheaf.support.isClosed).union (hqcl 0))))
      have hWne : W.Nonempty := by
        refine ⟨(E' iR).genericPoint, primeDivisor_genericPoint_mem_support _, ?_⟩
        rintro (h | h)
        · obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp h
          exact hi (hinj (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hmem)).symm
        · have h' : (E' iR).genericPoint = (pt 0).2 := h
          apply hDE 0 (e iR)
          refine (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support ?_).symm
          rw [h']; exact (hΓ.isGermBoundaryPoint 0).2.1
      obtain ⟨pR, ⟨hpRE, hpRo⟩, hpRcl⟩ := nonempty_inter_closedPoints hWne hWlc
      rw [mem_closedPoints_iff] at hpRcl
      have hpRo1 : pR ∉ ⋃ i ∈ {i | i ≠ iR}, ((E' i).support : Set Y') :=
        fun h => hpRo (Or.inl h)
      have hpRo2 : pR ≠ (pt 0).2 := fun h => hpRo (Or.inr h)
      obtain ⟨wR, hwR⟩ := hprin pR hpRcl (E' iR) hpRE
      have := hreg' pR
      obtain ⟨h0R, hmR⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hY'v hY'd (E' iR) hpRE hpRcl
      have hdimR := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (f ≫ sY) hY'v hY'd pR hpRcl
      obtain ⟨hR, hhwR⟩ := exists_span_pair_eq_maximalIdeal (E' iR) hpRE hdimR hwR h0R hmR
      have hIR : IdealSheafData.stalk I pR = Ideal.span {wR} :=
        (hIstalk pR iR fun i hi hmem => hpRo1 (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)).trans hwR
      obtain ⟨ZR, hZR, hZR_succ, hZRs, hZRc, -⟩ :=
        exists_marking_of_span_eq (f ≫ sY) pR hpRcl hdimR I hIR hhwR
      refine ⟨(pt 0).2, pR, fun h => hpRo2 h.symm, ?_, ?_, hpRE,
        fun i hi hmem => hpRo1 (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩), Zm 0, ZR, hZm 0, hZR,
        hZm_succ 0, hZR_succ, hZms 0, hZRs, hZmc 0, hZRc, fun t => (hJgen t).trans ?_⟩
      · change (pt 0).2 ∈ (E (e ⟨0, hn⟩)).support
        rw [← he0]; exact (hqE 0 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 0 (e i)).mp hmem).trans he0))
      · rw [if_pos rfl, Fin.forall_fin_one]
    · -- type (9): the two boundary points
      have he0 : eend 0 = e ⟨0, hn⟩ := by rw [heend]; simp
      have he1 : eend 1 = e ⟨n - 1, by omega⟩ := by rw [heend]; simp
      refine ⟨(pt 0).2, (pt 1).2, hpt 0 1 (by decide), ?_, ?_, ?_, ?_, Zm 0, Zm 1, hZm 0, hZm 1,
        hZm_succ 0, hZm_succ 1, hZms 0, hZms 1, hZmc 0, hZmc 1, fun t => (hJgen t).trans ?_⟩
      · change (pt 0).2 ∈ (E (e ⟨0, hn⟩)).support
        rw [← he0]; exact (hqE 0 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 0 (e i)).mp hmem).trans he0))
      · change (pt 1).2 ∈ (E (e ⟨n - 1, by omega⟩)).support
        rw [← he1]; exact (hqE 1 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 1 (e i)).mp hmem).trans he1))
      · rw [if_neg (by decide), Fin.forall_fin_two]
  -- the contraction of the marked chain (`exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre`)
  have : IsNormal Y := hYn
  have happ := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (f ≫ sY)
    sY hY'v ⟨hYv, hYn⟩ f hg.isSmoothResolution.isBirationalMorphism).1
  have hcontr : IsContraction K sY (f ≫ sY) f := ⟨hYv, hY'v, rfl, inferInstance, happ⟩
  have hfib' := preimage_singleton_eq_iUnion_support f y E' hfib hmaps
  obtain ⟨m, hm, q, hq, φ, ψ, hc, hψ, h0, -, h01⟩ :=
    MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre (f ≫ sY) sY f hcontr hYd y
      hycl hn E' b hb hfib' hinj hrat hself hadj hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR
      hZL_succ hZR_succ (hZLs 0) (hZRs 0) hZLc hZRc
  -- its formal-functions comparison is that of the theorem on formal functions
  have hψχ := fun n => eq_completionToFormalNeighborhood_of_germ f y I hmaps n (ψ n) (hψ n)
  have hJ' : ∀ t, t ∈ Ideal.map (algebraMap (Y.presheaf.stalk y)
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
      (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) ↔
      if l = 1 then (∀ n, ((Scheme.IdealSheafData.inclusion (hZL n)).app ⊤).hom (ψ n t) = 0)
      else (∀ n, ((Scheme.IdealSheafData.inclusion (hZL n)).app ⊤).hom (ψ n t) = 0) ∧
        (∀ n, ((Scheme.IdealSheafData.inclusion (hZR n)).app ⊤).hom (ψ n t) = 0) := by
    intro t
    rw [hJ t]
    simp only [hψχ]
    rfl
  refine ⟨m, q, ⟨inferInstance, inferInstance, by omega, hq⟩, φ, hm, hc,
    map_comap_eq_of_forall_mem_iff _ φ hJ' fun a => ?_⟩
  split_ifs
  exacts [h0 a, h01 a]

end Cases

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}}
  (sY : Y ⟶ Spec (.of K))

/-- **The boundary ideal of a chain germ** (FA 16.6.3). Let `(Y, y; C)` be a surface germ with
reduced boundary `C` over an algebraically closed field `K` of characteristic `0`, of type (3),
resp. type (9), whose minimal resolution has at least one exceptional curve. Then for some
`m ≥ 2` and `q` prime to `m` there is a `K`-isomorphism `φ : K[[u, v]]^{μ_m} ≃ 𝒪̂_{Y,y}` carrying
the invariants in `(u)`, resp. `(uv) = (u) ∩ (v)`, onto `I_{C,y} 𝒪̂_{Y,y}`; equivalently it
carries the ideal of `C^{(1)}_{m,q}`, resp. `C^{(2)}_{m,q}`, onto `I_{C,y} 𝒪̂_{Y,y}`. -/
@[mmp "lem_mmp_foundation_fa16_chain_boundary_ideal"]
theorem exists_ringEquiv_cyclicInvariants_of_isFig3Type3_or_isFig3Type9_of_pos
    (y : Y) (B : QDivisor Y) (hB : IsReducedBoundary B) (g : MvPowerSeries (Fin 2) K)
    (htype : IsFig3Type3 sY y B ∧ g = MvPowerSeries.X 0 ∨
      IsFig3Type9 sY y B ∧ g = MvPowerSeries.X 0 * MvPowerSeries.X 1)
    (hchain : ∃ (X : Scheme.{u}) (f : X ⟶ Y) (_ : QuasiCompact (f ≫ sY))
      (_ : IsLocallyNoetherian X) (_ : IsNormal X) (n : ℕ) (E : Fin n → Mori.PrimeDivisor X),
      IsMinimalGermResolution sY y f ∧ IsExceptionalCurveEnumeration f y E ∧ 1 ≤ n) :
    letI := Mori.stalkAlgebra sY y
    ∃ (m : ℕ) (q : ℤ) (h : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)),
      2 ≤ m ∧
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g})) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) ∧
      Ideal.map φ (Ideal.comap (Scheme.ΓSpecIso (.of (cyclicInvariants K m q))).inv.hom
          ((Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h g)).ideal
            ⟨⊤, isAffineOpen_top _⟩)) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨X₂, f₂, _, _, _, n₂, E₂, hf₂, hE₂, hn₂⟩ := hchain
  have hrad : (Ideal.span {g}).radical = Ideal.span {g} := by
    rcases htype with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact radical_span_X 0
    · rw [← span_X_inf_span_X, Ideal.radical_inf, radical_span_X, radical_span_X]
  suffices H : ∃ (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)),
      2 ≤ m ∧
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g})) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) by
    obtain ⟨m, q, h, φ, hm, hc, hI⟩ := H
    refine ⟨m, q, h, φ, hm, hc, hI, ?_⟩
    rwa [comap_vanishingIdeal_cyclicQuotientImage, hrad]
  rcases htype with ⟨⟨hS, Y', f, _, _, _, n, E, hf, hE, hcase⟩, rfl⟩ |
    ⟨⟨hS, Y', f, _, _, _, n, E, hf, hE, hcase⟩, rfl⟩
  · rcases hcase with ⟨rfl, -⟩ | ⟨hn, pt, Γ, e, hΓ, hch, hw, hbd⟩
    · exact (false_of_isExceptionalCurveEnumeration_zero hf hE hf₂ hE₂ hn₂).elim
    · obtain ⟨m, q, h, φ, hm, hc, hI⟩ := exists_ringEquiv_of_chain sY y B hS hB f E hf hE hn pt Γ e
        hΓ hch hw (Or.inl rfl) (fun a b hab => absurd (Subsingleton.elim a b) hab)
        (fun a j => by rw [Subsingleton.elim a 0]; simpa using hbd j)
      refine ⟨m, q, h, φ, hm, hc, ?_⟩
      rwa [if_pos rfl] at hI
  · rcases hcase with ⟨rfl, -⟩ | ⟨hn, pt, Γ, e, hΓ, hch, hw, hne, hbd0, hbd1⟩
    · exact (false_of_isExceptionalCurveEnumeration_zero hf hE hf₂ hE₂ hn₂).elim
    · obtain ⟨m, q, h, φ, hm, hc, hI⟩ := exists_ringEquiv_of_chain sY y B hS hB f E hf hE hn pt Γ e
        hΓ hch hw (Or.inr rfl) (fun a b hab => by
          fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | exact hne | exact hne.symm)
        (fun a j => by fin_cases a <;> simpa using by first | exact hbd0 j | exact hbd1 j)
      refine ⟨m, q, h, φ, hm, hc, ?_⟩
      rw [← span_X_inf_span_X]
      rwa [if_neg (by decide)] at hI

end MMP.Flips
