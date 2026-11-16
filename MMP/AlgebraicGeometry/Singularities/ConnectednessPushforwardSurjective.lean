module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Vanishing.ProperRelativeKawamataViehweg
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
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
import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition

/-!
# lem fa17 connectedness pushforward surjective

Chain fold of: `lem_fa17_connectedness_pushforward_surjective`.

## Main results

* `MMP.Flips.IsSNCDivisor.isSNCDivisor_of_support_subset`: a reduced effective divisor supported
  on an snc divisor in the sense of FA is an snc divisor in the sense of Lazarsfeld.
* `MMP.Mori.DivisorWithCoeffs.IsSNC.isSNCDivisor`: a reduced effective snc divisor in the sense
  of `MMP.Mori.DivisorWithCoeffs.IsSNC` is an snc divisor in the sense of Lazarsfeld.
* `MMP.Mori.genericFiberH0_eq_relativeGenericRank`: for a quasi-compact quasi-separated
  morphism from an integral scheme, the dimension of the sections of a quasi-coherent module on
  the generic fibre is the generic rank of its direct image.
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MMP MMP.Mori MMP.Flips

/-! ### Simple normal crossings -/

namespace MMP.Flips

/-- A reduced effective divisor whose components are among those of an snc divisor in the sense
of FA is an snc divisor in the sense of Lazarsfeld: at a closed point, the local equations of the
components through it are distinct members of a regular system of parameters, so their product
generates the ideal of the reduced divisor. -/
public theorem IsSNCDivisor.isSNCDivisor_of_support_subset {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] {D D' : Divisor X}
    (hD : IsSNCDivisor sX D) (hD' : MMP.Intersection.IsReducedEffective D')
    (h : D'.support ⊆ D.support) : MMP.Intersection.IsSNCDivisor sX D' := by
  classical
  refine ⟨hD', fun E hE => hD.2.1 E (h hE), fun x hx => ?_⟩
  obtain ⟨n, w, σ, hw, hσ, hloc⟩ := hD.2.2 x hx
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  set T := D'.support.filter fun E => x ∈ E.support with hT
  have hTD : ∀ E ∈ T, E ∈ D.support ∧ x ∈ E.support := fun E hE =>
    ⟨h (Finset.mem_filter.mp hE).1, (Finset.mem_filter.mp hE).2⟩
  let σ' : T → Fin n := fun E => σ ⟨E.1, hTD E.1 E.2⟩
  have hσ' : Function.Injective σ' := fun E E' hEE' => by
    have h' := congrArg Subtype.val (hσ hEE')
    exact Subtype.ext h'
  let g : Fin T.card → Fin n := σ' ∘ T.equivFin.symm
  have hg : Function.Injective g := hσ'.comp T.equivFin.symm.injective
  have hk : T.card ≤ n := by simpa using Fintype.card_le_of_injective g hg
  let e : {j : Fin n // j ∈ Set.range (Fin.castLE hk)} ≃ {j : Fin n // j ∈ Set.range g} :=
    (Equiv.ofInjective _ (Fin.castLE_injective hk)).symm.trans (Equiv.ofInjective g hg)
  let π : Equiv.Perm (Fin n) := e.extendSubtype
  have hπ : ∀ i, π (Fin.castLE hk i) = g i := by
    intro i
    rw [Equiv.extendSubtype_apply_of_mem e _ ⟨i, rfl⟩]
    simp [e]
  refine ⟨n, w ∘ π, T.card, hk, ⟨?_, hw.2⟩, ?_⟩
  · rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact hw.1
  · rw [MMP.Intersection.stalk_suppIdeal, ← hT]
    let p : MMP.Mori.PrimeDivisor X → X.presheaf.stalk x := fun E =>
      if hE : E ∈ T then w (σ' ⟨E, hE⟩) else 1
    have hpT : ∀ E (hE : E ∈ T), p E = w (σ' ⟨E, hE⟩) := fun E hE => by simp [p, hE]
    have hspan : ∀ E ∈ T, IdealSheafData.stalk E.idealSheaf x = Ideal.span {p E} :=
      fun E hE => by
        rw [hpT E hE]
        exact hloc ⟨E, hTD E hE⟩
    rw [Finset.inf_congr rfl hspan, MMP.Intersection.finsetInf_span_singleton_eq_span_prod]
    · refine congrArg (fun r => Ideal.span {r}) ?_
      rw [← Finset.prod_coe_sort T]
      refine (Fintype.prod_equiv T.equivFin.symm (fun i => (w ∘ π) (Fin.castLE hk i))
        (fun E : T => p E) fun i => ?_).symm
      rw [Function.comp_apply, hπ i, hpT _ (T.equivFin.symm i).2]
      rfl
    · intro E hE
      rw [hpT E hE]
      exact MMP.Intersection.prime_of_isRegularSystemOfParameters hw _
    · intro E hE E' hE' hass
      refine MMP.Intersection.eq_of_stalk_idealSheaf_eq (hTD E hE).2 (hTD E' hE').2 ?_
      rw [hspan E hE, hspan E' hE']
      exact Ideal.span_singleton_eq_span_singleton.mpr hass

/-- A reduced effective divisor which is snc in the sense of `MMP.Mori.DivisorWithCoeffs.IsSNC`
is an snc divisor in the sense of Lazarsfeld. -/
public theorem _root_.MMP.Mori.DivisorWithCoeffs.IsSNC.isSNCDivisor {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] {D : Divisor X}
    (h : D.IsSNC sX) (hD : MMP.Intersection.IsReducedEffective D) :
    MMP.Intersection.IsSNCDivisor sX D :=
  IsSNCDivisor.isSNCDivisor_of_support_subset ⟨hD, h.1, fun x _ => h.2 x⟩ hD subset_rfl

end MMP.Flips

/-! ### `lem_fa17_connectedness_pushforward_surjective` -/

namespace MMP.Fold06.LemFa17ConnectednessPushforwardSurjective

/-- A left exact functor maps the second arrow of a short exact sequence to an epimorphism when
its first right derived functor vanishes on the first term. -/
private theorem epi_map_g_of_isZero_rightDerived_one {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {S : ShortComplex C} (hS : S.ShortExact)
    (h : IsZero ((F.rightDerived 1).obj S.X₁)) : Epi (F.map S.g) := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  set E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  have hδ : E.δ hS 0 = 0 := h.eq_of_tgt _ _
  have hepi : Epi ((F.rightDerived 0).map S.g) :=
    (ShortComplex.exact_iff_epi _ hδ).1 (E.exact_δ₁ hS 0)
  rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf S.g]
  infer_instance

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX g τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  have hpull : pullbackRationalPluriForms sX g τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `g : Y ⟶ X`: on a
proper curve `C ⊆ Y` whose image is the proper curve `C₀ ⊆ X`,
`g^*D · C = [k(C) : k(C₀)] · (D · C₀)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (g : Y ⟶ X) [QuasiCompact (g ≫ sX)] [CompactSpace X] [CompactSpace Y] {D : Divisor X}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ D.supp)
    (C : ProperCurve (g ≫ sX)) (C₀ : ProperCurve sX) (hC : C₀.point = g C.point) :
    (D.pullback hD hB).degreeOn k (g ≫ sX) C.ι C.dim_le (hD.isCartier_pullback g hB) =
      (residueFieldDegree g C.point : ℤ) * D.degreeOn k sX C₀.ι C₀.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward g rfl hD hB C, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C₀.isProperCurve)]
  have hCe : (⟨g C.point, hC ▸ C₀.isProperCurve⟩ : ProperCurve sX) = C₀ :=
    ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `g : Y ⟶ X` has degree zero on a proper curve
`C ⊆ Y` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (g : Y ⟶ X) [QuasiCompact (g ≫ sX)] [CompactSpace X] [CompactSpace Y] {D : Divisor X}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ D.supp)
    (C : ProperCurve (g ≫ sX)) (hc : ¬ IsProperCurve sX (g C.point)) :
    (D.pullback hD hB).degreeOn k (g ≫ sX) C.ι C.dim_le (hD.isCartier_pullback g hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward g rfl hD hB C, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **Pull-backs of relatively nef divisors.** Let `g : Y ⟶ X` be proper and `N` a Cartier
divisor on `X` with `N = m₀ M` for a `ℚ`-divisor `M` which is `h`-nef. Then
`m₀⁻¹ g^* N`, the pull-back of `M`, is `(g ≫ h)`-nef: by the projection formula its degree on a
curve `C` contracted by `g ≫ h` is `0` if `g(C)` is a point, and a positive multiple of
`M · g(C)` otherwise, `g(C)` being contracted by `h`. -/
private theorem isRelativelyNef_smul_toQDivisor_pullback {k : Type} [Field k]
    {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (g : Y ⟶ X) [IsProper g] (h : X ⟶ Z)
    {N : Divisor X} (hNc : N.IsCartier)
    (hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp) {m₀ : ℕ}
    (hm₀ : 0 < m₀) {M : QDivisor X} (hNM : Divisor.toQDivisor N = (m₀ : ℚ) • M)
    (hnef : M.IsRelativelyNef sX h) :
    ((m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB)).IsRelativelyNef (g ≫ sX) (g ≫ h) := by
  have hM : M.IsQCartier := hnef.1
  have hN'c := hNc.isCartier_pullback g hNB
  set L : QDivisor Y := (m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB) with hL
  have hm₀q : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hLN : Divisor.toQDivisor (N.pullback hNc hNB) = (m₀ : ℚ) • L := by
    rw [hL, smul_smul, mul_inv_cancel₀ hm₀q, one_smul]
  have hLq : L.IsQCartier := ⟨m₀, by exact_mod_cast hm₀.ne', N.pullback hNc hNB,
    by rw [hLN, natCast_zsmul, Nat.cast_smul_eq_nsmul], hN'c⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (g ≫ sX) hLq
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul k (g ≫ sX) C.ι _ L hLq hm₀ _ hN'c hLN]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  by_cases hc : IsProperCurve sX (g C.point)
  · obtain ⟨C₀, hC₀pt⟩ : ∃ C₀ : ProperCurve sX, C₀.point = g C.point := ⟨⟨_, hc⟩, rfl⟩
    have hC₀ : C₀.IsContractedBy h := by
      intro y hy
      rw [hC₀pt] at hy ⊢
      have hsub : closure ({g C.point} : Set X) ⊆ g '' closure ({C.point} : Set Y) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (g.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC z hz
    have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hM C₀ hC₀
    rw [QDivisor.intersectionNumber_eq_of_smul k sX C₀.ι _ M hM hm₀ N hNc hNM] at h0
    have h1 : (0 : ℚ) ≤ N.degreeOn k sX C₀.ι C₀.dim_le hNc :=
      (div_nonneg_iff.mp h0).elim (fun h => h.1)
        (fun h => absurd h.2 (not_le.mpr (by exact_mod_cast hm₀)))
    rw [degreeOn_pullback_eq_mul g hNc hNB C C₀ hC₀pt]
    push_cast
    exact mul_nonneg (Nat.cast_nonneg _) h1
  · rw [degreeOn_pullback_eq_zero g hNc hNB C hc]
    simp

/-! ### Fibre ranks and sections on the generic fibre -/

section FiberRank

variable {X : Scheme.{0}} {F G : X.Modules}

private lemma germM_smul' (M : X.Modules) (y : X) (W : X.Opens) (hy : y ∈ W) (r : Γ(X, W))
    (m : Γ(M, W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy (r • m) =
      X.presheaf.germ W y hy r • TopCat.Presheaf.germ M.val.presheaf W y hy m :=
  PresheafOfModules.germ_smul M.val y W hy r m

/-- The map on stalks (as abelian groups) induced by a morphism of modules. -/
private noncomputable def stalkMapAb (φ : F ⟶ G) (y : X) :
    TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y ⟶
      TopCat.Presheaf.stalk (C := Ab.{0}) G.val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor Ab.{0} y).map φ.mapPresheaf

private lemma stalkMapAb_germ (φ : F ⟶ G) (y : X) {W : X.Opens} (hy : y ∈ W) (ξ : Γ(F, W)) :
    stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hy ξ) =
      TopCat.Presheaf.germ G.val.presheaf W y hy (φ.app W ξ) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy φ.mapPresheaf ξ

private lemma stalkMapAb_smul (φ : F ⟶ G) (y : X) (ρ : X.presheaf.stalk y)
    (n : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf y) :
    stalkMapAb φ y (ρ • n) = ρ • stalkMapAb φ y n := by
  obtain ⟨V, hyV, ξ, rfl⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hyV
  have key : ∀ (r : Γ(X, W)) (m : Γ(F, W)),
      stalkMapAb φ y (X.presheaf.germ W y hyW r •
          TopCat.Presheaf.germ F.val.presheaf W y hyW m) =
        X.presheaf.germ W y hyW r •
          stalkMapAb φ y (TopCat.Presheaf.germ F.val.presheaf W y hyW m) := by
    intro r m
    rw [← germM_smul' F y W hyW r m, stalkMapAb_germ φ y hyW,
      stalkMapAb_germ φ y hyW m, ← germM_smul' G y W hyW r (φ.app W m)]
    congr 1
    exact Scheme.Modules.Hom.app_smul φ r m
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) y hyW ξ]
  exact key _ ζ

private lemma stalkMapAb_hom_inv_id_apply (e : F ≅ G) (x : X)
    (n : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x) :
    stalkMapAb e.inv x (stalkMapAb e.hom x n) = n := by
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf n
  have h1 := stalkMapAb_germ e.hom x hW (ζ : Γ(F, W))
  have h2 := stalkMapAb_germ e.inv x hW (e.hom.app W (ζ : Γ(F, W)))
  have h3 : e.inv.app W (e.hom.app W (ζ : Γ(F, W))) = ζ := by
    have := ConcreteCategory.congr_hom (show e.hom.app W ≫ e.inv.app W = 𝟙 _ from by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
      rfl) ζ
    exact this
  rw [h1, h2, h3]

/-- The fibre rank is invariant under isomorphism of modules. -/
private theorem fiberRank_eq_of_iso (e : F ≅ G) (x : X) :
    Scheme.Modules.fiberRank F x = Scheme.Modules.fiberRank G x := by
  unfold Scheme.Modules.fiberRank
  let eS : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{0}) G.val.presheaf x :=
    { toFun := stalkMapAb e.hom x
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul e.hom x ρ n
      invFun := stalkMapAb e.inv x
      left_inv := stalkMapAb_hom_inv_id_apply e x
      right_inv := stalkMapAb_hom_inv_id_apply e.symm x }
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) _) eS).finrank_eq

end FiberRank

/-- The dimension of a module under scalars pulled back along a ring map depends only on that
ring map. -/
private theorem finrank_compHom_congr {K R M : Type*} [Field K] [CommRing R] [AddCommGroup M]
    [Module R M] {φ ψ : K →+* R} (h : φ = ψ) :
    @Module.finrank K M _ _ (Module.compHom M φ) =
      @Module.finrank K M _ _ (Module.compHom M ψ) := by
  subst h
  rfl

/-- For a quasi-compact quasi-separated `f` from an integral scheme and a quasi-coherent `F`,
the dimension of the sections of `F` on the generic fibre is the generic rank of `f_* F`. -/
public theorem _root_.MMP.Mori.genericFiberH0_eq_relativeGenericRank {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsIntegral X] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] :
    genericFiberH0 f F = relativeGenericRank f F := by
  rw [MMP.Mori.relativeGenericRank_eq_finrank_fibre,
    LinearEquiv.finrank_eq (cohomologyOverFieldZeroLinearIso _ _ _).toLinearEquiv]
  unfold genericFiberH0
  refine finrank_compHom_congr ?_
  simp only [scalarsToGlobalSections, Scheme.Hom.appLE, Scheme.Hom.appTop]
  congr 2
  exact (Category.comp_id _).symm.trans (congrArg _ (CategoryTheory.Functor.map_id _ _).symm)

/-- **Sections on the generic fibre of a pull-back.** For a proper birational morphism
`g : Y ⟶ X` of normal varieties, a morphism `h : X ⟶ Z` and a Cartier divisor `B` on `X`,
`dim H⁰(Y_η, 𝒪(g^*B)) = dim H⁰(X_η, 𝒪(B))` on the generic fibres of `g ≫ h` and `h`: both are
the generic rank of `h_* 𝒪_X(B) = h_* g_* 𝒪_Y(g^*B)`. -/
private theorem genericFiberH0_comp_of_isPullback {k : Type} [Field k] {X Y Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (sX : X ⟶ Spec (.of k)) (g : Y ⟶ X)
    (h : X ⟶ Z)
    (hX : MMP.Mori.IsVariety k sX) (hY : MMP.Mori.IsVariety k (g ≫ sX)) [IsProper g]
    [IsProper h] (hg : IsBirationalMorphism g) (B : Divisor X) (hBc : B.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ B.supp)
    {BY : Divisor Y} (hBY : B.IsPullback g hB BY) :
    genericFiberH0 (g ≫ h) BY.divisorialSheaf = genericFiberH0 h B.divisorialSheaf := by
  have : IsDominant g := hg.isDominant
  have : QuasiSeparated h := IsSeparated.instQuasiSeparated h
  have : QuasiSeparated (g ≫ h) := IsSeparated.instQuasiSeparated (g ≫ h)
  rw [genericFiberH0_eq_relativeGenericRank, genericFiberH0_eq_relativeGenericRank]
  obtain ⟨e, -⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX g hX
    hY hg B hBc hB BY hBY 0 Divisor.isCartier_zero le_rfl
    (fun P hP => absurd (DivisorWithCoeffs.coeff_zero P) hP)
  unfold relativeGenericRank
  have hpt : (g ≫ h) (genericPoint Y) = h (genericPoint X) := by
    rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  rw [hpt]
  exact fiberRank_eq_of_iso (((Scheme.Modules.pushforwardComp g h).app _).symm ≪≫
    (Scheme.Modules.pushforward h).mapIso
      (eqToIso (by rw [add_zero]) ≪≫ e.symm)) _

/-- **Pull-backs of relatively big divisors.** Let `g : Y ⟶ X` be a proper birational morphism of
normal varieties and `N` a Cartier divisor on `X` with `N = m₀ M`. If `M` is `h`-big (by sections
on the generic fibre), then so is its pull-back `m₀⁻¹ g^* N`, for `g ≫ h`: the generic fibres have
the same dimension, and the sections of the multiples agree by
`genericFiberH0_comp_of_isPullback`. -/
private theorem isRelativelyBigOnGenericFiber_smul_toQDivisor_pullback {k : Type} [Field k]
    {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (g : Y ⟶ X) [IsProper g] (h : X ⟶ Z) (hY : MMP.Mori.IsVariety k (g ≫ sX))
    (hgb : IsBirationalMorphism g) {N : Divisor X} (hNc : N.IsCartier)
    (hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp) {m₀ : ℕ}
    (hm₀ : 0 < m₀) {M : QDivisor X} (hNM : Divisor.toQDivisor N = (m₀ : ℚ) • M)
    (hbig : IsRelativelyBigOnGenericFiber h k sX sZ M) :
    IsRelativelyBigOnGenericFiber (g ≫ h) k (g ≫ sX) sZ
      ((m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB)) := by
  obtain ⟨hXv, hZv, hhs, hhp, a, b, ha, hb, m₁, hm₁, D₁, hD₁, hD₁c, c, hc, k₀, hk⟩ := hbig
  have : IsProper h := hhp
  have : IsDominant g := hgb.isDominant
  have : MMP.Mori.IsVariety k sX := hXv
  have : MMP.Mori.IsVariety k (g ≫ sX) := hY
  have hgen : ∀ B : Divisor X, ∀ Z : irreducibleComponents Y,
      g (componentGenericPoint Y Z) ∉ B.supp := fun B =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g B
  have hD₁B := hgen D₁
  have hgs : Set.range g.base = Set.univ := by
    rw [← g.isClosedMap.isClosed_range.closure_eq, g.denseRange.closure_eq]
  refine ⟨hY, hZv, by rw [Category.assoc, hhs], inferInstance, a, b, ?_, ?_, m₁, hm₁,
    D₁.pullback hD₁c hD₁B, ?_, hD₁c.isCartier_pullback g hD₁B, c, hc, k₀, fun j hj => ?_⟩
  · rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hgb, ha]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hgs, Set.image_univ, hb]
  · have hm₀q : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
    have key : (m₀ : ℤ) • D₁ = (m₁ : ℤ) • N := by
      apply Divisor.toQDivisor_injective
      rw [map_zsmul, map_zsmul, hD₁, hNM, natCast_zsmul, natCast_zsmul,
        ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul, mul_comm]
    have hp1 := (Divisor.isPullback_pullback hD₁c hD₁B).zsmul hD₁c (m₀ : ℤ) (hgen _)
    have hp2 := ((Divisor.isPullback_pullback hNc hNB).zsmul hNc (m₁ : ℤ) (hgen _)).of_eq
      key.symm (hB₂ := hgen _)
    have h3 : (m₀ : ℤ) • D₁.pullback hD₁c hD₁B = (m₁ : ℤ) • N.pullback hNc hNB :=
      hp1.eq (hD₁c.zsmul _) hp2
    have h4 := congrArg Divisor.toQDivisor h3
    rw [map_zsmul, map_zsmul, natCast_zsmul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h4
    calc Divisor.toQDivisor (D₁.pullback hD₁c hD₁B)
        = (m₀ : ℚ)⁻¹ • ((m₀ : ℚ) • Divisor.toQDivisor (D₁.pullback hD₁c hD₁B)) := by
          rw [smul_smul, inv_mul_cancel₀ hm₀q, one_smul]
      _ = (m₀ : ℚ)⁻¹ • ((m₁ : ℚ) • Divisor.toQDivisor (N.pullback hNc hNB)) := by rw [h4]
      _ = _ := by rw [smul_smul, smul_smul, mul_comm]
  · rw [genericFiberH0_comp_of_isPullback sX g h hXv hY hgb _ (hD₁c.zsmul _) (hgen _)
      ((Divisor.isPullback_pullback hD₁c hD₁B).zsmul hD₁c _ (hgen _))]
    exact hk j hj

/-! ### Exceptional divisors and birational transforms -/

/-- If `d + c = n`, then `d + 2 ≤ n` exactly when `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

/-- A divisor over `X` is exceptional exactly when its center has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) :
    E.IsExceptional ↔ 2 ≤ Order.coheight (E.f E.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (E.f E.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{0}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- A rational map defined at the generic point of `P` and sending it to the generic point of `E`
transforms `P` into `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{0}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A scheme separated over a field is separated over the terminal scheme. -/
private lemma isSeparated_toTerminal {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : Mori.PrimeDivisor X) (E : Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal (f ≫ sX)
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := Mori.RationalMap.IsBirational.inverse hf
  have hdef : Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties and prime divisors `P` of
`X` and `E` of `Y` with `f(η_E) = η_P`, the coefficient of `E` in `f⁻¹_* D` is that of `P` in
`D`. -/
private theorem coeff_birationalInverseTransform_of_map_genericPoint {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
    (P : Mori.PrimeDivisor X) (E : Mori.PrimeDivisor Y) (h : f E.genericPoint = P.genericPoint) :
    (birationalInverseTransform f hf D).coeff E = D.coeff P := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal (f ≫ sX)
  have htr := transformPrimeDivisor_inverse_eq_some hX f hY hf P E h
  have huniq : ∀ P', Mori.RationalMap.transformPrimeDivisor
      (Mori.RationalMap.IsBirational.inverse hf) P' = some E → P' = P := by
    intro P' h'
    obtain ⟨g', hP', hg'⟩ := Mori.RationalMap.definedAt_iff.mp
      (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h').1
    obtain ⟨e', he, he'⟩ := hf.isInverse_inverse
    have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h' g' hg' hP'
    have h2 := apply_hom_eq_of_isInverse f e' he g' (hg'.trans he'.symm) hP'
    rw [← h1] at h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h2.symm.trans h)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq D

/-! ### Discrepancies on a log resolution -/

/-- **The discrepancies of `g^*(K + D)`.** Let `ω` be a rational form with `div ω = K`, and let
`N = -m₀ (K + D)` be Cartier. Then the discrepancy of a prime divisor `E` on the model `Y` is
`a(E, D) = ord_E(g^* ω) + coeff_E(g^* N) / m₀`: it is computed with the one-term presentation
`div ω + D = -(1/m₀) N`. -/
private theorem eq_ordForm_add_coeff_pullback_of_isDiscrepancy {k : Type} [Field k]
    [PerfectField k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hX : IsNormalVariety k sX) {g : Y ⟶ X}
    [IsProper g]
    (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g) {n : ℕ} {K : Divisor X}
    {D : QDivisor X} {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hdivω : divisorOfForm ω = K)
    {m₀ : ℕ} (hm₀ : 0 < m₀) {N : Divisor X} (hNc : N.IsCartier)
    (hNM : Divisor.toQDivisor N = (m₀ : ℚ) • -(Divisor.toQDivisor K + D))
    (hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp)
    (E : Mori.PrimeDivisor Y) {a : ℚ}
    (ha : IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation a) :
    haveI : IsDominant g := hgb.isDominant
    a = (divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E +
      (m₀ : ℚ)⁻¹ * (N.pullback hNc hNB).coeff E := by
  have : IsDominant g := hgb.isDominant
  have hm : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hdisc : IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation
      (((divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E : ℝ) +
        (m₀ : ℝ)⁻¹ * ((N.pullback hNc hNB).coeff E : ℝ)) := by
    refine ⟨ha.1, ha.2.1, ha.2.2.1, _, ω, 1, fun _ => -(m₀ : ℝ)⁻¹, fun _ => N, rfl, hdivω, hX,
      ha.1.topologicalKrullDim_eq, hω0, fun _ => hNc, ?_, fun _ => N.pullback hNc hNB,
      fun _ => ⟨hNB, Divisor.isPullback_pullback hNc hNB⟩, ?_⟩
    · ext Γ
      have hΓ := congrArg (fun G : QDivisor X => ((G.coeff Γ : ℚ) : ℝ)) hNM
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_add] at hΓ
      push_cast at hΓ
      simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hdivω,
        QDivisor.coeff_toRDivisor, Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      rw [hΓ]
      field_simp
    · rw [Fin.sum_univ_one, coeff_divisorOfForm]
      change _ = (E.ordForm (pullbackRationalPluriForms sX g ω) : ℝ) - _
      ring
  have h : ((a : ℚ) : ℝ) = (((divisorOfForm (pullbackRationalPluriForms sX g ω)).coeff E +
      (m₀ : ℚ)⁻¹ * (N.pullback hNc hNB).coeff E : ℚ) : ℝ) := by
    push_cast
    exact ha.eq hdisc
  exact_mod_cast h

/-- A prime divisor `E` of `Y` with nonzero discrepancy `a(E, D)` is exceptional over `X` or the
birational transform of a component of `D`: if `E` is not exceptional, it is the transform of
the prime divisor `P` with `g(η_E) = η_P`, and `a(E, D) = -coeff_P D`. -/
private theorem coeff_inverseTransform_ne_zero_or_isExceptional {k : Type} [Field k]
    [PerfectField k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hX : IsNormalVariety k sX) {g : Y ⟶ X}
    [IsProper g]
    (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g) {n : ℕ} {K : Divisor X}
    {D : QDivisor X} (E : Mori.PrimeDivisor Y) {a : ℚ}
    (ha : IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation a) (ha0 : a ≠ 0) :
    (birationalInverseTransform g hgb
        (Divisor.toRDivisor (MMP.Intersection.reducedDivisor D))).coeff E ≠ 0 ∨
      IsExceptionalPrimeDivisor sX g E := by
  classical
  refine or_iff_not_imp_right.mpr fun hex => ?_
  set DE : ProperDivisorOver k sX := ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center,
      ← isExceptional_iff_two_le_coheight ha.1.topologicalKrullDim_eq]
    exact fun h' => hex ⟨hY, hgb, inferInstance, h'⟩
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
  push Not at hc
  obtain ⟨P, hv⟩ := hc
  have hvP : DE.valuation = P.divisorialValuation := by
    change DE.toDivisorOver.valuation = _
    rw [hv]
    ext φ
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  have hDP := (hvP ▸ ha).eq_neg_coeff
  rw [QDivisor.coeff_toRDivisor] at hDP
  have hDP0 : D.coeff P ≠ 0 := fun h0 => ha0 (by simpa [h0] using hDP)
  rw [coeff_birationalInverseTransform_of_map_genericPoint hX g hY hgb _ P E
      (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv),
    Divisor.coeff_toRDivisor, MMP.Intersection.reducedDivisor,
    MMP.Intersection.coeff_reducedDivisorOf, if_pos (Finsupp.mem_support_iff.mpr hDP0)]
  norm_num

/-- **The round-up identity.** If `A = Σ_{a > -1} a(E) E`, `F = Σ_{a ≤ -1} -a(E) E` and
`L = Σ a(E) E - K_Y` with `K_Y` integral, then `K_Y + ⌈L⌉ = ⌈A⌉ - ⌊F⌋`. -/
private theorem add_roundUp_eq_roundUp_sub_roundDown {Y : Scheme.{0}}
    (e : Mori.PrimeDivisor Y → ℚ) {KY : Divisor Y} {L A F : QDivisor Y}
    (hL : ∀ E, L.coeff E = e E - KY.coeff E) (hA : ∀ E, A.coeff E = if -1 < e E then e E else 0)
    (hF : ∀ E, F.coeff E = if e E ≤ -1 then -e E else 0) :
    KY + L.roundUp = A.roundUp - F.roundDown := by
  ext E
  rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_roundUp,
    DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundDown, hL, hA, hF]
  split_ifs with h1 h2 h2
  · exact absurd h2 (not_le.mpr h1)
  · rw [Int.ceil_sub_intCast]
    ring
  · rw [Int.ceil_sub_intCast, Int.ceil_zero, Int.floor_neg]
    ring
  · exact absurd (not_lt.mp h1) h2

/-- The divisor of the pull-back of a nonzero rational top form along a birational morphism
with smooth source is a canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {g : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType (g ≫ sX)] [IsDominant g] [IsProper g]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (hsm : IsSmoothScheme (g ≫ sX)) {n : ℕ} (hn : topologicalKrullDim X = n)
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) :
    (divisorOfForm (pullbackRationalPluriForms sX g ω)).IsCanonicalDivisor (g ≫ sX) n := by
  have : MMP.Mori.IsVariety k (g ≫ sX) := hY.1
  have hnY : topologicalKrullDim Y = n := by
    have := hX.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (g ≫ sX) hgb, hn]
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hsm hnY
  have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
    (pullbackRationalPluriForms_ne_zero sX hn g hgb hω0)
  rw [one_smul] at h
  exact hK₀.of_linearlyEquivalent h

/-- On a log resolution of `(X, (Supp D)_red)`, a `ℚ`-divisor whose coefficients differ from the
discrepancies by integers has its fractional part on an snc divisor. -/
private theorem hasSNCSupport_roundUp_sub {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {g : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsProper g] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (g ≫ sX))
    (hgb : IsBirationalMorphism g) {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (hg : MMP.Flips.IsLogResolution sX (Divisor.toRDivisor (MMP.Intersection.reducedDivisor D)) g)
    (e : Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E, IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E))
    {L : QDivisor Y} {KY : Divisor Y} (hLc : ∀ E, L.coeff E = e E - KY.coeff E) :
    MMP.Intersection.HasSNCSupport (g ≫ sX) (Divisor.toQDivisor L.roundUp - L) := by
  obtain ⟨-, -, -, -, hgb', G, -, hGiff, hGsnc⟩ := hg
  unfold MMP.Intersection.HasSNCSupport MMP.Intersection.reducedDivisor
  refine hGsnc.isSNCDivisor_of_support_subset
    (MMP.Intersection.isReducedEffective_reducedDivisorOf _) ?_
  rw [MMP.Intersection.support_reducedDivisorOf]
  intro E hE
  have hE' : (Divisor.toQDivisor L.roundUp - L).coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
  have he0 : e E ≠ 0 := fun h0 => hE' (by
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundUp,
      hLc, h0, zero_sub, ← Int.cast_neg, Int.ceil_intCast, Int.cast_neg, sub_self])
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply,
    (hGiff E).mpr (coeff_inverseTransform_ne_zero_or_isExceptional hX hY hgb E (he E) he0)]
  exact one_ne_zero

private theorem epi_pushforward_cokernel_π_of_isLogResolution
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {h : X ⟶ Z}
    {g : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hhs : h ≫ sZ = sX)
    [IsProper h] [Surjective h] (hfib : ∀ z : Z, _root_.IsConnected (h ⁻¹' {z}))
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X}
    (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (hneg : ∀ P : Mori.PrimeDivisor X, D.coeff P < 0 → 2 ≤ Order.coheight (h P.genericPoint))
    (hnef : (-(Divisor.toQDivisor K + D)).IsRelativelyNef sX h)
    (hbig : IsRelativelyBigOnGenericFiber h k sX sZ (-(Divisor.toQDivisor K + D)))
    (hg : MMP.Flips.IsLogResolution sX (Divisor.toRDivisor (MMP.Intersection.reducedDivisor D)) g)
    [IsProper g] (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (e : Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E, IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E))
    {A F : QDivisor Y} (hA : ∀ E, A.coeff E = if -1 < e E then e E else 0)
    (hF : ∀ E, F.coeff E = if e E ≤ -1 then -e E else 0)
    (hle : A.roundUp - F.roundDown ≤ A.roundUp) :
    Epi ((Scheme.Modules.pushforward (g ≫ h)).map
      (cokernel.π (Divisor.divisorialSheafInclusion hle))) := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant g := hgb.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have hsm : IsSmoothScheme (g ≫ sX) := hg.2.2.1
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdivω : divisorOfForm ω = K := by
    ext Γ
    rw [coeff_divisorOfForm, hωK]
  set KY : Divisor Y := divisorOfForm (pullbackRationalPluriForms sX g ω)
  have hKY : KY.IsCanonicalDivisor (g ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_pullback hX hY hgb hsm hn hω0
  obtain ⟨m₀, hm₀, N, hNM, hNc⟩ : ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ N : Divisor X,
      Divisor.toQDivisor N = (m₀ : ℚ) • -(Divisor.toQDivisor K + D) ∧ N.IsCartier := by
    refine ⟨_, QDivisor.cartierIndex_pos hKD, ?_⟩
    obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hKD
    refine ⟨-D₀, ?_, hD₀c.neg⟩
    rw [map_neg, hD₀, smul_neg, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hNB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ N.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant g N
  set L : QDivisor Y := (m₀ : ℚ)⁻¹ • Divisor.toQDivisor (N.pullback hNc hNB)
  have hLc : ∀ E, L.coeff E = e E - KY.coeff E := fun E => by
    rw [eq_ordForm_add_coeff_pullback_of_isDiscrepancy hX hY hgb hω0 hdivω hm₀ hNc hNM hNB E
      (he E), DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
    ring
  have hsncL := hasSNCSupport_roundUp_sub hX hY hgb hg e he hLc
  have hR1 := isZero_rightDerived_divisorialSheaf_canonical_add_roundUp hsm hKY
    (isRelativelyNef_smul_toQDivisor_pullback g h hNc hNB hm₀ hNM hnef)
    (isRelativelyBigOnGenericFiber_smul_toQDivisor_pullback g h hY.1 hgb hNc hNB hm₀ hNM hbig)
    hsncL 1 one_pos
  rw [add_roundUp_eq_roundUp_sub_roundDown e hLc hA hF] at hR1
  have : PreservesFiniteLimits (Scheme.Modules.pushforward (g ≫ h)) :=
    Stacks.SchemeCohomology.pushforward_preservesFiniteLimits _
  exact epi_map_g_of_isZero_rightDerived_one _
    (S := ShortComplex.mk (Divisor.divisorialSheafInclusion hle) (cokernel.π _)
      (cokernel.condition _))
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      inferInstance inferInstance) hR1

end MMP.Fold06.LemFa17ConnectednessPushforwardSurjective

namespace MMP.Flips

/-- **FA 17.4.3.** Let `h : X ⟶ Z` be a proper surjective morphism of normal varieties over an
algebraically closed field `k` of characteristic zero with connected fibres, `K` a canonical
divisor of `X` of dimension `n`, and `D` a `ℚ`-divisor on `X` with `K + D` `ℚ`-Cartier, such that
`codim_Z h(P) ≥ 2` for every prime divisor `P` with negative coefficient in `D`, and with
`-(K + D)` `h`-nef and `h`-big. Let `g : Y ⟶ X` be a log resolution of `(X, (Supp D)_red)`,
`e(E) = a(E, X, D)` the discrepancy of each prime divisor `E` of `Y`, and `A`, `F` the
`ℚ`-divisors with coefficients `e(E)` where `e(E) > -1` (resp. `-e(E)` where `e(E) ≤ -1`) and `0`
elsewhere. Then `(g ≫ h)_* 𝒪_Y(⌈A⌉) ⟶ (g ≫ h)_* 𝒪_{⌊F⌋}(⌈A⌉)` is surjective, where
`𝒪_{⌊F⌋}(⌈A⌉)` is the cokernel of `𝒪_Y(⌈A⌉ - ⌊F⌋) ⟶ 𝒪_Y(⌈A⌉)`. -/
@[mmp "lem_fa17_connectedness_pushforward_surjective"]
public theorem epi_pushforward_cokernel_π_divisorialSheafInclusion_roundUp_sub_roundDown
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {h : X ⟶ Z}
    {g : Y ⟶ X}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hhs : h ≫ sZ = sX)
    [IsProper h] [Surjective h] (hfib : ∀ z : Z, _root_.IsConnected (h ⁻¹' {z}))
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X}
    (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (hneg : ∀ P : Mori.PrimeDivisor X, D.coeff P < 0 → 2 ≤ Order.coheight (h P.genericPoint))
    (hnef : (-(Divisor.toQDivisor K + D)).IsRelativelyNef sX h)
    (hbig : IsRelativelyBigOnGenericFiber h k sX sZ (-(Divisor.toQDivisor K + D)))
    (hg : MMP.Flips.IsLogResolution sX (Divisor.toRDivisor (MMP.Intersection.reducedDivisor D)) g)
    [IsProper g] (hY : IsNormalVariety k (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (e : Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E, IsDiscrepancy sX n K (QDivisor.toRDivisor D)
      (ProperDivisorOver.mk ⟨Y, g, hY, hgb, E⟩ inferInstance).valuation (e E))
    {A F : QDivisor Y} (hA : ∀ E, A.coeff E = if -1 < e E then e E else 0)
    (hF : ∀ E, F.coeff E = if e E ≤ -1 then -e E else 0)
    (hle : A.roundUp - F.roundDown ≤ A.roundUp) :
    Epi ((Scheme.Modules.pushforward (g ≫ h)).map
      (cokernel.π (Divisor.divisorialSheafInclusion hle))) :=
  MMP.Fold06.LemFa17ConnectednessPushforwardSurjective.epi_pushforward_cokernel_π_of_isLogResolution
    hZ hX hhs hfib hK hKD hneg hnef hbig hg hY hgb e he hA hF hle

end MMP.Flips
