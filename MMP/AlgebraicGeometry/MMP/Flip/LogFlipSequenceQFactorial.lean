module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.Resolution.Blowup
import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
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
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
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
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
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
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Sequences of log flips, and blow-ups of regular centres

This file collects results used in the termination of sequences of log flips.

Let `(X_i, B_i)_{i < L}` be a sequence of log flips starting from `(X₀, B₀)`. Each flip
`θ_i : X_i ⤏ X_{i+1}` is an isomorphism off the exceptional loci of the small contractions
`φ_i` and `φ_i⁺`, which contain the generic point of no prime divisor; so the birational
transform `θ_{i*}` is a bijection on prime divisors. Hence the nonzero coefficients of `B_i` are
those of `B₀`, and, transporting `ℚ`-Cartier divisors across the flip through the extremal
ray `ρ(X_i/Z_i) = 1`, every `X_i` is `ℚ`-factorial when `X₀` is.

Let `X` be a normal variety over a field of characteristic zero and
`W ⊆ X` an irreducible closed subset of codimension `c ≥ 2` with `𝒪_{X,η_W}` regular. Near
`η_W`, both `X` and `W` are smooth. The order valuation of `𝒪_{X,η_W}` is the valuation of the
exceptional divisor `E_W` of the blow-up along `W`, with centre `W`, and
`a(E_W, X, B) = c - 1 - mult_W B`. When `X` and `W` are regular and `c = 2`, a chart computation
over `η_W` bounds the multiplicity of a strict transform along a codimension-two subset of the
exceptional divisor by the multiplicity along `W`.

Finally, every normal surface over an algebraically closed field has a proper birational
morphism onto it from an open subscheme of a smooth projective surface (compactify, normalize,
resolve).

## Main results

* `MMP.Flips.SequenceOfLogFlips.frange_boundary_model`: the set of nonzero coefficients of
  every boundary `B_i` is that of `B₀`.
* `MMP.Flips.SequenceOfLogFlips.isQFactorial_model`: every model `X_i` is `ℚ`-factorial.
* `MMP.Mori.exists_smooth_projective_open_isProper_isBirationalMorphism`: smooth projective
  models of normal surfaces.
* `MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing`: `a(E_W, X, B) = c - 1 - mult_W B`.
* `MMP.Mori.multiplicityAlong_inverseTransformDivisor_blowUpToBase_le`:
  `mult_Z (π⁻¹_* P) ≤ mult_W P` for the blow-up of a regular codimension-two centre.
* `MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp`: the order valuation along
  a regular centre is divisorial, with centre `W`.

## Implementation notes

The base field is an algebraically closed field of characteristic zero rather than `ℂ`: the
proofs use only that a regular point of a variety over a perfect field has a smooth
neighbourhood, and `valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp_of_charZero` and
`isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero` hold over any field of characteristic
zero. The normalization of a compactification *in* `S`
(`AlgebraicGeometry.Scheme.Hom.normalization`) takes the reduced closure and normalizes it in
one step.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.9.1, 4.15,
  7.1, 7.4.5, 7.5.3
* [Y. Kawamata, K. Matsuda, K. Matsuki, *Introduction to the minimal model problem*][KMM87],
  5-1-11
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollar-mori], Lemma 2.29
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

open MMP.Mori MMP.Fourfold Topology

/-! ### Sequences of log flips -/

section SequenceOfLogFlips

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
theorem isQCartier_smul {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) (q : ℚ) : (q • D).IsQCartier := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hD
  refine ⟨m * q.den, mul_ne_zero hm (by exact_mod_cast q.den_ne_zero), q.num • E, ?_, hEc.zsmul _⟩
  refine Finsupp.ext fun P => ?_
  have hP := congrArg (fun F : QDivisor X => F P) hE
  change ((E P : ℤ) : ℚ) = (m : ℚ) * D P at hP
  change ((q.num * E P : ℤ) : ℚ) = ((m * q.den : ℤ) : ℚ) * (q * D P)
  have := Rat.mul_den_eq_num q
  push_cast
  rw [hP, ← this]
  ring

section RelativePicardNumberOne

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]

/-- On an integral normal scheme, every Cartier Weil divisor `D` has a Cartier divisor whose
degree on every proper curve is `deg_C 𝒪_X(D)`. -/
theorem exists_cartierDivisor_degree_eq [IsIntegral X] (D : Divisor X)
    (hD : D.IsCartier) : ∃ E : X.CartierDivisor, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨E, fun C => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- On an integral normal scheme, every `ℚ`-Cartier `ℚ`-divisor `L` has an `ℝ`-Cartier divisor
with the same intersection numbers with every proper curve. -/
theorem exists_kCartierDivisor_intersectionNumber_eq [IsIntegral X] (L : QDivisor X)
    (hL : L.IsQCartier) : ∃ δ : KCartierDivisor ℝ X, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber δ = (L.intersectionNumber k sX C.ι C.dim_le hL : ℝ) := by
  set hF := QDivisor.isCartierDivisor_cartierIndex_smul hL
  obtain ⟨E, hE⟩ := exists_cartierDivisor_degree_eq sX hF.toDivisor hF.isCartier_toDivisor
  refine ⟨((L.cartierIndex hL : ℝ))⁻¹ • KCartierDivisor.ofCartier ℝ E, fun C => ?_⟩
  simp only [OneCycle.intersectionNumber, map_smul, LinearMap.smul_apply, smul_eq_mul] at hE ⊢
  rw [hE, QDivisor.intersectionNumber]
  push_cast
  ring

variable {sX}

/-- `(∑ⱼ qⱼ Lⱼ) · C = ∑ⱼ qⱼ deg_C 𝒪_X(Lⱼ)` for Cartier divisors `Lⱼ` and rational `qⱼ`. -/
theorem intersectionNumber_sum_smul {C : Scheme.{u}} (i : C ⟶ X) [IsProper (i ≫ sX)]
    (hdim : topologicalKrullDim C ≤ 1) {m : ℕ} (q : Fin m → ℚ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (s : Finset (Fin m)) :
    ∃ h : (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).IsQCartier,
      (∑ j ∈ s, q j • Divisor.toQDivisor (L j)).intersectionNumber k sX i hdim h =
        ∑ j ∈ s, q j * (L j).degreeOn k sX i hdim (hL j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using QDivisor.isQCartier_zero, ?_⟩
    simp only [Finset.sum_empty]
    rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ (QDivisor.isQCartier_toQDivisor
      Divisor.isCartier_zero) (by simp), QDivisor.intersectionNumber_toQDivisor k sX i hdim _
      Divisor.isCartier_zero, Divisor.degreeOn_zero']
    simp
  | insert a s ha ih =>
    obtain ⟨h, ih⟩ := ih
    have ha' := isQCartier_smul (QDivisor.isQCartier_toQDivisor (hL a)) (q a)
    have hs := ha'.add h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hs, ?_⟩
    rw [QDivisor.intersectionNumber_add' k sX i hdim _ _ ha' h hs, ih,
      MMP.Fourfold.intersectionNumber_smul sX i hdim _ (QDivisor.isQCartier_toQDivisor (hL a))
        (q a) ha',
      QDivisor.intersectionNumber_toQDivisor k sX i hdim _ (hL a)]

/-- **Independence of the presentation.** If the `ℚ`-Cartier `ℚ`-divisor `H` equals
`∑ⱼ rⱼ Lⱼ` as an `ℝ`-divisor, with `Lⱼ` Cartier and `rⱼ ∈ ℝ`, then
`H · C = ∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
theorem intersectionNumber_eq_sum_of_toRDivisor_eq {C : Scheme.{u}} (i : C ⟶ X)
    [IsProper (i ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) (H : QDivisor X) (hH : H.IsQCartier)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : QDivisor.toRDivisor H = ∑ j, r j • Divisor.toRDivisor (L j)) :
    (H.intersectionNumber k sX i hdim hH : ℝ) =
      ∑ j, r j * (L j).degreeOn k sX i hdim (hL j) := by
  -- test the difference against every `ℚ`-linear functional `π : ℝ → ℚ`
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro π
  have hcast : ∀ x : ℚ, π (x : ℝ) = x * π 1 := fun x => by
    rw [show (x : ℝ) = x • (1 : ℝ) by rw [Rat.smul_def, mul_one], map_smul, smul_eq_mul]
  have hzs : ∀ (x : ℝ) (n : ℤ), π (x * n) = n * π x := fun x n => by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  have key : π 1 • H = ∑ j, π (r j) • Divisor.toQDivisor (L j) := by
    refine Finsupp.ext fun P => ?_
    have hP := congrArg (fun G : RDivisor X => G P) h
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at hP ⊢
    change ((H P : ℚ) : ℝ) = ∑ j, r j * ((L j P : ℤ) : ℝ) at hP
    change π 1 * H P = ∑ j, π (r j) * ((L j P : ℤ) : ℚ)
    have := congrArg π hP
    rw [hcast, map_sum] at this
    simp only [hzs] at this
    rw [mul_comm, this]
    simp [mul_comm]
  obtain ⟨hs, hsum⟩ := intersectionNumber_sum_smul (sX := sX) i hdim (fun j => π (r j)) L hL
    Finset.univ
  have h1 := MMP.Fourfold.intersectionNumber_smul sX i hdim H hH (π 1)
    (by rwa [key])
  rw [MMP.Fourfold.intersectionNumber_congr sX i hdim _ hs key, hsum] at h1
  rw [map_sub, map_sum, hcast]
  simp only [hzs]
  rw [mul_comm, ← h1, sub_eq_zero]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  have := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample `ℚ`-Cartier `ℚ`-divisor has positive intersection number with every proper curve
contracted by `f`. -/
theorem intersectionNumber_pos_of_isRelativelyAmple [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {H : QDivisor X} (hH : H.IsQCartier)
    (hHa : IsRelativelyAmple f (QDivisor.toRDivisor H)) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    0 < H.intersectionNumber k sX C.ι C.dim_le hH := by
  obtain ⟨m, r, L, hm, hr, hL, hHL⟩ := hHa
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  have h := intersectionNumber_eq_sum_of_toRDivisor_eq (sX := sX) C.ι C.dim_le H hH r L hLc hHL
  have hpos : (0 : ℝ) < ∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hLc j) := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) Finset.univ_nonempty
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) C hC
  rw [← h] at hpos
  exact_mod_cast hpos

omit [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
/-- **Numerical proportionality in a one-dimensional `N¹(X/Z)`.** If `N¹(X/Z)` is
one-dimensional and `δH` is not numerically trivial on some contracted curve, then every
`ℝ`-Cartier divisor `δL` is numerically `f`-equivalent to a multiple `c • δH`. -/
theorem exists_intersectionNumber_eq_mul_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    (δH δL : KCartierDivisor ℝ X) {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : (C₀.cycle ℝ).intersectionNumber δH ≠ 0) :
    ∃ c : ℝ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.cycle ℝ).intersectionNumber δL = c * (C.cycle ℝ).intersectionNumber δH := by
  have hne : (Submodule.Quotient.mk δH : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀ (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δL)
  have hmem : δL - c • δH ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  refine ⟨c, fun C hC => ?_⟩
  have := (mem_relativeNumericallyTrivialDivisors sX f).mp hmem C hC
  simp only [OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul] at this ⊢
  linarith

/-- If `N¹(X/Z)` is one-dimensional, some proper curve is contracted by `f`. -/
private theorem exists_isContractedBy_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  haveI := Module.finite_of_finrank_eq_succ hfin
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp (by rw [hfin]; exact one_pos)
  obtain ⟨δ, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors] at hv
  push Not at hv
  obtain ⟨C, hC, -⟩ := hv
  exact ⟨C, hC⟩

end RelativePicardNumberOne

/-- A Weil divisor whose divisorial sheaf is the pull-back of the divisorial sheaf of a Cartier
divisor is Cartier. -/
private theorem isCartier_of_iso_pullback {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    (f : X ⟶ Z) {D : Divisor X}
    {M : Divisor Z} (hM : M.IsCartier)
    (e : D.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M.divisorialSheaf) :
    D.IsCartier := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  intro x
  obtain ⟨U, hxU, ψ, hψ⟩ :=
    MMP.Fourfold.exists_isLocalEquation_preimage_of_iso_pullback f M.divisorialSheaf e (f x)
  exact ⟨f ⁻¹ᵁ U, hxU, ψ, hψ⟩

/-- The birational transform of divisors commutes with any additive change of coefficients. -/
private theorem transformDivisor_mapCoeffsAddMonoidHom {X Y : Scheme.{u}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (φ : X.RationalMap Y) (g : R →+ S)
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{u}} (Q : MMP.Mori.PrimeDivisor Z) (r : R),
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (Finsupp.single Q r) = Finsupp.single Q (g r) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero g)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, RationalMap.transformDivisor_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- The birational transform of divisors commutes with regarding a divisor as a
`ℚ`-divisor. -/
theorem transformDivisor_toQDivisor {X Y : Scheme.{u}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom φ (Int.castAddHom ℚ) D

/-! ### Prime divisors across the flip -/

section Transport

/-- If `f` is an isomorphism over `W` and `f y ∈ W`, then `f` preserves the coheight of `y`. -/
theorem coheight_map_eq_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (W : Z.Opens) [IsIso (f ∣_ W)] {y : Y} (hy : f y ∈ W) :
    Order.coheight (f y) = Order.coheight y := by
  have hη : y ∈ f ⁻¹ᵁ W := hy
  have e1 : (f ∣_ W) ⟨y, hη⟩ = ⟨f y, hy⟩ :=
    Subtype.ext (morphismRestrict_base_coe f W ⟨y, hη⟩)
  have c1 := coheight_eq_of_isOpenImmersion (x := (⟨f y, hy⟩ : W.toScheme)) W.ι
  have c2 := coheight_eq_of_isOpenImmersion (x := (⟨y, hη⟩ : (f ⁻¹ᵁ W).toScheme)) (f ∣_ W)
  have c3 := coheight_eq_of_isOpenImmersion (x := (⟨y, hη⟩ : (f ⁻¹ᵁ W).toScheme)) (f ⁻¹ᵁ W).ι
  rw [e1] at c2
  exact c1.trans (c2.trans c3.symm)

/-- If a separated morphism `f` from an irreducible scheme restricts to an isomorphism from a
nonempty open `U` onto an open `W`, then `U` is all of `f⁻¹(W)`. -/
theorem preimage_le_of_isIso_resLE {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsSeparated f]
    [IrreducibleSpace Y] (U : Y.Opens) (W : Z.Opens) (h : U ≤ f ⁻¹ᵁ W)
    [IsIso (f.resLE W U h)] (hU : (U : Set Y).Nonempty) : f ⁻¹ᵁ W ≤ U := by
  let j : U.toScheme ⟶ (f ⁻¹ᵁ W).toScheme := Y.homOfLE h
  have hj : j ≫ f ∣_ W = f.resLE W U h := rfl
  let s := inv (f.resLE W U h) ≫ j
  have hs : s ≫ f ∣_ W = 𝟙 _ := by simp [s, hj]
  have : IsClosedImmersion (s ≫ f ∣_ W) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (f ∣_ W)
  have hrange : Set.range j ⊆ Set.range s := by
    rintro _ ⟨u, rfl⟩
    refine ⟨f.resLE W U h u, ?_⟩
    change (f.resLE W U h ≫ s) u = j u
    simp [s]
  have hclopen : IsClopen (Set.range j) :=
    ⟨by
      rw [show Set.range j = Set.range s from
        hrange.antisymm (by rintro _ ⟨w, rfl⟩; exact ⟨_, rfl⟩)]
      exact s.isClosedEmbedding.isClosed_range,
      j.isOpenEmbedding.isOpen_range⟩
  obtain ⟨x₀, hx₀⟩ := hU
  have : IrreducibleSpace (f ⁻¹ᵁ W : Set Y) := Subtype.irreducibleSpace
    ⟨⟨x₀, h hx₀⟩, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset
      (f ⁻¹ᵁ W).isOpen (Set.subset_univ _)⟩
  have : PreconnectedSpace (f ⁻¹ᵁ W).toScheme :=
    inferInstanceAs (PreconnectedSpace (f ⁻¹ᵁ W : Set Y))
  have huniv : Set.range j = Set.univ := by
    refine (isClopen_iff.mp hclopen).resolve_left ?_
    exact Set.Nonempty.ne_empty ⟨_, ⟨x₀, hx₀⟩, rfl⟩
  intro x hx
  obtain ⟨u, hu⟩ := huniv.ge (Set.mem_univ (⟨x, hx⟩ : (f ⁻¹ᵁ W).toScheme))
  have hxu : x = u.1 := (congrArg Subtype.val hu).symm.trans (Scheme.homOfLE_apply h u)
  exact hxu ▸ u.2

/-- The generic point of a prime divisor does not lie in a closed subset of codimension `≥ 2`. -/
theorem genericPoint_notMem_of_two_le_closedsCodimension {Y : Scheme.{u}}
    (V : TopologicalSpace.Closeds Y) (hV : 2 ≤ closedsCodimension V)
    (D : AlgebraicGeometry.PrimeDivisor Y) : D.genericPoint ∉ V := by
  intro hD
  have h2 := MMP.Mori.le_closedsCodimension_iff.mp hV
    (TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint)
    (closure_minimal (Set.singleton_subset_iff.mpr hD) V.isClosed)
  rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
      D.genericPoint = (irreducibleSetEquivPoints (α := Y)).symm D.genericPoint from rfl,
    Order.coheight_orderIso, D.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- A small contraction `f : Y ⟶ Z` is an isomorphism over an open `W` of `Z` containing the
generic point of every prime divisor of `Z` and the image of the generic point of every prime
divisor of `Y`. -/
theorem exists_isIso_morphismRestrict_of_isSmall {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ Z}
    (hf : IsSmall k sZ sY f) :
    ∃ W : Z.Opens, IsIso (f ∣_ W) ∧
      (∀ D : AlgebraicGeometry.PrimeDivisor Y, f D.genericPoint ∈ W) ∧
      ∀ Q : AlgebraicGeometry.PrimeDivisor Z, Q.genericPoint ∈ W := by
  have := hf.isVariety_source.toIsIntegral
  have := hf.isProper
  obtain ⟨V₀, W₀, hV₀, hW₀, h₀, hiso⟩ := hf.exists_isIso
  have hle := preimage_le_of_isIso_resLE f V₀.compl W₀.compl h₀
    (nonempty_compl_of_two_le_closedsCodimension V₀ hV₀)
  have key : ∀ (U : Y.Opens) (hU : U = f ⁻¹ᵁ W₀.compl) (h : U ≤ f ⁻¹ᵁ W₀.compl),
      IsIso (f.resLE W₀.compl U h) → IsIso (f ∣_ W₀.compl) := by
    rintro _ rfl h hi
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact ⟨W₀.compl, key _ (le_antisymm h₀ hle) h₀ hiso,
    fun D ↦ h₀ (genericPoint_notMem_of_two_le_closedsCodimension V₀ hV₀ D),
    fun Q ↦ genericPoint_notMem_of_two_le_closedsCodimension W₀ hW₀ Q⟩

/-- If `f` is an isomorphism over `W` and sends the generic point of a prime divisor `D` into `W`,
then `f(η_D)` is the generic point of a prime divisor. -/
theorem exists_primeDivisor_map_genericPoint_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (W : Z.Opens) [IsIso (f ∣_ W)] (D : AlgebraicGeometry.PrimeDivisor Y)
    (hD : f D.genericPoint ∈ W) :
    ∃ Q : AlgebraicGeometry.PrimeDivisor Z, f D.genericPoint = Q.genericPoint := by
  have hcoh : Order.coheight (f D.genericPoint) = 1 := by
    rw [coheight_map_eq_of_isIso_morphismRestrict f W hD, D.coheight_genericPoint]
  exact ⟨.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm⟩

/-- A small contraction sends the generic point of every prime divisor to the generic point of a
prime divisor. -/
theorem exists_primeDivisor_map_genericPoint_eq_of_isSmall {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ Z}
    (hf : IsSmall k sZ sY f) (D : AlgebraicGeometry.PrimeDivisor Y) :
    ∃ Q : AlgebraicGeometry.PrimeDivisor Z, f D.genericPoint = Q.genericPoint := by
  obtain ⟨W, hW, hWD, -⟩ := exists_isIso_morphismRestrict_of_isSmall hf
  exact exists_primeDivisor_map_genericPoint_eq f W D (hWD D)

/-- **Push-forward along a birational morphism, coefficientwise.** If `f : Y ⟶ Z` is a proper
birational morphism of normal varieties sending the generic point of the prime divisor `P` to that
of `Q`, the coefficient of `Q` in `f_* D` is the coefficient of `P` in `D`. -/
theorem transformDivisor_apply_of_map_genericPoint_eq {k : Type u} [Field k]
    {Y Z : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ) {f : Y ⟶ Z}
    (hY : IsNormalVariety k (f ≫ sZ)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : AlgebraicGeometry.PrimeDivisor Y} {Q : AlgebraicGeometry.PrimeDivisor Z}
    (hPQ : f P.genericPoint = Q.genericPoint) (D : Divisor Y) :
    MMP.Mori.RationalMap.transformDivisor (X := Y) f.toRationalMap D Q = D P := by
  classical
  have : IsIntegral Y := hY.1.toIsIntegral
  have := hZ.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal sZ
  obtain ⟨E, -, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hY hf Q
  have hEP : E = P := by
    have h1 := hE (Finsupp.single P (1 : ℤ))
    rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hPQ),
      Finsupp.single_eq_same, Finsupp.single_apply] at h1
    by_contra h
    simp [Ne.symm h] at h1
  rw [hE, hEP]

/-- **The birational transform under a modification of small contractions, coefficientwise.**
Let `φ : X ⟶ Z` and `φ⁺ : X' ⟶ Z` be small contractions of normal varieties and `θ : X ⤏ X'` a
rational map over `Z`. If `φ⁺` sends the generic point of the prime divisor `P'` to that of `Q`,
the coefficient of `P'` in `θ_* A` is the coefficient of `Q` in `φ_* A`. -/
theorem transformDivisor_apply_of_isOver {k : Type u} [Field k]
    {X X' Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian X'] [IsNormal X'] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    {φ : X ⟶ Z} {φp : X' ⟶ Z} (hφ : IsSmall k sZ sX φ) (hφp : IsSmall k sZ sX' φp)
    {θ : X.RationalMap X'} (hθ : θ.compHom φp = φ.toRationalMap)
    {P' : AlgebraicGeometry.PrimeDivisor X'} {Q : AlgebraicGeometry.PrimeDivisor Z}
    (hQ : φp P'.genericPoint = Q.genericPoint) (A : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor θ A P' =
      MMP.Mori.RationalMap.transformDivisor (X := X) φ.toRationalMap A Q := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  have := hX'.1.toIsSeparated
  have : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_terminal sX'
  have : IsProper φ := hφ.isProper
  have : IsProper φp := hφp.isProper
  have hYφ : IsNormalVariety k (φ ≫ sZ) := by rwa [hφ.comp_eq]
  have hYφp : IsNormalVariety k (φp ≫ sZ) := by rwa [hφp.comp_eq]
  have hbφ := hφ.isBirationalMorphism
  have hbφp := hφp.isBirationalMorphism
  obtain ⟨Wφ, hWφ, hWφD, -⟩ := exists_isIso_morphismRestrict_of_isSmall hφ
  obtain ⟨Wp, hWp, -, hWpQ⟩ := exists_isIso_morphismRestrict_of_isSmall hφp
  obtain ⟨E, hEQ, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hYφ hbφ Q
  have hd : Dense ((φ ⁻¹ᵁ Wp : X.Opens) : Set X) :=
    (φ ⁻¹ᵁ Wp).isOpen.dense ⟨E.genericPoint, show φ E.genericPoint ∈ Wp from hEQ ▸ hWpQ Q⟩
  let g' : X.PartialMap X' := Scheme.PartialMap.mk (φ ⁻¹ᵁ Wp) hd
    ((φ ∣_ Wp ≫ inv (φp ∣_ Wp)) ≫ (φp ⁻¹ᵁ Wp).ι)
  have hg' : g'.toRationalMap = θ :=
    toRationalMap_eq_of_comp_morphismRestrict_eq hd (by simp) hθ
  have key : g'.hom ≫ φp = (φ ⁻¹ᵁ Wp).ι ≫ φ := by
    change ((φ ∣_ Wp ≫ inv (φp ∣_ Wp)) ≫ (φp ⁻¹ᵁ Wp).ι) ≫ φp = _
    simp only [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hcomp : ∀ x : (φ ⁻¹ᵁ Wp).toScheme, φp (g'.hom x) = φ x.1 := fun x =>
    congrArg (fun g : (φ ⁻¹ᵁ Wp).toScheme ⟶ Z ↦ g x) key
  have hD : ∀ D : AlgebraicGeometry.PrimeDivisor X, ∃ Q' : AlgebraicGeometry.PrimeDivisor Z,
      φ D.genericPoint = Q'.genericPoint ∧ ∃ P'' : AlgebraicGeometry.PrimeDivisor X',
        MMP.Mori.RationalMap.transformPrimeDivisor θ D = some P'' ∧
          φp P''.genericPoint = Q'.genericPoint := by
    intro D
    obtain ⟨Q', hQ'⟩ := exists_primeDivisor_map_genericPoint_eq φ Wφ D (hWφD D)
    have hDU : D.genericPoint ∈ g'.domain :=
      show φ D.genericPoint ∈ Wp from hQ' ▸ hWpQ Q'
    have hy : φp (g'.hom ⟨D.genericPoint, hDU⟩) = Q'.genericPoint := (hcomp _).trans hQ'
    have hcy : Order.coheight (g'.hom ⟨D.genericPoint, hDU⟩) = 1 := by
      rw [← coheight_map_eq_of_isIso_morphismRestrict φp Wp
        (show φp (g'.hom ⟨D.genericPoint, hDU⟩) ∈ Wp from hy ▸ hWpQ Q'), hy,
        Q'.coheight_genericPoint]
    refine ⟨Q', hQ', .ofCoheightOne _ hcy, transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg'
      hDU (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy), ?_⟩
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  obtain ⟨Q₁, hQ₁, P'', hP'', hP''Q₁⟩ := hD E
  have hQ₁Q : Q₁ = Q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hQ₁.symm.trans hEQ)
  rw [hQ₁Q] at hP''Q₁
  have hPP : P'' = P' := by
    have h1 := transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hbφp hP''Q₁
      (Finsupp.single P' (1 : ℤ))
    rw [transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hbφp hQ, Finsupp.single_eq_same,
      Finsupp.single_apply] at h1
    by_contra h
    simp [Ne.symm h] at h1
  rw [hPP] at hP''
  rw [hE A]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP'' (fun D' hD' => ?_) A
  obtain ⟨Q', hQ', P₃, hP₃, hP₃Q⟩ := hD D'
  rw [hD'] at hP₃
  cases Option.some.inj hP₃
  have hQQ : Q' = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP₃Q.symm.trans hQ)
  rw [hQQ] at hQ'
  have h1 := transformDivisor_apply_of_map_genericPoint_eq hZ hYφ hbφ hQ'
    (Finsupp.single E (1 : ℤ))
  rw [hE, Finsupp.single_eq_same, Finsupp.single_apply] at h1
  by_contra h
  simp [Ne.symm h] at h1

/-- If a separated morphism `f` from an irreducible scheme is an isomorphism off closed subsets
whose source one has codimension `≥ 2`, the fibre of `f` through the generic point of a prime
divisor is that point alone. -/
theorem subsingleton_preimage_genericPoint {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsSeparated f] [IrreducibleSpace Y] (V : Closeds Y) (W : Closeds Z)
    (hV : 2 ≤ closedsCodimension V) (h : V.compl ≤ f ⁻¹ᵁ W.compl)
    (hiso : IsIso (f.resLE W.compl V.compl h)) (D : AlgebraicGeometry.PrimeDivisor Y) :
    Subsingleton (f ⁻¹' {f D.genericPoint}) := by
  have hη : D.genericPoint ∈ V.compl := genericPoint_notMem_of_two_le_closedsCodimension V hV D
  have hle := preimage_le_of_isIso_resLE f V.compl W.compl h ⟨_, hη⟩
  suffices ∀ y, f y = f D.genericPoint → y = D.genericPoint from
    ⟨fun a b ↦ Subtype.ext ((this a.1 a.2).trans (this b.1 b.2).symm)⟩
  intro y hy
  have hy' : y ∈ V.compl := hle (show f y ∈ W.compl from hy ▸ h hη)
  refine congrArg Subtype.val ((f.resLE W.compl V.compl h).isOpenEmbedding.injective
    (a₁ := ⟨y, hy'⟩) (a₂ := ⟨_, hη⟩) (Subtype.ext ?_))
  rwa [Scheme.Hom.coe_resLE_apply, Scheme.Hom.coe_resLE_apply]

/-- A partial map of prime divisors that is everywhere defined, by `ψ`, pushes divisors forward
along `ψ`. -/
theorem mapPrimeDivisors_eq_mapDomain {R : Type*} [AddCommMonoid R] {X Y : Scheme.{u}}
    {φ : AlgebraicGeometry.PrimeDivisor X → Option (AlgebraicGeometry.PrimeDivisor Y)}
    {ψ : AlgebraicGeometry.PrimeDivisor X → AlgebraicGeometry.PrimeDivisor Y}
    (h : ∀ D, φ D = some (ψ D)) (B : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ B = Finsupp.mapDomain ψ B := by
  induction B using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, h, h', Finsupp.mapDomain_add]
  | single D r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some (h D), Finsupp.mapDomain_single]

/-- A rational map represented by an open immersion `g'` whose domain contains the generic point of
every prime divisor induces an injective map `ψ` of prime divisors: its transform, carrying the
generic point of `D` to its image under `g'`. -/
theorem exists_injective_transformPrimeDivisor {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    [IsOpenImmersion g'.hom] (hg' : g'.toRationalMap = φ)
    (hdom : ∀ D : AlgebraicGeometry.PrimeDivisor X, D.genericPoint ∈ g'.domain) :
    ∃ ψ : AlgebraicGeometry.PrimeDivisor X → AlgebraicGeometry.PrimeDivisor Y,
      Function.Injective ψ ∧ ∀ D, RationalMap.transformPrimeDivisor φ D = some (ψ D) ∧
        (ψ D).genericPoint = g'.hom ⟨D.genericPoint, hdom D⟩ := by
  have hcoh (D : AlgebraicGeometry.PrimeDivisor X) :
      Order.coheight (g'.hom ⟨D.genericPoint, hdom D⟩) = 1 :=
    (coheight_eq_of_isOpenImmersion g'.hom).trans
      ((coheight_eq_of_isOpenImmersion g'.domain.ι).symm.trans D.coheight_genericPoint)
  have hψη (D) := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ (hcoh D)
  refine ⟨fun D ↦ .ofCoheightOne _ (hcoh D), fun D₁ D₂ h ↦ ?_, fun D ↦
    ⟨transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' (hdom D) (hψη D), hψη D⟩⟩
  have := congrArg AlgebraicGeometry.PrimeDivisor.genericPoint h
  rw [hψη, hψη] at this
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (congrArg Subtype.val (g'.hom.isOpenEmbedding.injective this))

/-- In a sequence of log flips, the transform under the flip map `θ_i` is a bijection `ψ` from the
prime divisors of `X_i` to those of `X_{i+1}`. -/
private theorem exists_bijective_transformPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    ∃ ψ : AlgebraicGeometry.PrimeDivisor (S.model i).1 →
        AlgebraicGeometry.PrimeDivisor (S.model (i + 1)).1,
      Function.Bijective ψ ∧
        ∀ D, RationalMap.transformPrimeDivisor (S.flipMap i) D = some (ψ D) := by
  obtain ⟨hV, hpre, hpre', hd, e, -, hrep⟩ := S.exists_iso_compl_exceptionalLocus_flipMap i hi
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := (S.isNormalVariety_model i hi').1.toIsIntegral
  have := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
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
  obtain ⟨V₀, W₀, hV₀, -, h₀, hiso⟩ := hsmall.exists_isIso
  obtain ⟨V₁, W₁, hV₁, -, h₁, hiso₁⟩ := hsmall'.exists_isIso
  let g' := Scheme.PartialMap.mk (S.contraction i ⁻¹ᵁ ⟨_, hV⟩) hd
    (e.hom ≫ (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι)
  have : IsOpenImmersion g'.hom := inferInstanceAs (IsOpenImmersion (e.hom ≫ _))
  have hdom (D : AlgebraicGeometry.PrimeDivisor (S.model i).1) : D.genericPoint ∈ g'.domain :=
    (Set.ext_iff.mp hpre D.genericPoint).mpr fun ⟨_, _, _, hdim⟩ ↦ by
      have := subsingleton_preimage_genericPoint _ V₀ W₀ hV₀ h₀ hiso D
      exact hdim.not_ge (topologicalKrullDim_zero_of_discreteTopology _)
  have hdom' (E : AlgebraicGeometry.PrimeDivisor (S.model (i + 1)).1) :
      E.genericPoint ∈ S.flip i ⁻¹ᵁ ⟨_, hV⟩ :=
    (Set.ext_iff.mp hpre' E.genericPoint).mpr fun ⟨_, _, _, hdim⟩ ↦ by
      have := subsingleton_preimage_genericPoint _ V₁ W₁ hV₁ h₁ hiso₁ E
      exact hdim.not_ge (topologicalKrullDim_zero_of_discreteTopology _)
  obtain ⟨ψ, hψinj, hψ⟩ := exists_injective_transformPrimeDivisor g' hrep hdom
  refine ⟨ψ, ⟨hψinj, fun E ↦ ?_⟩, fun D ↦ (hψ D).1⟩
  let y : (S.flip i ⁻¹ᵁ ⟨_, hV⟩).toScheme := ⟨E.genericPoint, hdom' E⟩
  let x := e.inv y
  have hxy : e.hom x = y := by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  have hx : Order.coheight x.1 = 1 := by
    have c1 := coheight_eq_of_isOpenImmersion (S.contraction i ⁻¹ᵁ ⟨_, hV⟩).ι (x := x)
    have c2 := coheight_eq_of_isOpenImmersion e.hom (x := x)
    have c3 := coheight_eq_of_isOpenImmersion (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι (x := y)
    rw [hxy] at c2
    exact c1.trans (c2.symm.trans (c3.symm.trans E.coheight_genericPoint))
  refine ⟨.ofCoheightOne _ hx, AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_⟩
  rw [(hψ _).2]
  have hxD : (⟨(AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx).genericPoint, hdom _⟩ :
      g'.domain.toScheme) = x :=
    Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx)
  rw [hxD]
  change (S.flip i ⁻¹ᵁ ⟨_, hV⟩).ι (e.hom x) = E.genericPoint
  rw [hxy]
  rfl

/-- In a sequence of log flips, every Weil divisor `G⁺` on `X_{i+1}` is the transform
`θ_{i*} G` of a Weil divisor `G` on `X_i`. -/
private theorem exists_transformDivisor_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (Gp : Divisor (S.model (i + 1)).1) :
    ∃ G : Divisor (S.model i).1,
      RationalMap.transformDivisor (S.flipMap i) (Divisor.toQDivisor G) =
        Divisor.toQDivisor Gp := by
  obtain ⟨ψ, hψb, hψ⟩ := exists_bijective_transformPrimeDivisor S i hi
  let σ := Equiv.ofBijective ψ hψb
  refine ⟨Finsupp.mapDomain σ.symm Gp, ?_⟩
  have h1 (G : Divisor (S.model i).1) :
      RationalMap.transformDivisor (S.flipMap i) G = Finsupp.mapDomain ψ G :=
    mapPrimeDivisors_eq_mapDomain hψ G
  have h2 : ψ ∘ σ.symm = id := funext σ.apply_symm_apply
  change RationalMap.transformDivisor (S.flipMap i)
      (DivisorWithCoeffs.mapCoeffsAddMonoidHom (Int.castAddHom ℚ) _) =
    DivisorWithCoeffs.mapCoeffsAddMonoidHom (Int.castAddHom ℚ) Gp
  rw [transformDivisor_mapCoeffsAddMonoidHom, h1, ← Finsupp.mapDomain_comp, h2,
    Finsupp.mapDomain_id]

end Transport

/-- For the `i`-th flip of a sequence of log flips, `Z_i`, `X_i` and `X_{i+1}` are normal
varieties, `φ_i` and `φ_i⁺` are small, `θ_i` lies over `Z_i`, and `dim Z_i = 3`. -/
theorem flip_data {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    IsNormalVariety k (S.baseStr i) ∧ IsNormalVariety k (S.model i).2.1 ∧
      IsNormalVariety k (S.model (i + 1)).2.1 ∧
      IsSmall k (S.baseStr i) (S.model i).2.1 (S.contraction i) ∧
      IsSmall k (S.baseStr i) (S.model (i + 1)).2.1 (S.flip i) ∧
      (S.flipMap i).compHom (S.flip i) = (S.contraction i).toRationalMap ∧
      topologicalKrullDim (S.base i) = (3 : ℕ) := by
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hF := S.isFlip i hi
  have hsm := S.isSmall i hi
  refine ⟨hF.isNormalVariety_target, S.isNormalVariety_model i hi',
    S.isNormalVariety_model (i + 1) hi, hsm, hF.isSmall, hF.isModificationOf.2, ?_⟩
  rw [← hsm.dim_eq, S.dim_model i hi']
  rfl

/-- Transport of a linear equivalence with a pull-back across the flip: if
`𝒪_{X_i}(L) ≅ φ_i^* 𝒪_{Z_i}(M)` with `M` Cartier, then
`𝒪_{X_{i+1}}(θ_{i*} L) ≅ φ_i⁺^* 𝒪_{Z_i}(M)`. -/
theorem nonempty_divisorialSheaf_transformDivisor_iso_pullback_flip
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
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
    Nonempty (Divisor.divisorialSheaf
        (MMP.Mori.RationalMap.transformDivisor (S.flipMap i) L) ≅
        (Scheme.Modules.pullback (S.flip i)).obj M.divisorialSheaf) := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  obtain ⟨hZ, hX, hX', hsm, hsm', hθ, -⟩ := flip_data S i hi
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
  have : IsDominant (S.contraction i) := hb.isDominant
  have : IsDominant (S.flip i) := hb'.isDominant
  have hYφ : IsNormalVariety k (S.contraction i ≫ S.baseStr i) := by rwa [hsm.comp_eq]
  have hYφp : IsNormalVariety k (S.flip i ≫ S.baseStr i) := by rwa [hsm'.comp_eq]
  obtain ⟨e⟩ := e
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (S.contraction i) M
  obtain ⟨e₁⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM (S.contraction i) hB
  obtain ⟨χ, hχ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ e₁.symm)
  obtain ⟨h, hh, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hb χ
  have hB' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (S.flip i) M
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM (S.flip i) hB'
  have hh' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (S.flip i)
    (MMP.Mori.principalDivisor h)
  have hL : L = M.pullback hM hB +
      MMP.Mori.principalDivisor (MMP.Mori.pullbackRationalFunction (S.contraction i) h hh) := by
    rw [← hχ]; abel
  have hlin : Divisor.LinearlyEquivalent
      (MMP.Mori.RationalMap.transformDivisor (S.flipMap i) L) (M.pullback hM hB') := by
    refine ⟨MMP.Mori.pullbackRationalFunction (S.flip i) h hh', Finsupp.ext fun P' => ?_⟩
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall hsm' P'
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    rw [transformDivisor_apply_of_isOver hZ hX hX' hsm hsm' hθ hQ,
      ← transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hb' hQ (M.pullback hM hB'),
      ← transformDivisor_apply_of_map_genericPoint_eq hZ hYφp hb' hQ,
      MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hYφp hb' h hh',
      MMP.Positivity.transformDivisor_of_isPullback_divisor hZ hYφp hb' hM
        (Divisor.isPullback_pullback hM hB'),
      hL, map_add, MMP.Positivity.transformDivisor_of_isPullback_divisor hZ hYφ hb hM
        (Divisor.isPullback_pullback hM hB),
      MMP.Positivity.transformDivisor_principalDivisor_pullback hZ hYφ hb h hh,
      Finsupp.coe_add, Pi.add_apply]
    abel
  exact ⟨hlin.divisorialSheafIso ≪≫ e₂⟩

/-- `ρ(X_i/Z_i) = 1`: the space of numerical classes of `X_i` over `Z_i` is a line. -/
private theorem finrank_relativeNumericalDivisorClasses_contraction
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
    Module.finrank ℝ (RelativeNumericalDivisorClasses (S.model i).2.1 (S.contraction i)) = 1 := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  exact Module.finrank_eq_of_rank_eq (by
    rw [Cardinal.toENat_eq_one.mp
      (S.isExtremalRayContraction i hi).isNegativeExtremalContraction.relativePicardNumber_eq_one]
    rfl)

/-- `(K_{X_i} + B_i) · C < 0` for every proper curve `C` contracted by `φ_i`, because
`-(K_{X_i} + B_i)` is `φ_i`-ample. -/
private theorem intersectionNumber_logCanonical_neg
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (C : ProperCurve (S.model i).2.1) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
    ∀ hKB : (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).IsQCartier,
      C.IsContractedBy (S.contraction i) →
      (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).intersectionNumber
        k (S.model i).2.1 C.ι C.dim_le hKB < 0 := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  intro hKB hC
  have hneg := (S.isExtremalRayContraction i hi).isNegativeExtremalContraction
  have : IsIntegral (S.model i).1 := hneg.isNormalVariety_source.1.toIsIntegral
  set KB := Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2
  have hH : ((-1 : ℚ) • KB).IsQCartier := isQCartier_smul hKB (-1)
  have hHa : IsRelativelyAmple (S.contraction i) (QDivisor.toRDivisor ((-1 : ℚ) • KB)) := by
    have := hneg.isRelativelyAntiAmple
    rwa [neg_one_smul, map_neg, map_add, QDivisor.toRDivisor_toQDivisor]
  have hHC := intersectionNumber_pos_of_isRelativelyAmple (S.contraction i) hH hHa C hC
  rw [MMP.Fourfold.intersectionNumber_smul (S.model i).2.1 C.ι C.dim_le KB hKB (-1) hH] at hHC
  linarith

/-- If `L = n (G - μ (K_{X_i} + B_i))` is Cartier with `n > 0`, and `G · C = μ (K + B) · C` for a
flipping curve `C`, then `L` has degree zero on every curve contracted by `φ_i`. -/
theorem degreeOn_eq_zero_of_isContractedBy
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (G : QDivisor (S.model i).1) (C : ProperCurve (S.model i).2.1)
    (hC : IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i)
      (closure {C.point}))
    (μ : ℚ)
    (hGC : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
      ∃ (hG : G.IsQCartier)
        (hKB : (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).IsQCartier),
        G.intersectionNumber k (S.model i).2.1 C.ι C.dim_le hG =
          μ * (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).intersectionNumber
            k (S.model i).2.1 C.ι C.dim_le hKB) (n : ℕ) (hn : 0 < n) (L : Divisor (S.model i).1)
    (hL : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      L.IsCartier)
    (hLG : Divisor.toQDivisor L = (n : ℚ) • (G -
      μ • (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2))) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
    ∀ C' : ProperCurve (S.model i).2.1, C'.IsContractedBy (S.contraction i) →
      L.degreeOn k (S.model i).2.1 C'.ι C'.dim_le hL = 0 := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  have : IsIntegral (S.model i).1 := (S.isExtremalRayContraction i
    hi).isNegativeExtremalContraction.isNormalVariety_source.1.toIsIntegral
  -- `C` is contracted by `φ_i`
  have hCc : C.IsContractedBy (S.contraction i) := by
    obtain ⟨-, -, -, -, z, -, hmax, -⟩ := hC
    intro x hx
    rw [hmax.prop.2 hx, hmax.prop.2 (subset_closure rfl)]
  obtain ⟨hG, hKB, hGCeq⟩ := hGC
  set KB := Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2
  -- `L · C = 0`
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hLq := QDivisor.isQCartier_toQDivisor hL
  have hLn := isQCartier_smul hLq (1 / n : ℚ)
  have hKBμ := isQCartier_smul hKB μ
  have hGeq : G = (1 / n : ℚ) • Divisor.toQDivisor L + μ • KB := by
    rw [hLG, smul_smul, one_div, inv_mul_cancel₀ hn', one_smul, sub_add_cancel]
  have hLC : L.degreeOn k (S.model i).2.1 C.ι C.dim_le hL = 0 := by
    have h := MMP.Fourfold.intersectionNumber_congr (S.model i).2.1 C.ι C.dim_le hG
      (hLn.add hKBμ) hGeq
    rw [QDivisor.intersectionNumber_add' k _ C.ι C.dim_le _ _ hLn hKBμ,
      MMP.Fourfold.intersectionNumber_smul _ C.ι C.dim_le _ hLq _ hLn,
      MMP.Fourfold.intersectionNumber_smul _ C.ι C.dim_le _ hKB _ hKBμ,
      QDivisor.intersectionNumber_toQDivisor k _ C.ι C.dim_le _ hL, hGCeq] at h
    have : (1 / n : ℚ) * (L.degreeOn k (S.model i).2.1 C.ι C.dim_le hL : ℚ) = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp this).resolve_left (by positivity)
  have hKBC := intersectionNumber_logCanonical_neg S i hi C hKB hCc
  obtain ⟨δK, hδK⟩ := exists_kCartierDivisor_intersectionNumber_eq (S.model i).2.1 KB hKB
  obtain ⟨E, hE⟩ := exists_cartierDivisor_degree_eq (S.model i).2.1 L hL
  obtain ⟨c, hc⟩ := exists_intersectionNumber_eq_mul_of_finrank_eq_one (S.contraction i)
    (finrank_relativeNumericalDivisorClasses_contraction S i hi) δK
    (KCartierDivisor.ofCartier ℝ E) hCc (by rw [hδK]; exact_mod_cast hKBC.ne)
  have hc0 : c = 0 := by
    have h := hc C hCc
    rw [hE, hLC, hδK] at h
    push_cast at h
    exact (mul_eq_zero.mp h.symm).resolve_right (by exact_mod_cast hKBC.ne)
  intro C' hC'
  have h := hc C' hC'
  rw [hE, hc0, zero_mul] at h
  exact_mod_cast h

/-- Descent on `X_i`: there are `m > 0` with `m μ ∈ ℤ`, an integral divisor
`L = m (G - μ (K_{X_i} + B_i))` and a Cartier divisor `M` on `Z_i` with
`𝒪_{X_i}(L) ≅ φ_i^* 𝒪_{Z_i}(M)`. -/
theorem exists_smul_sub_linearEquiv_pullback_contraction
    {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (hQ : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      MMP.Fourfold.IsQFactorial (S.model i).2.1)
    (G : QDivisor (S.model i).1) (C : ProperCurve (S.model i).2.1)
    (hC : IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i)
      (closure {C.point}))
    (μ : ℚ)
    (hGC : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
      ∃ (hG : G.IsQCartier)
        (hKB : (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).IsQCartier),
        G.intersectionNumber k (S.model i).2.1 C.ι C.dim_le hG =
          μ * (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).intersectionNumber
            k (S.model i).2.1 C.ι C.dim_le hKB) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.isLocallyNoetherian_base i
    haveI := S.isNormal_base i
    ∃ m : ℕ, 0 < m ∧ (∃ a : ℤ, (m : ℚ) * μ = a) ∧
      ∃ (L : Divisor (S.model i).1) (M : Divisor (S.base i)), M.IsCartier ∧
        Divisor.toQDivisor L = (m : ℚ) • (G -
          μ • (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2)) ∧
        Nonempty (L.divisorialSheaf ≅
          (Scheme.Modules.pullback (S.contraction i)).obj M.divisorialSheaf) := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_base i
  have := S.isNormal_base i
  obtain ⟨N, hN, L₀, hL₀⟩ := MMP.Flips.exists_pos_smul_eq_toQDivisor
    (G - μ • (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2))
  obtain ⟨m₁, hm₁, hc⟩ := hQ.2 ((μ.den : ℤ) • L₀)
  set L₂ := (m₁ : ℤ) • (μ.den : ℤ) • L₀
  have hL₂ : Divisor.toQDivisor L₂ = ((m₁ * μ.den * N : ℕ) : ℚ) • (G -
      μ • (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2)) := by
    simp only [L₂, map_zsmul, hL₀, smul_smul, ← Int.cast_smul_eq_zsmul ℚ]
    push_cast
    ring_nf
  obtain ⟨m₂, hm₂, M, hM, ⟨e⟩⟩ := (S.isExtremalRayContraction i hi).exists_pullback L₂ hc
    (degreeOn_eq_zero_of_isContractedBy S i hi G C hC μ hGC _
      (by positivity) L₂ hc hL₂)
  refine ⟨m₂ * (m₁ * μ.den * N), by positivity, ⟨m₂ * m₁ * N * μ.num, ?_⟩,
    (m₂ : ℤ) • L₂, M, hM, ?_, ⟨e⟩⟩
  · push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  · rw [map_zsmul, hL₂, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    push_cast
    ring_nf

/-! ### The models of a sequence of log flips -/

/-- The base `Z_i` of the `i`-th contraction is quasi-compact. -/
private theorem compactSpace_base {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B)
    (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) : CompactSpace (S.base i) := by
  have hsmall := S.isSmall i hi
  have := hsmall.isVariety_target
  exact QuasiCompact.compactSpace_of_compactSpace (S.baseStr i)

/-- `X_0` is `ℚ`-factorial. -/
private theorem isQFactorial_model_zero {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X} (S : SequenceOfLogFlips sX K B)
    (h0 : ((0 : ℕ) : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model 0
    haveI := S.isNormal_model 0
    MMP.Fourfold.IsQFactorial (S.model 0).2.1 := by
  haveI := S.isLocallyNoetherian_model 0
  haveI := S.isNormal_model 0
  refine ⟨S.isNormalVariety_model 0 h0, ?_⟩
  have key : ∀ (M : FlipModel k) (_ : M = ⟨X, sX, K, B⟩) [IsLocallyNoetherian M.1] [IsNormal M.1],
      ∀ D : Divisor M.1, ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • D).IsCartier := by
    rintro M rfl _ _
    exact S.isQFactorial
  exact key _ S.model_zero

/-- `φ_i` has a flipping curve `C` with `(K_{X_i} + B_i) · C < 0`. -/
private theorem exists_isFlippingCurve_intersectionNumber_neg {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
    ∃ (C : ProperCurve (S.model i).2.1)
      (hKB : (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).IsQCartier),
      IsFlippingCurve k (S.model i).2.1 (S.baseStr i) (S.contraction i) (closure {C.point}) ∧
      (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2).intersectionNumber
        k (S.model i).2.1 C.ι C.dim_le hKB < 0 := by
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
  haveI := S.isLocallyNoetherian_base i
  haveI := S.isNormal_base i
  have hi' : (i : ℕ∞) < S.length := lt_of_le_of_lt (by simp) hi
  have hR := S.isExtremalRayContraction i hi
  have hsm := S.isSmall i hi
  haveI : IsIntegral (S.model i).1 :=
    hR.isNegativeExtremalContraction.isNormalVariety_source.1.toIsIntegral
  obtain ⟨C, hCc⟩ := exists_isContractedBy_of_finrank_eq_one (S.contraction i)
    (finrank_relativeNumericalDivisorClasses_contraction S i hi)
  set KB := Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2
  have hKB : KB.IsQCartier := hR.isQCartier
  -- the closure of `C` is a curve
  have hdim : topologicalKrullDim (closure {C.point} : Set (S.model i).1) = 1 := by
    have hr : Set.range C.ι = closure {C.point} := by
      change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    rw [← hr, ← C.dim_eq]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (C.ι.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  -- it lies in the exceptional set of `φ_i`
  have hex : closure {C.point} ⊆ MMP.Flips.exceptionalSet (S.contraction i) := by
    intro x hx hxn
    obtain ⟨V, hxV, hV⟩ := hxn
    have hpV : C.point ∈ V := (specializes_iff_mem_closure.mpr hx).mem_open V.isOpen hxV
    have := hsm.isVariety_source.toLocallyOfFiniteType
    haveI : JacobsonSpace (S.model i).1 := LocallyOfFiniteType.jacobsonSpace (S.model i).2.1
    have hcl : IsClosed ({C.point} : Set (S.model i).1) := by
      refine isClosed_singleton_of_isLocallyClosed_singleton
        ⟨V, closure {C.point}, V.isOpen, isClosed_closure, Set.ext fun t => ⟨?_, ?_⟩⟩
      · rintro rfl
        exact ⟨hpV, subset_closure rfl⟩
      · rintro ⟨htV, ht⟩
        have := (V.ι ≫ S.contraction i).isOpenEmbedding.injective
          (a₁ := ⟨t, htV⟩) (a₂ := ⟨C.point, hpV⟩)
          (by simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact hCc t ht)
        exact congrArg Subtype.val this
    rw [hcl.closure_eq] at hdim
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({C.point} : Set (S.model i).1)
    rw [hdim] at h0
    exact absurd h0 (by decide)
  refine ⟨C, hKB, isFlippingCurve_of_subset_exceptionalSet hsm (S.dim_model i hi')
    isIrreducible_singleton.closure isClosed_closure hdim hex,
    intersectionNumber_logCanonical_neg S i hi C hKB hCc⟩

/-- If `X_i` is `ℚ`-factorial, so is `X_{i+1}`. -/
private theorem isQFactorial_model_succ {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    (hQ : haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      MMP.Fourfold.IsQFactorial (S.model i).2.1) :
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    MMP.Fourfold.IsQFactorial (S.model (i + 1)).2.1 := by
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.compactSpace_model i
  haveI : QuasiCompact (S.model i).2.1 := quasiCompact_of_compactSpace _
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI := S.isLocallyNoetherian_base i
  haveI := S.isNormal_base i
  haveI := compactSpace_base S i hi
  haveI := S.compactSpace_model (i + 1)
  haveI : IsIntegral (S.model (i + 1)).1 := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
  refine ⟨S.isNormalVariety_model (i + 1) hi, fun Gp => ?_⟩
  -- `G⁺ = θ_{i*} G`
  obtain ⟨G, hG⟩ := exists_transformDivisor_eq S i hi Gp
  obtain ⟨C, hKB, hC, hneg⟩ := exists_isFlippingCurve_intersectionNumber_neg S i hi
  have hGq : (Divisor.toQDivisor G).IsQCartier := by
    obtain ⟨m, hm, hc⟩ := hQ.2 G
    exact ⟨m, by exact_mod_cast hm.ne', by
      rw [← map_zsmul]; exact QDivisor.isCartierDivisor_toQDivisor.mpr hc⟩
  set KB := Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2
  set μ : ℚ := (Divisor.toQDivisor G).intersectionNumber k (S.model i).2.1 C.ι C.dim_le hGq /
    KB.intersectionNumber k (S.model i).2.1 C.ι C.dim_le hKB with hμ
  -- `m (G - μ (K_{X_i} + B_i)) ∼ φ_i^* M`, transported to `θ_{i*}` of it `∼ φ_i⁺^* M`
  obtain ⟨m, hm, -, L, M, hM, hL, e⟩ :=
    exists_smul_sub_linearEquiv_pullback_contraction S i hi hQ (Divisor.toQDivisor G) C hC μ
      ⟨hGq, hKB, by rw [hμ, div_mul_cancel₀ _ hneg.ne]⟩
  obtain ⟨e'⟩ := nonempty_divisorialSheaf_transformDivisor_iso_pullback_flip S i hi L M hM e
  have hDc := isCartier_of_iso_pullback (S.flip i) hM e'
  -- `θ_{i*}(K_{X_i} + B_i)` is `ℚ`-Cartier
  set T := RationalMap.transformDivisor (S.flipMap i) KB
  have hT : QDivisor.IsQCartier T := by
    refine QDivisor.isQCartier_of_isCartierCombination ?_
    have h := (S.isFlip i hi).isCartierCombination_transform
    have hT' : QDivisor.toRDivisor T = RationalMap.transformDivisor (S.flipMap i)
        (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2)) := by
      change DivisorWithCoeffs.mapCoeffsAddMonoidHom (Rat.castHom ℝ).toAddMonoidHom _ = _
      rw [← transformDivisor_mapCoeffsAddMonoidHom]
      congr 1
      change QDivisor.toRDivisor _ = _
      rw [map_add, QDivisor.toRDivisor_toQDivisor]
      rfl
    rwa [hT']
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlin (E : QDivisor (S.model i).1) : RationalMap.transformDivisor (S.flipMap i) E =
      RationalMap.transformDivisorₗ ℚ (S.flipMap i) E := rfl
  have hGp : Divisor.toQDivisor Gp = (1 / (m : ℚ)) •
      Divisor.toQDivisor (RationalMap.transformDivisor (S.flipMap i) L) + μ • T := by
    rw [← transformDivisor_toQDivisor, hL, ← hG]
    simp only [T, hlin, map_smul, map_sub, smul_smul, one_div_mul_cancel hm', one_smul]
    exact (sub_add_cancel _ _).symm
  have hq : (Divisor.toQDivisor Gp).IsQCartier := by
    rw [hGp]
    exact (isQCartier_smul (QDivisor.isQCartier_toQDivisor hDc) _).add (isQCartier_smul hT μ)
  obtain ⟨n, hn, D', hD', hD'c⟩ := hq.exists_pos
  refine ⟨n, hn, ?_⟩
  have : (n : ℤ) • Gp = D' := Divisor.toQDivisor_injective (by rw [map_zsmul, hD'])
  rwa [this]

/-- Pushing a finitely supported function forward along an injective map preserves its set of
nonzero values. -/
private theorem frange_mapDomain_of_injective {α β R : Type*} [AddCommMonoid R] {f : α → β}
    (hf : Function.Injective f) (v : α →₀ R) : (Finsupp.mapDomain f v).frange = v.frange := by
  ext c
  rw [Finsupp.mem_frange, Finsupp.mem_frange]
  refine and_congr_right fun hc ↦ ⟨?_, ?_⟩
  · rintro ⟨E, rfl⟩
    by_cases hE : E ∈ Set.range f
    · obtain ⟨D, rfl⟩ := hE
      exact ⟨D, (Finsupp.mapDomain_apply_of_injective hf v D).symm⟩
    · exact absurd (Finsupp.mapDomain_notin_range v E hE) hc
  · rintro ⟨D, rfl⟩
    exact ⟨f D, Finsupp.mapDomain_apply_of_injective hf v D⟩

/-- One step: the flip map `θ_i`, a bijection on prime divisors, preserves the set of nonzero
boundary coefficients. -/
private theorem frange_boundary_succ {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    (S.model (i + 1)).2.2.2.frange = (S.model i).2.2.2.frange := by
  obtain ⟨ψ, hψ, hψD⟩ := exists_bijective_transformPrimeDivisor S i hi
  rw [S.transform_eq i hi]
  exact (congrArg Finsupp.frange (mapPrimeDivisors_eq_mapDomain hψD _)).trans
    (frange_mapDomain_of_injective hψ.1 _)

/-- In a sequence of log flips `S` starting from `(X₀, B₀)`, the set of nonzero coefficients of
the boundary `B_i` of every model `X_i`, `i < L`, equals the set of nonzero coefficients of
`B₀`. -/
@[mmp "lem_fa7_sequence_coefficients"]
theorem SequenceOfLogFlips.frange_boundary_model {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : (i : ℕ∞) < S.length) :
    (S.model i).2.2.2.frange = B.frange := by
  induction i with
  | zero => rw [S.model_zero]
  | succ n ih =>
    rw [frange_boundary_succ S n hi, ih (lt_of_le_of_lt (by exact_mod_cast Nat.le_succ n) hi)]

/-- In a sequence of log flips `S` starting from `(X₀, B₀)`, every model `X_i` with `i < L` is
`ℚ`-factorial. -/
@[mmp "lem_fa7_sequence_stays_qfactorial"]
theorem SequenceOfLogFlips.isQFactorial_model {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfLogFlips sX K B) (i : ℕ) (hi : (i : ℕ∞) < S.length) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    MMP.Fourfold.IsQFactorial (S.model i).2.1 := by
  induction i with
  | zero => exact isQFactorial_model_zero S hi
  | succ i ih => exact isQFactorial_model_succ S i hi (ih (lt_of_le_of_lt (by simp) hi))

end SequenceOfLogFlips

end MMP.Flips

namespace MMP.Mori

/-! ### Smooth projective models of normal surfaces -/

section NormalSurface

/-- The normalization of `P` in a normal locally Noetherian scheme `Y`, along a quasi-compact
open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal and finite
over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type u}
    [Field k] {Y P : Scheme.{u}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] [IsNormal Y]
    [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- A morphism of irreducible schemes which is an open immersion on a nonempty open of its
source is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_ι_comp {A B : Scheme.{u}}
    [IrreducibleSpace A] [IrreducibleSpace B] (g : A ⟶ B) (W : A.Opens)
    (hW : (W : Set A).Nonempty) (h : IsOpenImmersion (W.ι ≫ g)) :
    MMP.Mori.IsBirationalMorphism g := by
  let V : B.Opens := (W.ι ≫ g).opensRange
  have hWV : W ≤ g ⁻¹ᵁ V := fun w hw => ⟨⟨w, hw⟩, rfl⟩
  have hc : g.resLE V W hWV ≫ V.ι = W.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have : IsOpenImmersion (g.resLE V W hWV ≫ V.ι) := by rwa [hc]
  have : IsOpenImmersion (g.resLE V W hWV) := IsOpenImmersion.of_comp _ V.ι
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g W V hW ?_ hWV ?_
  · obtain ⟨w, hw⟩ := hW
    exact ⟨_, ⟨w, hw⟩, rfl⟩
  · rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
    obtain ⟨w, rfl⟩ := hz
    refine ⟨w, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hc]
    rfl

/-- Let `f : T ⟶ N` be a birational morphism of integral schemes and `t : S ⟶ N` an open
immersion. A morphism `τ : U ⟶ S` from a nonempty open `U ⊆ T` lifting `f|_U` through `t` is
birational. -/
private theorem isBirationalMorphism_of_comp_isOpenImmersion {T N S : Scheme.{u}}
    [IsIntegral T] [IsIntegral S] (f : T ⟶ N) (hf : MMP.Mori.IsBirationalMorphism f)
    (U : T.Opens) (hU : (U : Set T).Nonempty) (t : S ⟶ N) [IsOpenImmersion t] (τ : U.toScheme ⟶ S)
    (hτ : τ ≫ t = U.ι ≫ f) : MMP.Mori.IsBirationalMorphism τ := by
  have : Nonempty T := hU.to_subtype.map Subtype.val
  have : Nonempty U := hU.to_subtype
  obtain ⟨W, hWne, hW⟩ := hf.exists_isOpenImmersion
  obtain ⟨x, hxW, hxU⟩ := nonempty_preirreducible_inter W.isOpen U.isOpen hWne hU
  let W' : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  refine isBirationalMorphism_of_isOpenImmersion_ι_comp τ W' ⟨⟨x, hxU⟩, hxW⟩ ?_
  have : IsOpenImmersion (U.ι.resLE W W' le_rfl) :=
    have : IsOpenImmersion (U.ι.resLE W W' le_rfl ≫ W.ι) := by
      rw [Scheme.Hom.resLE_comp_ι]; infer_instance
    IsOpenImmersion.of_comp _ W.ι
  have : IsOpenImmersion ((W'.ι ≫ τ) ≫ t) := by
    rw [Category.assoc, hτ, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ (le_rfl : W' ≤ _),
      Category.assoc]
    infer_instance
  exact IsOpenImmersion.of_comp _ t

/-- Over an algebraically closed field `k`, every normal surface `S` is the target of a proper
birational `k`-morphism `τ : T° ⟶ S` from an open subscheme `T°` of a smooth projective surface
`T` over `k`. -/
@[mmp "lem_mmp_foundation_normal_surface_projective_model"]
theorem exists_smooth_projective_open_isProper_isBirationalMorphism
    (k : Type u) [Field k] [IsAlgClosed k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    (hS : IsNormalVariety k sS) (hdim : topologicalKrullDim S = 2) :
    ∃ (T : Scheme.{u}) (sT : T ⟶ Spec (.of k)) (U : T.Opens) (τ : (U : Scheme.{u}) ⟶ S),
      IsProjectiveVariety k sT ∧ Smooth sT ∧ topologicalKrullDim T = 2 ∧
        U.ι ≫ sT = τ ≫ sS ∧ IsProper τ ∧ IsBirationalMorphism τ := by
  have hSv : AlgebraicGeometry.IsVariety k sS := hS.1
  have : IsNormal S := hS.2
  have : IsIntegral S := hSv.toIsIntegral
  have : IsSeparated sS := hSv.toIsSeparated
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : QuasiCompact sS := hSv.toQuasiCompact
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  -- Nagata compactification `S ⊆ P → Spec k`.
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace sS
  let j : S ⟶ c.space := c.immersion
  let p : c.space ⟶ Spec (.of k) := c.toBase
  have hjp : j ≫ p = sS := Over.w c.obj.hom
  have : QuasiCompact j := hc
  have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
  have : IsSeparated j := IsSeparated.of_comp j p
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  -- The normalization `N` of `P` in `S`.
  obtain ⟨ht, hnorm, hfin⟩ := isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p) j
  set t := j.toNormalization
  let sN := j.fromNormalization ≫ p
  have htN : t ≫ sN = sS := by
    simp only [sN, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hNv : MMP.Mori.IsNormalVariety k sN :=
    ⟨(MMP.Mori.isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      hnorm⟩
  have : IsIntegral j.normalization := hNv.1.toIsIntegral
  have hNdim : topologicalKrullDim j.normalization = 2 := by
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k _ sN _ t.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _), ← hdim]
    exact (t.isOpenEmbedding.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq.symm
  -- Resolve `N`.
  obtain ⟨T, sT, f, hTv, hTs, hTdim, hfs, hfp, hfb⟩ :=
    MMP.Mori.exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety k sN hNv hNdim
  have : IsProper sT := by rw [← hfs]; infer_instance
  have hproj : IsProjectiveMorphism sT :=
    MMP.isProjectiveMorphism_of_smooth_of_isProper_of_topologicalKrullDim_eq_two sT hTdim
  have : IsIntegral T := hTv.toIsIntegral
  let V := t.opensRange
  let τ : ((f ⁻¹ᵁ V : T.Opens) : Scheme.{u}) ⟶ S := f ∣_ V ≫ t.isoOpensRange.inv
  have hτt : τ ≫ t = (f ⁻¹ᵁ V).ι ≫ f := by
    have e : f ∣_ V ≫ t.isoOpensRange.inv ≫ t.isoOpensRange.hom ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f := by
      rw [Iso.inv_hom_id_assoc, morphismRestrict_ι]
    rw [Scheme.Hom.isoOpensRange_hom_ι] at e
    simpa only [τ, Category.assoc] using e
  refine ⟨T, sT, f ⁻¹ᵁ V, τ, (MMP.Mori.isProjectiveVariety_iff k sT).2 ⟨hTv, hproj⟩, hTs,
    hTdim, ?_, inferInstance, ?_⟩
  · rw [← hfs, ← reassoc_of% hτt, htN]
  · obtain ⟨s⟩ := (inferInstance : Nonempty S)
    obtain ⟨x, hx⟩ := hfb.isDominant.denseRange.exists_mem_open V.isOpen ⟨t s, s, rfl⟩
    exact isBirationalMorphism_of_comp_isOpenImmersion f hfb _ ⟨x, hx⟩ t τ hτt

end NormalSurface

/-! ### Regular local rings and smooth points -/

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing_of_perfectField {k : Type u} [Field k]
    [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- Over a perfect field, a scheme is smooth when all its local rings are regular. -/
private theorem isSmoothScheme_of_forall_isRegularLocalRing {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme s :=
  eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing_of_perfectField s y).mpr (h y)

/-- If `j` is an open immersion and `𝒪_{Y, j p}` is regular, then `𝒪_{P, p}` is regular. -/
theorem isRegularLocalRing_of_isOpenImmersion {P Y : Scheme.{u}} (j : P ⟶ Y)
    [IsOpenImmersion j] (p : P) (h : IsRegularLocalRing (Y.presheaf.stalk (j p))) :
    IsRegularLocalRing (P.presheaf.stalk p) := by
  have : IsIso (j.stalkMap p) := inferInstanceAs (IsIso (j.toLRSHom.stalkMap p))
  exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv

/-- The generic point of an irreducible closed subset is a generic point of that subset. -/
private theorem isGenericPoint_genericPoint {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    (V : IrreducibleCloseds Y) : IsGenericPoint V.isIrreducible.genericPoint (V : Set Y) :=
  V.isIrreducible.isGenericPoint_genericPoint V.isClosed

/-- The codimension of an irreducible closed subset is the coheight of its generic point. -/
private theorem codimension_eq_coheight_genericPoint {Y : Scheme.{u}}
    (V : IrreducibleCloseds Y) :
    codimension V = Order.coheight V.isIrreducible.genericPoint := by
  have hcl : V = IrreducibleCloseds.closureSingleton V.isIrreducible.genericPoint := by
    ext1
    exact (isGenericPoint_genericPoint V).symm
  conv_lhs => rw [hcl]
  exact Stacks.Divisors.PrimeDivisor.codimension_closureSingleton _

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- Membership in powers of the maximal ideal is read through an isomorphism of local rings. -/
private theorem mem_maximalIdeal_pow_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (a : R) :
    e a ∈ IsLocalRing.maximalIdeal S ^ n ↔ a ∈ IsLocalRing.maximalIdeal R ^ n := by
  have hm : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [← hm, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨b, hb, hba⟩ => e.injective hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

/-! ### The discrepancy of the blow-up of a generically regular centre -/

section BlowupDiscrepancy

/-- Over a field of characteristic zero, a point of a normal variety with regular local ring has
a smooth open neighbourhood. -/
private theorem exists_smooth_open_of_isRegularLocalRing {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation sX :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hx : x ∈ sX.smoothLocus :=
    (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus sX x).mp
      ((AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk sX x
        (Algebra.isSeparableExtension_of_perfectField k (X.residueField x))).mpr hreg)
  rw [← MMP.Mori.smoothLocus_eq_smoothLocus] at hx
  exact MMP.Mori.mem_smoothLocus_iff.mp hx

/-- For a bijective ring hom `f` of local rings, `I.map f ≤ 𝔪_S ^ s ↔ I ≤ 𝔪_R ^ s`. -/
theorem map_le_maximalIdeal_pow_iff {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : Function.Bijective f) (I : Ideal R)
    (s : ℕ) :
    I.map f ≤ IsLocalRing.maximalIdeal S ^ s ↔ I ≤ IsLocalRing.maximalIdeal R ^ s := by
  have h : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map f :=
    (IsLocalRing.map_maximalIdeal_of_surjective f hf.2).symm
  rw [h, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective f hf]

/-- If `W'` is an irreducible closed subset of the open `U` with the same generic point as `W`,
then `∑_Γ coeff_Γ(B|_U) · mult_{W'} Γ = ∑_Γ coeff_Γ(B) · mult_W Γ`. -/
theorem sum_multiplicityAlong_restrictOpen {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (B : QDivisor X) (W : IrreducibleCloseds X) (U : X.Opens)
    (W' : IrreducibleCloseds U.toScheme)
    (hW'η : U.ι W'.isIrreducible.genericPoint = W.isIrreducible.genericPoint) :
    ((B.restrictOpen U).sum fun Γ b => b * ((Γ.multiplicityAlong W').toNat : ℚ)) =
      B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  classical
  set η := W.isIrreducible.genericPoint
  have hle : ∀ (I : X.IdealSheafData) (s : ℕ),
      (I.comap U.ι).stalkIdeal W'.isIrreducible.genericPoint ≤
        IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk W'.isIrreducible.genericPoint) ^ s ↔
      I.stalkIdeal η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ s := by
    intro I s
    rw [← hW'η]
    generalize W'.isIrreducible.genericPoint = x'
    rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk, Scheme.IdealSheafData.stalkIdeal_eq_stalk,
      MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map]
    haveI := IsOpenImmersion.instIsIsoCommRingCatStalkMap U.ι x'
    exact map_le_maximalIdeal_pow_iff _ (ConcreteCategory.bijective_of_isIso _) _ s
  have hmult : ∀ Γ' : MMP.Mori.PrimeDivisor U.toScheme, Γ'.multiplicityAlong W' =
      MMP.Mori.PrimeDivisor.multiplicityAlong (OpenWeilRestriction.primeDivisorMap U.ι Γ') W := by
    intro Γ'
    unfold PrimeDivisor.multiplicityAlong
    rw [← MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι Γ']
    simp only [hle]
    rfl
  have hzero : ∀ Γ : MMP.Mori.PrimeDivisor X,
      Γ ∉ Set.range (OpenWeilRestriction.primeDivisorMap U.ι) →
      Γ.multiplicityAlong W = 0 := by
    intro Γ hΓ
    have hη : η ∉ Γ.support := by
      intro hmem
      obtain ⟨Γ', hΓ'⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
        U.ι Γ W'.isIrreducible.genericPoint (by rwa [hW'η])
      exact hΓ ⟨Γ', hΓ'⟩
    unfold PrimeDivisor.multiplicityAlong
    rw [Γ.idealSheaf.stalkIdeal_eq_top_of_notMem_support hη]
    refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp
    · exact absurd (top_le_iff.mp (hs.trans (Ideal.pow_le_self hs0.ne')))
        (Ideal.IsMaximal.ne_top inferInstance)
  rw [Finsupp.sum, Finsupp.sum]
  change ∑ Γ' ∈ (B.support.preimage _
    (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn), _ = _
  rw [← Finset.sum_preimage (OpenWeilRestriction.primeDivisorMap U.ι) B.support
    (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn]
  · refine Finset.sum_congr rfl fun Γ' _ => ?_
    rw [hmult]; rfl
  · intro Γ _ hΓ
    simp [hzero Γ hΓ]

/-- On a scheme, the codimension of the closure of a point is the Krull dimension of the local
ring at that point. -/
theorem codimension_closureSingleton_eq_ringKrullDim {X : Scheme.{u}} (x : X) :
    (codimension (IrreducibleCloseds.closureSingleton x) : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk x) := by
  have h : IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x :=
    IrreducibleCloseds.ext (by
      rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
  rw [ringKrullDim_stalk_eq_coheight, codimension_eq_coheight, h,
    Order.coheight_orderIso irreducibleSetEquivPoints.symm x]

/-- The centre `W ∩ U` on an open `U ∋ η_W`: an irreducible closed subset of `U` with the same
generic point and codimension as `W`, along which the multiplicities of prime divisors are those
along `W`. -/
theorem exists_irreducibleCloseds_restrict {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (B : QDivisor X) (W : IrreducibleCloseds X) (U : X.Opens)
    (hU : W.isIrreducible.genericPoint ∈ U) :
    ∃ W' : IrreducibleCloseds U.toScheme, (W' : Set U.toScheme) = U.ι ⁻¹' (W : Set X) ∧
      U.ι W'.isIrreducible.genericPoint = W.isIrreducible.genericPoint ∧
      codimension W' = codimension W ∧
      ((B.restrictOpen U).sum fun Γ b => b * ((Γ.multiplicityAlong W').toNat : ℚ)) =
        B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  set η := W.isIrreducible.genericPoint
  let x : U.toScheme := ⟨η, hU⟩
  have hx : U.ι x = η := rfl
  let W' := IrreducibleCloseds.closureSingleton x
  have hW'gen : W'.isIrreducible.genericPoint = x :=
    (W'.isIrreducible.isGenericPoint_genericPoint W'.isClosed).eq (isGenericPoint_closure (x := x))
  have hWcl : (W : Set X) = closure {η} :=
    (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm
  have hW'η : U.ι W'.isIrreducible.genericPoint = η := by rw [hW'gen]; rfl
  refine ⟨W', ?_, hW'η, ?_, sum_multiplicityAlong_restrictOpen B W U W' hW'η⟩
  · change closure {x} = _
    rw [hWcl, U.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.image_singleton, hx]
  · have h1 := codimension_closureSingleton_eq_ringKrullDim x
    have h2 := codimension_closureSingleton_eq_ringKrullDim η
    have hWη : IrreducibleCloseds.closureSingleton η = W := by
      ext1; exact hWcl.symm
    rw [hWη] at h2
    have h3 : ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk η) :=
      ringKrullDim_eq_of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv
    exact WithBot.coe_injective (h1.trans (h3.trans h2.symm))

/-- Blowing up commutes with restriction to an open `U`: an open immersion `j` of `D.Y` into
`Bl_W X` over `X` restricts to an open immersion of `D.f⁻¹(U)` into `Bl_{W ∩ U} U` over `U`. -/
private theorem exists_isOpenImmersion_blowUp_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (W : IrreducibleCloseds X) (U : X.Opens) (W' : IrreducibleCloseds U.toScheme)
    (hW' : (W' : Set U.toScheme) = U.ι ⁻¹' (W : Set X)) (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j] (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f) :
    ∃ j' : (D.f ⁻¹ᵁ U).toScheme ⟶ Stacks.Blowup.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨W', W'.isClosed⟩ : Closeds U.toScheme)),
      IsOpenImmersion j' ∧ j' ≫ Stacks.Blowup.blowUpToBase _ = D.f ∣_ U := by
  let Z := Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)
  have hZ : Z.comap U.ι =
      Scheme.IdealSheafData.vanishingIdeal (⟨W', W'.isClosed⟩ : Closeds U.toScheme) := by
    have : IsReduced (Z.comap U.ι).subscheme :=
      isReduced_of_isOpenImmersion ((Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι)
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    rw [Scheme.IdealSheafData.support_comap]
    apply Closeds.ext
    rw [Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hW'.symm
  rw [← hZ]
  have sq := MMP.Resolution.Kollar.isPullback_canonicalLift_of_flat U.ι Z
  have hc : IsOpenImmersion (MMP.Resolution.canonicalLift U.ι Z) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  let j₀ := j ≫ (Stacks.Blowup.blowUpIso Z).hom
  have hw : ((D.f ⁻¹ᵁ U).ι ≫ j₀) ≫ AlgebraicGeometry.blowUpToBase Z = (D.f ∣_ U) ≫ U.ι := by
    rw [Category.assoc, Category.assoc, Stacks.Blowup.blowUpIso_hom_comp, hj, morphismRestrict_ι]
  set l := sq.lift (D.f ∣_ U) ((D.f ⁻¹ᵁ U).ι ≫ j₀) hw.symm
  have h2 : l ≫ MMP.Resolution.canonicalLift U.ι Z = (D.f ⁻¹ᵁ U).ι ≫ j₀ := sq.lift_snd _ _ _
  have : IsOpenImmersion (l ≫ MMP.Resolution.canonicalLift U.ι Z) := by
    rw [h2]; exact inferInstanceAs (IsOpenImmersion ((D.f ⁻¹ᵁ U).ι ≫ j ≫ _))
  have : IsOpenImmersion l := IsOpenImmersion.of_comp _ (MMP.Resolution.canonicalLift U.ι Z)
  refine ⟨l ≫ (Stacks.Blowup.blowUpIso (Z.comap U.ι)).inv, inferInstance, ?_⟩
  rw [Category.assoc, ← Stacks.Blowup.blowUpIso_hom_comp, Iso.inv_hom_id_assoc]
  exact sq.lift_fst _ _ _

/-- The formula on a smooth open neighbourhood `U` of `η_W`: restrict to `U`, identify
`D.f⁻¹(U)` with an open of `Bl_{W ∩ U} U`, apply `isDiscrepancy_blowUp_of_charZero`, and
transport the value back (multiplicities along `W` and discrepancies are local). -/
private theorem isDiscrepancy_of_smooth_open {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (B : QDivisor X)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    (W : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension W) (hc2 : 2 ≤ c)
    (U : X.Opens) (hU : W.isIrreducible.genericPoint ∈ U) (hUs : Smooth (U.ι ≫ sX))
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = W.isIrreducible.genericPoint) :
    IsDiscrepancy sX n K B D
      ((c : ℚ) - 1 - B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ)) := by
  have hΔ : IsPairWith sX n K B := ⟨hX, hK, hKB⟩
  have hη : D.f D.E.genericPoint ∈ U := hE ▸ hU
  have hUc : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hη⟩
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hΔ D U hUc
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΔ.isPair hK D
  have hKU := ((hiff a₀).mp ha₀).2.1
  rw [hiff]
  obtain ⟨W', hW', hW'η, hW'c, hsum⟩ := exists_irreducibleCloseds_restrict B W U hU
  obtain ⟨j', _, hj'⟩ := exists_isOpenImmersion_blowUp_restrict W U W' hW' D j hj
  have hE'' : (D.f ∣_ U) E'.genericPoint = W'.isIrreducible.genericPoint := by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hW'η, ← hE, ← hE',
      ← OpenWeilRestriction.genericPoint_primeDivisorMap]
  have hUv := isNormalVariety_ι hX U
  have : IsIntegral U.toScheme := hUv.1.toIsIntegral
  have : IsLocallyNoetherian U.toScheme := hUv.1.toLocallyOfFiniteType.isLocallyNoetherian
  have : IsNormal U.toScheme := hUv.2
  rw [← hsum]
  exact (isDiscrepancy_blowUp_of_charZero (U.ι ≫ sX) hUv.1 hKU (B.restrictOpen U) W'
    (hc.trans hW'c.symm) hc2 ⟨_, D.f ∣_ U, hY, hf, E'⟩ j' hj' hE'').2

/-- The characteristic-zero version of the discrepancy of a generically regular centre;
`isDiscrepancy_blowUp_of_isRegularLocalRing` specializes it. -/
theorem isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (B : QDivisor X)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    (W : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension W) (hc2 : 2 ≤ c)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = W.isIrreducible.genericPoint) :
    IsDiscrepancy sX n K B D
      ((c : ℚ) - 1 - B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ)) := by
  obtain ⟨U, hU, hUs⟩ := exists_smooth_open_of_isRegularLocalRing sX hX _ hreg
  exact isDiscrepancy_of_smooth_open sX hX hK B hKB W hc hc2 U hU hUs D j hj hE

/-- **Discrepancy of the blow-up of a generically regular centre.** Let `X` be a normal variety
over an algebraically closed field `k` of characteristic zero, with canonical divisor `K` of
dimension `n`, `B` a `ℚ`-divisor with `K + B` `ℚ`-Cartier, and `W ⊆ X` an irreducible closed
subset of codimension `c ≥ 2` with `𝒪_{X,η_W}` regular. Let `D = (Y, f, E)` be a divisor over `X`
whose model `Y` is an open subscheme of the blow-up `Bl_W X` of the vanishing ideal of `W`
(through `j`, with `f = j ≫ p`) and with `f(η_E) = η_W`. Then
`a(E, X, B) = c - 1 - ∑_Γ coeff_Γ(B) · mult_W Γ`. -/
@[mmp "lem_mmp_blowup_discrepancy_at_regular_generic_point"]
theorem isDiscrepancy_blowUp_of_isRegularLocalRing {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (B : QDivisor X)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    (W : IrreducibleCloseds X) {c : ℕ} (hc : (c : ℕ∞) = codimension W) (hc2 : 2 ≤ c)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)))
    [IsOpenImmersion j]
    (hj : j ≫ Stacks.Blowup.blowUpToBase _ = D.f)
    (hE : D.f D.E.genericPoint = W.isIrreducible.genericPoint) :
    IsDiscrepancy sX n K B D
      ((c : ℚ) - 1 - B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ)) :=
  isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sX hX hK B hKB W hc hc2 hreg D j hj hE

end BlowupDiscrepancy

/-! ### Strict transforms under the blow-up of a regular codimension-two centre -/

section StrictTransform

open IsLocalRing

/-- A section lies in the prime of a point of an affine open iff its germ is not a unit. -/
private theorem mem_primeIdealOf_iff {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (g : Γ(X, U)) :
    g ∈ (hU.primeIdealOf x).asIdeal ↔ X.presheaf.germ U x x.2 g ∈ maximalIdeal _ := by
  have h1 : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g ↔
      (x : X) ∈ (X.basicOpen g : Set X) := by
    change hU.fromSpec (hU.primeIdealOf x) ∈ (X.basicOpen g : Set X) ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [hU.fromSpec_preimage_basicOpen] at h1
  have h2 := Scheme.mem_basicOpen X g x x.2
  rwa [← not_iff_not, IsLocalRing.notMem_maximalIdeal, ← h2]

/-- At a point of the support of an integral closed subscheme, the stalk of its ideal is
prime. -/
private theorem isPrime_stalkIdeal {X : Scheme} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    {x : X} (hx : x ∈ (I.support : Set X)) : (I.stalkIdeal x).IsPrime := by
  rw [← I.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  rw [← I.ker_stalkMap_subschemeι]
  exact RingHom.ker_isPrime _

/-- The stalk of an ideal sheaf maps into its stalk at a generization. -/
private theorem stalkSpecializes_mem_stalkIdeal {X : Scheme} (I : X.IdealSheafData) {x x' : X}
    (h : x' ⤳ x) {g : X.presheaf.stalk x} (hg : g ∈ I.stalkIdeal x) :
    X.presheaf.stalkSpecializes h g ∈ I.stalkIdeal x' := by
  revert g
  change I.stalkIdeal x ≤ (I.stalkIdeal x').comap (X.presheaf.stalkSpecializes h).hom
  refine iSup_le fun V => Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  simp only [Ideal.mem_comap]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  exact I.germ_mem_stalkIdeal V.1 _ hg

/-- A section lies in a prime of the spectrum of an affine open iff its germ at the
corresponding point is not a unit. -/
private theorem mem_asIdeal_iff_germ {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) (hP : hU.fromSpec P ∈ U) (g : Γ(X, U)) :
    g ∈ P.asIdeal ↔ X.presheaf.germ U _ hP g ∈ maximalIdeal _ := by
  have h1 : P ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g ↔ hU.fromSpec P ∈ (X.basicOpen g : Set X) :=
    Iff.rfl
  rw [hU.fromSpec_preimage_basicOpen] at h1
  have h2 := Scheme.mem_basicOpen X g _ hP
  rwa [← not_iff_not, IsLocalRing.notMem_maximalIdeal, ← h2]

/-- The pull-back of a local equation of `D` vanishes along the strict transform of `D`. -/
private theorem stalkMap_mem_stalkIdeal_of_eq_some {X Y : Scheme} (π : Y ⟶ X) (ζ : Y)
    {D : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (hDE : inverseTransformPrimeDivisor π D = some E)
    {f : X.presheaf.stalk (π ζ)} (hf : f ∈ D.idealSheaf.stalkIdeal (π ζ)) :
    π.stalkMap ζ f ∈ E.idealSheaf.stalkIdeal ζ := by
  revert f
  change D.idealSheaf.stalkIdeal (π ζ) ≤ (E.idealSheaf.stalkIdeal ζ).comap (π.stalkMap ζ).hom
  refine iSup_le fun V => Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  simp only [Ideal.mem_comap]
  rw [Scheme.Hom.germ_stalkMap_apply]
  obtain ⟨V', hV', hζV', hV'V⟩ := exists_isAffineOpen_mem_and_subset (x := ζ) (U := π ⁻¹ᵁ V.1.1)
    V.2
  have hle : V' ≤ π ⁻¹ᵁ V.1.1 := hV'V
  rw [← Y.presheaf.germ_res_apply (homOfLE hle) ζ hζV']
  refine E.idealSheaf.germ_mem_stalkIdeal ⟨V', hV'⟩ hζV' ?_
  have hEid := (inverseTransformPrimeDivisor_eq_some_iff.mp hDE).2
  rw [hEid]
  change _ ∈ PrimeSpectrum.vanishingIdeal _
  rw [PrimeSpectrum.mem_vanishingIdeal]
  intro P hP
  have hPV : hV'.fromSpec P ∈ V' := hV'.range_fromSpec.le ⟨P, rfl⟩
  rw [mem_asIdeal_iff_germ hV' P hPV, Y.presheaf.germ_res_apply,
    ← Scheme.Hom.germ_stalkMap_apply π V.1.1 _ (hle hPV)]
  refine map_nonunit _ _ ?_
  -- `π` maps the point into `D`
  have hPD : π (hV'.fromSpec P) ∈ D.support := by
    have h1 : (inverseTransform π D.idealSheaf.support : Set Y) ⊆ π ⁻¹' D.support :=
      closure_minimal (fun y hy => hy.1) (D.idealSheaf.support.isClosed.preimage π.continuous)
    exact h1 hP
  have hgv : g ∈ (Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support).ideal V.1 :=
    Scheme.IdealSheafData.le_def.mp
      (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl) V.1 hg
  change g ∈ PrimeSpectrum.vanishingIdeal _ at hgv
  rw [PrimeSpectrum.mem_vanishingIdeal] at hgv
  have hmem := hgv (V.1.2.primeIdealOf ⟨_, hle hPV⟩)
    (by change V.1.2.fromSpec _ ∈ (D.idealSheaf.support : Set X)
        rwa [V.1.2.fromSpec_primeIdealOf])
  exact (mem_primeIdealOf_iff V.1.2 ⟨_, hle hPV⟩ g).mp hmem

open Polynomial

/-- The degree-`a` form `∑_j P_j y^{a-j} z^j` attached to a polynomial `P`. -/
private noncomputable def homForm {R : Type*} [CommRing R] (y z : R) (a : ℕ) (P : R[X]) : R :=
  ∑ j ∈ Finset.range (a + 1), P.coeff j * y ^ (a - j) * z ^ j

private theorem homForm_add {R : Type*} [CommRing R] (y z : R) (a : ℕ) (P Q : R[X]) :
    homForm y z a (P + Q) = homForm y z a P + homForm y z a Q := by
  simp only [homForm, coeff_add, add_mul, Finset.sum_add_distrib]

private theorem homForm_smul {R : Type*} [CommRing R] (y z : R) (a : ℕ) (r : R) (P : R[X]) :
    homForm y z a (C r * P) = r * homForm y z a P := by
  simp only [homForm, coeff_C_mul, Finset.mul_sum, mul_assoc]

private theorem homForm_succ_mul_left {R : Type*} [CommRing R] (y z : R) (a : ℕ) (P : R[X])
    (hP : P.natDegree ≤ a) : homForm y z (a + 1) P = homForm y z a P * y := by
  rw [homForm, Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega), zero_mul,
    zero_mul, add_zero, homForm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have : a + 1 - j = a - j + 1 := by have := Finset.mem_range.mp hj; omega
  rw [this, pow_succ]; ring

private theorem homForm_succ_mul_right {R : Type*} [CommRing R] (y z : R) (a : ℕ) (P : R[X]) :
    homForm y z (a + 1) (Polynomial.X * P) = homForm y z a P * z := by
  rw [homForm, Finset.sum_range_succ', coeff_X_mul_zero, zero_mul, zero_mul, add_zero, homForm,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_X_mul, show a + 1 - (j + 1) = a - j by omega, pow_succ]; ring

private theorem exists_homForm_of_mem_pow {R : Type*} [CommRing R] (y z : R) (a : ℕ) (f : R)
    (hf : f ∈ Ideal.span {y, z} ^ a) :
    ∃ P : R[X], P.natDegree ≤ a ∧ f = homForm y z a P := by
  induction a generalizing f with
  | zero =>
    refine ⟨C f, by simp, ?_⟩
    simp [homForm]
  | succ a ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun m hm n hn => ?_) (fun f g hf hg => ?_)
    · obtain ⟨P, hP, rfl⟩ := ih m hm
      obtain ⟨r, s, rfl⟩ := Ideal.mem_span_pair.mp hn
      refine ⟨C r * P + C s * (Polynomial.X * P), ?_, ?_⟩
      · refine natDegree_add_le_of_degree_le ?_ ?_
        · exact (natDegree_C_mul_le _ _).trans (hP.trans (Nat.le_succ a))
        · refine (natDegree_C_mul_le _ _).trans ?_
          exact (natDegree_mul_le).trans (by have := natDegree_X_le (R := R); omega)
      · rw [homForm_add, homForm_smul, homForm_smul, homForm_succ_mul_left _ _ _ _ hP,
          homForm_succ_mul_right]
        ring
    · obtain ⟨P, hP, rfl⟩ := hf
      obtain ⟨Q, hQ, rfl⟩ := hg
      exact ⟨P + Q, natDegree_add_le_of_degree_le hP hQ, (homForm_add _ _ _ _ _).symm⟩

/-- **The order of the strict transform is at most the order of the divisor.** -/
private theorem le_of_stalkIdeal_le {X Y : Scheme} (π : Y ⟶ X) (ζ : Y)
    {D : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (hDE : inverseTransformPrimeDivisor π D = some E)
    (S : Set X) (hSgen : ∀ s ∈ S, π ζ ⤳ s) (hξ : ∃ ξ, ξ ≠ ζ ∧ π ξ = π ζ)
    (y z : X.presheaf.stalk (π ζ)) (T0 : Y.presheaf.stalk ζ)
    (hm : maximalIdeal (X.presheaf.stalk (π ζ)) = Ideal.span {y, z})
    (hT : π.stalkMap ζ z = T0 * π.stalkMap ζ y)
    (hc : ∀ (a : ℕ) (P : (X.presheaf.stalk (π ζ))[X]), P.natDegree ≤ a →
      (∃ j, P.coeff j ∉ maximalIdeal _) →
      (P.map (π.stalkMap ζ).hom).eval T0 ∉ maximalIdeal (Y.presheaf.stalk ζ) ^ (a + 1))
    (hd : ∀ ε (h : ε ⤳ ζ), π ε ∉ S → IsUnit (Y.presheaf.stalkSpecializes h (π.stalkMap ζ y)))
    (s a : ℕ) (hs : E.idealSheaf.stalkIdeal ζ ≤ maximalIdeal _ ^ s)
    (ha : ¬ D.idealSheaf.stalkIdeal (π ζ) ≤ maximalIdeal _ ^ (a + 1)) : s ≤ a := by
  classical
  -- a local equation of `D` of order `a' ≤ a`
  obtain ⟨f, hfD, hfa⟩ := Set.not_subset.mp ha
  have hex : ∃ k, f ∉ maximalIdeal (X.presheaf.stalk (π ζ)) ^ (k + 1) := ⟨a, hfa⟩
  set a' := Nat.find hex with ha'
  have ha'a : a' ≤ a := Nat.find_min' hex hfa
  have hfa' : f ∉ maximalIdeal (X.presheaf.stalk (π ζ)) ^ (a' + 1) := Nat.find_spec hex
  have hfa'' : f ∈ maximalIdeal (X.presheaf.stalk (π ζ)) ^ a' := by
    rcases Nat.eq_zero_or_pos a' with h0 | h0
    · rw [h0, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    · have h1 := Nat.find_min hex (show a' - 1 < a' by omega)
      push Not at h1
      rwa [Nat.sub_add_cancel h0] at h1
  rw [hm] at hfa''
  obtain ⟨P, hPdeg, hfP⟩ := exists_homForm_of_mem_pow y z a' f hfa''
  have hPm : ∃ j, P.coeff j ∉ maximalIdeal _ := by
    by_contra hcon
    push Not at hcon
    apply hfa'
    rw [hfP, homForm]
    refine Ideal.sum_mem _ fun j hj => ?_
    have hj' : j ≤ a' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [pow_succ', mul_assoc]
    refine Ideal.mul_mem_mul (hcon j) ?_
    have h1 := Ideal.mul_mem_mul
      (Ideal.pow_mem_pow (show y ∈ maximalIdeal (X.presheaf.stalk (π ζ)) from
        hm ▸ Ideal.subset_span (by simp)) (a' - j))
      (Ideal.pow_mem_pow (show z ∈ maximalIdeal (X.presheaf.stalk (π ζ)) from
        hm ▸ Ideal.subset_span (by simp)) j)
    rwa [← pow_add, Nat.sub_add_cancel hj'] at h1
  have hg := hc a' P hPdeg hPm
  set g := (P.map (π.stalkMap ζ).hom).eval T0 with hgdef
  have hfg : π.stalkMap ζ f = π.stalkMap ζ y ^ a' * g := by
    rw [hfP, homForm, map_sum, hgdef, Polynomial.eval_eq_sum_range' (n := a' + 1)
      (lt_of_le_of_lt (Polynomial.natDegree_map_le.trans hPdeg) (Nat.lt_succ_self _)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ a' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Polynomial.coeff_map, map_mul, map_mul, map_pow, map_pow, hT]
    conv_rhs => rw [← Nat.sub_add_cancel hj', pow_add]
    ring
  -- the case `ζ ∉ E`
  by_cases hζE : ζ ∈ E.support
  swap
  · have htop : E.idealSheaf.stalkIdeal ζ = ⊤ := (E.idealSheaf.stalkIdeal_eq_top_iff).mpr hζE
    rw [htop, top_le_iff] at hs
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · omega
    · exfalso
      have h1 : (1 : Y.presheaf.stalk ζ) ∈ maximalIdeal _ :=
        Ideal.pow_le_self h0.ne' (hs ▸ Submodule.mem_top)
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  haveI := E.integral
  have hPE := isPrime_stalkIdeal E.idealSheaf hζE
  have hfE := stalkMap_mem_stalkIdeal_of_eq_some π ζ hDE hfD
  rw [hfg] at hfE
  -- the generic point `ε` of `E`
  set ε := E.genericPoint with hεdef
  have hεE : ε ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hεζ : ε ⤳ ζ := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  -- `π(ε)` lies in the biregular locus
  have hsuppE : E.support = closure (π ⁻¹' (D.support ∩ biregularLocus π)) := by
    rw [support_inverseTransformPrimeDivisor hDE]; rfl
  have hA : π ε ∈ biregularLocus π := by
    obtain ⟨d, hdD, hdV⟩ := (inverseTransformPrimeDivisor_eq_some_iff.mp hDE).1
    obtain ⟨V0, hV0, hdV0⟩ := TopologicalSpace.Opens.mem_sSup.mp hdV
    have : IsIso (π ∣_ V0) := (hV0 : IsBiregular π V0)
    obtain ⟨q0, hq0⟩ := (TopCat.homeoOfIso
      (Scheme.forgetToTop.mapIso (asIso (π ∣_ V0)))).surjective ⟨d, hdV0⟩
    have hq0d : π q0.1 = d := by
      have h1 := congrArg Subtype.val hq0
      exact (morphismRestrict_base_coe π V0 q0).symm.trans h1
    have hq0E : q0.1 ∈ E.support := by
      rw [hsuppE]
      exact subset_closure ⟨hq0d ▸ hdD, hq0d ▸ le_biregularLocus hV0 hdV0⟩
    have hgenE : IsGenericPoint ε E.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    exact ((hgenE.mem_open_set_iff ((biregularLocus π).isOpen.preimage π.continuous)).mpr
      ⟨q0.1, hq0E, le_biregularLocus hV0 (hq0d ▸ hdV0)⟩)
  -- `π(ζ)` does not
  have hB : π ζ ∉ biregularLocus π := by
    intro hζV
    obtain ⟨V1, hV1, hζV1⟩ := TopologicalSpace.Opens.mem_sSup.mp hζV
    obtain ⟨ξ, hξζ, hπξ⟩ := hξ
    have : IsIso (π ∣_ V1) := (hV1 : IsBiregular π V1)
    have hξV : ξ ∈ π ⁻¹ᵁ V1 := show π ξ ∈ V1 from hπξ ▸ hζV1
    let a1 : ↥(π ⁻¹ᵁ V1).toScheme := ⟨ξ, hξV⟩
    let b1 : ↥(π ⁻¹ᵁ V1).toScheme := ⟨ζ, hζV1⟩
    have h1 : (π ∣_ V1) a1 = (π ∣_ V1) b1 :=
      Subtype.ext ((morphismRestrict_base_coe π V1 a1).trans
        (hπξ.trans (morphismRestrict_base_coe π V1 b1).symm))
    have h2 := (π ∣_ V1).isOpenEmbedding.injective h1
    exact hξζ (congrArg Subtype.val h2)
  have hC : π ε ∉ S := by
    intro hεS
    have h1 : π ε ⤳ π ζ := hεζ.map π.continuous
    have h2 := (hSgen _ hεS).antisymm h1
    exact hB (h2.eq ▸ hA)
  -- `π^* y` does not vanish along `E`
  have hyE : π.stalkMap ζ y ∉ E.idealSheaf.stalkIdeal ζ := by
    intro hmem
    have h1 := stalkSpecializes_mem_stalkIdeal E.idealSheaf hεζ hmem
    have h2 := E.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support hεE h1
    exact (IsLocalRing.notMem_maximalIdeal.mpr (hd ε hεζ hC)) h2
  have hgE : g ∈ E.idealSheaf.stalkIdeal ζ := by
    rcases hPE.mem_or_mem hfE with h | h
    · exact absurd (hPE.mem_of_pow_mem _ h) hyE
    · exact h
  by_contra hlt
  push Not at hlt
  exact hg (Ideal.pow_le_pow_right (by omega) (hs hgE))

open Polynomial in
attribute [local instance] Polynomial.algebra in
/-- **The order bound on the chart.** Let `B = C[T]/K` with `K ⊆ p·C[T]`, `q` a prime of `B`
over `p` not contained in `p·B`, and `A = B_q`. A polynomial `H` of degree at most `a` with a
coefficient outside `p` does not lie in `𝔪_A^{a+1}`: in `κ(p)[T]` the prime `q` becomes a
nonzero prime `(π₀)`, and `π₀^{a+1}` cannot divide the nonzero image of `H`. -/
private theorem algebraMap_notMem_pow_of_coeff_notMem {C B A : Type*} [CommRing C] [CommRing B]
    [CommRing A]
    (p : Ideal C) [p.IsPrime] (ρ : C[X] →+* B) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ ≤ p.map (Polynomial.C : C →+* C[X]))
    (q : Ideal B) [q.IsPrime] (hqp : q.comap (ρ.comp (Polynomial.C : C →+* C[X])) = p)
    (hq : ¬ q ≤ (p.map (Polynomial.C : C →+* C[X])).map ρ)
    [Algebra B A] [IsLocalization.AtPrime A q]
    (a : ℕ) (H : C[X]) (hH : H.natDegree ≤ a) (hHp : ∃ j, H.coeff j ∉ p) :
    algebraMap B A (ρ H) ∉ (q.map (algebraMap B A)) ^ (a + 1) := by
  classical
  set K := FractionRing (C ⧸ p)
  let φ0 : C →+* K := (algebraMap (C ⧸ p) K).comp (Ideal.Quotient.mk p)
  have hφ0 : RingHom.ker φ0 = p := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (C ⧸ p) K), Ideal.mk_ker]
  let M : C[X] →+* (C ⧸ p)[X] := mapRingHom (Ideal.Quotient.mk p)
  let L : (C ⧸ p)[X] →+* K[X] := algebraMap (C ⧸ p)[X] K[X]
  have hL : L = mapRingHom (algebraMap (C ⧸ p) K) := rfl
  let Φ : C[X] →+* K[X] := mapRingHom φ0
  have hΦ : Φ = L.comp M := by
    rw [hL]; ext <;> simp [Φ, M, φ0]
  have hkerΦ : RingHom.ker Φ = p.map (Polynomial.C : C →+* C[X]) := by
    rw [Polynomial.ker_mapRingHom, hφ0]
  have hkerM : RingHom.ker M = p.map (Polynomial.C : C →+* C[X]) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  have hMs : Function.Surjective M := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  set Q := q.comap ρ with hQ
  have hQC : Q.comap (Polynomial.C : C →+* C[X]) = p := by rw [hQ, Ideal.comap_comap, hqp]
  have hpQ : p.map (Polynomial.C : C →+* C[X]) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQC]
  have hQmap : Q.map ρ = q := Ideal.map_comap_of_surjective ρ hρ q
  have hQne : ¬ Q ≤ p.map (Polynomial.C : C →+* C[X]) := fun h => hq (hQmap ▸ Ideal.map_mono h)
  -- the image of `Q` in `(C/p)[X]`
  set Q1 := Q.map M with hQ1
  have hQ1p : Q1.IsPrime := Ideal.map_isPrime_of_surjective hMs (hkerM ▸ hpQ)
  have hQ1c : Q1.comap M = Q := by
    rw [hQ1, Ideal.comap_map_of_surjective' M hMs Q]
    exact sup_eq_left.mpr (hkerM ▸ hpQ)
  let S : Submonoid (C ⧸ p)[X] := Submonoid.map (Polynomial.C : C ⧸ p →+* (C ⧸ p)[X])
    (nonZeroDivisors (C ⧸ p))
  have : IsLocalization S K[X] := Polynomial.isLocalization _ _
  have hdisj : Disjoint (S : Set (C ⧸ p)[X]) Q1 := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcQ
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : (Polynomial.C c : C[X]) ∈ Q := by
      rw [← hQ1c, Ideal.mem_comap]; simpa [M] using hcQ
    have hcp : c ∈ p := by rwa [← hQC]
    exact nonZeroDivisors.coe_ne_zero ⟨_, hc⟩ (Ideal.Quotient.eq_zero_iff_mem.mpr hcp)
  set P' := Q1.map L with hP'
  have hP'p : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint S K[X] Q1 hQ1p hdisj
  have hP'c : P'.comap L = Q1 :=
    IsLocalization.comap_map_of_isPrime_disjoint S K[X] hQ1p hdisj
  have hP'Φ : P'.comap Φ = Q := by rw [hΦ, ← Ideal.comap_comap, hP'c, hQ1c]
  have hQP' : Q.map Φ = P' := by rw [hΦ, ← Ideal.map_map]
  -- `P'` is a nonzero proper prime of `K[X]`
  obtain ⟨π0, hπ0'⟩ := (IsPrincipalIdealRing.principal P').principal
  have hP'ne : P' ≠ ⊥ := by
    obtain ⟨g, hgQ, hgp⟩ := Set.not_subset.mp hQne
    intro h0
    have h1 : Φ g ∈ P' := hQP' ▸ Ideal.mem_map_of_mem Φ hgQ
    rw [h0, Ideal.mem_bot, ← RingHom.mem_ker, hkerΦ] at h1
    exact hgp h1
  have hπ0ne : π0 ≠ 0 := fun h => hP'ne (by rw [hπ0', h]; exact Ideal.span_singleton_eq_bot.mpr rfl)
  have hπ0prime : Prime π0 :=
    (Ideal.span_singleton_prime hπ0ne).mp (by rwa [← Ideal.submodule_span_eq, ← hπ0'])
  have hdeg : 1 ≤ π0.natDegree := by
    by_contra h0
    push Not at h0
    have h1 := Polynomial.eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp h0)
    apply hπ0prime.not_unit
    rw [h1]
    refine Polynomial.isUnit_C.mpr (IsUnit.mk0 _ ?_)
    intro h2; rw [h2, map_zero] at h1; exact hπ0ne h1
  -- the contradiction
  intro hmem
  rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff q.primeCompl A] at hmem
  obtain ⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h1⟩ := hmem
  simp only at h1
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl] at h1
  obtain ⟨⟨c, hc⟩, h2⟩ := h1
  simp only at h2
  obtain ⟨U', hU'⟩ := hρ (c * s)
  have hU'Q : U' ∉ Q := by
    simp only [Q, Ideal.mem_comap, hU']
    exact q.primeCompl.mul_mem hc hs
  have hmemq : ρ (U' * H) ∈ (Q ^ (a + 1)).map ρ := by
    rw [Ideal.map_pow, hQmap, map_mul, hU', mul_assoc, mul_comm s, ← mul_assoc, mul_assoc, h2]
    exact Ideal.mul_mem_left _ _ hi
  obtain ⟨w, hw, hwe⟩ := (Ideal.mem_map_iff_of_surjective ρ hρ).mp hmemq
  have hdiff : w - U' * H ∈ RingHom.ker Φ := by
    rw [hkerΦ]; apply hker; rw [RingHom.mem_ker, map_sub, hwe, sub_self]
  have hΦw : Φ (U' * H) ∈ Ideal.span {π0 ^ (a + 1)} := by
    have h3 : Φ (U' * H) = Φ w := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hdiff; exact hdiff.symm
    rw [h3, ← Ideal.span_singleton_pow, ← Ideal.submodule_span_eq, ← hπ0', ← hQP', ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem Φ hw
  rw [Ideal.mem_span_singleton, map_mul] at hΦw
  have hU'n : ¬ π0 ∣ Φ U' := by
    rwa [← Ideal.mem_span_singleton, Ideal.submodule_span_eq.symm, ← hπ0', ← Ideal.mem_comap, hP'Φ]
  have hdvd := hπ0prime.pow_dvd_of_dvd_mul_left (a + 1) hU'n hΦw
  have hΦH : Φ H ≠ 0 := by
    obtain ⟨j, hj⟩ := hHp
    intro h0
    have h3 : (Φ H).coeff j = 0 := by rw [h0, coeff_zero]
    simp only [Φ, coe_mapRingHom, coeff_map] at h3
    exact hj (hφ0 ▸ RingHom.mem_ker.mpr h3)
  have h3 := Polynomial.natDegree_le_of_dvd hdvd hΦH
  rw [Polynomial.natDegree_pow] at h3
  have h4 : (Φ H).natDegree ≤ a := (Polynomial.natDegree_map_le).trans hH
  nlinarith

/-- In a Noetherian local ring whose maximal ideal has height `2`, the maximal ideal is not
contained in the principal ideal of a non-unit. -/
theorem maximalIdeal_not_le_span_singleton_of_height_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (h2 : (maximalIdeal R).height = 2) {t : R}
    (ht : t ∈ maximalIdeal R) : ¬ maximalIdeal R ≤ Ideal.span {t} := by
  intro hle
  have hne : Ideal.span {t} ≠ ⊤ := fun h1 =>
    (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h1 ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)))
  have h := (Ideal.height_mono hle).trans (Ideal.height_le_spanFinrank _ hne)
  have h3 : (Ideal.span {t}).spanFinrank ≤ 1 := by
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton t)
  rw [h2] at h
  have h4 : (2 : ℕ∞) ≤ 1 := h.trans (by exact_mod_cast h3)
  exact absurd h4 (by decide)

/-- In a Noetherian local ring whose maximal ideal has height `2`, any family generating the
maximal ideal has at least two members. -/
theorem two_le_of_maximalIdeal_eq_span_range_of_height_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {r : ℕ} (v : Fin r → R)
    (hm : maximalIdeal R = Ideal.span (Set.range v)) (h2 : (maximalIdeal R).height = 2) :
    2 ≤ r := by
  classical
  have h := Ideal.height_le_spanFinrank (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  have h3 : (maximalIdeal R).spanFinrank ≤ r := by
    rw [hm, ← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le.trans (by simp)
  rw [h2] at h
  have h4 : (2 : ℕ∞) ≤ r := h.trans (by exact_mod_cast h3)
  exact_mod_cast h4

open Polynomial in
/-- **The chart at a closed point of the exceptional line.** -/
private theorem chart_data {k : Type*} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k))
    (Zc : Closeds X) (J : X.IdealSheafData) (hJ : J = Scheme.IdealSheafData.vanishingIdeal Zc)
    (h : MMP.Resolution.IsSmoothBlowup sX J) (hirr : IsIrreducible (J.support : Set X))
    (hc : ((2 : ℕ) : ℕ∞) = codimension (⟨_, hirr, J.support.isClosed⟩ : IrreducibleCloseds X))
    (ζ0 : blowUp J) (hζ : IsGenericPoint (blowUpToBase J ζ0) (Zc : Set X))
    (hζ2 : Order.coheight ζ0 = 2) :
    ∃ (y z : X.presheaf.stalk (blowUpToBase J ζ0)) (T0 : (blowUp J).presheaf.stalk ζ0),
      maximalIdeal _ = Ideal.span {y, z} ∧
      (blowUpToBase J).stalkMap ζ0 z = T0 * (blowUpToBase J).stalkMap ζ0 y ∧
      (∀ (a : ℕ) (P : (X.presheaf.stalk (blowUpToBase J ζ0))[X]), P.natDegree ≤ a →
        (∃ j, P.coeff j ∉ maximalIdeal _) →
        (P.map ((blowUpToBase J).stalkMap ζ0).hom).eval T0 ∉ maximalIdeal _ ^ (a + 1)) ∧
      ∀ (ε : blowUp J) (hε : ε ⤳ ζ0), blowUpToBase J ε ∉ (Zc : Set X) →
        IsUnit ((blowUp J).presheaf.stalkSpecializes hε ((blowUpToBase J).stalkMap ζ0 y)) := by
  classical
  have hJsupp : (J.support : Set X) = Zc := hJ ▸ Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
  haveI := MMP.Resolution.isIntegral_subscheme_of_isIrreducible sX J h.2 hirr
  have hη : J.subschemeι (genericPoint J.subscheme) = blowUpToBase J ζ0 := by
    have h1 : IsGenericPoint (J.subschemeι (genericPoint J.subscheme)) (Zc : Set X) := by
      change closure _ = _
      rw [MMP.Resolution.closure_subschemeι_genericPoint, hJsupp]
    exact h1.eq hζ
  obtain ⟨hdim, U0, hU0, hηU0, n, x, hx, hcut⟩ :=
    MMP.Threefold.Resolution.exists_isLocalCoordinates_genericPoint J sX h hirr hc
  rw [hη] at hdim hηU0
  obtain ⟨cd, hU, hηU, x', hx', hrn, hr, hcx⟩ :=
    MMP.Threefold.Resolution.exists_blowupChartData J sX hU0 hηU0 x hx hcut
  obtain ⟨ℓ, hℓ⟩ := MMP.Threefold.Resolution.exists_mem_chart J cd (p := ζ0) hηU
  -- Noetherian local rings
  have : Smooth sX := MMP.Threefold.Resolution.smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hsmB := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    sX J h).1
  have : IsLocallyNoetherian (blowUp J) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase J ≫ sX)
  -- the prime `p` of `η` in `C = 𝒪(U)` is `I_W(U)`
  set η := blowUpToBase J ζ0 with hηdef
  set p := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal with hp
  have hJU : J.ideal ⟨cd.U, hU⟩ = p := by
    subst hJ
    change PrimeSpectrum.vanishingIdeal _ = _
    ext g
    rw [PrimeSpectrum.mem_vanishingIdeal]
    refine ⟨fun hg => hg _ ?_, fun hg P hP => ?_⟩
    · change hU.fromSpec _ ∈ (Zc : Set X)
      rw [hU.fromSpec_primeIdealOf]
      exact hζ.mem
    · have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ⤳ hU.fromSpec P := by
        rw [hU.fromSpec_primeIdealOf]
        exact hζ.specializes hP
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr
        (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1) hg
  have hgenU : J.ideal ⟨cd.U, hU⟩ = Ideal.span (Set.range cd.x) := by
    rw [cd.generates ⟨cd.U, hU⟩ le_rfl]
    congr 1
    ext s
    simp only [Set.mem_range]
    have e : ∀ a : Γ(X, cd.U), (X.presheaf.map (homOfLE (le_refl cd.U)).op).hom a = a := by
      intro a
      have h1 : homOfLE (le_refl cd.U) = 𝟙 cd.U := Subsingleton.elim _ _
      rw [h1, op_id, X.presheaf.map_id]; rfl
    simp only [e]
  -- the local ring `R = 𝒪_{X,η}` and its maximal ideal
  letI : Algebra Γ(X, cd.U) (X.presheaf.stalk η) := X.presheaf.algebra_section_stalk ⟨η, hηU⟩
  haveI hRloc : IsLocalization.AtPrime (X.presheaf.stalk η) p := hU.isLocalization_stalk ⟨η, hηU⟩
  set germR := (X.presheaf.germ cd.U η hηU).hom with hgermR
  have halgR : algebraMap Γ(X, cd.U) (X.presheaf.stalk η) = germR := rfl
  have hmR : maximalIdeal (X.presheaf.stalk η) = Ideal.span (germR '' Set.range cd.x) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← hJU, hgenU, Ideal.map_span, halgR]
  -- there are exactly two generators
  have hr2 : cd.r = 2 := by
    have h1 : (maximalIdeal (X.presheaf.stalk η)).height = 2 := by
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk η)
      rw [hdim] at this
      exact WithBot.coe_injective (this.trans rfl)
    have := two_le_of_maximalIdeal_eq_span_range_of_height_eq_two (germR ∘ cd.x)
      (by rw [hmR, Set.range_comp]) h1
    omega
  obtain ⟨m, hmℓ, hall⟩ : ∃ m : Fin cd.r, m ≠ ℓ ∧ ∀ i : Fin cd.r, i = ℓ ∨ i = m := by
    refine ⟨⟨1 - ℓ.1, by omega⟩, fun h => ?_, fun i => ?_⟩
    · have := congrArg Fin.val h; simp at this; omega
    · have := i.2; have := ℓ.2
      by_cases hi : i.1 = ℓ.1
      · exact Or.inl (Fin.ext hi)
      · exact Or.inr (Fin.ext (by simp; omega))
  set y0 := cd.x ℓ with hy0
  set z0 := cd.x m with hz0
  have hrange : Set.range cd.x = {y0, z0} := by
    ext t
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rcases hall i with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      exacts [⟨ℓ, rfl⟩, ⟨m, rfl⟩]
  have hy0p : y0 ∈ p := hJU ▸ hgenU ▸ Ideal.subset_span ⟨ℓ, rfl⟩
  have hz0p : z0 ∈ p := hJU ▸ hgenU ▸ Ideal.subset_span ⟨m, rfl⟩
  have hpyz : p = Ideal.span {y0, z0} := by rw [← hJU, hgenU, hrange]
  -- the chart ring `B = 𝒪(U_ℓ)`
  set ψ := MMP.Flips.ResolutionInputs.chartPullbackHom cd ℓ with hψ
  set T := MMP.Flips.ResolutionInputs.chartFraction cd ℓ m with hT
  set germA := ((blowUp J).presheaf.germ (cd.chart ℓ) ζ0 hℓ).hom with hgermA
  have hsm : ∀ a, (blowUpToBase J).stalkMap ζ0 (germR a) = germA (ψ a) :=
    fun a => cd.stalkMap_germ ℓ hℓ a
  have hzT : ψ z0 = T * ψ y0 := MMP.Flips.ResolutionInputs.chartPullback_eq_chartFraction_mul cd ℓ m
  refine ⟨germR y0, germR z0, germA T, ?_, ?_, ?_, ?_⟩
  · rw [hmR, hrange, Set.image_insert_eq, Set.image_singleton]
  · rw [hsm, hsm, hzT, map_mul]
  · intro a P hP hPm
    -- clearing denominators
    obtain ⟨b, hb, hbP⟩ := IsLocalization.integerNormalization_spec p.primeCompl P
    set H := IsLocalization.integerNormalization p.primeCompl P with hH
    have hHdeg : H.natDegree ≤ a := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
      by_contra hne
      have h1 := IsLocalization.integerNormalization_support p.primeCompl P
        (Polynomial.mem_support_iff.mpr hne)
      rw [Polynomial.mem_support_iff] at h1
      exact h1 (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP (by exact_mod_cast hN)))
    have hHp : ∃ j, H.coeff j ∉ p := by
      obtain ⟨j, hj⟩ := hPm
      refine ⟨j, fun hjp => hj ?_⟩
      have h1 := congrArg (fun Q => Q.coeff j) hbP
      simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at h1
      have h2 : algebraMap Γ(X, cd.U) (X.presheaf.stalk η) (H.coeff j) ∈ maximalIdeal _ := by
        rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p]
        exact Ideal.mem_map_of_mem _ hjp
      rw [h1, Algebra.smul_def] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units _ ⟨b, hb⟩)).mp h2
    -- the presentation of the chart ring
    set ρ : Γ(X, cd.U)[X] →+* Γ(blowUp J, cd.chart ℓ) := Polynomial.eval₂RingHom ψ T with hρ
    have hρC : ρ.comp Polynomial.C = ψ := by ext; simp [ρ]
    let i0 : {i : Fin cd.r // i ≠ ℓ} := ⟨m, hmℓ⟩
    have hi0 : ∀ i : {i : Fin cd.r // i ≠ ℓ}, i = i0 := fun i =>
      Subtype.ext ((hall i.1).resolve_left i.2)
    obtain ⟨hsurj, hker⟩ :=
      MMP.Flips.ResolutionInputs.chartPresentation_surjective_and_ker cd sX hU x' hx' hrn hcx ℓ
    set CP := MMP.Flips.ResolutionInputs.chartPresentation cd ℓ with hCP
    set ι : Γ(X, cd.U)[X] →+* MvPolynomial {i : Fin cd.r // i ≠ ℓ} Γ(X, cd.U) :=
      Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i0) with hι
    set θ : MvPolynomial {i : Fin cd.r // i ≠ ℓ} Γ(X, cd.U) →+* Γ(X, cd.U)[X] :=
      MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) with hθ
    have hCPι : CP.comp ι = ρ := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · simp [ρ, ι, CP, MMP.Flips.ResolutionInputs.chartPresentation, ψ]
      · simp [ρ, ι, CP, MMP.Flips.ResolutionInputs.chartPresentation, T, i0]
    have hθι : θ.comp ι = RingHom.id _ := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;> simp [θ, ι]
    have hρθ : ρ.comp θ = CP := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · simp [ρ, θ, CP, MMP.Flips.ResolutionInputs.chartPresentation, ψ]
      · rw [hi0 i]
        simp [ρ, θ, CP, MMP.Flips.ResolutionInputs.chartPresentation, T, i0]
    have hρs : Function.Surjective ρ := fun t => by
      obtain ⟨Q, hQ⟩ := hsurj t
      exact ⟨θ Q, by rw [← hQ, ← RingHom.comp_apply, hρθ]⟩
    have hxp : ∀ i, cd.x i ∈ p := fun i => hJU ▸ hgenU ▸ Ideal.subset_span ⟨i, rfl⟩
    have hkerρ : RingHom.ker ρ ≤ p.map (Polynomial.C : Γ(X, cd.U) →+* Γ(X, cd.U)[X]) := by
      intro H' hH'
      have h1 : ι H' ∈ RingHom.ker CP := by
        rwa [RingHom.mem_ker, ← RingHom.comp_apply, hCPι]
      rw [hker] at h1
      have h2 : ι H' ∈ p.map (MvPolynomial.C : Γ(X, cd.U) →+* MvPolynomial _ _) := by
        refine (Ideal.span_le.mpr ?_) h1
        rintro _ ⟨i, rfl⟩
        exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ (hxp _))
          (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hxp _)))
      have h3 := Ideal.mem_map_of_mem θ h2
      rw [Ideal.map_map, show θ.comp MvPolynomial.C = Polynomial.C from by ext; simp [θ]] at h3
      rwa [← RingHom.comp_apply θ ι, hθι] at h3
    -- the prime `q` of `ζ0` in the chart ring
    have hVaff := MMP.Flips.ResolutionInputs.isAffineOpen_chart cd hU ℓ
    set q := (hVaff.primeIdealOf ⟨ζ0, hℓ⟩).asIdeal with hq
    letI : Algebra Γ(blowUp J, cd.chart ℓ) ((blowUp J).presheaf.stalk ζ0) :=
      (blowUp J).presheaf.algebra_section_stalk ⟨ζ0, hℓ⟩
    haveI : IsLocalization.AtPrime ((blowUp J).presheaf.stalk ζ0) q :=
      hVaff.isLocalization_stalk ⟨ζ0, hℓ⟩
    have halgA : algebraMap Γ(blowUp J, cd.chart ℓ) ((blowUp J).presheaf.stalk ζ0) = germA := rfl
    have hqmax : q.map (algebraMap _ ((blowUp J).presheaf.stalk ζ0)) = maximalIdeal _ :=
      IsLocalization.AtPrime.map_eq_maximalIdeal _ _
    have hloc : ∀ g, (blowUpToBase J).stalkMap ζ0 (germR g) ∈ maximalIdeal _ ↔
        germR g ∈ maximalIdeal _ := by
      intro g
      refine ⟨fun h1 => ?_, fun h1 => map_nonunit _ _ h1⟩
      by_contra h2
      exact (IsLocalRing.notMem_maximalIdeal.mpr
        ((IsLocalRing.notMem_maximalIdeal.mp h2).map ((blowUpToBase J).stalkMap ζ0).hom)) h1
    have hqp : q.comap (ρ.comp Polynomial.C) = p := by
      rw [hρC]
      ext g
      rw [Ideal.mem_comap, hq, mem_primeIdealOf_iff, ← hsm, hloc, hp, mem_primeIdealOf_iff]
    have hgy : germR y0 ∈ maximalIdeal (X.presheaf.stalk η) := by
      rw [hmR]; exact Ideal.subset_span ⟨y0, ⟨ℓ, rfl⟩, rfl⟩
    have hqne : ¬ q ≤ (p.map (Polynomial.C : Γ(X, cd.U) →+* Γ(X, cd.U)[X])).map ρ := by
      intro hle
      rw [Ideal.map_map, hρC, hpyz, Ideal.map_span] at hle
      have hle2 : q ≤ Ideal.span {ψ y0} := by
        refine hle.trans (Ideal.span_le.mpr ?_)
        rintro _ ⟨t, ht, rfl⟩
        rcases ht with rfl | rfl
        · exact Ideal.subset_span rfl
        · rw [hzT]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      have hmA : maximalIdeal ((blowUp J).presheaf.stalk ζ0) ≤ Ideal.span {germA (ψ y0)} := by
        rw [← hqmax]
        refine (Ideal.map_mono hle2).trans ?_
        rw [Ideal.map_span, Set.image_singleton, halgA]
      have hyA : germA (ψ y0) ∈ maximalIdeal ((blowUp J).presheaf.stalk ζ0) := by
        rw [← hsm]; exact (hloc y0).mpr hgy
      have h1 : (maximalIdeal ((blowUp J).presheaf.stalk ζ0)).height = 2 := by
        have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := (blowUp J).presheaf.stalk ζ0)
        rw [ringKrullDim_stalk_eq_coheight, hζ2] at this
        exact WithBot.coe_injective (this.trans rfl)
      exact maximalIdeal_not_le_span_singleton_of_height_eq_two h1 hyA hmA
    have hcal := algebraMap_notMem_pow_of_coeff_notMem (A := (blowUp J).presheaf.stalk ζ0)
      p ρ hρs hkerρ q hqp hqne a H hHdeg hHp
    rw [hqmax] at hcal
    intro hmem
    apply hcal
    have hcomp : germA.comp ψ = ((blowUpToBase J).stalkMap ζ0).hom.comp germR := by
      ext g; exact (hsm g).symm
    have heval : algebraMap _ ((blowUp J).presheaf.stalk ζ0) (ρ H) =
        (blowUpToBase J).stalkMap ζ0 (algebraMap _ (X.presheaf.stalk η) b) *
          (P.map ((blowUpToBase J).stalkMap ζ0).hom).eval (germA T) := by
      rw [halgA, hρ, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, hcomp,
        ← Polynomial.eval_map, ← Polynomial.map_map, halgR.symm, hbP,
        ← algebraMap_smul (X.presheaf.stalk η) b P, Polynomial.smul_eq_C_mul,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
    rw [heval]
    exact Ideal.mul_mem_left _ _ hmem
  · intro ε hε hεZ
    have hεch : ε ∈ cd.chart ℓ := hε.mem_open (cd.chart ℓ).isOpen hℓ
    have hεU : blowUpToBase J ε ∈ cd.U := cd.chart_le ℓ hεch
    have hspec : ∀ t, (blowUp J).presheaf.stalkSpecializes hε (germA t) =
        (blowUp J).presheaf.germ (cd.chart ℓ) ε hεch t := fun t =>
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ t
    have hsmε : ∀ a, (blowUpToBase J).stalkMap ε (X.presheaf.germ cd.U _ hεU a) =
        (blowUp J).presheaf.germ (cd.chart ℓ) ε hεch (ψ a) := fun a => cd.stalkMap_germ ℓ hεch a
    have key : IsUnit (X.presheaf.germ cd.U _ hεU y0) ∨ IsUnit (X.presheaf.germ cd.U _ hεU z0) := by
      by_contra hcon
      push Not at hcon
      apply hεZ
      rw [← hJsupp]
      have hmem : blowUpToBase J ε ∈ (J.support : Set X) ∩ cd.U := by
        rw [Scheme.IdealSheafData.coe_support_inter J ⟨cd.U, hU⟩]
        refine ⟨(X.mem_zeroLocus_iff _ _).mpr fun f hf => ?_, hεU⟩
        rw [Scheme.mem_basicOpen X f _ hεU]
        have hf' : f ∈ Ideal.span {y0, z0} := by
          have : f ∈ J.ideal ⟨cd.U, hU⟩ := hf
          rwa [hgenU, hrange] at this
        have h1 := Ideal.mem_map_of_mem (X.presheaf.germ cd.U _ hεU).hom hf'
        rw [Ideal.map_span] at h1
        have h2 : X.presheaf.germ cd.U _ hεU f ∈ maximalIdeal _ := by
          refine (Ideal.span_le.mpr ?_) h1
          rintro _ ⟨t, ht, rfl⟩
          rcases ht with rfl | rfl
          · exact (IsLocalRing.mem_maximalIdeal _).mpr hcon.1
          · exact (IsLocalRing.mem_maximalIdeal _).mpr hcon.2
        exact (IsLocalRing.mem_maximalIdeal _).mp h2
      exact hmem.1
    have hgoal : (blowUp J).presheaf.stalkSpecializes hε
        ((blowUpToBase J).stalkMap ζ0 (germR y0)) =
        (blowUpToBase J).stalkMap ε (X.presheaf.germ cd.U _ hεU y0) := by
      rw [hsm, hspec, hsmε]
    rw [hgoal]
    rcases key with hu | hu
    · exact hu.map _
    · have h1 := hu.map ((blowUpToBase J).stalkMap ε).hom
      rw [hsmε, hzT, map_mul, ← hsmε] at h1
      exact isUnit_of_mul_isUnit_right h1

/-- The blow-up of a regular centre in a regular variety over a perfect field is a smooth
blow-up. -/
private theorem isSmoothBlowup_vanishingIdeal {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX)
    (hXreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (W : IrreducibleCloseds X)
    (hWreg : ∀ w ∈ (W : Set X), IsRegularLocalRing (X.presheaf.stalk w ⧸
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)).stalkIdeal w)) :
    MMP.Resolution.IsSmoothBlowup sX
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)) := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  set J := Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)
  refine ⟨isSmoothScheme_of_forall_isRegularLocalRing sX hXreg,
    isSmoothScheme_of_forall_isRegularLocalRing _ fun y => ?_⟩
  have hmem : J.subschemeι y ∈ (W : Set X) := by
    have h1 : J.subschemeι y ∈ (J.support : Set X) := by
      rw [← J.range_subschemeι]; exact ⟨y, rfl⟩
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
  have hsurj : Function.Surjective (J.subschemeι.stalkMap y).hom :=
    J.subschemeι.stalkMap_surjective y
  have e := (Ideal.quotEquivOfEq (J.ker_stalkMap_subschemeι y).symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)
  have := hWreg _ hmem
  exact IsRegularLocalRing.of_ringEquiv e

open Polynomial in
/-- The chart data at a point transport along an isomorphism of schemes. -/
private theorem transport_chart_data {X Y Y' : Scheme} (e : Y ⟶ Y') [IsIso e] (π' : Y' ⟶ X)
    (ζ : Y) (S : Set X)
    (y z : X.presheaf.stalk (π' (e ζ))) (T0 : Y'.presheaf.stalk (e ζ))
    (hm : maximalIdeal (X.presheaf.stalk (π' (e ζ))) = Ideal.span {y, z})
    (hT : π'.stalkMap (e ζ) z = T0 * π'.stalkMap (e ζ) y)
    (hc : ∀ (a : ℕ) (P : (X.presheaf.stalk (π' (e ζ)))[X]), P.natDegree ≤ a →
      (∃ j, P.coeff j ∉ maximalIdeal _) →
      (P.map (π'.stalkMap (e ζ)).hom).eval T0 ∉ maximalIdeal (Y'.presheaf.stalk (e ζ)) ^ (a + 1))
    (hd : ∀ ε (h : ε ⤳ e ζ), π' ε ∉ S →
      IsUnit (Y'.presheaf.stalkSpecializes h (π'.stalkMap (e ζ) y))) :
    ∃ T0' : Y.presheaf.stalk ζ,
      (e ≫ π').stalkMap ζ z = T0' * (e ≫ π').stalkMap ζ y ∧
      (∀ (a : ℕ) (P : (X.presheaf.stalk (π' (e ζ)))[X]), P.natDegree ≤ a →
        (∃ j, P.coeff j ∉ maximalIdeal _) →
        (P.map ((e ≫ π').stalkMap ζ).hom).eval T0' ∉ maximalIdeal (Y.presheaf.stalk ζ) ^ (a + 1)) ∧
      ∀ ε (h : ε ⤳ ζ), (e ≫ π') ε ∉ S →
        IsUnit (Y.presheaf.stalkSpecializes h ((e ≫ π').stalkMap ζ y)) := by
  have : IsIso (e.stalkMap ζ) := inferInstanceAs (IsIso (e.toLRSHom.stalkMap ζ))
  set φ := (asIso (e.stalkMap ζ)).commRingCatIsoToRingEquiv with hφ
  have hφa : ∀ t, φ t = e.stalkMap ζ t := fun _ => rfl
  have hcomp : ∀ t : X.presheaf.stalk (π' (e ζ)),
      (e ≫ π').stalkMap ζ t = e.stalkMap ζ (π'.stalkMap (e ζ) t) := by
    intro t; rw [Scheme.Hom.stalkMap_comp]; rfl
  refine ⟨e.stalkMap ζ T0, ?_, ?_, ?_⟩
  · rw [hcomp, hcomp, hT, map_mul]
  · intro a P hP hPm hmem
    apply hc a P hP hPm
    rw [← mem_maximalIdeal_pow_iff_of_ringEquiv φ, hφa]
    have hc2 : (e.stalkMap ζ).hom.comp (π'.stalkMap (e ζ)).hom = ((e ≫ π').stalkMap ζ).hom := by
      ext t; exact (hcomp t).symm
    have h1 : (P.map ((e ≫ π').stalkMap ζ).hom).eval (e.stalkMap ζ T0) =
        e.stalkMap ζ ((P.map (π'.stalkMap (e ζ)).hom).eval T0) := by
      refine (Polynomial.eval_map _ _).trans ?_
      refine Eq.trans ?_ (congrArg (e.stalkMap ζ).hom (Polynomial.eval_map _ _).symm)
      rw [Polynomial.hom_eval₂, hc2]
      rfl
    rwa [h1] at hmem
  · intro ε h hε
    have h' : e ε ⤳ e ζ := h.map e.continuous
    have hu := (hd (e ε) h' hε).map (e.stalkMap ε).hom
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply] at hu
    rwa [hcomp]

/-- A downward-closed condition with a finite bound: the `toNat` comparison of two suprema. -/
private theorem toNat_iSup_le_toNat_iSup {QE QD : ℕ → Prop} (hQD0 : QD 0)
    (hanti : ∀ s t, s ≤ t → QD t → QD s) (hfin : ∃ a, ¬ QD (a + 1))
    (H : ∀ s a, QE s → ¬ QD (a + 1) → s ≤ a) :
    (⨆ (s : ℕ) (_ : QE s), (s : ℕ∞)).toNat ≤ (⨆ (a : ℕ) (_ : QD a), (a : ℕ∞)).toNat := by
  classical
  set a0 := Nat.find hfin with ha0
  have hna0 : ¬ QD (a0 + 1) := Nat.find_spec hfin
  have hQa0 : QD a0 := by
    rcases Nat.eq_zero_or_pos a0 with h0 | h0
    · rwa [h0]
    · have h1 := Nat.find_min hfin (show a0 - 1 < a0 by omega)
      rwa [not_not, Nat.sub_add_cancel h0] at h1
  have hD : (⨆ (a : ℕ) (_ : QD a), (a : ℕ∞)) = a0 := by
    refine le_antisymm (iSup₂_le fun a ha => ?_) (le_iSup₂_of_le a0 hQa0 le_rfl)
    have : a ≤ a0 := by
      by_contra hlt
      exact hna0 (hanti _ _ (by omega) ha)
    exact_mod_cast this
  have hE : (⨆ (s : ℕ) (_ : QE s), (s : ℕ∞)) ≤ a0 :=
    iSup₂_le fun s hs => by exact_mod_cast H s a0 hs hna0
  rw [hD, ENat.toNat_coe]
  exact ENat.toNat_le_of_le_coe hE

/-- The ideal of a prime divisor at a point of an integral scheme is nonzero. -/
private theorem stalkIdeal_ne_bot {X : Scheme} [IsIntegral X] (D : MMP.Mori.PrimeDivisor X)
    (x : X) : D.idealSheaf.stalkIdeal x ≠ ⊥ := by
  have hD : D.idealSheaf ≠ ⊥ := by
    intro h0
    have hsupp : D.support = Set.univ := by
      change ((D.idealSheaf.support : Set X)) = _
      rw [h0, Scheme.IdealSheafData.support_bot]; rfl
    have hgen : IsGenericPoint D.genericPoint (Set.univ : Set X) := by
      rw [← hsupp, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    have h1 := D.coheight_genericPoint
    have h2 : Order.coheight D.genericPoint = 0 := by
      rw [Order.coheight_eq_zero]
      intro b hb
      have hb' : b ⤳ D.genericPoint := hb
      have hbgen : IsGenericPoint b (Set.univ : Set X) := by
        refine (isGenericPoint_iff_specializes).mpr fun w => ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        exact hb'.trans (hgen.specializes (Set.mem_univ w))
      exact (hbgen.eq hgen).symm ▸ le_rfl
    rw [h2] at h1
    exact absurd h1 (by decide)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hne := Stacks.IdealSheaf.ideal_ne_bot D.idealSheaf hD (U := ⟨V, hV⟩) hxV
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro h0
  have h1 := D.idealSheaf.germ_mem_stalkIdeal ⟨V, hV⟩ hxV hg
  rw [h0, Ideal.mem_bot] at h1
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact hg0 (germ_injective_of_isIntegral X x hxV (h1.trans (map_zero _).symm))

/-- The prime-divisor case: if the strict transform of a prime divisor `D` under the blow-up of
a regular codimension-two centre `W` is the prime divisor `E`, and `Z ⊆ π⁻¹ W` of codimension
two dominates `W`, then `mult_Z E ≤ mult_W D`. -/
private theorem multiplicityAlong_strictTransform_le {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : MMP.Mori.IsVariety k sX)
    (hXreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (W : IrreducibleCloseds X) (hW : codimension W = 2)
    (hWreg : ∀ w ∈ (W : Set X), IsRegularLocalRing (X.presheaf.stalk w ⧸
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)).stalkIdeal w))
    (Z : IrreducibleCloseds (Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))))
    (hZ : codimension Z = 2)
    (hZW : Stacks.Blowup.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))
        Z.isIrreducible.genericPoint = W.isIrreducible.genericPoint)
    (D : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor _)
    (hDE : inverseTransformPrimeDivisor (Stacks.Blowup.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))) D = some E) :
    (E.multiplicityAlong Z).toNat ≤ (D.multiplicityAlong W).toNat := by
  classical
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsIntegral X := hX.toIsIntegral
  have hsb := isSmoothBlowup_vanishingIdeal sX hX hXreg W hWreg
  revert Z E
  generalize hJ : Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X) = J at hsb
  intro Z hZ hZW E hDE
  have hJsupp : (J.support : Set X) = W := hJ ▸ Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hirr : IsIrreducible (J.support : Set X) := hJsupp ▸ W.isIrreducible
  have hc : ((2 : ℕ) : ℕ∞) =
      codimension (⟨_, hirr, J.support.isClosed⟩ : IrreducibleCloseds X) := by
    have : (⟨_, hirr, J.support.isClosed⟩ : IrreducibleCloseds X) = W := by ext1; exact hJsupp
    rw [this, hW]; rfl
  set e := Stacks.Blowup.blowUpIso J with he
  set ζ := Z.isIrreducible.genericPoint with hζdef
  have hcomp : e.hom ≫ blowUpToBase J = Stacks.Blowup.blowUpToBase J :=
    Stacks.Blowup.blowUpIso_hom_comp J
  have hζη : (e.hom ≫ blowUpToBase J) ζ = W.isIrreducible.genericPoint := by
    rwa [hcomp]
  have hζgen : IsGenericPoint (blowUpToBase J (e.hom ζ)) (W : Set X) :=
    hζη ▸ isGenericPoint_genericPoint W
  have hζ2 : Order.coheight (e.hom ζ) = 2 := by
    rw [coheight_eq_of_isOpenImmersion e.hom, ← codimension_eq_coheight_genericPoint, hZ]
  obtain ⟨y, z, T0, hm, hT, hcc, hd⟩ :=
    chart_data sX ⟨W, W.isClosed⟩ J hJ.symm hsb hirr hc (e.hom ζ) hζgen hζ2
  obtain ⟨T0', hT', hc', hd'⟩ :=
    transport_chart_data e.hom (blowUpToBase J) ζ (W : Set X) y z T0 hm hT hcc hd
  -- a second point over `η`: the generic point of the exceptional divisor
  have hξ : ∃ ξ, ξ ≠ ζ ∧ (e.hom ≫ blowUpToBase J) ξ = (e.hom ≫ blowUpToBase J) ζ := by
    have hc1 : 1 ≤ codimension (⟨_, hirr, J.support.isClosed⟩ : IrreducibleCloseds X) := by
      rw [← hc]; norm_num
    obtain ⟨-, F', -, -, hFimg⟩ :=
      MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sX J hsb
        hirr hc1
    have hgenπ : IsGenericPoint (blowUpToBase J F'.genericPoint) (W : Set X) := by
      change closure {_} = _
      rw [← Set.image_singleton, (blowUpToBase J).isClosedMap.closure_image_eq_of_continuous
        (blowUpToBase J).continuous, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        hFimg, hJsupp]
    have hinv : e.hom (e.inv F'.genericPoint) = F'.genericPoint := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
    refine ⟨e.inv F'.genericPoint, fun h => ?_, ?_⟩
    · have h1 : Order.coheight (e.inv F'.genericPoint) = 1 := by
        rw [coheight_eq_of_isOpenImmersion e.inv]
        exact MMP.Mori.PrimeDivisor.coheight_genericPoint F'
      have h2 : Order.coheight ζ = 2 := by
        rw [← coheight_eq_of_isOpenImmersion e.hom]; exact hζ2
      rw [h, h2] at h1
      exact absurd h1 (by decide)
    · change blowUpToBase J (e.hom (e.inv F'.genericPoint)) = blowUpToBase J (e.hom ζ)
      rw [hinv]
      exact hgenπ.eq hζgen
  have hDE' : inverseTransformPrimeDivisor (e.hom ≫ blowUpToBase J) D = some E := by
    rwa [hcomp]
  have hSgen : ∀ s ∈ (W : Set X), (e.hom ≫ blowUpToBase J) ζ ⤳ s := fun s hs => by
    rw [hζη]; exact (isGenericPoint_genericPoint W).specializes hs
  have key : ∀ (w : X) (_ : (e.hom ≫ blowUpToBase J) ζ = w) (s a : ℕ),
      E.idealSheaf.stalkIdeal ζ ≤ maximalIdeal _ ^ s →
      ¬ D.idealSheaf.stalkIdeal w ≤ maximalIdeal _ ^ (a + 1) → s ≤ a := by
    rintro w rfl s a hs ha
    exact le_of_stalkIdeal_le (e.hom ≫ blowUpToBase J) ζ hDE' (W : Set X) hSgen hξ y z T0' hm
      hT' hc' hd' s a hs ha
  unfold MMP.Mori.PrimeDivisor.multiplicityAlong
  refine toNat_iSup_le_toNat_iSup ?_ ?_ ?_ (fun s a hs ha => key _ hζη s a hs ha)
  · rw [pow_zero, Ideal.one_eq_top]; exact le_top
  · intro s t hst h; exact h.trans (Ideal.pow_le_pow_right hst)
  · by_contra hcon
    push Not at hcon
    apply stalkIdeal_ne_bot D W.isIrreducible.genericPoint
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
    refine le_iInf fun i => ?_
    rcases i with _ | i
    · rw [pow_zero, Ideal.one_eq_top]; exact le_top
    · exact hcon i

/-- **Multiplicity of a strict transform under the blow-up of a regular codimension-two centre.**
Let `X` be a regular variety over a field `k` of characteristic zero and `W ⊆ X` a regular
irreducible closed subset of codimension two, `π : X' ⟶ X` the blow-up of the vanishing ideal of
`W`. If `Z ⊆ π⁻¹(W)` is an irreducible closed subset of codimension two of
`X'` with `π(η_Z) = η_W`, then for every effective `ℚ`-divisor `P` on `X`,
`∑_Γ coeff_Γ(π⁻¹_* P) · mult_Z Γ ≤ ∑_Γ coeff_Γ(P) · mult_W Γ`. -/
@[mmp "lem_mmp_regular_codimension_two_strict_transform_order"]
theorem multiplicityAlong_inverseTransformDivisor_blowUpToBase_le {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsVariety k sX)
    (hXreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (W : IrreducibleCloseds X) (hW : codimension W = 2)
    (hWreg : ∀ w ∈ (W : Set X), IsRegularLocalRing (X.presheaf.stalk w ⧸
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)).stalkIdeal w))
    (Z : IrreducibleCloseds (Stacks.Blowup.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))))
    (hZ : codimension Z = 2)
    (hZF : ∀ z ∈ (Z : Set _), Stacks.Blowup.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)) z ∈ (W : Set X))
    (hZW : Stacks.Blowup.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))
        Z.isIrreducible.genericPoint = W.isIrreducible.genericPoint)
    (P : QDivisor X) (hP : 0 ≤ P) :
    ((inverseTransformDivisor (Stacks.Blowup.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))) P).sum fun Γ b =>
        b * ((Γ.multiplicityAlong Z).toNat : ℚ)) ≤
      P.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
  set π := Stacks.Blowup.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))
  conv_lhs => rw [← Finsupp.sum_single P]
  rw [map_finsuppSum, Finsupp.sum_sum_index (by simp) (by intros; ring)]
  refine Finsupp.sum_le_sum fun D _ => ?_
  have hPD : 0 ≤ P D := hP D
  rcases h : inverseTransformPrimeDivisor π D with _ | E
  · rw [inverseTransformDivisor_single_of_eq_none h]
    simp only [Finsupp.sum_zero_index]
    positivity
  · rw [inverseTransformDivisor_single_of_eq_some h, Finsupp.sum_single_index (by simp)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast
      multiplicityAlong_strictTransform_le sX hX hXreg W hW hWreg Z hZ hZW D E h) hPD

end StrictTransform

end MMP.Mori

namespace MMP.Flips

open MMP.Mori
open scoped WithZero

/-! ### The order valuation along a regular centre -/

section RegularCentreOrder

/-- The order function is characterized by `φ ∈ 𝔪ⁿ`, `φ ∉ 𝔪ⁿ⁺¹`. -/
private theorem maximalIdealOrder_eq_of_mem {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {φ : R} (hφ : φ ≠ 0) {n : ℕ}
    (h1 : φ ∈ IsLocalRing.maximalIdeal R ^ n) (h2 : φ ∉ IsLocalRing.maximalIdeal R ^ (n + 1)) :
    maximalIdealOrder R φ = n := by
  obtain ⟨h3, h4⟩ := maximalIdealOrder_spec hφ
  apply le_antisymm
  · by_contra hlt
    exact h2 (Ideal.pow_le_pow_right (by omega) h3)
  · by_contra hlt
    exact h4 (Ideal.pow_le_pow_right (by omega) h1)

/-- The order function is invariant under isomorphisms of local rings. -/
private theorem maximalIdealOrder_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] (e : R ≃+* S)
    {a : R} (ha : a ≠ 0) : maximalIdealOrder S (e a) = maximalIdealOrder R a := by
  obtain ⟨h1, h2⟩ := maximalIdealOrder_spec ha
  exact maximalIdealOrder_eq_of_mem (by simpa using ha)
    ((mem_maximalIdeal_pow_iff_of_ringEquiv e _ a).mpr h1)
    fun h3 => h2 ((mem_maximalIdeal_pow_iff_of_ringEquiv e _ a).mp h3)

/-- **A smooth neighbourhood of `η_V` in which `V` is smooth.** If `Y` is a variety over a
perfect field and `V ⊆ Y` an irreducible closed subset with generic point `x` and `𝒪_{Y,x}`
regular, there is an open `U ∋ x` such that `U` and `V ∩ U` (with its reduced structure, the
inverse image of that of `V`) are smooth over `k`, with generic point `x` and the codimension of
`V`. -/
private theorem exists_smoothBlowup {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsVariety k s) (V : IrreducibleCloseds Y) (x : Y)
    (hx : x = V.isIrreducible.genericPoint)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk x)) :
    ∃ (U : Y.Opens) (hxU : x ∈ U)
      (_ : MMP.Resolution.IsSmoothBlowup (U.ι ≫ s)
        ((Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds Y)).comap U.ι))
      (hirr : IsIrreducible (((Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds Y)).comap U.ι).support : Set U)),
      hirr.genericPoint = ⟨x, hxU⟩ ∧
        codimension (⟨_, hirr, ((Scheme.IdealSheafData.vanishingIdeal
          (⟨V, V.isClosed⟩ : Closeds Y)).comap U.ι).support.isClosed⟩ : IrreducibleCloseds U) =
          Order.coheight x := by
  have : LocallyOfFiniteType s := hY.toLocallyOfFiniteType
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds Y) with hZ
  have hZsupp : (Z.support : Set Y) = V := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsIntegral Z.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ V.isIrreducible
  set ζ := genericPoint Z.subscheme with hζ
  have hζx : Z.subschemeι ζ = x := by
    have h1 : IsGenericPoint (Z.subschemeι ζ) (V : Set Y) := by
      change closure _ = _
      rw [MMP.Resolution.closure_subschemeι_genericPoint, hZsupp]
    rw [hx]; exact h1.eq (isGenericPoint_genericPoint V)
  set S := smoothLocus (Z.subschemeι ≫ s) with hS
  have hζreg : IsRegularLocalRing Z.subscheme.functionField := inferInstance
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing_of_perfectField _ ζ).mpr hζreg
  set T : Set Y := Z.subschemeι '' (S : Set Z.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : x ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (Z.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  set R := smoothLocus s with hR
  have hxR : x ∈ R := (mem_smoothLocus_iff_isRegularLocalRing_of_perfectField s x).mpr hreg
  set U : Y.Opens := R ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩ with hU
  have hxU : x ∈ U := ⟨hxR, hxT⟩
  set I := Z.comap U.ι with hI
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' V := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change U.ι ⁻¹' (Z.support : Set Y) = _
    rw [hZsupp]
  have hUsm : IsSmoothScheme (U.ι ≫ s) :=
    isSmoothScheme_of_forall_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((mem_smoothLocus_iff_isRegularLocalRing_of_perfectField s _).mp u.2.1)
  have e : I.subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
      Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  have hIsm : IsSmoothScheme (I.subschemeι ≫ U.ι ≫ s) := by
    refine isSmoothScheme_of_forall_isRegularLocalRing _ fun y => ?_
    set j := (Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι with hj
    have hjy : Z.subschemeι (j y) = U.ι (I.subschemeι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
    refine isRegularLocalRing_of_isOpenImmersion j y
      ((mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (Z.subschemeι ≫ s) _).mp ?_)
    by_contra hns
    exact (I.subschemeι y).2.2 ⟨j y, hns, hjy⟩
  have hxgen : IsGenericPoint x (V : Set Y) := hx ▸ isGenericPoint_genericPoint V
  let xU : U.toScheme := ⟨x, hxU⟩
  have hxU' : U.ι xU = x := rfl
  have hpre' : IsGenericPoint xU (I.support : Set U.toScheme) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hxU', hxgen.specializes_iff_mem]
    change _ ↔ y ∈ (I.support : Set U.toScheme)
    rw [hIsupp]
    rfl
  have hirr : IsIrreducible (I.support : Set U.toScheme) := hpre'.isIrreducible
  have hgen : hirr.genericPoint = xU := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    rw [I.support.isClosed.closure_eq] at h1
    exact h1.eq hpre'
  refine ⟨U, hxU, ⟨hUsm, hIsm⟩, hirr, hgen, ?_⟩
  have hcl : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U.toScheme) =
      IrreducibleCloseds.closureSingleton xU := by
    ext1
    exact hpre'.symm
  rw [hcl, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  exact (coheight_eq_of_isOpenImmersion U.ι (x := xU)).symm

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- **The exceptional divisor of the blow-up of a smooth neighbourhood of `η_V`.** Let `Y` be a
normal variety over a perfect field and `V ⊆ Y` an irreducible closed subset of codimension
`≥ 2` with generic point `x` and `𝒪_{Y,x}` regular. On a neighbourhood `U` of `x` on which `Y` and
`V` are smooth, the exceptional prime `F` of `Bl_{V ∩ U} U` is a divisor over `Y`; its model is
an open subscheme of `Bl_V Y` containing every point over `x`, `F` is the only prime of the model
over `x`, and its valuation is the order function of `𝒪_{Y,x}`. -/
private theorem exists_divisorOver_smoothBlowup {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} [IsIntegral Y] {s : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k s)
    (V : IrreducibleCloseds Y) (hV : 2 ≤ codimension V) (x : Y)
    (hx : x = V.isIrreducible.genericPoint) (hreg : IsRegularLocalRing (Y.presheaf.stalk x)) :
    ∃ (D : DivisorOver k s) (h : D.Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds Y))),
      IsOpenImmersion h ∧ h ≫ blowUpToBase _ = D.f ∧ D.f D.E.genericPoint = x ∧
      (∀ b, blowUpToBase _ b = x → b ∈ Set.range h) ∧
      (∀ a : D.Y, D.f a = x → Order.coheight a = 1 → a = D.E.genericPoint) ∧
      ∀ g : Y.presheaf.stalk x, g ≠ 0 →
        D.valuation (algebraMap _ Y.functionField g) =
          WithZero.exp (-(maximalIdealOrder _ g : ℤ)) := by
  have : LocallyOfFiniteType s := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds Y) with hZ
  obtain ⟨U, hxU, hsb, hirr, hgen, hcod⟩ := exists_smoothBlowup hY.1 V x hx hreg
  set I := Z.comap U.ι with hI
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have hUnv := isNormalVariety_ι hY U
  have : LocallyOfFiniteType (U.ι ≫ s) := hUnv.1.toLocallyOfFiniteType
  -- the codimension `c` of the centre
  have hcx : codimension V = Order.coheight x := by
    rw [codimension_eq_coheight_genericPoint, hx]
  have hfin : Order.coheight x ≠ ⊤ := by
    have h1 := ringKrullDim_stalk_eq_coheight x
    have h2 := ringKrullDim_lt_top (R := Y.presheaf.stalk x)
    intro htop
    rw [h1, htop] at h2
    exact lt_irrefl _ h2
  set c := (Order.coheight x).toNat with hcdef
  have hcc : (c : ℕ∞) = Order.coheight x := by rw [hcdef, ENat.coe_toNat hfin]
  have hc : (c : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcod, hcc]
  have hc2 : 2 ≤ c := by
    have : ((2 : ℕ) : ℕ∞) ≤ (c : ℕ∞) := by rwa [hcc, ← hcx]
    exact_mod_cast this
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [← hc]; exact_mod_cast (by omega : 1 ≤ c)
  -- the dimension of `U`
  have : QuasiCompact (U.ι ≫ s) := hUnv.1.toQuasiCompact
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ s)
  have : Nonempty (IrreducibleCloseds U) := ⟨IrreducibleCloseds.closureSingleton ⟨x, hxU⟩⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim U = n := by
    have h1 := AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType k (U.ι ≫ s)
    have h2 : topologicalKrullDim U ≠ ⊥ := by
      intro h0
      have := Order.krullDim_nonneg (α := IrreducibleCloseds U)
      exact absurd (h0 ▸ this : (0 : WithBot ℕ∞) ≤ ⊥) (by simp)
    generalize topologicalKrullDim U = d at h1 h2
    induction d using WithBot.recBotCoe with
    | bot => exact absurd rfl h2
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd rfl h1
      | coe d => exact ⟨d, rfl⟩
  obtain ⟨hvarB, hsmB, -, hbirπ, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ s) hUnv.1 hn I hsb hirr hc hc2
  obtain ⟨hordE, -⟩ :=
    MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
      (U.ι ≫ s) hUnv.1 I hsb hirr hc hc2 hn
  set π := blowUpToBase I with hπ
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have : IsDominant π := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1
  have : LocallyOfFiniteType (π ≫ U.ι ≫ s) := hvarB.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ U.ι ≫ s)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := hsmB
  have : IsNormal (blowUp I) := AlgebraicGeometry.isNormal_of_smooth (π ≫ U.ι ≫ s)
  have : IsDominant (π ≫ U.ι) := inferInstance
  set Eex := MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ s) I hsb hirr hc1 with hEex
  have hnv : IsNormalVariety k ((π ≫ U.ι) ≫ s) := by
    rw [Category.assoc]; exact ⟨hvarB, inferInstance⟩
  have hbir : IsBirationalMorphism (π ≫ U.ι) := by
    obtain ⟨O, hO, hOi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hbirπ
    have : IsOpenImmersion (O.ι ≫ π ≫ U.ι) := by
      rw [← Category.assoc]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion (π ≫ U.ι) O hO
  let D : DivisorOver k s := ⟨blowUp I, π ≫ U.ι, hnv, hbir, Eex⟩
  -- the generic point of `F` lies over `x`
  obtain ⟨-, F', hF'id, -, hFimg⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal (U.ι ≫ s) I hsb
      hirr hc1
  have hsuppF : Eex.support = ((exceptionalIdeal I).support : Set (blowUp I)) := rfl
  have hsuppF' : F'.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by
    simp only [AlgebraicGeometry.PrimeDivisor.support, hF'id]
  have hgenπ : IsGenericPoint (π Eex.genericPoint) (I.support : Set U) := by
    change closure {π _} = _
    rw [← Set.image_singleton, π.isClosedMap.closure_image_eq_of_continuous π.continuous,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF, ← hsuppF', hFimg]
  have hgenI : IsGenericPoint hirr.genericPoint (I.support : Set U) :=
    hirr.isGenericPoint_genericPoint_closure.trans I.support.isClosed.closure_eq
  have hπη : π Eex.genericPoint = hirr.genericPoint := hgenπ.eq hgenI
  have hDf : D.f D.E.genericPoint = x := by
    change U.ι (π Eex.genericPoint) = x
    rw [hπη, hgen]
    rfl
  -- the model is an open of `Bl_V Y`
  obtain ⟨h, hP⟩ := AlgebraicGeometry.exists_isPullback_blowUpToBase_comap U.ι Z
  have hiso : hP.isoPullback.hom ≫ Limits.pullback.snd U.ι (blowUpToBase Z) = h :=
    hP.isoPullback_hom_snd
  have hh : IsOpenImmersion h := by
    rw [← hiso]; infer_instance
  have hrange : ∀ b, blowUpToBase Z b = x → b ∈ Set.range h := by
    intro b hb
    have hb' : b ∈ Set.range (Limits.pullback.snd U.ι (blowUpToBase Z)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      change blowUpToBase Z b ∈ Set.range U.ι
      rw [hb]
      exact ⟨⟨x, hxU⟩, rfl⟩
    obtain ⟨p, rfl⟩ := hb'
    refine ⟨hP.isoPullback.inv p, ?_⟩
    rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd]
  -- `F` is the only prime of the model over `x`
  have huniq : ∀ a : D.Y, D.f a = x → Order.coheight a = 1 → a = D.E.genericPoint := by
    intro a ha ha1
    have hπa : π a = hirr.genericPoint := by
      rw [hgen]
      exact U.ι.isOpenEmbedding.injective ha
    have hmem : a ∈ Eex.support := by
      change a ∈ ((I.comap π).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      change π a ∈ (I.support : Set U)
      rw [hπa]
      exact hgenI.mem
    have hsp : Eex.genericPoint ⤳ a := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    by_contra hne
    have hle : a ≤ Eex.genericPoint := hsp
    have hlt : a < Eex.genericPoint := lt_of_le_not_ge hle fun h' =>
      hne ((show a ⤳ Eex.genericPoint from h').antisymm hsp).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [Eex.coheight_genericPoint] at h2
    change Order.coheight a = 1 at ha1
    rw [ha1] at h2
    exact absurd h2 (by decide)
  refine ⟨D, h, hh, hP.w.symm, hDf, hrange, huniq, ?_⟩
  -- the valuation of `F` is the order function
  intro g hg
  set y := hirr.genericPoint with hy
  have hxy : U.ι y = x := by rw [hgen]; rfl
  subst hxy
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk (U.ι y))
  have : IsIso (U.ι.stalkMap y) := inferInstance
  set e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv with he
  set g' := e g with hg'
  have hg'0 : g' ≠ 0 := fun h0 => hg (e.injective (h0.trans (map_zero e).symm))
  have hmem : ∀ s : ℕ, (s : ℤ) ≤ (blowUp I).ord (functionFieldMap π
      (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint ↔
        g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (U.ι y)) ^ s := fun s =>
    (hordE g' hg'0 s).trans (mem_maximalIdeal_pow_iff_of_ringEquiv e s g)
  have hffm : functionFieldMap (π ≫ U.ι) (algebraMap _ Y.functionField g) =
      functionFieldMap π (algebraMap _ (U : Scheme).functionField g') := by
    rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
    rfl
  obtain ⟨hM1, hM2⟩ := maximalIdealOrder_spec hg
  have hord : (blowUp I).ord (functionFieldMap π
      (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint =
        maximalIdealOrder _ g := by
    have h1 := (hmem _).mpr hM1
    have h2 : ¬ ((maximalIdealOrder _ g + 1 : ℕ) : ℤ) ≤ (blowUp I).ord (functionFieldMap π
        (algebraMap _ (U : Scheme).functionField g')) Eex.genericPoint := fun h =>
      hM2 ((hmem _).mp h)
    push_cast at h2
    omega
  have hne : functionFieldMap (π ≫ U.ι) (algebraMap _ Y.functionField g) ≠ 0 :=
    (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hg))
  change MMP.Mori.PrimeDivisor.divisorialValuation Eex (functionFieldMap (π ≫ U.ι) _) = _
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Eex hne, hffm, hord]

/-- In a Noetherian local ring, `1 ≤ ord φ` exactly when `φ ∈ 𝔪`, for `φ ≠ 0`. -/
private theorem one_le_maximalIdealOrder_iff {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {φ : R} (hφ : φ ≠ 0) :
    1 ≤ maximalIdealOrder R φ ↔ φ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨h1, h2⟩ := maximalIdealOrder_spec hφ
  refine ⟨fun h => by simpa using Ideal.pow_le_pow_right h h1, fun h => ?_⟩
  by_contra h0
  push Not at h0
  rw [Nat.lt_one_iff.mp h0, zero_add, pow_one] at h2
  exact h2 h

/-- On a nonzero element of `𝒪_{X,η_W}` the order valuation is the order function. -/
private theorem blowupDivisor_algebraMap {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (hX : IsNormalVariety k sX)
    {W : IrreducibleCloseds X} (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (f : X.functionFieldˣ) (φ : X.presheaf.stalk W.isIrreducible.genericPoint) (hφ : φ ≠ 0)
    (hf : (f : X.functionField) = algebraMap _ _ φ) :
    blowupDivisor W f = maximalIdealOrder _ φ := by
  have h := (isBlowupDivisor_blowupDivisor (sX := sX) hX hW hreg).2.2.2 f φ 1 hφ one_ne_zero
    (by rw [map_one, mul_one, hf])
  have h1 : maximalIdealOrder _ (1 : X.presheaf.stalk W.isIrreducible.genericPoint) = 0 :=
    Nat.lt_one_iff.mp <| not_le.mp fun h0 => IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
      ((one_le_maximalIdealOrder_iff one_ne_zero).mp h0)
  rw [h, h1, Nat.cast_zero, sub_zero]

/-- The centre clause follows from the valuation formula. -/
private theorem centre_of_valuation_eq {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (hX : IsNormalVariety k sX)
    {W : IrreducibleCloseds X} (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (v : Valuation X.functionField ℤᵐ⁰)
    (hv : ∀ f : X.functionFieldˣ, v (f : X.functionField) = WithZero.exp (-blowupDivisor W f))
    (φ : X.presheaf.stalk W.isIrreducible.genericPoint) :
    v (algebraMap _ X.functionField φ) ≤ 1 ∧
      (v (algebraMap _ X.functionField φ) < 1 ↔
        φ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)) := by
  by_cases hφ : φ = 0
  · subst hφ
    simp
  have hne : algebraMap _ X.functionField φ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (X.presheaf.stalk W.isIrreducible.genericPoint)
      X.functionField), (IsFractionRing.injective _ X.functionField).eq_iff]
    exact hφ
  have hval := hv (Units.mk0 _ hne)
  rw [blowupDivisor_algebraMap hX hW hreg _ φ hφ rfl, Units.val_mk0] at hval
  rw [hval, ← one_le_maximalIdealOrder_iff hφ]
  refine ⟨?_, ?_⟩
  · rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

/-- The exceptional prime of `Bl_W X` over `η_W`, as a divisor over `X` on an open normal
subscheme of the blow-up. -/
private theorem exists_divisorOver_blowUp {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CharZero k] (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    ∃ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
          D.f D.E.genericPoint = W.isIrreducible.genericPoint := by
  obtain ⟨D, h, hh, hhf, hDf, -, -, -⟩ := exists_divisorOver_smoothBlowup hX W hW _ rfl hreg
  have hinv : (Stacks.Blowup.blowUpIso _).inv ≫ Stacks.Blowup.blowUpToBase _ =
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)) := by
    rw [Iso.inv_comp_eq, Stacks.Blowup.blowUpIso_hom_comp]
  have := hh
  refine ⟨D, h ≫ (Stacks.Blowup.blowUpIso _).inv, inferInstance, ?_, hDf⟩
  rw [Category.assoc, hinv, hhf]

/-- The valuation of an exceptional prime over `η_W` of `Bl_{W ∩ U} U` is the order valuation. -/
private theorem valuation_eq_exp_neg_blowupDivisor {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CharZero k] (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint))
    (U : X.Opens) (hU : W.isIrreducible.genericPoint ∈ U) (D : DivisorOver k sX)
    (j : D.Y ⟶ Stacks.Blowup.blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨U.ι ⁻¹' (W : Set X), W.isClosed.preimage U.ι.continuous⟩ : Closeds U)))
    (hj : IsOpenImmersion j) (hf : j ≫ Stacks.Blowup.blowUpToBase _ ≫ U.ι = D.f)
    (hE : D.f D.E.genericPoint = W.isIrreducible.genericPoint) (f : X.functionFieldˣ) :
    D.valuation (f : X.functionField) = WithZero.exp (-blowupDivisor W f) := by
  have : IsOpenImmersion j := hj
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set x := W.isIrreducible.genericPoint with hxdef
  have hxgen : IsGenericPoint x (W : Set X) := isGenericPoint_genericPoint W
  let xU : U.toScheme := ⟨x, hU⟩
  have : Nonempty U := ⟨xU⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hU⟩)
  have hUnv := isNormalVariety_ι hX U
  have : IsLocallyNoetherian U.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sX)
  -- `W ∩ U`, with generic point `x` and the codimension of `W`
  have hWirr : IsIrreducible (U.ι ⁻¹' (W : Set X)) :=
    W.isIrreducible.preimage U.ι.isOpenEmbedding ⟨x, hxgen.mem, xU, rfl⟩
  set WU : IrreducibleCloseds U := ⟨U.ι ⁻¹' (W : Set X), hWirr,
    W.isClosed.preimage U.ι.continuous⟩ with hWU
  have hpre : IsGenericPoint xU (WU : Set U) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff]
    exact hxgen.specializes_iff_mem
  have hxU : xU = WU.isIrreducible.genericPoint := hpre.eq (isGenericPoint_genericPoint WU)
  have hcodU : codimension WU = codimension W := by
    rw [codimension_eq_coheight_genericPoint, codimension_eq_coheight_genericPoint, ← hxU,
      ← hxdef]
    exact (coheight_eq_of_isOpenImmersion U.ι (x := xU)).symm
  have hregU : IsRegularLocalRing (U.toScheme.presheaf.stalk xU) :=
    isRegularLocalRing_of_isOpenImmersion U.ι xU hreg
  obtain ⟨D₀, h, hh, hhf, hD₀E, hrange, huniq, hval₀⟩ :=
    exists_divisorOver_smoothBlowup hUnv WU (by rwa [hcodU]) xU hxU hregU
  -- the blow-up `Bl_{W ∩ U} U`
  let J : U.toScheme.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (⟨U.ι ⁻¹' (W : Set X), W.isClosed.preimage U.ι.continuous⟩ : Closeds U)
  let h' : D₀.Y ⟶ blowUp J := h
  have : IsOpenImmersion h' := hh
  have hhf' : h' ≫ blowUpToBase J = D₀.f := hhf
  have hrange' : ∀ b, blowUpToBase J b = xU → b ∈ Set.range h' := hrange
  have hJsupp : (J.support : Set U) = WU := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hJirr : IsIrreducible (J.support : Set U) := by rw [hJsupp]; exact WU.isIrreducible
  have hJc : 1 ≤ codimension (⟨J.support, hJirr, J.support.isClosed⟩ : IrreducibleCloseds U) := by
    have : (⟨J.support, hJirr, J.support.isClosed⟩ : IrreducibleCloseds U) = WU := by
      ext1; exact hJsupp
    rw [this, hcodU]
    exact le_trans (by norm_num) hW
  have : IsIntegral (blowUp J) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension J hJirr hJc
  have : IsDominant (blowUpToBase J) := MMP.Threefold.Resolution.isDominant_blowUpToBase J hJirr hJc
  have : IsLocallyNoetherian (blowUp J) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase J)
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D₀.isIntegral
  have := D₀.isNormal
  have := D₀.isLocallyNoetherian
  have := D₀.isDominant
  have : Nonempty D.Y := ⟨D.E.genericPoint⟩
  have : Nonempty D₀.Y := ⟨D₀.E.genericPoint⟩
  -- the model of `D` in the blow-up of `AlgebraicGeometry`
  set ψ : D.Y ⟶ blowUp J := j ≫ (Stacks.Blowup.blowUpIso J).hom with hψdef
  have hψ : ψ ≫ blowUpToBase J ≫ U.ι = D.f := by
    rw [← hf, hψdef, Category.assoc, ← Category.assoc (Stacks.Blowup.blowUpIso J).hom,
      Stacks.Blowup.blowUpIso_hom_comp]
  have : IsOpenImmersion ψ := by rw [hψdef]; infer_instance
  have : IsDominant ψ := ⟨(ψ.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩
  have : IsDominant h' := ⟨(h'.isOpenEmbedding.isOpen_range).dense (Set.range_nonempty _)⟩
  -- `ψ(η_E)` is the generic point of the exceptional prime of `D₀`
  have hy : blowUpToBase J (ψ D.E.genericPoint) = xU := by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ, hE]
    rfl
  obtain ⟨b, hb⟩ := hrange' _ hy
  have hb1 : Order.coheight b = 1 := by
    rw [← coheight_eq_of_isOpenImmersion h', hb, coheight_eq_of_isOpenImmersion ψ]
    exact D.E.coheight_genericPoint
  have hbf : D₀.f b = xU := by rw [← hhf', Scheme.Hom.comp_apply, hb, hy]
  have hbξ : b = D₀.E.genericPoint := huniq b hbf hb1
  -- the two spellings of the function field map, and its functoriality
  have hffd : ∀ {P Q : Scheme.{u}} [IsIntegral P] [IsIntegral Q] (i : P ⟶ Q) [IsDominant i],
      functionFieldMap i = dominantFunctionFieldMap i := by
    intro P Q _ _ i _
    exact (congrArg CommRingCat.Hom.hom (stalkMap_cast_target i (genericPoint _)
      (((tfae_isDominant_of_isIntegral i).out 1 2).mp (inferInstance : IsDominant i)))).symm
  have hcongr : ∀ {P Q : Scheme.{u}} [IsIntegral P] [IsIntegral Q] {f₁ f₂ : P ⟶ Q},
      f₁ = f₂ → ∀ [IsDominant f₁] [IsDominant f₂] (t : Q.functionField),
        functionFieldMap f₁ t = functionFieldMap f₂ t := by
    intro P Q _ _ f₁ f₂ hf₁₂ _ _ t
    subst hf₁₂
    rfl
  -- the order of a function of `𝒪_{X,x}` along `E`
  have key : ∀ φ : X.presheaf.stalk x, φ ≠ 0 →
      D.valuation (algebraMap _ X.functionField φ) =
        WithZero.exp (-(maximalIdealOrder _ φ : ℤ)) := by
    intro φ hφ
    have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    have := IsRegularLocalRing.isDomain (U.toScheme.presheaf.stalk xU)
    have : IsIso (U.ι.stalkMap xU) := inferInstance
    set e := (asIso (U.ι.stalkMap xU)).commRingCatIsoToRingEquiv with he
    have hφ' : e φ ≠ 0 := fun h0 => hφ (e.injective (h0.trans (map_zero e).symm))
    have hv₀ := hval₀ (e φ) hφ'
    rw [maximalIdealOrder_ringEquiv e hφ] at hv₀
    set a := algebraMap _ X.functionField φ with ha
    have ha0 : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hφ)
    set a₀ := algebraMap _ U.toScheme.functionField (e φ) with ha₀
    have ha₀0 : a₀ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hφ')
    have hfa : functionFieldMap D.f a ≠ 0 := (map_ne_zero _).mpr ha0
    have hfa₀ : functionFieldMap D₀.f a₀ ≠ 0 := (map_ne_zero _).mpr ha₀0
    have h1 : D.valuation a =
        WithZero.exp (-D.Y.ord (functionFieldMap D.f a) D.E.genericPoint) :=
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord D.E hfa
    have h2 : D₀.valuation a₀ =
        WithZero.exp (-D₀.Y.ord (functionFieldMap D₀.f a₀) D₀.E.genericPoint) :=
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord D₀.E hfa₀
    set c := functionFieldMap (blowUpToBase J ≫ U.ι) a with hc
    have e1 : functionFieldMap D.f a = functionFieldMap ψ c := by
      rw [hc, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      exact hcongr hψ.symm a
    have e2 : functionFieldMap D₀.f a₀ = functionFieldMap h' c := by
      have : a₀ = functionFieldMap U.ι a :=
        (MMP.Mori.functionFieldMap_algebraMap_stalk U.ι xU φ).symm
      rw [this, hc, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      refine hcongr ?_ a
      rw [← hhf', Category.assoc]
    have hord : D.Y.ord (functionFieldMap D.f a) D.E.genericPoint =
        D₀.Y.ord (functionFieldMap D₀.f a₀) D₀.E.genericPoint := by
      rw [e1, e2, hffd ψ, hffd h', Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion ψ,
        Stacks.Chow.ord_dominantFunctionFieldMap_of_isOpenImmersion h', ← hbξ, hb]
    rwa [h1, hord, ← h2]
  -- `f = φ/ψ` with `φ, ψ ∈ 𝒪_{X,x}`
  obtain ⟨⟨a, s⟩, hs⟩ :=
    IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk x)) (f : X.functionField)
  have hs0 : (s : X.presheaf.stalk x) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hs
    rcases hs with h0 | h0
    · exact f.ne_zero h0
    · exact hs0 (hinj.eq_iff.mp (h0.trans (map_zero _).symm))
  have hbd := (isBlowupDivisor_blowupDivisor (sX := sX) hX hW hreg).2.2.2 f a s ha0 hs0 hs
  have hv := congrArg D.valuation hs
  rw [map_mul, key a ha0, key s hs0] at hv
  rw [hbd, show -((maximalIdealOrder _ a : ℤ) - maximalIdealOrder _ (s : X.presheaf.stalk x)) =
      -(maximalIdealOrder _ a : ℤ) + maximalIdealOrder _ (s : X.presheaf.stalk x) by ring,
    WithZero.exp_add, ← hv, mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero,
    mul_one]

/-- The characteristic-zero version of the regular-centre order valuation;
`valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp` specializes it. -/
theorem valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp_of_charZero {k : Type u}
    [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    (∃ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
          D.f D.E.genericPoint = W.isIrreducible.genericPoint) ∧
    ∀ (U : X.Opens), W.isIrreducible.genericPoint ∈ U →
      ∀ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨U.ι ⁻¹' (W : Set X), W.isClosed.preimage U.ι.continuous⟩ : Closeds U))),
        IsOpenImmersion j → j ≫ Stacks.Blowup.blowUpToBase _ ≫ U.ι = D.f →
        D.f D.E.genericPoint = W.isIrreducible.genericPoint →
        (∀ f : X.functionFieldˣ,
          D.valuation (f : X.functionField) = WithZero.exp (-blowupDivisor W f)) ∧
        ∀ φ : X.presheaf.stalk W.isIrreducible.genericPoint,
          D.valuation (algebraMap _ X.functionField φ) ≤ 1 ∧
            (D.valuation (algebraMap _ X.functionField φ) < 1 ↔
              φ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)) := by
  refine ⟨exists_divisorOver_blowUp hX W hW hreg, fun U hU D j hj hf hE => ?_⟩
  have hv := valuation_eq_exp_neg_blowupDivisor hX W hW hreg U hU D j hj hf hE
  exact ⟨hv, centre_of_valuation_eq hX hW hreg D.valuation hv⟩

/-- **The order valuation along a regular centre is the valuation of the exceptional divisor of
its blow-up.** Let `X` be a normal variety over an algebraically closed field `k` of
characteristic zero and `W ⊆ X` an irreducible closed subset of
codimension `≥ 2` with `𝒪_{X,η_W}` regular, and let `E_W = MMP.Flips.blowupDivisor W` be the
order valuation of `𝒪_{X,η_W}` on `k(X)`. Then:
* there is a divisor `D = (Y, f, E)` over `X` whose model `Y` is an open subscheme of the blow-up
  `Bl_W X` of the vanishing ideal of `W` and with `f(η_E) = η_W`;
* for every open `U ∋ η_W` and every divisor `D = (Y, f, E)` over `X` whose model is an open
  subscheme of `Bl_{W ∩ U} U` (through `j`, with `f = j ≫ π ≫ ι_U`) and with `f(η_E) = η_W`,
  `ord_E(f) = exp (-E_W(f))` for all `f ∈ k(X)ˣ`, and the centre of `ord_E` on `X` is `W`:
  `ord_E ≤ 1` on `𝒪_{X,η_W}`, with `ord_E(φ) < 1` exactly for `φ ∈ 𝔪_{η_W}`. -/
@[mmp "lem_mmp_regular_centre_order_divisorial"]
theorem valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    (∃ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
          D.f D.E.genericPoint = W.isIrreducible.genericPoint) ∧
    ∀ (U : X.Opens), W.isIrreducible.genericPoint ∈ U →
      ∀ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨U.ι ⁻¹' (W : Set X), W.isClosed.preimage U.ι.continuous⟩ : Closeds U))),
        IsOpenImmersion j → j ≫ Stacks.Blowup.blowUpToBase _ ≫ U.ι = D.f →
        D.f D.E.genericPoint = W.isIrreducible.genericPoint →
        (∀ f : X.functionFieldˣ,
          D.valuation (f : X.functionField) = WithZero.exp (-blowupDivisor W f)) ∧
        ∀ φ : X.presheaf.stalk W.isIrreducible.genericPoint,
          D.valuation (algebraMap _ X.functionField φ) ≤ 1 ∧
            (D.valuation (algebraMap _ X.functionField φ) < 1 ↔
              φ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)) :=
  valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp_of_charZero sX hX W hW hreg

end RegularCentreOrder

end MMP.Flips
