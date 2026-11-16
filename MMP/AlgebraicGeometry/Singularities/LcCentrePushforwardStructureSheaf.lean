module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.LogResolution.FloorIdealVanishing
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Vanishing.SncDirectImageCohomology
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Vanishing.SncTorsionFreeness
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension

/-!
# The direct image of the structure sheaf of the floor over a union of lc centres

Let `(X, B)` be an lc pair with effective `ℚ`-boundary on a normal projective variety over `ℂ`
and let `W ⊆ X` be a union of lc centres of `(X, B)`, with its reduced subscheme structure. There
are a projective log resolution `g : R ⟶ X` from a smooth projective variety and a reduced snc
divisor `T = ∑ T_i` on `R` with `g(T) = W` such that `g_* 𝒪_T = 𝒪_W`: the morphism
`T ⟶ X` factors through `W`, and its comorphism `𝒪_W ⟶ (T ⟶ W)_* 𝒪_T` is an isomorphism.

## Main results

* `MMP.Mori.exists_isIso_app_comp_subschemeι_vanishingIdeal_of_isLcPair`: the statement.
* `MMP.Mori.exists_isIso_app_comp_subschemeι_vanishingIdeal_and_isCrepantBoundary_of_coeff_le_one`:
  for boundaries with coefficients `≤ 1`, the same on a crepant model with snc boundary.

## Implementation notes

Write `D = K_X + B`, let `K_V + B_V = g^* D` be the crepant boundary on a log resolution
`g : V ⟶ X` on which every lc centre in `W` is dominated by a divisor of coefficient one and on
which `g⁻¹(W)` is a divisor, snc together with `Supp B_V` and `Ex(g)`. Let `T` be the sum of the
coefficient-one components of `B_V` mapping into `W`, `A = ⌈-(B_V^{<1})⌉` and
`C = A - T + B_V`. Then `A - T - (K_V + C) = -g^* D` is `g`-semiample, and no snc stratum of
`⌊C⌋` maps into `W`, so the torsion-freeness theorem shows that `R¹g_* 𝒪_V(A - T)` has no
associated point in `W`. Since `g_* 𝒪_T(A)` is killed by the ideal of `W`, the connecting map
of `0 ⟶ 𝒪_V(A - T) ⟶ 𝒪_V(A) ⟶ 𝒪_T(A) ⟶ 0` vanishes, so `𝒪_X = g_* 𝒪_V(A) ⟶ g_* 𝒪_T(A)` is
onto. As `𝒪_T ⟶ 𝒪_T(A)` is injective, `𝒪_X ⟶ g_* 𝒪_T` is onto, and `g_* 𝒪_T` is the structure
sheaf of the scheme-theoretic image of `T ⟶ X`, which is `W` with its reduced structure.

Here `𝒪_T(A)` is `ι_* ι^* 𝒪_V(A)` for the closed immersion `ι : T ⟶ V` of the reduced support,
and the injectivity of `𝒪_T ⟶ 𝒪_T(A)` is the equality of kernels of `𝒪_V ⟶ ι_* 𝒪_T` and
`𝒪_V ⟶ 𝒪_V(A) ⟶ ι_* ι^* 𝒪_V(A)`, a statement about orders along the components of `T`.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino11]
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite MMP.Mori

namespace MMP.Mori.LcCentrePushforward

attribute [local instance] HasDerivedCategory.standard

section Image

variable {S X R : Scheme.{0}}

/-- The comorphism `𝒪_X ⟶ ι_* 𝒪_S` of a morphism `ι : S ⟶ X`, as a morphism of
`𝒪_X`-modules. -/
private noncomputable def unitHom (ι : S ⟶ X) :
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pushforward ι).obj (SheafOfModules.unit S.ringCatSheaf)) :=
  SheafOfModules.unitToPushforwardObjUnit ι.toRingCatSheafHom

/-- The unit `𝒪_Y ⟶ g_* 𝒪_X` of a composite factors through the units of the factors. -/
private theorem unitHom_comp (ι : S ⟶ X) (f : X ⟶ R) :
    unitHom (ι ≫ f) = unitHom f ≫ (Scheme.Modules.pushforward f).map (unitHom ι) ≫
      ((Scheme.Modules.pushforwardComp ι f).app _).inv := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  rfl

/-- On sections over `U`, `unitHom q` is an isomorphism exactly when the comorphism of `q` is:
both are the same map, bijective in either category. -/
private theorem isIso_app_unitHom_iff (q : S ⟶ X) (U : X.Opens) :
    IsIso ((unitHom q).app U) ↔ IsIso (q.app U) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  rfl

/-- `unitHom q` is a monomorphism when the comorphism of `q` is injective on every open. -/
private theorem mono_unitHom_of_injective (q : S ⟶ X)
    (hinj : ∀ U : X.Opens, Function.Injective (q.app U)) : Mono (unitHom q) := by
  apply (Scheme.Modules.toPresheaf _).mono_of_mono_map
  have : ∀ U, Mono (((Scheme.Modules.toPresheaf _).map (unitHom q)).app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).2 (hinj U.unop)
  exact NatTrans.mono_of_mono_app _

/-- If `𝒪_R ⟶ g_* 𝒪_S` is an epimorphism of `𝒪_R`-modules, for `g` quasi-compact, then the
comorphism of `g.toImage` is an isomorphism on every open of the scheme-theoretic image. -/
private theorem isIso_toImage_app_of_epi (g : S ⟶ R) [QuasiCompact g] (h : Epi (unitHom g)) :
    ∀ U : g.image.Opens, IsIso (g.toImage.app U) := by
  set j := g.imageι
  set q := g.toImage
  have hqj : q ≫ j = g := g.toImage_imageι
  have hinj : ∀ U : g.image.Opens, Function.Injective (q.app U) := fun U =>
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective (F := g.image.sheaf) q.c
      U fun x _ => g.stalkFunctor_toImage_injective x
  let ρ : (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit S.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward g).obj (SheafOfModules.unit S.ringCatSheaf) :=
    (Scheme.Modules.pushforwardComp q j).symm.app _ ≪≫
      (Scheme.Modules.pushforwardCongr hqj).app _
  have hfac : unitHom g = unitHom j ≫ (Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext x
    have h1 := Scheme.Hom.congr_app hqj.symm U
    rw [Scheme.Hom.comp_app] at h1
    exact ConcreteCategory.congr_hom h1 x
  haveI : Mono (unitHom q) := mono_unitHom_of_injective q hinj
  have hpq : IsIso ((Scheme.Modules.pushforward j).map (unitHom q)) := by
    haveI := (Scheme.Modules.pullbackPushforwardAdjunction j).rightAdjoint_preservesLimits
    haveI : Mono ((Scheme.Modules.pushforward j).map (unitHom q)) :=
      (Scheme.Modules.pushforward j).map_mono _
    haveI : Epi ((Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom) := by
      rw [hfac] at h
      exact epi_of_epi (unitHom j) _
    haveI : Epi ((Scheme.Modules.pushforward j).map (unitHom q)) := by
      have he : (Scheme.Modules.pushforward j).map (unitHom q) =
          ((Scheme.Modules.pushforward j).map (unitHom q) ≫ ρ.hom) ≫ ρ.inv := by
        simp
      rw [he]
      exact epi_comp _ _
    exact isIso_of_mono_of_epi _
  intro U
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : R.Opens, j ⁻¹ᵁ U₀ = U := by
    obtain ⟨V, hV, hVU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
    exact ⟨⟨V, hV⟩, TopologicalSpace.Opens.ext hVU⟩
  subst hU₀
  exact (isIso_app_unitHom_iff q _).1
    ((Scheme.Modules.Hom.isIso_iff_isIso_app (φ := (Scheme.Modules.pushforward j).map
      (unitHom q))).mp hpq U₀)

end Image

section Homological

universe u v

/-- In the long exact sequence of a left exact functor, `T X₂ ⟶ T X₃` is an epimorphism as soon
as every morphism `R⁰T X₃ ⟶ R¹T X₁` vanishes, since the connecting morphism is one of them. -/
private theorem epi_map_g_of_forall_eq_zero {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] (T : C ⥤ D) [T.Additive]
    [PreservesFiniteLimits T] {S : ShortComplex C} (hS : S.ShortExact)
    (h : ∀ φ : (T.rightDerived 0).obj S.X₃ ⟶ (T.rightDerived 1).obj S.X₁, φ = 0) :
    Epi (T.map S.g) := by
  letI := HasDerivedCategory.standard C
  letI := HasDerivedCategory.standard D
  let Δ := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives T
  have hex := Δ.exact_δ₁ hS 0
  have hδ : Δ.δ hS 0 = 0 := h _
  have h0 : Epi ((T.rightDerived 0).map S.g) := hex.epi_f hδ
  have heq : T.map S.g = T.rightDerivedZeroIsoSelf.inv.app _ ≫ (T.rightDerived 0).map S.g ≫
      T.rightDerivedZeroIsoSelf.hom.app _ := by
    rw [T.rightDerivedZeroIsoSelf.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [heq]
  infer_instance

end Homological

section Orders

/-- A regular function on an affine open `U` lies in the ideal of the reduced closed subscheme
`W` exactly when it vanishes at every point of `W ∩ U`. -/
private theorem mem_vanishingIdeal_ideal_iff {X : Scheme.{0}} (W : Closeds X) (U : X.affineOpens)
    (a : Γ(X, U)) :
    a ∈ (Scheme.IdealSheafData.vanishingIdeal W).ideal U ↔
      ∀ x ∈ (W : Set X), x ∈ (U : X.Opens) → x ∉ X.basicOpen a := by
  have hmem : ∀ p, U.2.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := fun p => by
    change p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen a ↔ _
    rw [U.2.fromSpec_preimage_basicOpen]
    rfl
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h x hxW hxU hxa
    obtain ⟨p, rfl⟩ : x ∈ Set.range U.2.fromSpec := by rwa [U.2.range_fromSpec]
    exact (hmem p).1 hxa (h p hxW)
  · intro h p hp
    by_contra hpa
    have hU : U.2.fromSpec p ∈ (U : X.Opens) := by
      have := Set.mem_range_self (f := U.2.fromSpec) p
      rwa [U.2.range_fromSpec] at this
    exact h _ hp hU ((hmem p).2 hpa)

/-- An element of the maximal ideal of the discrete valuation ring `𝒪_{X,E}` vanishes to order at
least one along `E`. -/
private theorem ordGE_one_toComponent_of_mem_maximalIdeal {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (E : MMP.Mori.PrimeDivisor X) {a : E.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal E.localRing) : E.OrdGE 1 (E.toComponent.hom a) := by
  by_cases h0 : a = 0
  · left; rw [h0, map_zero]
  right
  let := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  have := E.isDiscreteValuationRing_localRing
  change WithZero.exp 1 ≤ Ring.ordFrac E.localRing (IsLocalization.algEquiv
    (nonZeroDivisors E.localRing) _ (FractionRing E.localRing) (algebraMap E.localRing _ a))
  rw [AlgEquiv.commutes]
  set v := Ring.ordFrac E.localRing (algebraMap E.localRing (FractionRing E.localRing) a)
  have h1 : 1 ≤ v := Ring.ordFrac_ge_one_of_ne_zero h0
  have h2 : v ≠ 1 := fun h =>
    (IsLocalRing.mem_maximalIdeal _).mp ha
      (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.2 h)
  have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h1)
  rw [← WithZero.exp_log hv0] at h1 h2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [← WithZero.exp_zero, Ne, WithZero.exp_inj] at h2
  rw [WithZero.exp_le_exp]
  omega

/-- The germ of a regular function along a prime divisor, read in the function field of its
component, is the image of its germ in the local ring of the divisor. -/
private theorem germ_component_eq_toComponent {V : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U')) (hP : P.genericPoint ∈ U')
    (hc : componentGenericPoint V P.component ∈ U') :
    V.presheaf.germ U' _ hc b = P.toComponent.hom (V.presheaf.germ U' _ hP b) :=
  (TopCat.Presheaf.germ_stalkSpecializes_apply V.presheaf hP _ b).symm

/-- A regular function vanishing at the generic point of a prime divisor `P` vanishes to order at
least one along `P`. -/
private theorem ordGE_one_germ_of_notMem_basicOpen {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U'))
    (hP : P.genericPoint ∈ U') (hb : P.genericPoint ∉ V.basicOpen b)
    (hc : componentGenericPoint V P.component ∈ U') :
    P.OrdGE 1 (V.presheaf.germ U' _ hc b) := by
  rw [germ_component_eq_toComponent P b hP hc]
  refine ordGE_one_toComponent_of_mem_maximalIdeal P ?_
  rw [IsLocalRing.mem_maximalIdeal]
  exact fun hu => hb ((Scheme.mem_basicOpen V b _ hP).2 hu)

/-- A regular function has nonnegative order along every prime divisor. -/
private theorem ordGE_zero_germ {V : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U')) (hP : P.genericPoint ∈ U')
    (hc : componentGenericPoint V P.component ∈ U') :
    P.OrdGE 0 (V.presheaf.germ U' _ hc b) := by
  rw [germ_component_eq_toComponent P b hP hc]
  by_cases h0 : V.presheaf.germ U' _ hP b = 0
  · left
    rw [h0, map_zero]
  · right
    rw [WithZero.exp_zero]
    exact P.one_le_valuation_toComponent h0

/-- A regular function invertible at the generic point of a prime divisor has order zero along
it. -/
private theorem valuation_germ_of_mem_basicOpen {V : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] (P : MMP.Mori.PrimeDivisor V) {U' : V.Opens} (b : Γ(V, U'))
    (hP : P.genericPoint ∈ U') (hb : P.genericPoint ∈ V.basicOpen b)
    (hc : componentGenericPoint V P.component ∈ U') :
    P.valuation (V.presheaf.germ U' _ hc b) = 1 := by
  rw [germ_component_eq_toComponent P b hP hc]
  exact P.valuation_toComponent_of_isUnit ((Scheme.mem_basicOpen V b _ hP).1 hb)

/-- The coefficients of the reduced divisor `∑_{P ∈ T} P`. -/
private theorem sum_single_one_apply {V : Scheme.{0}} [DecidableEq (MMP.Mori.PrimeDivisor V)]
    (T : Finset (MMP.Mori.PrimeDivisor V))
    (P : MMP.Mori.PrimeDivisor V) :
    (∑ Q ∈ T, Finsupp.single Q (1 : ℤ)) P = if P ∈ T then 1 else 0 := by
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

end Orders

section SES

variable {S X W : Scheme.{0}}

/-- A regular function restricts to zero on the reduced support of a divisor exactly when it
vanishes at the generic points of its prime divisors. -/
private theorem app_subschemeι_eq_zero_iff (T : Divisor X) [IsReduced T.suppIdeal.subscheme]
    (U : X.Opens) (r : Γ(X, U)) :
    T.suppIdeal.subschemeι.app U r = 0 ↔ ∀ Q : MMP.Mori.PrimeDivisor X, T.coeff Q ≠ 0 →
      Q.genericPoint ∈ U → Q.genericPoint ∉ X.basicOpen r := by
  have hrange : Set.range T.suppIdeal.subschemeι = (T.supp : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal]
  constructor
  · intro h0 Q hQ _ hb
    have hQs : Q.genericPoint ∈ (T.supp : Set X) :=
      DivisorWithCoeffs.support_subset_supp hQ (MMP.Flips.primeDivisor_genericPoint_mem_support Q)
    rw [← hrange] at hQs
    obtain ⟨y, hy⟩ := hQs
    have : y ∈ T.suppIdeal.subschemeι ⁻¹ᵁ X.basicOpen r := by
      change T.suppIdeal.subschemeι y ∈ X.basicOpen r
      rwa [hy]
    rwa [Scheme.Hom.preimage_basicOpen, h0, Scheme.basicOpen_zero] at this
  · intro h
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.Hom.preimage_basicOpen]
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    have hyb : T.suppIdeal.subschemeι y ∈ X.basicOpen r := hy
    have hyT : T.suppIdeal.subschemeι y ∈ (T.supp : Set X) := hrange ▸ ⟨y, rfl⟩
    obtain ⟨Q, hQ, hyQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyT
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyQ
    have hsp : Q.genericPoint ⤳ T.suppIdeal.subschemeι y := specializes_iff_mem_closure.mpr hyQ
    exact h Q hQ ((hsp.mem_open (X.basicOpen r).isOpen hyb) |> X.basicOpen_le r)
      (hsp.mem_open (X.basicOpen r).isOpen hyb)

end SES

private theorem fieldMap_eq_of_stalkSpecializes {X V : Scheme.{0}} [IsIntegral X] [IsIntegral V]
    (g : V ⟶ X) [IsDominant g] (ZX : irreducibleComponents X) (ZY : irreducibleComponents V)
    (x : X.presheaf.stalk (componentGenericPoint X ZX))
    (y : V.presheaf.stalk (componentGenericPoint V ZY))
    (h : (V.presheaf.stalkSpecializes (genericPoint_specializes _)).hom y =
      functionFieldMap g ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom x)) :
    MMP.Fourfold.fieldMap g ZX ZY x = y := by
  rw [MMP.Fourfold.fieldMap_eq, RingHom.comp_apply, RingHom.comp_apply]
  change (V.presheaf.stalkSpecializes
      (specializes_of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint ZY))).hom
    (functionFieldMap g ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom x)) = y
  rw [← h, ← ConcreteCategory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

section Kernel

variable {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]

/-- The reduced divisor `∑_{P ∈ T} P` is effective. -/
private theorem sum_single_one_nonneg (T : Finset (MMP.Mori.PrimeDivisor V)) :
    (0 : Divisor V) ≤ ∑ P ∈ T, Finsupp.single P (1 : ℤ) :=
  Finset.sum_nonneg fun _ _ => Finsupp.single_nonneg.2 zero_le_one

/-- A regular function vanishes to order at least one along a prime divisor through its open
exactly when it vanishes at the generic point of the divisor. -/
private theorem ordGE_one_germ_iff (P : MMP.Mori.PrimeDivisor V) {U : V.Opens} (r : Γ(V, U))
    (hP : P.genericPoint ∈ U) (hc : componentGenericPoint V P.component ∈ U) :
    P.OrdGE 1 (V.presheaf.germ U _ hc r) ↔ P.genericPoint ∉ V.basicOpen r := by
  refine ⟨fun h hb => ?_, fun hb => ordGE_one_germ_of_notMem_basicOpen P r hP hb hc⟩
  have hv := valuation_germ_of_mem_basicOpen P r hP hb hc
  rcases h with h0 | h1
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega

/-- The vanishing of a regular function on the reduced divisor `T`. -/
private theorem app_subschemeι_eq_zero_iff_of_finset (T : Finset (MMP.Mori.PrimeDivisor V))
    [IsReduced (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subscheme]
    (U : V.Opens) (r : Γ(V, U)) :
    (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι.app U r = 0 ↔
      ∀ Q ∈ T, Q.genericPoint ∈ U → Q.genericPoint ∉ V.basicOpen r := by
  classical
  rw [app_subschemeι_eq_zero_iff]
  have hco : ∀ Q, (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).coeff Q ≠ 0 ↔ Q ∈ T := by
    intro Q
    rw [DivisorWithCoeffs.coeff_apply, sum_single_one_apply]
    split_ifs with h <;> simp [h]
  exact forall_congr' fun Q => by rw [hco]

variable [CompactSpace V]

/-- **The kernel of `𝒪_V(A) ⟶ 𝒪_T(A)`.** For a Cartier divisor `A` on `V` with no component in
the reduced divisor `T = ∑ T_i`, the kernel of the unit `𝒪_V(A) ⟶ ι_* ι^* 𝒪_V(A)` of the
reduced closed immersion `ι : T ⟶ V` is the subsheaf `𝒪_V(A - T)`. -/
private theorem imageSubmodule_eq_kernelSubmodule_unit (A : Divisor V) (hAc : A.IsCartier)
    (T : Finset (MMP.Mori.PrimeDivisor V)) (hAT : ∀ P ∈ T, A P = 0) :
    imageSubmodule (Divisor.divisorialSheafInclusion (sub_le_self A (sum_single_one_nonneg T))) =
      Stacks.Algebraization.kernelSubmodule
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι).unit.app
            A.divisorialSheaf) := by
  classical
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P (1 : ℤ)
  set ι := TD.suppIdeal.subschemeι
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app A.divisorialSheaf with hη
  set φ := Divisor.divisorialSheafInclusion (sub_le_self A (sum_single_one_nonneg T))
  haveI : IsReduced TD.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hTco : ∀ P, TD P = if P ∈ T then 1 else 0 := sum_single_one_apply T
  have hKη : Stacks.Algebraization.kernelSubmodule η =
      Stacks.Algebraization.idealPowerMultiple TD.suppIdeal 1 A.divisorialSheaf := by
    rw [hη, Stacks.Algebraization.kernelSubmodule_unit_app_eq_idealMultiple,
      Scheme.IdealSheafData.ker_subschemeι]
  have hKaff := (Stacks.Algebraization.idealPowerMultiple_le_iff TD.suppIdeal 1
    A.divisorialSheaf _).1 le_rfl
  -- membership in the ideal of `T` over an affine open
  have hmemI : ∀ (U : V.affineOpens) (a : Γ(V, U)), a ∈ TD.suppIdeal.ideal U ↔
      ∀ Q ∈ T, Q.genericPoint ∈ (U : V.Opens) → Q.genericPoint ∉ V.basicOpen a := by
    intro U a
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
    exact app_subschemeι_eq_zero_iff_of_finset T U a
  -- the sections of `𝒪_V(A - T)` land in `ℐ_T · 𝒪_V(A)` over small affine opens
  have key : ∀ (V' : V.affineOpens) (V₀ : V.Opens) (_ : (V'.1 : V.Opens) ≤ V₀)
      (ψ : (RationalFunctions V)ˣ) (_ : A.IsLocalEquation V₀ ψ)
      (t : Γ((A - TD).divisorialSheaf, V'.1)),
      (φ.app V'.1).hom t ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op V'.1) := by
    intro V' V₀ hV'₀ ψ hψ t
    rw [hKη]
    refine hKaff V' ?_
    rw [pow_one]
    set σ := (φ.app V'.1).hom t with hσdef
    -- the local generator `ψ⁻¹` of `𝒪_V(A)` on `V'`
    have hψinv : A.IsDivisorialSection V'.1
        (fun Z => ((ψ⁻¹ : (RationalFunctions V)ˣ) : RationalFunctions V) Z.1) := by
      intro P hP
      right
      rw [P.valuation_component, P.ord_inv,
        ← hψ P (hP.mono (Set.inter_subset_inter_right _ hV'₀))]
    let e' : Γ(A.divisorialSheaf, V'.1) :=
      (⟨_, Divisor.mem_divisorialSubmodule.2 hψinv⟩ : A.divisorialSubmodule V'.1)
    -- `ψ σ` is a regular function `a` on `V'`
    have hsec : (0 : Divisor V).IsDivisorialSection V'.1
        (fun Z => (ψ : RationalFunctions V) Z.1 * σ.1 Z) := by
      intro P hP
      have hPV₀ : (P.support ∩ V₀).Nonempty := hP.mono (Set.inter_subset_inter_right _ hV'₀)
      have h1 : P.OrdGE (A.coeff P) ((ψ : RationalFunctions V) P.component) :=
        Or.inr (le_of_eq (by rw [P.valuation_component, hψ P hPV₀]))
      have h2 := h1.mul (σ.2 P hP)
      rw [add_neg_cancel] at h2
      rw [DivisorWithCoeffs.coeff_zero, neg_zero]
      exact h2
    obtain ⟨a, ha⟩ := hsec.exists_eq
    have hσ : σ = a • e' := by
      refine Subtype.ext (funext fun Z => ?_)
      change σ.1 Z = V.presheaf.germ _ _ Z.2 a *
        ((ψ⁻¹ : (RationalFunctions V)ˣ) : RationalFunctions V) Z.1
      have hZ : V.presheaf.germ _ _ Z.2 a = (ψ : RationalFunctions V) Z.1 * σ.1 Z := congrFun ha Z
      rw [hZ, mul_comm ((ψ : RationalFunctions V) Z.1), mul_assoc, ← Pi.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Pi.one_apply, mul_one]
    rw [hσ]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    -- `a` vanishes along every component of `T`
    rw [hmemI]
    intro Q hQT hQU hQa
    have hQV' : (Q.support ∩ (V'.1 : V.Opens)).Nonempty :=
      ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support Q, hQU⟩
    have hc := Q.componentGenericPoint_mem_of_nonempty hQV'
    have hga : V.presheaf.germ _ _ hc a =
        (ψ : RationalFunctions V) Q.component * σ.1 ⟨Q.component, hc⟩ :=
      congrFun ha ⟨Q.component, hc⟩
    have hQV₀ : (Q.support ∩ V₀).Nonempty := hQV'.mono (Set.inter_subset_inter_right _ hV'₀)
    have h1 : Q.OrdGE (A.coeff Q) ((ψ : RationalFunctions V) Q.component) :=
      Or.inr (le_of_eq (by rw [Q.valuation_component, hψ Q hQV₀]))
    have h2 := h1.mul (t.2 Q hQV')
    have hco : A.coeff Q + -(A - TD).coeff Q = 1 := by
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply, hAT Q hQT, hTco,
        if_pos hQT]
      ring
    rw [hco] at h2
    exact (ordGE_one_germ_iff Q a hQU hc).1 (by rw [hga]; exact h2) hQa
  have hφη : φ ≫ η = 0 := by
    have hK : ∀ (U : V.Opens) (t : Γ((A - TD).divisorialSheaf, U)),
        (φ.app U).hom t ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op U) := by
      intro U t
      apply (Stacks.Algebraization.kernelSubmodule η).isSheaf
      rw [Opens.mem_grothendieckTopology]
      intro x hx
      obtain ⟨V₀, hxV₀, ψ, hψ⟩ := hAc x
      obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'U⟩ :=
        V.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx, hxV₀⟩ : x ∈ U ⊓ V₀) (U ⊓ V₀).2
      refine ⟨V', homOfLE (hV'U.trans inf_le_left), ?_, hxV'⟩
      have h1 := key ⟨V', hV'⟩ V₀ (hV'U.trans inf_le_right) ψ hψ
        ((((A - TD).divisorialSheaf).presheaf.map (homOfLE (hV'U.trans inf_le_left)).op).hom t)
      have h2 := (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality
        (homOfLE (hV'U.trans inf_le_left)).op) t).symm
      have h3 : (A.divisorialSheaf.presheaf.map (homOfLE (hV'U.trans inf_le_left)).op).hom
          ((φ.app U).hom t) = (φ.app V').hom
            ((((A - TD).divisorialSheaf).presheaf.map
              (homOfLE (hV'U.trans inf_le_left)).op).hom t) := h2
      change (A.divisorialSheaf.presheaf.map (homOfLE (hV'U.trans inf_le_left)).op).hom
        ((φ.app U).hom t) ∈ (Stacks.Algebraization.kernelSubmodule η).obj (op V')
      rw [h3]
      exact h1
    ext U t
    have := hK U t
    rwa [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj] at this
  have hle : Stacks.Algebraization.kernelSubmodule η ≤ imageSubmodule φ := by
    rw [hKη, Stacks.Algebraization.idealPowerMultiple_le_iff]
    intro U
    rw [pow_one]
    change _ ≤ (imageSubmodule φ).toSubmodule.obj _
    rw [imageSubmodule_obj φ inferInstance]
    refine Submodule.smul_le.2 fun a ha s _ => ?_
    have hmem : (A - TD).IsDivisorialSection (U : V.Opens) (a • s).1 := by
      intro P hP
      have hc := P.componentGenericPoint_mem_of_nonempty hP
      have hgP : P.genericPoint ∈ (U : V.Opens) := P.genericPoint_mem_of_nonempty hP
      have hval : (a • s).1 ⟨P.component, hc⟩ =
          V.presheaf.germ _ _ hc a * s.1 ⟨P.component, hc⟩ := rfl
      rw [hval]
      have hs := s.2 P hP
      have ha' : P.OrdGE (TD P) (V.presheaf.germ _ _ hc a) := by
        rw [hTco]; split_ifs with hPT
        · exact ordGE_one_germ_of_notMem_basicOpen P _ hgP ((hmemI U a).1 ha P hPT hgP) hc
        · exact ordGE_zero_germ P _ hgP hc
      refine (ha'.mul hs).mono ?_
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply]
      omega
    exact ⟨⟨(a • s).1, hmem⟩, rfl⟩
  exact le_antisymm (imageSubmodule_le_kernelSubmodule φ η hφη) hle

/-- **The kernels of `𝒪_V ⟶ 𝒪_T` and of `𝒪_V ⟶ 𝒪_V(A) ⟶ 𝒪_T(A)` agree**, for an effective
Cartier divisor `A` with no component in the reduced divisor `T`: a regular function vanishes on
`T` exactly when, as a section of `𝒪_V(A)`, it lies in `𝒪_V(A - T)`. -/
private theorem app_unitHom_eq_zero_iff (A : Divisor V) (hAc : A.IsCartier) (hA0 : 0 ≤ A)
    (T : Finset (MMP.Mori.PrimeDivisor V)) (hAT : ∀ P ∈ T, A P = 0) (U : (Opens V)ᵒᵖ)
    (r : Γ(V, U.unop)) :
    ((unitHom (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι).val.app
        U).hom r = 0 ↔
      ((Divisor.structureSheafToDivisorialSheaf hA0 ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι).unit.app
            A.divisorialSheaf).val.app U).hom r = 0 := by
  classical
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P (1 : ℤ)
  set ι := TD.suppIdeal.subschemeι
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app A.divisorialSheaf
  set φ := Divisor.divisorialSheafInclusion (sub_le_self A (sum_single_one_nonneg T))
  set j := Divisor.structureSheafToDivisorialSheaf hA0
  haveI : IsReduced TD.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hTco : ∀ P, TD P = if P ∈ T then 1 else 0 := sum_single_one_apply T
  have heq := imageSubmodule_eq_kernelSubmodule_unit A hAc T hAT
  -- the left side: vanishing on `T`
  have hL : ((unitHom ι).val.app U).hom r = 0 ↔
      ∀ Q ∈ T, Q.genericPoint ∈ U.unop → Q.genericPoint ∉ V.basicOpen r :=
    app_subschemeι_eq_zero_iff_of_finset T U.unop r
  -- the right side: membership in `𝒪_V(A - T)`
  have hjr : ((j.val.app U).hom r).1 = (toRationalFunctionsPresheaf V).app (op U.unop) r :=
    Divisor.coe_structureSheafToDivisorialSheaf_app hA0 U.unop r
  have hR : ((j ≫ η).val.app U).hom r = 0 ↔
      (toRationalFunctionsPresheaf V).app (op U.unop) r ∈
        (A - TD).divisorialSubmodule U.unop := by
    change (η.val.app U).hom ((j.val.app U).hom r) = 0 ↔ _
    rw [← LinearMap.mem_ker, ← Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, ← heq,
      imageSubmodule_obj φ inferInstance, ← hjr]
    constructor
    · rintro ⟨t, ht⟩
      rw [← ht]
      exact t.2
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  rw [hL, hR, Divisor.mem_divisorialSubmodule]
  have hco : ∀ P ∈ T, -(A - TD).coeff P = 1 := fun P hP => by
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply, hAT P hP, hTco,
      if_pos hP]
    ring
  constructor
  · intro h P hP
    have hc := P.componentGenericPoint_mem_of_nonempty hP
    have hgP : P.genericPoint ∈ U.unop := P.genericPoint_mem_of_nonempty hP
    change P.OrdGE _ (V.presheaf.germ _ _ hc r)
    by_cases hPT : P ∈ T
    · rw [hco P hPT]
      exact ordGE_one_germ_of_notMem_basicOpen P _ hgP (h P hPT hgP) hc
    · refine (ordGE_zero_germ P r hgP hc).mono ?_
      have := hA0 P
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply, hTco, if_neg hPT]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
  · intro h Q hQT hQU
    have hQV : (Q.support ∩ U.unop).Nonempty :=
      ⟨_, MMP.Flips.primeDivisor_genericPoint_mem_support Q, hQU⟩
    have hc := Q.componentGenericPoint_mem_of_nonempty hQV
    have h1 := h Q hQV
    rw [hco Q hQT] at h1
    exact (ordGE_one_germ_iff Q r hQU hc).1 h1

end Kernel

section Abelian

universe w z

/-- In an abelian category, let `u : O ⟶ P` be an epimorphism and `j ≫ η : O ⟶ Q` a morphism with
the same kernel as `u`. Then `j ≫ η` factors as `u ≫ c` with `c` a monomorphism. -/
private theorem exists_mono_comp_eq {C : Type w} [Category.{z} C] [Abelian C] {O P F Q : C}
    (u : O ⟶ P) [Epi u] (j : O ⟶ F) (η : F ⟶ Q) (h1 : kernel.ι u ≫ j ≫ η = 0)
    (h2 : kernel.ι (j ≫ η) ≫ u = 0) :
    ∃ c : P ⟶ Q, Mono c ∧ u ≫ c = j ≫ η := by
  let hc := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel u)
  let c : P ⟶ Q := hc.desc (CokernelCofork.ofπ (j ≫ η) h1)
  have hfac : u ≫ c = j ≫ η := hc.fac (CokernelCofork.ofπ (j ≫ η) h1) WalkingParallelPair.one
  refine ⟨c, ?_, hfac⟩
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z y hy
  obtain ⟨A', π, hπ, x, hx⟩ := surjective_up_to_refinements_of_epi u y
  have hx0 : x ≫ j ≫ η = 0 := by
    rw [← hfac, ← Category.assoc, ← hx, Category.assoc, hy, comp_zero]
  have hxu : x ≫ u = 0 := by
    rw [← kernel.lift_ι (j ≫ η) x hx0, Category.assoc, h2, comp_zero]
  exact zero_of_epi_comp π (by rw [hx, hxu])

end Abelian

section Vanishing

variable {R : Scheme.{0}}

open Stacks.AlgebraicGeometry in
/-- On an affine open of a locally Noetherian scheme, a section of a quasi-coherent module none
of whose associated points lies in the closed set `Z` vanishes as soon as it is killed by the
ideal of `Z`. -/
private theorem eq_zero_of_ideal_smul_eq_zero [IsLocallyNoetherian R] (N : R.Modules)
    [N.IsQuasicoherent] (Z : Closeds R)
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint N x → x ∉ (Z : Set R))
    {U : R.Opens} (hU : IsAffineOpen U) (t : Γ(N, U))
    (ht : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hU⟩, a • t = 0) : t = 0 := by
  by_contra ht0
  haveI : IsNoetherianRing Γ(R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Γ(R, U) t ht0
  let P' : PrimeSpectrum Γ(R, U) := ⟨P, hP.isPrime⟩
  set y : R := hU.fromSpec P' with hy
  have hyU : y ∈ U := by
    have : y ∈ Set.range hU.fromSpec := ⟨P', rfl⟩
    rwa [hU.range_fromSpec] at this
  have hyP : hU.primeIdealOf ⟨y, hyU⟩ = P' :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨y, hyU⟩)
  have hass : Stacks.Divisors.IsAssociatedPoint N y := by
    rw [AssociatedPointPrime.divisorsIsAssociatedPoint_iff_mem_associatedPrimes N hU hyU, hyP]
    exact hP
  apply hN y hass
  -- a function vanishing on `Z` but not at `y` would lie in `P` and not in `P`
  by_contra hyZ
  obtain ⟨f, hfZ, hyf⟩ := hU.exists_basicOpen_le
    (V := ⟨(Z : Set R)ᶜ, Z.isClosed.isOpen_compl⟩) ⟨y, hyZ⟩ hyU
  have hfI : f ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hU⟩ :=
    (mem_vanishingIdeal_ideal_iff Z ⟨U, hU⟩ f).2 fun x hxZ _ hxf => hfZ hxf hxZ
  have hfP : f ∈ P := hle (by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact ht f hfI)
  have : P' ∈ hU.fromSpec ⁻¹ᵁ R.basicOpen f := hyf
  rw [hU.fromSpec_preimage_basicOpen] at this
  exact this hfP

/-- A morphism into a quasi-coherent module none of whose associated points lies in `Z`
vanishes if every section of its source over an affine open is killed by the ideal of `Z`. -/
private theorem hom_eq_zero_of_forall_ideal_smul_eq_zero [IsLocallyNoetherian R]
    {M N : R.Modules} [N.IsQuasicoherent] (Z : Closeds R)
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint N x → x ∉ (Z : Set R))
    (hM : ∀ (U : R.affineOpens) (s : Γ(M, U.1)),
      ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U, a • s = 0)
    (φ : M ⟶ N) : φ = 0 := by
  apply (Scheme.Modules.toPresheaf R).map_injective
  let N' : TopCat.Sheaf AddCommGrpCat R := ⟨N.presheaf, N.isSheaf⟩
  refine TopCat.Sheaf.hom_ext M.presheaf N'
    (B := fun U : R.affineOpens => (U : R.Opens)) ?_ fun U => ?_
  · rw [show Set.range (fun U : R.affineOpens => (U : R.Opens)) = R.affineOpens from
      Subtype.range_coe]
    exact R.isBasis_affineOpens
  · rw [Functor.map_zero]
    change Scheme.Modules.Hom.app φ U.1 = Scheme.Modules.Hom.app 0 U.1
    rw [Scheme.Modules.Hom.zero_app]
    ext s
    refine eq_zero_of_ideal_smul_eq_zero N Z hN U.2 _ fun a ha => ?_
    rw [← Scheme.Modules.Hom.app_smul, hM U s a ha, map_zero]

end Vanishing

section Pushforward

variable {X V : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]

/-- **`g_* 𝒪_V(A) = 𝒪_X`.** For a proper birational morphism `g : V ⟶ X` of normal varieties and
an effective `g`-exceptional Cartier divisor `A`, the composite `𝒪_X ⟶ g_* 𝒪_V ⟶ g_* 𝒪_V(A)` is
an isomorphism. -/
private theorem isIso_unitHom_comp_map_structureSheafToDivisorialSheaf
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsVariety ℂ sX) (g : V ⟶ X)
    (hV : MMP.Mori.IsVariety ℂ (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g)
    (A : Divisor V) (hAc : A.IsCartier) (hA0 : 0 ≤ A)
    (hAexc : ∀ P, A.coeff P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P) :
    IsIso (unitHom g ≫ (Scheme.Modules.pushforward g).map
      (Divisor.structureSheafToDivisorialSheaf hA0)) := by
  haveI := hg.isDominant
  have hB0 : ∀ Z : irreducibleComponents V,
      g (componentGenericPoint V Z) ∉ (0 : Divisor X).supp := by
    intro Z h
    rwa [DivisorWithCoeffs.supp_zero] at h
  obtain ⟨e, he⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sX g hX hV
    hg 0 Divisor.isCartier_zero hB0 0 (Divisor.isPullback_zero hB0) A hAc hA0 hAexc
  have hle : (0 : Divisor V) + A ≤ A := le_of_eq (zero_add A)
  have hle' : A ≤ (0 : Divisor V) + A := le_of_eq (zero_add A).symm
  haveI : IsIso (Divisor.divisorialSheafInclusion hle) :=
    ⟨⟨Divisor.divisorialSheafInclusion hle', by
      rw [Divisor.divisorialSheafInclusion_comp]; exact Divisor.divisorialSheafInclusion_refl, by
      rw [Divisor.divisorialSheafInclusion_comp]; exact Divisor.divisorialSheafInclusion_refl⟩⟩
  have := MMP.Fourfold.subsingleton_irreducibleComponents (X := X)
  let ZX : irreducibleComponents X := pointComponent (genericPoint X)
  have hfac : unitHom g ≫ (Scheme.Modules.pushforward g).map
      (Divisor.structureSheafToDivisorialSheaf hA0) =
      Divisor.divisorialSheafZeroIso.inv ≫ e.hom ≫
        (Scheme.Modules.pushforward g).map (Divisor.divisorialSheafInclusion hle) := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext r
    apply Subtype.ext
    funext Z
    have hZX : componentGenericPoint X ZX ∈ U := by
      have h : g (componentGenericPoint V Z.1) ∈ U := Z.2
      rwa [MMP.Fourfold.map_componentGenericPoint g Z.1 ZX] at h
    let σ : (0 : Divisor X).divisorialSubmodule U :=
      (Divisor.divisorialSheafZeroIso (X := X)).inv.app U r
    have hσ : σ.1 ⟨ZX, hZX⟩ = X.presheaf.germ U _ hZX r :=
      congrFun (Divisor.coe_structureSheafToDivisorialSheaf_app
        (le_refl (0 : Divisor X)) U r) ⟨ZX, hZX⟩
    have h1 := fieldMap_eq_of_stalkSpecializes g ZX Z.1 (σ.1 ⟨ZX, hZX⟩)
      ((e.hom.app U σ).1 ⟨Z.1, Z.2⟩) (he U σ ZX hZX Z.1 Z.2).1
    rw [hσ, MMP.Fourfold.fieldMap_germ g ZX Z.1 hZX r] at h1
    change ((Divisor.structureSheafToDivisorialSheaf hA0).app (g ⁻¹ᵁ U) (g.app U r)).1 Z =
      (e.hom.app U σ).1 ⟨Z.1, Z.2⟩
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, toRationalFunctionsPresheaf_app_apply,
      ← h1]
  haveI : IsIso (Divisor.divisorialSheafZeroIso.inv ≫ e.hom ≫
      (Scheme.Modules.pushforward g).map (Divisor.divisorialSheafInclusion hle)) :=
    Iso.isIso_hom (Divisor.divisorialSheafZeroIso.symm ≪≫ e ≪≫
      (Scheme.Modules.pushforward g).mapIso (asIso (Divisor.divisorialSheafInclusion hle)))
  rw [hfac]
  infer_instance

/-- **The connecting map vanishes.** Let `g : V ⟶ X` be proper, `A` a Cartier divisor on `V` with
no component in the reduced divisor `T`, and `W ⊆ X` closed with `g(T) ⊆ W`. If no associated
point of `R¹g_* 𝒪_V(A - T)` lies in `W`, then `g_* 𝒪_V(A) ⟶ g_* 𝒪_T(A)` is an epimorphism,
where `𝒪_T(A) = ι_* ι^* 𝒪_V(A)`. -/
private theorem epi_pushforward_map_unit [CompactSpace V] (g : V ⟶ X) [IsProper g]
    (A : Divisor V) (hAc : A.IsCartier) (T : Finset (MMP.Mori.PrimeDivisor V))
    (hAT : ∀ P ∈ T, A P = 0) (W : Closeds X) (hTW : ∀ P ∈ T, g.base '' P.support ⊆ W)
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (A - ∑ P ∈ T, Finsupp.single P (1 : ℤ)).divisorialSheaf) x → x ∉ (W : Set X)) :
    Epi ((Scheme.Modules.pushforward g).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι).unit.app
          A.divisorialSheaf)) := by
  classical
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P (1 : ℤ) with hTD
  set ι := TD.suppIdeal.subschemeι with hι
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app A.divisorialSheaf
  set φ := Divisor.divisorialSheafInclusion (sub_le_self A (sum_single_one_nonneg T))
  haveI : IsReduced TD.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  haveI : Epi η := Stacks.ClosedImmersion.epi_unit_app ι A.divisorialSheaf
  have hSE : (ShortComplex.mk (kernel.ι η) η (kernel.condition η)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel η) }
  refine epi_map_g_of_forall_eq_zero (Scheme.Modules.pushforward g) hSE fun ψ => ?_
  have heq := imageSubmodule_eq_kernelSubmodule_unit A hAc T hAT
  let κ : kernel η ≅ (A - TD).divisorialSheaf :=
    (Stacks.Algebraization.kernelSubmoduleIso η).symm ≪≫ eqToIso (by rw [heq]) ≪≫
      (imageSubmoduleIso φ inferInstance).symm
  haveI : (((Scheme.Modules.pushforward g).rightDerived 1).obj
      (A - TD).divisorialSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived g _ 1
  let ψ' := (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.inv.app _ ≫ ψ ≫
    ((Scheme.Modules.pushforward g).rightDerived 1).map κ.hom
  have hψ' : ψ' = 0 := by
    refine hom_eq_zero_of_forall_ideal_smul_eq_zero W hN (fun U s a ha => ?_) ψ'
    have h0 : ι.app (g ⁻¹ᵁ U.1) (g.app U.1 a) = 0 := by
      apply eq_zero_of_basicOpen_eq_bot
      rw [← Scheme.Hom.preimage_basicOpen, ← Scheme.Hom.preimage_basicOpen]
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hy
      have hyT : ι y ∈ (TD.supp : Set V) := by
        have : ι y ∈ Set.range ι := ⟨y, rfl⟩
        rwa [hι, Scheme.IdealSheafData.range_subschemeι,
          DivisorWithCoeffs.coe_support_suppIdeal] at this
      obtain ⟨Q, hQ, hyQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyT
      have hQT : Q ∈ T := by
        by_contra hQT
        apply hQ
        rw [DivisorWithCoeffs.coeff_apply, hTD, sum_single_one_apply, if_neg hQT]
      have hW : g (ι y) ∈ (W : Set X) := hTW Q hQT ⟨ι y, hyQ, rfl⟩
      have hb : g (ι y) ∈ X.basicOpen a := hy
      exact (mem_vanishingIdeal_ideal_iff W U a).1 ha _ hW (X.basicOpen_le a hb) hb
    let s' : Γ((Scheme.Modules.pullback ι).obj A.divisorialSheaf, ι ⁻¹ᵁ g ⁻¹ᵁ U.1) := s
    change (ι.app (g ⁻¹ᵁ U.1) (g.app U.1 a)) • s' = 0
    rw [h0, zero_smul]
  have h1 : ψ ≫ ((Scheme.Modules.pushforward g).rightDerived 1).map κ.hom = 0 :=
    ((((Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf).app _).cancel_iso_inv_left _ _).1
      (by rwa [comp_zero])
  exact (cancel_mono (((Scheme.Modules.pushforward g).rightDerived 1).map κ.hom)).1
    (by rw [h1, zero_comp])

/-- **Surjectivity of `𝒪_X ⟶ g_* 𝒪_T`.** In the situation of
`epi_pushforward_map_unit`, with `g` birational and `A ≥ 0` exceptional, the comorphism
`𝒪_X ⟶ (ι ≫ g)_* 𝒪_T` of `T ⟶ X` is an epimorphism. -/
private theorem epi_unitHom_comp_of_isAssociatedPoint [CompactSpace V]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsVariety ℂ sX) (g : V ⟶ X)
    (hV : MMP.Mori.IsVariety ℂ (g ≫ sX)) [IsProper g] (hg : IsBirationalMorphism g)
    (A : Divisor V) (hAc : A.IsCartier) (hA0 : 0 ≤ A)
    (hAexc : ∀ P, A.coeff P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P)
    (T : Finset (MMP.Mori.PrimeDivisor V)) (hAT : ∀ P ∈ T, A P = 0) (W : Closeds X)
    (hTW : ∀ P ∈ T, g.base '' P.support ⊆ W)
    (hN : ∀ x, Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (A - ∑ P ∈ T, Finsupp.single P (1 : ℤ)).divisorialSheaf) x → x ∉ (W : Set X)) :
    Epi (unitHom ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι ≫ g)) := by
  classical
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P (1 : ℤ)
  set ι := TD.suppIdeal.subschemeι
  set η := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app A.divisorialSheaf
  set j := Divisor.structureSheafToDivisorialSheaf hA0
  set u := unitHom ι
  set G := Scheme.Modules.pushforward g
  haveI : Epi u := Scheme.Modules.epi_unitToPushforwardObjUnit ι
  haveI : HasKernel (j ≫ η) :=
    @HasKernels.has_limit _ _ _ (inferInstanceAs (HasKernels V.Modules)) _ _ (j ≫ η)
  have h1 : kernel.ι u ≫ j ≫ η = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.Hom.ext
    ext x
    have hz : (u.val.app U).hom (((kernel.ι u).val.app U).hom x) = 0 :=
      congrArg (fun t : kernel u ⟶ _ => (t.val.app U).hom x) (kernel.condition u)
    exact (app_unitHom_eq_zero_iff A hAc hA0 T hAT U _).1 hz
  have h2 : kernel.ι (j ≫ η) ≫ u = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    apply ModuleCat.Hom.ext
    ext x
    have hz : ((j ≫ η).val.app U).hom (((kernel.ι (j ≫ η)).val.app U).hom x) = 0 :=
      congrArg (fun t : kernel (j ≫ η) ⟶ _ => (t.val.app U).hom x) (kernel.condition (j ≫ η))
    exact (app_unitHom_eq_zero_iff A hAc hA0 T hAT U _).2 hz
  obtain ⟨c, hc, hfac⟩ := exists_mono_comp_eq u j η h1 h2
  haveI := (Scheme.Modules.pullbackPushforwardAdjunction g).rightAdjoint_preservesLimits
  haveI : Mono (G.map c) := G.map_mono c
  haveI hF1 := isIso_unitHom_comp_map_structureSheafToDivisorialSheaf sX hX g hV hg A hAc hA0 hAexc
  haveI hF2 : Epi (G.map η) := epi_pushforward_map_unit g A hAc T hAT W hTW hN
  have hcomp : (unitHom g ≫ G.map u) ≫ G.map c = (unitHom g ≫ G.map j) ≫ G.map η :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => unitHom g ≫ t)
      ((G.map_comp u c).symm.trans ((congrArg G.map hfac).trans (G.map_comp j η)))).trans
        (Category.assoc _ _ _).symm)
  haveI h3 : Epi ((unitHom g ≫ G.map u) ≫ G.map c) :=
    hcomp ▸ epi_comp' (IsIso.epi_of_iso _) hF2
  haveI : Epi (G.map c) := epi_of_epi (unitHom g ≫ G.map u) (G.map c)
  haveI : IsIso (G.map c) := isIso_of_mono_of_epi _
  haveI h4 : Epi (unitHom g ≫ G.map u) :=
    (((Category.assoc _ _ _).trans ((congrArg (fun t => (unitHom g ≫ G.map u) ≫ t)
      (IsIso.hom_inv_id (G.map c))).trans (Category.comp_id _))).symm) ▸
    epi_comp' h3 (IsIso.epi_of_iso _)
  have h5 : Epi ((Scheme.Modules.pushforwardComp ι g).app
      (SheafOfModules.unit TD.suppIdeal.subscheme.ringCatSheaf)).inv := inferInstance
  exact ((unitHom_comp ι g).trans (Category.assoc _ _ _).symm) ▸ epi_comp' h4 h5

end Pushforward

section Geometry

/-- The center of a divisor over an integral scheme `X` does not contain the generic point of
`X`: the valuation is nontrivial, so it does not dominate `𝒪_{X,η} = k(X)`. -/
private theorem genericPoint_notMem_center {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} (D : DivisorOver ℂ sX) :
    genericPoint X ∉ (D.center : Set X) := by
  intro h
  have hx : genericPoint X = D.f D.E.genericPoint := by
    refine (genericPoint_spec X).eq ?_
    rw [IsGenericPoint, ← DivisorOver.center_eq_closure_genericPoint D]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def]
    exact (D.center.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 h)
  obtain ⟨g, hg⟩ := MMP.Positivity.DivisorOver.exists_valuation_eq_exp_neg_one D
  obtain ⟨b, hb⟩ : ∃ b : X.presheaf.stalk (genericPoint X),
      @algebraMap _ X.functionField _ _ (stalkFunctionFieldAlgebra X (genericPoint X)) b = g⁻¹ :=
    ⟨g⁻¹, by
      rw [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
      rfl⟩
  have h1 := MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ hx b
  have h3 : D.valuation g⁻¹ ≤ 1 := by
    convert h1 using 2
    exact hb.symm
  rw [map_inv₀, hg] at h3
  exact absurd h3 (by simp)

/-- An snc subset is the union of the members of an snc divisor. -/
private theorem exists_finset_of_isSNCSubset {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : Closeds Y} (hS : IsSNCSubset sY S) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y), (⋃ E ∈ s, (E.support : Set Y)) = S ∧
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
  rcases hS with rfl | h
  · refine ⟨∅, by simp, ?_⟩
    rw [Finset.sum_empty]
    exact MMP.Mori.DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) _ hsm
  · exact h

/-- A member of a finite set of prime divisors lies in the support of their sum. -/
private theorem mem_support_sum_single {Y : Scheme.{0}} {s : Finset (MMP.Mori.PrimeDivisor Y)}
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∈ s) :
    P ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, hP]

universe u

/-- The support of an effective Cartier divisor on a scheme locally of finite type over a field
is of pure codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : IsPureCodimOne D.support := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine MMP.coheight_eq_one_of_isEffectiveCartierDivisor k hD (hW.1 hηW)
    fun y hy hyη => ?_
  have hle : W ≤ e.symm y := by
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
    exact hyη
  have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ D.support := by
    change closure {y} ⊆ _
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) D.support.isClosed
  have heq : e.symm y = W := le_antisymm (hW.2 hsub hle) hle
  rw [← heq, e.apply_symm_apply]

/-- The preimage in a subspace `C` of a preirreducible subset of `C` is preirreducible. -/
private theorem isPreirreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C W : Set Y}
    (hW : IsPreirreducible W) (hWC : W ⊆ C) : IsPreirreducible (Subtype.val ⁻¹' W : Set C) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWC hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible closed set contained in a closed set lies in an irreducible closed subset
maximal in it. -/
private theorem exists_maximal_ge {Y : Type*} [TopologicalSpace Y] {C : Set Y} (hC : IsClosed C)
    (Z : IrreducibleCloseds Y) (hZ : (Z : Set Y) ⊆ C) :
    ∃ W : IrreducibleCloseds Y, Maximal (fun W' : IrreducibleCloseds Y ↦ (W' : Set Y) ⊆ C) W ∧
      Z ≤ W := by
  obtain ⟨t, ht, hxt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' (Z : Set Y) : Set C)
    (isPreirreducible_preimage_val Z.isIrreducible.isPreirreducible hZ)
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  let W : IrreducibleCloseds Y := ⟨closure (Subtype.val '' t),
    (IsIrreducible.closure ⟨⟨z, ⟨z, hZ hz⟩, hxt hz, rfl⟩,
      ht.image _ continuous_subtype_val.continuousOn⟩), isClosed_closure⟩
  have hWC : (W : Set Y) ⊆ C := closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hC
  refine ⟨W, ⟨hWC, fun W' hW'C hWW' y hy ↦ ?_⟩, fun y hy ↦ subset_closure ⟨⟨y, hZ hy⟩, hxt hy, rfl⟩⟩
  have := hmax _ (isPreirreducible_preimage_val W'.isIrreducible.isPreirreducible hW'C)
    fun y hy ↦ hWW' (subset_closure ⟨y, hy, rfl⟩)
  have : (⟨y, hW'C hy⟩ : C) ∈ t := by rwa [← this]
  exact subset_closure ⟨_, this, rfl⟩

/-- The support of a prime divisor, as an irreducible closed subset. -/
private noncomputable def primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    IrreducibleCloseds X :=
  IrreducibleCloseds.closureSingleton E.genericPoint

private theorem coe_primeIrr {X : Scheme.{u}} (E : AlgebraicGeometry.PrimeDivisor X) :
    (primeIrr E : Set X) = E.support := by
  rw [E.support_eq_closure]; rfl

private theorem exists_mem_of_subset_iUnion {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)}
    (W : IrreducibleCloseds X) (hW : (W : Set X) ⊆ ⋃ E ∈ s, E.support) :
    ∃ E ∈ s, W ≤ primeIrr E := by
  classical
  obtain ⟨z, hz, hWz⟩ := (isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible)
    (s.image AlgebraicGeometry.PrimeDivisor.support)
    (by
      intro z hz
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← coe_primeIrr]; exact (primeIrr E).isClosed)
    (by
      intro x hx
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp (hW hx)
      exact ⟨E.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨E, hE, fun x hx ↦ by
    change x ∈ (primeIrr E : Set X); rw [coe_primeIrr]; exact hWz hx⟩

/-- A point of a closed subset `C` of pure codimension one inside the union `S` of a finite set
`s` of prime divisors lies on a member of `s` contained in `C`. -/
private theorem exists_mem_support_subset_of_isPureCodimOne {X : Scheme.{u}}
    {s : Finset (AlgebraicGeometry.PrimeDivisor X)} {S C : Closeds X}
    (hs : (⋃ E ∈ s, (E.support : Set X)) = S) (hC : IsPureCodimOne C) (hCS : C ≤ S) (x : X)
    (hx : x ∈ (C : Set X)) :
    ∃ E ∈ s, x ∈ (E.support : Set X) ∧ (E.support : Set X) ⊆ C := by
  obtain ⟨W, hW, hxW⟩ := exists_maximal_ge C.isClosed
    (IrreducibleCloseds.closureSingleton x) (by
      change closure {x} ⊆ (C : Set X)
      exact closure_minimal (by simpa using hx) C.isClosed)
  have hxW' : x ∈ (W : Set X) := hxW (subset_closure rfl)
  obtain ⟨E, hE, hWE⟩ := exists_mem_of_subset_iUnion W (hs ▸ hW.1.trans hCS)
  have hWE' : W = primeIrr E := by
    by_contra hne
    have hlt : W < primeIrr E := lt_of_le_of_ne hWE hne
    have := Order.coheight_add_one_le hlt
    rw [← codimension_eq_coheight, ← codimension_eq_coheight,
      show codimension (primeIrr E) = 1 from E.codimension_one,
      hC W hW] at this
    exact absurd this (by decide)
  refine ⟨E, hE, ?_, ?_⟩
  · rw [← coe_primeIrr, ← hWE']; exact hxW'
  · rw [← coe_primeIrr, ← hWE']; exact hW.1

/-- A maximal irreducible subset of a closed set is closed. -/
private theorem isClosed_of_maximal_irreducible_subset {Y : Type*} [TopologicalSpace Y]
    {C S : Set Y} (hC : IsClosed C)
    (hS : Maximal (fun T : Set Y => IsIrreducible T ∧ T ⊆ C) S) : IsClosed S := by
  have : closure S = S :=
    le_antisymm (hS.2 ⟨hS.1.1.closure, closure_minimal hS.1.2 hC⟩ subset_closure) subset_closure
  exact this ▸ isClosed_closure

end Geometry

/-- **Members of an snc divisor through a point.** If `x` lies on the members of `J ⊆ Supp D` of
an snc divisor `D` and its local ring has dimension at most `|J|`, then the members of `Supp D`
through `x` are those of `J`: their local equations are distinct members of a regular system of
parameters at `x`. -/
private theorem mem_of_isSNC_of_ringKrullDim_le {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : DivisorWithCoeffs R Y} (hD : D.IsSNC sY)
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (hJ : J ⊆ D.support) {x : Y}
    (hxJ : ∀ E ∈ J, x ∈ (E.support : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk x) ≤ J.card) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P ∈ D.support) (hxP : x ∈ (P.support : Set Y)) : P ∈ J := by
  classical
  by_contra hPJ
  obtain ⟨n, z, j, hz, hj, -⟩ := hD.2 x
  have hn : (n : WithBot ℕ∞) ≤ J.card := hz.2 ▸ hdim
  have hn' : n ≤ J.card := by exact_mod_cast hn
  have hmem : ∀ E ∈ insert P J, E ∈ D.support ∧ x ∈ (E.support : Set Y) := by
    intro E hE
    rcases Finset.mem_insert.1 hE with rfl | hE
    · exact ⟨hP, hxP⟩
    · exact ⟨hJ hE, hxJ E hE⟩
  let g : {E : MMP.Mori.PrimeDivisor Y // E ∈ insert P J} →
      {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ x ∈ E.support} :=
    fun E => ⟨E.1, hmem E.1 E.2⟩
  have hinj : Function.Injective (fun E => j (g E)) := fun a b h =>
    Subtype.ext (congrArg Subtype.val (hj h) : (g a).1 = (g b).1)
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Finset.card_insert_of_notMem hPJ, Fintype.card_fin] at this
  omega

section Strata

/-- On a smooth variety, the local ring at the generic point of a nonempty stratum of members of
an snc divisor `∑ s` has dimension at most the number of members cut out. -/
theorem ringKrullDim_stalk_le_card_of_isSNCStratum {V : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] {sV : V ⟶ Spec (.of ℂ)} (hVvar : MMP.Mori.IsVariety ℂ sV)
    (hsm : MMP.Mori.IsSmoothScheme sV) (sbig : Finset (MMP.Mori.PrimeDivisor V))
    (hsnc : DivisorWithCoeffs.IsSNC sV (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)))
    (J : Finset (MMP.Mori.PrimeDivisor V)) (hJs : ∀ H ∈ J, H ∈ sbig) (hJ0 : ¬ J = ∅)
    {S : Set V} (hSm : Maximal (fun T : Set V => IsIrreducible T ∧
      T ⊆ ⋂ E ∈ J, (E.support : Set V)) S) (hScl : IsClosed S) {σ : V}
    (hσ : IsGenericPoint σ S) : ringKrullDim (V.presheaf.stalk σ) ≤ J.card := by
  classical
  rw [ringKrullDim_stalk_eq_coheight]
  rcases Nat.lt_or_ge J.card 2 with hlt | h2
  · interval_cases hcard : J.card
    · exact absurd (Finset.card_eq_zero.1 hcard) hJ0
    · obtain ⟨H, rfl⟩ := Finset.card_eq_one.1 hcard
      have hHirr : IsIrreducible (H.support : Set V) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have hSH : S = (H.support : Set V) :=
        le_antisymm (by simpa using hSm.1.2) (hSm.2 ⟨hHirr, by simp⟩ (by simpa using hSm.1.2))
      have hgH : IsGenericPoint H.genericPoint S := by
        rw [hSH, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isGenericPoint_closure
      rw [hσ.eq hgH, H.coheight_genericPoint]
      simp
  let fam : {P : MMP.Mori.PrimeDivisor V // P ∈ sbig} → MMP.Mori.PrimeDivisor V := Subtype.val
  have hfam : Function.Injective fam := Subtype.val_injective
  have hsncfam : DivisorWithCoeffs.IsSNC sV (∑ o, Finsupp.single (fam o) (1 : ℤ)) := by
    rw [Finset.sum_coe_sort sbig (fun E => Finsupp.single E (1 : ℤ))]
    exact hsnc
  let J3 : Finset {P : MMP.Mori.PrimeDivisor V // P ∈ sbig} :=
    Finset.univ.filter (fun o => fam o ∈ J)
  have hJ3card : J3.card = J.card :=
    Finset.card_bij (fun o _ => fam o) (fun o ho => (Finset.mem_filter.1 ho).2)
      (fun a _ b _ h => hfam h)
      (fun H hH => ⟨⟨H, hJs H hH⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hH⟩, rfl⟩)
  have hinter3 : (⋂ o ∈ J3, ((fam o).support : Set V)) = ⋂ H ∈ J, (H.support : Set V) := by
    ext y
    simp only [Set.mem_iInter, J3, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h H hH => h ⟨H, hJs H hH⟩ hH, fun h o ho => h (fam o) ho⟩
  obtain ⟨-, hcod, -⟩ := MMP.Resolution.blowUp_snc_stratum sV hVvar hsm fam hfam hsncfam J3
    (hJ3card ▸ h2) ⟨S, hinter3 ▸ hSm⟩
  have hcl : TopologicalSpace.Closeds.closure S =
      ⟨(TopologicalSpace.IrreducibleCloseds.closureSingleton σ : Set V),
        (TopologicalSpace.IrreducibleCloseds.closureSingleton σ).isClosed⟩ := by
    ext1
    change closure S = closure {σ}
    rw [hσ.def, hScl.closure_eq]
  change MMP.Mori.closedsCodimension (TopologicalSpace.Closeds.closure S) = _ at hcod
  rw [hcl, MMP.Mori.closedsCodimension_coe,
    Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hJ3card] at hcod
  rw [hcod]
  norm_cast

/-- **No stratum of the boundary maps into `W`.** Let `V` be a smooth variety, `g : V ⟶ X` and
`W ⊆ X` closed, such that `g⁻¹(W) ≠ V` is covered by members of an snc divisor `∑ s` lying over
`W`. If `D` is a divisor with `Supp D ⊆ ∑ s` none of whose components maps into `W`, then no snc
stratum of `D` maps into `W`: at the generic point of such a stratum another member of `∑ s`
would pass through it, against the snc condition. -/
private theorem not_image_subset_of_isSNCStratum {X V : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] {sV : V ⟶ Spec (.of ℂ)} (hVvar : MMP.Mori.IsVariety ℂ sV)
    (hsm : MMP.Mori.IsSmoothScheme sV) (g : V ⟶ X) (W : Closeds X)
    (sbig : Finset (MMP.Mori.PrimeDivisor V))
    (hsnc : DivisorWithCoeffs.IsSNC sV (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)))
    (hWdiv : ∀ x : V, g x ∈ (W : Set X) →
      ∃ E ∈ sbig, x ∈ (E.support : Set V) ∧ g.base '' E.support ⊆ W)
    (hgW : ∃ x : V, g x ∉ (W : Set X)) (D : Divisor V) (hDs : ∀ P ∈ D.support, P ∈ sbig)
    (hD : ∀ P ∈ D.support, ¬ g.base '' P.support ⊆ W) (S : Set V)
    (hS : MMP.Fourfold.IsSNCStratum D S) : ¬ g.base '' S ⊆ W := by
  classical
  intro hSW
  obtain ⟨J, hJ, hSm⟩ := hS
  have hScl : IsClosed S := isClosed_of_maximal_irreducible_subset
    (isClosed_biInter fun E _ => E.idealSheaf.support.isClosed) hSm
  obtain ⟨σ, hσ⟩ := QuasiSober.sober hSm.1.1 hScl
  have hσJ : ∀ H ∈ J, σ ∈ (H.support : Set V) := fun H hH =>
    Set.mem_iInter₂.1 (hSm.1.2 hσ.mem) H hH
  have hσW : g σ ∈ (W : Set X) := hSW ⟨σ, hσ.mem, rfl⟩
  by_cases hJ0 : J = ∅
  · subst hJ0
    have hSu : S = Set.univ := le_antisymm (Set.subset_univ _)
      (hSm.2 ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ => by simp⟩ (Set.subset_univ _))
    obtain ⟨x, hx⟩ := hgW
    exact hx (hSW ⟨x, hSu ▸ Set.mem_univ x, rfl⟩)
  obtain ⟨E, hE, hσE, hEW⟩ := hWdiv σ hσW
  have hJsupp : J ⊆ (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)).support := fun H hH =>
    mem_support_sum_single (hDs H (hJ hH))
  have hdim := ringKrullDim_stalk_le_card_of_isSNCStratum hVvar hsm sbig hsnc J
    (fun H hH => hDs H (hJ hH)) hJ0 hSm hScl hσ
  have hEJ := mem_of_isSNC_of_ringKrullDim_le hsnc hJsupp hσJ hdim (mem_support_sum_single hE) hσE
  exact hD E (hJ hEJ) hEW

end Strata

section Free

/-- A Cartier divisor whose sheaf is a pull-back from the base is free over the base: the counit
of `g^* ⊣ g_*` is split at a pulled-back module. -/
private theorem isRelativelyFreeCartier_of_iso_pullback {W R : Scheme.{0}} (g : W ⟶ R)
    (E : W.CartierDivisor) (L : R.Modules)
    (e : MMP.CartierDivisor.sheaf E ≅ (Scheme.Modules.pullback g).obj L) :
    IsRelativelyFreeCartier g E := by
  have h := MMP.Mori.epi_counit_app_pullback g L
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  have hn := adj.counit.naturality e.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have heq : adj.counit.app (MMP.CartierDivisor.sheaf E) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward g).map e.hom) ≫
        adj.counit.app _ ≫ e.inv := by
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Epi (adj.counit.app _)
  rw [heq]
  infer_instance

section Semiample

variable {X R W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] [CompactSpace R]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **The pull-back of a `ℚ`-linear pull-back from the base is semiample over the base.** If
`(cN) L = (mN) f^*D_H + div χ` on `X` for a Cartier `D_H` on `R`, then `-(1/m) p^*L` is
semiample over `R` on a smooth `W`. -/
private theorem isRelativelySemiample_neg_smul_pullback {k : Type} [Field k] [IsAlgClosed k]
    (sW : W ⟶ Spec (.of k))
    (hWsm : IsSmoothScheme sW) (f : X ⟶ R) [IsDominant f] (p : W ⟶ X) [IsDominant p]
    {m N c : ℕ} (hm : 0 < m) (hN : 0 < N) (hc : 0 < c) {L : Divisor X} (hLc : L.IsCartier)
    {LW : Divisor W}
    (hLW : L.IsPullback p (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L)
      LW)
    {DH : Divisor R} (hDH : DH.IsCartier) {DX : Divisor X} (hDXc : DX.IsCartier)
    (hDX : DH.IsPullback f (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f DH)
      DX)
    (χ : (RationalFunctions X)ˣ)
    (hrel : ((c * N : ℕ) : ℤ) • L = ((m * N : ℕ) : ℤ) • DX + principalDivisor χ) :
    MMP.Fourfold.QDivisor.IsRelativelySemiample (p ≫ f)
      (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)) := by
  classical
  have hBp : ∀ (C : Divisor X) (Z : irreducibleComponents W),
      p (componentGenericPoint W Z) ∉ C.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p
  have hBf : ∀ (C : Divisor R) (Z : irreducibleComponents X),
      f (componentGenericPoint X Z) ∉ C.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f
  -- the pull-backs of `D_X` and of `χ`
  set DW : Divisor W := DX.pullback hDXc (hBp DX)
  have hDW : DX.IsPullback p (hBp DX) DW := Divisor.isPullback_pullback hDXc (hBp DX)
  set χW := pullbackRationalFunction p χ (hBp (principalDivisor χ))
  have hχW := Divisor.isPullback_principalDivisor (f := p) χ (hBp _)
  -- the relation on `W`
  have hrelW : ((c * N : ℕ) : ℤ) • LW = ((m * N : ℕ) : ℤ) • DW + principalDivisor χW := by
    have h1 := (hLW.zsmul hLc ((c * N : ℕ) : ℤ) (hBp _)).of_eq hrel (hB₂ := hBp _)
    have h2 := (hDW.zsmul hDXc ((m * N : ℕ) : ℤ) (hBp _)).add (hDXc.zsmul _)
      (Divisor.isCartier_principalDivisor χ) (hBp _) hχW
    exact h1.eq ((hDXc.zsmul _).add (Divisor.isCartier_principalDivisor χ)) h2
  set D'' : Divisor W := -(((m * N : ℕ) : ℤ) • DW + principalDivisor χW) with hD''def
  have hn : 0 < m * c * N := Nat.mul_pos (Nat.mul_pos hm hc) hN
  have hD'' : ∀ P, (D''.coeff P : ℚ) =
      ((m * c * N : ℕ) : ℚ) * (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)).coeff P := by
    intro P
    have h := congrArg (fun D : Divisor W => (D.coeff P : ℚ)) hrelW
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul,
      Int.cast_mul, Int.cast_add, Int.cast_natCast] at h
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hinv : (m : ℚ) * (1 / (m : ℚ)) = 1 := by field_simp
    have hQ : (-((1 / (m : ℚ)) • Divisor.toQDivisor LW)).coeff P =
        -((1 / (m : ℚ)) * (LW.coeff P : ℚ)) := by
      rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
        smul_eq_mul]
    have hD : (D''.coeff P : ℚ) = -((((m * N : ℕ) : ℤ) : ℚ) * (DW.coeff P : ℚ) +
        ((principalDivisor χW).coeff P : ℚ)) := by
      rw [hD''def, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul]
      push_cast
      ring
    rw [hQ, hD]
    push_cast at h ⊢
    linear_combination h + ((c : ℚ) * N * (LW.coeff P : ℚ)) * hinv
  obtain ⟨E'', hE''⟩ :=
    (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2 W
      (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme sW hWsm) D''
  have hfree : IsRelativelyFreeCartier (p ≫ f) E'' := by
    have hDHn := hDX.zsmul hDH (-((m * N : ℕ) : ℤ)) (hBf _)
    have hDWn := hDW.zsmul hDXc (-((m * N : ℕ) : ℤ)) (hBp _)
    have hlin : D''.LinearlyEquivalent ((-((m * N : ℕ) : ℤ)) • DW) :=
      ⟨χW⁻¹, by rw [MMP.Mori.principalDivisor_inv, hD''def, neg_smul]; abel⟩
    exact isRelativelyFreeCartier_of_iso_pullback (p ≫ f) E''
      ((-((m * N : ℕ) : ℤ)) • DH).divisorialSheaf
      (hE''.sheafIsoDivisorialSheaf ≪≫ hlin.divisorialSheafIso ≪≫
        Divisor.IsPullback.divisorialSheafIso (hBc := hDXc.zsmul _) hDWn ≪≫
        (Scheme.Modules.pullback p).mapIso
          (Divisor.IsPullback.divisorialSheafIso (hBc := hDH.zsmul _) hDHn) ≪≫
        (Scheme.Modules.pullbackComp p f).app _)
  exact MMP.Fourfold.QDivisor.isRelativelySemiample_of_isRelativelyFreeCartier (p ≫ f) _
    (m * c * N) hn D'' hD'' E'' hE'' hfree

end Semiample

end Free

section Crepant

/-- Every divisor is its own pull-back along the identity. -/
private theorem isPullback_id {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (M : Divisor X) :
    M.IsPullback (𝟙 X) (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 X) M)
      M := by
  intro U φ hφ E hE
  have hffm : ∀ t : X.functionField, functionFieldMap (𝟙 X) t = t := fun t =>
    (functionFieldMap (𝟙 X)).injective
      (MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply (𝟙 X) (𝟙 X) (Category.id_comp _) t)
  have hfm : ∀ x, MMP.Fourfold.fieldMap (𝟙 X) E.component E.component x = x := by
    intro x
    rw [MMP.Fourfold.fieldMap_eq, RingHom.comp_apply, RingHom.comp_apply, hffm,
      ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  have hu : MMP.Mori.pullbackComponent (𝟙 X)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (𝟙 X) M) hφ E.component
        (E.map_componentGenericPoint_mem (𝟙 X) hE) =
      Units.map (RationalFunctions.component X E.component).toMonoidHom φ := by
    ext
    rw [MMP.Fourfold.pullbackComponent_eq_fieldMap (𝟙 X) _ hφ E.component _ E.component, hfm]
    rfl
  rw [hu, ← PrimeDivisor.ord_eq_ordUnit]
  exact hφ E hE

/-- A closed subset of a Noetherian space which is a union of irreducible closed subsets from a
family `S` is already the union of finitely many members of `S`: each of its finitely many
irreducible pieces has its generic point in some member of `S`. -/
private theorem exists_finset_subset_eq_biUnion {X : Scheme.{0}} [IsLocallyNoetherian X]
    [CompactSpace X] (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ S' : Finset (IrreducibleCloseds X), (S' : Set (IrreducibleCloseds X)) ⊆ S ∧
      (W : Set X) = ⋃ Z ∈ S', (Z : Set X) := by
  classical
  haveI : IsNoetherian X := {}
  obtain ⟨T, hT, hTW⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible W
  have key : ∀ C ∈ T, ∃ Z ∈ S, (C : Set X) ⊆ Z := by
    intro C hC
    have hirr : IsIrreducible (C : Set X) := hT ⟨C, hC⟩
    have hCW : (C : Set X) ⊆ W := by
      rw [hTW]
      exact (Finset.le_sup (f := id) hC : C ≤ T.sup id)
    have hgen := hirr.isGenericPoint_genericPoint_closure
    rw [C.isClosed.closure_eq] at hgen
    have hξ : hirr.genericPoint ∈ (W : Set X) := hCW hgen.mem
    rw [hW] at hξ
    simp only [Set.mem_iUnion] at hξ
    obtain ⟨Z, hZS, hξZ⟩ := hξ
    refine ⟨Z, hZS, ?_⟩
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξZ) Z.isClosed
  choose f hfS hfC using key
  refine ⟨T.attach.image fun C => f C.1 C.2, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hZ
    exact hfS C.1 C.2
  · apply le_antisymm
    · intro x hx
      have hx' : x ∈ ((T.sup id : Closeds X) : Set X) := by rwa [← hTW]
      rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hx'
      simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Function.comp_apply, id] at hx'
      obtain ⟨C, hC, hxC⟩ := hx'
      simp only [Set.mem_iUnion, Finset.mem_image]
      exact ⟨f C hC, ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩, hfC C hC hxC⟩
    · intro x hx
      simp only [Set.mem_iUnion, Finset.mem_image] at hx
      obtain ⟨Z, ⟨C, -, rfl⟩, hxZ⟩ := hx
      rw [hW]
      simp only [Set.mem_iUnion]
      exact ⟨f C.1 C.2, hfS C.1 C.2, hxZ⟩

/-- On a variety, the valuation of every divisor over `X` has a nonempty centre: it is realized
by a divisor on a projective birational model of `X`, which dominates the local ring at the
centre `f(η_E)`. -/
private theorem hasNonemptyCenter_valuation {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sX] (E : DivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  have hdiv : MMP.Flips.IsDivisorOfFunctionField ℂ sX E.valuation :=
    MMP.Fourfold.SNCWeight.Restriction.isDivisorOfFunctionField_comap_primeDivisor sX E.f
      E.isNormalVariety E.isBirationalMorphism.functionFieldMap_bijective E.E
  obtain ⟨D, -, hD, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hdiv
    (E.f E.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E _ rfl)
  exact ⟨hdiv, D, hD⟩

/-- **A crepant log resolution adapted to `W`.** There is a projective birational morphism
`g : V ⟶ X` from a smooth projective variety with a canonical divisor `K_V` and a `ℚ`-divisor
`B_V` with snc support, coefficients `≤ 1` and negative coefficients only along `g`-exceptional
divisors, such that `K_V + B_V = g^*(K + B)` through every Cartier multiple of `K + B`; and a
finite set `T` of prime divisors of `V` of coefficient one in `B_V`, mapping into `W`, whose images
cover `W`. -/
private theorem exists_crepantModel_snc_preimage
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sV) (g : V ⟶ X) (_ : IsDominant g)
      (KV : Divisor V) (BV : QDivisor V) (T : Finset (MMP.Mori.PrimeDivisor V)),
      MMP.Mori.IsSmoothScheme sV ∧ g ≫ sX = sV ∧ IsProjective g ∧ IsProper g ∧
      IsBirationalMorphism g ∧ KV.IsCanonicalDivisor sV n ∧
      (∃ (hV : IsNormalVariety ℂ (g ≫ sX)) (hg : IsBirationalMorphism g),
        IsCrepantBoundary sX n K B g hV hg BV) ∧ BV.IsSNC sV ∧ (∀ P, BV P ≤ 1) ∧
      (∀ P, BV P < 0 → RationalMap.IsExceptional g.toRationalMap P) ∧
      (∀ (m : ℕ), 0 < m → ∀ D : Divisor X,
        Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + B) → D.IsCartier →
          ∃ DV : Divisor V, Divisor.toQDivisor DV = (m : ℤ) • (Divisor.toQDivisor KV + BV) ∧
            ∃ hD, D.IsPullback g hD DV) ∧
      (∀ P ∈ T, BV P = 1 ∧ g.base '' P.support ⊆ W) ∧
      (W : Set X) ⊆ ⋃ P ∈ T, g.base '' P.support ∧
      genericPoint X ∉ (W : Set X) ∧
      ∃ sbig : Finset (MMP.Mori.PrimeDivisor V),
        DivisorWithCoeffs.IsSNC sV (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)) ∧
        (∀ P ∈ BV.support, P ∈ sbig) ∧
        ∀ x : V, g x ∈ (W : Set X) →
          ∃ E ∈ sbig, x ∈ (E.support : Set V) ∧ g.base '' E.support ⊆ W := by
  classical
  have hX : IsNormalVariety ℂ sX := hB.1.1
  have hPw : IsPairWith sX n K B := hB.1
  have hP : IsPair sX B := hB.isPair
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).2 ⟨hX.1, hproj⟩
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  -- finitely many centres, each with a divisor of discrepancy `-1`
  obtain ⟨S', hS'S, hWS'⟩ := exists_finset_subset_eq_biUnion W S hW
  choose E hEc hEd using fun Z : S' => hS Z.1 (hS'S Z.2)
  -- a smooth projective model `W₀` on which every `E Z` is a prime divisor
  obtain ⟨W₀, w, hW₀, hwb, -, hsm₀, hwp, -, hE', hpv⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX
      (ι := PUnit.{1}) (fun _ => 𝟙 X) (fun _ => isBirationalMorphism_of_isIso _)
      (fun _ => by simpa using hX)
      (κ := S') (fun Z => (E Z).valuation) (fun Z => hasNonemptyCenter_valuation sX (E Z))
  choose E' hE'v using hE'
  haveI : IsIntegral W₀ := hW₀.1.toIsIntegral
  haveI : LocallyOfFiniteType (w ≫ sX) := hW₀.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sX)
  haveI : IsNormal W₀ := hW₀.2
  haveI := hwb.isDominant
  -- the crepant boundary of `(X, B)` on `W₀`
  obtain ⟨⟨B₀, hB₀, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hB.1.2.1 w hW₀ hwb
  -- `W` does not contain the generic point of `X`
  have hηW : genericPoint X ∉ (W : Set X) := by
    rw [hWS']
    simp only [Set.mem_iUnion, not_exists]
    intro Z hZ hmem
    have hmem' : genericPoint X ∈ ((E ⟨Z, hZ⟩).center : Set X) := by
      rwa [hEc ⟨Z, hZ⟩]
    exact genericPoint_notMem_center (E ⟨Z, hZ⟩) hmem'
  -- a principalization of `ℐ_{w⁻¹ W} · ℐ_{Supp B₀ ∪ ⋃ E'}` on `W₀`
  set Zw : Closeds W₀ := W.preimage w.continuous
  set S₀ : Closeds W₀ := ⟨(B₀.support ∪ Finset.univ.image E').sup
    fun E => (E.idealSheaf.support : Set W₀), by
      rw [Finset.sup_set_eq_biUnion]
      exact isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed⟩
  set I := Scheme.IdealSheafData.vanishingIdeal Zw * Scheme.IdealSheafData.vanishingIdeal S₀
    with hI
  have hIne : I ≠ ⊥ := by
    intro h0
    have hξ : genericPoint W₀ ∈ (I.support : Set W₀) := by
      rw [h0, Scheme.IdealSheafData.support_bot]; trivial
    rw [hI, Scheme.IdealSheafData.support_mul, Closeds.coe_sup,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hξ
    rcases hξ with h1 | h2
    · apply hηW
      have : w (genericPoint W₀) = genericPoint X := map_genericPoint_of_isDominant w
      rw [← this]
      exact h1
    · change genericPoint W₀ ∈ ((B₀.support ∪ Finset.univ.image E').sup
        fun E => (E.idealSheaf.support : Set W₀)) at h2
      rw [Finset.sup_set_eq_biUnion] at h2
      obtain ⟨E₀, -, hE₀⟩ := Set.mem_iUnion₂.1 h2
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support E₀ hE₀
  obtain ⟨Y, h, hYv, hhp, hhb, hhsm, -, hcart, hsncI, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (w ≫ sX) hW₀.1 I
      hIne
  have hres : MMP.Resolution.IsResolutionOfVariety (w ≫ sX) h := ⟨hW₀.1, hYv, hhp, hhb, hhsm⟩
  haveI : IsProper h := hres.isProjective.isProper
  haveI : IsProper w := hwp.isProjective.isProper
  haveI : IsIntegral Y := hres.isVariety_source.toIsIntegral
  set g : Y ⟶ X := h ≫ w with hg
  have hgb : IsBirationalMorphism g :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational w h
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hwb)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hres.isBirationalMorphism)
  have hgres : IsSmoothResolution sX g := ⟨inferInstance, hgb, by
    have := hres.isSmoothScheme; rwa [hg, Category.assoc]⟩
  obtain ⟨hY, hdimY, -⟩ := hgres.isNormalVariety hX
  haveI : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI := hgb.isDominant
  have hgproj : IsProjective g := hres.isProjective.comp hwp.isProjective
  have hprojY : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ (g ≫ sX)).2 ⟨hY.1,
      isProjectiveMorphism_of_isProjective_of_isAffine (g ≫ sX)
        (hgproj.comp hproj.isProjective)⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ sX) := hY.1
  -- a canonical divisor `K_V` with `g_* K_V = K`, and the crepant boundary `B_V`
  have hn : topologicalKrullDim Y = n := hdimY.trans hB.1.2.1.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hgres.isSmoothScheme hn
  obtain ⟨KV, hKV, hKVt⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hX hY hgb hB.1.2.1 hK₀
  obtain ⟨⟨BV, hBV, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hB.1.2.1 g hY hgb
  have hpull := IsPair.isPullback_of_isCrepantBoundary hP g hY hgb hB.1.2.1 hKV
    (Or.inr ⟨inferInstance, hKVt⟩) hBV
  -- the strict transforms on `V` of the divisors `E' Z`
  have hT : ∀ j : S', ∃ T : MMP.Mori.PrimeDivisor Y,
      (⟨Y, g, hY, hgb, T⟩ : DivisorOver ℂ sX).valuation = (E j).valuation := fun j => by
    obtain ⟨T, hT⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq
      (⟨W₀, w, hW₀, hwb, E' j⟩ : DivisorOver ℂ sX) g hY hgb h hres.isBirationalMorphism rfl
    exact ⟨T, hT.trans (hE'v j)⟩
  choose Tj hTj using hT
  -- the coefficients of `B_V`: at most one, and negative only along `g`-exceptional divisors
  have hcoef : ∀ P : MMP.Mori.PrimeDivisor Y, BV P ≤ 1 ∧
      (¬ (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).IsExceptional → 0 ≤ BV P) := by
    intro P
    by_cases hPe : (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).IsExceptional
    · refine ⟨?_, fun h => absurd hPe h⟩
      have h1 : (((BV.coeff P : ℚ) : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) := by
        simpa using (discrep_le hPe (hBV P)).trans' hB.2
      rw [← DivisorWithCoeffs.coeff_apply]
      exact_mod_cast EReal.coe_le_coe_iff.mp h1
    · obtain ⟨Γ, -, hΓ⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw _ hPe
      have hco : BV.coeff P = B.coeff Γ := neg_injective ((hBV P).eq hΓ)
      rw [← DivisorWithCoeffs.coeff_apply, hco]
      exact ⟨hB1 Γ, fun _ => hBeff Γ⟩
  -- the strict transforms `T_j` lie over the centres `Z_j`
  have hTη : ∀ j : S', g (Tj j).genericPoint = (E j).f (E j).E.genericPoint := fun j =>
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 (hTj j)
  have hZ : ∀ j : S', ((j : IrreducibleCloseds X) : Set X) = closure {g (Tj j).genericPoint} :=
    fun j => by
      rw [hTη j, ← hEc j]
      exact DivisorOver.center_eq_closure_genericPoint (E j)
  have hgs : g ≫ sX = h ≫ w ≫ sX := by rw [hg, Category.assoc]
  have hYW : IsNormalVariety ℂ (h ≫ w ≫ sX) := hgs ▸ hY
  haveI := hres.isBirationalMorphism.isDominant
  -- `Supp B_V` lies in the snc divisor `Ex(h) ∪ h⁻¹(Supp B₀ ∪ ⋃ E')`
  have hval : ∀ P : MMP.Mori.PrimeDivisor Y, (⟨Y, g, hY, hgb, P⟩ : DivisorOver ℂ sX).valuation =
      (⟨Y, h, hYW, hres.isBirationalMorphism, P⟩ : DivisorOver ℂ (w ≫ sX)).valuation.comap
        (functionFieldMap w) := by
    intro P; ext x
    change P.divisorialValuation (functionFieldMap g x) =
      P.divisorialValuation (functionFieldMap h (functionFieldMap w x))
    rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply h w hg.symm]
  have hval₀ : ∀ P₀ : MMP.Mori.PrimeDivisor W₀,
      (⟨W₀, w, hW₀, hwb, P₀⟩ : DivisorOver ℂ sX).valuation =
        (DivisorOver.ofPrimeDivisor ℂ hW₀ P₀).valuation.comap (functionFieldMap w) := by
    intro P₀; ext x
    change P₀.divisorialValuation (functionFieldMap w x) =
      P₀.divisorialValuation (functionFieldMap (𝟙 W₀) (functionFieldMap w x))
    rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply (𝟙 W₀) w (Category.id_comp w)]
  have hsupp : ∀ P ∈ BV.support, P.genericPoint ∈ ((exceptionalSet h : Set Y) ∪
      h ⁻¹' ((B₀.support ∪ Finset.univ.image E').sup
        fun E => (E.idealSheaf.support : Set W₀))) := by
    intro P hP
    by_cases hPe :
        (⟨Y, h, hYW, hres.isBirationalMorphism, P⟩ : DivisorOver ℂ (w ≫ sX)).IsExceptional
    · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet P hPe
        (MMP.Flips.primeDivisor_genericPoint_mem_support P))
    · right
      obtain ⟨P₀, hP₀⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hW₀ _ hPe
      have hη : h P.genericPoint = P₀.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hW₀.1 hP₀
      have hco : BV.coeff P = B₀.coeff P₀ := neg_injective
        (MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw
          (by rw [hval, hval₀, hP₀]) (hBV P) (hB₀ P₀))
      show h P.genericPoint ∈
        ((B₀.support ∪ Finset.univ.image E').sup fun E => (E.idealSheaf.support : Set W₀))
      rw [hη, Finset.sup_set_eq_biUnion]
      refine Set.mem_iUnion₂.2 ⟨P₀, Finset.mem_union_left _ ?_,
        MMP.Flips.primeDivisor_genericPoint_mem_support P₀⟩
      rw [Finsupp.mem_support_iff] at hP ⊢
      rwa [← DivisorWithCoeffs.coeff_apply, ← hco, DivisorWithCoeffs.coeff_apply]
  -- the snc divisor `Ex(h) ∪ h⁻¹(w⁻¹ W) ∪ h⁻¹(Supp B₀ ∪ ⋃ E')`
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  have hsm : IsSmoothScheme (h ≫ w ≫ sX) := hgs ▸ hgres.isSmoothScheme
  haveI : LocallyOfFinitePresentation (h ≫ w ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := h ≫ w ≫ sX)).mpr
      (hgs ▸ inferInstance)
  obtain ⟨sbig, hsbig, hsncbig⟩ := exists_finset_of_isSNCSubset hsm hsncI
  have hIsupp : ((I.comap h).support : Set Y) =
      h ⁻¹' (Zw : Set W₀) ∪ h ⁻¹' (S₀ : Set W₀) := by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI,
      Scheme.IdealSheafData.support_mul, Closeds.coe_sup,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Set.preimage_union]
  have hmembig : ∀ y : Y, y ∈ (exceptionalSet h : Set Y) ∨ h y ∈ (Zw : Set W₀) ∨
      h y ∈ (S₀ : Set W₀) → ∃ E ∈ sbig, y ∈ (E.support : Set Y) := by
    intro y hy
    have : y ∈ ⋃ E ∈ sbig, (E.support : Set Y) := by
      rw [hsbig]
      change y ∈ (exceptionalSet h : Set Y) ∪ ((I.comap h).support : Set Y)
      rw [hIsupp]
      rcases hy with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3)
    exact Set.mem_iUnion₂.1 this |>.imp fun E hE => ⟨hE.1, hE.2⟩
  have hBVbig : ∀ P ∈ BV.support, P ∈ sbig := by
    intro P hP
    obtain ⟨E₁, hE₁, hηE⟩ : ∃ E ∈ sbig, P.genericPoint ∈ (E.support : Set Y) := by
      refine hmembig _ ?_
      rcases hsupp P hP with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE] at hE₁
  -- `h⁻¹(w⁻¹ W)` is a divisor
  haveI : LocallyOfFiniteType (h ≫ w ≫ sX) := hgs ▸ inferInstance
  have hpure : IsPureCodimOne ((Scheme.IdealSheafData.vanishingIdeal Zw).comap h).support := by
    have hc := hcart
    rw [hI, Stacks.IdealSheaf.comap_mul] at hc
    exact isPureCodimOne_support_of_isEffectiveCartierDivisor (h ≫ w ≫ sX)
      (isEffectiveCartierDivisor_left_of_mul _ _ hc)
  have hZwsupp : (((Scheme.IdealSheafData.vanishingIdeal Zw).comap h).support : Set Y) =
      h ⁻¹' (Zw : Set W₀) := by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hWdiv : ∀ x : Y, g x ∈ (W : Set X) →
      ∃ E ∈ sbig, x ∈ (E.support : Set Y) ∧ g.base '' E.support ⊆ W := by
    intro x hx
    have hxC : x ∈ (((Scheme.IdealSheafData.vanishingIdeal Zw).comap h).support : Set Y) := by
      rwa [hZwsupp]
    have hCS : ((Scheme.IdealSheafData.vanishingIdeal Zw).comap h).support ≤
        exceptionalSet h ⊔ (I.comap h).support := by
      intro y hy
      right
      change y ∈ ((I.comap h).support : Set Y)
      rw [hIsupp]
      left
      change y ∈ (((Scheme.IdealSheafData.vanishingIdeal Zw).comap h).support : Set Y) at hy
      rwa [hZwsupp] at hy
    obtain ⟨E, hE, hxE, hEC⟩ := exists_mem_support_subset_of_isPureCodimOne hsbig hpure hCS x hxC
    refine ⟨E, hE, hxE, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hEC hy
    rwa [hZwsupp] at this
  refine ⟨Y, inferInstance, inferInstance, inferInstance, g ≫ sX, hprojY, g, inferInstance, KV,
    BV, Finset.univ.image Tj, hgres.isSmoothScheme, rfl, hgproj, inferInstance, hgb, hKV,
    ⟨hY, hgb, hBV⟩, ?_, ?_,
    ?_, fun m hm D hD hDC => (hpull.1 m hm D hD hDC).imp fun DY h => ⟨h.1, h.2.2⟩, ?_, ?_, hηW,
    sbig, hgs ▸ hsncbig, hBVbig, hWdiv⟩
  · rw [hgs]
    refine hsncbig.of_support_subset fun P hP => ?_
    exact mem_support_sum_single (hBVbig P hP)
  · exact fun P => (hcoef P).1
  · intro P hP
    by_contra hPe
    exact absurd hP (not_lt.mpr ((hcoef P).2 hPe))
  · intro P hP
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨?_, ?_⟩
    · have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw (hTj j) (hBV (Tj j)) (hEd j)
      rw [← DivisorWithCoeffs.coeff_apply]
      linarith
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton, ← hZ j, hWS']
      exact Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds X => (Z : Set X)) j.2
  · intro x hx
    rw [hWS'] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨Z, hZS', hxZ⟩ := hx
    have hxZ' : x ∈ closure {g (Tj ⟨Z, hZS'⟩).genericPoint} := by
      rwa [← hZ ⟨Z, hZS'⟩]
    have hcl : IsClosed (g.base '' (Tj ⟨Z, hZS'⟩).support) :=
      g.isClosedMap _ (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
    have hmem : g (Tj ⟨Z, hZS'⟩).genericPoint ∈ g.base '' (Tj ⟨Z, hZS'⟩).support := by
      refine ⟨_, ?_, rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have := closure_minimal (Set.singleton_subset_iff.mpr hmem) hcl hxZ'
    simp only [Set.mem_iUnion]
    exact ⟨Tj ⟨Z, hZS'⟩, Finset.mem_image.mpr ⟨⟨Z, hZS'⟩, Finset.mem_univ _, rfl⟩, this⟩

/-- On a scheme of dimension at most one every point has coheight at most one. -/
private theorem coheight_le_one_of_topologicalKrullDim_le_one {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (x : X) : Order.coheight x ≤ 1 := by
  have h : (Order.coheight x : WithBot ℕ∞) ≤ 1 := by
    refine le_trans ?_ hd
    rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact Order.coheight_le_krullDim _
  exact_mod_cast h

/-- On a normal variety of dimension at most one no divisor over `X` is exceptional: its centre
has codimension at most one. -/
private theorem not_isExceptional_of_topologicalKrullDim_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hd : topologicalKrullDim X ≤ 1) (D : DivisorOver ℂ sX) : ¬ D.IsExceptional := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  intro hD
  unfold DivisorOver.IsExceptional at hD
  rw [MMP.Positivity.isExceptional_toRationalMap_iff] at hD
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center] at hD
  exact absurd (hD.trans (coheight_le_one_of_topologicalKrullDim_le_one hd _)) (by decide)

/-- On a normal integral scheme of dimension at most one every local ring is a field or a discrete
valuation ring, hence factorial, so every divisor is Cartier. -/
private theorem isCartier_of_topologicalKrullDim_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hd : topologicalKrullDim X ≤ 1) (D : Divisor X) :
    D.IsCartier := by
  have hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := by
    intro x
    have hco' := coheight_le_one_of_topologicalKrullDim_le_one hd x
    rcases (show Order.coheight x = 0 ∨ Order.coheight x = 1 by
      rcases eq_or_ne (Order.coheight x) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (le_antisymm hco' (ENat.one_le_iff_ne_zero.mpr h))) with h0 | h1
    · -- the generic point: the stalk is the function field
      have hmax : IsMax x := Order.coheight_eq_zero.mp h0
      have hx : x = genericPoint X := by
        have hle : x ≤ genericPoint X :=
          Scheme.le_iff_specializes.mpr ((genericPoint_spec X).specializes (Set.mem_univ x))
        exact ((Scheme.le_iff_specializes.mp (hmax hle)).antisymm
          (Scheme.le_iff_specializes.mp hle)).eq
      subst hx
      change UniqueFactorizationMonoid X.functionField
      infer_instance
    · let P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1
      have hP : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1
      have := P.isDiscreteValuationRing_localRing
      rw [← hP]
      change UniqueFactorizationMonoid P.localRing
      infer_instance
  induction D using Finsupp.induction_linear with
  | zero => exact Divisor.isCartier_zero
  | add D₁ D₂ h₁ h₂ => exact h₁.add h₂
  | single P c =>
    rw [← Finsupp.smul_single_one]
    exact (MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid hUFD P).zsmul c

/-- In dimension at least two the boundary of an lc pair has coefficients at most one: a
coefficient above one makes the total discrepancy `< -1`, hence `discrep = -∞` (Kollár–Mori
2.31(1)). -/
private theorem coeff_le_one_of_isLcPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) (E : MMP.Mori.PrimeDivisor X) :
    Δ.coeff E ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hX := h.1.1
  have htot := totalDiscrep_le_neg_coeff hX (MMP.Positivity.IsPair.exists_isDiscrepancy
    h.1.isPair h.1.2.1 (DivisorOver.ofPrimeDivisor ℂ hX E))
  have hc : (((-Δ.coeff E : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -Δ.coeff E < -1))
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd
    (htot.trans_lt (hc.trans_eq (by norm_num)))] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

end Crepant

/-- **`f_* 𝒪_S = ι_* 𝒪_W` from a factorization.** If `f = φ ≫ ι` and the comorphism of `φ` is
bijective on every open, then `ι_* 𝒪_W ≅ f_* 𝒪_S` under the comorphisms of `ι` and `f`. -/
private theorem exists_iso_unitToPushforwardObjUnit {S X W' : Scheme.{0}} (φ : S ⟶ W')
    (ιW : W' ⟶ X) (f : S ⟶ X) (h : φ ≫ ιW = f) (hiso : ∀ U, IsIso (φ.app U)) :
    ∃ e : (Scheme.Modules.pushforward ιW).obj (SheafOfModules.unit W'.ringCatSheaf) ≅
        (Scheme.Modules.pushforward f).obj (SheafOfModules.unit S.ringCatSheaf),
      SheafOfModules.unitToPushforwardObjUnit ιW.toRingCatSheafHom ≫ e.hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  haveI : IsIso (unitHom φ) := (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := unitHom φ)).mpr
    fun U => (isIso_app_unitHom_iff φ U).2 (hiso U)
  refine ⟨(Scheme.Modules.pushforward ιW).mapIso (asIso (unitHom φ)) ≪≫
    ((Scheme.Modules.pushforwardComp φ ιW).app _).symm ≪≫
    (Scheme.Modules.pushforwardCongr h).app _, ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  have h1 := Scheme.Hom.congr_app h.symm U
  rw [Scheme.Hom.comp_app] at h1
  exact (ConcreteCategory.congr_hom h1 x).symm

section Main

/-- **Surjectivity of `𝒪_X ⟶ g_* 𝒪_T`, boundary coefficients `≤ 1`.** In the setting of the main
theorem, with `B ≤ 1`, there are a smooth projective log resolution `g : V ⟶ X` and a reduced snc
divisor `T` on `V` with `g(T) = W` such that the comorphism `𝒪_X ⟶ (T ⟶ X)_* 𝒪_T` is an
epimorphism. -/
private theorem exists_epi_unitHom_of_coeff_le_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sV) (g : V ⟶ X)
      (T : Finset (MMP.Mori.PrimeDivisor V)),
      MMP.Mori.IsSmoothScheme sV ∧ g ≫ sX = sV ∧ IsProjective g ∧ IsBirationalMorphism g ∧
      DivisorWithCoeffs.IsSNC sV (∑ P ∈ T, Finsupp.single P (1 : ℤ)) ∧
      g.base '' (⋃ P ∈ T, (P.support : Set V)) = W ∧
      Epi (unitHom ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι ≫ g)) ∧
      ∃ (KV : Divisor V) (BV : QDivisor V) (sbig : Finset (MMP.Mori.PrimeDivisor V)),
        KV.IsCanonicalDivisor sV n ∧
        (∃ (hV : IsNormalVariety ℂ (g ≫ sX)) (hg : IsBirationalMorphism g),
          IsCrepantBoundary sX n K B g hV hg BV) ∧
        (∀ P, BV.coeff P ≤ 1) ∧ (∀ P ∈ T, BV.coeff P = 1) ∧ BV.support ⊆ sbig ∧
        DivisorWithCoeffs.IsSNC sV (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)) := by
  classical
  obtain ⟨V, _, _, _, sV, _, g, _, KV, BV, T₀, hsm, hgs, hgp, hgpr, hgb, hKV, hcb, hBVs, hBV1,
    hBVexc, hcrep, hT₀, hWT₀, hηW, sbig, hsncbig, hBVbig, hWdiv⟩ :=
    exists_crepantModel_snc_preimage sX hproj hB hBeff hB1 W S hS hW
  have hVar : MMP.Mori.IsVariety ℂ (g ≫ sX) := hgs ▸ ‹MMP.Mori.IsProjectiveVariety ℂ sV›.toIsVariety
  have hXvar : MMP.Mori.IsVariety ℂ sX := hB.1.1.1
  haveI : CompactSpace V :=
    haveI := hVar.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).2 ⟨hB.1.1.1, hproj⟩
  -- `T`: the coefficient-one components of `B_V` mapping into `W`
  set T : Finset (MMP.Mori.PrimeDivisor V) :=
    BV.support.filter (fun P => BV P = 1 ∧ g.base '' P.support ⊆ W)
  have hT : ∀ P ∈ T, BV P = 1 ∧ g.base '' P.support ⊆ W := fun P hP => (Finset.mem_filter.1 hP).2
  have hT₀T : T₀ ⊆ T := fun P hP => Finset.mem_filter.2
    ⟨by rw [Finsupp.mem_support_iff, (hT₀ P hP).1]; norm_num, hT₀ P hP⟩
  have hWT : (W : Set X) ⊆ ⋃ P ∈ T, g.base '' P.support :=
    hWT₀.trans (Set.biUnion_subset_biUnion_left hT₀T)
  -- `A = ⌈-(B_V^{<1})⌉` and the reduced divisor `T`
  let A : Divisor V := Finsupp.ofSupportFinite (fun P => if BV P < 1 then -⌊BV P⌋ else 0)
    (BV.support.finite_toSet.subset fun P hP => by
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      simp [h] at hP)
  have hAco : ∀ P, A P = if BV P < 1 then -⌊BV P⌋ else 0 := fun P => rfl
  let TD : Divisor V := ∑ P ∈ T, Finsupp.single P 1
  have hTco : ∀ P, TD P = if P ∈ T then 1 else 0 := sum_single_one_apply T
  have hA0 : 0 ≤ A := by
    rw [Finsupp.le_def]
    intro P
    rw [hAco]; split_ifs with h
    · have : ⌊BV P⌋ ≤ 0 := Int.floor_le_iff.mpr (by simpa using h)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    · exact le_rfl
  have hAexc : ∀ P, A.coeff P ≠ 0 → RationalMap.IsExceptional g.toRationalMap P := by
    intro P hP
    rw [DivisorWithCoeffs.coeff_apply, hAco] at hP
    split_ifs at hP with h
    · apply hBVexc
      have : ⌊BV P⌋ ≤ 0 := Int.floor_le_iff.mpr (by simpa using h)
      have h2 : ⌊BV P⌋ < 0 := by omega
      exact Int.floor_lt.mp h2 |>.trans_eq (by simp)
    · exact absurd rfl hP
  have hAT : ∀ P ∈ T, A P = 0 := by
    intro P hP
    rw [hAco, if_neg (by rw [(hT P hP).1]; exact lt_irrefl 1)]
  have hBV1T : ∀ P, BV P < 1 → P ∉ T := fun P h hP => by
    rw [(hT P hP).1] at h; exact lt_irrefl _ h
  have hAc : A.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  -- `C = A - T + B_V`
  let C : QDivisor V := Divisor.toQDivisor (A - TD) + BV
  have hCco : ∀ P, C P = ((A P - TD P : ℤ) : ℚ) + BV P := fun P => by
    simp [C, ← DivisorWithCoeffs.coeff_apply]
  have hCval : ∀ P, (BV P < 1 → C P = Int.fract (BV P)) ∧ (¬ BV P < 1 → BV P = 1 ∧
      C P = if P ∈ T then 0 else 1) := by
    intro P
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hCco, hAco, if_pos h, hTco, if_neg (hBV1T P h), Int.fract]
      push_cast; ring
    · have h1 : BV P = 1 := le_antisymm (hBV1 P) (not_lt.mp h)
      refine ⟨h1, ?_⟩
      rw [hCco, hAco, if_neg h, hTco, h1]
      split_ifs <;> norm_num
  have hCsnc : C.IsSNC sV := by
    refine hBVs.of_support_subset fun P hP => ?_
    rw [Finsupp.mem_support_iff] at hP ⊢
    intro h0
    apply hP
    rw [(hCval P).1 (by rw [h0]; exact zero_lt_one), h0, Int.fract_zero]
  have hC0 : ∀ E, 0 ≤ C E := by
    intro P
    by_cases h : BV P < 1
    · rw [(hCval P).1 h]; exact Int.fract_nonneg _
    · rw [((hCval P).2 h).2]; split_ifs <;> norm_num
  have hC1 : ∀ E, C E ≤ 1 := by
    intro P
    by_cases h : BV P < 1
    · rw [(hCval P).1 h]; exact (Int.fract_lt_one _).le
    · rw [((hCval P).2 h).2]; split_ifs <;> norm_num
  -- the components of `⌊C⌋`: coefficient one in `B_V`, not mapping into `W`
  have hfl : ∀ P ∈ C.roundDown.support, BV P = 1 ∧ P ∉ T := by
    intro P hP
    rw [Finsupp.mem_support_iff] at hP
    have hfl : ⌊C P⌋ ≠ 0 := by
      have h := DivisorWithCoeffs.coeff_roundDown C P
      simp only [DivisorWithCoeffs.coeff_apply] at h
      rwa [← h]
    have hC : C P = 1 := by
      have h2 : (1 : ℚ) ≤ C P := by
        by_contra hlt
        exact hfl (Int.floor_eq_zero_iff.2 ⟨hC0 P, lt_of_not_ge hlt⟩)
      exact le_antisymm (hC1 P) h2
    by_cases h : BV P < 1
    · rw [(hCval P).1 h] at hC
      exact absurd hC (ne_of_lt (Int.fract_lt_one _))
    · obtain ⟨h1, h2⟩ := (hCval P).2 h
      refine ⟨h1, fun hPT => ?_⟩
      rw [h2, if_pos hPT] at hC
      exact zero_ne_one hC
  have hDs : ∀ P ∈ C.roundDown.support, P ∈ sbig := by
    intro P hP
    refine hBVbig P ?_
    rw [Finsupp.mem_support_iff, (hfl P hP).1]
    norm_num
  have hDW : ∀ P ∈ C.roundDown.support, ¬ g.base '' P.support ⊆ W := by
    intro P hP hPW
    obtain ⟨h1, h2⟩ := hfl P hP
    apply h2
    refine Finset.mem_filter.2 ⟨?_, h1, hPW⟩
    rw [Finsupp.mem_support_iff, h1]
    norm_num
  -- the adjoint gap `A - T - (K_V + C) = -(K_V + B_V) = -g^* (K + B)` is semiample over `X`
  obtain ⟨m, hm, D, hD, hDc⟩ := hB.1.2.2.exists_pos
  obtain ⟨DV, hDVq, hDsupp, hDVpb⟩ := hcrep m hm D hD hDc
  have hsa : MMP.Fourfold.QDivisor.IsRelativelySemiample g
      (Divisor.toQDivisor (A - TD) - (Divisor.toQDivisor KV + C)) := by
    have hrel : ((m * 1 : ℕ) : ℤ) • D = ((m * 1 : ℕ) : ℤ) • D +
        principalDivisor (1 : (RationalFunctions X)ˣ) := by
      rw [MMP.Mori.principalDivisor_one, add_zero]
    have h := isRelativelySemiample_neg_smul_pullback sV hsm (𝟙 X) g hm one_pos hm hDc hDVpb hDc
      hDc (isPullback_id D) 1 hrel
    rw [Category.comp_id] at h
    convert h using 1
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [hDVq, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      show (1 / (m : ℚ)) * ((m : ℤ) : ℚ) = 1 by push_cast; field_simp, one_smul]
    change Divisor.toQDivisor (A - TD) - (Divisor.toQDivisor KV +
      (Divisor.toQDivisor (A - TD) + BV)) = -(Divisor.toQDivisor KV + BV)
    abel
  -- no associated point of `R¹g_* 𝒪_V(A - T)` lies in `W`
  have hgW : ∃ x : V, g x ∉ (W : Set X) :=
    ⟨genericPoint V, by rwa [map_genericPoint_of_isDominant g]⟩
  have hN : ∀ x, Stacks.Divisors.IsAssociatedPoint
      (((Scheme.Modules.pushforward g).rightDerived 1).obj (A - TD).divisorialSheaf) x →
        x ∉ (W : Set X) := by
    intro x hx hxW
    obtain ⟨S', hS', hcl⟩ :=
      exists_isSNCStratum_closure_eq_image_of_isAssociatedPoint_rightDerived_pushforward sX sV
        hsm g hgs hgp KV hKV C hCsnc hC0 hC1 (A - TD)
        (MMP.Fourfold.isCartier_of_isSmoothScheme hsm _) hsa 1 x hx
    have hsub : g.base '' S' ⊆ W := by
      rw [← hcl]
      exact closure_minimal (Set.singleton_subset_iff.2 hxW) W.isClosed
    exact not_image_subset_of_isSNCStratum
      ‹MMP.Mori.IsProjectiveVariety ℂ sV›.toIsVariety hsm g W sbig
      (hgs ▸ hsncbig) hWdiv hgW C.roundDown hDs hDW S' hS' hsub
  haveI : IsProper g := hgpr
  refine ⟨V, inferInstance, inferInstance, inferInstance, sV, inferInstance, g, T, hsm, hgs, hgp,
    hgb, ?_, ?_, epi_unitHom_comp_of_isAssociatedPoint sX hXvar g hVar hgb A hAc hA0 hAexc T hAT
      W (fun P hP => (hT P hP).2) hN, KV, BV, sbig, hKV, hcb, hBV1, fun P hP => (hT P hP).1,
      hBVbig, hsncbig⟩
  · refine hBVs.of_support_subset fun P hP => ?_
    have hPT : P ∈ T := by
      by_contra hPT
      rw [Finsupp.mem_support_iff] at hP
      apply hP
      change TD P = 0
      rw [hTco, if_neg hPT]
    rw [Finsupp.mem_support_iff, (hT P hPT).1]
    norm_num
  · rw [Set.image_iUnion₂]
    refine le_antisymm (Set.iUnion₂_subset fun P hP => (hT P hP).2) hWT

/-- From the surjectivity of `𝒪_X ⟶ (T ⟶ X)_* 𝒪_T`: the morphism `T ⟶ X` factors through the
reduced subscheme `W` on the closed set `g(T)`, and the comorphism of `T ⟶ W` is bijective on every
open of `W`. -/
private theorem exists_hom_isIso_app_of_epi {X V : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] (g : V ⟶ X) [QuasiCompact g]
    (T : Finset (MMP.Mori.PrimeDivisor V)) (W : Closeds X)
    (hTW : g.base '' (⋃ P ∈ T, (P.support : Set V)) = W)
    (h : Epi (unitHom ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι ≫ g))) :
    ∃ φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal W).subscheme,
      φ ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
        (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι ≫ g ∧
      ∀ U, IsIso (φ.app U) := by
  classical
  set TD : Divisor V := ∑ P ∈ T, Finsupp.single P (1 : ℤ) with hTD
  set ι := TD.suppIdeal.subschemeι with hι
  set f := ι ≫ g with hf
  haveI : IsReduced TD.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hsupp : (TD.supp : Set V) = ⋃ P ∈ T, (P.support : Set V) := by
    ext y
    rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
    simp only [Set.mem_iUnion, exists_prop]
    refine exists_congr fun Q => and_congr_left fun _ => ?_
    rw [DivisorWithCoeffs.coeff_apply, hTD, sum_single_one_apply]
    split_ifs with hQ <;> simp [hQ]
  have hrange : Set.range f = (W : Set X) := by
    rw [hf, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hι,
      Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal, hsupp, hTW]
  have hiso := isIso_toImage_app_of_epi f h
  -- the kernel of `T ⟶ X` is the ideal of `W`
  have hle₁ : Scheme.IdealSheafData.vanishingIdeal W ≤ f.ker := by
    rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U a ha
    rw [RingHom.mem_ker]
    change ι.app (g ⁻¹ᵁ U.1) (g.app U.1 a) = 0
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.Hom.preimage_basicOpen, ← Scheme.Hom.preimage_basicOpen]
    ext y
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    have hW : f y ∈ (W : Set X) := hrange ▸ ⟨y, rfl⟩
    have hb : g (ι y) ∈ X.basicOpen a := hy
    exact (mem_vanishingIdeal_ideal_iff W U a).1 ha _ hW (X.basicOpen_le a hb) hb
  have hle₂ : f.ker ≤ Scheme.IdealSheafData.vanishingIdeal W := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro x hx
    have hx' : x ∈ (W : Set X) := hx
    rw [← hrange] at hx'
    exact f.range_subset_ker_support hx'
  haveI : IsIso (Scheme.IdealSheafData.inclusion hle₁) :=
    ⟨⟨Scheme.IdealSheafData.inclusion hle₂, by
      rw [Scheme.IdealSheafData.inclusion_comp]; exact Scheme.IdealSheafData.inclusion_id _, by
      rw [Scheme.IdealSheafData.inclusion_comp]; exact Scheme.IdealSheafData.inclusion_id _⟩⟩
  refine ⟨f.toImage ≫ Scheme.IdealSheafData.inclusion hle₁, ?_, fun U => ?_⟩
  · rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    exact f.toImage_imageι
  · rw [Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (hiso (Scheme.IdealSheafData.inclusion hle₁ ⁻¹ᵁ U))

end Main

section Reduction

/-- **The coefficients-at-most-one reduction.** An lc pair has a boundary coefficient `> 1` only
on a curve, where lowering such coefficients to `≤ 1` keeps the pair lc with the same lc centres;
so the statement for boundaries with coefficients `≤ 1` gives it in general. -/
private theorem exists_epi_unitHom
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sV) (g : V ⟶ X)
      (T : Finset (MMP.Mori.PrimeDivisor V)),
      MMP.Mori.IsSmoothScheme sV ∧ g ≫ sX = sV ∧ IsProjective g ∧ IsBirationalMorphism g ∧
      DivisorWithCoeffs.IsSNC sV (∑ P ∈ T, Finsupp.single P (1 : ℤ)) ∧
      g.base '' (⋃ P ∈ T, (P.support : Set V)) = W ∧
      Epi (unitHom ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor V).suppIdeal.subschemeι ≫ g)) := by
  by_cases hB1 : ∀ P, B.coeff P ≤ 1
  · obtain ⟨V, _, _, _, sV, hV, g, T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, -⟩ :=
      exists_epi_unitHom_of_coeff_le_one sX hproj hB hBeff hB1 W S hS hW
    exact ⟨V, inferInstance, inferInstance, inferInstance, sV, hV, g, T, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  classical
  have hX : IsNormalVariety ℂ sX := hB.1.1
  have hPw : IsPairWith sX n K B := hB.1
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj
  -- an lc pair has a coefficient above one only in dimension at most one
  have hn1 : n ≤ 1 := by
    by_contra h
    exact hB1 fun P => coeff_le_one_of_isLcPair hB (by omega) P
  have hd : topologicalKrullDim X ≤ 1 := by
    rw [hB.1.2.1.topologicalKrullDim_eq]; exact_mod_cast hn1
  have hnoexc := not_isExceptional_of_topologicalKrullDim_le_one hX hd
  have hcart := isCartier_of_topologicalKrullDim_le_one hd
  -- lower the coefficients above one: `R = ∑ (⌈b⌉ - 1) P` over the points with `b > 1`
  let R : Divisor X := Finsupp.ofSupportFinite (fun P => if 1 < B P then ⌈B P⌉ - 1 else 0)
    (B.support.finite_toSet.subset fun P hP => by
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      simp [h] at hP)
  have hRco : ∀ P, R P = if 1 < B P then ⌈B P⌉ - 1 else 0 := fun P => rfl
  have hR0 : 0 ≤ R := by
    rw [Finsupp.le_def]
    intro P
    rw [hRco]; split_ifs with h
    · have : (1 : ℤ) < ⌈B P⌉ := Int.lt_ceil.mpr (by exact_mod_cast h)
      simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
    · exact le_rfl
  set B'' : QDivisor X := B - Divisor.toQDivisor R with hB''
  have hB''co : ∀ P, B'' P = B P - R P := fun P => by simp [B'', ← DivisorWithCoeffs.coeff_apply]
  have hB''le : ∀ P, B''.coeff P ≤ 1 := by
    intro P
    rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco]
    split_ifs with h
    · push_cast
      linarith [Int.le_ceil (B P)]
    · simp only [Int.cast_zero, sub_zero]; exact not_lt.mp h
  have hB''eff : B''.IsEffective := by
    intro P
    rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco]
    split_ifs with h
    · push_cast
      linarith [Int.ceil_lt_add_one (B P)]
    · simp only [Int.cast_zero, sub_zero]; exact hBeff P
  -- `(X, B'')` is an lc pair with the same lc centres in `S`
  have hB'' : IsLcPair sX n K B'' := by
    refine ⟨⟨hX, hB.1.2.1, ?_⟩, ?_⟩
    · have := hB.1.2.2.add (QDivisor.isQCartier_toQDivisor (hcart (-R)))
      convert this using 1
      simp [B'', sub_eq_add_neg, add_assoc]
    · rw [discrep_eq_top fun D a hD _ => hnoexc D hD]
      exact le_top
  have hcentre : ∀ E : DivisorOver ℂ sX, IsDiscrepancy sX n K B E (-1) →
      ∃ Γ : MMP.Mori.PrimeDivisor X, (E.center : Set X) = Γ.support ∧ B.coeff Γ = 1 ∧
        IsDiscrepancy sX n K B'' E (-1) := by
    intro E hE
    obtain ⟨Γ, hΓc, hΓd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw E (hnoexc E)
    have hBΓ : B.coeff Γ = 1 := neg_injective (hΓd.eq hE)
    obtain ⟨Γ', hΓ'c, hΓ'd⟩ :=
      DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hB''.1 E (hnoexc E)
    have hΓΓ' : Γ' = Γ := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support (by
      rw [← hΓ'c, hΓc]; exact MMP.Flips.primeDivisor_genericPoint_mem_support Γ)
    rw [hΓΓ'] at hΓ'd
    have hB''Γ : B''.coeff Γ = 1 := by
      rw [DivisorWithCoeffs.coeff_apply, hB''co, hRco, ← DivisorWithCoeffs.coeff_apply, hBΓ,
        if_neg (lt_irrefl 1)]
      simp
    rw [hB''Γ] at hΓ'd
    exact ⟨Γ, hΓc, hBΓ, hΓ'd⟩
  have hS'' : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B'' E (-1) :=
    fun Z hZ => by
      obtain ⟨E, hEc, hEd⟩ := hS Z hZ
      obtain ⟨-, -, -, h⟩ := hcentre E hEd
      exact ⟨E, hEc, h⟩
  obtain ⟨V, _, _, _, sV, hV, g, T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, -⟩ :=
    exists_epi_unitHom_of_coeff_le_one sX hproj hB'' hB''eff hB''le W S hS'' hW
  exact ⟨V, inferInstance, inferInstance, inferInstance, sV, hV, g, T, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩

end Reduction

end MMP.Mori.LcCentrePushforward

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

/-- **The direct image of the structure sheaf of the floor over a union of lc centres.** Let
`(X, B)` be an lc pair (with canonical divisor `K` of dimension `n` and effective `ℚ`-boundary
`B`) on a normal projective variety over `ℂ`, and let `W ⊆ X` be a union of lc centres of
`(X, B)`, with its reduced subscheme structure `ι_W`. There are a projective birational morphism
`g : R ⟶ X` from a smooth projective variety and a reduced snc divisor `T = ∑_{P ∈ T} P` on `R`,
with reduced subscheme `ι_T`, such that `g(T) = W` and `g_* 𝒪_T = 𝒪_W` canonically: `ι_T ≫ g`
factors as `φ ≫ ι_W` with the comorphism of `φ` bijective on every open of `W`, and the
comorphism `𝒪_X ⟶ g_* 𝒪_T` of `T ⟶ X` is `𝒪_X ⟶ ι_{W*} 𝒪_W` followed by an isomorphism
`ι_{W*} 𝒪_W ≅ g_* 𝒪_T`. -/
public theorem exists_isIso_app_comp_subschemeι_vanishingIdeal_of_isLcPair
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (R : Scheme.{0}) (_ : IsIntegral R) (_ : IsLocallyNoetherian R) (_ : IsNormal R)
      (sR : R ⟶ Spec (.of ℂ)) (_ : MMP.Mori.IsProjectiveVariety ℂ sR) (g : R ⟶ X)
      (T : Finset (MMP.Mori.PrimeDivisor R))
      (φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal W).subscheme),
      MMP.Mori.IsSmoothScheme sR ∧ g ≫ sX = sR ∧ IsProjective g ∧ IsBirationalMorphism g ∧
      DivisorWithCoeffs.IsSNC sR (∑ P ∈ T, Finsupp.single P (1 : ℤ)) ∧
      g.base '' (⋃ P ∈ T, (P.support : Set R)) = W ∧
      φ ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
        (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g ∧
      (∀ U, IsIso (φ.app U)) ∧
      ∃ e : (Scheme.Modules.pushforward (Scheme.IdealSheafData.vanishingIdeal W).subschemeι).obj
            (SheafOfModules.unit (Scheme.IdealSheafData.vanishingIdeal W).subscheme.ringCatSheaf) ≅
          (Scheme.Modules.pushforward
            ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g)).obj
            (SheafOfModules.unit
              (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme.ringCatSheaf),
        SheafOfModules.unitToPushforwardObjUnit
            (Scheme.IdealSheafData.vanishingIdeal W).subschemeι.toRingCatSheafHom ≫ e.hom =
          SheafOfModules.unitToPushforwardObjUnit
            ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫
              g).toRingCatSheafHom := by
  obtain ⟨R, _, _, _, sR, hR, g, T, hsm, hgs, hgp, hgb, hsnc, hTW, hepi⟩ :=
    LcCentrePushforward.exists_epi_unitHom sX hproj hB hBeff W S hS hW
  haveI : IsProper g := hgp.isProper
  obtain ⟨φ, hφ, hiso⟩ := LcCentrePushforward.exists_hom_isIso_app_of_epi g T W hTW hepi
  obtain ⟨e, he⟩ := LcCentrePushforward.exists_iso_unitToPushforwardObjUnit φ
    (Scheme.IdealSheafData.vanishingIdeal W).subschemeι _ hφ hiso
  exact ⟨R, inferInstance, inferInstance, inferInstance, sR, hR, g, T, φ, hsm, hgs, hgp, hgb,
    hsnc, hTW, hφ, hiso, e, he⟩

/-- **`g_* 𝒪_T = 𝒪_W` on a crepant model, boundary coefficients `≤ 1`.** In the setting of
`exists_isIso_app_comp_subschemeι_vanishingIdeal_of_isLcPair`, with `B ≤ 1`, the model
`g : R ⟶ X` can be taken crepant: there are a canonical divisor `K_R` and the crepant boundary
`B_R` of `(X, B)` on `R`, with coefficients `≤ 1` and equal to one along `T`, whose support lies
in the members of an snc divisor `∑_{E ∈ sbig} E`. -/
public theorem exists_isIso_app_comp_subschemeι_vanishingIdeal_and_isCrepantBoundary_of_coeff_le_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) (hB1 : ∀ P, B.coeff P ≤ 1)
    (W : Closeds X) (S : Set (IrreducibleCloseds X))
    (hS : ∀ Z ∈ S, ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1))
    (hW : (W : Set X) = ⋃ Z ∈ S, (Z : Set X)) :
    ∃ (R : Scheme.{0}) (_ : IsIntegral R) (_ : IsLocallyNoetherian R) (_ : IsNormal R)
      (g : R ⟶ X) (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
      (T : Finset (MMP.Mori.PrimeDivisor R))
      (φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme ⟶
        (Scheme.IdealSheafData.vanishingIdeal W).subscheme),
      MMP.Mori.IsSmoothScheme (g ≫ sX) ∧ MMP.Mori.IsProjectiveVariety ℂ (g ≫ sX) ∧
      IsProjective g ∧
      g.base '' (⋃ P ∈ T, (P.support : Set R)) = W ∧
      φ ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
        (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g ∧
      (∀ U, IsIso (φ.app U)) ∧
      ∃ (KR : Divisor R) (BR : QDivisor R) (sbig : Finset (MMP.Mori.PrimeDivisor R)),
        KR.IsCanonicalDivisor (g ≫ sX) n ∧ IsCrepantBoundary sX n K B g hR hgb BR ∧
        (∀ P, BR.coeff P ≤ 1) ∧ (∀ P ∈ T, BR.coeff P = 1) ∧ BR.support ⊆ sbig ∧
        DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)) := by
  obtain ⟨R, _, _, _, sR, hR, g, T, hsm, rfl, hgp, -, -, hTW, hepi, KR, BR, sbig, hKR,
    ⟨hRn, hgb, hcb⟩, hBR1, hBRT, hBRs, hsnc⟩ :=
    LcCentrePushforward.exists_epi_unitHom_of_coeff_le_one sX hproj hB hBeff hB1 W S hS hW
  haveI : IsProper g := hgp.isProper
  obtain ⟨φ, hφ, hiso⟩ := LcCentrePushforward.exists_hom_isIso_app_of_epi g T W hTW hepi
  exact ⟨R, inferInstance, inferInstance, inferInstance, g, hRn, hgb, T, φ, hsm, hR, hgp, hTW, hφ,
    hiso, KR, BR, sbig, hKR, hcb, hBR1, hBRT, hBRs, hsnc⟩

end MMP.Mori
