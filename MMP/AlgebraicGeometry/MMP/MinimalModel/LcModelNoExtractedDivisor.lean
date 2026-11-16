module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.TwistTrivial
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParametersCharZero
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization

/-!
# Log canonical models of an lc pair extract no divisors

Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕`,
through the modification `φ : X ⤏ Y`. If `(X, D_X)` is itself log canonical, then no prime divisor
of `Y` is `φ⁻¹`-exceptional: every prime divisor of `Y` is the birational transform of a prime
divisor of `X`. Consequently the correction term `∑ cᵢ Fᵢ` of the `𝓕`-birational transform is
empty and `D_{𝓕,Y} = φ_* D_X`.

## Main results

* `MMP.Flips.IsLogCanonicalModelOf.not_isInverseExceptional_and_eq_transformDivisor`.
* `MMP.Flips.eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent`: a divisor linearly
  equivalent to `0` has intersection number `0` with every proper curve. Consequently
  `MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero` and
  `MMP.Flips.IsNumericallyTrivialOver.sub_of_linearlyEquivalent_zero`: relative nefness and
  numerical triviality are unchanged by subtracting such a divisor.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.24.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Flips
open scoped WithZero

universe u

namespace MMP.Flips.Fa2NoExtractedDivisors

section TwoStructures

open KaehlerDifferential

section Alg

open Topology

/-- A constructible set containing a point `x` that lies in every nonempty open set contains an
open neighbourhood of `x`. -/
private theorem exists_isOpen_subset_of_isConstructible {X : Type*} [TopologicalSpace X] {x : X}
    (hx : ∀ U : Set X, IsOpen U → U.Nonempty → x ∈ U) {s : Set X} (hs : IsConstructible s)
    (hxs : x ∈ s) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ s := by
  have key : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (U ⊆ s ∨ U ⊆ sᶜ) := by
    clear hxs
    induction hs using IsConstructible.empty_union_induction with
    | open_retrocompact V hV _ =>
      by_cases hxV : x ∈ V
      · exact ⟨V, hV, hxV, Or.inl le_rfl⟩
      · refine ⟨Set.univ, isOpen_univ, trivial, Or.inr fun y _ hy => hxV (hx V hV ⟨y, hy⟩)⟩
    | union s _ t _ hs' ht' =>
      obtain ⟨U₁, hU₁, hx₁, h₁⟩ := hs'
      obtain ⟨U₂, hU₂, hx₂, h₂⟩ := ht'
      rcases h₁ with h₁ | h₁
      · exact ⟨U₁, hU₁, hx₁, Or.inl (h₁.trans Set.subset_union_left)⟩
      rcases h₂ with h₂ | h₂
      · exact ⟨U₂, hU₂, hx₂, Or.inl (h₂.trans Set.subset_union_right)⟩
      exact ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hx₁, hx₂⟩, Or.inr fun y hy hy' =>
        hy'.elim (h₁ hy.1) (h₂ hy.2)⟩
    | compl s _ hs' =>
      obtain ⟨U, hU, hxU, h⟩ := hs'
      exact ⟨U, hU, hxU, h.symm.imp id fun h' => by rwa [compl_compl]⟩
  obtain ⟨U, hU, hxU, h⟩ := key
  exact ⟨U, hU, hxU, h.resolve_right fun h' => h' hxU hxs⟩

/-- In a finitely generated domain `B` over a field `K` of characteristic zero, an element `a`
such that `a - q` is a unit for every rational `q` is algebraic over `K`. -/
private theorem isAlgebraic_of_forall_isUnit_sub {K B : Type*} [Field K] [CharZero K] [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (a : B)
    (ha : ∀ q : ℚ, IsUnit (a - algebraMap K B (q : K))) : IsAlgebraic K a := by
  classical
  by_contra htr
  have hinj : Function.Injective (Polynomial.aeval (R := K) a) :=
    (transcendental_iff_injective).mp htr
  let φ : Polynomial K →+* B := (Polynomial.aeval (R := K) a).toRingHom
  letI : Algebra (Polynomial K) B := φ.toAlgebra
  haveI : IsScalarTower K (Polynomial K) B := IsScalarTower.of_algebraMap_eq fun c => by
    simp [φ, RingHom.algebraMap_toAlgebra]
  haveI : Algebra.FiniteType (Polynomial K) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (Polynomial K) B
  haveI : Algebra.FinitePresentation (Polynomial K) B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hfp : φ.FinitePresentation := by
    change (algebraMap (Polynomial K) B).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hc := PrimeSpectrum.isConstructible_range_comap hfp
  let x₀ : PrimeSpectrum (Polynomial K) := ⟨⊥, Ideal.isPrime_bot⟩
  have hx₀ : x₀ ∈ Set.range (PrimeSpectrum.comap φ) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  have hgen : ∀ U : Set (PrimeSpectrum (Polynomial K)), IsOpen U → U.Nonempty → x₀ ∈ U := by
    intro U hU ⟨y, hy⟩
    exact (show x₀ ⤳ y from (PrimeSpectrum.le_iff_specializes x₀ y).mp bot_le).mem_open hU hy
  obtain ⟨U, hU, hxU, hUs⟩ := exists_isOpen_subset_of_isConstructible hgen hc hx₀
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hxf (Submodule.zero_mem _)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, ¬ f.IsRoot (q : K) := by
    by_contra! h
    exact (Set.infinite_range_of_injective Rat.cast_injective :
      Set.Infinite (Set.range ((↑) : ℚ → K))) (f.roots.toFinset.finite_toSet.subset
        fun _ ⟨q, hq⟩ => hq ▸ by simpa [Polynomial.mem_roots hf0] using h q)
  let y : PrimeSpectrum (Polynomial K) :=
    ⟨Ideal.span {Polynomial.X - Polynomial.C (q : K)},
      (Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero _)).mpr
        (Polynomial.prime_X_sub_C _)⟩
  have hyf : y ∈ PrimeSpectrum.basicOpen f := by
    change f ∉ Ideal.span _
    rwa [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]
  obtain ⟨P, hP⟩ := hUs (hfU hyf)
  have hmem : Polynomial.X - Polynomial.C (q : K) ∈ Ideal.comap φ P.asIdeal := by
    rw [show Ideal.comap φ P.asIdeal = y.asIdeal from congrArg PrimeSpectrum.asIdeal hP]
    exact Ideal.subset_span rfl
  have : a - algebraMap K B (q : K) ∈ P.asIdeal := by
    simpa [φ] using hmem
  exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ this (ha q))

end Alg

section

variable {k A : Type*} [CommRing k] [CommRing A]

/-- The kernel of `Ω_{A/ℤ} → Ω_{A/k}` for the `k`-algebra structure `i`. -/
private noncomputable def kerInt (i : k →+* A) : Submodule A Ω[A⁄ℤ] :=
  letI := i.toAlgebra; LinearMap.ker (KaehlerDifferential.map ℤ k A A)

private theorem ker_map_int_le_span [Algebra k A] :
    LinearMap.ker (KaehlerDifferential.map ℤ k A A) ≤
      Submodule.span A (Set.range fun c => KaehlerDifferential.D ℤ A (algebraMap k A c)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map ℤ k A x).mp hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a w =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have hw : w ∈ Submodule.span k (Set.range (KaehlerDifferential.D ℤ k)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hw using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨c, rfl⟩ := h
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c _ _ h =>
      rw [map_smul]
      exact Submodule.smul_of_tower_mem _ c h
  | add _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

private theorem D_mem_ker_of_aeval [Algebra k A] {a : A} (P : Polynomial k)
    (h0 : Polynomial.aeval a P = 0) (hu : IsUnit (Polynomial.aeval a (Polynomial.derivative P))) :
    KaehlerDifferential.D ℤ A a ∈ LinearMap.ker (KaehlerDifferential.map ℤ k A A) := by
  rw [LinearMap.mem_ker, KaehlerDifferential.map_D]
  have h := (KaehlerDifferential.D k A).map_aeval P a
  rw [h0, map_zero] at h
  exact (hu.smul_eq_zero).mp h.symm

private theorem kerInt_le (i₁ i₂ : k →+* A)
    (h : ∀ c, ∃ P : Polynomial k, P.eval₂ i₂ (i₁ c) = 0 ∧
      IsUnit ((Polynomial.derivative P).eval₂ i₂ (i₁ c))) : kerInt i₁ ≤ kerInt i₂ := by
  letI := i₁.toAlgebra
  refine (ker_map_int_le_span (k := k) (A := A)).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨P, h0, hu⟩ := h c
  letI := i₂.toAlgebra
  exact D_mem_ker_of_aeval P h0 hu

/-- `Ω_{A/k} ≅ Ω_{A/ℤ} / ker` for the `k`-algebra structure `i`. -/
private noncomputable def omegaQuotEquiv (i : k →+* A) :
    (Ω[A⁄ℤ] ⧸ kerInt i) ≃ₗ[A] @KaehlerDifferential k A _ _ i.toAlgebra :=
  letI := i.toAlgebra
  LinearMap.quotKerEquivOfSurjective (KaehlerDifferential.map ℤ k A A)
    (KaehlerDifferential.map_surjective ℤ k A)

private theorem omegaQuotEquiv_mk (i : k →+* A) (a : A) :
    omegaQuotEquiv i (Submodule.Quotient.mk (KaehlerDifferential.D ℤ A a)) =
      @KaehlerDifferential.D k A _ _ i.toAlgebra a := by
  letI := i.toAlgebra
  exact KaehlerDifferential.map_D ℤ k A A a

/-- Two `k`-algebra structures on `A` with the same kernel `ker(Ω_{A/ℤ} → Ω_{A/k})` have
isomorphic modules of differentials. -/
private noncomputable def omegaEquiv (i₁ i₂ : k →+* A) (h : kerInt i₁ = kerInt i₂) :
    @KaehlerDifferential k A _ _ i₁.toAlgebra ≃ₗ[A] @KaehlerDifferential k A _ _ i₂.toAlgebra :=
  (omegaQuotEquiv i₁).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ h ≪≫ₗ omegaQuotEquiv i₂

private theorem omegaEquiv_D (i₁ i₂ : k →+* A) (h : kerInt i₁ = kerInt i₂) (a : A) :
    omegaEquiv i₁ i₂ h (@KaehlerDifferential.D k A _ _ i₁.toAlgebra a) =
      @KaehlerDifferential.D k A _ _ i₂.toAlgebra a := by
  have h1 : (omegaQuotEquiv i₁).symm (@KaehlerDifferential.D k A _ _ i₁.toAlgebra a) =
      Submodule.Quotient.mk (KaehlerDifferential.D ℤ A a) :=
    (LinearEquiv.symm_apply_eq _).mpr (omegaQuotEquiv_mk i₁ a).symm
  rw [omegaEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  exact omegaQuotEquiv_mk i₂ a

end

section ExtEquiv

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The isomorphism of exterior powers induced by an isomorphism of modules. -/
private noncomputable def extEquiv (n : ℕ) (e : M ≃ₗ[R] N) : ⋀[R]^n M ≃ₗ[R] ⋀[R]^n N :=
  LinearEquiv.ofLinear (exteriorPower.map n e.toLinearMap) (exteriorPower.map n e.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

private theorem extEquiv_ιMulti (n : ℕ) (e : M ≃ₗ[R] N) (m : Fin n → M) :
    extEquiv n e (exteriorPower.ιMulti R n m) = exteriorPower.ιMulti R n (fun i => e (m i)) :=
  exteriorPower.map_apply_ιMulti _ _

end ExtEquiv

private theorem span_singleton_linearEquiv_eq_top {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {x : M}
    (h : Submodule.span R {x} = ⊤) : Submodule.span R {e x} = ⊤ := by
  rw [← Set.image_singleton, Submodule.span_image_linearEquiv, h, Submodule.map_top,
    LinearEquiv.range]

section Compat

variable {k A K : Type*} [CommRing k] [CommRing A] [Field K] [Algebra A K]

private theorem topFormsMap_ιMulti_D (i : k →+* A) (j : k →+* K)
    (hs : letI := i.toAlgebra; letI := j.toAlgebra; IsScalarTower k A K) (d : ℕ) (a : Fin d → A) :
    (letI := i.toAlgebra; letI := j.toAlgebra; haveI := hs;
      MMP.Mori.topFormsMap k A K d
        (exteriorPower.ιMulti A d fun l => KaehlerDifferential.D k A (a l))) =
    (letI := j.toAlgebra;
      exteriorPower.ιMulti K d fun l => KaehlerDifferential.D k K (algebraMap A K (a l))) := by
  letI := i.toAlgebra
  letI := j.toAlgebra
  haveI := hs
  simp [MMP.Mori.topFormsMap_ιMulti, KaehlerDifferential.map_D]

private theorem extEquiv_omegaEquiv_ιMulti_D (i₁ i₂ : k →+* A) (h : kerInt i₁ = kerInt i₂) (d : ℕ)
    (a : Fin d → A) :
    extEquiv d (omegaEquiv i₁ i₂ h)
        (exteriorPower.ιMulti A d fun l => @KaehlerDifferential.D k A _ _ i₁.toAlgebra (a l)) =
      exteriorPower.ιMulti A d fun l => @KaehlerDifferential.D k A _ _ i₂.toAlgebra (a l) := by
  rw [extEquiv_ιMulti]
  simp only [omegaEquiv_D]

private theorem topFormsMap_extEquiv (i₁ i₂ : k →+* A) (j₁ j₂ : k →+* K)
    (hA : kerInt i₁ = kerInt i₂)
    (hK : kerInt j₁ = kerInt j₂)
    (hs₁ : letI := i₁.toAlgebra; letI := j₁.toAlgebra; IsScalarTower k A K)
    (hs₂ : letI := i₂.toAlgebra; letI := j₂.toAlgebra; IsScalarTower k A K) (d : ℕ)
    (σ : letI := i₁.toAlgebra; ⋀[A]^d Ω[A⁄k]) (σ' : letI := i₂.toAlgebra; ⋀[A]^d Ω[A⁄k])
    (hσ' : σ' = extEquiv d (omegaEquiv i₁ i₂ hA) σ) :
    (letI := i₂.toAlgebra; letI := j₂.toAlgebra; haveI := hs₂;
      MMP.Mori.topFormsMap k A K d σ') =
    extEquiv d (omegaEquiv j₁ j₂ hK)
      (letI := i₁.toAlgebra; letI := j₁.toAlgebra; haveI := hs₁;
        MMP.Mori.topFormsMap k A K d σ) := by
  subst hσ'
  have hspan := letI := i₁.toAlgebra
    exteriorPower.ιMulti_span_of_span (R := A) (n := d) (M := Ω[A⁄k])
      (KaehlerDifferential.span_range_derivation k A)
  have hσ : σ ∈ Submodule.span A _ := hspan ▸ Submodule.mem_top
  induction hσ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    choose a ha using fun l => hm (Set.mem_range_self l)
    have hm' : m = fun l => @KaehlerDifferential.D k A _ _ i₁.toAlgebra (a l) :=
      funext fun l => (ha l).symm
    subst hm'
    rw [extEquiv_omegaEquiv_ιMulti_D, topFormsMap_ιMulti_D i₂ j₂ hs₂,
      topFormsMap_ιMulti_D i₁ j₁ hs₁]
    exact (extEquiv_omegaEquiv_ιMulti_D j₁ j₂ hK d (fun l => algebraMap A K (a l))).symm
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [map_smul, map_smul, hx]
    conv_rhs => rw [map_smul]
    exact (LinearMap.map_smul_of_tower (extEquiv d (omegaEquiv j₁ j₂ hK)).toLinearMap r _).symm

end Compat

section Scheme

open Opposite

variable {k : Type*} [Field k] {W : Scheme.{u_1}}

/-- The `k`-algebra structure of `Γ(W, ⊤)` given by `s`. -/
private noncomputable def globalHom (s : W ⟶ Spec (.of k)) : k →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop).hom

/-- The `k`-algebra structure of the stalk `𝒪_{W,x}` given by `s`. -/
private noncomputable def stalkHom (s : W ⟶ Spec (.of k)) (x : W) : k →+* W.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ W.presheaf.germ ⊤ x trivial).hom

private theorem stalkHom_eq (s : W ⟶ Spec (.of k)) (x : W) :
    stalkHom s x = (W.presheaf.germ ⊤ x trivial).hom.comp (globalHom s) := rfl

private theorem globalHom_ratCast (s s' : W ⟶ Spec (.of k)) [CharZero k] (q : ℚ) :
    globalHom s (q : k) = globalHom s' (q : k) :=
  congrArg (fun φ : ℚ →+* Γ(W, ⊤) => φ q)
    (RingHom.ext_rat ((globalHom s).comp (Rat.castHom k)) ((globalHom s').comp (Rat.castHom k)))

/-- On an integral scheme `W` with two structures `s₁, s₂` of a variety over a field `k` of
characteristic zero, every `s₁(c)` is a root of a polynomial over `s₂(k)` whose derivative is a
unit at it. -/
private theorem exists_eval₂_eq_zero_isUnit [CharZero k] [IsIntegral W] (s₁ s₂ : W ⟶ Spec (.of k))
    [LocallyOfFiniteType s₂] (c : k) :
    ∃ P : Polynomial k, P.Monic ∧ P.eval₂ (globalHom s₂) (globalHom s₁ c) = 0 ∧
      IsUnit ((Polynomial.derivative P).eval₂ (globalHom s₂) (globalHom s₁ c)) := by
  classical
  by_cases hq : ∃ q : ℚ, c = q
  · obtain ⟨q, rfl⟩ := hq
    refine ⟨Polynomial.X - Polynomial.C (q : k), Polynomial.monic_X_sub_C _, ?_, ?_⟩
    · simp [globalHom_ratCast s₁ s₂]
    · simp
  push Not at hq
  letI : Algebra k Γ(W, ⊤) := (globalHom s₂).toAlgebra
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  -- algebraicity, through an affine open
  obtain ⟨U, hU, hUne⟩ : ∃ U : W.Opens, IsAffineOpen U ∧ Nonempty U := by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
      (Set.mem_univ (genericPoint W))
    exact ⟨U, hU, ⟨⟨_, hx⟩⟩⟩
  let ρ : Γ(W, ⊤) →+* Γ(W, U) := (W.presheaf.map (homOfLE le_top).op).hom
  have hρ : Function.Injective ρ := map_injective_of_isIntegral W _
  letI : Algebra k Γ(W, U) := MMP.Mori.sectionAlgebra s₂ U
  haveI : Algebra.FiniteType k Γ(W, U) := MMP.Mori.finiteType_sectionAlgebra s₂ hU
  have hρk : ∀ c', ρ (globalHom s₂ c') = algebraMap k Γ(W, U) c' := fun c' => rfl
  have hunit : ∀ q : ℚ, IsUnit (ρ (globalHom s₁ c) - algebraMap k Γ(W, U) (q : k)) := by
    intro q
    rw [← hρk, ← globalHom_ratCast s₁ s₂, ← map_sub, ← map_sub]
    exact ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hq q))).map _).map _
  obtain ⟨P, hP0, hP⟩ := isAlgebraic_of_forall_isUnit_sub (ρ (globalHom s₁ c)) hunit
  have hPa : Polynomial.aeval (globalHom s₁ c) P = 0 := by
    apply hρ
    rw [map_zero, ← hP, Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rfl
  have hint : IsIntegral k (globalHom s₁ c) := IsAlgebraic.isIntegral ⟨P, hP0, hPa⟩
  obtain ⟨u, v, huv⟩ := (minpoly.irreducible hint).separable
  have h1 := congrArg (Polynomial.aeval (globalHom s₁ c)) huv
  rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, zero_add, map_one] at h1
  exact ⟨minpoly k (globalHom s₁ c), minpoly.monic hint, minpoly.aeval k _,
    IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at h1)⟩

/-- Two structures of a variety over a field of characteristic zero on an integral scheme give
the same kernel of `Ω_{𝒪_{W,x}/ℤ} → Ω_{𝒪_{W,x}/k}`. -/
private theorem kerInt_stalkHom_eq [CharZero k] [IsIntegral W] (s₁ s₂ : W ⟶ Spec (.of k))
    [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] (x : W) :
    kerInt (stalkHom s₁ x) = kerInt (stalkHom s₂ x) := by
  have key : ∀ (t₁ t₂ : W ⟶ Spec (.of k)) [LocallyOfFiniteType t₂],
      kerInt (stalkHom t₁ x) ≤ kerInt (stalkHom t₂ x) := by
    intro t₁ t₂ _
    refine kerInt_le _ _ fun c => ?_
    obtain ⟨P, -, h0, hu⟩ := exists_eval₂_eq_zero_isUnit t₁ t₂ c
    refine ⟨P, ?_, ?_⟩
    · rw [stalkHom_eq, stalkHom_eq, RingHom.comp_apply, ← Polynomial.hom_eval₂, h0, map_zero]
    · rw [stalkHom_eq, stalkHom_eq, RingHom.comp_apply, ← Polynomial.hom_eval₂]
      exact hu.map _
  exact le_antisymm (key s₁ s₂) (key s₂ s₁)

end Scheme

section FT

/-- Let `B` be a domain with two ring maps `i₁, i₂ : k → B` from a field, `B` of finite type
through `i₂`, each `i₂(c)` integral over `i₁(k)`, and `π : B → L` a map to a field finite over
`k` through `i₁`. Then `B` is of finite type through `i₁`. -/
private theorem finiteType_of_finiteType_of_isIntegral {k B L : Type*} [Field k] [CommRing B]
    [IsDomain B]
    [Field L] (i₁ i₂ : k →+* B) (π : B →+* L) (h₂ : i₂.FiniteType)
    (hint : ∀ c, letI := i₁.toAlgebra; IsIntegral k (i₂ c)) (hfin : (π.comp i₁).Finite) :
    i₁.FiniteType := by
  obtain ⟨S, hS⟩ := (h₂ : @Algebra.FiniteType k B _ _ i₂.toAlgebra).out
  have hS' : Subring.closure (Set.range i₂ ∪ (S : Set B)) = ⊤ := by
    letI := i₂.toAlgebra
    have h := Algebra.adjoin_eq_ring_closure (R := k) (S : Set B)
    rw [hS] at h
    exact h.symm
  letI := i₁.toAlgebra
  let F : Subalgebra k B := Algebra.adjoin k (Set.range i₂)
  haveI : Algebra.IsIntegral k F := by
    refine ⟨fun x => ?_⟩
    have := (Algebra.IsIntegral.adjoin (R := k) (S := Set.range i₂)
      (by rintro _ ⟨c, rfl⟩; exact hint c))
    exact this.isIntegral x
  have hF : IsField F :=
    isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  letI : Field F := hF.toField
  letI : Algebra k L := (π.comp i₁).toAlgebra
  haveI : Module.Finite k L := hfin
  let πF : F →ₗ[k] L :=
    { toFun := fun x => π (x : B)
      map_add' := fun x y => map_add π (x : B) y
      map_smul' := fun c x => by
        change π (algebraMap k B c * x) = (π.comp i₁) c * π x
        rw [map_mul]; rfl }
  have hπinj : Function.Injective πF := fun x y hxy =>
    (π.comp (F.val : F →+* B)).injective hxy
  haveI : Module.Finite k F := Module.Finite.of_injective πF hπinj
  haveI : Algebra.FiniteType k F := inferInstance
  -- `B` is of finite type over `F`
  haveI : Algebra.FiniteType F B := by
    refine ⟨⟨S, ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subring.closure (Set.range i₂ ∪ (S : Set B)) := by rw [hS']; trivial
    rw [← Subalgebra.mem_toSubring, Algebra.adjoin_eq_ring_closure]
    refine Subring.closure_mono ?_ hx
    rintro _ (⟨c, rfl⟩ | h)
    · exact Or.inl ⟨⟨i₂ c, Algebra.subset_adjoin ⟨c, rfl⟩⟩, rfl⟩
    · exact Or.inr h
  exact Algebra.FiniteType.trans (S := F) inferInstance inferInstance

end FT

section Forms

variable {k : Type*} [Field k] [CharZero k] {W : Scheme.{u_1}} [IsIntegral W]
  [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- The coordinate of a nonzero vector of `L^{⊗1}` along `b^{⊗1}` is nonzero. -/
private theorem repr_basis_one_ne_zero {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) {τ : ZTensorPower K L 1} (hτ : τ ≠ 0) :
    (ZTensorPower.basis b 1).repr τ () ≠ 0 := fun h0 =>
  hτ (by rw [← basis_unit_repr_smul (ZTensorPower.basis b 1) τ, h0, zero_smul])

/-- The order of a nonzero form along `Γ`, computed from a generator `σ` of `Ω^n_{𝒪_{W,Γ}/k}` with
image `g • β` for a basis `β` of `Ω^n_{k(W)/k}`. -/
private theorem ordForm_eq_ord_inv_add (s : W ⟶ Spec (.of k)) (Γ : MMP.Mori.PrimeDivisor W) {n : ℕ}
    (β : letI := functionFieldAlgebra s
      Module.Basis Unit W.functionField (⋀[W.functionField]^n Ω[W.functionField⁄k]))
    (σ : letI := stalkAlgebra s Γ.genericPoint; ⋀[Γ.localRing]^n Ω[Γ.localRing⁄k])
    (hσ : letI := stalkAlgebra s Γ.genericPoint; Submodule.span Γ.localRing {σ} = ⊤)
    {g : W.functionField} (hg0 : g ≠ 0)
    (hg : letI := stalkAlgebra s Γ.genericPoint; letI := functionFieldAlgebra s
      haveI := isScalarTower_stalk_functionField s Γ.genericPoint
      topFormsMap k Γ.localRing W.functionField n σ = g • β ())
    {τ : RationalPluriForms s n 1} (hτ : τ ≠ 0) :
    Γ.ordForm τ = W.ord g⁻¹ Γ.genericPoint + W.ord (letI := functionFieldAlgebra s
      (ZTensorPower.basis β 1).repr (τ : PluriForms k W.functionField n 1) ())
        Γ.genericPoint := by
  letI := stalkAlgebra s Γ.genericPoint
  letI := functionFieldAlgebra s
  haveI := isScalarTower_stalk_functionField s Γ.genericPoint
  have h0 : topFormsMap k Γ.localRing W.functionField n σ ≠ 0 := by
    rw [hg]; exact smul_ne_zero hg0 (β.ne_zero ())
  rw [PrimeDivisor.ordForm_eq Γ τ hσ h0]
  have hb : topFormsBasis Γ.localRing hσ h0 () = g • β () := by
    rw [topFormsBasis_apply, hg]
  have hrepr :
      formCoeff (k := k) (m := 1) Γ.localRing hσ h0 (τ : PluriForms k W.functionField n 1) =
      (g ^ (1 : ℤ))⁻¹ * (ZTensorPower.basis β 1).repr (τ : PluriForms k W.functionField n 1) () :=
    ZTensorPower.basis_repr_of_eq_smul hb 1 τ
  rw [hrepr, zpow_one]
  exact Scheme.ord_mul (inv_ne_zero hg0) (repr_basis_one_ne_zero β hτ)

/-- **Rational top forms for two structures of a variety.** On a normal integral scheme `W` with
two structures `s₁, s₂` of a normal variety of dimension `n` over a field of characteristic zero,
nonzero rational `n`-forms `τ₁` (for `s₁`) and `τ₂` (for `s₂`) have orders differing by the
orders of a nonzero rational function: `ord_Γ(τ₁) - v_Γ(c₁) = ord_Γ(τ₂) - v_Γ(c₂)`. -/
private theorem exists_ordForm_sub_eq (s₁ s₂ : W ⟶ Spec (.of k)) (h₁ : IsNormalVariety k s₁)
    (h₂ : IsNormalVariety k s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] {n : ℕ}
    (hn : topologicalKrullDim W = n) {τ₁ : RationalPluriForms s₁ n 1}
    {τ₂ : RationalPluriForms s₂ n 1} (hτ₁ : τ₁ ≠ 0) (hτ₂ : τ₂ ≠ 0) :
    ∃ c₁ c₂ : W.functionField, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ ∀ Γ : MMP.Mori.PrimeDivisor W,
      Γ.ordForm τ₁ - W.ord c₁ Γ.genericPoint = Γ.ordForm τ₂ - W.ord c₂ Γ.genericPoint := by
  have hK := kerInt_stalkHom_eq s₁ s₂ (genericPoint W)
  obtain ⟨β₁⟩ := MMP.Positivity.exists_basis_topForms h₁ hn
  let EK := extEquiv n (omegaEquiv (stalkHom s₁ (genericPoint W)) (stalkHom s₂ (genericPoint W)) hK)
  let β₂ : letI := functionFieldAlgebra s₂
      Module.Basis Unit W.functionField (⋀[W.functionField]^n Ω[W.functionField⁄k]) :=
    β₁.map EK
  let c₁ : W.functionField := letI := functionFieldAlgebra s₁
    (ZTensorPower.basis β₁ 1).repr (τ₁ : PluriForms k W.functionField n 1) ()
  let c₂ : W.functionField := letI := functionFieldAlgebra s₂
    (ZTensorPower.basis β₂ 1).repr (τ₂ : PluriForms k W.functionField n 1) ()
  have hc₁ : c₁ ≠ 0 := letI := functionFieldAlgebra s₁; repr_basis_one_ne_zero β₁ hτ₁
  have hc₂ : c₂ ≠ 0 := letI := functionFieldAlgebra s₂; repr_basis_one_ne_zero β₂ hτ₂
  refine ⟨c₁, c₂, hc₁, hc₂, fun Γ => ?_⟩
  have hA := kerInt_stalkHom_eq s₁ s₂ Γ.genericPoint
  have hs₁ := isScalarTower_stalk_functionField s₁ Γ.genericPoint
  have hs₂ := isScalarTower_stalk_functionField s₂ Γ.genericPoint
  obtain ⟨σ₁, hσ₁, h0₁⟩ :=
    PrimeDivisor.exists_topForms_generator_of_topologicalKrullDim_eq (sX := s₁) Γ hn
  let t₁ := (letI := stalkAlgebra s₁ Γ.genericPoint; letI := functionFieldAlgebra s₁
    haveI := hs₁; topFormsMap k Γ.localRing W.functionField n σ₁)
  let g : W.functionField := letI := functionFieldAlgebra s₁; β₁.repr t₁ ()
  have hg₁ : t₁ = g • β₁ () := letI := functionFieldAlgebra s₁; (basis_unit_repr_smul β₁ t₁).symm
  have hg0 : g ≠ 0 := by
    intro h
    apply h0₁
    change t₁ = 0
    rw [hg₁, h]
    letI := functionFieldAlgebra s₁
    exact zero_smul _ _
  let σ₂ := extEquiv n (omegaEquiv (stalkHom s₁ Γ.genericPoint) (stalkHom s₂ Γ.genericPoint) hA) σ₁
  have hσ₂ : letI := stalkAlgebra s₂ Γ.genericPoint; Submodule.span Γ.localRing {σ₂} = ⊤ :=
    span_singleton_linearEquiv_eq_top _ hσ₁
  have hcompat := topFormsMap_extEquiv (stalkHom s₁ Γ.genericPoint) (stalkHom s₂ Γ.genericPoint)
    (stalkHom s₁ (genericPoint W)) (stalkHom s₂ (genericPoint W)) hA hK hs₁ hs₂ n σ₁ σ₂ rfl
  have hg₂ : (letI := stalkAlgebra s₂ Γ.genericPoint; letI := functionFieldAlgebra s₂
      haveI := hs₂; topFormsMap k Γ.localRing W.functionField n σ₂) = g • β₂ () := by
    refine hcompat.trans ?_
    change EK t₁ = g • EK (β₁ ())
    rw [hg₁]
    exact map_smul EK g (β₁ ())
  rw [ordForm_eq_ord_inv_add s₁ Γ β₁ σ₁ hσ₁ hg0 hg₁ hτ₁,
    ordForm_eq_ord_inv_add s₂ Γ β₂ σ₂ hσ₂ hg0 hg₂ hτ₂]
  ring

end Forms

section StructureVia

open Opposite

variable {k : Type*} [Field k] {W Y : Scheme.{u_1}}

/-- The structure morphism `Y ⟶ Spec k` corresponding to `s` through `Γ(Y, 𝒪_Y) ≅ Γ(W, 𝒪_W)`. -/
private noncomputable def structureVia (q : W ⟶ Y) [IsIso q.appTop] (s : W ⟶ Spec (.of k)) :
    Y ⟶ Spec (.of k) :=
  Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ inv q.appTop)

private theorem comp_structureVia (q : W ⟶ Y) [IsIso q.appTop] (s : W ⟶ Spec (.of k)) :
    q ≫ structureVia q s = s := by
  rw [structureVia, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

private theorem globalHom_structureVia (q : W ⟶ Y) [IsIso q.appTop] (s : W ⟶ Spec (.of k)) :
    globalHom (structureVia q s) = (inv q.appTop).hom.comp (globalHom s) := by
  have h : (structureVia q s).appTop =
      (Scheme.ΓSpecIso (.of k)).hom ≫ (Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ inv q.appTop := by
    rw [structureVia, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  rw [globalHom, globalHom, h, Iso.inv_hom_id_assoc]
  rfl

private theorem globalHom_comp (q : W ⟶ Y) (s : Y ⟶ Spec (.of k)) :
    globalHom (q ≫ s) = q.appTop.hom.comp (globalHom s) := by
  rw [globalHom, globalHom, Scheme.Hom.comp_appTop]
  rfl

private theorem appLE_top_eq (f : Y ⟶ Spec (.of k)) (V : Y.Opens) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V le_top).hom =
      (Y.presheaf.map (homOfLE le_top).op).hom.comp (globalHom f) := rfl

/-- At a closed point `w` of `W` over `V`, the composite `k ⟶ Γ(V, 𝒪_Y) ⟶ κ(w)` through
`structureVia q s₁` is the residue field structure of `s₁`, hence finite. -/
private theorem finite_residue_comp_structureVia (q : W ⟶ Y) [IsIso q.appTop]
    (s₁ : W ⟶ Spec (.of k)) [LocallyOfFiniteType s₁] (V : Y.Opens) (w : W) (hwV : q w ∈ V)
    (hwc : w ∈ closedPoints W) :
    (((IsLocalRing.residue _).comp ((q.stalkMap w).hom.comp (Y.presheaf.germ V (q w) hwV).hom)).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (structureVia q s₁).appLE ⊤ V le_top).hom).Finite := by
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace s₁
  letI := MMP.Mori.stalkAlgebra s₁ w
  have hf := MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed s₁ w
    (mem_closedPoints_iff.mp hwc)
  have e : ((IsLocalRing.residue _).comp ((q.stalkMap w).hom.comp
      (Y.presheaf.germ V (q w) hwV).hom)).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (structureVia q s₁).appLE ⊤ V le_top).hom =
      algebraMap k (IsLocalRing.ResidueField (W.presheaf.stalk w)) := by
    ext c
    rw [appLE_top_eq, globalHom_structureVia]
    change IsLocalRing.residue _ ((q.stalkMap w).hom ((Y.presheaf.germ V (q w) hwV).hom
      ((Y.presheaf.map (homOfLE le_top).op).hom ((inv q.appTop).hom (globalHom s₁ c))))) =
      IsLocalRing.residue _ (stalkHom s₁ w c)
    congr 1
    rw [TopCat.Presheaf.germ_res_apply]
    have e1 : Y.presheaf.germ ⊤ (q w) trivial ≫ q.stalkMap w =
        q.appTop ≫ W.presheaf.germ ⊤ w trivial := Scheme.Hom.germ_stalkMap q ⊤ w trivial
    have e2 := congrArg (fun φ => φ.hom ((inv q.appTop).hom (globalHom s₁ c))) e1
    simp only [CommRingCat.comp_apply] at e2
    refine e2.trans ?_
    have e3 : q.appTop.hom ((inv q.appTop).hom (globalHom s₁ c)) = globalHom s₁ c := by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    rw [e3]
    rfl
  rw [e]
  exact RingHom.finite_algebraMap.mpr hf

/-- Over an affine open `V` of `Y`, the map `k ⟶ Γ(V, 𝒪_Y)` given by `structureVia q s₁` is of
finite type. -/
private theorem finiteType_appLE_structureVia [CharZero k] [IsIntegral W] [IsIntegral Y]
    (q : W ⟶ Y) [IsIso q.appTop] [Surjective q]
    (s₁ : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s₁]
    [LocallyOfFiniteType sY] (V : Y.affineOpens) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (structureVia q s₁).appLE ⊤ V.1 le_top).hom.FiniteType := by
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace s₁
  let i₁ := ((Scheme.ΓSpecIso (.of k)).inv ≫ (structureVia q s₁).appLE ⊤ V.1 le_top).hom
  by_cases hV : (V.1 : Set Y).Nonempty
  swap
  · have : Subsingleton Γ(Y, V.1) := by
      rw [Set.not_nonempty_iff_eq_empty] at hV
      have hV' : V.1 = ⊥ := TopologicalSpace.Opens.ext hV
      rw [hV']
      infer_instance
    exact RingHom.FiniteType.of_surjective _ fun _ => ⟨0, Subsingleton.elim _ _⟩
  haveI : Nonempty V.1 := hV.to_subtype
  let i₂ := ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ V.1 le_top).hom
  have h₂ : i₂.FiniteType := MMP.Mori.finiteType_sectionAlgebra sY V.2
  let ρ : Γ(W, ⊤) →+* Γ(Y, V.1) :=
    (Y.presheaf.map (homOfLE le_top).op).hom.comp (inv q.appTop).hom
  have hi₁ : i₁ = ρ.comp (globalHom s₁) := by
    rw [show i₁ = _ from appLE_top_eq _ _, globalHom_structureVia]
    rfl
  have hinv : ∀ x, (inv q.appTop).hom (q.appTop.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  have hi₂ : ∀ c, i₂ c = ρ (globalHom (q ≫ sY) c) := by
    intro c
    rw [show i₂ = _ from appLE_top_eq _ _, globalHom_comp]
    simp only [ρ, RingHom.comp_apply, hinv]
  have hint : ∀ c, letI := i₁.toAlgebra; IsIntegral k (i₂ c) := by
    intro c
    obtain ⟨P, hPm, hP0, -⟩ := exists_eval₂_eq_zero_isUnit (q ≫ sY) s₁ c
    refine ⟨P, hPm, ?_⟩
    change P.eval₂ i₁ (i₂ c) = 0
    rw [hi₁, hi₂, ← Polynomial.hom_eval₂, hP0, map_zero]
  -- a closed point `w` of `W` over `V`
  obtain ⟨y, hy⟩ := hV
  obtain ⟨w', hw'⟩ := q.surjective y
  obtain ⟨w, hwV, hwc⟩ := nonempty_inter_closedPoints
    (⟨w', show q w' ∈ V.1 from hw' ▸ hy⟩ : ((q ⁻¹ᵁ V.1 : W.Opens) : Set W).Nonempty)
    (q ⁻¹ᵁ V.1).isOpen.isLocallyClosed
  exact finiteType_of_finiteType_of_isIntegral i₁ i₂ _ h₂ hint
    (finite_residue_comp_structureVia q s₁ V.1 w hwV hwc)

/-- `structureVia q s₁` is locally of finite type, for `q : W ⟶ Y` proper surjective with
`Γ(Y, 𝒪_Y) ≅ Γ(W, 𝒪_W)`, `Y` of finite type over `k` through some `sY`, and `W` of finite type
through `s₁`. -/
private theorem locallyOfFiniteType_structureVia [CharZero k] [IsIntegral W] [IsIntegral Y]
    (q : W ⟶ Y) [IsIso q.appTop] [Surjective q]
    (s₁ : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s₁]
    [LocallyOfFiniteType sY] : LocallyOfFiniteType (structureVia q s₁) := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) fun V => ?_
  have e : ((structureVia q s₁).appLE ⊤ V.1 le_top).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (structureVia q s₁).appLE ⊤ V.1 le_top).hom.comp
        (Scheme.ΓSpecIso (.of k)).hom.hom := by
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id]
  rw [e]
  exact (finiteType_appLE_structureVia q s₁ sY V).comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.surjective)

end StructureVia

end TwoStructures

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

end MMP.Flips.Fa2NoExtractedDivisors

namespace MMP.Flips

/-! ### `ℝ`-Cartier divisors and linear equivalence -/

section LinearEquivalence

open Fa2NoExtractedDivisors

variable {k : Type u} [Field k]

/-- The difference of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
public theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D - D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r (fun j => -r' j), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The sum of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
public theorem isCartierCombination_add {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add]

/-- A divisor linearly equivalent to `0` is `ℝ`-Cartier. -/
public theorem isCartierCombination_toRDivisor_of_linearlyEquivalent_zero {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {L₀ : Divisor X}
    (h : L₀.LinearlyEquivalent 0) : IsCartierCombination (Divisor.toRDivisor L₀) :=
  ⟨1, fun _ => 1, fun _ => L₀,
    fun _ => Divisor.IsCartier.of_linearlyEquivalent h Divisor.isCartier_zero,
    by simp [← toRDivisor_eq_mapCoeffs]⟩

/-- An `ℝ`-Cartier divisor has an intersection number with every proper curve. -/
public theorem exists_isRIntersectionNumber {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : RDivisor X}
    (hD : IsCartierCombination D) (C : ProperCurve sX) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX D r L C x := by
  obtain ⟨m, r, L, hL, hpres⟩ := hD
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  subst hpres
  exact ⟨m, r, L, _, isRIntersectionNumber_sum_degreeOn k sX C r L hL⟩

/-- A divisor `L₀` linearly equivalent to `0` has intersection number `0` with every proper curve,
for every presentation. -/
public theorem eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {L₀ : Divisor X} (h : L₀.LinearlyEquivalent 0)
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) r L C x) : x = 0 := by
  have hc : L₀.IsCartier := Divisor.IsCartier.of_linearlyEquivalent h Divisor.isCartier_zero
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L₀)
    (fun _ => hc)
  rw [show ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ = Divisor.toRDivisor L₀ by simp] at h1
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1]
  simp [Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h]

variable {W X : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W]
  [IsNormal W] [CompactSpace W] {p : W ⟶ X}

/-- If `M` is `p`-nef and the `ℝ`-Cartier divisor `N` is numerically trivial on the curves
contracted by `p`, then `M - N` is `p`-nef. -/
public theorem isRelativelyNef_sub_of_eq_zero {M N : RDivisor W}
    (hM : IsRelativelyNef k sW p M) (hNc : IsCartierCombination N)
    (hN0 : ∀ C : ProperCurve sW, C.IsContractedBy p → ∀ {m : ℕ} {r : Fin m → ℝ}
      {L : Fin m → Divisor W} {x : ℝ}, IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW p (M - N) := by
  have hMc : IsCartierCombination M := let ⟨m, r, L, hL, hD, _⟩ := hM; ⟨m, r, L, hL, hD⟩
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_sub hMc hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mM, rM, LM, hLM, hMpres, hall⟩ := hM
  obtain ⟨_, _, _, xN, hxN⟩ := exists_isRIntersectionNumber (k := k) hNc C
  have hxM := isRIntersectionNumber_sum_degreeOn k sW C rM LM hLM
  rw [← hMpres] at hxM
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hxM hxN
  rw [show (1 : ℝ) • M + (-1 : ℝ) • N = M - N by simp only [one_smul, neg_one_smul]; abel]
    at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum, hN0 C hC hxN]
  linarith [hall C hC _ hxM]

/-- If `M` is `p`-nef and `L₀` is linearly equivalent to `0`, then `M - L₀` is `p`-nef. -/
public theorem isRelativelyNef_sub_of_linearlyEquivalent_zero {M : RDivisor W}
    (hM : IsRelativelyNef k sW p M) {L₀ : Divisor W} (hL₀ : L₀.LinearlyEquivalent 0) :
    IsRelativelyNef k sW p (M - Divisor.toRDivisor L₀) :=
  isRelativelyNef_sub_of_eq_zero hM (isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL₀)
    fun C _ _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₀ C hx

/-- If `N` is numerically `p`-trivial and `L₀` is linearly equivalent to `0`, then `N - L₀` is
numerically `p`-trivial. -/
public theorem IsNumericallyTrivialOver.sub_of_linearlyEquivalent_zero {N : RDivisor W}
    (hN : IsNumericallyTrivialOver k sW p N) {L₀ : Divisor W} (hL₀ : L₀.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver k sW p (N - Divisor.toRDivisor L₀) := by
  have hLc := isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL₀
  refine ⟨isCartierCombination_sub hN.1 hLc, hN.2.1, fun C hC _ _ _ x₁ _ _ _ x₂ hx₁ hx₂ => ?_⟩
  obtain ⟨_, _, _, xN, hxN⟩ := exists_isRIntersectionNumber (k := k) hN.1 C
  obtain ⟨_, _, _, xL, hxL⟩ := exists_isRIntersectionNumber (k := k) hLc C
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hxN hxL
  rw [show (1 : ℝ) • N + (-1 : ℝ) • Divisor.toRDivisor L₀ = N - Divisor.toRDivisor L₀ by
    simp only [one_smul, neg_one_smul]; abel] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx₁ hsum,
    eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₀ C hxL,
    hN.2.2 C hC _ _ _ _ _ _ _ _ hxN hx₂]
  ring

end LinearEquivalence

end MMP.Flips

namespace MMP.Flips.Fa2NoExtractedDivisors

/-- **Projection formula** for a pull-back `L₁ = h^*D` of a Cartier divisor `D` along
`h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`L₁ · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- A divisor `L₁` given as a pull-back along `h` has degree zero on a proper curve whose image is
not a proper curve. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (hnc : ¬ IsProperCurve sY (h C'.point)) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hnc, map_zero]

/-- The pull-back of a Cartier divisor is Cartier. -/
private theorem isCartier_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {L : Divisor X} (hL : L.IsCartier) {L' : Divisor Y}
    (h : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback f hB L') : L'.IsCartier := by
  obtain ⟨hB, hp⟩ := h
  rw [← Divisor.IsPullback.pullback_eq hL hp]
  exact hL.isCartier_pullback f hB

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  exact ⟨m, r, L', fun j => isCartier_of_isPullback (hL j) (hpb j),
    by simp only [toRDivisor_eq_mapCoeffs]⟩

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

section CommonModel

/-- The point `Spec k(X) ⟶ Y` of a partial map defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

end CommonModel

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_self {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} {D : RDivisor W} (hD : IsCartierCombination D) :
    IsNumericallyEquivalentOver k sW p D D :=
  ⟨hD, hD, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-! ### Intersection numbers of negatives, pull-backs and lifted curves -/

section Curves

variable {k : Type u} [Field k]

/-- If `q ≫ g` contracts `C'`, then `g` contracts the image curve `C = q(C')`. -/
private theorem isContractedBy_of_comp {W Y Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} (q : W ⟶ Y) [IsProper q] (g : Y ⟶ Z) (C' : ProperCurve sW)
    (C : ProperCurve sY) (hC : C.point = q C'.point) (hC' : C'.IsContractedBy (q ≫ g)) :
    C.IsContractedBy g := by
  intro y hy
  rw [hC] at hy
  have hsub : closure ({q C'.point} : Set Y) ⊆ q '' closure ({C'.point} : Set W) :=
    closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
      (q.isClosedMap _ isClosed_closure)
  obtain ⟨z, hz, rfl⟩ := hsub hy
  rw [hC]
  simpa only [Scheme.Hom.comp_apply] using hC' z hz

/-- The generic point of a proper curve is not a closed point. -/
private theorem exists_specializes_ne_of_isProperCurve {G : Scheme.{u}} (sG : G ⟶ Spec (.of k))
    (p : G) (h : IsProperCurve sG p) : ∃ w, p ⤳ w ∧ w ≠ p := by
  by_contra! hcon
  have hsub : Subsingleton (closure ({p} : Set G)) :=
    ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => Subtype.ext
      ((hcon a (specializes_iff_mem_closure.mpr ha)).trans
        (hcon b (specializes_iff_mem_closure.mpr hb)).symm)⟩
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h2 := @topologicalKrullDim_zero_of_discreteTopology (closure ({p} : Set G)) _
    (@Subsingleton.discreteTopology _ _ hsub)
  rw [h1] at h2
  exact absurd h2 (by decide)

variable {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} [IsSeparated sT]
  [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_map (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

end Curves

/-- **Projection formula** for a pull-back `G = q^*N` of an `ℝ`-Cartier divisor: on a proper
curve `C' ⊆ W` whose image is the proper curve `C`, `G · C' = [k(C') : k(C)] (N · C)`, for all
presentations of `G` and `N`. -/
private theorem isRIntersectionNumber_pullback_eq_mul {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (C : ProperCurve sY)
    (hC : C.point = q C'.point) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY N r' L' C x) :
    x' = residueFieldDegree q C'.point * x := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hNpres, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => isCartier_of_isPullback (hL₀ j) (hpb j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  have hy0 := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
  rw [← hNpres] at hy0
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx hy0]
  have hdeg : ∀ j, ((L₁ j).degreeOn k (q ≫ sY) C'.ι C'.dim_le (hL₁ j) : ℝ) =
      (residueFieldDegree q C'.point : ℝ) * (L₀ j).degreeOn k sY C.ι C.dim_le (hL₀ j) :=
    fun j => by
      rw [degreeOn_eq_mul_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' C hC]
      push_cast
      ring
  simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]

/-- A pull-back `G = q^*N` of an `ℝ`-Cartier divisor has intersection number `0` with a proper
curve `C' ⊆ W` whose image is not a proper curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) (hq : q ≫ sY = sW) {N : RDivisor Y} {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hnc : ¬ IsProperCurve sY (q C'.point))
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x' : ℝ}
    (hx' : IsRIntersectionNumber k sW G r L C' x') : x' = 0 := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, -, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => isCartier_of_isPullback (hL₀ j) (hpb j)
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx' hx0]
  simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hnc]

/-- A curve contracted by `p` is contracted by `p ≫ f`. -/
private theorem isContractedBy_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} {p : W ⟶ X} (f : X ⟶ Z) {C : ProperCurve sW}
    (hC : C.IsContractedBy p) : C.IsContractedBy (p ≫ f) :=
  fun z hz => by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]

/-- A `(p ≫ f)`-nef divisor is `p`-nef. -/
private theorem isRelativelyNef_of_comp {k : Type u} [Field k] {W X Z : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {p : W ⟶ X} (f : X ⟶ Z) {D : RDivisor W}
    (hD : IsRelativelyNef k sW (p ≫ f) D) : IsRelativelyNef k sW p D :=
  let ⟨m, r, L, hL, hpres, hall⟩ := hD
  ⟨m, r, L, hL, hpres, fun C hC => hall C (isContractedBy_comp f hC)⟩

/-- **Pull-backs of relatively nef divisors.** Let `q : W ⟶ Y` be proper and `N` a `g`-nef
`ℝ`-Cartier divisor on `Y`. Then `q^*N` is `(q ≫ g)`-nef: on a proper curve `C' ⊆ W` contracted
by `q ≫ g`, the projection formula gives `q^*N · C' = [k(C') : k(q C')] (N · q C')` when `q(C')`
is a curve, which is contracted by `g`, and `q^*N · C' = 0` when `q(C')` is a point. -/
private theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {N : RDivisor Y}
    (hN : IsRelativelyNef k sY g N) {G : RDivisor W} (hG : IsRCartierPullback q N G) :
    IsRelativelyNef k sW (q ≫ g) G := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_of_isRCartierPullback hG
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C' hC' x hx => ?_⟩
  by_cases hc : IsProperCurve sY (q C'.point)
  · let C : ProperCurve sY := ⟨_, hc⟩
    obtain ⟨m', r', L', hL', hNpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    rw [← hNpres] at hy
    rw [isRIntersectionNumber_pullback_eq_mul q hq hG C' C rfl hx hy]
    exact mul_nonneg (Nat.cast_nonneg _) (hall C (isContractedBy_of_comp q g C' C rfl hC') _ hy)
  · exact (isRIntersectionNumber_pullback_eq_zero q hq hG C' hc hx).ge

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- If `L` is numerically trivial on the proper curve `C`, then
`(G - G' + L) · C = G · C - G' · C`. -/
private theorem isRIntersectionNumber_sub_add_eq {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {G G' L : RDivisor W} (hLc : IsCartierCombination L) (C : ProperCurve sW)
    (hL0 : ∀ {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW L r L' C x → x = 0)
    {m₁ : ℕ} {r₁ : Fin m₁ → ℝ} {L₁ : Fin m₁ → Divisor W} {x₁ : ℝ}
    {m₂ : ℕ} {r₂ : Fin m₂ → ℝ} {L₂ : Fin m₂ → Divisor W} {x₂ : ℝ}
    {m₃ : ℕ} {r₃ : Fin m₃ → ℝ} {L₃ : Fin m₃ → Divisor W} {x₃ : ℝ}
    (hx₁ : IsRIntersectionNumber k sW G r₁ L₁ C x₁)
    (hx₂ : IsRIntersectionNumber k sW G' r₂ L₂ C x₂)
    (hx₃ : IsRIntersectionNumber k sW (G - G' + L) r₃ L₃ C x₃) : x₃ = x₁ - x₂ := by
  obtain ⟨_, _, _, x₄, hx₄⟩ := exists_isRIntersectionNumber (k := k) hLc C
  have hlin := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
  have hlin' := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hlin hx₄
  rw [show (1 : ℝ) • ((1 : ℝ) • G + (-1 : ℝ) • G') + (1 : ℝ) • L = G - G' + L by
    simp only [one_smul, neg_one_smul]; abel] at hlin'
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx₃ hlin', hL0 hx₄]
  ring

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D)
    (hDc : D.IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

section FibreCurves

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- In a Noetherian quasi-sober space, a connected closed set `F` meeting a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected_of_inter_nonempty {Y : Type*}
    [TopologicalSpace Y] [NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : _root_.IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
  by_cases hdis : (closure T ∩ S).Nonempty
  · obtain ⟨s, hsT, hsS⟩ := hdis
    obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
        (isClosed_closure : IsClosed (closure T))
    have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
      refine closure_minimal (fun y hy => ?_) ?_
      · have : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
        obtain ⟨z, hz, hyz⟩ := this
        exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
      · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
    obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
    have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
    exact ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS),
      s, hsS, hζ.specializes hsz⟩
  · obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => by
        by_cases haS : a ∈ S
        · exact Or.inr haS
        · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact (hdis ⟨w, hwT, hwS⟩).elim

/-- The scheme-theoretic fibre of a proper `f : Y ⟶ X` over a closed point of a variety `X` is
proper over `k`. -/
private theorem isProper_fiberι_comp (k : Type u) [Field k] {X Y : Scheme}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hf : f ≫ sX = sY) [IsProper f] (x : X) (hx : IsClosed ({x} : Set X)) :
    IsProper (f.fiberι x ≫ sY) := by
  have h : f.fiberι x ≫ sY = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
    simp only [← hf, Scheme.Hom.fiber_fac_assoc]
  rw [h]
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  haveI : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  haveI : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
  infer_instance

/-- A proper curve `C'` of the fibre `f⁻¹(x)` maps to a proper curve of `Y` contracted by `f`; it
does not lie in `S` if its generic point does not, and meets `S` if a specialization does. -/
private theorem exists_properCurve_isContractedBy_of_fiber (k : Type u) [Field k] {X Y : Scheme}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] [IsSeparated sY] (f : Y ⟶ X) (x : X)
    {S : Set Y} (C' : MMP.Mori.ProperCurve (f.fiberι x ≫ sY)) (hCS : f.fiberι x C'.point ∉ S)
    {p' : f.fiber x} (hp' : C'.point ⤳ p') (hpS : f.fiberι x p' ∈ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  let ι := f.fiberι x
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hCι : ¬ C'.IsContractedBy ι := fun h => by
    obtain ⟨w, hw, hne⟩ := exists_specializes_ne_of_isProperCurve _ C'.point C'.isProperCurve
    exact hne (hemb.injective (h w (specializes_iff_mem_closure.mp hw)))
  let C : MMP.Mori.ProperCurve sY := ⟨ι C'.point, isProperCurve_map ι rfl C' hCι⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι C'.point} := C'.range_comp ι rfl
  have hrC : Set.range C.ι = closure {ι C'.point} := C.range_ι
  have hclF : closure {ι C'.point} ⊆ f.base ⁻¹' {x} := by
    rw [← hrange, ← f.range_fiberι x]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, rfl⟩
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι C'.point ∈ closure {ι C'.point})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, ?_, ι p', ?_, hpS⟩
  · rw [hrC]
    exact fun h => hCS (h (subset_closure rfl))
  · rw [hrC]
    exact specializes_iff_mem_closure.mp (hp'.map ι.continuous)

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ :=
    exists_specializes_of_isConnected_of_inter_nonempty hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  -- the scheme-theoretic fibre, proper over `k`
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : IsProper sF := isProper_fiberι_comp k hX f hf x hx
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rw [← hemb.isInducing.specializes_iff, hη', hp']
    exact hηp
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  exact exists_properCurve_isContractedBy_of_fiber k f x ⟨y', hy'⟩ hy'S hy'p'
    (show ι p' ∈ S from hp' ▸ hpS)

end FibreCurves

/-! ### A rational map is defined where a common model has a constant second projection -/

/-- **Rigidity at a point.** Let `p : W ⟶ X` be a proper dominant morphism of integral schemes
with `p_* 𝒪_W = 𝒪_X`, inducing an isomorphism of function fields, and let `q : W ⟶ Y` agree with
the rational map `φ : X ⤏ Y` through `p` at the generic point. If `q` maps the fibre `p⁻¹(y)` to
a single point `c`, then `φ` is defined at `y`: for an affine open `V ∋ c` there is an open
`U ∋ y` with `p⁻¹(U) ⊆ q⁻¹(V)`, and the map `Γ(V, 𝒪_Y) ⟶ Γ(p⁻¹ U, 𝒪_W) ≅ Γ(U, 𝒪_X)` is a
morphism `U ⟶ V` representing `φ`. -/
private theorem mem_domain_of_forall_eq {X Y W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] [IsProper p] (q : W ⟶ Y)
    (hbij : Function.Bijective (functionFieldMap p)) (hiso : ∀ U : X.Opens, IsIso (p.app U))
    (KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {y : X} {c : Y} (hc : ∀ w, p w = y → q w = c) : y ∈ φ.domain := by
  obtain ⟨V, hV, hcV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ c)
  have hK : IsClosed (p '' ((q ⁻¹ᵁ V : W.Opens) : Set W)ᶜ) :=
    p.isClosedMap _ (q ⁻¹ᵁ V).isOpen.isClosed_compl
  let U : X.Opens := ⟨_, hK.isOpen_compl⟩
  have hyU : y ∈ U := by
    rintro ⟨w, hw, rfl⟩
    exact hw (show q w ∈ V by rw [hc w rfl]; exact hcV)
  have hUV : p ⁻¹ᵁ U ≤ q ⁻¹ᵁ V := fun w hw => by_contra fun h => hw ⟨w, h, rfl⟩
  haveI : IsAffine V.toScheme := hV
  let h' : (p ⁻¹ᵁ U).toScheme ⟶ V.toScheme := W.homOfLE hUV ≫ (q ∣_ V)
  haveI : IsIso (p ∣_ U).appTop := by
    rw [morphismRestrict_appTop]
    have h1 := hiso (U.ι ''ᵁ ⊤)
    have h2 : IsIso (W.presheaf.map (eqToHom (image_morphismRestrict_preimage p U ⊤)).op) :=
      inferInstance
    exact IsIso.comp_isIso' h1 h2
  let ψV : U.toScheme ⟶ V.toScheme :=
    U.toScheme.toSpecΓ ≫ Spec.map (h'.appTop ≫ inv (p ∣_ U).appTop) ≫ V.toScheme.isoSpec.inv
  have hψ : (p ∣_ U) ≫ ψV = h' := by
    simp only [ψV]
    rw [reassoc_of% Scheme.toSpecΓ_naturality (p ∣_ U), ← Spec.map_comp_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id, ← reassoc_of% Scheme.toSpecΓ_naturality h']
    change h' ≫ V.toScheme.isoSpec.hom ≫ V.toScheme.isoSpec.inv = h'
    rw [Iso.hom_inv_id, Category.comp_id]
  have hψ' : (p ∣_ U) ≫ ψV ≫ V.ι = (p ⁻¹ᵁ U).ι ≫ q := by
    rw [← Category.assoc, hψ]
    simp only [h', Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have hd : Dense (U : Set X) := U.isOpen.dense ⟨y, hyU⟩
  let g : X.PartialMap Y := ⟨U, hd, ψV ≫ V.ι⟩
  refine Scheme.RationalMap.mem_domain.mpr ⟨g, hyU, ?_⟩
  have hηX : genericPoint X ∈ U := (genericPoint_specializes y).mem_open U.isOpen hyU
  have hηW : genericPoint W ∈ p ⁻¹ᵁ U := by
    change p (genericPoint W) ∈ U
    rw [map_genericPoint_of_isDominant]
    exact hηX
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), KF]
  have key : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      U.fromSpecStalkOfMem (genericPoint X) hηX =
      (p ⁻¹ᵁ U).fromSpecStalkOfMem (genericPoint W) hηW ≫ (p ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  change Spec.map _ ≫ U.fromSpecStalkOfMem (genericPoint X) hηX ≫ ψV ≫ V.ι = _
  rw [reassoc_of% key, hψ', ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-! ### Intersection numbers on curves contracted over the source -/

/-- A pull-back `G = q^*N` has intersection number `0` with every proper curve contracted by
`q`: its image is a closed point, not a curve. -/
private theorem isRIntersectionNumber_pullback_eq_zero_of_isContractedBy {k : Type u} [Field k]
    {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) {N : RDivisor Y}
    {G : RDivisor W} (hG : IsRCartierPullback q N G) (C : ProperCurve sW)
    (hC : C.IsContractedBy q) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C x) : x = 0 := by
  refine isRIntersectionNumber_pullback_eq_zero q hq hG C (fun hc => ?_) hx
  obtain ⟨w, hspec, hne⟩ := exists_specializes_ne_of_isProperCurve sY _ hc
  have hcl : IsClosed ({q C.point} : Set Y) := by
    have h1 : q '' closure ({C.point} : Set W) = {q C.point} := by
      ext z
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hC w' hw'
      · rintro rfl
        exact ⟨C.point, subset_closure rfl, rfl⟩
    rw [← h1]
    exact q.isClosedMap _ isClosed_closure
  exact hne (hspec.mem_closed hcl rfl)

/-- An `f`-ample `ℝ`-Cartier divisor is positive on every proper curve contracted by `f`. -/
private theorem pos_of_isRelativelyAmple {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {g : Y ⟶ Z} {A : RDivisor Y} (hA : IsRelativelyAmple g A)
    (C : ProperCurve sY) (hC : C.IsContractedBy g) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor Y} {x : ℝ} (hx : IsRIntersectionNumber k sY A r L C x) : 0 < x := by
  obtain ⟨m', r', L', hm, hr, hL, rfl⟩ := hA
  have hLc : ∀ j, (L' j).IsCartier := fun j => (hL j).1
  rw [(IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hx
    (isRIntersectionNumber_sum_degreeOn k sY C r' L' hLc)]
  refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier g (hL j) (hLc j) C hC

section Realized

/-- The generic point of `A` lies over every dense open of `X`, for dominant `a : A ⟶ X`. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a _ ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense _ hU

private theorem dense_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    Dense ((a ⁻¹ᵁ U : A.Opens) : Set A) :=
  (a ⁻¹ᵁ U).isOpen.dense ⟨_, genericPoint_mem_preimage a hU⟩

/-- The partial map `a⁻¹(dom g) ⟶ dom g ⟶ Y` is, at the generic point, `Spec k(A) ⟶ Spec k(X)`
followed by `g`. -/
private theorem fromFunctionField_morphismRestrict_comp {A X Y : Scheme.{u}} [IsIntegral A]
    [IsIntegral X] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) :
    (Scheme.PartialMap.mk (a ⁻¹ᵁ g.domain) (dense_preimage a g.dense_domain)
      ((a ∣_ g.domain) ≫ g.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField := by
  rw [partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain),
    partialMap_fromFunctionField_eq _ (genericPoint_mem_of_dense _ g.dense_domain)]
  change _ ≫ (a ∣_ g.domain) ≫ g.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk a).symm

/-- If `p' = g ∘ a` on `a⁻¹(dom g)` for a dominant `a : A ⟶ X`, then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` along `g` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  rw [← fromFunctionField_morphismRestrict_comp, ← hcomm,
    partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain)]
  exact Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _

/-- A ring isomorphism `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y`, read off a pair
`p : A ⟶ X`, `q : A ⟶ Y` inducing isomorphisms of function fields along which `m` is `q`; it
satisfies `p^* ∘ θ = q^*`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, (functionFieldMap p).comp θ = functionFieldMap q ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, hθ', ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

/-- Two models `p : W ⟶ X`, `a : A ⟶ X` of the same rational map `m : Spec k(X) ⟶ Y`, on which
prime divisors `F_W` and `E` both give the valuation `ord_F` of `k(Y)`, give the same valuation
of `k(X)`. -/
private theorem valuationOver_eq_of_specMap_comp {X Y W A : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral W] [IsIntegral A] [IsLocallyNoetherian W] [IsLocallyNoetherian A]
    [IsNormal W] [IsNormal A] [IsNormal Y] [IsLocallyNoetherian Y]
    (m : Spec X.functionField ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y) (a : A ⟶ X) (pA : A ⟶ Y)
    [IsDominant p] [IsDominant q] [IsDominant a] [IsDominant pA]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Surjective (functionFieldMap q))
    (hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ pA)
    (FW : Mori.PrimeDivisor W) (E : Mori.PrimeDivisor A) (F : Mori.PrimeDivisor Y)
    (hFW : FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation)
    (hE : E.divisorialValuation.comap (functionFieldMap pA) = F.divisorialValuation) :
    FW.valuationOver p = E.valuationOver a := by
  obtain ⟨θ, hθ', hm⟩ := exists_ringHom_of_specMap m p q hp hW
  have hθA : (functionFieldMap a).comp θ = functionFieldMap pA := by
    rw [← hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← functionFieldMap_fromSpecStalk pA] at hA
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hA))
  refine Valuation.ext fun t => ?_
  obtain ⟨s, hs⟩ := hq (functionFieldMap p t)
  obtain rfl : θ s = t := hp.1 (by rw [← RingHom.comp_apply, hθ', hs])
  rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
    ← RingHom.comp_apply (functionFieldMap p) θ, hθ', ← RingHom.comp_apply (functionFieldMap a) θ,
    hθA, ← Valuation.comap_apply, hFW, ← hE, Valuation.comap_apply]

/-- A prime divisor `F_W` of `W` over the generic point of a prime divisor `F` of `Y`, along which
`q : W ⟶ Y` is a local isomorphism, pulls `ord_F` back from `ord_{F_W}`. -/
private theorem comap_divisorialValuation_of_isIso_stalkMap {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian W] [IsLocallyNoetherian Y] [IsNormal W] [IsNormal Y]
    (q : W ⟶ Y) [IsDominant q] (FW : Mori.PrimeDivisor W) (F : Mori.PrimeDivisor Y)
    (heq : q FW.genericPoint = F.genericPoint) [IsIso (q.stalkMap FW.genericPoint)] :
    FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso q FW F heq t]

/-- If `p = g ∘ a` on `a⁻¹(dom g)` for a dominant `a`, then `p = g' ∘ a` on `a⁻¹(dom g')` for
every representative `g'` of the same rational map. -/
private theorem comp_eq_of_toRationalMap_eq {A X Y : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (a : A ⟶ X) [IsDominant a] (p : A ⟶ Y) (g g' : X.PartialMap Y)
    (hgg : g.toRationalMap = g'.toRationalMap)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p = (a ∣_ g.domain) ≫ g.hom) :
    (a ⁻¹ᵁ g'.domain).ι ≫ p = (a ∣_ g'.domain) ≫ g'.hom := by
  let m : A.PartialMap Y :=
    ⟨a ⁻¹ᵁ g'.domain, dense_preimage a g'.dense_domain, (a ∣_ g'.domain) ≫ g'.hom⟩
  have h1 : m.toRationalMap = p.toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      fromFunctionField_morphismRestrict_comp a g',
      ← Scheme.RationalMap.fromFunctionField_toRationalMap, ← hgg,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      specMap_functionFieldMap_fromFunctionField a g p hcomm,
      MMP.Flips.RationalMap.fromFunctionField_hom]
  exact ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)).symm

/-- If `p = g ∘ a` on `a⁻¹(dom g)`, then `p(z) = g(a(z))` for every `z` with `a(z) ∈ dom g`. -/
private theorem apply_eq_of_comp_eq {A X Y : Scheme.{u}} (a : A ⟶ X) (p : A ⟶ Y)
    (g : X.PartialMap Y) {z : A} (hz : a z ∈ g.domain)
    (hV : (a ⁻¹ᵁ g.domain).ι ≫ p = (a ∣_ g.domain) ≫ g.hom) : p z = g.hom ⟨a z, hz⟩ := by
  let v : (a ⁻¹ᵁ g.domain).toScheme := ⟨z, show z ∈ a ⁻¹ᵁ g.domain from hz⟩
  have h1 : ((a ⁻¹ᵁ g.domain).ι ≫ p) v = ((a ∣_ g.domain) ≫ g.hom) v := by rw [hV]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    show (a ∣_ g.domain) v = ⟨a z, hz⟩ from Subtype.ext (morphismRestrict_base_coe _ _ _)] at h1

/-- If `p = h ∘ a` near `z` and the stalk map of `p` at `z` is an isomorphism, then the stalk map
of `a` at `z` is onto: `𝒪_{Y,p(z)} ⟶ 𝒪_{X,a(z)} ⟶ 𝒪_{A,z}` is the stalk map of `p`. -/
private theorem surjective_stalkMap_of_comp_eq {A X Y : Scheme.{u}} (a : A ⟶ X) (p : A ⟶ Y)
    (U : X.Opens) (h : U.toScheme ⟶ Y) (hV : (a ⁻¹ᵁ U).ι ≫ p = (a ∣_ U) ≫ h) (z : A)
    (hz : a z ∈ U) [IsIso (p.stalkMap z)] : Function.Surjective (a.stalkMap z) := by
  let v : (a ⁻¹ᵁ U).toScheme := ⟨z, show z ∈ a ⁻¹ᵁ U from hz⟩
  haveI h1 : IsIso ((a ⁻¹ᵁ U).ι.stalkMap v) :=
    inferInstanceAs <| IsIso ((a ⁻¹ᵁ U).ι.toLRSHom.stalkMap v)
  haveI h2 : IsIso (p.stalkMap ((a ⁻¹ᵁ U).ι v)) := ‹IsIso (p.stalkMap z)›
  haveI h3 : IsIso (((a ⁻¹ᵁ U).ι ≫ p).stalkMap v) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso' h2 h1
  haveI h4 : IsIso (((a ∣_ U) ≫ h).stalkMap v) := by
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hV v] at h3
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (by infer_instance) h3
  haveI h5 : IsIso (h.stalkMap ((a ∣_ U) v) ≫ (a ∣_ U).stalkMap v) := by
    rwa [← Scheme.Hom.stalkMap_comp]
  have s2 : Function.Surjective ((a ∣_ U).stalkMap v).hom := by
    have hb := (ConcreteCategory.bijective_of_isIso
      (h.stalkMap ((a ∣_ U) v) ≫ (a ∣_ U).stalkMap v)).2
    rw [ConcreteCategory.coe_comp] at hb
    exact hb.of_comp
  have e := Arrow.iso_w' (morphismRestrictStalkMap a U v)
  change Function.Surjective (a.stalkMap v.1).hom
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp
    (s2.comp (ConcreteCategory.bijective_of_isIso _).2)

/-- The transform of a prime divisor `P` under `φ`, when `φ` is defined at `η_P`, is the closure
of the image of `η_P`. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm (closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed) ?_
    change P.support ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
    change P.genericPoint ∈ P.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- A prime divisor `P` whose generic point is sent by `φ` to the generic point of `E` is
transformed into `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- **The center of an extracted divisor lies outside the domain of `φ`.** If a divisor `E` over
`X` realizes a `φ⁻¹`-exceptional prime divisor `F` of `Y` through `φ`, then `φ` is not defined at
the image `h(η_E)` of the generic point of `E`. -/
private theorem map_genericPoint_notMem_domain {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hXn : Mori.IsNormalVariety k sX) (hYn : Mori.IsNormalVariety k sY)
    {φ : X.RationalMap Y} {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) :
    E.f E.E.genericPoint ∉ φ.domain := by
  intro hxd
  obtain ⟨g', hxg', hg'⟩ := Scheme.RationalMap.mem_domain.mp hxd
  obtain ⟨g, p, hp, hgφ, hcomm, hval⟩ := hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := hp.isDominant
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI := isSeparated_toTerminal sY
  have hV := comp_eq_of_toRationalMap_eq E.f p g g' (hgφ.trans hg'.symm) hcomm
  set η := E.E.genericPoint with hη
  -- `p(η_E) = φ(h(η_E))`
  have hpη : p η = g'.hom ⟨E.f η, hxg'⟩ :=
    apply_eq_of_comp_eq E.f p g' hxg' hV
  -- `p(η_E)` is the center of `ord_F` on `Y`, so it is `η_F`
  have hpF : p η = F.genericPoint := by
    refine MMP.Positivity.DivisorOver.eq_of_dominates sY F.divisorialValuation ?_ ?_ ?_ ?_
    · intro b
      rw [← hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
        Mori.PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨_, rfl⟩
    · intro b hb
      rw [← hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
        Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 hb (isUnit_of_map_unit _ _ hu)
    · intro b
      rw [Mori.PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨b, rfl⟩
    · intro b hb
      exact (F.divisorialValuation_algebraMap_lt_one_iff b).2 hb
  -- `𝒪_{X,h(η_E)} ≅ 𝒪_{V,E}`: the stalk map of `h` is injective, and onto since `𝒪_{Y,η_F}`
  -- is a valuation ring through which the stalk map of `p` factors
  haveI : ValuationRing (Y.presheaf.stalk (p η)) := by
    rw [hpF]
    haveI := F.isDiscreteValuationRing_localRing
    infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing p hp.functionFieldMap_bijective η
  have hsurj := surjective_stalkMap_of_comp_eq E.f p g'.domain g'.hom hV η hxg'
  have hinj : Function.Injective (E.f.stalkMap η) := by
    intro b b' hbb
    have := congrArg (algebraMap (E.Y.presheaf.stalk η) E.Y.functionField) hbb
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk,
      ← MMP.Mori.functionFieldMap_algebraMap_stalk] at this
    exact IsFractionRing.injective _ _ ((functionFieldMap E.f).injective this)
  have hdim : Order.coheight (E.f η) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective (E.f.stalkMap η).hom ⟨hinj, hsurj⟩)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      E.E.coheight_genericPoint] at h1
    exact_mod_cast h1
  -- so `h(η_E)` is the generic point of a prime divisor `P` of `X`, and `φ_* P = F`
  have hc : ¬ 2 ≤ codimension E.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center, hdim]
    decide
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hXn] at hc
  push Not at hc
  obtain ⟨P, hvP⟩ := hc
  have hxP : E.f η = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXn.1 hvP
  refine hF P (transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' (hxP ▸ hxg') ?_)
  rw [← hpF, hpη]
  congr 1
  exact Subtype.ext hxP

end Realized

section CommonModel'

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- **A morphism agreeing with a rational map at the generic point agrees with each of its
representatives.** Let `a : W ⟶ X` be dominant, `b : W ⟶ Y`, and `χ : X ⤏ Y` with
`χ ∘ a = b` at the generic point of `W`. Then for every representative `g` of `χ`,
`b = g ∘ a` on `a⁻¹(dom g)`. -/
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] (a : W ⟶ X) [IsDominant a] (b : W ⟶ Y)
    (χ : X.RationalMap Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ χ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ b)
    (g : X.PartialMap Y) (hg : g.toRationalMap = χ) :
    (a ⁻¹ᵁ g.domain).ι ≫ b = (a ∣_ g.domain) ≫ g.hom := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense _ g.dense_domain
  have hA : genericPoint W ∈ a ⁻¹ᵁ g.domain := genericPoint_mem_preimage a g.dense_domain
  refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint W) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
    Category.assoc, ← partialMap_fromFunctionField_eq g hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg]
  exact H.symm

/-- If `θ` induces `φ` at the generic points and `ψ` is inverse to `φ`, then
`Spec k(X) ⟶ Spec k(Y) ⟶ X` along `θ` and `ψ` is the canonical map. -/
private theorem specMap_comp_fromFunctionField_of_isInverse {X M : Scheme.{u}} [IsIntegral X]
    [IsIntegral M] {φ : X.RationalMap M} {ψ : M.RationalMap X}
    (hinv : Mori.RationalMap.IsInverse φ ψ) (θ : M.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ M.fromSpecStalk (genericPoint M) =
      φ.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ) ≫ ψ.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_dense _ e.dense_source
  have hy : genericPoint M ∈ e.target := genericPoint_mem_of_dense _ e.dense_target
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint M) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ) ≫ e.target.fromSpecStalkOfMem (genericPoint M) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ, hφ,
      Category.assoc]
  rw [hψ, ← Category.assoc, c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- If `φ_*P = E` and `g` is a representative of `φ` defined at `η_P`, then `η_E = g(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- **A common model maps points compatibly.** If `q = φ ∘ p` at the generic point of `W`, then
for every representative `g` of `φ` defined at `x = p(w)`, `q(w) = g(x)`. -/
private theorem apply_eq_hom_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) {w : W} {x : X} (hx : x ∈ g.domain)
    (hp : p w = x) : q w = g.hom ⟨x, hx⟩ := by
  let w' : (p ⁻¹ᵁ g.domain).toScheme := ⟨w, show p w ∈ g.domain from hp ▸ hx⟩
  calc q w = ((p ⁻¹ᵁ g.domain).ι ≫ q) w' := rfl
    _ = g.hom ((p ∣_ g.domain) w') := by
      rw [comp_eq_of_specMap_fromFunctionField_eq p q φ H g hg]; rfl
    _ = g.hom ⟨x, hx⟩ :=
      congrArg g.hom (Subtype.ext ((morphismRestrict_base_coe p g.domain w').trans hp))

/-- **Strict transforms on a common model.** If `q = φ ∘ p` at the generic point of `W` and
`φ_*Q = Q'`, then every point of `W` over `η_Q` lies over `η_{Q'}`. -/
private theorem apply_eq_genericPoint_of_transformPrimeDivisor_eq_some {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hT : Mori.RationalMap.transformPrimeDivisor φ Q = some Q') {w : W}
    (hp : p w = Q.genericPoint) : q w = Q'.genericPoint := by
  obtain ⟨g, hQg, hg⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hT).1
  exact (apply_eq_hom_of_specMap_fromFunctionField_eq H g hg hQg hp).trans
    (genericPoint_eq_of_transformPrimeDivisor_eq_some hT g hg hQg).symm

/-- The stalk of `Y` at the generic point of a prime divisor is a valuation ring. -/
private theorem valuationRing_stalk_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (Q : Mori.PrimeDivisor Y) {y : Y}
    (h : y = Q.genericPoint) : ValuationRing (Y.presheaf.stalk y) := by
  have := Q.isDiscreteValuationRing_localRing
  subst h
  infer_instance

/-- A birational morphism mapping `w` to the generic point of a prime divisor is a local
isomorphism at `w`. -/
private theorem isIso_stalkMap_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w : W}
    (h : q w = Q.genericPoint) : IsIso (q.stalkMap w) :=
  have := valuationRing_stalk_of_eq_genericPoint Q h
  MMP.Positivity.isIso_stalkMap_of_valuationRing q hq w

/-- A separated birational morphism has at most one point over the generic point of a prime
divisor. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w₁ w₂ : W}
    (h₁ : q w₁ = Q.genericPoint) (h₂ : q w₂ = Q.genericPoint) : w₁ = w₂ :=
  have := valuationRing_stalk_of_eq_genericPoint Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₂
  MMP.Positivity.eq_of_isIso_stalkMap q hq (h₂.trans h₁.symm)

end CommonModel'

/-! ### The strict inequality on a common model -/

/-- An `f`-ample `ℝ`-Cartier divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {g : Y ⟶ Z} {A : RDivisor Y} (hA : IsRelativelyAmple g A) :
    IsRelativelyNef k sY g A := by
  obtain ⟨m, r, L, -, -, hL, rfl⟩ := id hA
  exact ⟨m, r, L, fun j => (hL j).1, rfl, fun C hC x hx => (pos_of_isRelativelyAmple hA C hC hx).le⟩

/-- `structureVia q s` is separated when `Y` is separated over `k` through some `sY`. -/
private theorem isSeparated_structureVia {k : Type u} [Field k] {W Y : Scheme.{u}} (q : W ⟶ Y)
    [IsIso q.appTop] (s : W ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] :
    IsSeparated (structureVia q s) := by
  haveI := isSeparated_toTerminal sY
  have e : structureVia q s ≫ (Spec (.of k) ↘ ⊤_ Scheme) = Y ↘ ⊤_ Scheme :=
    Limits.terminal.hom_ext _ _
  haveI : IsSeparated (structureVia q s ≫ (Spec (.of k) ↘ ⊤_ Scheme)) := by
    rw [e]; infer_instance
  exact IsSeparated.of_comp _ (Spec (.of k) ↘ ⊤_ Scheme)

/-- **Divisors of top forms for two structures of a variety.** On a normal integral scheme with
two structures `s₁, s₂` of a normal variety of dimension `n` over a field of characteristic zero,
the divisors of nonzero rational `n`-forms for `s₁` and for `s₂` are linearly equivalent. -/
private theorem linearlyEquivalent_divisorOfForm_of_isNormalVariety {k : Type u} [Field k]
    [CharZero k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {s₁ s₂ : W ⟶ Spec (.of k)} (h₁ : IsNormalVariety k s₁)
    (h₂ : IsNormalVariety k s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] {n : ℕ}
    (hn : topologicalKrullDim W = n) {τ₁ : RationalPluriForms s₁ n 1}
    {τ₂ : RationalPluriForms s₂ n 1} (hτ₁ : τ₁ ≠ 0) (hτ₂ : τ₂ ≠ 0) :
    (divisorOfForm τ₁).LinearlyEquivalent (divisorOfForm τ₂) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := exists_ordForm_sub_eq s₁ s₂ h₁ h₂ hn hτ₁ hτ₂
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero hc₁ (inv_ne_zero hc₂))
  refine ⟨φ, ?_⟩
  ext Γ
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul hc₁ (inv_ne_zero hc₂),
    ← zpow_neg_one, ord_zpow _ hc₂, coeff_divisorOfForm, coeff_divisorOfForm]
  have := h Γ
  linarith

/-- **FA 2.23.3, along the divisors that are not exceptional over the source.** Let
`g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of `f : (X, D_X) ⟶ Z` through `φ`, and
`p : W ⟶ X`, `q : W ⟶ Y` proper birational morphisms from a normal variety with `q = φ ∘ p` at the
generic point. For a prime divisor `P` of `W` not exceptional over `X`,
`a(ord_P, D_X) ≤ a(ord_P, D_{𝓕,Y})`. -/
private theorem isDiscrepancy_le_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (KF : haveI := hpb.isDominant
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
        W.fromSpecStalk (genericPoint W) ≫ q)
    (P : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hWp, isBirationalMorphism := hpb, E := P,
        isProper := inferInstance }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hWq, isBirationalMorphism := hqb, E := P,
        isProper := inferInstance }
    ¬ EX.IsExceptional →
      ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
        IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  intro EX EY hEX a a' ha ha'
  obtain ⟨-, -, -, hFB, -, -, hexc⟩ := hM
  obtain ⟨hXn, hYn, hφb, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI := isSeparated_toTerminal sX
  haveI := isSeparated_toTerminal sY
  -- `Q = p(P)` is a prime divisor of `X` with `ord_P = ord_Q`.
  obtain ⟨Q, -, hpQ, -, hEXv⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXn EX hEX
  change p P.genericPoint = Q.genericPoint at hpQ
  rw [hEXv] at ha'
  rcases hT : Mori.RationalMap.transformPrimeDivisor φ Q with _ | Q'
  · -- `φ_*Q = 0`: the inequality is part of the definition of a weak log canonical model.
    obtain ⟨θ, hθq, hθ⟩ := exists_ringHom_of_specMap _ p q hpbij KF
    have hψθ := specMap_comp_fromFunctionField_of_isInverse hφb.isInverse_inverse θ hθ
    have KF' : Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫
        hφb.inverse.fromFunctionField = W.fromSpecStalk (genericPoint W) ≫ p := by
      rw [← hθq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψθ]
      exact functionFieldMap_fromSpecStalk p
    obtain ⟨g', hg'⟩ := hφb.inverse.exists_rep
    exact hexc hφb Q hT EY a a' ⟨g', p, hpb, hg',
      comp_eq_of_specMap_fromFunctionField_eq q p _ KF' g' hg', hEXv⟩ ha ha'
  · -- `φ_*Q = Q'`: both discrepancies are `-coeff_Q(D_X)`.
    have himg {Q₁ : Mori.PrimeDivisor X}
        (hT₁ : Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q')
        {w : W} (hw : p w = Q₁.genericPoint) : q w = Q'.genericPoint :=
      apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT₁ hw
    have hqP := himg hT hpQ
    have : IsIso (q.stalkMap P.genericPoint) :=
      isIso_stalkMap_of_apply_eq_genericPoint q hqbij Q' hqP
    rw [show EY.valuation = Q'.divisorialValuation from
      comap_divisorialValuation_of_isIso_stalkMap q P Q' hqP] at ha
    -- `Q` is the only prime divisor of `X` with `φ_*Q = Q'`.
    have huniq : ∀ Q₁, Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q' → Q₁ = Q := by
      intro Q₁ hT₁
      obtain ⟨P₁, hp₁, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWp hpb Q₁
      have heq := eq_of_apply_eq_genericPoint q hqbij Q' hqP (himg hT₁ hp₁)
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp₁.symm.trans (heq ▸ hpQ))
    have hQ'Fs : Q' ∉ Fs := fun h => (hFs Q').mp h Q hT
    have hcoef : G.coeff Q' = D_X.coeff Q := by
      rw [hG]
      change (Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F)) Q' =
        D_X Q
      rw [Finsupp.add_apply, Finsupp.finset_sum_apply,
        Finset.sum_eq_zero fun F hF =>
          Finsupp.single_eq_of_ne' fun h : F = Q' => hQ'Fs (h ▸ hF),
        add_zero]
      exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hT huniq D_X
    have h1 := ha.eq_neg_coeff
    have h2 := ha'.eq_neg_coeff
    linarith

/-- If `φ` is not defined at `p(η_{P₀})` and `Δ` is an effective `ℝ`-Cartier combination with
`-Δ` `p`-nef and coefficient `0` along `P₀`, some proper curve contracted by `p` but not by `q`
misses `Supp Δ`. -/
private theorem exists_properCurve_notMem_supp {k : Type u} [Field k] {X Y W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {φ : X.RationalMap Y} {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q]
    (hXn : IsNormalVariety k sX) (hWp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (KF : haveI := hpb.isDominant
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
        W.fromSpecStalk (genericPoint W) ≫ q)
    {P₀ : Mori.PrimeDivisor W} (hx : p P₀.genericPoint ∉ φ.domain) {Δ : RDivisor W}
    (hBc : IsCartierCombination Δ) (hΔeff : Δ.IsEffective)
    (hnegnef : IsRelativelyNef k (p ≫ sX) p (-Δ)) (hc0 : Δ.coeff P₀ = 0) :
    ∃ C : ProperCurve (p ≫ sX), C.IsContractedBy p ∧ ¬ C.IsContractedBy q ∧
      C.point ∉ (Δ.supp : Set W) := by
  haveI := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  haveI : IsDominant p := hpb.isDominant
  -- the fibre over the generic point `x` of the center misses `Supp Δ`
  have hdisj : Disjoint (p.base ⁻¹' {p P₀.genericPoint})
      (Δ.supp : Set W) :=
    (preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k sX (p ≫ sX) hXn hWp p
      rfl hpb hBc hΔeff hnegnef (p P₀.genericPoint)).resolve_left
      fun hsub => genericPoint_notMem_supp_of_coeff_eq_zero hc0 (hsub rfl)
  -- a closed point `y` of `closure {x}` whose fibre misses `Supp Δ`
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hSc : IsClosed (p '' (Δ.supp : Set W)) :=
    p.isClosedMap _ Δ.supp.isClosed
  have hxS : p P₀.genericPoint ∉ p '' (Δ.supp : Set W) := by
    rintro ⟨w, hw, hwx⟩
    exact Set.disjoint_left.mp hdisj (show p w ∈ ({p P₀.genericPoint} : Set X) from hwx) hw
  obtain ⟨y, ⟨hyT, hyS⟩, hyc⟩ := nonempty_inter_closedPoints
    (⟨p P₀.genericPoint, subset_closure rfl, hxS⟩ : (closure {p P₀.genericPoint} ∩
      (p '' (Δ.supp : Set W))ᶜ).Nonempty)
    (isClosed_closure.isLocallyClosed.inter hSc.isOpen_compl.isLocallyClosed)
  have hyφ : y ∉ φ.domain := fun hy =>
    hx ((specializes_iff_mem_closure.mpr hyT).mem_open φ.domain.2 hy)
  have hyfib : ∀ w, p w = y → w ∉ (Δ.supp : Set W) :=
    fun w hw hwS => hyS ⟨w, hwS, hw⟩
  -- `q` is not constant on `p⁻¹(y)`, since `φ` is not defined at `y`
  have hiso : ∀ U : X.Opens, IsIso (p.app U) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (p ≫ sX) sX hWp.1
      hXn p hpb).1
  have hconst : ∀ c : Y, ¬ ∀ w, p w = y → q w = c := fun c hc =>
    hyφ (mem_domain_of_forall_eq φ p q hpb.functionFieldMap_bijective hiso KF hc)
  haveI : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (p ≫ sX)
  have hyc' : IsClosed ({y} : Set X) := mem_closedPoints_iff.mp hyc
  have hFcl : IsClosed (p.base ⁻¹' {y}) := hyc'.preimage p.continuous
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  obtain ⟨w', hw'⟩ := Surjective.surj (f := p) y
  obtain ⟨w₀, hw₀F, hw₀c⟩ := nonempty_inter_closedPoints
    (⟨w', hw'⟩ : (p.base ⁻¹' {y}).Nonempty) hFcl.isLocallyClosed
  obtain ⟨w₁, hw₁, hqw₁⟩ : ∃ w₁, p w₁ = y ∧ q w₁ ≠ q w₀ := by
    by_contra! h
    exact hconst (q w₀) h
  have hqcl : IsClosed ({q w₀} : Set Y) := by
    rw [← Set.image_singleton]
    exact q.isClosedMap _ (mem_closedPoints_iff.mp hw₀c)
  have hS'c : IsClosed (p.base ⁻¹' {y} ∩ q.base ⁻¹' {q w₀}) :=
    hFcl.inter (hqcl.preimage q.continuous)
  -- a proper curve `C ⊆ p⁻¹(y)` meeting `q⁻¹(q w₀)` without lying in it
  obtain ⟨C, hCp, hCS, c₀, hc₀R, hc₀S⟩ := exists_properCurve_isContractedBy k sX (p ≫ sX) hXn hWp p
    rfl hpb y hyc' hS'c ⟨w₀, hw₀F, hw₀F, rfl⟩
    fun h => hqw₁ (h (show w₁ ∈ p.base ⁻¹' {y} from hw₁)).2
  rw [C.range_ι] at hCS hc₀R
  have hpC : p C.point = y := (hCp c₀ hc₀R).symm.trans hc₀S.1
  have hCq : ¬ C.IsContractedBy q := fun hq' => hCS fun z hz =>
    ⟨(hCp z hz).trans hpC, (hq' z hz).trans ((hq' c₀ hc₀R).symm.trans hc₀S.2)⟩
  exact ⟨C, hCp, hCq, hyfib _ hpC⟩

/-- Let `G_X = p^*N_X` and `G_Y = q^*N_Y` with `N_Y` `g`-ample, `L` principal, and
`G_X - G_Y + L` effective. A proper curve contracted by `p` but not by `q` meets its support. -/
private theorem mem_supp_of_not_isContractedBy {k : Type u} [Field k] {X Y Z W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsSeparated t]
    [LocallyOfFiniteType t] [QuasiCompact t] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q] [QuasiCompact (p ≫ sX)] {f : X ⟶ Z}
    {g : Y ⟶ Z} (hWp : IsNormalVariety k (p ≫ sX)) (hcomm : p ≫ f = q ≫ g)
    (htq : q ≫ t = p ≫ sX) {N_X : RDivisor X} {N_Y : RDivisor Y} {G_X G_Y : RDivisor W}
    {L : Divisor W} (hGX : IsRCartierPullback p N_X G_X) (hGY : IsRCartierPullback q N_Y G_Y)
    (hNY : IsCartierCombination N_Y) (hamp : IsRelativelyAmple g N_Y)
    (hL : L.LinearlyEquivalent 0) (hLc : IsCartierCombination (Divisor.toRDivisor L))
    (hBc : IsCartierCombination (G_X - G_Y + Divisor.toRDivisor L))
    (hΔ : (G_X - G_Y + Divisor.toRDivisor L).IsEffective) (C : ProperCurve (p ≫ sX))
    (hCp : C.IsContractedBy p) (hCq : ¬ C.IsContractedBy q) :
    C.point ∈ ((G_X - G_Y + Divisor.toRDivisor L).supp : Set W) := by
  by_contra hCsupp
  -- `q(C)` is a proper curve contracted by `g`
  have hCpg : C.IsContractedBy (q ≫ g) := hcomm ▸ isContractedBy_comp f hCp
  let C' : ProperCurve t := ⟨q C.point, isProperCurve_map q htq C hCq⟩
  have hC'g : C'.IsContractedBy g := isContractedBy_of_comp q g C C' rfl hCpg
  -- the intersection numbers with `C`
  obtain ⟨_, _, _, x₁, hx₁⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hGX) C
  obtain ⟨_, _, _, x₂, hx₂⟩ :=
    exists_isRIntersectionNumber (k := k) (isCartierCombination_of_isRCartierPullback hGY) C
  obtain ⟨_, _, _, x₃, hx₃⟩ := exists_isRIntersectionNumber (k := k) hBc C
  obtain ⟨_, _, _, y₂, hy₂⟩ := exists_isRIntersectionNumber (k := k) hNY C'
  have e₁ : x₁ = 0 :=
    isRIntersectionNumber_pullback_eq_zero_of_isContractedBy p rfl hGX C hCp hx₁
  have e₂ : x₂ = residueFieldDegree q C.point * y₂ :=
    isRIntersectionNumber_pullback_eq_mul q htq hGY C C' rfl hx₂ hy₂
  have hy₂pos : 0 < y₂ := pos_of_isRelativelyAmple hamp C' hC'g hy₂
  have hdeg : (0 : ℝ) < residueFieldDegree q C.point :=
    Nat.cast_pos.mpr (residueFieldDegree_pos q htq C hCq)
  have e₃ : x₃ = x₁ - x₂ := isRIntersectionNumber_sub_add_eq hLc C
    (fun hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL C hx) hx₁ hx₂ hx₃
  have h₃ : 0 ≤ x₃ :=
    IsRIntersectionNumber.nonneg_of_isEffective k (p ≫ sX) hWp _ hBc hΔ C hCsupp _ _ hx₃
  nlinarith [mul_pos hdeg hy₂pos]

/-- **FA 2.23.3, strict form, on a common model.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical
model of `f : (X, D_X) ⟶ Z` through `φ`, `p : W ⟶ X`, `q : W ⟶ Y` proper birational morphisms
from a normal variety with `p ≫ f = q ≫ g` and `q = φ ∘ p` at the generic point, and `P` a prime
divisor of `W` such that `φ` is not defined at `p(η_P)`. Then `a(ord_P, D_{𝓕,Y}) > a(ord_P, D_X)`.
On `W`, `Δ = p^*(K_X + D_X) - q^*(K_Y + D_{𝓕,Y}) + (div_W(q^*ω_Y) - div_W(p^*ω_X))` is effective
with coefficients `a(·, D_{𝓕,Y}) - a(·, D_X)`, and `-Δ` is `p`-nef; if its coefficient along `P`
vanished, a fibre of `p` missing `Supp Δ` would contain a proper curve `C` not contracted by `q`,
with `Δ · C ≥ 0` but `Δ · C = -q^*(K_Y + D_{𝓕,Y}) · C < 0`. -/
private theorem isDiscrepancy_lt_of_commonModel {k : Type u} [Field k] [CharZero k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {p : W ⟶ X} {q : W ⟶ Y} [IsProper p]
    [IsProper q] (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sY))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (KF : haveI := hpb.isDominant
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
        W.fromSpecStalk (genericPoint W) ≫ q)
    (hcomm : p ≫ f = q ≫ g) (P₀ : Mori.PrimeDivisor W) (hx : p P₀.genericPoint ∉ φ.domain) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hWp, isBirationalMorphism := hpb, E := P₀,
        isProper := inferInstance }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hWq, isBirationalMorphism := hqb, E := P₀,
        isProper := inferInstance }
    ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
      IsDiscrepancy sX n K_X D_X EX.valuation a' → a' < a := by
  intro EX EY a a' ha ha'
  obtain ⟨-, -, -, ⟨hXn, hYn, -⟩, -, -, -⟩ := id hM.1
  obtain ⟨-, -, hamp⟩ := hM.2
  haveI := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  haveI := hWq.1.toLocallyOfFiniteType
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  -- a structure `t` of `Y` over `k` with `q ≫ t = p ≫ sX`
  haveI : IsIso q.appTop :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (q ≫ sY) sY
      hWq.1 hYn q hqb).1 ⊤
  haveI : Surjective q :=
    surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  let t := structureVia q (p ≫ sX)
  have htq : q ≫ t = p ≫ sX := comp_structureVia q _
  haveI : LocallyOfFiniteType t := locallyOfFiniteType_structureVia q (p ≫ sX) sY
  haveI : IsSeparated t := isSeparated_structureVia q _ sY
  haveI : QuasiCompact t := quasiCompact_of_compactSpace t
  -- the forms `ω_X`, `ω_Y` with `K_X = div ω_X`, `K_Y = div ω_Y` used in the discrepancies
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha'
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := sX), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  -- `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms sY q ωY) -
        divisorOfForm (pullbackRationalPluriForms sX p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_isNormalVariety hWq hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  -- `p^*(K_X + D_X) - q^*(K_Y + G) + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  -- `a(P, D_X) = ord_P(p^*ω_X) - coeff_P(G_X)` and likewise over `Y`
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ωX) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ωX hwX.2.2.1 hKXc hBXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hwY.2.2.1 hKYc hBYc q hWq hqb hGY P
  -- `Δ = p^*(K_X + D_X) - q^*(K_Y + G) + L₁`
  set Δ : RDivisor W := G_X - G_Y + Divisor.toRDivisor L₁ with hΔ
  have hcoeff : ∀ P, Δ.coeff P =
      (dY.coeff P - G_Y.coeff P) - (dX.coeff P - G_X.coeff P) := by
    intro P
    rw [hΔ, hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  -- `M = q^*(K_Y + G) - L₁` is `p`-nef
  have hL₁r := isCartierCombination_toRDivisor_of_linearlyEquivalent_zero hL₁
  have hMnef : IsRelativelyNef k (p ≫ sX) p (G_Y - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_eq_zero (isRelativelyNef_of_comp f (by
      rw [hcomm]; exact isRelativelyNef_of_isRCartierPullback q htq g
        (isRelativelyNef_of_isRelativelyAmple (sY := t) hamp) hGY)) hL₁r
      fun C _ _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁ C hx
  -- the coefficients along prime divisors not exceptional over `X` are nonnegative
  have hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sX p P →
      0 ≤ Δ.coeff P := by
    intro P hP
    rw [hcoeff P, sub_nonneg]
    exact isDiscrepancy_le_of_not_isExceptional hM.1 hWp hWq hpb hqb KF P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
  have hMc := isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hL₁r
  have hBc := isCartierCombination_add (isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGX)
    (isCartierCombination_of_isRCartierPullback hGY)) hL₁r
  have hnum : IsNumericallyEquivalentOver k (p ≫ sX) p G_X
      ((G_Y - Divisor.toRDivisor L₁) + Δ) := by
    rw [hΔ, sub_add_add_cancel, add_sub_cancel]
    exact isNumericallyEquivalentOver_self (isCartierCombination_of_isRCartierPullback hGX)
  -- the negativity lemma: `Δ` is effective
  have hΔeff := isEffective_of_isNumericallyEquivalentOver_pullback k sX (p ≫ sX) hXn hWp p rfl
    hpb hBXc hGX hMc hMnef hBc hBG hnum
  have haP : a = dY.coeff P₀ - G_Y.coeff P₀ := ha.eq (haY P₀)
  have ha'P : a' = dX.coeff P₀ - G_X.coeff P₀ := ha'.eq (haX P₀)
  have hle : a' ≤ a := by
    linarith [hΔeff P₀, hcoeff P₀]
  refine lt_of_le_of_ne hle fun heq => ?_
  have hc0 : Δ.coeff P₀ = 0 := by
    rw [hcoeff P₀]
    linarith
  -- `-Δ` is `p`-nef, as `p^*(K_X + D_X)` is trivial on the curves contracted by `p`
  have hnegnef : IsRelativelyNef k (p ≫ sX) p (-Δ) := by
    have e : -Δ = (G_Y - Divisor.toRDivisor L₁) - G_X := by
      rw [hΔ]
      abel
    rw [e]
    exact isRelativelyNef_sub_of_eq_zero hMnef (isCartierCombination_of_isRCartierPullback hGX)
      fun C hC _ _ _ _ hx =>
        isRIntersectionNumber_pullback_eq_zero_of_isContractedBy p rfl hGX C hC hx
  obtain ⟨C, hCp, hCq, hCsupp⟩ :=
    exists_properCurve_notMem_supp hXn hWp hpb KF hx hBc hΔeff hnegnef hc0
  exact hCsupp (mem_supp_of_not_isContractedBy hWp hcomm htq hGX hGY hBYc hamp hL₁ hL₁r hBc hΔeff
    C hCp hCq)

/-! ### Divisors extracted by a log canonical model -/

/-- **FA 2.22.4.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of `f : (X, D_X) ⟶ Z`
through `φ`, and `F` a `φ⁻¹`-exceptional prime divisor of `Y`, realized over `X` by a divisor `E`.
Then every value `a` of `a(E, D_X)` is `< -1`. On a common normal model `(W, p, q)` of `φ`, the
strict transform `F_W` of `F` realizes `ord_F`; `φ` is not defined at `p(η_{F_W})`, so
`a(E, D_X) < a(ord_F, D_{𝓕,Y}) = -c_F`, and admissibility of `𝓕` forces `-a(E, D_X) > 1`. -/
private theorem lt_neg_one_of_isInverseExceptional {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) {a : ℝ}
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) : a < -1 := by
  obtain ⟨hfP, hgP, hmod, hFB, hKG, hRel, -⟩ := id hM.1
  obtain ⟨hXn, hYn, -, -, -, -, _, hFs, -, hc, -⟩ := id hFB
  obtain ⟨-, hcmin⟩ := hc F ((hFs F).2 hF)
  haveI := hfP
  haveI := hgP
  -- a common normal model `(W, p, q)` of `φ` over `Z`
  obtain ⟨W, p, q, hWp, hpP, hqP, hpb, hqb, ⟨φ', hφ', hrel⟩, hcomm⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism hXn hYn f g φ hmod.1 hmod.2
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hYn.1.toIsSeparated
  haveI := hYn.1.toQuasiCompact
  have hWqv : AlgebraicGeometry.IsVariety k (q ≫ sY) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance }
  have hWq : IsNormalVariety k (q ≫ sY) := ⟨hWqv, inferInstance⟩
  have KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q :=
    hφ' ▸ specMap_functionFieldMap_fromFunctionField p φ' q hrel
  -- the strict transform `F_W` of `F` realizes `F` over `X`
  obtain ⟨FW, hFWeq, hFWiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn hWq hqb F
  have hFW := comap_divisorialValuation_of_isIso_stalkMap q FW F hFWeq
  let E' : ProperDivisorOver k sX :=
    { Y := W, f := p, isNormalVariety := hWp, isBirationalMorphism := hpb, E := FW,
      isProper := inferInstance }
  have hE' : IsRealizedOver sX φ F E' := ⟨φ', q, hqb, hφ', hrel, hFW⟩
  have hx : p FW.genericPoint ∉ φ.domain := map_genericPoint_notMem_domain hXn hYn hF hE'
  -- `E'` and `E` give the same valuation of `k(X)`
  obtain ⟨g₀, pE, hpE, hg₀, hcE, hval⟩ := id hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := hpE.isDominant
  have hA : Spec.map (CommRingCat.ofHom (functionFieldMap E.f)) ≫ φ.fromFunctionField =
      E.Y.fromSpecStalk (genericPoint E.Y) ≫ pE :=
    hg₀ ▸ specMap_functionFieldMap_fromFunctionField E.f g₀ pE hcE
  have hv := valuationOver_eq_of_specMap_comp φ.fromFunctionField p q E.f pE
    hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective.2 KF hA FW E.E F hFW hval
  have ha' : IsDiscrepancy sX n K_X D_X E'.valuation a := by
    have hv' : E'.valuation = E.valuation := hv
    rw [hv']
    exact ha
  -- `a(ord_F, D_{𝓕,Y}) = -c F`
  have hb := IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hRel.2.1.2.1 hKG hF
  have hb' : IsDiscrepancy sY n K_Y G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, FW⟩ inferInstance).valuation (-c F) := by
    have hv' : (ProperDivisorOver.mk ⟨W, q, hWq, hqb, FW⟩ inferInstance :
        ProperDivisorOver k sY).valuation = F.divisorialValuation := hFW
    rw [hv']
    exact hb
  have hlt := isDiscrepancy_lt_of_commonModel hM hWp hWq hpb hqb KF hcomm FW hx (-c F) a hb' ha'
  have hmin := hcmin E a hE ha
  by_contra h
  rw [min_eq_right (by linarith)] at hmin
  linarith

/-- Every divisor `(W, p, P)` over `X` has a discrepancy with respect to `D_X`, once `K_X` is a
canonical divisor and `K_X + D_X` is `ℝ`-Cartier. -/
private theorem exists_isDiscrepancy {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} {K : Mori.Divisor X}
    {D_X : Mori.RDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor K + D_X)) (E : ProperDivisorOver k sX) :
    ∃ a : ℝ, IsDiscrepancy sX n K D_X E.valuation a := by
  obtain ⟨ω, hω, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := Finsupp.ext hωK
  subst hdiv
  obtain ⟨⟨W, p, hW, hp, P⟩, hpr⟩ := E
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsDominant p := hp.isDominant
  obtain ⟨Gp, hGp, -⟩ := existsUnique_isRCartierPullback p hKD
  exact ⟨_, isDiscrepancy_ordPullback_sub_coeff_pullback hX ω hω hK hKD p hW hp hGp P⟩

end MMP.Flips.Fa2NoExtractedDivisors

namespace MMP.Flips

/-- **FA 2.24.1.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of `f : (X, D_X) ⟶ Z` with
respect to `𝓕` (`MMP.Flips.IsLogCanonicalModelOf`, with `G = D_{𝓕,Y}`), through the modification
`φ : X ⤏ Y`, over a field of characteristic zero. If `(X, D_X)` is log canonical, then `Y` has no
`φ⁻¹`-exceptional prime divisors, and `D_{𝓕,Y} = φ_* D_X`. -/
@[mmp "lem_fa2_lc_model_no_extracted_divisors"]
public theorem IsLogCanonicalModelOf.not_isInverseExceptional_and_eq_transformDivisor
    {k : Type u} [Field k] [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X}
    {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    (hX : IsLogCanonical sX n K_X D_X) :
    (∀ F : Mori.PrimeDivisor Y, ¬ RationalMap.IsInverseExceptional φ F) ∧
      G = Mori.RationalMap.transformDivisor φ D_X := by
  obtain ⟨hXv, -, -, -, hK, hKD, Fs, hFs, hreal, -, hG⟩ := hM.1.2.2.2.1
  have hno : ∀ F : Mori.PrimeDivisor Y, ¬ RationalMap.IsInverseExceptional φ F := by
    intro F hF
    obtain ⟨E, hE⟩ := hreal F ((hFs F).2 hF)
    obtain ⟨a, ha⟩ := Fa2NoExtractedDivisors.exists_isDiscrepancy hXv hK hKD E
    have h1 := hX.2.2.2 E.valuation ha.2.2.1 a ha
    have h2 := Fa2NoExtractedDivisors.lt_neg_one_of_isInverseExceptional hM hF hE ha
    linarith
  have hFs0 : Fs = ∅ := Finset.eq_empty_of_forall_notMem fun F hF => hno F ((hFs F).1 hF)
  exact ⟨hno, by rw [hG, hFs0, Finset.sum_empty, add_zero]⟩

end MMP.Flips
