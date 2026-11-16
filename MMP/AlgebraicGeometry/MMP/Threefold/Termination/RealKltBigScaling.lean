module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelAmplePerturbation
import MMP.AlgebraicGeometry.MMP.Threefold.MinimalModel.BigBoundaryGeography
import MMP.AlgebraicGeometry.MMP.Threefold.Scaling.NefThresholdRay
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.Morphisms.CurveFactorization
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
import MMP.AlgebraicGeometry.Singularities.KltRelativeBigCore
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
import MMP.AlgebraicGeometry.MMP.MinimalModel.PltReference
import MMP.AlgebraicGeometry.Intersection.RelativeN1FiniteDimensional
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Termination with scaling for real klt threefolds with a big boundary

Let `π : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold, and let `B, C ≥ 0` be `ℝ`-Cartier divisors on `X` such that `(X, B + C)` is klt,
`K_X + B + C` is nef over `Z`, and `B ≥ A` for an effective `ℚ`-divisor `A` which is big over `Z`.
The `(K_X + B)`-program over `Z` with scaling of `C` runs as follows. At a model
`(X_i, B_i, C_i)` let `λ_i = min {t ≥ 0 | K_{X_i} + B_i + t C_i is nef over Z}`. If `λ_i > 0`,
contract over `Z` a `(K_{X_i} + B_i)`-negative extremal ray on which
`K_{X_i} + B_i + λ_i C_i` is numerically trivial; a divisorial contraction gives the next model,
a small one is replaced by its flip, and `B_{i+1}`, `C_{i+1}` are the birational transforms; a
contraction of fibre type is a Mori fibre space and ends the program.

The theorem: such a program exists and ends with a model whose adjoint `K + B` is nef over `Z`
or which carries a Mori fibre space structure over `Z`, and every such program has finitely many
birational steps.

## Main results

* `MMP.Fourfold.exists_scalingProgram_and_finite_of_isRelativelyBig`

## Implementation notes

The models are indexed as in `MMP.Fourfold.RelativeDltProgram`: `X₀ = X`, `X_{i+1} = Y i`
(`MMP.Fourfold.modelSeq`), with structure morphisms `MMP.Fourfold.modelStr` over `ℂ`,
`MMP.Fourfold.modelMap` over `Z`, and divisors `MMP.Fourfold.divisorSeq`; the number of
birational steps is `n ∈ ℕ ∪ {∞}`, and only the data indexed by `i ≤ n` (models) and `i < n`
(steps) are constrained. Every model `X_i`, `i ≤ n`, is a `ℚ`-factorial projective variety over
`Z` with a canonical divisor `K_i` and `(X_i, B_i)` klt. Step `i` is a
`(K_i + B_i)`-negative extremal contraction `f_i : X_i ⟶ W_i` onto a projective variety over `Z`
(`MMP.Flips.IsNegativeExtremalContraction`), with `K_i + B_i + λ_i C_i` numerically trivial over
`W_i`, followed either by an isomorphism `f_i⁺` (when `f_i` is divisorial) or by the flip
`f_i⁺ : X_{i+1} ⟶ W_i` of `f_i` (`MMP.Flips.IsFlip`); the `ℝ`-divisors `B_{i+1}`, `C_{i+1}` are
the transforms `(φ_i)_* B_i`, `(φ_i)_* C_i`. A Mori fibre space end is a
`(K_n + B_n)`-negative extremal contraction `X_n ⟶ T` over `Z`, null for the threshold adjoint
`K_n + B_n + λ_n C_n`, onto a projective variety of smaller dimension. The bigness of the
rational part of the boundary is `MMP.Mori.QDivisor.IsRelativelyBig`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.31
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_real_threefold_big_scaling_termination

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Real klt boundaries on `ℚ`-factorial varieties -/

section RealKlt

variable {k : Type} [Field k] {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
  [IsNormal V] {sV : V ⟶ Spec (.of k)}

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial (hV : IsQFactorial sV) (D : RDivisor V) :
    RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor V => hV.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor V) (1 : ℤ),
    fun i => hmC _, fun Γ => ?_⟩
  let F : MMP.Mori.PrimeDivisor V → ℝ := fun P =>
    D P / m P * ((((m P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ)) Γ : ℤ)
  have hF : ∀ i, D (e.symm i) / m (e.symm i) *
      ((DivisorWithCoeffs.coeff (((m (e.symm i) : ℕ) : ℤ) •
        Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor V) (1 : ℤ)) Γ : ℤ) : ℝ) =
        F (e.symm i) := fun i => rfl
  simp_rw [hF]
  rw [Equiv.sum_comp e.symm (fun i : D.support => F i), Finset.sum_coe_sort D.support F,
    DivisorWithCoeffs.coeff_apply]
  by_cases hΓ : Γ ∈ D.support
  · rw [Finset.sum_eq_single Γ (fun P _ hP => by simp [F, Finsupp.single_apply, hP])
      (fun h => absurd hΓ h)]
    have := (hm Γ).ne'
    simp [F]
    field_simp
  · rw [Finsupp.notMem_support_iff.mp hΓ]
    refine (Finset.sum_eq_zero fun P hP => ?_).symm
    have hne : P ≠ Γ := fun e => hΓ (e ▸ hP)
    simp [F, Finsupp.single_apply, hne]

/-- **Lowering a real klt boundary.** On a `ℚ`-factorial variety, a real divisor `B`
coefficientwise below a real klt boundary `Δ` is a real klt boundary: removing the effective
`ℝ`-Cartier divisor `Δ - B` raises every log discrepancy by the coefficient of its effective
pull-back. -/
private theorem isRealKltPair_of_le [CompactSpace V] (hV : IsQFactorial sV) {Δ B : RDivisor V}
    (hΔ : IsRealKltPair sV Δ) (hle : ∀ P, B.coeff P ≤ Δ.coeff P) : IsRealKltPair sV B := by
  classical
  refine ⟨hV.1, fun P => (hle P).trans_lt (hΔ.2.1 P), ?_, ?_⟩
  · obtain ⟨n, K, hK, -⟩ := hΔ.2.2.1
    exact ⟨n, K, hK, isRCartier_of_isQFactorial hV _⟩
  · intro n E a ha
    obtain ⟨hXn, hprop, ω, hω, hKω, m, r, L, L', hL, hsum, hpb, rfl⟩ := ha
    obtain ⟨m₂, s, M, hM, hMsum⟩ := isRCartier_of_isQFactorial hV (Δ - B)
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI := E.isDominant
    haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
    choose M' hM' using fun j => (hM j).exists_isPullback
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
    have hMpb : ∀ j, ∃ h, (M j).IsPullback E.f h (M' j) := fun j =>
      ⟨MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j), hM' j⟩
    have hpos := hΔ.2.2.2 n E _ ⟨hXn, hprop, ω, hω, hKω, m + m₂, Fin.append r s,
      Fin.append L M, Fin.append L' M',
      Fin.addCases (fun i => by simpa using hL i) (fun j => by simpa using hM j),
      fun Γ => ?_, Fin.addCases (fun i => by simpa using hpb i)
        (fun j => by simpa using hMpb j), rfl⟩
    · rw [Fin.sum_univ_add] at hpos
      simp only [Fin.append_left, Fin.append_right] at hpos
      have heff := (isEffective_of_isRCartierPullback E.f ⟨m₂, s, M, hM, hMsum⟩
        fun P => sub_nonneg.mpr (hle P)).2
        (∑ j, s j • Divisor.toRDivisor (M' j))
        ⟨m₂, s, M, M', hM, by ext P; rw [hMsum P, MMP.Fourfold.coeff_sum_smul_toRDivisor],
          hMpb, rfl⟩
      have hE := heff E.E
      rw [show (∑ j, s j • Divisor.toRDivisor (M' j)) E.E =
        (∑ j, s j • Divisor.toRDivisor (M' j)).coeff E.E from rfl,
        MMP.Fourfold.coeff_sum_smul_toRDivisor] at hE
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hE
      linarith
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      have h1 := hsum Γ
      have h2 := hMsum Γ
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2 ⊢
      linarith

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is a real combination of Cartier divisors. -/
private theorem isCartierCombination_of_isQFactorial (hV : IsQFactorial sV) (D : RDivisor V) :
    IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := isRCartier_of_isQFactorial hV D
  refine ⟨m, r, C, hC, ?_⟩
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  ext P
  rw [hD P, MMP.Fourfold.coeff_sum_smul_toRDivisor]

end RealKlt

/-! ### A basis of `N¹(X/Z)` -/

section WeilToCartier

open MMP.Intersection in
/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

open MMP.Intersection in
/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  haveI : IsNoetherian X := {}
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The order of vanishing at a point `η` of coheight one of the image in `k(X)` of an element of
the local ring `𝒪_{X,η}` is its order. -/
private theorem ord_algebraMap_stalk {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {η : X} (hη : Order.coheight η = 1)
    {r : X.presheaf.stalk η} (hr : r ≠ 0) :
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
    X.ord (algebraMap (X.presheaf.stalk η) X.functionField r) η = (Ring.ord _ r).toNat := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk η) := krullDimLE_of_coheight_le hη.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hη]
  simp only [Scheme.ordHom]
  rw [Ring.ordFrac_eq_ord _ hr]
  have hnz : r ∈ nonZeroDivisors (X.presheaf.stalk η) := mem_nonZeroDivisors_of_ne_zero hr
  simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_pos hnz]
  rw [← ENat.coe_toNat (Ring.ord_ne_top hnz)]
  simp

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

open MMP.Intersection MMP.CartierDivisorSheaf in
/-- The principal Cartier divisor of a rational function has the principal Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier_principalDivisor (φ : (RationalFunctions X)ˣ) :
    ∃ A : X.CartierDivisor, IsWeilDivisorOfCartier A (MMP.Mori.principalDivisor φ) := by
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  have hsub : ∀ W : irreducibleComponents X, W = Z₀ := fun W => by
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      have h1 : (W : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]
        exact W.2
      exact h1
    exact Subtype.ext ((hmem W).trans (hmem Z₀).symm)
  set r₀ := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : RationalFunctions X)
  have hr0 : r₀ ≠ 0 := (φ.isUnit.map _).ne_zero
  have hordφ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.ord φ = Scheme.ord r₀ Q.genericPoint := by
    intro Q
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hsub Q.component]
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (ofFunctionField (X := X) ⊤).toMonoidHom (Units.mk0 r₀ hr0)
  refine ⟨principalDivisor c, fun Q => ?_⟩
  rw [MMP.Mori.coeff_principalDivisor, hordφ]
  obtain ⟨⟨a, b⟩, hab⟩ :=
    IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r₀
  have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hb0 : (b : X.presheaf.stalk Q.genericPoint) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero hr0 hbK hab
  have hloc : IsLocalEquationAt (principalDivisor c) Q.genericPoint
      (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _)) :=
    ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
  have hfrac : IsFraction (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
      a b := by
    refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
    apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
    rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
      totalQuotientStalkToFunctionField_stalkToTotalQuotient]
    erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
    rw [mul_comm]
    exact hab
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
    krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  have hO := isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q) hloc
    (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac
  convert hO using 1
  have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
  rw [hab, ord_algebraMap_stalk Q.coheight_genericPoint ha0,
    ord_algebraMap_stalk Q.coheight_genericPoint hb0] at h1
  change _ = ((Ring.ord _ a).toNat : ℤ) -
    ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ)
  linarith

/-- **A Cartier Weil divisor is the Weil divisor of a Cartier divisor.** The divisorial sheaf of
`D` is `𝒪_X(C)` for a Cartier divisor `C`, whose Weil divisor is linearly equivalent to `D`; a
principal correction gives Weil divisor exactly `D`. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier {D : Divisor X} (hD : D.IsCartier) :
    ∃ A : X.CartierDivisor, MMP.Intersection.IsWeilDivisorOfCartier A D := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier C
  obtain ⟨ew⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eC ≪≫ ew)
  obtain ⟨P, hP⟩ := exists_isWeilDivisorOfCartier_principalDivisor ψ
  refine ⟨C + P, fun Q => ?_⟩
  have hDw : D = w + MMP.Mori.principalDivisor ψ := by rw [← hψ]; abel
  rw [hDw, DivisorWithCoeffs.coeff_add]
  exact (hw Q).add (hP Q)

end WeilToCartier

section Numerics

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- The degree of a Cartier Weil divisor along a curve is the degree of the invertible sheaf of
any Cartier divisor with that Weil divisor. -/
private theorem degreeOn_eq_degree_sheaf (C : ProperCurve sX) {A : X.CartierDivisor}
    {w : Divisor X} (h : MMP.Intersection.IsWeilDivisorOfCartier A w) (hw : w.IsCartier) :
    w.degreeOn ℂ sX C.ι C.dim_le hw = C.degree ℂ (MMP.CartierDivisor.sheaf A) := by
  haveI := hw.isInvertibleModule_divisorialSheaf
  rw [← ProperCurve.degree_divisorialSheaf]
  exact (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le h.sheafIsoDivisorialSheaf).symm

/-- The degree map on a real combination of Cartier divisors. -/
private theorem relativeDegreeMap_sum_ofCartier (π : X ⟶ Z) {m : ℕ} (r : Fin m → ℝ)
    (A : Fin m → X.CartierDivisor) (C : {C : ProperCurve sX // C.IsContractedBy π}) :
    MMP.Fourfold.relativeDegreeMap sX π (∑ j, r j • KCartierDivisor.ofCartier ℝ (A j)) C =
      ∑ j, r j * (C.1.degree ℂ (MMP.CartierDivisor.sheaf (A j)) : ℝ) := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    MMP.Fourfold.relativeDegreeMap_ofCartier, MMP.Fourfold.cdeg]

/-- An intersection number of an `ℝ`-divisor presented by Cartier divisors `L j` is the degree of
the corresponding real combination of Cartier divisors with those Weil divisors. -/
private theorem eq_relativeDegreeMap_of_isRIntersectionNumber (π : X ⟶ Z) {D : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {A : Fin m → X.CartierDivisor}
    (hA : ∀ j, MMP.Intersection.IsWeilDivisorOfCartier (A j) (L j)) (C : ProperCurve sX)
    (hC : C.IsContractedBy π) {x : ℝ} (hx : IsRIntersectionNumber ℂ sX D r L C x) :
    x = MMP.Fourfold.relativeDegreeMap sX π (∑ j, r j • KCartierDivisor.ofCartier ℝ (A j))
      ⟨C, hC⟩ := by
  obtain ⟨hL, -, hD, -⟩ := id hx
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL
  rw [← hD] at hy
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hy,
    relativeDegreeMap_sum_ofCartier]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [degreeOn_eq_degree_sheaf C (hA j) (hL j)]

end Numerics

section Spanning

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **Finitely many Cartier divisors span `N¹(X/Z)`.** For a projective morphism `π : X ⟶ Z` of
projective complex varieties with `X` normal, there are Cartier divisors `v j` such that every
`ℝ`-Cartier divisor is numerically equivalent over `Z` to a real combination of them. -/
private theorem exists_cartier_spanning (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hπp : IsProjective π) :
    ∃ (N : ℕ) (v : Fin N → Divisor X), (∀ j, (v j).IsCartier) ∧
      ∀ D : RDivisor X, IsCartierCombination D → ∃ c : Fin N → ℝ,
        IsNumericallyEquivalentOver ℂ sX π D (∑ j, c j • Divisor.toRDivisor (v j)) := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  haveI : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sZ :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sZ hZ
  obtain ⟨hfin, hspan⟩ :=
    MMP.Fourfold.RelativeNumericalDivisorClasses.finiteDimensional_and_span_ofCartier_eq_top
      sX sZ π hπp hπ
  set cls := MMP.Fourfold.relativeNumericalDivisorClass sX π with hcls
  let s : Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX π) :=
    Set.range fun E : X.CartierDivisor => cls (KCartierDivisor.ofCartier ℝ E)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℝ s
  have hbfin : b.Finite := hbli.setFinite
  letI : Fintype b := hbfin.fintype
  choose g hg using fun x : b => hbs x.2
  simp only at hg
  let e := Fintype.equivFin b
  let E : Fin (Fintype.card b) → X.CartierDivisor := fun j => g (e.symm j)
  choose v hv using fun j => exists_isWeilDivisorOfCartier (E j)
  have hvc : ∀ j, (v j).IsCartier := fun j => (hv j).isCartier
  refine ⟨Fintype.card b, v, hvc, fun D hD => ?_⟩
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hDL
  choose A hA using fun j => exists_isWeilDivisorOfCartier_of_isCartier (hL j)
  set KD : KCartierDivisor ℝ X := ∑ j, r j • KCartierDivisor.ofCartier ℝ (A j)
  have hmem :
      cls KD ∈ Submodule.span ℝ (Set.range fun j => cls (KCartierDivisor.ofCartier ℝ (E j))) := by
    have : Set.range (fun j => cls (KCartierDivisor.ofCartier ℝ (E j))) = b := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        change cls (KCartierDivisor.ofCartier ℝ (g (e.symm j))) ∈ b
        rw [hg]; exact (e.symm j).2
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        change cls (KCartierDivisor.ofCartier ℝ (g (e.symm (e ⟨x, hx⟩)))) = x
        rw [Equiv.symm_apply_apply, hg]
    rw [this, hbspan, hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hdeg : ∀ C : {C : ProperCurve sX // C.IsContractedBy π},
      MMP.Fourfold.relativeDegreeMap sX π KD C =
        MMP.Fourfold.relativeDegreeMap sX π (∑ j, c j • KCartierDivisor.ofCartier ℝ (E j)) C := by
    have h1 : cls (∑ j, c j • KCartierDivisor.ofCartier ℝ (E j)) = cls KD := by
      rw [← hc, map_sum]; simp only [map_smul]
    have h2 := LinearMap.mem_ker.mp ((Submodule.Quotient.eq _).mp h1)
    rw [map_sub, sub_eq_zero] at h2
    intro C
    rw [h2]
  refine ⟨c, ⟨⟨m, r, L, hL, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]; exact hDL⟩,
    ⟨_, c, v, hvc, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩⟩
  have hx₁ : x₁ = MMP.Fourfold.relativeDegreeMap sX π KD ⟨C, hC⟩ := by
    have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL
    rw [← hDL] at hy
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ h₁ hy]
    exact eq_relativeDegreeMap_of_isRIntersectionNumber π hA C hC hy
  have hx₂ : x₂ = MMP.Fourfold.relativeDegreeMap sX π
      (∑ j, c j • KCartierDivisor.ofCartier ℝ (E j)) ⟨C, hC⟩ := by
    have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C c v hvc
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ h₂ hy]
    exact eq_relativeDegreeMap_of_isRIntersectionNumber π hv C hC hy
  rw [hx₁, hx₂, hdeg]

end Spanning

section Basis

/-- A numerical intersection number of a real combination `∑ⱼ wⱼ Dⱼ` of `ℝ`-Cartier divisors
with known intersection numbers `xⱼ` with a curve is `∑ⱼ wⱼ xⱼ`. -/
private theorem exists_isRIntersectionNumber_sum {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (Γ : ProperCurve sX) {κ : Type} (s : Finset κ) (D : κ → RDivisor X) (x : κ → ℝ)
    (hx : ∀ j, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber k sX (D j) r L Γ (x j)) (w : κ → ℝ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber k sX (∑ j ∈ s, w j • D j) r L Γ (∑ j ∈ s, w j * x j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0,
      by simp⟩
  | insert a s ha ih =>
    obtain ⟨m₁, r₁, L₁, h₁⟩ := hx a
    obtain ⟨m₂, r₂, L₂, h₂⟩ := ih
    have h := (IsRIntersectionNumber.eq_and_linear k sX Γ).2 _ _ r₁ L₁ r₂ L₂ _ _ (w a) 1 h₁ h₂
    rw [one_smul, one_mul] at h
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨_, _, _, h⟩

/-- **A basis of `N¹(X/W)` inside a spanning family.** If the classes of finitely many Cartier
divisors `vⱼ` span `N¹(X/W)` (every `ℝ`-Cartier divisor is numerically equivalent over `W` to a
real combination of the `vⱼ`), some subfamily `v ∘ a` is a basis: it still spans, and a real
combination of it which is numerically trivial over `W` is trivial. -/
private theorem exists_basis_of_isNumericallyEquivalentOver {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (π : X ⟶ W) {N : ℕ} (v : Fin N → Divisor X)
    (hv : ∀ j, (v j).IsCartier)
    (hspan : ∀ D : RDivisor X, IsCartierCombination D → ∃ c : Fin N → ℝ,
      IsNumericallyEquivalentOver k sX π D (∑ j, c j • Divisor.toRDivisor (v j))) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → Fin N),
      (∀ D : RDivisor X, IsCartierCombination D → ∃ u : ι → ℝ,
        IsNumericallyEquivalentOver k sX π D (∑ i, u i • Divisor.toRDivisor (v (a i)))) ∧
      ∀ u : ι → ℝ,
        IsNumericallyTrivialOver k sX π (∑ i, u i • Divisor.toRDivisor (v (a i))) → u = 0 := by
  classical
  -- intersection numbers of the `vⱼ`
  have hvc : ∀ j, IsCartierCombination (Divisor.toRDivisor (v j)) := fun j =>
    ⟨1, fun _ => 1, fun _ => v j, fun _ => hv j, by
      simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  choose mv rv Lv deg hdeg using fun j (Γ : ProperCurve sX) =>
    MMP.Flips.exists_isRIntersectionNumber (k := k) (hvc j) Γ
  have hcomb : ∀ w : Fin N → ℝ, IsCartierCombination (∑ j, w j • Divisor.toRDivisor (v j)) :=
    fun w => ⟨N, w, v, hv, by simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hnum : ∀ (w : Fin N → ℝ) (Γ : ProperCurve sX), ∃ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X), IsRIntersectionNumber k sX (∑ j, w j • Divisor.toRDivisor (v j))
        r L Γ (∑ j, w j * deg j Γ) := fun w Γ =>
    exists_isRIntersectionNumber_sum Γ Finset.univ _ _ (fun j => ⟨_, _, _, hdeg j Γ⟩) w
  -- the degree map and its kernel
  let Φ : (Fin N → ℝ) →ₗ[ℝ] ({Γ : ProperCurve sX // Γ.IsContractedBy π} → ℝ) :=
    LinearMap.pi fun Γ => ∑ j, deg j Γ.1 • LinearMap.proj j
  have hΦ : ∀ w Γ, Φ w Γ = ∑ j, w j * deg j Γ.1 := fun w Γ => by
    simp [Φ, mul_comm]
  -- numerically trivial combinations lie in the kernel
  have htriv : ∀ w : Fin N → ℝ,
      IsNumericallyTrivialOver k sX π (∑ j, w j • Divisor.toRDivisor (v j)) → Φ w = 0 := by
    intro w hw
    funext Γ
    obtain ⟨m, r, L, h⟩ := hnum w Γ.1
    have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
        (Fin.elim0 : Fin 0 → Divisor X) Γ.1 0 :=
      ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
    rw [hΦ, Pi.zero_apply]
    exact hw.2.2 Γ.1 Γ.2 _ _ _ _ _ _ _ _ h h0
  -- equal degrees give numerical equivalence
  have hequiv : ∀ (D : RDivisor X) (c w : Fin N → ℝ),
      IsNumericallyEquivalentOver k sX π D (∑ j, c j • Divisor.toRDivisor (v j)) →
      Φ c = Φ w →
      IsNumericallyEquivalentOver k sX π D (∑ j, w j • Divisor.toRDivisor (v j)) := by
    intro D c w hD hcw
    refine ⟨hD.1, hcomb w, fun Γ hΓ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    obtain ⟨_, _, _, hc⟩ := hnum c Γ
    obtain ⟨_, _, _, hw⟩ := hnum w Γ
    rw [hD.2.2 Γ hΓ _ _ _ _ _ _ _ _ h₁ hc,
      (IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ h₂ hw]
    have := congrFun hcw ⟨Γ, hΓ⟩
    rwa [hΦ, hΦ] at this
  -- a basis of the quotient among the classes of the `vⱼ`
  let f : Fin N → (Fin N → ℝ) ⧸ LinearMap.ker Φ := fun j => (LinearMap.ker Φ).mkQ (Pi.single j 1)
  have hf : Submodule.span ℝ (Set.range f) = ⊤ := by
    have : Set.range f = (LinearMap.ker Φ).mkQ '' Set.range (Pi.basisFun ℝ (Fin N)) := by
      rw [← Set.range_comp]
      congr 1
      funext j
      simp [f, Pi.basisFun_apply]
    rw [this, Submodule.span_image, (Pi.basisFun ℝ (Fin N)).span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, -, hspan', hli⟩ := exists_linearIndependent' ℝ f
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  let wU : (κ → ℝ) → Fin N → ℝ := fun u => ∑ i, u i • Pi.single (a i) 1
  have hwU : ∀ u : κ → ℝ, ∑ j, wU u j • Divisor.toRDivisor (v j) =
      ∑ i, u i • Divisor.toRDivisor (v (a i)) := fun u => by
    simp only [wU, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp
  have hmk : ∀ u : κ → ℝ, (LinearMap.ker Φ).mkQ (wU u) = ∑ i, u i • f (a i) := fun u => by
    simp [wU, f, map_sum, map_smul]
  refine ⟨κ, inferInstance, a, fun D hD => ?_, fun u hu => ?_⟩
  · obtain ⟨c, hc⟩ := hspan D hD
    have hmem : (LinearMap.ker Φ).mkQ c ∈ Submodule.span ℝ (Set.range (f ∘ a)) := by
      rw [hspan', hf]; exact Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨u, ?_⟩
    rw [← hwU]
    refine hequiv D c (wU u) hc ?_
    have h1 : (LinearMap.ker Φ).mkQ (wU u) = (LinearMap.ker Φ).mkQ c := by
      rw [hmk, ← hu]; rfl
    have h2 := LinearMap.mem_ker.mp ((Submodule.Quotient.eq _).mp h1)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  · rw [← hwU] at hu
    have h0 := htriv _ hu
    have h1 : (LinearMap.ker Φ).mkQ (wU u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact h0
    rw [hmk] at h1
    exact funext (Fintype.linearIndependent_iff.mp hli u h1)

end Basis

/-! ### Numerical toolbox -/

section NumericalToolbox

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- A curve contracted by `f` is contracted by every composite `f ≫ h`. -/
private theorem isContractedBy_comp {C : ProperCurve sX} {f : X ⟶ Y} {T : Scheme.{0}}
    (h : Y ⟶ T) (hC : C.IsContractedBy f) : C.IsContractedBy (f ≫ h) := fun x hx => by
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, hC x hx]

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- Every presentation by Cartier divisors computes an intersection number with a proper
curve. -/
private theorem exists_isRIntersectionNumber (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∃ x, IsRIntersectionNumber k sX D r L C x :=
  ⟨_, hD ▸ isRIntersectionNumber_sum_degreeOn k sX C r L hL⟩

/-- The zero divisor meets every proper curve in `0`, whatever its presentation. -/
private theorem eq_zero_of_isRIntersectionNumber_zero (C : ProperCurve sX) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX 0 r L C x) : x = 0 := by
  have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 0 r L _ _ x 0 h h0

/-- A morphism of relative Picard number one contracts a proper curve: if it contracts none,
every divisor is numerically trivial over it and `N¹` vanishes. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one {f : X ⟶ Y}
    (h : MMP.Flips.relativePicardNumber sX f = 1) : ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hne
  simp only [not_exists] at hne
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ := by
    ext D
    simp only [mem_relativeNumericallyTrivialDivisors, Submodule.mem_top, iff_true]
    exact fun C hC => absurd hC (hne C)
  have : Subsingleton (MMP.Flips.RelativeNumericalDivisorClasses sX f) := by
    unfold MMP.Flips.RelativeNumericalDivisorClasses
    rw [htop]
    infer_instance
  rw [MMP.Flips.relativePicardNumber, rank_subsingleton'] at h
  simp at h

end NumericalToolbox

/-! ### Transforms of divisors along the steps -/

section Transforms

variable {X W X' : Scheme.{0}}

/-- The push-forward of divisors along a partial map of prime divisors preserves effectivity. -/
private theorem mapPrimeDivisors_nonneg {Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) {D : RDivisor X}
    (hD : ∀ P, 0 ≤ D.coeff P) (Q : MMP.Mori.PrimeDivisor Y) :
    0 ≤ (DivisorWithCoeffs.mapPrimeDivisors φ D).coeff Q := by
  classical
  rw [← Finsupp.sum_single D, map_finsuppSum, DivisorWithCoeffs.coeff_apply, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  cases h : φ P with
  | none => simp
  | some E =>
    simp only [Option.elim]
    rw [Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_rfl

/-- The strict transform `(f⁺)⁻¹_* f_*` preserves effectivity. -/
private theorem flipTransform_nonneg (f : X ⟶ W) (fp : X' ⟶ W) {D : RDivisor X}
    (hD : ∀ P, 0 ≤ D.coeff P) (Q : MMP.Mori.PrimeDivisor X') :
    0 ≤ (flipTransform f fp D).coeff Q :=
  mapPrimeDivisors_nonneg _ (mapPrimeDivisors_nonneg _ hD) Q

/-- The strict transform `(f⁺)⁻¹_* f_*` is `ℝ`-linear. -/
private theorem flipTransform_add_smul (f : X ⟶ W) (fp : X' ⟶ W) (B C : RDivisor X) (t : ℝ) :
    flipTransform f fp (B + t • C) = flipTransform f fp B + t • flipTransform f fp C := by
  rw [map_add]
  congr 1
  change DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ (t • C)) =
    t • DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ C)
  rw [DivisorWithCoeffs.mapPrimeDivisors_smul, DivisorWithCoeffs.mapPrimeDivisors_smul]

/-- Extending a composite of partial maps on prime divisors linearly is composing the linear
extensions. -/
private theorem mapPrimeDivisors_bind {Y T : Scheme.{0}} {R : Type*} [AddCommMonoid R]
    (φ₁ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (φ₂ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor T)) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors (fun P => (φ₁ P).bind φ₂) D =
      DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ₁ E with
    | none => simp
    | some E' => simp [DivisorWithCoeffs.mapPrimeDivisors_single]

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {Y : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with regarding a divisor as an `ℝ`-divisor. -/
private theorem flipTransform_toRDivisor (f : X ⟶ W) (fp : X' ⟶ W) (K : Divisor X) :
    flipTransform f fp (Divisor.toRDivisor K) = Divisor.toRDivisor (flipTransform f fp K) := by
  simp only [Divisor.toRDivisor, flipTransform, AddMonoidHom.comp_apply,
    MMP.Mori.RationalMap.transformDivisor, inverseTransformDivisor,
    mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- The birational transform of an adjoint divisor is the adjoint of the transforms. -/
private theorem transformDivisor_logCanonicalDivisor (φ : X.RationalMap X') (K : Divisor X)
    (D : RDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (logCanonicalDivisor K D) =
      logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ D) := by
  rw [logCanonicalDivisor, logCanonicalDivisor, map_add]
  congr 1
  simp only [Divisor.toRDivisor, MMP.Mori.RationalMap.transformDivisor,
    mapPrimeDivisors_mapCoeffsAddMonoidHom]

end Transforms

/-- A relatively ample `ℝ`-divisor is a real combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRelativelyAmple {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X}
    (h : MMP.Flips.IsRelativelyAmple f A) : IsCartierCombination A := by
  obtain ⟨m, r, L, -, -, hL, rfl⟩ := h
  refine ⟨m, r, L, fun j => (hL j).1, ?_⟩
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- A morphism with `f_* 𝒪_X = 𝒪_Y` onto an integral scheme is dominant: a nonempty open of `Y`
missing the image of `f` would have `Γ(Y, V) ≅ Γ(X, ∅) = 0`. -/
private theorem isDominant_of_isIso_app {X Y : Scheme.{0}} [IsIntegral Y] (p : X ⟶ Y)
    (hp : ∀ U : Y.Opens, IsIso (p.app U)) : IsDominant p := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨y, hy⟩ => ?_⟩
  by_contra hempty
  let V' : Y.Opens := ⟨V, hV⟩
  have hbot : p ⁻¹ᵁ V' = ⊥ := TopologicalSpace.Opens.ext <| Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => hempty ⟨p x, hx, x, rfl⟩
  have : Subsingleton Γ(X, p ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(Y, V') := (ConcreteCategory.bijective_of_isIso (p.app V')).1.subsingleton
  have h10 := congrArg (Y.presheaf.germ V' y hy).hom (Subsingleton.elim (1 : Γ(Y, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- The structure morphism of the target of a contraction over `Z` is the composite through
`Z`. -/
private theorem comp_eq_of_isIso_app {X W Z : Scheme.{0}} [IsIntegral W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ W}
    {h : W ⟶ Z} (hf : ∀ U : W.Opens, IsIso (f.app U)) (hfs : f ≫ sW = sX)
    (hfh : f ≫ h ≫ sZ = sX) : h ≫ sZ = sW := by
  haveI := isDominant_of_isIso_app f hf
  exact ext_of_isDominant f (by rw [hfh, hfs])

section StepConversions

variable {X W X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}

/-- A `(K + B)`-negative extremal contraction which is not birational lowers the dimension. -/
private theorem topologicalKrullDim_lt_of_not_isBirationalMorphism {E : RDivisor X}
    {f : X ⟶ W} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hf : IsNegativeExtremalContraction ℂ sX sW E f) (hb : ¬ IsBirationalMorphism f) :
    topologicalKrullDim W < topologicalKrullDim X := by
  have hc := hf.isContraction
  haveI : IsIntegral W := hc.isVariety_target.toIsIntegral
  haveI : LocallyOfFiniteType sW := hc.isVariety_target.toLocallyOfFiniteType
  haveI : IsDominant f := isDominant_of_isIso_app f hc.isIso_app
  have hle : topologicalKrullDim W ≤ topologicalKrullDim X := by
    have hs := hc.comp_eq
    subst hs
    haveI : LocallyOfFiniteType (f ≫ sW) := hc.isVariety_source.toLocallyOfFiniteType
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sW,
      MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (f ≫ sW)]
    letI := functionFieldAlgebra sW
    letI := functionFieldAlgebra (f ≫ sW)
    letI := functionFieldMapAlgebra f
    haveI := isScalarTower_functionFieldMap sW f
    have h := trdeg_le_of_injective
      (IsScalarTower.toAlgHom ℂ W.functionField X.functionField) (RingHom.injective _)
    haveI := essFiniteType_functionField (sX := f ≫ sW)
    have hfin : Algebra.trdeg ℂ X.functionField < Cardinal.aleph0 :=
      trdeg_lt_aleph0 (K := ℂ) (L := X.functionField)
    exact_mod_cast Cardinal.toNat_le_toNat h hfin
  refine lt_of_le_of_ne hle fun heq => hb ?_
  exact (IsBirationalContraction.surjective_and_isBirational (k := ℂ) ⟨hc, heq.symm⟩).2

/-- A divisorial contraction `f` followed by the inverse of an isomorphism `f⁺` is a modification
of `f` into `f⁺` which transforms divisors as `(f⁺)⁻¹_* f_*`. -/
private theorem exists_isModificationOf_of_isIso {f : X ⟶ W} {fp : X' ⟶ W} [IsIso fp]
    {E : RDivisor X} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hf : IsNegativeExtremalContraction ℂ sX sW E f)
    (hfb : IsBirationalMorphism f) (hfp : fp ≫ sW = sX') :
    IsModificationOf f fp (f ≫ inv fp).toRationalMap ∧
      ∀ (R : Type) [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor (X := X) (f ≫ inv fp).toRationalMap D =
          flipTransform f fp D := by
  classical
  haveI : IsIntegral W := hf.isNormalVariety_target.1.toIsIntegral
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = sW ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := by
    rw [show (X' ↘ ⊤_ Scheme) = fp ≫ (W ↘ ⊤_ Scheme) from Subsingleton.elim _ _]
    infer_instance
  have hcomp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C),
      a.toRationalMap.compHom b = (a ≫ b).toRationalMap := fun a b => by
    rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.Hom.toPartialMap_compHom]
  have hcompcomp : ∀ {A B C D : Scheme.{0}} (φ : A.RationalMap B) (b : B ⟶ C) (c : C ⟶ D),
      (φ.compHom b).compHom c = φ.compHom (b ≫ c) := fun φ b c => by
    obtain ⟨ψ, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective φ
    simp only [← Scheme.RationalMap.compHom_toRationalMap]
    congr 1
  set g : X ⟶ X' := f ≫ inv fp with hg
  have hover : MMP.Flips.RationalMap.IsOver f fp g.toRationalMap := by
    rw [MMP.Flips.RationalMap.IsOver, hcomp, hg, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  -- `g` is birational: it is represented by `e = e_f ∘ e_{f⁺}⁻¹`
  have hbir : MMP.Mori.RationalMap.IsBirational (X := X) g.toRationalMap := by
    obtain ⟨em, hm⟩ := hfb
    obtain ⟨ep, hp⟩ := isBirationalMorphism_of_isIso fp
    have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 W) hm
    have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 W) hp
    simp only [Category.comp_id] at h1 h2
    set e := em.trans ep.symm
    have H : e.IsOver f fp := h1.trans h2.symm
    have he : e.toRationalMap.compHom fp = f.toRationalMap := by
      rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
      refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
      change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
        X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
      rw [Category.assoc, H]
      simp
    refine ⟨e, ?_⟩
    have : e.toRationalMap = (e.toRationalMap.compHom fp).compHom (inv fp) := by
      rw [hcompcomp, IsIso.hom_inv_id]
      obtain ⟨ψ, hψ⟩ := Scheme.PartialMap.toRationalMap_surjective e.toRationalMap
      rw [← hψ, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
    rw [this, he, hcomp]
  refine ⟨⟨hbir, hover⟩, fun R _ D => ?_⟩
  -- prime divisors are transformed as `(f⁺)⁻¹_* f_*`
  have hreg : ∀ y : W, y ∈ biregularLocus fp := fun y =>
    le_biregularLocus ((isBiregular_top_iff fp).mpr inferInstance) (Set.mem_univ y)
  have hpt : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := X) g.toRationalMap P =
        (MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P).bind
          (inverseTransformPrimeDivisor fp) := by
    intro P
    cases hP : MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P with
    | some Q =>
      have hfP := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mp hP
      have hco : Order.coheight ((inv fp) Q.genericPoint) = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp
          (by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; exact hreg _),
          ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        exact Q.coheight_genericPoint
      set Q' : MMP.Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
      have hQ' : Q'.genericPoint = (inv fp) Q.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
      have hfpQ' : fp Q'.genericPoint = Q.genericPoint := by
        rw [hQ', ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
      rw [Option.bind_some,
        MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hfpQ'
        (hreg _), MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g P Q', hQ',
        hg, Scheme.Hom.comp_apply, hfP]
    | none =>
      rw [Option.bind_none]
      cases hgP : MMP.Mori.RationalMap.transformPrimeDivisor (X := X) g.toRationalMap P with
      | none => rfl
      | some Q' =>
        exfalso
        have hgη := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g P Q').mp hgP
        have hco : Order.coheight (fp Q'.genericPoint) = 1 := by
          rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hreg _)]
          exact Q'.coheight_genericPoint
        set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
        have hQ : Q.genericPoint = fp Q'.genericPoint :=
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
        have : MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P = some Q := by
          rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q, hQ, ← hgη, hg,
            ← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [hP] at this
        exact absurd this (by simp)
  change DivisorWithCoeffs.mapPrimeDivisors _ D = inverseTransformDivisor fp
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D)
  rw [funext hpt]
  exact mapPrimeDivisors_bind _ _ D

/-- The canonical divisor of the target of a divisorial contraction is the push-forward. -/
private theorem isCanonicalDivisor_flipTransform_of_isIso {f : X ⟶ W} {fp : X' ⟶ W} [IsIso fp]
    {K : Divisor X} {E : RDivisor X} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hf : IsNegativeExtremalContraction ℂ sX sW E f)
    (hfb : IsBirationalMorphism f) (hfp : fp ≫ sW = sX') (hX' : MMP.Mori.IsVariety ℂ sX')
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) :
    ∃ m : ℕ, Divisor.IsCanonicalDivisor sX' m (flipTransform f fp K) := by
  obtain ⟨m, hKm⟩ := hK
  obtain ⟨hmod, htr⟩ := exists_isModificationOf_of_isIso hW hf hfb hfp
  have hgs : (f ≫ inv fp) ≫ sX' = sX := by
    rw [← hfp, Category.assoc, IsIso.inv_hom_id_assoc, hf.isContraction.comp_eq]
  have hX'n : IsNormalVariety ℂ sX' := ⟨hX', inferInstance⟩
  have hgb : IsBirationalMorphism (f ≫ inv fp) := hmod.1
  haveI : IsProper f := hf.isContraction.isProper
  haveI : IsDominant (f ≫ inv fp) := hgb.isDominant
  haveI : LocallyOfFiniteType sX' := hX'.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hf.isNormalVariety_source.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType ((f ≫ inv fp) ≫ sX') := by rw [hgs]; infer_instance
  haveI : MMP.Mori.IsVariety ℂ sX := hf.isNormalVariety_source.1
  haveI : MMP.Mori.IsVariety ℂ sX' := hX'
  have hdim : topologicalKrullDim X' = m :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' sX hgb).trans
      hKm.topologicalKrullDim_eq
  -- a canonical divisor of the target, to compare with
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX' hX'n hdim
  have hsrc : IsNormalVariety ℂ ((f ≫ inv fp) ≫ sX') := hgs ▸ hf.isNormalVariety_source
  have hKm' : K.IsCanonicalDivisor ((f ≫ inv fp) ≫ sX') m := hgs ▸ hKm
  have := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hX'n hsrc hgb hK₀ hKm'
  rw [htr ℤ] at this
  exact ⟨m, this⟩

/-- A step of an extremal real flip sequence is a flip `φ = (f⁺)⁻¹ ∘ f` of `f` with respect to
`K + B`, which transforms divisors as `(f⁺)⁻¹_* f_*`. -/
private theorem exists_isFlip_of_isRealFlipStep {f : X ⟶ W} {fp : X' ⟶ W} {K : Divisor X}
    {B : RDivisor X} (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hstep : IsRealFlipStep sX sW sX' K B (flipTransform f fp K) (flipTransform f fp B) f fp)
    (hsmall : IsSmall ℂ sW sX f) :
    ∃ φ : X.RationalMap X', IsFlip ℂ sX sW sX' (logCanonicalDivisor K B) f fp φ ∧
      ∀ D : RDivisor X, MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  classical
  have hneg := hstep.isNegativeExtremalContraction
  have hsm' := hstep.isSmall_flip
  obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ := hstep.exists_opens_isIso
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : IsProper fp := hsm'.isProper
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = sW ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsSeparated sX' := hsm'.isVariety_source.toIsSeparated
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := by
    rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  obtain ⟨em, hm⟩ := hstep.isBirationalMorphism
  obtain ⟨ep, hp⟩ := hstep.isBirationalMorphism_flip
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 W) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 W) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver f fp := h1.trans h2.symm
  have hover : MMP.Flips.RationalMap.IsOver f fp e.toRationalMap := by
    rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
    change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
      X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
    rw [Category.assoc, H]
    simp
  have hmod : IsModificationOf f fp e.toRationalMap := ⟨⟨e, rfl⟩, hover⟩
  have hXn : IsNormalVariety ℂ (f ≫ sW) := hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
  have htr : ∀ D : RDivisor X,
      MMP.Mori.RationalMap.transformDivisor e.toRationalMap D = flipTransform f fp D :=
    fun D => MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict
      hneg.isNormalVariety_target hXn hstep.isBirationalMorphism V hXV hX'V hover D
  have hKB : MMP.Mori.RationalMap.transformDivisor e.toRationalMap (logCanonicalDivisor K B) =
      logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B) := by
    rw [logCanonicalDivisor, map_add, htr, htr, flipTransform_toRDivisor]
    rfl
  refine ⟨e.toRationalMap,
    { isNormalVariety_source := hneg.isNormalVariety_source
      isNormalVariety_target := hneg.isNormalVariety_target
      isNormalVariety_flip := ⟨hsm'.isVariety_source, inferInstance⟩
      isContraction := hneg.isContraction
      isCartierCombination := hneg.isCartierCombination
      isRelativelyAntiAmple := hneg.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver
        hneg.isNormalVariety_source f fp _ hover
      isSmall := hsm'
      isCartierCombination_transform := by
        rw [hKB]; exact isCartierCombination_of_isRelativelyAmple hstep.isRelativelyAmple_flip
      isRelativelyAmple_transform := by rw [hKB]; exact hstep.isRelativelyAmple_flip
      isSmall_source := hsmall }, htr⟩

end StepConversions

/-! ### Thresholds and null rays -/

section Threshold

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- If `K + B + t C` is nef over `Z` and null on a contracted curve on which `C` is positive,
then `t` is the nef threshold of `C`. -/
private theorem isLeast_of_null (hXq : IsQFactorial sX) {π : X ⟶ Z} {K : Divisor X}
    {B C : RDivisor X} {t : ℝ} (ht : 0 ≤ t)
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + t • C)))
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy π)
    (hnull : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX (logCanonicalDivisor K (B + t • C)) r L Γ x → x = 0)
    (hpos : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX C r L Γ x → 0 < x) :
    IsLeast {s : ℝ | 0 ≤ s ∧ IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + s • C))} t := by
  refine ⟨⟨ht, hnef⟩, fun s ⟨_, hsnef⟩ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨m, r, L, hL, hD, hnn⟩ := hsnef
  obtain ⟨x, hx⟩ := exists_isRIntersectionNumber Γ r L hL hD
  have hx0 := hnn Γ hΓ x hx
  obtain ⟨mc, rc, Lc, hLc, hCp⟩ := isCartierCombination_of_isQFactorial hXq C
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hCp
  obtain ⟨y, hy⟩ := exists_isRIntersectionNumber Γ rc Lc hLc hCp
  have hy0 := hpos _ _ _ _ hy
  have hlin := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ r L rc Lc x y 1 (t - s) hx hy
  have heq : (1 : ℝ) • logCanonicalDivisor K (B + s • C) + (t - s) • C =
      logCanonicalDivisor K (B + t • C) := by
    simp only [logCanonicalDivisor, one_smul, sub_smul]
    abel
  rw [heq] at hlin
  have := hnull _ _ _ _ hlin
  nlinarith

/-- A divisor which is null on every curve contracted by `f` is numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_of_null {W : Scheme.{0}} {f : X ⟶ W} {N : RDivisor X}
    (hN : IsCartierCombination N)
    (hnull : ∀ Γ : ProperCurve sX, Γ.IsContractedBy f →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber ℂ sX N r L Γ x → x = 0) :
    IsNumericallyTrivialOver ℂ sX f N :=
  ⟨hN, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun Γ hΓ _ _ _ _ _ _ _ _ h₁ h₂ =>
      (hnull Γ hΓ _ _ _ _ h₁).trans (eq_zero_of_isRIntersectionNumber_zero Γ h₂).symm⟩

end Threshold

/-! ### Models of a program with scaling -/

/-- A model of a program over `Z`: a normal integral locally noetherian quasi-compact scheme over
`ℂ` and over `Z`, with a canonical divisor `K` and real boundaries `B` and `C`. -/
private structure Model (Z : Scheme.{0}) where
  X : Scheme.{0}
  [isIntegral : IsIntegral X]
  [compactSpace : CompactSpace X]
  [isLocallyNoetherian : IsLocallyNoetherian X]
  [isNormal : IsNormal X]
  s : X ⟶ Spec (.of ℂ)
  π : X ⟶ Z
  K : Divisor X
  B : RDivisor X
  C : RDivisor X

attribute [local instance] Model.isIntegral Model.compactSpace Model.isLocallyNoetherian
  Model.isNormal

variable {Z : Scheme.{0}}

/-- The nef levels `{t ≥ 0 | K + B + t C is nef over Z}` of a model. -/
private def Model.nefLevels (M : Model Z) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K (M.B + t • M.C))}

/-- A model is *good at level `μ`*: it is a projective `ℚ`-factorial threefold over `Z` with a
canonical divisor, `B, C ≥ 0`, `μ > 0`, `(X, B + μ C)` is klt and `K + B + μ C` is nef over
`Z`. -/
private def Model.Good (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) (μ : ℝ) : Prop :=
  M.π ≫ sZ = M.s ∧ MMP.Mori.IsProjectiveVariety ℂ M.s ∧ IsQFactorial M.s ∧
    topologicalKrullDim M.X = 3 ∧ (∃ m : ℕ, M.K.IsCanonicalDivisor M.s m) ∧
    (∀ P, 0 ≤ M.B.coeff P) ∧ (∀ P, 0 ≤ M.C.coeff P) ∧ 0 < μ ∧
    IsRealKltPair M.s (M.B + μ • M.C) ∧
    IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K (M.B + μ • M.C))

/-- The data of one step of a program with scaling out of a model `M`: the threshold `t`, the
contraction `f : M ⟶ W` over `Z` (by `g`), the next model `M'` with `f⁺ : M' ⟶ W` and the
birational map `φ : M ⤏ M'`. -/
private structure StepOut (M : Model Z) where
  t : ℝ
  W : Scheme.{0}
  sW : W ⟶ Spec (.of ℂ)
  f : M.X ⟶ W
  g : W ⟶ Z
  M' : Model Z
  fp : M'.X ⟶ W
  φ : M.X.RationalMap M'.X

/-- The conditions shared by every step: `t` is the nef threshold, `f` is a `(K + B)`-negative
extremal contraction over `Z` onto a projective variety, null for `K + B + t C`. -/
private def StepOut.Common {M : Model Z} (o : StepOut M) : Prop :=
  IsLeast M.nefLevels o.t ∧ MMP.Mori.IsProjectiveVariety ℂ o.sW ∧ o.f ≫ o.g = M.π ∧
    IsNegativeExtremalContraction ℂ M.s o.sW (logCanonicalDivisor M.K M.B) o.f ∧
    IsNumericallyTrivialOver ℂ M.s o.f (logCanonicalDivisor M.K (M.B + o.t • M.C))

/-- The step is of fibre type: the target of the contraction has smaller dimension. -/
private def StepOut.IsFiberType {M : Model Z} (o : StepOut M) : Prop :=
  topologicalKrullDim o.W < topologicalKrullDim M.X

/-- The step is birational: a divisorial contraction or a flip, with next model good at the
threshold level and boundaries the birational transforms. -/
private def StepOut.IsBirationalStep (sZ : Z ⟶ Spec (.of ℂ)) {M : Model Z} (o : StepOut M) :
    Prop :=
  o.M'.Good sZ o.t ∧ o.fp ≫ o.g = o.M'.π ∧
    ((IsBirationalMorphism o.f ∧
        (∃ E : MMP.Mori.PrimeDivisor M.X,
          (MMP.Mori.exceptionalSet o.f : Set M.X) = E.support) ∧
        IsIso o.fp ∧ IsModificationOf o.f o.fp o.φ) ∨
      IsFlip ℂ M.s o.sW o.M'.s (logCanonicalDivisor M.K M.B) o.f o.fp o.φ) ∧
    o.M'.B = MMP.Mori.RationalMap.transformDivisor o.φ M.B ∧
    o.M'.C = MMP.Mori.RationalMap.transformDivisor o.φ M.C

/-- The step out of a good model whose adjoint `K + B` is not nef over `Z`. -/
private theorem exists_stepOut {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {M : Model Z} {μ : ℝ} (hM : M.Good sZ μ)
    (hnef : ¬ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B)) :
    ∃ o : StepOut M, o.Common ∧ (o.IsFiberType ∨ o.IsBirationalStep sZ) := by
  classical
  obtain ⟨hπ, hproj, hq, hdim, hK, hB, hC, hμ, hklt, hnefμ⟩ := hM
  have hB0 : (0 : RDivisor M.X) ≤ M.B := fun P => hB P
  have hC0 : (0 : RDivisor M.X) ≤ M.C := fun P => hC P
  obtain ⟨t, ht0, -, hnt, R, W, iW, lW, nW, sW, f, h, -, -, hnull, hpos, hcontr, hWproj,
    hnegext, hbir⟩ := IsRealKltPair.exists_isExtremalRay_of_isRelativelyNef_add_smul hproj hZ hπ
      hq hdim hK hB0 hC0 hklt hμ hnefμ hnef
  have hcomm : f ≫ h = M.π := hcontr.comp_eq
  -- curves contracted by `f` are contracted by `π`, with class in `R`
  have hRf : ∀ Γ : ProperCurve M.s, Γ.IsContractedBy f →
      ∃ hΓ : Γ.IsContractedBy M.π, Γ.relativeClass M.π hΓ ∈ R := by
    intro Γ hΓ
    have hΓπ : Γ.IsContractedBy M.π := hcomm ▸ isContractedBy_comp h hΓ
    exact ⟨hΓπ, (hcontr.isContractedBy_iff Γ hΓπ).mp hΓ⟩
  obtain ⟨Γ, hΓ⟩ :=
    exists_isContractedBy_of_relativePicardNumber_eq_one hnegext.relativePicardNumber_eq_one
  obtain ⟨hΓπ, hΓR⟩ := hRf Γ hΓ
  have hleast : IsLeast M.nefLevels t :=
    isLeast_of_null hq ht0.le hnt Γ hΓπ (fun m r L x hx => hnull Γ hΓπ hΓR m r L x hx)
      (fun m r L x hx => hpos Γ hΓπ hΓR m r L x hx)
  have htriv : IsNumericallyTrivialOver ℂ M.s f (logCanonicalDivisor M.K (M.B + t • M.C)) :=
    isNumericallyTrivialOver_of_null (isCartierCombination_of_isQFactorial hq _)
      fun Γ hΓ m r L x hx => by
        obtain ⟨hΓπ, hΓR⟩ := hRf Γ hΓ
        exact hnull Γ hΓπ hΓR m r L x hx
  have hsW : h ≫ sZ = sW := comp_eq_of_isIso_app hnegext.isContraction.isIso_app
    hnegext.isContraction.comp_eq (by rw [← Category.assoc, hcomm, hπ])
  by_cases hfb : IsBirationalMorphism f
  · obtain ⟨X', iI, iC, iL, iN, sX', fp, hcases, hX'proj, hX'q, hX'dim, hX'nef, hX'klt⟩ :=
      hbir hfb
    let M' : Model Z :=
      { X := X', s := sX', π := fp ≫ h, K := flipTransform f fp M.K,
        B := flipTransform f fp M.B, C := flipTransform f fp M.C }
    -- the step, its birational map and the canonical divisor of the next model
    obtain ⟨φ, hφ, hφtr, hfps, hK'⟩ : ∃ φ : M.X.RationalMap X',
        ((IsBirationalMorphism f ∧
            (∃ E : MMP.Mori.PrimeDivisor M.X,
              (MMP.Mori.exceptionalSet f : Set M.X) = E.support) ∧
            IsIso fp ∧ IsModificationOf f fp φ) ∨
          IsFlip ℂ M.s sW sX' (logCanonicalDivisor M.K M.B) f fp φ) ∧
        (∀ D : RDivisor M.X, MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D) ∧
        fp ≫ sW = sX' ∧ ∃ m : ℕ, Divisor.IsCanonicalDivisor sX' m (flipTransform f fp M.K) := by
      rcases hcases with ⟨hE, hiso, hfps⟩ | ⟨hsmall, hstep⟩
      · obtain ⟨hmod, htr⟩ := exists_isModificationOf_of_isIso hWproj hnegext hfb hfps
        exact ⟨_, Or.inl ⟨hfb, hE, hiso, hmod⟩, fun D => htr ℝ D, hfps,
          isCanonicalDivisor_flipTransform_of_isIso hWproj hnegext hfb hfps hX'proj.1 hK⟩
      · obtain ⟨φ, hflip, htr⟩ := exists_isFlip_of_isRealFlipStep hWproj hstep hsmall
        exact ⟨φ, Or.inr hflip, htr, hstep.isSmall_flip.comp_eq, hstep.isCanonicalDivisor_flip⟩
    have hgood : M'.Good sZ t := by
      refine ⟨by simp only [M', Category.assoc, hsW, hfps], hX'proj, hX'q, hX'dim, hK',
        flipTransform_nonneg f fp hB, flipTransform_nonneg f fp hC, ht0, ?_, ?_⟩
      · simpa only [M', flipTransform_add_smul] using hX'klt
      · simpa only [M', flipTransform_add_smul] using hX'nef
    exact ⟨⟨t, W, sW, f, h, M', fp, φ⟩, ⟨hleast, hWproj, hcomm, hnegext, htriv⟩,
      Or.inr ⟨hgood, rfl, hφ, (hφtr _).symm, (hφtr _).symm⟩⟩
  · exact ⟨⟨t, W, sW, f, h, M, f, Scheme.RationalMap.id M.X⟩,
      ⟨hleast, hWproj, hcomm, hnegext, htriv⟩,
      Or.inl (topologicalKrullDim_lt_of_not_isBirationalMorphism hproj hWproj hnegext hfb)⟩

/-- The boundary of a good model is klt. -/
private theorem Model.Good.isRealKltPair {sZ : Z ⟶ Spec (.of ℂ)} {M : Model Z} {μ : ℝ}
    (hM : M.Good sZ μ) : IsRealKltPair M.s M.B := by
  obtain ⟨-, -, hq, -, -, -, hC, hμ, hklt, -⟩ := hM
  refine isRealKltPair_of_le hq hklt fun P => ?_
  have := mul_nonneg hμ.le (hC P)
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at this ⊢
  linarith

/-- The step which does nothing. -/
private def StepOut.trivial (M : Model Z) : StepOut M :=
  ⟨0, M.X, M.s, 𝟙 _, M.π, M, 𝟙 _, Scheme.RationalMap.id M.X⟩

open Classical in
/-- The chosen step out of a model. -/
private noncomputable def advance (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) : StepOut M :=
  if h : ∃ o : StepOut M, o.Common ∧ (o.IsFiberType ∨ o.IsBirationalStep sZ) then h.choose
  else StepOut.trivial M

private theorem advance_spec {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {M : Model Z} {μ : ℝ} (hM : M.Good sZ μ)
    (hnef : ¬ IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B)) :
    (advance sZ M).Common ∧ ((advance sZ M).IsFiberType ∨ (advance sZ M).IsBirationalStep sZ) := by
  have h := exists_stepOut hZ hM hnef
  rw [advance, dif_pos h]
  exact h.choose_spec

/-- The sequence of models of the chosen program with scaling, with their levels. -/
private noncomputable def modelLevels (sZ : Z ⟶ Spec (.of ℂ)) (M₀ : Model Z) (μ₀ : ℝ) :
    ℕ → Model Z × ℝ
  | 0 => (M₀, μ₀)
  | i + 1 => ((advance sZ (modelLevels sZ M₀ μ₀ i).1).M',
      (advance sZ (modelLevels sZ M₀ μ₀ i).1).t)

/-- The program stops at a model: `K + B` is nef over `Z` or the chosen step is of fibre
type. -/
private def IsEnd (sZ : Z ⟶ Spec (.of ℂ)) (M : Model Z) : Prop :=
  IsRelativelyNef ℂ M.s M.π (logCanonicalDivisor M.K M.B) ∨ (advance sZ M).IsFiberType

private theorem good_modelLevels {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {M₀ : Model Z} {μ₀ : ℝ} (h₀ : M₀.Good sZ μ₀) :
    ∀ i, (∀ j < i, ¬ IsEnd sZ (modelLevels sZ M₀ μ₀ j).1) →
      (modelLevels sZ M₀ μ₀ i).1.Good sZ (modelLevels sZ M₀ μ₀ i).2
  | 0, _ => h₀
  | i + 1, h => by
    have hi := good_modelLevels hZ h₀ i fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hend := h i (Nat.lt_succ_self i)
    simp only [IsEnd, not_or] at hend
    obtain ⟨-, hs⟩ := advance_spec hZ hi hend.1
    exact (hs.resolve_left hend.2).1

/-! ### Descent of the threshold adjoint -/

section Descent

/-- Composing a rational map with two morphisms is composing with their composite. -/
private theorem compHom_compHom {A B C D : Scheme.{0}} (ψ : A.RationalMap B) (b : B ⟶ C)
    (c : C ⟶ D) : (ψ.compHom b).compHom c = ψ.compHom (b ≫ c) := by
  obtain ⟨ψ', rfl⟩ := Scheme.PartialMap.toRationalMap_surjective ψ
  simp only [← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- The rational map of a morphism, composed with a morphism. -/
private theorem toRationalMap_compHom {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) :
    a.toRationalMap.compHom b = (a ≫ b).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-- A partial isomorphism representing a rational map over `S` lies over `S`. -/
private theorem isOver_of_compHom_eq {A B S : Scheme.{0}} [IsReduced A]
    [IsSeparated (S ↘ ⊤_ Scheme)] (e : A.PartialIso B) (p : A ⟶ S) (q : B ⟶ S)
    (h : e.toRationalMap.compHom q = p.toRationalMap) : e.IsOver p q := by
  have h1 : (e.toPartialMap.compHom q).toRationalMap = p.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap]
    exact h
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  exact (Category.assoc _ _ _).symm.trans h2

/-- A partial isomorphism over `S` represents a rational map over `S`. -/
private theorem isOver_toRationalMap {A B S : Scheme.{0}} {e : A.PartialIso B} {p : A ⟶ S}
    {q : B ⟶ S} (H : e.IsOver p q) : MMP.Flips.RationalMap.IsOver p q e.toRationalMap := by
  rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change A.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ q =
    A.homOfLE (le_top : e.source ≤ ⊤) ≫ A.topIso.hom ≫ p
  rw [Category.assoc, H]
  simp

/-- Relative nefness of `K + D` does not depend on the canonical divisor `K` within its linear
equivalence class: `K₂ + D = (K₁ + D) + div φ`, and principal divisors have degree zero. -/
private theorem isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {K₁ K₂ : Divisor X} {D : RDivisor X}
    (h : K₂.LinearlyEquivalent K₁) (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K₁ D)) :
    IsRelativelyNef ℂ sX π (logCanonicalDivisor K₂ D) := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨m, r, L, hL, hD, hnn⟩ := hnef
  have hP := Divisor.isCartier_principalDivisor φ
  have hPL : ∀ j : Fin 1, (![principalDivisor φ] j).IsCartier := fun j => by
    fin_cases j; exact hP
  have heq : (1 : ℝ) • logCanonicalDivisor K₁ D + (1 : ℝ) • ∑ j : Fin 1,
      (![1] : Fin 1 → ℝ) j • Divisor.toRDivisor (![principalDivisor φ] j) =
      logCanonicalDivisor K₂ D := by
    have hK : K₂ = K₁ + principalDivisor φ := by rw [← hφ]; abel
    simp only [one_smul, Fin.sum_univ_one, Matrix.cons_val_zero, logCanonicalDivisor, hK,
      map_add]
    abel
  have hpres := fun (C : ProperCurve sX) =>
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 _ _ r L (![1] : Fin 1 → ℝ)
      ![principalDivisor φ] _ _ 1 1 (hD ▸ isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL)
      (isRIntersectionNumber_sum_degreeOn ℂ sX C ![1] ![principalDivisor φ] hPL)
  refine ⟨m + 1, Fin.append ((1 : ℝ) • r) ((1 : ℝ) • (![1] : Fin 1 → ℝ)),
    Fin.append L ![principalDivisor φ], Fin.addCases (fun j => by simpa using hL j)
      (fun j => by simpa using hPL j), ?_, fun C hC x hx => ?_⟩
  · rw [← heq, Fin.sum_univ_add, hD]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, one_mul, one_smul]
  · have hC2 := hpres C
    rw [heq] at hC2
    have hxeq := (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ x _ hx hC2
    have h0 := hnn C hC _ (hD ▸ isRIntersectionNumber_sum_degreeOn ℂ sX C r L hL)
    have hy0 : ((![principalDivisor φ] 0 : Divisor X)).degreeOn ℂ sX C.ι C.dim_le (hPL 0) = 0 :=
      Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le (hPL 0)
        (Divisor.linearlyEquivalent_principalDivisor_zero φ)
    simp only [Fin.sum_univ_one, hy0, Int.cast_zero, mul_zero, one_mul, add_zero] at hxeq
    linarith

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {A B : Scheme.{0}} [IsReduced A] [IsReduced B]
    [IsSeparated (A ↘ ⊤_ Scheme)] {p : B ⟶ A} {h : A.RationalMap B}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 A) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  have H := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq e p (𝟙 A) he1
  simp only [Scheme.PartialIso.IsOver, Category.comp_id] at H
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 A
  rw [← H, Iso.inv_hom_id_assoc, Category.comp_id]

/-- **Rational maps into a proper birational model of a base are unique.** Two rational maps
`φ, φ' : X₁ ⤏ X₂` which agree after a proper birational morphism `π₂ : X₂ ⟶ S` onto a normal
scheme, with dominant composite, are equal. -/
private theorem rationalMap_eq_of_compHom_eq {X₁ X₂ S : Scheme.{0}} [IsIntegral X₁]
    [IsIntegral X₂] [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] {π₂ : X₂ ⟶ S}
    [IsProper π₂] (hπ₂ : IsBirationalMorphism π₂) {π₁ : X₁ ⟶ S} [IsDominant π₁]
    {φ φ' : X₁.RationalMap X₂} (h : φ.compHom π₂ = π₁.toRationalMap)
    (h' : φ'.compHom π₂ = π₁.toRationalMap) : φ = φ' := by
  obtain ⟨g, rfl⟩ := φ.exists_rep
  obtain ⟨g', rfl⟩ := φ'.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff] at h h'
  obtain ⟨U, hU, hUl, _hUr, hUe⟩ := h
  obtain ⟨U', hU', hU'l, _hU'r, hU'e⟩ := h'
  have hUl' : U ≤ g.domain := hUl
  have hU'l' : U' ≤ g'.domain := hU'l
  have hUe' : X₁.homOfLE hUl' ≫ g.hom ≫ π₂ = U.ι ≫ π₁ := by
    change X₁.homOfLE hUl' ≫ g.hom ≫ π₂ =
      X₁.homOfLE (le_top : U ≤ ⊤) ≫ X₁.topIso.hom ≫ π₁ at hUe
    rw [hUe, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  have hU'e' : X₁.homOfLE hU'l' ≫ g'.hom ≫ π₂ = U'.ι ≫ π₁ := by
    change X₁.homOfLE hU'l' ≫ g'.hom ≫ π₂ =
      X₁.homOfLE (le_top : U' ≤ ⊤) ≫ X₁.topIso.hom ≫ π₁ at hU'e
    rw [hU'e, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  have hd : Dense ((U ⊓ U' : X₁.Opens) : Set X₁) := by
    simpa using hU.inter_of_isOpen_left hU' U.isOpen
  have hl : U ⊓ U' ≤ g.domain := inf_le_left.trans hUl'
  have hr : U ⊓ U' ≤ g'.domain := inf_le_right.trans hU'l'
  refine ⟨U ⊓ U', hd, hl, hr, ?_⟩
  haveI : Nonempty (U ⊓ U' : X₁.Opens) := by
    obtain ⟨x, hx⟩ := hd.nonempty
    exact ⟨⟨x, hx⟩⟩
  have e₁ : X₁.homOfLE hl ≫ g.hom ≫ π₂ = (U ⊓ U').ι ≫ π₁ := by
    rw [← X₁.homOfLE_homOfLE (inf_le_left : U ⊓ U' ≤ U) hUl', Category.assoc, hUe',
      X₁.homOfLE_ι_assoc]
  have e₂ : X₁.homOfLE hr ≫ g'.hom ≫ π₂ = (U ⊓ U').ι ≫ π₁ := by
    rw [← X₁.homOfLE_homOfLE (inf_le_right : U ⊓ U' ≤ U') hU'l', Category.assoc, hU'e',
      X₁.homOfLE_ι_assoc]
  haveI : IsDominant (U ⊓ U').ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hd⟩
  haveI : IsDominant ((X₁.homOfLE hl ≫ g.hom) ≫ π₂) := by
    rw [Category.assoc, e₁]; infer_instance
  have key : X₁.homOfLE hl ≫ g.hom = X₁.homOfLE hr ≫ g'.hom :=
    MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hπ₂ (by rw [Category.assoc, Category.assoc, e₁, e₂])
  exact key

variable {X W X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {f : X ⟶ W} {g : W ⟶ Z} {fp : X' ⟶ W}
  {φ : X.RationalMap X'}

/-- On a divisorial step or a flip, `φ` transforms divisors as `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform_of_step {E : RDivisor X}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hX' : MMP.Mori.IsVariety ℂ sX')
    (hfps : fp ≫ sW = sX')
    (hstep : (IsBirationalMorphism f ∧
        (∃ P : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = P.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sX sW sX' E f fp φ)
    (hneg : IsNegativeExtremalContraction ℂ sX sW E f) (R : Type) [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  rcases hstep with ⟨hfb, -, hiso, hmod⟩ | hflip
  · have hφ : φ = (f ≫ inv fp).toRationalMap := by
      have : φ = (φ.compHom fp).compHom (inv fp) := by
        rw [compHom_compHom, IsIso.hom_inv_id]
        obtain ⟨ψ, hψ⟩ := Scheme.PartialMap.toRationalMap_surjective φ
        rw [← hψ, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
      rw [this, hmod.2, toRationalMap_compHom]
    obtain ⟨-, htr⟩ := exists_isModificationOf_of_isIso hW hneg hfb hfps
    rw [hφ]
    exact htr R D
  · obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
    haveI := hfV
    haveI := hfpV
    haveI : IsProper f := hneg.isContraction.isProper
    haveI : IsSeparated sX' := hX'.toIsSeparated
    haveI : IsSeparated (X' ↘ ⊤_ Scheme) := by
      rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of ℂ)) from
        Subsingleton.elim _ _]
      infer_instance
    have hfb : IsBirationalMorphism f :=
      (IsBirationalContraction.surjective_and_isBirational
        hflip.isSmall_source.toIsBirationalContraction).2
    have hXn : IsNormalVariety ℂ (f ≫ sW) :=
      hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
    exact MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hneg.isNormalVariety_target
      hXn hfb V hXV hX'V hflip.isModificationOf.2 D

/-- Along a divisorial step or a flip `φ : X ⤏ X'` no prime divisor of `X'` is exceptional for
`φ⁻¹`: its generic point lies where `f⁺` is an isomorphism, over the generic point of a prime
divisor of `W`, whose strict transform on `X` is sent to it. -/
private theorem not_isInverseExceptional_of_step {E : RDivisor X}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hX' : MMP.Mori.IsVariety ℂ sX')
    (hfps : fp ≫ sW = sX')
    (hstep : (IsBirationalMorphism f ∧
        (∃ P : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = P.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sX sW sX' E f fp φ)
    (hneg : IsNegativeExtremalContraction ℂ sX sW E f) (F : MMP.Mori.PrimeDivisor X') :
    ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
  classical
  have hWn := hneg.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = sW ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsProper f := hneg.isContraction.isProper
  have hXn : IsNormalVariety ℂ (f ≫ sW) :=
    hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
  have htr := transformDivisor_eq_flipTransform_of_step hW hX' hfps hstep hneg ℤ
  obtain ⟨hfb, hreg⟩ : IsBirationalMorphism f ∧ fp F.genericPoint ∈ biregularLocus fp := by
    rcases hstep with ⟨hfb, -, hiso, -⟩ | hflip
    · exact ⟨hfb, le_biregularLocus ((isBiregular_top_iff fp).mpr hiso) (Set.mem_univ _)⟩
    · obtain ⟨V, -, hfpV, -, hX'V⟩ :=
        MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
      exact ⟨(IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall_source.toIsBirationalContraction).2,
        isBiregular_iff_le_biregularLocus.mp hfpV
          (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint F).le)⟩
  have hco : Order.coheight (fp F.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hreg]
    exact F.coheight_genericPoint
  set Q : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp F.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hinvQ : inverseTransformPrimeDivisor fp Q = some F :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ.symm hreg
  obtain ⟨P, hP, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn hXn hfb Q
  have hPQ : MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P = some Q :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hP
  intro hF
  have h1 := htr (Finsupp.single P (1 : ℤ))
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_single, hPQ, hinvQ,
    Option.elim] at h1
  cases hφP : MMP.Mori.RationalMap.transformPrimeDivisor φ P with
  | none =>
    rw [hφP] at h1
    simp only [Option.elim] at h1
    have := congrArg (fun D : DivisorWithCoeffs ℤ X' => D F) h1
    simp at this
  | some F' =>
    rw [hφP] at h1
    simp only [Option.elim] at h1
    have hF' : F' = F := by
      by_contra hne
      have := congrArg (fun D => D F) h1
      simp [Finsupp.single_apply, Ne.symm hne] at this
    exact hF P (by rw [hφP, hF'])

/-- **The null threshold adjoint descends.** Let `f : X ⟶ W` be a `(K + B)`-negative extremal
contraction over `Z`, followed by a divisorial step or a flip `φ : X ⤏ X'`, between
`ℚ`-factorial projective varieties. If an `ℝ`-divisor `N` is nef over `Z` and numerically trivial
over `W`, then `φ_* N` is nef over `Z`: on a common resolution `p : V ⟶ X`, `q : V ⟶ X'` over
`W`, the pull-backs `p^* N` and `q^* φ_* N` agree, nefness passes up along `p` and down along
the surjection `q`. -/
private theorem isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX) (hX'q : IsQFactorial sX')
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') {E : RDivisor X}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hneg : IsNegativeExtremalContraction ℂ sX sW E f) (hfg : f ≫ g = π)
    (hstep : (IsBirationalMorphism f ∧
        (∃ P : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = P.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sX sW sX' E f fp φ)
    {N : RDivisor X} (hN : IsRelativelyNef ℂ sX π N)
    (htriv : IsNumericallyTrivialOver ℂ sX f N) {πX' : X' ⟶ Z} (hfpg : fp ≫ g = πX')
    (hfps : fp ≫ sW = sX') :
    IsRelativelyNef ℂ sX' πX' (MMP.Mori.RationalMap.transformDivisor φ N) := by
  classical
  have hWn := hneg.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hWn.1
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'p.1.toQuasiCompact
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated sX' := hX'p.1.toIsSeparated
  haveI : LocallyOfFiniteType sX' := hX'p.1.toLocallyOfFiniteType
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  have hfs : f ≫ sW = sX := hneg.isContraction.comp_eq
  have hXn : IsNormalVariety ℂ (f ≫ sW) := hfs ▸ hneg.isNormalVariety_source
  have hX'n : IsNormalVariety ℂ (fp ≫ sW) :=
    hfps ▸ (⟨hX'p.1, inferInstance⟩ : IsNormalVariety ℂ sX')
  obtain ⟨hmod, hfb, hfpb, hfpp⟩ : IsModificationOf f fp φ ∧ IsBirationalMorphism f ∧
      IsBirationalMorphism fp ∧ IsProper fp := by
    rcases hstep with ⟨hfb, -, hiso, hmod⟩ | hflip
    · exact ⟨hmod, hfb, isBirationalMorphism_of_isIso fp, inferInstance⟩
    · exact ⟨hflip.isModificationOf, (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall_source.toIsBirationalContraction).2,
        (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall.toIsBirationalContraction).2, hflip.isProper⟩
  haveI := hfpp
  haveI : IsDominant f := hfb.isDominant
  -- `φ_* N` is numerically trivial over `W`, with the same pull-back as `N`
  have hφE := not_isInverseExceptional_of_step hW hX'p.1 hfps hstep hneg
  obtain ⟨htriv', hpb⟩ := MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq
    sX sX' sW hXq hX hX'q hX'p hW f fp hfs hfps hmod.1 hmod.2 hφE htriv
  -- a common projective resolution over `W`
  let Xb : Bool → Scheme.{0} := fun b => cond b X X'
  let Fb : ∀ b, Xb b ⟶ W := fun b => Bool.rec (motive := fun b => Xb b ⟶ W) fp f b
  haveI : ∀ b, IsProper (Fb b) := fun b => by cases b <;> (dsimp [Fb, Xb]; infer_instance)
  obtain ⟨V, w, hV, -, gb, -, -, hg, -, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sW Fb
      (fun b => by cases b; exacts [hfpb, hfb]) (fun b => by cases b; exacts [hX'n, hXn])
      (κ := Empty) Empty.elim (fun j => j.elim)
  obtain ⟨hp1, hpp, hpb'⟩ := hg true
  obtain ⟨hq1, hqp, hqb⟩ := hg false
  let p : V ⟶ X := gb true
  let q : V ⟶ X' := gb false
  have hp1' : p ≫ f = w := hp1
  have hq1' : q ≫ fp = w := hq1
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : IsNormal V := hV.2
  haveI : LocallyOfFiniteType (w ≫ sW) := hV.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sW)
  haveI : QuasiCompact (w ≫ sW) := hV.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (w ≫ sW)
  have hpX : p ≫ sX = w ≫ sW := by rw [← hfs, ← Category.assoc, hp1']
  have hqX' : q ≫ sX' = w ≫ sW := by rw [← hfps, ← Category.assoc, hq1']
  obtain ⟨h, hinv⟩ : ∃ h : X.RationalMap V, MMP.Mori.RationalMap.IsInverse p.toRationalMap h :=
    MMP.Mori.RationalMap.IsBirational.exists_isInverse hpb'
  have hhq : h.compHom q = φ := by
    refine rationalMap_eq_of_compHom_eq hfpb (π₁ := f) ?_ hmod.2
    rw [compHom_compHom, hq1', ← hp1', ← compHom_compHom, compHom_eq_of_isInverse hinv,
      toRationalMap_compHom, Category.id_comp]
  haveI : IsDominant p := hpb'.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : Surjective q :=
    surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  obtain ⟨NW, hNW, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p htriv.1
  obtain ⟨NW', hNW', -⟩ := MMP.Flips.existsUnique_isRCartierPullback q htriv'.1
  have heq : NW = NW' :=
    hpb V (w ≫ sW) p q h hV hpX hqX' hpp hpb' hqp hqb hinv hhq NW NW' hNW hNW'
  haveI : QuasiCompact (p ≫ sX) := by rw [hpX]; infer_instance
  haveI : LocallyOfFiniteType (p ≫ sX) := by rw [hpX]; infer_instance
  -- `p^* N` is nef over `Z`
  have hnefV : IsRelativelyNef ℂ (p ≫ sX) (p ≫ π) NW :=
    MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) π (p ≫ π) p (Category.comp_id _) hN hNW
  have hqπ : q ≫ πX' = p ≫ π := by
    rw [← hfpg, ← hfg, ← Category.assoc, hq1', ← hp1', Category.assoc]
  rw [heq, ← hqπ] at hnefV
  exact MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective q (hqX'.trans hpX.symm) πX'
    hNW' hnefV

/-- The transform of a canonical divisor along a divisorial step or a flip is canonical. -/
private theorem isCanonicalDivisor_transformDivisor_of_step
    {K : Divisor X} (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) {E : RDivisor X}
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hX' : MMP.Mori.IsVariety ℂ sX')
    (hfps : fp ≫ sW = sX')
    (hstep : (IsBirationalMorphism f ∧
        (∃ P : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = P.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sX sW sX' E f fp φ)
    (hneg : IsNegativeExtremalContraction ℂ sX sW E f) :
    ∃ m : ℕ, Divisor.IsCanonicalDivisor sX' m (MMP.Mori.RationalMap.transformDivisor φ K) := by
  rcases hstep with ⟨hfb, -, hiso, hmod⟩ | hflip
  · have hcomp : ∀ {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C),
        a.toRationalMap.compHom b = (a ≫ b).toRationalMap := fun a b => by
      rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
        Scheme.Hom.toPartialMap_compHom]
    have hcompcomp : ∀ {A B C D : Scheme.{0}} (ψ : A.RationalMap B) (b : B ⟶ C) (c : C ⟶ D),
        (ψ.compHom b).compHom c = ψ.compHom (b ≫ c) := fun ψ b c => by
      obtain ⟨ψ', rfl⟩ := Scheme.PartialMap.toRationalMap_surjective ψ
      simp only [← Scheme.RationalMap.compHom_toRationalMap]
      congr 1
    have hφ : φ = (f ≫ inv fp).toRationalMap := by
      have : φ = (φ.compHom fp).compHom (inv fp) := by
        rw [hcompcomp, IsIso.hom_inv_id]
        obtain ⟨ψ, hψ⟩ := Scheme.PartialMap.toRationalMap_surjective φ
        rw [← hψ, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
      rw [this, hmod.2, hcomp]
    obtain ⟨-, htr⟩ := exists_isModificationOf_of_isIso hW hneg hfb hfps
    obtain ⟨m, hm⟩ := isCanonicalDivisor_flipTransform_of_isIso hW hneg hfb hfps hX' hK
    exact ⟨m, by rw [hφ, htr ℤ]; exact hm⟩
  · obtain ⟨m, hKm⟩ := hK
    obtain ⟨V, hfV, hfpV, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
    haveI := hfV
    haveI := hfpV
    haveI : IsProper f := hneg.isContraction.isProper
    haveI : IsSeparated sX' := hX'.toIsSeparated
    haveI : IsSeparated (X' ↘ ⊤_ Scheme) := by
      rw [show (X' ↘ ⊤_ Scheme) = sX' ≫ Limits.terminal.from (Spec (.of ℂ)) from
        Subsingleton.elim _ _]
      infer_instance
    have hfb : IsBirationalMorphism f :=
      (IsBirationalContraction.surjective_and_isBirational
        hflip.isSmall_source.toIsBirationalContraction).2
    have hfpb : IsBirationalMorphism fp :=
      (IsBirationalContraction.surjective_and_isBirational
        hflip.isSmall.toIsBirationalContraction).2
    have hXn : IsNormalVariety ℂ (f ≫ sW) :=
      hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
    have hX'n : IsNormalVariety ℂ (fp ≫ sW) := hfps ▸ ⟨hX', inferInstance⟩
    have hKm' : K.IsCanonicalDivisor (f ≫ sW) m := hneg.isContraction.comp_eq ▸ hKm
    have hc := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict
      hneg.isNormalVariety_target hXn hX'n hfb hfpb V hXV hX'V hKm'
    rw [hfps] at hc
    refine ⟨m, ?_⟩
    rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hneg.isNormalVariety_target
      hXn hfb V hXV hX'V hflip.isModificationOf.2 K]
    exact hc

end Descent

/-! ### Composites of partial isomorphisms over a base -/

section Composite

/-- On its source, a restriction of the target of a partial isomorphism `a` is `a`. -/
private theorem restrictTarget_iso_hom_ι {X Y : Scheme.{0}} (a : X.PartialIso Y) (V : Y.Opens)
    (hV : Dense (V : Set Y)) (hV' : V ≤ a.target)
    (h : (a.restrictTarget V hV hV').source ≤ a.source) :
    (a.restrictTarget V hV hV').iso.hom ≫ (a.restrictTarget V hV hV').target.ι =
      X.homOfLE h ≫ a.iso.hom ≫ a.target.ι := by
  have hQ : a.source.ι ''ᵁ (a.iso.inv ''ᵁ a.target.ι ⁻¹ᵁ V) ≤ a.source := h
  change ((Scheme.Opens.isoOfLE hV').symm ≪≫ Scheme.Hom.isoImage a.iso.inv (a.target.ι ⁻¹ᵁ V) ≪≫
      Scheme.Hom.isoImage a.source.ι (a.iso.inv ''ᵁ a.target.ι ⁻¹ᵁ V)).inv ≫ V.ι =
    X.homOfLE hQ ≫ a.iso.hom ≫ a.target.ι
  have e1 : (Scheme.Hom.isoImage a.source.ι (a.iso.inv ''ᵁ a.target.ι ⁻¹ᵁ V)).hom ≫
      X.homOfLE hQ = (a.iso.inv ''ᵁ a.target.ι ⁻¹ᵁ V).ι := by
    apply (cancel_mono a.source.ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact Scheme.Hom.isoImage_hom_ι a.source.ι (a.iso.inv ''ᵁ a.target.ι ⁻¹ᵁ V)
  rw [Iso.inv_comp_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% e1, Scheme.Hom.isoImage_hom_ι_assoc, Iso.inv_hom_id_assoc,
    Scheme.Opens.isoOfLE_inv_ι]

/-- If `b` lies over `f` and `f⁺`, then on the source of `a.trans b` the composite followed by
`f⁺` is `a` followed by `f`. -/
private theorem trans_iso_hom_ι_comp {X Y Z W : Scheme.{0}} (a : X.PartialIso Y)
    (b : Y.PartialIso Z) (f : Y ⟶ W) (fp : Z ⟶ W) (hb : b.IsOver f fp)
    (h : (a.trans b).source ≤ a.source) :
    (a.trans b).iso.hom ≫ (a.trans b).target.ι ≫ fp =
      X.homOfLE h ≫ a.iso.hom ≫ a.target.ι ≫ f := by
  have hV : Dense ((a.target ⊓ b.source : Y.Opens) : Set Y) :=
    a.dense_target.inter_of_isOpen_right b.dense_source b.source.2
  have hb' := Scheme.PartialIso.IsOver.restrictSource hb (a.target ⊓ b.source) hV inf_le_right
  have ha' := restrictTarget_iso_hom_ι a (a.target ⊓ b.source) hV inf_le_left h
  change ((a.restrictTarget _ hV inf_le_left).iso ≪≫
      Y.isoOfEq (show (a.restrictTarget _ hV inf_le_left).target =
        (b.restrictSource _ hV inf_le_right).source from rfl) ≪≫
      (b.restrictSource _ hV inf_le_right).iso).hom ≫
      (b.restrictSource _ hV inf_le_right).target.ι ≫ fp = X.homOfLE h ≫ a.iso.hom ≫ a.target.ι ≫ f
  simp only [Iso.trans_hom, Category.assoc]
  rw [hb', Scheme.isoOfEq_hom_ι_assoc, reassoc_of% ha']
  rfl

/-- **Composites over a base.** If `b : Y ⤏ Z` lies over `f : Y ⟶ W` and `f⁺ : Z ⟶ W`, then
`(b ∘ a) ≫ f⁺ = a ≫ f` as rational maps. -/
private theorem trans_toRationalMap_compHom {X Y Z W : Scheme.{0}} (a : X.PartialIso Y)
    (b : Y.PartialIso Z) (f : Y ⟶ W) (fp : Z ⟶ W) (hb : b.IsOver f fp) :
    (a.trans b).toRationalMap.compHom fp = a.toRationalMap.compHom f := by
  have h : (a.trans b).source ≤ a.source := Scheme.Opens.ι_image_le _ _
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨(a.trans b).source, (a.trans b).dense_source, le_rfl, h, ?_⟩
  change X.homOfLE le_rfl ≫ ((a.trans b).iso.hom ≫ (a.trans b).target.ι) ≫ fp =
    X.homOfLE h ≫ (a.iso.hom ≫ a.target.ι) ≫ f
  rw [Scheme.homOfLE_rfl, Category.id_comp, Category.assoc, Category.assoc,
    trans_iso_hom_ι_comp a b f fp hb h]

/-- **Rational maps into a proper birational model of a base are unique.** Two rational maps
`φ, φ' : X₁ ⤏ X₂` with the same dominant composite with a proper birational morphism
`π₂ : X₂ ⟶ S` onto a normal scheme are equal. -/
private theorem rationalMap_eq_of_compHom_eq' {X₁ X₂ S : Scheme.{0}} [IsIntegral X₁]
    [IsIntegral X₂] [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] {π₂ : X₂ ⟶ S}
    [IsProper π₂] (hπ₂ : IsBirationalMorphism π₂) {φ φ' : X₁.RationalMap X₂}
    (h : φ.compHom π₂ = φ'.compHom π₂) (hd : (φ.compHom π₂).IsDominant) : φ = φ' := by
  obtain ⟨g, rfl⟩ := φ.exists_rep
  obtain ⟨g', rfl⟩ := φ'.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap] at hd
  have hgd : IsDominant (g.hom ≫ π₂) :=
    (Scheme.PartialMap.isDominant_toRationalMap_iff (g.compHom π₂)).mp hd
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff] at h
  obtain ⟨U, hU, hUl, hUr, hUe⟩ := h
  have hUl' : U ≤ g.domain := hUl
  have hUr' : U ≤ g'.domain := hUr
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, hUl', hUr', ?_⟩
  have hUe' : X₁.homOfLE hUl' ≫ g.hom ≫ π₂ = X₁.homOfLE hUr' ≫ g'.hom ≫ π₂ := hUe
  haveI : Nonempty U := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  haveI : IsDominant (X₁.homOfLE hUl') := Opens.isDominant_homOfLE hU hUl'
  haveI : IsDominant ((X₁.homOfLE hUl' ≫ g.hom) ≫ π₂) := by
    rw [Category.assoc]; infer_instance
  have key : X₁.homOfLE hUl' ≫ g.hom = X₁.homOfLE hUr' ≫ g'.hom :=
    MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hπ₂ (by rw [Category.assoc, Category.assoc, hUe'])
  exact key

/-- **A tower computes the composites of a program.** Let `a_{i+1} = b_i ∘ a_i` be composites of
partial isomorphisms `b_i : X_i ⤏ X_{i+1}` lying over `f_i : X_i ⟶ W_i` and
`f⁺_i : X_{i+1} ⟶ W_i`, with `f⁺_i` proper birational onto a normal `W_i`, and let
`q_m : V ⟶ X_m` be compatible over every `W_m`. If `h ∘ q_0` is the identity, then
`q_m ∘ h = a_m` for every `m`. -/
private theorem compHom_eq_of_tower {X : Scheme.{0}} [IsIntegral X] {Y : ℕ → Scheme.{0}}
    [∀ i, IsIntegral (Y i)] {W : ℕ → Scheme.{0}} [∀ i, IsIntegral (W i)] [∀ i, IsNormal (W i)]
    [∀ i, IsLocallyNoetherian (W i)] {f : ∀ i, modelSeq X Y i ⟶ W i} {fp : ∀ i, Y i ⟶ W i}
    [∀ i, IsProper (fp i)] [∀ i, IsDominant (f i)] (hfpb : ∀ i, IsBirationalMorphism (fp i))
    (a : ∀ i, X.PartialIso (modelSeq X Y i)) (b : ∀ i, (modelSeq X Y i).PartialIso (Y i))
    (ha0 : (a 0).toRationalMap = Scheme.Hom.toRationalMap (𝟙 X))
    (ha : ∀ i, a (i + 1) = (a i).trans (b i)) (hb : ∀ i, (b i).IsOver (f i) (fp i))
    {V : Scheme.{0}} {j : ℕ} (q : ∀ m, m ≤ j → (V ⟶ modelSeq X Y m))
    (hq : ∀ m (hm : m < j), q m hm.le ≫ f m = q (m + 1) hm ≫ fp m) {h : X.RationalMap V}
    (hh : h.compHom (q 0 (Nat.zero_le j)) = Scheme.Hom.toRationalMap (𝟙 X)) :
    ∀ m (hm : m ≤ j), h.compHom (q m hm) = (a m).toRationalMap := by
  intro m
  induction m with
  | zero => intro hm; exact hh.trans ha0.symm
  | succ m ih =>
    intro hm
    have hmj : m < j := hm
    have hdom : IsDominant ((a m).toPartialMap.hom ≫ f m) := by
      haveI := Opens.isDominant_ι (a m).dense_target
      change IsDominant (((a m).iso.hom ≫ (a m).target.ι) ≫ f m)
      infer_instance
    obtain ⟨qq, hqq⟩ : ∃ qq : V ⟶ Y m, qq = q (m + 1) hm := ⟨_, rfl⟩
    have hq' : q m hmj.le ≫ f m = qq ≫ fp m := by rw [hqq]; exact hq m hmj
    have key : (h.compHom qq).compHom (fp m) = (a m).toRationalMap.compHom (f m) := by
      rw [compHom_compHom, ← hq', ← compHom_compHom, ih hmj.le]
    have H : h.compHom qq = ((a m).trans (b m)).toRationalMap := by
      refine rationalMap_eq_of_compHom_eq' (hfpb m) ?_ ?_
      · rw [key, trans_toRationalMap_compHom (a m) (b m) (f m) (fp m) (hb m)]
      · rw [key, ← Scheme.RationalMap.compHom_toRationalMap]
        exact (Scheme.PartialMap.isDominant_toRationalMap_iff _).mpr hdom
    rw [hqq] at H
    rw [ha m]
    exact H

/-- On a common model `V` over `S` of two models related by a rational map `φ` over `S`, the
inverse of the first projection followed by the second is `φ`. -/
private theorem compHom_eq_of_isInverse_of_comp_eq {A B S V : Scheme.{0}} [IsIntegral A]
    [IsSeparated (A ↘ ⊤_ Scheme)] [IsIntegral B] [IsReduced V] [IsIntegral S] [IsNormal S]
    [IsLocallyNoetherian S] {f : A ⟶ S} {fp : B ⟶ S} [IsDominant f] [IsProper fp]
    (hfp : IsBirationalMorphism fp) {φ : A.RationalMap B} (hφ : φ.compHom fp = f.toRationalMap)
    (p : V ⟶ A) (q : V ⟶ B) (hpq : p ≫ f = q ≫ fp) {h : A.RationalMap V}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) : h.compHom q = φ := by
  refine rationalMap_eq_of_compHom_eq hfp (π₁ := f) ?_ hφ
  rw [compHom_compHom, ← hpq, ← compHom_compHom, compHom_eq_of_isInverse hinv,
    toRationalMap_compHom, Category.id_comp]

/-- Morphisms out of a model `V` of `A` are determined by their composites with an inverse of
the birational morphism `V ⟶ A`. -/
private theorem eq_of_compHom_eq_of_isInverse {A V B : Scheme.{0}} [IsReduced A] [IsReduced V]
    [IsSeparated (B ↘ ⊤_ Scheme)] {p : V ⟶ A} {h : A.RationalMap V}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) {g₁ g₂ : V ⟶ B}
    (H : h.compHom g₁ = h.compHom g₂) : g₁ = g₂ := by
  obtain ⟨e, -, rfl⟩ := hinv
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) e.dense_target le_rfl
      le_rfl] at H
  have H' : e.iso.inv ≫ e.source.ι ≫ g₁ = e.iso.inv ≫ e.source.ι ≫ g₂ := by
    change A.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ g₁ =
      A.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ g₂ at H
    simpa only [Scheme.homOfLE_rfl, Category.id_comp, Category.assoc] using H
  rw [cancel_epi] at H'
  haveI := Opens.isDominant_ι e.dense_source
  exact ext_of_isDominant_of_isSeparated (B ↘ ⊤_ Scheme) (Subsingleton.elim _ _) e.source.ι H'

end Composite

/-! ### Negativity across a step -/

section StepNegativity

variable {X W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- On a `ℚ`-factorial variety, an `ℝ`-divisor of nonnegative degree on every curve contracted by
`f` is `f`-nef. -/
private theorem isRelativelyNef_of_forall (hXq : IsQFactorial sX) {f : X ⟶ W} {D : RDivisor X}
    (h : ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber ℂ sX D r L Γ x → 0 ≤ x) :
    IsRelativelyNef ℂ sX f D := by
  obtain ⟨m, r, L, hL, hD⟩ := isCartierCombination_of_isQFactorial hXq D
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hD
  exact ⟨m, r, L, hL, hD, fun Γ hΓ x hx => h Γ hΓ m r L x hx⟩

/-- No proper curve is contracted by a morphism injective on points. -/
private theorem false_of_isContractedBy_of_injective (C : ProperCurve sX) {f : X ⟶ W}
    (hf : Function.Injective f.base) (hC : C.IsContractedBy f) : False := by
  have hcl : ∀ x ∈ closure ({C.point} : Set X), x = C.point := fun x hx => hf (hC x hx)
  have hrange : ∀ a : C.scheme, C.ι a ∈ closure ({C.point} : Set X) := by
    intro a
    have : C.ι a ∈ Set.range C.ι := ⟨a, rfl⟩
    simpa [ProperCurve.ι, curveSubschemeAtι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] using this
  have : Subsingleton C.scheme := ⟨fun a b => C.ι.isClosedEmbedding.injective
    ((hcl _ (hrange a)).trans (hcl _ (hrange b)).symm)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- Every `ℝ`-divisor on a `ℚ`-factorial variety is nef over an isomorphism. -/
private theorem isRelativelyNef_of_isIso (hXq : IsQFactorial sX) (f : X ⟶ W) [IsIso f]
    (D : RDivisor X) : IsRelativelyNef ℂ sX f D :=
  isRelativelyNef_of_forall hXq fun Γ hΓ _ _ _ _ _ =>
    (false_of_isContractedBy_of_injective Γ f.isOpenEmbedding.injective hΓ).elim

/-- A relatively ample `ℝ`-divisor is relatively nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple [QuasiCompact sX] {f : X ⟶ W}
    {A : RDivisor X} (hA : IsRelativelyAmple f A) : IsRelativelyNef ℂ sX f A := by
  obtain ⟨m, r, L, -, hr, hLa, hAL⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hLa j).1
  refine ⟨m, r, L, hLc, hAL, fun C hC x hx => ?_⟩
  have hy := isRIntersectionNumber_sum_degreeOn ℂ sX C r L hLc
  rw [← hAL] at hy
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hy]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le (by
    exact_mod_cast (MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hLa j) (hLc j) C hC).le)

/-- **The scaling divisor is positive on the contracted ray.** If `f` is a `(K + B)`-negative
extremal contraction and `K + B + λ C` is numerically trivial over `f` with `λ > 0`, then `C` is
positive on every curve contracted by `f`. -/
private theorem pos_of_isNegativeExtremalContraction {sW : W ⟶ Spec (.of ℂ)} {f : X ⟶ W}
    {K : Divisor X} {B C : RDivisor X} {lam : ℝ} (hlam : 0 < lam)
    (hneg : IsNegativeExtremalContraction ℂ sX sW (logCanonicalDivisor K B) f)
    (htriv : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {x : ℝ} (hx : IsRIntersectionNumber ℂ sX C r L Γ x) : 0 < x := by
  obtain ⟨m', r', L', hm', hr', hL', hD'⟩ := hneg.isRelativelyAntiAmple
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hL' j).1
  have hy := isRIntersectionNumber_sum_degreeOn ℂ sX Γ r' L' hL'c
  rw [← hD'] at hy
  have hypos : 0 < ∑ j, r' j * ((L' j).degreeOn ℂ sX Γ.ι Γ.dim_le (hL'c j) : ℝ) := by
    haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
    refine Finset.sum_pos (fun j _ => mul_pos (hr' j) ?_) Finset.univ_nonempty
    exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL' j) (hL'c j) Γ hΓ
  obtain ⟨mk, rk, Lk, hLk, hE⟩ := hneg.isCartierCombination
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hE
  obtain ⟨xk, hxk⟩ := exists_isRIntersectionNumber Γ rk Lk hLk hE
  have h1 := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ rk Lk r' L' xk _ 1 1 hxk hy
  rw [one_smul, one_smul, add_neg_cancel] at h1
  have h1' := eq_zero_of_isRIntersectionNumber_zero Γ h1
  have h2 := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ rk Lk r L xk x 1 lam hxk hx
  rw [show (1 : ℝ) • logCanonicalDivisor K B + lam • C = logCanonicalDivisor K (B + lam • C) by
    simp only [logCanonicalDivisor, one_smul, add_assoc]] at h2
  have h0 : IsRIntersectionNumber ℂ sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) Γ 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have h2' := htriv.2.2 Γ hΓ _ _ _ _ _ _ _ _ h2 h0
  nlinarith

/-- **The level adjoint is anti-nef on a step.** If `K + B + λ C` is numerically trivial over
`f` and `C` is `f`-nef, then for every `μ ≤ λ` and every `K'` linearly equivalent to `K` the
divisor `-(K' + B + μ C)` is `f`-nef. -/
private theorem isRelativelyNef_neg_logCanonicalDivisor (hXq : IsQFactorial sX) {f : X ⟶ W}
    {K K' : Divisor X} (hKK : K'.LinearlyEquivalent K) {B C : RDivisor X} {lam μ : ℝ}
    (hμ : μ ≤ lam) (htriv : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (B + lam • C)))
    (hC : ∀ Γ : ProperCurve sX, Γ.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber ℂ sX C r L Γ x → 0 ≤ x) :
    IsRelativelyNef ℂ sX f (-logCanonicalDivisor K' (B + μ • C)) := by
  obtain ⟨φ, hφ⟩ := hKK
  refine isRelativelyNef_of_forall hXq fun Γ hΓ m r L x hx => ?_
  obtain ⟨mN, rN, LN, hLN, hN⟩ :=
    isCartierCombination_of_isQFactorial hXq (logCanonicalDivisor K (B + lam • C))
  obtain ⟨mC, rC, LC, hLC, hCp⟩ := isCartierCombination_of_isQFactorial hXq C
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hN hCp
  obtain ⟨xN, hxN⟩ := exists_isRIntersectionNumber Γ rN LN hLN hN
  obtain ⟨xC, hxC⟩ := exists_isRIntersectionNumber Γ rC LC hLC hCp
  have hP := Divisor.isCartier_principalDivisor φ
  have hPL : ∀ j : Fin 1, (![principalDivisor φ] j).IsCartier := fun j => by
    fin_cases j; exact hP
  have hxP := isRIntersectionNumber_sum_degreeOn ℂ sX Γ ![1] ![principalDivisor φ] hPL
  have h0 : IsRIntersectionNumber ℂ sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) Γ 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hxN0 : xN = 0 := htriv.2.2 Γ hΓ _ _ _ _ _ _ _ _ hxN h0
  have hxC0 := hC Γ hΓ _ _ _ _ hxC
  have hy0 : (principalDivisor φ).degreeOn ℂ sX Γ.ι Γ.dim_le (hPL 0) = 0 :=
    Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX Γ.ι Γ.dim_le (hPL 0)
      (Divisor.linearlyEquivalent_principalDivisor_zero φ)
  have h1 := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ rN LN rC LC xN xC (-1) (lam - μ)
    hxN hxC
  have h2 := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).2 _ _ _ _ ![1] ![principalDivisor φ] _
    _ 1 (-1) h1 hxP
  have hK : K' = K + principalDivisor φ := by rw [← hφ]; abel
  have heq : (1 : ℝ) • ((-1 : ℝ) • logCanonicalDivisor K (B + lam • C) + (lam - μ) • C) +
      (-1 : ℝ) • ∑ j : Fin 1, (![1] : Fin 1 → ℝ) j • Divisor.toRDivisor (![principalDivisor φ] j) =
      -logCanonicalDivisor K' (B + μ • C) := by
    simp only [logCanonicalDivisor, hK, map_add, Fin.sum_univ_one, Matrix.cons_val_zero,
      one_smul]
    module
  rw [heq] at h2
  have hxx := (IsRIntersectionNumber.eq_and_linear ℂ sX Γ).1 _ _ _ _ _ x _ hx h2
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hy0, Int.cast_zero, mul_zero, one_mul,
    hxN0] at hxx
  rw [hxx]
  nlinarith

end StepNegativity

/-- The identity transforms every divisor to itself. -/
private theorem transformDivisor_id_toRationalMap {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (Scheme.Hom.toRationalMap (𝟙 X)) D = D := by
  refine Finsupp.ext fun F => ?_
  obtain ⟨E, hE, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX (f := 𝟙 X)
      (by rw [Category.id_comp]; exact hX) (isBirationalMorphism_of_isIso _) F
  rw [htr D]
  have : E = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by simpa using hE)
  rw [this]

/-- **Negativity across a step on a common model.** Let `φ : X_m ⤏ X_n` be a divisorial step or
a flip of the extremal contraction `f : X_m ⟶ W`, and `p : V ⟶ X_m`, `q : V ⟶ X_n` projective
birational morphisms with `p ≫ f = q ≫ f⁺`. If `-L` is `f`-nef, then `p^* L - q^* φ_* L ≥ 0`. -/
private theorem nonneg_sub_of_isRCartierPullback_of_step {Xm Xn W V : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xn] [CompactSpace Xn] [IsLocallyNoetherian Xn] [IsNormal Xn]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sm : Xm ⟶ Spec (.of ℂ)} {sn : Xn ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    {sV : V ⟶ Spec (.of ℂ)} (hm : MMP.Mori.IsProjectiveVariety ℂ sm)
    (hn : MMP.Mori.IsProjectiveVariety ℂ sn) (hnq : IsQFactorial sn)
    (hW : MMP.Mori.IsProjectiveVariety ℂ sW) (hVn : IsNormalVariety ℂ sV)
    (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    {E : RDivisor Xm} {f : Xm ⟶ W} {fp : Xn ⟶ W} {φ : Xm.RationalMap Xn}
    (hneg : IsNegativeExtremalContraction ℂ sm sW E f)
    (hstep : (IsBirationalMorphism f ∧
        (∃ P : MMP.Mori.PrimeDivisor Xm, (MMP.Mori.exceptionalSet f : Set Xm) = P.support) ∧
        IsIso fp ∧ IsModificationOf f fp φ) ∨
      IsFlip ℂ sm sW sn E f fp φ)
    (hfps : fp ≫ sW = sn)
    (p : V ⟶ Xm) (q : V ⟶ Xn) (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p)
    (hq : IsProjectiveMorphism q) (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (hpV : p ≫ sm = sV) (hqV : q ≫ sn = sV)
    {L : RDivisor Xm} (hL : IsRelativelyNef ℂ sm f (-L)) {GA GB : RDivisor V}
    (hGA : IsRCartierPullback p L GA)
    (hGB : IsRCartierPullback q (MMP.Mori.RationalMap.transformDivisor φ L) GB) :
    0 ≤ GA - GB := by
  classical
  have hWn := hneg.isNormalVariety_target
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsProper f := hneg.isContraction.isProper
  haveI : QuasiCompact sm := hm.1.toQuasiCompact
  haveI : QuasiCompact sn := hn.1.toQuasiCompact
  haveI : IsSeparated sm := hm.1.toIsSeparated
  haveI : IsSeparated sn := hn.1.toIsSeparated
  haveI : IsSeparated (Xm ↘ ⊤_ Scheme) := by
    rw [show (Xm ↘ ⊤_ Scheme) = sm ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsSeparated (Xn ↘ ⊤_ Scheme) := by
    rw [show (Xn ↘ ⊤_ Scheme) = sn ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hq
  have hmn : IsNormalVariety ℂ sm := ⟨hm.1, inferInstance⟩
  have hnn : IsNormalVariety ℂ sn := ⟨hn.1, inferInstance⟩
  obtain ⟨hmod, hfb, hfpb, hfpp⟩ : IsModificationOf f fp φ ∧ IsBirationalMorphism f ∧
      IsBirationalMorphism fp ∧ IsProper fp := by
    rcases hstep with ⟨hfb, -, hiso, hmod⟩ | hflip
    · exact ⟨hmod, hfb, isBirationalMorphism_of_isIso fp, inferInstance⟩
    · exact ⟨hflip.isModificationOf, (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall_source.toIsBirationalContraction).2,
        (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall.toIsBirationalContraction).2, hflip.isProper⟩
  haveI := hfpp
  haveI : IsDominant f := hfb.isDominant
  -- `φ` is the inverse of `p` followed by `q`
  obtain ⟨h', hinv'⟩ : ∃ h' : Xm.RationalMap V,
      MMP.Mori.RationalMap.IsInverse p.toRationalMap h' :=
    MMP.Mori.RationalMap.IsBirational.exists_isInverse hpb
  have hh' : h'.compHom q = φ := by
    refine rationalMap_eq_of_compHom_eq hfpb (π₁ := f) ?_ hmod.2
    rw [compHom_compHom, ← hpq, ← compHom_compHom, compHom_eq_of_isInverse hinv',
      toRationalMap_compHom, Category.id_comp]
  obtain ⟨h'', hinv''⟩ : ∃ h'' : Xn.RationalMap V,
      MMP.Mori.RationalMap.IsInverse q.toRationalMap h'' :=
    MMP.Mori.RationalMap.IsBirational.exists_isInverse hqb
  have hφE := not_isInverseExceptional_of_step hW hn.1 hfps hstep hneg
  have hidE : ∀ F : MMP.Mori.PrimeDivisor Xn,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (Scheme.Hom.toRationalMap (𝟙 Xn)) F :=
    fun F hF => hF F ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 Xn) F
      F).mpr rfl)
  have hVm : IsNormalVariety ℂ (p ≫ sm) := hpV ▸ hVn
  have hVq : IsNormalVariety ℂ (q ≫ sn) := hqV ▸ hVn
  have t1 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hmn hnn hφE p q h' hVm hVq hpb
    hqb hinv' hh' hGA
  have t2 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hnn hnn hidE q q h'' hVq hVq
    hqb hqb hinv'' (compHom_eq_of_isInverse hinv'') hGB
  rw [transformDivisor_id_toRationalMap hnn] at t2
  have hMc : IsCartierCombination (-MMP.Mori.RationalMap.transformDivisor φ L) :=
    isCartierCombination_of_isQFactorial hnq _
  have hGB' : IsRCartierPullback q (-MMP.Mori.RationalMap.transformDivisor φ L) (-GB) := by
    simpa using isRCartierPullback_smul (-1) hGB
  have hGA' : IsRCartierPullback p (-L) (-GA) := by
    simpa using isRCartierPullback_smul (-1) hGA
  have key := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub sV sn sm hVn hVp hnn hn hmn
    hm fp f q p hqV hpV hpq.symm hq hqb hp hpb hMc hL hGB' hGA' (by
      rw [map_sub, map_neg, map_neg, t1, t2, sub_self])
  rwa [neg_sub_neg] at key

/-! ### Numerically trivial divisors -/

section NumericallyTrivial

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A sum of divisors nef over `g` is nef over `g`. -/
private theorem isRelativelyNef_add {g : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef k sX g D₁) (h₂ : IsRelativelyNef k sX g D₂) :
    IsRelativelyNef k sX g (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂, hn₂⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂,
    Fin.addCases (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i), ?_,
    fun C hC x hx => ?_⟩
  · rw [Fin.sum_univ_add, hD₁, hD₂]
    simp only [Fin.append_left, Fin.append_right]
  · have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
    have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
    rw [← hD₁] at e₁
    rw [← hD₂] at e₂
    have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ _ _ 1 1 e₁ e₂
    simp only [one_smul, one_mul] at hsum
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hsum]
    exact add_nonneg (hn₁ C hC _ e₁) (hn₂ C hC _ e₂)

/-- A numerically trivial divisor is nef. -/
private theorem isRelativelyNef_of_isNumericallyTrivialOver {g : X ⟶ Y} {D : RDivisor X}
    (h : IsNumericallyTrivialOver k sX g D) : IsRelativelyNef k sX g D := by
  obtain ⟨m, r, L, hL, hD⟩ := h.1
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hD
  refine ⟨m, r, L, hL, hD, fun C hC x hx => ?_⟩
  have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  exact (h.2.2 C hC _ _ _ _ _ _ _ _ hx h0).ge

/-- The negative of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_neg {g : X ⟶ Y} {D : RDivisor X}
    (h : IsNumericallyTrivialOver k sX g D) : IsNumericallyTrivialOver k sX g (-D) := by
  obtain ⟨m, r, L, hL, hD⟩ := h.1
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hD
  refine ⟨⟨m, -r, L, hL, ?_⟩, h.2.1, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  · simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    rw [hD]; simp [Finset.sum_neg_distrib, neg_smul]
  · have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
    rw [← hD] at e
    have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
        (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
      ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    have hx := h.2.2 C hC _ _ _ _ _ _ _ _ e h0
    have hn := (IsRIntersectionNumber.eq_and_linear k sX C).2 D 0 r L Fin.elim0 Fin.elim0 _ _
      (-1) 0 e h0
    rw [zero_smul, add_zero, neg_one_smul] at hn
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₁ hn,
      (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₂ h0, hx]
    ring

/-- A divisor nef over `g` together with its negative is numerically trivial over `g`. -/
private theorem isNumericallyTrivialOver_of_isRelativelyNef_neg {g : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef k sX g D) (h' : IsRelativelyNef k sX g (-D)) :
    IsNumericallyTrivialOver k sX g D := by
  obtain ⟨m, r, L, hL, hD, hn⟩ := h
  obtain ⟨m', r', L', hL', hD', hn'⟩ := h'
  refine ⟨⟨m, r, L, hL, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]; exact hD⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
  rw [← hD] at e
  have e' := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
  rw [← hD'] at e'
  have hsum := (IsRIntersectionNumber.eq_and_linear k sX C).2 D (-D) r L r' L' _ _ 1 1 e e'
  rw [one_smul, one_smul, add_neg_cancel] at hsum
  have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hz := (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hsum h0
  have a := hn C hC _ e
  have b := hn' C hC _ e'
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₁ e,
    (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₂ h0]
  linarith

/-- Numerical triviality over `g ≫ h` implies numerical triviality over `g`. -/
private theorem isNumericallyTrivialOver_of_comp {S : Scheme.{0}} {g : X ⟶ Y} {h : Y ⟶ S}
    {D : RDivisor X} (hD : IsNumericallyTrivialOver k sX (g ≫ h) D) :
    IsNumericallyTrivialOver k sX g D :=
  ⟨hD.1, hD.2.1, fun C hC => hD.2.2 C fun y hy => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC y hy]⟩

/-- Adding a numerically trivial divisor preserves nefness. -/
private theorem isRelativelyNef_add_isNumericallyTrivialOver {g : X ⟶ Y} {D T : RDivisor X}
    (hD : IsRelativelyNef k sX g D) (hT : IsNumericallyTrivialOver k sX g T) :
    IsRelativelyNef k sX g (D + T) :=
  isRelativelyNef_add hD (isRelativelyNef_of_isNumericallyTrivialOver hT)

/-- A sum of numerically trivial divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_add {g : X ⟶ Y} {D T : RDivisor X}
    (hD : IsNumericallyTrivialOver k sX g D) (hT : IsNumericallyTrivialOver k sX g T) :
    IsNumericallyTrivialOver k sX g (D + T) :=
  isNumericallyTrivialOver_of_isRelativelyNef_neg
    (isRelativelyNef_add (isRelativelyNef_of_isNumericallyTrivialOver hD)
      (isRelativelyNef_of_isNumericallyTrivialOver hT))
    (by
      rw [neg_add]
      exact isRelativelyNef_add
        (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg hD))
        (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg hT)))

end NumericallyTrivial

/-! ### A tower of resolutions over a program -/

section Tower

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)}
  [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
  [∀ i, IsNormal (Y i)] {W : ℕ → Scheme.{0}} {sW : ∀ i, W i ⟶ Spec (.of ℂ)}
  {f : ∀ i, modelSeq X Y i ⟶ W i} {fp : ∀ i, Y i ⟶ W i}

/-- **A smooth projective tower over a program.** For a sequence of birational steps
`X_i ⟶ W_i ⟵ X_{i+1}` between normal varieties, with `W_i` normal projective, and every `j`,
there is a smooth projective variety `V` with projective birational morphisms `q_m : V ⟶ X_m`,
`m ≤ j`, compatible over every `W_m`: `q_m ≫ f_m = q_{m+1} ≫ f⁺_m`. -/
private theorem exists_tower (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hY : ∀ i, MMP.Mori.IsVariety ℂ (sY i))
    (hstep : ∀ i, IsNormalVariety ℂ (sW i) ∧ MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧
      IsProper (f i) ∧ IsBirationalMorphism (f i) ∧ f i ≫ sW i = modelStr sX sY i ∧
      IsProper (fp i) ∧ IsBirationalMorphism (fp i) ∧ fp i ≫ sW i = sY i)
    (j : ℕ) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (q : ∀ m, m ≤ j → (V ⟶ modelSeq X Y m)),
      IsNormalVariety ℂ sV ∧ MMP.Mori.IsSmoothScheme sV ∧ MMP.Mori.IsProjectiveVariety ℂ sV ∧
      (∀ m (hm : m ≤ j), q m hm ≫ modelStr sX sY m = sV ∧ IsProjectiveMorphism (q m hm) ∧
        IsBirationalMorphism (q m hm)) ∧
      ∀ m (hm : m < j), q m hm.le ≫ f m = q (m + 1) hm ≫ fp m := by
  induction j with
  | zero =>
    haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
    obtain ⟨V, w, hV, -, g, hsm, -, hg, -, hproj⟩ :=
      MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX
        (X := fun _ : Unit => X) (fun _ => 𝟙 X) (fun _ => isBirationalMorphism_of_isIso _)
        (fun _ => by rw [Category.id_comp]; exact ⟨hX.1, inferInstance⟩)
        (κ := Empty) Empty.elim (fun j => j.elim)
    obtain ⟨hg1, hgp, hgb⟩ := hg ()
    rw [Category.comp_id] at hg1
    subst hg1
    haveI : IsIntegral V := hV.1.toIsIntegral
    haveI : IsNormal V := hV.2
    haveI : LocallyOfFiniteType (g () ≫ sX) := hV.1.toLocallyOfFiniteType
    refine ⟨V, inferInstance, LocallyOfFiniteType.isLocallyNoetherian (g () ≫ sX), inferInstance,
      g () ≫ sX, fun m hm => (show 0 = m by omega) ▸ g (), hV, hsm, hproj hX,
      fun m hm => ?_, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    obtain rfl : m = 0 := by omega
    exact ⟨rfl, hgp, hgb⟩
  | succ j ih =>
    obtain ⟨V, iI, iL, iN, sV, q, hVn, -, -, hq, hcomp⟩ := ih
    obtain ⟨hWn, hWp, hfp, hfb, hfs, hfpp, hfpb, hfps⟩ := hstep j
    haveI : AlgebraicGeometry.IsVariety ℂ (sW j) := hWn.1
    haveI : IsNormal (W j) := hWn.2
    haveI := hfp
    haveI := hfpp
    obtain ⟨hqs, hqp, hqb⟩ := hq j le_rfl
    haveI : IsProper (q j le_rfl) := isProper_of_isProjectiveMorphism _ hqp
    let Xb : Bool → Scheme.{0} := fun b => cond b V (Y j)
    let Fb : ∀ b, Xb b ⟶ W j := fun b =>
      Bool.rec (motive := fun b => Xb b ⟶ W j) (fp j) (q j le_rfl ≫ f j) b
    haveI : ∀ b, IsProper (Fb b) := fun b => by cases b <;> (dsimp [Fb, Xb]; infer_instance)
    have hVW : (q j le_rfl ≫ f j) ≫ sW j = sV := by rw [Category.assoc, hfs, hqs]
    obtain ⟨V', w, hV', -, gb, hsm', -, hg, -, hproj'⟩ :=
      MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (sW j) Fb
        (fun b => by
          cases b
          · exact hfpb
          · show IsBirationalMorphism (q j le_rfl ≫ f j)
            exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hqb hfb)
        (fun b => by
          cases b
          · change IsNormalVariety ℂ (fp j ≫ sW j)
            rw [hfps]
            exact ⟨hY j, inferInstance⟩
          · change IsNormalVariety ℂ ((q j le_rfl ≫ f j) ≫ sW j)
            rw [hVW]
            exact hVn)
        (κ := Empty) Empty.elim (fun j => j.elim)
    obtain ⟨ht1, htp, htb⟩ := hg true
    obtain ⟨hf1, hfp', hfb'⟩ := hg false
    let gt : V' ⟶ V := gb true
    let gf : V' ⟶ Y j := gb false
    have ht1' : gt ≫ q j le_rfl ≫ f j = w := ht1
    have hf1' : gf ≫ fp j = w := hf1
    haveI : IsIntegral V' := hV'.1.toIsIntegral
    haveI : IsNormal V' := hV'.2
    haveI : LocallyOfFiniteType (w ≫ sW j) := hV'.1.toLocallyOfFiniteType
    let q' : ∀ m, m ≤ j + 1 → (V' ⟶ modelSeq X Y m) := fun m hm =>
      if h : m ≤ j then gt ≫ q m h else (show j + 1 = m by omega) ▸ gf
    have hq'le : ∀ m (hm : m ≤ j), q' m (hm.trans j.le_succ) = gt ≫ q m hm := fun m hm =>
      dif_pos hm
    have hq'top : q' (j + 1) le_rfl = gf := dif_neg (by omega)
    have hgtV : gt ≫ sV = w ≫ sW j := by
      rw [← hVW, ← ht1']
      simp only [Category.assoc]
    refine ⟨V', inferInstance, LocallyOfFiniteType.isLocallyNoetherian (w ≫ sW j), inferInstance,
      w ≫ sW j, q', hV', hsm', hproj' hWp, fun m hm => ?_, fun m hm => ?_⟩
    · rcases Nat.lt_or_ge m (j + 1) with hlt | hge
      · have hmj : m ≤ j := Nat.lt_succ_iff.mp hlt
        rw [hq'le m hmj]
        obtain ⟨h1, h2, h3⟩ := hq m hmj
        refine ⟨by rw [Category.assoc, h1, hgtV], IsProjectiveMorphism.comp htp h2,
          MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp htb h3⟩
      · obtain rfl : m = j + 1 := by omega
        rw [hq'top]
        exact ⟨by change gf ≫ sY j = _; rw [← hfps, ← Category.assoc, hf1'], hfp', hfb'⟩
    · rcases Nat.lt_or_ge m j with hlt | hge
      · rw [hq'le m hlt.le, hq'le (m + 1) hlt, Category.assoc, hcomp m hlt]
        exact (Category.assoc _ _ _).symm
      · obtain rfl : m = j := by omega
        rw [hq'le m le_rfl, hq'top, Category.assoc, ht1']
        exact hf1'.symm

end Tower

/-! ### Uniqueness of ample log minimal models -/

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_of {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- **Transforms through a common model.** Let `r : W ⟶ X₁` and `q : W ⟶ X₂` be proper birational
morphisms of normal varieties, `h` an inverse of `r` and `φ = q ∘ h`. If `φ⁻¹` contracts no prime
divisor, then `φ_* r_* D = q_* D` for every divisor `D` on `W`: at a prime divisor `F` of `X₂`,
both sides are the coefficient of `D` along the strict transform of `F` in `W`. -/
private theorem transformDivisor_transformDivisor_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r] [IsProper q]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor X₂,
      ∃ R : MMP.Mori.PrimeDivisor X₁, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap D := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  have hW₂ : IsNormalVariety ℂ (q ≫ s₂) := hrq ▸ hW
  refine Finsupp.ext fun F => ?_
  obtain ⟨R₀, hR₀⟩ := hφE F
  obtain ⟨RW, hRW, -, hRWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R₀
  obtain ⟨FW, hFW, -, hFWc⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₂ hW₂ hqb F
  have := F.isDiscreteValuationRing_localRing
  -- every prime divisor of `X₁` with transform `F` has strict transform `F_W`
  have hkey : ∀ R' : MMP.Mori.PrimeDivisor X₁,
      MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F → R' = R₀ := by
    intro R' hR'
    obtain ⟨R'W, hR'W, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
    have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
      R'W hR'W F).mp hR'
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    have h3 : R'W.genericPoint = RW.genericPoint :=
      MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hR'W.symm.trans ((congrArg r h3).trans hRW))
  have hRF : RW = FW := by
    have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R₀
      RW hRW F).mp hR₀
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h2 hFW)
  change DivisorWithCoeffs.mapPrimeDivisors _ _ F = _
  rw [MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR₀ hkey, hRWc, hFWc, hRF]

/-- **Strict transforms through a common model are unique.** In the setting of
`transformDivisor_transformDivisor_of_isInverse`, two prime divisors of `X₁` with the same
transform `F` coincide: their strict transforms on `W` both map to the generic point of `F`. -/
private theorem eq_of_transformPrimeDivisor_eq_some_of_isInverse
    {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [IsLocallyNoetherian X₁] [IsNormal X₁]
    [IsIntegral X₂] [IsLocallyNoetherian X₂] [IsNormal X₂]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {s₁ : X₁ ⟶ Spec (.of ℂ)} {s₂ : X₂ ⟶ Spec (.of ℂ)}
    (hX₁ : IsNormalVariety ℂ s₁) (hX₂ : IsNormalVariety ℂ s₂) {r : W ⟶ X₁} {q : W ⟶ X₂}
    (hW : IsNormalVariety ℂ (r ≫ s₁)) (hrq : r ≫ s₁ = q ≫ s₂) [IsProper r]
    (hrb : IsBirationalMorphism r) (hqb : IsBirationalMorphism q) {h : X₁.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h) {φ : X₁.RationalMap X₂}
    (hφ : h.compHom q = φ) {F : MMP.Mori.PrimeDivisor X₂} {R R' : MMP.Mori.PrimeDivisor X₁}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F)
    (hR' : MMP.Mori.RationalMap.transformPrimeDivisor φ R' = some F) : R = R' := by
  haveI := hX₁.1.toIsSeparated
  haveI := hX₂.1.toIsSeparated
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : IsSeparated r := IsSeparated.of_comp r s₁
  haveI : IsSeparated (q ≫ s₂) := by rw [← hrq]; infer_instance
  haveI : IsSeparated q := IsSeparated.of_comp q s₂
  haveI := hqb.isDominant
  obtain ⟨RW, hRW, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R
  obtain ⟨R'W, hR'W, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX₁ hW hrb R'
  have := F.isDiscreteValuationRing_localRing
  have h1 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R
    RW hRW F).mp hR
  have h2 := (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse r hrb hinv q hφ R'
    R'W hR'W F).mp hR'
  have h3 : RW.genericPoint = R'W.genericPoint :=
    MMP.Fourfold.eq_of_map_eq_of_valuationRing hqb.functionFieldMap_bijective h1 h2
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hRW.symm.trans ((congrArg r h3).trans hR'W))

/-- A rational map composed with the identity. -/
private theorem rationalMap_compHom_id {X Y : Scheme.{0}} (f : X.RationalMap Y) :
    f.compHom (𝟙 Y) = f := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]

/-- A rational map `φ⁻¹` contracts no prime divisor of the target exactly when every prime divisor
of the target is the transform of a prime divisor of the source. -/
private theorem exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (F : MMP.Mori.PrimeDivisor Y) :
    ∃ R : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor φ R = some F := by
  by_contra h
  push Not at h
  exact hφE F h

/-- **A log minimal model extracting no divisor is a nef weak model.** Let `φ : X ⤏ Y` be a log
minimal model of `(X/Z, Δ)` with `X` projective and `ℚ`-factorial, such that `φ⁻¹` contracts no
prime divisor. Then the canonical divisor and boundary of the model are the transforms `φ_* K` and
`φ_* Δ`, and `φ` is a nef weak model of `(X, Δ)` over `Z`. -/
private theorem IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sY]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ : RDivisor X} {KY : Divisor Y}
    {ΔY : RDivisor Y} {φ : X.RationalMap Y}
    (h : IsRealLogMinimalModel sX sY sZ π πY K Δ KY ΔY φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F) :
    KY = MMP.Mori.RationalMap.transformDivisor φ K ∧
      ΔY = MMP.Mori.RationalMap.transformDivisor φ Δ ∧
      IsNefWeakModel sX sY sZ π πY K Δ φ := by
  have hXn : IsNormalVariety ℂ sX := h.isRealLcPair.1
  have hYn : IsNormalVariety ℂ sY := h.isNormalVariety_model
  have hΔ : ΔY = MMP.Mori.RationalMap.transformDivisor φ Δ := by
    refine Finsupp.ext fun F => ?_
    have := h.coeff_boundary F
    rw [if_neg (hφE F), add_zero] at this
    exact this
  obtain ⟨W, iW, lW, nW, sW, p, q, hh, GX, GY, hR⟩ := h.exists_resolution
  have hK : KY = MMP.Mori.RationalMap.transformDivisor φ K := by
    obtain ⟨n, KW, -, hp, hq⟩ := hR.exists_canonicalDivisor
    haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
    haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
    have hWn : IsNormalVariety ℂ (p ≫ sX) := by
      rw [hR.comp_eq_left]; exact ⟨hR.isVariety, inferInstance⟩
    rw [← hp, transformDivisor_transformDivisor_of_isInverse hXn hYn hWn
      (hR.comp_eq_left.trans hR.comp_eq_right.symm) hR.isBirationalMorphism_left
      hR.isBirationalMorphism_right hR.isInverse hR.compHom_eq
      (exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional hφE), hq]
  refine ⟨hK, hΔ, ?_⟩
  exact
    { isNormalVariety_source := hXn
      isProjectiveVariety_source := hX
      comp_eq_source := h.comp_eq
      isCanonicalDivisor := h.isCanonicalDivisor
      isCartierCombination := isCartierCombination_of_isQFactorial hXq _
      isNormalVariety_target := hYn
      isProjectiveVariety_target := h.isProjectiveVariety_model
      comp_eq_target := h.comp_eq_model
      isBirational := h.isBirational
      isOver := h.isOver
      not_isInverseExceptional := hφE
      isRelativelyNef := by rw [← hK, ← hΔ]; exact h.isRelativelyNef
      exists_resolution := ⟨W, iW, lW, nW, sW, p, q, hh, hR.isVariety, hR.isSmoothScheme,
        hR.comp_eq_left, hR.comp_eq_right, hR.isProjectiveMorphism_left,
        hR.isProjectiveMorphism_right, hR.isBirationalMorphism_left,
        hR.isBirationalMorphism_right, hR.isInverse, hR.compHom_eq, GX, GY,
        hR.isRCartierPullback_left, by rw [← hK, ← hΔ]; exact hR.isRCartierPullback_right,
        hR.effective, hR.isExceptional⟩ }

/-- **Pull-backs along a composite.** If `G = f^*D` and `G'` is the pull-back of `D` along
`r ≫ f`, then `G'` is the pull-back of `G` along `r`. -/
private theorem isRCartierPullback_of_isRCartierPullback_comp {X Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {f : Y ⟶ X} {r : W ⟶ Y} [IsDominant r] [IsDominant (r ≫ f)] {D : RDivisor X}
    {G' : RDivisor W} {G₀ : RDivisor Y} (hG : MMP.Flips.IsRCartierPullback f D G₀)
    (hG' : MMP.Flips.IsRCartierPullback (r ≫ f) D G') :
    MMP.Flips.IsRCartierPullback r G₀ G' := by
  obtain ⟨m, c, L, L', hL, hD, hpb, rfl⟩ := hG
  choose hB hp using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hp j).isCartier (hL j)
  let L'' : Fin m → Divisor W := fun j => (L' j).pullback (hL'c j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j))
  have hp'' : ∀ j, (L' j).IsPullback r
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant r (L' j)) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  have hcomp : MMP.Flips.IsRCartierPullback (r ≫ f) D (∑ j, c j • Divisor.toRDivisor (L'' j)) :=
    ⟨m, c, L, L'', hL, hD, fun j =>
      ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (r ≫ f) (L j),
        MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hp j) (hp'' j) _⟩, rfl⟩
  rw [MMP.Flips.IsRCartierPullback.eq (r ≫ f) hG' hcomp]
  exact ⟨m, c, L', L'', hL'c, rfl, fun j => ⟨_, hp'' j⟩, rfl⟩

/-- A divisor which is `f`-ample has positive intersection number, computed with any
presentation, on every proper curve contracted by `f`. -/
private theorem isRIntersectionNumber_pos_of_isRelativelyAmple {k : Type} [Field k]
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (f : X ⟶ W) {L : RDivisor X} (hL : IsRelativelyAmple f L)
    (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy f) {m : ℕ} (r : Fin m → ℝ)
    (Ls : Fin m → Divisor X) (x : ℝ) (hx : IsRIntersectionNumber k sX L r Ls Γ x) : 0 < x := by
  obtain ⟨m', a, A, hm, ha, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hy := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX Γ a A hAc
  rw [← hLeq] at hy
  rw [(IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hx hy]
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j => by
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) Γ hΓ
  exact Finset.sum_pos (fun j _ => mul_pos (ha j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

/-- **An ample log minimal model is unique.** Two log minimal models `φ₁ : X ⤏ Y₁`,
`φ₂ : X ⤏ Y₂` over `Z` of the same pair, extracting no divisor, the second with adjoint ample
over `Z`, are isomorphic compatibly with the maps from `X`: on a common resolution the
pulled-back adjoints agree, so the second resolution map contracts every curve contracted by the
first and factors through it by rigidity; the factorization contracts no divisor, since both
models contract the same prime divisors of `X`, and a projective birational morphism
contracting no divisor onto the `ℚ`-factorial ample model is an isomorphism. -/
private theorem exists_iso_of_isRealLogMinimalModel_of_isRelativelyAmple
    {X Z Y₁ Y₂ : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y₁] [IsLocallyNoetherian Y₁] [IsNormal Y₁] [CompactSpace Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₂] [IsNormal Y₂] [CompactSpace Y₂]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {s₁ : Y₁ ⟶ Spec (.of ℂ)}
    {s₂ : Y₂ ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {π : X ⟶ Z} {π₁ : Y₁ ⟶ Z} {π₂ : Y₂ ⟶ Z} {K : Divisor X} {Δ : RDivisor X}
    {K₁ : Divisor Y₁} {Δ₁ : RDivisor Y₁} {K₂ : Divisor Y₂} {Δ₂ : RDivisor Y₂}
    {φ₁ : X.RationalMap Y₁} {φ₂ : X.RationalMap Y₂}
    (h₁ : IsRealLogMinimalModel sX s₁ sZ π π₁ K Δ K₁ Δ₁ φ₁)
    (h₂ : IsRealLogMinimalModel sX s₂ sZ π π₂ K Δ K₂ Δ₂ φ₂)
    (hφ₁E : ∀ F : MMP.Mori.PrimeDivisor Y₁, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ₁ F)
    (hφ₂E : ∀ F : MMP.Mori.PrimeDivisor Y₂, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ₂ F)
    (hamp : IsRelativelyAmple π₂ (logCanonicalDivisor K₂ Δ₂)) :
    ∃ e : Y₁ ≅ Y₂, φ₁.compHom e.hom = φ₂ := by
  classical
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  have hY₁p := h₁.isProjectiveVariety_model
  have hY₂p := h₂.isProjectiveVariety_model
  haveI : QuasiCompact s₁ := hY₁p.toIsVariety.toQuasiCompact
  haveI : QuasiCompact s₂ := hY₂p.toIsVariety.toQuasiCompact
  haveI : IsSeparated s₁ := hY₁p.toIsVariety.toIsSeparated
  haveI : IsSeparated s₂ := hY₂p.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType s₁ := hY₁p.toIsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType s₂ := hY₂p.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsSeparated sX := hX.toIsVariety.toIsSeparated
  haveI := isSeparated_terminal_of sZ
  haveI := isSeparated_terminal_of sX
  haveI := isSeparated_terminal_of s₁
  haveI := isSeparated_terminal_of s₂
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  obtain ⟨hK₁, hΔ₁, N₁⟩ :=
    IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional hX hXq h₁ hφ₁E
  obtain ⟨hK₂, hΔ₂, N₂⟩ :=
    IsRealLogMinimalModel.isNefWeakModel_of_not_isInverseExceptional hX hXq h₂ hφ₂E
  subst hK₁ hΔ₁ hK₂ hΔ₂
  have hπ₁s : π₁ ≫ sZ = s₁ := h₁.comp_eq_model
  have hπ₂s : π₂ ≫ sZ = s₂ := h₂.comp_eq_model
  haveI : IsProper s₁ := isProper_of_isProjectiveMorphism _ hY₁p.isProjective
  haveI : IsProper s₂ := isProper_of_isProjectiveMorphism _ hY₂p.isProjective
  have hXn : IsNormalVariety ℂ sX := h₁.isRealLcPair.1
  have hY₁n : IsNormalVariety ℂ s₁ := h₁.isNormalVariety_model
  have hY₂n : IsNormalVariety ℂ s₂ := h₂.isNormalVariety_model
  -- the resolutions of `φ₁` and of `φ₂`, the second carrying the strict positivity
  obtain ⟨W₁, iW₁, lW₁, nW₁, sW₁, p₁, q₁, h₁', GX₁, GY₁, hR₁⟩ := h₁.exists_resolution
  obtain ⟨W₂, iW₂, lW₂, nW₂, sW₂, p₂, q₂, h₂', GX₂, GY₂, hR₂, hpos₂⟩ := h₂.exists_resolution_pos
  haveI := isProper_of_isProjectiveMorphism p₁ hR₁.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q₁ hR₁.isProjectiveMorphism_right
  haveI := isProper_of_isProjectiveMorphism p₂ hR₂.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q₂ hR₂.isProjectiveMorphism_right
  haveI := hR₁.isBirationalMorphism_left.isDominant
  haveI := hR₂.isBirationalMorphism_left.isDominant
  have hpq₁ : p₁ ≫ π = q₁ ≫ π₁ := MMP.Fourfold.comp_eq_comp_of_isOver π π₁ h₁.isOver p₁ q₁ h₁'
    hR₁.isInverse hR₁.compHom_eq
  have hpq₂ : p₂ ≫ π = q₂ ≫ π₂ := MMP.Fourfold.comp_eq_comp_of_isOver π π₂ h₂.isOver p₂ q₂ h₂'
    hR₂.isInverse hR₂.compHom_eq
  -- a common smooth projective model `W` of `W₁` and `W₂` over `X`
  let T : Bool → Scheme.{0} := fun b => cond b W₁ W₂
  let F : ∀ b, T b ⟶ X := fun b => Bool.rec (motive := fun b => T b ⟶ X) p₂ p₁ b
  haveI hFp : ∀ b, IsProper (F b) := fun b => by cases b <;> (dsimp [F, T]; infer_instance)
  obtain ⟨W, w, hWn, hwb, g, -, hwp, hg, -, -⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_smooth_projective_model sX F
      (fun b => by cases b; exacts [hR₂.isBirationalMorphism_left, hR₁.isBirationalMorphism_left])
      (fun b => by
        cases b
        · change IsNormalVariety ℂ (p₂ ≫ sX)
          rw [hR₂.comp_eq_left]; exact ⟨hR₂.isVariety, inferInstance⟩
        · change IsNormalVariety ℂ (p₁ ≫ sX)
          rw [hR₁.comp_eq_left]; exact ⟨hR₁.isVariety, inferInstance⟩)
      (κ := Empty) Empty.elim (fun j => j.elim)
  obtain ⟨hr₁w, hr₁p, hr₁b⟩ := hg true
  obtain ⟨hr₂w, hr₂p, hr₂b⟩ := hg false
  set r₁ : W ⟶ W₁ := g true with hr₁def
  set r : W ⟶ W₂ := g false with hrdef
  change r₁ ≫ p₁ = w at hr₁w
  change r ≫ p₂ = w at hr₂w
  set g₀ : W ⟶ X := w with hg₀def
  set g₁ : W ⟶ Y₁ := r₁ ≫ q₁ with hg₁def
  set g₂ : W ⟶ Y₂ := r ≫ q₂ with hg₂def
  have hg₁w : g₁ ≫ π₁ = w ≫ π := by
    rw [hg₁def, Category.assoc, ← hpq₁, ← Category.assoc, hr₁w]
  have hg₂w : g₂ ≫ π₂ = w ≫ π := by
    rw [hg₂def, Category.assoc, ← hpq₂, ← Category.assoc, hr₂w]
  have hg₀p : IsProjectiveMorphism g₀ := hwp
  have hg₁p : IsProjectiveMorphism g₁ := IsProjectiveMorphism.comp hr₁p
    hR₁.isProjectiveMorphism_right
  have hg₂p : IsProjectiveMorphism g₂ := IsProjectiveMorphism.comp hr₂p
    hR₂.isProjectiveMorphism_right
  haveI := hWn.1.toIsIntegral
  have hg₀b : IsBirationalMorphism g₀ := hwb
  have hg₁b : IsBirationalMorphism g₁ :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hr₁b hR₁.isBirationalMorphism_right
  have hg₂b : IsBirationalMorphism g₂ :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hr₂b hR₂.isBirationalMorphism_right
  have hrb : IsBirationalMorphism r := hr₂b
  haveI := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sX) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sX)
  haveI : QuasiCompact (w ≫ sX) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sX)
  haveI := isProper_of_isProjectiveMorphism g₀ hg₀p
  haveI := isProper_of_isProjectiveMorphism g₁ hg₁p
  haveI := isProper_of_isProjectiveMorphism g₂ hg₂p
  haveI := isProper_of_isProjectiveMorphism r₁ hr₁p
  haveI := isProper_of_isProjectiveMorphism r hr₂p
  haveI := hg₀b.isDominant
  haveI := hg₁b.isDominant
  haveI := hg₂b.isDominant
  haveI := hrb.isDominant
  haveI := hr₁b.isDominant
  have hg₀s : g₀ ≫ sX = w ≫ sX := rfl
  have hg₁s : g₁ ≫ s₁ = w ≫ sX := by
    rw [hg₁def, Category.assoc, hR₁.comp_eq_right, ← hR₁.comp_eq_left, ← Category.assoc, hr₁w]
  have hg₂s : g₂ ≫ s₂ = w ≫ sX := by
    rw [hg₂def, Category.assoc, hR₂.comp_eq_right, ← hR₂.comp_eq_left, ← Category.assoc, hr₂w]
  -- `h = g₀⁻¹`, and `g_i ∘ h = φ_i`
  obtain ⟨h, hinv⟩ : ∃ h : X.RationalMap W, MMP.Mori.RationalMap.IsInverse g₀.toRationalMap h :=
    MMP.Mori.RationalMap.IsBirational.exists_isInverse hg₀b
  have hψ : ∀ {W' Y' : Scheme.{0}} [IsIntegral W'] [IsIntegral Y'] (p' : W' ⟶ X) [IsProper p']
      (q' : W' ⟶ Y') (r' : W ⟶ W') (h' : X.RationalMap W'),
      IsBirationalMorphism p' → r' ≫ p' = w →
        MMP.Mori.RationalMap.IsInverse p'.toRationalMap h' →
          h.compHom (r' ≫ q') = h'.compHom q' := by
    intro W' Y' _ _ p' _ q' r' h' hp' hr' hinv'
    rw [← compHom_compHom]
    congr 1
    refine rationalMap_eq_of_compHom_eq hp' (π₁ := 𝟙 X) ?_ (compHom_eq_of_isInverse hinv')
    rw [compHom_compHom, hr', compHom_eq_of_isInverse hinv]
  have hψ₁ : h.compHom g₁ = φ₁ :=
    (hψ p₁ q₁ r₁ h₁' hR₁.isBirationalMorphism_left hr₁w hR₁.isInverse).trans hR₁.compHom_eq
  have hψ₂ : h.compHom g₂ = φ₂ :=
    (hψ p₂ q₂ r h₂' hR₂.isBirationalMorphism_left hr₂w hR₂.isInverse).trans hR₂.compHom_eq
  -- the pulled-back adjoints agree
  obtain ⟨D₁, hD₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₁
    (isCartierCombination_of_isQFactorial h₁.isQFactorial
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)))
  obtain ⟨D₂, hD₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₂
    (isCartierCombination_of_isQFactorial h₂.isQFactorial
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₂ K)
        (MMP.Mori.RationalMap.transformDivisor φ₂ Δ)))
  have hcomm₁₂' : g₁ ≫ π₁ = g₂ ≫ π₂ := hg₁w.trans hg₂w.symm
  have hDD : D₁ = D₂ := (N₁.eq_of_isRCartierPullback_and_isNefModelEquivalent N₂).1 (w ≫ sX)
    g₁ g₂ h hWn.1 hg₁s hg₂s hg₁p hg₂p hg₁b hg₂b hψ₁ hψ₂ hD₁ hD₂
  -- rigidity: a morphism `gg : Y₁ ⟶ Y₂` with `g₁ ≫ gg = g₂`
  haveI : IsProper w := isProper_of_isProjectiveMorphism w hwp
  haveI : IsProper (w ≫ sX) := inferInstance
  haveI : IsSeparated (π₂ ≫ sZ) := by rw [hπ₂s]; infer_instance
  haveI : IsSeparated π₂ := IsSeparated.of_comp π₂ sZ
  have hcurve : ∀ C : Set W, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
      (g₁.base '' C).Subsingleton → (g₂.base '' C).Subsingleton := by
    intro C hCc hCi hCd hC1
    by_contra hns
    set x := hCi.genericPoint with hxdef
    have hxC : closure ({x} : Set W) = C := hCi.isGenericPoint_genericPoint hCc
    have hΓp : IsProperCurve (w ≫ sX) x := MMP.Mori.isProperCurve_of_isProper _ (by
      rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hxC]; exact hCd)
    let Γ : ProperCurve (w ≫ sX) := ⟨x, hΓp⟩
    have hΓ₁ : Γ.IsContractedBy g₁ := fun y hy =>
      hC1 ⟨y, hxC ▸ hy, rfl⟩ ⟨x, hxC ▸ subset_closure rfl, rfl⟩
    have hΓ₂ : ¬ Γ.IsContractedBy g₂ := fun hc => hns (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← hxC] at ha hb
      exact (hc a ha).trans (hc b hb).symm)
    let Γ₂ : ProperCurve s₂ := ⟨g₂ x, MMP.Fourfold.Oai4C1.isProperCurve_map g₂ hg₂s Γ hΓ₂⟩
    have hΓ₂c : Γ₂.IsContractedBy π₂ := MMP.Fourfold.Oai4C1.isContractedBy_map g₂ hg₂s π₂ Γ hΓ₂
      (hcomm₁₂' ▸ isContractedBy_comp π₁ hΓ₁)
    -- `D₂ · Γ = [k(Γ) : k(Γ₂)] (A₂ · Γ₂) > 0`
    obtain ⟨m, c, L, L', hL, hAL, hpb, hDL⟩ := hD₂
    have hL'c : ∀ j, (L' j).IsCartier := fun j => (hpb j).2.isCartier (hL j)
    have hx₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (w ≫ sX) Γ c L' hL'c
    rw [← hDL] at hx₂
    have hmul : ∀ j, ((L' j).degreeOn ℂ (w ≫ sX) Γ.ι Γ.dim_le (hL'c j) : ℝ) =
        (residueFieldDegree g₂ Γ.point : ℝ) *
          ((L j).degreeOn ℂ s₂ Γ₂.ι Γ₂.dim_le (hL j) : ℝ) := fun j =>
      MMP.Fourfold.degreeOn_eq_mul_of_isPullback g₂ hg₂s (hL j) (hpb j).2 (hL'c j) Γ Γ₂ rfl
    have hA := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ s₂ Γ₂ c L hL
    rw [← hAL] at hA
    have hApos := isRIntersectionNumber_pos_of_isRelativelyAmple π₂ hamp Γ₂ hΓ₂c c L _ hA
    have hd := MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy g₂ hg₂s Γ hΓ₂
    -- `D₁ · Γ = 0`
    obtain ⟨m₁, c₁, L₁, L₁', hL₁, -, hpb₁, hDL₁⟩ := hD₁
    have hL₁'c : ∀ j, (L₁' j).IsCartier := fun j => (hpb₁ j).2.isCartier (hL₁ j)
    have hx₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (w ≫ sX) Γ c₁ L₁' hL₁'c
    rw [← hDL₁, hDD] at hx₁
    have h0 : ∀ j, (L₁' j).degreeOn ℂ (w ≫ sX) Γ.ι Γ.dim_le (hL₁'c j) = 0 := fun j =>
      MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_zero g₁ hg₁s (hL₁ j) (hpb₁ j).2 Γ hΓ₁
    have heq := (IsRIntersectionNumber.eq_and_linear ℂ (w ≫ sX) Γ).1 _ _ _ _ _ _ _ hx₁ hx₂
    simp only [h0, Int.cast_zero, mul_zero, Finset.sum_const_zero, hmul] at heq
    have hpos : 0 < ∑ j, c j * ((residueFieldDegree g₂ Γ.point : ℝ) *
        ((L j).degreeOn ℂ s₂ Γ₂.ι Γ₂.dim_le (hL j) : ℝ)) := by
      simp only [mul_left_comm (c _), ← Finset.mul_sum]
      exact mul_pos (by exact_mod_cast hd) hApos
    linarith
  obtain ⟨gg, hgg, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isBirationalMorphism_of_forall_curve
    s₁ hY₁n.1 (sX := π₁) (sY := π₂) g₁ (by rw [hg₁s]; exact hWn.1) hg₁b g₂ hcomm₁₂' hcurve
  have hggs : gg ≫ s₂ = s₁ := AlgebraicGeometry.ext_of_isDominant g₁ (by
    rw [← Category.assoc, hgg, hg₂s, hg₁s])
  have hggπ : gg ≫ π₂ = π₁ := AlgebraicGeometry.ext_of_isDominant_of_isSeparated sZ
    (by rw [Category.assoc, hπ₂s, hggs, hπ₁s]) g₁ (by rw [← Category.assoc, hgg, hg₂w, hg₁w])
  haveI : LocallyOfFiniteType (gg ≫ s₂) := by rw [hggs]; infer_instance
  haveI : LocallyOfFiniteType gg := LocallyOfFiniteType.of_comp (f := gg) (g := s₂) inferInstance
  haveI : IsProper (gg ≫ s₂) := by rw [hggs]; infer_instance
  haveI : IsProper gg := IsProper.of_comp gg s₂
  have hggb : IsBirationalMorphism gg :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left g₁ gg hg₁b (hgg ▸ hg₂b)
  haveI := hggb.isDominant
  -- `gg` contracts no prime divisor
  have hWg₀ : IsNormalVariety ℂ (g₀ ≫ sX) := by rw [hg₀s]; exact hWn
  have hWg₁ : IsNormalVariety ℂ (g₁ ≫ s₁) := by rw [hg₁s]; exact hWn
  obtain ⟨GX, hGX, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₀
    (isCartierCombination_of_isQFactorial hXq (logCanonicalDivisor K Δ))
  have hsmall : ∀ F : MMP.Mori.PrimeDivisor Y₁,
      ∃ F' : MMP.Mori.PrimeDivisor Y₂, gg F.genericPoint = F'.genericPoint := by
    intro F
    obtain ⟨P, hP⟩ := exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional hφ₁E F
    obtain ⟨PW, hPW, hPWiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWg₀ hg₀b P
    have hF : g₁ PW.genericPoint = F.genericPoint :=
      (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse g₀ hg₀b hinv g₁ hψ₁ P PW hPW
        F).mp hP
    obtain ⟨g', hg', hPg, hg'P⟩ :=
      MMP.Fourfold.exists_rep_apply_eq_of_isInverse g₀ hg₀b hinv P PW hPW
    by_cases hco : Order.coheight (g₂ PW.genericPoint) ≤ 1
    · obtain ⟨F', hF', -⟩ :=
        MMP.Fourfold.exists_primeDivisor_of_coheight_le_one g₂ hg₂b.functionFieldMap_bijective PW
          hco
      exact ⟨F', by rw [← hF, ← Scheme.Hom.comp_apply, hgg, hF']⟩
    exfalso
    -- `P` is contracted by `φ₂`
    have hexc : MMP.Mori.RationalMap.IsExceptional φ₂ P := by
      by_contra hne
      have := MMP.Fourfold.SamePrimes.coheight_apply_le_one_of_not_isExceptional g₂ g'
        (by rw [Scheme.RationalMap.compHom_toRationalMap, hg', hψ₂]) hPg hne
      rw [hg'P] at this
      exact hco this
    -- the strict transform of `P` on `W₂`, where the comparison is positive
    have hW₂p : IsNormalVariety ℂ (p₂ ≫ sX) := by
      rw [hR₂.comp_eq_left]; exact ⟨hR₂.isVariety, inferInstance⟩
    obtain ⟨P₂, hP₂, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn
        hW₂p hR₂.isBirationalMorphism_left P
    haveI : IsSeparated sW₂ := hR₂.isVariety.toIsSeparated
    haveI := isSeparated_terminal_of sW₂
    haveI : IsSeparated (p₂ ≫ sX) := by rw [hR₂.comp_eq_left]; infer_instance
    haveI : IsSeparated p₂ := IsSeparated.of_comp p₂ sX
    have hP₂h : MMP.Mori.RationalMap.transformPrimeDivisor h₂' P = some P₂ :=
      (MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse p₂ hR₂.isBirationalMorphism_left
        hR₂.isInverse (𝟙 W₂) (rationalMap_compHom_id h₂') P P₂ hP₂ P₂).mpr rfl
    have hpos := hpos₂ P hexc P₂ hP₂h
    -- transfer to `W` through `r : W ⟶ W₂`
    have hrp : r ≫ p₂ = g₀ := hr₂w
    have hrq : r ≫ q₂ = g₂ := rfl
    haveI : IsDominant (r ≫ p₂) := by rw [hrp]; infer_instance
    haveI : IsDominant (r ≫ q₂) := by rw [hrq]; infer_instance
    have hGXr : MMP.Flips.IsRCartierPullback r GX₂ GX :=
      isRCartierPullback_of_isRCartierPullback_comp hR₂.isRCartierPullback_left
        (by rw [hrp]; exact hGX)
    have hGYr : MMP.Flips.IsRCartierPullback r GY₂ D₂ :=
      isRCartierPullback_of_isRCartierPullback_comp hR₂.isRCartierPullback_right
        (by rw [hrq]; exact hD₂)
    have := P.isDiscreteValuationRing_localRing
    have hrP : r PW.genericPoint = P₂.genericPoint :=
      MMP.Fourfold.eq_of_map_eq_of_valuationRing
        hR₂.isBirationalMorphism_left.functionFieldMap_bijective
        (by rw [← Scheme.Hom.comp_apply, hrp, hPW]) hP₂
    have := P₂.isDiscreteValuationRing_localRing
    haveI : ValuationRing (W₂.presheaf.stalk (r PW.genericPoint)) := by
      rw [hrP]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing r hrb.functionFieldMap_bijective
      PW.genericPoint
    have c1 : GX.coeff PW = GX₂.coeff P₂ :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P₂ hrP hGXr
    have c2 : D₂.coeff PW = GY₂.coeff P₂ :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P₂ hrP hGYr
    -- on the other side the comparison vanishes at `P_W`, which `φ₁` keeps
    haveI := hPWiso
    have c3 : GX.coeff PW = (logCanonicalDivisor K Δ).coeff P :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW P hPW hGX
    have := F.isDiscreteValuationRing_localRing
    haveI : ValuationRing (Y₁.presheaf.stalk (g₁ PW.genericPoint)) := by
      rw [hF]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g₁ hg₁b.functionFieldMap_bijective
      PW.genericPoint
    have c4 : D₁.coeff PW = (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)).coeff F :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback PW F hF hD₁
    have c5 : (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ K)
        (MMP.Mori.RationalMap.transformDivisor φ₁ Δ)).coeff F =
        (logCanonicalDivisor K Δ).coeff P := by
      rw [← transformDivisor_logCanonicalDivisor]
      exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP
        (fun R hR => eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hY₁n hWg₀
          (hg₀s.trans hg₁s.symm) hg₀b hg₁b hinv hψ₁ hR hP) _
    rw [DivisorWithCoeffs.coeff_sub, ← c1, ← c2, ← hDD, c3, c4, c5, sub_self] at hpos
    exact lt_irrefl _ hpos
  -- `gg` is an isomorphism: the pull-back of the push-forward of an ample `H` is `H`
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s₁ := hY₁p
  obtain ⟨H, hHc, -, hHa⟩ := MMP.Mori.exists_isCartier_isEffective_isAmple s₁
  have hHr : MMP.Flips.IsRelativelyAmpleCartier gg H :=
    MMP.Flips.isRelativelyAmpleCartier_of_isRelativelyAmple hHc
      (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf gg hHc hHa)
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback gg
    (isCartierCombination_of_isQFactorial h₂.isQFactorial
      (MMP.Mori.RationalMap.transformDivisor gg.toRationalMap (Divisor.toRDivisor H)))
  have hGH : G = Divisor.toRDivisor H := by
    refine Finsupp.ext fun F => ?_
    obtain ⟨F', hF'⟩ := hsmall F
    have := F'.isDiscreteValuationRing_localRing
    haveI : ValuationRing (Y₂.presheaf.stalk (gg F.genericPoint)) := by rw [hF']; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing gg hggb.functionFieldMap_bijective
      F.genericPoint
    have c1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback F F' hF' hG
    obtain ⟨E, hE, -, hEc⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hY₂n
        (by rw [hggs]; exact hY₁n) hggb F'
    haveI : IsSeparated gg := inferInstance
    have hEF : E = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Fourfold.eq_of_map_eq_of_valuationRing hggb.functionFieldMap_bijective hE hF')
    change G.coeff F = (Divisor.toRDivisor H).coeff F
    rw [c1]
    change MMP.Mori.RationalMap.transformDivisor gg.toRationalMap (Divisor.toRDivisor H) F' = _
    rw [hEc, hEF]
    rfl
  have hamp' : MMP.Flips.IsRelativelyAmple gg G := by
    rw [hGH]
    exact ⟨1, fun _ => 1, fun _ => H, le_rfl, fun _ => one_pos, fun _ => hHr, by simp⟩
  haveI : IsNoetherian Y₁ := ⟨⟩
  haveI := MMP.Flips.isIso_of_isRelativelyAmple_of_isRCartierPullback gg hggb hG hamp'
  refine ⟨asIso gg, ?_⟩
  rw [asIso_hom, ← hψ₁, compHom_compHom, hgg, hψ₂]

/-! ### Shifting a nef weak model by a numerically trivial divisor -/

section WeakModelShift

/-- Nefness does not depend on how the structure morphism is written. -/
private theorem isRelativelyNef_of_eq_structure {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of k)} (hs : s = s')
    [QuasiCompact s] [QuasiCompact s'] {g : X ⟶ Y} {D : RDivisor X}
    (h : IsRelativelyNef k s g D) : IsRelativelyNef k s' g D := by
  subst hs
  exact h

/-- `0 ≡ 0` over any morphism. -/
private theorem isNumericallyEquivalentOver_zero_zero {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (g : X ⟶ Y) : IsNumericallyEquivalentOver k sX g (0 : RDivisor X) 0 :=
  ⟨⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C _ _ _ _ _ _ _ _ _ h₁ h₂ =>
      (eq_zero_of_isRIntersectionNumber_zero C h₁).trans
        (eq_zero_of_isRIntersectionNumber_zero C h₂).symm⟩

/-- **Two pull-backs of a numerically trivial divisor agree.** Let `p : W ⟶ X`, `q : W ⟶ Y`
resolve a birational contraction `φ : X ⤏ Y` over `Z`. If `T` is numerically trivial over `Z` and
so is `φ_* T`, then `p^* T = q^* φ_* T`: the difference is numerically trivial over `Y` and has
zero push-forward, so it vanishes by the negativity lemma. -/
private theorem eq_of_isRCartierPullback_of_isNumericallyTrivialOver
    {X Y Z W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hXn : IsNormalVariety ℂ sX) (hYn : IsNormalVariety ℂ sY) (hWv : MMP.Mori.IsVariety ℂ sW)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {φ : X.RationalMap Y}
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) (hpW : p ≫ sX = sW) (hqW : q ≫ sY = sW)
    (hpp : IsProjectiveMorphism p) (hqp : IsProjectiveMorphism q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ)
    (hpq : p ≫ π = q ≫ πY) {T : RDivisor X}
    (hT : IsNumericallyTrivialOver ℂ sX π T)
    (hTY : IsNumericallyTrivialOver ℂ sY πY (MMP.Mori.RationalMap.transformDivisor φ T))
    {PT QT : RDivisor W} (hPT : MMP.Flips.IsRCartierPullback p T PT)
    (hQT : MMP.Flips.IsRCartierPullback q (MMP.Mori.RationalMap.transformDivisor φ T) QT) :
    PT = QT := by
  classical
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : QuasiCompact (p ≫ sX) := by rw [hpW]; infer_instance
  haveI : QuasiCompact (q ≫ sY) := by rw [hqW]; infer_instance
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWp : IsNormalVariety ℂ (p ≫ sX) := by rw [hpW]; exact ⟨hWv, inferInstance⟩
  have hWq : IsNormalVariety ℂ (q ≫ sY) := by rw [hqW]; exact ⟨hWv, inferInstance⟩
  -- `±p^* T` and `±q^* φ_* T` are nef over `q`
  have hnef : ∀ {D : RDivisor X} {G : RDivisor W}, IsNumericallyTrivialOver ℂ sX π D →
      MMP.Flips.IsRCartierPullback p D G → IsRelativelyNef ℂ sW q G := by
    intro D G hD hG
    have := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback πY π q p hpq.symm
      (isRelativelyNef_of_isNumericallyTrivialOver hD) hG
    exact isRelativelyNef_of_eq_structure hpW this
  have hnef' : ∀ {D : RDivisor Y} {G : RDivisor W}, IsNumericallyTrivialOver ℂ sY πY D →
      MMP.Flips.IsRCartierPullback q D G → IsRelativelyNef ℂ sW q G := by
    intro D G hD hG
    have := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback πY πY q q rfl
      (isRelativelyNef_of_isNumericallyTrivialOver hD) hG
    exact isRelativelyNef_of_eq_structure hqW this
  have hPTn : MMP.Flips.IsRCartierPullback p (-T) (-PT) := by
    simpa using MMP.Fourfold.isRCartierPullback_smul (-1) hPT
  have hQTn :
      MMP.Flips.IsRCartierPullback q (-MMP.Mori.RationalMap.transformDivisor φ T) (-QT) := by
    simpa using MMP.Fourfold.isRCartierPullback_smul (-1) hQT
  have h1 : IsRelativelyNef ℂ sW q (PT - QT) := by
    rw [sub_eq_add_neg]
    exact isRelativelyNef_add (hnef hT hPT) (hnef' (isNumericallyTrivialOver_neg hTY) hQTn)
  have h2 : IsRelativelyNef ℂ sW q (-(PT - QT)) := by
    rw [neg_sub, sub_eq_add_neg]
    exact isRelativelyNef_add (hnef' hTY hQT) (hnef (isNumericallyTrivialOver_neg hT) hPTn)
  -- the push-forward of the difference vanishes
  have hpush : MMP.Mori.RationalMap.transformDivisor q.toRationalMap (PT - QT) = 0 := by
    obtain ⟨h', hinv'⟩ : ∃ h' : Y.RationalMap W,
        MMP.Mori.RationalMap.IsInverse q.toRationalMap h' :=
      MMP.Mori.RationalMap.IsBirational.exists_isInverse hqb
    haveI : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_terminal_of sY
    have hidE : ∀ F : MMP.Mori.PrimeDivisor Y,
        ¬ MMP.Flips.RationalMap.IsInverseExceptional (Scheme.Hom.toRationalMap (𝟙 Y)) F :=
      fun F hF => hF F ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 Y) F
        F).mpr rfl)
    have t1 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hXn hYn hφE p q h hWp hWq
      hpb hqb hinv hcomp hPT
    have t2 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hYn hYn hidE q q h' hWq hWq
      hqb hqb hinv' (compHom_eq_of_isInverse hinv') hQT
    rw [transformDivisor_id_toRationalMap hYn] at t2
    rw [map_sub, t1, t2, sub_self]
  have hcoeff : ∀ E, ¬ IsExceptionalPrimeDivisor sY q E → (PT - QT).coeff E = 0 := by
    intro E hE
    obtain ⟨P, -, -, hP⟩ :=
      MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hYn q hWq hqb
        E hE
    have := hP (PT - QT)
    rw [hpush] at this
    exact this.symm
  have hcomb : IsCartierCombination (PT - QT) := by
    obtain ⟨m, r, L, L', hL, -, hpb', rfl⟩ := hPT
    obtain ⟨m', r', M, M', hM, -, hpb'', rfl⟩ := hQT
    refine ⟨m + m', Fin.append r (-r'), Fin.append L' M',
      Fin.addCases (fun j => by simpa using (hpb' j).2.isCartier (hL j))
        (fun j => by simpa using (hpb'' j).2.isCartier (hM j)), ?_⟩
    simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    rw [Fin.sum_univ_add]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  have hcomb' : IsCartierCombination (-(PT - QT)) := by
    obtain ⟨m, r, L, hL, hD⟩ := hcomb
    exact ⟨m, -r, L, hL, by rw [hD]; simp [Finset.sum_neg_distrib, neg_smul]⟩
  have h00 : MMP.Flips.IsRCartierPullback q (0 : RDivisor Y) 0 := by
    simpa using MMP.Fourfold.isRCartierPullback_smul 0 hQT
  have hc0 : IsCartierCombination (0 : RDivisor Y) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hsW : q ≫ sY = sW := hqW
  have e1 := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sY sW hYn
    ⟨hWv, inferInstance⟩ q hsW hqb hc0 h00 hcomb h1 hcomb' (fun E hE => by
      rw [DivisorWithCoeffs.coeff_neg, hcoeff E hE, neg_zero]) (by
      rw [add_neg_cancel]; exact isNumericallyEquivalentOver_zero_zero q)
  have e2 := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sY sW hYn
    ⟨hWv, inferInstance⟩ q hsW hqb hc0 h00 hcomb' h2 hcomb (fun E hE => (hcoeff E hE).ge) (by
      rw [neg_add_cancel]; exact isNumericallyEquivalentOver_zero_zero q)
  rw [DivisorWithCoeffs.isEffective_iff_nonneg] at e1 e2
  refine sub_eq_zero.mp (Finsupp.ext fun E => le_antisymm ?_ (e2 E))
  have := e1 E
  simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
  linarith

/-- **A numerically trivial shift of a nef weak model.** If `φ : X ⤏ Y` is a nef weak model of
`(X, Δ)` over `Z` and `T` is numerically trivial over `Z`, with `φ_* T` numerically trivial over
`Z`, then `φ` is a nef weak model of `(X, Δ + T)`: the adjoint changes by a numerically trivial
divisor and the comparison on a common resolution is unchanged. -/
private theorem IsNefWeakModel.add_of_isNumericallyTrivialOver
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hXq : IsQFactorial sX)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ T : RDivisor X} {φ : X.RationalMap Y}
    (N : IsNefWeakModel sX sY sZ π πY K Δ φ)
    (hT : IsNumericallyTrivialOver ℂ sX π T)
    (hTY : IsNumericallyTrivialOver ℂ sY πY (MMP.Mori.RationalMap.transformDivisor φ T)) :
    IsNefWeakModel sX sY sZ π πY K (Δ + T) φ := by
  classical
  have hXn := N.isNormalVariety_source
  have hYn := N.isNormalVariety_target
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal_of sZ
  have hlc : ∀ {V : Scheme.{0}} (K' : Divisor V) (A B : RDivisor V),
      logCanonicalDivisor K' (A + B) = logCanonicalDivisor K' A + B := by
    intros; simp [logCanonicalDivisor, add_assoc]
  obtain ⟨W, iW, lW, nW, sW, p, q, h, hWv, hWs, hpW, hqW, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, heff, hexc⟩ := N.exists_resolution
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  obtain ⟨PT, hPT, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hT.1
  obtain ⟨QT, hQT, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hTY.1
  have hpq : p ≫ π = q ≫ πY :=
    MMP.Fourfold.comp_eq_comp_of_isOver π πY N.isOver p q h hinv hcomp
  have hPQ := eq_of_isRCartierPullback_of_isNumericallyTrivialOver hXn hYn hWv
    N.not_isInverseExceptional p q h hpW hqW hpp hqp hpb hqb hinv hcomp hpq hT hTY hPT hQT
  have htr : MMP.Mori.RationalMap.transformDivisor φ (Δ + T) =
      MMP.Mori.RationalMap.transformDivisor φ Δ + MMP.Mori.RationalMap.transformDivisor φ T :=
    map_add _ _ _
  exact
    { isNormalVariety_source := hXn
      isProjectiveVariety_source := N.isProjectiveVariety_source
      comp_eq_source := N.comp_eq_source
      isCanonicalDivisor := N.isCanonicalDivisor
      isCartierCombination := isCartierCombination_of_isQFactorial hXq _
      isNormalVariety_target := hYn
      isProjectiveVariety_target := N.isProjectiveVariety_target
      comp_eq_target := N.comp_eq_target
      isBirational := N.isBirational
      isOver := N.isOver
      not_isInverseExceptional := N.not_isInverseExceptional
      isRelativelyNef := by
        rw [htr, hlc]; exact isRelativelyNef_add_isNumericallyTrivialOver N.isRelativelyNef hTY
      exists_resolution := ⟨W, iW, lW, nW, sW, p, q, h, hWv, hWs, hpW, hqW, hpp, hqp, hpb, hqb,
        hinv, hcomp, GY + PT, GZ + QT,
        by rw [hlc]; exact MMP.Fourfold.isRCartierPullback_add hGY hPT,
        by rw [htr, hlc]; exact MMP.Fourfold.isRCartierPullback_add hGZ hQT,
        by rw [hPQ, add_sub_add_right_eq_sub]; exact heff,
        by rw [hPQ, add_sub_add_right_eq_sub]; exact hexc⟩ }

end WeakModelShift

/-! ### Pseudo-effectivity of adjoints with an ample model -/

section PseudoEffective

open MMP.Intersection in
/-- **A Cartier divisor with effective Weil divisor is effective** on a normal integral scheme: a
local equation `a / b` at `x` has `ord_Γ a ≥ ord_Γ b` along every prime divisor `Γ` through `x`,
so `a / b` is regular at `x` by algebraic Hartogs. -/
private theorem isEffective_of_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {A : X.CartierDivisor} {w : Divisor X}
    (hA : IsWeilDivisorOfCartier A w) (hw : ∀ P, 0 ≤ w.coeff P) :
    MMP.Intersection.IsEffective A := by
  intro x
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt A x
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set alg := algebraMap (X.presheaf.stalk x) X.functionField with halg
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have ha' : alg a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb' : alg b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
      X.ord (alg b) Γ.genericPoint ≤ X.ord (alg a) Γ.genericPoint := by
    intro Γ hΓ
    have hspec : Γ.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
      exact specializes_iff_mem_closure.mpr hΓ
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Γ
    have hsa := MMP.Intersection.stalkSpecializes_ne_zero hspec ha0
    have hsb := MMP.Intersection.stalkSpecializes_ne_zero hspec hb0
    rw [halg, ← MMP.Mori.algebraMap_stalkSpecializes hspec a,
      ← MMP.Mori.algebraMap_stalkSpecializes hspec b,
      ord_algebraMap_stalk h1 hsa, ord_algebraMap_stalk h1 hsb]
    have hsf := hf.stalkSpecializes hspec
    have hsab := hab.stalkSpecializes hspec
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Γ).genericPoint) :=
      krullDimLE_of_coheight_le h1.le
    have hN := isOrderAlong_of_isFraction (V := primeDivisorSubvariety Γ) hsf
      (mem_nonZeroDivisors_of_ne_zero hsa) (mem_nonZeroDivisors_of_ne_zero hsb) hsab
    have e := (hA Γ).unique hN
    have key : ∀ {u v u' v' : ℤ}, u = u' → v = v' → w.coeff Γ = u' - v' → 0 ≤ w.coeff Γ →
        v ≤ u := by
      intros; omega
    exact key rfl rfl e (hw Γ)
  obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x
    (div_ne_zero ha' hb') fun Γ hΓ => by
      rw [div_eq_mul_inv, Scheme.ord_mul ha' (inv_ne_zero hb')]
      have := MMP.Mori.ord_zpow Γ.genericPoint hb' (-1)
      rw [zpow_neg, zpow_one] at this
      rw [this]
      have := hord Γ hΓ
      linarith
  have har : a = b * r := hinj (by rw [map_mul, hr]; field_simp)
  have hfr : f = stalkToTotalQuotient x r := by
    apply hab.1.mul_left_cancel
    rw [hab.2, har, map_mul]
  rw [hfr] at hf
  obtain ⟨U, hxU, hU⟩ := IsLocalEquationAt.exists_isEffectiveOn hf
  exact ⟨U, hxU, hU⟩

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- On a `ℚ`-factorial variety an effective `ℝ`-divisor is a nonnegative combination of Weil
divisors of effective Cartier divisors. -/
private theorem exists_effective_presentation (hXq : IsQFactorial sX) {N : RDivisor X}
    (hN : ∀ P, 0 ≤ N.coeff P) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (A : Fin n → X.CartierDivisor),
      (∀ j, 0 ≤ c j) ∧ (∀ j, (L j).IsCartier) ∧
      (∀ j, MMP.Intersection.IsWeilDivisorOfCartier (A j) (L j)) ∧
      (∀ j, MMP.Intersection.IsEffective (A j)) ∧
      N = ∑ j, c j • Divisor.toRDivisor (L j) := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hXq.2 (Finsupp.single P 1)
  let e := N.support.equivFin
  let Q : Fin N.support.card → MMP.Mori.PrimeDivisor X := fun j => e.symm j
  let L : Fin N.support.card → Divisor X := fun j =>
    ((m (Q j) : ℕ) : ℤ) • Finsupp.single (Q j) (1 : ℤ)
  have hLc : ∀ j, (L j).IsCartier := fun j => hmC _
  choose A hA using fun j => exists_isWeilDivisorOfCartier_of_isCartier (hLc j)
  refine ⟨N.support.card, fun j => N.coeff (Q j) / m (Q j), L, A, fun j => ?_, hLc, hA,
    fun j => isEffective_of_isWeilDivisorOfCartier (hA j) fun P => ?_, ?_⟩
  · exact div_nonneg (hN _) (Nat.cast_nonneg _)
  · simp only [L, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp
  · refine Finsupp.ext fun P => ?_
    change N.coeff P = (∑ j, (N.coeff (Q j) / m (Q j)) • Divisor.toRDivisor (L j)).coeff P
    rw [MMP.Fourfold.coeff_sum_smul_toRDivisor]
    have hterm : ∀ j, N.coeff (Q j) / (m (Q j) : ℝ) * ((L j).coeff P : ℝ) =
        if Q j = P then N.coeff P else 0 := fun j => by
      simp only [L, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
      by_cases h : Q j = P
      · subst h
        have := (hm (Q j)).ne'
        simp only [if_true, mul_one]
        push_cast
        field_simp
      · simp [h]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    by_cases hP : P ∈ N.support
    · rw [Finset.sum_eq_single (e ⟨P, hP⟩) (fun j _ hj => if_neg fun h => hj (by
        rw [← Equiv.apply_symm_apply e j]; congr 1; exact Subtype.ext h))
        (fun h => (h (Finset.mem_univ _)).elim)]
      simp only [Q, Equiv.symm_apply_apply, if_true]
    · rw [Finset.sum_eq_zero fun j _ => if_neg fun (h : Q j = P) => hP (h ▸ (e.symm j).2)]
      exact Finsupp.notMem_support_iff.mp hP

/-- The Weil divisor of the real combination `∑ rⱼ Aⱼ` of Cartier divisors with Weil
divisors `Lⱼ` is `∑ rⱼ Lⱼ`. -/
private theorem coeff_sum_eq_sum_primeDivisorOrder {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (A : Fin m → X.CartierDivisor)
    (hA : ∀ j, MMP.Intersection.IsWeilDivisorOfCartier (A j) (L j)) (P : MMP.Mori.PrimeDivisor X) :
    (∑ j, r j • Divisor.toRDivisor (L j)).coeff P =
      (∑ j, r j • KCartierDivisor.ofCartier ℝ (A j)).sum
        fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ) := by
  classical
  rw [← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    MMP.Fourfold.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [KCartierDivisor.ofCartier, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Finsupp.sum_single_index (zero_mul _), (hA j P).primeDivisorOrder_eq]

variable [QuasiCompact sX]

/-- **Pseudo-effectivity from an effective numerical representative.** If an `ℝ`-Cartier divisor
`M` on a `ℚ`-factorial variety is numerically equivalent over `Z` to an effective `N`, then some
`ℝ`-Cartier divisor with Weil divisor `M` has its class in the effective cone of `N¹(X/Z)`. -/
private theorem exists_isRelativelyPseudoEffective_of_isNumericallyEquivalentOver
    (hXq : IsQFactorial sX) (π : X ⟶ Z) {M N : RDivisor X}
    (hMN : IsNumericallyEquivalentOver ℂ sX π M N) (hN : ∀ P, 0 ≤ N.coeff P) :
    ∃ D' : KCartierDivisor ℝ X,
      (∀ P : MMP.Mori.PrimeDivisor X,
        M.coeff P = D'.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ)) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX π D' := by
  classical
  obtain ⟨m, r, L, hL, hM⟩ := hMN.1
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hM
  choose A hA using fun j => exists_isWeilDivisorOfCartier_of_isCartier (hL j)
  obtain ⟨n, c, L', A', hc, hL', hA', hA'e, hN'⟩ := exists_effective_presentation hXq hN
  refine ⟨∑ j, r j • KCartierDivisor.ofCartier ℝ (A j), fun P => ?_, ?_⟩
  · rw [hM]; exact coeff_sum_eq_sum_primeDivisorOrder r L A hA P
  · refine subset_closure ?_
    have hcls : MMP.Fourfold.relativeNumericalDivisorClass sX π
        (∑ j, r j • KCartierDivisor.ofCartier ℝ (A j)) =
        MMP.Fourfold.relativeNumericalDivisorClass sX π
          (∑ j, c j • KCartierDivisor.ofCartier ℝ (A' j)) := by
      refine (Submodule.Quotient.eq _).2 ?_
      rw [LinearMap.mem_ker]
      funext C
      rw [map_sub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
      have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 r L hL
      rw [← hM] at e₁
      have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 c L' hL'
      rw [← hN'] at e₂
      rw [← eq_relativeDegreeMap_of_isRIntersectionNumber π hA C.1 C.2 e₁,
        ← eq_relativeDegreeMap_of_isRIntersectionNumber π hA' C.1 C.2 e₂]
      exact hMN.2.2 C.1 C.2 _ _ _ _ _ _ _ _ e₁ e₂
    rw [hcls, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact (MMP.Fourfold.relativeEffectiveCone sX π).smul_mem (hc j)
      (PointedCone.subset_hull ⟨A' j, hA'e j, rfl⟩)

end PseudoEffective

/-! ### Pushing numerical classes forward along a resolution -/

section PushForward

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- Numerically equivalent divisors differ by a numerically trivial one. -/
private theorem isNumericallyTrivialOver_sub {g : X ⟶ Y} {A B : RDivisor X}
    (h : IsNumericallyEquivalentOver k sX g A B) : IsNumericallyTrivialOver k sX g (A - B) := by
  obtain ⟨⟨m, r, L, hL, hA⟩, ⟨m', r', L', hL', hB⟩, hAB⟩ := id h
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hA hB
  refine ⟨⟨m + m', Fin.append r (-r'), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  · simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    rw [Fin.sum_univ_add, hA, hB]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib, neg_smul]
  · have eA := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
    rw [← hA] at eA
    have eB := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r' L' hL'
    rw [← hB] at eB
    have hsub := (IsRIntersectionNumber.eq_and_linear k sX C).2 A B r L r' L' _ _ 1 (-1) eA eB
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hsub
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₁ hsub,
      eq_zero_of_isRIntersectionNumber_zero C h₂, hAB C hC _ _ _ _ _ _ _ _ eA eB]
    ring

/-- Divisors differing by a numerically trivial one are numerically equivalent. -/
private theorem isNumericallyEquivalentOver_of_isNumericallyTrivialOver_sub {g : X ⟶ Y}
    {A B : RDivisor X} (hA : IsCartierCombination A) (hB : IsCartierCombination B)
    (h : IsNumericallyTrivialOver k sX g (A - B)) : IsNumericallyEquivalentOver k sX g A B := by
  refine ⟨hA, hB, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have hsub := (IsRIntersectionNumber.eq_and_linear k sX C).2 A B r₁ L₁ r₂ L₂ _ _ 1 (-1) h₁ h₂
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hsub
  have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have := h.2.2 C hC _ _ _ _ _ _ _ _ hsub h0
  linarith

/-- **Negativity.** On a common model `q : W ⟶ Y`, a divisor `Δ` with `±Δ` nef over `q` and
`q_* Δ = 0` vanishes. -/
private theorem eq_zero_of_isRelativelyNef_of_transformDivisor_eq_zero {Y W : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sY : Y ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hYn : IsNormalVariety ℂ sY)
    (hWv : MMP.Mori.IsVariety ℂ sW) (q : W ⟶ Y) (hqW : q ≫ sY = sW) [IsProper q]
    (hqb : IsBirationalMorphism q) {Δ : RDivisor W} (hcomb : IsCartierCombination Δ)
    (h1 : IsRelativelyNef ℂ sW q Δ) (h2 : IsRelativelyNef ℂ sW q (-Δ))
    (hpush : MMP.Mori.RationalMap.transformDivisor q.toRationalMap Δ = 0) : Δ = 0 := by
  classical
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWq : IsNormalVariety ℂ (q ≫ sY) := by rw [hqW]; exact ⟨hWv, inferInstance⟩
  have hcoeff : ∀ E, ¬ IsExceptionalPrimeDivisor sY q E → Δ.coeff E = 0 := by
    intro E hE
    obtain ⟨P, -, -, hP⟩ :=
      MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hYn q hWq hqb
        E hE
    have := hP Δ
    rw [hpush] at this
    exact this.symm
  have hcomb' : IsCartierCombination (-Δ) := by
    obtain ⟨m, r, L, hL, hD⟩ := hcomb
    exact ⟨m, -r, L, hL, by rw [hD]; simp [Finset.sum_neg_distrib, neg_smul]⟩
  have hc0 : IsCartierCombination (0 : RDivisor Y) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have h00 : MMP.Flips.IsRCartierPullback q (0 : RDivisor Y) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have e1 := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sY sW hYn
    ⟨hWv, inferInstance⟩ q hqW hqb hc0 h00 hcomb h1 hcomb' (fun E hE => by
      rw [DivisorWithCoeffs.coeff_neg, hcoeff E hE, neg_zero]) (by
      rw [add_neg_cancel]; exact isNumericallyEquivalentOver_zero_zero q)
  have e2 := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sY sW hYn
    ⟨hWv, inferInstance⟩ q hqW hqb hc0 h00 hcomb' h2 hcomb (fun E hE => (hcoeff E hE).ge) (by
      rw [neg_add_cancel]; exact isNumericallyEquivalentOver_zero_zero q)
  rw [DivisorWithCoeffs.isEffective_iff_nonneg] at e1 e2
  refine Finsupp.ext fun E => le_antisymm ?_ (e2 E)
  have := e1 E
  simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
  linarith

/-- The pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {D : RDivisor X} {G : RDivisor Y} (h : MMP.Flips.IsRCartierPullback f D G) :
    IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  refine ⟨m, r, L', fun j => ?_, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨hB, hp⟩ := hpb j
  exact hp.isCartier (hL j)

/-- A pull-back is numerically trivial over the morphism it is pulled back along. -/
private theorem isNumericallyTrivialOver_of_isRCartierPullback {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} [IsSeparated sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] (hXq : IsQFactorial sX) (p : W ⟶ X) [IsProper p]
    (hpW : p ≫ sX = sW) [QuasiCompact sW] {D : RDivisor X} {G : RDivisor W}
    (hG : MMP.Flips.IsRCartierPullback p D G) : IsNumericallyTrivialOver ℂ sW p G := by
  haveI : QuasiCompact (p ≫ sX) := by rw [hpW]; infer_instance
  have hGn : MMP.Flips.IsRCartierPullback p (-D) (-G) := by
    simpa using MMP.Fourfold.isRCartierPullback_smul (-1) hG
  have h1 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 X) (𝟙 X) p p rfl
    (isRelativelyNef_of_isIso hXq (𝟙 X) D) hG
  have h2 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 X) (𝟙 X) p p rfl
    (isRelativelyNef_of_isIso hXq (𝟙 X) (-D)) hGn
  exact isNumericallyTrivialOver_of_isRelativelyNef_neg (isRelativelyNef_of_eq_structure hpW h1)
    (isRelativelyNef_of_eq_structure hpW h2)

/-- **Push-forward of a numerical class.** Let `p : W ⟶ X` be a projective birational morphism
onto a `ℚ`-factorial projective variety and `π : X ⟶ Z`. If the pull-back `p^* M` is numerically
equivalent over `Z` to `F`, then `M` is numerically equivalent over `Z` to `p_* F`: `p^* p_* F - F`
is numerically trivial over `X` with zero push-forward, hence zero by the negativity lemma, and
numerical equivalence descends along the surjection `p`. -/
private theorem isNumericallyEquivalentOver_transformDivisor_of_isRCartierPullback
    {X W Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXq : IsQFactorial sX) (hWv : MMP.Mori.IsVariety ℂ sW) (p : W ⟶ X) (hpW : p ≫ sX = sW)
    (hpp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p) (π : X ⟶ Z)
    {M : RDivisor X} {G F : RDivisor W} (hG : MMP.Flips.IsRCartierPullback p M G)
    (hF : IsCartierCombination F)
    (hGF : IsNumericallyEquivalentOver ℂ sW (p ≫ π) G F) :
    IsNumericallyEquivalentOver ℂ sX π M
      (MMP.Mori.RationalMap.transformDivisor p.toRationalMap F) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsSeparated sX := hX.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_terminal_of sX
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsDominant p := hpb.isDominant
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  have hWp : IsNormalVariety ℂ (p ≫ sX) := by rw [hpW]; exact ⟨hWv, inferInstance⟩
  set N := MMP.Mori.RationalMap.transformDivisor p.toRationalMap F with hNdef
  have hNc : IsCartierCombination N := isCartierCombination_of_isQFactorial hXq N
  obtain ⟨GN, hGN, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hNc
  -- `p_* p^* N = N`
  obtain ⟨h, hinv⟩ : ∃ h : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap h :=
    MMP.Mori.RationalMap.IsBirational.exists_isInverse hpb
  have hidE : ∀ F : MMP.Mori.PrimeDivisor X,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (Scheme.Hom.toRationalMap (𝟙 X)) F :=
    fun F hF => hF F ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) F
      F).mpr rfl)
  have hpGN := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hXn hXn hidE p p h hWp hWp
    hpb hpb hinv (compHom_eq_of_isInverse hinv) hGN
  rw [transformDivisor_id_toRationalMap hXn] at hpGN
  -- `p^* N = F`
  have hMN : MMP.Flips.IsRCartierPullback p (M - N) (G - GN) := by
    have := MMP.Fourfold.isRCartierPullback_add hG (MMP.Fourfold.isRCartierPullback_smul (-1) hGN)
    simpa [sub_eq_add_neg, neg_one_smul] using this
  have hGNF : GN = F := by
    have htriv1 := isNumericallyTrivialOver_of_isRCartierPullback hXq p hpW hMN
    have htriv2 := isNumericallyTrivialOver_of_comp (isNumericallyTrivialOver_sub hGF)
    have hΔ : IsNumericallyTrivialOver ℂ sW p (GN - F) := by
      have := isNumericallyTrivialOver_add (isNumericallyTrivialOver_neg htriv1) htriv2
      rwa [show -(G - GN) + (G - F) = GN - F by abel] at this
    have hz := eq_zero_of_isRelativelyNef_of_transformDivisor_eq_zero hXn hWv p hpW hpb hΔ.1
      (isRelativelyNef_of_isNumericallyTrivialOver hΔ)
      (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg hΔ))
      (by rw [map_sub, hpGN, sub_self])
    exact sub_eq_zero.mp hz
  -- `M - N` is numerically trivial over `Z`
  have htr : IsNumericallyTrivialOver ℂ sW (p ≫ π) (G - GN) := by
    rw [hGNF]; exact isNumericallyTrivialOver_sub hGF
  have hMNn : MMP.Flips.IsRCartierPullback p (-(M - N)) (-(G - GN)) := by
    simpa using MMP.Fourfold.isRCartierPullback_smul (-1) hMN
  have n1 := MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective p hpW π hMN
    (isRelativelyNef_of_isNumericallyTrivialOver htr)
  have n2 := MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective p hpW π hMNn
    (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg htr))
  exact isNumericallyEquivalentOver_of_isNumericallyTrivialOver_sub
    (isCartierCombination_of_isQFactorial hXq M) hNc
    (isNumericallyTrivialOver_of_isRelativelyNef_neg n1 n2)

/-- **A relatively ample divisor is numerically effective.** On a normal projective variety over
a projective base, a relatively ample `ℝ`-divisor is numerically equivalent over the base to an
effective `ℝ`-Cartier divisor. -/
private theorem exists_nonneg_isNumericallyEquivalentOver_of_isRelativelyAmple
    {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (f : Y ⟶ S) (hf : f ≫ sS = sY) {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) :
    ∃ H : RDivisor Y, (∀ P, 0 ≤ H.coeff P) ∧ IsCartierCombination H ∧
      IsNumericallyEquivalentOver ℂ sY f A H := by
  classical
  haveI : QuasiCompact sY := hY.toIsVariety.toQuasiCompact
  obtain ⟨m, a, L, -, ha, hL, rfl⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  choose Ac hAc using fun j => exists_isWeilDivisorOfCartier_of_isCartier (hLc j)
  have hAamp : ∀ j, IsRelativelyAmple f (MMP.CartierDivisor.sheaf (Ac j)) := by
    intro j
    haveI := (hLc j).isInvertibleModule_divisorialSheaf
    exact MMP.Fourfold.isRelativelyAmple_of_iso f (hAc j).sheafIsoDivisorialSheaf.symm
      (hL j).isRelativelyAmple
  choose H n hn hHe hdeg using fun j =>
    MMP.Fourfold.exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple sY sS f hY hS hf (Ac j)
      (hAamp j)
  choose h hh using fun j => exists_isWeilDivisorOfCartier (H j)
  have hhc : ∀ j, (h j).IsCartier := fun j => (hh j).isCartier
  have hh0 : ∀ j P, 0 ≤ (h j).coeff P := fun j P =>
    (hh j P).nonneg_of_isEffective (hHe j)
  refine ⟨∑ j, (a j / n j) • Divisor.toRDivisor (h j), fun P => ?_,
    ⟨m, fun j => a j / n j, h, hhc, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    ⟨⟨m, a, L, hLc, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
      ⟨m, fun j => a j / n j, h, hhc, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
      fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩⟩
  · rw [MMP.Fourfold.coeff_sum_smul_toRDivisor]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (div_nonneg (ha j).le (Nat.cast_nonneg _)) (by exact_mod_cast hh0 j P)
  · have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sY C a L hLc
    have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sY C (fun j => a j / n j) h hhc
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sY C).1 _ _ _ _ _ _ _ h₁ e₁,
      (IsRIntersectionNumber.eq_and_linear ℂ sY C).1 _ _ _ _ _ _ _ h₂ e₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [degreeOn_eq_degree_sheaf C (hAc j) (hLc j), degreeOn_eq_degree_sheaf C (hh j) (hhc j),
      hdeg j C hC]
    have := (hn j).ne'
    push_cast
    field_simp

/-- **An adjoint with an ample log minimal model is pseudo-effective.** If `(Y/Z, D_Y)` is a log
minimal model of `(X/Z, D)` with `K_Y + D_Y` ample over `Z`, then `K_X + D` is pseudo-effective
over `Z`: on a common resolution `p^*(K_X + D) = q^*(K_Y + D_Y) + E` with `E ≥ 0`, the ample
`K_Y + D_Y` is numerically effective over `Z`, and the class pushes forward to `X`. -/
private theorem exists_isRelativelyPseudoEffective_of_isRealLogMinimalModel
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X}
    {D : RDivisor X} {KY : Divisor Y} {DY : RDivisor Y} {φ : X.RationalMap Y}
    (h : IsRealLogMinimalModel sX sY sZ π πY K D KY DY φ)
    (hamp : IsRelativelyAmple πY (logCanonicalDivisor KY DY)) :
    ∃ D' : KCartierDivisor ℝ X,
      (∀ P : MMP.Mori.PrimeDivisor X, (logCanonicalDivisor K D).coeff P =
        D'.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ)) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX π D' := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal_of sZ
  have hYp := h.isProjectiveVariety_model
  haveI : QuasiCompact sY := hYp.toIsVariety.toQuasiCompact
  have hYq := h.isQFactorial
  obtain ⟨W, iW, lW, nW, sW, p, q, h', GX, GY, hR⟩ := h.exists_resolution
  haveI : QuasiCompact sW := hR.isVariety.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  haveI : IsDominant q := hR.isBirationalMorphism_right.isDominant
  haveI : IsSeparated sY := hYp.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYp.toIsVariety.toLocallyOfFiniteType
  have hpq : p ≫ π = q ≫ πY :=
    MMP.Fourfold.comp_eq_comp_of_isOver π πY h.isOver p q h' hR.isInverse hR.compHom_eq
  -- the ample adjoint is numerically effective over `Z`
  obtain ⟨H, hH0, hHc, hAH⟩ := exists_nonneg_isNumericallyEquivalentOver_of_isRelativelyAmple hYp
    hZ πY h.comp_eq_model hamp
  obtain ⟨QH, hQH, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hHc
  have hQH0 : ∀ P, 0 ≤ QH.coeff P :=
    (MMP.Fourfold.isEffective_of_isRCartierPullback q (isRCartier_of_isQFactorial hYq H)
      fun P => hH0 P).2 QH hQH
  -- `q^*(K_Y + D_Y) ≡ q^* H` over `Z`
  have hGY : IsNumericallyEquivalentOver ℂ sW (q ≫ πY) GY QH := by
    have hdiff : MMP.Flips.IsRCartierPullback q (logCanonicalDivisor KY DY - H) (GY - QH) := by
      have := MMP.Fourfold.isRCartierPullback_add hR.isRCartierPullback_right
        (MMP.Fourfold.isRCartierPullback_smul (-1) hQH)
      simpa [sub_eq_add_neg, neg_one_smul] using this
    have hdiffn : MMP.Flips.IsRCartierPullback q (-(logCanonicalDivisor KY DY - H))
        (-(GY - QH)) := by
      simpa using MMP.Fourfold.isRCartierPullback_smul (-1) hdiff
    have htriv := isNumericallyTrivialOver_sub hAH
    have n1 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) πY (q ≫ πY) q
      (Category.comp_id _) (isRelativelyNef_of_isNumericallyTrivialOver htriv) hdiff
    have n2 := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Z) πY (q ≫ πY) q
      (Category.comp_id _)
      (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg htriv)) hdiffn
    exact isNumericallyEquivalentOver_of_isNumericallyTrivialOver_sub
      (isCartierCombination_of_isRCartierPullback hR.isRCartierPullback_right)
      (isCartierCombination_of_isRCartierPullback hQH)
      (isNumericallyTrivialOver_of_isRelativelyNef_neg
        (isRelativelyNef_of_eq_structure hR.comp_eq_right n1)
        (isRelativelyNef_of_eq_structure hR.comp_eq_right n2))
  -- `p^*(K_X + D) ≡ q^* H + (G_X - G_Y)` over `Z`
  have hGXc := isCartierCombination_of_isRCartierPullback hR.isRCartierPullback_left
  have hGYc := isCartierCombination_of_isRCartierPullback hR.isRCartierPullback_right
  have hF : IsCartierCombination (QH + (GX - GY)) :=
    MMP.Flips.isCartierCombination_add (isCartierCombination_of_isRCartierPullback hQH)
      (MMP.Flips.isCartierCombination_sub hGXc hGYc)
  have hGXF : IsNumericallyEquivalentOver ℂ sW (p ≫ π) GX (QH + (GX - GY)) := by
    refine isNumericallyEquivalentOver_of_isNumericallyTrivialOver_sub hGXc hF ?_
    rw [show GX - (QH + (GX - GY)) = GY - QH by abel, hpq]
    exact isNumericallyTrivialOver_sub hGY
  have hMN := isNumericallyEquivalentOver_transformDivisor_of_isRCartierPullback hX hXq hR.isVariety
    p hR.comp_eq_left hR.isProjectiveMorphism_left hR.isBirationalMorphism_left π
    hR.isRCartierPullback_left hF hGXF
  refine exists_isRelativelyPseudoEffective_of_isNumericallyEquivalentOver hXq π hMN fun P => ?_
  have hF0 : 0 ≤ QH + (GX - GY) := fun E => by
    have h1 := hQH0 E
    have h2 := hR.effective E
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
    exact add_nonneg h1 h2
  exact MMP.Mori.RationalMap.transformDivisor_nonneg _ hF0 P

end PushForward

/-! ### Rational klt polytopes -/

section Polytope

/-- A divisor supported on a finite set `s` is the sum of its coefficients along `s`. -/
private theorem eq_sum_single_of_support_subset {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {Θ : RDivisor X} {s : Finset (MMP.Mori.PrimeDivisor X)}
    (hs : Θ.support ⊆ s) :
    Θ = ∑ j : s, Finsupp.single j.1 (Θ.coeff j.1) := by
  classical
  refine Finsupp.ext fun W => ?_
  have h := MMP.Fourfold.coeff_sum_single (fun j : s => j.1) (fun j => Θ.coeff j.1) W
  rw [DivisorWithCoeffs.coeff_apply] at h
  rw [h]
  by_cases hW : W ∈ s
  · rw [Fintype.sum_eq_single ⟨W, hW⟩ (fun j hj => if_neg fun h' => hj (Subtype.ext h')),
      if_pos rfl]
    rfl
  · rw [Finset.sum_eq_zero fun (j : s) _ => if_neg fun (h' : j.1 = W) => hW (h' ▸ j.2)]
    by_contra h0
    exact hW (hs (Finsupp.mem_support_iff.mpr h0))

/-- **Klt pairs on a `ℚ`-factorial variety are convex**: if `(X, Θ₀)` and `(X, Θ₁)` are klt, so is
`(X, (1 - s) Θ₀ + s Θ₁)` for `0 ≤ s ≤ 1`. -/
private theorem isRealKltPair_segment {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {Θ₀ Θ₁ : RDivisor X} (h₀ : IsRealKltPair sX Θ₀) (h₁ : IsRealKltPair sX Θ₁) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsRealKltPair sX ((1 - s) • Θ₀ + s • Θ₁) := by
  classical
  set t := Θ₀.support ∪ Θ₁.support
  let p : t → MMP.Mori.PrimeDivisor X := Subtype.val
  have e₀ := eq_sum_single_of_support_subset (Θ := Θ₀) (s := t) Finset.subset_union_left
  have e₁ := eq_sum_single_of_support_subset (Θ := Θ₁) (s := t) Finset.subset_union_right
  have hΘ : (1 - s) • Θ₀ + s • Θ₁ = ∑ j : t, Finsupp.single (p j)
      ((1 - s) * Θ₀.coeff j.1 + s * Θ₁.coeff j.1) := by
    conv_lhs => rw [e₀, e₁]
    simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← Finset.sum_add_distrib,
      ← Finsupp.single_add]
    rfl
  choose m hm hmc using fun j : t => hQ.2 (Finsupp.single (p j) (1 : ℤ))
  have hconv := MMP.Fourfold.convex_setOf_lt_isLogDiscrepancy (k := ℂ) (sX := sX) p m hm hmc 0 (fun
      _ => True)
  have hy₀ : (fun j : t => Θ₀.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      True → MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D a →
        0 < a} := fun n D a _ ha => h₀.2.2.2 n D a (e₀ ▸ ha)
  have hy₁ : (fun j : t => Θ₁.coeff j.1) ∈ {y : t → ℝ | ∀ (n : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      True → MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D a →
        0 < a} := fun n D a _ ha => h₁.2.2.2 n D a (e₁ ▸ ha)
  have hy := hconv hy₀ hy₁ (sub_nonneg.2 hs1) hs0 (by ring)
  obtain ⟨n, K, hK, -⟩ := h₀.2.2.1
  refine ⟨h₀.1, fun P => ?_, ⟨n, K, hK, ?_⟩, fun n' D a ha => ?_⟩
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul, smul_eq_mul]
    have ha := h₀.2.1 P
    have hb := h₁.2.1 P
    by_cases h1 : s = 1
    · subst h1; simpa using hb
    · nlinarith [mul_lt_mul_of_pos_left ha (sub_pos.2 (lt_of_le_of_ne hs1 h1)),
        mul_le_mul_of_nonneg_left hb.le hs0]
  · rw [hΘ]
    exact MMP.Fourfold.isRCartier_add_sum_single hQ K p _
  · refine hy n' D a trivial ?_
    rw [hΘ] at ha
    convert ha using 3

open Filter Topology in
/-- **Klt survives a small effective perturbation.** If `(X, Θ)` is klt with `Θ` effective and
`T` is effective, then `(X, Θ + t T)` is klt for all small `t ≥ 0`. -/
private theorem exists_isRealKltPair_add_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX) {Θ T : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hT : ∀ P, 0 ≤ T.coeff P)
    (hk : IsRealKltPair sX Θ) :
    ∃ t₀ > 0, ∀ t : ℝ, 0 ≤ t → t < t₀ → IsRealKltPair sX (Θ + t • T) := by
  classical
  set s := Θ.support ∪ T.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : ℝ → s → ℝ := fun t j => Θ.coeff j.1 + t * T.coeff j.1
  have hrep : ∀ t : ℝ, Θ + t • T = ∑ j, Finsupp.single (p j) (y t j) := fun t => by
    have hsub : (Θ + t • T).support ⊆ s := fun P hP => by
      by_contra h
      rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at h
      exact (Finsupp.mem_support_iff.mp hP) (by simp [h.1, h.2])
    rw [eq_sum_single_of_support_subset hsub]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  have hcont : Continuous y :=
    continuous_pi fun j => continuous_const.add (continuous_id.mul continuous_const)
  have htend : Tendsto y (𝓝[≥] 0) (𝓝[Set.Ici 0] (y 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t (ht : 0 ≤ t) j =>
        add_nonneg (hΘ _) (mul_nonneg ht (hT _))⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (htend.eventually hev)
  exact ⟨u, hu, fun t ht0 htu => by rw [hrep]; exact hsub ⟨ht0, htu⟩⟩

/-- A rational box around a nonnegative point: finitely many nonnegative rational vectors within
`δ` of `x` whose convex hull contains every nonnegative vector within `δ / 2` of `x`. -/
private theorem exists_rat_box {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hx : ∀ k, 0 ≤ x k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : Finset (ι → ℚ), (∀ v ∈ V, ∀ k, (0 : ℚ) ≤ v k ∧ |(v k : ℝ) - x k| < δ) ∧
      ∀ y : ι → ℝ, (∀ k, 0 ≤ y k ∧ |y k - x k| < δ / 2) →
        y ∈ convexHull ℝ ((fun v : ι → ℚ => fun k => (v k : ℝ)) '' (V : Set (ι → ℚ))) := by
  classical
  choose a ha using fun k => exists_rat_btwn (show x k - δ < x k - δ / 2 by linarith)
  choose b hb using fun k => exists_rat_btwn (show x k + δ / 2 < x k + δ by linarith)
  set a' : ι → ℚ := fun k => max (a k) 0
  let V : Finset (ι → ℚ) := Fintype.piFinset fun k => {a' k, b k}
  refine ⟨V, fun v hv k => ?_, fun y hy => ?_⟩
  · have hvk := Fintype.mem_piFinset.mp hv k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvk
    rcases hvk with h | h <;> rw [h]
    · refine ⟨le_max_right _ _, ?_⟩
      simp only [a', Rat.cast_max, Rat.cast_zero]
      refine abs_lt.mpr ⟨?_, ?_⟩
      · linarith [(ha k).1, le_max_left (a k : ℝ) 0]
      · rcases le_total (a k : ℝ) 0 with h0 | h0
        · rw [max_eq_right h0]
          linarith [hx k]
        · rw [max_eq_left h0]
          linarith [(ha k).2]
    · refine ⟨?_, ?_⟩
      · exact_mod_cast (show (0 : ℝ) < b k by linarith [(hb k).1, hx k]).le
      · rw [abs_lt]
        constructor <;> linarith [(hb k).1, (hb k).2]
  · have himage : ((fun v : ι → ℚ => fun k => (v k : ℝ)) '' (V : Set (ι → ℚ))) =
        Set.univ.pi fun k => {((a' k : ℚ) : ℝ), ((b k : ℚ) : ℝ)} := by
      ext z
      simp only [Set.mem_image, Finset.mem_coe, V, Fintype.mem_piFinset, Finset.mem_insert,
        Finset.mem_singleton, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨v, hv, rfl⟩ k
        rcases hv k with h | h <;> simp [h]
      · intro hz
        refine ⟨fun k => if z k = (a' k : ℝ) then a' k else b k, fun k => ?_, funext fun k => ?_⟩
        · by_cases h : z k = (a' k : ℝ) <;> simp [h]
        · by_cases h : z k = (a' k : ℝ)
          · simp [h]
          · simp only [h, if_false]
            exact ((hz k).resolve_left h).symm
    rw [himage, convexHull_pi]
    intro k _
    show y k ∈ convexHull ℝ {((a' k : ℚ) : ℝ), ((b k : ℚ) : ℝ)}
    rw [convexHull_pair, segment_eq_Icc]
    · obtain ⟨hy0, hyx⟩ := hy k
      rw [abs_lt] at hyx
      constructor
      · simp only [a', Rat.cast_max, Rat.cast_zero]
        exact max_le (by linarith [(ha k).2]) hy0
      · linarith [(hb k).1]
    · simp only [a', Rat.cast_max, Rat.cast_zero]
      exact max_le (by linarith [(ha k).2, (hb k).1]) (by linarith [(hb k).1, hx k])

/-- On the support of `Θ`, the perturbation `Θ + ∑ uᵢ Dᵢ` by divisors supported there is the sum of
its coefficients along the support. -/
private theorem add_sum_smul_eq_sum_single {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Θ : RDivisor X) {ι : Type}
    [Fintype ι] (D : ι → RDivisor X) (hD0 : ∀ i W, W ∉ Θ.support → (D i).coeff W = 0)
    (u : ι → ℝ) :
    Θ + ∑ i, u i • D i = ∑ j : Θ.support, Finsupp.single j.1
      (Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1) := by
  classical
  refine Finsupp.ext fun W => ?_
  have h := MMP.Fourfold.coeff_sum_single (fun j : Θ.support => j.1)
    (fun j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1) W
  rw [DivisorWithCoeffs.coeff_apply] at h
  rw [h, Finsupp.add_apply, Finset.sum_apply']
  by_cases hW : W ∈ Θ.support
  · rw [Fintype.sum_eq_single ⟨W, hW⟩ (fun j hj => if_neg fun h' => hj (Subtype.ext h')),
      if_pos rfl]
    simp [DivisorWithCoeffs.coeff_apply]
  · rw [Finset.sum_eq_zero fun (j : Θ.support) _ => if_neg fun (h' : j.1 = W) => hW (h' ▸ j.2)]
    have h1 : Θ W = 0 := Finsupp.notMem_support_iff.mp hW
    have h2 : ∀ i, (D i) W = 0 := fun i => hD0 i W hW
    simp [h1, h2]

open Filter Topology in
/-- **A rational klt polytope around a perturbed boundary.** Let `Θ` be an effective klt boundary,
`S ≥ 0` a `ℚ`-divisor supported on `Θ` with `Θ + S` klt, `G ≥ 0` a `ℚ`-divisor with `2G ≤ Θ`,
and `Dᵢ` divisors supported where `Θ` has coefficients at least `δ > 0`. There are finitely many
effective `ℚ`-divisors `E ≥ G`, with `E` and `E + S` klt, whose convex hull contains
`Θ + ∑ uᵢ Dᵢ` for all small `u`. -/
private theorem exists_finset_isKltPair_convexHull_of_shift {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX)
    {Θ : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hk : IsRealKltPair sX Θ)
    (Sh : QDivisor X) (hSh0 : ∀ P, 0 ≤ Sh.coeff P)
    (hShΘ : ∀ P, Sh.coeff P ≠ 0 → Θ.coeff P ≠ 0)
    (hkS : IsRealKltPair sX (Θ + QDivisor.toRDivisor Sh))
    (G : QDivisor X) (hG0 : ∀ P, 0 ≤ G.coeff P) (hGΘ : ∀ P, 2 * (G.coeff P : ℝ) ≤ Θ.coeff P)
    {ι : Type} [Fintype ι] (D : ι → RDivisor X) {δ : ℝ} (hδ : 0 < δ)
    (hDδ : ∀ i P, (D i).coeff P ≠ 0 → δ ≤ Θ.coeff P) :
    ∃ (V : Finset (QDivisor X)) (ε : ℝ), 0 < ε ∧ (∀ E ∈ V, ∀ P, 0 ≤ E.coeff P) ∧
      (∀ E ∈ V, IsRealKltPair sX (QDivisor.toRDivisor E)) ∧
      (∀ E ∈ V, IsRealKltPair sX (QDivisor.toRDivisor E + QDivisor.toRDivisor Sh)) ∧
      (∀ E ∈ V, ∀ P, G.coeff P ≤ E.coeff P) ∧ ∀ u : ι → ℝ, (∀ i, |u i| < ε) →
        Θ + ∑ i, u i • D i ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
  classical
  let s := Θ.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : (ι → ℝ) → s → ℝ := fun u j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1
  let yS : s → ℝ := fun j => (Sh.coeff j.1 : ℝ)
  have hD0 : ∀ i W, W ∉ s → (D i).coeff W = 0 := fun i W hW => by
    by_contra h
    have := hDδ i W h
    have h0 : Θ.coeff W = 0 := Finsupp.notMem_support_iff.mp hW
    linarith
  have hrep : ∀ u, Θ + ∑ i, u i • D i = ∑ j, Finsupp.single (p j) (y u j) :=
    add_sum_smul_eq_sum_single Θ D hD0
  -- the linear map from coordinates to divisors
  let L : (s → ℝ) →ₗ[ℝ] RDivisor X :=
    { toFun := fun z => ∑ j, Finsupp.single (p j) (z j)
      map_add' := fun a b => by
        simp only [Pi.add_apply, Finsupp.single_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, Finsupp.smul_single, Finset.smul_sum, RingHom.id_apply] }
  let F : (s → ℚ) → QDivisor X := fun v => ∑ j, Finsupp.single (p j) (v j)
  have hFL : ∀ v, QDivisor.toRDivisor (F v) = L (fun j => (v j : ℝ)) := fun v => by
    refine Finsupp.ext fun W => ?_
    change ((∑ j, Finsupp.single (p j) (v j) : QDivisor X).coeff W : ℝ) =
      (∑ j, Finsupp.single (p j) ((v j : ℝ)) : RDivisor X).coeff W
    rw [MMP.Fourfold.coeff_sum_single, MMP.Fourfold.coeff_sum_single]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hFcoeff : ∀ v (j : s), (F v).coeff j.1 = v j := fun v j => by
    simp only [F]
    rw [MMP.Fourfold.coeff_sum_single, Fintype.sum_eq_single j
      (fun i hi => if_neg fun h => hi (Subtype.ext h)), if_pos rfl]
  have hFcoeff' : ∀ v W, W ∉ s → (F v).coeff W = 0 := fun v W hW => by
    simp only [F]
    rw [MMP.Fourfold.coeff_sum_single]
    exact Finset.sum_eq_zero fun j _ => if_neg fun (h : j.1 = W) => hW (h ▸ j.2)
  have hSrep : QDivisor.toRDivisor Sh = L yS := by
    refine Finsupp.ext fun W => ?_
    change ((Sh.coeff W : ℚ) : ℝ) = (∑ j, Finsupp.single (p j) (yS j) : RDivisor X).coeff W
    rw [MMP.Fourfold.coeff_sum_single]
    by_cases hW : W ∈ s
    · rw [Fintype.sum_eq_single ⟨W, hW⟩ (fun i hi => if_neg fun h => hi (Subtype.ext h)),
        if_pos rfl]
    · rw [Finset.sum_eq_zero fun j _ => if_neg fun (h : j.1 = W) => hW (h ▸ j.2)]
      by_contra h
      exact hW (Finsupp.mem_support_iff.mpr (hShΘ W fun h0 => h (by rw [h0]; simp)))
  have hcont : Continuous y := by
    refine continuous_pi fun j => continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_apply i).mul continuous_const
  have hx0 : ∀ j, 0 < y 0 j := fun j => by
    have : Θ.coeff j.1 ≠ 0 := Finsupp.mem_support_iff.mp j.2
    simpa [y] using lt_of_le_of_ne (hΘ j.1) (Ne.symm this)
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hkS0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) ((y 0 + yS) j)) := by
    have : ∑ j, Finsupp.single (p j) ((y 0 + yS) j) = Θ + QDivisor.toRDivisor Sh := by
      rw [hSrep]
      change L (y 0 + yS) = _
      rw [map_add]
      change ∑ j, Finsupp.single (p j) (y 0 j) + _ = _
      rw [← hrep 0]; simp
    rw [this]; exact hkS
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  have hevS := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0 + yS)).1 hkS0
  obtain ⟨U, hUo, hxU, hU⟩ := mem_nhdsWithin.mp hev
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hUo (y 0) hxU
  obtain ⟨US, hUSo, hxUS, hUS⟩ := mem_nhdsWithin.mp hevS
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hUSo (y 0 + yS) hxUS
  -- a margin below the positive coefficients of `G`
  obtain ⟨g, hg, hgG⟩ : ∃ g : ℝ, 0 < g ∧ ∀ j : s, 0 < (G.coeff j.1 : ℝ) → g ≤ G.coeff j.1 := by
    let T := (Finset.univ : Finset s).filter (fun j => 0 < (G.coeff j.1 : ℝ))
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT (fun j => (G.coeff j.1 : ℝ)), ?_, fun j hj =>
        Finset.inf'_le (s := T) (fun j : s => (G.coeff j.1 : ℝ))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)⟩
      rw [Finset.lt_inf'_iff]
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    · exact ⟨1, one_pos, fun j hj =>
        absurd ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩ hT⟩
  set r := min (min r₁ r₂) g with hr
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) hg
  obtain ⟨V', hV'1, hV'2⟩ := exists_rat_box (y 0) (fun j => (hx0 j).le) hr0
  have hall : ∀ᶠ u in 𝓝 (0 : ι → ℝ), ∀ j, 0 < y u j ∧ |y u j - y 0 j| < r / 2 := by
    refine eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun u => y u j) 0 :=
      ((continuous_apply j).comp hcont).continuousAt
    have h1 := hc.eventually (lt_mem_nhds (hx0 j))
    have h2 := hc.eventually (Metric.ball_mem_nhds (y 0 j) (half_pos hr0))
    filter_upwards [h1, h2] with u hu1 hu2
    exact ⟨hu1, by rw [← Real.dist_eq]; exact hu2⟩
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.mp hall
  have hnn : ∀ v ∈ V', ∀ P, 0 ≤ (F v).coeff P := fun v hv P => by
    simp only [F]
    rw [MMP.Fourfold.coeff_sum_single]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [(hV'1 v hv j).1]
  refine ⟨V'.image F, ε, hε, ?_, ?_, ?_, ?_, ?_⟩
  · intro E hE P
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    exact hnn v hv P
  · intro E hE
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    rw [hFL]
    refine hU ⟨hball₁ ((dist_pi_lt_iff hr₁).mpr fun j => ?_), fun j => ?_⟩
    · rw [Real.dist_eq]
      exact (hV'1 v hv j).2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    · show (0 : ℝ) ≤ (v j : ℝ)
      exact_mod_cast (hV'1 v hv j).1
  · intro E hE
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    rw [hFL, hSrep, ← map_add]
    refine hUS ⟨hball₂ ((dist_pi_lt_iff hr₂).mpr fun j => ?_), fun j => ?_⟩
    · rw [Real.dist_eq]
      simp only [Pi.add_apply]
      rw [show (v j : ℝ) + yS j - (y 0 j + yS j) = (v j : ℝ) - y 0 j by ring]
      exact (hV'1 v hv j).2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    · show (0 : ℝ) ≤ (v j : ℝ) + yS j
      have := hSh0 j.1
      have h2 : (0 : ℝ) ≤ (v j : ℝ) := by exact_mod_cast (hV'1 v hv j).1
      have h3 : (0 : ℝ) ≤ yS j := by simp only [yS]; exact_mod_cast this
      linarith
  · intro E hE P
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
    by_cases hP : P ∈ s
    · rw [hFcoeff v ⟨P, hP⟩]
      have h1 := hV'1 v hv ⟨P, hP⟩
      rw [abs_lt] at h1
      have h2 := hGΘ P
      have h3 : y 0 ⟨P, hP⟩ = Θ.coeff P := by simp [y]
      have hGP := hG0 P
      have hv0 : (0 : ℚ) ≤ v ⟨P, hP⟩ := (hV'1 v hv ⟨P, hP⟩).1
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ G.coeff P by exact_mod_cast hGP) with hpos | h0
      · have hgle := hgG ⟨P, hP⟩ hpos
        have hrg : r ≤ g := min_le_right _ _
        have : (G.coeff P : ℝ) ≤ v ⟨P, hP⟩ := by linarith [h1.2.1]
        exact_mod_cast this
      · have : G.coeff P = 0 := by exact_mod_cast h0.symm
        rw [this]; exact hv0
    · rw [hFcoeff' v P hP]
      have h2 := hGΘ P
      rw [show Θ.coeff P = 0 from Finsupp.notMem_support_iff.mp hP] at h2
      have : (G.coeff P : ℝ) ≤ 0 := by linarith
      exact_mod_cast this
  · intro u hu
    have hd : dist u 0 < ε := (dist_pi_lt_iff hε).mpr fun i => by
      simpa [Real.dist_eq] using hu i
    have hyu := hεh hd
    have hmem := hV'2 (y u) fun j => ⟨(hyu j).1.le, (hyu j).2⟩
    rw [hrep u]
    change L (y u) ∈ _
    have himg : QDivisor.toRDivisor '' ((V'.image F : Finset (QDivisor X)) : Set (QDivisor X)) =
        L '' ((fun v : s → ℚ => fun j => (v j : ℝ)) '' (V' : Set (s → ℚ))) := by
      rw [Finset.coe_image, Set.image_image, Set.image_image]
      exact Set.image_congr fun v _ => hFL v
    rw [himg, ← LinearMap.image_convexHull]
    exact Set.mem_image_of_mem L hmem

end Polytope

/-! ### Klt neighbourhoods on a nef weak model -/

section Neighbourhood

/-- The birational transform of `ℝ`-divisors is `ℝ`-linear. -/
private theorem transformDivisor_smul {X Y : Scheme.{0}} (φ : X.RationalMap Y) (c : ℝ)
    (D : RDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (c • D) =
      c • MMP.Mori.RationalMap.transformDivisor φ D :=
  (MMP.Mori.RationalMap.transformDivisorₗ ℝ φ).map_smul c D

/-- The push-forward along a composite of proper birational morphisms is the composite of the
push-forwards. -/
private theorem transformDivisor_comp_of_isBirationalMorphism {X W V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {p : W ⟶ X} {r : V ⟶ W}
    (hW : IsNormalVariety ℂ (p ≫ sX)) (hV : IsNormalVariety ℂ (r ≫ p ≫ sX)) [IsProper p]
    [IsProper r] (hpb : IsBirationalMorphism p) (hrb : IsBirationalMorphism r)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R V) :
    MMP.Mori.RationalMap.transformDivisor p.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor r.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor (r ≫ p).toRationalMap D := by
  haveI := hX.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := hW.1.toIsSeparated
  haveI := isSeparated_terminal_of (p ≫ sX)
  haveI : IsProper (r ≫ p) := inferInstance
  have hrpb : IsBirationalMorphism (r ≫ p) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hrb hpb
  set h := hrb.inverse
  have hinv : MMP.Mori.RationalMap.IsInverse r.toRationalMap h := hrb.isInverse_inverse
  have hψ : h.compHom (r ≫ p) = p.toRationalMap := by
    rw [← MMP.Fourfold.Oai4C1.Main.compHom_compHom, MMP.Fourfold.Crepant.compHom_eq_of_isInverse
        hinv,
      toRationalMap_compHom, Category.id_comp]
  have hE : ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ P : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P =
        some F := by
    intro F
    obtain ⟨P, hP, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hW hpb F
    exact ⟨P, (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P F).mpr hP⟩
  have hV' : IsNormalVariety ℂ (r ≫ p ≫ sX) := hV
  exact transformDivisor_transformDivisor_of_isInverse hW hX (by rwa [← Category.assoc] at hV' ⊢)
    (by rw [Category.assoc]) hrb hrpb hinv hψ hE D

/-- **The log discrepancy of a prime divisor of a model.** If `K_M = div(ω)` and `K_W = div(f^*ω)`
on a model `f : W ⟶ M`, the log discrepancy of a prime divisor `E` of `W` with respect to
`(M, Δ)` is `1 + coeff_E K_W - coeff_E f^*(K_M + Δ)`. -/
private theorem isLogDiscrepancy_of_isRCartierPullback {M W : Scheme.{0}} [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM]
    {KM : Divisor M} {ΔM : RDivisor M} {f : W ⟶ M} [IsProper f] [IsDominant f] {G : RDivisor W}
    {e : ℕ} (hMn : IsNormalVariety ℂ sM) (hKM : KM.IsCanonicalDivisor sM e)
    (hWnf : IsNormalVariety ℂ (f ≫ sM)) (hfb : IsBirationalMorphism f) {KW : Divisor W}
    (ω : MMP.Mori.RationalPluriForms sM e 1) (hω0 : ω ≠ 0) (hωK : MMP.Mori.divisorOfForm ω = KM)
    (hωW : MMP.Mori.divisorOfForm (MMP.Mori.pullbackRationalPluriForms sM f ω) = KW)
    (hG : MMP.Flips.IsRCartierPullback f (logCanonicalDivisor KM ΔM) G)
    (E' : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sM e ΔM ⟨W, f, hWnf, hfb, E'⟩
      (1 + (KW.coeff E' : ℝ) - G.coeff E') := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hMn, inferInstanceAs (IsProper f), ω, hω0, ⟨KM, hKM, fun Γ => by
    rw [← hωK]; exact MMP.Mori.coeff_divisorOfForm ω Γ⟩, m, r, L, L', hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor M => D.coeff Γ) hD
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, ← hωK, MMP.Mori.coeff_divisorOfForm]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor, ← hωW, MMP.Mori.coeff_divisorOfForm]
    rfl

/-- **A nef weak model of a klt pair is klt.** Let `φ : X ⤏ Y` be a nef weak model over `Z` of
the klt pair `(X, Δ)`, with `Y` `ℚ`-factorial. Then `(Y, φ_* Δ)` is klt: a divisor `E` over `Y`
is realized on a common smooth model `V` of its own model and of the resolution `W` of `φ`, and
with compatible canonical divisors `K_V` there,
`a(E; Y, φ_* Δ) - a(E; X, Δ) = coeff_E (p^*(K_X + Δ) - q^*(K_Y + φ_* Δ)) ≥ 0`. -/
private theorem isRealKltPair_transformDivisor_of_isNefWeakModel
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] [QuasiCompact sY] [IsSeparated sZ]
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Δ : RDivisor X} {φ : X.RationalMap Y}
    (N : IsNefWeakModel sX sY sZ π πY K Δ φ) (hYq : IsQFactorial sY)
    {KY : Divisor Y} {m : ℕ} (hKY : KY.IsCanonicalDivisor sY m) (hklt : IsRealKltPair sX Δ) :
    IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ Δ) := by
  classical
  have hXn : IsNormalVariety ℂ sX := N.isNormalVariety_source
  have hYn : IsNormalVariety ℂ sY := N.isNormalVariety_target
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := isSeparated_terminal_of sX
  haveI := isSeparated_terminal_of sY
  haveI := hYn.1
  obtain ⟨W, iW, lW, nW, sW, p, q, h, hWv, hWsm, hp, hq, hpp, hqp, hpb, hqb, hinv, hcomp, GY, GZ,
    hGY, hGZ, heff, -⟩ := N.exists_resolution
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWnp : IsNormalVariety ℂ (p ≫ sX) := by rw [hp]; exact ⟨hWv, inferInstance⟩
  have hWnq : IsNormalVariety ℂ (q ≫ sY) := by rw [hq]; exact ⟨hWv, inferInstance⟩
  have hφE := exists_transformPrimeDivisor_eq_some_of_not_isInverseExceptional
    N.not_isInverseExceptional
  refine ⟨hYn, fun F => ?_, ⟨m, KY, hKY, isRCartier_of_isQFactorial hYq _⟩,
    fun e E a ha => ?_⟩
  · -- coefficients below one
    obtain ⟨R, hR⟩ := hφE F
    have hc : (MMP.Mori.RationalMap.transformDivisor φ Δ).coeff F = Δ.coeff R :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hR (fun R' hR' =>
        eq_of_transformPrimeDivisor_eq_some_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hR' hR) Δ
    rw [hc]
    exact hklt.2.1 R
  · -- log discrepancies
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI : IsProper E.f := ha.2.1
    obtain ⟨V, r, p', hVn, hVsm, hcomm, hrp, hrb, hp'p, hp'b⟩ :=
      MMP.Fourfold.exists_common_model_over sY E.f q E.isBirationalMorphism hqb E.isNormalVariety
        hWnq
    haveI := hVn.1.toIsIntegral
    haveI := hVn.2
    haveI : LocallyOfFiniteType (p' ≫ q ≫ sY) := hVn.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ q ≫ sY)
    haveI : QuasiCompact (p' ≫ q ≫ sY) := hVn.1.toQuasiCompact
    haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p' ≫ q ≫ sY)
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hrp
    haveI : IsProper p' := isProper_of_isProjectiveMorphism p' hp'p
    haveI := hp'b.isDominant
    haveI := hrb.isDominant
    set α : V ⟶ X := p' ≫ p with hαdef
    set β : V ⟶ Y := p' ≫ q with hβdef
    have hαb : IsBirationalMorphism α := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hpb
    have hβb : IsBirationalMorphism β := MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        hp'b hqb
    haveI := hαb.isDominant
    haveI := hβb.isDominant
    have hαs : α ≫ sX = p' ≫ q ≫ sY := by
      simp only [hαdef, Category.assoc, hp, hq]
    have hVα : IsNormalVariety ℂ (α ≫ sX) := by rw [hαs]; exact hVn
    have hVβ : IsNormalVariety ℂ (β ≫ sY) := by rw [hβdef, Category.assoc]; exact hVn
    haveI : LocallyOfFiniteType (α ≫ sX) := hVα.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (β ≫ sY) := hVβ.1.toLocallyOfFiniteType
    -- the strict transform of `E` on `V`
    obtain ⟨E'', hE''⟩ := MMP.Fourfold.Oai4C1.CommonModel.exists_primeDivisor_valuation_eq E β hVβ
      hβb r hrb (by rw [hcomm])
    -- compatible canonical divisors on `V`
    obtain ⟨n₀, hK⟩ := N.isCanonicalDivisor
    haveI := hXn.1
    haveI : MMP.Mori.IsVariety ℂ (α ≫ sX) := hVα.1
    have hdV : topologicalKrullDim V = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (α ≫ sX) hαb).symm.trans
        hK.1
    have hsmα : IsSmoothScheme (α ≫ sX) := by rw [hαs]; exact hVsm
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (α ≫ sX) hsmα hdV
    obtain ⟨KV, hKV, hKVα⟩ :=
      MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hVα hαb hK hK₀
    -- `β_* K_V = φ_* K`
    have hp'n : IsNormalVariety ℂ (p' ≫ p ≫ sX) := by rw [← Category.assoc]; exact hVα
    have hp'q : IsNormalVariety ℂ (p' ≫ q ≫ sY) := hVn
    have hKVβ : MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV =
        MMP.Mori.RationalMap.transformDivisor φ K := by
      rw [← transformDivisor_comp_of_isBirationalMorphism hYn hWnq hp'q hqb hp'b,
        ← transformDivisor_transformDivisor_of_isInverse hXn hYn hWnp (hp.trans hq.symm) hpb hqb
          hinv hcomp hφE, transformDivisor_comp_of_isBirationalMorphism hXn hWnp hp'n hpb hp'b]
      change MMP.Mori.RationalMap.transformDivisor φ
        (MMP.Mori.RationalMap.transformDivisor α.toRationalMap KV) = _
      rw [hKVα]
    -- canonical forms
    obtain ⟨ω, hω0, hωK, hωV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn
      hVα hαb hK hKV hKVα
    haveI : MMP.Mori.IsVariety ℂ (β ≫ sY) := hVβ.1
    have hdY : topologicalKrullDim Y = n₀ :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (β ≫ sY) hβb).trans hdV
    obtain rfl : m = n₀ := by exact_mod_cast hKY.1.symm.trans hdY
    have hKV' : KV.IsCanonicalDivisor (β ≫ sY) m := by
      have e : β ≫ sY = α ≫ sX := by rw [hαs, hβdef, Category.assoc]
      rw [e]; exact hKV
    have hKYc := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn hVβ hβb hKY hKV'
    obtain ⟨ωY, hωY0, hωYK, hωYV⟩ := MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq
      hYn hVβ hβb hKYc hKV' rfl
    -- pull-backs of the adjoints to `V`
    obtain ⟨Gα, hGα, -⟩ := MMP.Flips.existsUnique_isRCartierPullback α N.isCartierCombination
    have hGZc : IsCartierCombination (logCanonicalDivisor
        (MMP.Mori.RationalMap.transformDivisor β.toRationalMap KV)
        (MMP.Mori.RationalMap.transformDivisor φ Δ)) :=
      isCartierCombination_of_isQFactorial hYq _
    obtain ⟨Gβ, hGβ, -⟩ := MMP.Flips.existsUnique_isRCartierPullback β hGZc
    have hGα' : MMP.Flips.IsRCartierPullback p' GY Gα :=
      isRCartierPullback_of_isRCartierPullback_comp hGY hGα
    have hGβ' : MMP.Flips.IsRCartierPullback p' GZ Gβ :=
      isRCartierPullback_of_isRCartierPullback_comp (by rw [hKVβ]; exact hGZ) hGβ
    have hWq : IsQFactorial sW :=
      ⟨⟨hWv, inferInstance⟩, fun D => ⟨1, one_pos, by
        simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D⟩⟩
    have hdiff : MMP.Flips.IsRCartierPullback p' (GY - GZ) (Gα - Gβ) := by
      have h1 := MMP.Fourfold.isRCartierPullback_smul (-1) hGβ'
      simp only [neg_one_smul] at h1
      have := MMP.Fourfold.isRCartierPullback_add hGα' h1
      simpa only [← sub_eq_add_neg] using this
    have hpos : 0 ≤ Gα - Gβ := (MMP.Fourfold.isEffective_of_isRCartierPullback p'
      (isRCartier_of_isQFactorial hWq _) (fun P => heff P)).2 _ hdiff
    -- the two log discrepancies
    have hDY := isLogDiscrepancy_of_isRCartierPullback hYn hKYc hVβ hβb ωY hωY0 hωYK hωYV hGβ E''
    have hDX := isLogDiscrepancy_of_isRCartierPullback hXn hK hVα hαb ω hω0 hωK hωV hGα E''
    have ha' := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hDY hE''.symm
    have hX0 := hklt.2.2.2 _ _ _ hDX
    have hE : 0 ≤ (Gα - Gβ).coeff E'' := hpos E''
    rw [DivisorWithCoeffs.coeff_sub] at hE
    rw [ha']
    linarith

/-- The transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {X₁ X₂ : Scheme.{0}} (φ' : X₁.RationalMap X₂)
    {D : RDivisor X₁} (hD : ∀ P, 0 ≤ D.coeff P) (Q : MMP.Mori.PrimeDivisor X₂) :
    0 ≤ (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q := by
  classical
  revert hD
  induction D using Finsupp.induction with
  | zero => intro _; simp
  | single_add a b D ha hb ih =>
    intro hD
    have hDa : D a = 0 := Finsupp.notMem_support_iff.mp ha
    have hD' : ∀ P, 0 ≤ DivisorWithCoeffs.coeff D P := fun P => by
      by_cases hP : P = a
      · subst hP; change 0 ≤ D P; rw [hDa]
      · have := hD P
        change 0 ≤ (Finsupp.single a b + D) P at this
        rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hP), zero_add] at this
        exact this
    have hb0 : 0 ≤ b := by
      have := hD a
      change 0 ≤ (Finsupp.single a b + D) a at this
      rwa [Finsupp.add_apply, Finsupp.single_eq_same, hDa, add_zero] at this
    rw [map_add, DivisorWithCoeffs.coeff_add]
    refine add_nonneg ?_ (ih hD')
    rw [MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ' a with _ | F
    · simp
    · change 0 ≤ (Finsupp.single F b) Q
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb0]

open Filter Topology in
/-- A real boundary perturbed along divisors supported where its coefficients are at least
`δ > 0` stays effective and klt for small perturbations. -/
private theorem exists_isRealKltPair_add_sum_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hQ : IsQFactorial sX)
    {Θ : RDivisor X} (hΘ : ∀ P, 0 ≤ Θ.coeff P) (hk : IsRealKltPair sX Θ)
    {ι : Type} [Fintype ι] (D : ι → RDivisor X) {δ : ℝ} (hδ : 0 < δ)
    (hDδ : ∀ i P, (D i).coeff P ≠ 0 → δ ≤ Θ.coeff P) :
    ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (Θ + ∑ i, u i • D i).coeff P) ∧ IsRealKltPair sX (Θ + ∑ i, u i • D i) := by
  classical
  let s := Θ.support
  let p : s → MMP.Mori.PrimeDivisor X := Subtype.val
  let y : (ι → ℝ) → s → ℝ := fun u j => Θ.coeff j.1 + ∑ i, u i * (D i).coeff j.1
  have hD0 : ∀ i W, W ∉ s → (D i).coeff W = 0 := fun i W hW => by
    by_contra h
    have := hDδ i W h
    have h0 : Θ.coeff W = 0 := Finsupp.notMem_support_iff.mp hW
    linarith
  have hrep : ∀ u, Θ + ∑ i, u i • D i = ∑ j, Finsupp.single (p j) (y u j) :=
    add_sum_smul_eq_sum_single Θ D hD0
  have hcont : Continuous y := by
    refine continuous_pi fun j => continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
    exact (continuous_apply i).mul continuous_const
  have hpos : ∀ᶠ u in 𝓝 (0 : ι → ℝ), ∀ j, 0 < y u j := by
    refine eventually_all.2 fun j => ?_
    have hj : 0 < y 0 j := by
      have : Θ.coeff j.1 ≠ 0 := Finsupp.mem_support_iff.mp j.2
      simpa [y] using lt_of_le_of_ne (hΘ j.1) (Ne.symm this)
    exact ((continuous_apply j).comp hcont).continuousAt.eventually (lt_mem_nhds hj)
  have hk0 : IsRealKltPair sX (∑ j, Finsupp.single (p j) (y 0 j)) := by
    rw [← hrep 0]; simpa using hk
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX hXq hQ p
    (y 0)).1 hk0
  have htend : Filter.Tendsto y (𝓝 0) (𝓝[Set.Ici 0] (y 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont.continuousAt,
      hpos.mono fun u hu => fun j => (hu j).le⟩
  have hall : ∀ᶠ u in 𝓝 (0 : ι → ℝ), (∀ j, 0 < y u j) ∧
      IsRealKltPair sX (∑ j, Finsupp.single (p j) (y u j)) := hpos.and (htend.eventually hev)
  obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε, hε, fun u hu => ?_⟩
  have hd : dist u 0 < ε := (dist_pi_lt_iff hε).mpr fun i => by
    simpa [Real.dist_eq] using hu i
  obtain ⟨h1, h2⟩ := hεh hd
  rw [hrep u]
  refine ⟨fun P => ?_, h2⟩
  rw [MMP.Fourfold.coeff_sum_single]
  exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [(h1 j).le]

/-- A component of a transform comes from a component of the divisor. -/
private theorem exists_of_transformDivisor_coeff_ne_zero {X₁ X₂ : Scheme.{0}}
    (φ' : X₁.RationalMap X₂) {D : RDivisor X₁} {Q : MMP.Mori.PrimeDivisor X₂}
    (h : (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q ≠ 0) :
    ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q ∧ D.coeff P ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  apply h
  clear h
  revert hne
  induction D using Finsupp.induction with
  | zero => intro _; simp
  | single_add a b D ha hb ih =>
    intro hne
    have hDa : D a = 0 := Finsupp.notMem_support_iff.mp ha
    have hD' : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q →
        DivisorWithCoeffs.coeff D P = 0 := fun P hP => by
      have := hne P hP
      change (Finsupp.single a b + D) P = 0 at this
      by_cases hPa : P = a
      · subst hPa; exact hDa
      · rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hPa), zero_add] at this
        exact this
    rw [map_add, DivisorWithCoeffs.coeff_add, ih hD', add_zero,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases hta : MMP.Mori.RationalMap.transformPrimeDivisor φ' a with _ | F
    · simp
    · change (Finsupp.single F b) Q = 0
      rw [Finsupp.single_apply]
      split_ifs with hFQ
      · subst hFQ
        have := hne a hta
        change (Finsupp.single a b + D) a = 0 at this
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, hDa, add_zero] at this
      · rfl

/-- The coefficient of an effective divisor along `P` is at most that of its transform along the
transform of `P`. -/
private theorem coeff_le_transformDivisor_coeff {X₁ X₂ : Scheme.{0}} (φ' : X₁.RationalMap X₂)
    {D : RDivisor X₁} (hD : ∀ P, 0 ≤ D.coeff P) {P : MMP.Mori.PrimeDivisor X₁}
    {Q : MMP.Mori.PrimeDivisor X₂} (hPQ : MMP.Mori.RationalMap.transformPrimeDivisor φ' P = some Q)
        :
    D.coeff P ≤ (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q := by
  classical
  have hsplit : D = Finsupp.single P (D P) + D.erase P := (Finsupp.single_add_erase P D).symm
  have hE : ∀ W, 0 ≤ DivisorWithCoeffs.coeff (D.erase P) W := fun W => by
    change 0 ≤ (D.erase P) W
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hD W
  have key : (MMP.Mori.RationalMap.transformDivisor φ' D).coeff Q =
      D P + (MMP.Mori.RationalMap.transformDivisor φ' (D.erase P)).coeff Q := by
    conv_lhs => rw [hsplit]
    rw [map_add, DivisorWithCoeffs.coeff_add,
      MMP.Mori.RationalMap.transformDivisor_single_of_eq_some hPQ]
    change (Finsupp.single Q (D P)) Q + _ = _
    simp
  rw [key]
  change D P ≤ _
  linarith [transformDivisor_nonneg φ' hE Q]

/-- **The neighbourhood of the boundary.** Let `ψ : X ⤏ Y` be a nef weak model over `Z` of an
effective klt boundary `Θ`, with `Y` projective and `ℚ`-factorial. For divisors `Hᵢ` supported
where `Θ` has coefficients at least `δ > 0`, every small perturbation `Θ + ∑ uᵢ Hᵢ` and its
transform to `Y` are effective and klt. -/
private theorem exists_nbhd_of_isNefWeakModel {X Y Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hYp : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hYq : IsQFactorial sY) {KY : Divisor Y} {m : ℕ} (hKY : KY.IsCanonicalDivisor sY m)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {K : Divisor X} {Θ : RDivisor X} (hΘ0 : ∀ P, 0 ≤ Θ.coeff P)
    (hklt : IsRealKltPair sX Θ) {ι : Type} [Fintype ι] (H : ι → Divisor X) {δ : ℝ} (hδ : 0 < δ)
    (hHδ : ∀ i P, (H i).coeff P ≠ 0 → δ ≤ Θ.coeff P) {ψ : X.RationalMap Y}
    (hNW : IsNefWeakModel sX sY sZ π πY K Θ ψ) :
    ∃ ε₀ > 0, ∀ u : ι → ℝ, (∀ i, |u i| < ε₀) →
      (∀ P, 0 ≤ (Θ + ∑ i, u i • Divisor.toRDivisor (H i)).coeff P) ∧
      IsRealKltPair sX (Θ + ∑ i, u i • Divisor.toRDivisor (H i)) ∧
      (∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ
        (Θ + ∑ i, u i • Divisor.toRDivisor (H i))).coeff Q) ∧
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor ψ
        (Θ + ∑ i, u i • Divisor.toRDivisor (H i))) := by
  classical
  have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_isRealKltPair_add_sum_smul sX hXqp hXq hΘ0 hklt
    (fun i => Divisor.toRDivisor (H i)) hδ (fun i P hP => hHδ i P (by
      intro h0; apply hP; rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero]))
  have hYqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sY :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ _ hYp
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hYp.toIsVariety.toQuasiCompact
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  have hkltY := isRealKltPair_transformDivisor_of_isNefWeakModel hNW hYq hKY hklt
  have hΘ0Y : ∀ Q, 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ Θ).coeff Q :=
    transformDivisor_nonneg ψ hΘ0
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_isRealKltPair_add_sum_smul sY hYqp hYq hΘ0Y
    hkltY (fun i => MMP.Mori.RationalMap.transformDivisor ψ (Divisor.toRDivisor (H i))) hδ
    (fun i Q hQ => by
      obtain ⟨P, hPQ, hP⟩ := exists_of_transformDivisor_coeff_ne_zero ψ hQ
      refine (hHδ i P ?_).trans (coeff_le_transformDivisor_coeff ψ hΘ0 hPQ)
      intro h0; apply hP; rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero])
  have hlin : ∀ u : ι → ℝ, MMP.Mori.RationalMap.transformDivisor ψ
      (Θ + ∑ i, u i • Divisor.toRDivisor (H i)) =
      MMP.Mori.RationalMap.transformDivisor ψ Θ + ∑ i, u i •
        MMP.Mori.RationalMap.transformDivisor ψ (Divisor.toRDivisor (H i)) := fun u => by
    rw [map_add, map_sum]
    simp only [transformDivisor_smul]
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun u hu => ?_⟩
  obtain ⟨a₁, a₂⟩ := h₁ u fun i => (hu i).trans_le (min_le_left _ _)
  obtain ⟨b₁, b₂⟩ := h₂ u fun i => (hu i).trans_le (min_le_right _ _)
  rw [hlin]
  exact ⟨a₁, a₂, b₁, b₂⟩

end Neighbourhood

/-! ### A numerically trivial shift of the boundary containing a basis of `N¹(X/Z)` -/

section Shift

/-- A positive multiple of a numerically trivial divisor is numerically trivial. -/
private theorem isNumericallyTrivialOver_smul {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ Y}
    {D : RDivisor X} (hD : IsNumericallyTrivialOver k sX g D) (a : ℝ) :
    IsNumericallyTrivialOver k sX g (a • D) := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD.1
  simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hDL
  refine ⟨⟨m, a • r, L, hL, ?_⟩, hD.2.1, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  · simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]
    rw [hDL, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul]
  · have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r L hL
    rw [← hDL] at e
    have h0 : IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
        (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
      ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    have hx := hD.2.2 C hC _ _ _ _ _ _ _ _ e h0
    have hs := (IsRIntersectionNumber.eq_and_linear k sX C).2 D 0 r L Fin.elim0 Fin.elim0 _ _ a 0
      e h0
    rw [zero_smul, add_zero] at hs
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₁ hs,
      eq_zero_of_isRIntersectionNumber_zero C h₂, hx]
    ring

/-- A principal divisor is numerically trivial over any morphism. -/
private theorem isNumericallyTrivialOver_principalDivisor {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] (g : X ⟶ Y) (φ : (RationalFunctions X)ˣ) :
    IsNumericallyTrivialOver ℂ sX g (Divisor.toRDivisor (MMP.Mori.principalDivisor φ)) := by
  have hP := Divisor.isCartier_principalDivisor φ
  refine ⟨⟨1, fun _ => 1, fun _ => MMP.Mori.principalDivisor φ, fun _ => hP, by
      simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => MMP.Mori.principalDivisor φ) (fun _ => hP)
  have hy0 : (MMP.Mori.principalDivisor φ).degreeOn ℂ sX C.ι C.dim_le hP = 0 :=
    Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hP
      (Divisor.linearlyEquivalent_principalDivisor_zero φ)
  rw [eq_zero_of_isRIntersectionNumber_zero C h₂,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ h₁ (by simpa using e)]
  simp [hy0]

/-- **A pull-back from the base is numerically trivial over the base.** Let `π : X ⟶ Z` be a
morphism of projective varieties with `X` normal. The Weil divisor of the pull-back of a Cartier
divisor of `Z` is numerically trivial over `Z`: through the Stein factorization `X ⟶ Y' ⟶ Z`, it
is the pull-back of a Cartier divisor of the normal variety `Y'`. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_isPullback {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    {T₀ : Z.CartierDivisor} {T₀' : X.CartierDivisor} {w : Divisor X}
    (hT : MMP.Intersection.IsPullback π T₀ T₀')
    (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w) :
    IsNumericallyTrivialOver ℂ sX π (Divisor.toRDivisor w) := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper (π ≫ sZ) := by rw [hπ]; infer_instance
  haveI : IsProper π := IsProper.of_comp π sZ
  obtain ⟨Y', f', g, ⟨hS⟩, -, hf's, -, -, -, hvar, -, hnorm, -, hcontr⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sX sZ π hπ
  have hcomp : f' ≫ g = π := hS.comp
  haveI : IsNormal Y' := hnorm inferInstance
  haveI : IsIntegral Y' := hvar.toIsIntegral
  haveI : LocallyOfFiniteType (g ≫ sZ) := hvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sZ)
  haveI : QuasiCompact (g ≫ sZ) := hvar.toQuasiCompact
  haveI : IsSeparated (g ≫ sZ) := hvar.toIsSeparated
  haveI : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (g ≫ sZ)
  haveI : IsDominant f' := inferInstance
  have hgen : f' (genericPoint X) = genericPoint Y' := map_genericPoint_of_isDominant f'
  have hassoc : ∀ (V : Scheme.{0}) [IsIntegral V] [IsLocallyNoetherian V],
      Stacks.Divisors.schemeAssociatedPoints V = {genericPoint V} := fun V _ =>
    calc Stacks.Divisors.schemeAssociatedPoints V
        = Stacks.Divisors.schemeWeaklyAssociatedPoints V :=
          AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints V _
      _ = genericPoints V := AlgebraicGeometry.weaklyAssociatedPointsOfScheme_eq_genericPoints V
      _ = {genericPoint V} := genericPoints_eq_singleton
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hpcg : MMP.Intersection.PullbackCondition g T₀ := by
    intro η hη
    rw [hassoc Y'] at hη
    rw [Set.mem_singleton_iff.mp hη, ← hgen, ← Scheme.Hom.comp_apply, hcomp]
    exact hT.1 _ (by rw [hassoc X]; rfl)
  obtain ⟨T₁, hT₁⟩ := MMP.Intersection.exists_isPullback hpcg
  have hpcf : MMP.Intersection.PullbackCondition f' T₁ := by
    intro η hη
    rw [hassoc X] at hη
    rw [Set.mem_singleton_iff.mp hη, hgen]
    exact notMem_cartierSupport_of_coheight_eq_zero T₁ (Order.coheight_eq_zero.2 fun b hb => by
      rw [Scheme.le_iff_specializes] at hb ⊢
      exact genericPoint_specializes _)
  obtain ⟨T₂, hT₂⟩ := MMP.Intersection.exists_isPullback hpcf
  have hT₂' : T₀' = T₂ := MMP.Intersection.IsPullback.comp_eq hT₁ hT₂ (hcomp ▸ hT)
  subst hT₂'
  obtain ⟨w₀, hw₀⟩ := exists_isWeilDivisorOfCartier T₁
  have hwc : w.IsCartier := hw.isCartier
  refine ⟨⟨1, fun _ => 1, fun _ => w, fun _ => hwc, by
      simp [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩,
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have hC' : C.IsContractedBy f' := (hcontr C).mp hC
  have e := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => w) (fun _ => hwc)
  have hd := MMP.Fourfold.eq_zero_of_isCartierIntersectionNumber_of_isPullback (k := ℂ) f'
    (by rw [← Category.assoc, hcomp, hπ]) hw₀ hT₂ hw hwc C hC'
    (MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX C w hwc)
  rw [eq_zero_of_isRIntersectionNumber_zero C h₂,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ h₁ (by simpa using e)]
  simp [hd]

/-- A `ℚ`-divisor `ℚ`-linearly equivalent to a multiple of the Weil divisor of a pull-back from
the base is numerically trivial over the base. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_qLinearlyEquivalent {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    {T₀ : Z.CartierDivisor} {T₀' : X.CartierDivisor} {w : Divisor X}
    (hT : MMP.Intersection.IsPullback π T₀ T₀')
    (hw : MMP.Intersection.IsWeilDivisorOfCartier T₀' w) {c : ℚ} {TY : QDivisor X}
    (hTY : TY.QLinearlyEquivalent (c • Divisor.toQDivisor w)) :
    IsNumericallyTrivialOver ℂ sX π (QDivisor.toRDivisor TY) := by
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  obtain ⟨m, hm, φ, hφ⟩ := hTY
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : QDivisor.toRDivisor TY = (c : ℝ) • Divisor.toRDivisor w +
      (m : ℝ)⁻¹ • Divisor.toRDivisor (MMP.Mori.principalDivisor φ) := by
    refine Finsupp.ext fun P => ?_
    have := congrArg (fun D : QDivisor X => D.coeff P) hφ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.coe_sub,
      Pi.sub_apply, zsmul_eq_mul, smul_eq_mul] at this
    change ((TY P : ℚ) : ℝ) = (c : ℝ) * ((w P : ℤ) : ℝ) + (m : ℝ)⁻¹ *
      (((MMP.Mori.principalDivisor φ) P : ℤ) : ℝ)
    have h2 : (TY P : ℚ) = c * (w P : ℚ) + (m : ℚ)⁻¹ * (((MMP.Mori.principalDivisor φ) P : ℤ) : ℚ)
        := by
      have hm'' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      have h3 : (m : ℚ) * (TY P - c * (w P : ℚ)) = (((MMP.Mori.principalDivisor φ) P : ℤ) : ℚ) := by
        have := this
        push_cast at this
        exact this
      rw [← h3]
      field_simp
      ring
    rw [h2]
    push_cast
    ring
  rw [heq]
  exact isNumericallyTrivialOver_add
    (isNumericallyTrivialOver_smul
      (isNumericallyTrivialOver_toRDivisor_of_isPullback hX hZ π hπ hT hw) _)
    (isNumericallyTrivialOver_smul (isNumericallyTrivialOver_principalDivisor π φ) _)

/-- Real klt boundaries form a convex set on a `ℚ`-factorial variety. -/
private theorem nonneg_isRealKltPair_add_of_mem_convexHull {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {V : Set (RDivisor X)} (c : RDivisor X)
    (hV : ∀ v ∈ V, (∀ P, 0 ≤ (v + c).coeff P) ∧ IsRealKltPair sX (v + c)) {x : RDivisor X}
    (hx : x ∈ convexHull ℝ V) : (∀ P, 0 ≤ (x + c).coeff P) ∧ IsRealKltPair sX (x + c) := by
  have hconv : Convex ℝ {y : RDivisor X | (∀ P, 0 ≤ (y + c).coeff P) ∧
      IsRealKltPair sX (y + c)} := by
    intro y hy z hz a b ha hb hab
    have e : a • y + b • z + c = (1 - b) • (y + c) + b • (z + c) := by
      rw [show a = 1 - b by linarith]; module
    refine ⟨fun P => ?_, ?_⟩
    · rw [e, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul]
      have := hy.1 P; have := hz.1 P
      nlinarith
    · rw [e]
      exact isRealKltPair_segment hQ hy.2 hz.2 hb (by linarith)
  exact convexHull_min hV hconv hx

end Shift

/-! ### The shift: an ample core and a basis inside the boundary -/

section ShiftConstruction

/-- A rational klt pair is a real klt pair. -/
private theorem isRealKltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hXq : IsQFactorial sX) {D : QDivisor X} (hD : MMP.Fourfold.IsKltPair sX D) :
    IsRealKltPair sX (QDivisor.toRDivisor D) := by
  have hXn : IsNormalVariety ℂ sX := hD.1.isPair.1
  obtain ⟨n, K, hK, -⟩ := hD.1.isPair.2
  refine ⟨hXn, fun P => ?_, ⟨n, K, hK, isRCartier_of_isQFactorial hXq _⟩, hD.2⟩
  have hm := MMP.Fourfold.PltReference.isLogDiscrepancy_ofPrimeDivisor hXn hK
    (isRCartier_of_isQFactorial hXq (Divisor.toRDivisor K + QDivisor.toRDivisor D)) P
  have := hD.2 _ _ _ hm
  linarith

/-- A fraction of a relatively big `ℚ`-divisor is relatively big. -/
private theorem isRelativelyBig_inv_smul {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {π : X ⟶ Z} {A : QDivisor X} (hA : A.IsRelativelyBig π)
    (n : ℕ) (hn : 0 < n) : ((n : ℚ)⁻¹ • A).IsRelativelyBig π := by
  obtain ⟨m, hm, D, hD, hDc, hDb⟩ := hA
  refine ⟨m * n, Nat.mul_pos hm hn, D, ?_, hDc, hDb⟩
  rw [hD, smul_smul]
  congr 1
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-- **Effective twists of a relatively ample divisor.** For an `f`-ample Cartier divisor `A` and
Cartier divisors `vᵢ`, there are `n ≥ 1` and effective Cartier divisors `h i ε`, `ε = ±`, with
`h i ε ≡ ℓ (n A ± vᵢ)` over the base for some `ℓ ≥ 1`. -/
private theorem exists_effective_family {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (π : X ⟶ Z) (hπ : π ≫ sZ = sX) {Ac : X.CartierDivisor}
    (hAc : IsRelativelyAmple π (MMP.CartierDivisor.sheaf Ac))
    {ι : Type} [Fintype ι] (v : ι → Divisor X) (hv : ∀ i, (v i).IsCartier) :
    ∃ (n : ℕ) (h : ι → Bool → Divisor X) (ℓ : ι → Bool → ℕ) (hhc : ∀ i ε, (h i ε).IsCartier),
      0 < n ∧ (∀ i ε, 0 < ℓ i ε) ∧ (∀ i ε P, 0 ≤ (h i ε).coeff P) ∧
      ∀ i ε (C : ProperCurve sX), C.IsContractedBy π →
        haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
        ((h i ε).degreeOn ℂ sX C.ι C.dim_le (hhc i ε) : ℝ) =
          ℓ i ε * (n * (C.degree ℂ (MMP.CartierDivisor.sheaf Ac) : ℝ) +
            (if ε then 1 else -1) * ((v i).degreeOn ℂ sX C.ι C.dim_le (hv i) : ℝ)) := by
  classical
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : QuasiCompact sZ := hZ.toIsVariety.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper (π ≫ sZ) := by rw [hπ]; infer_instance
  haveI : IsProper π := IsProper.of_comp π sZ
  choose V hV using fun i => exists_isWeilDivisorOfCartier_of_isCartier (hv i)
  let E : ι → Bool → X.CartierDivisor := fun i ε => if ε then V i else -V i
  choose n₀ hn₀ using fun p : ι × Bool =>
    MMP.Fourfold.exists_isRelativelyAmple_nsmul_add π hAc (E p.1 p.2)
  set n := (Finset.univ.sup fun p : ι × Bool => n₀ p) + 1 with hn
  have hamp : ∀ i ε, IsRelativelyAmple π
      (MMP.CartierDivisor.sheaf (n • Ac + E i ε)) := fun i ε =>
    hn₀ (i, ε) n ((Finset.le_sup (f := fun p : ι × Bool => n₀ p) (Finset.mem_univ (i, ε))).trans
      (Nat.le_succ _))
  choose H ℓ hℓ hHe hdeg using fun p : ι × Bool =>
    MMP.Fourfold.exists_isEffective_degree_eq_nsmul_of_isRelativelyAmple sX sZ π hX hZ hπ
      (n • Ac + E p.1 p.2) (hamp p.1 p.2)
  choose h hh using fun p : ι × Bool => exists_isWeilDivisorOfCartier (H p)
  refine ⟨n, fun i ε => h (i, ε), fun i ε => ℓ (i, ε), fun i ε => (hh (i, ε)).isCartier,
    Nat.succ_pos _, fun i ε => hℓ (i, ε), fun i ε P =>
      (hh (i, ε) P).nonneg_of_isEffective (hHe (i, ε)),
    fun i ε C hC => ?_⟩
  rw [degreeOn_eq_degree_sheaf C (hh (i, ε)), hdeg (i, ε) C hC,
    degreeOn_eq_degree_sheaf C (hV i) (hv i)]
  have h1 := MMP.Fourfold.cdeg_add (n • Ac) (E i ε) C
  have h2 := MMP.Fourfold.cdeg_nsmul Ac n C
  have h3 := MMP.Fourfold.cdeg_neg (V i) C
  simp only [MMP.Fourfold.cdeg] at h1 h2 h3
  cases ε
  · simp only [E, Bool.false_eq_true, if_false] at h1 ⊢
    rw [h1, h2, h3]
    push_cast; ring
  · simp only [E, if_true] at h1 ⊢
    rw [h1, h2]
    push_cast; ring

/-- Numerical equivalence from equal degrees of two presentations. -/
private theorem isNumericallyEquivalentOver_of_sum_degreeOn_eq {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {g : X ⟶ Y} {A B : RDivisor X} {m₁ m₂ : ℕ} (r₁ : Fin m₁ → ℝ)
    (L₁ : Fin m₁ → Divisor X) (hL₁ : ∀ j, (L₁ j).IsCartier) (r₂ : Fin m₂ → ℝ)
    (L₂ : Fin m₂ → Divisor X) (hL₂ : ∀ j, (L₂ j).IsCartier)
    (hA : A = ∑ j, r₁ j • Divisor.toRDivisor (L₁ j))
    (hB : B = ∑ j, r₂ j • Divisor.toRDivisor (L₂ j))
    (hdeg : ∀ C : ProperCurve sX, C.IsContractedBy g →
      ∑ j, r₁ j * ((L₁ j).degreeOn k sX C.ι C.dim_le (hL₁ j) : ℝ) =
        ∑ j, r₂ j * ((L₂ j).degreeOn k sX C.ι C.dim_le (hL₂ j) : ℝ)) :
    IsNumericallyEquivalentOver k sX g A B := by
  refine ⟨⟨m₁, r₁, L₁, hL₁, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]; exact hA⟩,
    ⟨m₂, r₂, L₂, hL₂, by simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]; exact hB⟩,
    fun C hC m₁' r₁' L₁' x₁ m₂' r₂' L₂' x₂ h₁ h₂ => ?_⟩
  have e₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₁ L₁ hL₁
  rw [← hA] at e₁
  have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn k sX C r₂ L₂ hL₂
  rw [← hB] at e₂
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₁ e₁,
    (IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ h₂ e₂]
  exact hdeg C hC

/-- **The shift of the boundary.** Let `π : X ⟶ Z` be a projective morphism of projective complex
varieties with `X` `ℚ`-factorial, `B, C ≥ 0` with `(X, B + C)` klt, and `A ≤ B` an effective
`ℚ`-divisor big over `Z`. There are Cartier divisors `Hᵢ` whose classes form a basis of
`N¹(X/Z)` and a divisor `T` numerically trivial over `Z` such that `B + T ≥ 0` contains every
component of every `Hᵢ` with coefficient at least `δ > 0`, every `(X, B + T + t C)`, `0 ≤ t ≤ 1`,
is klt, and `B + T ≥ A / 2`. Here `T = T_Y + s (F - A')` with `T_Y ∼_ℚ` a pull-back from `Z`
and `A'` an ample core given by the relative big-core translation, and `F ≡ A'` an effective
combination of twists of `A'` by a spanning family of `N¹(X/Z)`. -/
private theorem exists_shift {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (π : X ⟶ Z) (hπ : π ≫ sZ = sX) (hπp : IsProjective π) (hXq : IsQFactorial sX)
    {B C : RDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hklt : IsRealKltPair sX (B + C)) {A : QDivisor X} (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAbig : A.IsRelativelyBig π) (hAB : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P) :
    ∃ (ι : Type) (_ : Fintype ι) (H : ι → Divisor X) (T : RDivisor X),
      (∀ i, (H i).IsCartier) ∧
      (∀ D : RDivisor X, IsCartierCombination D → ∃ u : ι → ℝ,
        IsNumericallyEquivalentOver ℂ sX π D (∑ i, u i • Divisor.toRDivisor (H i))) ∧
      (∀ u : ι → ℝ,
        IsNumericallyTrivialOver ℂ sX π (∑ i, u i • Divisor.toRDivisor (H i)) → u = 0) ∧
      IsNumericallyTrivialOver ℂ sX π T ∧ (∀ P, 0 ≤ (B + T).coeff P) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → IsRealKltPair sX (B + T + t • C)) ∧
      (∃ δ > 0, ∀ i P, (H i).coeff P ≠ 0 → δ ≤ (B + T).coeff P) ∧
      ∀ P, (A.coeff P : ℝ) / 2 ≤ (B + T).coeff P := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsProper (π ≫ sZ) := by rw [hπ]; infer_instance
  haveI : IsProper π := IsProper.of_comp π sZ
  have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
    @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
  -- the halved core `S = A / 2` and the lowered boundary `B₁ = B - S`
  set S : QDivisor X := (2 : ℚ)⁻¹ • A with hSdef
  set G₀ : QDivisor X := (4 : ℚ)⁻¹ • A with hG₀def
  set B₁ : RDivisor X := B - QDivisor.toRDivisor S with hB₁def
  have hScoeff : ∀ P, ((S.coeff P : ℚ) : ℝ) = (A.coeff P : ℝ) / 2 := fun P => by
    simp only [hSdef, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
  have hG₀coeff : ∀ P, ((G₀.coeff P : ℚ) : ℝ) = (A.coeff P : ℝ) / 4 := fun P => by
    simp only [hG₀def, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
  have hB₁coeff : ∀ P, B₁.coeff P = B.coeff P - (A.coeff P : ℝ) / 2 := fun P => by
    rw [hB₁def, DivisorWithCoeffs.coeff_sub, QDivisor.coeff_toRDivisor, hScoeff]
  have hA0' : ∀ P, (0 : ℝ) ≤ A.coeff P := fun P => by exact_mod_cast hA0 P
  -- a rational klt polytope around the lowered segment, stable under adding `S`
  have hpoly : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ V : Finset (QDivisor X),
      (∀ E ∈ V, ∀ P, 0 ≤ E.coeff P) ∧ (∀ E ∈ V, IsRealKltPair sX (QDivisor.toRDivisor E)) ∧
      (∀ E ∈ V, IsRealKltPair sX (QDivisor.toRDivisor E + QDivisor.toRDivisor S)) ∧
      (∀ E ∈ V, ∀ P, G₀.coeff P ≤ E.coeff P) ∧
      B₁ + t • C ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
    intro t ht0 ht1
    have hcoeff : ∀ P, (B₁ + t • C).coeff P = B.coeff P - (A.coeff P : ℝ) / 2 + t * C.coeff P :=
      fun P => by
        rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hB₁coeff, smul_eq_mul]
    have hle : ∀ P, (B₁ + t • C).coeff P ≤ (B + C).coeff P := fun P => by
      rw [hcoeff, DivisorWithCoeffs.coeff_add]
      nlinarith [hA0' P, hC P, mul_le_mul_of_nonneg_right ht1 (hC P)]
    have hle' : ∀ P, (B₁ + t • C + QDivisor.toRDivisor S).coeff P ≤ (B + C).coeff P := fun P => by
      rw [DivisorWithCoeffs.coeff_add, hcoeff, QDivisor.coeff_toRDivisor, hScoeff,
        DivisorWithCoeffs.coeff_add]
      nlinarith [hC P, mul_le_mul_of_nonneg_right ht1 (hC P)]
    obtain ⟨V, ε, hε, hV0, hVk, hVkS, hVG, hVmem⟩ :=
      exists_finset_isKltPair_convexHull_of_shift sX hXqp hXq (Θ := B₁ + t • C)
        (fun P => by rw [hcoeff]; nlinarith [hAB P, hA0' P, hC P, mul_nonneg ht0 (hC P)])
        (isRealKltPair_of_le hXq hklt hle) S (fun P => by
          have := hScoeff P; have := hA0' P
          exact_mod_cast (show (0 : ℝ) ≤ (S.coeff P : ℝ) by linarith))
        (fun P hP => by
          have hSP : (S.coeff P : ℝ) ≠ 0 := by exact_mod_cast hP
          rw [hScoeff] at hSP
          have hApos : 0 < (A.coeff P : ℝ) := lt_of_le_of_ne (hA0' P) (by
            intro h; apply hSP; rw [← h]; ring)
          rw [hcoeff]
          nlinarith [hAB P, hC P, mul_nonneg ht0 (hC P)])
        (isRealKltPair_of_le hXq hklt hle') G₀ (fun P => by
          have := hG₀coeff P; have := hA0' P
          exact_mod_cast (show (0 : ℝ) ≤ (G₀.coeff P : ℝ) by linarith))
        (fun P => by
          rw [hG₀coeff, hcoeff]; nlinarith [hAB P, hC P, mul_nonneg ht0 (hC P)])
        (ι := Empty) Empty.elim one_pos (fun i => i.elim)
    refine ⟨V, hV0, hVk, hVkS, hVG, ?_⟩
    simpa using hVmem Empty.elim (fun i => i.elim)
  obtain ⟨V₀, hV₀0, hV₀k, hV₀kS, hV₀G, hV₀m⟩ := hpoly 0 le_rfl zero_le_one
  obtain ⟨V₁, hV₁0, hV₁k, hV₁kS, hV₁G, hV₁m⟩ := hpoly 1 zero_le_one le_rfl
  -- the rational vertices and their translates by `S`
  set W₀ : Finset (QDivisor X) := V₀ ∪ V₁ with hW₀def
  have hW₀ : ∀ E ∈ W₀, (∀ P, 0 ≤ E.coeff P) ∧ IsRealKltPair sX (QDivisor.toRDivisor E) ∧
      IsRealKltPair sX (QDivisor.toRDivisor E + QDivisor.toRDivisor S) ∧
      ∀ P, G₀.coeff P ≤ E.coeff P := by
    intro E hE
    rcases Finset.mem_union.mp hE with h | h
    · exact ⟨hV₀0 E h, hV₀k E h, hV₀kS E h, hV₀G E h⟩
    · exact ⟨hV₁0 E h, hV₁k E h, hV₁kS E h, hV₁G E h⟩
  have hS0 : ∀ P, 0 ≤ S.coeff P := fun P => by
    have := hScoeff P; have := hA0' P
    exact_mod_cast (show (0 : ℝ) ≤ (S.coeff P : ℝ) by linarith)
  set V : Finset (QDivisor X) := W₀ ∪ W₀.image (· + S) with hVdef
  have hV : ∀ Γ ∈ V, (∀ P, 0 ≤ Γ.coeff P) ∧ IsRealKltPair sX (QDivisor.toRDivisor Γ) ∧
      ∀ P, G₀.coeff P ≤ Γ.coeff P := by
    intro Γ hΓ
    rcases Finset.mem_union.mp hΓ with h | h
    · exact ⟨(hW₀ Γ h).1, (hW₀ Γ h).2.1, (hW₀ Γ h).2.2.2⟩
    · obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h0, -, hkS, hG⟩ := hW₀ E hE
      refine ⟨fun P => ?_, by rw [map_add]; exact hkS, fun P => ?_⟩
      · rw [DivisorWithCoeffs.coeff_add]; exact add_nonneg (h0 P) (hS0 P)
      · rw [DivisorWithCoeffs.coeff_add]; linarith [hG P, hS0 P]
  have hG₀big : G₀.IsRelativelyBig π := by
    have := isRelativelyBig_inv_smul hAbig 4 (by norm_num)
    simpa [hG₀def] using this
  have hG₀eff : G₀.IsEffective := fun P => by
    have := hG₀coeff P; have := hA0' P
    exact_mod_cast (show (0 : ℝ) ≤ (G₀.coeff P : ℝ) by linarith)
  -- the relative big-core translation
  obtain ⟨A', TY, hA'amp, hA'eff, ⟨c, T₀, T₀', w, hT, hw, hTY⟩, hconvV, hkltV⟩ :=
    MMP.Fourfold.QDivisor.IsRelativelyBig.exists_isKltPair_add_pullback_sub_isAmple sX sZ hXq π hπ
      hG₀big hG₀eff V (fun Γ hΓ => (hV Γ hΓ).1)
      (fun Γ hΓ => Finsupp.le_def.mpr fun P => (hV Γ hΓ).2.2 P)
      (fun Γ hΓ => MMP.Fourfold.isKltPair_of_isRealKltPair hXq (hV Γ hΓ).1 (hV Γ hΓ).2.1)
  set τ := QDivisor.toRDivisor TY with hτdef
  set α := QDivisor.toRDivisor A' with hαdef
  have hτ : IsNumericallyTrivialOver ℂ sX π τ :=
    isNumericallyTrivialOver_toRDivisor_of_qLinearlyEquivalent hX hZ π hπ hT hw hTY
  have hα0 : ∀ P, 0 ≤ α.coeff P := fun P => by
    rw [hαdef, QDivisor.coeff_toRDivisor]; exact_mod_cast hA'eff P
  -- every `Γ + τ - s α`, `Γ ∈ V`, `s ∈ [0, 1]`, is effective and klt
  have hΓs : ∀ Γ ∈ V, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (∀ P, 0 ≤ (QDivisor.toRDivisor Γ + τ - s • α).coeff P) ∧
        IsRealKltPair sX (QDivisor.toRDivisor Γ + τ - s • α) := by
    intro Γ hΓ s hs0 hs1
    have heff := hconvV Γ (subset_convexHull ℚ _ (Finset.mem_coe.mpr hΓ))
    obtain ⟨hk1, hk2⟩ := hkltV Γ hΓ
    have hk1' := isRealKltPair_of_isKltPair hXq hk1
    have hk2' := isRealKltPair_of_isKltPair hXq hk2
    rw [map_sub, map_add] at hk1'
    rw [map_add] at hk2'
    have e : QDivisor.toRDivisor Γ + τ - s • α =
        (1 - s) • (QDivisor.toRDivisor Γ + τ) + s • (QDivisor.toRDivisor Γ + τ - α) := by
      module
    refine ⟨fun P => ?_, ?_⟩
    · have h' : (0 : ℝ) ≤ ((Γ + TY - A').coeff P : ℝ) := by exact_mod_cast heff P
      have h'' := hα0 P
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, QDivisor.coeff_toRDivisor, hτdef,
        hαdef] at h' h'' ⊢
      push_cast at h'
      nlinarith
    · rw [e]
      exact isRealKltPair_segment hXq hk2' hk1' hs0 hs1
  -- the segment `B₁ + t C` lies in the rational hull of `W₀`
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      B₁ + t • C ∈ convexHull ℝ (QDivisor.toRDivisor '' (W₀ : Set (QDivisor X))) := by
    intro t ht0 ht1
    have hsub : ∀ W : Finset (QDivisor X), W ⊆ W₀ →
        convexHull ℝ (QDivisor.toRDivisor '' (W : Set (QDivisor X))) ⊆
          convexHull ℝ (QDivisor.toRDivisor '' (W₀ : Set (QDivisor X))) := fun W hW =>
      convexHull_mono (Set.image_mono (by exact_mod_cast hW))
    have h₀ := hsub V₀ Finset.subset_union_left hV₀m
    have h₁ := hsub V₁ Finset.subset_union_right hV₁m
    have heq : B₁ + t • C = (1 - t) • (B₁ + (0 : ℝ) • C) + t • (B₁ + (1 : ℝ) • C) := by module
    rw [heq]
    exact (convex_convexHull ℝ _) h₀ h₁ (sub_nonneg.2 ht1) ht0 (by ring)
  have hmain : ∀ t s : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ s → s ≤ 1 →
      (∀ P, 0 ≤ (B + t • C + τ - s • α).coeff P) ∧ IsRealKltPair sX (B + t • C + τ - s • α) := by
    intro t s ht0 ht1 hs0 hs1
    have := nonneg_isRealKltPair_add_of_mem_convexHull hXq
      (QDivisor.toRDivisor S + τ - s • α) (fun v hv => ?_) (hseg t ht0 ht1)
    · rwa [show B₁ + t • C + (QDivisor.toRDivisor S + τ - s • α) = B + t • C + τ - s • α by
        rw [hB₁def]; abel] at this
    · obtain ⟨E, hE, rfl⟩ := hv
      have hES : E + S ∈ V := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hE)
      have := hΓs (E + S) hES s hs0 hs1
      rwa [map_add, show QDivisor.toRDivisor E + QDivisor.toRDivisor S + τ - s • α =
        QDivisor.toRDivisor E + (QDivisor.toRDivisor S + τ - s • α) by abel] at this
  have hmain0 : ∀ t s : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ s → s ≤ 1 →
      ∀ P, 0 ≤ (B₁ + t • C + τ - s • α).coeff P := by
    intro t s ht0 ht1 hs0 hs1
    have := nonneg_isRealKltPair_add_of_mem_convexHull hXq (τ - s • α) (fun v hv => ?_)
      (hseg t ht0 ht1)
    · intro P
      have h := this.1 P
      rwa [show B₁ + t • C + (τ - s • α) = B₁ + t • C + τ - s • α by abel] at h
    · obtain ⟨E, hE, rfl⟩ := hv
      have := hΓs E (Finset.mem_union_left _ hE) s hs0 hs1
      rwa [show QDivisor.toRDivisor E + τ - s • α = QDivisor.toRDivisor E + (τ - s • α) by
        abel] at this
  -- the ample core as a Cartier divisor
  obtain ⟨mA, hmA, DA, hDA, hDAc, hDAamp⟩ := hA'amp
  obtain ⟨Ac, hAc⟩ := exists_isWeilDivisorOfCartier_of_isCartier hDAc
  haveI := hDAc.isInvertibleModule_divisorialSheaf
  have hAcamp : IsRelativelyAmple π (MMP.CartierDivisor.sheaf Ac) :=
    MMP.Fourfold.isRelativelyAmple_of_iso π hAc.sheafIsoDivisorialSheaf.symm
      (MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple π _ hDAamp)
  have hmA' : (mA : ℝ) ≠ 0 := by exact_mod_cast hmA.ne'
  have hαDA : α = (mA : ℝ)⁻¹ • Divisor.toRDivisor DA := by
    refine Finsupp.ext fun P => ?_
    have := congrArg (fun D : QDivisor X => D.coeff P) hDA
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at this
    change ((A'.coeff P : ℚ) : ℝ) = (mA : ℝ)⁻¹ * ((DA.coeff P : ℤ) : ℝ)
    have h2 : (A'.coeff P : ℚ) = (mA : ℚ)⁻¹ * (DA.coeff P : ℚ) := by
      have hm : (mA : ℚ) ≠ 0 := by exact_mod_cast hmA.ne'
      rw [this]
      field_simp
    rw [h2]; push_cast; ring
  -- a spanning family of `N¹(X/Z)` and its effective twists `h o ε ≡ ℓ (n D_A ± v o)`
  obtain ⟨N, v, hvc, hvspan⟩ := exists_cartier_spanning hX hZ π hπ hπp
  let v' : Option (Fin N) → Divisor X := fun o => o.elim 0 v
  have hv'c : ∀ o, (v' o).IsCartier := fun o => by
    cases o
    · exact Divisor.isCartier_zero
    · exact hvc _
  obtain ⟨n, h, ℓ, hhc, hn, hℓ, hh0, hdeg⟩ := exists_effective_family hX hZ π hπ hAcamp v' hv'c
  have hdA : ∀ C : ProperCurve sX, (DA.degreeOn ℂ sX C.ι C.dim_le hDAc : ℝ) =
      (C.degree ℂ (MMP.CartierDivisor.sheaf Ac) : ℝ) := fun C => by
    rw [degreeOn_eq_degree_sheaf C hAc hDAc]
  -- reindexing the family by `Fin`
  let e := Fintype.equivFin (Option (Fin N) × Bool)
  let hf : Fin (Fintype.card (Option (Fin N) × Bool)) → Divisor X := fun j =>
    h (e.symm j).1 (e.symm j).2
  have hfc : ∀ j, (hf j).IsCartier := fun j => hhc _ _
  have hsum_e : ∀ g : Option (Fin N) × Bool → ℝ,
      ∑ j, g (e.symm j) = ∑ o, (g (o, true) + g (o, false)) := fun g => by
    rw [Equiv.sum_comp e.symm g, Fintype.sum_prod_type]
    simp [Fintype.sum_bool, add_comm]
  have hfspan : ∀ D : RDivisor X, IsCartierCombination D → ∃ c' : Fin _ → ℝ,
      IsNumericallyEquivalentOver ℂ sX π D (∑ j, c' j • Divisor.toRDivisor (hf j)) := by
    intro D hD
    obtain ⟨c₀, hc₀⟩ := hvspan D hD
    let wc : Option (Fin N) × Bool → ℝ := fun κ =>
      κ.1.elim 0 fun k => (if κ.2 then 1 else -1) * c₀ k / (2 * ℓ (some k) κ.2)
    refine ⟨fun j => wc (e.symm j), ?_⟩
    have hD' := hc₀
    refine ⟨hD, ⟨_, fun j => wc (e.symm j), hf, hfc, by
      simp_rw [← MMP.Flips.toRDivisor_eq_mapCoeffs]⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
    have e₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C (fun j => wc (e.symm j)) hf hfc
    have e₃ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C c₀ v hvc
    rw [hc₀.2.2 C hC _ _ _ _ _ _ _ _ h₁ e₃,
      (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ h₂ e₂]
    rw [hsum_e (fun κ => wc κ * ((h κ.1 κ.2).degreeOn ℂ sX C.ι C.dim_le (hhc κ.1 κ.2) : ℝ)),
      Fintype.sum_option]
    simp only [wc, Option.elim, zero_mul, add_zero, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdeg (some k) true C hC, hdeg (some k) false C hC]
    have h1 : (ℓ (some k) true : ℝ) ≠ 0 := by exact_mod_cast (hℓ _ _).ne'
    have h2 : (ℓ (some k) false : ℝ) ≠ 0 := by exact_mod_cast (hℓ _ _).ne'
    simp only [v', Option.elim, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  obtain ⟨ι, _, a, hspanH, hindH⟩ := exists_basis_of_isNumericallyEquivalentOver π hf hfc hfspan
  -- the effective representative `F ≡ α` of the ample core
  let cF : Option (Fin N) × Bool → ℝ := fun κ =>
    ((2 * (N + 1) * n * mA * ℓ κ.1 κ.2 : ℕ) : ℝ)⁻¹
  have hcF : ∀ κ, 0 < cF κ := fun κ => by
    have := hℓ κ.1 κ.2
    simp only [cF]
    positivity
  set F : RDivisor X := ∑ j, cF (e.symm j) • Divisor.toRDivisor (hf j) with hFdef
  have hF0 : ∀ P, 0 ≤ F.coeff P := fun P => by
    rw [hFdef, MMP.Fourfold.coeff_sum_smul_toRDivisor]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hcF _).le (by exact_mod_cast hh0 (e.symm j).1 (e.symm j).2 P)
  have hFα : IsNumericallyEquivalentOver ℂ sX π F α := by
    refine isNumericallyEquivalentOver_of_sum_degreeOn_eq (fun j => cF (e.symm j)) hf hfc
      (fun _ : Fin 1 => (mA : ℝ)⁻¹) (fun _ => DA) (fun _ => hDAc) rfl
      (by rw [hαDA]; simp) fun C hC => ?_
    rw [hsum_e (fun κ => cF κ * ((h κ.1 κ.2).degreeOn ℂ sX C.ι C.dim_le (hhc κ.1 κ.2) : ℝ))]
    simp only [Fin.sum_univ_one, hdA C]
    have hterm : ∀ o, cF (o, true) * ((h o true).degreeOn ℂ sX C.ι C.dim_le (hhc o true) : ℝ) +
        cF (o, false) * ((h o false).degreeOn ℂ sX C.ι C.dim_le (hhc o false) : ℝ) =
        ((N : ℝ) + 1)⁻¹ * ((mA : ℝ)⁻¹ *
          (C.degree ℂ (MMP.CartierDivisor.sheaf Ac) : ℝ)) := fun o => by
      rw [hdeg o true C hC, hdeg o false C hC]
      have h1 : (ℓ o true : ℝ) ≠ 0 := by exact_mod_cast (hℓ _ _).ne'
      have h2 : (ℓ o false : ℝ) ≠ 0 := by exact_mod_cast (hℓ _ _).ne'
      have h3 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [cF, if_true, Bool.false_eq_true, if_false]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl fun o _ => hterm o, Finset.sum_const, Finset.card_univ,
      Fintype.card_option, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hFαt : IsNumericallyTrivialOver ℂ sX π (F - α) := isNumericallyTrivialOver_sub hFα
  -- the shift is `T = τ + s₀ (F - α)` for a small `s₀ > 0`
  obtain ⟨hΘ0, hΘk⟩ := hmain 1 0 zero_le_one le_rfl le_rfl zero_le_one
  rw [zero_smul, sub_zero, one_smul] at hΘ0 hΘk
  obtain ⟨t₀, ht₀, hkF⟩ := exists_isRealKltPair_add_smul sX hXqp hXq hΘ0 hF0 hΘk
  set s₀ : ℝ := min (1 / 2) (t₀ / 2) with hs₀def
  have hs₀0 : 0 < s₀ := lt_min (by norm_num) (by linarith)
  have hs₀1 : s₀ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hs₀t : s₀ < t₀ := (min_le_right _ _).trans_lt (by linarith)
  have hBT : B + (τ + s₀ • (F - α)) = (B + (0 : ℝ) • C + τ - s₀ • α) + s₀ • F := by module
  have hBT' : B + (τ + s₀ • (F - α)) =
      (B₁ + (0 : ℝ) • C + τ - s₀ • α) + QDivisor.toRDivisor S + s₀ • F := by
    rw [hB₁def]; module
  obtain ⟨hm0, -⟩ := hmain 0 s₀ le_rfl zero_le_one hs₀0.le hs₀1
  have hm1 := hmain0 0 s₀ le_rfl zero_le_one hs₀0.le hs₀1
  -- the basis and the margin
  obtain ⟨cmin, hcmin, hcminle⟩ : ∃ cmin : ℝ, 0 < cmin ∧ ∀ κ, cmin ≤ cF κ :=
    ⟨Finset.univ.inf' ⟨(none, true), Finset.mem_univ _⟩ cF,
      (Finset.lt_inf'_iff _).2 fun κ _ => hcF κ,
      fun κ => Finset.inf'_le cF (Finset.mem_univ κ)⟩
  refine ⟨ι, inferInstance, hf ∘ a, τ + s₀ • (F - α), fun i => hfc _, hspanH, hindH,
    isNumericallyTrivialOver_add hτ (isNumericallyTrivialOver_smul hFαt s₀), fun P => ?_,
    fun t ht0 ht1 => ?_, ⟨s₀ * cmin, mul_pos hs₀0 hcmin, fun i P hP => ?_⟩, fun P => ?_⟩
  · rw [hBT, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    exact add_nonneg (hm0 P) (mul_nonneg hs₀0.le (hF0 P))
  · refine isRealKltPair_of_le hXq (hkF s₀ hs₀0.le hs₀t) fun P => ?_
    rw [show B + (τ + s₀ • (F - α)) + t • C = (B + t • C + τ - s₀ • α) + s₀ • F by module]
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    nlinarith [hα0 P, hC P, mul_le_mul_of_nonneg_right ht1 (hC P), mul_nonneg hs₀0.le (hα0 P)]
  · -- the components of `H i` have coefficient at least `s₀ cmin` in `B + T`
    have hHP : (1 : ℝ) ≤ ((hf (a i)).coeff P : ℝ) := by
      have h0 := hh0 (e.symm (a i)).1 (e.symm (a i)).2 P
      have : (hf (a i)).coeff P ≠ 0 := hP
      have : 1 ≤ (hf (a i)).coeff P := by
        change 0 ≤ (hf (a i)).coeff P at h0
        omega
      exact_mod_cast this
    have hFP : cF (e.symm (a i)) ≤ F.coeff P := by
      rw [hFdef, MMP.Fourfold.coeff_sum_smul_toRDivisor]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => cF (e.symm j) *
        (((hf j).coeff P : ℤ) : ℝ)) (fun j _ => mul_nonneg (hcF _).le
          (by exact_mod_cast hh0 (e.symm j).1 (e.symm j).2 P)) (Finset.mem_univ (a i)))
      nlinarith [hcF (e.symm (a i))]
    rw [hBT, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have := hm0 P
    nlinarith [hcminle (e.symm (a i))]
  · rw [hBT', DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, QDivisor.coeff_toRDivisor, hScoeff]
    have := hm1 P
    have := mul_nonneg hs₀0.le (hF0 P)
    linarith

end ShiftConstruction

/-- Every program with scaling is finite. -/
private theorem n_ne_top_of_scalingProgram
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 3)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C)))
    (hA : ∃ A : QDivisor X, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig π ∧
      QDivisor.toRDivisor A ≤ B) :
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤ := by
  intro n Y sY _ _ _ _ πY KY BY CY lam W sW f g fp φ hm hs htop
  subst htop
  -- (F1) the thresholds are positive, at most one and nonincreasing: the threshold adjoint
  -- descends to the contraction base and stays nef on the next model
  have hstep_i := fun i : ℕ => hs i (ENat.coe_lt_top i)
  have hdesc : ∀ i, IsRelativelyNef ℂ (sY i) (πY i)
      (logCanonicalDivisor (KY i) (BY i + lam i • CY i)) := by
    intro i
    obtain ⟨hπi, hXi, hqi, hKi, hBi⟩ := hm i le_top
    obtain ⟨hπ1, hX1, hq1, hK1, -⟩ := hm (i + 1) le_top
    obtain ⟨⟨⟨-, hnefi⟩, -⟩, hWi, hfg, hfpg, hneg, htriv, hcase, hBY, hCY⟩ := hstep_i i
    haveI : IsIntegral (W i) := hneg.isNormalVariety_target.1.toIsIntegral
    haveI : IsNormal (W i) := hneg.isNormalVariety_target.2
    have hsW : g i ≫ sZ = sW i := comp_eq_of_isIso_app hneg.isContraction.isIso_app
      hneg.isContraction.comp_eq (by rw [← Category.assoc, hfg, hπi])
    have hfps : fp i ≫ sW i = sY i := by
      rw [← hsW, ← Category.assoc, hfpg]
      exact hπ1
    have h : IsRelativelyNef ℂ (sY i) (πY i) (MMP.Mori.RationalMap.transformDivisor (φ i)
        (logCanonicalDivisor (divisorSeq K KY i)
          (divisorSeq B BY i + lam i • divisorSeq C CY i))) :=
      isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver hXi hqi hq1 hX1 hWi hneg hfg
        hcase hnefi htriv hfpg hfps
    have hlin : MMP.Mori.RationalMap.transformDivisor (φ i)
        (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + lam i • divisorSeq C CY i)) =
        logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq K KY i))
          (BY i + lam i • CY i) := by
      rw [logCanonicalDivisor, logCanonicalDivisor, map_add, map_add, hBY, hCY]
      congr 1
      · simp only [Divisor.toRDivisor, MMP.Mori.RationalMap.transformDivisor,
          mapPrimeDivisors_mapCoeffsAddMonoidHom]
      · congr 1
        exact DivisorWithCoeffs.mapPrimeDivisors_smul _ _ _
    rw [hlin] at h
    obtain ⟨m, hKt⟩ := isCanonicalDivisor_transformDivisor_of_step hKi hWi hX1.1 hfps hcase hneg
    obtain ⟨m', hKY⟩ := hK1
    have hle := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sY i)
      ⟨hX1.1, inferInstance⟩ hKY hKt
    exact isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent hle h
  have hlam : ∀ i, 0 < lam i ∧ lam i ≤ 1 ∧ lam (i + 1) ≤ lam i := by
    have hmono : ∀ i, lam (i + 1) ≤ lam i := fun i =>
      (hstep_i (i + 1)).1.2 ⟨(hstep_i i).1.1.1, hdesc i⟩
    have hle1 : ∀ i, lam i ≤ 1 := by
      intro i
      induction i with
      | zero => exact (hstep_i 0).1.2 ⟨zero_le_one, by rw [one_smul]; exact hnef⟩
      | succ i ih => exact (hmono i).trans ih
    refine fun i => ⟨?_, hle1 i, hmono i⟩
    -- a `(K + B)`-negative contraction contracts a curve on which `K + B` is negative
    rcases (hstep_i i).1.1.1.lt_or_eq with h | h
    · exact h
    exfalso
    obtain ⟨⟨⟨-, hnef0⟩, -⟩, -, hfg, -, hneg, -⟩ := hstep_i i
    obtain ⟨Γ, hΓ⟩ :=
      exists_isContractedBy_of_relativePicardNumber_eq_one hneg.relativePicardNumber_eq_one
    have hΓπ : Γ.IsContractedBy (modelMap π πY i) := hfg ▸ isContractedBy_comp (g i) hΓ
    rw [← h, zero_smul, add_zero] at hnef0
    obtain ⟨m, r, L, hL, hD, hnn⟩ := hnef0
    obtain ⟨x, hx⟩ := exists_isRIntersectionNumber Γ r L hL hD
    have hx0 := hnn Γ hΓπ x hx
    obtain ⟨m', r', L', hm', hr', hL', hD'⟩ := hneg.isRelativelyAntiAmple
    have hL'c : ∀ j, (L' j).IsCartier := fun j => (hL' j).1
    have hy := isRIntersectionNumber_sum_degreeOn ℂ (modelStr sX sY i) Γ r' L' hL'c
    rw [← hD'] at hy
    have hypos :
        0 < ∑ j, r' j * ((L' j).degreeOn ℂ (modelStr sX sY i) Γ.ι Γ.dim_le (hL'c j) : ℝ) := by
      haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
      refine Finset.sum_pos (fun j _ => mul_pos (hr' j) ?_) Finset.univ_nonempty
      exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier (f i) (hL' j) (hL'c j) Γ hΓ
    have hlin := (IsRIntersectionNumber.eq_and_linear ℂ (modelStr sX sY i) Γ).2 _ _ r L r' L' x _
      1 1 hx hy
    rw [one_smul, one_smul, add_neg_cancel] at hlin
    have := eq_zero_of_isRIntersectionNumber_zero Γ hlin
    linarith
  -- (F2) the composites `ψ_i : X ⤏ X_i`; each `X_i` is a nef weak model of `(X, B + λ_i C)`,
  -- every earlier step being negative or crepant for this adjoint
  have hφb : ∀ i, MMP.Mori.RationalMap.IsBirational (φ i) := fun i => by
    rcases (hstep_i i).2.2.2.2.2.2.1 with ⟨-, -, -, hmod⟩ | hflip
    · exact hmod.1
    · exact hflip.isModificationOf.1
  choose b hb using hφb
  let a : ∀ i, X.PartialIso (modelSeq X Y i) := fun i =>
    Nat.rec (motive := fun i => X.PartialIso (modelSeq X Y i)) (Scheme.PartialIso.refl X)
      (fun i ai => ai.trans (b i)) i
  let ψ : ∀ i, X.RationalMap (modelSeq X Y i) := fun i => (a i).toRationalMap
  have hψ0 : ψ 0 = Scheme.RationalMap.id X := by
    change (Scheme.PartialIso.refl X).toRationalMap = _
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    exact ⟨⊤, dense_univ, le_rfl, le_rfl, by
      simp [Scheme.PartialMap.restrict, Scheme.PartialMap.id]; rfl⟩
  have hψ : ∀ i, ∃ (a : X.PartialIso (modelSeq X Y i)) (b : (modelSeq X Y i).PartialIso (Y i)),
      a.toRationalMap = ψ i ∧ b.toRationalMap = φ i ∧ (a.trans b).toRationalMap = ψ (i + 1) :=
    fun i => ⟨a i, b i, rfl, hb i, rfl⟩
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  -- the composites lie over `Z`
  have haover : ∀ i, (a i).IsOver π (modelMap π πY i) := by
    intro i
    induction i with
    | zero =>
      change (Scheme.PartialIso.refl X).IsOver π π
      simp [Scheme.PartialIso.IsOver, Scheme.PartialIso.refl]
    | succ i ih =>
      refine ih.trans (isOver_of_compHom_eq (b i) _ (πY i) ?_)
      obtain ⟨-, -, hfg, hfpg, -, -, hcase, -, -⟩ := hstep_i i
      have hov : (φ i).compHom (fp i) = (f i).toRationalMap := by
        rcases hcase with ⟨-, -, -, hmod⟩ | hflip
        · exact hmod.2
        · exact hflip.isModificationOf.2
      rw [hb i, ← hfpg, ← compHom_compHom, hov, toRationalMap_compHom, hfg]
  -- (F2a) the steps, their contractions and the composites `ψ_i`
  have hstepfacts : ∀ i, IsNormalVariety ℂ (sW i) ∧ MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧
      IsProper (f i) ∧ IsBirationalMorphism (f i) ∧ f i ≫ sW i = modelStr sX sY i ∧
      IsProper (fp i) ∧ IsBirationalMorphism (fp i) ∧ fp i ≫ sW i = sY i := by
    intro i
    obtain ⟨hπi, -, -, -, -⟩ := hm i le_top
    obtain ⟨hπ1, -, -, -, -⟩ := hm (i + 1) le_top
    obtain ⟨-, hWi, hfg, hfpg, hneg, -, hcase, -, -⟩ := hstep_i i
    haveI : IsIntegral (W i) := hneg.isNormalVariety_target.1.toIsIntegral
    haveI : IsNormal (W i) := hneg.isNormalVariety_target.2
    have hsW : g i ≫ sZ = sW i := comp_eq_of_isIso_app hneg.isContraction.isIso_app
      hneg.isContraction.comp_eq (by rw [← Category.assoc, hfg, hπi])
    have hfps : fp i ≫ sW i = sY i := by
      rw [← hsW, ← Category.assoc, hfpg]
      exact hπ1
    refine ⟨hneg.isNormalVariety_target, hWi, hneg.isContraction.isProper, ?_,
      hneg.isContraction.comp_eq, ?_, ?_, hfps⟩
    · rcases hcase with ⟨hfb, -, -, -⟩ | hflip
      · exact hfb
      · exact (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall_source.toIsBirationalContraction).2
    · rcases hcase with ⟨-, -, hiso, -⟩ | hflip
      · infer_instance
      · exact hflip.isProper
    · rcases hcase with ⟨-, -, hiso, -⟩ | hflip
      · exact isBirationalMorphism_of_isIso _
      · exact (IsBirationalContraction.surjective_and_isBirational
          hflip.isSmall.toIsBirationalContraction).2
  haveI iWI : ∀ i, IsIntegral (W i) := fun i => (hstepfacts i).1.1.toIsIntegral
  haveI iWN : ∀ i, IsNormal (W i) := fun i => (hstepfacts i).1.2
  haveI iWL : ∀ i, IsLocallyNoetherian (W i) := fun i =>
    haveI : LocallyOfFiniteType (sW i) := (hstepfacts i).1.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (sW i)
  haveI iWS : ∀ i, IsSeparated (W i ↘ ⊤_ Scheme) := fun i => by
    haveI : IsSeparated (sW i) := (hstepfacts i).2.1.1.toIsSeparated
    rw [show (W i ↘ ⊤_ Scheme) = sW i ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  haveI iMS : ∀ i, IsSeparated (modelSeq X Y i ↘ ⊤_ Scheme) := fun i => by
    haveI : IsSeparated (modelStr sX sY i) := (hm i le_top).2.1.1.toIsSeparated
    rw [show (modelSeq X Y i ↘ ⊤_ Scheme) = modelStr sX sY i ≫
      Limits.terminal.from (Spec (.of ℂ)) from Subsingleton.elim _ _]
    infer_instance
  haveI iFP : ∀ i, IsProper (fp i) := fun i => (hstepfacts i).2.2.2.2.2.1
  haveI iFP' : ∀ i, IsProper (f i) := fun i => (hstepfacts i).2.2.1
  haveI iFD : ∀ i, IsDominant (f i) := fun i => (hstepfacts i).2.2.2.1.isDominant
  have hbover : ∀ i, (b i).IsOver (f i) (fp i) := fun i => by
    refine isOver_of_compHom_eq (b i) (f i) (fp i) ?_
    obtain ⟨-, -, -, -, -, -, hcase, -, -⟩ := hstep_i i
    rw [hb i]
    rcases hcase with ⟨-, -, -, hmod⟩ | hflip
    · exact hmod.2
    · exact hflip.isModificationOf.2
  have ha0 : (a 0).toRationalMap = Scheme.Hom.toRationalMap (𝟙 X) := by
    change (Scheme.PartialIso.refl X).toRationalMap = _
    rw [Scheme.PartialIso.toRationalMap, Scheme.Hom.toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    exact ⟨⊤, dense_univ, le_rfl, le_rfl, by
      simp [Scheme.PartialMap.restrict, Scheme.Hom.toPartialMap, Scheme.PartialIso.refl]
      exact Scheme.homOfLE_ι _ _⟩
  have hXn : IsNormalVariety ℂ sX := hklt.1
  haveI iXS : IsSeparated (X ↘ ⊤_ Scheme) := iMS 0
  -- a tower over the first `j` steps, for every `j`
  have htower := fun j => exists_tower (sY := sY) hX (fun i => (hm (i + 1) le_top).2.1.1)
    hstepfacts j
  choose TV TI TL TN Ts Tq hTn hTsm hTp hTq hTc using htower
  have hTinv : ∀ j, ∃ h : X.RationalMap (TV j),
      MMP.Mori.RationalMap.IsInverse (Tq j 0 (Nat.zero_le j)).toRationalMap h := fun j =>
    MMP.Mori.RationalMap.IsBirational.exists_isInverse (hTq j 0 (Nat.zero_le j)).2.2
  choose Th hTh using hTinv
  have hT1 : ∀ j m (hmj : m ≤ j), (Th j).compHom (Tq j m hmj) = ψ m := by
    intro j
    haveI := TI j
    exact compHom_eq_of_tower (fun i => (hstepfacts i).2.2.2.2.2.2.1) a b ha0 (fun i => rfl)
      hbover (Tq j) (hTc j) (compHom_eq_of_isInverse (hTh j))
  -- (F2b) strict transforms on the towers and the composition of transforms
  have hTsep : ∀ j m (hmj : m ≤ j), IsSeparated (Tq j m hmj) ∧ IsProper (Tq j m hmj) := by
    intro j m hmj
    obtain ⟨hs, hp, -⟩ := hTq j m hmj
    haveI : IsSeparated (Ts j) := (hTn j).1.toIsSeparated
    haveI : IsSeparated (Tq j m hmj ≫ modelStr sX sY m) := by rw [hs]; infer_instance
    exact ⟨IsSeparated.of_comp _ (modelStr sX sY m), isProper_of_isProjectiveMorphism _ hp⟩
  have hTstrict : ∀ j (P : MMP.Mori.PrimeDivisor X), ∃ E : MMP.Mori.PrimeDivisor (TV j),
      Tq j 0 (Nat.zero_le j) E.genericPoint = P.genericPoint := by
    intro j P
    haveI := TI j
    haveI := TL j
    haveI := TN j
    obtain ⟨hs0, hp0, hb0⟩ := hTq j 0 (Nat.zero_le j)
    obtain ⟨q0, hq0⟩ : ∃ q0 : TV j ⟶ X, q0 = Tq j 0 (Nat.zero_le j) := ⟨_, rfl⟩
    haveI : IsProper q0 := by rw [hq0]; exact (hTsep j 0 (Nat.zero_le j)).2
    have hV0 : IsNormalVariety ℂ (q0 ≫ sX) := by
      have := hTn j
      rw [← hs0] at this
      rw [hq0]
      exact this
    obtain ⟨E, hE, -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn
        (f := q0) hV0 (by rw [hq0]; exact hb0) P
    subst hq0
    exact ⟨E, hE⟩
  have hT2 : ∀ j m (hmj : m ≤ j) (P : MMP.Mori.PrimeDivisor X)
      (E : MMP.Mori.PrimeDivisor (TV j)), Tq j 0 (Nat.zero_le j) E.genericPoint = P.genericPoint →
      ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y m),
        MMP.Mori.RationalMap.transformPrimeDivisor (ψ m) P = some F ↔
          Tq j m hmj E.genericPoint = F.genericPoint := by
    intro j m hmj P E hE F
    haveI := TI j
    haveI := (hTsep j 0 (Nat.zero_le j)).1
    haveI := (hTsep j 0 (Nat.zero_le j)).2
    exact MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse (Tq j 0 (Nat.zero_le j))
      (hTq j 0 (Nat.zero_le j)).2.2 (hTh j) (Tq j m hmj) (hT1 j m hmj) P E hE F
  have hφover : ∀ i, (φ i).compHom (fp i) = (f i).toRationalMap := fun i => by
    obtain ⟨-, -, -, -, -, -, hcase, -, -⟩ := hstep_i i
    rcases hcase with ⟨-, -, -, hmod⟩ | hflip
    · exact hmod.2
    · exact hflip.isModificationOf.2
  have hφE : ∀ i (F : MMP.Mori.PrimeDivisor (Y i)),
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ i) F := fun i F => by
    obtain ⟨-, hWi, -, -, hneg, -, hcase, -, -⟩ := hstep_i i
    exact not_isInverseExceptional_of_step hWi (hm (i + 1) le_top).2.1.1
      (hstepfacts i).2.2.2.2.2.2.2 hcase hneg F
  have hTcomp : ∀ i (P : MMP.Mori.PrimeDivisor X),
      MMP.Mori.RationalMap.transformPrimeDivisor (ψ (i + 1)) P =
        (MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) P).bind
          (MMP.Mori.RationalMap.transformPrimeDivisor (φ i)) := by
    intro i P
    haveI := TI (i + 1)
    obtain ⟨E, hE⟩ := hTstrict (i + 1) P
    haveI := (hTsep (i + 1) i (Nat.le_succ i)).1
    haveI := (hTsep (i + 1) i (Nat.le_succ i)).2
    haveI := (hTsep (i + 1) (i + 1) le_rfl).1
    have hpb := (hTq (i + 1) i (Nat.le_succ i)).2.2
    have hqb := (hTq (i + 1) (i + 1) le_rfl).2.2
    obtain ⟨h', hinv'⟩ : ∃ h' : (modelSeq X Y i).RationalMap (TV (i + 1)),
        MMP.Mori.RationalMap.IsInverse (Tq (i + 1) i (Nat.le_succ i)).toRationalMap h' :=
      MMP.Mori.RationalMap.IsBirational.exists_isInverse hpb
    have hh' : h'.compHom (Tq (i + 1) (i + 1) le_rfl) = φ i :=
      compHom_eq_of_isInverse_of_comp_eq (B := Y i) (hstepfacts i).2.2.2.2.2.2.1 (hφover i)
        (Tq (i + 1) i (Nat.le_succ i)) (Tq (i + 1) (i + 1) le_rfl)
        (hTc (i + 1) i (Nat.lt_succ_self i)) hinv'
    have hT2' : ∀ (F' : MMP.Mori.PrimeDivisor (modelSeq X Y i))
        (E' : MMP.Mori.PrimeDivisor (TV (i + 1))),
        Tq (i + 1) i (Nat.le_succ i) E'.genericPoint = F'.genericPoint →
        ∀ F : MMP.Mori.PrimeDivisor (Y i),
          MMP.Mori.RationalMap.transformPrimeDivisor (φ i) F' = some F ↔
            Tq (i + 1) (i + 1) le_rfl E'.genericPoint = F.genericPoint :=
      fun F' E' hE' F => MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse
        (Tq (i + 1) i (Nat.le_succ i)) hpb hinv' (Tq (i + 1) (i + 1) le_rfl) hh' F' E' hE' F
    cases hψi : MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) P with
    | some F' =>
      have h1 : Tq (i + 1) i (Nat.le_succ i) E.genericPoint = F'.genericPoint :=
        (hT2 (i + 1) i (Nat.le_succ i) P E hE F').mp hψi
      rw [Option.bind_some]
      cases hφF : MMP.Mori.RationalMap.transformPrimeDivisor (φ i) F' with
      | some F =>
        exact (hT2 (i + 1) (i + 1) le_rfl P E hE F).mpr ((hT2' F' E h1 F).mp hφF)
      | none =>
        cases hψ1 : MMP.Mori.RationalMap.transformPrimeDivisor (ψ (i + 1)) P with
        | none => rfl
        | some F =>
          have := (hT2' F' E h1 F).mpr ((hT2 (i + 1) (i + 1) le_rfl P E hE F).mp hψ1)
          rw [hφF] at this
          exact absurd this (by simp)
    | none =>
      rw [Option.bind_none]
      cases hψ1 : MMP.Mori.RationalMap.transformPrimeDivisor (ψ (i + 1)) P with
      | none => rfl
      | some F =>
        exfalso
        have h2 := (hT2 (i + 1) (i + 1) le_rfl P E hE F).mp hψ1
        obtain ⟨F'', hF''⟩ := not_forall.mp (hφE i F)
        rw [not_not] at hF''
        haveI := TL (i + 1)
        haveI := TN (i + 1)
        haveI : IsDominant (Tq (i + 1) (i + 1) le_rfl) := hqb.isDominant
        have hVi : IsNormalVariety ℂ (Tq (i + 1) i (Nat.le_succ i) ≫ modelStr sX sY i) := by
          rw [(hTq (i + 1) i (Nat.le_succ i)).1]; exact hTn (i + 1)
        obtain ⟨E'', hE'', -, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
            ⟨(hm i le_top).2.1.1, inferInstance⟩ hVi hpb F''
        have h3 := (hT2' F'' E'' hE'' F).mp hF''
        have hEE : E''.genericPoint = E.genericPoint :=
          (MMP.Fourfold.Crepant.eq_of_apply_eq_of_coheight_le_one (Tq (i + 1) (i + 1) le_rfl)
            hqb.functionFieldMap_bijective (h3.trans h2.symm)
            (by rw [h2]; exact F.coheight_genericPoint.le)).symm
        rw [hEE] at hE''
        have := (hT2 (i + 1) i (Nat.le_succ i) P E hE F'').mpr hE''
        rw [hψi] at this
        exact absurd this (by simp)
  have hTcompD : ∀ i {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      MMP.Mori.RationalMap.transformDivisor (ψ (i + 1)) D =
        MMP.Mori.RationalMap.transformDivisor (φ i)
          (MMP.Mori.RationalMap.transformDivisor (ψ i) D) := by
    intro i R _ D
    change DivisorWithCoeffs.mapPrimeDivisors _ D =
      DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ D)
    exact (congrArg (fun φ' => DivisorWithCoeffs.mapPrimeDivisors φ' D)
      (funext (hTcomp i))).trans (mapPrimeDivisors_bind _ _ D)
  have hψ0' : ψ 0 = Scheme.Hom.toRationalMap (𝟙 X) := ha0
  have hTr0 : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      MMP.Mori.RationalMap.transformDivisor (ψ 0) D = D := fun D => by
    rw [hψ0']; exact transformDivisor_id_toRationalMap hXn D
  -- the composites extract no divisor
  have hψE : ∀ i (F : MMP.Mori.PrimeDivisor (modelSeq X Y i)),
      ¬ MMP.Flips.RationalMap.IsInverseExceptional (ψ i) F := by
    intro i
    induction i with
    | zero =>
      intro F hF
      exact hF F (by
        rw [hψ0']
        exact (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) F F).mpr rfl)
    | succ i ih =>
      intro F hF
      obtain ⟨F', hF'⟩ := not_forall.mp (hφE i F)
      rw [not_not] at hF'
      obtain ⟨P, hP⟩ := not_forall.mp (ih F')
      rw [not_not] at hP
      exact hF P (by rw [hTcomp i P, hP, Option.bind_some]; exact hF')
  -- the transformed boundaries are those of the program
  have hBtr : ∀ i, MMP.Mori.RationalMap.transformDivisor (ψ i) B = divisorSeq B BY i := by
    intro i
    induction i with
    | zero => exact hTr0 B
    | succ i ih => rw [hTcompD i B, ih, ← (hstep_i i).2.2.2.2.2.2.2.1]; rfl
  have hCtr : ∀ i, MMP.Mori.RationalMap.transformDivisor (ψ i) C = divisorSeq C CY i := by
    intro i
    induction i with
    | zero => exact hTr0 C
    | succ i ih => rw [hTcompD i C, ih, ← (hstep_i i).2.2.2.2.2.2.2.2]; rfl
  -- the transformed canonical divisors are canonical
  have hKtr : ∀ i, ∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m
      (MMP.Mori.RationalMap.transformDivisor (ψ i) K) := by
    intro i
    induction i with
    | zero => exact ⟨3, by rw [hTr0 K]; exact hK⟩
    | succ i ih =>
      obtain ⟨-, hWi, -, -, hneg, -, hcase, -, -⟩ := hstep_i i
      rw [hTcompD i K]
      exact isCanonicalDivisor_transformDivisor_of_step ih hWi (hm (i + 1) le_top).2.1.1
        (hstepfacts i).2.2.2.2.2.2.2 hcase hneg
  -- (F2c) the level adjoints of `X` transported to the models, and their pull-backs to towers
  let Lv : ℝ → ∀ m, RDivisor (modelSeq X Y m) := fun μ m =>
    logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ m) K)
      (MMP.Mori.RationalMap.transformDivisor (ψ m) (B + μ • C))
  have hLv0 : ∀ μ, Lv μ 0 = logCanonicalDivisor K (B + μ • C) := fun μ => by
    simp only [Lv, hTr0]
    rfl
  have hLvform : ∀ μ m, Lv μ m = logCanonicalDivisor
      (MMP.Mori.RationalMap.transformDivisor (ψ m) K)
      (divisorSeq B BY m + μ • divisorSeq C CY m) := fun μ m => by
    simp only [Lv, map_add, hBtr, ← hCtr]
    congr 2
    exact DivisorWithCoeffs.mapPrimeDivisors_smul _ _ _
  have hLvψ : ∀ μ m, Lv μ m = MMP.Mori.RationalMap.transformDivisor (ψ m)
      (logCanonicalDivisor K (B + μ • C)) := fun μ m =>
    (transformDivisor_logCanonicalDivisor (ψ m) K (B + μ • C)).symm
  have hLvφ : ∀ μ m, MMP.Mori.RationalMap.transformDivisor (φ m) (Lv μ m) = Lv μ (m + 1) :=
    fun μ m => by
      simp only [Lv, transformDivisor_logCanonicalDivisor, ← hTcompD]
      rfl
  have hKK : ∀ m, Divisor.LinearlyEquivalent (MMP.Mori.RationalMap.transformDivisor (ψ m) K)
      (divisorSeq K KY m) := fun m => by
    obtain ⟨n₁, h₁⟩ := hKtr m
    obtain ⟨n₂, h₂⟩ := (hm m le_top).2.2.2.1
    exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (modelStr sX sY m)
      ⟨(hm m le_top).2.1.1, inferInstance⟩ h₁ h₂
  have hLvneg : ∀ μ m, μ ≤ lam m → IsRelativelyNef ℂ (modelStr sX sY m) (f m) (-Lv μ m) :=
    fun μ m hμ => by
      obtain ⟨-, -, -, -, hneg, htriv, -, -, -⟩ := hstep_i m
      rw [hLvform]
      exact isRelativelyNef_neg_logCanonicalDivisor (hm m le_top).2.2.1 (hKK m) hμ htriv
        fun Γ hΓ _ _ _ _ hx => (pos_of_isNegativeExtremalContraction (hlam m).1 hneg htriv Γ hΓ
          hx).le
  have hLvc : ∀ μ m, IsCartierCombination (Lv μ m) := fun μ m =>
    isCartierCombination_of_isQFactorial (hm m le_top).2.2.1 _
  have hGex : ∀ (μ : ℝ) j m (hmj : m ≤ j), ∃ G : RDivisor (TV j),
      MMP.Flips.IsRCartierPullback (Tq j m hmj) (Lv μ m) G := fun μ j m hmj => by
    haveI := TI j
    haveI : QuasiCompact (Ts j) := (hTn j).1.toQuasiCompact
    haveI : CompactSpace (TV j) := QuasiCompact.compactSpace_of_compactSpace (Ts j)
    haveI : IsDominant (Tq j m hmj) := (hTq j m hmj).2.2.isDominant
    exact (MMP.Flips.existsUnique_isRCartierPullback (Tq j m hmj) (hLvc μ m)).exists
  choose G hG using hGex
  have hGstep : ∀ (μ : ℝ) j m (hmj : m < j), μ ≤ lam m → 0 ≤ G μ j m hmj.le - G μ j (m + 1) hmj :=
    fun μ j m hmj hμ => by
      haveI := TI j
      haveI := TL j
      haveI := TN j
      haveI : QuasiCompact (Ts j) := (hTn j).1.toQuasiCompact
      haveI : CompactSpace (TV j) := QuasiCompact.compactSpace_of_compactSpace (Ts j)
      obtain ⟨-, hWm, -, -, hneg, -, hcase, -, -⟩ := hstep_i m
      have hGB := hG μ j (m + 1) hmj
      rw [← hLvφ] at hGB
      exact nonneg_sub_of_isRCartierPullback_of_step (hm m le_top).2.1 (hm (m + 1) le_top).2.1
        (hm (m + 1) le_top).2.2.1 hWm (hTn j) (hTp j) hneg hcase (hstepfacts m).2.2.2.2.2.2.2
        (Tq j m hmj.le) (Tq j (m + 1) hmj) (hTq j m hmj.le).2.1 (hTq j m hmj.le).2.2
        (hTq j (m + 1) hmj).2.1 (hTq j (m + 1) hmj).2.2 (hTc j m hmj) (hTq j m hmj.le).1
        (hTq j (m + 1) hmj).1 (hLvneg μ m hμ) (hG μ j m hmj.le) hGB
  have hGsum : ∀ (μ : ℝ) j, (∀ m < j, μ ≤ lam m) → ∀ k (hk : k ≤ j),
      0 ≤ G μ j 0 (Nat.zero_le j) - G μ j k hk := by
    intro μ j hμ k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 := hGstep μ j k hk (hμ k hk)
      have : G μ j 0 (Nat.zero_le j) - G μ j (k + 1) hk =
          (G μ j 0 (Nat.zero_le j) - G μ j k (Nat.le_of_succ_le hk)) +
            (G μ j k (Nat.le_of_succ_le hk) - G μ j (k + 1) hk) := by abel
      rw [this]
      exact add_nonneg h1 h2
  have hlam_anti : ∀ m i, m ≤ i → lam i ≤ lam m := by
    intro m i hmi
    induction hmi with
    | refl => exact le_rfl
    | step _ ih => exact ((hlam _).2.2).trans ih
  have hweak : ∀ i, IsNefWeakModel sX (modelStr sX sY i) sZ π (modelMap π πY i) K
      (B + lam i • C) (ψ i) := by
    intro i
    obtain ⟨hπi, hXi, -, -, -⟩ := hm i le_top
    obtain ⟨h11, h12, h13⟩ :
        (∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y i),
          ¬ MMP.Flips.RationalMap.IsInverseExceptional (ψ i) F) ∧
        IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ i) K)
            (MMP.Mori.RationalMap.transformDivisor (ψ i) (B + lam i • C))) ∧
        ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V)
          (_ : IsNormal V) (sV : V ⟶ Spec (.of ℂ)) (p : V ⟶ X) (q : V ⟶ modelSeq X Y i)
          (h : X.RationalMap V),
          MMP.Mori.IsVariety ℂ sV ∧ MMP.Mori.IsSmoothScheme sV ∧ p ≫ sX = sV ∧
            q ≫ modelStr sX sY i = sV ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
            IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
            MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = ψ i ∧
            ∃ GY GZ : RDivisor V,
              MMP.Flips.IsRCartierPullback p (logCanonicalDivisor K (B + lam i • C)) GY ∧
              MMP.Flips.IsRCartierPullback q
                (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor (ψ i) K)
                  (MMP.Mori.RationalMap.transformDivisor (ψ i) (B + lam i • C))) GZ ∧
              (∀ P, 0 ≤ (GY - GZ).coeff P) ∧
              ∀ P, (GY - GZ).coeff P ≠ 0 →
                MMP.Flips.IsExceptionalPrimeDivisor (modelStr sX sY i) q P := by
      refine ⟨hψE i, ?_, ?_⟩
      · -- the transformed adjoint is the program's level adjoint up to linear equivalence
        have h := isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent (hKK i)
          (hstep_i i).1.1.2
        rw [← hLvform] at h
        exact h
      · haveI := TI i
        haveI := TL i
        haveI := TN i
        haveI := (hTsep i 0 (Nat.zero_le i)).2
        haveI := (hTsep i i le_rfl).2
        have hGY := hG (lam i) i 0 (Nat.zero_le i)
        rw [hLv0] at hGY
        refine ⟨TV i, inferInstance, inferInstance, inferInstance, Ts i, Tq i 0 (Nat.zero_le i),
          Tq i i le_rfl, Th i, (hTn i).1, hTsm i, (hTq i 0 (Nat.zero_le i)).1,
          (hTq i i le_rfl).1, (hTq i 0 (Nat.zero_le i)).2.1, (hTq i i le_rfl).2.1,
          (hTq i 0 (Nat.zero_le i)).2.2, (hTq i i le_rfl).2.2, hTh i, hT1 i i le_rfl,
          G (lam i) i 0 (Nat.zero_le i), G (lam i) i i le_rfl, hGY, hG (lam i) i i le_rfl,
          fun P => hGsum (lam i) i (fun m hm => hlam_anti m i hm.le) i le_rfl P, ?_⟩
        intro P hP
        by_contra hPe
        have hVq : IsNormalVariety ℂ (Tq i i le_rfl ≫ modelStr sX sY i) := by
          rw [(hTq i i le_rfl).1]; exact hTn i
        obtain ⟨F, hF, hFiso, -⟩ :=
          MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
            ⟨hXi.1, inferInstance⟩ (Tq i i le_rfl) hVq (hTq i i le_rfl).2.2 P hPe
        obtain ⟨P₀, hP₀⟩ := not_forall.mp (hψE i F)
        rw [not_not] at hP₀
        obtain ⟨E, hE⟩ := hTstrict i P₀
        have h1 := (hT2 i i le_rfl P₀ E hE F).mp hP₀
        have hqb := (hTq i i le_rfl).2.2
        haveI := (hTsep i i le_rfl).1
        haveI : IsDominant (Tq i i le_rfl) := hqb.isDominant
        have hEP : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (MMP.Fourfold.Crepant.eq_of_apply_eq_of_coheight_le_one (Tq i i le_rfl)
            hqb.functionFieldMap_bijective (hF.trans h1.symm)
            (by rw [h1]; exact F.coheight_genericPoint.le))
        subst hEP
        -- the two coefficients at `E` agree
        obtain ⟨q0, hq0⟩ : ∃ q0 : TV i ⟶ X, q0 = Tq i 0 (Nat.zero_le i) := ⟨_, rfl⟩
        have hE' : q0 E.genericPoint = P₀.genericPoint := by subst hq0; exact hE
        have hGY' : MMP.Flips.IsRCartierPullback q0 (logCanonicalDivisor K (B + lam i • C))
            (G (lam i) i 0 (Nat.zero_le i)) := by subst hq0; exact hGY
        haveI : IsIso (q0.stalkMap E.genericPoint) :=
          MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint
            (by subst hq0; exact (hTq i 0 (Nat.zero_le i)).2.2) hE'
        have e1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E P₀ hE' hGY'
        have e2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback E F hF (hG (lam i) i i le_rfl)
        have huniq : ∀ P₁ : MMP.Mori.PrimeDivisor X,
            MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) P₁ = some F → P₁ = P₀ := by
          intro P₁ hP₁
          obtain ⟨E₁, hE₁⟩ := hTstrict i P₁
          have h2 := (hT2 i i le_rfl P₁ E₁ hE₁ F).mp hP₁
          have hEE := MMP.Fourfold.Crepant.eq_of_apply_eq_of_coheight_le_one (Tq i i le_rfl)
            hqb.functionFieldMap_bijective (h2.trans h1.symm)
            (by rw [h1]; exact F.coheight_genericPoint.le)
          exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
            (hE₁.symm.trans ((congrArg (Tq i 0 (Nat.zero_le i)) hEE.symm).trans hE))
        have e3 : (Lv (lam i) i).coeff F = (logCanonicalDivisor K (B + lam i • C)).coeff P₀ := by
          rw [hLvψ]
          exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP₀ huniq _
        apply hP
        rw [DivisorWithCoeffs.coeff_sub, e1, e2, e3, sub_self]
    exact
      { isNormalVariety_source := hklt.1
        isProjectiveVariety_source := hX
        comp_eq_source := hπ
        isCanonicalDivisor := ⟨3, hK⟩
        isCartierCombination := isCartierCombination_of_isQFactorial hXq _
        isNormalVariety_target := ⟨hXi.1, inferInstance⟩
        isProjectiveVariety_target := hXi
        comp_eq_target := hπi
        isBirational := ⟨a i, rfl⟩
        isOver := isOver_toRationalMap (haover i)
        not_isInverseExceptional := h11
        isRelativelyNef := h12
        exists_resolution := h13 }
  -- (F3) after an ample perturbation inside a fixed rational klt polytope, each `X_i` is the
  -- ample model of its pair, hence one of the finitely many models of the geography
  obtain ⟨N, c, hc⟩ : ∃ (N : ℕ) (c : ℕ → Fin N), ∀ i j, c i = c j →
      ∃ e : modelSeq X Y i ≅ modelSeq X Y j, (ψ i).compHom e.hom = ψ j := by
    -- finitely many log minimal models, among which a model of each perturbed pair of `X_i`
    have hfinite : ∃ (N : ℕ) (Y' : Fin N → Scheme.{0}) (_ : ∀ k, IsIntegral (Y' k))
        (_ : ∀ k, CompactSpace (Y' k)) (_ : ∀ k, IsLocallyNoetherian (Y' k))
        (_ : ∀ k, IsNormal (Y' k)) (sY' : ∀ k, Y' k ⟶ Spec (.of ℂ)) (πY' : ∀ k, Y' k ⟶ Z)
        (φ' : ∀ k, X.RationalMap (Y' k)),
        (∀ k (F : MMP.Mori.PrimeDivisor (Y' k)),
          ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ' k) F) ∧
        ∀ i, ∃ (k : Fin N) (D : RDivisor X) (K₁ : Divisor (Y' k)) (D₁ : RDivisor (Y' k))
          (K₂ : Divisor (modelSeq X Y i)) (D₂ : RDivisor (modelSeq X Y i)),
          IsRealLogMinimalModel sX (sY' k) sZ π (πY' k) K D K₁ D₁ (φ' k) ∧
          IsRealLogMinimalModel sX (modelStr sX sY i) sZ π (modelMap π πY i) K D K₂ D₂ (ψ i) ∧
          IsRelativelyAmple (modelMap π πY i) (logCanonicalDivisor K₂ D₂) := by
      classical
      haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
      haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
      haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
      have hπpm : IsProjectiveMorphism π :=
        IsProjectiveMorphism.of_comp π sZ (by rw [hπ]; exact hX.isProjective)
      have hπp : IsProjective π := hπpm.isProjective
      have hXqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX :=
        @AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _ _ sX hX
      -- the big core and the shift of the boundary
      obtain ⟨A, hA0, hAbig, hAB⟩ := hA
      have hAB' : ∀ P, (A.coeff P : ℝ) ≤ B.coeff P := fun P => by
        have := hAB P
        exact this
      obtain ⟨ι, _, H, T, hHc, hspan, hind, hT, hBT0, hTklt, ⟨δ, hδ, hHδ⟩, hAT⟩ :=
        exists_shift hX hZ π hπ hπp hXq hB hC hklt hA0 hAbig hAB'
      set G : QDivisor X := (4 : ℚ)⁻¹ • A with hGdef
      have hGcoeff : ∀ P, ((G.coeff P : ℚ) : ℝ) = (A.coeff P : ℝ) / 4 := fun P => by
        simp only [hGdef, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; push_cast; ring
      have hA0' : ∀ P, (0 : ℝ) ≤ A.coeff P := fun P => by exact_mod_cast hA0 P
      have hG0 : ∀ P, 0 ≤ G.coeff P := fun P => by
        have := hGcoeff P; have := hA0' P
        exact_mod_cast (show (0 : ℝ) ≤ (G.coeff P : ℝ) by linarith)
      have hGbig : G.IsRelativelyBig π := by
        have := isRelativelyBig_inv_smul hAbig 4 (by norm_num)
        simpa [hGdef] using this
      -- a rational klt polytope containing every perturbed boundary of the segment
      have hpoly : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ (V : Finset (QDivisor X)) (ε : ℝ), 0 < ε ∧
          (∀ E ∈ V, ∀ P, 0 ≤ E.coeff P) ∧ (∀ E ∈ V, MMP.Fourfold.IsKltPair sX E) ∧
          (∀ E ∈ V, ∀ P, G.coeff P ≤ E.coeff P) ∧ ∀ u : ι → ℝ, (∀ i, |u i| < ε) →
            B + T + t • C + ∑ i, u i • Divisor.toRDivisor (H i) ∈
              convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
        intro t ht0 ht1
        have hle : ∀ P, (B + T).coeff P ≤ (B + T + t • C).coeff P := fun P => by
          rw [DivisorWithCoeffs.coeff_add (B + T), DivisorWithCoeffs.coeff_smul, smul_eq_mul]
          nlinarith [mul_nonneg ht0 (hC P)]
        obtain ⟨V, ε, hε, hV0, hVk, -, hVG, hVm⟩ :=
          exists_finset_isKltPair_convexHull_of_shift sX hXqp hXq (Θ := B + T + t • C)
            (fun P => (hBT0 P).trans (hle P)) (hTklt t ht0 ht1) 0 (fun P => le_rfl)
            (fun P hP => absurd rfl hP) (by simpa using hTklt t ht0 ht1) G hG0
            (fun P => by rw [hGcoeff]; linarith [hAT P, hle P])
            (fun i => Divisor.toRDivisor (H i)) hδ (fun i P hP => (hHδ i P (by
              intro h0; apply hP; rw [Divisor.coeff_toRDivisor, h0, Int.cast_zero])).trans (hle P))
        exact ⟨V, ε, hε, hV0, fun E hE => MMP.Fourfold.isKltPair_of_isRealKltPair hXq (hV0 E hE)
          (hVk E hE), hVG, hVm⟩
      obtain ⟨V₀, ε₀, hε₀, hV₀0, hV₀k, hV₀G, hV₀m⟩ := hpoly 0 le_rfl zero_le_one
      obtain ⟨V₁, ε₁, hε₁, hV₁0, hV₁k, hV₁G, hV₁m⟩ := hpoly 1 zero_le_one le_rfl
      set V := V₀ ∪ V₁ with hVdef
      set εV := min ε₀ ε₁ with hεVdef
      have hεV : 0 < εV := lt_min hε₀ hε₁
      have hVhull : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ u : ι → ℝ, (∀ i, |u i| < εV) →
          B + T + t • C + ∑ i, u i • Divisor.toRDivisor (H i) ∈
            convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := by
        intro t ht0 ht1 u hu
        have hsub : ∀ W : Finset (QDivisor X), W ⊆ V →
            convexHull ℝ (QDivisor.toRDivisor '' (W : Set (QDivisor X))) ⊆
              convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))) := fun W hW =>
          convexHull_mono (Set.image_mono (by exact_mod_cast hW))
        have h₀ := hsub V₀ Finset.subset_union_left
          (hV₀m u fun i => (hu i).trans_le (min_le_left _ _))
        have h₁ := hsub V₁ Finset.subset_union_right
          (hV₁m u fun i => (hu i).trans_le (min_le_right _ _))
        have heq : B + T + t • C + ∑ i, u i • Divisor.toRDivisor (H i) =
            (1 - t) • (B + T + (0 : ℝ) • C + ∑ i, u i • Divisor.toRDivisor (H i)) +
              t • (B + T + (1 : ℝ) • C + ∑ i, u i • Divisor.toRDivisor (H i)) := by
          module
        rw [heq]
        exact (convex_convexHull ℝ _) h₀ h₁ (sub_nonneg.2 ht1) ht0 (by ring)
      -- the finite geography of the polytope
      obtain ⟨N, Y', iI', iC', iL', iN', sY', πY', KY', φ', hY', hcov⟩ :=
        MMP.Fourfold.exists_finite_isRealLogMinimalModel_of_mem_convexHull_of_isRelativelyBig
          (KX := K) V G hX hZ hπ hK.topologicalKrullDim_eq hXq ⟨3, hK⟩
          (fun D hD => (Finset.mem_union.mp hD).elim (hV₀0 D) (hV₁0 D))
          (fun D hD => (Finset.mem_union.mp hD).elim (hV₀k D) (hV₁k D)) hG0 hGbig
          (fun D hD => (Finset.mem_union.mp hD).elim (hV₀G D) (hV₁G D))
      refine ⟨N, Y', iI', iC', iL', iN', sY', πY', φ', fun k => (hY' k).2.2.2.2.2.2, fun i => ?_⟩
      -- the shift is numerically trivial on every model
      have hTtr : ∀ m, IsNumericallyTrivialOver ℂ (modelStr sX sY m) (modelMap π πY m)
          (MMP.Mori.RationalMap.transformDivisor (ψ m) T) := by
        intro m
        induction m with
        | zero => rw [hTr0]; exact hT
        | succ m ih =>
          obtain ⟨hπm, hXm, hqm, -, -⟩ := hm m le_top
          obtain ⟨hπ1, hX1, hq1, -, -⟩ := hm (m + 1) le_top
          obtain ⟨-, hWm, hfg, hfpg, hneg, -, hcase, -, -⟩ := hstep_i m
          have hfps := (hstepfacts m).2.2.2.2.2.2.2
          have htm : IsNumericallyTrivialOver ℂ (modelStr sX sY m) (f m)
              (MMP.Mori.RationalMap.transformDivisor (ψ m) T) :=
            isNumericallyTrivialOver_of_comp (by rw [hfg]; exact ih)
          have n1 := isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver hXm hqm hq1 hX1
            hWm hneg hfg hcase (isRelativelyNef_of_isNumericallyTrivialOver ih) htm hfpg hfps
          have n2 := isRelativelyNef_transformDivisor_of_isNumericallyTrivialOver hXm hqm hq1 hX1
            hWm hneg hfg hcase
            (isRelativelyNef_of_isNumericallyTrivialOver (isNumericallyTrivialOver_neg ih))
            (isNumericallyTrivialOver_neg htm) hfpg hfps
          rw [map_neg] at n2
          rw [hTcompD m T]
          exact isNumericallyTrivialOver_of_isRelativelyNef_neg n1 n2
      -- the model `X_i` is a nef weak model of `(X, B + T + λᵢ C)`
      have hNW : IsNefWeakModel sX (modelStr sX sY i) sZ π (modelMap π πY i) K
          (B + T + lam i • C) (ψ i) := by
        have := IsNefWeakModel.add_of_isNumericallyTrivialOver hZ hXq (hweak i) hT (hTtr i)
        rwa [show B + lam i • C + T = B + T + lam i • C by abel] at this
      obtain ⟨hl0, hl1, -⟩ := hlam i
      have hΘle : ∀ P, (B + T).coeff P ≤ (B + T + lam i • C).coeff P := fun P => by
        rw [DivisorWithCoeffs.coeff_add (B + T), DivisorWithCoeffs.coeff_smul, smul_eq_mul]
        nlinarith [mul_nonneg hl0.le (hC P)]
      obtain ⟨mi, hKi⟩ := (hm i le_top).2.2.2.1
      obtain ⟨ε₂, hε₂, hnb⟩ := exists_nbhd_of_isNefWeakModel hX hXq hZ (hm i le_top).2.1
        (hm i le_top).2.2.1 hKi (fun P => (hBT0 P).trans (hΘle P)) (hTklt (lam i) hl0.le hl1) H
        hδ (fun j P hP => (hHδ j P hP).trans (hΘle P)) hNW
      -- an ample perturbation inside the polytope
      have hBi : ∀ j, ∀ P, 0 ≤ (divisorSeq B BY j).coeff P := fun j P => by
        rw [← hBtr j]
        exact mapPrimeDivisors_nonneg _ hB P
      obtain ⟨u, hu, hLMM, hamp⟩ :=
        MMP.Fourfold.exists_isRealLogMinimalModel_isRelativelyAmple_of_isNefWeakModel sX sZ hZ π
          hπ hπpm hX hXq K ⟨3, hK⟩ H hHc hspan hind i Y sY πY W sW f g fp φ ψ
          (fun j _ => ⟨(hm j le_top).1, (hm j le_top).2.1⟩)
          (fun j _ => ⟨(hstep_i j).2.1, (hstep_i j).2.2.1, (hstep_i j).2.2.2.1,
            divisorSeq K KY j, divisorSeq B BY j, (hm j le_top).2.2.2.1, hBi j,
            (hm j le_top).2.2.2.2, (hstep_i j).2.2.2.2.1, (hstep_i j).2.2.2.2.2.2.1⟩)
          hψ0 (fun j _ => hψ j) (hm i le_top).2.2.1 (B + T + lam i • C)
          (hTklt (lam i) hl0.le hl1) hNW ⟨ε₂, hε₂, hnb⟩ εV hεV
      -- pseudo-effectivity, and the geography model of the perturbed pair
      have hpsef := exists_isRelativelyPseudoEffective_of_isRealLogMinimalModel hX hXq hZ hLMM hamp
      obtain ⟨j, hj, -⟩ := hcov _ (hVhull (lam i) hl0.le hl1 u hu) hpsef
      exact ⟨j, _, _, _, _, _, hj, hLMM, hamp⟩
    obtain ⟨N, Y', iI', iC', iL', iN', sY', πY', φ', hE', hfin⟩ := hfinite
    choose k D K₁ D₁ K₂ D₂ h₁ h₂ hamp using hfin
    have hiso : ∀ i, ∃ e : Y' (k i) ≅ modelSeq X Y i, (φ' (k i)).compHom e.hom = ψ i := fun i =>
      exists_iso_of_isRealLogMinimalModel_of_isRelativelyAmple hX hXq hZ (h₁ i) (h₂ i) (hE' (k i))
        (hψE i) (hamp i)
    refine ⟨N, k, fun i j hij => ?_⟩
    obtain ⟨e₁, he₁⟩ := hiso i
    obtain ⟨e₂, he₂⟩ : ∃ e : Y' (k i) ≅ modelSeq X Y j, (φ' (k i)).compHom e.hom = ψ j :=
      hij ▸ hiso j
    refine ⟨e₁.symm ≪≫ e₂, ?_⟩
    rw [← he₁, ← he₂, Iso.trans_hom, Iso.symm_hom, compHom_compHom, Iso.hom_inv_id_assoc]
  -- (F4) a nonempty sequence of steps is not an isomorphism over `X`: discrepancies are
  -- nondecreasing and strictly increase at the first step
  have hnorep : ∀ i j, i < j →
      ¬ ∃ e : modelSeq X Y i ≅ modelSeq X Y j, (ψ i).compHom e.hom = ψ j := by
    rintro i j hij ⟨e, he⟩
    haveI := TI j
    haveI := TL j
    haveI := TN j
    haveI : QuasiCompact (Ts j) := (hTn j).1.toQuasiCompact
    haveI : CompactSpace (TV j) := QuasiCompact.compactSpace_of_compactSpace (Ts j)
    haveI := iMS j
    have hXip := (hm i le_top).2.1
    have hXjp := (hm j le_top).2.1
    have hXin : IsNormalVariety ℂ (modelStr sX sY i) := ⟨hXip.1, inferInstance⟩
    have hXjn : IsNormalVariety ℂ (modelStr sX sY j) := ⟨hXjp.1, inferInstance⟩
    -- the tower maps to `X_i` and `X_j` differ by `e`
    have hqe : Tq j j le_rfl = Tq j i hij.le ≫ e.hom :=
      eq_of_compHom_eq_of_isInverse (A := X) (hTh j) (by
        rw [hT1 j j le_rfl, ← compHom_compHom, hT1 j i hij.le, he])
    -- prime divisors correspond under `e`
    have hregE : ∀ y : modelSeq X Y j, y ∈ biregularLocus e.hom := fun y =>
      le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance) (Set.mem_univ y)
    have hEtr : ∀ F' : MMP.Mori.PrimeDivisor (modelSeq X Y i),
        ∃ F : MMP.Mori.PrimeDivisor (modelSeq X Y j),
          MMP.Mori.RationalMap.transformPrimeDivisor e.hom.toRationalMap F' = some F ∧
            e.hom F'.genericPoint = F.genericPoint := by
      intro F'
      have hco : Order.coheight (e.hom F'.genericPoint) = 1 := by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus e.hom (hregE _)]
        exact F'.coheight_genericPoint
      refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, ?_,
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩
      exact (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom F' _).mpr
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    have hEinv : ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y j),
        ∃ F' : MMP.Mori.PrimeDivisor (modelSeq X Y i), e.hom F'.genericPoint = F.genericPoint := by
      intro F
      have hee : e.hom (e.inv F.genericPoint) = F.genericPoint := Scheme.inv_hom_apply e _
      have hco : Order.coheight (e.inv F.genericPoint) = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus e.hom (hregE _), hee]
        exact F.coheight_genericPoint
      exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
        (congrArg (fun x => e.hom x)
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco)).trans hee⟩
    have he_inj : Function.Injective e.hom.base := e.hom.isOpenEmbedding.injective
    have hEE : ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y j),
        ¬ MMP.Flips.RationalMap.IsInverseExceptional e.hom.toRationalMap F := by
      intro F hF
      obtain ⟨F', hF'⟩ := hEinv F
      exact hF F' ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom F' F).mpr
        hF')
    -- the transforms through `X_j` are the transforms through `X_i` followed by `e`
    have hI1 : ∀ D : RDivisor X, MMP.Mori.RationalMap.transformDivisor (ψ j) D =
        MMP.Mori.RationalMap.transformDivisor e.hom.toRationalMap
          (MMP.Mori.RationalMap.transformDivisor (ψ i) D) := by
      intro D
      have hP : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor (ψ j) P =
          (MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) P).bind
            (MMP.Mori.RationalMap.transformPrimeDivisor e.hom.toRationalMap) := by
        intro P
        obtain ⟨E, hE⟩ := hTstrict j P
        cases hψi : MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) P with
        | some F' =>
          have h1 := (hT2 j i hij.le P E hE F').mp hψi
          obtain ⟨F, hF, hFe⟩ := hEtr F'
          rw [Option.bind_some, hF]
          exact (hT2 j j le_rfl P E hE F).mpr (by rw [hqe, Scheme.Hom.comp_apply, h1, hFe])
        | none =>
          rw [Option.bind_none]
          cases hψj : MMP.Mori.RationalMap.transformPrimeDivisor (ψ j) P with
          | none => rfl
          | some F =>
            exfalso
            have h2 := (hT2 j j le_rfl P E hE F).mp hψj
            rw [hqe, Scheme.Hom.comp_apply] at h2
            obtain ⟨F', hF'⟩ := hEinv F
            have h3 : Tq j i hij.le E.genericPoint = F'.genericPoint := he_inj (h2.trans hF'.symm)
            have := (hT2 j i hij.le P E hE F').mpr h3
            rw [hψi] at this
            exact absurd this (by simp)
      change DivisorWithCoeffs.mapPrimeDivisors _ D =
        DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ D)
      exact (congrArg (fun φ' => DivisorWithCoeffs.mapPrimeDivisors φ' D) (funext hP)).trans
        (mapPrimeDivisors_bind _ _ D)
    -- the pulled-back adjoint of `X_j` dominates that of `X_i`
    haveI := (hTsep j i hij.le).2
    haveI := (hTsep j j le_rfl).2
    have hpbi := (hTq j i hij.le).2.2
    have hpbj := (hTq j j le_rfl).2.2
    obtain ⟨hi', hinvi⟩ : ∃ h' : (modelSeq X Y i).RationalMap (TV j),
        MMP.Mori.RationalMap.IsInverse (Tq j i hij.le).toRationalMap h' :=
      MMP.Mori.RationalMap.IsBirational.exists_isInverse hpbi
    obtain ⟨hj', hinvj⟩ : ∃ h' : (modelSeq X Y j).RationalMap (TV j),
        MMP.Mori.RationalMap.IsInverse (Tq j j le_rfl).toRationalMap h' :=
      MMP.Mori.RationalMap.IsBirational.exists_isInverse hpbj
    haveI := iMS i
    have hcomp_e : hi'.compHom (Tq j j le_rfl) = e.hom.toRationalMap := by
      rw [hqe, ← compHom_compHom, compHom_eq_of_isInverse hinvi, toRationalMap_compHom,
        Category.id_comp]
    have hVi : IsNormalVariety ℂ (Tq j i hij.le ≫ modelStr sX sY i) := by
      rw [(hTq j i hij.le).1]; exact hTn j
    have hVj : IsNormalVariety ℂ (Tq j j le_rfl ≫ modelStr sX sY j) := by
      rw [(hTq j j le_rfl).1]; exact hTn j
    have hidE : ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Y j),
        ¬ MMP.Flips.RationalMap.IsInverseExceptional
          (Scheme.Hom.toRationalMap (𝟙 (modelSeq X Y j))) F :=
      fun F hF => hF F ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff
        (𝟙 (modelSeq X Y j)) F F).mpr rfl)
    have t1 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hXin hXjn hEE
      (Tq j i hij.le) (Tq j j le_rfl) hi' hVi hVj hpbi hpbj hinvi hcomp_e (hG 0 j i hij.le)
    rw [hLvψ 0 i, ← hI1, ← hLvψ 0 j] at t1
    have t2 := MMP.Fourfold.transformDivisor_eq_of_isRCartierPullback hXjn hXjn hidE
      (Tq j j le_rfl) (Tq j j le_rfl) hj' hVj hVj hpbj hpbj hinvj
      (compHom_eq_of_isInverse hinvj) (hG 0 j j le_rfl)
    rw [transformDivisor_id_toRationalMap hXjn] at t2
    have key := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (Ts j) (modelStr sX sY j)
      (modelStr sX sY i) (hTn j) (hTp j) hXjn hXjp hXin hXip (𝟙 _) e.hom (Tq j j le_rfl)
      (Tq j i hij.le) (hTq j j le_rfl).1 (hTq j i hij.le).1 (by rw [Category.comp_id, hqe])
      (hTq j j le_rfl).2.1 hpbj (hTq j i hij.le).2.1 hpbi (hLvc 0 j)
      (isRelativelyNef_of_isIso (hm i le_top).2.2.1 e.hom _) (hG 0 j j le_rfl) (hG 0 j i hij.le)
      (by rw [map_sub, t1, t2, sub_self])
    -- the pulled-back adjoints decrease from `X_{i+1}` to `X_j`
    have hchain : ∀ k (hik : i + 1 ≤ k) (hk : k ≤ j),
        0 ≤ G 0 j (i + 1) hij - G 0 j k hk := by
      intro k hik
      induction k, hik using Nat.le_induction with
      | base => intro hk; simp
      | succ k hik ih =>
        intro hk
        have h1 := ih (Nat.le_of_succ_le hk)
        have h2 := hGstep 0 j k hk (hlam k).1.le
        have : G 0 j (i + 1) hij - G 0 j (k + 1) hk =
            (G 0 j (i + 1) hij - G 0 j k (Nat.le_of_succ_le hk)) +
              (G 0 j k (Nat.le_of_succ_le hk) - G 0 j (k + 1) hk) := by abel
        rw [this]
        exact add_nonneg h1 h2
    have h1 := hGstep 0 j i hij (hlam i).1.le
    have h2 := hchain j hij le_rfl
    have hEq : G 0 j i hij.le = G 0 j (i + 1) hij := by
      refine Finsupp.ext fun P => ?_
      have a1 : (0 : ℝ) ≤ G 0 j i hij.le P - G 0 j (i + 1) hij P := by simpa using h1 P
      have a2 : (0 : ℝ) ≤ G 0 j (i + 1) hij P - G 0 j j le_rfl P := by simpa using h2 P
      have a3 : (0 : ℝ) ≤ G 0 j j le_rfl P - G 0 j i hij.le P := by simpa using key P
      linarith
    -- the adjoint of `X_{i+1}` is nef over `W_i`, so the adjoint of `X_i` is nef over `W_i`
    obtain ⟨-, hWi, -, -, hneg, -, hcase, -, -⟩ := hstep_i i
    have hX1q := (hm (i + 1) le_top).2.2.1
    have hLnef : IsRelativelyNef (X := modelSeq X Y (i + 1)) ℂ (modelStr sX sY (i + 1)) (fp i)
        (Lv 0 (i + 1)) := by
      rcases hcase with ⟨-, -, hiso, -⟩ | hflip
      · haveI := hiso
        exact isRelativelyNef_of_isIso (X := Y i) (sX := sY i) hX1q (fp i) (Lv 0 (i + 1))
      · haveI : QuasiCompact (sY i) := (hm (i + 1) le_top).2.1.1.toQuasiCompact
        have ha := isRelativelyNef_of_isRelativelyAmple (X := Y i) (sX := sY i)
          hflip.isRelativelyAmple_transform
        rw [transformDivisor_logCanonicalDivisor, ← (hstep_i i).2.2.2.2.2.2.2.1] at ha
        obtain ⟨n₁, h₁⟩ := hKtr (i + 1)
        obtain ⟨n₂, h₂⟩ := isCanonicalDivisor_transformDivisor_of_step
          (hm i le_top).2.2.2.1 hWi (hm (i + 1) le_top).2.1.1 (hstepfacts i).2.2.2.2.2.2.2
          (Or.inr hflip) hneg
        have hle := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sY i)
          ⟨(hm (i + 1) le_top).2.1.1, inferInstance⟩ h₁ h₂
        have := isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent hle ha
        have e : Lv 0 (i + 1) = logCanonicalDivisor
            (MMP.Mori.RationalMap.transformDivisor (ψ (i + 1)) K) (BY i) := by
          have h3 := hLvform 0 (i + 1)
          simp only [zero_smul, add_zero] at h3
          exact h3
        rw [e]
        exact this
    haveI := (hTsep j (i + 1) hij).2
    haveI : IsSeparated (modelStr sX sY (i + 1)) := (hm (i + 1) le_top).2.1.1.toIsSeparated
    haveI : LocallyOfFiniteType (modelStr sX sY (i + 1)) :=
      (hm (i + 1) le_top).2.1.1.toLocallyOfFiniteType
    haveI : QuasiCompact (modelStr sX sY (i + 1)) := (hm (i + 1) le_top).2.1.1.toQuasiCompact
    haveI : QuasiCompact (Tq j (i + 1) hij ≫ modelStr sX sY (i + 1)) := by
      rw [(hTq j (i + 1) hij).1]; infer_instance
    have hGnef := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback
      (Z := modelSeq X Y (i + 1)) (sZ := modelStr sX sY (i + 1)) (𝟙 (W i)) (fp i)
      (Tq j i hij.le ≫ f i) (Tq j (i + 1) hij) (by rw [Category.comp_id]; exact hTc j i hij)
      hLnef (hG 0 j (i + 1) hij)
    rw [← hEq] at hGnef
    have hs : Tq j (i + 1) hij ≫ modelStr sX sY (i + 1) = Tq j i hij.le ≫ modelStr sX sY i :=
      ((hTq j (i + 1) hij).1).trans (hTq j i hij.le).1.symm
    haveI : IsDominant (Tq j i hij.le) := hpbi.isDominant
    haveI : Surjective (Tq j i hij.le) :=
      surjective_of_isDominant_of_isClosed_range _ (Tq j i hij.le).isClosedMap.isClosed_range
    haveI : LocallyOfFiniteType (Tq j (i + 1) hij ≫ modelStr sX sY (i + 1)) := by
      rw [(hTq j (i + 1) hij).1]; exact (hTn j).1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (modelStr sX sY i) := hXip.1.toLocallyOfFiniteType
    haveI : QuasiCompact (modelStr sX sY i) := hXip.1.toQuasiCompact
    haveI : IsSeparated (modelStr sX sY i) := hXip.1.toIsSeparated
    have hLi := MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective (Tq j i hij.le)
      hs.symm (f i) (hG 0 j i hij.le) hGnef
    rw [hLvform, zero_smul, add_zero] at hLi
    have hnef0 := isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent (hKK i).symm hLi
    -- but `K + B` is negative on the curves contracted by `f_i`
    obtain ⟨Γ, hΓ⟩ :=
      exists_isContractedBy_of_relativePicardNumber_eq_one hneg.relativePicardNumber_eq_one
    obtain ⟨m, r, L, hL, hD, hnn⟩ := hnef0
    obtain ⟨x, hx⟩ := exists_isRIntersectionNumber Γ r L hL hD
    have hx0 := hnn Γ hΓ x hx
    obtain ⟨m', r', L', hm', hr', hL', hD'⟩ := hneg.isRelativelyAntiAmple
    have hL'c : ∀ j, (L' j).IsCartier := fun j => (hL' j).1
    have hy := isRIntersectionNumber_sum_degreeOn ℂ (modelStr sX sY i) Γ r' L' hL'c
    rw [← hD'] at hy
    have hypos : 0 < ∑ j, r' j *
        ((L' j).degreeOn ℂ (modelStr sX sY i) Γ.ι Γ.dim_le (hL'c j) : ℝ) := by
      haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
      refine Finset.sum_pos (fun j _ => mul_pos (hr' j) ?_) Finset.univ_nonempty
      exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier (f i) (hL' j) (hL'c j) Γ hΓ
    have hlin := (IsRIntersectionNumber.eq_and_linear ℂ (modelStr sX sY i) Γ).2 _ _ r L r' L' x _
      1 1 hx hy
    rw [one_smul, one_smul, add_neg_cancel] at hlin
    have := eq_zero_of_isRIntersectionNumber_zero Γ hlin
    linarith
  obtain ⟨i, j, hij, hcij⟩ := Finite.exists_ne_map_eq_of_infinite c
  rcases lt_or_gt_of_ne hij with h | h
  · exact hnorep i j h (hc i j hcij)
  · exact hnorep j i h (hc j i hcij.symm)

/-- A program with scaling exists, given that every program with scaling is finite. -/
private theorem exists_scalingProgram
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 3)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C)))
    (hA : ∃ A : QDivisor X, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig π ∧
      QDivisor.toRDivisor A ≤ B)
    (hfin :
      ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
        [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
        (∀ i : ℕ, (i : ℕ∞) ≤ n →
          modelMap π πY i ≫ sZ = modelStr sX sY i ∧
          MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
          (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
          IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
        (∀ i : ℕ, (i : ℕ∞) < n →
          IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
            (lam i) ∧
          MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
          fp i ≫ g i = πY i ∧
          IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
          IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
            (logCanonicalDivisor (divisorSeq K KY i)
              (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
          ((IsBirationalMorphism (f i) ∧
              (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
                (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
              IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
            IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
              (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
          BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
          CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
        n ≠ ⊤) :
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      (IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
          (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) ∨
        ∃ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ)) (h : modelSeq X Y n ⟶ T) (gT : T ⟶ Z),
          IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n + t • divisorSeq C CY n))}
            (lam n) ∧
          MMP.Mori.IsProjectiveVariety ℂ sT ∧ h ≫ gT = modelMap π πY n ∧
          IsNegativeExtremalContraction ℂ (modelStr sX sY n) sT
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) h ∧
          IsNumericallyTrivialOver ℂ (modelStr sX sY n) h
            (logCanonicalDivisor (divisorSeq K KY n)
              (divisorSeq B BY n + lam n • divisorSeq C CY n)) ∧
          topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n))) := by
  classical
  let M₀ : Model Z := { X := X, s := sX, π := π, K := K, B := B, C := C }
  have h₀ : M₀.Good sZ 1 := by
    refine ⟨hπ, hX, hXq, ?_, ⟨3, hK⟩, hB, hC, one_pos, ?_, ?_⟩
    · exact hK.topologicalKrullDim_eq
    · simpa only [one_smul] using hklt
    · simpa only [one_smul] using hnef
  let L : ℕ → Model Z × ℝ := modelLevels sZ M₀ 1
  let Y : ℕ → Scheme.{0} := fun i => (L (i + 1)).1.X
  let sY : ∀ i, Y i ⟶ Spec (.of ℂ) := fun i => (L (i + 1)).1.s
  let πY : ∀ i, Y i ⟶ Z := fun i => (L (i + 1)).1.π
  let KY : ∀ i, Divisor (Y i) := fun i => (L (i + 1)).1.K
  let BY : ∀ i, RDivisor (Y i) := fun i => (L (i + 1)).1.B
  let CY : ∀ i, RDivisor (Y i) := fun i => (L (i + 1)).1.C
  let lam : ℕ → ℝ := fun i => (advance sZ (L i).1).t
  let W : ℕ → Scheme.{0} := fun i => (advance sZ (L i).1).W
  let sW : ∀ i, W i ⟶ Spec (.of ℂ) := fun i => (advance sZ (L i).1).sW
  let g : ∀ i, W i ⟶ Z := fun i => (advance sZ (L i).1).g
  let fp : ∀ i, Y i ⟶ W i := fun i => (advance sZ (L i).1).fp
  let f : ∀ i, modelSeq X Y i ⟶ W i := fun i =>
    match i with
    | 0 => (advance sZ (L 0).1).f
    | i + 1 => (advance sZ (L (i + 1)).1).f
  let φ : ∀ i, (modelSeq X Y i).RationalMap (Y i) := fun i =>
    match i with
    | 0 => (advance sZ (L 0).1).φ
    | i + 1 => (advance sZ (L (i + 1)).1).φ
  have iI : ∀ i, IsIntegral (Y i) := fun i => (L (i + 1)).1.isIntegral
  have iC : ∀ i, CompactSpace (Y i) := fun i => (L (i + 1)).1.compactSpace
  have iL : ∀ i, IsLocallyNoetherian (Y i) := fun i => (L (i + 1)).1.isLocallyNoetherian
  have iN : ∀ i, IsNormal (Y i) := fun i => (L (i + 1)).1.isNormal
  -- the model conditions
  have hmodel : ∀ i, (∀ j < i, ¬ IsEnd sZ (L j).1) →
      modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i) := by
    intro i hi
    have hg := good_modelLevels hZ h₀ i hi
    have hk := hg.isRealKltPair
    obtain ⟨h1, h2, h3, -, h5, -⟩ := hg
    cases i with
    | zero => exact ⟨h1, h2, h3, h5, hk⟩
    | succ i => exact ⟨h1, h2, h3, h5, hk⟩
  -- the step conditions
  have hstep : ∀ i, (∀ j ≤ i, ¬ IsEnd sZ (L j).1) →
      IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i) := by
    intro i hi
    have hg := good_modelLevels hZ h₀ i fun j hj => hi j hj.le
    have hend := hi i le_rfl
    simp only [IsEnd, not_or] at hend
    obtain ⟨⟨c1, c2, c3, c4, c5⟩, hs⟩ := advance_spec hZ hg hend.1
    obtain ⟨-, b2, b3, b4, b5⟩ := hs.resolve_left hend.2
    cases i with
    | zero => exact ⟨c1, c2, c3, b2, c4, c5, b3, b4, b5⟩
    | succ i => exact ⟨c1, c2, c3, b2, c4, c5, b3, b4, b5⟩
  by_cases hstop : ∃ i, IsEnd sZ (L i).1
  · refine ⟨Nat.find hstop, Y, sY, iI, iC, iL, iN, πY, KY, BY, CY, lam, W, sW, f, g, fp, φ,
      fun i hi => hmodel i fun j hj => Nat.find_min hstop (lt_of_lt_of_le hj hi),
      fun i hi => hstep i fun j hj => Nat.find_min hstop (lt_of_le_of_lt hj hi), ?_⟩
    have hn := Nat.find_spec hstop
    set n := Nat.find hstop with hn_def
    have hg := good_modelLevels hZ h₀ n fun j hj => Nat.find_min hstop hj
    by_cases hnef : IsRelativelyNef ℂ (L n).1.s (L n).1.π
        (logCanonicalDivisor (L n).1.K (L n).1.B)
    · left
      clear_value n
      cases n with
      | zero => exact hnef
      | succ n => exact hnef
    · have hfib := hn.resolve_left hnef
      obtain ⟨⟨c1, c2, c3, c4, c5⟩, -⟩ := advance_spec hZ hg hnef
      right
      clear_value n
      cases n with
      | zero => exact ⟨W 0, sW 0, f 0, g 0, c1, c2, c3, c4, c5, hfib⟩
      | succ n => exact ⟨W (n + 1), sW (n + 1), f (n + 1), g (n + 1), c1, c2, c3, c4, c5, hfib⟩
  · simp only [not_exists] at hstop
    exact absurd rfl (@hfin ⊤ Y sY iI iC iL iN πY KY BY CY lam W sW f g fp φ
      (fun i _ => hmodel i fun j _ => hstop j) (fun i _ => hstep i fun j _ => hstop j))

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 3)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C)))
    (hA : ∃ A : QDivisor X, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig π ∧
      QDivisor.toRDivisor A ≤ B) :
    -- existence of a program with scaling, ending with a nef adjoint or a Mori fibre space
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      (IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
          (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) ∨
        ∃ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ)) (h : modelSeq X Y n ⟶ T) (gT : T ⟶ Z),
          IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n + t • divisorSeq C CY n))}
            (lam n) ∧
          MMP.Mori.IsProjectiveVariety ℂ sT ∧ h ≫ gT = modelMap π πY n ∧
          IsNegativeExtremalContraction ℂ (modelStr sX sY n) sT
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) h ∧
          IsNumericallyTrivialOver ℂ (modelStr sX sY n) h
            (logCanonicalDivisor (divisorSeq K KY n)
              (divisorSeq B BY n + lam n • divisorSeq C CY n)) ∧
          topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n))) ∧
    -- finiteness of every program with scaling
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤ := by
  have hfin := n_ne_top_of_scalingProgram sX sZ π hπ hX hZ hXq K hK B C hB hC hBc hCc hklt hnef hA
  exact ⟨exists_scalingProgram sX sZ π hπ hX hZ hXq K hK B C hB hC hBc hCc hklt hnef hA hfin,
    hfin⟩

end Proof_thm_fourfold_real_threefold_big_scaling_termination

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Termination with scaling for real klt threefolds with a big boundary.** Let `π : X ⟶ Z` be
a morphism of projective complex varieties, `X` a `ℚ`-factorial threefold with canonical
divisor `K`, and let `B, C ≥ 0` be `ℝ`-Cartier divisors with `(X, B + C)` klt, `K + B + C` nef
over `Z`, and `B ≥ A` for an effective `ℚ`-divisor `A` big over `Z`. Then there is a
`(K + B)`-program over `Z` with scaling of `C` with finitely many steps whose last model either
has `K_n + B_n` nef over `Z` or is a Mori fibre space over `Z`, and every `(K + B)`-program over
`Z` with scaling of `C` has finitely many steps. -/
@[mmp "thm_fourfold_real_threefold_big_scaling_termination"]
public theorem exists_scalingProgram_and_finite_of_isRelativelyBig
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (hπ : π ≫ sZ = sX)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX) (K : Divisor X) (hK : K.IsCanonicalDivisor sX 3)
    (B C : RDivisor X) (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hBc : IsCartierCombination B) (hCc : IsCartierCombination C)
    (hklt : IsRealKltPair sX (B + C))
    (hnef : IsRelativelyNef ℂ sX π (logCanonicalDivisor K (B + C)))
    (hA : ∃ A : QDivisor X, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig π ∧
      QDivisor.toRDivisor A ≤ B) :
    -- existence of a program with scaling, ending with a nef adjoint or a Mori fibre space
    (∃ (n : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
        (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
        (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
        (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
        (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
        (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
        (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ n,
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) ∧
      (∀ i < n,
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) ∧
      (IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
          (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) ∨
        ∃ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ)) (h : modelSeq X Y n ⟶ T) (gT : T ⟶ Z),
          IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY n) (modelMap π πY n)
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n + t • divisorSeq C CY n))}
            (lam n) ∧
          MMP.Mori.IsProjectiveVariety ℂ sT ∧ h ≫ gT = modelMap π πY n ∧
          IsNegativeExtremalContraction ℂ (modelStr sX sY n) sT
            (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) h ∧
          IsNumericallyTrivialOver ℂ (modelStr sX sY n) h
            (logCanonicalDivisor (divisorSeq K KY n)
              (divisorSeq B BY n + lam n • divisorSeq C CY n)) ∧
          topologicalKrullDim T < topologicalKrullDim (modelSeq X Y n))) ∧
    -- finiteness of every program with scaling
    ∀ (n : ℕ∞) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i)) (BY CY : ∀ i, RDivisor (Y i))
      (lam : ℕ → ℝ) (W : ℕ → Scheme.{0}) (sW : ∀ i, W i ⟶ Spec (.of ℂ))
      (f : ∀ i, modelSeq X Y i ⟶ W i) (g : ∀ i, W i ⟶ Z) (fp : ∀ i, Y i ⟶ W i)
      (φ : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i : ℕ, (i : ℕ∞) ≤ n →
        modelMap π πY i ≫ sZ = modelStr sX sY i ∧
        MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i) ∧ IsQFactorial (modelStr sX sY i) ∧
        (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX sY i) m (divisorSeq K KY i)) ∧
        IsRealKltPair (modelStr sX sY i) (divisorSeq B BY i)) →
      (∀ i : ℕ, (i : ℕ∞) < n →
        IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (modelStr sX sY i) (modelMap π πY i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i + t • divisorSeq C CY i))}
          (lam i) ∧
        MMP.Mori.IsProjectiveVariety ℂ (sW i) ∧ f i ≫ g i = modelMap π πY i ∧
        fp i ≫ g i = πY i ∧
        IsNegativeExtremalContraction ℂ (modelStr sX sY i) (sW i)
          (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) ∧
        IsNumericallyTrivialOver ℂ (modelStr sX sY i) (f i)
          (logCanonicalDivisor (divisorSeq K KY i)
            (divisorSeq B BY i + lam i • divisorSeq C CY i)) ∧
        ((IsBirationalMorphism (f i) ∧
            (∃ E : MMP.Mori.PrimeDivisor (modelSeq X Y i),
              (MMP.Mori.exceptionalSet (f i) : Set (modelSeq X Y i)) = E.support) ∧
            IsIso (fp i) ∧ IsModificationOf (f i) (fp i) (φ i)) ∨
          IsFlip ℂ (modelStr sX sY i) (sW i) (sY i)
            (logCanonicalDivisor (divisorSeq K KY i) (divisorSeq B BY i)) (f i) (fp i) (φ i)) ∧
        BY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq B BY i) ∧
        CY i = MMP.Mori.RationalMap.transformDivisor (φ i) (divisorSeq C CY i)) →
      n ≠ ⊤ :=
        by
          revert X Z sX sZ π hπ hX hZ hXq K hK B C hB hC hBc hCc hklt hnef hA
          exact Proof_thm_fourfold_real_threefold_big_scaling_termination.solution

end MMP.Fourfold
