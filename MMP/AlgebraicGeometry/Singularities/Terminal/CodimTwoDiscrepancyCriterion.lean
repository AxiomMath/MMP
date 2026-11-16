module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.Singularities.PairClasses
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipBoundaryTransform
import MMP.AlgebraicGeometry.MMP.Flip.Defs
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Resolution.Blowup
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
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Morphisms.Birational.IsoInCodimOne
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Positive discrepancies over a codimension-two point, and terminal pairs

Let `X` be a normal variety over a field `k` of characteristic zero, `K` a canonical divisor of
`X`, `D = ∑ⱼ dⱼ Dⱼ` an effective `ℚ`-divisor with `K + D` `ℚ`-Cartier, and `W ⊆ X` an irreducible
closed subset of codimension two. Every divisor `E` over `X` with `Center_X(E) = W` has positive
discrepancy `a(E, X, D)` if and only if the local ring `𝒪_{X,η_W}` at the generic point of `W` is
regular and `mult_W(D) = ∑ⱼ dⱼ mult_W(Dⱼ) < 1`. For the germ of a normal surface at a closed point
this is the classical characterisation of terminal surface pairs: the surface is smooth there and
the boundary has multiplicity `< 1`.

If `𝒪_{X,η_W}` is regular and `mult_W(D) ≤ 1`, every such discrepancy is at least `1 - mult_W(D)`:
blow up the centre of `E` repeatedly, the discrepancy `a(E, Y, 0)` dropping at each step, until `E`
is the exceptional divisor of the blow-up of its centre, whose discrepancy is computed directly.
Conversely, positivity forces `𝒪_{X,η_W}` to be regular (via the minimal resolution of the generic
surface germ), and the exceptional divisor of the blow-up of `W` near `η_W` has discrepancy
`1 - mult_W(D)`, which is therefore positive.

As a consequence, a terminal pair `(X, D)` of dimension `n ≥ 2` has `⌊D⌋ = 0`: a component `Dⱼ`
contains an irreducible closed `W` of codimension two at whose generic point `X` is regular and
`Dⱼ` is the only component of `D`, with multiplicity one. Every divisor over `X` with center `W`
is exceptional, so has positive discrepancy, and the characterisation gives `dⱼ = mult_W(D) < 1`.

## Main results

* `MMP.Flips.forall_isDiscrepancy_pos_iff_isRegularLocalRing_and_lt_one`: the characterisation.
* `MMP.Flips.IsTerminalPair.roundDown_eq_zero`: `⌊D⌋ = 0` for a terminal pair `(X, D)` of
  dimension at least two.

## Implementation notes

The discrepancy is the general one, `MMP.Flips.IsDiscrepancy`, of the `ℝ`-divisor underlying `D`;
"every divisor with center `W` has positive discrepancy" reads: for every divisor
`E : MMP.Flips.ProperDivisorOver k sX` with `E.center = W`, every value `a` of `a(E, X, D)` is
positive. The multiplicity `mult_W(D)` is `∑_Γ coeff_Γ(D) · mult_W(Γ)`, with
`MMP.Mori.PrimeDivisor.multiplicityAlong` (finite, as `𝒪_{X,η_W}` is Noetherian).

The regularity and blow-up inputs are in the Kollár–Mori form `MMP.Mori.IsDiscrepancy` of a
`MMP.Mori.DivisorOver`. They are carried over to `MMP.Flips.IsDiscrepancy` of a divisor with
proper model with the same valuation and center (Nagata compactification).

The discrepancy of the blow-up at a generically regular centre
(`MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero`), the multiplicity bound for
strict transforms (`MMP.Mori.multiplicityAlong_inverseTransformDivisor_blowUpToBase_le`) and the
blow-up induction are used over a field of characteristic zero (perfectness is what they use),
not over an algebraically closed field as elsewhere in the library.

The round-down is stated as `D.roundDown = 0`; since `D` is effective this is the coefficient
form `∀ P, D.coeff P < 1` (`MMP.Mori.roundDown_nonpos_iff`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips],
  Exercise 4.9.1, (4.9.1.1)
-/
universe u

namespace MMP.Flips.Sec35aBound

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open MMP.Mori

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
private theorem exists_natCast_isDiscrepancy_zero {k : Type u} [Field k] [PerfectField k]
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
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
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
private theorem one_sub_le_of_valuation_eq_blowUp {k : Type u} [Field k] [PerfectField k]
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
  have hD' := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sY hY hK
    (P - N) hKB Z (c := 2)
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
    isBirationalMorphism := MMP.Mori.isBirationalMorphism_comp E.isBirationalMorphism hf
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
  rw [mk_support_vanishingIdeal, hZ]
  norm_num

/-- **The blow-up of a smooth codimension-two centre** is a regular normal variety of the same
dimension, and the blow-down `π` is proper and birational. -/
private theorem blowUp_basic {k : Type u} [Field k] [PerfectField k]
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
    exact MMP.Mori.isBirationalMorphism_comp (isBirationalMorphism_of_isIso e.hom) hbir
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
private theorem blowUp_map_genericPoint_of_two_le_coheight {k : Type u} [Field k] [PerfectField k]
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
  have he := Stacks.Blowup.blowUpIso_hom_comp
    𝓘[Z]
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
private theorem blowUp_coheight_le_two {k : Type u} [Field k] [PerfectField k]
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
private theorem blowUp_crepant {k : Type u} [Field k] [PerfectField k]
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
    have ha := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sY hY hK
      (P - N) hKB Z (c := 2) (by rw [hZ]; rfl) le_rfl (hYreg _) ⟨_, _, hB, hπ, G⟩ (𝟙 _)
      (Category.id_comp _) hη
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
private theorem exists_isExceptional_mem_support {k : Type u} [Field k] [PerfectField k]
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
private theorem blowUp_measure_lt {k : Type u} [Field k] [PerfectField k]
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
    have ha := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sY hY hK
      0 hKB Z (c := 2) (by rw [hZ]; rfl) le_rfl (hYreg _) ⟨_, _, hB, hπ, G⟩ (𝟙 _)
      (Category.id_comp _) hη
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
private theorem exists_blowUp_data {k : Type u} [Field k] [PerfectField k]
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
    have : c = 2 := by omega
    rw [this]; rfl
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
`MMP.Mori.multiplicityAlong_inverseTransformDivisor_blowUpToBase_le`. -/
private theorem exists_stage_blowUp {k : Type u} [Field k] [PerfectField k]
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
  exact (MMP.Mori.multiplicityAlong_inverseTransformDivisor_blowUpToBase_le
    sY hY.1 hYreg Z hZ hZreg Z'
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

/-- **Generic smoothness of the centre.** An irreducible closed subset `Z` of a variety over a
perfect field is regular on an open neighbourhood `V` of its
generic point: `𝒪_{Z ∩ V, w}` is regular for every `w ∈ Z ∩ V`. -/
private theorem exists_open_isRegularLocalRing_quotient {k : Type u} [Field k] [PerfectField k]
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
  have hζreg : IsRegularLocalRing I.subscheme.functionField := inferInstance
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr hζreg
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
  have hJZ : J = Scheme.IdealSheafData.vanishingIdeal (⟨Z', Z'.isClosed⟩ : Closeds V.toScheme) := by
    have : IsReduced J.subscheme :=
      isReduced_of_isOpenImmersion ((I.comapIso V.ι).hom ≫ Limits.pullback.snd V.ι I.subschemeι)
    refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
    rw [Scheme.IdealSheafData.support_comap]
    exact Closeds.ext <| by
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
private theorem Stage.smoothStage {k : Type u} [Field k] [CharZero k]
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
private theorem SmoothStage.step {k : Type u} [Field k] [CharZero k] {μ q : ℚ}
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
private theorem Stage.one_sub_le {k : Type u} [Field k] [CharZero k]
    {μ q : ℚ} (hμ : μ ≤ 1) : ∀ {m : ℕ}, Stage k μ q m → 1 - μ ≤ q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    rcases h.smoothStage.step hμ with h' | ⟨m', hm', h'⟩
    · exact h'
    · exact ih m' hm' h'

/-- **Discrepancies over a regular codimension-two point** (FA Exercise 4.9.1). Let `X` be a normal
variety of dimension `n` over a field `k` of characteristic zero, `K` a
canonical divisor, `D` an effective `ℚ`-divisor with `K + D` `ℚ`-Cartier, and `W ⊆ X` an
irreducible closed subset of codimension `2`
with `𝒪_{X,η_W}` regular and `mult_W(D) = ∑_Γ coeff_Γ(D) · mult_W Γ ≤ 1`. If `E` is a divisor over
`X` with center `W` and `a = a(E, X, D)`, then `1 - mult_W(D) ≤ a`. -/
private theorem IsDiscrepancy.one_sub_le_of_isRegularLocalRing_of_charZero {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
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
  obtain ⟨m, hm⟩ := exists_stage hX hK hD hKD hW hreg E.toDivisorOver (map_genericPoint_eq E hE) hq
  have hb := Stage.one_sub_le hmult hm
  have : a = q := by linarith
  rw [this]
  exact_mod_cast hb

end DiscrepancyBound

end MMP.Flips.Sec35aBound

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

namespace MMP.Mori.TerminalCodimTwo

open MMP MMP.Mori

section Transport

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The FA discrepancy computed with a form `ω` cutting out `K` is the Kollár–Mori
discrepancy. -/
private theorem eq_of_isDiscrepancyWith_of_isDiscrepancy {n : ℕ} {K : Divisor X}
    {B : QDivisor X} {ω : RationalPluriForms sX n 1} (hω : divisorOfForm ω = K) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {E : Flips.ProperDivisorOver k sX} {a : ℝ}
    (h : Flips.IsDiscrepancyWith sX n (QDivisor.toRDivisor B) ω r L E a) {a' : ℚ}
    (ha' : IsDiscrepancy sX n K B E.toDivisorOver a') : a = a' := by
  obtain ⟨hX, hn, hω0, hLc, hsum, L', hpb, rfl⟩ := h
  have hco : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor B).coeff Γ =
      ∑ j, r j * (L j).coeff Γ := by
    intro Γ
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
    simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      Flips.coeff_sum_smul_toRDivisor] using this
  have hb : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E.toDivisorOver
      (1 + ((E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * (L' j).coeff E.E)) :=
    ⟨hX, E.isProper, ω, hω0, ⟨K, ha'.2.1, fun Γ => by rw [← hω]; rfl⟩, m, r, L, L', hLc, hco,
      hpb, by ring⟩
  have := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hb
  linarith

/-- The FA discrepancy `a(F, B)` is the Kollár–Mori discrepancy of every divisor over `X` with
valuation `F`. -/
private theorem eq_of_isDiscrepancy_of_valuation_eq {n : ℕ} {K : Divisor X} {B : QDivisor X}
    {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) F a) {D : DivisorOver k sX}
    (hD : D.valuation = F) {a' : ℚ} (ha' : IsDiscrepancy sX n K B D a') : a = a' := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, hω, hw⟩ := h
  obtain ⟨a'', ha''⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ha'.isPair hK E.toDivisorOver
  rw [eq_of_isDiscrepancyWith_of_isDiscrepancy hω hw ha'']
  have hv : E.toDivisorOver.valuation = D.valuation := hEF.trans hD.symm
  exact_mod_cast MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq ha'.1 hv) ha'' ha'

/-- The valuation of a divisor over `X` with `f` proper has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation (E : Flips.ProperDivisorOver k sX) :
    Flips.HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

omit [PerfectField k] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] in
/-- If `M = m(K + B)` with `m > 0`, then `K + B = m⁻¹ M` as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_sum {K : Divisor X} {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    simpa [mul_add] using congrArg (fun G : QDivisor X => G.coeff Γ) hM
  have h'' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast h'
  rw [Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, h'', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
  field_simp

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
/-- If `m(K + B)` is Cartier, `K + B` is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_add {K : Divisor X} {B : QDivisor X} {m : ℕ}
    (hm : 0 < m) {M : Divisor X}
    (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B)) (hMc : M.IsCartier) :
    Flips.IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor B) := by
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  rw [toRDivisor_add_eq_sum hm hM]
  simp only [Flips.toRDivisor_eq_mapCoeffs]

/-- If `M = m(K + B)` is Cartier, the FA discrepancy of every divisor over `X` with `f` proper
exists and lies in `m⁻¹ℤ`. -/
private theorem exists_isDiscrepancy_intCast_div (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (m : ℤ) • (Divisor.toQDivisor K + B))
    (hMc : M.IsCartier) (E : Flips.ProperDivisorOver k sX) :
    ∃ z : ℤ, Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation ((z : ℝ) / m) := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    have := E.isProper
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hωK : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f hMc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsum : Divisor.toRDivisor (divisorOfForm ω) + QDivisor.toRDivisor B =
      ∑ _j : Fin 1, (1 / (m : ℝ)) • Divisor.toRDivisor M := by
    rw [hωK]; exact toRDivisor_add_eq_sum hm hM
  refine ⟨m * E.toDivisorOver.ordPullback ω - M'.coeff E.E, hK,
    isCartierCombination_toRDivisor_add hm hM hMc, hasNonemptyCenter_valuation E,
    E, ω, 1, fun _ => 1 / (m : ℝ), fun _ => M, rfl, hωK, hX, hK.topologicalKrullDim_eq, hω0,
    fun _ => hMc, hsum, fun _ => M', fun _ => ⟨_, hM'⟩, ?_⟩
  rw [Fin.sum_univ_one]
  push_cast
  field_simp

/-- **Transport of a Kollár–Mori discrepancy.** A Kollár–Mori discrepancy `q = a(D, X, B)` of a
divisor `D` over `X` is the FA discrepancy of a divisor over `X` with proper model and the same
center. -/
private theorem exists_properDivisorOver_isDiscrepancy (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    {D : DivisorOver k sX} {q : ℚ} (hq : IsDiscrepancy sX n K B D q) :
    ∃ E : Flips.ProperDivisorOver k sX, E.center = D.center ∧
      Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation q := by
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨m, hm, M, hM, hMc⟩ := hKB.exists_pos
  obtain ⟨z, hz⟩ := exists_isDiscrepancy_intCast_div hX hq.2.1 hm hM hMc E
  have hzq := eq_of_isDiscrepancy_of_valuation_eq hz hE.symm hq
  refine ⟨E, ?_, hzq ▸ hz⟩
  rw [E.center_eq_toDivisorOver_center]
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 hE

/-- Every divisor over `X` with proper model has a discrepancy `a_ω(E, X, B)` with respect to a
pair `(X, B)` with `K_X + B` `ℚ`-Cartier. -/
private theorem exists_isQDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) (E : Flips.ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), Flips.IsQDiscrepancyWith sX n B ω E a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' E.f
    (Divisor.toQDivisor (divisorOfForm ω) + B)
  obtain ⟨G, hG, -⟩ := hKB.existsUnique_isPullback hB
  exact ⟨ω, _, hX, hK.1, hω0, hKB, hB, G, hG, rfl⟩

end Transport

section Regularity

/-- **Positive discrepancies over a codimension-two point force regularity**, over a field of
characteristic zero: if every exceptional divisor over `X` with center `W` has positive
Kollár–Mori discrepancy `a(E, X, B)`, then `𝒪_{X,η_W}` is regular. -/
private theorem isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : (Divisor.toQDivisor K + B).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hpos : ∀ (D : DivisorOver k sX), D.IsExceptional → D.center = W →
      ∀ a : ℚ, IsDiscrepancy sX n K B D a → 0 < a) :
    IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) := by
  classical
  have hP : IsPair sX B := ⟨hX, n, K, hK, hKB⟩
  have hPair : MMP.Fourfold.IsCharZeroPair sX B := ⟨inferInstance, hP, hB⟩
  set x := W.isIrreducible.genericPoint with hx_def
  have hxW : closure {x} = (W : Set X) := W.isIrreducible.isGenericPoint_genericPoint_closure.trans
    W.isClosed.closure_eq
  have hcx : Order.coheight x = 2 := by
    have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext hxW
    rw [← hW, codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hxW, hcx, hK.topologicalKrullDim_eq] at hdim
  obtain ⟨d, rfl, hWd⟩ : ∃ d : ℕ, n = d + 2 ∧ topologicalKrullDim (W : Set X) = d := by
    revert hdim
    induction topologicalKrullDim (W : Set X) using WithBot.recBotCoe with
    | bot => intro h; exact absurd h.symm (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        intro h
        rw [← WithBot.coe_add, top_add] at h
        exact absurd h.symm (by exact_mod_cast ENat.coe_ne_top n)
      | coe m =>
        intro h
        refine ⟨m, ?_, rfl⟩
        have h' : ((m + 2 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
          rw [← h]; norm_cast
        exact_mod_cast h'.symm
  obtain ⟨U, -, φ, -, -, S, ι, sS, -, _, _, _, _, hSa, hSft, hSnv, hSdim, p, hp, -, hgen,
    hiso, -, -, BS, hBS, hBS0, -, hbij, hlog⟩ :=
    MMP.Fourfold.exists_genericFibre_bijOn_valuation_center sX hPair hK.topologicalKrullDim_eq
      W hWd
  by_contra hreg
  have hsing : p ∉ smoothLocus sS := by
    intro hps
    apply hreg
    obtain ⟨V, hpV, hV⟩ := mem_smoothLocus_iff.mp hps
    have : Smooth (V.ι ≫ sS) := hV
    have hrV := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sS) ⟨p, hpV⟩
    have hrS : IsRegularLocalRing (S.presheaf.stalk p) :=
      IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨p, hpV⟩).commRingCatIsoToRingEquiv
    have hrU : IsRegularLocalRing ((U : Scheme).presheaf.stalk (ι p)) :=
      IsRegularLocalRing.of_ringEquiv (asIso (ι.stalkMap p)).symm.commRingCatIsoToRingEquiv
    have hrX : IsRegularLocalRing (X.presheaf.stalk (U.ι (ι p))) :=
      IsRegularLocalRing.of_ringEquiv (U.stalkIso (ι p)).commRingCatIsoToRingEquiv
    have hxe : U.ι (ι p) = x := hgen.eq hxW
    rwa [hxe] at hrX
  have : IsQuasiProjectiveVariety _ sS := by
    have : AlgebraicGeometry.IsVariety _ sS := hSnv.1
    exact ⟨Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom sS inferInstance⟩
  have : CharZero (FractionRing (MvPolynomial (Fin d) k)) :=
    charZero_of_injective_algebraMap
      (algebraMap k (FractionRing (MvPolynomial (Fin d) k))).injective
  obtain ⟨D, hDproj, -, hDc, a, ha1, ha⟩ :=
    MMP.Threefold.exists_isLogDiscrepancy_le_one_of_notMem_smoothLocus sS hSdim
      ⟨inferInstance, hBS, hBS0⟩ hp hsing
  have hξ : D.valuation ∈ {ξ | ∃ D : DivisorOver (FractionRing (MvPolynomial (Fin d) k)) sS,
      D.valuation = ξ ∧ (D.center : Set S) = {p}} := ⟨D, rfl, hDc⟩
  obtain ⟨D₂, hD₂v, hD₂c⟩ := hbij.mapsTo hξ
  obtain ⟨n', D₁, -, hD₁v, hD₁⟩ :=
    (hlog _ hξ a).mp ⟨2, D, isProper_of_isProjectiveMorphism D.f hDproj, rfl, ha⟩
  have hD₁c : D₁.center = W :=
    (MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX.1 (hD₁v.trans hD₂v.symm)).trans hD₂c
  have hD₁e : D₁.IsExceptional := by
    by_contra hne
    obtain ⟨P, hPv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D₁ hne
    exact (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D₁).mp
      (by rw [hD₁c, hW]) P hPv
  obtain ⟨a₁, ha₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D₁
  have hnn : n' = d + 2 := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD₁
    rw [hK.topologicalKrullDim_eq] at this
    exact_mod_cast this.symm
  subst hnn
  have h1 := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha₁ hD₁
  have h2 := hpos D₁ hD₁e hD₁c a₁ ha₁
  have h3 : (0 : ℝ) < a₁ := by exact_mod_cast h2
  linarith

end Regularity

section BlowUp

open Topology
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
    rw [hx]; exact h1.eq (V.isIrreducible.isGenericPoint_genericPoint V.isClosed)
  set S := smoothLocus (Z.subschemeι ≫ s) with hS
  have hζreg : IsRegularLocalRing Z.subscheme.functionField := inferInstance
  have hζS : ζ ∈ S := (MMP.Flips.Sec35aBound.mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr hζreg
  set T : Set Y := Z.subschemeι '' (S : Set Z.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : x ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (Z.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  set R := smoothLocus s with hR
  have hxR : x ∈ R := (MMP.Flips.Sec35aBound.mem_smoothLocus_iff_isRegularLocalRing s x).mpr hreg
  set U : Y.Opens := R ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩ with hU
  have hxU : x ∈ U := ⟨hxR, hxT⟩
  set I := Z.comap U.ι with hI
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' V := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change U.ι ⁻¹' (Z.support : Set Y) = _
    rw [hZsupp]
  have hUsm : IsSmoothScheme (U.ι ≫ s) :=
    MMP.Flips.Sec35aBound.isSmoothScheme_of_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((MMP.Flips.Sec35aBound.mem_smoothLocus_iff_isRegularLocalRing s _).mp u.2.1)
  have e : I.subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
      Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  have hIsm : IsSmoothScheme (I.subschemeι ≫ U.ι ≫ s) := by
    refine MMP.Flips.Sec35aBound.isSmoothScheme_of_isRegularLocalRing _ fun y => ?_
    set j := (Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι with hj
    have hjy : Z.subschemeι (j y) = U.ι (I.subschemeι y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
    refine isRegularLocalRing_of_isOpenImmersion j y
      ((MMP.Flips.Sec35aBound.mem_smoothLocus_iff_isRegularLocalRing (Z.subschemeι ≫ s) _).mp ?_)
    by_contra hns
    exact (I.subschemeι y).2.2 ⟨j y, hns, hjy⟩
  have hxgen : IsGenericPoint x (V : Set Y) :=
    hx ▸ V.isIrreducible.isGenericPoint_genericPoint V.isClosed
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
an open subscheme of `Bl_V Y`, and the generic point of `F` lies over `x`. -/
private theorem exists_divisorOver_smoothBlowup {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} [IsIntegral Y] {s : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k s)
    (V : IrreducibleCloseds Y) (hV : 2 ≤ codimension V) (x : Y)
    (hx : x = V.isIrreducible.genericPoint) (hreg : IsRegularLocalRing (Y.presheaf.stalk x)) :
    ∃ (D : DivisorOver k s) (h : D.Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨V, V.isClosed⟩ : Closeds Y))),
      IsOpenImmersion h ∧ h ≫ blowUpToBase _ = D.f ∧ D.f D.E.genericPoint = x := by
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
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hx]
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
    have : ((2 : ℕ) : ℕ∞) ≤ (c : ℕ∞) := by rw [hcc, ← hcx]; exact hV
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
    obtain ⟨O, hO, hOi⟩ := hbirπ.exists_isOpenImmersion
    have : IsOpenImmersion (O.ι ≫ π ≫ U.ι) := by
      rw [← Category.assoc]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion (π ≫ U.ι) O (O.isOpen.dense hO)
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
  exact ⟨D, h, hh, hP.w.symm, hDf⟩

/-- The exceptional prime of `Bl_W X` over `η_W`, as a divisor over `X` on an open normal
subscheme of the blow-up. -/
private theorem exists_divisorOver_blowUp {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (hX : IsNormalVariety k sX)
    (W : IrreducibleCloseds X) (hW : 2 ≤ codimension W)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    ∃ (D : DivisorOver k sX)
        (j : D.Y ⟶ Stacks.Blowup.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X))),
        IsOpenImmersion j ∧ j ≫ Stacks.Blowup.blowUpToBase _ = D.f ∧
          D.f D.E.genericPoint = W.isIrreducible.genericPoint := by
  obtain ⟨D, h, hh, hhf, hDf⟩ := exists_divisorOver_smoothBlowup hX W hW _ rfl hreg
  have hinv : (Stacks.Blowup.blowUpIso _).inv ≫ Stacks.Blowup.blowUpToBase _ =
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨W, W.isClosed⟩ : Closeds X)) := by
    rw [Iso.inv_comp_eq, Stacks.Blowup.blowUpIso_hom_comp]
  refine ⟨D, h ≫ (Stacks.Blowup.blowUpIso _).inv, inferInstance, ?_, hDf⟩
  rw [Category.assoc, hinv, hhf]

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The exceptional divisor of the blow-up of a codimension-two `W` with `𝒪_{X,η_W}` regular,
near `η_W`, has center `W` and discrepancy `a(E, X, B) = 1 - mult_W(B)`. -/
private theorem exists_properDivisorOver_center_eq_isDiscrepancy_one_sub
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2)
    (hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint)) :
    ∃ E : Flips.ProperDivisorOver k sX, E.center = W ∧
      Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor B) E.valuation
        ((1 - B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) : ℚ) : ℝ) := by
  obtain ⟨Dbl, j, hj, hjf, hE⟩ := exists_divisorOver_blowUp hX W hW.ge hreg
  have hq := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing_of_charZero sX hX hK B
    hKB W (c := 2)
    (by rw [hW]; rfl) le_rfl hreg Dbl j hjf hE
  obtain ⟨E, hEc, hEa⟩ := exists_properDivisorOver_isDiscrepancy hX hKB hq
  refine ⟨E, hEc.trans (IrreducibleCloseds.ext ?_), ?_⟩
  · rw [Dbl.center_eq_closure_genericPoint, hE,
      W.isIrreducible.isGenericPoint_genericPoint_closure, W.isClosed.closure_eq]
  · convert hEa using 2
    push_cast
    ring

end BlowUp

end MMP.Mori.TerminalCodimTwo

namespace MMP.Flips

open MMP.Mori

/-- **Terminality at a codimension-two point** (FA Exercise 4.9.1). Let `X` be a normal variety
of dimension `n` over a field `k` of characteristic zero, `K` a canonical divisor, `D` an effective
`ℚ`-divisor with `K + D` `ℚ`-Cartier, and `W ⊆ X` an irreducible closed subset of codimension `2`.
Then `a(E, X, D) > 0` for every divisor `E` over `X` with center `W` if and only if
`𝒪_{X,η_W}` is regular and `mult_W(D) = ∑_Γ coeff_Γ(D) · mult_W Γ < 1`. -/
@[mmp "lem_fa4_surface_terminal_iff"]
public theorem forall_isDiscrepancy_pos_iff_isRegularLocalRing_and_lt_one {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {D : QDivisor X} (hD : 0 ≤ D)
    (hKD : (Divisor.toQDivisor K + D).IsQCartier) {W : IrreducibleCloseds X}
    (hW : codimension W = 2) :
    (∀ E : ProperDivisorOver k sX, E.center = W →
        ∀ a : ℝ, IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a → 0 < a) ↔
      IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) ∧
        (D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ)) < 1 := by
  constructor
  · intro hpos
    have hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) :=
      MMP.Mori.TerminalCodimTwo.isRegularLocalRing_stalk_genericPoint_of_isDiscrepancy_pos hX hK hD
        hKD hW
        fun D' _ hD'c q hq => by
          obtain ⟨E, hEc, hEq⟩ :=
            MMP.Mori.TerminalCodimTwo.exists_properDivisorOver_isDiscrepancy hX hKD hq
          exact_mod_cast hpos E (hEc.trans hD'c) q hEq
    refine ⟨hreg, ?_⟩
    obtain ⟨E, hEc, hEa⟩ :=
      MMP.Mori.TerminalCodimTwo.exists_properDivisorOver_center_eq_isDiscrepancy_one_sub hX hK hKD
        hW hreg
    have h' : (0 : ℚ) < 1 - D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ) := by
      exact_mod_cast hpos E hEc _ hEa
    linarith
  · rintro ⟨hreg, hlt⟩ E hE a ha
    have hb := Sec35aBound.IsDiscrepancy.one_sub_le_of_isRegularLocalRing_of_charZero hX hD hKD hW
      hreg hlt.le hE ha
    have h0 : (0 : ℝ) <
        ((1 - D.sum fun Γ d => d * ((Γ.multiplicityAlong W).toNat : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast sub_pos.mpr hlt
    linarith

/-- **Terminal pairs have no reduced part** (FA Exercise 4.9.1). Let `X` be a normal variety of
dimension `n ≥ 2` over a field `k` of characteristic zero, `K` a canonical divisor of `X` and
`D = ∑ⱼ dⱼ Dⱼ` an effective `ℚ`-divisor such that `(X, D)` is a terminal pair. Then
`dⱼ < 1` for every `j`, i.e. `⌊D⌋ = 0`. -/
@[mmp "lem_fa4_terminal_round_down_zero"]
public theorem IsTerminalPair.roundDown_eq_zero {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (h : IsTerminalPair sX n K D) (hn : 2 ≤ n) : D.roundDown = 0 := by
  obtain ⟨hX, hK, hDeff, hKD, hdisc⟩ := h
  have hlt (P : Mori.PrimeDivisor X) : D.coeff P < 1 := by
    by_contra! hge
    have hPs : P ∈ D.support := Finsupp.mem_support_iff.mpr fun h0 => by
      norm_num [DivisorWithCoeffs.coeff_apply, h0] at hge
    obtain ⟨W, -, hWc, hreg, hPW, hother⟩ := exists_codimension_eq_two_multiplicityAlong_eq hX
      (by rw [hK.topologicalKrullDim_eq]; exact_mod_cast hn) D hPs
    -- every divisor with center `W` is exceptional, so has positive discrepancy
    have hpos : ∀ E : ProperDivisorOver k sX, E.center = W → ∀ a : ℝ,
        IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a → 0 < a := by
      intro E hEc a ha
      have hxW : closure {W.isIrreducible.genericPoint} = (W : Set X) :=
        W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq
      have hcod : Order.coheight W.isIrreducible.genericPoint = 2 := by
        rw [← codimension_eq_coheight_genericPoint, hWc]
      have hEx : E.IsExceptional := by
        have := topologicalKrullDim_closure_singleton_add_coheight sX W.isIrreducible.genericPoint
        rw [hcod, hxW] at this
        rw [ProperDivisorOver.IsExceptional, hEc]
        exact this.le
      obtain ⟨ω, a', h'⟩ := MMP.Mori.TerminalCodimTwo.exists_isQDiscrepancyWith hX hK hKD E
      have ha' : (a' : ℝ) = a := (h'.isDiscrepancy hK hKD hEx).eq ha
      have := EReal.coe_pos.mp (hdisc.trans_le (sInf_le ⟨E, ω, a', hEx, h', rfl⟩))
      linarith
    have hlt := ((forall_isDiscrepancy_pos_iff_isRegularLocalRing_and_lt_one hX hK hDeff hKD
      hWc).1 hpos).2
    rw [Finsupp.sum, Finset.sum_eq_single P (fun Γ hΓ hne => by simp [hother Γ hΓ hne])
      (absurd hPs), hPW] at hlt
    simp only [ENat.toNat_one, Nat.cast_one, mul_one] at hlt
    exact absurd hlt (not_lt.mpr (by simpa [DivisorWithCoeffs.coeff_apply] using hge))
  refine DivisorWithCoeffs.ext' fun P => ?_
  rw [DivisorWithCoeffs.coeff_roundDown]
  simpa using Int.floor_eq_zero_iff.mpr ⟨hDeff P, hlt P⟩

end MMP.Flips
