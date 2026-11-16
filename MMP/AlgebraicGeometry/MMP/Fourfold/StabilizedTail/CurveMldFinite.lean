module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeLabels
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLine
import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.ProjectiveLineProperties
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceCurves
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.MMP.Surface.AdjunctionPerfectField
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Cohomology.ProperCoherentSections
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.GenericSurfaceCodimTwo
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# Generic curve minimal log discrepancies on a stabilized tail

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail, with step diagrams
`X_i⁻ = X_i → Z_i ← X_i⁺ = X_{i+1}`, bad loci `W_i⁻ ⊆ X_i`, `W_i⁺ ⊆ X_{i+1}` and common
low-discrepancy set `I_∞ = I(X_0, B_0)`, and let `δ > 0` bound all log discrepancies of all
stages from below. This file proves three facts about irreducible curves `V ⊆ X_i` and their
generic minimal log discrepancies `mld_{η_V}(X_i, B_i)`.

*Bounded denominators.* Take an affine neighbourhood of `η_V` and the generic fibre `S` of a
regular function whose residue on `V` is transcendental: a normal affine surface over `ℂ(u)` with
a closed point `p` whose local ring is `𝒪_{X_i,η_V}`. Divisorial valuations of `ℂ(X_i)` centred
at `V` are those of `ℂ(u)(S)` centred at `p`, with the same log discrepancies. On the minimal
resolution of `S` the prime divisors over `p` have log discrepancies in `[δ, 1]`, so they lie in
`I(X_i, B_i)` and number at most `N = |I_∞|`; their normalized intersection matrix `M'` has
entries bounded by `C = ⌈4/δ²⌉`, so `D = q |det M'| ≤ q N! C^N`, and every log discrepancy at `V`
lies in `(1/D) ℤ`. The generic mld at `V`, when at most one, is then one of finitely many
fractions in `(0, 1]`.

*Attainment.* When `mld_{η_V}(X_i, B_i) ≤ 1`, the infimum defining it is a minimum, attained by a
normalized divisorial valuation centred at `V`; every such valuation lies in `I(X_i, B_i)` and is
the transport of an element of `I_∞`.

*Finiteness of bad steps.* On each side `σ ∈ {-, +}`, only finitely many indices `i` admit an
irreducible curve `V ⊆ W_i^σ` with `mld_{η_V}(X_i^σ, B_i^σ) ≤ 1`. Otherwise one `ν ∈ I_∞` would
recur, with one mld value, at infinitely many such indices; but the log discrepancies of the
transports of `ν` are nondecreasing along the tail and increase strictly at each step whose bad
locus contains the centre.

## Main results

* `MMP.Fourfold.StabilizedTail.exists_logDiscrepancy_denom_le_and_minimalLogDiscrepancy_mem`:
  the uniform denominator bound `D_max` and the finite set `F ⊆ (0, 1] ∩ ℚ` of generic curve mlds.
* `MMP.Fourfold.StabilizedTail.exists_isCentre_isLogDiscrepancyAt_eq_minimalLogDiscrepancy`:
  generic curve mlds at most one are attained, by valuations coming from `I_∞`.
* `MMP.Fourfold.StabilizedTail.finite_setOf_exists_minimalLogDiscrepancy_le_one`: bad curves of
  mld at most one occur at finitely many steps, on each side.

## Implementation notes

* The models `X_i⁻ = X_i` and `X_i⁺ = X_{i+1}` of the `i`-th step are both stages of the tail, so
  the first two results quantify over all stages once. A curve is an irreducible closed subset of
  dimension one, its centre condition is `MMP.Intersection.IsCentre`, and `η_V` is its generic
  point; the mld is `MMP.Fourfold.minimalLogDiscrepancy` there, valued in `EReal`.
* The surface `S` is the one of `MMP.Threefold.exists_generic_surface_of_coheight_eq_two`; a
  valuation centred at `V` is realized on `S` by
  `MMP.Flips.exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType`. The
  denominator bound is proved for a pair over any field of characteristic zero, using only the
  positivity of the log discrepancies at the point; the real margin `δ` is replaced by a rational
  `0 < δ' ≤ min δ 1`.
* The comparison `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)` across a step diagram is proved by its two cases:
  strictly on the bad locus, by
  `MMP.Fourfold.IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus`, and with equality
  off it, by crepant invariance along the open set where both contractions are isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori
open scoped WithZero

universe u

namespace MMP.Fourfold

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {R S Γ₀ : Type*} [Ring R] [Ring S]
    [LinearOrderedCommMonoidWithZero Γ₀] {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S Γ₀} (h : v.comap g = w.comap g) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hg t
  exact congrArg (fun u : Valuation R Γ₀ => u s) h

/-! ### Log discrepancies of a pair -/

section LogDiscrepancy

open MMP.Flips

/-- A Cartier presentation `div(ω) + B = ∑ rⱼ Lⱼ` of `K_X + B`, read coefficientwise. -/
private theorem toRDivisor_divisorOfForm_add_eq_sum_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} (ω : RationalPluriForms sX n 1) (B : RDivisor X)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) :
    Divisor.toRDivisor (divisorOfForm ω) + B =
        ∑ j, r j • Divisor.toRDivisor (L j) ↔
      ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ j, r j * (L j).coeff Γ := by
  refine ⟨fun h Γ => ?_, fun h => Finsupp.ext fun Γ => ?_⟩
  · have h := congrArg (fun F : RDivisor X => F Γ) h
    simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h
    rw [← coeff_divisorOfForm ω Γ]
    exact h
  · simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rw [show (Divisor.toRDivisor (divisorOfForm ω)) Γ = ((Γ.ordForm ω : ℤ) : ℝ) by
      rw [← coeff_divisorOfForm ω Γ]; rfl]
    exact h Γ

/-- Every proper divisor over a pair `(X, B)` of dimension `n` has a log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_isPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B) {n : ℕ} (hn : topologicalKrullDim X = n)
    (D : DivisorOver k sX) (hD : IsProper D.f) :
    ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a := by
  obtain ⟨-, m, K, hK, -⟩ := id hB
  obtain rfl : m = n := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB hK D
  exact ⟨1 + c, (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc _).2 ⟨hD, rfl⟩⟩

end LogDiscrepancy

/-! ### The normalized exceptional matrix of a surface resolution -/

namespace NormalizedMatrix

/-- An element dividing every term of a function divides its `finsum`. -/
private theorem dvd_finsum_of_forall_dvd {α R : Type*} [Semiring R] {a : R} {g : α → R}
    (h : ∀ n, a ∣ g n) :
    a ∣ ∑ᶠ n, g n := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact Finset.dvd_sum fun n _ => h n
  · rw [finsum_of_infinite_support hfin]
    exact dvd_zero a

variable (k : Type u) [Field k] {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))

/-- On a reduced connected scheme proper over `k`, the degree `[H⁰(Z, 𝒪_Z) : k]` divides the
`k`-dimension of every cohomology group of every `𝒪_Z`-module. -/
private theorem finrank_unit_dvd_finrank_cohomologyOverField [IsProper sZ] [IsReduced Z]
    [ConnectedSpace Z] (F : Z.Modules) (n : ℕ) :
    Module.finrank k (cohomologyOverField k sZ (SheafOfModules.unit Z.ringCatSheaf) 0) ∣
      Module.finrank k (cohomologyOverField k sZ F n) := by
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  exact finrank_globalSections_dvd_finrank_cohomologyOverField k sZ
    (isField_globalSections_of_isReduced_of_connectedSpace k sZ) F n

/-- On a nonempty reduced connected scheme proper over `k`, `[H⁰(Z, 𝒪_Z) : k]` is positive. -/
private theorem finrank_unit_pos [IsProper sZ] [IsReduced Z] [ConnectedSpace Z] :
    0 < Module.finrank k (cohomologyOverField k sZ (SheafOfModules.unit Z.ringCatSheaf) 0) := by
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appTop).hom.toAlgebra
  obtain ⟨hF, hfin⟩ := isField_and_finite_globalSections k sZ
  have : Nontrivial Γ(Z, ⊤) := hF.nontrivial
  exact Module.finrank_pos

/-- On a reduced connected curve proper over `k`, `[H⁰(Z, 𝒪_Z) : k]` divides the degree of every
invertible sheaf. -/
private theorem finrank_unit_dvd_invertibleCurveDegree [IsProper sZ] [IsReduced Z]
    [ConnectedSpace Z] (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    (Module.finrank k (cohomologyOverField k sZ (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ) ∣
      invertibleCurveDegree k sZ hdim L := by
  have key : ∀ (F : Z.Modules) (n : ℕ),
      (Module.finrank k (cohomologyOverField k sZ (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ) ∣
        (-1) ^ n * (Module.finrank k (cohomologyOverField k sZ F n) : ℤ) := fun F n =>
    Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr
      (finrank_unit_dvd_finrank_cohomologyOverField k sZ F n)) _
  exact dvd_sub (dvd_finsum_of_forall_dvd (key L)) (dvd_finsum_of_forall_dvd (key _))

/-- On a scheme of dimension at most one proper over `k`, `χ(F) = h⁰(F) - h¹(F)`. -/
private theorem eulerCharacteristic_eq_sub [IsProper sZ] (hdim : topologicalKrullDim Z ≤ 1)
    (F : Z.Modules) [F.IsCoherent] :
    eulerCharacteristic k sZ F = Module.finrank k (cohomologyOverField k sZ F 0) -
      Module.finrank k (cohomologyOverField k sZ F 1) := by
  have hsupp : topologicalKrullDim (SheafOfModules.supp F) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le Z _).trans (by exact_mod_cast hdim)
  have hz : ∀ n, 2 ≤ n → Module.finrank k (cohomologyOverField k sZ F n) = 0 := by
    intro n hn
    have h := isZero_cohomologyOverField_of_topologicalKrullDim_supp_le k sZ F hsupp
      (by omega : 1 < n)
    have := ModuleCat.isZero_iff_subsingleton.mp h
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic, finsum_eq_sum_of_support_subset (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
    ring
  · intro n hn
    simp only [Function.mem_support] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hn (by rw [hz n (by omega)]; simp)

variable {k} {S Y : Scheme.{u}}

/-- A prime divisor of `Y` lying over a point `x` of `S` has its generic point over `x`. -/
private theorem map_genericPoint_eq_of_support_subset {f : Y ⟶ S} {x : S}
    {E : MMP.Mori.PrimeDivisor Y} (hE : E.support ⊆ f.base ⁻¹' {x}) : f E.genericPoint = x :=
  hE (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)

/-- On a surface integral and locally of finite type over `k`, the closure of the generic point
of a prime divisor is one-dimensional. -/
private theorem topologicalKrullDim_closure_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) (Γ : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim (closure {Γ.genericPoint} : Set Y) = 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY Γ.genericPoint
  rw [Γ.coheight_genericPoint, hdim] at h
  exact ENat.WithBot.add_one_cancel.mp h

/-- On a surface locally of finite type over `k`, a prime divisor is a curve. -/
private theorem topologicalKrullDim_idealSheaf_subscheme (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hdim : topologicalKrullDim Y = 2) (E : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim E.idealSheaf.subscheme = 1 := by
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
  change topologicalKrullDim (E.support : Set Y) = 1
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact topologicalKrullDim_closure_genericPoint sY hdim E

/-- A prime divisor of `Y` lying over a closed point of `S` is proper over `k`. -/
private theorem isProper_idealSheaf_subschemeι (sS : S ⟶ Spec (.of k)) (f : Y ⟶ S)
    [LocallyOfFiniteType sS] [IsProper f] [IsLocallyNoetherian Y] [IsNormal Y]
    {x : S} (hx : IsClosed ({x} : Set S)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.support ⊆ f.base ⁻¹' {x}) :
    IsProper (E.idealSheaf.subschemeι ≫ f ≫ sS) := by
  have := E.integral
  have := MMP.Mori.isProper_comp_of_range_subset_singleton sS (E.idealSheaf.subschemeι ≫ f) hx
    (by
      rintro _ ⟨z, rfl⟩
      have hz : E.idealSheaf.subschemeι z ∈ (E.support : Set Y) := by
        change _ ∈ (E.idealSheaf.support : Set Y)
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨z, rfl⟩
      exact hE hz)
  rwa [Category.assoc] at this

/-- A prime divisor of a surface `Y` lying over a closed point of `S` is a proper curve of `Y`
contracted by `f`. -/
private theorem exists_properCurve (sS : S ⟶ Spec (.of k)) (f : Y ⟶ S)
    [LocallyOfFiniteType sS] [IsProper f] [IsIntegral Y] [LocallyOfFiniteType (f ≫ sS)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hdim : topologicalKrullDim Y = 2)
    {x : S} (hx : IsClosed ({x} : Set S)) (E : MMP.Mori.PrimeDivisor Y)
    (hE : E.support ⊆ f.base ⁻¹' {x}) :
    ∃ C : ProperCurve (f ≫ sS), C.point = E.genericPoint ∧ C.IsContractedBy f := by
  have h := vanishingIdeal_closure_genericPoint_eq_idealSheaf E
  have hcl : closure ({E.genericPoint} : Set Y) = E.support :=
    (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  refine ⟨⟨E.genericPoint, ⟨?_, ?_⟩⟩, rfl, fun z hz => ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal _).subscheme = 1
    rw [h]; exact topologicalKrullDim_idealSheaf_subscheme (f ≫ sS) hdim E
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ f ≫ sS)
    rw [h]; exact isProper_idealSheaf_subschemeι sS f hx E hE
  · change z ∈ closure ({E.genericPoint} : Set Y) at hz
    rw [hcl] at hz
    exact (hE hz).trans (map_genericPoint_eq_of_support_subset hE).symm

section Linear

variable {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
  (hsm : IsSmoothScheme sY) (C : ProperCurve sY)

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A `ℚ`-divisor supported on one prime divisor is a multiple of that prime divisor. -/
private theorem single_eq_smul (P : MMP.Mori.PrimeDivisor Y) (q : ℚ) :
    (Finsupp.single P q : QDivisor Y) = q • Divisor.toQDivisor (Finsupp.single P 1) := by
  ext F
  rcases eq_or_ne P F with rfl | hF <;>
    simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]

/-- **Intersection numbers on a smooth scheme are linear in the coefficients.** Every
`ℚ`-divisor `D` has `(D · C) = ∑_P coeff_P(D) (P · C)`. -/
private theorem intersectionNumber_eq_sum (D : QDivisor Y) (hD : D.IsQCartier) :
    D.intersectionNumber k sY C.ι C.dim_le hD = D.sum fun P q => q *
      (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sY C.ι C.dim_le
        (isQCartier_of_isSmoothScheme hsm _) := by
  induction D using Finsupp.induction_linear with
  | zero =>
    rw [MMP.Fourfold.intersectionNumber_zero sY C.ι C.dim_le, Finsupp.sum_zero_index]
  | add D₁ D₂ h₁ h₂ =>
    rw [QDivisor.intersectionNumber_add' k sY C.ι C.dim_le D₁ D₂
      (isQCartier_of_isSmoothScheme hsm _) (isQCartier_of_isSmoothScheme hsm _) hD, h₁, h₂,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single P q =>
    rw [Finsupp.sum_single_index (zero_mul _),
      MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le hD
        (isQCartier_of_isSmoothScheme hsm _) (single_eq_smul P q),
      MMP.Fourfold.intersectionNumber_smul sY C.ι C.dim_le _ (isQCartier_of_isSmoothScheme hsm _)
        q (isQCartier_of_isSmoothScheme hsm _)]

/-- `intersectionNumber_eq_sum` as a real linear functional: with `n(P) = (P · C)`, every
`ℚ`-divisor `D` has `(D · C) = ∑_P coeff_P(D) n(P)`. -/
private theorem intersectionNumber_eq_linearCombination (D : QDivisor Y) (hD : D.IsQCartier) :
    (D.intersectionNumber k sY C.ι C.dim_le hD : ℝ) =
      Finsupp.linearCombination ℝ (fun P : MMP.Mori.PrimeDivisor Y =>
        ((Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sY C.ι C.dim_le
          (isQCartier_of_isSmoothScheme hsm _) : ℝ)) (QDivisor.toRDivisor D) := by
  rw [intersectionNumber_eq_sum hsm C D hD, Finsupp.linearCombination_apply,
    show QDivisor.toRDivisor D = Finsupp.mapRange (Rat.cast : ℚ → ℝ) Rat.cast_zero D from rfl,
    Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, Rat.cast_sum, Rat.cast_mul, smul_eq_mul]

/-- The integral version of `intersectionNumber_eq_linearCombination`. -/
private theorem intersectionNumber_toQDivisor_eq_linearCombination (D : Divisor Y)
    (hD : (Divisor.toQDivisor D).IsQCartier) :
    ((Divisor.toQDivisor D).intersectionNumber k sY C.ι C.dim_le hD : ℝ) =
      Finsupp.linearCombination ℝ (fun P : MMP.Mori.PrimeDivisor Y =>
        ((Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sY C.ι C.dim_le
          (isQCartier_of_isSmoothScheme hsm _) : ℝ)) (Divisor.toRDivisor D) := by
  rw [intersectionNumber_eq_linearCombination hsm C]
  congr 1
  ext P
  change ((D P : ℚ) : ℝ) = (D P : ℝ)
  push_cast; rfl

/-- Linearly equivalent divisors on a smooth scheme have the same intersection number with a
proper curve. -/
private theorem intersectionNumber_toQDivisor_eq_of_linearlyEquivalent [CompactSpace Y]
    {K K' : Divisor Y} (hlin : K'.LinearlyEquivalent K) :
    (Divisor.toQDivisor K').intersectionNumber k sY C.ι C.dim_le
        (isQCartier_of_isSmoothScheme hsm _) =
      (Divisor.toQDivisor K).intersectionNumber k sY C.ι C.dim_le
        (isQCartier_of_isSmoothScheme hsm _) := by
  have hc' := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm K'
  have hc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm K
  rw [QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le _ hc',
    QDivisor.intersectionNumber_toQDivisor k sY C.ι C.dim_le _ hc]
  have := hc'.isInvertibleModule_divisorialSheaf
  have := hc.isInvertibleModule_divisorialSheaf
  have e : K'.degreeOn k sY C.ι C.dim_le hc' = K.degreeOn k sY C.ι C.dim_le hc :=
    degreeOn_eq_of_iso k sY C.ι C.dim_le hlin.divisorialSheafIso
  rw [e]

end Linear

section Pullback

variable {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
  [CompactSpace S] [MMP.Mori.IsVariety k sS] {f : Y ⟶ S} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [QuasiCompact (f ≫ sS)] [MMP.Mori.IsVariety k (f ≫ sS)]

omit [IsIntegral S] [MMP.Mori.IsVariety k (f ≫ sS)] in
/-- **Pull-backs are numerically trivial on contracted curves.** If `L'` is the pull-back of a
Cartier divisor `L` of `S` and `C` is a proper curve of `Y` contracted by `f`, then
`(L' · C) = 0`. -/
private theorem intersectionNumber_pullback_eq_zero {L : Divisor S} {L' : Divisor Y}
    (hL : L.IsCartier)
    (hpb : ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback f hB L') (C : ProperCurve (f ≫ sS)) (hC : C.IsContractedBy f)
    (hL' : (Divisor.toQDivisor L').IsQCartier) :
    (Divisor.toQDivisor L').intersectionNumber k (f ≫ sS) C.ι C.dim_le hL' = 0 := by
  have hL'c := hpb.choose_spec.isCartier hL
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  have := C.isCurve
  have := hL.isInvertibleModule_divisorialSheaf
  have := hL'c.isInvertibleModule_divisorialSheaf
  have hpt : ∃ w : S, Set.range (C.ι ≫ f) = {w} := ⟨f C.point, by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact hC _ (C.range_ι ▸ ⟨c, rfl⟩)
    · rintro rfl
      exact ⟨genericPoint C.scheme, by simp [C.ι_genericPoint]⟩⟩
  have e : (C.ι ≫ f) ≫ sS = C.ι ≫ f ≫ sS := Category.assoc _ _ _
  have : IsProper ((C.ι ≫ f) ≫ sS) := by rw [e]; exact C.isProper_ι_comp
  have : MMP.Mori.IsCurve k ((C.ι ≫ f) ≫ sS) := by rw [e]; infer_instance
  rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sS) C.ι C.dim_le _ hL'c, Divisor.degreeOn,
    degreeOn_eq_of_iso k (f ≫ sS) C.ι _ (hpb.choose_spec.divisorialSheafIso (hBc := hL)),
    degreeOn_pullback_eq_degreeOn_comp (f ≫ sS) sS f C.ι rfl,
    degreeOn_eq_zero_of_range_eq_singleton sS (C.ι ≫ f) _ hpt]
  simp

end Pullback

section Transform

open MMP.Flips TopologicalSpace

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX g τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← repr_pullbackFormsAlong hω m τ, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
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

/-- The transform of a prime divisor `P` under a rational map defined at its generic point is the
closure of the image of that generic point. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
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

/-- A rational map defined at the generic point of `P` and sending it to the generic point of `E`
transforms `P` into `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  change _ = Scheme.IdealSheafData.vanishingIdeal (MMP.Mori.RationalMap.transform φ _)
  rw [h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) (E : MMP.Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := MMP.Mori.RationalMap.IsBirational.inverse hf with hg_def
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- Two maps on prime divisors which agree on the support of a `ℚ`-divisor `D` have the same
linear extension on `D`, compatibly with `ℚ ⊆ ℝ`. -/
private theorem mapPrimeDivisors_toRDivisor_eq {X Y : Scheme.{u}}
    {φ ψ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)} (D : QDivisor X)
    (h : ∀ C ∈ D.support, φ C = ψ C) :
    DivisorWithCoeffs.mapPrimeDivisors φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (DivisorWithCoeffs.mapPrimeDivisors ψ D) := by
  have hs : ∀ (C : MMP.Mori.PrimeDivisor X) (q : ℚ),
      QDivisor.toRDivisor (Finsupp.single C q) = Finsupp.single C (q : ℝ) := fun C q =>
    Finsupp.mapRange_single (hf := map_zero _)
  have hs' : ∀ (o : Option (MMP.Mori.PrimeDivisor Y)) (q : ℚ),
      QDivisor.toRDivisor (o.elim 0 (Finsupp.single · q)) = o.elim 0 (Finsupp.single · (q : ℝ)) :=
    fun o q => by
      cases o
      · simp
      · exact Finsupp.mapRange_single (hf := map_zero _)
  classical
  revert h
  induction D using Finsupp.induction with
  | zero => intro; simp
  | single_add a b f ha hb ih =>
    intro h
    rw [Finsupp.support_single_add ha hb] at h
    rw [map_add, map_add, map_add, ih (fun C hC => h C (Finset.mem_cons_of_mem hC)), hs,
      DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single,
      h a (Finset.mem_cons_self _ _), map_add QDivisor.toRDivisor, hs']

/-- On a surface integral and locally of finite type over `k`, the generic point of a prime
divisor is not a closed point. -/
private theorem not_isClosed_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) (Γ : MMP.Mori.PrimeDivisor Y) :
    ¬ IsClosed ({Γ.genericPoint} : Set Y) := fun hcl => by
  have h := topologicalKrullDim_closure_genericPoint sY hdim Γ
  rw [hcl.closure_eq] at h
  have := topologicalKrullDim_zero_of_discreteTopology ({Γ.genericPoint} : Set Y)
  rw [h] at this
  exact absurd this (by decide)

variable {sS : S ⟶ Spec (.of k)} {f : Y ⟶ S}

/-- The generic point of a prime divisor of a normal variety `S` lies in the biregular locus of a
proper birational morphism `f : Y ⟶ S` of varieties. -/
private theorem genericPoint_mem_biregularLocus [IsNormal S] (hS : MMP.Mori.IsVariety k sS)
    (hY : MMP.Mori.IsVariety k (f ≫ sS)) [IsProper f] (hf : IsBirationalMorphism f)
    (P : MMP.Mori.PrimeDivisor S) : P.genericPoint ∈ biregularLocus f := by
  have h := two_le_closedsCodimension_compl_biregularLocus sS f (hY := hS) (hX := hY) hf
  by_contra hP
  have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h) P.genericPoint hP
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- The birational transform `f⁻¹_*` of `ℝ`-divisors along the inverse of the birational map
agrees with the inverse transform of `ℚ`-divisors. -/
private theorem birationalInverseTransform_toRDivisor [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hS : IsNormalVariety k sS) (hY : IsNormalVariety k (f ≫ sS)) [IsProper f]
    (hf : IsBirationalMorphism f) (D : QDivisor S) :
    birationalInverseTransform f hf (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (inverseTransformDivisor f D) := by
  refine mapPrimeDivisors_toRDivisor_eq D fun C _ => ?_
  obtain ⟨Γ, hΓ, hηΓ⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some C
    (genericPoint_mem_biregularLocus hS.1 hY.1 hf C)
  rw [transformPrimeDivisor_inverse_eq_some hS f hY hf C Γ hηΓ, hΓ]

/-- The coefficient of `P` in the linear extension of a partial map `φ` on prime divisors is `0`
when no prime divisor is sent to `P`. -/
private theorem mapPrimeDivisors_apply_eq_zero_of_forall_ne {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {P : MMP.Mori.PrimeDivisor Y} (h : ∀ E, φ E ≠ some P) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ D P = 0 := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hE : φ E with _ | E'
    · rfl
    · have hne : E' ≠ P := fun he => h E (by rw [hE, he])
      exact Finsupp.single_eq_of_ne' hne

/-- The inverse transform of a divisor with nonnegative coefficients has nonnegative
coefficients. -/
private theorem mapPrimeDivisors_nonneg {X Y : Scheme.{u}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : QDivisor X)
    (hD : ∀ P, 0 ≤ D P) (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ DivisorWithCoeffs.mapPrimeDivisors φ D P := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | single_add a b g ha hb ih =>
    have hga : g a = 0 := Finsupp.notMem_support_iff.mp ha
    have hb0 : 0 ≤ b := by simpa [hga] using hD a
    have hg : ∀ Q, 0 ≤ g Q := fun Q => by
      by_cases hQ : Q = a
      · subst hQ; rw [hga]
      · have := hD Q
        simpa [Finsupp.single_apply, Ne.symm hQ] using this
    rw [map_add, Finsupp.add_apply, DivisorWithCoeffs.mapPrimeDivisors_single]
    refine add_nonneg ?_ (ih hg)
    rcases φ a with _ | E'
    · simp
    · simp only [Option.elim_some, Finsupp.single_apply]
      split_ifs <;> simp [hb0]

end Transform

section Exceptional

open MMP.Flips

variable {sS : S ⟶ Spec (.of k)} {f : Y ⟶ S}

/-- On a surface `S`, an exceptional prime divisor of `f : Y ⟶ S` lies over a closed point. -/
private theorem isClosed_singleton_of_isExceptionalPrimeDivisor [IsIntegral S]
    [LocallyOfFiniteType sS] [CompactSpace S] (hS2 : topologicalKrullDim S = 2)
    {E : MMP.Mori.PrimeDivisor Y} (h : IsExceptionalPrimeDivisor sS f E) :
    IsClosed ({f E.genericPoint} : Set S) := by
  obtain ⟨_, _, _, hexc⟩ := h
  set x := f E.genericPoint
  have hx : topologicalKrullDim (closure {x} : Set S) + 2 ≤ 2 := by
    unfold ProperDivisorOver.IsExceptional at hexc
    rwa [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hS2] at hexc
  by_contra hn
  obtain ⟨c, -, hxc, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hn
  have h1 := one_le_topologicalKrullDim_of_specializes_of_ne
    (x := (⟨x, subset_closure rfl⟩ : closure ({x} : Set S)))
    (y := ⟨c, specializes_iff_mem_closure.mp hxc⟩) ((subtype_specializes_iff _ _).mpr hxc)
    (fun h => hne (congrArg Subtype.val h))
  exact absurd ((add_le_add h1 (le_refl (2 : WithBot ℕ∞))).trans hx) (by decide)

/-- A prime divisor of `Y` lies over the closure of the image of its generic point. -/
private theorem map_mem_closure_of_mem_support (E : MMP.Mori.PrimeDivisor Y) {z : Y}
    (hz : z ∈ E.support) : f z ∈ closure ({f E.genericPoint} : Set S) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
  exact specializes_iff_mem_closure.mp
    ((specializes_iff_mem_closure.mpr hz).map f.continuous)

/-- On a surface `S`, an exceptional prime divisor of `f : Y ⟶ S` other than the prime divisors
`E_i` over a closed point `x` is disjoint from each `E_i`. -/
private theorem disjoint_support_closure_of_isExceptionalPrimeDivisor [IsIntegral S]
    [LocallyOfFiniteType sS] [CompactSpace S] (hS2 : topologicalKrullDim S = 2) {x : S}
    {s : ℕ} {E : Fin s → MMP.Mori.PrimeDivisor Y} (hEx : ∀ i, (E i).support ⊆ f.base ⁻¹' {x})
    (hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P)
    {P : MMP.Mori.PrimeDivisor Y} (hexc : IsExceptionalPrimeDivisor sS f P)
    (hne : ∀ i, E i ≠ P) (j : Fin s) :
    Disjoint (P.support : Set Y) (closure {(E j).genericPoint}) := by
  have hcl := isClosed_singleton_of_isExceptionalPrimeDivisor hS2 hexc
  have hsub : ∀ z ∈ P.support, f z = f P.genericPoint := fun z hz => by
    have := map_mem_closure_of_mem_support (f := f) P hz
    rwa [hcl.closure_eq] at this
  have hy : f P.genericPoint ≠ x := by
    intro hyx
    obtain ⟨i, hi⟩ := hEall P fun z hz => by
      change f z ∈ ({x} : Set S)
      rw [hsub z hz, hyx]
      rfl
    exact hne i hi
  rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact Set.disjoint_left.mpr fun z hzP hzE => hy (by rw [← hsub z hzP]; exact hEx j hzE)

end Exceptional

section Adjunction

/-- The reduced subscheme on the support of the divisor of a prime divisor `E` is `E`. -/
private theorem suppIdeal_single_one [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = E.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E]
  change Scheme.IdealSheafData.vanishingIdeal _ = _
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E, DivisorWithCoeffs.coe_supp]
  rw [Finsupp.support_single _ one_ne_zero]
  simp

open MMP.Threefold in
/-- **Adjunction on a smooth surface over a perfect field.** For a prime divisor `E` proper over
`k`, `((K + E) · E) = -2 χ(𝒪_E) = -2 (h⁰(𝒪_E) - h¹(𝒪_E))`. -/
private theorem isIntersectionNumber_canonical_add_single [PerfectField k]
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2) (E : MMP.Mori.PrimeDivisor Y)
    (hpr : IsProper (E.idealSheaf.subschemeι ≫ sY)) :
    IsIntersectionNumber sY (Divisor.toQDivisor K + Finsupp.single E 1) E.idealSheaf
      (-2 * ((Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ sY)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 0) : ℚ) -
        Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ sY)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1))) := by
  have : IsIntegral Y := hY.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hI := suppIdeal_single_one E
  have hC : ∀ F ∈ (Finsupp.single E (1 : ℤ) : Divisor Y).support,
      (Finsupp.single E (1 : ℤ) : Divisor Y) F = 1 := by
    intro F hF
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hF
    rw [hF, Finsupp.single_eq_same]
  have hpr' : IsProper ((DivisorWithCoeffs.suppIdeal
      (Finsupp.single E (1 : ℤ) : Divisor Y)).subschemeι ≫ sY) := by
    rw [hI]; exact hpr
  have hdim : topologicalKrullDim (DivisorWithCoeffs.suppIdeal
      (Finsupp.single E (1 : ℤ) : Divisor Y)).subscheme ≤ 1 := by
    rw [hI]; exact (topologicalKrullDim_idealSheaf_subscheme sY hYd E).le
  have h :=
    isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic_of_perfectField
    hY hYs hYd hK _ hC hpr'
  rw [map_add, MMP.Threefold.Resolution.toQDivisor_single] at h
  revert h hpr' hdim
  generalize DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = I at hI ⊢
  subst hI
  intro _ hdim h
  convert h using 1
  · have := hpr
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ sY)
    have he := eulerCharacteristic_eq_sub k (E.idealSheaf.subschemeι ≫ sY) hdim
      (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf)
    have he' : ((eulerCharacteristic k (E.idealSheaf.subschemeι ≫ sY)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) : ℤ) : ℚ) =
        (Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ sY)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 0) : ℚ) -
        Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ sY)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1) := by
      exact_mod_cast he
    linear_combination 2 * he'

end Adjunction

section Aux

variable {k : Type u} [Field k] {S Y : Scheme.{u}}

/-- The inverse transform of a divisor of a surface `S` has no component over a closed point. -/
private theorem inverseTransformDivisor_apply_eq_zero_of_support_subset {sS : S ⟶ Spec (.of k)}
    [IsIntegral S] [LocallyOfFiniteType sS] [IsLocallyNoetherian S] [IsNormal S]
    (hS2 : topologicalKrullDim S = 2) {f : Y ⟶ S} {x : S} (hx : IsClosed ({x} : Set S))
    (D : QDivisor S) {E : MMP.Mori.PrimeDivisor Y} (hE : E.support ⊆ f.base ⁻¹' {x}) :
    inverseTransformDivisor f D E = 0 := by
  refine mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun Q hQ => ?_) D
  obtain ⟨hη, -⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ
  exact not_isClosed_genericPoint sS hS2 Q
    (by rw [← hη, map_genericPoint_eq_of_support_subset hE]; exact hx)

/-- The `k`-dimensions of the cohomology of the structure sheaves of equal closed subschemes
agree. -/
private theorem finrank_cohomologyOverField_unit_congr (sY : Y ⟶ Spec (.of k))
    {I J : Y.IdealSheafData} (h : I = J) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (I.subschemeι ≫ sY)
        (SheafOfModules.unit I.subscheme.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k (J.subschemeι ≫ sY)
        (SheafOfModules.unit J.subscheme.ringCatSheaf) n) := by
  subst h; rfl

end Aux

section Main

open MMP.Flips

/-- A linear combination `∑ R P • n P` is the sum over an injective family `E` when `n` vanishes
on the rest of the support of `R`. -/
private theorem linearCombination_eq_sum_of_injective {α ι : Type*} [Fintype ι] (R : α →₀ ℝ)
    (n : α → ℝ) {E : ι → α} (hE : Function.Injective E)
    (h : ∀ P, R P ≠ 0 → (∀ i, E i ≠ P) → n P = 0) :
    Finsupp.linearCombination ℝ n R = ∑ i, R (E i) • n (E i) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  set T := Finset.univ.image E
  have e1 : ∑ P ∈ R.support, R P • n P = ∑ P ∈ R.support ∪ T, R P • n P :=
    Finset.sum_subset Finset.subset_union_left fun P _ hP => by
      rw [Finsupp.notMem_support_iff.mp hP, zero_smul]
  have e2 : ∑ P ∈ T, R P • n P = ∑ P ∈ R.support ∪ T, R P • n P :=
    Finset.sum_subset Finset.subset_union_right fun P hP hPT => by
      rw [h P (Finsupp.mem_support_iff.mp ((Finset.mem_union.mp hP).resolve_right hPT))
        fun i hi => hPT (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩), smul_zero]
  rw [e1, ← e2, Finset.sum_image fun i _ i' _ h => hE h]

/-- **The intersection equation of the discrepancy formula.** Let `(S, B)` be a pair on a
surface over a field of characteristic zero, `f : Y ⟶ S` a resolution, `K` a canonical divisor of
`Y`, `E_1, …, E_s` the prime divisors of `Y` over a closed point `x`, with log discrepancies
`α_i`, and `C_i` the proper curves with the generic points of the `E_i`. Then for every `j`,
`∑_i (α_i - 1) (E_i · C_j) = (K · C_j) + (f⁻¹_* B · C_j)`. -/
private theorem sum_mul_intersectionNumber_eq {k : Type u} [Field k] [CharZero k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] {B : QDivisor S} (hBp : MMP.Mori.IsPair sS B)
    (hS2 : topologicalKrullDim S = 2) {x : S} (hx : IsClosed ({x} : Set S))
    {f : Y ⟶ S} [QuasiCompact (f ≫ sS)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : MMP.Mori.IsVariety k (f ≫ sS)) (hres : IsSmoothResolution sS f)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor (f ≫ sS) 2)
    {s : ℕ} (E : Fin s → MMP.Mori.PrimeDivisor Y)
    (hEx : ∀ i, (E i).support ⊆ f.base ⁻¹' {x})
    (hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P)
    (hEinj : Function.Injective E) (α : Fin s → ℝ)
    (hα : ∀ i, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B)
      ⟨Y, f, ⟨hYv, inferInstance⟩, hres.isBirationalMorphism, E i⟩ (α i))
    (C : Fin s → ProperCurve (f ≫ sS)) (hC : ∀ i, (C i).point = (E i).genericPoint)
    (hCc : ∀ i, (C i).IsContractedBy f) (j : Fin s) :
    ∑ i, (α i - 1) * ((Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k
        (f ≫ sS) (C j).ι (C j).dim_le (isQCartier_of_isSmoothScheme hres.isSmoothScheme _) : ℝ) =
      ((Divisor.toQDivisor K).intersectionNumber k (f ≫ sS) (C j).ι (C j).dim_le
          (isQCartier_of_isSmoothScheme hres.isSmoothScheme _) : ℝ) +
        (QDivisor.intersectionNumber k (f ≫ sS) (C j).ι (C j).dim_le
          (inverseTransformDivisor f B)
          (isQCartier_of_isSmoothScheme hres.isSmoothScheme _) : ℝ) := by
  classical
  have hsm := hres.isSmoothScheme
  have : IsProper f := hres.isProper
  have hf := hres.isBirationalMorphism
  have hSn : IsNormalVariety k sS := hBp.1
  have : IsIntegral Y := hYv.toIsIntegral
  have hYn : IsNormalVariety k (f ≫ sS) := ⟨hYv, inferInstance⟩
  have : MMP.Mori.IsVariety k sS := hSn.1
  have := hYv
  have : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sS) := hYv.toLocallyOfFiniteType
  have : QuasiCompact sS := inferInstance
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  have : IsDominant f := hf.isDominant
  -- a rational top form `ω` on `S` and a presentation of `K_S + B`, from `hα j`
  obtain ⟨-, -, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m, r, Cc, -, hCcart, hdec, -, -⟩ := hα j
  have hdivω : divisorOfForm ω = K₀ :=
    DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hK₀ω]
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sS 2 := hdivω ▸ hK₀
  obtain ⟨Ex, a', G, hEx', ⟨m', r', L, L', hLc, hLdec, hLpb, rfl⟩, -, heq⟩ :=
    discrepancy_formula hSn (QDivisor.toRDivisor B) ω hω0 hKω
      ⟨m, r, Cc, hCcart, (toRDivisor_divisorOfForm_add_eq_sum_iff ω _ r Cc).2 hdec⟩ f hYn hf
  have hLdec' := (toRDivisor_divisorOfForm_add_eq_sum_iff ω _ r' L).1 hLdec
  rw [birationalInverseTransform_toRDivisor hSn hYn hf B] at heq
  set K' := divisorOfForm (pullbackRationalPluriForms sS f ω) with hK'
  set R : RDivisor Y := ∑ E ∈ Ex, Finsupp.single E (a' E) with hR
  -- the log discrepancies in terms of the presentation `(r', L, L')`
  have hαi : ∀ i, α i = 1 + (K' (E i) : ℝ) - ∑ l, r' l * (L' l (E i) : ℝ) := by
    intro i
    refine MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hα i)
      ⟨hSn, inferInstance, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m', r', L, L', hLc, hLdec', hLpb, ?_⟩
    change _ = 1 + ((E i).ordForm (pullbackRationalPluriForms sS f ω) : ℝ) - _
    rw [← coeff_divisorOfForm]
    rfl
  -- the inverse transform of `B` has no component over `x`
  have hB0 : ∀ i, inverseTransformDivisor f B (E i) = 0 := fun i =>
    inverseTransformDivisor_apply_eq_zero_of_support_subset (sS := sS) hS2 hx B (hEx i)
  -- the coefficients of the exceptional part
  have hRi : ∀ i, R (E i) = α i - 1 := by
    intro i
    have h := congrArg (fun F : RDivisor Y => F (E i)) heq
    simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h
    have h1 : (QDivisor.toRDivisor (inverseTransformDivisor f B)) (E i) = 0 := by
      change ((inverseTransformDivisor f B (E i) : ℚ) : ℝ) = 0
      rw [hB0 i, Rat.cast_zero]
    rw [h1, add_zero] at h
    rw [hαi i]
    change R (E i) = 1 + ((K' (E i) : ℤ) : ℝ) - _ - 1
    have h2 : (Divisor.toRDivisor K') (E i) = ((K' (E i) : ℤ) : ℝ) := rfl
    have h3 : ∀ l, (Divisor.toRDivisor (L' l)) (E i) = ((L' l (E i) : ℤ) : ℝ) := fun l => rfl
    simp only [h2, h3] at h
    rw [hR] at h ⊢
    linarith
  -- the degrees `n(P) = (P · C_j)` and the linear functional they define
  set n : MMP.Mori.PrimeDivisor Y → ℝ := fun P =>
    ((Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (f ≫ sS) (C j).ι
      (C j).dim_le (isQCartier_of_isSmoothScheme hsm _) : ℝ) with hn
  -- prime divisors exceptional over other points do not meet `C_j`
  have hnEx : ∀ P ∈ Ex, (∀ i, E i ≠ P) → n P = 0 := by
    intro P hP hne
    have hdisj := disjoint_support_closure_of_isExceptionalPrimeDivisor hS2 hEx hEall
      ((hEx' P).mp hP) hne j
    rw [← hC j] at hdisj
    simp only [hn]
    rw [MMP.Threefold.Resolution.intersectionNumber_single_eq_zero_of_disjoint hsm P (C j) hdisj,
      Rat.cast_zero]
  set ℓ := Finsupp.linearCombination ℝ n with hℓ
  have h := congrArg ℓ heq
  rw [map_add, map_add, map_sum] at h
  have h1 : ℓ (Divisor.toRDivisor K') = ((Divisor.toQDivisor K').intersectionNumber k (f ≫ sS)
      (C j).ι (C j).dim_le (isQCartier_of_isSmoothScheme hsm _) : ℝ) :=
    (intersectionNumber_toQDivisor_eq_linearCombination hsm (C j) K' _).symm
  have h2 : ℓ (QDivisor.toRDivisor (inverseTransformDivisor f B)) =
      (QDivisor.intersectionNumber k (f ≫ sS) (C j).ι (C j).dim_le (inverseTransformDivisor f B)
        (isQCartier_of_isSmoothScheme hsm _) : ℝ) :=
    (intersectionNumber_eq_linearCombination hsm (C j) _ _).symm
  have h3 : ∀ l, ℓ (r' l • Divisor.toRDivisor (L' l)) = 0 := by
    intro l
    rw [map_smul, hℓ, ← intersectionNumber_toQDivisor_eq_linearCombination hsm (C j) (L' l)
      (isQCartier_of_isSmoothScheme hsm _),
      intersectionNumber_pullback_eq_zero (hLc l) (hLpb l) (C j) (hCc j), Rat.cast_zero,
      smul_zero]
  have h4 : ℓ R = ∑ i, (α i - 1) * n (E i) := by
    have hRsupp : ∀ P, R P ≠ 0 → P ∈ Ex := by
      intro P hP
      by_contra hPEx
      apply hP
      rw [hR, Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun E' hE' =>
        Finsupp.single_eq_of_ne' (fun h => hPEx (h ▸ hE'))
    rw [hℓ, linearCombination_eq_sum_of_injective R n hEinj fun P hP => hnEx P (hRsupp P hP)]
    exact Finset.sum_congr rfl fun i _ => by rw [hRi i, smul_eq_mul]
  rw [h1, h2, h4] at h
  simp only [h3, Finset.sum_const_zero, zero_add] at h
  -- `K'` and `K` are linearly equivalent, so they have the same degree on `C_j`
  have hlin : K'.LinearlyEquivalent K := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hK
      (pullbackRationalPluriForms_ne_zero sS (d := 2) (by rw [hS2]; rfl) f hf hω0)
    rwa [one_smul] at this
  rw [intersectionNumber_toQDivisor_eq_of_linearlyEquivalent hsm (C j) hlin] at h
  linarith

end Main

/-- **The normalized exceptional matrix.** For a pair `(S, B)` over a field of characteristic
zero, a closed point `x`, a projective resolution `f : Y ⟶ S` with `K_Y` nef over `S`, and the
prime divisors `E_1, …, E_s` of `Y` over `x` with positive log discrepancies `α_i`, the matrix
`M'_{ij} = (E_i · E_j) / d_i`, `d_i = dim_k H⁰(E_i, 𝒪_{E_i})`, is integral and nonsingular,
`0 < α_i ≤ 1`, `α_i (-M'_{ii}) ≤ 2`, and `M' (α - 1) ∈ (1/q) ℤ^s` when `qB` is integral. -/
private theorem exists_int_normalized_intersectionMatrix
    {k : Type u} [Field k] {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    {B : QDivisor S} (hB : IsCharZeroPair sS B) (hS2 : topologicalKrullDim S = 2)
    {x : S} (hx : IsClosed ({x} : Set S))
    {f : Y ⟶ S} [QuasiCompact (f ≫ sS)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : MMP.Mori.IsVariety k (f ≫ sS)) (hres : IsSmoothResolution sS f)
    (hKnef : ∃ K : Divisor Y, K.IsCanonicalDivisor (f ≫ sS) 2 ∧
      (Divisor.toQDivisor K).IsRelativelyNef (f ≫ sS) f)
    {s : ℕ} (E : Fin s → MMP.Mori.PrimeDivisor Y) (hEinj : Function.Injective E)
    (hEx : ∀ i, (E i).support ⊆ f.base ⁻¹' {x})
    (hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P)
    (α : Fin s → ℝ)
    (hα : ∀ i, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B)
      ⟨Y, f, ⟨hYv, inferInstance⟩, hres.isBirationalMorphism, E i⟩ (α i))
    (hαpos : ∀ i, 0 < α i) :
    let d : Fin s → ℕ := fun i => Module.finrank k
      (cohomologyOverField k ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
        (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 0)
    let g : Fin s → ℝ := fun i => (Module.finrank k
      (cohomologyOverField k ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
        (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 1) : ℝ) / d i
    ∃ (M : Matrix (Fin s) (Fin s) ℤ) (β : Fin s → ℚ),
      (∀ i j, IsIntersectionNumber (f ≫ sS) (Divisor.toQDivisor (Finsupp.single (E i) 1))
        (E j).idealSheaf (d i * M i j)) ∧
      (∀ i, IsIntersectionNumber (f ≫ sS) (inverseTransformDivisor f B) (E i).idealSheaf
        (β i)) ∧
      (∀ i, 0 < α i ∧ α i ≤ 1) ∧
      M.det ≠ 0 ∧ (∀ i, 1 ≤ -M i i) ∧ (∀ i j, i ≠ j → 0 ≤ M i j) ∧
      (∀ i, α i * (-M i i : ℝ) =
          2 - 2 * g i - (β i : ℝ) / d i - ∑ j ∈ Finset.univ.erase i, (1 - α j) * (M i j : ℝ) ∧
        α i * (-M i i : ℝ) ≤ 2) ∧
      ∀ q : ℕ, 0 < q → (∀ P, ∃ n : ℤ, (q : ℚ) * B P = n) →
        ∀ i, ∃ n : ℤ, ∑ j, (M i j : ℝ) * (α j - 1) = n / q := by
  intro d g
  classical
  have : CharZero k := hB.charZero
  obtain ⟨K, hK, hKn⟩ := hKnef
  have hsm := hres.isSmoothScheme
  have : IsProper f := hres.isProper
  have hSn : IsNormalVariety k sS := hB.isPair.1
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sS) := hYv.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  have hdimY : topologicalKrullDim Y = 2 := hK.1
  choose C hC hCc using fun i => exists_properCurve sS f hdimY hx (E i) (hEx i)
  /- the curves `E_i`: their proper curves `C_i`, and the degrees `d_i` -/
  have hprop : ∀ i, IsProper ((E i).idealSheaf.subschemeι ≫ f ≫ sS) := fun i =>
    isProper_idealSheaf_subschemeι sS f hx (E i) (hEx i)
  have hvan : ∀ i, Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({(C i).point} : Set Y)) = (E i).idealSheaf := fun i => by
    rw [hC i]; exact vanishingIdeal_closure_genericPoint_eq_idealSheaf (E i)
  have hdC : ∀ i, Module.finrank k (cohomologyOverField k ((C i).ι ≫ f ≫ sS)
      (SheafOfModules.unit (C i).scheme.ringCatSheaf) 0) = d i := fun i =>
    finrank_cohomologyOverField_unit_congr (f ≫ sS) (hvan i) 0
  have hCint : ∀ i, IsIntegral (C i).scheme := fun i =>
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hdpos : ∀ i, 0 < d i := by
    intro i
    rw [← hdC i]
    have := hCint i
    exact finrank_unit_pos k _
  have hdvd1 : ∀ i, d i ∣ Module.finrank k (cohomologyOverField k
      ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
      (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 1) := by
    intro i
    have := hprop i
    have := (E i).integral
    exact finrank_unit_dvd_finrank_cohomologyOverField k _ _ 1
  /- intersection numbers with the `C_i` -/
  set N : Fin s → Fin s → ℚ := fun i j =>
    (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (f ≫ sS) (C j).ι
      (C j).dim_le (isQCartier_of_isSmoothScheme hsm _) with hN
  have hNsymm : ∀ i j, N i j = N j i := fun i j =>
    MMP.Threefold.Resolution.intersectionNumber_single_comm hsm (E j) (E i) (C j) (C i)
      (hC j) (hC i)
  have hdvd : ∀ i (P : MMP.Mori.PrimeDivisor Y), ∃ t : ℤ,
      (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (f ≫ sS) (C i).ι
        (C i).dim_le (isQCartier_of_isSmoothScheme hsm _) = (d i : ℚ) * t := by
    intro i P
    have hc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
      (Finsupp.single P (1 : ℤ))
    have := hc.isInvertibleModule_divisorialSheaf
    have := hCint i
    obtain ⟨t, ht⟩ := finrank_unit_dvd_invertibleCurveDegree k ((C i).ι ≫ f ≫ sS) (C i).dim_le
      ((Scheme.Modules.pullback (C i).ι).obj
        (Divisor.divisorialSheaf (Finsupp.single P (1 : ℤ))))
    refine ⟨t, ?_⟩
    rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sS) (C i).ι (C i).dim_le _ hc, ← hdC i]
    exact_mod_cast ht
  have hNdvd : ∀ i j, ∃ t : ℤ, N i j = (d i : ℚ) * t := fun i j => by
    rw [hNsymm]; exact hdvd i (E j)
  choose M hM using hNdvd
  set β : Fin s → ℚ := fun i => QDivisor.intersectionNumber k (f ≫ sS) (C i).ι (C i).dim_le
    (inverseTransformDivisor f B) (isQCartier_of_isSmoothScheme hsm _) with hβ
  /- signs -/
  have hBs0 : ∀ i, inverseTransformDivisor f B (E i) = 0 := fun i =>
    inverseTransformDivisor_apply_eq_zero_of_support_subset (sS := sS) hS2 hx B (hEx i)
  have hBsnn : ∀ P, 0 ≤ inverseTransformDivisor f B P := fun P =>
    mapPrimeDivisors_nonneg _ B hB.nonneg P
  have hnn : ∀ i (P : MMP.Mori.PrimeDivisor Y), P ≠ E i → 0 ≤
      (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (f ≫ sS) (C i).ι
        (C i).dim_le (isQCartier_of_isSmoothScheme hsm _) := by
    intro i P hP
    refine MMP.Threefold.Mori.intersectionNumber_single_nonneg hsm P (C i) ?_
    rw [hC i]
    intro hmem
    exact hP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P (E i) hmem)
  have hβnn : ∀ i, 0 ≤ β i := by
    intro i
    simp only [hβ]
    rw [intersectionNumber_eq_sum hsm, Finsupp.sum]
    refine Finset.sum_nonneg fun P _ => ?_
    by_cases hP : P = E i
    · subst hP; rw [hBs0 i, zero_mul]
    · exact mul_nonneg (hBsnn P) (hnn i P hP)
  have hneg := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hYv hsm hdimY hSn.1 rfl hres.isBirationalMorphism E hEinj C hC hCc
  have heq := fun j => sum_mul_intersectionNumber_eq hB.isPair hS2 hx hYv hres hK E hEx hEall
    hEinj α hα C hC hCc j
  have hKnn : ∀ j, 0 ≤ (Divisor.toQDivisor K).intersectionNumber k (f ≫ sS) (C j).ι
      (C j).dim_le (isQCartier_of_isSmoothScheme hsm _) := fun j =>
    MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg (f ≫ sS) hKn _ (C j) (hCc j)
  have hαle : ∀ i, α i - 1 ≤ 0 := by
    refine MMP.Threefold.Mori.coeff_nonpos_of_negDef_of_intersectionNumber_nonneg hYv hsm hdimY
      E hEinj C hC (fun i => α i - 1) hneg fun j => ?_
    rw [heq j]
    have h1 : (0 : ℝ) ≤ ((Divisor.toQDivisor K).intersectionNumber k (f ≫ sS) (C j).ι
        (C j).dim_le (isQCartier_of_isSmoothScheme hsm _) : ℝ) := by exact_mod_cast hKnn j
    have h2 : (0 : ℝ) ≤ (β j : ℝ) := by exact_mod_cast hβnn j
    exact add_nonneg h1 h2
  have hdq : ∀ i, (0 : ℚ) < d i := fun i => by exact_mod_cast hdpos i
  have hMoff : ∀ i j, i ≠ j → 0 ≤ M i j := by
    intro i j hij
    have h := hnn j (E i) (fun h => hij (hEinj h))
    change 0 ≤ N i j at h
    rw [hM i j] at h
    exact_mod_cast (mul_nonneg_iff_of_pos_left (hdq i)).mp h
  /- adjunction -/
  have hadj : ∀ i, (Divisor.toQDivisor K).intersectionNumber k (f ≫ sS) (C i).ι (C i).dim_le
      (isQCartier_of_isSmoothScheme hsm _) + N i i =
      -2 * ((d i : ℚ) - Module.finrank k (cohomologyOverField k
        ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
        (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 1)) := by
    intro i
    have h1 := isIntersectionNumber_canonical_add_single hYv hsm hdimY hK (E i) (hprop i)
    have h2 := isIntersectionNumber_of_properCurve
      (Divisor.toQDivisor K + Finsupp.single (E i) 1) (isQCartier_of_isSmoothScheme hsm _)
      (C i) (E i) (hC i)
    have e := h2.unique h1
    rw [QDivisor.intersectionNumber_add' k (f ≫ sS) (C i).ι (C i).dim_le _ _
      (isQCartier_of_isSmoothScheme hsm _) (isQCartier_of_isSmoothScheme hsm _)] at e
    have e3 : N i i = QDivisor.intersectionNumber k (f ≫ sS) (C i).ι (C i).dim_le
        (Finsupp.single (E i) 1) (isQCartier_of_isSmoothScheme hsm _) :=
      MMP.Fourfold.intersectionNumber_congr (f ≫ sS) (C i).ι (C i).dim_le _ _
        (by rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one])
    rw [e3]
    exact e
  /- the normalized identity -/
  have hkey : ∀ i, ∑ l, (α l - 1) * (M i l : ℝ) =
      -2 + 2 * g i - M i i + (β i : ℝ) / d i := by
    intro i
    have hsum : ∑ l, (α l - 1) * (M i l : ℝ) * d i =
        ((Divisor.toQDivisor K).intersectionNumber k (f ≫ sS) (C i).ι (C i).dim_le
          (isQCartier_of_isSmoothScheme hsm _) : ℝ) + (β i : ℝ) := by
      rw [← heq i]
      refine Finset.sum_congr rfl fun l _ => ?_
      change _ = (α l - 1) * ((N l i : ℚ) : ℝ)
      rw [hNsymm l i, hM i l]
      push_cast
      ring
    have hadjR := congrArg (Rat.cast : ℚ → ℝ) (hadj i)
    rw [hM i i] at hadjR
    push_cast at hadjR
    have hd : (d i : ℝ) ≠ 0 := by exact_mod_cast (hdpos i).ne'
    apply mul_right_cancel₀ hd
    rw [Finset.sum_mul, hsum]
    simp only [g]
    field_simp
    linear_combination hadjR
  have hident : ∀ i, α i * (-M i i : ℝ) = 2 - 2 * g i - (β i : ℝ) / d i -
      ∑ j ∈ Finset.univ.erase i, (1 - α j) * (M i j : ℝ) := by
    intro i
    have hsplit := Finset.add_sum_erase Finset.univ (fun l => (α l - 1) * (M i l : ℝ))
      (Finset.mem_univ i)
    have herase : ∑ j ∈ Finset.univ.erase i, (1 - α j) * (M i j : ℝ) =
        -∑ j ∈ Finset.univ.erase i, (α j - 1) * (M i j : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have := hkey i
    linarith
  refine ⟨M, β, fun i j => ?_, fun i => ?_, fun i => ⟨hαpos i, by linarith [hαle i]⟩,
    ?_, fun i => ?_, hMoff, fun i => ⟨hident i, ?_⟩, ?_⟩
  · have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (Finsupp.single (E i) 1))
      (isQCartier_of_isSmoothScheme hsm _) (C j) (E j) (hC j)
    change IsIntersectionNumber _ _ _ (N i j) at h
    rwa [hM i j] at h
  · exact isIntersectionNumber_of_properCurve _ _ (C i) (E i) (hC i)
  · -- `M` is the intersection matrix with its rows divided by the positive `d_i`
    have hA : (Matrix.of fun i j : Fin s => ((N i j : ℚ) : ℝ)) =
        Matrix.diagonal (fun i => (d i : ℝ)) * (Matrix.of M).map (Int.cast : ℤ → ℝ) := by
      ext i j
      rw [Matrix.diagonal_mul, Matrix.of_apply, Matrix.map_apply, Matrix.of_apply, hM i j]
      push_cast
      ring
    have hdet := hneg.det_pos
    change 0 < (-(Matrix.of fun i j : Fin s => ((N i j : ℚ) : ℝ))).det at hdet
    rw [Matrix.det_neg, hA, Matrix.det_mul, Matrix.det_diagonal] at hdet
    have hmap : ((Matrix.of M).map (Int.cast : ℤ → ℝ)).det = ((Matrix.of M).det : ℝ) := by
      simpa using ((Int.castRingHom ℝ).map_det (Matrix.of M)).symm
    rw [hmap] at hdet
    intro h0
    change (Matrix.of M).det = 0 at h0
    rw [h0, Int.cast_zero, mul_zero, mul_zero] at hdet
    exact lt_irrefl _ hdet
  · have h := hneg.diag_pos (i := i)
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at h
    have h' : (N i i : ℚ) < 0 := by exact_mod_cast h
    rw [hM i i] at h'
    have h'' : (M i i : ℚ) < 0 := neg_of_mul_neg_right h' (hdq i).le
    have : M i i < 0 := by exact_mod_cast h''
    omega
  · rw [hident i]
    have hg0 : 0 ≤ g i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hb0 : (0 : ℝ) ≤ (β i : ℝ) / d i :=
      div_nonneg (by exact_mod_cast hβnn i) (Nat.cast_nonneg _)
    have hs0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, (1 - α j) * (M i j : ℝ) :=
      Finset.sum_nonneg fun j hj => mul_nonneg (by linarith [hαle j])
        (by exact_mod_cast hMoff i j (Finset.ne_of_mem_erase hj).symm)
    linarith
  · -- integrality
    intro q hq hqB i
    have hqBs : ∀ P, ∃ n : ℤ, (q : ℚ) * inverseTransformDivisor f B P = n := by
      obtain ⟨B', hB'⟩ := (QDivisor.mem_range_toQDivisor_iff (q • B)).2 fun P => by
        obtain ⟨n, hn⟩ := hqB P
        exact ⟨n, by rw [DivisorWithCoeffs.coeff, Finsupp.smul_apply, nsmul_eq_mul]; exact hn⟩
      intro P
      refine ⟨inverseTransformDivisor f B' P, ?_⟩
      have h1 : inverseTransformDivisor f (q • B) = q • inverseTransformDivisor f B :=
        map_nsmul _ _ _
      rw [← hB', MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor] at h1
      have h2 := congrArg (fun F : QDivisor Y => F P) h1
      simp only [Finsupp.smul_apply, nsmul_eq_mul] at h2
      rw [← h2]
      rfl
    choose b hb using hqBs
    choose t ht using hdvd i
    obtain ⟨t1, ht1⟩ := hdvd1 i
    have hdR : (0 : ℝ) < d i := by exact_mod_cast hdpos i
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hgt : g i = t1 := by
      change (Module.finrank k (cohomologyOverField k ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
        (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 1) : ℝ) / d i = _
      rw [ht1]
      push_cast
      field_simp
    have hβq : (β i : ℚ) / d i * q =
        ∑ P ∈ (inverseTransformDivisor f B).support, (b P : ℚ) * t P := by
      simp only [hβ]
      rw [intersectionNumber_eq_sum hsm, Finsupp.sum, Finset.sum_div, Finset.sum_mul]
      have hdQ : (d i : ℚ) ≠ 0 := (hdq i).ne'
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [ht P, ← hb P]
      field_simp
    refine ⟨q * (-2 + 2 * t1 - M i i) +
      ∑ P ∈ (inverseTransformDivisor f B).support, b P * t P, ?_⟩
    have hβR : (β i : ℝ) / d i = (∑ P ∈ (inverseTransformDivisor f B).support,
        (b P : ℝ) * t P) / q := by
      rw [eq_div_iff hqR.ne']
      have := congrArg (fun z : ℚ => (z : ℝ)) hβq
      push_cast at this
      exact this
    have hsum : ∑ j, (M i j : ℝ) * (α j - 1) = ∑ l, (α l - 1) * (M i l : ℝ) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hsum, hkey i, hgt, hβR, eq_div_iff hqR.ne']
    push_cast
    field_simp

end NormalizedMatrix

/-! ### Bounded denominators at a surface point -/

namespace Denominators

open NormalizedMatrix

/-! ### Orders along a centred valuation -/

section Hartogs

/-- A valuation of `k(Y)` which is at most one on `𝒪_{Y,y}` is one on its units. -/
private theorem valuation_algebraMap_eq_one_of_isUnit {Y : Scheme.{u}} [IsIntegral Y]
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))) {y : Y}
    (hξ : ∀ a : Y.presheaf.stalk y, ξ (algebraMap _ Y.functionField a) ≤ 1)
    {a : Y.presheaf.stalk y} (ha : IsUnit a) : ξ (algebraMap _ Y.functionField a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  refine le_antisymm (hξ _) ?_
  have h2 : ξ (algebraMap _ Y.functionField (u : Y.presheaf.stalk y)) *
      ξ (algebraMap _ Y.functionField (↑u⁻¹ : Y.presheaf.stalk y)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  by_contra h
  rw [not_le] at h
  have := mul_lt_one_of_lt_of_le h (hξ (↑u⁻¹ : Y.presheaf.stalk y))
  rw [h2] at this
  exact lt_irrefl _ this

/-- **Hartogs for a centred valuation.** Let `Y` be normal and `ξ` a valuation of `k(Y)` which is
at most one on `𝒪_{Y,y}`, and let `g_j` be nonzero rational functions with `ξ(g_j) = exp(n_j)`.
If a real combination of the orders of the `g_j` vanishes along every prime divisor through `y`,
the same combination of the `n_j` vanishes. -/
private theorem sum_mul_eq_zero_of_valuation_le_one {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))) {y : Y}
    (hξ : ∀ a : Y.presheaf.stalk y, ξ (algebraMap _ Y.functionField a) ≤ 1)
    {p : Type*} [Fintype p] (g : p → Y.functionField) (hg : ∀ j, g j ≠ 0) (n : p → ℤ)
    (hn : ∀ j, ξ (g j) = WithZero.exp (n j)) (s : p → ℝ)
    (hs : ∀ Γ : MMP.Mori.PrimeDivisor Y, y ∈ Γ.support →
      ∑ j, (Y.ord (g j) Γ.genericPoint : ℝ) * s j = 0) :
    ∑ j, (n j : ℝ) * s j = 0 := by
  classical
  refine MMP.Threefold.Bridges.sum_real_eq_zero_of_int
    (ι := {Γ : MMP.Mori.PrimeDivisor Y // y ∈ Γ.support})
    (fun Γ j => Y.ord (g j) Γ.1.genericPoint) n (fun e he => ?_) s (fun Γ => hs Γ.1 Γ.2)
  set G : Y.functionField := ∏ j, g j ^ e j with hGdef
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hg i)
  obtain ⟨t, ht, htG⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    y hG fun Γ hΓ => by
      rw [hGdef, MMP.Threefold.Bridges.ord_prod_zpow _ _ _ hg]
      simpa [mul_comm] using he ⟨Γ, hΓ⟩
  have h1 : ξ G = 1 := htG ▸ valuation_algebraMap_eq_one_of_isUnit ξ hξ ht
  have h2 : ξ G = WithZero.exp (∑ j, n j * e j) := by
    rw [hGdef, map_prod]
    simp only [map_zpow₀, hn, ← WithZero.exp_zsmul, smul_eq_mul]
    simp [WithZero.exp, ofAdd_sum, ← WithZero.coeMonoidHom_apply, map_prod, mul_comm]
  rw [h1, ← WithZero.exp_zero] at h2
  exact (WithZero.exp_injective h2).symm

end Hartogs

/-! ### Divisors over a surface and their centres -/

section Centres

/-- The valuation of a divisor over `X` dominates the local ring of `X` at the image of the generic
point of the divisor. -/
private theorem divisorOver_dominates {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : DivisorOver k sX) {y : X}
    (hy : D.f D.E.genericPoint = y) :
    (∀ a : X.presheaf.stalk y, D.valuation (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y),
        D.valuation (algebraMap _ X.functionField a) < 1 := by
  subst hy
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have happ : ∀ a : X.presheaf.stalk (D.f D.E.genericPoint),
      D.valuation (algebraMap _ X.functionField a) = D.E.divisorialValuation
        (algebraMap D.E.localRing D.Y.functionField ((D.f.stalkMap D.E.genericPoint).hom a)) :=
    fun a => by
      change D.E.divisorialValuation (functionFieldMap D.f _) = _
      rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [happ, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  · rw [happ]
    have hm : (D.f.stalkMap D.E.genericPoint).hom a ∈ IsLocalRing.maximalIdeal D.E.localRing :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)
    have := D.E.isDiscreteValuationRing_localRing
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal D.E.localRing) _).2 hm

/-- A divisor over `X` whose centre is a closed point `x` has its generic point over `x`. -/
private theorem map_genericPoint_eq_of_center_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) {x : X}
    (hc : (D.center : Set X) = {x}) : D.f D.E.genericPoint = x := by
  have h := D.center_eq_closure_genericPoint
  rw [hc] at h
  show D.f D.E.genericPoint ∈ ({x} : Set X)
  rw [h]
  exact subset_closure rfl

/-- If every coefficient of `D` lies in `(1/c) ℤ`, so does every coefficient of its linear
extension along a partial map of prime divisors. -/
private theorem exists_int_mul_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*} [CommRing R]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (c : R)
    (D : DivisorWithCoeffs R X)
    (hD : ∀ P, ∃ n : ℤ, c * D P = n) (P : MMP.Mori.PrimeDivisor Y) :
    ∃ n : ℤ, c * DivisorWithCoeffs.mapPrimeDivisors φ D P = n := by
  classical
  induction D using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add a b g ha hb ih =>
    have hga : g a = 0 := Finsupp.notMem_support_iff.mp ha
    obtain ⟨nb, hnb⟩ : ∃ n : ℤ, c * b = n := by
      obtain ⟨n, hn⟩ := hD a
      exact ⟨n, by simpa [hga] using hn⟩
    have hg : ∀ Q, ∃ n : ℤ, c * g Q = n := fun Q => by
      by_cases hQ : Q = a
      · subst hQ; exact ⟨0, by rw [hga]; simp⟩
      · obtain ⟨n, hn⟩ := hD Q
        exact ⟨n, by simpa [Finsupp.single_apply, Ne.symm hQ] using hn⟩
    obtain ⟨n, hn⟩ := ih hg
    rw [map_add, Finsupp.add_apply, DivisorWithCoeffs.mapPrimeDivisors_single, mul_add, hn]
    rcases φ a with _ | E'
    · exact ⟨n, by simp⟩
    · simp only [Option.elim_some, Finsupp.single_apply]
      split_ifs
      · exact ⟨nb + n, by rw [hnb]; push_cast; ring⟩
      · exact ⟨n, by simp⟩

end Centres

/-! ### The denominator of an arbitrary log discrepancy -/

section Denominator

open MMP.Flips

/-- **Denominators of log discrepancies at `x`.** Let `(S, B)` be a pair on a surface over a
field of characteristic zero with `qB` integral, `f : Y ⟶ S` a resolution, `E_1, …, E_s` the
prime divisors of `Y` over the closed point `x`, with log discrepancies `α_i ∈ 1 + (1/D) ℤ`, and
`q ∣ D`. Then every log discrepancy of a divisor over `S` with centre `x` lies in `(1/D) ℤ`. -/
private theorem exists_eq_div_of_isLogDiscrepancy {k : Type u} [Field k] [CharZero k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] {B : QDivisor S} (hBp : MMP.Mori.IsPair sS B)
    (hS2 : topologicalKrullDim S = 2) {x : S} (hx : IsClosed ({x} : Set S))
    {f : Y ⟶ S} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hYv : MMP.Mori.IsVariety k (f ≫ sS)) (hres : IsSmoothResolution sS f)
    {s : ℕ} (E : Fin s → MMP.Mori.PrimeDivisor Y)
    (hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P)
    (α : Fin s → ℝ)
    (hα : ∀ i, MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B)
      ⟨Y, f, ⟨hYv, inferInstance⟩, hres.isBirationalMorphism, E i⟩ (α i))
    {q D : ℕ} (hqD : q ∣ D) (hD : 0 < D) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    (hαD : ∀ i, ∃ r : ℤ, α i - 1 = r / D)
    (F : DivisorOver k sS) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) F a)
    (hc : (F.center : Set S) = {x}) : ∃ r : ℤ, a = r / D := by
  classical
  have hsm := hres.isSmoothScheme
  have : IsProper f := hres.isProper
  have hf := hres.isBirationalMorphism
  have hSn : IsNormalVariety k sS := hBp.1
  have hYn : IsNormalVariety k (f ≫ sS) := ⟨hYv, inferInstance⟩
  have : MMP.Mori.IsVariety k sS := hSn.1
  have := hYv
  have : LocallyOfFiniteType sS := hSn.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sS) := hYv.toLocallyOfFiniteType
  have : QuasiCompact sS := inferInstance
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  have : IsDominant f := hf.isDominant
  have := F.isIntegral
  have := F.isLocallyNoetherian
  have := F.isNormal
  have := F.isDominant
  have hFx : F.f F.E.genericPoint = x := map_genericPoint_eq_of_center_eq F hc
  -- a rational top form `ω` on `S` and a presentation of `K_S + B`, from `ha`
  obtain ⟨-, hFp, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m, r, Cc, -, hCcart, hdec, -, -⟩ := id ha
  have : IsProper F.f := hFp
  have : CompactSpace F.Y := by
    have : QuasiCompact F.f := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace F.f
  have hdivω : divisorOfForm ω = K₀ :=
    DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hK₀ω]
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sS 2 := hdivω ▸ hK₀
  obtain ⟨Ex, a', G, hEx', ⟨m', r', L, L', hLc, hLdec, hLpb, rfl⟩, -, heq⟩ :=
    discrepancy_formula hSn (QDivisor.toRDivisor B) ω hω0 hKω
      ⟨m, r, Cc, hCcart, (toRDivisor_divisorOfForm_add_eq_sum_iff ω _ r Cc).2 hdec⟩ f hYn hf
  have hLdec' := (toRDivisor_divisorOfForm_add_eq_sum_iff ω _ r' L).1 hLdec
  set K' := divisorOfForm (pullbackRationalPluriForms sS f ω) with hK'
  set R : RDivisor Y := ∑ E ∈ Ex, Finsupp.single E (a' E) with hR
  -- the log discrepancies in terms of the presentation `(r', L)`
  have hαi : ∀ i, α i = 1 + (K' (E i) : ℝ) - ∑ l, r' l * (L' l (E i) : ℝ) := by
    intro i
    refine MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hα i)
      ⟨hSn, inferInstance, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m', r', L, L', hLc, hLdec', hLpb, ?_⟩
    change _ = 1 + ((E i).ordForm (pullbackRationalPluriForms sS f ω) : ℝ) - _
    rw [← coeff_divisorOfForm]
    rfl
  choose L'' hL'' using fun l => MMP.Threefold.Bridges.exists_isPullback_of_isDominant F.f (hLc l)
  have haF : a = 1 + (F.ordPullback ω : ℝ) - ∑ l, r' l * (L'' l F.E : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
      ⟨hSn, hFp, ω, hω0, ⟨K₀, hK₀, hK₀ω⟩, m', r', L, L'', hLc, hLdec',
        fun l => ⟨_, hL'' l⟩, rfl⟩
  -- the centre `y` of the valuation of `F` on `Y`
  have hbij : Function.Bijective (functionFieldMap f) := hf.functionFieldMap_bijective
  set e := RingEquiv.ofBijective (functionFieldMap f) hbij with he
  set ξY : Valuation Y.functionField (WithZero (Multiplicative ℤ)) :=
    F.valuation.comap (e.symm : Y.functionField →+* S.functionField) with hξYdef
  have hξY : ∀ g, ξY (functionFieldMap f g) = F.valuation g := fun g => by
    rw [hξYdef, Valuation.comap_apply]
    congr 1
    exact e.symm_apply_apply g
  have hdomS := divisorOver_dominates F hFx
  obtain ⟨y, hyξ, hfy⟩ := MMP.Fourfold.SNCWeight.SNCModel.exists_dominates_of_isProper f ξY x
    ⟨fun a => by rw [Valuation.comap_apply, hξY]; exact hdomS.1 a,
      fun a ha => by rw [Valuation.comap_apply, hξY]; exact hdomS.2 a ha⟩
  have hηx : ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support → f P.genericPoint ⤳ x :=
    fun P hP => by
      rw [← hfy]
      refine (specializes_iff_mem_closure.mpr ?_).map f.continuous
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  -- the crepant boundary has coefficients in `(1/D) ℤ` along the prime divisors through `y`
  have hint : ∀ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support →
      ∃ z : ℤ, (D : ℝ) * ∑ l, r' l * (L' l P : ℝ) = z := by
    intro P hP
    obtain ⟨d₀, rfl⟩ := hqD
    have hDR : ((q * d₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    by_cases hPEx : P ∈ Ex
    · -- `P` lies over `x`, so it is one of the `E_i`
      have hcl := isClosed_singleton_of_isExceptionalPrimeDivisor hS2 ((hEx' P).mp hPEx)
      have hsub : ∀ z ∈ P.support, f z = f P.genericPoint := fun z hz => by
        have := map_mem_closure_of_mem_support (f := f) P hz
        rwa [hcl.closure_eq] at this
      have hPx : f P.genericPoint = x := by rw [← hsub y hP, hfy]
      obtain ⟨i, rfl⟩ := hEall P fun z hz => by
        show f z ∈ ({x} : Set S)
        rw [hsub z hz, hPx]
        rfl
      obtain ⟨t, ht⟩ := hαD i
      refine ⟨q * d₀ * K' (E i) - t, ?_⟩
      have hsum : ∑ l, r' l * (L' l (E i) : ℝ) = (K' (E i) : ℝ) - t / ((q * d₀ : ℕ) : ℝ) := by
        linarith [hαi i, ht]
      rw [hsum]
      field_simp
      push_cast
      ring
    · -- `P` is not exceptional: the coefficient is that of the strict transform of `B`
      have hRP : R P = 0 := by
        rw [hR, Finsupp.finsetSum_apply]
        exact Finset.sum_eq_zero fun E' hE' =>
          Finsupp.single_eq_of_ne' (fun h => hPEx (h ▸ hE'))
      have h := congrArg (fun F : RDivisor Y => F P) heq
      simp only [Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, smul_eq_mul, hRP, add_zero] at h
      obtain ⟨n, hn⟩ := exists_int_mul_mapPrimeDivisors
        (RationalMap.IsBirational.inverse hf).transformPrimeDivisor (q : ℝ)
        (QDivisor.toRDivisor B) (fun Q => by
          obtain ⟨n, hn⟩ := hqB Q
          refine ⟨n, ?_⟩
          change (q : ℝ) * ((B Q : ℚ) : ℝ) = n
          have := congrArg (Rat.cast : ℚ → ℝ) hn
          push_cast at this
          exact this) P
      refine ⟨q * d₀ * K' P + d₀ * n, ?_⟩
      have h2 : (Divisor.toRDivisor K') P = ((K' P : ℤ) : ℝ) := rfl
      have h3 : ∀ l, (Divisor.toRDivisor (L' l)) P = ((L' l P : ℤ) : ℝ) := fun l => rfl
      simp only [h2, h3] at h
      have hn' : (q : ℝ) * (birationalInverseTransform f hf (QDivisor.toRDivisor B)) P = n := hn
      rw [← h]
      push_cast
      linear_combination (d₀ : ℝ) * hn'
  -- the integral divisor `D · f^*(K_S + B)` near `y`, and a local equation `ψ` of it at `y`
  have hfin : (Function.support fun P : MMP.Mori.PrimeDivisor Y =>
      if y ∈ P.support then round ((D : ℝ) * ∑ l, r' l * (L' l P : ℝ)) else 0).Finite := by
    refine (Set.finite_iUnion fun l => (L' l).support.finite_toSet).subset fun P hP => ?_
    by_contra hPn
    simp only [Set.mem_iUnion, Finset.mem_coe, Finsupp.mem_support_iff, not_exists,
      not_not] at hPn
    apply hP
    simp [hPn]
  set Gi : Divisor Y := Finsupp.ofSupportFinite _ hfin with hGi
  have hGiP : ∀ P, y ∈ P.support → ((Gi P : ℤ) : ℝ) = (D : ℝ) * ∑ l, r' l * (L' l P : ℝ) := by
    intro P hP
    obtain ⟨z, hz⟩ := hint P hP
    simp only [hGi, Finsupp.ofSupportFinite_coe, if_pos hP, hz, round_intCast]
  obtain ⟨V', hyV', ψ, hψ⟩ := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm Gi y
  -- local equations `φ_l` of the `L_l` near `x`
  choose V hxV φ hφ using fun l => hLc l x
  choose hB' hpb' using hLpb
  set Zx := MMP.Mori.pointComponent x
  set Zy := MMP.Mori.pointComponent y
  set gS : Fin m' → S.functionField := fun l =>
    MMP.Threefold.Mori.Helpers.evalFF Zx (φ l : MMP.Mori.RationalFunctions S) with hgS
  have hgS0 : ∀ l, gS l ≠ 0 := fun l =>
    ((φ l).isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zx)).ne_zero
  set h : Y.functionField :=
    MMP.Threefold.Mori.Helpers.evalFF Zy (ψ : MMP.Mori.RationalFunctions Y) with hh
  have hh0 : h ≠ 0 := (ψ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Zy)).ne_zero
  set g : Option (Fin m') → Y.functionField := fun j =>
    j.elim h fun l => functionFieldMap f (gS l) with hg
  have hg0 : ∀ j, g j ≠ 0 := by
    rintro (_ | l)
    · exact hh0
    · exact (map_ne_zero _).mpr (hgS0 l)
  set n : Option (Fin m') → ℤ := fun j =>
    j.elim (WithZero.log (ξY h)) fun l =>
      -F.Y.ord (functionFieldMap F.f (gS l)) F.E.genericPoint with hn
  have hn' : ∀ j, ξY (g j) = WithZero.exp (n j) := by
    rintro (_ | l)
    · exact (WithZero.exp_log ((Valuation.ne_zero_iff ξY).mpr hh0)).symm
    · change ξY (functionFieldMap f (gS l)) = _
      rw [hξY]
      change F.E.divisorialValuation (functionFieldMap F.f (gS l)) = _
      exact F.E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (hgS0 l))
  set c : Option (Fin m') → ℝ := fun j => j.elim (-1) fun l => (D : ℝ) * r' l with hc'
  have hzero := sum_mul_eq_zero_of_valuation_le_one ξY hyξ.1 g hg0 n hn' c (fun Γ hΓ => by
    rw [Fintype.sum_option]
    have hΓV : ∀ l, f Γ.genericPoint ∈ V l := fun l =>
      (hηx Γ hΓ).mem_open (V l).isOpen (hxV l)
    have hL : ∀ l, Y.ord (g (some l)) Γ.genericPoint = L' l Γ := fun l =>
      (MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hpb' l) (hφ l) Γ (hΓV l) Zx).symm
    have hG : Y.ord (g none) Γ.genericPoint = Gi Γ := by
      have h1 := hψ Γ ⟨y, hΓ, hyV'⟩
      rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h1
      have hZ : Γ.component = Zy :=
        Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
      rw [hZ] at h1
      exact h1.symm
    simp only [hc', Option.elim_none, Option.elim_some, hL, hG, hGiP Γ hΓ, Finset.mul_sum]
    rw [mul_neg_one, neg_add_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring)
  -- the coefficients of the `L_l` pulled back to the model of `F`
  have hnL : ∀ l, (n (some l) : ℝ) = -(L'' l F.E : ℝ) := fun l => by
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL'' l) (hφ l) F.E
      (by rw [hFx]; exact hxV l) Zx
    change ((-F.Y.ord (functionFieldMap F.f (gS l)) F.E.genericPoint : ℤ) : ℝ) = _
    rw [← h1]
    push_cast
    rfl
  rw [Fintype.sum_option] at hzero
  simp only [hc', Option.elim_none, Option.elim_some, hnL] at hzero
  have hS1 : (D : ℝ) * ∑ l, r' l * (L'' l F.E : ℝ) = -(n none : ℝ) := by
    have e : ∑ l, -(L'' l F.E : ℝ) * ((D : ℝ) * r' l) =
        -((D : ℝ) * ∑ l, r' l * (L'' l F.E : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    linarith [hzero, e]
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨D * (1 + F.ordPullback ω) + n none, ?_⟩
  rw [haF, eq_div_iff hDR]
  push_cast
  linear_combination (-1 : ℝ) * hS1

end Denominator

/-! ### The canonical divisor of the minimal resolution -/

section MinimalResolution

open MMP.Resolution

/-- If `𝒪_X(D)` is the divisorial sheaf of a Cartier Weil divisor `D'`, then the intersection
number of `D` with a projective curve is the degree of `D'` along it. -/
private theorem cartierCurveIntersection_eq_degreeOn {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsNormal S] [IsLocallyNoetherian S] [QuasiCompact sS]
    {D : S.CartierDivisor} {D' : Divisor S} (hD' : D'.IsCartier)
    (e : MMP.CartierDivisor.sheaf D ≅ D'.divisorialSheaf) (C : ProperCurve sS)
    (hC : IsProjectiveMorphism (C.ι ≫ sS)) :
    cartierCurveIntersection D C = D'.degreeOn k sS C.ι C.dim_le hD' := by
  have := QuasiCompact.compactSpace_of_compactSpace sS
  have hinv := hD'.isInvertibleModule_divisorialSheaf
  have : Stacks.Ample.IsInvertibleModule S (MMP.CartierDivisor.sheaf D) :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hinv
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf D) := this
  have : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 D'.divisorialSheaf := hinv
  have hcurve : AlgebraicGeometry.IsCurve k (C.ι ≫ sS) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := C.dim_eq }
  have : AlgebraicGeometry.IsProjectiveVariety k (C.ι ≫ sS) :=
    { toIsVariety := hcurve.toIsVariety
      isProjective := hC }
  have : Stacks.Ample.IsInvertibleModule C.scheme
      ((Scheme.Modules.pullback C.ι).obj (MMP.CartierDivisor.sheaf D)) :=
    MMP.Mori.isInvertible_pullback_obj C.ι _
  unfold cartierCurveIntersection lineBundleCurveIntersection
  rw [MMP.Resolution.degree_eq_invertibleCurveDegree (C.ι ≫ sS) _ C.dim_le,
    ← MMP.Mori.degreeOn_eq_invertibleCurveDegree, MMP.Mori.degreeOn_eq_of_iso k sS C.ι C.dim_le e]
  rfl

/-- **`K_Y` is relatively nef on a minimal resolution.** For the minimal resolution `f : Y ⟶ S`
and a nonzero rational `2`-form `ω` on `Y`, the divisor `div(ω)` meets every projective curve
contracted by `f` nonnegatively. -/
private theorem intersectionNumber_divisorOfForm_nonneg {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral Y] [IsNoetherian Y] {f : Y ⟶ S}
    [LocallyOfFiniteType (f ≫ sS)] (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    [IsNormal Y] [QuasiCompact (f ≫ sS)]
    (ω : RationalPluriForms (f ≫ sS) 2 1) (hω : ω ≠ 0) (C : ProperCurve (f ≫ sS))
    (hC : IsContractedProjectiveCurve (f ≫ sS) f C) :
    0 ≤ (Divisor.toQDivisor (divisorOfForm ω)).intersectionNumber k (f ≫ sS) C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hmin.1.isSmoothScheme _) := by
  have hf := hmin.1
  have hYv : AlgebraicGeometry.IsVariety k sS := hf.isVariety
  have : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hXv : AlgebraicGeometry.IsVariety k (f ≫ sS) := {}
  have : IsSmoothVariety k (f ≫ sS) :=
    { toIsVariety := hXv,
      toSmooth := (@isSmoothScheme_iff _ _ _
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance)).mp
          hf.isSmoothScheme }
  obtain ⟨Kc, hKc, hnef⟩ := hmin.2 ω hω
  set B : Divisor Y := divisorOfForm ω
  have hBK : weilDivisorEquivFinsupp (cartierWeilDivisor Kc) = B := by
    ext P
    refine (hKc P).trans ?_
    simp only [divisorOfFormOnSmoothLocus, Finsupp.filter_apply]
    split_ifs with hP
    · rfl
    · refine absurd ⟨AlgebraicGeometry.PrimeDivisor.genericPoint P, ?_, ?_⟩ hP
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · rw [show smoothLocus (f ≫ sS) = ⊤ from hf.isSmoothScheme]; trivial
  obtain ⟨hcart, -, -, hdict, -, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (f ≫ sS)
  have eB : MMP.CartierDivisor.sheaf Kc ≅ B.divisorialSheaf := by
    have e := (hdict Kc).some
    rw [hBK] at e
    exact e.symm
  have hnefC := hnef C hC
  simp only [curveIntersectionPairing, MMP.Mori.KCartierDivisor.ofCartier,
    MMP.Mori.ProperCurve.cycle, Finsupp.linearCombination_single, LinearMap.smul_apply,
    one_smul] at hnefC
  rw [QDivisor.intersectionNumber_toQDivisor k (f ≫ sS) C.ι C.dim_le B (hcart B),
    ← cartierCurveIntersection_eq_degreeOn (hcart B) eB C hC.1]
  exact_mod_cast hnefC

/-- A proper curve contracted by a projective birational morphism from a surface is a projective
curve: it is the generic point of a prime divisor mapping to a closed point. -/
private theorem isContractedProjectiveCurve_of_isContractedBy {k : Type u} [Field k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} (hS : AlgebraicGeometry.IsVariety k sS)
    [IsIntegral Y] (f : Y ⟶ S) (hY : AlgebraicGeometry.IsVariety k (f ≫ sS))
    (hdimY : topologicalKrullDim Y = 2) (hproj : IsProjectiveMorphism f)
    (C : ProperCurve (f ≫ sS)) (hC : C.IsContractedBy f) :
    IsContractedProjectiveCurve (f ≫ sS) f C := by
  have : LocallyOfFiniteType (f ≫ sS) := hY.toLocallyOfFiniteType
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have hCdim : topologicalKrullDim (closure {C.point} : Set Y) = 1 := by
    have h := C.dim_eq
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq] at h
    exact h
  have hco : Order.coheight C.point = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sS) C.point
    rw [hCdim, hdimY] at h
    have h' : ((Order.coheight C.point : ℕ∞) : WithBot ℕ∞) = 1 :=
      ENat.WithBot.add_one_cancel.mp (by rw [add_comm]; exact h)
    exact_mod_cast h'
  set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne C.point hco
  have hG : G.genericPoint = C.point :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsupp : (G.support : Set Y) = closure {C.point} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hG]
  have himg : f.base '' (G.support : Set Y) = {f C.point} := by
    rw [hsupp]
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩; exact hC z hz
    · rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩
  have hcl : IsClosed (f.base '' (G.support : Set Y)) :=
    f.isClosedMap _ (hsupp ▸ isClosed_closure)
  have hP : topologicalKrullDim (closure (f.base '' (G.support : Set Y))) <
      topologicalKrullDim (G.support : Set Y) := by
    rw [hcl.closure_eq, himg, hsupp, hCdim]
    have h0 : topologicalKrullDim ({f C.point} : Set S) ≤ 0 :=
      @topologicalKrullDim_zero_of_discreteTopology _ _
        (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := f C.point)).coe_sort)
    exact lt_of_le_of_lt h0 (by decide)
  obtain ⟨C', hC'p, hC'⟩ :=
    exists_isContractedProjectiveCurve_of_isExceptional (sS := f ≫ sS) (sX := sS) hY hdimY hS f
      rfl hproj G hP
  have : C' = C := ProperCurve.ext (hC'p.trans hG)
  exact this ▸ hC'

/-- On the minimal resolution `f : Y ⟶ S` of a surface there is a canonical divisor `K_Y` which is
`f`-nef. -/
private theorem exists_isCanonicalDivisor_isRelativelyNef {k : Type u} [Field k] [CharZero k]
    {S Y : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral Y] [IsNoetherian Y] [IsNormal Y]
    {f : Y ⟶ S} [LocallyOfFiniteType (f ≫ sS)] [QuasiCompact (f ≫ sS)]
    (hmin : MMP.Resolution.IsMinimalSurfaceResolution sS f)
    (hYn : IsNormalVariety k (f ≫ sS)) :
    ∃ K : Divisor Y, K.IsCanonicalDivisor (f ≫ sS) 2 ∧
      (Divisor.toQDivisor K).IsRelativelyNef (f ≫ sS) f := by
  have hf := hmin.1
  have hsm := hf.isSmoothScheme
  have : AlgebraicGeometry.IsVariety k (f ≫ sS) := hYn.1
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sS) hsm
    (n := 2) hf.dim_source_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hK
  have hdiv : divisorOfForm ω = K :=
    DivisorWithCoeffs.ext' fun Γ => by rw [coeff_divisorOfForm, hωK]
  refine ⟨K, hK, MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (f ≫ sS)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _) fun C hC => ?_⟩
  have hC' := isContractedProjectiveCurve_of_isContractedBy hf.isVariety f hYn.1
    hf.dim_source_eq hf.isProjectiveMorphism C hC
  have := intersectionNumber_divisorOfForm_nonneg hmin ω hω0 C hC'
  rwa [MMP.Fourfold.intersectionNumber_congr (f ≫ sS) C.ι C.dim_le _ _
    (by rw [hdiv])] at this

end MinimalResolution

/-! ### The prime divisors over the point -/

section Fibre

variable {k : Type u} [Field k] {S Y : Scheme.{u}}

/-- The prime divisors of `Y` lying over a point `x` which is not the image of the generic point
are finitely many. -/
private theorem finite_setOf_support_subset [IsIntegral Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] (f : Y ⟶ S) {x : S} (hx : IsClosed ({x} : Set S))
    (hη : f (genericPoint Y) ≠ x) :
    {P : MMP.Mori.PrimeDivisor Y | P.support ⊆ f.base ⁻¹' {x}}.Finite := by
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  set U : Y.Opens := ⟨(f.base ⁻¹' {x})ᶜ, (hx.preimage f.continuous).isOpen_compl⟩
  have hηU : genericPoint Y ∈ U := hη
  refine Set.Finite.of_finite_image
    ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) U hηU).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨P, hP, rfl⟩
  refine ⟨by rw [(genericPoint_spec Y).def]; trivial, fun hmem => hmem ?_,
    P.coheight_genericPoint⟩
  exact map_genericPoint_eq_of_support_subset hP

/-- Distinct prime divisors of `Y` give distinct divisorial valuations of `k(S)` through a
birational morphism `f : Y ⟶ S`. -/
private theorem eq_of_valuation_eq {sS : S ⟶ Spec (.of k)} [IsIntegral S] {f : Y ⟶ S}
    (hYv : IsNormalVariety k (f ≫ sS)) (hf : IsBirationalMorphism f)
    {P Q : MMP.Mori.PrimeDivisor Y}
    (h : (⟨Y, f, hYv, hf, P⟩ : DivisorOver k sS).valuation =
      (⟨Y, f, hYv, hf, Q⟩ : DivisorOver k sS).valuation) :
    P = Q := by
  have : IsIntegral Y := hYv.1.toIsIntegral
  have : IsNormal Y := hYv.2
  have : LocallyOfFiniteType (f ≫ sS) := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  have : IsDominant f := hf.isDominant
  have hdiv : P.divisorialValuation = Q.divisorialValuation := by
    ext g
    obtain ⟨g, rfl⟩ := hf.functionFieldMap_bijective.2 g
    exact congrArg (fun v => v g) h
  have hv : (DivisorOver.ofPrimeDivisor k hYv P).valuation =
      (DivisorOver.ofPrimeDivisor k hYv Q).valuation := by
    ext g
    change P.divisorialValuation (functionFieldMap (𝟙 Y) g) =
      Q.divisorialValuation (functionFieldMap (𝟙 Y) g)
    rw [hdiv]
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hYv.1 hv
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- The centre of a prime divisor of `Y` lying over a closed point `x` is `x`. -/
private theorem center_eq_singleton {sS : S ⟶ Spec (.of k)} {f : Y ⟶ S}
    (hYv : IsNormalVariety k (f ≫ sS)) (hf : IsBirationalMorphism f)
    {x : S} (hx : IsClosed ({x} : Set S)) {P : MMP.Mori.PrimeDivisor Y}
    (hP : P.support ⊆ f.base ⁻¹' {x}) :
    ((⟨Y, f, hYv, hf, P⟩ : DivisorOver k sS).center : Set S) = {x} := by
  rw [DivisorOver.center_eq_closure_genericPoint]
  change closure {f P.genericPoint} = _
  rw [map_genericPoint_eq_of_support_subset hP, hx.closure_eq]

end Fibre

/-! ### Linear algebra of the normalized matrix -/

section LinearAlgebra

open Matrix

/-- A `2 × 2` principal minor of a positive definite real matrix is positive. -/
private theorem mul_lt_mul_of_posDef {s : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} (hA : A.PosDef)
    {i j : Fin s} (hij : i ≠ j) : A i j * A j i < A i i * A j j := by
  have hsymm : A j i = A i j := by
    have := congrFun (congrFun hA.1 i) j
    simpa using this
  have hii : 0 < A i i := hA.diag_pos
  set v : Fin s → ℝ := Pi.single i (A i j) + Pi.single j (-A i i) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrFun h j
    simp [hv, Pi.single_apply, hij.symm] at this
    linarith
  have hq := hA.dotProduct_mulVec_pos hv0
  have hval : star v ⬝ᵥ (A *ᵥ v) = A i i * (A i i * A j j - A i j * A j i) := by
    simp only [star_trivial, hv, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
      Matrix.mulVec_single, single_dotProduct, dotProduct_single]
    simp [Pi.single_apply, hij, hij.symm, hsymm]
    ring
  rw [hval] at hq
  nlinarith [(mul_pos_iff_of_pos_left hii).mp hq]

/-- **Entries of a normalized intersection matrix.** Let `M` be an integral matrix, symmetrizable
by positive weights `d`, with positive principal `2 × 2` minors, diagonal entries `≤ -1` and
nonnegative off-diagonal entries. If every `-M_ii` is at most `b`, every entry has absolute value
at most `b²`. -/
private theorem abs_le_sq_of_symmetrizable {s : ℕ} (M : Matrix (Fin s) (Fin s) ℤ) (d : Fin s → ℝ)
    (hd : ∀ i, 0 < d i) (hsymm : ∀ i j, d i * M i j = d j * M j i)
    (hminor : ∀ i j, i ≠ j → (M i j : ℝ) * M j i < M i i * M j j)
    (hdiag : ∀ i, 1 ≤ -M i i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) {b : ℝ}
    (hb : ∀ i, (-M i i : ℝ) ≤ b) (i j : Fin s) : |(M i j : ℝ)| ≤ b ^ 2 := by
  have hdiagR : ∀ i, (1 : ℝ) ≤ -M i i := fun i => by exact_mod_cast hdiag i
  have hb1 : 1 ≤ b := (hdiagR i).trans (hb i)
  obtain rfl | hij := eq_or_ne i j
  · rw [abs_of_neg (by linarith [hdiagR i])]
    nlinarith [hb i]
  rcases (hoff i j hij).eq_or_lt with h | h
  · rw [← h, Int.cast_zero, abs_zero]
    positivity
  have hji : (0 : ℝ) < M j i :=
    pos_of_mul_pos_right (hsymm i j ▸ mul_pos (hd i) (by exact_mod_cast h)) (hd j).le
  have h1 : (1 : ℝ) ≤ M i j := by exact_mod_cast h
  have hji1 : (1 : ℝ) ≤ M j i := by exact_mod_cast (show (0 : ℤ) < M j i by exact_mod_cast hji)
  rw [abs_of_pos (by linarith)]
  nlinarith [hminor i j hij, hb i, hb j, hdiagR i, hdiagR j,
    mul_le_mul (hb i) (hb j) (by linarith [hdiagR j]) (by linarith)]

/-- **The Leibniz bound.** An integral `s × s` matrix with `s ≤ N` and entries bounded by
`C ≥ 1` has `|det M| ≤ N! C^N`. -/
private theorem natAbs_det_le {s N C : ℕ} (hs : s ≤ N) (hC : 1 ≤ C)
    (M : Matrix (Fin s) (Fin s) ℤ) (hM : ∀ i j, |M i j| ≤ C) :
    M.det.natAbs ≤ N.factorial * C ^ N := by
  have h1 : |M.det| ≤ (s.factorial * C ^ s : ℕ) := by
    simpa using Matrix.det_le (abv := AbsoluteValue.abs) hM
  have h2 : s.factorial * C ^ s ≤ N.factorial * C ^ N :=
    Nat.mul_le_mul (Nat.factorial_le hs) (Nat.pow_le_pow_right hC hs)
  have h3 : (M.det.natAbs : ℤ) ≤ (N.factorial * C ^ N : ℕ) := by
    rw [Int.natCast_natAbs]; exact h1.trans (by exact_mod_cast h2)
  exact_mod_cast h3

/-- **Cramer's rule.** If `M` is an invertible integral matrix and every entry of `M c` lies in
`(1/q) ℤ`, then every entry of `c` lies in `(1/(q |det M|)) ℤ`. -/
private theorem exists_eq_div_of_mulVec {s q : ℕ} (hq : 0 < q) (M : Matrix (Fin s) (Fin s) ℤ)
    (hdet : M.det ≠ 0) (c : Fin s → ℝ) (hc : ∀ i, ∃ n : ℤ, ∑ j, (M i j : ℝ) * c j = n / q)
    (i : Fin s) : ∃ r : ℤ, c i = r / (q * M.det.natAbs) := by
  choose n hn using hc
  set A : Matrix (Fin s) (Fin s) ℝ := M.map (Int.cast : ℤ → ℝ) with hA
  have hAc : A *ᵥ c = fun i => (n i : ℝ) / q := by
    funext i; rw [← hn i]; rfl
  have hadj : A.adjugate = M.adjugate.map (Int.cast : ℤ → ℝ) :=
    ((Int.castRingHom ℝ).map_adjugate M).symm
  have hdetA : A.det = (M.det : ℝ) := ((Int.castRingHom ℝ).map_det M).symm
  have key : A.det • c = A.adjugate *ᵥ (A *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congrFun key i
  rw [hAc, hadj, hdetA] at hi
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  set T : ℤ := ∑ j, M.adjugate i j * n j with hT
  have hTR : ((T : ℤ) : ℝ) = ∑ j, (M.adjugate i j : ℝ) * n j := by rw [hT]; push_cast; rfl
  have hsum : ∑ j, (M.adjugate i j : ℝ) * ((n j : ℝ) / q) = (T : ℝ) / q := by
    rw [hTR, Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum] at hi
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  generalize M.det = d at *
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hi' : (d : ℝ) * c i * q = T := by rw [hi]; field_simp
  have hci : c i = (T : ℝ) / (q * (d : ℝ)) := by
    rw [eq_div_iff (mul_ne_zero hqR hdR)]; linear_combination hi'
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases le_or_gt 0 (d : ℝ) with h | h
  · exact ⟨T, by rw [hci, abs_of_nonneg h]⟩
  · exact ⟨-T, by rw [hci, abs_of_neg h, Int.cast_neg]; ring⟩

end LinearAlgebra

/-! ### The quasi-projective case -/

/-- **Bounded denominators on a quasi-projective surface.** On the minimal resolution of `S`, the
prime divisors over `x` number at most `N`; their normalized matrix has entries bounded by
`C = ⌈4/δ²⌉`, so `D = q |det M'| ≤ q N! C^N`, and every log discrepancy at `x` lies in
`(1/D) ℤ`. -/
private theorem exists_denominator_of_isQuasiProjectiveVariety {k : Type u} [Field k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsQuasiProjectiveVariety k sS]
    {B : QDivisor S} (hB : IsCharZeroPair sS B) (hS2 : topologicalKrullDim S = 2)
    {x : S} (hx : IsClosed ({x} : Set S))
    {q N : ℕ} (hq : 1 ≤ q) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
        (E.center : Set S) = {x} → (δ : ℝ) ≤ a)
    (hlow : {v : Valuation S.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver k sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a ∧
        (E.center : Set S) = {x} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ q * N.factorial * ⌈(4 : ℚ) / δ ^ 2⌉₊ ^ N ∧
      (∀ (E : DivisorOver k sS) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor B) E a →
          (E.center : Set S) = {x} → ∃ r : ℤ, a = r / D) := by
  classical
  have := hB.charZero
  have hBp : MMP.Mori.IsPair sS B := hB.isPair
  have hX : IsNormalVariety k sS := hBp.isNormalVariety
  have hSv : AlgebraicGeometry.IsVariety k sS := hX.1
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : QuasiCompact sS := hSv.toQuasiCompact
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  -- the minimal resolution `f : Y ⟶ S`
  obtain ⟨Y, hYi, hYn, f, hft, hmin, -⟩ := MMP.Resolution.exists_isMinimalSurfaceResolution sS hS2
  have hf := hmin.1
  have : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hsm : IsSmoothScheme (f ≫ sS) := hf.isSmoothScheme
  have hres : IsSmoothResolution sS f := ⟨inferInstance, hf.isBirationalMorphism, hsm⟩
  obtain ⟨hYv, -, -⟩ := hres.isNormalVariety hX
  have : IsNormal Y := hYv.2
  have : QuasiCompact (f ≫ sS) := hYv.1.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sS)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sS)
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  have hdimY : topologicalKrullDim Y = 2 := hf.dim_source_eq
  have hKnef := exists_isCanonicalDivisor_isRelativelyNef hmin hYv
  -- the prime divisors `E_1, …, E_s` of `Y` over `x`
  have hηx : f (genericPoint Y) ≠ x := by
    rw [map_genericPoint_of_isDominant]
    intro h
    have hu : (Set.univ : Set S) = {x} := by
      rw [← hx.closure_eq, ← h]
      exact (genericPoint_spec S).def.symm
    have : Subsingleton S := ⟨fun a b => by
      have ha : a ∈ ({x} : Set S) := hu ▸ Set.mem_univ a
      have hb : b ∈ ({x} : Set S) := hu ▸ Set.mem_univ b
      exact ha.trans hb.symm⟩
    have : DiscreteTopology S := Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology S
    rw [hS2] at h0
    exact absurd h0 (by decide)
  have hfin := finite_setOf_support_subset f hx hηx
  set T := hfin.toFinset with hT
  set s := T.card with hs
  let E : Fin s → MMP.Mori.PrimeDivisor Y := fun i => (T.equivFin.symm i).1
  have hEinj : Function.Injective E := fun i j h =>
    T.equivFin.symm.injective (Subtype.ext h)
  have hEx : ∀ i, (E i).support ⊆ f.base ⁻¹' {x} := fun i =>
    (Set.Finite.mem_toFinset hfin).mp (T.equivFin.symm i).2
  have hEall : ∀ P : MMP.Mori.PrimeDivisor Y, P.support ⊆ f.base ⁻¹' {x} → ∃ i, E i = P :=
    fun P hP => ⟨T.equivFin ⟨P, (Set.Finite.mem_toFinset hfin).mpr hP⟩, by simp [E]⟩
  -- their log discrepancies `α_i`
  let DE : Fin s → DivisorOver k sS := fun i =>
    ⟨Y, f, ⟨hYv.1, inferInstance⟩, hres.isBirationalMorphism, E i⟩
  choose α hα using fun i =>
    exists_isLogDiscrepancy_of_isPair hBp hS2 (DE i) (inferInstanceAs (IsProper f))
  have hcen : ∀ i, ((DE i).center : Set S) = {x} := fun i =>
    center_eq_singleton ⟨hYv.1, inferInstance⟩ hres.isBirationalMorphism hx (hEx i)
  have hδα : ∀ i, (δ : ℝ) ≤ α i := fun i => hδ (DE i) (α i) (hα i) (hcen i)
  -- the normalized intersection matrix
  obtain ⟨M, β, hMint, -, hαb, hdet, hdiag, hoff, hident, hint⟩ :=
    NormalizedMatrix.exists_int_normalized_intersectionMatrix hB hS2 hx hYv.1 hres
      hKnef E hEinj hEx hEall α hα
      (fun i => lt_of_lt_of_le (by exact_mod_cast hδ0) (hδα i))
  set d : Fin s → ℕ := fun i => Module.finrank k
    (cohomologyOverField k ((E i).idealSheaf.subschemeι ≫ f ≫ sS)
      (SheafOfModules.unit (E i).idealSheaf.subscheme.ringCatSheaf) 0) with hd
  -- `δ ≤ α_i ≤ 1`, so there are at most `N` prime divisors over `x`
  have hsN : s ≤ N := by
    have h1 : (Set.univ : Set (Fin s)).encard ≤ N := by
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun i => (DE i).valuation)
        ?_ (fun i _ j _ h => hEinj (eq_of_valuation_eq _ _ h))) hlow
      exact fun i _ => ⟨DE i, α i, hα i, hcen i, (hαb i).2, rfl⟩
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  -- the intersection matrix of the `E_i` is negative definite
  choose C hC hCc using fun i => exists_properCurve sS f hdimY hx (E i) (hEx i)
  set Nm : Fin s → Fin s → ℚ := fun i j =>
    (Divisor.toQDivisor (Finsupp.single (E i) 1)).intersectionNumber k (f ≫ sS) (C j).ι
      (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i)) with hNm
  have hNM : ∀ i j, Nm i j = (d i : ℚ) * M i j := fun i j =>
    (MMP.Mori.isIntersectionNumber_of_properCurve _ _ (C j) (E j) (hC j)).unique (hMint i j)
  have hneg := MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hYv.1 hsm hdimY hSv rfl hres.isBirationalMorphism E hEinj C hC hCc
  have hsymm : ∀ i j, Nm i j = Nm j i := fun i j =>
    MMP.Threefold.Resolution.intersectionNumber_single_comm hsm (E j) (E i) (C j) (C i)
      (hC j) (hC i)
  have hNii : ∀ i, Nm i i < 0 := fun i => by
    have h := hneg.diag_pos (i := i)
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at h
    exact_mod_cast h
  have hdpos : ∀ i, 0 < d i := fun i => by
    rcases Nat.eq_zero_or_pos (d i) with h0 | h0
    · have := hNii i
      rw [hNM, h0, Nat.cast_zero, zero_mul] at this
      exact absurd this (lt_irrefl 0)
    · exact h0
  have hdR : ∀ i, (0 : ℝ) < d i := fun i => by exact_mod_cast hdpos i
  -- the principal `2 × 2` minors are positive, and `d_i M_{ij} = d_j M_{ji}`
  have hminor : ∀ i j, i ≠ j → (M i j : ℝ) * M j i < M i i * M j j := by
    intro i j hij
    have h := mul_lt_mul_of_posDef hneg hij
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_mul_neg] at h
    have e : ∀ a b, ((Nm a b : ℚ) : ℝ) = (d a : ℝ) * M a b := fun a b => by
      rw [hNM]; push_cast; ring
    rw [e, e, e, e] at h
    have hpos : (0 : ℝ) < d i * d j := mul_pos (hdR i) (hdR j)
    have h' : (d i * d j : ℝ) * ((M i j : ℝ) * M j i) < (d i * d j : ℝ) * (M i i * M j j) := by
      linarith
    exact lt_of_mul_lt_mul_left h' hpos.le
  have hsymmM : ∀ i j, (d i : ℝ) * M i j = d j * M j i := fun i j => by
    have h := congrArg (fun t : ℚ => (t : ℝ)) (hsymm i j)
    simp only [hNM] at h
    push_cast at h
    exact h
  -- the entries of `M'` are bounded by `C = ⌈4 / δ²⌉`
  set Cb := ⌈(4 : ℚ) / δ ^ 2⌉₊ with hCb
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hCbR : (4 : ℝ) / (δ : ℝ) ^ 2 ≤ Cb := by
    have h := Nat.le_ceil ((4 : ℚ) / δ ^ 2)
    have h' : (((4 : ℚ) / δ ^ 2 : ℚ) : ℝ) ≤ ((Cb : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hbi : ∀ i, (-M i i : ℝ) ≤ 2 / δ := fun i => by
    rw [le_div_iff₀ hδR]
    nlinarith [hδα i, (hident i).2, (show (1 : ℝ) ≤ -M i i by exact_mod_cast hdiag i)]
  have hbound : ∀ i j, |M i j| ≤ (Cb : ℤ) := fun i j => by
    have h := abs_le_sq_of_symmetrizable M (fun i => (d i : ℝ)) hdR hsymmM hminor hdiag hoff
      hbi i j
    have e : (2 / (δ : ℝ)) ^ 2 = 4 / δ ^ 2 := by ring
    exact_mod_cast h.trans (e ▸ hCbR)
  have hC1 : 1 ≤ Cb := by
    have : (1 : ℝ) ≤ Cb := by
      refine le_trans ?_ hCbR
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    exact_mod_cast this
  -- `D = q |det M'|`
  have hdetle := natAbs_det_le hsN hC1 M hbound
  have hdet1 : 1 ≤ M.det.natAbs := Int.natAbs_pos.mpr hdet
  refine ⟨q * M.det.natAbs, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    ?_, ?_⟩
  · rw [mul_assoc]; exact Nat.mul_le_mul_left q hdetle
  · intro F a ha hc
    refine exists_eq_div_of_isLogDiscrepancy hBp hS2 hx hYv.1 hres E hEall α hα
      (Dvd.intro _ rfl) (by positivity) hqB (fun i => ?_) F a ha hc
    obtain ⟨r, hr⟩ := exists_eq_div_of_mulVec hq M hdet (fun j => α j - 1)
      (hint q hq hqB) i
    exact ⟨r, by rw [hr]; push_cast; ring⟩

/-! ### Restriction to an affine neighbourhood -/

section Open

variable {k : Type u} [Field k]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- An open immersion `U ⟶ X` restricted to its image is an isomorphism. -/
private theorem isIso_ι_restrict_self {X : Scheme.{u}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    refine ⟨fun y => ?_⟩
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (isIso_ι_restrict_self U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- **Log discrepancies over an open subscheme.** For a pair `(X, B)`, a proper divisor `D` over
`X` whose centre meets `U` and a proper divisor `D'` over `U` with the same valuation have the same
log discrepancies, for `B` and `B|_U` respectively. -/
private theorem isLogDiscrepancy_open_iff [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B) {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    (D : DivisorOver k sX) (hDp : IsProper D.f) (hDU : D.f D.E.genericPoint ∈ U)
    (D' : DivisorOver k (U.ι ≫ sX)) (hD'p : IsProper D'.f)
    (hv : D.valuation = D'.valuation.comap (functionFieldMap U.ι)) (a : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ↔
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a := by
  classical
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  obtain ⟨hXv, n0, K, hK, hQ⟩ := hB
  have hn0 : n0 = n := by
    have := hK.topologicalKrullDim_eq.symm.trans hn
    exact_mod_cast this
  subst hn0
  have hPW : MMP.Mori.IsPairWith sX n0 K B := ⟨hXv, hK, hQ⟩
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hXv, n0, K, hK, hQ⟩ hK D
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', -, hval, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPW D U hcen
  have hcU := (hiff c).1 hc
  have : IsProper (D.f ∣_ U) := by have := hDp; infer_instance
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcU.isPair hcU.2.1 D'
  have hDUv : DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)) =
      D'.valuation :=
    comap_injective_of_surjective (functionFieldMap_opens_ι_bijective U).2
      (hval.symm.trans hv)
  have hcc : (c' : ℝ) = c := by
    have h1 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc' (1 + c')).2
      ⟨hD'p, rfl⟩
    have h2 := (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcU (1 + c)).2
      ⟨inferInstance, rfl⟩
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h1 h2 hDUv.symm
    linarith
  rw [MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc,
    inverseTransformDivisor_ι_eq_restrictOpen,
    MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc', hcc]
  exact ⟨fun h => ⟨hD'p, h.2⟩, fun h => ⟨hDp, h.2⟩⟩

/-- Domination of local rings passes to the restriction of a valuation along a dominant
morphism. -/
private lemma dominates_comap {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    [IsDominant f] (w : Valuation Y.functionField (WithZero (Multiplicative ℤ))) (y : Y)
    (hle : ∀ a : Y.presheaf.stalk y, w (algebraMap _ Y.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y),
      w (algebraMap _ Y.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (f y),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (f y)),
        (w.comap (functionFieldMap f)) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hle _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hlt _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-- The valuation of a divisor over `Y`, restricted along a birational dominant `f : Y ⟶ X`, is a
divisor of the function field of `X`. -/
private lemma isDivisorOfFunctionField_comap {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (D : DivisorOver k (f ≫ sX)) :
    MMP.Flips.IsDivisorOfFunctionField k sX (D.valuation.comap (functionFieldMap f)) := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  letI := MMP.Mori.functionFieldAlgebra sX
  letI := MMP.Mori.functionFieldAlgebra (f ≫ sX)
  letI := MMP.Mori.functionFieldAlgebra (D.f ≫ f ≫ sX)
  letI := MMP.Mori.functionFieldMapAlgebra f
  letI := MMP.Mori.functionFieldMapAlgebra D.f
  have := MMP.Mori.isScalarTower_functionFieldMap sX f
  have := MMP.Mori.isScalarTower_functionFieldMap (f ≫ sX) D.f
  let e₀ : X.functionField →ₐ[k] D.Y.functionField :=
    (IsScalarTower.toAlgHom k Y.functionField D.Y.functionField).comp
      (IsScalarTower.toAlgHom k X.functionField Y.functionField)
  have he : Function.Bijective e₀ := D.isBirationalMorphism.functionFieldMap_bijective.comp hf
  refine ⟨D.Y, D.f ≫ f ≫ sX, D.isNormalVariety, D.E, AlgEquiv.ofBijective e₀ he, ?_⟩
  ext g
  rfl

/-- A proper divisor over an open subscheme `U` of `X` with a log discrepancy is realized by a
proper divisor over `X` with the same valuation, centre and log discrepancy. -/
private theorem exists_isLogDiscrepancy_of_opens [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {n : ℕ}
    (D' : DivisorOver k (U.ι ≫ sX)) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
      (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a) :
    ∃ D : DivisorOver k sX, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ∧
      D.valuation = D'.valuation.comap (functionFieldMap U.ι) ∧
      D.f D.E.genericPoint = U.ι (D'.f D'.E.genericPoint) := by
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  have : AlgebraicGeometry.IsVariety k sX := hB.1.1
  have hn : topologicalKrullDim X = n :=
    (topologicalKrullDim_opens_eq hB.1 U).symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha)
  have hv := isDivisorOfFunctionField_comap sX U.ι (functionFieldMap_opens_ι_bijective U) D'
  have hdom0 := divisorOver_dominates D' rfl
  have hdom := dominates_comap U.ι D'.valuation _ hdom0.1 hdom0.2
  obtain ⟨D, -, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX hv _ hdom.1 hdom.2
  have hDU : D.f D.E.genericPoint ∈ U := by
    rw [hDx]; exact (D'.f D'.E.genericPoint).2
  exact ⟨D.toDivisorOver, (isLogDiscrepancy_open_iff sX hB hn U D.toDivisorOver D.isProper hDU
    D' ha.2.1 hDv a).2 ha, hDv, hDx⟩

/-- A proper divisor over `X` whose centre meets `U`, with a log discrepancy, restricts to a
proper divisor over `U` with the same valuation, centre and log discrepancy. -/
private theorem exists_isLogDiscrepancy_restrict [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B)
    (U : X.Opens) [Nonempty U] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {n : ℕ}
    (D : DivisorOver k sX) (hDU : D.f D.E.genericPoint ∈ U) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a) :
    ∃ D' : DivisorOver k (U.ι ≫ sX), MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a ∧
      U.ι (D'.f D'.E.genericPoint) = D.f D.E.genericPoint ∧
      D.valuation = D'.valuation.comap (functionFieldMap U.ι) := by
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  have hn : topologicalKrullDim X = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨hXv, n0, K, hK, hQ⟩ := id hB
  have hn0 : n0 = n := by
    have := hK.topologicalKrullDim_eq.symm.trans hn
    exact_mod_cast this
  subst hn0
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', hE', hval, -⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hXv, hK, hQ⟩ D U hcen
  have hDp : IsProper D.f := ha.2.1
  have : IsProper (D.f ∣_ U) := by have := hDp; infer_instance
  refine ⟨⟨_, D.f ∣_ U, hY, hf, E'⟩, (isLogDiscrepancy_open_iff sX hB hn U D hDp hDU _
    inferInstance hval a).1 ha, ?_, hval⟩
  change U.ι ((D.f ∣_ U) E'.genericPoint) = _
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE',
    ← OpenWeilRestriction.genericPoint_primeDivisorMap]

end Open

end Denominators

/-! ### Transport of divisorial valuations to a generic fibre -/

namespace Transport

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  letI := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- The `k`-structure of a local ring of a `K`-scheme regarded over `k` is the composite one. -/
private lemma stalkAlgebra_comp_apply {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S' : Scheme.{u}} (sS : S' ⟶ Spec (.of K)) (f : S' ⟶ Spec (.of k))
    (hf : f = sS ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) (q : S') (c : k) :
    (letI := stalkAlgebra f q; algebraMap k (S'.presheaf.stalk q) c) =
      (letI := stalkAlgebra sS q; algebraMap K (S'.presheaf.stalk q) (algebraMap k K c)) := by
  have : (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ S'.presheaf.germ ⊤ q trivial =
      CommRingCat.ofHom (algebraMap k K) ≫ (Scheme.ΓSpecIso (.of K)).inv ≫
        sS.appTop ≫ S'.presheaf.germ ⊤ q trivial := by
    subst hf
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Category.assoc]
  exact congrArg (fun φ => φ.hom c) this

/-- **Transport of a divisorial valuation to a generic fibre.** Let `ι : S ⟶ U` be a dominant
morphism from a variety `S` over `K` to an integral scheme `U` over `k ⊆ K`, compatible with the
structure morphisms, inducing an isomorphism of function fields and an isomorphism of local rings
at `p`. A divisor `(Y', f', E')` over `U` with `f'(η_{E'}) = ι(p)` gives a divisor over `S`, with
projective morphism, the same valuation of the common function field and generic point over
`p`. -/
private theorem exists_properDivisorOver_comap_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {U S : Scheme.{u}} {sU : U ⟶ Spec (.of k)} {sS : S ⟶ Spec (.of K)}
    [IsIntegral U] [IsIntegral S] [AlgebraicGeometry.IsVariety K sS]
    (ι : S ⟶ U) [IsDominant ι] (hι : Function.Bijective (functionFieldMap ι))
    (hcomm : ι ≫ sU = sS ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (p : S) [IsIso (ι.stalkMap p)]
    (D' : DivisorOver k sU) (hD' : D'.f D'.E.genericPoint = ι p) :
    ∃ D : MMP.Flips.ProperDivisorOver K sS, IsProjective D.f ∧
      D.valuation.comap (functionFieldMap ι) = D'.valuation ∧ D.f D.E.genericPoint = p := by
  classical
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : LocallyOfFiniteType (D'.f ≫ sU) := D'.isNormalVariety.1.toLocallyOfFiniteType
  set e := RingEquiv.ofBijective (functionFieldMap ι) hι with he
  set θ := RingEquiv.ofBijective (functionFieldMap D'.f)
    D'.isBirationalMorphism.functionFieldMap_bijective with hθ
  set v : Valuation S.functionField ℤᵐ⁰ :=
    D'.valuation.comap (e.symm : S.functionField →+* U.functionField) with hvdef
  have hv : ∀ g, v (functionFieldMap ι g) = D'.valuation g := fun g => by
    rw [hvdef, Valuation.comap_apply]
    congr 1
    exact e.symm_apply_apply g
  have hvc : v.comap (functionFieldMap ι) = D'.valuation := by
    ext g
    exact hv g
  have hD'v : ∀ g, D'.valuation g = D'.E.divisorialValuation (θ g) := fun _ => rfl
  have hdom := Denominators.divisorOver_dominates D' hD'
  have hsurj : Function.Surjective (ι.stalkMap p).hom := fun a =>
    ⟨(inv (ι.stalkMap p)).hom a, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  have hle : ∀ a : S.presheaf.stalk p, v (algebraMap _ S.functionField a) ≤ 1 := by
    intro a
    obtain ⟨b, rfl⟩ := hsurj a
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, hv]
    exact hdom.1 b
  have hlt : ∀ a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk p),
      v (algebraMap _ S.functionField a) < 1 := by
    intro a ha
    obtain ⟨b, rfl⟩ := hsurj a
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, hv]
    refine hdom.2 b ((IsLocalRing.mem_maximalIdeal _).2 fun hb => ?_)
    exact (IsLocalRing.mem_maximalIdeal _).1 ha (hb.map _)
  -- a uniformizer
  obtain ⟨g₀, hg₀⟩ : ∃ g, D'.valuation g = WithZero.exp (-1) := by
    have := D'.E.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D'.E.localRing
    refine ⟨θ.symm (algebraMap D'.E.localRing D'.Y.functionField ϖ), ?_⟩
    rw [hD'v, RingEquiv.apply_symm_apply]
    exact D'.E.divisorialValuation_algebraMap_of_irreducible hϖ
  -- the valuation ring of `v` is essentially of finite type over `K`
  letI := functionFieldAlgebra sS
  have hK : ∀ c : K, v (algebraMap K S.functionField c) ≤ 1 := fun c => by
    letI := stalkAlgebra sS p
    have := isScalarTower_stalk_functionField sS p
    rw [IsScalarTower.algebraMap_apply K (S.presheaf.stalk p) S.functionField]
    exact hle _
  set R := v.valuationSubring with hR
  have hmemR : ∀ g, g ∈ R ↔ v g ≤ 1 := fun g => Valuation.mem_valuationSubring_iff v g
  letI algKR : Algebra K R :=
    (RingHom.codRestrict (algebraMap K S.functionField) R.toSubring
      (fun c => (hmemR _).2 (hK c))).toAlgebra
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI := stalkAlgebra (D'.f ≫ sU) D'.E.genericPoint
  have := essFiniteType_stalkAlgebra (D'.f ≫ sU) D'.E.genericPoint
  have hmemψ : ∀ o : D'.E.localRing,
      e (θ.symm (algebraMap D'.E.localRing D'.Y.functionField o)) ∈ R.toSubring := fun o => by
    rw [ValuationSubring.mem_toSubring, hmemR, he, RingEquiv.ofBijective_apply, hv, hD'v,
      RingEquiv.apply_symm_apply, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨o, rfl⟩
  let ψr : D'.E.localRing →+* R :=
    RingHom.codRestrict (((e : U.functionField →+* S.functionField).comp
      (θ.symm : D'.Y.functionField →+* U.functionField)).comp
        (algebraMap D'.E.localRing D'.Y.functionField)) R.toSubring hmemψ
  have hψc : ∀ c : k, ψr (algebraMap k D'.E.localRing c) = algebraMap k R c := by
    intro c
    apply Subtype.ext
    change e (θ.symm (algebraMap D'.E.localRing D'.Y.functionField
      (algebraMap k D'.E.localRing c))) = algebraMap K S.functionField (algebraMap k K c)
    letI := functionFieldAlgebra (D'.f ≫ sU)
    letI := functionFieldAlgebra sU
    letI := functionFieldMapAlgebra D'.f
    have := isScalarTower_stalk_functionField (D'.f ≫ sU) D'.E.genericPoint
    have := isScalarTower_functionFieldMap sU D'.f
    rw [← IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField,
      IsScalarTower.algebraMap_apply k U.functionField D'.Y.functionField]
    change e (θ.symm (θ _)) = _
    rw [RingEquiv.symm_apply_apply, he, RingEquiv.ofBijective_apply]
    letI := functionFieldAlgebra (ι ≫ sU)
    letI := functionFieldMapAlgebra ι
    have := isScalarTower_functionFieldMap sU ι
    change algebraMap U.functionField S.functionField _ = _
    rw [← IsScalarTower.algebraMap_apply k U.functionField S.functionField]
    exact stalkAlgebra_comp_apply sS (ι ≫ sU) hcomm (genericPoint S) c
  let ψ : D'.E.localRing →ₐ[k] R := { ψr with commutes' := hψc }
  have hψ : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    have h1 : D'.E.divisorialValuation (θ (e.symm r)) ≤ 1 := by
      rw [← hD'v, ← hv, show functionFieldMap ι (e.symm r) = r from e.apply_symm_apply r]
      exact (hmemR r).1 hr
    obtain ⟨o, ho⟩ := (MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff _ _).1 h1
    refine ⟨o, Subtype.ext ?_⟩
    change e (θ.symm (algebraMap D'.E.localRing D'.Y.functionField o)) = r
    rw [ho, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
  have : Algebra.EssFiniteType k R := Algebra.EssFiniteType.of_surjective ψ hψ
  have : Algebra.EssFiniteType K R := Algebra.EssFiniteType.of_comp k K R
  let φ : R →ₐ[K] S.functionField :=
    { toRingHom := R.subtype
      commutes' := fun _ => rfl }
  have hS : ∀ g, v g ≤ 1 ↔ g ∈ φ.range := fun g => by
    rw [← hmemR]
    exact ⟨fun h => ⟨⟨g, h⟩, rfl⟩, by rintro ⟨r, rfl⟩; exact r.2⟩
  obtain ⟨D, hDp, hDv, hDx⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType sS
      ⟨R, inferInstance, inferInstance, inferInstance, φ, hS⟩ (g₀ := e g₀)
      (by rw [he, RingEquiv.ofBijective_apply, hv]; exact hg₀) p hle hlt
  exact ⟨D, hDp, by rw [hDv]; exact hvc, hDx⟩

/-- A dominant morphism of integral schemes inducing an isomorphism of local rings at one point
induces an isomorphism of function fields. -/
private theorem functionFieldMap_bijective_of_isIso_stalkMap {S U : Scheme.{u}} [IsIntegral S]
    [IsIntegral U] (ι : S ⟶ U) [IsDominant ι] (p : S) [IsIso (ι.stalkMap p)] :
    Function.Bijective (functionFieldMap ι) := by
  refine ⟨(functionFieldMap ι).injective, fun g => ?_⟩
  have hsurj : Function.Surjective (ι.stalkMap p).hom := fun a =>
    ⟨(inv (ι.stalkMap p)).hom a, by
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S.presheaf.stalk p) g
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  refine ⟨algebraMap _ U.functionField a' / algebraMap _ U.functionField b', ?_⟩
  rw [map_div₀, MMP.Mori.functionFieldMap_algebraMap_stalk,
    MMP.Mori.functionFieldMap_algebraMap_stalk]

end Transport

/-! ### The stabilized tail -/

/-- A divisor over `Y` whose centre is the closure of `y` has its generic point over `y`. -/
private theorem map_genericPoint_eq_of_center_eq_closure {k' : Type u} [Field k'] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k')} (E : DivisorOver k' s) {y : Y}
    (h : (E.center : Set Y) = closure {y}) : E.f E.E.genericPoint = y := by
  rw [E.center_eq_closure_genericPoint] at h
  exact (inseparable_iff_closure_eq.mpr h).eq

open Denominators Transport in
/-- **Bounded denominators at a codimension-two point.** Let `(X, B)` be a pair over an
algebraically closed field of characteristic zero and `x ∈ X` a point of codimension two. Let
`q ≥ 1` with `qB` integral, `0 < δ ≤ 1` a lower bound for the log discrepancies of the divisors
over `X` with centre `closure {x}`, and `N` a bound for the size of `I(X, B)`. Then there is
`1 ≤ D ≤ q N! ⌈4/δ²⌉^N` such that every log discrepancy of a divisor over `X` with centre
`closure {x}` lies in `(1/D) ℤ`. -/
private theorem exists_denominator_of_coheight_eq_two {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {x : X} (hx : Order.coheight x = 2)
    {q N : ℕ} (hq : 1 ≤ q) (hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * B.coeff P = n)
    {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E a →
        (E.center : Set X) = closure {x} → (δ : ℝ) ≤ a)
    (hlow : (lowDiscrepancySet sX B).encard ≤ N) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ q * N.factorial * ⌈(4 : ℚ) / δ ^ 2⌉₊ ^ N ∧
      ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E a →
          (E.center : Set X) = closure {x} → ∃ r : ℤ, a = r / D := by
  classical
  have := hB.charZero
  obtain ⟨U, hxU, hUa, iU1, iU2, iU3, d, K, iK, iKa, -, hdimX, S, sS, iS1, iS2, iS3, iS4, iS5,
    hSa, hSv, hS2, ι, iι, p, hpcl, hcomm, hιp, hiso, -, BS, hBSp, hBS0, hBScoeff, htr⟩ :=
    MMP.Threefold.exists_generic_surface_of_coheight_eq_two sX hB hx
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : IsAffine S := hSa
  have : AlgebraicGeometry.IsVariety K sS := hSv.1
  have : IsQuasiProjectiveVariety K sS :=
    { toIsVariety := hSv.1
      isQuasiProjective := isQuasiProjective_of_isQuasiAffineHom _ inferInstance }
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have := hiso
  have hιbij := functionFieldMap_bijective_of_isIso_stalkMap ι p
  have hUbij := functionFieldMap_opens_ι_bijective U
  set xU : U.toScheme := ⟨x, hxU⟩ with hxUdef
  -- the boundary of `S` is `q`-integral
  have hqBS : ∀ P, ∃ n : ℤ, (q : ℚ) * BS.coeff P = n := fun P => by
    obtain ⟨P', -, hP'⟩ := hBScoeff P
    rw [hP']
    exact hqB P'
  -- divisors over `S` centred at `p` are divisors over `X` centred at `x`
  have hSX : ∀ (E : DivisorOver K sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor BS) E a →
        (E.center : Set S) = {p} →
      ∃ E0 : DivisorOver k sX,
        MMP.Intersection.IsLogDiscrepancy sX (d + 2) (QDivisor.toRDivisor B) E0 a ∧
        E0.valuation = (E.valuation.comap (functionFieldMap ι)).comap (functionFieldMap U.ι) ∧
        (E0.center : Set X) = closure {x} := by
    intro E a ha hEc
    obtain ⟨D', hD'c, hD'v, hiff⟩ := htr E ha.2.1 hEc
    obtain ⟨E0, hE0, hE0v, hE0x⟩ :=
      exists_isLogDiscrepancy_of_opens hB.isPair U D' a ((hiff a).1 ha)
    refine ⟨E0, hE0, by rw [hE0v, hD'v], ?_⟩
    rw [E0.center_eq_closure_genericPoint, hE0x, map_genericPoint_eq_of_center_eq_closure D' hD'c]
    rfl
  have hδS : ∀ (E : DivisorOver K sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor BS) E a →
        (E.center : Set S) = {p} → (δ : ℝ) ≤ a := fun E a ha hEc => by
    obtain ⟨E0, hE0, -, hE0c⟩ := hSX E a ha hEc
    exact hδ _ E0 a hE0 hE0c
  have hlowS : {v : Valuation S.functionField (WithZero (Multiplicative ℤ)) |
      ∃ (E : DivisorOver K sS) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sS 2 (QDivisor.toRDivisor BS) E a ∧
        (E.center : Set S) = {p} ∧ a ≤ 1 ∧ E.valuation = v}.encard ≤ N := by
    refine le_trans (Set.encard_le_encard_of_injOn
      (f := fun v => (v.comap (functionFieldMap ι)).comap (functionFieldMap U.ι)) ?_ ?_) hlow
    · rintro v ⟨E, a, ha, hEc, ha1, rfl⟩
      obtain ⟨E0, hE0, hE0v, hE0c⟩ := hSX E a ha hEc
      have hc : E0.center = IrreducibleCloseds.closureSingleton x := IrreducibleCloseds.ext hE0c
      refine ⟨⟨E0, hE0.2.1, hE0v.symm, ?_⟩, a, ⟨d + 2, E0, hE0.2.1, hE0v, hE0⟩, ha1⟩
      rw [hc, MMP.Flips.codimension_closureSingleton, hx]
    · intro v _ w _ h
      exact comap_injective_of_surjective hιbij.2 (comap_injective_of_surjective hUbij.2 h)
  obtain ⟨D, hD1, hDle, hden⟩ := exists_denominator_of_isQuasiProjectiveVariety
    (⟨inferInstance, hBSp, hBS0⟩ : IsCharZeroPair sS BS) hS2 hpcl hq hqBS hδ0 hδ1 hδS hlowS
  refine ⟨D, hD1, hDle, fun n E a ha hEc => ?_⟩
  have hEx := map_genericPoint_eq_of_center_eq_closure E hEc
  obtain ⟨E', hE', hE'η, hE'v⟩ :=
    exists_isLogDiscrepancy_restrict hB.isPair U E (by rw [hEx]; exact hxU) a ha
  have hE'x : E'.f E'.E.genericPoint = ι p := by
    rw [hιp]
    exact U.ι.isOpenEmbedding.injective (hE'η.trans hEx)
  obtain ⟨DS, -, hDSv, hDSx⟩ :=
    exists_properDivisorOver_comap_eq (sU := U.ι ≫ sX) ι hιbij hcomm p E' hE'x
  have hDSc : (DS.toDivisorOver.center : Set S) = {p} := by
    rw [DS.toDivisorOver.center_eq_closure_genericPoint]
    change closure {DS.f DS.E.genericPoint} = _
    rw [hDSx, hpcl.closure_eq]
  obtain ⟨aS, haS⟩ := exists_isLogDiscrepancy_of_isPair hBSp hS2 DS.toDivisorOver DS.isProper
  have hcmp : aS = a := by
    obtain ⟨D'', -, hD''v, hiff⟩ := htr DS.toDivisorOver DS.isProper hDSc
    exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ((hiff aS).1 haS) hE'
      (hD''v.trans hDSv)
  obtain ⟨r, hr⟩ := hden _ aS haS hDSc
  exact ⟨r, hcmp ▸ hr⟩

/-- If every log discrepancy of a divisor centred at `closure {x}` is a positive multiple of
`1 / D`, then the minimal log discrepancy at `x`, when it is at most one, is `m / D` for some
`0 < m ≤ D`. -/
private theorem exists_minimalLogDiscrepancy_eq_div {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {x : X} {D : ℕ} (hD : 1 ≤ D)
    (hden : ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E a →
        (E.center : Set X) = closure {x} → ∃ m : ℕ, 0 < m ∧ a = m / D)
    (hle : minimalLogDiscrepancy sX B x ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ m ≤ D ∧ minimalLogDiscrepancy sX B x = (((m : ℝ) / D : ℝ) : EReal) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  set T : Set EReal := {t : EReal | ∃ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) E a ∧
      (E.center : Set X) = closure {x} ∧ t = a} with hT
  have hmld : minimalLogDiscrepancy sX B x = sInf T := rfl
  have hTm : ∀ t ∈ T, ∃ m : ℕ, 0 < m ∧ t = (((m : ℝ) / D : ℝ) : EReal) := by
    rintro t ⟨n, E, a, ha, hc, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hden n E a ha hc
    exact ⟨m, hm, rfl⟩
  have hne : T.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hmld, h, sInf_empty] at hle
    exact absurd hle (not_le.mpr (by exact_mod_cast EReal.coe_lt_top 1))
  obtain ⟨t₀, ht₀⟩ := hne
  have hP : ∃ m : ℕ, (((m : ℝ) / D : ℝ) : EReal) ∈ T := by
    obtain ⟨m, -, rfl⟩ := hTm t₀ ht₀
    exact ⟨m, ht₀⟩
  have hleast : IsLeast T (((Nat.find hP : ℝ) / D : ℝ) : EReal) := by
    refine ⟨Nat.find_spec hP, fun t ht => ?_⟩
    obtain ⟨m, -, rfl⟩ := hTm t ht
    have hm : Nat.find hP ≤ m := Nat.find_min' hP ht
    exact EReal.coe_le_coe_iff.mpr
      (div_le_div_of_nonneg_right (by exact_mod_cast hm) hDpos.le)
  have heq : minimalLogDiscrepancy sX B x = (((Nat.find hP : ℝ) / D : ℝ) : EReal) := by
    rw [hmld, hleast.csInf_eq]
  obtain ⟨m, hm0, hm⟩ := hTm _ (Nat.find_spec hP)
  refine ⟨Nat.find hP, ?_, ?_, heq⟩
  · have h := EReal.coe_injective hm
    rw [div_left_inj' hDpos.ne'] at h
    have : (Nat.find hP : ℝ) = m := h
    exact_mod_cast (show (0 : ℝ) < Nat.find hP by rw [this]; exact_mod_cast hm0)
  · have h1 : ((Nat.find hP : ℝ) / D : ℝ) ≤ 1 := by
      rw [heq] at hle
      exact_mod_cast hle
    rw [div_le_one hDpos] at h1
    exact_mod_cast h1

namespace StabilizedTail

/-- **A finite generic curve-mld set on a stabilized tail.** Let `δ > 0` bound every log
discrepancy `a(ξ; X_i, B_i)` of every normalized divisorial valuation at every stage of the tail
`T` from below. Then there are `D_max ≥ 1` and a finite `F ⊆ (0, 1] ∩ ℚ` such that for every
`i` and every irreducible curve `V ⊆ X_i` there is `1 ≤ D ≤ D_max` with: every log discrepancy
`a(ξ; X_i, B_i)` of a valuation `ξ` with centre `V` lies in `(1/D)ℤ` and is at least `δ`; and
`mld_{η_V}(X_i, B_i) ∈ F` if `mld_{η_V}(X_i, B_i) ≤ 1`. -/
@[mmp "thm_mmp_indexc_curve_mld_finite"]
public theorem exists_logDiscrepancy_denom_le_and_minimalLogDiscrepancy_mem (T : StabilizedTail)
    {δ : ℝ} (hδpos : 0 < δ)
    (hδ : ∀ i (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))),
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ (T.sX i) ξ →
        ∀ a : ℝ, T.IsLogDiscrepancyAt i ξ a → δ ≤ a) :
    ∃ Dmax : ℕ, 1 ≤ Dmax ∧ ∃ F : Finset ℚ, (F : Set ℚ) ⊆ Set.Ioc 0 1 ∧
      ∀ i (V : IrreducibleCloseds (T.X i)), topologicalKrullDim (V : Set (T.X i)) = 1 →
        ∃ D : ℕ, 1 ≤ D ∧ D ≤ Dmax ∧
          (∀ (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))),
            MMP.Intersection.IsCentre ℂ (T.sX i) ξ V → ∀ a : ℝ, T.IsLogDiscrepancyAt i ξ a →
              (∃ n : ℤ, a = n / D) ∧ δ ≤ a) ∧
          (minimalLogDiscrepancy (T.sX i) (T.B i) V.isIrreducible.genericPoint ≤ 1 →
            ∃ x ∈ F, minimalLogDiscrepancy (T.sX i) (T.B i) V.isIrreducible.genericPoint =
              ((x : ℝ) : EReal)) := by
  classical
  obtain ⟨q, -, hq, -, hG, -, hfin⟩ := T.exists_smul_eq_and_inv_le_and_ncard_eq
  obtain ⟨δ', hδ'0, hδ'lt⟩ := exists_rat_btwn (lt_min hδpos one_pos)
  set N := T.lowDiscrepancySetLimit.ncard with hN
  set Dmax := q * N.factorial * ⌈(4 : ℚ) / δ' ^ 2⌉₊ ^ N with hDmax
  have hδ'0' : (0 : ℚ) < δ' := by exact_mod_cast hδ'0
  have hδ'δ : (δ' : ℝ) ≤ δ := hδ'lt.le.trans (min_le_left _ _)
  have hδ'1 : δ' ≤ 1 := by exact_mod_cast hδ'lt.le.trans (min_le_right δ 1)
  have hC : 0 < ⌈(4 : ℚ) / δ' ^ 2⌉₊ := Nat.ceil_pos.2 (by positivity)
  have hDmax1 : 1 ≤ Dmax :=
    Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (by positivity))
  let F : Finset ℚ := ((Finset.Icc 1 Dmax ×ˢ Finset.range (Dmax + 1)).image
    (fun pr : ℕ × ℕ => (pr.2 : ℚ) / pr.1)).filter (fun y => 0 < y ∧ y ≤ 1)
  refine ⟨Dmax, hDmax1, F, fun y hy => (Finset.mem_filter.1 hy).2, fun i V hV => ?_⟩
  set x := V.isIrreducible.genericPoint with hxdef
  have hVx : closure {x} = (V : Set (T.X i)) :=
    (IsIrreducible.isGenericPoint_genericPoint V.isIrreducible V.isClosed).def
  have hBp : MMP.Fourfold.IsPair (T.sX i) (T.B i) := (T.isKltPair i).1
  have : LocallyOfFiniteType (T.sX i) := hBp.isPair.1.1.toLocallyOfFiniteType
  have hx : Order.coheight x = 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T.sX i) x
    rw [hVx, hV, T.dim_eq i] at h
    generalize Order.coheight x = c at h ⊢
    have h' : ((1 + c : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
      rwa [WithBot.coe_add]
    have h'' : 1 + c = 3 := WithBot.coe_injective h'
    induction c using ENat.recTopCoe with
    | top => simp at h''
    | coe c =>
      have : 1 + c = 3 := by exact_mod_cast h''
      obtain rfl : c = 2 := by omega
      rfl
  have hqB : ∀ P, ∃ n : ℤ, (q : ℚ) * (T.B i).coeff P = n := by
    obtain ⟨G, hGi⟩ := hG i
    intro P
    refine ⟨G P, ?_⟩
    have h := congrArg (fun D : QDivisor (T.X i) => D.coeff P) hGi
    simp only [Divisor.coeff_toQDivisor] at h
    rw [show (G P : ℚ) = ((G.coeff P : ℤ) : ℚ) from rfl, h]
    simp [DivisorWithCoeffs.coeff]
  have hδX : ∀ (n : ℕ) (E : DivisorOver ℂ (T.sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (T.sX i) n (QDivisor.toRDivisor (T.B i)) E a →
        (E.center : Set (T.X i)) = closure {x} → (δ' : ℝ) ≤ a := fun n E a ha _ =>
    hδ'δ.trans (hδ i E.valuation ⟨E, ha.2.1, rfl⟩ a ⟨n, E, ha.2.1, rfl, ha⟩)
  have hlow : (lowDiscrepancySet (T.sX i) (T.B i)).encard ≤ N := by
    rw [← (hfin i).1.cast_ncard_eq, (hfin i).2]
  obtain ⟨D, hD1, hDle, hden⟩ :=
    exists_denominator_of_coheight_eq_two (T.sX i) hBp hx hq hqB hδ'0' hδ'1 hδX hlow
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  refine ⟨D, hD1, hDle, fun ξ hξ a ha => ?_, fun hle => ?_⟩
  · obtain ⟨E1, hE1p, rfl, hV1⟩ := hξ
    obtain ⟨n0, E0, hE0p, hE0v, ha0⟩ := ha
    obtain ⟨a1, ha1⟩ := exists_isLogDiscrepancy_of_isPair hBp.isPair (T.dim_eq i) E1 hE1p
    have h1 : a1 = a := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha1 ha0 hE0v.symm
    subst h1
    exact ⟨hden 3 E1 a1 ha1 (by rw [← hV1, hVx]),
      hδ i _ ⟨E1, hE1p, rfl⟩ a1 ⟨n0, E0, hE0p, hE0v, ha0⟩⟩
  · have hden' : ∀ (n : ℕ) (E : DivisorOver ℂ (T.sX i)) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy (T.sX i) n (QDivisor.toRDivisor (T.B i)) E a →
          (E.center : Set (T.X i)) = closure {x} → ∃ m : ℕ, 0 < m ∧ a = m / D := by
      intro n E a ha hc
      obtain ⟨r, hr⟩ := hden n E a ha hc
      have hr0 : (0 : ℝ) < r := by
        have h0 : (0 : ℝ) < δ' := by exact_mod_cast hδ'0
        have : (0 : ℝ) < r / D := hr ▸ h0.trans_le (hδX n E a ha hc)
        exact (div_pos_iff_of_pos_right hDpos).mp this
      have hr0' : 0 < r := by exact_mod_cast hr0
      refine ⟨r.toNat, by omega, ?_⟩
      rw [hr]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg hr0'.le).symm
    obtain ⟨m, hm0, hmD, hmld⟩ := exists_minimalLogDiscrepancy_eq_div hD1 hden' hle
    have hDq : (0 : ℚ) < D := by exact_mod_cast hD1
    refine ⟨(m : ℚ) / D, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(D, m),
      Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hD1, hDle⟩, Finset.mem_range.2 (by omega)⟩, rfl⟩,
      by positivity, (div_le_one hDq).2 (by exact_mod_cast hmD)⟩, ?_⟩
    rw [hmld]
    push_cast
    rfl

end StabilizedTail

open MMP.Flips

/-! ### Log discrepancies off the bad locus -/

section OffBadLocus

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme is that of its closure,
through the identification of function fields. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext t
  change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [functionFieldMap_id_apply]

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {W Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- `functionFieldMap` only depends on the morphism. -/
private theorem functionFieldMap_congr {A C : Scheme.{0}} [IsIntegral A] [IsIntegral C]
    {a b : A ⟶ C} (hab : a = b) [IsDominant a] [IsDominant b] (t : C.functionField) :
    functionFieldMap a t = functionFieldMap b t := by
  subst hab
  rfl

/-- **Crepant invariance**, with the structure morphism of the source given up to equality: if
`ΔY` is the crepant boundary of `(X, Δ)` along a birational `φ : Y ⟶ X`, divisors over `Y` and
over `X` with corresponding valuations have the same discrepancies. -/
private theorem isDiscrepancy_iff_of_crepant {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {KX : Divisor X} {Δ : QDivisor X}
    {KY : Divisor Y} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ)
    (hKX : KX.IsCanonicalDivisor sX n) (φ : Y ⟶ X) [IsDominant φ] (hs : φ ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hφ : IsBirationalMorphism φ) (hKY : KY.IsCanonicalDivisor sY n)
    (hcb : ∀ (F : MMP.Mori.PrimeDivisor Y) (D : DivisorOver ℂ sX), D.valuation = F.valuationOver φ →
      IsDiscrepancy sX n KX Δ D (-ΔY.coeff F))
    (E : DivisorOver ℂ sY) (E' : DivisorOver ℂ sX)
    (hv : E'.valuation = E.valuation.comap (functionFieldMap φ)) (a : ℚ) :
    IsDiscrepancy sY n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a := by
  subst hs
  have hcb' : IsCrepantBoundary sX n KX Δ φ hY hφ ΔY := fun F => hcb F _ rfl
  exact (IsPair.isDiscrepancy_iff_of_crepant hP φ hY hφ hKX hKY (Or.inl hcb')).2 E E' hv a

/-- Off the bad locus the log discrepancies of corresponding divisors agree. -/
private theorem eq_of_not_subset_badLocusPlus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hc : ¬ (Dp.center : Set Xp) ⊆ badLocusPlus fm fp)
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am = ap := by
  have : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  have := h.isBirationalMorphism_minus.isDominant
  have := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxW⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [coe_badLocusPlus, coe_badLocusBase] at hxW
    simpa using hxW
  -- dimensions and canonical divisors
  obtain ⟨mp, hKp⟩ := h.isCanonicalDivisor_plus
  obtain ⟨mm, hKm⟩ := h.isCanonicalDivisor
  obtain rfl : mp = n := by
    exact_mod_cast hKp.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hap)
  obtain rfl : mm = n' := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ham)
  obtain rfl : mm = mp := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (h.dim_minus.trans (h.dim_plus.symm.trans hKp.topologicalKrullDim_eq))
  have hPp : IsPairWith sXp mm (flipTransform fm fp K) (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, hKp, h.isQCartier_plus⟩
  obtain ⟨cp, hcp⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp.isPair hKp Dp
  obtain ⟨cm, hcm⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm Dm
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcp ap).mp hap).2,
    ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcm am).mp ham).2]
  suffices hcc : cm = cp by rw [hcc]
  -- restriction of `Dp` to `V⁺ = (f⁺)⁻¹(U)`
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPp Dp _ hU
  have hcE := (hiff cp).mp hcp
  -- the identification `V⁺ ≅ V⁻ ⊆ X⁻` over `U`
  have : Nonempty (fp ⁻¹ᵁ commonBiregularLocus fm fp) := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
  have : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  have : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  let φ : (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ⟶ Xm :=
    (fp ∣_ commonBiregularLocus fm fp) ≫ inv (fm ∣_ commonBiregularLocus fm fp) ≫
      (fm ⁻¹ᵁ commonBiregularLocus fm fp).ι
  have hφ : φ ≫ fm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hs : φ ≫ sXm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, hφ, Category.assoc]
  have : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  have hφb : IsBirationalMorphism φ := isBirationalMorphism_of_isOpenImmersion φ
  have : IsDominant φ := hφb.isDominant
  have : IsDominant (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι :=
    Opens.isDominant_ι ((fp ⁻¹ᵁ commonBiregularLocus fm fp).isOpen.dense
      ⟨hU.choose, hU.choose_spec.2⟩)
  have : IsDominant (φ ≫ fm) := inferInstance
  have : IsDominant ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp) := inferInstance
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective.2
  -- valuations of prime divisors of `V⁺`, read on `k(X⁻)` and on `k(X⁺)`
  have hvF : ∀ F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme,
      (F.valuationOver φ).comap (functionFieldMap fm) =
        MMP.Mori.PrimeDivisor.valuationOver
          (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F) fp := by
    intro F
    ext t
    simp only [MMP.Mori.PrimeDivisor.valuationOver, Valuation.comap_apply]
    rw [divisorialValuation_primeDivisorMap, Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hvE : Dm.valuation = (DivisorOver.valuation (⟨_, Dp.f ∣_ _, hY, hf, E'⟩ :
      DivisorOver ℂ ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp))).comap
        (functionFieldMap φ) := by
    apply comap_injective_of_surjective hfm
    rw [← hv, hval]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hcb : ∀ (F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme)
      (D : DivisorOver ℂ sXm), D.valuation = F.valuationOver φ →
      IsDiscrepancy sXm mm K B D
        (-((flipTransform fm fp B).restrictOpen (fp ⁻¹ᵁ commonBiregularLocus fm fp)).coeff F) := by
    intro F D hD
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨Pm, -, hPm, -, -, -, hcoef, -⟩ := h.exists_primeDivisor_valuationOver_eq
      (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F)
    rw [hcoef]
    obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm
      (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm)
    obtain ⟨cD, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm D
    have hvD :
        D.valuation = (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm).valuation := by
      rw [valuation_ofPrimeDivisor, hD]
      apply comap_injective_of_surjective hfm
      rw [hvF, ← hPm]
      rfl
    have e := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvD
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq h.isNormalVariety_minus hvD)
      hcD hc₀
    rw [← hc₀.eq_neg_coeff_of_ofPrimeDivisor h.isNormalVariety_minus, ← e]
    exact hcD
  have hcrep := isDiscrepancy_iff_of_crepant hB.isPair hKm φ hs hcE.1 hφb hcE.2.1 hcb
    ⟨_, Dp.f ∣_ _, hY, hf, E'⟩ Dm hvE cp
  exact hcm.eq (hcrep.mp hcE)

/-- **The comparison** `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`. -/
private theorem le_of_isLogDiscrepancy (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am ≤ ap := by
  by_cases hc : (Dp.center : Set Xp) ⊆ badLocusPlus fm fp
  · have ham' : IsValuationLogDiscrepancy sXm B Dm.valuation am := ⟨n', Dm, hDm, rfl, ham⟩
    have hap' : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) Dp.valuation ap :=
      ⟨n, Dp, hap.2.1, rfl, hap⟩
    have hCm : MMP.Intersection.IsCentre ℂ sXm Dm.valuation Dm.center := ⟨Dm, hDm, rfl, rfl⟩
    have hCp : MMP.Intersection.IsCentre ℂ sXp Dp.valuation Dp.center :=
      ⟨Dp, hap.2.1, rfl, rfl⟩
    have hT := IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hv
      ham' hap' hCm hCp
    exact (show am < ap from (hT.out 3 1).mp hc).le
  · exact (eq_of_not_subset_badLocusPlus h hB Dp Dm hv hc hap ham).le

end OffBadLocus

namespace StabilizedTail

/-! ### Attainment of generic minimal log discrepancies -/

/-- Every element of `I(X_j, B_j)` is the transport of an element of `I_∞`. -/
private theorem exists_mem_isTransportedValuationFrom (T : StabilizedTail) :
    ∀ (j : ℕ) {ξ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))},
      ξ ∈ lowDiscrepancySet (T.sX j) (T.B j) →
        ∃ ν ∈ T.lowDiscrepancySetLimit, T.IsTransportedValuationFrom j ν ξ
  | 0, ξ, hξ => ⟨ξ, hξ, rfl⟩
  | j + 1, ξ, hξ => by
    have : IsIntegral (T.Z j) := (T.isThreefoldStepDiagram j).isNormalVariety_target.1.toIsIntegral
    have := (T.isThreefoldStepDiagram j).isBirationalMorphism_minus.isDominant
    have := (T.isThreefoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmem : ξ.comap (functionFieldMap (T.fp j)) ∈
        valuationsOver (T.fp j) (lowDiscrepancySet (T.sX (j + 1)) (T.B (j + 1))) := ⟨ξ, hξ, rfl⟩
    rw [← T.lowDiscrepancySet_eq j] at hmem
    obtain ⟨u, hu, hue⟩ := hmem
    obtain ⟨ν, hν, hνu⟩ := exists_mem_isTransportedValuationFrom T j hu
    exact ⟨ν, hν, u, hνu, hue.symm⟩

/-- A nonempty set of extended reals all of whose elements are of the form `m / D`, `m : ℕ`, for
a fixed `D > 0`, contains its infimum as soon as that infimum is finite. -/
private theorem sInf_mem_of_forall_eq_natCast_div {S : Set EReal} {D : ℝ} (hD : 0 < D)
    (hS : sInf S ≠ ⊤) (h : ∀ t ∈ S, ∃ m : ℕ, t = ((m / D : ℝ) : EReal)) : sInf S ∈ S := by
  classical
  have hex : ∃ m : ℕ, ((m / D : ℝ) : EReal) ∈ S :=
    let ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 fun h : S = ∅ => hS (h ▸ sInf_empty)
    let ⟨m, hm⟩ := h t ht
    ⟨m, hm ▸ ht⟩
  convert Nat.find_spec hex
  refine le_antisymm (sInf_le (Nat.find_spec hex)) (le_sInf fun t ht => ?_)
  obtain ⟨m, rfl⟩ := h t ht
  exact EReal.coe_le_coe_iff.2 <|
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.find_min' hex ht) hD.le

/-- The generic point of a curve on a threefold of the tail has coheight two. -/
private theorem coheight_genericPoint_eq_two (T : StabilizedTail) {j : ℕ}
    (V : IrreducibleCloseds (T.X j)) (hV : topologicalKrullDim (V : Set (T.X j)) = 1) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  have : LocallyOfFiniteType (T.sX j) := (T.isKltPair j).1.isPair.1.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T.sX j)
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, T.dim_eq j] at h
  exact ENat.add_right_injective_of_ne_top ENat.one_ne_top
    (WithBot.coe_injective (by push_cast; rw [h]; rfl) : (1 : ℕ∞) + _ = 1 + 2)

/-- **Generic mlds at most one are attained on a stabilized tail.** Let `T` be a stabilized tail
and `V ⊆ X_j` an irreducible curve with `mld_{η_V}(X_j, B_j) ≤ 1`. Then some normalized
divisorial valuation `ξ` of `k(X_j)` with centre `V` has log discrepancy
`a(ξ; X_j, B_j) = mld_{η_V}(X_j, B_j)`; and every such `ξ` lies in `I(X_j, B_j)` and is the
transport to `k(X_j)` of an element of `I_∞ = I(X_0, B_0)`. -/
@[mmp "lem_mmp_indexc_curve_mld_attained"]
public theorem exists_isCentre_isLogDiscrepancyAt_eq_minimalLogDiscrepancy (T : StabilizedTail)
    {j : ℕ} (V : IrreducibleCloseds (T.X j))
    (hVdim : topologicalKrullDim (V : Set (T.X j)) = 1)
    (hmld : minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint ≤ 1) :
    (∃ ξ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ (T.sX j) ξ V ∧
        ∃ a : ℝ, T.IsLogDiscrepancyAt j ξ a ∧
          (a : EReal) = minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint) ∧
    ∀ (ξ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))) (a : ℝ),
      MMP.Intersection.IsCentre ℂ (T.sX j) ξ V → T.IsLogDiscrepancyAt j ξ a →
      (a : EReal) = minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint →
      ξ ∈ lowDiscrepancySet (T.sX j) (T.B j) ∧
        ∃ ν ∈ T.lowDiscrepancySetLimit, T.IsTransportedValuationFrom j ν ξ := by
  have hVx : closure {V.isIrreducible.genericPoint} = (V : Set (T.X j)) :=
    (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def
  refine ⟨?_, fun ξ a hξ ha haeq => ?_⟩
  · obtain ⟨q, r, -, hr1, -, hr, -⟩ := StabilizedTail.exists_smul_eq_and_inv_le_and_ncard_eq T
    have hrpos : (0 : ℝ) < (r : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hr1)
    obtain ⟨Dmax, -, F, -, hF⟩ :=
      StabilizedTail.exists_logDiscrepancy_denom_le_and_minimalLogDiscrepancy_mem T hrpos hr
    obtain ⟨D, hD1, -, hden, -⟩ := hF j V hVdim
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
    have hcent : ∀ (n : ℕ) (E : DivisorOver ℂ (T.sX j)) (a : ℝ),
        MMP.Intersection.IsLogDiscrepancy (T.sX j) n (QDivisor.toRDivisor (T.B j)) E a →
        (E.center : Set (T.X j)) = closure {V.isIrreducible.genericPoint} →
        MMP.Intersection.IsCentre ℂ (T.sX j) E.valuation V ∧
          T.IsLogDiscrepancyAt j E.valuation a := fun n E a ha hc =>
      ⟨⟨E, ha.2.1, rfl, IrreducibleCloseds.ext (hc.trans hVx).symm⟩, ⟨n, E, ha.2.1, rfl, ha⟩⟩
    obtain ⟨n, E, a, ha, hc, hta⟩ := sInf_mem_of_forall_eq_natCast_div hDpos
      (hmld.trans_lt (EReal.coe_lt_top 1)).ne (by
        rintro t ⟨n, E, a, ha, hc, rfl⟩
        obtain ⟨hcV, haV⟩ := hcent n E a ha hc
        obtain ⟨⟨k, rfl⟩, hδa⟩ := hden _ hcV a haV
        have hk : (0 : ℝ) ≤ k := (div_pos_iff_of_pos_right hDpos).1 (hrpos.trans_le hδa) |>.le
        refine ⟨k.toNat, ?_⟩
        congr 2
        exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast hk)).symm)
    obtain ⟨hcV, haV⟩ := hcent n E a ha hc
    exact ⟨E.valuation, hcV, a, haV, hta.symm⟩
  · have hmem : ξ ∈ lowDiscrepancySet (T.sX j) (T.B j) := by
      obtain ⟨D, hDp, rfl, hVD⟩ := hξ
      refine ⟨⟨D, hDp, rfl, ?_⟩, a, ha, ?_⟩
      · have hc := MMP.Flips.codimension_closureSingleton V.isIrreducible.genericPoint
        rw [← (IrreducibleCloseds.ext hVx.symm : V = .closureSingleton _),
          coheight_genericPoint_eq_two T V hVdim] at hc
        rw [← hVD, hc]
      · exact_mod_cast (haeq ▸ hmld : (a : EReal) ≤ 1)
    exact ⟨hmem, exists_mem_isTransportedValuationFrom T j hmem⟩

/-! ### Transports along the tail -/

section Tail

variable (T : StabilizedTail)

/-- A log discrepancy `a(ξ; X, B)` of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_unique {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : IsValuationLogDiscrepancy sX B ξ a) (h' : IsValuationLogDiscrepancy sX B ξ a') :
    a = a' := by
  obtain ⟨n, D, -, hD, ha⟩ := h
  obtain ⟨n', D', -, hD', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)

/-- The transport of a valuation across one step diagram is unique. -/
private theorem isTransportedValuation_unique {i : ℕ}
    {u : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (h : T.IsTransportedValuation i u w) (h' : T.IsTransportedValuation i u w') : w = w' := by
  have hst := T.isThreefoldStepDiagram i
  have : IsIntegral (T.Z i) := hst.isNormalVariety_target.1.toIsIntegral
  have := hst.isBirationalMorphism_minus.isDominant
  have := hst.isSmallMorphism_plus.isBirationalMorphism.isDominant
  unfold StabilizedTail.IsTransportedValuation at h h'
  exact comap_injective_of_surjective
    hst.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2 (h.trans h'.symm)

/-- The transport of a valuation of `k(X_0)` to `k(X_j)` is unique. -/
private theorem isTransportedValuationFrom_unique {ν} :
    ∀ (j : ℕ) {w w' : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom j ν w → T.IsTransportedValuationFrom j ν w' → w = w'
  | 0, w, w', h, h' => h.trans h'.symm
  | j + 1, w, w', h, h' => by
    obtain ⟨u, hu, ht⟩ := h
    obtain ⟨u', hu', ht'⟩ := h'
    obtain rfl := isTransportedValuationFrom_unique j hu hu'
    exact isTransportedValuation_unique T ht ht'

/-- Every element of `I_∞` is transported to an element of `I(X_j, B_j)`, for every `j`. -/
private theorem exists_isTransportedValuationFrom_mem {ν} (hν : ν ∈ T.lowDiscrepancySetLimit) :
    ∀ j : ℕ, ∃ w, T.IsTransportedValuationFrom j ν w ∧ w ∈ lowDiscrepancySet (T.sX j) (T.B j)
  | 0 => ⟨ν, rfl, hν⟩
  | j + 1 => by
    obtain ⟨w, hw, hwI⟩ := exists_isTransportedValuationFrom_mem hν j
    have : IsIntegral (T.Z j) :=
      (T.isThreefoldStepDiagram j).isNormalVariety_target.1.toIsIntegral
    have := (T.isThreefoldStepDiagram j).isBirationalMorphism_minus.isDominant
    have := (T.isThreefoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmem : w.comap (functionFieldMap (T.f j)) ∈
        valuationsOver (T.f j) (lowDiscrepancySet (T.sX j) (T.B j)) := ⟨w, hwI, rfl⟩
    rw [T.lowDiscrepancySet_eq j] at hmem
    obtain ⟨w', hw', hwe⟩ := hmem
    exact ⟨w', ⟨w, hw, hwe⟩, hw'⟩

/-- Unpacking a transport to `k(X_{j+1})` against a known transport to `k(X_j)`. -/
private theorem isTransportedValuation_of_succ {ν} {j : ℕ}
    {w : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    {w' : Valuation (T.X (j + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.IsTransportedValuationFrom j ν w) (hw' : T.IsTransportedValuationFrom (j + 1) ν w') :
    T.IsTransportedValuation j w w' := by
  obtain ⟨u, hu, ht⟩ := hw'
  obtain rfl := isTransportedValuationFrom_unique T j hu hw
  exact ht

/-- The log discrepancies `a_j(ν)` of the transports of `ν` do not decrease from `j` to `j + 1`;
and they increase strictly when the centre on `X_j` lies in `W_j⁻`, or the centre on `X_{j+1}`
lies in `W_j⁺`. -/
private theorem le_and_lt_of_isTransportedValuationFrom {ν} {j : ℕ}
    {w : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    {w' : Valuation (T.X (j + 1)).functionField (WithZero (Multiplicative ℤ))}
    (hw : T.IsTransportedValuationFrom j ν w) (hw' : T.IsTransportedValuationFrom (j + 1) ν w')
    {a a' : ℝ} (ha : T.IsLogDiscrepancyAt j w a) (ha' : T.IsLogDiscrepancyAt (j + 1) w' a') :
    a ≤ a' ∧
      (∀ C : IrreducibleCloseds (T.X j), MMP.Intersection.IsCentre ℂ (T.sX j) w C →
        (C : Set (T.X j)) ⊆ T.badLocusMinusAt j → a < a') ∧
      (∀ C : IrreducibleCloseds (T.X (j + 1)), MMP.Intersection.IsCentre ℂ (T.sX (j + 1)) w' C →
        (C : Set (T.X (j + 1))) ⊆ T.badLocusPlusAt j → a < a') := by
  have ht := isTransportedValuation_of_succ T hw hw'
  have h := T.isThreefoldStepDiagram j
  unfold StabilizedTail.IsTransportedValuation at ht
  have ha'' : IsValuationLogDiscrepancy (T.sX (j + 1)) (flipTransform (T.f j) (T.fp j) (T.B j))
      w' a' := T.B_eq j ▸ ha'
  obtain ⟨n', Dm, hDm, hDmv, ham⟩ := id ha
  obtain ⟨n, Dp, hDp, hDpv, hap⟩ := id ha''
  have hCm : MMP.Intersection.IsCentre ℂ (T.sX j) w Dm.center := ⟨Dm, hDm, hDmv.symm, rfl⟩
  have hCp : MMP.Intersection.IsCentre ℂ (T.sX (j + 1)) w' Dp.center := ⟨Dp, hDp, hDpv.symm, rfl⟩
  refine ⟨le_of_isLogDiscrepancy h (T.isKltPair j).1 Dp Dm hDm
    (by rw [hDpv, hDmv]; exact ht) hap ham, fun C hC hCW => ?_, fun C hC hCW => ?_⟩
  · exact ((h.tfae_lt_and_centre_subset_badLocus ht ha ha'' hC hCp).out 2 1).mp hCW
  · exact ((h.tfae_lt_and_centre_subset_badLocus ht ha ha'' hCm hC).out 3 1).mp hCW

/-- The log discrepancies `a_j(ν)` of the transports of `ν ∈ I_∞` form a nondecreasing
sequence. -/
private theorem exists_monotone {ν} (hν : ν ∈ T.lowDiscrepancySetLimit) :
    ∃ (w : ∀ j, Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))) (A : ℕ → ℝ),
      (∀ j, T.IsTransportedValuationFrom j ν (w j)) ∧ (∀ j, T.IsLogDiscrepancyAt j (w j) (A j)) ∧
        Monotone A := by
  choose w hw hwI using exists_isTransportedValuationFrom_mem T hν
  choose A hA using fun j => (hwI j).2
  exact ⟨w, A, hw, fun j => (hA j).1, monotone_nat_of_le_succ fun j =>
    (le_and_lt_of_isTransportedValuationFrom T (hw j) (hw (j + 1)) (hA j).1 (hA (j + 1)).1).1⟩

/-- On the negative side, the log discrepancies of the transports of `ν` at two indices `i < i'`,
the first centred inside `W_i⁻`, increase strictly. -/
private theorem lt_of_lt_of_subset_badLocusMinus {ν} (hν : ν ∈ T.lowDiscrepancySetLimit)
    {i i' : ℕ} (hii : i < i') {ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {ξ' : Valuation (T.X i').functionField (WithZero (Multiplicative ℤ))}
    {V : IrreducibleCloseds (T.X i)} {a a' : ℝ} (hc : MMP.Intersection.IsCentre ℂ (T.sX i) ξ V)
    (hV : (V : Set (T.X i)) ⊆ T.badLocusMinusAt i) (htr : T.IsTransportedValuationFrom i ν ξ)
    (ha : T.IsLogDiscrepancyAt i ξ a) (htr' : T.IsTransportedValuationFrom i' ν ξ')
    (ha' : T.IsLogDiscrepancyAt i' ξ' a') : a < a' := by
  obtain ⟨w, A, hw, hA, hmono⟩ := exists_monotone T hν
  obtain rfl := isTransportedValuationFrom_unique T i htr (hw i)
  obtain rfl := isTransportedValuationFrom_unique T i' htr' (hw i')
  rw [isValuationLogDiscrepancy_unique ha (hA i), isValuationLogDiscrepancy_unique ha' (hA i')]
  exact ((le_and_lt_of_isTransportedValuationFrom T (hw i) (hw (i + 1)) (hA i)
    (hA (i + 1))).2.1 V hc hV).trans_le (hmono hii)

/-- On the positive side, the log discrepancies of the transports of `ν` to `X_{i+1}` and
`X_{i'+1}`, for `i < i'`, the second centred inside `W_{i'}⁺`, increase strictly. -/
private theorem lt_of_lt_of_subset_badLocusPlus {ν} (hν : ν ∈ T.lowDiscrepancySetLimit)
    {i i' : ℕ} (hii : i < i')
    {ξ : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    {ξ' : Valuation (T.X (i' + 1)).functionField (WithZero (Multiplicative ℤ))}
    {V' : IrreducibleCloseds (T.X (i' + 1))} {a a' : ℝ}
    (htr : T.IsTransportedValuationFrom (i + 1) ν ξ) (ha : T.IsLogDiscrepancyAt (i + 1) ξ a)
    (hc' : MMP.Intersection.IsCentre ℂ (T.sX (i' + 1)) ξ' V')
    (hV' : (V' : Set (T.X (i' + 1))) ⊆ T.badLocusPlusAt i')
    (htr' : T.IsTransportedValuationFrom (i' + 1) ν ξ')
    (ha' : T.IsLogDiscrepancyAt (i' + 1) ξ' a') : a < a' := by
  obtain ⟨w, A, hw, hA, hmono⟩ := exists_monotone T hν
  obtain rfl := isTransportedValuationFrom_unique T (i + 1) htr (hw (i + 1))
  obtain rfl := isTransportedValuationFrom_unique T (i' + 1) htr' (hw (i' + 1))
  rw [isValuationLogDiscrepancy_unique ha (hA (i + 1)),
    isValuationLogDiscrepancy_unique ha' (hA (i' + 1))]
  exact (hmono hii).trans_lt ((le_and_lt_of_isTransportedValuationFrom T (hw i') (hw (i' + 1))
    (hA i') (hA (i' + 1))).2.2 V' hc' hV')

/-- **The finitely many labels of bad curves.** There is a finite `F ⊆ ℚ` such that the mld at
the generic point of every curve `V ⊆ X_j` with `mld_{η_V}(X_j, B_j) ≤ 1` is a value `x ∈ F`,
attained by a valuation with centre `V` which is the transport of some `ν ∈ I_∞`. -/
private theorem exists_finset_forall_exists_isTransportedValuationFrom :
    ∃ F : Finset ℚ, ∀ j (V : IrreducibleCloseds (T.X j)),
      topologicalKrullDim (V : Set (T.X j)) = 1 →
      minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint ≤ 1 →
      ∃ ν ∈ T.lowDiscrepancySetLimit, ∃ x ∈ F,
        ∃ ξ : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ)),
          MMP.Intersection.IsCentre ℂ (T.sX j) ξ V ∧ T.IsTransportedValuationFrom j ν ξ ∧
            T.IsLogDiscrepancyAt j ξ (x : ℝ) := by
  obtain ⟨q, r, -, hr1, -, hr, -⟩ := T.exists_smul_eq_and_inv_le_and_ncard_eq
  obtain ⟨Dmax, -, F, -, hF⟩ := T.exists_logDiscrepancy_denom_le_and_minimalLogDiscrepancy_mem
    (inv_pos.2 (by exact_mod_cast hr1)) hr
  refine ⟨F, fun j V hdim hmld => ?_⟩
  obtain ⟨⟨ξ, hc, a, ha, hae⟩, hall⟩ :=
    T.exists_isCentre_isLogDiscrepancyAt_eq_minimalLogDiscrepancy V hdim hmld
  obtain ⟨-, ν, hν, htr⟩ := hall ξ a hc ha hae
  obtain ⟨-, -, -, -, hFm⟩ := hF j V hdim
  obtain ⟨x, hx, hxe⟩ := hFm hmld
  obtain rfl : a = x := EReal.coe_injective (hae.trans hxe)
  exact ⟨ν, hν, x, hx, ξ, hc, htr, ha⟩

end Tail

/-- A set of indices is finite if each of its elements carries a label `(ν, x)` from a finite
set, and no label is carried by two indices `i < i'`. -/
private theorem finite_of_forall_exists_label {α β : Type*} {S : Set ℕ} {I : Set α} {F : Set β}
    (hI : I.Finite) (hF : F.Finite) (R : α → β → ℕ → Prop)
    (hR : ∀ ν ∈ I, ∀ x i i', R ν x i → R ν x i' → ¬ i < i')
    (hS : ∀ i ∈ S, ∃ ν ∈ I, ∃ x ∈ F, R ν x i) : S.Finite := by
  refine (hI.biUnion fun ν hν => hF.biUnion fun x _ => Set.Subsingleton.finite
    (s := {i | R ν x i}) fun i hi i' hi' => ?_).subset fun i hi => ?_
  · exact le_antisymm (not_lt.1 (hR ν hν x i' i hi' hi)) (not_lt.1 (hR ν hν x i i' hi hi'))
  · obtain ⟨ν, hν, x, hx, h⟩ := hS i hi
    simp only [Set.mem_iUnion]
    exact ⟨ν, hν, x, hx, h⟩

/-- **Bad curves of small mld occur finitely often on each side.** For a stabilized tail `T`,
the set of indices `i` for which some irreducible curve `V ⊆ W_i⁻ ⊆ X_i` has
`mld_{η_V}(X_i, B_i) ≤ 1` is finite, and so is the set of indices `i` for which some irreducible
curve `V ⊆ W_i⁺ ⊆ X_{i+1}` has `mld_{η_V}(X_{i+1}, B_{i+1}) ≤ 1`. -/
@[mmp "lem_mmp_indexc_bad_curves_mld_one_side"]
public theorem finite_setOf_exists_minimalLogDiscrepancy_le_one (T : StabilizedTail) :
    {i : ℕ | ∃ V : IrreducibleCloseds (T.X i),
        topologicalKrullDim (V : Set (T.X i)) = 1 ∧
        (V : Set (T.X i)) ⊆ (T.badLocusMinusAt i : Set (T.X i)) ∧
        minimalLogDiscrepancy (T.sX i) (T.B i) V.isIrreducible.genericPoint ≤ 1}.Finite ∧
      {i : ℕ | ∃ V : IrreducibleCloseds (T.X (i + 1)),
        topologicalKrullDim (V : Set (T.X (i + 1))) = 1 ∧
        (V : Set (T.X (i + 1))) ⊆ (T.badLocusPlusAt i : Set (T.X (i + 1))) ∧
        minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1))
          V.isIrreducible.genericPoint ≤ 1}.Finite := by
  obtain ⟨-, -, -, -, -, -, hfin⟩ := T.exists_smul_eq_and_inv_le_and_ncard_eq
  have hI : T.lowDiscrepancySetLimit.Finite := (hfin 0).1
  obtain ⟨F, hF⟩ := exists_finset_forall_exists_isTransportedValuationFrom T
  constructor
  · refine finite_of_forall_exists_label hI F.finite_toSet (fun ν (x : ℚ) i =>
      ∃ (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
        (V : IrreducibleCloseds (T.X i)),
        MMP.Intersection.IsCentre ℂ (T.sX i) ξ V ∧ (V : Set (T.X i)) ⊆ T.badLocusMinusAt i ∧
          T.IsTransportedValuationFrom i ν ξ ∧ T.IsLogDiscrepancyAt i ξ (x : ℝ))
      (fun ν hν x i i' ⟨ξ, V, hc, hV, htr, ha⟩ ⟨ξ', _, _, _, htr', ha'⟩ h =>
        lt_irrefl _ (lt_of_lt_of_subset_badLocusMinus T hν h hc hV htr ha htr' ha'))
      fun i ⟨V, hdim, hsub, hmld⟩ => ?_
    obtain ⟨ν, hν, x, hx, ξ, hc, htr, ha⟩ := hF i V hdim hmld
    exact ⟨ν, hν, x, hx, ξ, V, hc, hsub, htr, ha⟩
  · refine finite_of_forall_exists_label hI F.finite_toSet (fun ν (x : ℚ) i =>
      ∃ (ξ : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))
        (V : IrreducibleCloseds (T.X (i + 1))),
        MMP.Intersection.IsCentre ℂ (T.sX (i + 1)) ξ V ∧
          (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i ∧
          T.IsTransportedValuationFrom (i + 1) ν ξ ∧ T.IsLogDiscrepancyAt (i + 1) ξ (x : ℝ))
      (fun ν hν x i i' ⟨ξ, _, _, _, htr, ha⟩ ⟨ξ', V', hc', hV', htr', ha'⟩ h =>
        lt_irrefl _ (lt_of_lt_of_subset_badLocusPlus T hν h htr ha hc' hV' htr' ha'))
      fun i ⟨V, hdim, hsub, hmld⟩ => ?_
    obtain ⟨ν, hν, x, hx, ξ, hc, htr, ha⟩ := hF (i + 1) V hdim hmld
    exact ⟨ν, hν, x, hx, ξ, V, hc, hsub, htr, ha⟩

end StabilizedTail

end MMP.Fourfold
