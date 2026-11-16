module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.ConeTheorem.NefAdjointRadialRay
import MMP.AlgebraicGeometry.MMP.BasepointFree.BigAdjointSemiample
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.Positivity.BigBirationalTransform
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.ConeTheorem.CommonRayCurveBound
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
import MMP.AlgebraicGeometry.Divisor.PullbackExistence
import MMP.AlgebraicGeometry.MMP.Threefold.MinimalModel.RealKltLogTerminalModel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Resolution.SncComplementResolution
import MMP.AlgebraicGeometry.Intersection.RelativePicardNumberFinite
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefModelEquivalence
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Finite geography of real klt threefold models with a big boundary core

Let `π : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold and `K_X` a canonical divisor of `X`. Let `P` be a rational polytope of boundaries:
the real convex hull of finitely many effective `ℚ`-divisors `V` on `X`, each making `(X, V)`
klt and each containing a fixed effective `ℚ`-divisor `G` which is big over `Z`. Then there are
finitely many birational contractions `φ_j : X ⤏ Y_j` over `Z` (birational maps over `Z`
extracting no prime divisor), with every `Y_j` normal, projective and `ℚ`-factorial, such that
every `B ∈ P` with `K_X + B` pseudo-effective over `Z` has one of them as a log minimal model:
the transformed pair `(Y_j, φ_j_* B)` is klt and `(Y_j/Z, φ_j_* B)` is a log minimal model of
`(X/Z, B)`.

## Main results

* `MMP.Fourfold.exists_finite_isRealLogMinimalModel_of_mem_convexHull_of_isRelativelyBig`: the
  finite geography.

## Implementation notes

* The polytope is `convexHull ℝ (QDivisor.toRDivisor '' V)` for a finite set `V` of rational
  vertices. Effectivity of its members, and the inequality `G ≤ B`, follow from those of the
  vertices by convexity, so both are imposed on the vertices only.
* Pseudo-effectivity over `Z` of the real Weil divisor `K_X + B` is that of an `ℝ`-Cartier
  divisor `D = ∑ cᵢ Dᵢ` (`MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective`) whose Weil
  divisor is `K_X + B`: `coeff_P (K_X + B) = ∑ cᵢ ord_P Dᵢ` for every prime divisor `P`. On the
  normal variety `X` the numerical class of `D` only depends on this Weil divisor.
* The log minimal model is `MMP.Fourfold.IsRealLogMinimalModel`: nef adjoint over `Z`, effective
  `q`-exceptional comparison on a common resolution, strictly positive comparison at every prime
  of `X` contracted on the model, and projectivity and `ℚ`-factoriality of the model. Since `φ_j`
  extracts no prime divisor, the model boundary is the strict transform
  `MMP.Mori.RationalMap.transformDivisor (φ j) B`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Fourfold MMP.Mori MMP.Flips

namespace Proof_thm_fourfold_threefold_big_boundary_geography

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The finite-model property of a set of boundaries -/

section Defs

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- `K_X + B` is pseudo-effective over `Z`: some `ℝ`-Cartier divisor with Weil divisor `K_X + B`
is pseudo-effective over `Z`. -/
private def IsPsef (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (π : X ⟶ Z) (KX : Divisor X)
    (B : RDivisor X) : Prop :=
  ∃ D : KCartierDivisor ℝ X,
    (∀ P : MMP.Mori.PrimeDivisor X, (logCanonicalDivisor KX B).coeff P =
      D.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ)) ∧
    KCartierDivisor.IsRelativelyPseudoEffective sX π D

/-- Finitely many birational contractions `X ⤏ Y_j` over `Z` supply a klt log minimal model of
`(X/Z, B)` for every `B ∈ S` with `K_X + B` pseudo-effective over `Z`. -/
private def HasFiniteModels (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (sZ : Z ⟶ Spec (.of ℂ)) (π : X ⟶ Z) (KX : Divisor X) (S : Set (RDivisor X)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Y : ι → Scheme.{0}) (_ : ∀ j, IsIntegral (Y j))
      (_ : ∀ j, CompactSpace (Y j))
      (_ : ∀ j, IsLocallyNoetherian (Y j)) (_ : ∀ j, IsNormal (Y j))
      (sY : ∀ j, Y j ⟶ Spec (.of ℂ)) (πY : ∀ j, Y j ⟶ Z) (KY : ∀ j, Divisor (Y j))
      (φ : ∀ j, X.RationalMap (Y j)),
      (∀ j, MMP.Mori.IsProjectiveVariety ℂ (sY j) ∧ IsNormalVariety ℂ (sY j) ∧
        IsQFactorial (sY j) ∧ πY j ≫ sZ = sY j ∧ MMP.Mori.RationalMap.IsBirational (φ j) ∧
        MMP.Flips.RationalMap.IsOver π (πY j) (φ j) ∧
        ∀ F : MMP.Mori.PrimeDivisor (Y j), ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ j) F) ∧
      ∀ B ∈ S, IsPsef sX π KX B →
        ∃ j, IsRealLogMinimalModel sX (sY j) sZ π (πY j) KX B (KY j)
            (MMP.Mori.RationalMap.transformDivisor (φ j) B) (φ j) ∧
          IsRealKltPair (sY j) (MMP.Mori.RationalMap.transformDivisor (φ j) B)

variable {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
  {KX : Divisor X}

private theorem HasFiniteModels.mono {S T : Set (RDivisor X)} (h : HasFiniteModels sX sZ π KX T)
    (hST : S ⊆ T) : HasFiniteModels sX sZ π KX S := by
  obtain ⟨ι, hι, Y, i1, i2, i3, i4, sY, πY, KY, φ, hY, hB⟩ := h
  exact ⟨ι, hι, Y, i1, i2, i3, i4, sY, πY, KY, φ, hY, fun B hB' hps => hB B (hST hB') hps⟩

private theorem hasFiniteModels_of_forall_not_isPsef {S : Set (RDivisor X)}
    (h : ∀ B ∈ S, ¬ IsPsef sX π KX B) : HasFiniteModels sX sZ π KX S :=
  ⟨Empty, inferInstance, Empty.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim,
    fun j => j.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim, fun j => j.elim,
    fun j => j.elim, fun B hB hps => (h B hB hps).elim⟩

/-- The finite-model property is preserved by finite unions. -/
private theorem HasFiniteModels.union {S T : Set (RDivisor X)} (hS : HasFiniteModels sX sZ π KX S)
    (hT : HasFiniteModels sX sZ π KX T) : HasFiniteModels sX sZ π KX (S ∪ T) := by
  obtain ⟨ι, hι, Y, i1, i2, i3, i4, sY, πY, KY, φ, hY, hB⟩ := hS
  obtain ⟨ι', hι', Y', i1', i2', i3', i4', sY', πY', KY', φ', hY', hB'⟩ := hT
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim Y Y', Sum.rec i1 i1', Sum.rec i2 i2', Sum.rec i3 i3',
    Sum.rec i4 i4', Sum.rec sY sY', Sum.rec πY πY', Sum.rec KY KY', Sum.rec φ φ',
    Sum.rec hY hY', ?_⟩
  rintro B (hBS | hBT) hps
  · obtain ⟨j, hj⟩ := hB B hBS hps
    exact ⟨Sum.inl j, hj⟩
  · obtain ⟨j, hj⟩ := hB' B hBT hps
    exact ⟨Sum.inr j, hj⟩

private theorem hasFiniteModels_biUnion {ι : Type*} (t : Finset ι) (S : ι → Set (RDivisor X))
    (h : ∀ i ∈ t, HasFiniteModels sX sZ π KX (S i)) :
    HasFiniteModels sX sZ π KX (⋃ i ∈ t, S i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact hasFiniteModels_of_forall_not_isPsef (by simp)
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a t)).union
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Defs

/-! ### Boundaries parametrised by a simplex -/

section Simplex

variable {X : Scheme.{0}}

/-- The boundary `∑ μᵢ vᵢ` of barycentric coordinates `μ` with respect to vertices `v`. -/
private noncomputable def bary {N : ℕ} (v : Fin N → QDivisor X) :
    (Fin N → ℝ) →ₗ[ℝ] RDivisor X :=
  ∑ i, (LinearMap.proj i).smulRight (QDivisor.toRDivisor (v i))

private theorem bary_apply {N : ℕ} (v : Fin N → QDivisor X) (μ : Fin N → ℝ) :
    bary v μ = ∑ i, μ i • QDivisor.toRDivisor (v i) := by
  simp [bary]

private theorem image_bary_stdSimplex {N : ℕ} (v : Fin N → QDivisor X) :
    bary v '' stdSimplex ℝ (Fin N) =
      convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (v i)) := by
  classical
  rw [← convexHull_rangle_single_eq_stdSimplex, LinearMap.image_convexHull, ← Set.range_comp]
  congr 2
  funext i
  simp [bary_apply, Pi.single_apply]

private theorem coeff_bary {N : ℕ} (v : Fin N → QDivisor X) (μ : Fin N → ℝ)
    (P : MMP.Mori.PrimeDivisor X) :
    (bary v μ).coeff P = ∑ i, μ i * ((v i).coeff P : ℝ) := by
  rw [bary_apply, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  rfl

private theorem bary_nonneg {N : ℕ} (v : Fin N → QDivisor X) (hv : ∀ i P, 0 ≤ (v i).coeff P)
    {μ : Fin N → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin N)) (P : MMP.Mori.PrimeDivisor X) :
    0 ≤ (bary v μ).coeff P := by
  rw [coeff_bary]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ.1 i) (by exact_mod_cast hv i P)

end Simplex

/-! ### Strict transforms -/

section Transform

variable {X Y : Scheme.{0}}

open Classical in
/-- The coefficients of a strict transform: the coefficient at `E` collects the coefficients of
the prime divisors whose transform is `E`. -/
private theorem transformDivisor_apply {R : Type*} [AddCommMonoid R] (φ : X.RationalMap Y)
    (D : DivisorWithCoeffs R X) (E : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.RationalMap.transformDivisor φ D E =
      D.sum fun P r => if MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E then r
        else 0 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' =>
    rw [map_add, Finsupp.add_apply, h, h', Finsupp.sum_add_index'] <;> intros <;> split_ifs <;>
      simp
  | single P r =>
    rw [Finsupp.sum_single_index (by split_ifs <;> rfl),
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases hP : MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | E'
    · simp
    · by_cases hE : E' = E
      · subst hE; simp
      · simp [Finsupp.single_apply, hE]

private theorem transformDivisor_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R]
    (φ : X.RationalMap Y) {D : DivisorWithCoeffs R X} (hD : ∀ P, 0 ≤ D.coeff P)
    (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ (MMP.Mori.RationalMap.transformDivisor φ D).coeff P := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, transformDivisor_apply]
  exact Finset.sum_nonneg fun Q _ => by dsimp only; split_ifs; exacts [hD Q, le_rfl]

private theorem transformDivisor_mono {D E : QDivisor X} (φ : X.RationalMap Y)
    (h : ∀ P, D.coeff P ≤ E.coeff P) (P : MMP.Mori.PrimeDivisor Y) :
    (MMP.Mori.RationalMap.transformDivisor φ D).coeff P ≤
      (MMP.Mori.RationalMap.transformDivisor φ E).coeff P := by
  have h0 := transformDivisor_nonneg (R := ℚ) φ (D := E - D)
    (fun Q => by simpa [DivisorWithCoeffs.coeff_apply] using h Q) P
  have : E = D + (E - D) := by abel
  rw [this, map_add]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply] at h0 ⊢
  linarith

/-- The strict transform commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor (φ : X.RationalMap Y)
    (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  ext E
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    show QDivisor.toRDivisor D = Finsupp.mapRange (fun q : ℚ => (q : ℝ)) Rat.cast_zero D
      from rfl, transformDivisor_apply, transformDivisor_apply,
    Finsupp.sum_mapRange_index (by intros; split_ifs <;> rfl), Finsupp.sum, Finsupp.sum,
    Rat.cast_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  split_ifs <;> simp

end Transform

/-! ### Convex combinations of klt boundaries -/

section Algebra

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The boundary `∑ wᵢ Vᵢ` of a weight vector `w`. -/
private noncomputable def wsum {n : ℕ} (V : Fin n → RDivisor X) (w : Fin n → ℝ) : RDivisor X :=
  ∑ i, w i • V i

private theorem coeff_wsum {n : ℕ} (V : Fin n → RDivisor X) (w : Fin n → ℝ)
    (P : MMP.Mori.PrimeDivisor X) : (wsum V w).coeff P = ∑ i, w i * (V i).coeff P := by
  simp [wsum, DivisorWithCoeffs.coeff, Finsupp.finsetSum_apply]

/-- **Adding Cartier divisors to the boundary.** For Cartier divisors `Cᵢ` and a divisor `D` over
`X` there are numbers `μᵢ` (the coefficients along `D` of the pull-backs of the `Cᵢ`) such that a
log discrepancy `a` of `D` for `(X, B)` gives the log discrepancy `a - ∑ sᵢ μᵢ` for
`(X, B + ∑ sᵢ Cᵢ)`. -/
private theorem exists_isLogDiscrepancy_add {ι : Type*} [Fintype ι] (C : ι → Divisor X)
    (hC : ∀ i, (C i).IsCartier) (D : DivisorOver ℂ sX) :
    ∃ μ : ι → ℝ, ∀ (n : ℕ) (B B' : RDivisor X) (s : ι → ℝ) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B D a →
      (∀ Γ, B'.coeff Γ = B.coeff Γ + ∑ i, s i * ((C i).coeff Γ : ℝ)) →
      MMP.Intersection.IsLogDiscrepancy sX n B' D (a - ∑ i, s i * μ i) := by
  classical
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isIntegral
  have := D.isBirationalMorphism.isDominant
  have : CompactSpace D.Y := (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hB := fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f (C i)
  choose C' hC' using fun i => (hC i).exists_isPullback (hB i)
  refine ⟨fun i => ((C' i).coeff D.E : ℝ), fun n B B' s a h hB' => ?_⟩
  obtain ⟨hnv, hprop, ω, hω0, hK, m, r, C₀, C₀', hC₀, hrel, hpb, ha⟩ := h
  let e := Fintype.equivFin ι
  refine ⟨hnv, hprop, ω, hω0, hK, m + Fintype.card ι, Fin.append r (s ∘ e.symm),
    Fin.append C₀ (C ∘ e.symm), Fin.append C₀' (C' ∘ e.symm), ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hC₀ j
    · simpa using hC (e.symm j)
  · intro Γ
    rw [Fin.sum_univ_add, hB', ← add_assoc, hrel Γ]
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]
    congr 1
    exact (e.symm.sum_comp (fun i => s i * ((C i).coeff Γ : ℝ))).symm
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hpb j
    · rw [Fin.append_right, Fin.append_right]
      exact ⟨hB _, hC' _⟩
  · rw [ha, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Function.comp_apply]
    rw [e.symm.sum_comp (fun i => s i * ((C' i).coeff D.E : ℝ))]
    ring

/-- A weight in the standard simplex has a positive entry. -/
private theorem exists_pos_of_mem_stdSimplex {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ stdSimplex ℝ (Fin n)) : ∃ i, 0 < w i := by
  by_contra h
  push Not at h
  have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
  linarith [hw.2]

/-- **Convex combinations of klt boundaries are klt** on a `ℚ`-factorial variety. -/
private theorem isRealKltPair_wsum (hXq : IsQFactorial sX) {n : ℕ} {V : Fin n → RDivisor X}
    (hV : ∀ i, IsRealKltPair sX (V i)) {w : Fin n → ℝ} (hw : w ∈ stdSimplex ℝ (Fin n)) :
    IsRealKltPair sX (wsum V w) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_mem_stdSimplex hw
  obtain ⟨hXn, -, ⟨n₀, K, hK, -⟩, -⟩ := hV i₀
  refine ⟨hXn, fun P => ?_, ⟨n₀, K, hK, hXq.isRCartier _⟩, fun d D a ha => ?_⟩
  · rw [coeff_wsum]
    have : ∑ i, w i * (V i).coeff P < ∑ i, w i * 1 :=
      Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left ((hV i).2.1 P).le (hw.1 i))
        ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left ((hV i₀).2.1 P) hi₀⟩
    simpa [hw.2] using this
  set S : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.biUnion fun i => (V i).support
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hXq.2 (Finsupp.single P 1)
  let C : S → Divisor X := fun P =>
    ((m P : ℕ) : ℤ) • Finsupp.single (P : MMP.Mori.PrimeDivisor X) (1 : ℤ)
  obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_add C (fun P => hmC P) D
  let s : Fin n → S → ℝ := fun i P => ((V i).coeff P - (wsum V w).coeff P) / m P
  have hCΓ : ∀ (P : S) (Γ : MMP.Mori.PrimeDivisor X),
      ((C P).coeff Γ : ℝ) = if (P : MMP.Mori.PrimeDivisor X) = Γ then (m P : ℝ) else 0 := by
    intro P Γ
    simp only [C, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp
  have hnotS : ∀ Γ, Γ ∉ S → ∀ i, (V i).coeff Γ = 0 := fun Γ hΓ i => by
    by_contra h
    exact hΓ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  have hai : ∀ i, 0 < a - ∑ P, s i P * μ P := fun i =>
    (hV i).2.2.2 d D _ (hμ d _ _ (s i) a ha fun Γ => by
      simp_rw [hCΓ, mul_ite, mul_zero]
      by_cases hΓ : Γ ∈ S
      · rw [Finset.sum_eq_single ⟨Γ, hΓ⟩ (fun P _ hP => if_neg fun h => hP (Subtype.ext h))
          (fun h => (h (Finset.mem_univ _)).elim), if_pos rfl]
        have : (m Γ : ℝ) ≠ 0 := by exact_mod_cast (hm Γ).ne'
        simp only [s]
        field_simp
        ring
      · have h0 : ∑ P : S, (if (P : MMP.Mori.PrimeDivisor X) = Γ then s i P * (m P : ℝ) else 0)
            = 0 := Finset.sum_eq_zero fun P _ =>
              if_neg fun (h : (P : MMP.Mori.PrimeDivisor X) = Γ) => hΓ (h ▸ P.2)
        rw [h0, add_zero, hnotS Γ hΓ i, coeff_wsum,
          Finset.sum_eq_zero fun j _ => by rw [hnotS Γ hΓ j, mul_zero]])
  have hsum : ∑ i, w i * (a - ∑ P, s i P * μ P) = a := by
    have h0 : ∀ P : S, ∑ i, w i * s i P = 0 := fun P => by
      simp only [s, mul_div_assoc', ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hw.2, one_mul, ← coeff_wsum, sub_self, zero_div]
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hw.2, one_mul]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul, h0, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [← hsum]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw.1 i) (hai i).le)
    ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (hai i₀)⟩

/-- **Convex combinations of klt boundaries are klt** on a `ℚ`-factorial variety. -/
private theorem isRealKltPair_bary (hXq : IsQFactorial sX) {N : ℕ}
    {v : Fin N → QDivisor X} (hv : ∀ i, IsRealKltPair sX (QDivisor.toRDivisor (v i)))
    {μ : Fin N → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin N)) : IsRealKltPair sX (bary v μ) := by
  rw [bary_apply]
  exact isRealKltPair_wsum hXq hv hμ

end Algebra

/-! ### Strict transforms under resolutions -/

/-- If a representative `g'` of `φ` sends the generic point of `P` to that of `E`, the strict
transform of `P` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq' {X Y : Scheme.{0}}
    [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain)
    (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

section StrictTransforms

open MMP.Mori

variable {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]

/-- A dominant morphism inducing an isomorphism of function fields induces an isomorphism of
local rings at every point lying over the generic point of a prime divisor. -/
private theorem isIso_stalkMap_of_map_eq_genericPoint (p : W ⟶ X) [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) {w : W} {P : MMP.Mori.PrimeDivisor X}
    (hw : p w = P.genericPoint) : IsIso (p.stalkMap w) := by
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p w)) := by rw [hw]; infer_instance
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing p hp w

/-- For a separated dominant morphism inducing an isomorphism of function fields, at most one
point lies over the generic point of a prime divisor. -/
private theorem eq_of_map_eq_genericPoint (p : W ⟶ X) [IsSeparated p] [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) {w w' : W} {P : MMP.Mori.PrimeDivisor X}
    (hw : p w = P.genericPoint) (hw' : p w' = P.genericPoint) : w = w' := by
  haveI := isIso_stalkMap_of_map_eq_genericPoint p hp hw
  haveI := isIso_stalkMap_of_map_eq_genericPoint p hp hw'
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p w)) := by rw [hw]; infer_instance
  exact MMP.Positivity.eq_of_isIso_stalkMap p hp (hw'.trans hw.symm)

variable [IsSeparated (X ↘ ⊤_ Scheme)]

/-- Every representative `g` of an inverse of a birational morphism `p` satisfies
`g ≫ p = ι`. -/
private theorem hom_comp_eq_of_isInverse [IsReduced W] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (g : X.PartialMap W)
    (hg : g.toRationalMap = h) : g.hom ≫ p = g.domain.ι := by
  have h1 : (g.compHom p).toRationalMap = (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg]
    exact hinv.compHom_eq_id
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)
  exact h2.trans (Category.comp_id _)

/-- **The strict transform under the inverse of a resolution.** If `p : W ⟶ X` is a proper
birational morphism with inverse `h`, and the prime divisor `P_W` of `W` lies over the prime
divisor `P` of `X`, then `h` sends `P` to `P_W`. -/
private theorem transformPrimeDivisor_eq_some_of_isInverse [IsNormal W] [IsLocallyNoetherian W]
    [IsSeparated (W ↘ ⊤_ Scheme)]
    {p : W ⟶ X} [IsProper p] [IsDominant p] (hp : Function.Bijective (functionFieldMap p))
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    {P : MMP.Mori.PrimeDivisor X} {PW : MMP.Mori.PrimeDivisor W}
    (hPW : p PW.genericPoint = P.genericPoint) :
    RationalMap.transformPrimeDivisor h P = some PW := by
  have := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  have hdom : P.genericPoint ∈ h.domain :=
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h
      hinv.compHom_eq_id P.coheight_genericPoint.le
  obtain ⟨g, hgP, hg⟩ := RationalMap.definedAt_iff.mp hdom
  have hgp := hom_comp_eq_of_isInverse hinv g hg
  have hw : p (g.hom ⟨P.genericPoint, hgP⟩) = P.genericPoint := by
    change (g.hom ≫ p) ⟨P.genericPoint, hgP⟩ = _
    rw [hgp]; rfl
  exact transformPrimeDivisor_eq_some_of_genericPoint_eq' g hg hgP
    (eq_of_map_eq_genericPoint p hp hPW hw)

/-- If the inverse `h` of a birational morphism `p` sends `P` to `P'`, then `p` sends the
generic point of `P'` to that of `P`. -/
private theorem map_genericPoint_of_transformPrimeDivisor_eq_some [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : RationalMap.IsInverse p.toRationalMap h) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor W} (hP : RationalMap.transformPrimeDivisor h P = some P') :
    p P'.genericPoint = P.genericPoint := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g, hgP, hg⟩ := RationalMap.definedAt_iff.mp hdef
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hgP]
  change (g.hom ≫ p) ⟨P.genericPoint, hgP⟩ = _
  rw [hom_comp_eq_of_isInverse hinv g hg]; rfl

/-- If `h : X ⤏ W` sends the prime divisor `P` to `P'`, then `q ∘ h` sends `P` where the
morphism `q` sends `P'`. -/
private theorem transformPrimeDivisor_compHom {Y : Scheme.{0}} [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {h : X.RationalMap W}
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.transformPrimeDivisor h P = some P') (q : W ⟶ Y) :
    RationalMap.transformPrimeDivisor (h.compHom q) P =
      RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P' := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g', hg'P, hg'⟩ := RationalMap.definedAt_iff.mp hdef
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hg'P
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  refine Option.ext fun F => ?_
  rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff]
  constructor
  · intro h1
    have h2 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h1 (g'.compHom q) hrep
      hg'P
    rw [h2, hη]
    rfl
  · intro h1
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq' (g'.compHom q) hrep hg'P ?_
    rw [← h1, hη]
    rfl

/-- If `h : X ⤏ W` sends the prime divisor `P` to `P'`, then `P` is exceptional for `q ∘ h`
exactly when `P'` is exceptional for the morphism `q`. -/
private theorem isExceptional_compHom_iff {Y : Scheme.{0}} [IsReduced W]
    [IsSeparated (W ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {h : X.RationalMap W}
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.transformPrimeDivisor h P = some P') (q : W ⟶ Y) :
    RationalMap.IsExceptional (h.compHom q) P ↔
      RationalMap.IsExceptional (X := W) q.toRationalMap P' := by
  obtain ⟨hdef, -⟩ := RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g', hg'P, hg'⟩ := RationalMap.definedAt_iff.mp hdef
  have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hg'P
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg']
  have hdef1 : RationalMap.DefinedAt (h.compHom q) P.genericPoint :=
    RationalMap.definedAt_iff.mpr ⟨g'.compHom q, hg'P, hrep⟩
  have hdef2 : RationalMap.DefinedAt (X := W) q.toRationalMap P'.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have htr : RationalMap.transform (h.compHom q) P.idealSheaf.support =
      RationalMap.transform (X := W) q.toRationalMap P'.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton (g'.compHom q) hrep P hg'P,
      MMP.Flips.coe_transform_eq_closure_singleton q.toPartialMap rfl P' trivial]
    congr 2
    change q (g'.hom ⟨P.genericPoint, hg'P⟩) = q P'.genericPoint
    rw [hη]
  rw [RationalMap.isExceptional_iff, RationalMap.isExceptional_iff, htr]
  exact ⟨fun h1 _ => h1 hdef1, fun h1 _ => h1 hdef2⟩

end StrictTransforms

/-! ### The central model -/

section CentralModel

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

/-- A pseudo-effective adjoint has a presentation `K_X + B = ∑ rᵢ [Aᵢ]` by Cartier divisors `Aᵢ`
with `∑ rᵢ Aᵢ` pseudo-effective over `Z`. -/
private theorem exists_presentation_of_isPsef {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    {π : X ⟶ Z} {KX : Divisor X} {B : RDivisor X} (hps : IsPsef sX π KX B) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → X.CartierDivisor) (w : Fin m → Divisor X),
      (∀ i, MMP.Intersection.IsWeilDivisorOfCartier (A i) (w i)) ∧
      logCanonicalDivisor KX B = ∑ i, r i • Divisor.toRDivisor (w i) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX π (∑ i, Finsupp.single (A i) (r i)) := by
  classical
  obtain ⟨D, hD, hDps⟩ := hps
  choose w hw using fun E : X.CartierDivisor => exists_isWeilDivisorOfCartier E
  let e := D.support.equivFin
  have hsum : ∀ {M : Type} [AddCommMonoid M] (g : X.CartierDivisor → M),
      ∑ i, g (e.symm i) = ∑ E ∈ D.support, g E := fun g => by
    rw [Equiv.sum_comp e.symm (fun E : D.support => g E), Finset.sum_coe_sort D.support g]
  refine ⟨D.support.card, fun i => D (e.symm i), fun i => e.symm i, fun i => w (e.symm i),
    fun i => hw _, ?_, ?_⟩
  · refine Finsupp.ext fun P => ?_
    have h1 := hD P
    rw [DivisorWithCoeffs.coeff_apply] at h1
    rw [h1, hsum (fun E => D E • Divisor.toRDivisor (w E)), Finsupp.finset_sum_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, ← DivisorWithCoeffs.coeff_apply,
      Divisor.coeff_toRDivisor, ← (hw E P).primeDivisorOrder_eq]
  · convert hDps
    rw [hsum (fun E => Finsupp.single E (D E))]
    exact Finsupp.sum_single D

/-- A klt pair with effective boundary is dlt: take the closed set `Z = X` in the definition. -/
private theorem isRealDltPair_of_isRealKltPair {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {B : RDivisor Y}
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hB : IsRealKltPair sY B) : IsRealDltPair sY B := by
  refine ⟨⟨hB.1, hB0, hB.2.2.1, fun n E a ha => (hB.2.2.2 n E a ha).le⟩,
    fun P => (hB.2.1 P).le, ⊤, ?_, ⟨fun E _ => (E.genericPoint.2 (Set.mem_univ _)).elim,
      fun x => (x.2 (Set.mem_univ _)).elim⟩, fun n D _ a ha => hB.2.2.2 n D a ha⟩
  exact SetLike.ext fun x => (x.2 (Set.mem_univ _)).elim

/-- **Strict transforms compose through a resolution.** Let `p : W ⟶ X` and `q : W ⟶ Y` be proper
birational morphisms of normal varieties, `h` the inverse of `p`, and suppose `φ = q ∘ h`
extracts no prime divisor. Then `φ_* p_* D = q_* D` for every divisor `D` on `W`. -/
private theorem transformDivisor_compHom_transformDivisor {X Y W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (hXn : IsNormalVariety ℂ sX) (hYn : IsNormalVariety ℂ sY)
    {p : W ⟶ X} {q : W ⟶ Y} [IsProper p] [IsProper q] (hWp : IsNormalVariety ℂ (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) {h : X.RationalMap W}
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hφ : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (h.compHom q) F)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor (h.compHom q)
        (MMP.Mori.RationalMap.transformDivisor p.toRationalMap D) =
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap D := by
  classical
  have := hXn.1
  have := hYn.1
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hWp
  haveI : IsSeparated p := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  haveI : IsSeparated q := IsSeparated.of_comp q (Y ↘ ⊤_ Scheme)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | single Q r =>
    rw [MMP.Mori.RationalMap.transformDivisor_single (X := W) p.toRationalMap,
      MMP.Mori.RationalMap.transformDivisor_single (X := W) q.toRationalMap]
    rcases hpQ : MMP.Mori.RationalMap.transformPrimeDivisor (X := W) p.toRationalMap Q with
      _ | P
    · rcases hqQ : MMP.Mori.RationalMap.transformPrimeDivisor (X := W) q.toRationalMap Q with
        _ | F
      · simp
      · exfalso
        refine hφ F fun P hP => ?_
        obtain ⟨E, hE, -, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWp hpb P
        have hhP := transformPrimeDivisor_eq_some_of_isInverse hpbij hinv hE
        rw [transformPrimeDivisor_compHom hhP q] at hP
        have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q E F).1 hP
        have h2 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q Q F).1 hqQ
        have hEQ : E = Q := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_map_eq_genericPoint q hqbij h1 h2)
        subst hEQ
        rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p E P).2 hE] at hpQ
        simp at hpQ
    · have hP := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p Q P).1 hpQ
      have hhP := transformPrimeDivisor_eq_some_of_isInverse hpbij hinv hP
      rw [show ((some P).elim 0 (Finsupp.single · r) : DivisorWithCoeffs R X) =
          Finsupp.single P r from rfl, MMP.Mori.RationalMap.transformDivisor_single,
        transformPrimeDivisor_compHom hhP q]

end CentralModel

/-! ### Pseudo-effectivity is a closed condition -/

section Psef

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {π : X ⟶ Z} {KX : Divisor X}

/-- The Weil divisor `∑_E c_E [E]` of an `ℝ`-Cartier divisor `∑_E c_E E`, as a function on prime
divisors. -/
private noncomputable def weil : KCartierDivisor ℝ X →ₗ[ℝ] (MMP.Mori.PrimeDivisor X → ℝ) :=
  Finsupp.linearCombination ℝ fun E P => (MMP.Intersection.primeDivisorOrder P E : ℝ)

private theorem weil_apply (D : KCartierDivisor ℝ X) (P : MMP.Mori.PrimeDivisor X) :
    weil D P = D.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ) := by
  simp only [weil, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

/-- **Rational kernels.** Let `o` be an integer matrix and `d` an integer vector vanishing on the
integer kernel of `o`. Then `d` vanishes on the real kernel of `o`: `d` lies in the rational row
space of `o`. -/
private theorem sum_mul_eq_zero_of_forall_int {ι κ : Type*} [Fintype ι] (o : κ → ι → ℤ)
    (d : ι → ℤ) (hd : ∀ n : ι → ℤ, (∀ k, ∑ i, n i * o k i = 0) → ∑ i, n i * d i = 0)
    (c : ι → ℝ) (hc : ∀ k, ∑ i, c i * o k i = 0) : ∑ i, c i * d i = 0 := by
  classical
  let r : κ → Module.Dual ℚ (ι → ℚ) := fun k => ∑ i, (o k i : ℚ) • LinearMap.proj i
  have hr : ∀ k n, r k n = ∑ i, n i * o k i := fun k n => by
    simp [r, mul_comm]
  let f : Module.Dual ℚ (ι → ℚ) := ∑ i, (d i : ℚ) • LinearMap.proj i
  have hf : ∀ n, f n = ∑ i, n i * d i := fun n => by simp [f, mul_comm]
  let R : Submodule ℚ (Module.Dual ℚ (ι → ℚ)) := Submodule.span ℚ (Set.range r)
  have hmem : f ∈ R := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := R), Submodule.mem_dualAnnihilator]
    intro n hn
    rw [Submodule.mem_dualCoannihilator] at hn
    have hn' : ∀ k, r k n = 0 := fun k => hn _ (Submodule.subset_span ⟨k, rfl⟩)
    let N : ℕ := ∏ i, (n i).den
    have hN : (N : ℚ) ≠ 0 := by
      simp only [N, Nat.cast_prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (n i).den_nz
    have hint : ∀ i, ∃ z : ℤ, (N : ℚ) * n i = z := fun i => by
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i => (n i).den) (Finset.mem_univ i)
      refine ⟨(n i).num * m, ?_⟩
      rw [show (N : ℚ) = ((n i).den * m : ℕ) from congrArg _ hm]
      push_cast
      rw [← Rat.mul_den_eq_num]
      ring
    choose z hz using hint
    have hz0 : ∀ k, ∑ i, z i * o k i = 0 := fun k => by
      have h3 : ((∑ i, z i * o k i : ℤ) : ℚ) = 0 := by
        have : ((∑ i, z i * o k i : ℤ) : ℚ) = N * r k n := by
          rw [hr, Finset.mul_sum]
          push_cast
          exact Finset.sum_congr rfl fun i _ => by rw [← hz i]; ring
        rw [this, hn' k, mul_zero]
      exact_mod_cast h3
    have := hd z hz0
    have h2 : ((∑ i, z i * d i : ℤ) : ℚ) = N * f n := by
      rw [hf, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [← hz i]; ring
    rw [this, Int.cast_zero] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left hN
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  have hdi : ∀ i, (d i : ℝ) = l.sum fun k a => (a : ℝ) * o k i := fun i => by
    have := congrArg (fun φ : Module.Dual ℚ (ι → ℚ) => φ (Pi.single i 1)) hl
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hr, hf, smul_eq_mul,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at this
    rw [Finsupp.sum]
    exact_mod_cast this.symm
  simp_rw [hdi, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  calc ∑ i, c i * ((l k : ℝ) * o k i) = (l k : ℝ) * ∑ i, c i * o k i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hc k, mul_zero]

/-- `deg_C 𝒪_X(E + E') = deg_C 𝒪_X(E) + deg_C 𝒪_X(E')` along a proper curve. -/
private theorem degree_cartierSheaf_add (C : ProperCurve sX) (E E' : X.CartierDivisor) :
    C.degree ℂ (MMP.CartierDivisor.sheaf (E + E')) =
      C.degree ℂ (MMP.CartierDivisor.sheaf E) +
        C.degree ℂ (MMP.CartierDivisor.sheaf E') := by
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 _ _
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf]
  exact (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le
    (L := ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        X.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf E)).obj
          (MMP.CartierDivisor.sheaf E'))
    (MMP.CartierDivisorSheaf.sheafMulIso E E')).symm

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeHom (C : ProperCurve sX) : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun E => C.degree ℂ (MMP.CartierDivisor.sheaf E))
    (degree_cartierSheaf_add C)

/-- The order of vanishing at a point `η` of coheight one of the image in `k(X)` of an element of
the local ring `𝒪_{X,η}` is its order. -/
private theorem ord_algebraMap_stalk {η : X} (hη : Order.coheight η = 1)
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

/-- **Units of a normal local ring.** Two nonzero elements of the local ring `𝒪_{X,x}` of a normal
scheme with the same order at every point of coheight one specializing to `x` are associated:
their quotient and its inverse are regular at `x`, by algebraic Hartogs. -/
private theorem associated_of_forall_ord_eq (x : X) {a b : X.presheaf.stalk x}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ (y : X) (hy : y ⤳ x), Order.coheight y = 1 →
      Ring.ord (X.presheaf.stalk y) ((X.presheaf.stalkSpecializes hy).hom a) =
        Ring.ord (X.presheaf.stalk y) ((X.presheaf.stalkSpecializes hy).hom b)) :
    Associated a b := by
  set alg := algebraMap (X.presheaf.stalk x) X.functionField
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have ha' : alg a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hb' : alg b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
      X.ord (alg a) Γ.genericPoint = X.ord (alg b) Γ.genericPoint := by
    intro Γ hΓ
    have hspec : Γ.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
      exact specializes_iff_mem_closure.mpr hΓ
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Γ
    have hsa := MMP.Intersection.stalkSpecializes_ne_zero hspec ha
    have hsb := MMP.Intersection.stalkSpecializes_ne_zero hspec hb
    rw [← MMP.Mori.algebraMap_stalkSpecializes hspec a,
      ← MMP.Mori.algebraMap_stalkSpecializes hspec b,
      ord_algebraMap_stalk h1 hsa, ord_algebraMap_stalk h1 hsb, h _ hspec h1]
  have hdiv : ∀ {c d : X.presheaf.stalk x}, alg c ≠ 0 → alg d ≠ 0 →
      (∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
        X.ord (alg c) Γ.genericPoint = X.ord (alg d) Γ.genericPoint) →
      ∃ r, alg r = alg c / alg d := by
    intro c d hc hd hcd
    refine MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x
      (div_ne_zero hc hd) fun Γ hΓ => ?_
    rw [div_eq_mul_inv, Scheme.ord_mul hc (inv_ne_zero hd)]
    have := MMP.Mori.ord_zpow Γ.genericPoint hd (-1)
    rw [zpow_neg, zpow_one] at this
    rw [this, hcd Γ hΓ]
    simp
  obtain ⟨r, hr⟩ := hdiv ha' hb' hord
  obtain ⟨s, hs⟩ := hdiv hb' ha' fun Γ hΓ => (hord Γ hΓ).symm
  have hrs : r * s = 1 := hinj (by rw [map_mul, hr, hs, map_one, div_mul_div_cancel₀ hb',
    div_self ha'])
  refine ⟨Units.mkOfMulEqOne s r (by rw [mul_comm]; exact hrs), hinj ?_⟩
  simp only [Units.val_mkOfMulEqOne, map_mul, hs]
  field_simp

open MMP.Intersection in
/-- **Cartier divisors are determined by their Weil divisors** on a normal variety: a Cartier
divisor of order zero along every prime divisor is trivial. At every point a local equation
`a / b` has `a` and `b` associated in the local ring, by `associated_of_forall_ord_eq`. -/
private theorem cartierDivisor_eq_zero_of_forall_primeDivisorOrder_eq_zero
    {A : X.CartierDivisor} (hA : ∀ P, MMP.Intersection.primeDivisorOrder P A = 0) : A = 0 := by
  apply eq_of_forall_isLocalEquationAt
  intro x
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt A x
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hassoc : Associated a b := by
    refine associated_of_forall_ord_eq x ha0 hb0 fun y hy h1 => ?_
    have hsa := stalkSpecializes_ne_zero hy ha0
    have hsb := stalkSpecializes_ne_zero hy hb0
    set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1
    have hgp : (primeDivisorSubvariety P).genericPoint = y :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1
    have h0 : IsOrderAlong A (primeDivisorSubvariety P) 0 := by
      rw [← hA P]; exact isOrderAlong_primeDivisorOrder A P
    have hsf := hf.stalkSpecializes hy
    have hsab := hab.stalkSpecializes hy
    clear_value P
    subst hgp
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety P).genericPoint) :=
      krullDimLE_of_coheight_le (by rw [h1]; rfl)
    have hN := isOrderAlong_of_isFraction hsf (mem_nonZeroDivisors_of_ne_zero hsa)
      (mem_nonZeroDivisors_of_ne_zero hsb) hsab
    have e := h0.unique hN
    have e' : (Ring.ord _ (X.presheaf.stalkSpecializes hy a)).toNat =
        (Ring.ord _ (X.presheaf.stalkSpecializes hy b)).toNat := by omega
    rw [← ENat.coe_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hsa)),
      ← ENat.coe_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hsb)), e']
  obtain ⟨u, hu⟩ := hassoc
  have hua : IsUnit (stalkToTotalQuotient x a) :=
    isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors ha
  have hfu : f = stalkToTotalQuotient x ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := by
    apply hua.mul_left_cancel
    have h2 := hab.2
    rw [← hu, map_mul] at h2
    have hu' : stalkToTotalQuotient x (u : X.presheaf.stalk x) *
        stalkToTotalQuotient x ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (stalkToTotalQuotient x ((u⁻¹ : (X.presheaf.stalk x)ˣ) :
      X.presheaf.stalk x)) * h2 - (stalkToTotalQuotient x a * f) * hu'
  refine ⟨f, hf, ?_⟩
  rw [hfu]
  exact isLocalEquationAt_zero_stalkToTotalQuotient x u⁻¹

/-- **Weil-trivial integral combinations have degree zero.** If the Cartier divisor `∑ nᵢ Eᵢ` has
order zero along every prime divisor, then `∑ nᵢ deg_C 𝒪_X(Eᵢ) = 0` for every proper curve `C`:
the divisor is trivial, and the degree is additive. -/
private theorem sum_mul_degree_eq_zero {ι : Type*} [Fintype ι] (E : ι → X.CartierDivisor)
    (n : ι → ℤ) (hn : ∀ P, ∑ i, n i * MMP.Intersection.primeDivisorOrder P (E i) = 0)
    (C : ProperCurve sX) :
    ∑ i, n i * C.degree ℂ (MMP.CartierDivisor.sheaf (E i)) = 0 := by
  have hA : ∑ i, n i • E i = 0 := cartierDivisor_eq_zero_of_forall_primeDivisorOrder_eq_zero
    fun P => by simpa [map_sum, map_zsmul, smul_eq_mul] using hn P
  have := congrArg (degreeHom C) hA
  rw [map_zero, map_sum] at this
  simpa [map_zsmul, smul_eq_mul, degreeHom] using this

/-- **Numerical triviality of Weil-trivial divisors.** On a normal variety an `ℝ`-Cartier divisor
whose Weil divisor vanishes has degree zero on every curve, so its class in `N¹(X/Z)` vanishes:
its coefficient vector lies in the real kernel of the integer matrix of orders, on whose integer
kernel the degrees vanish by `sum_mul_degree_eq_zero`. -/
private theorem relativeNumericalDivisorClass_eq_zero_of_weil_eq_zero
    {D : KCartierDivisor ℝ X} (hD : weil D = 0) :
    MMP.Fourfold.relativeNumericalDivisorClass sX π D = 0 := by
  classical
  rw [MMP.Fourfold.relativeNumericalDivisorClass, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  funext C
  have hC : MMP.Fourfold.relativeDegreeMap sX π D C =
      ∑ E : D.support, D E * (C.1.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) := by
    rw [Finset.sum_coe_sort D.support
      (fun E => D E * (C.1.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ))]
    simp [MMP.Fourfold.relativeDegreeMap, OneCycle.intersectionPairing,
      Finsupp.linearCombination_apply, OneCycle.cartierDegree, OneCycle.degree_apply,
      ProperCurve.cycle, Finsupp.sum]
  rw [hC, Pi.zero_apply]
  refine sum_mul_eq_zero_of_forall_int (fun P (E : D.support) =>
      MMP.Intersection.primeDivisorOrder P (E : X.CartierDivisor)) _
    (fun n hn => sum_mul_degree_eq_zero (fun E : D.support => (E : X.CartierDivisor)) n hn C.1)
    _ fun P => ?_
  have := congrFun hD P
  rw [weil_apply, Pi.zero_apply, Finsupp.sum] at this
  rw [← this]
  exact Finset.sum_coe_sort D.support
    (fun E => D E * (MMP.Intersection.primeDivisorOrder P E : ℝ))

private theorem isPsef_iff (B : RDivisor X) :
    IsPsef sX π KX B ↔ ∃ D : KCartierDivisor ℝ X,
      weil D = (fun P => (logCanonicalDivisor KX B).coeff P) ∧
      MMP.Fourfold.relativeNumericalDivisorClass sX π D ∈
        closure (MMP.Fourfold.relativeEffectiveCone sX π :
          Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX π)) := by
  refine exists_congr fun D => and_congr ?_ Iff.rfl
  rw [funext_iff]
  exact forall_congr' fun P => by rw [weil_apply, eq_comm]

/-- **Closedness of pseudo-effectivity.** The weights `μ` for which `K_X + ∑ μᵢ vᵢ` is
pseudo-effective over `Z` form a closed set. -/
private theorem isClosed_setOf_isPsef {N : ℕ} (v : Fin N → QDivisor X) :
    IsClosed {μ : Fin N → ℝ | IsPsef sX π KX (bary v μ)} := by
  classical
  set C := closure (MMP.Fourfold.relativeEffectiveCone sX π :
    Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX π))
  let a : (Fin N → ℝ) → (MMP.Mori.PrimeDivisor X → ℝ) := fun μ P =>
    (logCanonicalDivisor KX (bary v μ)).coeff P
  let lin : (Fin N → ℝ) →ₗ[ℝ] (MMP.Mori.PrimeDivisor X → ℝ) :=
    (LinearMap.pi fun P => Finsupp.lapply P) ∘ₗ bary v
  have ha : ∀ μ μ', a μ = a μ' + lin (μ - μ') := fun μ μ' => by
    funext P
    simp only [a, lin, logCanonicalDivisor, LinearMap.coe_comp, Function.comp_apply, map_sub,
      LinearMap.pi_apply, Finsupp.lapply_apply, Pi.add_apply, Pi.sub_apply,
      DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  by_cases hA : ∃ (μs : Fin N → ℝ) (Ds : KCartierDivisor ℝ X), weil Ds = a μs
  swap
  · convert isClosed_empty
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hps
    obtain ⟨D, hD, -⟩ := (isPsef_iff _).1 hps
    exact hA ⟨μ, D, hD⟩
  obtain ⟨μs, Ds, hDs⟩ := hA
  let L : Submodule ℝ (Fin N → ℝ) := (LinearMap.range weil).comap lin
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : L →ₗ[ℝ] KCartierDivisor ℝ X, ∀ δ : L, weil (ℓ δ) = lin δ := by
    obtain ⟨h, hh⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict weil)
      ((lin.domRestrict L).codRestrict (LinearMap.range weil) fun δ => δ.2)
      (LinearMap.surjective_rangeRestrict _)
    exact ⟨h, fun δ => congrArg Subtype.val (LinearMap.congr_fun hh δ)⟩
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl L
  let pr : (Fin N → ℝ) →ₗ[ℝ] L := Submodule.linearProjOfIsCompl L L' hL'
  let ψ : (Fin N → ℝ) → MMP.Fourfold.RelativeNumericalDivisorClasses sX π := fun μ =>
    MMP.Fourfold.relativeNumericalDivisorClass sX π (Ds + ℓ (pr (μ - μs)))
  have hpr : ∀ μ (hμ : μ - μs ∈ L), pr (μ - μs) = ⟨μ - μs, hμ⟩ := fun μ hμ =>
    Submodule.linearProjOfIsCompl_apply_left hL' ⟨μ - μs, hμ⟩
  have hweil : ∀ μ (hμ : μ - μs ∈ L), weil (Ds + ℓ (pr (μ - μs))) = a μ := fun μ hμ => by
    rw [map_add, hpr μ hμ, hℓ, hDs, ha μ μs]
  have key : {μ : Fin N → ℝ | IsPsef sX π KX (bary v μ)} =
      {μ | μ - μs ∈ L} ∩ ψ ⁻¹' C := by
    ext μ
    constructor
    · intro hps
      obtain ⟨D, hD, hDC⟩ := (isPsef_iff _).1 hps
      have hmem : μ - μs ∈ L := ⟨D - Ds, by
        rw [map_sub, hD, hDs]
        exact sub_eq_of_eq_add' (ha μ μs)⟩
      refine ⟨hmem, ?_⟩
      have : ψ μ = MMP.Fourfold.relativeNumericalDivisorClass sX π D := by
        rw [← sub_eq_zero, ← map_sub]
        refine relativeNumericalDivisorClass_eq_zero_of_weil_eq_zero ?_
        rw [map_sub, hweil μ hmem, hD, sub_self]
      simpa [Set.mem_preimage, this] using hDC
    · rintro ⟨hmem, hψ⟩
      exact (isPsef_iff _).2 ⟨_, hweil μ hmem, hψ⟩
  rw [key]
  refine IsClosed.inter ?_ (isClosed_closure.preimage ?_)
  · exact (Submodule.closed_of_finiteDimensional L).preimage (continuous_id.sub continuous_const)
  · refine continuous_induced_rng.2 ?_
    have hlin : Continuous ((MMP.Fourfold.relativeDegreeMap sX π) ∘ₗ ℓ ∘ₗ pr) :=
      LinearMap.continuous_of_finiteDimensional _
    have : ((LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π)).liftQ
        (MMP.Fourfold.relativeDegreeMap sX π) le_rfl) ∘ ψ =
        fun μ => MMP.Fourfold.relativeDegreeMap sX π Ds +
          ((MMP.Fourfold.relativeDegreeMap sX π) ∘ₗ ℓ ∘ₗ pr) (μ - μs) := by
      funext μ
      simp only [ψ, MMP.Fourfold.relativeNumericalDivisorClass, Function.comp_apply,
        Submodule.mkQ_apply, Submodule.liftQ_apply, map_add, LinearMap.coe_comp]
    rw [this]
    exact continuous_const.add (hlin.comp (continuous_id.sub continuous_const))

/-- **Pseudo-effectivity over a factorisation.** If `X ⟶ Z` factors through `g : X ⟶ T`, a
divisor pseudo-effective over `Z` is pseudo-effective over `T`: the curves contracted by `g` are
contracted over `Z`, so restriction of degrees induces a continuous linear map
`N¹(X/Z) ⟶ N¹(X/T)` carrying the effective cone into the effective cone. -/
private theorem isRelativelyPseudoEffective_of_comp {X Z T : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {g : X ⟶ T} {h : T ⟶ Z} {D : KCartierDivisor ℝ X}
    (hD : MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective sX (g ≫ h) D) :
    MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective sX g D := by
  classical
  have hC : ∀ C : ProperCurve sX, C.IsContractedBy g → C.IsContractedBy (g ≫ h) :=
    fun C hC x hx => by simp only [Scheme.Hom.comp_apply, hC x hx]
  let res : ({C : ProperCurve sX // C.IsContractedBy (g ≫ h)} → ℝ) →ₗ[ℝ]
      ({C : ProperCurve sX // C.IsContractedBy g} → ℝ) :=
    LinearMap.pi fun C => LinearMap.proj ⟨C.1, hC C.1 C.2⟩
  have hres : ∀ D, MMP.Fourfold.relativeDegreeMap sX g D =
      res (MMP.Fourfold.relativeDegreeMap sX (g ≫ h) D) := fun D => rfl
  have hker : LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX (g ≫ h)) ≤
      (LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX g)).comap LinearMap.id := by
    intro D hD
    simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.id_apply] at hD ⊢
    rw [hres, hD, map_zero]
  let Φ := Submodule.mapQ _ _ LinearMap.id hker
  have hΦ : ∀ D, Φ (MMP.Fourfold.relativeNumericalDivisorClass sX (g ≫ h) D) =
      MMP.Fourfold.relativeNumericalDivisorClass sX g D := fun D => rfl
  have hΦc : Continuous Φ := by
    refine continuous_induced_rng.2 ?_
    have : ((LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX g)).liftQ
        (MMP.Fourfold.relativeDegreeMap sX g) le_rfl) ∘ Φ =
        res ∘ ((LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX (g ≫ h))).liftQ
          (MMP.Fourfold.relativeDegreeMap sX (g ≫ h)) le_rfl) := by
      funext x
      induction x using Submodule.Quotient.induction_on with
      | H D => rfl
    rw [this]
    exact (continuous_pi fun C => continuous_apply _).comp continuous_induced_dom
  have hcone : Set.MapsTo Φ (MMP.Fourfold.relativeEffectiveCone sX (g ≫ h))
      (MMP.Fourfold.relativeEffectiveCone sX g) := by
    intro x hx
    change x ∈ Submodule.span _ _ at hx
    change Φ x ∈ Submodule.span _ _
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨E, hE, rfl⟩ := hy
      exact Submodule.subset_span ⟨E, hE, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have : Φ (c • a) = c • Φ a := map_smul Φ (c : ℝ) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  have := map_mem_closure hΦc hD hcone
  rwa [hΦ] at this

/-- The closure of the relative effective cone is stable under positive scalings. -/
private theorem smul_mem_closure_relativeEffectiveCone {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {c : ℝ} (hc : 0 ≤ c)
    {x : MMP.Fourfold.RelativeNumericalDivisorClasses sX π}
    (hx : x ∈ closure (MMP.Fourfold.relativeEffectiveCone sX π :
      Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX π))) :
    c • x ∈ closure (MMP.Fourfold.relativeEffectiveCone sX π :
      Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX π)) := by
  let Φ : MMP.Fourfold.RelativeNumericalDivisorClasses sX π →ₗ[ℝ]
      MMP.Fourfold.RelativeNumericalDivisorClasses sX π := c • LinearMap.id
  have hΦc : Continuous Φ := by
    refine continuous_induced_rng.2 ?_
    have : ((LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π)).liftQ
        (MMP.Fourfold.relativeDegreeMap sX π) le_rfl) ∘ Φ =
        (fun y => c • y) ∘ ((LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π)).liftQ
          (MMP.Fourfold.relativeDegreeMap sX π) le_rfl) := by
      funext y
      simp [Φ]
    rw [this]
    exact (continuous_const_smul c).comp continuous_induced_dom
  have hcone : Set.MapsTo Φ (MMP.Fourfold.relativeEffectiveCone sX π)
      (MMP.Fourfold.relativeEffectiveCone sX π) := fun y hy =>
    PointedCone.smul_mem _ hc hy
  exact map_mem_closure hΦc hx hcone

end Psef

/-! ### Cartier divisors with a prescribed Weil divisor -/

section WeilToCartier

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
        rw [← irreducibleComponents_eq_singleton]; exact W.2
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

/-! ### Convex geometry of the simplex -/

section SimplexGeometry

/-- **Radial decomposition near a point of the simplex.** For `λ⁰ ∈ Δ` and `ε > 0`, every
`λ ≠ λ⁰` of `Δ` near `λ⁰` is `(1 - t) λ⁰ + t λ''` with `0 < t < ε` and `λ''` on a facet of `Δ`:
`λ''` is where the ray from `λ⁰` through `λ` leaves `Δ`. -/
private theorem exists_mem_nhds_eq_lineMap_of_mem_stdSimplex {N : ℕ} {l₀ : Fin N → ℝ}
    (hl₀ : l₀ ∈ stdSimplex ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ nhds l₀, ∀ l ∈ V ∩ stdSimplex ℝ (Fin N), l ≠ l₀ →
      ∃ t : ℝ, 0 < t ∧ t < ε ∧ ∃ l'' ∈ stdSimplex ℝ (Fin N), (∃ i, l'' i = 0) ∧
        l = (1 - t) • l₀ + t • l'' := by
  classical
  set P := Finset.univ.filter fun i => 0 < l₀ i
  have hP : P.Nonempty :=
    let ⟨i, hi⟩ := exists_pos_of_mem_stdSimplex hl₀
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  set m := P.inf' hP l₀
  have hm : 0 < m := (Finset.lt_inf'_iff _).2 fun i hi => (Finset.mem_filter.1 hi).2
  have hmle : ∀ i ∈ P, m ≤ l₀ i := fun i hi => Finset.inf'_le _ hi
  refine ⟨Metric.ball l₀ (ε * m), Metric.ball_mem_nhds _ (mul_pos hε hm), ?_⟩
  rintro l ⟨hlb, hl⟩ hne
  have hdist : ∀ i, |l i - l₀ i| < ε * m := fun i => by
    have := (dist_le_pi_dist l l₀ i).trans_lt (Metric.mem_ball.1 hlb)
    rwa [Real.dist_eq] at this
  set D := Finset.univ.filter fun i => l i < l₀ i
  have hD : D.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hge : ∀ i, l₀ i ≤ l i := fun i => by
      by_contra hi
      push Not at hi
      have : i ∈ D := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
      simp [h] at this
    apply hne
    have hs : ∑ i, l i = ∑ i, l₀ i := by rw [hl.2, hl₀.2]
    funext i
    exact ((Finset.sum_eq_sum_iff_of_le fun i _ => hge i).1 hs.symm i (Finset.mem_univ _)).symm
  have hDP : ∀ i ∈ D, 0 < l₀ i := fun i hi =>
    lt_of_le_of_lt (hl.1 i) (Finset.mem_filter.1 hi).2
  set f : Fin N → ℝ := fun i => (l₀ i - l i) / l₀ i
  obtain ⟨i₀, hi₀D, hi₀⟩ := D.exists_max_image f hD
  set t := f i₀
  have hsub : 0 < l₀ i₀ - l i₀ := sub_pos.2 (Finset.mem_filter.1 hi₀D).2
  have ht0 : 0 < t := div_pos hsub (hDP i₀ hi₀D)
  have hi₀P : i₀ ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hDP i₀ hi₀D⟩
  have htε : t < ε := by
    rw [div_lt_iff₀ (hDP i₀ hi₀D)]
    calc l₀ i₀ - l i₀ < ε * m := by linarith [(abs_lt.1 (hdist i₀)).1]
      _ ≤ ε * l₀ i₀ := mul_le_mul_of_nonneg_left (hmle i₀ hi₀P) hε.le
  refine ⟨t, ht0, htε, l₀ + t⁻¹ • (l - l₀), ⟨fun i => ?_, ?_⟩, ⟨i₀, ?_⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    by_cases hi : i ∈ D
    · have hfi : f i ≤ t := hi₀ i hi
      have hpos := hDP i hi
      have : l₀ i - l i ≤ t * l₀ i := by
        have := (div_le_iff₀ hpos).1 hfi; linarith
      have : t⁻¹ * (l₀ i - l i) ≤ l₀ i := by
        rw [inv_mul_le_iff₀ ht0]; linarith
      nlinarith
    · have : l₀ i ≤ l i := by
        by_contra h; push Not at h; exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      have : 0 ≤ t⁻¹ * (l i - l₀ i) := mul_nonneg (inv_nonneg.2 ht0.le) (by linarith)
      linarith [hl₀.1 i]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hl.2, hl₀.2, sub_self, mul_zero, add_zero]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hpos := hDP i₀ hi₀D
    simp only [t, f]
    field_simp [hsub.ne', hpos.ne']
    ring
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring

/-- **A small rational simplex around a point of the simplex.** For `μ₀ ∈ Δ` and `r > 0` there
are a rational point `q ∈ Δ` and a rational `0 < δ < 1` with `‖q - μ₀‖ < r / 2`, `δ < r / 2`, and
`(1 - δ) qᵢ < μ₀ᵢ` whenever `qᵢ ≠ 0`. Then the rational simplex `(1 - δ) q + δ Δ` lies in the
`r`-ball around `μ₀` and contains a relative neighbourhood of `μ₀` in `Δ`. -/
private theorem exists_rat_simplex {N : ℕ} {μ₀ : Fin N → ℝ} (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin N))
    {r : ℝ} (hr : 0 < r) :
    ∃ (q : Fin N → ℚ) (δ : ℚ), 0 < δ ∧ δ < 1 ∧ (fun i => (q i : ℝ)) ∈ stdSimplex ℝ (Fin N) ∧
      (∀ i, |(q i : ℝ) - μ₀ i| < r / 2) ∧ (δ : ℝ) < r / 2 ∧
      ∀ i, q i = 0 ∨ (1 - (δ : ℝ)) * q i < μ₀ i := by
  classical
  obtain ⟨i₁, hi₁⟩ := exists_pos_of_mem_stdSimplex hμ₀
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (lt_min one_pos (half_pos hr))
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1 : (δ : ℝ) < 1 := hδ.trans_le (min_le_left _ _)
  have hδr : (δ : ℝ) < r / 2 := hδ.trans_le (min_le_right _ _)
  set S := Finset.univ.filter fun i => 0 < μ₀ i with hS
  have hN : (0 : ℝ) < N + 1 := by positivity
  set η : ℝ := min (r / (2 * (N + 1))) (δ * μ₀ i₁ / (N + 1)) with hη
  have hηpos : 0 < η :=
    lt_min (div_pos hr (by positivity)) (div_pos (mul_pos hδ0' hi₁) hN)
  have hrat : ∀ i, ∃ ρ : ℚ, μ₀ i - η < ρ ∧ (ρ : ℝ) < μ₀ i ∧ (0 < μ₀ i → 0 ≤ (ρ : ℝ)) := by
    intro i
    by_cases hi : 0 < μ₀ i
    · obtain ⟨ρ, h1, h2⟩ := exists_rat_btwn (show max (μ₀ i - η) 0 < μ₀ i from
        max_lt (by linarith) hi)
      exact ⟨ρ, lt_of_le_of_lt (le_max_left _ _) h1, h2, fun _ => (le_max_right _ _).trans h1.le⟩
    · obtain ⟨ρ, h1, h2⟩ := exists_rat_btwn (show μ₀ i - η < μ₀ i by linarith)
      exact ⟨ρ, h1, h2, fun h => absurd h hi⟩
  choose ρ hρ1 hρ2 hρ3 using hrat
  have hi₁S : i₁ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi₁⟩
  have hoff : ∀ i, i ∉ S → μ₀ i = 0 := fun i hi =>
    le_antisymm (not_lt.1 fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) (hμ₀.1 i)
  set T := S.erase i₁
  have hcardT : (T.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_univ T).trans (by simp)
  let q : Fin N → ℚ := fun i => if i = i₁ then 1 - ∑ j ∈ T, ρ j else if i ∈ S then ρ i else 0
  have hsumμ : μ₀ i₁ = 1 - ∑ j ∈ T, μ₀ j := by
    have h1 : ∑ i ∈ S, μ₀ i = 1 := by
      rw [← hμ₀.2]
      exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hoff i hi
    rw [← Finset.add_sum_erase S μ₀ hi₁S] at h1
    linarith
  have hgap : 0 ≤ ∑ j ∈ T, (μ₀ j - ρ j) ∧ ∑ j ∈ T, (μ₀ j - ρ j) ≤ N * η := by
    constructor
    · exact Finset.sum_nonneg fun j _ => by linarith [hρ2 j]
    · calc ∑ j ∈ T, (μ₀ j - ρ j) ≤ ∑ j ∈ T, η := Finset.sum_le_sum fun j _ => by linarith [hρ1 j]
        _ = T.card * η := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * η := mul_le_mul_of_nonneg_right hcardT hηpos.le
  have hq₁ : ((q i₁ : ℚ) : ℝ) = μ₀ i₁ + ∑ j ∈ T, (μ₀ j - ρ j) := by
    simp only [q, if_pos rfl]
    push_cast
    rw [Finset.sum_sub_distrib, hsumμ]
    ring
  have hqT : ∀ i, i ≠ i₁ → ((q i : ℚ) : ℝ) = if i ∈ S then (ρ i : ℝ) else 0 := fun i hi => by
    simp only [q, if_neg hi]
    split_ifs <;> simp
  have hNη' : (N : ℝ) * η < δ * μ₀ i₁ := by
    have : η ≤ δ * μ₀ i₁ / (N + 1) := min_le_right _ _
    calc (N : ℝ) * η ≤ N * (δ * μ₀ i₁ / (N + 1)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ < δ * μ₀ i₁ := by
        rw [mul_div_assoc', div_lt_iff₀ hN]
        nlinarith [mul_pos hδ0' hi₁]
  have hNη : (N : ℝ) * η < r / 2 := by
    have : η ≤ r / (2 * (N + 1)) := min_le_left _ _
    calc (N : ℝ) * η ≤ N * (r / (2 * (N + 1))) := mul_le_mul_of_nonneg_left this (by positivity)
      _ < r / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  refine ⟨q, δ, by exact_mod_cast hδ0, by exact_mod_cast hδ1, ⟨fun i => ?_, ?_⟩, fun i => ?_,
    hδr, fun i => ?_⟩
  · show 0 ≤ ((q i : ℚ) : ℝ)
    by_cases hi : i = i₁
    · subst hi; rw [hq₁]; linarith [hgap.1]
    · rw [hqT i hi]; split_ifs with h
      · exact hρ3 i (Finset.mem_filter.1 h).2
      · exact le_rfl
  · show ∑ i, ((q i : ℚ) : ℝ) = 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁), hq₁]
    have : ∑ i ∈ Finset.univ.erase i₁, ((q i : ℚ) : ℝ) = ∑ j ∈ T, (ρ j : ℝ) := by
      rw [Finset.sum_congr rfl fun i hi => hqT i (Finset.ne_of_mem_erase hi), ← Finset.sum_filter]
      congr 1
      ext i
      simp [T, Finset.mem_erase, and_comm]
    rw [this, Finset.sum_sub_distrib, hsumμ]
    ring
  · by_cases hi : i = i₁
    · subst hi; rw [hq₁, add_sub_cancel_left, abs_of_nonneg hgap.1]; linarith [hgap.2]
    · rw [hqT i hi]; split_ifs with h
      · have h1 : η ≤ r / (2 * (N + 1)) := min_le_left _ _
        have h2 : r / (2 * (N + 1)) ≤ r / 2 :=
          div_le_div_of_nonneg_left hr.le (by norm_num) (by linarith)
        rw [abs_lt]; constructor <;> linarith [hρ1 i, hρ2 i]
      · rw [hoff i h]; simp [hr]
  · by_cases hi : i = i₁
    · subst hi
      right
      rw [hq₁]
      nlinarith [hgap.1, hgap.2]
    · by_cases h : i ∈ S
      · right
        rw [hqT i hi, if_pos h]
        nlinarith [hρ2 i, hρ3 i (Finset.mem_filter.1 h).2]
      · left
        simp [q, hi, h]

/-- A positive function on a finite type has a positive lower bound. -/
private theorem exists_pos_forall_le_of_finite {κ : Type*} [Finite κ] (f : κ → ℝ)
    (hf : ∀ k, 0 < f k) : ∃ ε > 0, ∀ k, ε ≤ f k := by
  classical
  haveI := Fintype.ofFinite κ
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨1, one_pos, fun k => (IsEmpty.false k).elim⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, fun k => Finset.inf'_le _ (by simp)⟩
    exact (Finset.lt_inf'_iff _).2 fun k _ => hf k

end SimplexGeometry

section BaryAlgebra

variable {X : Scheme.{0}}

/-- The boundary of the weights `β` with respect to the rational combinations
`wⱼ = ∑ᵢ cⱼᵢ vᵢ` is the boundary of the weights `∑ⱼ βⱼ cⱼ` with respect to `v`. -/
private theorem bary_sum_smul {N M : ℕ} (v : Fin N → QDivisor X) (c : Fin M → Fin N → ℚ)
    (β : Fin M → ℝ) :
    bary (fun j => ∑ i, c j i • v i) β = bary v (fun i => ∑ j, β j * c j i) := by
  refine Finsupp.ext fun P => ?_
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply, coeff_bary, coeff_bary]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A boundary of weights vanishing at `i₀` is a boundary of the facet opposite `i₀`. -/
private theorem bary_eq_bary_comp_succAbove {M : ℕ} (w : Fin (M + 1) → QDivisor X)
    {β : Fin (M + 1) → ℝ} (i₀ : Fin (M + 1)) (hβ : β i₀ = 0) :
    bary w β = bary (w ∘ i₀.succAbove) (β ∘ i₀.succAbove) := by
  rw [bary_apply, bary_apply, Fin.sum_univ_succAbove _ i₀, hβ, zero_smul, zero_add]
  rfl

private theorem stdSimplex_comp_succAbove {M : ℕ} {β : Fin (M + 1) → ℝ}
    (hβ : β ∈ stdSimplex ℝ (Fin (M + 1))) (i₀ : Fin (M + 1)) (h0 : β i₀ = 0) :
    β ∘ i₀.succAbove ∈ stdSimplex ℝ (Fin M) := by
  refine ⟨fun i => hβ.1 _, ?_⟩
  have := hβ.2
  rw [Fin.sum_univ_succAbove _ i₀, h0, zero_add] at this
  exact this

private theorem coe_le_coeff_bary {N : ℕ} (v : Fin N → QDivisor X) {G : QDivisor X}
    (hGv : ∀ i P, G.coeff P ≤ (v i).coeff P) {μ : Fin N → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin N))
    (P : MMP.Mori.PrimeDivisor X) : (G.coeff P : ℝ) ≤ (bary v μ).coeff P := by
  rw [coeff_bary]
  calc (G.coeff P : ℝ) = ∑ i, μ i * (G.coeff P : ℝ) := by rw [← Finset.sum_mul, hμ.2, one_mul]
    _ ≤ ∑ i, μ i * ((v i).coeff P : ℝ) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hGv i P) (hμ.1 i)

end BaryAlgebra

/-- A nef log birational model whose boundary is the strict transform extracts no prime
divisor. -/
private theorem IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor
    {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y} {B : RDivisor X} {φ : X.RationalMap Y}
    (hφ : IsRealLogMinimalModel sX sY sZ π πY KX B KY
      (MMP.Mori.RationalMap.transformDivisor φ B) φ) (F : MMP.Mori.PrimeDivisor Y) :
    ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
  classical
  intro hF
  have := hφ.coeff_boundary F
  rw [if_pos hF] at this
  linarith

/-! ### Crepant comparisons of log discrepancies -/

universe u

/-- **The centre of a divisorial valuation on a proper model.** Let `π : W ⟶ X` be a proper
dominant morphism of integral schemes and `D` a divisor over `X`. A valuation `ξ` of `k(W)`
restricting to `ord_D` on `k(X)` dominates the local ring of some point of `W`. -/
private theorem exists_dominated_point {k : Type u} [Field k] {X W : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] {sX : X ⟶ Spec (.of k)} (π : W ⟶ X) [IsDominant π] (hπ : IsProper π)
    (D : DivisorOver k sX) (ξ : Valuation W.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ.comap (functionFieldMap π) = D.valuation) :
    ∃ x : W, (∀ a : W.presheaf.stalk x, ξ (algebraMap _ W.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk x),
        ξ (algebraMap _ W.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  have hw : ∀ b : X.presheaf.stalk y,
      ξ (functionFieldMap π (algebraMap _ X.functionField b)) =
        D.valuation (algebraMap _ X.functionField b) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ X.functionField b)) h
    simpa only [Valuation.comap_apply] using this
  let R := ξ.valuationSubring
  let φ : X.presheaf.stalk y →+* R :=
    ((functionFieldMap π).comp (algebraMap (X.presheaf.stalk y) X.functionField)).codRestrict R
      fun b => (ξ.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  have hex : ValuativeCriterion.Existence π := by
    have h : @IsProper _ _ π := hπ
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq π :=
    { R := R
      K := W.functionField
      i₁ := W.fromSpecStalk (genericPoint W)
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk y
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk π,
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R W.functionField)) ≫ l =
      W.fromSpecStalk (genericPoint W) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint W ⤳ x := (genericPoint_spec W).specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R W.functionField) =
      W.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : W.presheaf.stalk x,
      algebraMap _ W.functionField a = ((f.hom a : R) : W.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]; exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

open Classical in
/-- Sums over the prime divisors of a finite set, written through `Fin`. -/
private theorem sum_equivFin_mul_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∑ i : Fin S.card, c (S.equivFin.symm i) *
        (((Finsupp.single (S.equivFin.symm i : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ) =
      if Γ ∈ S then c Γ else 0 := by
  rw [Equiv.sum_comp S.equivFin.symm (fun x : S => c x *
    (((Finsupp.single (x : MMP.Mori.PrimeDivisor X) (1 : ℤ)) Γ : ℤ) : ℝ))]
  rw [Finset.sum_coe_sort S (fun x => c x * (((Finsupp.single x (1 : ℤ)) Γ : ℤ) : ℝ))]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single Γ]
    · simp
    · intro b _ hb; simp [hb]
    · intro h'; exact absurd h h'
  · refine Finset.sum_eq_zero fun b hb => ?_
    have : b ≠ Γ := fun h' => h (h' ▸ hb)
    simp [this]

section CrepantInputs

open MMP.Flips
open scoped WithZero

/-! ### Log discrepancies and discrepancies -/

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A discrepancy computed with a form whose divisor is canonical gives the log discrepancy
`1 + a`. -/
private theorem isLogDiscrepancy_of_isDiscrepancyWith {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    {E : ProperDivisorOver k sX} {b : ℝ} (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (h : IsDiscrepancyWith sX n D ω r L E b) :
    MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + b) := by
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := h
  refine ⟨hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r,
    L, L', hLc, fun Γ => ?_, hpb, by ring⟩
  have := congrArg (fun D : RDivisor X => D.coeff Γ) hsum
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    MMP.Flips.coeff_sum_smul_toRDivisor] using this

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : ProperDivisorOver k sX) : ∃ b, IsDiscrepancyWith sX n D ω r L E b := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := E.isProper
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end Discrepancy

/-! ### Changing the structure morphism -/

section StructureMorphism

variable {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] [CompactSpace W]

private theorem isDiscrepancy_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {n : ℕ} {K : Divisor W} {D : RDivisor W}
    {v : Valuation W.functionField ℤᵐ⁰} {a : ℝ} (ha : MMP.Flips.IsDiscrepancy s n K D v a) :
    MMP.Flips.IsDiscrepancy s' n K D v a := by
  subst h
  exact ha

omit [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] in
private theorem exists_properDivisorOver_of_eq {s s' : W ⟶ Spec (.of k)} (h : s = s')
    (E : ProperDivisorOver k s) : ∃ E' : ProperDivisorOver k s', E'.valuation = E.valuation := by
  subst h
  exact ⟨E, rfl⟩

end StructureMorphism

/-! ### Lifting a divisor over `M` to a proper model `W ⟶ M` -/

section Lift

variable {k : Type u} [Field k] {M W : Scheme.{u}} [IsIntegral M] [IsIntegral W]
  {sM : M ⟶ Spec (.of k)}

variable [IsLocallyNoetherian M] [IsNormal M] [IsLocallyNoetherian W] [IsNormal W]

/-- **Lifting a divisor over `M` along a proper birational morphism.** Every divisor `D` over `M`
with proper model has the valuation `ord_E ∘ q^*` of a divisor `E` over `W`, for `q : W ⟶ M`
proper birational with `W` a variety. -/
private theorem exists_properDivisorOver_comap_eq (q : W ⟶ M) [IsProper q]
    (hq : IsBirationalMorphism q) [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (D : ProperDivisorOver k sM) :
    haveI := hq.isDominant
    ∃ E : ProperDivisorOver k (q ≫ sM),
      E.valuation.comap (functionFieldMap q) = D.valuation := by
  haveI := hq.isDominant
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hbq := hq.functionFieldMap_bijective
  let eq := RingEquiv.ofBijective (functionFieldMap q) hbq
  let ξ : Valuation W.functionField ℤᵐ⁰ := D.valuation.comap eq.symm.toRingHom
  have hξ : ξ.comap (functionFieldMap q) = D.valuation := by
    ext a
    change D.valuation (eq.symm (functionFieldMap q a)) = D.valuation a
    rw [show functionFieldMap q a = eq a from rfl, RingEquiv.symm_apply_apply]
  obtain ⟨x, hle, hlt⟩ := exists_dominated_point q ‹_› D.toDivisorOver ξ hξ
  have hdiv : IsDivisorOfFunctionField k (q ≫ sM) ξ := by
    refine ⟨D.Y, D.f ≫ sM, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra sM
    letI := functionFieldAlgebra (q ≫ sM)
    letI := functionFieldAlgebra (D.f ≫ sM)
    let eP := functionFieldAlgEquiv sM q hbq
    let eY := functionFieldAlgEquiv sM D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbq.2 t
    change D.valuation (eq.symm (functionFieldMap q s)) =
      D.E.divisorialValuation (eY (eP.symm (functionFieldMap q s)))
    have h1 : eP.symm (functionFieldMap q s) = s := eP.symm_apply_apply s
    rw [h1, show functionFieldMap q s = eq s from rfl, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨E, -, hv, -⟩ := exists_properDivisorOver_isProjective_of_dominates (q ≫ sM) hdiv x hle hlt
  exact ⟨E, by rw [hv, hξ]⟩

end Lift

/-! ### Compatible forms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

open MMP.Positivity in
/-- For a proper birational morphism `f : Y → X` of normal varieties of dimension `n` and a
canonical divisor `K_Y` of `Y`, there is a nonzero rational top form `ω` on `X` with
`div_Y(f^*ω) = K_Y` and `div_X(ω) = f_* K_Y`. -/
private theorem exists_divisorOfForm_eq_transformDivisor (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX)) [IsProper f]
    (hf : IsBirationalMorphism f) [IsDominant f] {n : ℕ} (hn : topologicalKrullDim X = n)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n) :
    ∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧
      divisorOfForm ω = RationalMap.transformDivisor (X := Y) f.toRationalMap KY ∧
      divisorOfForm (pullbackRationalPluriForms sX f ω) = KY := by
  have hbij := hf.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨ω₁, hω₁0, hω₁⟩ := IsCanonicalDivisor.exists_ordForm_eq hY hKY
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr ω₁ ())
  let τ : RationalPluriForms sX n 1 :=
    g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sX f τ = ω₁ := by
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 τ = ω₁
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
    change functionFieldMap f g • _ = ω₁
    rw [hg]
    exact basis_unit_repr_smul _ ω₁
  refine ⟨τ, fun h0 => hω₁0 ?_, Finsupp.ext fun P => ?_, Finsupp.ext fun Γ => ?_⟩
  · rw [← hpull, h0]
    change pullbackForms (K := X.functionField) (K' := Y.functionField) 1 0 = 0
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    simp
  · obtain ⟨E, heq, hiso, htr⟩ := exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hf P
    rw [htr]
    change P.ordForm τ = KY.coeff E
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E P heq τ, hpull, hω₁]
  · change Γ.ordForm _ = KY.coeff Γ
    rw [hpull, hω₁]

end Forms

/-! ### Comparison of log discrepancies along a common resolution -/

section Comparison

variable {k : Type u} [Field k] [PerfectField k]

/-- **Adding an effective `ℝ`-Cartier divisor lowers discrepancies.** If `a` is the discrepancy
of a valuation `v` with respect to `D` and `D' ≥ 0` is `ℝ`-Cartier, the discrepancy with respect
to `D + D'` is some `a' ≤ a`. -/
private theorem exists_le_isDiscrepancy_add {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [LocallyOfFiniteType sW] {n : ℕ} {K : Divisor W} {D : RDivisor W}
    {v : Valuation W.functionField ℤᵐ⁰} {a : ℝ} (h : IsDiscrepancy sW n K D v a)
    {D' : RDivisor W} (hD' : RDivisor.IsRCartier D') (h0 : 0 ≤ D') :
    ∃ a', a' ≤ a ∧ IsDiscrepancy sW n K (D + D') v a' := by
  obtain ⟨hK, ⟨m, r, L, hL, hKD⟩, hc, E₀, ω₀, m₀, r₀, L₀, hE₀, hdiv₀, hw₀⟩ := h
  obtain ⟨hX, hn, hω, hLc, hsum, L', hpb, rfl⟩ := hw₀
  obtain ⟨m', r', C, hC, hD'eq⟩ := hD'
  have hD'eq' : D' = ∑ j, r' j • Divisor.toRDivisor (C j) := by
    ext Γ
    exact (hD'eq Γ).trans (MMP.Flips.coeff_sum_smul_toRDivisor r' C Γ).symm
  haveI := E₀.isIntegral
  haveI := E₀.isNormal
  haveI := E₀.isLocallyNoetherian
  haveI := E₀.isDominant
  haveI := E₀.isProper
  haveI : CompactSpace E₀.Y := QuasiCompact.compactSpace_of_compactSpace E₀.f
  choose C' hC' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E₀.f (hC j)
  have hG : IsRCartierPullback E₀.f D' (∑ j, r' j • Divisor.toRDivisor (C' j)) :=
    ⟨m', r', C, C', hC, hD'eq', fun j => ⟨_, hC' j⟩, rfl⟩
  have hG0 := (MMP.Fourfold.isEffective_of_isRCartierPullback E₀.f
    ⟨m', r', C, hC, hD'eq⟩ h0).2 _ hG
  have hnn : (0 : ℝ) ≤ ∑ j, r' j * ((C' j).coeff E₀.E : ℝ) := by
    have := hG0 E₀.E
    change (0 : ℝ) ≤ DivisorWithCoeffs.coeff (∑ j, r' j • Divisor.toRDivisor (C' j)) E₀.E at this
    rwa [MMP.Flips.coeff_sum_smul_toRDivisor] at this
  refine ⟨(E₀.toDivisorOver.ordPullback ω₀ : ℝ) - ∑ j, r₀ j * (L' j).coeff E₀.E -
    ∑ j, r' j * ((C' j).coeff E₀.E : ℝ), by linarith, hK, ⟨m + m', Fin.append r r',
      Fin.append L C, Fin.addCases (by simpa using hL) (by simpa using hC), ?_⟩, hc, E₀, ω₀,
      m₀ + m', Fin.append r₀ r', Fin.append L₀ C, hE₀, hdiv₀, hX, hn, hω,
      Fin.addCases (by simpa using hLc) (by simpa using hC), ?_, Fin.append L' C',
      Fin.addCases (by simpa using hpb) (by simpa using fun j =>
        (⟨_, hC' j⟩ : ∃ hB, (C j).IsPullback E₀.f hB (C' j))), ?_⟩
  · rw [← add_assoc, hKD, hD'eq', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, MMP.Flips.toRDivisor_eq_mapCoeffs]
  · rw [← add_assoc, hsum, hD'eq', Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

variable {X M W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sM : M ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [IsIntegral M] [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M]
  [LocallyOfFiniteType sM] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]

/-- **Comparison of log discrepancies along a common resolution.** Let `p : W ⟶ X` and
`q : W ⟶ M` be proper birational morphisms of normal varieties of dimension `n`, with rational
top forms `ω_X`, `ω_M` whose canonical divisors pull back to the same `K_W`. If
`G_X = p^*(K_X + D_X)` and `G_M = q^*(K_M + D_M)` differ by an effective `ℝ`-Cartier divisor
`G_X - G_M ≥ 0`, then every log discrepancy of `(M, D_M)` is at least one of `(X, D_X)`; in
particular if all log discrepancies of `(X, D_X)` are positive, so are those of `(M, D_M)`. -/
private theorem logDiscrepancy_pos_of_crepant_le {p : W ⟶ X} {q : W ⟶ M} [IsProper p]
    [IsProper q] [IsDominant p] [IsDominant q] [LocallyOfFiniteType (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sM)] [AlgebraicGeometry.IsVariety k (q ≫ sM)]
    (hXn : IsNormalVariety k sX) (hMn : IsNormalVariety k sM)
    (hWnp : IsNormalVariety k (p ≫ sX)) (hWnq : IsNormalVariety k (q ≫ sM))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hss : q ≫ sM = p ≫ sX)
    {n : ℕ} (hdM : topologicalKrullDim M = n)
    {ωX : RationalPluriForms sX n 1} (hωX0 : ωX ≠ 0)
    (hKXc : (divisorOfForm ωX).IsCanonicalDivisor sX n)
    {ωM : RationalPluriForms sM n 1} (hωM0 : ωM ≠ 0)
    (hKMc : (divisorOfForm ωM).IsCanonicalDivisor sM n)
    {KW : Divisor W} (hKWp : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hKWq : KW.IsCanonicalDivisor (q ≫ sM) n)
    (hωXW : divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW)
    (hωMW : divisorOfForm (pullbackRationalPluriForms sM q ωM) = KW)
    {DX : RDivisor X} {DM : RDivisor M} {GX GM : RDivisor W}
    (hGp : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX) GX)
    (hGq : MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM) GM)
    (hRC : RDivisor.IsRCartier (GX - GM)) (hle : 0 ≤ GX - GM)
    (hkltX : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d DX E a → 0 < a)
    (d : ℕ) (E : DivisorOver k sM) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sM d DM E a) : 0 < a := by
  obtain rfl : d = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hdM
  let EP : MMP.Flips.ProperDivisorOver k sM := ⟨E, ha.2.1⟩
  obtain ⟨mM, rM, LM, -, hLMc, hLMsum, -, -⟩ := id hGq
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith hMn hdM hωM0 hLMc hLMsum EP
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha
    (isLogDiscrepancy_of_isDiscrepancyWith hKMc hb)]
  have hKDM : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωM) + DM) :=
    ⟨mM, rM, LM, hLMc, by rw [hLMsum]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨E', hE'⟩ := exists_properDivisorOver_comap_eq q hqb EP
  have hDYq : MMP.Flips.IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωM) + DM)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sM q ωM)) +
        (GM - Divisor.toRDivisor KW)) := by
    rw [hωMW, add_sub_cancel]; exact hGq
  have h1 := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hMn hωM0 hKMc hKDM q hWnq hqb
    hDYq (by rw [hωMW]; exact hKWq) E' b).mp (by
      rw [hE']
      exact ⟨hKMc, hKDM, hasNonemptyCenter_valuation EP, EP, ωM, mM, rM, LM, rfl, rfl, hb⟩)
  rw [hωMW] at h1
  -- lowering the boundary on `W` from `G_M - K_W` to `G_X - K_W`
  obtain ⟨b', hb'b, h2⟩ := exists_le_isDiscrepancy_add h1 hRC hle
  have hGsum : GM - Divisor.toRDivisor KW + (GX - GM) = GX - Divisor.toRDivisor KW := by abel
  rw [hGsum] at h2
  obtain ⟨E'', hE''⟩ := exists_properDivisorOver_of_eq hss E'
  obtain ⟨mX, rX, LX, -, hLXc, hLXsum, -, -⟩ := id hGp
  have hKDX : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωX) + DX) :=
    ⟨mX, rX, LX, hLXc, by rw [hLXsum]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hDYp : MMP.Flips.IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ωX) + DX)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX)) +
        (GX - Divisor.toRDivisor KW)) := by
    rw [hωXW, add_sub_cancel]; exact hGp
  obtain ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, -, hdiv₀, hw₀⟩ :=
    (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXn hωX0 hKXc hKDX p hWnp hpb hDYp
      (by rw [hωXW]; exact hKWp) E'' b').mpr (by rw [hωXW, hE'']; exact isDiscrepancy_of_eq hss h2)
  have := hkltX _ E₀.toDivisorOver (1 + b')
    (isLogDiscrepancy_of_isDiscrepancyWith (by rw [hdiv₀]; exact hKXc) hw₀)
  linarith

omit [PerfectField k] in
open Classical in
/-- On a smooth variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isSmoothScheme {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (hsm : IsSmoothScheme sZ)
    (D : RDivisor Z) : RDivisor.IsRCartier D := by
  refine ⟨D.support.card, fun i => D.coeff (D.support.equivFin.symm i),
    fun i => Finsupp.single (D.support.equivFin.symm i : MMP.Mori.PrimeDivisor Z) (1 : ℤ),
    fun i => MMP.Fourfold.isCartier_of_isSmoothScheme hsm _, fun Γ => ?_⟩
  simp only [DivisorWithCoeffs.coeff_apply]
  rw [sum_equivFin_mul_single D.support (⇑D) Γ]
  split_ifs with h
  · rfl
  · exact Finsupp.notMem_support_iff.mp h

end Comparison

end CrepantInputs

section NefModel

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem isNormalVariety_comp_left {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) :
    IsNormalVariety k (p ≫ sX) := by
  rw [hR.comp_eq_left]; exact ⟨hR.isVariety, inferInstance⟩

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem isNormalVariety_comp_right {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) :
    IsNormalVariety k (q ≫ sY) := by
  rw [hR.comp_eq_right]; exact ⟨hR.isVariety, inferInstance⟩

omit [PerfectField k] [CompactSpace X] [LocallyOfFiniteType sX] in
private theorem compactSpace_of_isLogComparisonResolution {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY) : CompactSpace W := by
  have := hR.isVariety
  exact QuasiCompact.compactSpace_of_compactSpace sW

/-- **One rational top form on each side of a common resolution.** On a common resolution
`p : W ⟶ X`, `q : W ⟶ Y` comparing canonical divisors `K_X` and `K_Y`, the varieties have the
same dimension `n`, and there are a canonical divisor `K_W` of `W` and nonzero rational top forms
`ω_X`, `ω_Y` with `div ω_X = K_X`, `div ω_Y = K_Y` and `div(p^*ω_X) = K_W = div(q^*ω_Y)`. -/
private theorem exists_rationalPluriForms_of_isLogComparisonResolution {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [CompactSpace Y]
    [LocallyOfFiniteType sY] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y} {KX : Divisor X}
    {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W} [IsProper p] [IsProper q] [IsDominant p]
    [IsDominant q] [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sY)]
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY) :
    nY = n ∧ ∃ KW : Divisor W, KW.IsCanonicalDivisor (p ≫ sX) n ∧
      KW.IsCanonicalDivisor (q ≫ sY) n ∧
      (∃ ωX : RationalPluriForms sX n 1, ωX ≠ 0 ∧ divisorOfForm ωX = KX ∧
        divisorOfForm (pullbackRationalPluriForms sX p ωX) = KW) ∧
      ∃ ωY : RationalPluriForms sY n 1, ωY ≠ 0 ∧ divisorOfForm ωY = KY ∧
        divisorOfForm (pullbackRationalPluriForms sY q ωY) = KW := by
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  obtain ⟨nW, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hdimX := hKX.topologicalKrullDim_eq
  have := hXn.1
  have := hYn.1
  have := hWnp.1
  have := hWnq.1
  have hdimW : topologicalKrullDim W = topologicalKrullDim X :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  have hdimY : topologicalKrullDim W = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (q ≫ sY) hqb).symm
  obtain rfl : nW = n := by
    exact_mod_cast hKW.topologicalKrullDim_eq.symm.trans (hdimW.trans hdimX)
  have hKWp : KW.IsCanonicalDivisor (p ≫ sX) nW := by rw [hR.comp_eq_left]; exact hKW
  have hKWq : KW.IsCanonicalDivisor (q ≫ sY) nW := by rw [hR.comp_eq_right]; exact hKW
  have hdM : topologicalKrullDim Y = nW := hdimY.symm.trans hKW.topologicalKrullDim_eq
  obtain ⟨ωX, hωX0, hωX, hωXW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hXn hWnp hpb hdimX hKWp
  obtain ⟨ωY, hωY0, hωY, hωYW⟩ :=
    exists_divisorOfForm_eq_transformDivisor hYn hWnq hqb hdM hKWq
  exact ⟨by exact_mod_cast hKY.topologicalKrullDim_eq.symm.trans hdM, KW, hKWp, hKWq,
    ⟨ωX, hωX0, hωX.trans hKWX, hωXW⟩, ωY, hωY0, hωY.trans hKWY, hωYW⟩

/-- **Klt descends along an effective comparison.** If a common resolution compares the adjoints
of `(X, Δ)` and `(Y, Δ_Y)` with `p^*(K_X + Δ) - q^*(K_Y + Δ_Y)` effective, then every log
discrepancy of `(Y, Δ_Y)` is positive as soon as every log discrepancy of `(X, Δ)` is. -/
private theorem isLogDiscrepancy_pos_of_isLogComparisonResolution {W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)}
    {φ : X.RationalMap Y} {KX : Divisor X} {Δ : RDivisor X} {KY : Divisor Y} {ΔY : RDivisor Y}
    {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX Δ KY ΔY p q h GX GY)
    (hXn : IsNormalVariety k sX) (hYn : IsNormalVariety k sY) {n nY : ℕ}
    (hKX : KX.IsCanonicalDivisor sX n) (hKY : KY.IsCanonicalDivisor sY nY)
    (hkltX : ∀ (d : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX d Δ E a → 0 < a) :
    ∀ (d : ℕ) (E : DivisorOver k sY) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY d ΔY E a → 0 < a := by
  have hWnp := isNormalVariety_comp_left hR
  have hWnq := isNormalVariety_comp_right hR
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (q ≫ sY) := hWnq.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety k (q ≫ sY) := hWnq.1
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have := hYn.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have := compactSpace_of_isLogComparisonResolution hR
  obtain ⟨rfl, KW, hKWp, hKWq, ⟨ωX, hωX0, hωX, hωXW⟩, ωY, hωY0, hωY, hωYW⟩ :=
    exists_rationalPluriForms_of_isLogComparisonResolution hR hXn hYn hKX hKY
  have hGp := hR.isRCartierPullback_left
  have hGq := hR.isRCartierPullback_right
  rw [MMP.Flips.logCanonicalDivisor, ← hωX] at hGp
  rw [MMP.Flips.logCanonicalDivisor, ← hωY] at hGq
  exact logDiscrepancy_pos_of_crepant_le hXn hYn hWnp hWnq hpb hqb
    (hR.comp_eq_right.trans hR.comp_eq_left.symm) hKY.topologicalKrullDim_eq hωX0
    (by rw [hωX]; exact hKX) hωY0 (by rw [hωY]; exact hKY) hKWp hKWq hωXW hωYW hGp hGq
    (isRCartier_of_isSmoothScheme hR.isSmoothScheme _) (fun P => hR.effective P) hkltX

end NefModel

/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor_real {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X]
    (hX : IsNormalVariety ℂ sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

section FiberRankCongr

open TensorProduct

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
  obtain ⟨V, hyV, ξ, hξ⟩ := X.presheaf.exists_germ_eq ρ
  obtain ⟨W, hWV, hyW, ζ, hζ⟩ := TopCat.Presheaf.exists_le_germ_eq F.val.presheaf n hyV
  subst hξ
  subst hζ
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

private lemma stalkMapAb_inv_hom (e : F ≅ G) (x : X)
    (n : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x) :
    stalkMapAb e.inv x (stalkMapAb e.hom x n) = n := by
  obtain ⟨W, hW, ζ, rfl⟩ := TopCat.Presheaf.germ_exist F.val.presheaf n
  have h1 := stalkMapAb_germ e.hom x hW (ζ : Γ(F, W))
  have h2 := stalkMapAb_germ e.inv x hW (e.hom.app W (ζ : Γ(F, W)))
  have h3 : e.inv.app W (e.hom.app W (ζ : Γ(F, W))) = ζ := by
    have := ConcreteCategory.congr_hom (show e.hom.app W ≫ e.inv.app W = 𝟙 _ from by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl) ζ
    exact this
  rw [h1, h2, h3]

/-- The fibre rank is invariant under isomorphism of modules. -/
private theorem fiberRank_congr (e : F ≅ G) (x : X) :
    Scheme.Modules.fiberRank F x = Scheme.Modules.fiberRank G x := by
  unfold Scheme.Modules.fiberRank
  let eS : TopCat.Presheaf.stalk (C := Ab.{0}) F.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{0}) G.val.presheaf x :=
    { toFun := stalkMapAb e.hom x
      map_add' := map_add _
      map_smul' := fun ρ n => stalkMapAb_smul e.hom x ρ n
      invFun := stalkMapAb e.inv x
      left_inv := stalkMapAb_inv_hom e x
      right_inv := stalkMapAb_inv_hom e.symm x }
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (X.residueField x) _) eS).finrank_eq

end FiberRankCongr

/-! ### Curves under morphisms -/

section CurveImages

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `g` is a proper curve. -/
private theorem isProperCurve_map (g : X ⟶ Y) (hg : g ≫ sY = sX) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : IsProperCurve sY (g Γ.point) := by
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hcurve := isCurve_imageι_comp sY φ (not_exists_range_eq_singleton g Γ h)
  have hker := Γ.ker_comp g
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (g Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (g Γ.point) ≫ sY) := by
    have h1 : IsProper (φ.imageι ≫ sY) := isProper_imageι_comp φ sY
    change IsProper (φ.ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- A morphism over `k` which does not contract a proper curve has positive residue degree at
its generic point: `k(C)` is a finite extension of the function field of the image curve. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
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
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end CurveImages

section Projection

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- The projection formula, for a structure morphism `s` of the source equal to `h ≫ s_Y`. -/
private theorem degreeOn_pullback_eq_mul' {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) {s : Y' ⟶ Spec (.of k)} (hs : h ≫ sY = s) [QuasiCompact s] [CompactSpace Y]
    [CompactSpace Y'] {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve s) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k s C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  subst hs
  exact degreeOn_pullback_eq_mul h hD hB C' C hC

end Projection

/-! ### Degree forms on relative curve classes -/

section Normalization

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_isCurveNormalization {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : MMP.Flips.IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve ℂ p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType ℂ p
  haveI hvar : AlgebraicGeometry.IsVariety ℂ (normalizationOverField ℂ p ≫ p) :=
    isVariety_normalizationOverField ℂ p
  haveI : IsIntegral (normalizationSchemeOverField ℂ p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField ℂ p) := isFinite_normalizationOverField ℂ p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField ℂ p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField ℂ p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField ℂ p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField ℂ p).le.trans C.dim_le⟩

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    MMP.Flips.IsCartierIntersectionNumber ℂ sX C L hL (L.degreeOn ℂ sX C.ι C.dim_le hL) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_isCurveNormalization C
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

end Normalization

section Forms

variable {Y Z : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  (sY : Y ⟶ Spec (.of ℂ)) (f : Y ⟶ Z)

/-- The degree form `z ↦ (z · 𝒪_Y(L))` on `N₁(Y/Z)` of a Cartier divisor `L`. -/
private noncomputable def relDeg (L : Divisor Y) (hL : L.IsCartier) :
    RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  haveI := hL.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sY f L.divisorialSheaf

private theorem relDeg_congr {L L' : Divisor Y} (h : L = L') (hL : L.IsCartier)
    (hL' : L'.IsCartier) : relDeg sY f L hL = relDeg sY f L' hL' := by
  subst h; rfl

/-- The degree form `z ↦ ∑ⱼ rⱼ (z · 𝒪_Y(Lⱼ))` on `N₁(Y/Z)` of a Cartier presentation. -/
private noncomputable def relForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  ∑ j, r j • relDeg sY f (L j) (hL j)

private theorem relForm_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : RelativeNumericalCurveClasses sY f) :
    relForm sY f r L hL z = ∑ j, r j *
      (haveI := (hL j).isInvertibleModule_divisorialSheaf
       RelativeNumericalCurveClasses.degree sY f (L j).divisorialSheaf z) := by
  simp [relForm, LinearMap.sum_apply, relDeg]

variable {sY f} in
/-- On the class of a contracted curve `ℓ`, the degree form of a presentation is
`∑ⱼ rⱼ deg_ℓ 𝒪_Y(Lⱼ)`. -/
private theorem relForm_relativeClass [QuasiCompact sY] {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier) {ℓ : ProperCurve sY}
    (hℓ : ℓ.IsContractedBy f) :
    relForm sY f r L hL (ℓ.relativeClass f hℓ) =
      ∑ j, r j * ((L j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hL j) : ℝ) := by
  rw [relForm_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  change OneCycle.degree ℝ sY (L j).divisorialSheaf (ℓ.cycle ℝ) = _
  rw [OneCycle.degree_cycle]
  rfl

private theorem continuous_relForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : Continuous (relForm sY f r L hL) := by
  rw [show ⇑(relForm sY f r L hL) = fun z => ∑ j, r j * relDeg sY f (L j) (hL j) z from
    funext fun z => by simp [relForm, LinearMap.sum_apply]]
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  exact RelativeNumericalCurveClasses.continuous_degree sY f _

/-- The form of the presentation `Fin.append (a • r₁) (b • r₂)`, `Fin.append L₁ L₂`. -/
private theorem relForm_append {m₁ m₂ : ℕ} (a b : ℝ) (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor Y)
    (hL₁ : ∀ j, (L₁ j).IsCartier) (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor Y)
    (hL₂ : ∀ j, (L₂ j).IsCartier) (hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier)
    (z : RelativeNumericalCurveClasses sY f) :
    relForm sY f (Fin.append (a • r₁) (b • r₂)) (Fin.append L₁ L₂) hL z =
      a * relForm sY f r₁ L₁ hL₁ z + b * relForm sY f r₂ L₂ hL₂ z := by
  have h₁ : ∀ j, relDeg sY f (Fin.append L₁ L₂ (Fin.castAdd m₂ j)) (hL _) =
      relDeg sY f (L₁ j) (hL₁ j) := fun j => relDeg_congr sY f (Fin.append_left L₁ L₂ j) _ _
  have h₂ : ∀ j, relDeg sY f (Fin.append L₁ L₂ (Fin.natAdd m₁ j)) (hL _) =
      relDeg sY f (L₂ j) (hL₂ j) := fun j => relDeg_congr sY f (Fin.append_right L₁ L₂ j) _ _
  simp only [relForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Fin.sum_univ_add,
    h₁, h₂, Fin.append_left, Fin.append_right, Pi.smul_apply, Finset.mul_sum, mul_assoc]
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]

/-- The degree form `z ↦ ∑ⱼ rⱼ (z · 𝒪_Y(Lⱼ))` on `N₁(Y)` of a Cartier presentation. -/
private noncomputable def absForm {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : NumericalCurveClasses sY →ₗ[ℝ] ℝ :=
  ∑ j, r j • (haveI := (hL j).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sY (L j).divisorialSheaf)

private theorem absForm_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : NumericalCurveClasses sY) :
    absForm sY r L hL z = ∑ j, r j *
      (haveI := (hL j).isInvertibleModule_divisorialSheaf
       NumericalCurveClasses.degree sY (L j).divisorialSheaf z) := by
  simp [absForm, LinearMap.sum_apply]

private theorem absForm_relativeToAbsolute {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (z : RelativeNumericalCurveClasses sY f) :
    absForm sY r L hL (relativeToAbsolute sY f z) = relForm sY f r L hL z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sY f z
  rw [absForm_apply, relForm_apply]
  rfl

variable {sY f} in
/-- On a contracted curve `ℓ`, the value of the degree form of a presentation of `D` at `[ℓ]` is
an intersection number `D · ℓ`. -/
private theorem isRIntersectionNumber_relForm [QuasiCompact sY] {D : RDivisor Y} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor Y) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {ℓ : ProperCurve sY}
    (hℓ : ℓ.IsContractedBy f) :
    IsRIntersectionNumber ℂ sY D r L ℓ (relForm sY f r L hL (ℓ.relativeClass f hℓ)) :=
  ⟨hL, fun j => (L j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hL j), hD,
    fun j => isCartierIntersectionNumber_degreeOn sY ℓ (L j) (hL j),
    relForm_relativeClass r L hL hℓ⟩

variable {sY f} in
/-- The degree form of any presentation of an `f`-nef divisor is nonnegative on `NE̅(Y/Z)`. -/
private theorem relForm_nonneg_of_isRelativelyNef [QuasiCompact sY] {D : RDivisor Y}
    (hnef : IsRelativelyNef ℂ sY f D) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, 0 ≤ relForm sY f r L hL z := by
  obtain ⟨m₀, r₀, L₀, hL₀, hD₀, hnn⟩ := hnef
  have hcurve : ∀ (ℓ : ProperCurve sY) (hℓ : ℓ.IsContractedBy f),
      0 ≤ relForm sY f r L hL (ℓ.relativeClass f hℓ) := by
    intro ℓ hℓ
    have hx := isRIntersectionNumber_relForm r L hL hD hℓ
    have hx₀ := isRIntersectionNumber_relForm r₀ L₀ hL₀ hD₀ hℓ
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sY ℓ).1 _ _ _ _ _ _ _ hx hx₀]
    exact hnn ℓ hℓ _ hx₀
  have hcone : ∀ z ∈ relativeConeOfCurves sY f, 0 ≤ relForm sY f r L hL z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hcurve C hC
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  intro z hz
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal (t := {z | 0 ≤ relForm sY f r L hL z}) hcone
    (isClosed_le continuous_const (continuous_relForm sY f r L hL)) hz

variable {sY f} in
/-- Over a projective base, a curve whose class comes from `N₁(Y/Z)` is contracted. -/
private theorem isContractedBy_of_relativeToAbsolute_eq {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hfc : f ≫ sZ = sY) (ℓ : ProperCurve sY)
    (u : RelativeNumericalCurveClasses sY f)
    (hu : relativeToAbsolute sY f u = OneCycle.numericalClass sY (ℓ.cycle ℝ)) :
    ℓ.IsContractedBy f := by
  obtain ⟨H, hHinv, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj H) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback f.toLRSHom.toShHom _
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfc H hHa ℓ ?_
  obtain ⟨⟨Z₁, hZ₁⟩, rfl⟩ := relativeNumericalClass_surjective sY f u
  have h0 : OneCycle.degree ℝ sY ((Scheme.Modules.pullback f).obj H) Z₁ = 0 := by
    rw [OneCycle.degree_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    dsimp only
    rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hfc C (hZ₁ hC) H]
    simp
  have h1 : ((ℓ.degree ℂ ((Scheme.Modules.pullback f).obj H) : ℤ) : ℝ) = 0 := by
    rw [← OneCycle.degree_cycle ℝ]
    change NumericalCurveClasses.degree sY _ (OneCycle.numericalClass sY (ℓ.cycle ℝ)) = 0
    rw [← hu]
    exact h0
  exact_mod_cast h1

end Forms

/-! ### The nef case -/

section NefCase

/-- A rational map over `T` is over `Z` for the composites with `h : T ⟶ Z`. -/
private theorem isOver_comp {X Y T Z : Scheme.{0}} {g : X ⟶ T} {πY : Y ⟶ T} {h : T ⟶ Z}
    {φ : X.RationalMap Y} (hφ : MMP.Flips.RationalMap.IsOver g πY φ) :
    MMP.Flips.RationalMap.IsOver (g ≫ h) (πY ≫ h) φ := by
  have hcc : ∀ {A B C D : Scheme.{0}} (ψ : A.RationalMap B) (f : B ⟶ C) (f' : C ⟶ D),
      (ψ.compHom f).compHom f' = ψ.compHom (f ≫ f') := fun ψ f f' => by
    obtain ⟨ψ', rfl⟩ := ψ.exists_rep
    rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
      ← Scheme.RationalMap.compHom_toRationalMap]
    rfl
  unfold MMP.Flips.RationalMap.IsOver at hφ ⊢
  rw [← hcc, hφ]
  rfl

/-- **Klt is open on the simplex.** If `(X, B_{μ₀})` is klt, so is `(X, B_μ)` for `μ ∈ Δ` near
`μ₀`. -/
private theorem exists_pos_forall_dist_lt_isRealKltPair
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXq : IsQFactorial sX) {N : ℕ} (v : Fin N → QDivisor X) (hv : ∀ i P, 0 ≤ (v i).coeff P)
    {μ₀ : Fin N → ℝ} (hklt : IsRealKltPair sX (bary v μ₀)) :
    ∃ r > 0, ∀ μ ∈ stdSimplex ℝ (Fin N), dist μ μ₀ < r → IsRealKltPair sX (bary v μ) := by
  classical
  set S : Finset (MMP.Mori.PrimeDivisor X) := Finset.univ.biUnion fun i => (v i).support
  let e := S.equivFin
  let p : Fin S.card → MMP.Mori.PrimeDivisor X := fun k => (e.symm k : MMP.Mori.PrimeDivisor X)
  have hp : Function.Injective p := fun k k' h => e.symm.injective (Subtype.ext h)
  have hsupp : ∀ μ P, (bary v μ).coeff P ≠ 0 → P ∈ Set.range p := fun μ P hP => by
    have hPS : P ∈ S := by
      by_contra hS
      apply hP
      rw [coeff_bary]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : (v i).coeff P = 0 := by
        by_contra h0
        exact hS (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h0⟩)
      rw [this, Rat.cast_zero, mul_zero]
    exact ⟨e ⟨P, hPS⟩, by simp [p]⟩
  let x : (Fin N → ℝ) → Fin S.card → ℝ := fun μ k => (bary v μ).coeff (p k)
  have hx : ∀ μ, bary v μ = ∑ k, Finsupp.single (p k) (x μ k) := fun μ =>
    MMP.Fourfold.eq_sum_single_coeff hp (hsupp μ)
  have hxcont : Continuous x := continuous_pi fun k => by
    simp only [x, coeff_bary]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hev := (MMP.Fourfold.eventually_isRealKltPair_and_isRealTerminalPair sX
    hX.isQuasiProjectiveVariety hXq p (x μ₀)).1 (hx μ₀ ▸ hklt)
  have hmaps : Set.MapsTo x (stdSimplex ℝ (Fin N)) (Set.Ici 0) := fun μ hμ k =>
    bary_nonneg v hv hμ (p k)
  have hev' : ∀ᶠ μ in nhdsWithin μ₀ (stdSimplex ℝ (Fin N)), IsRealKltPair sX (bary v μ) :=
    ((hxcont.continuousWithinAt.tendsto_nhdsWithin hmaps).eventually hev).mono fun μ hμ =>
      (hx μ).symm ▸ hμ
  obtain ⟨r, hr, hr'⟩ := Metric.mem_nhdsWithin_iff.1 hev'
  exact ⟨r, hr, fun μ hμ hd => hr' ⟨Metric.mem_ball.2 hd, hμ⟩⟩

/-- **Bigness over the adjoint contraction.** A `ℚ`-divisor big over `Z` is big over every `T`
through which `X ⟶ Z` factors by a contraction `X ⟶ T`. -/
private theorem isRelativelyBig_of_isContraction
    {X Z T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {g : X ⟶ T} {h : T ⟶ Z} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hπ : π ≫ sZ = sX)
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (hg : IsContraction sX sT g) (hgh : g ≫ h = π) {G : QDivisor X} (hG : ∀ P, 0 ≤ G.coeff P)
    (hGbig : G.IsRelativelyBig π) : G.IsRelativelyBig g := by
  classical
  haveI := hX
  haveI := hZ
  haveI := hT
  obtain ⟨m, hm, D, hD, hDc, hDbig⟩ := hGbig
  obtain ⟨A, hA⟩ := exists_isWeilDivisorOfCartier_of_isCartier hDc
  -- the ranks of `𝒪_X(kD)` and `𝒪_X(kA)` agree
  have hk : ∀ k : ℤ, MMP.Intersection.IsWeilDivisorOfCartier (k • A) (k • D) := fun k P => by
    have := MMP.Intersection.isOrderAlong_primeDivisorOrder (k • A) P
    rwa [map_zsmul, (hA P).primeDivisorOrder_eq, smul_eq_mul,
      show k * D.coeff P = (k • D).coeff P by
        simp [DivisorWithCoeffs.coeff_apply]] at this
  have hrk : ∀ {Y : Scheme.{0}} (f : X ⟶ Y) (k : ℤ),
      relativeGenericRank f (k • D).divisorialSheaf =
        relativeGenericRank f (MMP.CartierDivisor.sheaf (k • A)) := fun f k => by
    obtain ⟨e⟩ := (hk k).nonempty_sheaf_iso_divisorialSheaf
    exact (fiberRank_congr ((Scheme.Modules.pushforward f).mapIso e) _).symm
  have hiff : ∀ {Y : Scheme.{0}} (f : X ⟶ Y),
      D.IsRelativelyBig f ↔ IsRelativelyBigCartier f A := fun f => by
    unfold Divisor.IsRelativelyBig IsRelativelyBigCartier
    simp only [hrk f]
  -- over `Z`: `m' A ∼ A' + E` with `A'` ample over `Z`
  have hqcπ : QuasiCompact π := by
    haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
    haveI : QuasiCompact (π ≫ sZ) := by rw [hπ]; exact hX.toIsVariety.toQuasiCompact
    exact QuasiCompact.of_comp π sZ
  obtain ⟨m', hm', A', E, hA', hE, hlin⟩ :=
    (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sX sZ π hπ A).1
      ((hiff π).1 hDbig)
  -- `A'` is ample over `T`
  haveI := isProper_of_isProjectiveMorphism g hg.isProjectiveMorphism
  have hA'g : IsRelativelyAmple g (MMP.CartierDivisor.sheaf A') := by
    have h1 := MMP.Mori.IsRelativelyAmple.to_stacks (f := π) hA'
    rw [← hgh] at h1
    exact MMP.Mori.IsRelativelyAmple.of_stacks g _
      (Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp g h _ h1 inferInstance)
  have hbigg := (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sX sT g
    hg.comp_eq A).2 ⟨m', hm', A', E, hA'g, hE, hlin⟩
  exact ⟨m, hm, D, hD, hDc, (hiff g).2 hbigg⟩

/-- **An `ℝ`-Cartier form of a pull-back adjoint.** If `K_X + B₀ ∼_ℝ g^* H`, some `ℝ`-Cartier
divisor with Weil divisor `K_X + B₀` has class zero in `N¹(X/T)`. -/
private theorem exists_weil_eq_relativeNumericalDivisorClass_eq_zero
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sT : T ⟶ Spec (.of ℂ)}
    {g : X ⟶ T} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hg : IsContraction sX sT g) {KX : Divisor X} {B₀ : RDivisor X} {H : RDivisor T}
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i))) :
    ∃ D₀ : KCartierDivisor ℝ X, weil D₀ = (fun P => (logCanonicalDivisor KX B₀).coeff P) ∧
      MMP.Fourfold.relativeNumericalDivisorClass sX g D₀ = 0 := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  have hTn := hg.isNormalVariety_target
  haveI : IsSeparated sT := hTn.1.toIsSeparated
  haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sT := hTn.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  -- an `ℝ`-Cartier presentation of `K_X + B₀` by Cartier divisors of `X`
  obtain ⟨m, r, L, hL, hcoeff⟩ := hXq.isRCartier (logCanonicalDivisor KX B₀)
  choose A hA using fun i => exists_isWeilDivisorOfCartier_of_isCartier (hL i)
  have hLsum : logCanonicalDivisor KX B₀ = ∑ i, r i • Divisor.toRDivisor (L i) := by
    refine Finsupp.ext fun P => ?_
    have := hcoeff P
    rw [DivisorWithCoeffs.coeff_apply] at this
    rw [this, Finsupp.finset_sum_apply]
    rfl
  refine ⟨∑ i, Finsupp.single (A i) (r i), ?_, ?_⟩
  · funext P
    rw [map_sum, Finset.sum_apply, hcoeff P]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weil_apply, Finsupp.sum_single_index (by simp), (hA i P).primeDivisorOrder_eq]
  rw [MMP.Fourfold.relativeNumericalDivisorClass, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker]
  funext C
  have hdeg : ∀ i, C.1.degree ℂ (MMP.CartierDivisor.sheaf (A i)) =
      (L i).degreeOn ℂ sX C.1.ι C.1.dim_le (hL i) := fun i => by
    obtain ⟨e⟩ := (hA i).nonempty_sheaf_iso_divisorialSheaf
    haveI := (hL i).isInvertibleModule_divisorialSheaf
    rw [← ProperCurve.degree_divisorialSheaf]
    unfold ProperCurve.degree
    exact degreeOn_eq_of_iso ℂ sX C.1.ι C.1.dim_le e
  have hval : MMP.Fourfold.relativeDegreeMap sX g (∑ i, Finsupp.single (A i) (r i)) C =
      ∑ i, r i * ((L i).degreeOn ℂ sX C.1.ι C.1.dim_le (hL i) : ℝ) := by
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hdeg]
    simp [MMP.Fourfold.relativeDegreeMap, OneCycle.intersectionPairing,
      Finsupp.linearCombination_single, OneCycle.cartierDegree, OneCycle.degree_apply,
      ProperCurve.cycle]
  rw [hval, Pi.zero_apply]
  -- the same intersection number from `K_X + B₀ = g^* H + ∑ sₖ div φₖ` is zero
  obtain ⟨gH, ⟨m', r', L₁, L₁', hL₁, hH, hpb, hgH⟩, m'', s, φ, hsum⟩ := hpull
  choose hB₁ hpb₁ using hpb
  have hL₁' : ∀ j, (L₁' j).IsCartier := fun j => by
    rw [← (hpb₁ j).pullback_eq (hL₁ j)]
    exact (hL₁ j).isCartier_pullback g (hB₁ j)
  have h0 : ∀ j, (L₁' j).degreeOn ℂ sX C.1.ι C.1.dim_le (hL₁' j) = 0 := fun j => by
    have := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy g hg.comp_eq (hL₁ j) (hB₁ j)
      C.1 C.2
    convert this using 2
    exact ((hpb₁ j).pullback_eq (hL₁ j)).symm
  have hP0 : ∀ k, (principalDivisor (φ k)).degreeOn ℂ sX C.1.ι C.1.dim_le
      (Divisor.isCartier_principalDivisor (φ k)) = 0 := fun k =>
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent _ _ _ _ ⟨φ k, by rw [sub_zero]⟩
  have hI₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 r' L₁' hL₁'
  have hI₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 s
    (fun k => principalDivisor (φ k)) fun k => Divisor.isCartier_principalDivisor (φ k)
  have hI := (IsRIntersectionNumber.eq_and_linear ℂ sX C.1).2 _ _ _ _ _ _ _ _ 1 1 hI₁ hI₂
  have hKB : (1 : ℝ) • (∑ j, r' j • Divisor.toRDivisor (L₁' j)) +
      (1 : ℝ) • (∑ k, s k • Divisor.toRDivisor (principalDivisor (φ k))) =
      logCanonicalDivisor KX B₀ := by
    rw [one_smul, one_smul, ← hgH, ← hsum]; abel
  rw [hKB] at hI
  have := (IsRIntersectionNumber.eq_and_linear ℂ sX C.1).1 _ _ _ _ _ _ _ hI
    (hLsum ▸ MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 r L hL)
  rw [← this]
  simp [h0, hP0]

/-- **Pseudo-effectivity along the ray.** If `K_X + B₀ ∼_ℝ g^* H` and
`K_X + ((1 - t) B₀ + t B'')` is pseudo-effective over `Z` with `t > 0`, then `K_X + B''` is
pseudo-effective over `T`: `K_X + B₀` is numerically trivial over `T`, and curves contracted by
`g` are contracted by `π`. -/
private theorem isPsef_of_isPsef_lineMap
    {X Z T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sT : T ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {g : X ⟶ T} {h : T ⟶ Z} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    (hg : IsContraction sX sT g) (hgh : g ≫ h = π) {KX : Divisor X} {B₀ : RDivisor X}
    {H : RDivisor T}
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    {t : ℝ} (ht : 0 < t) {B'' : RDivisor X}
    (hps : IsPsef sX π KX ((1 - t) • B₀ + t • B'')) : IsPsef sX g KX B'' := by
  obtain ⟨D₀, hD₀w, hD₀0⟩ := exists_weil_eq_relativeNumericalDivisorClass_eq_zero hX hXq hg hpull
  obtain ⟨D', hD'w, hD'ps⟩ := (isPsef_iff _).1 hps
  rw [← hgh] at hD'ps
  have hD'g := isRelativelyPseudoEffective_of_comp hD'ps
  refine (isPsef_iff _).2 ⟨t⁻¹ • (D' - (1 - t) • D₀), ?_, ?_⟩
  · rw [map_smul, map_sub, map_smul, hD'w, hD₀w]
    funext P
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, logCanonicalDivisor,
      DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.smul_apply]
    field_simp
    ring
  · rw [map_smul, map_sub, map_smul, hD₀0, smul_zero, sub_zero]
    exact smul_mem_closure_relativeEffectiveCone (inv_nonneg.2 ht.le) hD'g

/-- Pull-backs of `ℝ`-Cartier divisors are linear. -/
private theorem isRCartierPullback_smul_add_smul {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X}
    {D₁ D₂ : RDivisor X} {G₁ G₂ : RDivisor Y} (h₁ : MMP.Flips.IsRCartierPullback f D₁ G₁)
    (h₂ : MMP.Flips.IsRCartierPullback f D₂ G₂) (a b : ℝ) :
    MMP.Flips.IsRCartierPullback f (a • D₁ + b • D₂) (a • G₁ + b • G₂) := by
  obtain ⟨m, r, L, L', hL, hD, hpb, hG⟩ := h₁
  obtain ⟨m', r', M, M', hM, hD', hpb', hG'⟩ := h₂
  refine ⟨m + m', Fin.append (a • r) (b • r'), Fin.append L M, Fin.append L' M',
    fun j => Fin.addCases (motive := fun j => (Fin.append L M j).IsCartier)
      (fun i => by simpa using hL i) (fun i => by simpa using hM i) j, ?_,
    fun j => Fin.addCases (motive := fun j => ∃ hB : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (Fin.append L M j).supp,
        (Fin.append L M j).IsPullback f hB (Fin.append L' M' j))
      (fun i => by simpa using hpb i) (fun i => by simpa using hpb' i) j, ?_⟩
  · simp [Fin.sum_univ_add, hD, hD', Finset.smul_sum, smul_smul]
  · simp [Fin.sum_univ_add, hG, hG', Finset.smul_sum, smul_smul]

/-- **A pulled-back adjoint is numerically trivial over the base.** If `K_X + B₀ ∼_ℝ g^* H`,
every intersection number of `c (K_X + B₀)` with a curve contracted by `g` is zero. -/
private theorem isRIntersectionNumber_eq_zero_of_pull
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sT : T ⟶ Spec (.of ℂ)}
    {g : X ⟶ T} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hXq : IsQFactorial sX) (hg : IsContraction sX sT g) {KX : Divisor X} {B₀ : RDivisor X}
    {H : RDivisor T}
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (c : ℝ) (C : ProperCurve sX) (hC : C.IsContractedBy g) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX (c • logCanonicalDivisor KX B₀) r L C x) : x = 0 := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  have hTn := hg.isNormalVariety_target
  haveI : IsSeparated sT := hTn.1.toIsSeparated
  haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sT := hTn.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨gH, ⟨m', r', L₁, L₁', hL₁, hH, hpb, hgH⟩, m'', s, φ, hsum⟩ := hpull
  choose hB₁ hpb₁ using hpb
  have hL₁' : ∀ j, (L₁' j).IsCartier := fun j => by
    rw [← (hpb₁ j).pullback_eq (hL₁ j)]
    exact (hL₁ j).isCartier_pullback g (hB₁ j)
  have h0 : ∀ j, (L₁' j).degreeOn ℂ sX C.ι C.dim_le (hL₁' j) = 0 := fun j => by
    have := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy g hg.comp_eq (hL₁ j) (hB₁ j) C hC
    convert this using 2
    exact ((hpb₁ j).pullback_eq (hL₁ j)).symm
  have hP0 : ∀ k, (principalDivisor (φ k)).degreeOn ℂ sX C.ι C.dim_le
      (Divisor.isCartier_principalDivisor (φ k)) = 0 := fun k =>
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent _ _ _ _ ⟨φ k, by rw [sub_zero]⟩
  have hI₁ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r' L₁' hL₁'
  have hI₂ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C s
    (fun k => principalDivisor (φ k)) fun k => Divisor.isCartier_principalDivisor (φ k)
  have hI := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 _ _ _ _ _ _ _ _ c c hI₁ hI₂
  have hKB : c • (∑ j, r' j • Divisor.toRDivisor (L₁' j)) +
      c • (∑ k, s k • Divisor.toRDivisor (principalDivisor (φ k))) =
      c • logCanonicalDivisor KX B₀ := by
    rw [← smul_add, ← hgH, ← hsum]; congr 1; abel
  rw [hKB] at hI
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hI]
  simp [h0, hP0]

/-- A pulled-back adjoint and its multiples are nef over the base. -/
private theorem isRelativelyNef_smul_of_pull
    {X T : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sT : T ⟶ Spec (.of ℂ)}
    {g : X ⟶ T} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (hXq : IsQFactorial sX) (hg : IsContraction sX sT g) {KX : Divisor X} {B₀ : RDivisor X}
    {H : RDivisor T}
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (c : ℝ) : MMP.Flips.IsRelativelyNef ℂ sX g (c • logCanonicalDivisor KX B₀) := by
  obtain ⟨m, r, L, hL, hcoeff⟩ := hXq.isRCartier (c • logCanonicalDivisor KX B₀)
  refine ⟨m, r, L, hL, Finsupp.ext fun P => ?_, fun C hC x hx => ?_⟩
  · have := hcoeff P
    rw [DivisorWithCoeffs.coeff_apply] at this
    rw [this, Finsupp.finset_sum_apply]
    rfl
  · rw [isRIntersectionNumber_eq_zero_of_pull hXq hg hpull c C hC hx]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is a combination of Cartier divisors. -/
private theorem isCartierCombination_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hXq : IsQFactorial sX)
    (D : RDivisor X) : MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hcoeff⟩ := hXq.isRCartier D
  refine ⟨m, r, L, hL, Finsupp.ext fun P => ?_⟩
  have := hcoeff P
  rw [DivisorWithCoeffs.coeff_apply] at this
  rw [this, Finsupp.finset_sum_apply]
  rfl

/-- The coefficient of an `ℝ`-Cartier pull-back at a prime divisor over which the morphism is a
local isomorphism is the coefficient downstairs. -/
private theorem coeff_eq_of_isRCartierPullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {D : RDivisor Y} {G : RDivisor X} (h : MMP.Flips.IsRCartierPullback f D G)
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = P.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    G E = D P := by
  obtain ⟨m, r, L, L', hL, hD, hpb, hG⟩ := h
  subst hD hG
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hB, hp⟩ := hpb j
  have := MMP.Positivity.coeff_eq_of_isPullback E P heq (hL j) hp
  simp only [DivisorWithCoeffs.coeff_apply] at this
  show r j * (((L' j) E : ℤ) : ℝ) = r j * (((L j) P : ℤ) : ℝ)
  rw [this]

/-- **The central comparison vanishes.** On a common resolution of a model `φ : X ⤏ Y` over `T`,
the pull-backs of `K_X + B₀ ∼_ℝ g^* H` and of its strict transform `K_Y + φ_* B₀ ∼_ℝ π_Y^* H`
coincide. -/
private theorem exists_isRCartierPullback_eq_of_isOver
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    {p : W ⟶ X} {q : W ⟶ Y} {hh : X.RationalMap W} {B'' : RDivisor X} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B'' KY
      (MMP.Mori.RationalMap.transformDivisor φ B'') p q hh GX GY) :
    ∃ GX₀ GY₀ : RDivisor W, MMP.Flips.IsRCartierPullback p (logCanonicalDivisor KX B₀) GX₀ ∧
      MMP.Flips.IsRCartierPullback q
        (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀)) GY₀ ∧
      GX₀ = GY₀ := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have := hXn.1
  have := hYn.1
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have hTn := hg.isNormalVariety_target
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hTn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have hWv := hR.isVariety
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWn : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  have hWp' : IsNormalVariety ℂ (p ≫ sX) := by rw [hR.comp_eq_left]; exact hWn
  have hWq' : IsNormalVariety ℂ (q ≫ sY) := by rw [hR.comp_eq_right]; exact hWn
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hWn
  haveI : IsSeparated p := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  haveI : IsSeparated q := IsSeparated.of_comp q (Y ↘ ⊤_ Scheme)
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hWproj : MMP.Mori.IsProjectiveVariety ℂ sW := by
    rw [← hR.comp_eq_left]
    exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr
      ⟨hWp'.1, IsProjectiveMorphism.comp hR.isProjectiveMorphism_left hX.2⟩
  have hpq : p ≫ g = q ≫ πY := comp_eq_comp_of_isOver g πY hφT p q hh hR.isInverse hR.compHom_eq
  obtain ⟨nW, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hKY : KY = MMP.Mori.RationalMap.transformDivisor φ KX := by
    rw [← hKWY, ← hKWX, ← hR.compHom_eq, transformDivisor_compHom_transformDivisor hXn hYn hWp'
      hpb hqb hR.isInverse (hR.compHom_eq ▸ hφe) KW]
  have hDX := isCartierCombination_of_isQFactorial hXq (logCanonicalDivisor KX B₀)
  have hDY := isCartierCombination_of_isQFactorial hYq
    (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀))
  obtain ⟨GX₀, hGX₀, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hDX
  obtain ⟨GY₀, hGY₀, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hDY
  refine ⟨GX₀, GY₀, hGX₀, hGY₀, ?_⟩
  -- at the strict transform on `W` of every prime divisor of `Y`, the pull-backs agree
  have hkey : ∀ F : MMP.Mori.PrimeDivisor Y,
      MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap (GY₀ - GX₀) F = 0 := by
    intro F
    obtain ⟨F', hF', hisoF, htrF⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hWq' hqb F
    rw [htrF]
    obtain ⟨P, hP⟩ : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F := by
      by_contra hne
      push Not at hne
      exact hφe F hne
    obtain ⟨P', hP', hisoP, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWp' hpb P
    have hhP := transformPrimeDivisor_eq_some_of_isInverse hpbij hR.isInverse hP'
    have hqP' : MMP.Mori.RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P' =
        some F := by
      rw [← transformPrimeDivisor_compHom hhP q, hR.compHom_eq, hP]
    have hPF : P' = F' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_genericPoint q hqbij
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P' F).1 hqP') hF')
    subst hPF
    haveI := hisoF
    haveI := hisoP
    have hcY := coeff_eq_of_isRCartierPullback hGY₀ P' F hF'
    have hcX := coeff_eq_of_isRCartierPullback hGX₀ P' P hP'
    -- the strict transform along `φ` reads off the coefficient at `P`
    have huniq : ∀ P₁ : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor φ P₁ = some F → P₁ = P := fun P₁ hP₁ => by
      obtain ⟨P₁', hP₁', -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWp' hpb P₁
      have hhP₁ := transformPrimeDivisor_eq_some_of_isInverse hpbij hR.isInverse hP₁'
      have hq₁ : MMP.Mori.RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P₁' =
          some F := by
        rw [← transformPrimeDivisor_compHom hhP₁ q, hR.compHom_eq, hP₁]
      have h₁ : P₁' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_genericPoint q hqbij
          ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P₁' F).1 hq₁) hF')
      subst h₁
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP₁'.symm.trans hP')
    have htrφ : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ D F = D P := fun D => by
      rw [transformDivisor_apply, Finsupp.sum]
      by_cases hPs : P ∈ D.support
      · rw [Finset.sum_eq_single P (fun P₁ _ hne => if_neg fun h => hne (huniq P₁ h))
          (fun h => absurd hPs h), if_pos hP]
      · rw [Finset.sum_eq_zero fun P₁ hP₁ => by
          rw [if_neg]; exact fun h => hPs (huniq P₁ h ▸ hP₁)]
        exact (Finsupp.notMem_support_iff.mp hPs).symm
    rw [Finsupp.sub_apply, hcY, hcX]
    simp only [logCanonicalDivisor, Finsupp.add_apply]
    rw [hKY]
    change ((MMP.Mori.RationalMap.transformDivisor φ KX F : ℤ) : ℝ) +
      MMP.Mori.RationalMap.transformDivisor φ B₀ F - ((KX P : ℤ) + B₀ P) = 0
    rw [htrφ, htrφ]
    ring
  -- the two comparisons
  have hnef₁ := isRelativelyNef_smul_of_pull hXq hg hpull 1
  have hnef₂ := isRelativelyNef_smul_of_pull hXq hg hpull (-1)
  rw [one_smul] at hnef₁
  have h₁ := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (k := ℂ) sW sY sX hWn hWproj
    hYn hY hXn hX πY g q p hR.comp_eq_right hR.comp_eq_left hpq.symm
    hR.isProjectiveMorphism_right hqb hR.isProjectiveMorphism_left hpb hDY hnef₁ hGY₀ hGX₀
    (fun F => (hkey F).ge)
  have hGY₀' : MMP.Flips.IsRCartierPullback q
      ((-1 : ℝ) • logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀))
      ((-1 : ℝ) • GY₀) := by
    simpa using isRCartierPullback_smul_add_smul hGY₀ hGY₀ (-1) 0
  have hGX₀' : MMP.Flips.IsRCartierPullback p ((-1 : ℝ) • logCanonicalDivisor KX B₀)
      ((-1 : ℝ) • GX₀) := by
    simpa using isRCartierPullback_smul_add_smul hGX₀ hGX₀ (-1) 0
  have h₂ := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (k := ℂ) sW sY sX hWn hWproj
    hYn hY hXn hX πY g q p hR.comp_eq_right hR.comp_eq_left hpq.symm
    hR.isProjectiveMorphism_right hqb hR.isProjectiveMorphism_left hpb
    (isCartierCombination_of_isQFactorial hYq _) hnef₂ hGY₀' hGX₀' (fun F => by
      have := hkey F
      rw [map_sub, Finsupp.sub_apply] at this
      rw [← smul_sub, ← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_smul,
        MMP.Mori.RationalMap.transformDivisorₗ_apply, map_sub]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, Finsupp.coe_zero,
        Pi.zero_apply]
      linarith)
  refine Finsupp.ext fun P => le_antisymm ?_ ?_
  · have := h₁ P
    simp only [Finsupp.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    linarith
  · have := h₂ P
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at this
    linarith

/-- **The central pair stays klt on a model over `T`.** It is crepant to `(X, B₀)`. -/
private theorem isRealKltPair_transformDivisor_of_isOver
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {B'' : RDivisor X}
    (hmod : IsRealLogMinimalModel sX sY sT g πY KX B'' KY
      (MMP.Mori.RationalMap.transformDivisor φ B'') φ) :
    IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B₀) := by
  classical
  obtain ⟨W, _, _, _, sW, p, q, hh, GX, GY, hR⟩ := hmod.exists_resolution
  obtain ⟨GX₀, GY₀, hGX₀, hGY₀, hG₀⟩ := exists_isRCartierPullback_eq_of_isOver hX hZ hπ hdim
    hXq hKX hB₀ hklt hnef hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hR
  have hR₀ : IsLogComparisonResolution sX sY sW φ KX B₀ KY
      (MMP.Mori.RationalMap.transformDivisor φ B₀) p q hh GX₀ GY₀ :=
    { hR with
      isRCartierPullback_left := hGX₀
      isRCartierPullback_right := hGY₀
      effective := fun P => by rw [hG₀, sub_self]; exact le_rfl
      isExceptional := fun P hP => absurd (by rw [hG₀, sub_self]; rfl) hP }
  have hXn : IsNormalVariety ℂ sX := hklt.1
  have hYn := hmod.isNormalVariety_model
  obtain ⟨n, hn⟩ := hKX
  obtain ⟨nY, hnY⟩ := hmod.isCanonicalDivisor_model
  have hpos := isLogDiscrepancy_pos_of_isLogComparisonResolution hR₀ hXn hYn hn hnY hklt.2.2.2
  have hRCY : RDivisor.IsRCartier
      (Divisor.toRDivisor KY + MMP.Mori.RationalMap.transformDivisor φ B₀) := by
    obtain ⟨m, r, L, -, hLc, hD, -, -⟩ := hR₀.isRCartierPullback_right
    refine ⟨m, r, L, hLc, fun Γ => ?_⟩
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← hD]
    rfl
  refine ⟨hYn, fun F => ?_, ⟨nY, KY, hnY, hRCY⟩, hpos⟩
  have := hpos nY _ _ (isLogDiscrepancy_ofPrimeDivisor_real hYn hnY hRCY F)
  linarith

/-- **The transformed central adjoint is nef over `Z`.** Its pull-back to a common resolution
is that of `K_X + B₀`, which is nef over `Z`. -/
private theorem isRelativelyNef_transformDivisor_of_isOver
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    {p : W ⟶ X} {q : W ⟶ Y} {hh : X.RationalMap W} {B'' : RDivisor X} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B'' KY
      (MMP.Mori.RationalMap.transformDivisor φ B'') p q hh GX GY) :
    MMP.Flips.IsRelativelyNef ℂ sY (πY ≫ h)
      (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀)) := by
  classical
  obtain ⟨GX₀, GY₀, hGX₀, hGY₀, hG₀⟩ := exists_isRCartierPullback_eq_of_isOver hX hZ hπ hdim
    hXq hKX hB₀ hklt hnef hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hR
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have := hXn.1
  have := hYn.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  have hTn := hg.isNormalVariety_target
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hTn
  have hWv := hR.isVariety
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  haveI : IsDominant q := hR.isBirationalMorphism_right.isDominant
  haveI : Surjective q := surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  have hpq : p ≫ g = q ≫ πY := comp_eq_comp_of_isOver g πY hφT p q hh hR.isInverse hR.compHom_eq
  have hps : p ≫ sX = sW := hR.comp_eq_left
  have hqs : q ≫ sY = sW := hR.comp_eq_right
  subst hps
  haveI : QuasiCompact (q ≫ sY) := by rw [hqs]; infer_instance
  have h1 := isRelativelyNef_of_isRCartierPullback (k := ℂ) (𝟙 Z) π (p ≫ π) p
    (by rw [Category.comp_id]) hnef hGX₀
  have hpq' : p ≫ π = q ≫ (πY ≫ h) := by rw [← hgh, ← Category.assoc, hpq, Category.assoc]
  rw [hpq', hG₀] at h1
  exact IsRelativelyNef.of_isRCartierPullback_of_surjective (k := ℂ) q hqs (πY ≫ h) hGY₀ h1

/-- **Curves of degree zero lie over `T`.** A curve on the model, contracted over `Z`, on which the
transformed central adjoint has degree zero, is contracted over `T`: lift it to the common
resolution and push it down to `X`, where degree zero means being contracted by `g`. -/
private theorem isContractedBy_of_isRIntersectionNumber_eq_zero
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (hcrit : ∀ C : ProperCurve sX, C.IsContractedBy π → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX (logCanonicalDivisor KX B₀) r L C x →
        (x = 0 ↔ C.IsContractedBy g))
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    {p : W ⟶ X} {q : W ⟶ Y} {hh : X.RationalMap W} {B'' : RDivisor X} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B'' KY
      (MMP.Mori.RationalMap.transformDivisor φ B'') p q hh GX GY)
    (ℓ : ProperCurve sY) (hℓ : ℓ.IsContractedBy (πY ≫ h)) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor Y}
    (hx : MMP.Flips.IsRIntersectionNumber ℂ sY
      (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀)) r L ℓ 0) :
    ℓ.IsContractedBy πY := by
  classical
  obtain ⟨GX₀, GY₀, hGX₀, hGY₀, hG₀⟩ := exists_isRCartierPullback_eq_of_isOver hX hZ hπ hdim
    hXq hKX hB₀ hklt hnef hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hR
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have := hXn.1
  have := hYn.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  have hTn := hg.isNormalVariety_target
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hTn
  have hWv := hR.isVariety
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  haveI : IsDominant q := hR.isBirationalMorphism_right.isDominant
  haveI : Surjective q := surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  have hpq : p ≫ g = q ≫ πY := comp_eq_comp_of_isOver g πY hφT p q hh hR.isInverse hR.compHom_eq
  have hps : p ≫ sX = sW := hR.comp_eq_left
  have hqs : q ≫ sY = sW := hR.comp_eq_right
  subst hps
  haveI : QuasiCompact (q ≫ sY) := by rw [hqs]; infer_instance
  haveI : CompactSpace X := inferInstance
  by_contra hnc
  -- a curve of `W` over `ℓ`
  obtain ⟨C', hC', -⟩ := exists_properCurve_map_eq (k := ℂ) (p ≫ sX) sY q hqs ℓ
  have hclq : ∀ w ∈ closure ({C'.point} : Set W), q w ∈ closure ({ℓ.point} : Set Y) :=
    fun w hw => map_mem_closure q.continuous hw (by
      rintro _ rfl; exact hC')
  have hpq' : p ≫ π = q ≫ (πY ≫ h) := by rw [← hgh, ← Category.assoc, hpq, Category.assoc]
  have hcp : C'.IsContractedBy (p ≫ π) := fun w hw => by
    have h1 := hℓ _ (hclq w hw)
    rw [hpq']
    simp only [Scheme.Hom.comp_apply] at h1 ⊢
    rw [h1, hC']
  have hncq : ¬ C'.IsContractedBy (q ≫ πY) := fun hc => hnc fun y hy => by
    have himg : closure ({ℓ.point} : Set Y) = q '' closure ({C'.point} : Set W) := by
      rw [← q.isClosedMap.closure_image_eq_of_continuous q.continuous, Set.image_singleton, hC']
    rw [himg] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have := hc w hw
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hC']
  have hncp : ¬ C'.IsContractedBy p := fun hc => hncq fun w hw => by
    rw [← hpq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hc w hw]
  set C : ProperCurve sX := ⟨p C'.point, isProperCurve_map p rfl C' hncp⟩
  have hCimg : closure ({C.point} : Set X) = p '' closure ({C'.point} : Set W) := by
    rw [← p.isClosedMap.closure_image_eq_of_continuous p.continuous, Set.image_singleton]
  have hCπ : C.IsContractedBy π := fun x hx => by
    rw [hCimg] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have := hcp w hw
    simpa only [Scheme.Hom.comp_apply] using this
  have hCg : ¬ C.IsContractedBy g := fun hc => hncq fun w hw => by
    have hmem : p w ∈ closure ({C.point} : Set X) := by rw [hCimg]; exact ⟨w, hw, rfl⟩
    rw [← hpq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hc _ hmem]
  -- the degree of `K_X + B₀` along `C` is positive
  obtain ⟨mX, rX, LX, LX', hLX, hDX, hpbX, hGXeq⟩ := hGX₀
  choose hBX hpbXj using hpbX
  have hLXp : ∀ j, LX' j = (LX j).pullback (hLX j) (hBX j) := fun j =>
    ((hpbXj j).pullback_eq (hLX j)).symm
  have hLX' : ∀ j, (LX' j).IsCartier := fun j => by
    rw [hLXp]; exact (hLX j).isCartier_pullback p (hBX j)
  have hxC := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C rX LX hLX
  rw [← hDX] at hxC
  obtain ⟨m0, r0, L0, hL0, hD0, hnn⟩ := hnef
  have hx0 := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C r0 L0 hL0
  rw [← hD0] at hx0
  have hvC0 : 0 ≤ ∑ j, rX j * ((LX j).degreeOn ℂ sX C.ι C.dim_le (hLX j) : ℝ) := by
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hxC hx0]
    exact hnn C hCπ _ hx0
  have hvCne : ∑ j, rX j * ((LX j).degreeOn ℂ sX C.ι C.dim_le (hLX j) : ℝ) ≠ 0 :=
    fun h0 => hCg ((hcrit C hCπ _ _ _ _ hxC).1 h0)
  have hvC : 0 < ∑ j, rX j * ((LX j).degreeOn ℂ sX C.ι C.dim_le (hLX j) : ℝ) :=
    lt_of_le_of_ne hvC0 (Ne.symm hvCne)
  -- the degree of the pull-back along `C'`, from `X`
  have hxX := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (p ≫ sX) C' rX LX' hLX'
  rw [← hGXeq] at hxX
  have hvX : ∑ j, rX j * ((LX' j).degreeOn ℂ (p ≫ sX) C'.ι C'.dim_le (hLX' j) : ℝ) =
      (residueFieldDegree p C'.point : ℝ) *
        ∑ j, rX j * ((LX j).degreeOn ℂ sX C.ι C.dim_le (hLX j) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e := degreeOn_pullback_eq_mul' (k := ℂ) p rfl (hLX j) (hBX j) C' C rfl
    have e' : (LX' j).degreeOn ℂ (p ≫ sX) C'.ι C'.dim_le (hLX' j) =
        (residueFieldDegree p C'.point : ℤ) * (LX j).degreeOn ℂ sX C.ι C.dim_le (hLX j) := by
      convert e using 2 <;> simp [hLXp]
    rw [e']
    push_cast
    ring
  -- the degree of the pull-back along `C'`, from `Y`
  obtain ⟨mY, rY, LY, LY', hLY, hDY, hpbY, hGYeq⟩ := hGY₀
  choose hBY hpbYj using hpbY
  have hLYp : ∀ j, LY' j = (LY j).pullback (hLY j) (hBY j) := fun j =>
    ((hpbYj j).pullback_eq (hLY j)).symm
  have hLY' : ∀ j, (LY' j).IsCartier := fun j => by
    rw [hLYp]; exact (hLY j).isCartier_pullback q (hBY j)
  have hxY := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ (p ≫ sX) C' rY LY' hLY'
  rw [← hGYeq, ← hG₀] at hxY
  have hxℓ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sY ℓ rY LY hLY
  rw [← hDY] at hxℓ
  have hvℓ := (IsRIntersectionNumber.eq_and_linear ℂ sY ℓ).1 _ _ _ _ _ _ _ hxℓ hx
  have hvY : ∑ j, rY j * ((LY' j).degreeOn ℂ (p ≫ sX) C'.ι C'.dim_le (hLY' j) : ℝ) = 0 := by
    have : ∑ j, rY j * ((LY' j).degreeOn ℂ (p ≫ sX) C'.ι C'.dim_le (hLY' j) : ℝ) =
        (residueFieldDegree q C'.point : ℝ) *
          ∑ j, rY j * ((LY j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hLY j) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e := degreeOn_pullback_eq_mul' (k := ℂ) q hqs (hLY j) (hBY j) C' ℓ hC'.symm
      have e' : (LY' j).degreeOn ℂ (p ≫ sX) C'.ι C'.dim_le (hLY' j) =
          (residueFieldDegree q C'.point : ℤ) * (LY j).degreeOn ℂ sY ℓ.ι ℓ.dim_le (hLY j) := by
        convert e using 2 <;> simp [hLYp]
      rw [e']
      push_cast
      ring
    rw [this, hvℓ, mul_zero]
  have heq := (IsRIntersectionNumber.eq_and_linear ℂ (p ≫ sX) C').1 _ _ _ _ _ _ _ hxX hxY
  rw [hvX, hvY] at heq
  have hdp : (0 : ℝ) < residueFieldDegree p C'.point := by
    exact_mod_cast residueFieldDegree_pos_of_not_isContractedBy p rfl C' hncp
  have := mul_pos hdp hvC
  linarith

/-- **Nefness over `Z` along the ray.** By the radial-ray lemma, for small `t > 0` every extremal
ray over `Z` negative for the transformed adjoint of `(1 - t) B₀ + t B''` is
`K_Y + φ_* B₀`-trivial, hence lies over `T`, where that adjoint is nef as a combination of a
trivial and a nef divisor; so there is no negative ray and the adjoint is nef over `Z`. -/
private theorem exists_pos_isRelativelyNef_lineMap
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (G : QDivisor X) (hG0 : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGB : ∀ P, (G.coeff P : ℝ) ≤ B₀.coeff P)
    (hcrit : ∀ C : ProperCurve sX, C.IsContractedBy π → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX (logCanonicalDivisor KX B₀) r L C x →
        (x = 0 ↔ C.IsContractedBy g)) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → ∀ B'' : RDivisor X, (∀ P, 0 ≤ B''.coeff P) →
      IsRealKltPair sX B'' →
      IsRealLogMinimalModel sX sY sT g πY KX B'' KY
        (MMP.Mori.RationalMap.transformDivisor φ B'') φ →
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B'') →
      MMP.Flips.IsRelativelyNef ℂ sY (πY ≫ h)
        (logCanonicalDivisor KY
          (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B''))) := by
  classical
  by_cases hex : ∃ B₁ : RDivisor X, IsRealLogMinimalModel sX sY sT g πY KX B₁ KY
      (MMP.Mori.RationalMap.transformDivisor φ B₁) φ
  swap
  · exact ⟨1, one_pos, fun t _ _ B'' _ _ hmod _ => absurd ⟨B'', hmod⟩ hex⟩
  obtain ⟨B₁, hmod₁⟩ := hex
  obtain ⟨W, _, _, _, sW, p, q, hh, GX, GY, hR⟩ := hmod₁.exists_resolution
  have hnefY := isRelativelyNef_transformDivisor_of_isOver hX hZ hπ hdim hXq hKX hB₀ hklt hnef
    hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hR
  have hY0klt := isRealKltPair_transformDivisor_of_isOver hX hZ hπ hdim hXq hKX hB₀ hklt hnef
    hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hmod₁
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hY
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  -- `Y` is a threefold
  have hdimY : topologicalKrullDim Y = 3 := by
    haveI := hX.toIsVariety
    haveI := hY.toIsVariety
    haveI := hR.isVariety
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY sW
      hR.isBirationalMorphism_right,
      ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW
        hR.isBirationalMorphism_left, hdim]
  obtain ⟨nY, hnY⟩ := hmod₁.isCanonicalDivisor_model
  have hnY3 : KY.IsCanonicalDivisor sY 3 := by
    have h3 : (nY : WithBot ℕ∞) = 3 := hnY.topologicalKrullDim_eq.symm.trans hdimY
    have : nY = 3 := by exact_mod_cast h3
    exact this ▸ hnY
  -- the base `Z` of the model
  set f := πY ≫ h with hfdef
  have hhZ : h ≫ sZ = sT := by
    haveI : IsDominant g := ⟨hg.surjective.denseRange⟩
    refine ext_of_isDominant (ι := g) ?_
    rw [← Category.assoc, hgh, hπ, hg.comp_eq]
  have hf : f ≫ sZ = sY := by rw [hfdef, Category.assoc, hhZ, hπY]
  have hφZ : MMP.Flips.RationalMap.IsOver π f φ := hgh ▸ isOver_comp hφT
  -- the uniform gap of `K_Y + φ_* B₀`, from its adjoint contraction
  have hGY0 : ∀ P, 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ G).coeff P :=
    transformDivisor_nonneg φ hG0
  have hGYB : ∀ P, ((MMP.Mori.RationalMap.transformDivisor φ G).coeff P : ℝ) ≤
      (MMP.Mori.RationalMap.transformDivisor φ B₀).coeff P := fun P => by
    have h1 : ∀ Q, 0 ≤ (B₀ - QDivisor.toRDivisor G).coeff Q := fun Q => by
      have := hGB Q
      simp only [DivisorWithCoeffs.coeff_apply] at this
      show 0 ≤ (B₀ - QDivisor.toRDivisor G) Q
      rw [Finsupp.sub_apply]
      change 0 ≤ B₀ Q - ((G Q : ℚ) : ℝ)
      linarith
    have h2 := transformDivisor_nonneg (R := ℝ) φ h1 P
    rw [map_sub, transformDivisor_toRDivisor] at h2
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply] at h2 ⊢
    have h3 : (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ G)) P =
        ((MMP.Mori.RationalMap.transformDivisor φ G P : ℚ) : ℝ) := rfl
    linarith
  have hGYbig := (isRelativelyBig_transformDivisor_of_isBirationalContraction sX sY sZ hXn hX
    hYq hY hZ π f hπ hf φ hφ hφZ hφe G (fun P => hG0 P) (isQCartier_of_isQFactorial sX hXq G)
    hGbig).2.2
  obtain ⟨T', _, _, _, _, sT', g', h', H', -, -, -, -, -, a, ha, hgapY⟩ :=
    exists_isContraction_of_isRelativelyNef_of_isRelativelyBig sY sZ f hf hY hYq hZ 3 KY hnY3
      (MMP.Mori.RationalMap.transformDivisor φ B₀) (transformDivisor_nonneg φ hB₀) hY0klt
      (MMP.Mori.RationalMap.transformDivisor φ G) hGY0 hGYB hGYbig hnefY
  have hgap : ∀ ℓ : ProperCurve sY, ℓ.IsContractedBy f →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber ℂ sY
          (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀)) r L ℓ x →
          0 < x → a ≤ x := fun ℓ hℓ m r L x hx hpos =>
    ((hgapY ℓ hℓ m r L x hx).1.resolve_left hpos.ne')
  refine ⟨a / (2 * (a + 6)), by positivity, fun t ht0 ht B'' hB''0 hB''klt hmod hmodklt => ?_⟩
  set C := MMP.Mori.RationalMap.transformDivisor φ B'' with hCdef
  have hC0 : ∀ P, 0 ≤ C.coeff P := transformDivisor_nonneg φ hB''0
  -- presentations
  obtain ⟨m₀, r₀, L₀, hL₀, hD₀⟩ := isCartierCombination_of_isQFactorial hYq
    (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀))
  obtain ⟨mC, rC, LC, hLC, hDC⟩ := isCartierCombination_of_isQFactorial hYq
    (logCanonicalDivisor KY C)
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs] at hD₀ hDC
  set rA : Fin (m₀ + mC) → ℝ := Fin.append ((1 - t) • r₀) (t • rC)
  set LA : Fin (m₀ + mC) → Divisor Y := Fin.append L₀ LC
  have hLA : ∀ j, (LA j).IsCartier := Fin.addCases (fun j => by simpa [LA] using hL₀ j)
    (fun j => by simpa [LA] using hLC j)
  have htr : MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'') =
      (1 - t) • MMP.Mori.RationalMap.transformDivisor φ B₀ + t • C := by
    rw [← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_add, map_smul, map_smul]
    rfl
  have hDA : logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ +
      t • B'')) = ∑ j, rA j • Divisor.toRDivisor (LA j) := by
    rw [htr]
    have hsplit : logCanonicalDivisor KY ((1 - t) • MMP.Mori.RationalMap.transformDivisor φ B₀ +
        t • C) = (1 - t) • logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀) +
          t • logCanonicalDivisor KY C := by
      refine Finsupp.ext fun P => ?_
      simp only [logCanonicalDivisor, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      ring
    rw [hsplit, hD₀, hDC]
    simp only [rA, LA, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply,
      smul_eq_mul, mul_smul, Finset.smul_sum]
  have hform : ∀ z, relForm sY f rA LA hLA z =
      (1 - t) * relForm sY f r₀ L₀ hL₀ z + t * relForm sY f rC LC hLC z :=
    fun z => relForm_append sY f _ _ r₀ L₀ hL₀ rC LC hLC hLA z
  refine ⟨m₀ + mC, rA, LA, hLA, hDA, fun ℓ hℓ x hx => ?_⟩
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sY ℓ).1 _ _ _ _ _ _ _ hx
    (isRIntersectionNumber_relForm rA LA hLA hDA hℓ)]
  have hz : ℓ.relativeClass f hℓ ∈ relativeClosedConeOfCurves sY f := by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (Submodule.subset_span ⟨⟨ℓ, hℓ⟩, rfl⟩)
  obtain ⟨s', R, w, hRw, hsum⟩ :=
    exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sY sZ f hf hz
  rw [hsum, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  by_contra hneg
  push Not at hneg
  obtain ⟨hRi, hwi⟩ := hRw i
  obtain ⟨-, v, hv0, hRv⟩ := hRi
  have hwi' := hwi
  rw [hRv] at hwi'
  obtain ⟨c, hc0, hcv⟩ := hwi'
  have hcpos : 0 < c := lt_of_le_of_ne hc0 fun h0 => by
    rw [← hcv, ← h0, zero_smul, map_zero] at hneg; exact lt_irrefl _ hneg
  have hvneg : relForm sY f rA LA hLA v < 0 := by
    rw [← hcv, map_smul, smul_eq_mul] at hneg
    exact neg_of_mul_neg_right hneg hcpos.le
  have hnegR : ∀ u ∈ R i, u ≠ 0 → relForm sY f rA LA hLA u < 0 := fun u hu hu0 => by
    rw [hRv] at hu
    obtain ⟨c', hc'0, rfl⟩ := hu
    have hc'pos : 0 < c' := lt_of_le_of_ne hc'0 fun h0 => hu0 (by rw [← h0, zero_smul])
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc'pos hvneg
  -- the radial-ray lemma: `K_Y + φ_* B₀` vanishes on the ray
  have hzero := extremalRay_degree_eq_zero_of_lt sY hY hZ f hf hYq KY hnY3
    (MMP.Mori.RationalMap.transformDivisor φ B₀) hY0klt hnefY a ha hgap C hC0 hmodklt t ht0 ht
    (R i) (hRw i).1 ⟨m₀ + mC, rA, LA, hLA, by
      rw [← hDA, htr]
      refine Finsupp.ext fun P => ?_
      simp only [logCanonicalDivisor, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      ring, fun u hu hu0 => by rw [← relForm_apply]; exact hnegR u hu hu0⟩
    m₀ r₀ L₀ hL₀ hD₀
  have hzero' : ∀ u ∈ R i, relForm sY f r₀ L₀ hL₀ u = 0 := fun u hu => by
    rw [relForm_apply]; exact hzero u hu
  have hCneg : ∀ u ∈ R i, u ≠ 0 → relForm sY f rC LC hLC u < 0 := fun u hu hu0 => by
    have := hnegR u hu hu0
    rw [hform, hzero' u hu, mul_zero, zero_add] at this
    exact neg_of_mul_neg_right this ht0.le
  -- a rational curve spanning the ray
  have hR' := isExtremalRay_image_relativeToAbsolute sY sZ f hf (hRw i).1
  have hinj := (existsUnique_isNaturalRelativeMap_and_injective sY f).2 _
    (isNaturalRelativeMap_relativeToAbsolute sY f)
  have hneg' : ∃ (j₀ : Unit) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y)
      (hL : ∀ i, (L i).IsCartier),
      Divisor.toRDivisor KY + (fun _ => C) j₀ = ∑ i, r i • Divisor.toRDivisor (L i) ∧
      ∀ u ∈ relativeToAbsolute sY f '' R i, u ≠ 0 →
        ∑ i, r i * (haveI := (hL i).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sY (L i).divisorialSheaf u) < 0 := by
    refine ⟨(), mC, rC, LC, hLC, hDC, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ hz0
    have hz0' : z ≠ 0 := fun h => hz0 (by rw [h, map_zero])
    rw [← absForm_apply sY rC LC hLC, absForm_relativeToAbsolute]
    exact hCneg z hz hz0'
  obtain ⟨ℓ', -, ⟨u₁, hu₁R, hu₁⟩, hℓ'0, -⟩ :=
    exists_isRationalCurve_numericalClass_mem_and_neg_six_le (sX := sY) hYq hnY3
      (B := fun _ : Unit => C) (fun _ => hC0) (fun _ => hmodklt) hR' hneg'
  have hℓ'c := isContractedBy_of_relativeToAbsolute_eq hZ hf ℓ' u₁ hu₁
  have hu₁eq : ℓ'.relativeClass f hℓ'c = u₁ := hinj (by rw [hu₁]; rfl)
  have hu₁0 : u₁ ≠ 0 := fun h => hℓ'0 (by rw [← hu₁, h, map_zero])
  -- `ℓ'` is contracted over `T`
  have hx0 : MMP.Flips.IsRIntersectionNumber ℂ sY
      (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ B₀)) r₀ L₀ ℓ' 0 := by
    have := isRIntersectionNumber_relForm r₀ L₀ hL₀ hD₀ hℓ'c
    rwa [hu₁eq, hzero' u₁ hu₁R] at this
  have hπc := isContractedBy_of_isRIntersectionNumber_eq_zero hX hZ hπ hdim hXq hKX hB₀ hklt hnef
    hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hcrit hR ℓ' hℓ'c hx0
  -- but `K_Y + φ_* B''` is nef over `T`
  obtain ⟨mN, rN, LN, hLN, hDN, hnnN⟩ := hmod.isRelativelyNef
  have hxN := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sY ℓ' rN LN hLN
  rw [← hDN] at hxN
  have hxC := isRIntersectionNumber_relForm rC LC hLC hDC hℓ'c
  rw [hu₁eq] at hxC
  have heq := (IsRIntersectionNumber.eq_and_linear ℂ sY ℓ').1 _ _ _ _ _ _ _ hxC hxN
  have := hnnN ℓ' hπc _ hxN
  have := hCneg u₁ hu₁R hu₁0
  linarith

/-- **The radial step.** Let `g : X ⟶ T` be the adjoint contraction of the klt pair `(X, B₀)`
with `K_X + B₀` nef over `Z`, and `φ : X ⤏ Y` a birational contraction over `T`. There is
`ε > 0` such that whenever `Y` is a klt log minimal model over `T` of an effective klt pair
`(X, B'')`, it is a klt log minimal model over `Z` of `(X, (1 - t) B₀ + t B'')` for every
`0 < t < ε`: by the radial-ray lemma no negative extremal ray over `Z` of the transformed adjoint
survives, and the comparison at the contracted primes is the affine combination of the zero
comparison for `B₀` and the positive comparison for `B''`. -/
private theorem exists_pos_isRealLogMinimalModel_lineMap
    {X Z T Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sT : T ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {g : X ⟶ T} {h : T ⟶ Z}
    {πY : Y ⟶ T} {KX : Divisor X} {KY : Divisor Y} {B₀ : RDivisor X} {H : RDivisor T}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hB₀ : ∀ P, 0 ≤ B₀.coeff P)
    (hklt : IsRealKltPair sX B₀)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX B₀))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) (hg : IsContraction sX sT g) (hgh : g ≫ h = π)
    (hH : MMP.Flips.IsRelativelyAmple h H)
    (hpull : ∃ gH : RDivisor X, MMP.Flips.IsRCartierPullback g H gH ∧
      ∃ (m : ℕ) (r : Fin m → ℝ) (φ : Fin m → (RationalFunctions X)ˣ),
        MMP.Flips.logCanonicalDivisor KX B₀ - gH =
          ∑ i, r i • Divisor.toRDivisor (principalDivisor (φ i)))
    (φ : X.RationalMap Y) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYq : IsQFactorial sY)
    (hπY : πY ≫ sT = sY) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hφT : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (G : QDivisor X) (hG0 : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGB : ∀ P, (G.coeff P : ℝ) ≤ B₀.coeff P)
    (hcrit : ∀ C : ProperCurve sX, C.IsContractedBy π → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX (logCanonicalDivisor KX B₀) r L C x →
        (x = 0 ↔ C.IsContractedBy g)) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → ∀ B'' : RDivisor X, (∀ P, 0 ≤ B''.coeff P) →
      IsRealKltPair sX B'' →
      IsRealLogMinimalModel sX sY sT g πY KX B'' KY
        (MMP.Mori.RationalMap.transformDivisor φ B'') φ →
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B'') →
      IsRealLogMinimalModel sX sY sZ π (πY ≫ h) KX ((1 - t) • B₀ + t • B'') KY
          (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'')) φ ∧
        IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'')) := by
  classical
  obtain ⟨ε, hε, hεnef⟩ := exists_pos_isRelativelyNef_lineMap (KY := KY) hX hZ hπ hdim hXq hKX
    hB₀ hklt hnef
    hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe G hG0 hGbig hGB hcrit
  refine ⟨min ε 1, lt_min hε one_pos, fun t ht0 ht B'' hB''0 hB''klt hmod hmodklt => ?_⟩
  have htε : t < ε := ht.trans_le (min_le_left _ _)
  have ht1 : t < 1 := ht.trans_le (min_le_right _ _)
  have hhZ : h ≫ sZ = sT := by
    haveI : IsDominant g := ⟨hg.surjective.denseRange⟩
    refine ext_of_isDominant (ι := g) ?_
    rw [← Category.assoc, hgh, hπ, hg.comp_eq]
  have hw : ![1 - t, t] ∈ stdSimplex ℝ (Fin 2) :=
    ⟨fun i => by fin_cases i <;> simp <;> linarith, by simp⟩
  have hconv : ∀ {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
      {sV : V ⟶ Spec (.of ℂ)}, IsQFactorial sV → ∀ {C₁ C₂ : RDivisor V},
      IsRealKltPair sV C₁ → IsRealKltPair sV C₂ → IsRealKltPair sV ((1 - t) • C₁ + t • C₂) :=
    fun hq C₁ C₂ h₁ h₂ => by
      have := isRealKltPair_wsum hq (V := ![C₁, C₂]) (fun i => by fin_cases i <;> simpa) hw
      simpa [wsum, Fin.sum_univ_two] using this
  have htr : MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'') =
      (1 - t) • MMP.Mori.RationalMap.transformDivisor φ B₀ +
        t • MMP.Mori.RationalMap.transformDivisor φ B'' := by
    rw [← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_add, map_smul, map_smul]
    rfl
  have hY₀klt := isRealKltPair_transformDivisor_of_isOver hX hZ hπ hdim hXq hKX hB₀ hklt hnef
    hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hmod
  have hYklt : IsRealKltPair sY
      (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'')) := by
    rw [htr]; exact hconv hmod.isQFactorial hY₀klt hmodklt
  have hXklt' := hconv hXq hklt hB''klt
  have hB'0 : ∀ P, 0 ≤ ((1 - t) • B₀ + t • B'').coeff P := fun P => by
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    have h1 := hB₀ P
    have h2 := hB''0 P
    simp only [DivisorWithCoeffs.coeff_apply] at h1 h2
    nlinarith
  have hnoext := IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hmod
  obtain ⟨W, _, _, _, sW, p, q, hh, GX, GY, hR, hpos⟩ := hmod.exists_resolution_pos
  obtain ⟨GX₀, GY₀, hGX₀, hGY₀, hG₀⟩ := exists_isRCartierPullback_eq_of_isOver hX hZ hπ hdim hXq
    hKX hB₀ hklt hnef hT hg hgh hH hpull φ hY hYq hπY hφ hφT hφe hR
  have hsplit : ∀ {V : Scheme.{0}} (K : Divisor V) (C₁ C₂ : RDivisor V),
      logCanonicalDivisor K ((1 - t) • C₁ + t • C₂) =
        (1 - t) • logCanonicalDivisor K C₁ + t • logCanonicalDivisor K C₂ := fun K C₁ C₂ => by
    refine Finsupp.ext fun P => ?_
    simp only [logCanonicalDivisor, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  have hdiff : (1 - t) • GX₀ + t • GX - ((1 - t) • GY₀ + t • GY) = t • (GX - GY) := by
    rw [hG₀, smul_sub]; abel
  have hres : IsLogComparisonResolution sX sY sW φ KX ((1 - t) • B₀ + t • B'') KY
      (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B₀ + t • B'')) p q hh
      ((1 - t) • GX₀ + t • GX) ((1 - t) • GY₀ + t • GY) :=
    { hR with
      isRCartierPullback_left := by
        rw [hsplit]; exact isRCartierPullback_smul_add_smul hGX₀ hR.isRCartierPullback_left _ _
      isRCartierPullback_right := by
        rw [htr, hsplit]
        exact isRCartierPullback_smul_add_smul hGY₀ hR.isRCartierPullback_right _ _
      effective := fun P => by
        rw [hdiff]
        simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul]
        have := hR.effective P
        simp only [DivisorWithCoeffs.coeff_apply] at this
        positivity
      isExceptional := fun P hP => hR.isExceptional P (by
        rw [hdiff] at hP
        simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul] at hP
        rw [DivisorWithCoeffs.coeff_apply]
        exact right_ne_zero_of_mul hP) }
  refine ⟨{ isRealLcPair := ⟨hXklt'.1, hB'0, hXklt'.2.2.1,
              fun n E a ha => (hXklt'.2.2.2 n E a ha).le⟩
            isCanonicalDivisor := hmod.isCanonicalDivisor
            comp_eq := hπ
            isNormalVariety_model := hmod.isNormalVariety_model
            isCanonicalDivisor_model := hmod.isCanonicalDivisor_model
            isProjectiveVariety_model := hmod.isProjectiveVariety_model
            comp_eq_model := by rw [Category.assoc, hhZ]; exact hmod.comp_eq_model
            isQFactorial := hmod.isQFactorial
            isRealDltPair := isRealDltPair_of_isRealKltPair
              (fun P => transformDivisor_nonneg φ hB'0 P) hYklt
            isBirational := hmod.isBirational
            isOver := hgh ▸ isOver_comp hmod.isOver
            coeff_boundary := fun F => by rw [if_neg (hnoext F), add_zero]
            isRelativelyNef := hεnef t ht0 htε B'' hB''0 hB''klt hmod hmodklt
            exists_resolution := ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, hh, _,
              _, hres⟩
            exists_resolution_pos := ⟨W, inferInstance, inferInstance, inferInstance, sW, p, q, hh,
              _, _, hres, fun P hP P' hP' => by
                rw [hdiff]
                simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul]
                have := hpos P hP P' hP'
                simp only [DivisorWithCoeffs.coeff_apply] at this
                exact mul_pos ht0 this⟩ }, hYklt⟩

end NefCase

/-! ### Rational maps through function fields -/

section FunctionFields

variable {V W X Y Z : Scheme.{0}}

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp' [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  haveI : Nonempty Y := ⟨f (genericPoint X)⟩
  obtain ⟨U₁, hU₁, h₁⟩ := hf.exists_isOpenImmersion
  obtain ⟨U₂, hU₂, h₂⟩ := hg.exists_isOpenImmersion
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous (U₁.2.dense hU₁)
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := ((U₂.2.dense hU₂).inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' (f ≫ g) U hne

end FunctionFields

/-! ### Exceptional prime divisors of birational morphisms -/

section ExceptionalPrimes

open MMP.Mori

variable {W Y : Scheme.{0}} [IsIntegral W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A prime divisor with a strict transform along a morphism is not exceptional. -/
private theorem transformPrimeDivisor_eq_none_of_isExceptional [IsReduced W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) {P : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.IsExceptional (X := W) q.toRationalMap P) :
    RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P = none := by
  rcases h : RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P with _ | F
  · rfl
  · exfalso
    have hq := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P F).1 h
    have hdef : RationalMap.DefinedAt (X := W) q.toRationalMap P.genericPoint := by
      rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]; trivial
    have h2 := RationalMap.isExceptional_iff.1 hP hdef
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h2
    have hmem : F.genericPoint ∈ (RationalMap.transform (X := W) q.toRationalMap
        P.idealSheaf.support : Set Y) := by
      rw [MMP.Flips.coe_transform_eq_closure_singleton q.toPartialMap rfl P trivial]
      change F.genericPoint ∈ closure {q P.genericPoint}
      rw [← hq]
      exact subset_closure rfl
    have := h2 _ hmem
    rw [F.coheight_genericPoint] at this
    exact absurd this (by norm_num)

/-- A prime divisor without strict transform along a separated birational morphism onto a
normal scheme is exceptional: the image of its generic point has coheight at least two. -/
private theorem isExceptional_of_transformPrimeDivisor_eq_none [IsReduced W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) {P : MMP.Mori.PrimeDivisor W}
    (hP : RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P = none) :
    RationalMap.IsExceptional (X := W) q.toRationalMap P := by
  rw [RationalMap.isExceptional_iff]
  intro _
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    MMP.Flips.coe_transform_eq_closure_singleton q.toPartialMap rfl P trivial]
  set y := q.toPartialMap.hom ⟨P.genericPoint, trivial⟩ with hy
  have hy' : y = q P.genericPoint := rfl
  suffices h2 : 2 ≤ Order.coheight y by
    intro x hx
    have hxy : x ≤ y := specializes_iff_mem_closure.mpr hx
    exact h2.trans (Order.coheight_anti hxy)
  by_contra hlt
  push Not at hlt
  have hy1 : Order.coheight y ≤ 1 := by
    by_contra h
    push Not at h
    exact absurd (Order.add_one_le_of_lt h) (by rw [one_add_one_eq_two]; exact not_le.mpr hlt)
  rcases eq_or_ne (Order.coheight y) 0 with h0 | h0
  · -- `y` is the generic point of `Y`, over which only the generic point of `W` lies
    have hmax : IsMax y := Order.coheight_eq_zero.mp h0
    have hgen : y = genericPoint Y := by
      have h1 : y ≤ genericPoint Y :=
        specializes_iff_mem_closure.mpr ((genericPoint_spec Y).specializes trivial).mem_closure
      exact (Specializes.antisymm (hmax h1) h1).eq
    have hqW : q (genericPoint W) = genericPoint Y :=
      MMP.Positivity.map_genericPoint_eq_of_isDominant q
    haveI : ValuationRing (Y.presheaf.stalk (q (genericPoint W))) := by
      rw [hqW]; exact inferInstanceAs (ValuationRing Y.functionField)
    haveI : ValuationRing (Y.presheaf.stalk (q P.genericPoint)) := by
      rw [← hy', hgen]; exact inferInstanceAs (ValuationRing Y.functionField)
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing q hq (genericPoint W)
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing q hq P.genericPoint
    have heq : P.genericPoint = genericPoint W :=
      MMP.Positivity.eq_of_isIso_stalkMap q hq (by rw [hqW, ← hy', hgen])
    have h1 := P.coheight_genericPoint
    rw [heq] at h1
    have h0W : Order.coheight (genericPoint W) = 0 :=
      Order.coheight_eq_zero.mpr fun z _ =>
        specializes_iff_mem_closure.mpr ((genericPoint_spec W).specializes trivial).mem_closure
    rw [h0W] at h1
    exact zero_ne_one h1
  · have h1 : Order.coheight y = 1 := le_antisymm hy1 (Order.one_le_iff_ne_zero.mpr h0)
    have hF := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y h1
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y h1)).2 (hF.trans hy').symm] at hP
    exact Option.some_ne_none _ hP

end ExceptionalPrimes

/-! ### Strict transforms through a common model -/

section CommonModel

open MMP.Mori

variable {V X Y Y' : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
  {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)}

/-- **The strict transform reads off one coefficient.** On a common resolution `p`, `q` of
`φ = q ∘ p⁻¹`, if `φ` sends `P` to `F`, the coefficient of `φ_* D` at `F` is that of `D` at `P`:
no other prime divisor is sent to `F`. -/
private theorem transformDivisor_compHom_apply_of_eq_some (hXn : IsNormalVariety ℂ sX)
    (hYn : IsNormalVariety ℂ sY) {p : V ⟶ X} {q : V ⟶ Y} [IsProper p] [IsProper q]
    (hVp : IsNormalVariety ℂ (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) {h : X.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) {P : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y} (hP : RationalMap.transformPrimeDivisor (h.compHom q) P = some F)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (h.compHom q) D F = D P := by
  classical
  have := hXn.1
  have := hYn.1
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hVp
  haveI : IsSeparated p := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  haveI : IsSeparated q := IsSeparated.of_comp q (Y ↘ ⊤_ Scheme)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hq : ∀ P₁ : MMP.Mori.PrimeDivisor X,
      RationalMap.transformPrimeDivisor (h.compHom q) P₁ = some F →
        ∃ P₁' : MMP.Mori.PrimeDivisor V, p P₁'.genericPoint = P₁.genericPoint ∧
          q P₁'.genericPoint = F.genericPoint := fun P₁ hP₁ => by
    obtain ⟨P₁', hP₁', -, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVp hpb P₁
    have hhP₁ := transformPrimeDivisor_eq_some_of_isInverse hpbij hinv hP₁'
    rw [transformPrimeDivisor_compHom hhP₁ q] at hP₁
    exact ⟨P₁', hP₁', (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P₁' F).1
      hP₁⟩
  obtain ⟨P', hP'p, hP'q⟩ := hq P hP
  have huniq : ∀ P₁ : MMP.Mori.PrimeDivisor X,
      RationalMap.transformPrimeDivisor (h.compHom q) P₁ = some F → P₁ = P := fun P₁ hP₁ => by
    obtain ⟨P₁', hP₁'p, hP₁'q⟩ := hq P₁ hP₁
    have h₁ : P₁' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_genericPoint q hqbij hP₁'q hP'q)
    subst h₁
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP₁'p.symm.trans hP'p)
  rw [transformDivisor_apply, Finsupp.sum]
  by_cases hPs : P ∈ D.support
  · rw [Finset.sum_eq_single P (fun P₁ _ hne => if_neg fun h => hne (huniq P₁ h))
      (fun h => absurd hPs h), if_pos hP]
  · rw [Finset.sum_eq_zero fun P₁ hP₁ => by
      rw [if_neg]; exact fun h => hPs (huniq P₁ h ▸ hP₁)]
    exact (Finsupp.notMem_support_iff.mp hPs).symm

variable {a : V ⟶ X} {b : V ⟶ Y} {c : V ⟶ Y'} [IsProper a] [IsProper b] [IsProper c]
  {ha : X.RationalMap V} {hb : Y.RationalMap V}

/-- **Strict transforms through a common model.** Let `a : V ⟶ X`, `b : V ⟶ Y`, `c : V ⟶ Y'` be
proper birational morphisms of normal varieties with inverses `a⁻¹`, `b⁻¹`, and suppose that
`ψ = c ∘ b⁻¹` extracts no prime divisor. Then `χ = c ∘ a⁻¹` is `ψ ∘ φ` on prime divisors, for
`φ = b ∘ a⁻¹`: `χ` sends `P` where `ψ` sends `φ(P)`, and contracts `P` if `φ` does. -/
private theorem transformPrimeDivisor_compHom_eq_bind (hXn : IsNormalVariety ℂ sX)
    (hYn : IsNormalVariety ℂ sY) (hY'n : IsNormalVariety ℂ sY')
    (hVa : IsNormalVariety ℂ (a ≫ sX)) (hVb : IsNormalVariety ℂ (b ≫ sY))
    (hab : IsBirationalMorphism a) (hbb : IsBirationalMorphism b) (hcb : IsBirationalMorphism c)
    (hainv : RationalMap.IsInverse a.toRationalMap ha)
    (hbinv : RationalMap.IsInverse b.toRationalMap hb)
    (hψ : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (hb.compHom c) F)
    (P : MMP.Mori.PrimeDivisor X) :
    RationalMap.transformPrimeDivisor (ha.compHom c) P =
      (RationalMap.transformPrimeDivisor (ha.compHom b) P).bind
        (RationalMap.transformPrimeDivisor (hb.compHom c)) := by
  have := hXn.1
  have := hYn.1
  have := hY'n.1
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hY'n
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hVa
  haveI : IsSeparated a := IsSeparated.of_comp a (X ↘ ⊤_ Scheme)
  haveI : IsSeparated b := IsSeparated.of_comp b (Y ↘ ⊤_ Scheme)
  haveI : IsSeparated c := IsSeparated.of_comp c (Y' ↘ ⊤_ Scheme)
  haveI : IsDominant a := hab.isDominant
  haveI : IsDominant b := hbb.isDominant
  haveI : IsDominant c := hcb.isDominant
  obtain ⟨P', hP', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVa hab P
  have haP := transformPrimeDivisor_eq_some_of_isInverse hab.functionFieldMap_bijective hainv hP'
  rw [transformPrimeDivisor_compHom haP c, transformPrimeDivisor_compHom haP b]
  rcases hbP : RationalMap.transformPrimeDivisor (X := V) b.toRationalMap P' with _ | Q
  · rcases hcP : RationalMap.transformPrimeDivisor (X := V) c.toRationalMap P' with _ | F
    · rfl
    · exfalso
      obtain ⟨Q, hQ⟩ : ∃ Q, RationalMap.transformPrimeDivisor (hb.compHom c) Q = some F := by
        by_contra hne
        push Not at hne
        exact hψ F hne
      obtain ⟨Q', hQ', -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hVb hbb Q
      have hbQ :=
        transformPrimeDivisor_eq_some_of_isInverse hbb.functionFieldMap_bijective hbinv hQ'
      rw [transformPrimeDivisor_compHom hbQ c] at hQ
      have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff c Q' F).1 hQ
      have h2 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff c P' F).1 hcP
      have hQP : Q' = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (eq_of_map_eq_genericPoint c hcb.functionFieldMap_bijective h1 h2)
      subst hQP
      rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff b Q' Q).2 hQ'] at hbP
      exact Option.some_ne_none _ hbP
  · have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff b P' Q).1 hbP
    have hbQ := transformPrimeDivisor_eq_some_of_isInverse hbb.functionFieldMap_bijective hbinv h1
    rw [Option.bind_some, transformPrimeDivisor_compHom hbQ c]

/-- The composite `c ∘ a⁻¹` extracts no prime divisor if `b ∘ a⁻¹` and `c ∘ b⁻¹` do not. -/
private theorem not_isInverseExceptional_compHom (hXn : IsNormalVariety ℂ sX)
    (hYn : IsNormalVariety ℂ sY) (hY'n : IsNormalVariety ℂ sY')
    (hVa : IsNormalVariety ℂ (a ≫ sX)) (hVb : IsNormalVariety ℂ (b ≫ sY))
    (hab : IsBirationalMorphism a) (hbb : IsBirationalMorphism b) (hcb : IsBirationalMorphism c)
    (hainv : RationalMap.IsInverse a.toRationalMap ha)
    (hbinv : RationalMap.IsInverse b.toRationalMap hb)
    (hφ : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ha.compHom b) F)
    (hψ : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (hb.compHom c) F)
    (F : MMP.Mori.PrimeDivisor Y') :
    ¬ MMP.Flips.RationalMap.IsInverseExceptional (ha.compHom c) F := by
  intro hF
  obtain ⟨Q, hQ⟩ : ∃ Q, RationalMap.transformPrimeDivisor (hb.compHom c) Q = some F := by
    by_contra hne; push Not at hne; exact hψ F hne
  obtain ⟨P, hP⟩ : ∃ P, RationalMap.transformPrimeDivisor (ha.compHom b) P = some Q := by
    by_contra hne; push Not at hne; exact hφ Q hne
  refine hF P ?_
  rw [transformPrimeDivisor_compHom_eq_bind hXn hYn hY'n hVa hVb hab hbb hcb hainv hbinv hψ, hP,
    Option.bind_some, hQ]

/-- The strict transform along `c ∘ a⁻¹` is the strict transform along `c ∘ b⁻¹` of the strict
transform along `b ∘ a⁻¹`. -/
private theorem transformDivisor_compHom_eq_transformDivisor (hXn : IsNormalVariety ℂ sX)
    (hYn : IsNormalVariety ℂ sY) (hY'n : IsNormalVariety ℂ sY')
    (hVa : IsNormalVariety ℂ (a ≫ sX)) (hVb : IsNormalVariety ℂ (b ≫ sY))
    (hab : IsBirationalMorphism a) (hbb : IsBirationalMorphism b) (hcb : IsBirationalMorphism c)
    (hainv : RationalMap.IsInverse a.toRationalMap ha)
    (hbinv : RationalMap.IsInverse b.toRationalMap hb)
    (hψ : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (hb.compHom c) F)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (ha.compHom c) D =
      RationalMap.transformDivisor (hb.compHom c)
        (RationalMap.transformDivisor (ha.compHom b) D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | single P r =>
    rw [RationalMap.transformDivisor_single, RationalMap.transformDivisor_single,
      transformPrimeDivisor_compHom_eq_bind hXn hYn hY'n hVa hVb hab hbb hcb hainv hbinv hψ]
    rcases RationalMap.transformPrimeDivisor (ha.compHom b) P with _ | Q
    · simp
    · rw [Option.bind_some, show ((some Q).elim 0 (Finsupp.single · r) : DivisorWithCoeffs R Y) =
        Finsupp.single Q r from rfl, RationalMap.transformDivisor_single]

end CommonModel

/-! ### Pull-backs of `ℝ`-Cartier divisors -/

/-- The pull-back of an `ℝ`-Cartier divisor is a combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRCartierPullback' {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {D : RDivisor X} {G : RDivisor Y} (h : MMP.Flips.IsRCartierPullback f D G) :
    MMP.Flips.IsCartierCombination G := by
  obtain ⟨m, r, L, L', hLc, -, hpb, rfl⟩ := h
  exact ⟨m, r, L', fun j => ((hpb j).2).isCartier (hLc j), rfl⟩

/-! ### Composing log minimal models -/

section CompositeModel

open MMP.Mori

/-- **The composite of two log minimal models.** Let `φ : X ⤏ Y` be a birational contraction over
`Z` to a `ℚ`-factorial `Y`, realised on a smooth common resolution `p₁ : W₁ ⟶ X`, `q₁ : W₁ ⟶ Y`
comparing canonical divisors `K_X`, `K_Y`, and let `(X, B)` be a klt pair whose comparison
`p₁^*(K_X + B) - q₁^*(K_Y + φ_* B)` is positive along the strict transforms of the prime divisors
contracted by `φ`. If `ψ : Y ⤏ Y'` is a klt log minimal model of `(Y/Z, φ_* B)`, then the
composite `χ = ψ ∘ φ` is a klt log minimal model of `(X/Z, B)`.

On a smooth common model `V` of the resolutions of `φ` and `ψ`, the comparison for `χ` is the sum
of the comparisons for `φ` and `ψ`. Its push-forward to `X` is effective, positive at the prime
divisors contracted by `χ`, and `K_{Y'} + χ_* B` is nef over `Z`, so the comparison is effective
by the negativity lemma; it is exceptional over `Y'` since `χ` extracts no prime divisor. -/
private theorem isRealLogMinimalModel_compHom
    {X Y Y' Z W₁ : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [CompactSpace Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    [IsIntegral W₁] [IsLocallyNoetherian W₁] [IsNormal W₁]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] {sY' : Y' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sW₁ : W₁ ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {πY : Y ⟶ Z} {πY' : Y' ⟶ Z}
    {KX : Divisor X} {KY : Divisor Y} {KY' : Divisor Y'}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) (hYq : IsQFactorial sY)
    {φ : X.RationalMap Y} (hφo : MMP.Flips.RationalMap.IsOver π πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {B₀ : RDivisor X} {p₁ : W₁ ⟶ X} {q₁ : W₁ ⟶ Y} {h₁ : X.RationalMap W₁}
    {GX₀ GY₀ : RDivisor W₁}
    (hR₁ : IsLogComparisonResolution sX sY sW₁ φ KX B₀ KY
      (RationalMap.transformDivisor φ B₀) p₁ q₁ h₁ GX₀ GY₀)
    {B : RDivisor X} (hB0 : ∀ P, 0 ≤ B.coeff P) (hBklt : IsRealKltPair sX B)
    {GX₁ GY₁ : RDivisor W₁}
    (hGX₁ : MMP.Flips.IsRCartierPullback p₁ (logCanonicalDivisor KX B) GX₁)
    (hGY₁ : MMP.Flips.IsRCartierPullback q₁
      (logCanonicalDivisor KY (RationalMap.transformDivisor φ B)) GY₁)
    (hpos : ∀ P : MMP.Mori.PrimeDivisor X, RationalMap.IsExceptional φ P →
      ∀ P₁, RationalMap.transformPrimeDivisor h₁ P = some P₁ → 0 < (GX₁ - GY₁).coeff P₁)
    {ψ : Y.RationalMap Y'}
    (hψ : IsRealLogMinimalModel sY sY' sZ πY πY' KY (RationalMap.transformDivisor φ B) KY'
      (RationalMap.transformDivisor ψ (RationalMap.transformDivisor φ B)) ψ)
    (hψklt : IsRealKltPair sY'
      (RationalMap.transformDivisor ψ (RationalMap.transformDivisor φ B)))
    [IsDominant p₁] [IsDominant q₁] {χ : X.RationalMap Y'}
    (hχ : specFunctionFieldMap p₁ ≫ χ.fromFunctionField =
      specFunctionFieldMap q₁ ≫ ψ.fromFunctionField) :
    IsRealLogMinimalModel sX sY' sZ π πY' KX B KY' (RationalMap.transformDivisor χ B) χ ∧
      IsRealKltPair sY' (RationalMap.transformDivisor χ B) := by
  classical
  -- the varieties `X`, `Y`, `Y'`
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have hY'n : IsNormalVariety ℂ sY' := hψ.isNormalVariety_model
  have := hXn.1
  have := hYn.1
  have := hY'n.1
  haveI : IsSeparated sX := hXn.1.toIsSeparated
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsSeparated sY' := hY'n.1.toIsSeparated
  haveI : LocallyOfFiniteType sY' := hY'n.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY' := hY'n.1.toQuasiCompact
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hY'n
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := by
    have : (Z ↘ ⊤_ Scheme) = sZ ≫ CategoryTheory.Limits.terminal.from (Spec (.of ℂ)) :=
      Subsingleton.elim _ _
    rw [this]; infer_instance
  have hψe := IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hψ
  -- the resolution `W₁` of `φ`
  have hW₁v := hR₁.isVariety
  haveI : QuasiCompact sW₁ := hW₁v.toQuasiCompact
  haveI : CompactSpace W₁ := QuasiCompact.compactSpace_of_compactSpace sW₁
  have hW₁n : IsNormalVariety ℂ sW₁ := ⟨hW₁v, inferInstance⟩
  have hW₁p : IsNormalVariety ℂ (p₁ ≫ sX) := by rw [hR₁.comp_eq_left]; exact hW₁n
  have hW₁q : IsNormalVariety ℂ (q₁ ≫ sY) := by rw [hR₁.comp_eq_right]; exact hW₁n
  haveI := isProper_of_isProjectiveMorphism p₁ hR₁.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q₁ hR₁.isProjectiveMorphism_right
  have hp₁b := hR₁.isBirationalMorphism_left
  have hq₁b := hR₁.isBirationalMorphism_right
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hW₁n
  haveI : IsSeparated p₁ := IsSeparated.of_comp p₁ (X ↘ ⊤_ Scheme)
  haveI : IsSeparated q₁ := IsSeparated.of_comp q₁ (Y ↘ ⊤_ Scheme)
  -- the resolution `W₂` of `ψ`
  obtain ⟨W₂, _, _, _, sW₂, q₂, r₂, h₂, GY₂, GY'₂, hR₂, hpos₂⟩ := hψ.exists_resolution_pos
  have hW₂v := hR₂.isVariety
  haveI : QuasiCompact sW₂ := hW₂v.toQuasiCompact
  haveI : CompactSpace W₂ := QuasiCompact.compactSpace_of_compactSpace sW₂
  have hW₂n : IsNormalVariety ℂ sW₂ := ⟨hW₂v, inferInstance⟩
  have hW₂q : IsNormalVariety ℂ (q₂ ≫ sY) := by rw [hR₂.comp_eq_left]; exact hW₂n
  have hW₂r : IsNormalVariety ℂ (r₂ ≫ sY') := by rw [hR₂.comp_eq_right]; exact hW₂n
  haveI := isProper_of_isProjectiveMorphism q₂ hR₂.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism r₂ hR₂.isProjectiveMorphism_right
  have hq₂b := hR₂.isBirationalMorphism_left
  have hr₂b := hR₂.isBirationalMorphism_right
  haveI : IsDominant q₂ := hq₂b.isDominant
  haveI : IsDominant r₂ := hr₂b.isDominant
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hW₂n
  haveI : IsSeparated q₂ := IsSeparated.of_comp q₂ (Y ↘ ⊤_ Scheme)
  haveI : IsSeparated r₂ := IsSeparated.of_comp r₂ (Y' ↘ ⊤_ Scheme)
  -- a smooth common model `V` of `W₁` and `W₂` over `Y`
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hYn.1
  haveI : AlgebraicGeometry.IsVariety ℂ (q₁ ≫ sY) := hW₁q.1
  haveI : AlgebraicGeometry.IsVariety ℂ (q₂ ≫ sY) := hW₂q.1
  obtain ⟨V, g₁, g₂, hres, _, hg₂b, hg⟩ := MMP.Intersection.exists_isResolution_comp_eq_comp sY q₁
    q₂ (by rw [hR₁.comp_eq_right]; exact hR₁.isSmoothScheme)
    (by rw [hR₂.comp_eq_left]; exact hR₂.isSmoothScheme) hR₂.isProjectiveMorphism_left hq₁b hq₂b
  obtain ⟨-, hVv, hVsm, hg₁p, hg₁b⟩ := hres
  haveI : AlgebraicGeometry.IsVariety ℂ (g₁ ≫ q₁ ≫ sY) := hVv
  haveI : IsIntegral V := hVv.toIsIntegral
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hVsm
  haveI : QuasiCompact (g₁ ≫ q₁ ≫ sY) := hVv.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ q₁ ≫ sY)
  have hVn : IsNormalVariety ℂ (g₁ ≫ q₁ ≫ sY) := ⟨hVv, inferInstance⟩
  haveI := isProper_of_isProjectiveMorphism g₁ hg₁p
  haveI : IsDominant g₁ := hg₁b.isDominant
  haveI : IsDominant g₂ := hg₂b.isDominant
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hVn
  -- the three morphisms out of `V`
  have has : (g₁ ≫ p₁) ≫ sX = g₁ ≫ q₁ ≫ sY := by
    rw [Category.assoc, hR₁.comp_eq_left, hR₁.comp_eq_right]
  have hbs : (g₂ ≫ q₂) ≫ sY = g₁ ≫ q₁ ≫ sY := by rw [← hg, Category.assoc]
  have hcs : (g₂ ≫ r₂) ≫ sY' = g₁ ≫ q₁ ≫ sY := by
    rw [Category.assoc, hR₂.comp_eq_right, ← hR₂.comp_eq_left, ← Category.assoc g₂ q₂ sY, ← hg,
      Category.assoc]
  have hVa : IsNormalVariety ℂ ((g₁ ≫ p₁) ≫ sX) := by rw [has]; exact hVn
  have hVb : IsNormalVariety ℂ ((g₂ ≫ q₂) ≫ sY) := by rw [hbs]; exact hVn
  have hVc : IsNormalVariety ℂ ((g₂ ≫ r₂) ≫ sY') := by rw [hcs]; exact hVn
  have hab : IsBirationalMorphism (g₁ ≫ p₁) := isBirationalMorphism_comp' hg₁b hp₁b
  have hbb : IsBirationalMorphism (g₂ ≫ q₂) := isBirationalMorphism_comp' hg₂b hq₂b
  have hcb : IsBirationalMorphism (g₂ ≫ r₂) := isBirationalMorphism_comp' hg₂b hr₂b
  haveI : IsDominant (g₁ ≫ p₁) := hab.isDominant
  haveI : IsDominant (g₂ ≫ q₂) := hbb.isDominant
  haveI : IsDominant (g₂ ≫ r₂) := hcb.isDominant
  have hVp : MMP.Mori.IsProjectiveVariety ℂ (g₁ ≫ q₁ ≫ sY) := by
    rw [← has]
    exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr
      ⟨hVa.1, IsProjectiveMorphism.comp (IsProjectiveMorphism.comp hg₁p
        hR₁.isProjectiveMorphism_left) hX.2⟩
  have ha_proj : IsProjectiveMorphism (g₁ ≫ p₁) :=
    IsProjectiveMorphism.comp hg₁p hR₁.isProjectiveMorphism_left
  have hc_proj : IsProjectiveMorphism (g₂ ≫ r₂) :=
    IsProjectiveMorphism.of_comp (g₂ ≫ r₂) sY' (by rw [hcs]; exact hVp.2)
  haveI : IsProper (g₁ ≫ p₁) := isProper_of_isProjectiveMorphism _ ha_proj
  haveI : IsProper (g₂ ≫ r₂) := isProper_of_isProjectiveMorphism _ hc_proj
  haveI : IsSeparated g₁ := IsSeparated.of_comp g₁ (W₁ ↘ ⊤_ Scheme)
  haveI : IsSeparated g₂ := IsSeparated.of_comp g₂ (W₂ ↘ ⊤_ Scheme)
  -- inverses and the three rational maps
  obtain ⟨ha, hainv⟩ := hab.exists_isInverse
  obtain ⟨hb, hbinv⟩ := hbb.exists_isInverse
  have hφV : ha.compHom (g₂ ≫ q₂) = φ := by
    rw [← hg, hR₁.isInverse.compHom_comp_eq hainv q₁,
      hR₁.compHom_eq]
  have hψV : hb.compHom (g₂ ≫ r₂) = ψ := by
    rw [hR₂.isInverse.compHom_comp_eq hbinv r₂, hR₂.compHom_eq]
  haveI := hab.isIso_specFunctionFieldMap
  have e1 : specFunctionFieldMap (g₁ ≫ p₁) ≫ χ.fromFunctionField =
      specFunctionFieldMap (g₂ ≫ q₂) ≫ ψ.fromFunctionField := by
    rw [specFunctionFieldMap_comp g₁ p₁, Category.assoc, hχ, ← Category.assoc,
      ← specFunctionFieldMap_comp g₁ q₁,
      specFunctionFieldMap_congr hg]
  have hχV : ha.compHom (g₂ ≫ r₂) = χ := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [← cancel_epi (specFunctionFieldMap (g₁ ≫ p₁)),
      hainv.specFunctionFieldMap_comp_fromFunctionField_compHom, e1,
      ← hψV, hbinv.specFunctionFieldMap_comp_fromFunctionField_compHom]
  have hψVe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (hb.compHom (g₂ ≫ r₂)) F := by
    rw [hψV]; exact hψe
  have hφVe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ha.compHom (g₂ ≫ q₂)) F := by
    rw [hφV]; exact hφe
  have hχVe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional (ha.compHom (g₂ ≫ r₂)) F :=
    not_isInverseExceptional_compHom hXn hYn hY'n hVa hVb hab hbb hcb hainv hbinv hφVe hψVe
  have hχe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional χ F := by
    rw [← hχV]; exact hχVe
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      RationalMap.transformDivisor χ D =
        RationalMap.transformDivisor ψ (RationalMap.transformDivisor φ D) := fun D => by
    rw [← hχV, ← hψV, ← hφV]
    exact transformDivisor_compHom_eq_transformDivisor hXn hYn hY'n hVa hVb hab hbb hcb hainv
      hbinv hψVe D
  have hbind : ∀ P, RationalMap.transformPrimeDivisor χ P =
      (RationalMap.transformPrimeDivisor φ P).bind (RationalMap.transformPrimeDivisor ψ) :=
    fun P => by
      rw [← hχV, ← hψV, ← hφV]
      exact transformPrimeDivisor_compHom_eq_bind hXn hYn hY'n hVa hVb hab hbb hcb hainv hbinv
        hψVe P
  have htrB : RationalMap.transformDivisor χ B =
      RationalMap.transformDivisor ψ (RationalMap.transformDivisor φ B) := htr B
  -- the map `χ` is birational and lies over `Z`
  have hχb : RationalMap.IsBirational χ := by
    rw [← hχV]; exact hainv.isBirational_compHom hcb
  have hpq₁ : p₁ ≫ π = q₁ ≫ πY :=
    MMP.Fourfold.comp_eq_comp_of_isOver π πY hφo p₁ q₁ h₁ hR₁.isInverse hR₁.compHom_eq
  have hpq₂ : q₂ ≫ πY = r₂ ≫ πY' :=
    MMP.Fourfold.comp_eq_comp_of_isOver πY πY' hψ.isOver q₂ r₂ h₂ hR₂.isInverse hR₂.compHom_eq
  have hpq : (g₁ ≫ p₁) ≫ π = (g₂ ≫ r₂) ≫ πY' := by
    rw [Category.assoc, hpq₁, ← Category.assoc g₁, hg, Category.assoc g₂ q₂ πY, hpq₂,
      Category.assoc]
  have hχo : MMP.Flips.RationalMap.IsOver π πY' χ := by
    change χ.compHom πY' = π.toRationalMap
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [MMP.Flips.RationalMap.fromFunctionField_compHom,
      MMP.Flips.RationalMap.fromFunctionField_hom, ← cancel_epi (specFunctionFieldMap (g₁ ≫ p₁))]
    calc specFunctionFieldMap (g₁ ≫ p₁) ≫ χ.fromFunctionField ≫ πY'
        = (specFunctionFieldMap (g₁ ≫ p₁) ≫ (ha.compHom (g₂ ≫ r₂)).fromFunctionField) ≫
            πY' := by
          rw [hχV, Category.assoc]
      _ = V.fromSpecStalk (genericPoint V) ≫ (g₁ ≫ p₁) ≫ π := by
          rw [hainv.specFunctionFieldMap_comp_fromFunctionField_compHom, Category.assoc, hpq]
      _ = specFunctionFieldMap (g₁ ≫ p₁) ≫ X.fromSpecStalk (genericPoint X) ≫ π := by
          rw [specFunctionFieldMap_comp_fromSpecStalk_assoc (g₁ ≫ p₁)]
  -- canonical divisors
  obtain ⟨m, hm⟩ := hKX
  haveI : LocallyOfFiniteType ((g₁ ≫ p₁) ≫ sX) := hVa.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ ((g₁ ≫ p₁) ≫ sX) := hVa.1
  have hdimV : topologicalKrullDim V = m := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX ((g₁ ≫ p₁) ≫ sX)
      hab]
    exact hm.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety ((g₁ ≫ p₁) ≫ sX) hVa hdimV
  obtain ⟨KV, hKV, hKVX⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hVa hab hm hK₀
  obtain ⟨n₁, KW₁, hKW₁, hKW₁X, hKW₁Y⟩ := hR₁.exists_canonicalDivisor
  have hKY : KY = RationalMap.transformDivisor φ KX := by
    rw [← hKW₁Y, ← hKW₁X, ← hR₁.compHom_eq, transformDivisor_compHom_transformDivisor hXn hYn hW₁p
      hp₁b hq₁b hR₁.isInverse (hR₁.compHom_eq ▸ hφe) KW₁]
  obtain ⟨n₂, KW₂, hKW₂, hKW₂Y, hKW₂Y'⟩ := hR₂.exists_canonicalDivisor
  have hKY' : KY' = RationalMap.transformDivisor ψ KY := by
    rw [← hKW₂Y', ← hKW₂Y, ← hR₂.compHom_eq, transformDivisor_compHom_transformDivisor hYn hY'n
      hW₂q hq₂b hr₂b hR₂.isInverse (hR₂.compHom_eq ▸ hψe) KW₂]
  have hKY'χ : KY' = RationalMap.transformDivisor χ KX := by rw [hKY', hKY, htr]
  have hcKV : RationalMap.transformDivisor (X := V) (g₂ ≫ r₂).toRationalMap KV = KY' := by
    rw [hKY'χ, ← hKVX, ← hχV, transformDivisor_compHom_transformDivisor hXn hY'n hVa hab hcb hainv
      hχVe KV]
  -- pull-backs of the adjoints to `V`
  obtain ⟨GXV, hGXV₁, -⟩ :=
    MMP.Flips.existsUnique_isRCartierPullback g₁ (isCartierCombination_of_isRCartierPullback' hGX₁)
  have hGXV := MMP.Flips.IsRCartierPullback.comp hGX₁ hGXV₁
  obtain ⟨GYV, hGYV₁, -⟩ :=
    MMP.Flips.existsUnique_isRCartierPullback g₁ (isCartierCombination_of_isRCartierPullback' hGY₁)
  have hGYV := MMP.Flips.IsRCartierPullback.comp hGY₁ hGYV₁
  obtain ⟨GYV₂, hGYV₂₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₂
    (isCartierCombination_of_isRCartierPullback' hR₂.isRCartierPullback_left)
  have hGYV₂ := MMP.Flips.IsRCartierPullback.comp hR₂.isRCartierPullback_left hGYV₂₂
  have hYY : GYV₂ = GYV := MMP.Flips.IsRCartierPullback.eq (g₂ ≫ q₂) hGYV₂ (hg ▸ hGYV)
  obtain ⟨GY'V, hGY'V₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback g₂
    (isCartierCombination_of_isRCartierPullback' hR₂.isRCartierPullback_right)
  have hGY'V := MMP.Flips.IsRCartierPullback.comp hR₂.isRCartierPullback_right hGY'V₂
  -- the comparison for `ψ`, pulled back to `V`, is effective
  have hYY'eff : ∀ E, 0 ≤ (GYV - GY'V).coeff E := by
    have h1 := isRCartierPullback_smul_add_smul hGYV₂₂ hGY'V₂ 1 (-1)
    have h0 : (0 : RDivisor W₂) ≤ (1 : ℝ) • GY₂ + (-1 : ℝ) • GY'₂ := by
      rw [Finsupp.le_def]
      intro P
      have := hR₂.effective P
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply] at this
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul]
      linarith
    have h2 := (MMP.Fourfold.isEffective_of_isRCartierPullback g₂
      (isRCartier_of_isSmoothScheme hR₂.isSmoothScheme _) h0).2 _ h1
    intro E
    have h3 := Finsupp.le_def.1 h2 E
    rw [hYY] at h3
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul] at h3
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply]
    linarith
  -- coefficients along strict transforms of prime divisors of `X`
  have key : ∀ (P : MMP.Mori.PrimeDivisor X) (PV : MMP.Mori.PrimeDivisor V),
      (g₁ ≫ p₁) PV.genericPoint = P.genericPoint →
        0 ≤ (GXV - GY'V).coeff PV ∧
          (RationalMap.IsExceptional χ P → 0 < (GXV - GY'V).coeff PV) := by
    intro P PV hPV
    obtain ⟨P₁, hP₁, hP₁iso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hW₁p hp₁b P
    have hgP : g₁ PV.genericPoint = P₁.genericPoint :=
      eq_of_map_eq_genericPoint p₁ hp₁b.functionFieldMap_bijective
        (by rw [← Scheme.Hom.comp_apply]; exact hPV) hP₁
    haveI : IsIso (g₁.stalkMap PV.genericPoint) :=
      isIso_stalkMap_of_map_eq_genericPoint g₁ hg₁b.functionFieldMap_bijective hgP
    have c1 : GXV PV = GX₁ P₁ := coeff_eq_of_isRCartierPullback hGXV₁ PV P₁ hgP
    have c2 : GYV PV = GY₁ P₁ := coeff_eq_of_isRCartierPullback hGYV₁ PV P₁ hgP
    have h₁P := transformPrimeDivisor_eq_some_of_isInverse hp₁b.functionFieldMap_bijective
      hR₁.isInverse hP₁
    have hφP : RationalMap.transformPrimeDivisor φ P =
        RationalMap.transformPrimeDivisor (X := W₁) q₁.toRationalMap P₁ := by
      rw [← hR₁.compHom_eq, transformPrimeDivisor_compHom h₁P q₁]
    have haP := transformPrimeDivisor_eq_some_of_isInverse hab.functionFieldMap_bijective hainv hPV
    have hχP : RationalMap.transformPrimeDivisor χ P =
        RationalMap.transformPrimeDivisor (X := V) (g₂ ≫ r₂).toRationalMap PV := by
      rw [← hχV, transformPrimeDivisor_compHom haP (g₂ ≫ r₂)]
    have hφPV : RationalMap.transformPrimeDivisor φ P =
        RationalMap.transformPrimeDivisor (X := V) (g₂ ≫ q₂).toRationalMap PV := by
      rw [← hφV, transformPrimeDivisor_compHom haP (g₂ ≫ q₂)]
    have hsplit : (GXV - GY'V).coeff PV = (GX₁ - GY₁).coeff P₁ + (GYV - GY'V).coeff PV := by
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, c1, c2]
      ring
    have h2 := hYY'eff PV
    rcases hQ : RationalMap.transformPrimeDivisor φ P with _ | Q
    · -- `φ` contracts `P`
      have hexφ : RationalMap.IsExceptional φ P := by
        rw [← hR₁.compHom_eq, isExceptional_compHom_iff h₁P q₁]
        exact isExceptional_of_transformPrimeDivisor_eq_none q₁ hq₁b.functionFieldMap_bijective
          (hφP ▸ hQ)
      have h1 := hpos P hexφ P₁ h₁P
      rw [hsplit]
      exact ⟨by linarith, fun _ => by linarith⟩
    · -- `φ` sends `P` to `Q`; the comparison for `φ` vanishes there
      have hq₁Q := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q₁ P₁ Q).1
        (hφP ▸ hQ)
      haveI : IsIso (q₁.stalkMap P₁.genericPoint) :=
        isIso_stalkMap_of_map_eq_genericPoint q₁ hq₁b.functionFieldMap_bijective hq₁Q
      haveI := hP₁iso
      have e1 : GX₁ P₁ = (logCanonicalDivisor KX B) P :=
        coeff_eq_of_isRCartierPullback hGX₁ P₁ P hP₁
      have e2 : GY₁ P₁ = (logCanonicalDivisor KY (RationalMap.transformDivisor φ B)) Q :=
        coeff_eq_of_isRCartierPullback hGY₁ P₁ Q hq₁Q
      have hφQ : RationalMap.transformPrimeDivisor (h₁.compHom q₁) P = some Q := by
        rw [hR₁.compHom_eq]; exact hQ
      have e3 : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
          RationalMap.transformDivisor φ D Q = D P := fun D => by
        rw [← hR₁.compHom_eq]
        exact transformDivisor_compHom_apply_of_eq_some hXn hYn hW₁p hp₁b hq₁b hR₁.isInverse
          hφQ D
      have hzero : (GX₁ - GY₁).coeff P₁ = 0 := by
        simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, e1, e2, logCanonicalDivisor,
          Finsupp.add_apply]
        rw [hKY]
        change ((KX P : ℤ) : ℝ) + B P - (((RationalMap.transformDivisor φ KX Q : ℤ) : ℝ) +
          RationalMap.transformDivisor φ B Q) = 0
        rw [e3, e3]
        ring
      rw [hsplit, hzero, zero_add]
      refine ⟨h2, fun hexχ => ?_⟩
      -- `ψ` contracts `Q`
      have hcPV : RationalMap.transformPrimeDivisor (X := V) (g₂ ≫ r₂).toRationalMap PV = none := by
        refine transformPrimeDivisor_eq_none_of_isExceptional _ ?_
        rw [← isExceptional_compHom_iff haP (g₂ ≫ r₂), hχV]
        exact hexχ
      have hψQ : RationalMap.transformPrimeDivisor ψ Q = none := by
        rw [← hcPV, ← hχP, hbind, hQ, Option.bind_some]
      obtain ⟨Q₂, hQ₂, -, -⟩ :=
        MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn hW₂q hq₂b Q
      have h₂Q := transformPrimeDivisor_eq_some_of_isInverse hq₂b.functionFieldMap_bijective
        hR₂.isInverse hQ₂
      have hexψ : RationalMap.IsExceptional ψ Q := by
        rw [← hR₂.compHom_eq, isExceptional_compHom_iff h₂Q r₂]
        refine isExceptional_of_transformPrimeDivisor_eq_none r₂ hr₂b.functionFieldMap_bijective ?_
        rw [← transformPrimeDivisor_compHom h₂Q r₂, hR₂.compHom_eq]
        exact hψQ
      have h3 := hpos₂ Q hexψ Q₂ h₂Q
      -- transport along `g₂`
      have hbPV := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (g₂ ≫ q₂) PV
        Q).1 (by rw [← hφPV]; exact hQ)
      have hgQ : g₂ PV.genericPoint = Q₂.genericPoint :=
        eq_of_map_eq_genericPoint q₂ hq₂b.functionFieldMap_bijective
          (by rw [← Scheme.Hom.comp_apply]; exact hbPV) hQ₂
      haveI : IsIso (g₂.stalkMap PV.genericPoint) :=
        isIso_stalkMap_of_map_eq_genericPoint g₂ hg₂b.functionFieldMap_bijective hgQ
      have c3 : GYV₂ PV = GY₂ Q₂ := coeff_eq_of_isRCartierPullback hGYV₂₂ PV Q₂ hgQ
      have c4 : GY'V PV = GY'₂ Q₂ := coeff_eq_of_isRCartierPullback hGY'V₂ PV Q₂ hgQ
      rw [hYY] at c3
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply] at h3 ⊢
      rw [c3, c4]
      exact h3
  -- the comparison for `χ` on `V`
  have hDX := isCartierCombination_of_isQFactorial hXq (logCanonicalDivisor KX B)
  have hpush : 0 ≤ RationalMap.transformDivisor (X := V) (g₁ ≫ p₁).toRationalMap (GXV - GY'V) := by
    rw [Finsupp.le_def]
    intro P
    obtain ⟨PV, hPV, -, htrP⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVa hab P
    rw [Finsupp.coe_zero, Pi.zero_apply, htrP]
    have := (key P PV hPV).1
    simpa only [DivisorWithCoeffs.coeff_apply] using this
  have heff : 0 ≤ GXV - GY'V := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (k := ℂ)
    (g₁ ≫ q₁ ≫ sY) sX sY' hVn hVp hXn hX hY'n hψ.isProjectiveVariety_model π πY' (g₁ ≫ p₁)
    (g₂ ≫ r₂) has hcs hpq ha_proj hab hc_proj hcb hDX hψ.isRelativelyNef hGXV hGY'V hpush
  have hres : IsLogComparisonResolution sX sY' (g₁ ≫ q₁ ≫ sY) χ KX B KY'
      (RationalMap.transformDivisor χ B) (g₁ ≫ p₁) (g₂ ≫ r₂) ha GXV GY'V :=
    { isVariety := hVv
      isSmoothScheme := hVsm
      comp_eq_left := has
      comp_eq_right := hcs
      isProjectiveMorphism_left := ha_proj
      isProjectiveMorphism_right := hc_proj
      isBirationalMorphism_left := hab
      isBirationalMorphism_right := hcb
      isInverse := hainv
      compHom_eq := hχV
      exists_canonicalDivisor := ⟨m, KV, by rw [← has]; exact hKV, hKVX, hcKV⟩
      isRCartierPullback_left := hGXV
      isRCartierPullback_right := by rw [htrB]; exact hGY'V
      effective := fun E => by
        have := Finsupp.le_def.1 heff E
        simpa only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_zero, Pi.zero_apply] using this
      isExceptional := fun E hE => by
        by_contra hne
        obtain ⟨F, hcF, hFiso, -⟩ :=
          MMP.Fourfold.exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor hY'n
            (g₂ ≫ r₂) hVc hcb E hne
        obtain ⟨P, hP⟩ : ∃ P, RationalMap.transformPrimeDivisor χ P = some F := by
          by_contra h0
          push Not at h0
          exact hχe F h0
        obtain ⟨PV, hPV, hPViso, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hVa hab P
        have haP := transformPrimeDivisor_eq_some_of_isInverse hab.functionFieldMap_bijective
          hainv hPV
        have hcP : RationalMap.transformPrimeDivisor (X := V) (g₂ ≫ r₂).toRationalMap PV =
            some F := by
          rw [← transformPrimeDivisor_compHom haP (g₂ ≫ r₂), hχV]; exact hP
        have hEPV : E = PV := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_map_eq_genericPoint (g₂ ≫ r₂) hcb.functionFieldMap_bijective hcF
            ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ PV F).1 hcP))
        subst hEPV
        haveI := hFiso
        haveI := hPViso
        have e1 : GXV E = (logCanonicalDivisor KX B) P :=
          coeff_eq_of_isRCartierPullback hGXV E P hPV
        have e2 : GY'V E = (logCanonicalDivisor KY'
            (RationalMap.transformDivisor ψ (RationalMap.transformDivisor φ B))) F :=
          coeff_eq_of_isRCartierPullback hGY'V E F hcF
        have hχF : RationalMap.transformPrimeDivisor (ha.compHom (g₂ ≫ r₂)) P = some F := by
          rw [hχV]; exact hP
        have e3 : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
            RationalMap.transformDivisor χ D F = D P := fun D => by
          rw [← hχV]
          exact transformDivisor_compHom_apply_of_eq_some hXn hY'n hVa hab hcb hainv hχF D
        apply hE
        simp only [DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, e1, e2, logCanonicalDivisor,
          Finsupp.add_apply]
        rw [hKY'χ, ← htrB]
        change ((KX P : ℤ) : ℝ) + B P - (((RationalMap.transformDivisor χ KX F : ℤ) : ℝ) +
          RationalMap.transformDivisor χ B F) = 0
        rw [e3, e3]
        ring }
  refine ⟨{ isRealLcPair := ⟨hXn, hB0, hBklt.2.2.1, fun n E a ha => (hBklt.2.2.2 n E a ha).le⟩
            isCanonicalDivisor := ⟨m, hm⟩
            comp_eq := hπ
            isNormalVariety_model := hY'n
            isCanonicalDivisor_model := hψ.isCanonicalDivisor_model
            isProjectiveVariety_model := hψ.isProjectiveVariety_model
            comp_eq_model := hψ.comp_eq_model
            isQFactorial := hψ.isQFactorial
            isRealDltPair := by rw [htrB]; exact hψ.isRealDltPair
            isBirational := hχb
            isOver := hχo
            coeff_boundary := fun F => by rw [if_neg (hχe F), add_zero]
            isRelativelyNef := by rw [htrB]; exact hψ.isRelativelyNef
            exists_resolution := ⟨V, inferInstance, inferInstance, inferInstance, _, _, _, ha, _, _,
              hres⟩
            exists_resolution_pos := ⟨V, inferInstance, inferInstance, inferInstance, _, _, _, ha,
              _, _, hres, fun P hP P' hP' => (key P P'
                (map_genericPoint_of_transformPrimeDivisor_eq_some hainv hP')).2 hP⟩ },
    by rw [htrB]; exact hψklt⟩

end CompositeModel

/-! ### Pushing pseudo-effectivity forward along a birational contraction -/

section PsefPushforward

open MMP.Mori MMP.Intersection

section WeilR

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {π : X ⟶ Z}

/-- The degree of `𝒪_X(A)` along a proper curve is the degree of the Weil divisor of `A`. -/
private theorem degree_sheaf_eq_degreeOn [QuasiCompact sX] (C : ProperCurve sX)
    {A : X.CartierDivisor} {w : Divisor X} (hA : IsWeilDivisorOfCartier A w) :
    C.degree ℂ (MMP.CartierDivisor.sheaf A) =
      w.degreeOn ℂ sX C.ι C.dim_le hA.isCartier := by
  obtain ⟨e⟩ := hA.nonempty_sheaf_iso_divisorialSheaf
  haveI := hA.isCartier.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e

/-- The Weil `ℝ`-divisor `∑ c_A [A]` of an `ℝ`-Cartier divisor `∑ c_A A`, for a choice `w` of the
Weil divisors of Cartier divisors. -/
private noncomputable abbrev weilR (w : X.CartierDivisor → Divisor X) :
    KCartierDivisor ℝ X →ₗ[ℝ] RDivisor X :=
  Finsupp.linearCombination ℝ fun A => Divisor.toRDivisor (w A)

private theorem weilR_eq_sum (w : X.CartierDivisor → Divisor X) (D : KCartierDivisor ℝ X) :
    weilR w D = ∑ i : Fin D.support.card, D (D.support.equivFin.symm i) •
      Divisor.toRDivisor (w (D.support.equivFin.symm i)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_coe_sort D.support _).symm.trans (Equiv.sum_comp D.support.equivFin.symm
    (fun A : D.support => D A • Divisor.toRDivisor (w A))).symm

private theorem coeff_weilR {w : X.CartierDivisor → Divisor X}
    (hw : ∀ A, IsWeilDivisorOfCartier A (w A)) (D : KCartierDivisor ℝ X)
    (P : MMP.Mori.PrimeDivisor X) : (weilR w D).coeff P = weil D P := by
  rw [weil_apply, Finsupp.linearCombination_apply, DivisorWithCoeffs.coeff_apply, Finsupp.sum,
    Finsupp.finset_sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, ← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toRDivisor,
    ← (hw A P).primeDivisorOrder_eq]

/-- `D · C = ∑ c_A deg_C 𝒪_X(A)` through the Weil divisors of the `A`. -/
private theorem relativeDegreeMap_eq_sum [QuasiCompact sX] {w : X.CartierDivisor → Divisor X}
    (hw : ∀ A, IsWeilDivisorOfCartier A (w A)) (D : KCartierDivisor ℝ X)
    (C : {C : ProperCurve sX // C.IsContractedBy π}) :
    MMP.Fourfold.relativeDegreeMap sX π D C = ∑ i : Fin D.support.card,
      D (D.support.equivFin.symm i) * ((w (D.support.equivFin.symm i)).degreeOn ℂ sX C.1.ι
        C.1.dim_le (hw _).isCartier : ℝ) := by
  have hC : MMP.Fourfold.relativeDegreeMap sX π D C =
      ∑ E : D.support, D E * (C.1.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) := by
    rw [Finset.sum_coe_sort D.support
      (fun E => D E * (C.1.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ))]
    simp [MMP.Fourfold.relativeDegreeMap, OneCycle.intersectionPairing,
      Finsupp.linearCombination_apply, OneCycle.cartierDegree, OneCycle.degree_apply,
      ProperCurve.cycle, Finsupp.sum]
  rw [hC]
  refine (Equiv.sum_comp D.support.equivFin.symm (fun E : D.support =>
    D E * (C.1.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ))).symm.trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [degree_sheaf_eq_degreeOn C.1 (hw _)]

/-- A multiple of the Weil divisor of a numerically trivial `ℝ`-Cartier divisor is nef. -/
private theorem isRelativelyNef_smul_weilR_of_mem_ker [QuasiCompact sX]
    {w : X.CartierDivisor → Divisor X} (hw : ∀ A, IsWeilDivisorOfCartier A (w A))
    {D : KCartierDivisor ℝ X} (hD : D ∈ LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π))
    (c : ℝ) : IsRelativelyNef ℂ sX π (c • weilR w D) := by
  have hpres : c • weilR w D = ∑ i : Fin D.support.card, (c * D (D.support.equivFin.symm i)) •
      Divisor.toRDivisor (w (D.support.equivFin.symm i)) := by
    rw [weilR_eq_sum, Finset.smul_sum]
    simp only [smul_smul]
  refine ⟨D.support.card, fun i => c * D (D.support.equivFin.symm i),
    fun i => w (D.support.equivFin.symm i), fun i => (hw _).isCartier, hpres,
    fun C hC x hx => ?_⟩
  have hx' := MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C
    (fun i => c * D (D.support.equivFin.symm i)) (fun i => w (D.support.equivFin.symm i))
    (fun i => (hw _).isCartier) hpres hx
  have h0 := congrFun (LinearMap.mem_ker.1 hD) ⟨C, hC⟩
  rw [relativeDegreeMap_eq_sum hw, Pi.zero_apply] at h0
  rw [hx']
  simp only [mul_assoc]
  rw [← Finset.mul_sum, h0, mul_zero]

/-- The degrees of an `ℝ`-Cartier divisor with nef Weil divisor are nonnegative. -/
private theorem relativeDegreeMap_nonneg_of_isRelativelyNef [QuasiCompact sX]
    {w : X.CartierDivisor → Divisor X} (hw : ∀ A, IsWeilDivisorOfCartier A (w A))
    {D : KCartierDivisor ℝ X} (hnef : IsRelativelyNef ℂ sX π (weilR w D))
    (C : {C : ProperCurve sX // C.IsContractedBy π}) :
    0 ≤ MMP.Fourfold.relativeDegreeMap sX π D C := by
  obtain ⟨m₀, r₀, L₀, hL₀, hR₀, hnn⟩ := hnef
  have hx₀ := MMP.Flips.isRIntersectionNumber_sum_degreeOn ℂ sX C.1 r₀ L₀ hL₀
  rw [← hR₀] at hx₀
  have h1 := hnn C.1 C.2 _ hx₀
  have h2 := MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C.1
    (fun i => D (D.support.equivFin.symm i)) (fun i => w (D.support.equivFin.symm i))
    (fun i => (hw _).isCartier) (weilR_eq_sum w D) hx₀
  rw [relativeDegreeMap_eq_sum hw, ← h2]
  exact h1

/-- An `ℝ`-Cartier divisor whose Weil divisor and its negative are nef is numerically trivial. -/
private theorem mem_ker_of_isRelativelyNef [QuasiCompact sX]
    {w : X.CartierDivisor → Divisor X} (hw : ∀ A, IsWeilDivisorOfCartier A (w A))
    {D : KCartierDivisor ℝ X} (h₁ : IsRelativelyNef ℂ sX π (weilR w D))
    (h₂ : IsRelativelyNef ℂ sX π (-weilR w D)) :
    D ∈ LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π) := by
  rw [LinearMap.mem_ker]
  funext C
  have e1 := relativeDegreeMap_nonneg_of_isRelativelyNef hw h₁ C
  have e2 := relativeDegreeMap_nonneg_of_isRelativelyNef hw (D := -D) (by rwa [map_neg]) C
  rw [map_neg, Pi.neg_apply] at e2
  rw [Pi.zero_apply]
  linarith

end WeilR

section Hartogs

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

open MMP.CartierDivisorSheaf in
/-- **Effective Weil divisors of Cartier divisors are effective**, on a normal scheme: a local
equation `a / b` at a point `x` has `ord_Γ(a) ≥ ord_Γ(b)` along every prime divisor `Γ` through
`x`, so `a / b` is regular at `x` by algebraic Hartogs. -/
private theorem isEffective_of_isWeilDivisorOfCartier {A : X.CartierDivisor} {w : Divisor X}
    (hA : IsWeilDivisorOfCartier A w) (hw : ∀ P, 0 ≤ w.coeff P) :
    MMP.Intersection.IsEffective A := by
  intro x
  obtain ⟨f, hf⟩ := MMP.Intersection.exists_isLocalEquationAt A x
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set alg := algebraMap (X.presheaf.stalk x) X.functionField
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have ha' : alg a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  have hb' : alg b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  obtain ⟨c, hc⟩ : ∃ c, alg c = alg a / alg b := by
    refine MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x
      (div_ne_zero ha' hb') fun Γ hΓ => ?_
    have hspec : Γ.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
      exact specializes_iff_mem_closure.mpr hΓ
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Γ
    have hsa := MMP.Intersection.stalkSpecializes_ne_zero hspec ha0
    have hsb := MMP.Intersection.stalkSpecializes_ne_zero hspec hb0
    rw [div_eq_mul_inv, Scheme.ord_mul ha' (inv_ne_zero hb')]
    have hinv := MMP.Mori.ord_zpow Γ.genericPoint hb' (-1)
    rw [zpow_neg, zpow_one] at hinv
    rw [hinv, ← MMP.Mori.algebraMap_stalkSpecializes hspec a,
      ← MMP.Mori.algebraMap_stalkSpecializes hspec b, ord_algebraMap_stalk h1 hsa,
      ord_algebraMap_stalk h1 hsb]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk Γ.genericPoint) :=
      krullDimLE_of_coheight_le h1.le
    have e := hA.ord_sub_ord_eq_coeff h1 (hf.stalkSpecializes hspec)
      (mem_nonZeroDivisors_of_ne_zero hsa) (mem_nonZeroDivisors_of_ne_zero hsb)
      (hab.stalkSpecializes hspec)
    have hΓ' : AlgebraicGeometry.PrimeDivisor.ofCoheightOne Γ.genericPoint h1 = Γ :=
      ((Γ.eq_ofCoheightOne_iff h1).mpr rfl).symm
    rw [hΓ'] at e
    have := hw Γ
    linarith
  have hbc : b * c = a := hinj (by
    rw [map_mul, hc, mul_div_cancel₀ _ hb'])
  have hfc : f = stalkToTotalQuotient x c := by
    apply hab.1.mul_left_cancel
    rw [hab.2, ← map_mul, hbc]
  rw [hfc] at hf
  obtain ⟨U, hxU, hU⟩ := hf.exists_isEffectiveOn
  exact ⟨U, hxU, hU⟩

end Hartogs

section Transport

variable {X Y Z W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
  [LocallyOfFiniteType sY] {sZ : Z ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
  {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}

/-- **Numerically trivial divisors push forward to numerically trivial divisors.** Let `φ` be a
birational contraction over `Z` of projective `ℚ`-factorial varieties with a common resolution
`p`, `q`. If `D` and `-D` are nef over `Z`, so is `φ_* D`: by the negativity lemma in both signs
`p^* D = q^*(φ_* D)`, which is nef over `Z`, and nefness descends along `q`. -/
private theorem isRelativelyNef_transformDivisor_of_isRelativelyNef_neg
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hXq : IsQFactorial sX) (hYq : IsQFactorial sY) [IsSeparated (Z ↘ ⊤_ Scheme)]
    {φ : X.RationalMap Y} (hφo : MMP.Flips.RationalMap.IsOver π πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {B₀ : RDivisor X} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W} (hR : IsLogComparisonResolution sX sY sW φ KX B₀ KY BY p q h GX GY)
    {D : RDivisor X} (h₁ : IsRelativelyNef ℂ sX π D) (h₂ : IsRelativelyNef ℂ sX π (-D)) :
    IsRelativelyNef ℂ sY πY (RationalMap.transformDivisor φ D) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have := hXn.1
  have := hYn.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have hWv := hR.isVariety
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWn : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  have hWp' : IsNormalVariety ℂ (p ≫ sX) := by rw [hR.comp_eq_left]; exact hWn
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : Surjective q := surjective_of_isDominant_of_isClosed_range q q.isClosedMap.isClosed_range
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hWn
  haveI : IsSeparated p := IsSeparated.of_comp p (X ↘ ⊤_ Scheme)
  haveI : IsSeparated q := IsSeparated.of_comp q (Y ↘ ⊤_ Scheme)
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hWproj : MMP.Mori.IsProjectiveVariety ℂ sW := by
    rw [← hR.comp_eq_left]
    exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr
      ⟨hWp'.1, IsProjectiveMorphism.comp hR.isProjectiveMorphism_left hX.2⟩
  have hpq : p ≫ π = q ≫ πY :=
    MMP.Fourfold.comp_eq_comp_of_isOver π πY hφo p q h hR.isInverse hR.compHom_eq
  have hDX := isCartierCombination_of_isQFactorial hXq D
  have hDY := isCartierCombination_of_isQFactorial hYq (RationalMap.transformDivisor φ D)
  obtain ⟨GXD, hGXD, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p hDX
  obtain ⟨GYD, hGYD, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q hDY
  -- at the strict transform on `W` of every prime divisor of `Y`, the pull-backs agree
  have hkey : ∀ F : MMP.Mori.PrimeDivisor Y,
      RationalMap.transformDivisor (X := W) q.toRationalMap (GYD - GXD) F = 0 := by
    intro F
    obtain ⟨F', hF', hisoF, htrF⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hYn
        (by rw [hR.comp_eq_right]; exact hWn) hqb F
    rw [htrF]
    obtain ⟨P, hP⟩ : ∃ P, RationalMap.transformPrimeDivisor φ P = some F := by
      by_contra hne
      push Not at hne
      exact hφe F hne
    obtain ⟨P', hP', hisoP, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hXn hWp' hpb P
    have hhP := transformPrimeDivisor_eq_some_of_isInverse hpbij hR.isInverse hP'
    have hqP' : RationalMap.transformPrimeDivisor (X := W) q.toRationalMap P' = some F := by
      rw [← transformPrimeDivisor_compHom hhP q, hR.compHom_eq, hP]
    have hPF : P' = F' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_genericPoint q hqbij
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P' F).1 hqP') hF')
    subst hPF
    haveI := hisoF
    haveI := hisoP
    have hcY := coeff_eq_of_isRCartierPullback hGYD P' F hF'
    have hcX := coeff_eq_of_isRCartierPullback hGXD P' P hP'
    have hφF : RationalMap.transformPrimeDivisor (h.compHom q) P = some F := by
      rw [hR.compHom_eq]; exact hP
    have htrφ := transformDivisor_compHom_apply_of_eq_some hXn hYn hWp' hpb hqb hR.isInverse hφF D
    rw [hR.compHom_eq] at htrφ
    rw [Finsupp.sub_apply, hcY, hcX, htrφ, sub_self]
  have hn₁ := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (k := ℂ) sW sY sX hWn hWproj
    hYn hY hXn hX πY π q p hR.comp_eq_right hR.comp_eq_left hpq.symm
    hR.isProjectiveMorphism_right hqb hR.isProjectiveMorphism_left hpb hDY h₁ hGYD hGXD
    (by rw [Finsupp.le_def]; intro F; rw [hkey F]; rfl)
  have hGYD' : MMP.Flips.IsRCartierPullback q ((-1 : ℝ) • RationalMap.transformDivisor φ D)
      ((-1 : ℝ) • GYD) := by
    simpa using isRCartierPullback_smul_add_smul hGYD hGYD (-1) 0
  have hGXD' : MMP.Flips.IsRCartierPullback p (-D) ((-1 : ℝ) • GXD) := by
    simpa using isRCartierPullback_smul_add_smul hGXD hGXD (-1) 0
  have hn₂ := MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (k := ℂ) sW sY sX hWn hWproj
    hYn hY hXn hX πY π q p hR.comp_eq_right hR.comp_eq_left hpq.symm
    hR.isProjectiveMorphism_right hqb hR.isProjectiveMorphism_left hpb
    (isCartierCombination_of_isQFactorial hYq _) h₂ hGYD' hGXD' (by
      rw [Finsupp.le_def]
      intro F
      have := hkey F
      rw [map_sub, Finsupp.sub_apply] at this
      rw [← smul_sub, ← RationalMap.transformDivisorₗ_apply ℝ, map_smul,
        RationalMap.transformDivisorₗ_apply, map_sub]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, Finsupp.coe_zero,
        Pi.zero_apply]
      linarith)
  have hG : GXD = GYD := by
    refine Finsupp.ext fun P => le_antisymm ?_ ?_
    · have := Finsupp.le_def.1 hn₁ P
      simp only [Finsupp.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at this
      linarith
    · have := Finsupp.le_def.1 hn₂ P
      simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
        Pi.zero_apply] at this
      linarith
  have hps : p ≫ sX = sW := hR.comp_eq_left
  have hqs : q ≫ sY = sW := hR.comp_eq_right
  subst hps
  haveI : QuasiCompact (q ≫ sY) := by rw [hqs]; infer_instance
  have hnefW := MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (k := ℂ) (𝟙 Z) π (p ≫ π) p
    (by rw [Category.comp_id]) h₁ hGXD
  rw [hpq, hG] at hnefW
  exact MMP.Fourfold.IsRelativelyNef.of_isRCartierPullback_of_surjective (k := ℂ) q hqs πY hGYD
    hnefW

end Transport

section Pushforward

variable {X Y Z W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
  [LocallyOfFiniteType sY] {sZ : Z ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
  {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}

/-- The topology of `N¹(X/Z)` makes it a Hausdorff topological vector space. -/
private theorem relativeNumericalDivisorClasses_tvs {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ Z) :
    IsTopologicalAddGroup (MMP.Fourfold.RelativeNumericalDivisorClasses sX π) ∧
      ContinuousSMul ℝ (MMP.Fourfold.RelativeNumericalDivisorClasses sX π) ∧
      T2Space (MMP.Fourfold.RelativeNumericalDivisorClasses sX π) := by
  let ι := (LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π)).liftQ
    (MMP.Fourfold.relativeDegreeMap sX π) le_rfl
  refine ⟨topologicalAddGroup_induced ι, continuousSMul_induced ι,
    T2Space.of_injective_continuous ?_ continuous_induced_dom⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl

/-- **Pseudo-effectivity pushes forward along a birational contraction.** Let `φ : X ⤏ Y` be a
birational map over `Z` of normal projective `ℚ`-factorial varieties extracting no prime divisor,
with a common resolution comparing canonical divisors `K_X`, `K_Y`. If `K_X + B` is
pseudo-effective over `Z`, so is `K_Y + φ_* B`.

The transform of Weil divisors induces a linear map `N¹(X/Z) ⟶ N¹(Y/Z)`: numerically trivial
divisors have numerically trivial transforms, by the negativity lemma on the common resolution.
It is continuous, `N¹(X/Z)` being finite-dimensional, and it sends effective classes to effective
classes, since an effective Weil divisor on the `ℚ`-factorial normal variety `Y` has a multiple
which is an effective Cartier divisor. -/
private theorem isPsef_transformDivisor
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hXq : IsQFactorial sX) (hYq : IsQFactorial sY) [IsSeparated (Z ↘ ⊤_ Scheme)]
    {φ : X.RationalMap Y} (hφo : MMP.Flips.RationalMap.IsOver π πY φ)
    (hφe : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    {B₀ : RDivisor X} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W} (hR : IsLogComparisonResolution sX sY sW φ KX B₀ KY BY p q h GX GY)
    {B : RDivisor X} (hps : IsPsef sX π KX B) :
    IsPsef sY πY KY (RationalMap.transformDivisor φ B) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXq.1
  have hYn : IsNormalVariety ℂ sY := hYq.1
  have := hXn.1
  have := hYn.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  haveI : QuasiCompact sY := hYn.1.toQuasiCompact
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hYn
  have hWv := hR.isVariety
  haveI : QuasiCompact sW := hWv.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hWn : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  have hWp' : IsNormalVariety ℂ (p ≫ sX) := by rw [hR.comp_eq_left]; exact hWn
  haveI := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  haveI := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  -- every prime divisor of `Y` is the transform of exactly one of `X`
  have hpre : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ P, RationalMap.transformPrimeDivisor φ P = some F :=
    fun F => by
      by_contra hne
      push Not at hne
      exact hφe F hne
  have htrapp : ∀ {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y},
      RationalMap.transformPrimeDivisor φ P = some F → ∀ {R : Type} [AddCommMonoid R]
        (D : DivisorWithCoeffs R X), RationalMap.transformDivisor φ D F = D P :=
    fun {P F} hP {R} _ D => by
      have hφF : RationalMap.transformPrimeDivisor (h.compHom q) P = some F := by
        rw [hR.compHom_eq]; exact hP
      have := transformDivisor_compHom_apply_of_eq_some hXn hYn hWp' hpb hqb hR.isInverse hφF D
      rwa [hR.compHom_eq] at this
  -- `K_Y = φ_* K_X`
  obtain ⟨n, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hKY : KY = RationalMap.transformDivisor φ KX := by
    rw [← hKWY, ← hKWX, ← hR.compHom_eq, transformDivisor_compHom_transformDivisor hXn hYn hWp'
      hpb hqb hR.isInverse (hR.compHom_eq ▸ hφe) KW]
  -- Weil divisors of Cartier divisors on `X` and `Y`
  choose wX hwX using fun A : X.CartierDivisor => exists_isWeilDivisorOfCartier A
  choose wY hwY using fun A : Y.CartierDivisor => exists_isWeilDivisorOfCartier A
  -- every `ℝ`-divisor on `Y` is the Weil divisor of an `ℝ`-Cartier divisor
  have hsurj : Function.Surjective (weilR wY) := by
    intro R
    obtain ⟨m, r, L, hL, hcoeff⟩ := hYq.isRCartier R
    choose A hA using fun j => exists_isWeilDivisorOfCartier_of_isCartier (hL j)
    have hwA : ∀ j, wY (A j) = L j := fun j => Finsupp.ext fun P =>
      ((hwY (A j) P).unique (hA j P))
    refine ⟨∑ j, Finsupp.single (A j) (r j), ?_⟩
    rw [map_sum]
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.linearCombination_single, hwA]
    have := hcoeff P
    rw [DivisorWithCoeffs.coeff_apply] at this
    rw [this, Finsupp.finset_sum_apply]
    rfl
  -- a linear lift of the transform of Weil divisors
  let T₀ : KCartierDivisor ℝ X →ₗ[ℝ] RDivisor Y := RationalMap.transformDivisorₗ ℝ φ ∘ₗ weilR wX
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property (weilR wY) T₀ hsurj
  have hℓD : ∀ D, weilR wY (ℓ D) = RationalMap.transformDivisor φ (weilR wX D) := fun D =>
    LinearMap.congr_fun hℓ D
  -- numerically trivial classes go to numerically trivial classes
  have hker : LinearMap.ker (MMP.Fourfold.relativeDegreeMap sX π) ≤
      (LinearMap.ker (MMP.Fourfold.relativeDegreeMap sY πY)).comap ℓ := by
    intro D hD
    rw [Submodule.mem_comap]
    have h₁ := isRelativelyNef_smul_weilR_of_mem_ker hwX hD 1
    have h₂ := isRelativelyNef_smul_weilR_of_mem_ker hwX hD (-1)
    rw [one_smul] at h₁
    rw [neg_one_smul] at h₂
    have k₁ := isRelativelyNef_transformDivisor_of_isRelativelyNef_neg hX hY hXq hYq hφo hφe hR h₁
      h₂
    have k₂ := isRelativelyNef_transformDivisor_of_isRelativelyNef_neg hX hY hXq hYq hφo hφe hR h₂
      (by rw [neg_neg]; exact h₁)
    rw [← hℓD] at k₁
    rw [map_neg, ← hℓD] at k₂
    exact mem_ker_of_isRelativelyNef hwY k₁ k₂
  let Φ := Submodule.mapQ _ _ ℓ hker
  have hΦ : ∀ D, Φ (MMP.Fourfold.relativeNumericalDivisorClass sX π D) =
      MMP.Fourfold.relativeNumericalDivisorClass sY πY (ℓ D) := fun D => rfl
  -- `Φ` is continuous
  obtain ⟨_, _, _⟩ := relativeNumericalDivisorClasses_tvs sX π
  obtain ⟨_, _, _⟩ := relativeNumericalDivisorClasses_tvs sY πY
  haveI : FiniteDimensional ℝ (MMP.Fourfold.NumericalDivisorClasses sX) :=
    (MMP.Fourfold.exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional sX
      ((isProjectiveVariety_iff_isProjective ℂ sX).mp hX)).2
  haveI : FiniteDimensional ℝ (MMP.Fourfold.RelativeNumericalDivisorClasses sX π) :=
    MMP.Fourfold.RelativeNumericalDivisorClasses.finiteDimensional_of_finiteDimensional_numericalDivisorClasses sX π
  have hΦc : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
  -- `Φ` maps effective classes to effective classes
  have hcone : Set.MapsTo Φ (MMP.Fourfold.relativeEffectiveCone sX π)
      (MMP.Fourfold.relativeEffectiveCone sY πY) := by
    intro x hx
    change x ∈ Submodule.span _ _ at hx
    change Φ x ∈ Submodule.span _ _
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨E, hE, rfl⟩ := hy
      rw [hΦ]
      -- the Weil divisor of `E` is effective, and so is its transform
      have hwE : ∀ P, 0 ≤ (wX E).coeff P := fun P => (hwX E P).nonneg_of_isEffective hE
      set N := RationalMap.transformDivisor φ (wX E) with hN
      have hN0 : ∀ F, 0 ≤ N.coeff F := transformDivisor_nonneg φ hwE
      obtain ⟨m, hm, hmc⟩ := hYq.2 N
      obtain ⟨A, hA⟩ := exists_isWeilDivisorOfCartier_of_isCartier hmc
      have hAeff : MMP.Intersection.IsEffective A :=
        isEffective_of_isWeilDivisorOfCartier hA fun F => by
          rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul]
          have := hN0 F
          rw [DivisorWithCoeffs.coeff_apply] at this
          exact mul_nonneg (by positivity) this
      have hwA : wY A = (m : ℤ) • N := Finsupp.ext fun F => (hwY A F).unique (hA F)
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have hclass : MMP.Fourfold.relativeNumericalDivisorClass sY πY
          (ℓ (KCartierDivisor.ofCartier ℝ E)) = (1 / (m : ℝ)) •
            MMP.Fourfold.relativeNumericalDivisorClass sY πY (KCartierDivisor.ofCartier ℝ A) := by
        rw [← map_smul, ← sub_eq_zero, ← map_sub]
        refine relativeNumericalDivisorClass_eq_zero_of_weil_eq_zero (π := πY) ?_
        funext F
        obtain ⟨P, hP⟩ := hpre F
        have e1 : weilR wX (KCartierDivisor.ofCartier ℝ E) = Divisor.toRDivisor (wX E) := by
          simp [KCartierDivisor.ofCartier]
        have e2 : weilR wY (KCartierDivisor.ofCartier ℝ A) = Divisor.toRDivisor (wY A) := by
          simp [KCartierDivisor.ofCartier]
        have e3 : ((N F : ℤ) : ℝ) = ((wX E P : ℤ) : ℝ) := by rw [hN, htrapp hP]
        rw [← coeff_weilR hwY, map_sub, map_smul, hℓD, DivisorWithCoeffs.coeff_apply,
          Finsupp.sub_apply, Finsupp.smul_apply, htrapp hP, smul_eq_mul, Pi.zero_apply, e1, e2,
          hwA]
        change ((wX E P : ℤ) : ℝ) - 1 / (m : ℝ) * ((((m : ℤ) • N) F : ℤ) : ℝ) = 0
        rw [Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, ← e3]
        field_simp
        push_cast
        ring
      rw [hclass]
      exact (MMP.Fourfold.relativeEffectiveCone sY πY).smul_mem (by positivity)
        (PointedCone.subset_hull ⟨A, hAeff, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      have : Φ (c • a) = c • Φ a := map_smul Φ (c : ℝ) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  -- the pseudo-effective class of `K_X + B` goes to that of `K_Y + φ_* B`
  obtain ⟨D, hD, hDps⟩ := hps
  refine ⟨ℓ D, fun F => ?_, ?_⟩
  · have h1 : (weilR wY (ℓ D)).coeff F = weil (ℓ D) F := coeff_weilR hwY _ F
    rw [weil_apply] at h1
    rw [← h1, hℓD]
    obtain ⟨P, hP⟩ := hpre F
    have h2 : (weilR wX D) P = weil D P := by
      rw [← DivisorWithCoeffs.coeff_apply]; exact coeff_weilR hwX D P
    rw [hKY, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, htrapp hP, h2,
      weil_apply, ← hD P]
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply]
    change (((RationalMap.transformDivisor φ KX) F : ℤ) : ℝ) + RationalMap.transformDivisor φ B F =
      ((KX P : ℤ) : ℝ) + B P
    rw [htrapp hP, htrapp hP]
  · have := map_mem_closure hΦc hDps hcone
    rwa [hΦ] at this

end Pushforward

end PsefPushforward

/-! ### The induction on the number of vertices -/

section Induction

/-- The finite geography for polytopes with `N` vertices, over every projective base. -/
private def Claim (N : ℕ) : Prop :=
  ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (v : Fin N → QDivisor X) (G : QDivisor X),
    MMP.Mori.IsProjectiveVariety ℂ sX → MMP.Mori.IsProjectiveVariety ℂ sZ → π ≫ sZ = sX →
    topologicalKrullDim X = 3 → IsQFactorial sX → (∃ m : ℕ, KX.IsCanonicalDivisor sX m) →
    (∀ i P, 0 ≤ (v i).coeff P) → (∀ i, IsRealKltPair sX (QDivisor.toRDivisor (v i))) →
    (∀ P, 0 ≤ G.coeff P) → G.IsRelativelyBig π → (∀ i P, G.coeff P ≤ (v i).coeff P) →
    HasFiniteModels sX sZ π KX (bary v '' stdSimplex ℝ (Fin N))

/-- **The central model.** A klt pair `(X, B)` with `K_X + B` pseudo-effective over `Z` has a klt
log minimal model `φ : X ⤏ Y` over `Z`, with `Y` a `ℚ`-factorial projective threefold. -/
private theorem exists_isRealLogMinimalModel_of_isPsef
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3)
    (hXq : IsQFactorial sX) (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m) {B : RDivisor X}
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hB : IsRealKltPair sX B) (hps : IsPsef sX π KX B) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (_ : LocallyOfFiniteType sY) (πY : Y ⟶ Z)
      (KY : Divisor Y) (φ : X.RationalMap Y),
      IsRealLogMinimalModel sX sY sZ π πY KX B KY
        (MMP.Mori.RationalMap.transformDivisor φ B) φ ∧
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B) ∧
      topologicalKrullDim Y = 3 := by
  classical
  have hXn : IsNormalVariety ℂ sX := hB.1
  obtain ⟨Y, _, _, _, sY, _, πY, φ, hWM, hYq, hYklt, W, _, _, _, sW, p, q, h, hWv, hWsm, hpW,
    hqW, hpproj, hqproj, hpb, hqb, hinv, hcomp, GX, GY, hGX, hGY, heff, hexc, hpos⟩ :=
    IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective hX hZ hπ hXq hdim hKX
      (fun P => hB0 P) hB (exists_presentation_of_isPsef hps)
  have hYn : IsNormalVariety ℂ sY := hWM.isNormalVariety_target
  have := hYn.1
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  subst hpW
  haveI := isProper_of_isProjectiveMorphism p hpproj
  haveI := isProper_of_isProjectiveMorphism q hqproj
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWnp : IsNormalVariety ℂ (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hWnq : IsNormalVariety ℂ (q ≫ sY) := hqW ▸ hWnp
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sY) := hqW ▸ hWv.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (q ≫ sY) := hWnq.1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  obtain ⟨m, hm⟩ := hKX
  have hdimW : topologicalKrullDim W = m := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb]
    exact hm.topologicalKrullDim_eq
  have hdimY : topologicalKrullDim Y = m := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (q ≫ sY) hqb,
      hdimW]
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWnp hdimW
  obtain ⟨KW, hKW, hKWX⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hWnp hpb hm hK₀
  have hKWq : KW.IsCanonicalDivisor (q ≫ sY) m := hqW ▸ hKW
  obtain ⟨K₁, hK₁⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sY hYn hdimY
  have hKYc := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hYn hWnq hqb hK₁ hKWq
  have hnoext : ∀ F, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F :=
    hWM.not_isInverseExceptional
  have hKcompat : MMP.Mori.RationalMap.transformDivisor (X := W) q.toRationalMap KW =
      MMP.Mori.RationalMap.transformDivisor φ KX := by
    rw [← hKWX, ← hcomp, transformDivisor_compHom_transformDivisor hXn hYn hWnp hpb hqb hinv
      (hcomp ▸ hnoext) KW]
  rw [hKcompat] at hKYc
  have hres : IsLogComparisonResolution sX sY (p ≫ sX) φ KX B
      (MMP.Mori.RationalMap.transformDivisor φ KX)
      (MMP.Mori.RationalMap.transformDivisor φ B) p q h GX GY :=
    { isVariety := hWv
      isSmoothScheme := hWsm
      comp_eq_left := rfl
      comp_eq_right := hqW
      isProjectiveMorphism_left := hpproj
      isProjectiveMorphism_right := hqproj
      isBirationalMorphism_left := hpb
      isBirationalMorphism_right := hqb
      isInverse := hinv
      compHom_eq := hcomp
      exists_canonicalDivisor := ⟨m, KW, hKW, hKWX, hKcompat⟩
      isRCartierPullback_left := hGX
      isRCartierPullback_right := hGY
      effective := heff
      isExceptional := hexc }
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hWnp
  have := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hXn
  refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, sY, inferInstance, πY,
    MMP.Mori.RationalMap.transformDivisor φ KX, φ,
    { isRealLcPair := ⟨hXn, hB0, hB.2.2.1, fun n E a ha => (hB.2.2.2 n E a ha).le⟩
      isCanonicalDivisor := ⟨m, hm⟩
      comp_eq := hπ
      isNormalVariety_model := hYn
      isCanonicalDivisor_model := ⟨m, hKYc⟩
      isProjectiveVariety_model := hWM.isProjectiveVariety_target
      comp_eq_model := hWM.comp_eq_target
      isQFactorial := hYq
      isRealDltPair := isRealDltPair_of_isRealKltPair
        (fun P => transformDivisor_nonneg φ hB0 P) hYklt
      isBirational := hWM.isBirational
      isOver := hWM.isOver
      coeff_boundary := fun F => by rw [if_neg (hnoext F), add_zero]
      isRelativelyNef := hWM.isRelativelyNef
      exists_resolution := ⟨W, inferInstance, inferInstance, inferInstance, p ≫ sX, p, q, h, GX,
        GY, hres⟩
      exists_resolution_pos := ⟨W, inferInstance, inferInstance, inferInstance, p ≫ sX, p, q, h,
        GX, GY, hres, fun P hP P' hP' => hpos P hP P'
          ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p P' P).2
            (map_genericPoint_of_transformPrimeDivisor_eq_some hinv hP'))⟩ },
    hYklt, ?_⟩
  rw [hdimY, ← hm.topologicalKrullDim_eq, hdim]

/-- The strict transform commutes with the boundary of a weight vector. -/
private theorem transformDivisor_bary {X Y : Scheme.{0}} {N : ℕ} (φ : X.RationalMap Y)
    (v : Fin N → QDivisor X) (μ : Fin N → ℝ) :
    MMP.Mori.RationalMap.transformDivisor φ (bary v μ) =
      bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ := by
  classical
  rw [bary_apply, bary_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← MMP.Mori.RationalMap.transformDivisorₗ_apply ℝ, map_smul,
    MMP.Mori.RationalMap.transformDivisorₗ_apply]
  congr 1
  ext E
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    show QDivisor.toRDivisor (v i) = Finsupp.mapRange (fun q : ℚ => (q : ℝ)) Rat.cast_zero (v i)
      from rfl, transformDivisor_apply, transformDivisor_apply,
    Finsupp.sum_mapRange_index (by intros; split_ifs <;> rfl), Finsupp.sum, Finsupp.sum,
    Rat.cast_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  split_ifs <;> simp

/-- Pull-backs of finite combinations are the combinations of the pull-backs. -/
private theorem isRCartierPullback_sum_smul {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : X ⟶ Y} {ι : Type*} (s : Finset ι) {D : ι → RDivisor Y} {G : ι → RDivisor X}
    (h : ∀ i, MMP.Flips.IsRCartierPullback f (D i) (G i)) (μ : ι → ℝ) :
    MMP.Flips.IsRCartierPullback f (∑ i ∈ s, μ i • D i) (∑ i ∈ s, μ i • G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0,
      by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    simpa using isRCartierPullback_smul_add_smul (h a) ih (μ a) 1

/-- The adjoint of a weighted boundary is the weighted combination of the vertex adjoints. -/
private theorem logCanonicalDivisor_bary {V : Scheme.{0}} {N : ℕ} (K : Divisor V)
    (w : Fin N → QDivisor V) {μ : Fin N → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin N)) :
    logCanonicalDivisor K (bary w μ) =
      ∑ i, μ i • logCanonicalDivisor K (QDivisor.toRDivisor (w i)) := by
  refine Finsupp.ext fun P => ?_
  simp only [logCanonicalDivisor, bary_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hμ.2, one_mul]

/-- **Transfer from the central model.** Let `φ : X ⤏ Y` be a klt log minimal model of the
central pair `(X, B_{μ₀})`. Near `μ₀`, a klt log minimal model over `Z` of `(Y, φ_* B_μ)` is,
composed with `φ`, a klt log minimal model of `(X, B_μ)`, and pseudo-effectivity of `K_X + B_μ`
passes to `K_Y + φ_* B_μ`. The neighbourhood is the one on which the comparison for `φ`, which is
affine in the weights, stays positive along the prime divisors contracted by `φ`. -/
private theorem exists_mem_nhds_hasFiniteModels_of_transfer {N : ℕ}
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {KY : Divisor Y} (v : Fin N → QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX) (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hv : ∀ i P, 0 ≤ (v i).coeff P) (hvklt : ∀ i, IsRealKltPair sX (QDivisor.toRDivisor (v i)))
    {μ₀ : Fin N → ℝ} (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin N)) (φ : X.RationalMap Y)
    (hφ : IsRealLogMinimalModel sX sY sZ π πY KX (bary v μ₀) KY
      (MMP.Mori.RationalMap.transformDivisor φ (bary v μ₀)) φ)
    (hφklt : IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ (bary v μ₀))) :
    ∃ U ∈ nhds μ₀, ∀ S ⊆ U ∩ stdSimplex ℝ (Fin N),
      HasFiniteModels sY sZ πY KY
          (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) '' S) →
        HasFiniteModels sX sZ π KX (bary v '' S) := by
  classical
  have hYq : IsQFactorial sY := hφ.isQFactorial
  have hYp : MMP.Mori.IsProjectiveVariety ℂ sY := hφ.isProjectiveVariety_model
  have hπ : π ≫ sZ = sX := hφ.comp_eq
  have hφe := IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hφ
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := by
    have : (Z ↘ ⊤_ Scheme) = sZ ≫ CategoryTheory.Limits.terminal.from (Spec (.of ℂ)) :=
      Subsingleton.elim _ _
    rw [this]; infer_instance
  obtain ⟨W₁, _, _, _, sW₁, p₁, q₁, h₁, GX₀, GY₀, hR₁, hpos₀⟩ := hφ.exists_resolution_pos
  haveI : IsDominant p₁ := hR₁.isBirationalMorphism_left.isDominant
  haveI : IsDominant q₁ := hR₁.isBirationalMorphism_right.isDominant
  haveI : QuasiCompact sW₁ := hR₁.isVariety.toQuasiCompact
  haveI : CompactSpace W₁ := QuasiCompact.compactSpace_of_compactSpace sW₁
  haveI := hR₁.isBirationalMorphism_left.isIso_specFunctionFieldMap
  -- the comparisons of the vertices on `W₁`
  choose GXi hGXi using fun i => (MMP.Flips.existsUnique_isRCartierPullback p₁
    (isCartierCombination_of_isQFactorial hXq
      (logCanonicalDivisor KX (QDivisor.toRDivisor (v i))))).exists
  choose GYi hGYi using fun i => (MMP.Flips.existsUnique_isRCartierPullback q₁
    (isCartierCombination_of_isQFactorial hYq (logCanonicalDivisor KY
      (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ (v i)))))).exists
  have hGXμ : ∀ μ ∈ stdSimplex ℝ (Fin N), MMP.Flips.IsRCartierPullback p₁
      (logCanonicalDivisor KX (bary v μ)) (∑ i, μ i • GXi i) := fun μ hμ => by
    rw [logCanonicalDivisor_bary KX v hμ]
    exact isRCartierPullback_sum_smul Finset.univ hGXi μ
  have hGYμ : ∀ μ ∈ stdSimplex ℝ (Fin N), MMP.Flips.IsRCartierPullback q₁
      (logCanonicalDivisor KY (MMP.Mori.RationalMap.transformDivisor φ (bary v μ)))
      (∑ i, μ i • GYi i) := fun μ hμ => by
    rw [transformDivisor_bary, logCanonicalDivisor_bary KY _ hμ]
    exact isRCartierPullback_sum_smul Finset.univ hGYi μ
  -- the comparison is affine in the weights
  let c : MMP.Mori.PrimeDivisor W₁ → (Fin N → ℝ) → ℝ :=
    fun E μ => ∑ i, μ i * ((GXi i - GYi i).coeff E)
  have hc : ∀ μ E, ((∑ i, μ i • GXi i) - ∑ i, μ i • GYi i).coeff E = c E μ := fun μ E => by
    simp only [c, DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hX0 : GX₀ = ∑ i, μ₀ i • GXi i :=
    MMP.Flips.IsRCartierPullback.eq p₁ hR₁.isRCartierPullback_left (hGXμ μ₀ hμ₀)
  have hY0 : GY₀ = ∑ i, μ₀ i • GYi i :=
    MMP.Flips.IsRCartierPullback.eq q₁ hR₁.isRCartierPullback_right (hGYμ μ₀ hμ₀)
  have hcont : ∀ E, Continuous (c E) := fun E =>
    continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  set s := (GX₀ - GY₀).support with hs
  have hopen : IsOpen {μ : Fin N → ℝ | ∀ E ∈ s, 0 < c E μ} := by
    have : {μ : Fin N → ℝ | ∀ E ∈ s, 0 < c E μ} = ⋂ E ∈ s, {μ | 0 < c E μ} := by
      ext μ; simp
    rw [this]
    exact isOpen_biInter_finset fun E _ => isOpen_lt continuous_const (hcont E)
  have hmem : μ₀ ∈ {μ : Fin N → ℝ | ∀ E ∈ s, 0 < c E μ} := fun E hE => by
    rw [← hc, ← hX0, ← hY0]
    have h1 := hR₁.effective E
    have h2 : (GX₀ - GY₀) E ≠ 0 := Finsupp.mem_support_iff.mp hE
    rw [DivisorWithCoeffs.coeff_apply] at h1 ⊢
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  refine ⟨_, hopen.mem_nhds hmem, fun S hS hYS => ?_⟩
  obtain ⟨ι, hι, Y', i1, i2, i3, i4, sY', πY', KY', ψ, hY'm, hB'⟩ := hYS
  -- the composite maps `χ_j = ψ_j ∘ φ`
  have hlft : ∀ j, LocallyOfFiniteType (sY' j) := fun j =>
    (hY'm j).2.1.1.toLocallyOfFiniteType
  have hover : ∀ j, (inv (specFunctionFieldMap p₁) ≫ specFunctionFieldMap q₁ ≫
      (ψ j).fromFunctionField) ≫ sY' j =
      X.fromSpecStalk (genericPoint X) ≫ sX := fun j => by
    have hψo : (ψ j).fromFunctionField ≫ πY' j = Y.fromSpecStalk (genericPoint Y) ≫ πY := by
      rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, (hY'm j).2.2.2.2.2.1,
        MMP.Flips.RationalMap.fromFunctionField_hom]
    rw [← (hY'm j).2.2.2.1]
    simp only [Category.assoc]
    rw [reassoc_of% hψo, hφ.comp_eq_model, specFunctionFieldMap_comp_fromSpecStalk_assoc q₁,
      hR₁.comp_eq_right, ← hR₁.comp_eq_left, ← specFunctionFieldMap_comp_fromSpecStalk_assoc p₁,
      IsIso.inv_hom_id_assoc]
  let χ : ∀ j, X.RationalMap (Y' j) := fun j => by
    haveI := hlft j
    exact Scheme.RationalMap.ofFunctionField sX (sY' j) _ (hover j)
  have hχ : ∀ j, specFunctionFieldMap p₁ ≫ (χ j).fromFunctionField =
      specFunctionFieldMap q₁ ≫ (ψ j).fromFunctionField :=
    fun j => by
      haveI := hlft j
      change specFunctionFieldMap p₁ ≫
        (Scheme.RationalMap.ofFunctionField sX (sY' j) _ (hover j)).fromFunctionField = _
      rw [Scheme.RationalMap.fromFunctionField_ofFunctionField, IsIso.hom_inv_id_assoc]
  -- a log minimal model of a nearby pushed pair gives one of the pair on `X`
  have key : ∀ j, ∀ μ ∈ S,
      IsRealLogMinimalModel sY (sY' j) sZ πY (πY' j) KY
          (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ) (KY' j)
          (MMP.Mori.RationalMap.transformDivisor (ψ j)
            (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ)) (ψ j) →
        IsRealKltPair (sY' j) (MMP.Mori.RationalMap.transformDivisor (ψ j)
            (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ)) →
        IsRealLogMinimalModel sX (sY' j) sZ π (πY' j) KX (bary v μ) (KY' j)
            (MMP.Mori.RationalMap.transformDivisor (χ j) (bary v μ)) (χ j) ∧
          IsRealKltPair (sY' j) (MMP.Mori.RationalMap.transformDivisor (χ j) (bary v μ)) := by
    intro j μ hμS hm hk
    haveI := i1 j
    haveI := i2 j
    haveI := i3 j
    haveI := i4 j
    have hμU := (hS hμS).1
    have hμ := (hS hμS).2
    rw [← transformDivisor_bary] at hm hk
    refine isRealLogMinimalModel_compHom hX hZ hπ hXq hKX hYq hφ.isOver hφe hR₁
      (bary_nonneg v hv hμ) (isRealKltPair_bary hXq hvklt hμ) (hGXμ μ hμ) (hGYμ μ hμ) ?_ hm hk
      (hχ j)
    intro P hP P₁ hP₁
    have h0 := hpos₀ P hP P₁ hP₁
    have hP₁s : P₁ ∈ s := by
      rw [hs, Finsupp.mem_support_iff]
      rw [DivisorWithCoeffs.coeff_apply] at h0
      exact h0.ne'
    rw [hc]
    exact hμU P₁ hP₁s
  haveI := hι
  let ι' := {j : ι // ∃ μ ∈ S,
    IsRealLogMinimalModel sY (sY' j) sZ πY (πY' j) KY
        (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ) (KY' j)
        (MMP.Mori.RationalMap.transformDivisor (ψ j)
          (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ)) (ψ j) ∧
      IsRealKltPair (sY' j) (MMP.Mori.RationalMap.transformDivisor (ψ j)
          (bary (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i)) μ))}
  refine ⟨ι', inferInstance, fun j => Y' j.1, fun j => i1 j.1, fun j => i2 j.1, fun j => i3 j.1,
    fun j => i4 j.1, fun j => sY' j.1, fun j => πY' j.1, fun j => KY' j.1, fun j => χ j.1,
    fun j => ?_, ?_⟩
  · obtain ⟨j, μ, hμS, hm, hk⟩ := j
    obtain ⟨hmod, -⟩ := key j μ hμS hm hk
    exact ⟨(hY'm j).1, (hY'm j).2.1, (hY'm j).2.2.1, (hY'm j).2.2.2.1, hmod.isBirational,
      hmod.isOver, IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hmod⟩
  · rintro _ ⟨μ, hμS, rfl⟩ hps
    have hμ := (hS hμS).2
    have hpsY := isPsef_transformDivisor hX hYp hXq hYq hφ.isOver hφe hR₁ hps
    rw [transformDivisor_bary] at hpsY
    obtain ⟨j, hm, hk⟩ := hB' _ ⟨μ, hμS, rfl⟩ hpsY
    exact ⟨⟨j, μ, hμS, hm, hk⟩, key j μ hμS hm hk⟩

/-- **Local finiteness at a nef point.** Assuming the geography for fewer vertices, if the
central pair `(X, B_{μ₀})` is klt with `K_X + B_{μ₀}` nef over `Z`, the points of a punctured
neighbourhood of `μ₀` have finitely many models. The vertices need not be klt. -/
private theorem exists_mem_nhds_hasFiniteModels_of_isRelativelyNef {N : ℕ}
    (IH : ∀ M < N, Claim M)
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (v : Fin N → QDivisor X) (G : QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hv : ∀ i P, 0 ≤ (v i).coeff P) (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGv : ∀ i P, G.coeff P ≤ (v i).coeff P) {μ₀ : Fin N → ℝ} (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin N))
    (hklt : IsRealKltPair sX (bary v μ₀))
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (logCanonicalDivisor KX (bary v μ₀))) :
    ∃ U ∈ nhds μ₀,
      HasFiniteModels sX sZ π KX (bary v '' ((U ∩ stdSimplex ℝ (Fin N)) \ {μ₀})) := by
  classical
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := by
    rcases N with _ | M
    · exact absurd hμ₀.2 (by simp)
    · exact ⟨M, rfl⟩
  have hXn : IsNormalVariety ℂ sX := hklt.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  obtain ⟨n, hn⟩ := hKX
  -- the adjoint contraction
  obtain ⟨T, _, _, _, _, sT, g, h, H, hT, hg, hgh, hH, hpull, aX, haX, hgapX⟩ :=
    exists_isContraction_of_isRelativelyNef_of_isRelativelyBig sX sZ π hπ hX hXq hZ n KX hn
      (bary v μ₀) (bary_nonneg v hv hμ₀) hklt G hG (coe_le_coeff_bary v hGv hμ₀) hGbig hnef
  have hhZ : h ≫ sZ = sT := by
    haveI : IsDominant g := ⟨hg.surjective.denseRange⟩
    refine ext_of_isDominant (ι := g) ?_
    rw [← Category.assoc, hgh, hπ, hg.comp_eq]
  -- a small rational simplex of klt boundaries around `μ₀`
  obtain ⟨r, hr, hrklt⟩ := exists_pos_forall_dist_lt_isRealKltPair hX hXq v hv hklt
  obtain ⟨q, δ, hδ0, hδ1, hqΔ, hqclose, hδr, hqμ⟩ := exists_rat_simplex hμ₀ hr
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  let c : Fin (M + 1) → Fin (M + 1) → ℚ := fun j i =>
    (1 - δ) * q i + δ * (if i = j then 1 else 0)
  let w : Fin (M + 1) → QDivisor X := fun j => ∑ i, c j i • v i
  let m : (Fin (M + 1) → ℝ) → (Fin (M + 1) → ℝ) := fun β i => (1 - δ) * q i + δ * β i
  have hsumc : ∀ (β : Fin (M + 1) → ℝ) (i : Fin (M + 1)),
      ∑ j, β j * (c j i : ℝ) = (1 - δ) * q i * ∑ j, β j + δ * β i := fun β i => by
    simp only [c]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj)]; ring)
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
      ring
  have hbw : ∀ β ∈ stdSimplex ℝ (Fin (M + 1)), bary w β = bary v (m β) := fun β hβ => by
    rw [bary_sum_smul]
    congr 1
    funext i
    rw [hsumc, hβ.2, mul_one]
  have hmΔ : ∀ β ∈ stdSimplex ℝ (Fin (M + 1)), m β ∈ stdSimplex ℝ (Fin (M + 1)) :=
    fun β hβ => ⟨fun i => add_nonneg (mul_nonneg (by linarith) (hqΔ.1 i))
      (mul_nonneg hδ0'.le (hβ.1 i)), by
        simp only [m, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [show ∑ i, ((q i : ℚ) : ℝ) = 1 from hqΔ.2, hβ.2]
        ring⟩
  have hmdist : ∀ β ∈ stdSimplex ℝ (Fin (M + 1)), dist (m β) μ₀ < r := fun β hβ => by
    rw [dist_pi_lt_iff hr]
    intro i
    rw [Real.dist_eq]
    have h1 := hqclose i
    have hβi : β i ≤ 1 := by
      rw [← hβ.2]
      exact Finset.single_le_sum (fun j _ => hβ.1 j) (Finset.mem_univ i)
    have hqi : ((q i : ℚ) : ℝ) ≤ 1 := by
      rw [← show ∑ i, ((q i : ℚ) : ℝ) = 1 from hqΔ.2]
      exact Finset.single_le_sum (f := fun i => ((q i : ℚ) : ℝ)) (fun j _ => hqΔ.1 j)
        (Finset.mem_univ i)
    have hq0 := hqΔ.1 i
    have hb0 := hβ.1 i
    have : |m β i - μ₀ i| ≤ |((q i : ℚ) : ℝ) - μ₀ i| + δ := by
      have e : m β i - μ₀ i = (((q i : ℚ) : ℝ) - μ₀ i) + δ * (β i - q i) := by
        simp only [m]; ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_pos hδ0']
      have : |β i - q i| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith
    linarith
  have hsingle : ∀ j, QDivisor.toRDivisor (w j) = bary w (Pi.single j 1) := fun j => by
    rw [bary_apply, Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  have hsingleΔ : ∀ j, (Pi.single j 1 : Fin (M + 1) → ℝ) ∈ stdSimplex ℝ (Fin (M + 1)) :=
    fun j => single_mem_stdSimplex ℝ j
  have hwv : ∀ j, QDivisor.toRDivisor (w j) = bary v (m (Pi.single j 1)) := fun j => by
    rw [hsingle, hbw _ (hsingleΔ j)]
  have hwklt : ∀ j, IsRealKltPair sX (QDivisor.toRDivisor (w j)) := fun j => by
    rw [hwv]; exact hrklt _ (hmΔ _ (hsingleΔ j)) (hmdist _ (hsingleΔ j))
  have hw0 : ∀ j P, 0 ≤ (w j).coeff P := fun j P => by
    have := bary_nonneg v hv (hmΔ _ (hsingleΔ j)) P
    rw [← hwv, QDivisor.coeff_toRDivisor] at this
    exact_mod_cast this
  have hGw : ∀ j P, G.coeff P ≤ (w j).coeff P := fun j P => by
    have := coe_le_coeff_bary v hGv (hmΔ _ (hsingleΔ j)) P
    rw [← hwv, QDivisor.coeff_toRDivisor] at this
    exact_mod_cast this
  have hGT : G.IsRelativelyBig g := isRelativelyBig_of_isContraction hX hZ hπ hT hg hgh hG hGbig
  -- the induction hypothesis over `T` on every facet of the small simplex
  have hfacet : ∀ i : Fin (M + 1), HasFiniteModels sX sT g KX
      (bary (w ∘ i.succAbove) '' stdSimplex ℝ (Fin M)) := fun i =>
    IH M (Nat.lt_succ_self M) (w ∘ i.succAbove) G hX hT hg.comp_eq hdim hXq ⟨n, hn⟩
      (fun k P => hw0 _ P) (fun k => hwklt _) hG hGT (fun k P => hGw _ P)
  choose ι hι Yf i1 i2 i3 i4 sYf πYf KYf φf hYf hBf using hfacet
  -- the radial step for every facet model
  have hrad : ∀ i (j : ι i), ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → ∀ B'' : RDivisor X,
      (∀ P, 0 ≤ B''.coeff P) → IsRealKltPair sX B'' →
      IsRealLogMinimalModel sX (sYf i j) sT g (πYf i j) KX B'' (KYf i j)
        (MMP.Mori.RationalMap.transformDivisor (φf i j) B'') (φf i j) →
      IsRealKltPair (sYf i j) (MMP.Mori.RationalMap.transformDivisor (φf i j) B'') →
      IsRealLogMinimalModel sX (sYf i j) sZ π (πYf i j ≫ h) KX
          ((1 - t) • bary v μ₀ + t • B'') (KYf i j)
          (MMP.Mori.RationalMap.transformDivisor (φf i j) ((1 - t) • bary v μ₀ + t • B''))
          (φf i j) ∧
        IsRealKltPair (sYf i j)
          (MMP.Mori.RationalMap.transformDivisor (φf i j) ((1 - t) • bary v μ₀ + t • B'')) :=
    fun i j => exists_pos_isRealLogMinimalModel_lineMap hX hZ hπ hdim hXq ⟨n, hn⟩
      (bary_nonneg v hv hμ₀) hklt hnef hT hg hgh hH hpull (φf i j) (hYf i j).1 (hYf i j).2.2.1
      (hYf i j).2.2.2.1 (hYf i j).2.2.2.2.1 (hYf i j).2.2.2.2.2.1 (hYf i j).2.2.2.2.2.2
      G hG hGbig (coe_le_coeff_bary v hGv hμ₀) fun C hC m r L x hx => (hgapX C hC m r L x hx).2
  choose ε hε hεm using hrad
  haveI : ∀ i, Finite (ι i) := hι
  obtain ⟨ε₀, hε₀, hε₀le⟩ := exists_pos_forall_le_of_finite (fun k : Σ i, ι i => ε k.1 k.2)
    fun k => hε k.1 k.2
  -- the barycentric coordinates in the small simplex
  let βmap : (Fin (M + 1) → ℝ) → (Fin (M + 1) → ℝ) := fun μ i => (μ i - (1 - δ) * q i) / δ
  have hmβ : ∀ μ, m (βmap μ) = μ := fun μ => by
    funext i; simp only [m, βmap]; field_simp; ring
  have hβ₀ : βmap μ₀ ∈ stdSimplex ℝ (Fin (M + 1)) := by
    refine ⟨fun i => div_nonneg ?_ hδ0'.le, ?_⟩
    · rcases hqμ i with h0 | h0
      · simp [h0, hμ₀.1 i]
      · linarith
    · simp only [βmap, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hμ₀.2]
      rw [show ∑ i, ((q i : ℚ) : ℝ) = 1 from hqΔ.2]
      field_simp
      ring
  obtain ⟨Vβ, hVβ, hradial⟩ := exists_mem_nhds_eq_lineMap_of_mem_stdSimplex hβ₀ hε₀
  have hβcont : Continuous βmap :=
    continuous_pi fun i => ((continuous_apply i).sub continuous_const).div_const _
  refine ⟨βmap ⁻¹' Vβ ∩ {μ | ∀ i, q i ≠ 0 → (1 - (δ : ℝ)) * q i < μ i},
    Filter.inter_mem (hβcont.continuousAt.preimage_mem_nhds hVβ)
      (Filter.eventually_all.2 fun i => ?_), ?_⟩
  · rcases hqμ i with h0 | h0
    · exact Filter.Eventually.of_forall fun μ hq => absurd h0 hq
    · exact ((continuous_apply i).continuousAt.eventually (lt_mem_nhds h0)).mono
        fun μ hμ _ => hμ
  -- the family of models over `Z`
  refine ⟨Σ i, ι i, inferInstance, fun k => Yf k.1 k.2, fun k => i1 k.1 k.2,
    fun k => i2 k.1 k.2, fun k => i3 k.1 k.2, fun k => i4 k.1 k.2, fun k => sYf k.1 k.2,
    fun k => πYf k.1 k.2 ≫ h, fun k => KYf k.1 k.2, fun k => φf k.1 k.2, fun k => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hYf k.1 k.2
    exact ⟨h1, h2, h3, by rw [Category.assoc, hhZ, h4], h5, hgh ▸ isOver_comp h6, h7⟩
  rintro _ ⟨μ, ⟨⟨⟨hμV, hμq⟩, hμΔ⟩, hμne⟩, rfl⟩ hps
  have hβΔ : βmap μ ∈ stdSimplex ℝ (Fin (M + 1)) := by
    refine ⟨fun i => div_nonneg ?_ hδ0'.le, ?_⟩
    · by_cases h0 : q i = 0
      · simp [h0, hμΔ.1 i]
      · linarith [hμq i h0]
    · simp only [βmap, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hμΔ.2]
      rw [show ∑ i, ((q i : ℚ) : ℝ) = 1 from hqΔ.2]
      field_simp
      ring
  have hβne : βmap μ ≠ βmap μ₀ := fun he =>
    hμne (by rw [Set.mem_singleton_iff, ← hmβ μ, he, hmβ])
  obtain ⟨t, ht0, htε, β'', hβ''Δ, ⟨i₀, hi₀⟩, hβeq⟩ := hradial _ ⟨hμV, hβΔ⟩ hβne
  set B'' := bary w β'' with hB''
  have hB : bary v μ = (1 - t) • bary v μ₀ + t • B'' := by
    rw [← hmβ μ, ← hbw _ hβΔ, hβeq, map_add, map_smul, map_smul, hbw _ hβ₀, hmβ]
  have hB''v : B'' = bary v (m β'') := hbw _ hβ''Δ
  have hB''0 : ∀ P, 0 ≤ B''.coeff P := fun P => by
    rw [hB''v]; exact bary_nonneg v hv (hmΔ _ hβ''Δ) P
  have hB''klt : IsRealKltPair sX B'' := by
    rw [hB''v]; exact hrklt _ (hmΔ _ hβ''Δ) (hmdist _ hβ''Δ)
  rw [hB] at hps ⊢
  have hpsT := isPsef_of_isPsef_lineMap hX hXq hg hgh hpull ht0 hps
  have hmem : B'' ∈ bary (w ∘ i₀.succAbove) '' stdSimplex ℝ (Fin M) :=
    ⟨β'' ∘ i₀.succAbove, stdSimplex_comp_succAbove hβ''Δ i₀ hi₀,
      (bary_eq_bary_comp_succAbove w i₀ hi₀).symm⟩
  obtain ⟨j, hj, hjklt⟩ := hBf i₀ B'' hmem hpsT
  exact ⟨⟨i₀, j⟩, hεm i₀ j t ht0 (htε.trans_le (hε₀le ⟨i₀, j⟩)) B'' hB''0 hB''klt hj hjklt⟩

/-- The vertices pushed forward to the central model satisfy the hypotheses of the nef case:
`Y` is a projective `ℚ`-factorial variety with canonical divisor `K_Y` over `Z`, and the strict
transform of `G` is big over `Z`. -/
private theorem transform_hypotheses
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {KY : Divisor Y} {B : RDivisor X} (φ : X.RationalMap Y)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXq : IsQFactorial sX)
    (hφ : IsRealLogMinimalModel sX sY sZ π πY KX B KY
      (MMP.Mori.RationalMap.transformDivisor φ B) φ)
    (G : QDivisor X) (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π) :
    MMP.Mori.IsProjectiveVariety ℂ sY ∧ πY ≫ sZ = sY ∧ IsQFactorial sY ∧
      (∃ m : ℕ, KY.IsCanonicalDivisor sY m) ∧
      QDivisor.IsRelativelyBig πY (MMP.Mori.RationalMap.transformDivisor φ G) := by
  refine ⟨hφ.isProjectiveVariety_model, hφ.comp_eq_model, hφ.isQFactorial,
    hφ.isCanonicalDivisor_model, ?_⟩
  exact (isRelativelyBig_transformDivisor_of_isBirationalContraction sX sY sZ
    hφ.isRealLcPair.1 hX hφ.isQFactorial hφ.isProjectiveVariety_model hZ π πY hφ.comp_eq
    hφ.comp_eq_model φ hφ.isBirational hφ.isOver
    (fun F => IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hφ F) G
    (fun P => hG P) (isQCartier_of_isQFactorial sX hXq G) hGbig).2.2

/-- A single klt log minimal model gives the finite-model property of a single boundary. -/
private theorem hasFiniteModels_singleton
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {KY : Divisor Y} {B : RDivisor X} (φ : X.RationalMap Y)
    (hφ : IsRealLogMinimalModel sX sY sZ π πY KX B KY
      (MMP.Mori.RationalMap.transformDivisor φ B) φ)
    (hφklt : IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B)) :
    HasFiniteModels sX sZ π KX {B} := by
  refine ⟨Unit, inferInstance, fun _ => Y, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, fun _ => sY, fun _ => πY, fun _ => KY,
    fun _ => φ, fun _ => ⟨hφ.isProjectiveVariety_model, hφ.isNormalVariety_model,
      hφ.isQFactorial, hφ.comp_eq_model, hφ.isBirational, hφ.isOver,
      IsRealLogMinimalModel.not_isInverseExceptional_of_transformDivisor hφ⟩, ?_⟩
  rintro B' rfl -
  exact ⟨(), hφ, hφklt⟩

/-- **Local finiteness at a pseudo-effective point.** -/
private theorem exists_mem_nhds_hasFiniteModels_of_isPsef {N : ℕ} (IH : ∀ M < N, Claim M)
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (v : Fin N → QDivisor X) (G : QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hv : ∀ i P, 0 ≤ (v i).coeff P) (hvklt : ∀ i, IsRealKltPair sX (QDivisor.toRDivisor (v i)))
    (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGv : ∀ i P, G.coeff P ≤ (v i).coeff P) {μ₀ : Fin N → ℝ} (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin N))
    (hps : IsPsef sX π KX (bary v μ₀)) :
    ∃ U ∈ nhds μ₀, HasFiniteModels sX sZ π KX (bary v '' (U ∩ stdSimplex ℝ (Fin N))) := by
  obtain ⟨Y, _, _, _, _, sY, _, πY, KY, φ, hφ, hφklt, hYdim⟩ :=
    exists_isRealLogMinimalModel_of_isPsef hX hZ hπ hdim hXq hKX
      (bary_nonneg v hv hμ₀) (isRealKltPair_bary hXq hvklt hμ₀) hps
  obtain ⟨U₁, hU₁, hU₁m⟩ :=
    exists_mem_nhds_hasFiniteModels_of_transfer v hX hZ hXq hKX hv hvklt hμ₀ φ hφ hφklt
  obtain ⟨hY, hπY, hYq, hKY, hGYbig⟩ := transform_hypotheses φ hX hZ hXq hφ G hG hGbig
  have hu : ∀ i P, 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ (v i)).coeff P :=
    fun i P => transformDivisor_nonneg φ (hv i) P
  have hGY : ∀ P, 0 ≤ (MMP.Mori.RationalMap.transformDivisor φ G).coeff P :=
    transformDivisor_nonneg φ hG
  have hGu : ∀ i P, (MMP.Mori.RationalMap.transformDivisor φ G).coeff P ≤
      (MMP.Mori.RationalMap.transformDivisor φ (v i)).coeff P :=
    fun i => transformDivisor_mono φ (hGv i)
  obtain ⟨U₂, hU₂, hU₂m⟩ := exists_mem_nhds_hasFiniteModels_of_isRelativelyNef IH
    (fun i => MMP.Mori.RationalMap.transformDivisor φ (v i))
    (MMP.Mori.RationalMap.transformDivisor φ G) hY hZ hπY hYdim hYq hKY hu hGY hGYbig hGu hμ₀
    (by rw [← transformDivisor_bary]; exact hφklt)
    (by rw [← transformDivisor_bary]; exact hφ.isRelativelyNef)
  refine ⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, ?_⟩
  have h₁ := hU₁m ((U₁ ∩ U₂ ∩ stdSimplex ℝ (Fin N)) \ {μ₀})
    (fun μ hμ => ⟨hμ.1.1.1, hμ.1.2⟩) (hU₂m.mono ?_)
  · refine (h₁.union (hasFiniteModels_singleton φ hφ hφklt)).mono ?_
    rintro _ ⟨μ, hμ, rfl⟩
    by_cases h : μ = μ₀
    · exact Or.inr (h ▸ rfl)
    · exact Or.inl ⟨μ, ⟨hμ, h⟩, rfl⟩
  · rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨μ, ⟨⟨hμ.1.1.2, hμ.1.2⟩, hμ.2⟩, rfl⟩

/-- **Local finiteness.** Assuming the geography for fewer vertices, every point of the simplex
has a neighbourhood whose boundaries have finitely many models. -/
private theorem exists_mem_nhds_hasFiniteModels {N : ℕ} (IH : ∀ M < N, Claim M)
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (v : Fin N → QDivisor X) (G : QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hv : ∀ i P, 0 ≤ (v i).coeff P) (hvklt : ∀ i, IsRealKltPair sX (QDivisor.toRDivisor (v i)))
    (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGv : ∀ i P, G.coeff P ≤ (v i).coeff P) {μ₀ : Fin N → ℝ} (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin N)) :
    ∃ U ∈ nhds μ₀, HasFiniteModels sX sZ π KX (bary v '' (U ∩ stdSimplex ℝ (Fin N))) := by
  by_cases hps : IsPsef sX π KX (bary v μ₀)
  · exact exists_mem_nhds_hasFiniteModels_of_isPsef IH v G hX hZ hπ hdim hXq hKX hv hvklt hG
      hGbig hGv hμ₀ hps
  refine ⟨_, (isClosed_setOf_isPsef (π := π) (KX := KX) v).isOpen_compl.mem_nhds hps,
    hasFiniteModels_of_forall_not_isPsef ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩ hpsμ
  exact hμ.1 hpsμ

private theorem claim (N : ℕ) : Claim N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro X Z _ _ _ _ sX _ sZ π KX v G hX hZ hπ hdim hXq hKX hv hvklt hG hGbig hGv
  choose! U hU hUm using fun μ (hμ : μ ∈ stdSimplex ℝ (Fin N)) =>
    exists_mem_nhds_hasFiniteModels IH v G hX hZ hπ hdim hXq hKX hv hvklt hG hGbig hGv hμ
  obtain ⟨t, ht⟩ := (isCompact_stdSimplex ℝ (Fin N)).elim_nhds_subcover' (fun μ hμ => U μ)
    (fun μ hμ => hU μ hμ)
  refine (hasFiniteModels_biUnion t (fun μ => bary v '' (U μ ∩ stdSimplex ℝ (Fin N)))
    fun μ _ => hUm μ μ.2).mono ?_
  rintro _ ⟨μ, hμ, rfl⟩
  obtain ⟨μ', hμ't, hμ'⟩ := Set.mem_iUnion₂.mp (ht hμ)
  exact Set.mem_biUnion hμ't ⟨μ, ⟨hμ', hμ⟩, rfl⟩

end Induction

/-- A rational klt pair is a real klt pair. -/
private theorem isRealKltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hXq : IsQFactorial sX) {D : QDivisor X} (hD : IsKltPair sX D) :
    IsRealKltPair sX (QDivisor.toRDivisor D) := by
  have hXn : IsNormalVariety ℂ sX := hD.1.isPair.1
  obtain ⟨n, K, hK, -⟩ := hD.1.isPair.2
  refine ⟨hXn, fun P => ?_, ⟨n, K, hK, hXq.isRCartier _⟩, hD.2⟩
  obtain ⟨m, hm⟩ := isLogDiscrepancy_ofPrimeDivisor hXn hD.1.isPair P
  have := hD.2 _ _ _ hm
  rw [QDivisor.coeff_toRDivisor]
  linarith

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (V : Finset (QDivisor X)) (G : QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hV : ∀ D ∈ V, ∀ P, 0 ≤ D.coeff P) (hVklt : ∀ D ∈ V, IsKltPair sX D)
    (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGV : ∀ D ∈ V, ∀ P, G.coeff P ≤ D.coeff P) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (_ : ∀ j, IsIntegral (Y j)) (_ : ∀ j, CompactSpace (Y j))
      (_ : ∀ j, IsLocallyNoetherian (Y j)) (_ : ∀ j, IsNormal (Y j))
      (sY : ∀ j, Y j ⟶ Spec (.of ℂ)) (πY : ∀ j, Y j ⟶ Z) (KY : ∀ j, Divisor (Y j))
      (φ : ∀ j, X.RationalMap (Y j)),
      (∀ j, MMP.Mori.IsProjectiveVariety ℂ (sY j) ∧ IsNormalVariety ℂ (sY j) ∧
        IsQFactorial (sY j) ∧ πY j ≫ sZ = sY j ∧ MMP.Mori.RationalMap.IsBirational (φ j) ∧
        MMP.Flips.RationalMap.IsOver π (πY j) (φ j) ∧
        ∀ F : MMP.Mori.PrimeDivisor (Y j), ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ j) F) ∧
      ∀ B ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))),
        (∃ D : KCartierDivisor ℝ X,
          (∀ P : MMP.Mori.PrimeDivisor X, (logCanonicalDivisor KX B).coeff P =
            D.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ)) ∧
          KCartierDivisor.IsRelativelyPseudoEffective sX π D) →
        ∃ j, IsRealLogMinimalModel sX (sY j) sZ π (πY j) KX B (KY j)
            (MMP.Mori.RationalMap.transformDivisor (φ j) B) (φ j) ∧
          IsRealKltPair (sY j) (MMP.Mori.RationalMap.transformDivisor (φ j) B) := by
  classical
  have hcl := claim V.card (fun i => (V.equivFin.symm i : QDivisor X)) G hX hZ hπ hdim hXq hKX
    (fun i => hV _ (V.equivFin.symm i).2)
    (fun i => isRealKltPair_of_isKltPair hXq (hVklt _ (V.equivFin.symm i).2)) hG hGbig
    (fun i => hGV _ (V.equivFin.symm i).2)
  rw [image_bary_stdSimplex] at hcl
  have hrange : (Set.range fun i => QDivisor.toRDivisor (V.equivFin.symm i : QDivisor X)) =
      QDivisor.toRDivisor '' (V : Set (QDivisor X)) := by
    ext D
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (V.equivFin.symm i).2, rfl⟩
    · rintro ⟨E, hE, rfl⟩
      exact ⟨V.equivFin ⟨E, hE⟩, by simp⟩
  rw [hrange] at hcl
  obtain ⟨ι, hι, Y, i1, i2, i3, i4, sY, πY, KY, φ, hY, hB⟩ := hcl
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact ⟨n, fun j => Y (e.symm j), fun j => i1 _, fun j => i2 _, fun j => i3 _, fun j => i4 _,
    fun j => sY _, fun j => πY _, fun j => KY _, fun j => φ _, fun j => hY _,
    fun B hBm hps => by
      obtain ⟨j, hj⟩ := hB B hBm hps
      refine ⟨e j, ?_⟩
      beta_reduce
      have h := e.symm_apply_apply j
      generalize e.symm (e j) = k at h ⊢
      subst h
      exact hj⟩

end Proof_thm_fourfold_threefold_big_boundary_geography

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Finite geography of real klt threefold models with a big boundary core.** Let
`π : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold and `K_X` a canonical divisor. Let `V` be a finite set of effective `ℚ`-divisors on
`X`, with every `(X, D)`, `D ∈ V`, klt and every `D ∈ V` at least `G`, for an effective
`ℚ`-divisor `G` big over `Z`. There are finitely many birational maps `φ j : X ⤏ Y j` over `Z`,
extracting no prime divisor, to normal projective `ℚ`-factorial varieties, such that for every
`B` in the convex hull of `V` with `K_X + B` pseudo-effective over `Z` some `Y j`, with the
strict transform `φ_j_* B`, is a klt log minimal model of `(X/Z, B)`. -/
@[mmp "thm_fourfold_threefold_big_boundary_geography"]
public theorem exists_finite_isRealLogMinimalModel_of_mem_convexHull_of_isRelativelyBig
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} (V : Finset (QDivisor X)) (G : QDivisor X)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hπ : π ≫ sZ = sX) (hdim : topologicalKrullDim X = 3) (hXq : IsQFactorial sX)
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hV : ∀ D ∈ V, ∀ P, 0 ≤ D.coeff P) (hVklt : ∀ D ∈ V, IsKltPair sX D)
    (hG : ∀ P, 0 ≤ G.coeff P) (hGbig : G.IsRelativelyBig π)
    (hGV : ∀ D ∈ V, ∀ P, G.coeff P ≤ D.coeff P) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (_ : ∀ j, IsIntegral (Y j)) (_ : ∀ j, CompactSpace (Y j))
      (_ : ∀ j, IsLocallyNoetherian (Y j)) (_ : ∀ j, IsNormal (Y j))
      (sY : ∀ j, Y j ⟶ Spec (.of ℂ)) (πY : ∀ j, Y j ⟶ Z) (KY : ∀ j, Divisor (Y j))
      (φ : ∀ j, X.RationalMap (Y j)),
      (∀ j, MMP.Mori.IsProjectiveVariety ℂ (sY j) ∧ IsNormalVariety ℂ (sY j) ∧
        IsQFactorial (sY j) ∧ πY j ≫ sZ = sY j ∧ MMP.Mori.RationalMap.IsBirational (φ j) ∧
        MMP.Flips.RationalMap.IsOver π (πY j) (φ j) ∧
        ∀ F : MMP.Mori.PrimeDivisor (Y j), ¬ MMP.Flips.RationalMap.IsInverseExceptional (φ j) F) ∧
      ∀ B ∈ convexHull ℝ (QDivisor.toRDivisor '' (V : Set (QDivisor X))),
        (∃ D : KCartierDivisor ℝ X,
          (∀ P : MMP.Mori.PrimeDivisor X, (logCanonicalDivisor KX B).coeff P =
            D.sum fun E c => c * (MMP.Intersection.primeDivisorOrder P E : ℝ)) ∧
          KCartierDivisor.IsRelativelyPseudoEffective sX π D) →
        ∃ j, IsRealLogMinimalModel sX (sY j) sZ π (πY j) KX B (KY j)
            (MMP.Mori.RationalMap.transformDivisor (φ j) B) (φ j) ∧
          IsRealKltPair (sY j) (MMP.Mori.RationalMap.transformDivisor (φ j) B) := by
  revert X Z sX sZ π KX V G hX hZ hπ hdim hXq hKX hV hVklt hG hGbig hGV
  exact Proof_thm_fourfold_threefold_big_boundary_geography.solution

end MMP.Fourfold
