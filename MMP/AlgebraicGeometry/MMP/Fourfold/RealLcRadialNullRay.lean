module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.RealLcPositiveGap
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor

/-!
# Nearby negative rays are null for a nef real lc adjoint on a fourfold

Let `f : X ⟶ Z` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
fourfold with canonical divisor `K_X`. Let `(X, B)` and `(X, E)` be log canonical pairs with
effective real boundaries, and suppose `D = K_X + B` is nef over `Z`. There is `t₀ > 0` such that
for `0 < t < t₀` every extremal ray of the relative closed cone of curves `NE̅(X/Z)` on which
`(1 - t) D + t (K_X + E)` is negative is `D`-null.

Both boundaries lie in one rational polytope `P` of effective rational lc boundaries, and `B` is a
positive convex combination of rational lc points of `P`. The uniform curve and positive gap `τ`
of `MMP.Fourfold.exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le` give, on a
negative ray with `D · L > 0`, the bound `((1 - t) D + t (K_X + E)) · L ≥ (1 - t) τ - 8 t > 0` for
`t < τ / (τ + 8)`, a contradiction; since `D` is nef over `Z`, `D · L = 0`.

## Main results

* `MMP.Fourfold.exists_pos_forall_isExtremalRay_null_of_isRealLcPair`.

## Implementation notes

An `ℝ`-Cartier divisor is paired with a class `u ∈ N₁(X/Z)` through a presentation `∑ cᵢ Mᵢ` by
Cartier divisors `Mᵢ`, as `∑ cᵢ (u · 𝒪_X(Mᵢ))` computed with
`MMP.Mori.RelativeNumericalCurveClasses.degree`. The pairing does not depend on the presentation,
so negativity on a ray asks for one presentation and nullness is asserted for all of them. The
dimension of `X` is the `4` of `MMP.Mori.Divisor.IsCanonicalDivisor`. Effectivity of `B` and `E`
is part of `MMP.Fourfold.IsRealLcPair`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology MMP.Mori MMP.Fourfold

namespace Proof_lem_fourfold_real_lc_radial_null_ray

section ErasedIntegral

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Pairing

open MMP.Flips

variable {k : Type} [Field k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (f : X ⟶ Z)

/-- Linear forms on `N₁(X/Z)` which agree on the classes of the contracted curves are equal. -/
private theorem linearMap_ext_relativeClass
    {φ ψ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ}
    (h : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f),
      φ (C.relativeClass f hC) = ψ (C.relativeClass f hC)) : φ = ψ := by
  have hsp : relativeOneCycles sX f = Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sX | C.IsContractedBy f}) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single]
  have key : ∀ (x : OneCycle ℝ sX) (hx : x ∈ Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sX | C.IsContractedBy f})),
      φ (relativeNumericalClass sX f ⟨x, hsp ▸ hx⟩) =
        ψ (relativeNumericalClass sX f ⟨x, hsp ▸ hx⟩) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C, hC, rfl⟩ := hx
      exact h C hC
    | zero =>
      have : (⟨0, hsp ▸ Submodule.zero_mem _⟩ : relativeOneCycles sX f) = 0 := rfl
      rw [this, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hsp ▸ Submodule.add_mem _ hx hy⟩ : relativeOneCycles sX f) =
          ⟨x, hsp ▸ hx⟩ + ⟨y, hsp ▸ hy⟩ := rfl
      rw [this, map_add, map_add, map_add, ihx, ihy]
    | smul c x hx ih =>
      have : (⟨c • x, hsp ▸ Submodule.smul_mem _ c hx⟩ : relativeOneCycles sX f) =
          c • ⟨x, hsp ▸ hx⟩ := rfl
      rw [this, map_smul, map_smul, map_smul, ih]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  obtain ⟨Z, hZ⟩ := Z
  exact key Z (hsp ▸ hZ)

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
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
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

variable [CompactSpace X]

variable (sX) in

/-- The linear form `z ↦ ∑ᵢ cᵢ (z · 𝒪_X(Mᵢ))` on `N₁(X/Z)` of a presentation `∑ᵢ cᵢ Mᵢ` by
Cartier divisors. -/
private noncomputable def presForm {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ :=
  ∑ i, c i • (haveI := (hM i).isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf)

private theorem presForm_apply {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (u : RelativeNumericalCurveClasses sX f) :
    presForm sX f c M hM u = ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) := by
  simp [presForm, LinearMap.sum_apply]

/-- On the class of a contracted curve `C`, the form of `∑ᵢ cᵢ Mᵢ` is `∑ᵢ cᵢ deg_C 𝒪_X(Mᵢ)`. -/
private theorem presForm_relativeClass {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    presForm sX f c M hM (C.relativeClass f hC) =
      ∑ i, c i * ((M i).degreeOn k sX C.ι C.dim_le (hM i) : ℝ) := by
  rw [presForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hM i).isInvertibleModule_divisorialSheaf
  exact congrArg (c i * ·) (OneCycle.degree_cycle ℝ _ C)

/-- Two presentations of the same `ℝ`-divisor give the same linear form on `N₁(X/Z)`. -/
private theorem presForm_eq_of_eq {n n' : ℕ} {c : Fin n → ℝ} {M : Fin n → Divisor X}
    (hM : ∀ i, (M i).IsCartier) {c' : Fin n' → ℝ} {M' : Fin n' → Divisor X}
    (hM' : ∀ i, (M' i).IsCartier)
    (h : ∑ i, c i • Divisor.toRDivisor (M i) = ∑ i, c' i • Divisor.toRDivisor (M' i)) :
    presForm sX f c M hM = presForm sX f c' M' hM' := by
  refine linearMap_ext_relativeClass f fun C hC => ?_
  rw [presForm_relativeClass, presForm_relativeClass]
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ c M c' M' _ _
    (isRIntersectionNumber_sum_degreeOn hM rfl C) (isRIntersectionNumber_sum_degreeOn hM' h C)

/-- The form of the concatenated presentation `∑ a cᵢ Mᵢ + ∑ b c'ⱼ M'ⱼ` is `a φ + b φ'`. -/
private theorem presForm_append {n n' : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (c' : Fin n' → ℝ) (M' : Fin n' → Divisor X)
    (hM' : ∀ i, (M' i).IsCartier) (a b : ℝ) (hMM : ∀ i, (Fin.append M M' i).IsCartier) :
    presForm sX f (Fin.append (a • c) (b • c')) (Fin.append M M') hMM =
      a • presForm sX f c M hM + b • presForm sX f c' M' hM' := by
  refine linearMap_ext_relativeClass f fun C hC => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, presForm_relativeClass,
    presForm_relativeClass, presForm_relativeClass, Fin.sum_univ_add, smul_eq_mul, smul_eq_mul,
    Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · simp only [Fin.append_left, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · simp only [Fin.append_right, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The concatenation of two presentations presents `a D + b D'`. -/
private theorem sum_append_eq {n n' : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (c' : Fin n' → ℝ) (M' : Fin n' → Divisor X) (a b : ℝ) :
    ∑ i, Fin.append (a • c) (b • c') i • Divisor.toRDivisor (Fin.append M M' i) =
      a • ∑ i, c i • Divisor.toRDivisor (M i) + b • ∑ i, c' i • Divisor.toRDivisor (M' i) := by
  rw [Fin.sum_univ_add, Finset.smul_sum, Finset.smul_sum]
  simp [smul_smul]

end Pairing

section Analysis

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

open scoped Classical in
/-- The coefficient of `∑ᵢ yᵢ pᵢ` along `P`. -/
private theorem coeff_sum_single {ι : Type*} [Fintype ι] {R : Type*} [AddCommMonoid R]
    (p : ι → MMP.Mori.PrimeDivisor X) (y : ι → R) (P : MMP.Mori.PrimeDivisor X) :
    (∑ i, Finsupp.single (p i) (y i) : DivisorWithCoeffs R X).coeff P =
      ∑ i, if p i = P then y i else 0 := by
  classical
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- **Adding Cartier divisors to the boundary.** For Cartier divisors `Cᵢ` and a divisor `D` over
`X`, there are numbers `μᵢ` (the orders along `D` of the pull-backs of the `Cᵢ`) such that a log
discrepancy `a` of `D` for `(X, B)` gives the log discrepancy `a - ∑ sᵢ μᵢ` for
`(X, B + ∑ sᵢ Cᵢ)`, for all real `sᵢ`. -/
private theorem exists_isLogDiscrepancy_add_sum {ι : Type*} [Fintype ι] (C : ι → Divisor X)
    (hC : ∀ i, (C i).IsCartier) (D : DivisorOver k sX) :
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

end Analysis

section Exceptional

open TopologicalSpace

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

end Exceptional

section Resolution

/-- The components of an snc subset form a finite set of prime divisors with snc reduced sum. -/
private theorem exists_finset_isSNC {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY]
    (hsm : IsSmoothScheme sY) {T : TopologicalSpace.Closeds Y} (hT : IsSNCSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ (T : Set Y) → F ∈ S := by
  rcases hT with h0 | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, fun F hF => ?_⟩
    · rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
    · rw [h0] at hF
      exact absurd hF (by simp)
  · refine ⟨s, hsnc, fun F hF => ?_⟩
    rw [← hs] at hF
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- A prime divisor of a proper birational model that is not exceptional maps generically onto a
prime divisor `P` of `X`, and its coefficient in the crepant boundary is `coeff_P Δ`. -/
private theorem exists_coeff_eq_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨P, neg_injective ((hΔY G).eq hd), hη⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The lc data of a log resolution of `∑ pᵢ`.** There are finitely many affine functions
`ℓ_s(y) = c_s - ∑ᵢ yᵢ w_{s,i}` with rational `c_s`, `w_{s,i}` (the log discrepancies of the
components `s` of the snc divisor of a log resolution), such that each `ℓ_s(y)` is a log
discrepancy of `(X, ∑ yᵢ pᵢ)`, and for an effective rational `y` with coefficients at most one
the pair `(X, ∑ yᵢ pᵢ)` is log canonical as soon as every `ℓ_s(y)` is nonnegative. -/
private theorem exists_lcResolution_data [IsAlgClosed k] [CharZero k] (hQ : IsQFactorial sX)
    {ι : Type*} [Fintype ι] (p : ι → MMP.Mori.PrimeDivisor X) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) :
    ∃ (σ : Type u) (S : Finset σ) (c : σ → ℚ) (w : σ → ι → ℚ),
      (∀ s ∈ S, ∀ y : ι → ℝ, ∃ D : DivisorOver k sX,
        MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D
          ((c s : ℝ) - ∑ i, y i * (w s i : ℝ))) ∧
      (∀ q : ι → ℚ, (∀ s ∈ S, 0 ≤ (c s : ℝ) - ∑ i, (q i : ℝ) * (w s i : ℝ)) →
        (∀ j, (∑ i, Finsupp.single (p i) (q i) : QDivisor X).coeff (p j) ≤ 1) →
        (∀ P, 0 ≤ (∑ i, Finsupp.single (p i) (q i) : QDivisor X).coeff P) →
        MMP.Intersection.IsLogCanonicalPair sX (∑ i, Finsupp.single (p i) (q i))) := by
  classical
  have hX : IsNormalVariety k sX := hQ.1
  have : MMP.Mori.IsVariety k sX := hX.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  -- Cartier multiples of the `pᵢ`
  choose m hm hmC using fun i => hQ.2 (Finsupp.single (p i) (1 : ℤ))
  set C : ι → Divisor X := fun i => (m i : ℤ) • Finsupp.single (p i) (1 : ℤ) with hCdef
  have hCcoeff : ∀ i Γ, ((C i).coeff Γ : ℝ) = (m i : ℝ) * if p i = Γ then 1 else 0 := by
    intro i Γ
    simp only [hCdef, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp
  have hcoeffrel : ∀ (q : ι → ℚ) (y : ι → ℝ) Γ,
      (∑ i, Finsupp.single (p i) (y i) : RDivisor X).coeff Γ =
        (∑ i, Finsupp.single (p i) ((q i : ℝ)) : RDivisor X).coeff Γ +
          ∑ i, ((y i - q i) / m i) * ((C i).coeff Γ : ℝ) := by
    intro q y Γ
    rw [coeff_sum_single, coeff_sum_single, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hCcoeff]
    have hm0 : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
    split_ifs <;> field_simp <;> ring
  -- the rational boundaries `B_q`
  set BQ : (ι → ℚ) → QDivisor X := fun q => ∑ i, Finsupp.single (p i) (q i) with hBQdef
  have hBQc : ∀ q P, (BQ q).coeff P = ∑ i, if p i = P then q i else 0 :=
    fun q P => coeff_sum_single p q P
  have hBQ : ∀ q : ι → ℚ,
      QDivisor.toRDivisor (BQ q) = ∑ i, Finsupp.single (p i) ((q i : ℝ)) := by
    intro q
    refine Finsupp.ext fun P => ?_
    change (QDivisor.toRDivisor (BQ q)).coeff P =
      (∑ i, Finsupp.single (p i) ((q i : ℝ)) : RDivisor X).coeff P
    rw [QDivisor.coeff_toRDivisor, hBQc, coeff_sum_single, Rat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hQC : ∀ D : Divisor X, (Divisor.toQDivisor D).IsQCartier := fun D => by
    obtain ⟨m', hm', hC'⟩ := hQ.2 D
    exact ⟨(m' : ℤ), by exact_mod_cast hm'.ne', (m' : ℤ) • D, map_zsmul _ _ _, hC'⟩
  have hBQcart : ∀ q, (BQ q).IsQCartier := by
    intro q
    have e : BQ q = ∑ i, q i • Divisor.toQDivisor (Finsupp.single (p i) (1 : ℤ)) := by
      refine Finset.sum_congr rfl fun i _ => Finsupp.ext fun P => ?_
      change Finsupp.single (p i) (q i) P =
        q i * ((Finsupp.single (p i) (1 : ℤ) P : ℤ) : ℚ)
      simp only [Finsupp.single_apply]
      split_ifs <;> simp
    rw [e]
    refine Finset.sum_induction _ QDivisor.IsQCartier (fun _ _ h h' => h.add h') ?_
      fun i _ => MMP.Flips.isQCartier_smul (hQC _) _
    simpa using QDivisor.isQCartier_toQDivisor (Divisor.isCartier_zero (X := X))
  have hpair : ∀ q, IsPairWith sX n K (BQ q) := fun q => ⟨hX, hK, (hQC K).add (hBQcart q)⟩
  -- a log resolution of `∑ pᵢ`
  obtain ⟨Y, f, hf⟩ := exists_isLogResolution sX hX (∑ i, Finsupp.single (p i) (1 : ℝ))
  obtain ⟨hY, hdimY, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsNormal Y := hY.2
  have : IsProper f := hf.isProper
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  set hfb := hf.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G => ⟨Y, f, hY, hfb, G⟩
  have hnY : topologicalKrullDim Y = n := hdimY.trans hn
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hf.isSmoothScheme hnY
  obtain ⟨S, hsncS, hmemS⟩ := exists_finset_isSNC hf.isSmoothScheme hf.isSNCSubset
  have hexcS : ∀ G, (DG G).IsExceptional → G ∈ S := fun G hG =>
    hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
      (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  -- the crepant boundaries `Θ_q` of `(X, B_q)` on `Y`
  have hex : ∀ q, ∃ Θ : QDivisor Y, IsCrepantBoundary sX n K (BQ q) f hY hfb Θ := fun q => by
    obtain ⟨⟨Θ, hΘ, -⟩, -⟩ :=
      MMP.Mori.IsPair.existsUnique_isCrepantBoundary (hpair q).isPair hK f hY hfb
    exact ⟨Θ, hΘ⟩
  choose Θ hΘ using hex
  have hlogG : ∀ q G, MMP.Intersection.IsLogDiscrepancy sX n
      (∑ i, Finsupp.single (p i) ((q i : ℝ))) (DG G) (1 - ((Θ q).coeff G : ℝ)) := fun q G => by
    have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΘ q G)
      (inferInstance : IsProper f)
    rw [hBQ q] at this
    convert this using 1
    push_cast
    ring
  -- log discrepancies are affine in the coefficients
  have hlin : ∀ D : DivisorOver k sX, ∃ w : ι → ℝ, ∀ a₀ : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n
        (∑ i, Finsupp.single (p i) ((((0 : ι → ℚ) i : ℚ)) : ℝ)) D a₀ →
      ∀ y : ι → ℝ, MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (p i) (y i)) D
        (a₀ - ∑ i, y i * w i) := by
    intro D
    obtain ⟨μ, hμ⟩ := exists_isLogDiscrepancy_add_sum C (fun i => hmC i) D
    refine ⟨fun i => μ i / m i, fun a₀ h₀ y => ?_⟩
    have := hμ n _ _ (fun i => (y i - (((0 : ι → ℚ) i : ℚ) : ℝ)) / m i) a₀ h₀ (hcoeffrel 0 y)
    convert this using 2
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.zero_apply, Rat.cast_zero, sub_zero]
    ring
  choose wG hwG using fun G => hlin (DG G)
  set cG : MMP.Mori.PrimeDivisor Y → ℝ := fun G => 1 - ((Θ 0).coeff G : ℝ) with hcG
  have ha : ∀ G (y : ι → ℝ), MMP.Intersection.IsLogDiscrepancy sX n
      (∑ i, Finsupp.single (p i) (y i)) (DG G) (cG G - ∑ i, y i * wG G i) :=
    fun G y => hwG G _ (hlogG 0 G) y
  have hkey : ∀ q G, ((Θ q).coeff G : ℝ) = 1 - (cG G - ∑ i, (q i : ℝ) * wG G i) := fun q G => by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hlogG q G) (ha G _)
    linarith
  have hsupp : ∀ q, (Θ q).support ⊆ S := by
    intro q G hG
    rw [Finsupp.mem_support_iff] at hG
    by_cases hGe : (DG G).IsExceptional
    · exact hexcS G hGe
    obtain ⟨P, hθP, hη⟩ := exists_coeff_eq_of_not_isExceptional (hpair q) hY hfb (hΘ q) hGe
    have hP0 : (BQ q).coeff P ≠ 0 := hθP ▸ hG
    obtain ⟨i, hi⟩ : ∃ i, p i = P := by
      by_contra h
      push Not at h
      exact hP0 (by rw [hBQc]; exact Finset.sum_eq_zero fun i _ => if_neg (h i))
    refine hmemS G (Or.inr ?_)
    change f G.genericPoint ∈ (∑ i, Finsupp.single (p i) (1 : ℝ) : RDivisor X).supp
    rw [hη]
    refine DivisorWithCoeffs.support_subset_supp ?_
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)
    rw [coeff_sum_single]
    exact (Finset.sum_pos' (fun j _ => by split_ifs <;> norm_num)
      ⟨i, Finset.mem_univ _, by simp [hi]⟩).ne'
  -- the discrepancy of `(X, B_q)`, bounded below on the resolution
  have hdisc : ∀ (q : ι → ℚ) (b : ℚ), (∀ G ∈ S, (Θ q).coeff G ≤ 1) →
      (∀ G ∈ S, b ≤ 1 - (Θ q).coeff G) →
      (∀ E ∈ S, ∀ F ∈ S, E ≠ F → (E.support ∩ F.support).Nonempty →
        b ≤ 1 - (Θ q).coeff E - (Θ q).coeff F) → b ≤ 1 →
      (∀ G, (DG G).IsExceptional → b ≤ -(Θ q).coeff G) → 2 ≤ n →
      (((b : ℚ) : ℝ) : EReal) ≤ discrep sX n K (BQ q) := by
    intro q b h0 h1 h2 h3 h4 hn2
    rw [IsCrepantBoundary.discrep_eq_min (hpair q).isPair hK hKY (hΘ q),
      discrep_eq_of_isSNC (f ≫ sX) hY hf.isSmoothScheme hn2 hKY S (hsupp q) hsncS h0]
    refine le_min (le_inf (le_inf ?_ ?_) ?_) ?_
    · exact le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF hm =>
        EReal.coe_le_coe_iff.mpr (by exact_mod_cast h2 E hE F hF hEF hm)
    · exact le_iInf₂ fun G hG => EReal.coe_le_coe_iff.mpr (by exact_mod_cast h1 G hG)
    · exact_mod_cast EReal.coe_le_coe_iff.mpr (by exact_mod_cast h3 : ((b : ℚ) : ℝ) ≤ 1)
    · refine le_sInf ?_
      rintro _ ⟨G, a, hGe, hGa, rfl⟩
      have := (hΘ q G).eq hGa
      refine EReal.coe_le_coe_iff.mpr ?_
      rw [← this]
      exact_mod_cast h4 G hGe
  -- the discrepancy of a divisor over `X` is `a - 1` for a log discrepancy `a`
  have hstart : ∀ (q : ι → ℚ) (n' : ℕ) (D : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n' (∑ i, Finsupp.single (p i) ((q i : ℝ))) D a →
      ∃ c : ℚ, IsDiscrepancy sX n K (BQ q) D c ∧ a = 1 + c := by
    intro q n' D a hDa
    have hn' : n' = n := by
      have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hDa).symm.trans hn
      exact_mod_cast this
    subst hn'
    rw [← hBQ q] at hDa
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hpair q).isPair hK D
    exact ⟨c, hc, ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp hDa).2⟩
  -- the coefficients are rational
  set cQ : MMP.Mori.PrimeDivisor Y → ℚ := fun G => 1 - (Θ 0).coeff G with hcQ
  set wQ : MMP.Mori.PrimeDivisor Y → ι → ℚ :=
    fun G i => (Θ (Pi.single i 1)).coeff G - (Θ 0).coeff G with hwQ
  have hcc : ∀ G, cG G = cQ G := fun G => by simp [hcG, hcQ]
  have hww : ∀ G i, wG G i = wQ G i := fun G i => by
    classical
    have h1 := hkey (Pi.single i 1) G
    have h0 := hkey 0 G
    simp only [Pi.single_apply, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_one, Rat.cast_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply,
      Finset.sum_const_zero, sub_zero] at h1 h0
    simp only [hwQ, Rat.cast_sub]
    linarith
  refine ⟨MMP.Mori.PrimeDivisor Y, S, cQ, wQ, fun G _ y => ⟨DG G, ?_⟩, ?_⟩
  · have h := ha G y
    simp only [hcc, hww] at h
    exact h
  · -- lc for rational coefficients
    intro q hq hcoef hnn
    refine ⟨(hpair q).isPair, hnn, fun n' D a hDa => ?_⟩
    rw [hBQ q] at hDa
    obtain ⟨c, hc, rfl⟩ := hstart q n' D a hDa
    suffices h : -1 ≤ c by
      have : (-1 : ℝ) ≤ c := by exact_mod_cast h
      linarith
    have hθ : ∀ G ∈ S, (Θ q).coeff G ≤ 1 := fun G hG => by
      have h := hkey q G
      have h' := hq G hG
      simp only [hcc, hww] at h
      exact_mod_cast (by linarith : ((Θ q).coeff G : ℝ) ≤ 1)
    by_cases hD : D.IsExceptional
    · have hn2 := two_le_of_isExceptional hX hn hD
      have hdl := hdisc q (-1) hθ (fun G hG => by linarith [hθ G hG])
        (fun E hE F hF _ _ => by linarith [hθ E hE, hθ F hF])
        (by norm_num) (fun G hGe => by linarith [hθ G (hexcS G hGe)]) hn2
      have h' := EReal.coe_le_coe_iff.mp (hdl.trans (discrep_le hD hc))
      exact_mod_cast h'
    · obtain ⟨P, hPv⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
      obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hpair q).isPair hK
        (DivisorOver.ofPrimeDivisor k hX P)
      rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq (hpair q) hPv hc hc',
        hc'.eq_neg_coeff_of_ofPrimeDivisor hX]
      have : (BQ q).coeff P ≤ 1 := by
        by_cases hP : ∃ j, p j = P
        · obtain ⟨j, rfl⟩ := hP
          exact hcoef j
        · rw [hBQc, Finset.sum_eq_zero fun i _ => if_neg fun h => hP ⟨i, h⟩]
          norm_num
      linarith

end Resolution

section PolytopeHelpers

open Set

variable {r : ℕ}

/-- The intersection of two rational polyhedra is a rational polyhedron. -/
private theorem IsRationalPolyhedron.inter {N N' : Set (Fin r → ℝ)} (hN : IsRationalPolyhedron N)
    (hN' : IsRationalPolyhedron N') : IsRationalPolyhedron (N ∩ N') := by
  classical
  obtain ⟨E, I, rfl⟩ := hN
  obtain ⟨E', I', rfl⟩ := hN'
  refine ⟨E ∪ E', I ∪ I', ?_⟩
  ext x
  simp only [mem_inter_iff, mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun f hf => hf.elim (h1 f) (h3 f), fun f hf => hf.elim (h2 f) (h4 f)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun f hf => h1 f (.inl hf), fun f hf => h2 f (.inl hf)⟩,
      fun f hf => h1 f (.inr hf), fun f hf => h2 f (.inr hf)⟩

private theorem ratAffineForm_single (i : Fin r) (c q : ℚ) (x : Fin r → ℝ) :
    ratAffineForm (Pi.single i c, q) x = c * x i + q := by
  classical
  simp only [ratAffineForm]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

/-- A set `{x | ∀ i, lᵢ ≤ xᵢ ≤ uᵢ}` with rational bounds is a rational polyhedron. -/
private theorem isRationalPolyhedron_box (l u : Fin r → ℚ) :
    IsRationalPolyhedron {x : Fin r → ℝ | ∀ i, (l i : ℝ) ≤ x i ∧ x i ≤ u i} := by
  classical
  refine ⟨∅, Finset.univ.image (fun i => (Pi.single i 1, -l i)) ∪
    Finset.univ.image (fun i => (Pi.single i (-1), u i)), ?_⟩
  ext x
  simp only [mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ]
  constructor
  · rintro h f (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> rw [ratAffineForm_single] <;> push_cast <;>
      linarith [(h i).1, (h i).2]
  · intro h i
    have h1 := h _ (.inl ⟨i, rfl⟩)
    have h2 := h _ (.inr ⟨i, rfl⟩)
    rw [ratAffineForm_single] at h1 h2
    push_cast at h1 h2
    constructor <;> linarith

/-- The coordinatewise lower bound `{x | ∀ i, gᵢ ≤ xᵢ}` with rational `g` is a rational
polyhedron. -/
private theorem isRationalPolyhedron_lowerBound (g : Fin r → ℚ) :
    IsRationalPolyhedron {x : Fin r → ℝ | ∀ i, (g i : ℝ) ≤ x i} := by
  classical
  refine ⟨∅, Finset.univ.image (fun i => (Pi.single i 1, -g i)), ?_⟩
  ext x
  simp only [mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    Finset.mem_image, Finset.mem_univ]
  constructor
  · rintro h f ⟨i, rfl⟩
    rw [ratAffineForm_single]; push_cast; linarith [h i]
  · intro h i
    have h1 := h _ ⟨i, rfl⟩
    rw [ratAffineForm_single] at h1
    push_cast at h1
    linarith

/-- A rational parallelotope is the convex hull of finitely many rational points (its corners). -/
private theorem IsRationalParallelotope.exists_finset {Q : Set (Fin r → ℝ)}
    (hQ : IsRationalParallelotope Q) :
    ∃ V : Finset (Fin r → ℚ), Q = convexHull ℝ ((fun v i => (v i : ℝ)) '' (V : Set (Fin r → ℚ))) := by
  classical
  obtain ⟨d, p, e, a, b, -, hab, rfl⟩ := hQ
  let φ : (Fin d → ℝ) →ᵃ[ℝ] (Fin r → ℝ) :=
    (Fintype.linearCombination ℝ (fun i j => (e i j : ℝ))).toAffineMap +
      AffineMap.const ℝ _ (fun j => (p j : ℝ))
  have hφ : ∀ s j, φ s j = (p j : ℝ) + ∑ i, s i * (e i j : ℝ) := fun s j => by
    simp [φ, Fintype.linearCombination_apply, add_comm]
  let corner : (Fin d → Bool) → Fin r → ℚ := fun c j => p j + ∑ i, (if c i then b i else a i) * e i j
  let C : Set (Fin d → ℝ) := univ.pi fun i => {(a i : ℝ), (b i : ℝ)}
  refine ⟨Finset.univ.image corner, ?_⟩
  have hbox : (univ.pi fun i => Icc (a i : ℝ) (b i)) = convexHull ℝ C := by
    rw [convexHull_pi]
    refine pi_congr rfl fun i _ => ?_
    rw [convexHull_pair, segment_eq_Icc (by exact_mod_cast (hab i).le)]
  have hV : (fun v i => (v i : ℝ)) '' ((Finset.univ.image corner : Finset _) : Set (Fin r → ℚ)) =
      φ '' C := by
    ext x
    simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_image, mem_range]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨fun i => ((if c i then b i else a i : ℚ) : ℝ), fun i _ => ?_, ?_⟩
      · by_cases h : c i <;> simp [h]
      · funext j
        rw [hφ]
        simp only [corner]
        push_cast
        exact congrArg _ (Finset.sum_congr rfl fun i _ => by by_cases h : c i <;> simp [h])
    · rintro ⟨s, hs, rfl⟩
      have hs' : ∀ i, s i = ((if decide (s i = b i) then b i else a i : ℚ) : ℝ) := fun i => by
        rcases hs i (mem_univ i) with h | h <;> by_cases h' : s i = b i <;> simp_all
      refine ⟨corner fun i => decide (s i = b i), ⟨_, rfl⟩, ?_⟩
      funext j; rw [hφ]; simp only [corner]; push_cast
      exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [← hs' i])
  rw [hV, ← AffineMap.image_convexHull, ← hbox]
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Set.mem_univ_pi.2 hs, funext fun j => hφ s j⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Set.mem_univ_pi.1 hs, funext fun j => hφ s j⟩
/-- A divisor supported on the injective family `p` is the sum of its coefficients along `p`. -/
private theorem eq_sum_single_coeff {R : Type*} [AddCommMonoid R] {Y : Scheme.{u}}
    {p : Fin r → MMP.Mori.PrimeDivisor Y} (hp : Function.Injective p)
    {D : DivisorWithCoeffs R Y}
    (hD : ∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) :
    D = ∑ i, Finsupp.single (p i) (D.coeff (p i)) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum_of_support_subset D (s := Finset.univ.image p) (g := Finsupp.single)
    (fun P hP => by simpa using hD P (by simpa [DivisorWithCoeffs.coeff_apply] using hP))
    (fun _ _ => Finsupp.single_zero _), Finset.sum_image fun i _ j _ h => hp h]
  rfl

/-- Casting the coefficients of `∑ᵢ vᵢ pᵢ` from `ℚ` to `ℝ`. -/
private theorem toRDivisor_sum_single {Y : Scheme.{u}} (p : Fin r → MMP.Mori.PrimeDivisor Y)
    (v : Fin r → ℚ) :
    QDivisor.toRDivisor (∑ i, Finsupp.single (p i) (v i)) =
      ∑ i, Finsupp.single (p i) (v i : ℝ) := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => DivisorWithCoeffs.ext' fun P => ?_
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

end PolytopeHelpers

section PrimeDivisorDiscrepancy

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The log discrepancy of a prime divisor `P` of `X` with respect to an `ℝ`-divisor `B` with
`K + B` `ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [CompactSpace X] (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor k hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor k hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor k hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

end PrimeDivisorDiscrepancy

section Polytope

/-- **Effective real lc boundaries lie in a rational lc polytope.** On a normal `ℚ`-factorial
variety over `ℂ`, two effective real lc boundaries `B`, `E` lie in the convex hull of finitely many
effective rational boundaries `V i` with every `(X, V i)` log canonical. -/
private theorem exists_lcPolytope {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hXq : IsQFactorial sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 4) {B E : RDivisor X} (hB : IsRealLcPair sX B)
    (hE : IsRealLcPair sX E) :
    ∃ (ι : Type) (_ : Fintype ι) (V : ι → QDivisor X), (∀ i P, 0 ≤ (V i).coeff P) ∧
      (∀ i, MMP.Intersection.IsLogCanonicalPair sX (V i)) ∧
      B ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)) ∧
      E ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)) := by
  classical
  -- the joint support, as an injective family `p : Fin r → PrimeDivisor X`
  set T : Finset (MMP.Mori.PrimeDivisor X) := B.support ∪ E.support with hT
  let p : Fin T.card → MMP.Mori.PrimeDivisor X := fun i => (T.equivFin.symm i : _)
  have hp : Function.Injective p := Subtype.val_injective.comp T.equivFin.symm.injective
  have hTp : ∀ P ∈ T, P ∈ Set.range p := fun P hP =>
    ⟨T.equivFin ⟨P, hP⟩, by simp [p]⟩
  have hBp : ∀ P, B.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    hTp P (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hP))
  have hEp : ∀ P, E.coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    hTp P (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hP))
  obtain ⟨σ, S, c, w, hlog, hlc⟩ := exists_lcResolution_data hXq p hK
  -- the lc polyhedron `N` in the coefficient space
  have hform : ∀ s (y : Fin T.card → ℝ), ratAffineForm (fun i => -w s i, c s) y =
      (c s : ℝ) - ∑ i, y i * (w s i : ℝ) := fun s y => by
    simp only [ratAffineForm, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
    rw [show ∑ i, (w s i : ℝ) * y i = ∑ i, y i * (w s i : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    ring
  set N : Set (Fin T.card → ℝ) :=
    {y | ∀ s ∈ S, 0 ≤ (c s : ℝ) - ∑ i, y i * (w s i : ℝ)} ∩
      {x | ∀ i, (((0 : Fin T.card → ℚ) i : ℚ) : ℝ) ≤ x i ∧ x i ≤ ((1 : Fin T.card → ℚ) i : ℚ)}
    with hNdef
  have hN : IsRationalPolyhedron N := by
    refine IsRationalPolyhedron.inter ⟨∅, S.image fun s => (fun i => -w s i, c s), ?_⟩
      (isRationalPolyhedron_box 0 1)
    ext y
    simp only [Set.mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      true_and, Finset.mem_image]
    constructor
    · rintro h _ ⟨s, hs, rfl⟩
      rw [hform]; exact h s hs
    · intro h s hs
      rw [← hform]; exact h _ ⟨s, hs, rfl⟩
  -- the coefficient vector of an effective real lc boundary on the support lies in `N`
  have hmemN : ∀ D : RDivisor X, IsRealLcPair sX D → (∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) →
      (fun i => D.coeff (p i)) ∈ N := by
    intro D hD hDp
    have hDeq := eq_sum_single_coeff hp hDp
    refine ⟨fun s hs => ?_, fun i => ⟨?_, ?_⟩⟩
    · obtain ⟨Dv, hDv⟩ := hlog s hs fun i => D.coeff (p i)
      rw [← hDeq] at hDv
      exact hD.2.2.2 4 Dv _ hDv
    · simpa using hD.2.1 (p i)
    · obtain ⟨hnv, -, ⟨n', K', hK', hKD⟩, hla⟩ := hD
      have := hla n' _ _ (isLogDiscrepancy_ofPrimeDivisor hnv hK' hKD (p i))
      simp only [Pi.one_apply, Rat.cast_one]
      linarith
  -- a rational polytope with vertices in `N` around such a coefficient vector
  have hfin : ∀ D : RDivisor X, IsRealLcPair sX D → (∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) →
      ∃ W : Finset (Fin T.card → ℚ), (∀ v ∈ W, (fun i => (v i : ℝ)) ∈ N) ∧
        (fun i => D.coeff (p i)) ∈
          convexHull ℝ ((fun v i => (v i : ℝ)) '' (W : Set (Fin T.card → ℚ))) := by
    intro D hD hDp
    obtain ⟨-, Q, hQ, hQN, hδQ, -⟩ := rational_hull_neighborhood hN (hmemN D hD hDp)
    obtain ⟨W, rfl⟩ := IsRationalParallelotope.exists_finset hQ
    exact ⟨W, fun v hv => (hQN (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)).1,
      intrinsicInterior_subset hδQ⟩
  obtain ⟨WB, hWB, hBW⟩ := hfin B hB hBp
  obtain ⟨WE, hWE, hEW⟩ := hfin E hE hEp
  set W := WB ∪ WE
  have hWN : ∀ v ∈ W, (fun i => (v i : ℝ)) ∈ N := fun v hv =>
    (Finset.mem_union.mp hv).elim (hWB v) (hWE v)
  -- the rational boundaries of the vertices
  let Vd : W → QDivisor X := fun v => ∑ i, Finsupp.single (p i) (v.1 i)
  have hcoeffV : ∀ (v : Fin T.card → ℚ) j,
      (∑ i, Finsupp.single (p i) (v i) : QDivisor X).coeff (p j) = v j := fun v j => by
    rw [coeff_sum_single, Finset.sum_eq_single j (fun i _ hij => if_neg (hp.ne hij))
      (by simp)]
    simp
  have hV0 : ∀ v : W, ∀ P, 0 ≤ (Vd v).coeff P := fun v P => by
    rw [coeff_sum_single]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs
    · have := ((hWN v.1 v.2).2 i).1
      simp only [Pi.zero_apply, Rat.cast_zero] at this
      exact_mod_cast this
    · exact le_rfl
  refine ⟨W, inferInstance, Vd, hV0, fun v => ?_, ?_⟩
  · refine hlc v.1 (fun s hs => (hWN v.1 v.2).1 s hs) (fun j => ?_) (hV0 v)
    rw [hcoeffV]
    have := ((hWN v.1 v.2).2 j).2
    simp only [Pi.one_apply, Rat.cast_one] at this
    exact_mod_cast this
  -- `B` and `E` are images of points of the polytopes under the coefficient map
  let Φ : (Fin T.card → ℝ) →ₗ[ℝ] RDivisor X :=
    ∑ i, (Finsupp.lsingle (p i)).comp (LinearMap.proj i)
  have hΦ : ∀ y, Φ y = ∑ i, Finsupp.single (p i) (y i) := fun y => by
    simp [Φ, LinearMap.sum_apply]
  have hsub : ∀ W' ⊆ W, Φ '' ((fun v i => (v i : ℝ)) '' (W' : Set (Fin T.card → ℚ))) ⊆
      Set.range fun v : W => QDivisor.toRDivisor (Vd v) := by
    rintro W' hW' _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hW' hv⟩, by rw [hΦ]; exact toRDivisor_sum_single p v⟩
  have hmem : ∀ D : RDivisor X, (∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) → ∀ W' ⊆ W,
      (fun i => D.coeff (p i)) ∈
        convexHull ℝ ((fun v i => (v i : ℝ)) '' (W' : Set (Fin T.card → ℚ))) →
      D ∈ convexHull ℝ (Set.range fun v : W => QDivisor.toRDivisor (Vd v)) := by
    intro D hDp W' hW' hD
    have h := Set.mem_image_of_mem Φ hD
    rw [LinearMap.image_convexHull, hΦ, ← eq_sum_single_coeff hp hDp] at h
    exact convexHull_mono (hsub W' hW') h
  exact ⟨hmem B hBp WB Finset.subset_union_left hBW, hmem E hEp WE Finset.subset_union_right hEW⟩

end Polytope

section Endgame

/-- A sum over indices weighted by nonnegative `w` only sees the indices of positive weight. -/
private theorem sum_subtype_pos_eq_sum {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (F : ι → M) (hF : ∀ j, w j = 0 → F j = 0) :
    ∑ j : {j // 0 < w j}, F j.1 = ∑ j, F j := by
  classical
  rw [← Finset.subtype_univ, Finset.sum_subtype_eq_sum_filter (p := fun j => 0 < w j) (f := F),
    Finset.sum_filter_of_ne]
  intro j _ hj
  by_contra h
  exact hj (hF j (le_antisymm (not_lt.mp h) (hw j)))

/-- **The radial gap.** If `D · L ≥ 0`, `D · L > 0` forces `D · L ≥ τ`, `(K + E) · L ≥ -8` and
`D_t · L = (1 - t) (D · L) + t ((K + E) · L) < 0` for some `0 < t < 1` with `t (τ + 8) < τ`,
then `D · L = 0`. -/
private theorem eq_zero_of_radial_gap {τ t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (htτ : t * (τ + 8) < τ) (ha : 0 ≤ a) (hgap : 0 < a → τ ≤ a) (hb : -8 ≤ b)
    (hneg : (1 - t) * a + t * b < 0) : a = 0 :=
  le_antisymm (not_lt.mp fun hpos => by nlinarith [hgap hpos]) ha

/-- A linear form vanishing at a nonzero point of an extremal ray vanishes on the whole ray. -/
private theorem IsExtremalRay.map_eq_zero {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {N R : Set V}
    (hR : IsExtremalRay 𝕜 N R) (φ : V →ₗ[𝕜] 𝕜) {ℓ : V} (hℓR : ℓ ∈ R) (hℓ : ℓ ≠ 0)
    (h : φ ℓ = 0) : ∀ u ∈ R, φ u = 0 := by
  obtain ⟨v, -, rfl⟩ := hR.2
  obtain ⟨a, -, rfl⟩ := hℓR
  rintro _ ⟨b, -, rfl⟩
  have ha : a ≠ 0 := by rintro rfl; exact hℓ (zero_smul _ _)
  rw [map_smul, smul_eq_mul] at h
  rw [map_smul, (mul_eq_zero.mp h).resolve_left ha, smul_zero]

end Endgame

open MMP.Flips in
private theorem solution :
    ∀ {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B E : RDivisor X} (hB : IsRealLcPair sX B) (hE : IsRealLcPair sX E)
    (hD : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K B)),
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R →
        (∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          (1 - t) • (Divisor.toRDivisor K + B) + t • (Divisor.toRDivisor K + E) =
              ∑ i, c i • Divisor.toRDivisor (M i) ∧
            ∀ u ∈ R, u ≠ 0 →
              ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) →
        ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) = 0 := by
  intro X Z _ _ _ _ sX sZ hX hZ f hf hXq K hK B E hB hE hD
  obtain ⟨ι, _, V, hV0, hV, hBP, hEP⟩ := exists_lcPolytope hXq hK hB hE
  -- `B` as a positive convex combination of rational lc points of the polytope
  obtain ⟨ι', _, w, z, hw0, hw1, hz, hwz⟩ := mem_convexHull_iff_exists_fintype.mp hBP
  choose g hg using hz
  simp only at hg
  let κ := {j : ι' // 0 < w j}
  have hsubR : ∑ j : κ, w j.1 = 1 := (sum_subtype_pos_eq_sum hw0 w fun _ h => h).trans hw1
  obtain ⟨τ, hτ, hgap⟩ :=
    exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le hX hZ hf hXq hK hV0 hV
      hBP (κ := κ) (r := fun j => w j.1) (fun j => j.2) hsubR (Bj := fun j => V (g j.1))
      (fun j => subset_convexHull ℝ _ ⟨g j.1, rfl⟩) (fun j => hV _) (by
        rw [← hwz, sum_subtype_pos_eq_sum hw0 (fun j => w j • QDivisor.toRDivisor (V (g j)))
          (fun j hj => by rw [hj, zero_smul])]
        exact Finset.sum_congr rfl fun j _ => by rw [hg j])
  refine ⟨τ / (τ + 8), div_pos hτ (by linarith), ?_⟩
  intro t ht0 htt R hR ⟨n, c, M, hM, heq, hneg⟩ n' c' M' hM' heq' u hu
  have ht1 : t < 1 := htt.trans ((div_lt_one (by linarith)).mpr (by linarith))
  have htτ : t * (τ + 8) < τ := (lt_div_iff₀ (by linarith)).mp htt
  -- the nearby adjoint is `K + B'` for the point `B' = (1 - t) B + t E` of the polytope
  have hB'P : (1 - t) • B + t • E ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)) :=
    convex_convexHull ℝ _ hBP hEP (by linarith) ht0.le (by ring)
  have hKB' : Divisor.toRDivisor K + ((1 - t) • B + t • E) = ∑ i, c i • Divisor.toRDivisor (M i) := by
    rw [← heq]; module
  obtain ⟨L, hLc, -, hLR, hL0, h8, hτL⟩ := hgap R hR ⟨_, hB'P, n, c, M, hM, hKB', hneg⟩
  set ℓ := L.relativeClass f hLc
  -- a presentation of `K + E`
  set cE := Fin.append ((1 / t) • c) ((-(1 - t) / t) • c') with hcE
  set ME := Fin.append M M' with hMEdef
  have hME : ∀ i, (ME i).IsCartier := fun i =>
    Fin.addCases (motive := fun i => (Fin.append M M' i).IsCartier)
      (fun i => by simpa using hM i) (fun i => by simpa using hM' i) i
  have hKE : Divisor.toRDivisor K + E = ∑ i, cE i • Divisor.toRDivisor (ME i) := by
    rw [sum_append_eq, ← heq, ← heq']
    match_scalars <;> field_simp <;> ring
  -- the forms of `D`, `K + E` and `D_t`
  have hMM : ∀ i, (Fin.append M' ME i).IsCartier := fun i =>
    Fin.addCases (motive := fun i => (Fin.append M' ME i).IsCartier)
      (fun i => by simpa using hM' i) (fun i => by simpa using hME i) i
  have hlin : presForm sX f c M hM =
      (1 - t) • presForm sX f c' M' hM' + t • presForm sX f cE ME hME := by
    rw [← presForm_append f c' M' hM' cE ME hME (1 - t) t hMM]
    refine presForm_eq_of_eq f hM hMM ?_
    rw [sum_append_eq, ← heq', ← hKE, heq]
  have hneg' : presForm sX f c M hM ℓ < 0 := by
    rw [presForm_apply]; exact hneg ℓ hLR hL0
  have h8' : -8 ≤ presForm sX f cE ME hME ℓ := by
    rw [presForm_apply]; exact h8 E hEP _ cE ME hME hKE
  have hτ' : 0 < presForm sX f c' M' hM' ℓ → τ ≤ presForm sX f c' M' hM' ℓ := by
    rw [presForm_apply]; exact hτL _ c' M' hM' heq'
  -- nefness of `D` over `Z`
  have hnef : 0 ≤ presForm sX f c' M' hM' ℓ := by
    obtain ⟨m, r, L₀, hL₀, hDeq, hDnef⟩ := hD
    have hDeq' : Divisor.toRDivisor K + B = ∑ j, r j • Divisor.toRDivisor (L₀ j) := hDeq
    rw [← presForm_eq_of_eq f hL₀ hM' (hDeq'.symm.trans heq'), presForm_relativeClass]
    exact hDnef L hLc _ (isRIntersectionNumber_sum_degreeOn hL₀ hDeq L)
  have hzero : presForm sX f c' M' hM' ℓ = 0 :=
    eq_zero_of_radial_gap ht0 ht1 htτ hnef hτ' h8' (by simpa [hlin] using hneg')
  -- `D` vanishes on the ray spanned by `[L]`
  rw [← presForm_apply f c' M' hM']
  exact IsExtremalRay.map_eq_zero hR _ hLR hL0 hzero u hu

end ErasedIntegral

end Proof_lem_fourfold_real_lc_radial_null_ray

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Nearby negative rays are null for a nef real lc adjoint.** Let `f : X ⟶ Z` be a morphism of
projective complex varieties, `X` normal `ℚ`-factorial of dimension four with canonical divisor
`K`, let `(X, B)` and `(X, E)` be log canonical pairs with effective real boundaries
(`MMP.Fourfold.IsRealLcPair`), and suppose `D = K + B` is nef over `Z`. Then there is `t₀ > 0`
such that for every `0 < t < t₀`, every extremal ray `R` of `NE̅(X/Z)` on which
`(1 - t) D + t (K + E)` is negative (for some presentation by Cartier divisors) is `D`-null: the
pairing of `D` with every class in `R`, computed from any presentation of `D` by Cartier
divisors, is zero. -/
@[mmp "lem_fourfold_real_lc_radial_null_ray"]
public theorem exists_pos_forall_isExtremalRay_null_of_isRealLcPair
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hXq : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B E : RDivisor X} (hB : IsRealLcPair sX B) (hE : IsRealLcPair sX E)
    (hD : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K B)) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ R : Set (RelativeNumericalCurveClasses sX f),
        IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) R →
        (∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          (1 - t) • (Divisor.toRDivisor K + B) + t • (Divisor.toRDivisor K + E) =
              ∑ i, c i • Divisor.toRDivisor (M i) ∧
            ∀ u ∈ R, u ≠ 0 →
              ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
                RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) < 0) →
        ∀ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier),
          Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
          ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX f (M i).divisorialSheaf u) = 0 :=
              by revert X Z sX sZ hX hZ f hf hXq K hK B E hB hE hD; first | exact Proof_lem_fourfold_real_lc_radial_null_ray.solution | exact Proof_lem_fourfold_real_lc_radial_null_ray.solution _ | exact Proof_lem_fourfold_real_lc_radial_null_ray.solution _ _ | exact Proof_lem_fourfold_real_lc_radial_null_ray.solution _ _ _ | exact Proof_lem_fourfold_real_lc_radial_null_ray.solution _ _ _ _

end MMP.Fourfold

