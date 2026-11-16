module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Basic
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# A real canonical flip has a rational canonical witness

Let `X ⟶ Z ⟵ X⁺` be a step of an extremal real flip sequence of `ℚ`-factorial quasi-projective
complex threefolds, with real boundary `B` on `X` and strict transform `B⁺` on `X⁺`. If `(X, B)`
is real canonical, then so is `(X⁺, B⁺)`. Moreover the same diagram is an extremal flip for a
rational boundary: there is a `ℚ`-divisor `B₀` on `X` such that `(X, B₀)` and
`(X⁺, (f⁺)⁻¹_* f_* B₀)` are real canonical (in particular `B₀` is effective with coefficients
less than one) and `X ⟶ Z ⟵ X⁺` is a step of an extremal real flip sequence for `B₀`, with the
same canonical divisors.

## Main results

* `MMP.Fourfold.IsRealFlipStep.exists_isRealCanonicalPair_qDivisor`

## Implementation notes

The rational witness is a `ℚ`-divisor `B₀ : QDivisor X`; its transform on `X⁺` is the
`ℚ`-divisor `MMP.Mori.flipTransform f fp B₀`, and both are viewed as real divisors through
`MMP.Mori.QDivisor.toRDivisor`. Effectivity of `B₀` and the bound `< 1` on its coefficients are
part of `MMP.Fourfold.IsRealCanonicalPair`.

The proof resolves only `X`. Every exceptional divisor over `X⁺` has a centre on `X`, and the
comparison of discrepancies over `Z` (for `-(K + B)` nef over `Z` and `K⁺ + B⁺` nef over `Z`)
shows that its log discrepancy with respect to `(X⁺, B⁺)` is at least the one with respect to
`(X, B)`; so `(X⁺, B⁺)` is real canonical. For the witness write `B = ∑ bᵢ Pᵢ`. On a log
resolution `μ : Y ⟶ X` of `(X, B)` the log discrepancies of the prime divisors of `Y`, and of the
blow-ups of the codimension two strata of the snc divisor, are rational affine functions of the
coefficient vector. The conditions "exceptional log discrepancies at least `1`, log discrepancies
nonnegative, and the crepant coefficients of every pair of meeting components sum to at most `1`"
are finitely many rational affine inequalities holding at `b`; they persist near `b` in the
smallest rational affine subspace through `b`, and at a rational point of it the snc discrepancy
formula makes the pair canonical. Relative ampleness persists under small perturbations, so a
rational point close to `b` gives `B₀`, and the first part applied to the rational step shows
that `(X⁺, (f⁺)⁻¹_* f_* B₀)` is real canonical.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.30–2.32
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MMP.Mori
open scoped WithZero

universe u

namespace MMP.Fourfold

/-- A scheme separated over an affine scheme is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {R : CommRingCat.{u}} {X : Scheme.{u}}
    (s : X ⟶ Spec R) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec R ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A canonical divisor of some index on a variety of dimension `d` is canonical of index `d`. -/
private theorem isCanonicalDivisor_of_topologicalKrullDim_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {K : Divisor X} {d : ℕ} (hd : topologicalKrullDim X = d)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) :
    K.IsCanonicalDivisor sX d := by
  obtain ⟨m, hm⟩ := hK
  obtain rfl : m = d := by exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hd
  exact hm

/-! ### Exceptional divisors and crepant boundaries over a proper birational model -/

section Crepant

variable {k : Type u} [Field k]

/-- A divisor `(Y, f, E)` over a normal variety is exceptional exactly when its center has
codimension at least two. -/
private theorem isExceptional_iff_two_le_codimension {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have := isSeparated_toTerminal sX
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe]

/-- A divisor over a normal variety `X` is exceptional exactly when its valuation is that of no
prime divisor of `X`. -/
private theorem isExceptional_iff_forall_valuation_ne {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    D.IsExceptional ↔
      ∀ P : MMP.Mori.PrimeDivisor X,
        D.valuation ≠ (DivisorOver.ofPrimeDivisor k hX P).valuation :=
  (isExceptional_iff_two_le_codimension hX D).trans
    (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D)

/-- Being exceptional depends only on the valuation. -/
private theorem isExceptional_of_valuation_eq {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    {D D' : DivisorOver k sX} (h : D.valuation = D'.valuation) (hD : D.IsExceptional) :
    D'.IsExceptional :=
  (isExceptional_iff_forall_valuation_ne hX D').mpr fun P hP =>
    (isExceptional_iff_forall_valuation_ne hX D).mp hD P (h.trans hP)

/-- The generic point of a prime divisor of a normal variety `X` lies in the biregular locus of
a proper birational morphism `f : Y ⟶ X` of varieties. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsNormal X] (hX : MMP.Mori.IsVariety k sX) {f : Y ⟶ X} (hY : MMP.Mori.IsVariety k (f ≫ sX))
    [IsProper f] (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ biregularLocus f := by
  have h := two_le_closedsCodimension_compl_biregularLocus sX f (hY := hX) (hX := hY) hf
  by_contra hP
  have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h) P.genericPoint hP
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- The valuation of the divisor `(Y, f, G)` over `X` is the valuation of the prime divisor `G`
of `Y`, read on `k(X)` through `f^*`. -/
private theorem valuation_mk_eq_comap {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (G : MMP.Mori.PrimeDivisor Y) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).valuation =
      (DivisorOver.ofPrimeDivisor k hY G).valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  ext t
  change G.divisorialValuation (functionFieldMap f t) =
    G.divisorialValuation (functionFieldMap (𝟙 Y) (functionFieldMap f t))
  rw [functionFieldMap_id_apply]

/-- **Divisors over `X` lift to a proper birational model.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, every divisor `D` over `X` has the valuation of a divisor `E`
over `Y`, read on `k(X)` through `f^*`: by the valuative criterion the valuation ring of `ord_D`
dominates the local ring of a point of `Y`. -/
private theorem exists_divisorOver_comap_eq {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    [IsProper f] (D : DivisorOver k sX) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    ∃ E : DivisorOver k (f ≫ sX), D.valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  -- `ξ` dominates the local ring of a point of `Y` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : Y, (∀ a : Y.presheaf.stalk x,
      ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := by
      intro b
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
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
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
        Y.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (Y.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : Y.presheaf.stalk x,
        algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]
      exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  refine ⟨D'.toDivisorOver, ?_⟩
  change D.valuation = D'.valuation.comap (functionFieldMap f)
  rw [hv, hξ]

/-- The components of the snc subset `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)` form a finite set of prime
divisors whose reduced sum is snc. -/
private theorem exists_finset_isSNC {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {T : Closeds Y} (hT : IsSNCSubset sY T) :
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

variable [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
  [IsProper f]

omit [IsAlgClosed k] in
/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, a prime divisor `G` of
`Y` that is not `f`-exceptional is the birational transform of a prime divisor `P` of `X`, and the
crepant boundary `Δ_Y` has `coeff_G(Δ_Y) = coeff_P(Δ)`. -/
private theorem exists_coeff_eq_of_not_isExceptional (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint ∧ inverseTransformPrimeDivisor f P = some G := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine ⟨P, neg_injective ((hΔY G).eq hd), hη, ?_⟩
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ genericPoint_mem_biregularLocus hP.1.1 hY.1 hf P)

omit [IsAlgClosed k] [CharZero k] in
/-- A divisor over `Y` which is exceptional over `Y` is exceptional over `X`, for a proper
birational morphism `f : Y ⟶ X` of normal varieties. -/
private theorem isExceptional_compDivisorOver [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    {E : DivisorOver k (f ≫ sX)} (hE : E.IsExceptional) :
    (compDivisorOver f hY hf E).IsExceptional := by
  have : IsDominant f := hf.isDominant
  have hv := valuation_compDivisorOver f hY hf E
  by_contra hne
  obtain ⟨P, hPv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hne
  obtain ⟨G, -, hηG⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
    (genericPoint_mem_biregularLocus hX.1 hY.1 hf P)
  have hGv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
    (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX) P hηG
  refine (isExceptional_iff_forall_valuation_ne hY E).mp hE G ?_
  ext t
  obtain ⟨s, rfl⟩ := hf.functionFieldMap_bijective.2 t
  exact congrArg (· s)
    (hv.symm.trans <| hPv.trans <| hGv.symm.trans <| valuation_mk_eq_comap f hY hf G)

/-- **The discrepancy via a proper birational model.** Let `f : Y ⟶ X` be a proper birational
morphism from a normal variety with canonical divisor `K_Y`, and `Δ_Y` the crepant boundary of
`(X, Δ)` on `Y`. Then `discrep(X, Δ)` is the minimum of `discrep(Y, Δ_Y)` and the discrepancies
`a(E, X, Δ)` of the `f`-exceptional prime divisors `E` of `Y`. -/
private theorem discrep_eq_min_of_isCrepantBoundary [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hP : IsPairWith sX n K Δ) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (a : MMP.Mori.PrimeDivisor Y → ℚ)
    (ha : ∀ E : MMP.Mori.PrimeDivisor Y, (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional →
      IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ (a E)) :
    discrep sX n K Δ = min (discrep (f ≫ sX) n KY ΔY)
      (⨅ (E : MMP.Mori.PrimeDivisor Y) (_ : (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional),
        ((a E : ℝ) : EReal)) := by
  obtain ⟨hX, hK, -⟩ := id hP
  have : IsDominant f := hf.isDominant
  obtain ⟨-, hcr⟩ := IsPair.isDiscrepancy_iff_of_crepant hP.isPair f hY hf hK hKY (Or.inl hΔY)
  refine le_antisymm (le_min ?_ (le_iInf₂ fun E hE => discrep_le hE (ha E hE))) ?_
  · -- a divisor exceptional over `Y` is exceptional over `X`, with the same discrepancy
    refine le_discrep_iff.mpr fun E b hE hb => ?_
    exact discrep_le (isExceptional_compDivisorOver hX hY hf hE)
      ((hcr E _ (valuation_compDivisorOver f hY hf E) b).mp hb)
  · -- a divisor exceptional over `X` is a divisor over `Y`, exceptional or a prime divisor of `Y`
    refine le_discrep_iff.mpr fun D b hD hb => ?_
    obtain ⟨E, hE⟩ := exists_divisorOver_comap_eq hY hf D
    by_cases hEx : E.IsExceptional
    · exact (min_le_left _ _).trans (discrep_le hEx ((hcr E D hE b).mpr hb))
    obtain ⟨G, hGv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hY E hEx
    have hval : D.valuation = (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).valuation := by
      rw [hE, hGv]
      exact (valuation_mk_eq_comap f hY hf G).symm
    have hGe := isExceptional_of_valuation_eq hX hval hD
    rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hval hb (ha G hGe)]
    exact (min_le_right _ _).trans (iInf₂_le G hGe)

end Crepant

/-! ### Log discrepancies as functions of the boundary -/

section Affine

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- On a `ℚ`-factorial normal variety, the log discrepancy `a(D, X, ∑ xᵢ Pᵢ)` of a fixed divisor
`D` over `X` (with proper structure map) is a rational affine function of the coefficient vector
`x ∈ ℝʳ`: write `K + ∑ xᵢ Pᵢ = (1/m₀)(m₀K) + ∑ (xᵢ/mᵢ)(mᵢPᵢ)` with Cartier `m₀K`, `mᵢPᵢ`. -/
private theorem exists_ratAffineForm_isLogDiscrepancy (hQ : MMP.Fourfold.IsQFactorial sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {r : ℕ}
    (P : Fin r → MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX) (hD : IsProper D.f) :
    ∃ g : (Fin r → ℚ) × ℚ, ∀ x : Fin r → ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (∑ i, Finsupp.single (P i) (x i)) D
        (MMP.Fourfold.ratAffineForm g x) := by
  classical
  obtain ⟨hX, hQf⟩ := hQ
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m₀, hm₀, hm₀C⟩ := hQf K
  choose m hm hmC using fun i => hQf (Finsupp.single (P i) (1 : ℤ))
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  let C : Fin (r + 1) → Divisor X :=
    Fin.cons ((m₀ : ℤ) • K) fun i => (m i : ℤ) • Finsupp.single (P i) 1
  have hC : ∀ j, (C j).IsCartier := Fin.cases hm₀C hmC
  choose C' hC' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC j)
  have hm₀' : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hm' : ∀ i, (m i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hm i).ne'
  refine ⟨(fun i => -((C' i.succ).coeff D.E : ℚ) / m i,
    1 + D.ordPullback ω - ((C' 0).coeff D.E : ℚ) / m₀), fun x => ?_⟩
  refine ⟨hX, hD, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, r + 1,
    Fin.cons (1 / (m₀ : ℝ)) fun i => x i / m i, C, C', hC, fun Γ => ?_, fun j => ⟨_, hC' j⟩, ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [C, Fin.cons_zero, Fin.cons_succ, DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.finset_sum_apply, Finsupp.single_apply, hω Γ, Int.cast_mul,
      Int.cast_natCast]
    rw [show (1 / (m₀ : ℝ)) * ((m₀ : ℝ) * (K Γ : ℝ)) = K Γ by field_simp]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        split_ifs <;> simp [hm' i]
  · simp only [MMP.Fourfold.ratAffineForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    push_cast
    rw [show ∑ i : Fin r, x i / (m i : ℝ) * ((C' i.succ).coeff D.E : ℝ) =
        ∑ i : Fin r, -(-((C' i.succ).coeff D.E : ℝ) / (m i : ℝ)) * x i from
      Finset.sum_congr rfl fun i _ => by field_simp]
    simp only [neg_neg, neg_div, neg_mul, Finset.sum_neg_distrib]
    ring

end Affine

/-! ### Canonicity at rational points near a real canonical boundary -/

section RationalHull

variable {r : ℕ}

private theorem ratAffineForm_add (g g' : (Fin r → ℚ) × ℚ) (x : Fin r → ℝ) :
    ratAffineForm (g + g') x = ratAffineForm g x + ratAffineForm g' x := by
  simp only [ratAffineForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Two rational affine functions agreeing at every rational point agree everywhere. -/
private theorem ratAffineForm_eq_of_forall_rat {g g' : (Fin r → ℚ) × ℚ}
    (h : ∀ q : Fin r → ℚ, ratAffineForm g (fun i => (q i : ℝ)) =
      ratAffineForm g' (fun i => (q i : ℝ))) (x : Fin r → ℝ) :
    ratAffineForm g x = ratAffineForm g' x := by
  classical
  have h0 := h 0
  simp only [ratAffineForm, Pi.zero_apply, Rat.cast_zero, mul_zero, Finset.sum_const_zero,
    zero_add] at h0
  have h1 : ∀ j, (g.1 j : ℝ) = g'.1 j := fun j => by
    have := h (Pi.single j 1)
    simp only [ratAffineForm] at this
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp),
      Finset.sum_eq_single j (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp)] at this
    simp only [Pi.single_eq_same, Rat.cast_one, mul_one] at this
    linarith
  simp only [ratAffineForm, h1, h0]

/-- A weak rational affine inequality holding at `b` holds near `b` in its rational affine hull. -/
private theorem eventually_le_ratAffineForm {b : Fin r → ℝ} (g : (Fin r → ℚ) × ℚ) (c : ℚ)
    (h : (c : ℝ) ≤ ratAffineForm g b) :
    ∀ᶠ x in 𝓝[(rationalAffineHull b : Set (Fin r → ℝ))] b, (c : ℝ) ≤ ratAffineForm g x := by
  have hval : ∀ x, ratAffineForm (g.1, g.2 - c) x = ratAffineForm g x - c := fun x => by
    simp only [ratAffineForm, Rat.cast_sub]; ring
  have hN : IsRationalPolyhedron {x : Fin r → ℝ | (c : ℝ) ≤ ratAffineForm g x} :=
    ⟨∅, {(g.1, g.2 - c)}, by ext x; simp [hval]⟩
  exact mem_nhdsWithin_rationalAffineHull hN h

open scoped Classical in
private theorem coeff_sum_single {X : Scheme.{u}} {R : Type*} [AddCommMonoid R]
    (P : Fin r → MMP.Mori.PrimeDivisor X) (x : Fin r → R) (Γ : MMP.Mori.PrimeDivisor X) :
    DivisorWithCoeffs.coeff (∑ i, Finsupp.single (P i) (x i) : DivisorWithCoeffs R X) Γ =
      ∑ i, if P i = Γ then x i else 0 := by
  simp [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]

private theorem toRDivisor_sum_single {X : Scheme.{u}} (P : Fin r → MMP.Mori.PrimeDivisor X)
    (q : Fin r → ℚ) :
    QDivisor.toRDivisor (∑ i, Finsupp.single (P i) (q i)) =
      ∑ i, Finsupp.single (P i) ((q i : ℚ) : ℝ) := by
  classical
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  rw [QDivisor.coeff_toRDivisor, coeff_sum_single, coeff_sum_single]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

/-- **Canonicity persists at nearby rational points of the rational affine hull.** Let `X` be a
`ℚ`-factorial normal complex variety of dimension `n ≥ 2` and `B = ∑ bᵢ Pᵢ` a real boundary with
`(X, B)` real canonical. For `x` near `b` in the smallest rational affine subspace through `b`,
every rational point `q = x` makes all exceptional log discrepancies of
`(X, ∑ qᵢ Pᵢ)` at least `1`. -/
private theorem eventually_one_le_isLogDiscrepancy {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hQ : MMP.Fourfold.IsQFactorial sX)
    {n : ℕ} (hn : 2 ≤ n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {r : ℕ} {P : Fin r → MMP.Mori.PrimeDivisor X} (hP : Function.Injective P) {b : Fin r → ℝ}
    (hb : ∀ i, b i ≠ 0)
    (hB : MMP.Fourfold.IsRealCanonicalPair sX (∑ i, Finsupp.single (P i) (b i))) :
    ∀ᶠ x in 𝓝[(MMP.Fourfold.rationalAffineHull b : Set (Fin r → ℝ))] b,
      ∀ q : Fin r → ℚ, x = (fun i => (q i : ℝ)) →
        ∀ (n' : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy sX n' (∑ i, Finsupp.single (P i) (x i)) E a →
            1 ≤ a := by
  classical
  have hX : IsNormalVariety ℂ sX := hQ.1
  have hXv := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set Bx : (Fin r → ℝ) → RDivisor X := fun x => ∑ i, Finsupp.single (P i) (x i)
  set Bq : (Fin r → ℚ) → QDivisor X := fun q => ∑ i, Finsupp.single (P i) (q i)
  have hBqx : ∀ q, QDivisor.toRDivisor (Bq q) = Bx (fun i => (q i : ℝ)) := fun q =>
    toRDivisor_sum_single P q
  -- `(X, ∑ qᵢ Pᵢ)` is a pair for every rational `q`
  have hpairq : ∀ q, IsPairWith sX n K (Bq q) := fun q =>
    ⟨hX, hK, isQCartier_of_isQFactorial sX hQ _⟩
  -- a log resolution of `(X, B)`
  obtain ⟨Y, μ, hres, -⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sX hX (Bx b)
  obtain ⟨hY, hdimY, -⟩ := hres.toIsSmoothResolution.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : IsProper μ := hres.isProper
  haveI : IsDominant μ := hres.isBirationalMorphism.isDominant
  haveI : MMP.Mori.IsVariety ℂ (μ ≫ sX) := hY.1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI : LocallyOfFinitePresentation (μ ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := μ ≫ sX)).mpr inferInstance
  set hμ := hres.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver ℂ sX := fun G => ⟨Y, μ, hY, hμ, G⟩
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (μ ≫ sX) hres.isSmoothScheme
    (hdimY.trans hK.topologicalKrullDim_eq)
  have hdimY' : topologicalKrullDim Y = n := hdimY.trans hK.topologicalKrullDim_eq
  obtain ⟨S, hsncS, hmemS⟩ := exists_finset_isSNC hres.isSmoothScheme hres.isSNCSubset
  have hexcS : ∀ G, (DG G).IsExceptional → G ∈ S := fun G hG =>
    hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hG
      (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  have hpre : ∀ (G : MMP.Mori.PrimeDivisor Y) (i : Fin r), μ G.genericPoint = (P i).genericPoint →
      G ∈ S := by
    intro G i hη
    refine hmemS G (Or.inr ?_)
    change μ G.genericPoint ∈ (Bx b).supp
    rw [hη]
    refine DivisorWithCoeffs.support_subset_supp (D := Bx b) (E := P i) ?_
      (MMP.Flips.primeDivisor_genericPoint_mem_support (P i))
    change DivisorWithCoeffs.coeff (∑ j, Finsupp.single (P j) (b j)) (P i) ≠ 0
    rw [coeff_sum_single, Finset.sum_eq_single i (fun j _ hji => if_neg (hP.ne hji))
      (by simp), if_pos rfl]
    exact hb i
  -- the log discrepancies of the prime divisors of `Y` are rational affine in the coefficients
  choose A hA using fun G => exists_ratAffineForm_isLogDiscrepancy hQ hK P (DG G) hres.isProper
  -- the crepant boundary at a rational point, and its coefficients
  have hcrep : ∀ q : Fin r → ℚ, ∃ ΔY : QDivisor Y,
      IsCrepantBoundary sX n K (Bq q) μ hY hμ ΔY ∧ ΔY.support ⊆ S ∧
        ∀ G, ratAffineForm (A G) (fun i => (q i : ℝ)) = 1 - ΔY.coeff G := by
    intro q
    obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ :=
      MMP.Mori.IsPair.existsUnique_isCrepantBoundary (hpairq q).isPair hK μ hY hμ
    have hval : ∀ G, ratAffineForm (A G) (fun i => (q i : ℝ)) = 1 - ΔY.coeff G := fun G => by
      have h1 : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (Bq q)) (DG G)
          (ratAffineForm (A G) (fun i => (q i : ℝ))) := by
        rw [hBqx]
        exact hA G _
      have h2 := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hΔY G) _).mp h1).2
      rw [h2]
      push_cast
      ring
    refine ⟨ΔY, hΔY, fun G hG => ?_, hval⟩
    by_cases hGe : (DG G).IsExceptional
    · exact hexcS G hGe
    · obtain ⟨P', hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional (hpairq q) hY hμ hΔY hGe
      have hne : DivisorWithCoeffs.coeff (∑ j, Finsupp.single (P j) (q j)) P' ≠ 0 :=
        hc ▸ Finsupp.mem_support_iff.mp hG
      rw [coeff_sum_single] at hne
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hPi : P i = P' := of_not_not fun h => hi (if_neg h)
      exact hpre G i (hη.trans (congrArg _ hPi.symm))
  -- a prime divisor of `Y` which is not exceptional: `a(G, X, ∑ xᵢ Pᵢ) = 1 - coeff_Γ`
  have hnexc : ∀ G, ¬ (DG G).IsExceptional → ∃ Γ : MMP.Mori.PrimeDivisor X, ∀ x,
      ratAffineForm (A G) x = 1 - ∑ i, if P i = Γ then x i else 0 := by
    intro G hGe
    obtain ⟨Δ0, hΔ0, -, -⟩ := hcrep 0
    obtain ⟨Γ, -, hηΓ, -⟩ := exists_coeff_eq_of_not_isExceptional (hpairq 0) hY hμ hΔ0 hGe
    refine ⟨Γ, fun x => ?_⟩
    rw [ratAffineForm_eq_of_forall_rat (g' := (fun i => -(if P i = Γ then (1 : ℚ) else 0), 1))
      (fun q => ?_) x]
    · simp only [ratAffineForm]
      rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      · simp
    · obtain ⟨Δq, hΔq, -, hvalq⟩ := hcrep q
      obtain ⟨Γ', hc, hη', -⟩ := exists_coeff_eq_of_not_isExceptional (hpairq q) hY hμ hΔq hGe
      obtain rfl : Γ' = Γ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη'.symm.trans hηΓ)
      rw [hvalq, hc]
      change (1 : ℝ) - ((DivisorWithCoeffs.coeff (∑ j, Finsupp.single (P j) (q j)) Γ' : ℚ) : ℝ) = _
      rw [coeff_sum_single, Rat.cast_sum]
      simp only [ratAffineForm]
      rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
      · simp
  -- the blow-ups of the codimension two strata of the snc divisor
  have hpair : ∀ G ∈ S, ∀ F ∈ S, G ≠ F → (G.support ∩ F.support).Nonempty →
      ∃ (E : DivisorOver ℂ (μ ≫ sX)) (g : (Fin r → ℚ) × ℚ), E.IsExceptional ∧
        (∀ Δ : QDivisor Y, MMP.Mori.IsPair (μ ≫ sX) Δ → Δ.support ⊆ S → ∀ c : ℚ,
          IsDiscrepancy (μ ≫ sX) n KY Δ E c → c = 1 - Δ.coeff G - Δ.coeff F) ∧
        ∀ x, MMP.Intersection.IsLogDiscrepancy sX n (Bx x) (compDivisorOver μ hY hμ E)
          (ratAffineForm g x) := by
    intro G hG F hF hGF hmeet
    obtain ⟨D, hDe, hDc⟩ := exists_isExceptional_isDiscrepancy_eq_one_sub_sub hY
      hres.isSmoothScheme hdimY' hsncS hG hF hGF hmeet
    obtain ⟨E, hEv⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hY D
    have hEe : E.toDivisorOver.IsExceptional := isExceptional_of_valuation_eq hY hEv.symm hDe
    haveI := E.isProper
    obtain ⟨g, hg⟩ := exists_ratAffineForm_isLogDiscrepancy hQ hK P
      (compDivisorOver μ hY hμ E.toDivisorOver) (by change IsProper (E.f ≫ μ); infer_instance)
    refine ⟨E.toDivisorOver, g, hEe, fun Δ hΔ hS c hc => ?_, hg⟩
    obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΔ hKY D
    rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hEv
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hY hEv) hc hc']
    exact hDc KY Δ hS c' hc'
  choose EP gP hEPe hEPc hEPlog using hpair
  have hpairval : ∀ G (hG : G ∈ S) F (hF : F ∈ S) (hGF : G ≠ F)
      (hm : (G.support ∩ F.support).Nonempty) (x : Fin r → ℝ),
      ratAffineForm (gP G hG F hF hGF hm) x = ratAffineForm (A G + A F) x := by
    intro G hG F hF hGF hm x
    refine ratAffineForm_eq_of_forall_rat (fun q => ?_) x
    rw [ratAffineForm_add]
    obtain ⟨Δq, hΔq, hSq, hvalq⟩ := hcrep q
    obtain ⟨hPY, hcr⟩ :=
      MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant (hpairq q).isPair μ hY hμ hK hKY (Or.inl hΔq)
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hpairq q).isPair hK
      (compDivisorOver μ hY hμ (EP G hG F hF hGF hm))
    have hcY := (hcr (EP G hG F hF hGF hm) _ (valuation_compDivisorOver μ hY hμ _) c).mpr hc
    have hc1 := hEPc G hG F hF hGF hm Δq hPY hSq c hcY
    have hl := hEPlog G hG F hF hGF hm (fun i => (q i : ℝ))
    rw [← hBqx] at hl
    rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc _).mp hl).2, hc1,
      hvalq G, hvalq F]
    push_cast
    ring
  -- the conditions at `b`
  have hb1 : ∀ G, (DG G).IsExceptional → (1 : ℝ) ≤ ratAffineForm (A G) b := fun G hG =>
    hB.2.2.2 n (DG G) _ hG (hA G b)
  have hb2 : ∀ G, (0 : ℝ) ≤ ratAffineForm (A G) b := by
    intro G
    by_cases hG : (DG G).IsExceptional
    · linarith [hb1 G hG]
    obtain ⟨Γ, hΓ⟩ := hnexc G hG
    rw [hΓ, ← coeff_sum_single]
    by_cases h0 : DivisorWithCoeffs.coeff (∑ i, Finsupp.single (P i) (b i)) Γ = 0
    · rw [h0]; norm_num
    · linarith [(hB.2.1 Γ h0).2]
  have hb3 : ∀ G (hG : G ∈ S) F (hF : F ∈ S) (hGF : G ≠ F)
      (hm : (G.support ∩ F.support).Nonempty), (1 : ℝ) ≤ ratAffineForm (A G + A F) b :=
    fun G hG F hF hGF hm => hpairval G hG F hF hGF hm b ▸
      hB.2.2.2 n _ _ (isExceptional_compDivisorOver hX hY hμ (hEPe G hG F hF hGF hm))
        (hEPlog G hG F hF hGF hm b)
  -- the conditions persist near `b` in the rational affine hull
  have hev1 : ∀ᶠ x in 𝓝[(rationalAffineHull b : Set (Fin r → ℝ))] b,
      ∀ G ∈ S, (DG G).IsExceptional → (1 : ℝ) ≤ ratAffineForm (A G) x := by
    refine (Filter.eventually_all_finset S).2 fun G _ => ?_
    by_cases hG : (DG G).IsExceptional
    · filter_upwards [eventually_le_ratAffineForm (A G) 1 (by simpa using hb1 G hG)] with x hx _
      simpa using hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hG
  have hev2 : ∀ᶠ x in 𝓝[(rationalAffineHull b : Set (Fin r → ℝ))] b,
      ∀ G ∈ S, (0 : ℝ) ≤ ratAffineForm (A G) x :=
    (Filter.eventually_all_finset S).2 fun G _ => by
      simpa using eventually_le_ratAffineForm (A G) 0 (by simpa using hb2 G)
  have hev3 : ∀ᶠ x in 𝓝[(rationalAffineHull b : Set (Fin r → ℝ))] b,
      ∀ G ∈ S, ∀ F ∈ S, G ≠ F → (G.support ∩ F.support).Nonempty →
        (1 : ℝ) ≤ ratAffineForm (A G + A F) x := by
    refine (Filter.eventually_all_finset S).2 fun G hG =>
      (Filter.eventually_all_finset S).2 fun F hF => ?_
    by_cases hGF : G ≠ F
    · by_cases hm : (G.support ∩ F.support).Nonempty
      · filter_upwards [eventually_le_ratAffineForm (A G + A F) 1
          (by simpa using hb3 G hG F hF hGF hm)] with x hx _ _
        simpa using hx
      · exact Filter.Eventually.of_forall fun x _ h => absurd h hm
    · exact Filter.Eventually.of_forall fun x h => absurd h hGF
  -- at a rational point satisfying the conditions, the pair is canonical
  filter_upwards [hev1, hev2, hev3] with x h1 h2 h3
  rintro q rfl n' E a hE ha
  obtain rfl : n = n' := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
    exact_mod_cast this.symm
  obtain ⟨Δq, hΔq, hSq, hvalq⟩ := hcrep q
  have hdisc : (0 : EReal) ≤ discrep sX n K (Bq q) := by
    rw [discrep_eq_min_of_isCrepantBoundary (hpairq q) hY hμ hKY hΔq (fun G => -Δq.coeff G)
      (fun G _ => hΔq G)]
    refine le_min ?_ (le_iInf₂ fun G hG => ?_)
    · rw [discrep_eq_of_isSNC (μ ≫ sX) hY hres.isSmoothScheme hn hKY S hSq hsncS
        (fun G hG => ?_)]
      · refine le_min (le_min ?_ ?_) zero_le_one
        · refine le_iInf₂ fun G hG => le_iInf₂ fun F hF => le_iInf₂ fun hGF hm => ?_
          have := h3 G hG F hF hGF hm
          rw [ratAffineForm_add, hvalq, hvalq] at this
          exact EReal.coe_nonneg.mpr (by push_cast; linarith)
        · refine le_iInf₂ fun G hG => ?_
          have := h2 G hG
          rw [hvalq] at this
          exact EReal.coe_nonneg.mpr (by push_cast; linarith)
      · have := h2 G hG
        rw [hvalq] at this
        exact_mod_cast (by linarith : ((Δq.coeff G : ℚ) : ℝ) ≤ 1)
    · have := h1 G (hexcS G hG) hG
      rw [hvalq] at this
      exact EReal.coe_nonneg.mpr (by push_cast; linarith)
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy (hpairq q).isPair hK E
  have hc0 : (0 : ℝ) ≤ c := by
    have := hdisc.trans (discrep_le hE hc)
    exact_mod_cast EReal.coe_nonneg.mp this
  have ha' : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (Bq q)) E a := by
    rwa [hBqx]
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc a).mp ha').2]
  linarith

end RationalHull

/-! ### Divisors and transforms -/

section Transforms

variable {X Y : Scheme.{u}}

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (g : R →+ S) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X' : Scheme.{u}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (g : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

private theorem toRDivisor_flipTransform {X' : Scheme.{u}} (fm : X ⟶ Y) (fp : X' ⟶ Y)
    (D : QDivisor X) :
    QDivisor.toRDivisor (flipTransform fm fp D) = flipTransform fm fp (QDivisor.toRDivisor D) :=
  (flipTransform_mapCoeffsAddMonoidHom fm fp _ D).symm

/-- The strict transform `(f⁺)⁻¹_* f_*` of real divisors is `ℝ`-linear. -/
private theorem flipTransform_smul {X' : Scheme.{u}} (fm : X ⟶ Y) (fp : X' ⟶ Y) (c : ℝ)
    (D : RDivisor X) : flipTransform fm fp (c • D) = c • flipTransform fm fp D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

private theorem toRDivisor_apply (L : Divisor X) (Γ : MMP.Mori.PrimeDivisor X) :
    Divisor.toRDivisor L Γ = (L Γ : ℝ) := rfl

/-- On a `ℚ`-factorial variety every divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {k : Type u} [Field k] {sX : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] (hQ : MMP.Fourfold.IsQFactorial sX) (D : Divisor X) :
    MMP.Flips.IsCartierCombination (Divisor.toRDivisor D) := by
  obtain ⟨m, hm, hmC⟩ := hQ.2 D
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => (m : ℤ) • D, fun _ => hmC, ?_⟩
  ext Γ
  simp only [Fin.sum_univ_one]
  change Divisor.toRDivisor D Γ = ((1 / (m : ℝ)) • Finsupp.mapRange Int.cast Int.cast_zero
    ((m : ℤ) • D)) Γ
  simp only [Finsupp.smul_apply, smul_eq_mul, toRDivisor_apply, Finsupp.mapRange_apply,
    Int.cast_mul, Int.cast_natCast]
  field_simp

/-- If `-(K + D)` is relatively ample, then `K + D` is `ℝ`-Cartier, in both senses used. -/
private theorem isRCartier_of_isRelativelyAntiAmple {Z : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Z} {K : Divisor X} {D : RDivisor X}
    (h : MMP.Flips.IsRelativelyAntiAmple f (MMP.Flips.logCanonicalDivisor K D)) :
    MMP.Flips.IsCartierCombination (MMP.Flips.logCanonicalDivisor K D) ∧
      MMP.Fourfold.RDivisor.IsRCartier
        (Finsupp.mapRange (Int.cast : ℤ → ℝ) Int.cast_zero K + D) := by
  obtain ⟨m, r, L, -, -, hL₀, hD⟩ := h
  have hL : ∀ j, (L j).IsCartier := fun j => (hL₀ j).1
  have hD' : MMP.Flips.logCanonicalDivisor K D = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [← neg_neg (MMP.Flips.logCanonicalDivisor K D), hD]
    simp only [neg_smul, Finset.sum_neg_distrib]
  refine ⟨⟨m, fun j => -r j, L, hL, hD'⟩, m, fun j => -r j, L, hL, fun Γ => ?_⟩
  have := congrArg (fun G : RDivisor X => G Γ) hD'
  simp only [MMP.Flips.logCanonicalDivisor, Finsupp.add_apply, toRDivisor_apply,
    Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at this
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.mapRange_apply, this]

end Transforms

/-- A property holding near `b` in its rational affine hull holds at a rational point. -/
private theorem exists_rat_of_eventually {r : ℕ} {b : Fin r → ℝ} {p : (Fin r → ℝ) → Prop}
    (h : ∀ᶠ x in 𝓝[(MMP.Fourfold.rationalAffineHull b : Set (Fin r → ℝ))] b, p x) :
    ∃ q : Fin r → ℚ, p (fun i => (q i : ℝ)) := by
  obtain ⟨m, p₀, e, -, -, hW⟩ := MMP.Fourfold.exists_rational_frame b
  obtain ⟨s₀, hs₀⟩ := (hW b).1 (MMP.Fourfold.self_mem_rationalAffineHull b)
  set φ : (Fin m → ℝ) → (Fin r → ℝ) := fun s j => (p₀ j : ℝ) + ∑ i, s i * (e i j : ℝ) with hφ
  have hφc : Continuous φ := by rw [hφ]; fun_prop
  have ht : Tendsto φ (𝓝 s₀) (𝓝[(MMP.Fourfold.rationalAffineHull b : Set (Fin r → ℝ))] b) :=
    tendsto_nhdsWithin_iff.2 ⟨hs₀ ▸ hφc.tendsto s₀, Eventually.of_forall fun s => (hW _).2 ⟨s, rfl⟩⟩
  obtain ⟨U, hU, hUo, hs₀U⟩ := eventually_nhds_iff.1 (ht.eventually h)
  obtain ⟨_, hmem, s, rfl⟩ :=
    (DenseRange.piMap (fun _ => Rat.denseRange_cast (𝕜 := ℝ))).inter_open_nonempty U hUo
      ⟨s₀, hs₀U⟩
  refine ⟨fun j => p₀ j + ∑ i, s i * e i j, ?_⟩
  convert hU _ hmem using 1
  ext j
  simp [hφ, Pi.map_apply]

/-! ### Intersection numbers, rational top forms and inverse transforms -/

section FlipsIntersection

open MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_exists_forall_base_eq_of_isCurveNormalization (C : ProperCurve sX)
    {C' : Scheme.{u}} {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
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
  refine not_exists_forall_base_eq_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'),
    fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

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
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_exists_forall_base_eq_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

end FlipsIntersection

section FlipsForms

open MMP.Flips

/-- Two nonzero rational top forms on a normal variety of dimension `n` over a perfect field have
linearly equivalent divisors. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ τ' : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr τ' () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 τ' hτ'
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, Scheme.ord_mul he (inv_ne_zero hc),
    ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm, coeff_divisorOfForm, e1, e2]
  ring

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

/-- A valuation of `k(Y)` is determined by its restriction to `k(Z)` along a birational
morphism `g : Y ⟶ Z`. -/
private theorem valuation_eq_of_comap_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {g : Y ⟶ Z} (hg : IsBirationalMorphism g) [IsDominant g]
    {v w : Valuation Y.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap g) = w.comap (functionFieldMap g)) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hg.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

/-- The valuation of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : MMP.Flips.ProperDivisorOver k sX) :
    MMP.Flips.HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

end FlipsForms

section FlipsTransforms

open MMP.Flips

variable {X Y : Scheme.{u}}

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
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
    have hfe : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
    rw [hfe, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
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
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If the strict transform of `P` under `φ` is `E` and `g'` represents `φ` at `η_P`, then
`η_E = g'(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
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
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    MMP.Mori.RationalMap.definedAt_iff.mp
      (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- Conversely, let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If
`f` sends the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`,
then the strict transform of `P` under `f⁻¹` is `E`: the map `f⁻¹` is defined at `η_P`
(`MMP.Flips.RationalMap.isMorphismInCodimOne_inverse`), and `f` is injective on the points over
`η_P`, whose local ring is a valuation ring. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : MMP.Mori.RationalMap.DefinedAt (MMP.Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom (MMP.Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
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

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

end FlipsTransforms

/-! ### Small contractions and relative nefness -/

section Small

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {C : MMP.Mori.ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- **A relatively ample divisor, shifted by a principal Cartier divisor, is relatively nef**:
an ample Cartier divisor has positive degree on every contracted curve, and a principal one has
degree zero. -/
private theorem isRelativelyNef_add_of_isRelativelyAmple {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {D : RDivisor X}
    (hD : MMP.Flips.IsRelativelyAmple f D) {G : Divisor X} (hG : G.IsCartier)
    (hG0 : G.LinearlyEquivalent 0) :
    MMP.Flips.IsRelativelyNef k sX f (D + Divisor.toRDivisor G) := by
  obtain ⟨m, r, L, -, hr, hL, rfl⟩ := hD
  refine ⟨m + 1, Fin.cons 1 r, Fin.cons G L, Fin.cases hG fun j => (hL j).1, ?_,
    fun C hC x hx => ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, one_smul]
    abel
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
    have h0 : (d 0 : ℝ) = 0 := by
      rw [eq_degreeOn_of_isCartierIntersectionNumber (hd 0)]
      exact_mod_cast
        MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le (hL' 0) hG0
    rw [h0, zero_add]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le ?_
    rw [eq_degreeOn_of_isCartierIntersectionNumber (hd j.succ)]
    exact_mod_cast (MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hL' j.succ) C
      hC).le

/-- A small contraction maps the generic point of every prime divisor to the generic point of
a prime divisor. -/
private theorem exists_primeDivisor_map_genericPoint_eq_of_isSmall {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {g : Y ⟶ Z}
    (hg : MMP.Flips.IsSmall k sZ sY g) (P : MMP.Mori.PrimeDivisor Y) :
    ∃ Q : MMP.Mori.PrimeDivisor Z, g P.genericPoint = Q.genericPoint := by
  obtain ⟨-, V, W, hV, -, hle, hiso⟩ := hg
  have hP : P.genericPoint ∉ (V : Set Y) := fun hmem => by
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) P.genericPoint hmem
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hex : P.genericPoint ∉ MMP.Flips.exceptionalSet g := fun hmem => hmem ⟨V.compl, hP, by
    rw [← Scheme.Hom.resLE_comp_ι g hle]; infer_instance⟩
  have hc : Order.coheight (g P.genericPoint) = 1 := by
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hex, P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm⟩

/-- A morphism is injective on the points lying over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {Y Z : Scheme.{u}} {g : Y ⟶ Z} {y₁ y₂ : Y}
    (h : g y₁ = g y₂) (hy : g y₁ ∈ biregularLocus g) : y₁ = y₂ := by
  set V := biregularLocus g
  have : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let p₁ : (g ⁻¹ᵁ V).toScheme := ⟨y₁, hy⟩
  let p₂ : (g ⁻¹ᵁ V).toScheme := ⟨y₂, show g y₂ ∈ V from h ▸ hy⟩
  have hp : ∀ p : (g ⁻¹ᵁ V).toScheme, ((g ∣_ V) ≫ V.ι) p = g p.1 := fun p => by
    rw [morphismRestrict_ι]
    rfl
  exact congrArg Subtype.val (((g ∣_ V) ≫ V.ι).isOpenEmbedding.injective
    (show ((g ∣_ V) ≫ V.ι) p₁ = ((g ∣_ V) ≫ V.ι) p₂ by rwa [hp, hp]))

/-- The coefficient of `(f⁺)⁻¹_* f_* D` at `P⁺` is that of `D` at `P` when `f(η_P) = η_Q =
f⁺(η_{P⁺})` for a prime divisor `Q` of `Z` over which both maps are biregular. -/
private theorem flipTransform_apply_of_genericPoint_eq {Xm Xp Z : Scheme.{u}} [IsReduced Xm]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {P : MMP.Mori.PrimeDivisor Xm} {P' : MMP.Mori.PrimeDivisor Xp} {Q : MMP.Mori.PrimeDivisor Z}
    (hP : fm P.genericPoint = Q.genericPoint) (hP' : fp P'.genericPoint = Q.genericPoint)
    (hQm : Q.genericPoint ∈ biregularLocus fm) (hQp : Q.genericPoint ∈ biregularLocus fp)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    flipTransform fm fp D P' = D P := by
  have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hP
  have h1' : ∀ E', MMP.Mori.RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap E' =
      some Q → E' = P := fun E' hE' => by
    have hE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm E' Q).mp hE'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus (hE.trans hP.symm) (hE ▸ hQm))
  have h2 := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hP'
    (hP' ▸ hQp)
  have h2' : ∀ Q', inverseTransformPrimeDivisor fp Q' = some P' → Q' = Q := fun Q' hQ' => by
    obtain ⟨e, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (e.symm.trans hP')
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h2 h2',
    MMP.Mori.RationalMap.transformDivisor,
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 h1']

/-- **One presentation, two discrepancies.** A presentation `K + D = ∑ rⱼ Lⱼ` by Cartier divisors,
with `K = div(ω)` canonical, computes both the discrepancy `a(E, X, D)` of a divisor `E` over `X`
and its log discrepancy `1 + a(E, X, D)`. -/
private theorem exists_isDiscrepancy_and_isLogDiscrepancy {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : MMP.Flips.ProperDivisorOver k sX) :
    ∃ a : ℝ, MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) D E.valuation a ∧
      MMP.Intersection.IsLogDiscrepancy sX n D E.toDivisorOver (1 + a) := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hL j)
  refine ⟨(E.toDivisorOver.ordPullback ω : ℝ) - ∑ j, r j * (L' j).coeff E.E,
    ⟨hK, ⟨m, r, L, hL, hD⟩, hasNonemptyCenter_valuation E, E, ω, m, r, L, rfl, rfl, hX,
      hK.topologicalKrullDim_eq, hω, hL, hD, L', fun j => ⟨_, hL' j⟩, rfl⟩,
    hX, E.isProper, ω, hω, ⟨divisorOfForm ω, hK, fun Γ => rfl⟩, m, r, L, L', hL, fun Γ => ?_,
    fun j => ⟨_, hL' j⟩, by ring⟩
  have := congrArg (fun G : RDivisor X => G Γ) hD
  simp only [Finsupp.add_apply, toRDivisor_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at this
  rw [show ((divisorOfForm ω) Γ : ℤ) = Γ.ordForm ω from rfl] at this
  simpa [DivisorWithCoeffs.coeff_apply] using this

/-- Over a perfect field, the divisor of a nonzero rational top form is linearly equivalent to
every canonical divisor. -/
private theorem linearlyEquivalent_divisorOfForm_of_isCanonicalDivisor {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) : (divisorOfForm τ).LinearlyEquivalent K := by
  obtain ⟨τ₀, hτ₀, hτ₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have e : divisorOfForm τ₀ = K := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hτ₀K]
  exact e ▸ linearlyEquivalent_divisorOfForm hX hK.topologicalKrullDim_eq hτ hτ₀

end Small

/-! ### The flip of a real canonical pair -/

section Flip

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Every prime divisor `P⁺` of `X⁺` corresponds to a prime divisor `P` of `X`, with the same
image in `Z`: the coefficient of `(f⁺)⁻¹_* f_* D` at `P⁺` is that of `D` at `P`. -/
private theorem IsRealFlipStep.exists_flipTransform_apply_eq
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X, ∀ D : RDivisor X, flipTransform f fp D P' = D P := by
  have hNE := h.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ sZ := hNE.isNormalVariety_target
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := hNE.isContraction.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  haveI : IsNormal Z := hZ.2
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI := isSeparated_toTerminal sZ
  obtain rfl : f ≫ sZ = sX := hNE.isContraction.comp_eq
  obtain rfl : fp ≫ sZ = sX' := h.isSmall_flip.comp_eq
  have hm :=
    genericPoint_mem_biregularLocus hZ.1 hNE.isNormalVariety_source.1 h.isBirationalMorphism
  have hp := genericPoint_mem_biregularLocus hZ.1 hX'v.1 h.isBirationalMorphism_flip
  obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall h.isSmall_flip P'
  obtain ⟨P, -, hP⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some Q (hm Q)
  exact ⟨P, flipTransform_apply_of_genericPoint_eq hP hQ (hm Q) (hp Q)⟩

/-- **A flip does not lower exceptional log discrepancies.** Let `X ⟶ Z ⟵ X⁺` be a step of a
real flip sequence of threefolds. Every divisor `E` exceptional over `X⁺` is realised by a divisor
`D` exceptional over `X` with `a(D, X, B) ≤ a(E, X⁺, B⁺)`. -/
theorem IsRealFlipStep.exists_isExceptional_isLogDiscrepancy_le
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hd : topologicalKrullDim X = 3) (hd' : topologicalKrullDim X' = 3) {n : ℕ}
    {E : DivisorOver ℂ sX'} {a : ℝ} (hE : E.IsExceptional)
    (ha : MMP.Intersection.IsLogDiscrepancy sX' n B' E a) :
    ∃ (D : DivisorOver ℂ sX) (a' : ℝ), D.IsExceptional ∧
      MMP.Intersection.IsLogDiscrepancy sX n B D a' ∧ a' ≤ a := by
  classical
  have hNE := h.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ sZ := hNE.isNormalVariety_target
  have hXv : IsNormalVariety ℂ sX := hNE.isNormalVariety_source
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := hNE.isContraction.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI := isSeparated_toTerminal sZ
  have hf : IsBirationalMorphism f := h.isBirationalMorphism
  have hfp : IsBirationalMorphism fp := h.isBirationalMorphism_flip
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  obtain rfl : f ≫ sZ = sX := hNE.isContraction.comp_eq
  obtain rfl : fp ≫ sZ = sX' := h.isSmall_flip.comp_eq
  haveI : MMP.Mori.IsVariety ℂ (f ≫ sZ) := hXv.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hX'v.1
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sZ) := hXv.1.toQuasiCompact
  haveI : QuasiCompact (fp ≫ sZ) := hX'v.1.toQuasiCompact
  -- the prime divisors of `X`, `Z` and `X⁺` correspond
  have hbir : ∀ Q : MMP.Mori.PrimeDivisor Z,
      Q.genericPoint ∈ biregularLocus f ∧ Q.genericPoint ∈ biregularLocus fp := fun Q =>
    ⟨genericPoint_mem_biregularLocus hZ.1 hXv.1 hf Q,
      genericPoint_mem_biregularLocus hZ.1 hX'v.1 hfp Q⟩
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ (P : MMP.Mori.PrimeDivisor X)
      (Q : MMP.Mori.PrimeDivisor Z), f P.genericPoint = Q.genericPoint ∧
        fp P'.genericPoint = Q.genericPoint := fun P' => by
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall h.isSmall_flip P'
    obtain ⟨P, -, hP⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some Q (hbir Q).1
    exact ⟨P, Q, hP, hQ⟩
  have hcorr' : ∀ P : MMP.Mori.PrimeDivisor X, ∃ (P' : MMP.Mori.PrimeDivisor X')
      (Q : MMP.Mori.PrimeDivisor Z), f P.genericPoint = Q.genericPoint ∧
        fp P'.genericPoint = Q.genericPoint := fun P => by
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_genericPoint_eq_of_isSmall h.isSmall P
    obtain ⟨P', -, hP'⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some Q (hbir Q).2
    exact ⟨P', Q, hQ, hP'⟩
  -- exceptional log discrepancies over `X⁺`
  have hEprop : IsProper E.f := ha.2.1
  obtain rfl : n = 3 := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans hd'
  have hK3 : K.IsCanonicalDivisor (f ≫ sZ) 3 := isCanonicalDivisor_of_topologicalKrullDim_eq hd hK
  have hK'3 : K'.IsCanonicalDivisor (fp ≫ sZ) 3 :=
    isCanonicalDivisor_of_topologicalKrullDim_eq hd' h.isCanonicalDivisor_flip
  -- a rational top form `ω` on `Z`, and the compatible canonical divisors `K_X`, `K_{X⁺}`
  have hdZ : topologicalKrullDim Z = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (f ≫ sZ) hf).trans hd
  obtain ⟨bZ⟩ := MMP.Positivity.exists_basis_topForms hZ hdZ
  let ω : RationalPluriForms sZ 3 1 := (ZTensorPower.basis bZ 1) ()
  have hω : ω ≠ 0 := (ZTensorPower.basis bZ 1).ne_zero ()
  have htr := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hdZ
  have hωX := pullbackRationalPluriForms_ne_zero f hf.functionFieldMap_bijective htr hω
  have hωY := pullbackRationalPluriForms_ne_zero fp hfp.functionFieldMap_bijective htr hω
  set KX := divisorOfForm (pullbackRationalPluriForms sZ f ω)
  set KY := divisorOfForm (pullbackRationalPluriForms sZ fp ω) with hKY
  have hKXK := linearlyEquivalent_divisorOfForm_of_isCanonicalDivisor hXv hK3 hωX
  have hKYK := linearlyEquivalent_divisorOfForm_of_isCanonicalDivisor hX'v hK'3 hωY
  have hKXc : KX.IsCanonicalDivisor (f ≫ sZ) 3 := hK3.of_linearlyEquivalent hKXK
  have hKYc : KY.IsCanonicalDivisor (fp ≫ sZ) 3 := hK'3.of_linearlyEquivalent hKYK
  have h0X : (K - KX).LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := hKXK.symm
    exact ⟨φ, by rwa [sub_zero]⟩
  have h0Y : (KY - K').LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := hKYK
    exact ⟨φ, by rwa [sub_zero]⟩
  -- `B` and `B⁺` are the birational transforms of `f_* B`
  set D := MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap B with hDdef
  have hDQ : ∀ (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Z),
      f P.genericPoint = Q.genericPoint → D Q = B P := by
    intro P Q hPQ
    rw [hDdef, MMP.Mori.RationalMap.transformDivisor]
    refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hPQ)
      (fun E' hE' => ?_) B
    have hE := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E' Q).mp hE'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus (hE.trans hPQ.symm) (hE ▸ (hbir Q).1))
  have hBX : MMP.Flips.birationalInverseTransform f hf D = B := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨-, Q, hP, -⟩ := hcorr' P
    rw [birationalInverseTransform_apply_of_genericPoint_eq hZ f hXv.1 hf D hP, hDQ P Q hP]
  have hBY : MMP.Flips.birationalInverseTransform fp hfp D = B' := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨P, Q, hP, hP'⟩ := hcorr P'
    rw [birationalInverseTransform_apply_of_genericPoint_eq hZ fp hX'v.1 hfp D hP', hDQ P Q hP,
      h.eq_flipTransform, flipTransform_apply_of_genericPoint_eq hP hP' (hbir Q).1 (hbir Q).2]
  -- the relative nefness hypotheses of the comparison
  have hAX : MMP.Flips.IsRelativelyNef ℂ (f ≫ sZ) f
      (-MMP.Flips.logCanonicalDivisor KX (MMP.Flips.birationalInverseTransform f hf D + 0)) := by
    have e : -MMP.Flips.logCanonicalDivisor KX (MMP.Flips.birationalInverseTransform f hf D + 0) =
        -MMP.Flips.logCanonicalDivisor K B + Divisor.toRDivisor (K - KX) := by
      rw [add_zero, hBX, MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, map_sub]
      abel
    rw [e]
    exact isRelativelyNef_add_of_isRelativelyAmple hNE.isRelativelyAntiAmple
      (Divisor.IsCartier.of_linearlyEquivalent h0X Divisor.isCartier_zero) h0X
  have hAY : MMP.Flips.IsRelativelyNef ℂ (fp ≫ sZ) fp
      (MMP.Flips.logCanonicalDivisor KY (MMP.Flips.birationalInverseTransform fp hfp D + 0)) := by
    have e : MMP.Flips.logCanonicalDivisor KY (MMP.Flips.birationalInverseTransform fp hfp D + 0) =
        MMP.Flips.logCanonicalDivisor K' B' + Divisor.toRDivisor (KY - K') := by
      rw [add_zero, hBY, MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, map_sub]
      abel
    rw [e]
    exact isRelativelyNef_add_of_isRelativelyAmple h.isRelativelyAmple_flip
      (Divisor.IsCartier.of_linearlyEquivalent h0Y Divisor.isCartier_zero) h0Y
  -- the valuation of `E` on `Z` and on `X`
  haveI := hEprop
  haveI := E.isIntegral
  let EZ : MMP.Flips.ProperDivisorOver ℂ sZ :=
    ⟨compDivisorOver fp hX'v hfp E, by change IsProper (E.f ≫ fp); infer_instance⟩
  set v := E.valuation.comap (functionFieldMap fp) with hv
  have hvZ : MMP.Flips.HasNonemptyCenter ℂ sZ v := by
    have := hasNonemptyCenter_valuation EZ
    rwa [show EZ.valuation = v from valuation_compDivisorOver fp hX'v hfp E] at this
  let e := RingEquiv.ofBijective (functionFieldMap f) hf.functionFieldMap_bijective
  set vX := v.comap (e.symm : X.functionField →+* Z.functionField)
  have hvX : vX.comap (functionFieldMap f) = v := by
    ext t
    exact congrArg v (e.symm_apply_apply t)
  -- the comparison of discrepancies over `Z`
  obtain ⟨hcX, -, hle⟩ := MMP.Flips.isDiscrepancy_le_of_isRelativelyNef (ω := ω)
    (K_X := KX) (K_Y := KY) (E_X := 0) (E_Y := 0) hZ hXv hX'v hf hfp rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hAX hAY hvZ hvX rfl
  obtain ⟨-, DX, hDX⟩ := hcX
  -- the centre of `E` on `X` is exceptional
  have hDXe : DX.toDivisorOver.IsExceptional := by
    by_contra hne
    obtain ⟨P, hPv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXv _ hne
    obtain ⟨P', Q, hP, hP'⟩ := hcorr' P
    refine (isExceptional_iff_forall_valuation_ne hX'v E).mp hE P'
      (valuation_eq_of_comap_eq hfp ?_)
    change v = _
    rw [← hvX, ← hDX]
    change DX.toDivisorOver.valuation.comap _ = _
    rw [hPv, ← valuation_mk_eq_comap f hXv hf P, ← valuation_mk_eq_comap fp hX'v hfp P',
      MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hZ
        (⟨X, f, hXv, hf, P⟩ : DivisorOver ℂ sZ) Q hP,
      MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hZ
        (⟨X', fp, hX'v, hfp, P'⟩ : DivisorOver ℂ sZ) Q hP']
  -- the two discrepancies
  obtain ⟨mX, rX, LX, hLX, heqX, -⟩ := hAX
  have hpresX : Divisor.toRDivisor KX + B = ∑ j, (-rX j) • Divisor.toRDivisor (LX j) := by
    rw [add_zero, hBX] at heqX
    rw [← neg_neg (Divisor.toRDivisor KX + B)]
    change -(-MMP.Flips.logCanonicalDivisor KX B) = _
    rw [heqX]
    simp only [neg_smul, Finset.sum_neg_distrib, neg_neg]
  obtain ⟨mY, rY, LY, hLY, heqY, -⟩ := hAY
  have hpresY : Divisor.toRDivisor KY + B' = ∑ j, rY j • Divisor.toRDivisor (LY j) := by
    rwa [add_zero, hBY] at heqY
  obtain ⟨aX, haXd, haXl⟩ := exists_isDiscrepancy_and_isLogDiscrepancy hXv hωX hKXc hLX hpresX DX
  obtain ⟨aY, haYd, haYl⟩ :=
    exists_isDiscrepancy_and_isLogDiscrepancy hX'v hωY hKYc hLY hpresY ⟨E, hEprop⟩
  have hae : a = 1 + aY := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha haYl
  have hle' := hle aX aY (by rwa [add_zero, hBX, ← hDX])
    (by rwa [add_zero, hBY])
  exact ⟨DX.toDivisorOver, 1 + aX, hDXe, haXl, by linarith⟩

/-- **A step of a real flip sequence preserves real canonicity.** -/
theorem IsRealFlipStep.isRealCanonicalPair (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hd : topologicalKrullDim X = 3) (hd' : topologicalKrullDim X' = 3)
    (hB : IsRealCanonicalPair sX B) : IsRealCanonicalPair sX' B' := by
  refine ⟨⟨h.isSmall_flip.isVariety_source, inferInstance⟩, fun P' hP' => ?_, ?_,
    fun n E a hE ha => ?_⟩
  · -- the coefficients of `B⁺` are those of `B`
    obtain ⟨P, hPD⟩ := h.exists_flipTransform_apply_eq P'
    rw [h.eq_flipTransform, DivisorWithCoeffs.coeff_apply, hPD B] at hP' ⊢
    exact hB.2.1 P hP'
  · -- `K⁺ + B⁺` is `ℝ`-Cartier, being relatively ample
    obtain ⟨m, hK'⟩ := h.isCanonicalDivisor_flip
    obtain ⟨M, r, L, -, -, hL, hD⟩ := h.isRelativelyAmple_flip
    refine ⟨m, K', hK', M, r, L, fun j => (hL j).1, fun Γ => ?_⟩
    have := congrArg (fun G : RDivisor X' => G Γ) hD
    simp only [MMP.Flips.logCanonicalDivisor, Finsupp.add_apply, toRDivisor_apply,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.mapRange_apply, this]
  · -- exceptional log discrepancies, by comparison with `X`
    obtain ⟨D, a', hD, hDa, hle⟩ := h.exists_isExceptional_isLogDiscrepancy_le hK hd hd' hE ha
    exact (hB.2.2.2 n D a' hD hDa).trans hle

/-- **A step of a real flip sequence preserves real terminality.** -/
theorem IsRealFlipStep.isRealTerminalPair (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hd : topologicalKrullDim X = 3) (hd' : topologicalKrullDim X' = 3)
    (hB : IsRealTerminalPair sX B) : IsRealTerminalPair sX' B' :=
  ⟨h.isRealCanonicalPair hK hd hd' hB.1, fun n E a hE ha => by
    obtain ⟨D, a', hD, hDa, hle⟩ := h.exists_isExceptional_isLogDiscrepancy_le hK hd hd' hE ha
    exact (hB.2 n D a' hD hDa).trans_le hle⟩

/-- **A rational canonical witness.** The same diagram is a step of a real flip sequence for a
`ℚ`-divisor `B₀` with `(X, B₀)` real canonical. -/
private theorem exists_qDivisor_isRealFlipStep
    (h : MMP.Fourfold.IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hQ : MMP.Fourfold.IsQFactorial sX) (hQ' : MMP.Fourfold.IsQFactorial sX')
    (hd : topologicalKrullDim X = 3) (hB : MMP.Fourfold.IsRealCanonicalPair sX B) :
    ∃ B₀ : QDivisor X,
      MMP.Fourfold.IsRealCanonicalPair sX (QDivisor.toRDivisor B₀) ∧
      MMP.Fourfold.IsRealFlipStep sX sZ sX' K (QDivisor.toRDivisor B₀) K'
        (QDivisor.toRDivisor (flipTransform f fp B₀)) f fp := by
  classical
  -- coordinates on the support of `B`
  set T := B.support with hT
  let e : Fin T.card ≃ T := T.equivFin.symm
  let P : Fin T.card → MMP.Mori.PrimeDivisor X := fun i => (e i).1
  have hP : Function.Injective P := fun i j hij => e.injective (Subtype.ext hij)
  let b : Fin T.card → ℝ := fun i => B (P i)
  have hb : ∀ i, b i ≠ 0 := fun i => Finsupp.mem_support_iff.mp (e i).2
  have hBsum : B = ∑ i, Finsupp.single (P i) (b i) := by
    conv_lhs => rw [← Finsupp.sum_single B]
    rw [Finsupp.sum, ← hT, ← Finset.sum_coe_sort T]
    exact (Fintype.sum_equiv e _ _ fun i => rfl).symm
  have hK3 : K.IsCanonicalDivisor sX 3 := isCanonicalDivisor_of_topologicalKrullDim_eq hd hK
  have hB' : MMP.Fourfold.IsRealCanonicalPair sX (∑ i, Finsupp.single (P i) (b i)) := hBsum ▸ hB
  have hCX := eventually_one_le_isLogDiscrepancy hQ (by norm_num) hK3 hP hb hB'
  -- relative ampleness persists under small perturbations
  have hNE := h.isNegativeExtremalContraction
  haveI : IsProper f := hNE.isContraction.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  have hsingle : ∀ i, Finsupp.single (P i) (1 : ℝ) =
      Divisor.toRDivisor (Finsupp.single (P i) (1 : ℤ)) := fun i => by
    ext Γ
    change (Finsupp.single (P i) (1 : ℝ)) Γ = Divisor.toRDivisor (Finsupp.single (P i) (1 : ℤ)) Γ
    rw [toRDivisor_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hFi : ∀ i, flipTransform f fp (Finsupp.single (P i) (1 : ℝ)) =
      Divisor.toRDivisor (flipTransform f fp (Finsupp.single (P i) (1 : ℤ))) := fun i => by
    rw [hsingle i]
    exact (flipTransform_mapCoeffsAddMonoidHom f fp _ _)
  obtain ⟨δ, hδ, hamp⟩ := MMP.Flips.exists_pos_isRelativelyAmple_add_sum_smul ℂ sX sZ
    hNE.isNormalVariety_source hNE.isNormalVariety_target f hNE.isContraction.comp_eq
    hNE.isRelativelyAntiAmple (fun i => Finsupp.single (P i) (1 : ℝ))
    (fun i => hsingle i ▸ isCartierCombination_toRDivisor hQ _)
  obtain ⟨δ', hδ', hamp'⟩ := MMP.Flips.exists_pos_isRelativelyAmple_add_sum_smul ℂ sX' sZ
    hX'v hNE.isNormalVariety_target fp h.isSmall_flip.comp_eq h.isRelativelyAmple_flip
    (fun i => flipTransform f fp (Finsupp.single (P i) (1 : ℝ)))
    (fun i => (hFi i).symm ▸ isCartierCombination_toRDivisor hQ' _)
  have hopen : ∀ᶠ x in 𝓝 b, (∀ i, |b i - x i| < δ) ∧ (∀ i, |x i - b i| < δ') ∧
      ∀ i, 0 < x i ∧ x i < 1 := by
    have hb01 : ∀ i, 0 < b i ∧ b i < 1 := fun i => by
      have := hB'.2.1 (P i)
      rw [coeff_sum_single, Finset.sum_eq_single i (fun j _ hji => if_neg (hP.ne hji))
        (by simp), if_pos rfl] at this
      exact this (hb i)
    refine (Filter.eventually_all.2 fun i => ?_).and
      ((Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i => ?_))
    · have := (continuous_apply i).tendsto b |>.eventually (Metric.ball_mem_nhds (b i) hδ)
      filter_upwards [this] with x hx
      rw [Real.dist_eq] at hx
      rwa [abs_sub_comm]
    · have := (continuous_apply i).tendsto b |>.eventually (Metric.ball_mem_nhds (b i) hδ')
      filter_upwards [this] with x hx
      rwa [Real.dist_eq] at hx
    · have := (continuous_apply i).tendsto b |>.eventually
        (isOpen_Ioo.mem_nhds ⟨(hb01 i).1, (hb01 i).2⟩)
      filter_upwards [this] with x hx using hx
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := exists_rat_of_eventually (hCX.and (nhdsWithin_le_nhds hopen))
  -- the rational witness
  refine ⟨∑ i, Finsupp.single (P i) (q i), ?_⟩
  have hB₀ := toRDivisor_sum_single P q
  have hsub : ∀ x : Fin T.card → ℝ, ∑ i, (b i - x i) • Finsupp.single (P i) (1 : ℝ) =
      ∑ i, Finsupp.single (P i) (b i) - ∑ i, Finsupp.single (P i) (x i) := fun x => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.smul_single_one, Finsupp.single_sub]
  have hFsum : ∀ x : Fin T.card → ℝ, flipTransform f fp (∑ i, Finsupp.single (P i) (x i)) =
      ∑ i, x i • flipTransform f fp (Finsupp.single (P i) (1 : ℝ)) := fun x => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.smul_single_one, flipTransform_smul]
  have hanti : MMP.Flips.IsRelativelyAntiAmple f
      (MMP.Flips.logCanonicalDivisor K
        (QDivisor.toRDivisor (∑ i, Finsupp.single (P i) (q i)))) := by
    have e : -MMP.Flips.logCanonicalDivisor K
        (QDivisor.toRDivisor (∑ i, Finsupp.single (P i) (q i))) =
        -MMP.Flips.logCanonicalDivisor K B +
          ∑ i, (b i - q i) • Finsupp.single (P i) (1 : ℝ) := by
      rw [hsub, hB₀, MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor, hBsum]
      abel
    change MMP.Flips.IsRelativelyAmple f _
    rw [e]
    exact hamp (fun i => b i - q i) hq2
  have hampl : MMP.Flips.IsRelativelyAmple fp (MMP.Flips.logCanonicalDivisor K'
      (QDivisor.toRDivisor (flipTransform f fp (∑ i, Finsupp.single (P i) (q i))))) := by
    have e : MMP.Flips.logCanonicalDivisor K'
        (QDivisor.toRDivisor (flipTransform f fp (∑ i, Finsupp.single (P i) (q i)))) =
        MMP.Flips.logCanonicalDivisor K' B' +
          ∑ i, (q i - b i) • flipTransform f fp (Finsupp.single (P i) (1 : ℝ)) := by
      rw [toRDivisor_flipTransform, hB₀, hFsum, h.eq_flipTransform, hBsum, hFsum,
        MMP.Flips.logCanonicalDivisor, MMP.Flips.logCanonicalDivisor]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    rw [e]
    exact hamp' (fun i => q i - b i) hq3
  obtain ⟨hcart, hRc⟩ := isRCartier_of_isRelativelyAntiAmple hanti
  refine ⟨⟨hQ.1, fun Γ hΓ => ?_, ⟨3, K, hK3, hRc⟩, fun n E a hE ha => ?_⟩, ?_⟩
  · rw [hB₀, coeff_sum_single] at hΓ ⊢
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hΓ
    have hPi : P i = Γ := of_not_not fun hne => hi (if_neg hne)
    rw [Finset.sum_eq_single i (fun j _ hji => if_neg fun h => hP.ne hji (h.trans hPi.symm))
      (by simp), if_pos hPi]
    exact hq4 i
  · rw [hB₀] at ha
    exact hq1 q rfl n E a hE ha
  · exact ⟨h.isQuasiProjectiveVariety_target, ⟨hNE.isNormalVariety_source,
      hNE.isNormalVariety_target, hcart, hNE.isContraction, hanti,
      hNE.relativePicardNumber_eq_one⟩, h.isSmall, h.isBirationalMorphism, h.isProjectiveMorphism,
      h.not_isIso, h.isCanonicalDivisor_flip, h.isSmall_flip, h.isBirationalMorphism_flip,
      h.isProjectiveMorphism_flip, h.not_isIso_flip, h.relativePicardNumber_flip, hampl,
      toRDivisor_flipTransform f fp _⟩

end Flip

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **A real canonical flip has a rational canonical witness.** Let `X ⟶ Z ⟵ X⁺` be a step
(`MMP.Fourfold.IsRealFlipStep`) of an extremal real flip sequence of `ℚ`-factorial
quasi-projective complex threefolds, with canonical divisors `K`, `K'` and real boundaries `B`,
`B'`. If `(X, B)` is real canonical (`MMP.Fourfold.IsRealCanonicalPair`), then `(X⁺, B')` is
real canonical, and there is a `ℚ`-divisor `B₀` on `X` such that `(X, B₀)` and its strict
transform `(X⁺, (f⁺)⁻¹_* f_* B₀)` are real canonical and the same diagram is a step of an
extremal real flip sequence for `B₀`. -/
@[mmp "lem_fourfold_real_canonical_rational_witness"]
public theorem IsRealFlipStep.exists_isRealCanonicalPair_qDivisor
    {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
    {f : X ⟶ Z} {fp : X' ⟶ Z}
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    (hX : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hX' : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX')
    (hd : topologicalKrullDim X = 3) (hd' : topologicalKrullDim X' = 3)
    (hB : IsRealCanonicalPair sX B) :
    IsRealCanonicalPair sX' B' ∧
      ∃ B₀ : QDivisor X,
        IsRealCanonicalPair sX (QDivisor.toRDivisor B₀) ∧
        IsRealCanonicalPair sX' (QDivisor.toRDivisor (flipTransform f fp B₀)) ∧
        IsRealFlipStep sX sZ sX' K (QDivisor.toRDivisor B₀) K'
          (QDivisor.toRDivisor (flipTransform f fp B₀)) f fp := by
  refine ⟨h.isRealCanonicalPair hK hd hd' hB, ?_⟩
  obtain ⟨B₀, hB₀, h₀⟩ := exists_qDivisor_isRealFlipStep h hK hQ hQ' hd hB
  exact ⟨B₀, hB₀, h₀.isRealCanonicalPair hK hd hd' hB₀, h₀⟩

end

end MMP.Fourfold

end
