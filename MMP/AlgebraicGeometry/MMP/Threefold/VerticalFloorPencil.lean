module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.FiberSpace.LogEllipticRelativeSemiample
public import MMP.AlgebraicGeometry.MMP.BasepointFree.UniformRelativeFreeness
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RayLength
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Singularities.GenericSurfacePlaces
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Singularities.PltDifferentCoefficients
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeBasepointFree
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
public import MMP.AlgebraicGeometry.Singularities.DltKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.GenericFibreDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.SurfaceContractionNullFace
public import MMP.AlgebraicGeometry.Positivity.RelativeEffectiveAdjoint
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
public import MMP.AlgebraicGeometry.Positivity.FreeDivisorSteinFactorization
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
public import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain

/-!
# Complemented dlt threefolds with vertical floor have a semiample off-floor pencil

Let `(X, B)` be an effective `ℚ`-factorial projective dlt threefold pair over `ℂ`, and let
`f : X ⟶ Z` be a contraction onto a normal projective variety `Z` with `D = K_X + B` nef over `Z`.
Suppose that `dim Z = 3`, or that `dim Z = 2` and no component of `⌊B⌋` dominates `Z`, and that `D`
is complemented: there is an effective `ℚ`-Cartier divisor `A` with `(X, B + A)` log canonical and
`D + A ∼_ℚ f^*H` for a `ℚ`-Cartier divisor `H` on `Z`.

Then there are a projective dlt pair `(Y, B_Y)` over `Z`, crepant birational to `(X, B)` over `Z`,
and an effective `ℚ`-Cartier divisor `P` on `Y` with support exactly `⌊B_Y⌋`, such that
`D_Y - δ P` is semiample over `Z` for every sufficiently small rational `δ > 0`, where
`D_Y = K_Y + B_Y`. Moreover `D_Y` is semiample over `Z` if and only if `D` is, and if
`⌊B_Y⌋ = 0` then `D` is semiample over `Z`.

The proof runs the klt program for `D - t₀⌊B⌋` over `Z` for a small `t₀`; every step is
`D`-null, and there is no Mori fibre space endpoint. On the endpoint `X'` the adjoints
`D' - t⌊B'⌋`, `0 < t ≤ t₀`, are klt and nef, hence semiample over `Z` by big-core freeness over a
birational base (`dim Z = 3`) or by log elliptic abundance (`dim Z = 2`). A crepant dlt
modification `Y ⟶ X'` with `P` the pull-back of `⌊B'⌋` gives the pencil.

## Main results

* `MMP.Fourfold.exists_isRelativelySemiample_sub_smul_of_isDltPair_of_add_qLinearlyEquivalent`:
  the statement above.

## Implementation notes

* "`f_* 𝒪_X = 𝒪_Z`" with `Z` normal projective is `MMP.Fourfold.IsContraction` together with
  `Z` projective.
* "`D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`" is `D + A ∼_ℚ G`
  (`MMP.Mori.QDivisor.QLinearlyEquivalent`) for a `ℚ`-divisor `G` with `𝒪_X(mG) ≅ f^* M` for some
  `m > 0` and an invertible `𝒪_Z`-module `M` (`M = 𝒪_Z(mH)`), as in
  `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`.
* A component `E` of `⌊B⌋` is *vertical* if its generic point does not map to the generic point
  of `Z`.
* "`(Y, B_Y)` is crepant birational to `(X, B)` over `Z`" is witnessed by a common normal model:
  projective birational morphisms `p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g` and a
  `ℚ`-divisor `Δ_W` on `W` which is the crepant boundary (`MMP.Mori.IsCrepantBoundary`) of both
  `(X, B)` and `(Y, B_Y)`, that is `K_W + Δ_W = p^*(K_X + B) = q^*(K_Y + B_Y)`.
* "Support exactly `⌊B_Y⌋`" is: `P ≥ 0`, and a prime divisor has nonzero coefficient in `P` if and
  only if it has nonzero coefficient in `⌊B_Y⌋`.
* Semiampleness over `Z` is `MMP.Fourfold.QDivisor.IsRelativelySemiample`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold

namespace Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil

/-- **Relative freeness pulls back.** If `M` is a Cartier divisor on `X` which is relatively
free over `Z` and `p : W ⟶ X` is dominant, then `p^*M` is relatively free over `Z` through
`p ≫ f`: a rational function `ψ` generating `𝒪_X(M)` near `p(w)` pulls back to one generating
`𝒪_W(p^*M)` near `w`. -/
private theorem isRelativelyFreeDivisor_of_isPullback {X W Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (p : W ⟶ X) [IsDominant p] (f : X ⟶ Z) {M : Divisor X}
    (hM : M.IsCartier) (hfree : IsRelativelyFreeDivisor f M)
    {hB : ∀ Zc : irreducibleComponents W, p (componentGenericPoint W Zc) ∉ M.supp}
    {M' : Divisor W} (hpb : M.IsPullback p hB M') : IsRelativelyFreeDivisor (p ≫ f) M' := by
  apply isRelativelyFreeDivisor_of_forall_exists
  intro w
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree f hM hfree (p w)
  set A : Divisor X := M + principalDivisor ψ with hAdef
  have hAc : A.IsCartier := hM.add (Divisor.isCartier_principalDivisor ψ)
  have hψ := map_componentGenericPoint_notMem_supp_of_isDominant p (principalDivisor ψ)
  set ψW := pullbackRationalFunction p ψ hψ
  have hA' : A.IsPullback p (map_componentGenericPoint_notMem_supp_of_isDominant p A)
      (M' + principalDivisor ψW) :=
    hpb.add hM (Divisor.isCartier_principalDivisor ψ) _ (Divisor.isPullback_principalDivisor ψ hψ)
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor W,
      (M' + principalDivisor ψW).coeff F = M'.coeff F + F.ord ψW := fun F => by
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  refine ⟨U, hU, ψW, fun F hF => ?_, fun F hwF => ?_⟩
  · have := coeff_nonneg_of_isPullback_of_isEffectiveOn hAc (V := f ⁻¹ᵁ U)
      (fun P hP => by
        rw [hAdef, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h1 P hP) hA' F hF
    rwa [hcoeff] at this
  · let V : X.Opens := ⟨(A.supp : Set X)ᶜ, A.isClosed_supp.isOpen_compl⟩
    have hxV : p w ∈ V := by
      change p w ∉ (A.supp : Set X)
      rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
      rintro ⟨E, hE, hxE⟩
      exact hE (by rw [hAdef, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]; exact h2 E hxE)
    have hzero : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ V).Nonempty → A.coeff P = 0 := by
      rintro P ⟨x, hxP, hxV'⟩
      by_contra hne
      exact hxV' (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, hxP⟩)
    have hF : (F.support ∩ p ⁻¹ᵁ V).Nonempty := ⟨w, hwF, hxV⟩
    have hpos := coeff_nonneg_of_isPullback_of_isEffectiveOn hAc
      (fun P hP => (hzero P hP).symm.le) hA' F hF
    have hneg := coeff_nonneg_of_isPullback_of_isEffectiveOn (hAc.zsmul (-1))
      (fun P hP => by rw [DivisorWithCoeffs.coeff_smul, hzero P hP]; simp)
      (hA'.zsmul hAc (-1) (map_componentGenericPoint_notMem_supp_of_isDominant p _)) F hF
    rw [DivisorWithCoeffs.coeff_smul, hcoeff] at hneg
    rw [hcoeff] at hpos
    simp at hneg
    omega

/-- **The discrepancy does not depend on the canonical divisor within its linear equivalence
class.** Replacing `K` by a linearly equivalent canonical divisor `K'` changes `m(K + Δ)` by the
principal divisor `m · div φ`, so it stays Cartier, and the generating form is unchanged. -/
private theorem isDiscrepancy_of_linearlyEquivalent {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K K' : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (hK' : K'.IsCanonicalDivisor sX n)
    (hKK' : K'.LinearlyEquivalent K) (h : IsDiscrepancy sX n K Δ D a) :
    IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, -, m, hm, ⟨C, hC, hCc⟩, U, hU, τ, hτ, ha⟩ := h
  obtain ⟨φ, hφ⟩ := hKK'
  refine ⟨hX, hK', m, hm, ⟨C + (m : ℤ) • principalDivisor φ, ?_,
    hCc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, U, hU, τ, hτ, ha⟩
  rw [map_add, hC, map_zsmul, ← hφ, map_sub, ← smul_add]
  congr 1
  abel

/-- **The crepant boundary through a rational top form.** If `Δ_W` is the crepant boundary of
`(X, B)` on `W` (for any canonical divisor `K`), `ω ≠ 0` is a rational top form on `X` and
`L = m(div ω + B)` is Cartier, then `Δ_W = (1/m) p^*L - div(p^*ω)`. -/
private theorem crepantBoundary_eq_of_topForm {X W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : MMP.Mori.IsNormalVariety ℂ sX) {n : ℕ} (hn : topologicalKrullDim X = n) {p : W ⟶ X}
    (hW : MMP.Mori.IsNormalVariety ℂ (p ≫ sX)) (hp : MMP.Mori.IsBirationalMorphism p)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [LocallyOfFiniteType (p ≫ sX)] (hnW : topologicalKrullDim W = n) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {ΔW : QDivisor W}
    (hcrep : IsCrepantBoundary sX n K B p hW hp ΔW) {ω : MMP.Mori.RationalTopForms sX n}
    (hω : ω ≠ 0) {m : ℕ} (hm : 0 < m) {L : Divisor X}
    (hL : Divisor.toQDivisor L = (m : ℤ) •
        (Divisor.toQDivisor (MMP.Mori.topFormDivisor sX ω) + B))
    (hLc : L.IsCartier) :
    haveI := hp.isDominant
    ΔW = (1 / (m : ℚ)) • Divisor.toQDivisor (L.pullback hLc
          (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L)) -
        Divisor.toQDivisor (MMP.Mori.divisorOfForm
          (MMP.Mori.pullbackRationalPluriForms sX p (ω.toPluriForms sX))) := by
  haveI := hp.isDominant
  have h' := MMP.ProgramBaseChange.isCrepantBoundary_pullback hX hn hW hp hnW hω hm hL hLc
  have hK' := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hX hn hω
  have hKK' := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hX hn hω hK
  ext F
  have e := IsDiscrepancy.eq (isDiscrepancy_of_linearlyEquivalent hK' hKK' (hcrep F)) (h' F)
  exact neg_inj.mp e

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent: both are linearly equivalent to a canonical divisor. -/
private theorem linearlyEquivalent_divisorOfForm {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [LocallyOfFiniteType sW] (hW : MMP.Mori.IsNormalVariety ℂ sW) {n : ℕ}
    (hn : topologicalKrullDim W = n) {τ τ' : RationalPluriForms sW n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (MMP.Mori.divisorOfForm τ).LinearlyEquivalent (MMP.Mori.divisorOfForm τ') := by
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sW hW hn
  exact (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hKW hτ).trans
    (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hKW hτ').symm

/-- **Relative semiampleness of a Cartier divisor transfers along a proper birational
morphism.** For `p : W ⟶ X` proper birational between normal varieties over `ℂ`, a Cartier
divisor `L` on `X` has a relatively free multiple over `Z` if and only if its pull-back `p^*L`
does over `Z` through `p ≫ f`. One direction pulls back generating sections; the other is the
descent of freeness under proper generically finite covers. -/
private theorem exists_isRelativelyFreeDivisor_iff_of_isPullback {X W Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hX : MMP.Mori.IsNormalVariety ℂ sX) (p : W ⟶ X) [IsProper p]
    (hW : MMP.Mori.IsNormalVariety ℂ (p ≫ sX)) (hp : MMP.Mori.IsBirationalMorphism p)
    (f : X ⟶ Z) {L : Divisor X} (hL : L.IsCartier)
    {hB : ∀ Zc : irreducibleComponents W, p (componentGenericPoint W Zc) ∉ L.supp}
    {L' : Divisor W} (hpb : L.IsPullback p hB L') :
    (∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor f ((k : ℤ) • L)) ↔
      ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor (p ≫ f) ((k : ℤ) • L') := by
  haveI := hp.isDominant
  constructor
  · rintro ⟨k, hk, hfree⟩
    exact ⟨k, hk, isRelativelyFreeDivisor_of_isPullback p f (hL.zsmul _) hfree
      (hpb.zsmul hL _ (map_componentGenericPoint_notMem_supp_of_isDominant p _))⟩
  · rintro ⟨k, hk, hfree⟩
    haveI : Surjective p := surjective_of_isDominant_of_isClosed_range p
      (p.isClosedMap.isClosed_range)
    have hfin : letI := functionFieldMapAlgebra p;
        Module.Finite X.functionField W.functionField := by
      letI := functionFieldMapAlgebra p
      exact Module.Finite.of_surjective (Algebra.linearMap X.functionField W.functionField)
        hp.functionFieldMap_bijective.2
    obtain ⟨m, hm, hmfree⟩ :=
      exists_isRelativelyFreeDivisor_zsmul_of_isRelativelyFreeDivisor_pullback (p ≫ sX) sX hW hX
        p rfl hfin f (hL.zsmul (k : ℤ))
        (hpb.zsmul hL _ (map_componentGenericPoint_notMem_supp_of_isDominant p _)) hfree
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rwa [smul_smul, ← Nat.cast_mul] at hmfree

/-- If `a L₁ = b L₂ + div φ` with `a, b > 0` and `L₁` Cartier, and some multiple of `L₁` is
relatively free, then so is some multiple of `L₂`: `k b L₂ = a (k L₁) + div φ^{-k}`. -/
private theorem exists_isRelativelyFreeDivisor_of_smul_eq_add {W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (g : W ⟶ Z) {L₁ L₂ : Divisor W}
    (hL₁ : L₁.IsCartier) {a b : ℕ} (hb : 0 < b) (φ : (RationalFunctions W)ˣ)
    (h : (a : ℤ) • L₁ = (b : ℤ) • L₂ + principalDivisor φ)
    (hfree : ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor g ((k : ℤ) • L₁)) :
    ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor g ((k : ℤ) • L₂) := by
  obtain ⟨k, hk, hkfree⟩ := hfree
  have h1 := MMP.Fourfold.isRelativelyFreeDivisor_nsmul g (hL₁.zsmul (k : ℤ)) hkfree a
  have h2 : IsRelativelyFreeDivisor g
      ((a : ℤ) • (k : ℤ) • L₁ + principalDivisor (φ⁻¹ ^ k)) :=
    MMP.Fourfold.epi_counit_of_iso g
      (MMP.Mori.Divisor.LinearlyEquivalent.divisorialSheafIso
        (D₁ := (a : ℤ) • (k : ℤ) • L₁ + principalDivisor (φ⁻¹ ^ k))
        (D₂ := (a : ℤ) • (k : ℤ) • L₁) ⟨φ⁻¹ ^ k, add_sub_cancel_left _ _⟩) h1
  refine ⟨k * b, Nat.mul_pos hk hb, ?_⟩
  convert h2 using 1
  ext F
  have e := congrArg (fun D : Divisor W => D.coeff F) h
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
    smul_eq_mul] at e
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
    PrimeDivisor.ord_pow, PrimeDivisor.ord_inv, smul_eq_mul, nsmul_eq_mul]
  push_cast
  linear_combination (-(k : ℤ)) * e

/-- **Relative semiampleness of the adjoint, read on a crepant model.** Let `(X, B)` be a
threefold pair and `p : W ⟶ X` a proper birational morphism from a normal variety on which `Δ_W`
is the crepant boundary. Then there are `m > 0`, a nonzero rational top form `τ` on `W` and a
Cartier divisor `L_W = m(div τ + Δ_W)` (the pull-back of `m(K + B)` up to linear equivalence)
such that `K + B` is semiample over `Z` exactly when some multiple of `L_W` is relatively free
over `Z` through `p ≫ f`. -/
private theorem exists_isRelativelyFreeDivisor_iff_of_isCrepantBoundary {X W Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {K : Divisor X} {B : QDivisor X} (hXB : IsPairWith sX 3 K B) (p : W ⟶ X) [IsProper p]
    (hW : MMP.Mori.IsNormalVariety ℂ (p ≫ sX)) (hp : MMP.Mori.IsBirationalMorphism p)
    {ΔW : QDivisor W} (hcrep : IsCrepantBoundary sX 3 K B p hW hp ΔW) (f : X ⟶ Z)
    (sW : W ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sW] (hs : p ≫ sX = sW) :
    ∃ (m : ℕ) (_ : 0 < m) (τ : RationalPluriForms sW 3 1) (_ : τ ≠ 0) (LW : Divisor W),
      LW.IsCartier ∧
      Divisor.toQDivisor LW = (m : ℤ) • (Divisor.toQDivisor (MMP.Mori.divisorOfForm τ) + ΔW) ∧
      (QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) ↔
        ∃ k : ℕ, 0 < k ∧ IsRelativelyFreeDivisor (p ≫ f) ((k : ℤ) • LW)) := by
  subst hs
  haveI := hp.isDominant
  obtain ⟨hX, hK, hQ⟩ := hXB
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn : topologicalKrullDim X = (3 : ℕ) := hK.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = (3 : ℕ) := by
    haveI := hX.1
    haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp, hn]
  -- a nonzero rational top form `ω` on `X`, with `div ω ∼ K`
  obtain ⟨b⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hn
  set ω : MMP.Mori.RationalTopForms sX 3 := b () with hωdef
  have hω : ω ≠ 0 := b.ne_zero ()
  obtain ⟨φ₀, hφ₀⟩ := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hX hn hω hK
  -- `L = m(div ω + B)` Cartier
  obtain ⟨m, hm, C, hC, hCc⟩ := hQ.exists_pos
  set L : Divisor X := C + (m : ℤ) • principalDivisor φ₀ with hLdef
  have hLc : L.IsCartier := hCc.add ((Divisor.isCartier_principalDivisor φ₀).zsmul _)
  have hL : Divisor.toQDivisor L = (m : ℤ) •
      (Divisor.toQDivisor (MMP.Mori.topFormDivisor sX ω) + B) := by
    rw [hLdef, map_add, hC, map_zsmul, ← hφ₀, map_sub, ← smul_add]
    congr 1
    abel
  have hΔ := crepantBoundary_eq_of_topForm hX hn hW hp hnW hK hcrep hω hm hL hLc
  set τ := MMP.Mori.pullbackRationalPluriForms sX p (ω.toPluriForms sX) with hτdef
  -- `ω ≠ 0` as a `1`-canonical form: `⨂^1` of a module is the module itself
  have hω₁ : ω.toPluriForms sX ≠ 0 := by
    letI := MMP.Mori.functionFieldAlgebra sX
    intro h
    apply hω
    have h' : (PiTensorProduct.tprod X.functionField
        fun _ : Fin 1 => (ω : ⋀[X.functionField]^3 Ω[X.functionField⁄ℂ])) = 0 := h
    have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
    rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''
  have hτ : τ ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hp.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hω₁
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L
  refine ⟨m, hm, τ, hτ, L.pullback hLc hB, MMP.Fourfold.isCartier_of_isPullback p hLc
    (Divisor.isPullback_pullback hLc hB), ?_, ?_⟩
  · rw [hΔ]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    ext F
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, smul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    field_simp
    ring
  · rw [← exists_isRelativelyFreeDivisor_iff_of_isPullback hX p hW hp f hLc
      (Divisor.isPullback_pullback hLc hB),
      MMP.Fourfold.QDivisor.isRelativelySemiample_iff_exists_isRelativelyFreeDivisor f hm hC hCc]
    have e₁ : ((1 : ℕ) : ℤ) • C = ((1 : ℕ) : ℤ) • L + principalDivisor (φ₀⁻¹ ^ m) := by
      ext F
      simp only [hLdef, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        coeff_principalDivisor, PrimeDivisor.ord_pow, PrimeDivisor.ord_inv, smul_eq_mul,
        nsmul_eq_mul]
      push_cast
      ring
    have e₂ : ((1 : ℕ) : ℤ) • L = ((1 : ℕ) : ℤ) • C + principalDivisor (φ₀ ^ m) := by
      ext F
      simp only [hLdef, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
        coeff_principalDivisor, PrimeDivisor.ord_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    exact ⟨exists_isRelativelyFreeDivisor_of_smul_eq_add f hCc one_pos _ e₁,
      exists_isRelativelyFreeDivisor_of_smul_eq_add f hLc one_pos _ e₂⟩

/-- **Crepant boundaries compose.** Let `Δ_W` be the crepant boundary of the pair `(X, B)` on a
birational model `p : W ⟶ X`, and `K_W` a canonical divisor of `W`. For a birational morphism
`v : V ⟶ W` from a normal variety and `r = v ≫ p`, a `ℚ`-divisor `Δ_V` is the crepant boundary of
`(X, B)` through `r` if and only if it is the crepant boundary of `(W, Δ_W)` through `v`: both say
that `-coeff_F(Δ_V)` is the discrepancy of every prime divisor `F` of `V`, and discrepancies are
invariant under crepant pull-back. -/
private theorem isCrepantBoundary_comp_iff {X W V : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) (hK : K.IsCanonicalDivisor sX n) {p : W ⟶ X}
    (hW : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {ΔW : QDivisor W}
    (hcW : IsCrepantBoundary sX n K B p hW hp ΔW) {KW : Divisor W}
    (hKW : KW.IsCanonicalDivisor (p ≫ sX) n) {v : V ⟶ W}
    (hV : IsNormalVariety ℂ (v ≫ p ≫ sX)) (hv : IsBirationalMorphism v) {r : V ⟶ X}
    (hr : v ≫ p = r) (hV' : IsNormalVariety ℂ (r ≫ sX)) (hvp : IsBirationalMorphism r)
    (ΔV : QDivisor V) :
    IsCrepantBoundary sX n K B r hV' hvp ΔV ↔
      IsCrepantBoundary (p ≫ sX) n KW ΔW v hV hv ΔV := by
  subst hr
  have key := (hP.isDiscrepancy_iff_of_crepant p hW hp hK hKW (Or.inl hcW)).2
  refine forall_congr' fun F => ?_
  exact (key ⟨V, v, hV, hv, F⟩ (compDivisorOver p hW hp ⟨V, v, hV, hv, F⟩)
    (valuation_compDivisorOver p hW hp _) _).symm

/-- **The boundary is its own crepant boundary.** For a pair `(Y, Δ)` with canonical divisor
`K`, `Δ` is the crepant boundary of `(Y, Δ)` through the identity: the discrepancy of a prime
divisor `F` of `Y` is `-coeff_F(Δ)`. -/
private theorem isCrepantBoundary_id {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor Y} {Δ : QDivisor Y}
    (hP : MMP.Mori.IsPair sY Δ) (hK : K.IsCanonicalDivisor sY n)
    (hY : IsNormalVariety ℂ (𝟙 Y ≫ sY))
    (hid : IsBirationalMorphism (𝟙 Y)) : IsCrepantBoundary sY n K Δ (𝟙 Y) hY hid Δ := by
  intro F
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor ℂ hP.1 F)
  have e := ha.eq_neg_coeff_of_ofPrimeDivisor hP.1
  subst e
  exact ha

/-- The crepant boundary only depends on the structure morphism through its value. -/
private theorem isCrepantBoundary_congr {W V : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {s₁ s₂ : W ⟶ Spec (.of ℂ)} (h : s₁ = s₂) {n : ℕ} {K : Divisor W}
    {Δ : QDivisor W} {v : V ⟶ W} (hV₁ : IsNormalVariety ℂ (v ≫ s₁))
    (hV₂ : IsNormalVariety ℂ (v ≫ s₂)) (hv : IsBirationalMorphism v) (ΔV : QDivisor V) :
    IsCrepantBoundary s₁ n K Δ v hV₁ hv ΔV ↔ IsCrepantBoundary s₂ n K Δ v hV₂ hv ΔV := by
  subst h
  rfl

/-- **Shifting the boundary by a pulled-back divisor.** If `Δ_Y` is the crepant boundary of
`(X, B)` on `e : Y ⟶ X` and `P = e^*Δ'` for a `ℚ`-Cartier `Δ'`, then `Δ_Y - δP` is the crepant
boundary of `(X, B - δΔ')`: `a(F, X, B - δΔ') = a(F, X, B) + δ coeff_F(e^*Δ')`. -/
private theorem isCrepantBoundary_sub_smul {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hP : IsPairWith sX n K B) {e : Y ⟶ X}
    (hY : IsNormalVariety ℂ (e ≫ sX)) (he : IsBirationalMorphism e) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y}
    (hc : IsCrepantBoundary sX n K B e hY he BY) {Δ' : QDivisor X} (hΔ' : Δ'.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, e (componentGenericPoint Y Z) ∉ Δ'.supp}
    {P : QDivisor Y} (hPb : Δ'.IsPullback e hB P) (δ : ℚ) :
    IsCrepantBoundary sX n K (B - δ • Δ') e hY he (BY - δ • P) := by
  intro F
  obtain ⟨-, hBE, hiff⟩ := hP.isDiscrepancy_add_smul_iff hΔ' ⟨Y, e, hY, he, F⟩
  obtain ⟨-, hiff⟩ := hiff P hPb
  have h := (hiff (-δ) (-BY.coeff F)).mpr (hc F)
  have e₁ : B + -δ • Δ' = B - δ • Δ' := by rw [neg_smul, sub_eq_add_neg]
  have e₂ : -BY.coeff F - -δ * P.coeff F = -(BY - δ • P).coeff F := by
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]; ring
  rw [e₁, e₂] at h
  exact h

/-- The coefficient of `B - t⌊B⌋` at a prime divisor `P` is `b - t⌊b⌋`, for `b` the coefficient
of `B` at `P`. -/
private theorem coeff_sub_smul_roundDown {X : Scheme.{0}} (B : QDivisor X) (t : ℚ)
    (P : MMP.Mori.PrimeDivisor X) :
    (B - t • Divisor.toQDivisor B.roundDown).coeff P = B.coeff P - t * ⌊B.coeff P⌋ := by
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
    DivisorWithCoeffs.coeff_roundDown, smul_eq_mul]

/-- For a boundary coefficient `0 ≤ b ≤ 1` and `t ≤ 1`, the lowered coefficient `b - t⌊b⌋` is
nonnegative. -/
private theorem coeff_sub_smul_roundDown_nonneg {X : Scheme.{0}} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} (hb0 : 0 ≤ B.coeff P) (hb1 : B.coeff P ≤ 1) {t : ℚ}
    (ht1 : t ≤ 1) : 0 ≤ (B - t • Divisor.toQDivisor B.roundDown).coeff P := by
  rw [coeff_sub_smul_roundDown]
  rcases hb1.lt_or_eq with h | h
  · simpa [Int.floor_eq_zero_iff.mpr ⟨hb0, h⟩] using hb0
  · rw [h, Int.floor_one, Int.cast_one, mul_one]
    linarith

/-- For a boundary coefficient `0 ≤ b ≤ 1` and `t > 0`, the lowered coefficient `b - t⌊b⌋` is
less than one. -/
private theorem coeff_sub_smul_roundDown_lt_one {X : Scheme.{0}} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} (hb0 : 0 ≤ B.coeff P) (hb1 : B.coeff P ≤ 1) {t : ℚ}
    (ht : 0 < t) : (B - t • Divisor.toQDivisor B.roundDown).coeff P < 1 := by
  rw [coeff_sub_smul_roundDown]
  rcases hb1.lt_or_eq with h | h
  · simpa [Int.floor_eq_zero_iff.mpr ⟨hb0, h⟩] using h
  · rw [h, Int.floor_one, Int.cast_one, mul_one]
    linarith

/-- The level of the floor-lowering program is below one. -/
private theorem lt_one_of_mul_six_mul_add_one_lt_one {t : ℚ} {m : ℕ} (ht : 0 < t)
    (h : t * (6 * m + 1) < 1) : t < 1 := by
  nlinarith [(by positivity : (0 : ℚ) ≤ 6 * m)]

/-- On a `ℚ`-factorial variety the floor `⌊B⌋` of a `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_roundDown {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hQ : IsQFactorial sX)
    (B : QDivisor X) : (Divisor.toQDivisor B.roundDown).IsQCartier := by
  obtain ⟨m, hm, hmc⟩ := hQ.2 B.roundDown
  exact ⟨m, by exact_mod_cast hm.ne', (m : ℤ) • B.roundDown, by rw [map_zsmul], hmc⟩

/-- **Lowering the floor of a dlt boundary gives a klt pair.** If `(X, B)` is a `ℚ`-factorial dlt
pair, then for `0 < t ≤ 1` the pair `(X, B - t⌊B⌋)` is dlt with `⌊B - t⌊B⌋⌋ = 0`, hence klt. -/
private theorem isDltPair_and_isKltPair_sub_smul_roundDown {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX)
    {K : Divisor X} {B : QDivisor X} (hdlt : IsDltPair sX 3 K B) {t : ℚ} (ht : 0 < t)
    (ht1 : t ≤ 1) :
    IsDltPair sX 3 K (B - t • Divisor.toQDivisor B.roundDown) ∧
      IsKltPair sX 3 K (B - t • Divisor.toQDivisor B.roundDown) := by
  have hTt : (t • Divisor.toQDivisor B.roundDown).IsQCartier :=
    MMP.Flips.QDivisor.IsQCartier.qsmul (isQCartier_roundDown hQ B) t
  have hcoeff : ∀ P, 0 ≤ (B - t • Divisor.toQDivisor B.roundDown).coeff P ∧
      (B - t • Divisor.toQDivisor B.roundDown).coeff P < 1 := fun P =>
    ⟨coeff_sub_smul_roundDown_nonneg (hdlt.2.1 P).1 (hdlt.2.1 P).2 ht1,
      coeff_sub_smul_roundDown_lt_one (hdlt.2.1 P).1 (hdlt.2.1 P).2 ht⟩
  have hpair : IsPairWith sX 3 K (B - t • Divisor.toQDivisor B.roundDown) := by
    refine ⟨hdlt.1.1, hdlt.1.2.1, ?_⟩
    have := hdlt.1.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hTt (-1))
    convert this using 1
    module
  have hTe : (t • Divisor.toQDivisor B.roundDown).IsEffective := fun P => by
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown,
      smul_eq_mul]
    exact mul_nonneg ht.le (by exact_mod_cast Int.floor_nonneg.mpr (hdlt.2.1 P).1)
  have hd : IsDltPair sX 3 K (B - t • Divisor.toQDivisor B.roundDown) :=
    MMP.Threefold.Mori.IsDltPair.of_add hpair (fun P => (hcoeff P).1) hTe hTt
      (by rw [sub_add_cancel]; exact hdlt)
  refine ⟨hd, hd.isKltPair_iff_roundDown_eq_zero.mpr ?_⟩
  refine DivisorWithCoeffs.ext' fun P => ?_
  rw [DivisorWithCoeffs.coeff_roundDown]
  exact Int.floor_eq_zero_iff.mpr (hcoeff P)

/-- **The invariants of the floor-lowering program.** A model `(X', B')` over `Z`, with
canonical divisor `K'` and structure morphism `g' : X' ⟶ Z`, is *floor-lowered* at level `t₀`
with Cartier index `m` for the pair `(X, B)` over `Z` if it is a projective `ℚ`-factorial
threefold contracting onto `Z`, `0 ≤ B' ≤ 1`, `(X', B')` is lc, `(X', B' - t₀⌊B'⌋)` is klt,
`D' = K' + B'` is nef over `Z` with `mD'` Cartier, `(X', B')` is crepant birational to `(X, B)`
over `Z` through a common projective model, and, when `dim Z = 2`, the floor of `B'` is vertical
and `D'` is rationally trivial along the horizontal prime divisors. -/
private structure IsFloorLoweredModel {X Z X' : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z)
    (K : Divisor X) (B : QDivisor X) (m : ℕ) (t₀ : ℚ) (sX' : X' ⟶ Spec (.of ℂ))
    [QuasiCompact sX'] (g' : X' ⟶ Z) (K' : Divisor X') (B' : QDivisor X') : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sX'
  dim_eq : topologicalKrullDim X' = 3
  isQFactorial : IsQFactorial sX'
  isContraction : IsContraction sX' sZ g'
  nonneg : 0 ≤ B'
  coeff_le_one : ∀ P, B'.coeff P ≤ 1
  isLcPair : IsLcPair sX' 3 K' B'
  isKltPair : IsKltPair sX' 3 K' (B' - t₀ • Divisor.toQDivisor B'.roundDown)
  isRelativelyNef : (Divisor.toQDivisor K' + B').IsRelativelyNef sX' g'
  isCartier : ∃ L : Divisor X', Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K' + B') ∧
    L.IsCartier
  generic : topologicalKrullDim Z = 2 →
    (∀ E : MMP.Mori.PrimeDivisor X', B'.roundDown.coeff E ≠ 0 →
      g'.base E.genericPoint ≠ genericPoint Z) ∧
    ∃ n : ℕ, 0 < n ∧ ∃ φ : (RationalFunctions X')ˣ, ∀ E : MMP.Mori.PrimeDivisor X',
      g'.base E.genericPoint = genericPoint Z →
        ((n : ℤ) • (Divisor.toQDivisor K' + B') -
          Divisor.toQDivisor (principalDivisor φ)).coeff E = 0
  commonModel : ∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ X') (ΔW : QDivisor W)
    (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWX' : IsNormalVariety ℂ (q ≫ sX'))
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
    IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g' ∧
      IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sX' 3 K' B' q hWX' hq ΔW

/-- **Horizontal prime divisors have positive degree on the generic fibre.** For a proper
surjective morphism `f : X ⟶ Z` of projective varieties with `dim X = 3` and `dim Z = 2`, the
generic fibre `X_η` is a proper curve over `k(Z)`, and a prime divisor `E` dominating `Z` meets it
in a closed point, of positive residue degree `[κ(ξ_E) : k(Z)]`. -/
private theorem genericFiberPointDegree_pos' {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z} (hf : f ≫ sZ = sX)
    (hdimX : topologicalKrullDim X = 3) (hdimZ : topologicalKrullDim Z = 2)
    (E : MMP.Mori.PrimeDivisor X) (hE : f.base E.genericPoint = genericPoint Z) :
    0 < MMP.Flips.genericFiberPointDegree f E := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : IsProper (f ≫ sZ) := hf ▸ inferInstance
  haveI : IsProper f := IsProper.of_comp f sZ
  haveI : IsDominant f := (isDominant_iff f).mpr (by
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro z
    exact closure_mono (Set.singleton_subset_iff.mpr (by exact ⟨E.genericPoint, hE⟩))
      (specializes_iff_mem_closure.mp ((genericPoint_spec Z).specializes trivial)))
  haveI := AlgebraicGeometry.isProper_fiberToSpecResidueField f (genericPoint Z)
  have hfib : topologicalKrullDim (f.fiber (genericPoint Z)) = 1 := by
    have hcl : closure (Set.range f.base) = Set.univ :=
      ((isDominant_iff f).mp inferInstance).closure_eq
    have hb : topologicalKrullDim (closure (Set.range f.base)) = ((2 : ℕ) : WithBot ℕ∞) := by
      rw [hcl, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Z).isHomeomorph, hdimZ]
      rfl
    have h := MMP.Flips.topologicalKrullDim_fiber_genericPoint_eq_sub f ℂ sX sZ hf (a := 3)
      (by rw [hdimX]; rfl) hb
    rw [map_genericPoint_of_isDominant f] at h
    rw [h]
    rfl
  haveI : AlgebraicGeometry.IsCurve (Z.residueField (genericPoint Z))
      (f.fiberToSpecResidueField (genericPoint Z)) := by
    rw [AlgebraicGeometry.isCurve_iff]
    exact ⟨{ }, hfib⟩
  exact MMP.Flips.genericFiberPointDegree_pos_of_map_genericPoint_eq hE

/-- **The complement has no horizontal component.** If `dim Z = 2`, `D = K + B` is nef over `Z`
and `D + A ∼_ℚ G` with `A ≥ 0` and `𝒪_X(mG) ≅ f^*M`, then no component of `A` dominates `Z`. Over
a general closed point `z` of `Z` every component of the fibre is a curve, no vertical component
of `A` meets the fibre and the horizontal ones meet it in finitely many points; a horizontal
component `E` of `A` meets the fibre at a closed point `x`, and a fibre component `γ ∋ x`, not
contained in `Supp A`, has `(A · γ) > 0`, `(D · γ) ≥ 0` and `((D + A) · γ) = 0`. -/
private theorem coeff_eq_zero_of_horizontal_of_complement {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 2) {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X}
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier)
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∀ E : MMP.Mori.PrimeDivisor X, f.base E.genericPoint = genericPoint Z → A.coeff E = 0 := by
  intro E hE
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI : Surjective f := ⟨hf.surjective⟩
  haveI : IsSeparated sX := hX.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.toIsVariety.toQuasiCompact
  haveI : IsProper sX := by
    haveI := hX
    infer_instance
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have hDq : (Divisor.toQDivisor K + B).IsQCartier := hnef.1
  have hDAq : (Divisor.toQDivisor K + B + A).IsQCartier := hDq.add hAq
  -- `D + A` is numerically trivial on every curve contracted by `f`
  have h0 : ∀ γ : ProperCurve sX, γ.IsContractedBy f →
      (Divisor.toQDivisor K + B + A).intersectionNumber ℂ sX γ.ι γ.dim_le hDAq = 0 := by
    obtain ⟨N, hN, φ₁, hφ₁⟩ := hDG
    obtain ⟨m, hm, L, hL, ⟨e⟩⟩ := hGM
    have hL'' : Divisor.toQDivisor ((N : ℤ) • L + (m : ℤ) • principalDivisor φ₁) =
        ((m * N : ℕ) : ℤ) • (Divisor.toQDivisor K + B + A) := by
      rw [map_add, map_zsmul, map_zsmul, hL, ← hφ₁]
      ext P
      simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_sub, zsmul_eq_mul]
      push_cast
      ring
    refine intersectionNumber_eq_zero_of_isLocalEquation_preimage sX hQ f hDAq
      (Nat.mul_pos hm hN) hL'' fun z => ?_
    obtain ⟨U, hzU, ψ, hψ⟩ := exists_isLocalEquation_preimage_of_iso_pullback f M e z
    refine ⟨U, hzU, ψ ^ (N : ℤ) * φ₁ ^ (m : ℤ), fun P hP => ?_⟩
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      hψ P hP, coeff_principalDivisor, PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow,
      PrimeDivisor.ord_zpow]
  -- on a general closed fibre, `deg(A|_{X_η}) = ∑ (A · C) ≤ 0`
  obtain ⟨U, hUd, hU⟩ := MMP.Flips.exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber
    sX sZ f hf.comp_eq (by rw [hdimX, hdimZ]; rfl) A hAq
  obtain ⟨w, hwU, hwcl⟩ := nonempty_inter_closedPoints hUd.nonempty U.isOpen.isLocallyClosed
  obtain ⟨S, hS, hdeg⟩ := (hU w hwU).2 hwcl
  have hle : MMP.Flips.genericFiberDegree f A ≤ 0 := by
    rw [hdeg]
    refine Finset.sum_nonpos fun C hC => ?_
    have hCw : f C.point = w := by
      have hmem : C.point ∈ ProperCurve.point '' (S : Set (ProperCurve sX)) := ⟨C, hC, rfl⟩
      rw [hS] at hmem
      exact hmem.1
    have hγ : C.IsContractedBy f := fun x hx => by
      have hx' := image_closure_subset_closure_image f.continuous ⟨x, hx, rfl⟩
      rw [Set.image_singleton, hCw, hwcl.closure_eq] at hx'
      rw [hCw]
      exact hx'
    have h1 := h0 C hγ
    rw [QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ A hDq hAq] at h1
    have h2 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hDq C hγ
    linarith
  -- while a horizontal component of `A` makes it positive
  by_contra hAE
  have hA0 : ∀ P, 0 ≤ A.coeff P := fun P => by simpa [DivisorWithCoeffs.coeff_apply] using hA P
  have hpos : 0 < MMP.Flips.genericFiberDegree f A := by
    have hdegE := genericFiberPointDegree_pos' hX hZ hf.comp_eq hdimX hdimZ E hE
    have hmem : E ∈ A.support := Finsupp.mem_support_iff.mpr hAE
    calc (0 : ℚ) < A.coeff E * MMP.Flips.genericFiberPointDegree f E :=
          mul_pos (lt_of_le_of_ne (hA0 E) (Ne.symm hAE)) (by exact_mod_cast hdegE)
      _ ≤ MMP.Flips.genericFiberDegree f A :=
          Finset.single_le_sum
            (f := fun P => A.coeff P * (MMP.Flips.genericFiberPointDegree f P : ℚ))
            (fun P _ => mul_nonneg (hA0 P) (Nat.cast_nonneg _)) hmem
  linarith

/-- **The complement has no horizontal part, and the adjoint is generically principal.** If
`dim Z = 2`, `D = K + B` is nef over `Z` and `D + A ∼_ℚ G` with `A ≥ 0` and `𝒪_X(mG) ≅ f^*M`, then
`A` has no component dominating `Z` (a general fibre curve `γ` would have `(A · γ) > 0` and
`(D · γ) ≥ 0`, while `((D + A) · γ) = 0`), and `ND - div φ` vanishes along every horizontal prime
divisor for some `N > 0`: near the generic point of `Z`, `mG` is principal. -/
private theorem exists_generic_principal_of_complement {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 2) {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X}
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier)
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ n : ℕ, 0 < n ∧ ∃ φ : (RationalFunctions X)ˣ, ∀ E : MMP.Mori.PrimeDivisor X,
      f.base E.genericPoint = genericPoint Z →
        ((n : ℤ) • (Divisor.toQDivisor K + B) -
          Divisor.toQDivisor (principalDivisor φ)).coeff E = 0 := by
  have hA0 := coeff_eq_zero_of_horizontal_of_complement hX hdimX hQ hZ hdimZ hf hnef hA hAq hDG
    M hGM
  obtain ⟨N, hN, φ₁, hφ₁⟩ := hDG
  obtain ⟨m, hm, L, hL, ⟨e⟩⟩ := hGM
  obtain ⟨U, hηU, ψ, hψ⟩ :=
    exists_isLocalEquation_preimage_of_iso_pullback f M e (genericPoint Z)
  refine ⟨m * N, Nat.mul_pos hm hN, ψ ^ (N : ℤ) * φ₁ ^ (m : ℤ), fun E hE => ?_⟩
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := ⟨E.genericPoint, by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, by
    change f E.genericPoint ∈ U
    rw [hE]; exact hηU⟩
  have h1 : L.coeff E = E.ord ψ := hψ E hEU
  have h2 := congrArg (fun D : QDivisor X => D.coeff E) hφ₁
  have h3 := congrArg (fun D : QDivisor X => D.coeff E) hL
  have h4 : A.coeff E = 0 := hA0 E hE

  rw [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor,
    coeff_principalDivisor, zsmul_eq_mul, Int.cast_natCast, h4, add_zero] at h2
  rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast,
    h1] at h3
  rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toQDivisor, Divisor.coeff_toQDivisor, coeff_principalDivisor,
    PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, PrimeDivisor.ord_zpow, zsmul_eq_mul,
    smul_eq_mul, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast,
    Int.cast_natCast, Nat.cast_mul]
  linear_combination (m : ℚ) * h2 - (N : ℚ) * h3

/-- **The starting model.** `(X, B)` itself is floor-lowered at every level `0 < t₀ ≤ 1`, for a
Cartier index `m` of `K + B`. -/
private theorem isFloorLoweredModel_self {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B) (hdlt : IsDltPair sX 3 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
        f.base E.genericPoint ≠ genericPoint Z))
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier)
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    {m : ℕ} {L₀ : Divisor X} (hL₀ : Divisor.toQDivisor L₀ = (m : ℤ) • (Divisor.toQDivisor K + B))
    (hL₀c : L₀.IsCartier) {t₀ : ℚ} (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1) :
    IsFloorLoweredModel sX sZ f K B m t₀ sX f K B := by
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hXn : IsNormalVariety ℂ sX := hdlt.1.1
  have hXid : IsNormalVariety ℂ (𝟙 X ≫ sX) := by rw [Category.id_comp]; exact hXn
  have hid : IsBirationalMorphism (𝟙 X) := isBirationalMorphism_of_isIso _
  have hcrep := isCrepantBoundary_id hdlt.1.isPair hdlt.1.2.1 hXid hid
  refine ⟨hX, hdimX, hQ, hf, hB, fun P => (hdlt.2.1 P).2, hdlt.isLcPair,
    (isDltPair_and_isKltPair_sub_smul_roundDown hQ hdlt ht₀ ht₀1).2, hnef, ⟨L₀, hL₀, hL₀c⟩,
    fun h2 => ?_, ⟨X, 𝟙 X, 𝟙 X, B, hXid, hXid, hid, hid,
      MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X),
      MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X), rfl, hcrep, hcrep⟩⟩
  refine ⟨?_, exists_generic_principal_of_complement hX hdimX hQ hZ h2 hf hnef hA hAq hDG M hGM⟩
  rcases hcase with h3 | ⟨-, hv⟩
  · rw [h3] at h2
    exact absurd h2 (by decide)
  · exact hv

/-- The curve form only depends on the divisor. -/
private theorem curveForm_congr {X : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) {D D' : QDivisor X} (e : D = D') (h : D.IsQCartier)
    (h' : D'.IsQCartier) : QDivisor.curveForm sX D h = QDivisor.curveForm sX D' h' := by
  subst e
  rfl

/-- **The relative curve form is the absolute one on the image class.** For a `ℚ`-Cartier
`ℚ`-divisor `D`, `(D · u) = (D · ι(u))` for `u ∈ N₁(X/S)` and `ι : N₁(X/S) → N₁(X)` the natural
map: both are computed on a relative 1-cycle `Z` with `[Z] = u` as the degree of `D` on `Z`. -/
private theorem relativeCurveForm_apply {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} (π : X ⟶ S)
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (D : QDivisor X) (h : D.IsQCartier)
    (u : RelativeNumericalCurveClasses sX π) :
    QDivisor.relativeCurveForm sX π D h u =
      QDivisor.curveForm sX D h (relativeToAbsolute sX π u) := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π u
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply]
  rfl

/-- The relative curve form of a `ℚ`-Cartier `ℚ`-divisor on the class of a contracted curve is
its intersection number with the curve. -/
private theorem relativeCurveForm_relativeClass {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (π : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX) (hC : C.IsContractedBy π) :
    QDivisor.relativeCurveForm sX π D h (C.relativeClass π hC) =
      (D.intersectionNumber ℂ sX C.ι C.dim_le h : ℝ) := by
  rw [relativeCurveForm_apply]
  exact MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D h C

/-- A finite sum of continuous real linear forms is continuous. -/
private theorem continuous_finset_sum_linearMap {M ι : Type*} [AddCommGroup M] [Module ℝ M]
    [TopologicalSpace M] (s : Finset ι) (φ : ι → M →ₗ[ℝ] ℝ) (hφ : ∀ i ∈ s, Continuous (φ i)) :
    Continuous ⇑(∑ i ∈ s, φ i) := by
  have : ⇑(∑ i ∈ s, φ i) = fun u => ∑ i ∈ s, φ i u := funext fun u => LinearMap.sum_apply s φ u
  rw [this]
  exact continuous_finset_sum s hφ

/-- A relatively nef `ℚ`-Cartier `ℚ`-divisor is nonnegative on the closed relative cone of
curves: it is nonnegative on the classes of contracted curves, which span the cone, and the
form is continuous. -/
private theorem relativeCurveForm_nonneg_of_isRelativelyNef {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (π : X ⟶ S) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] {D : QDivisor X} (hD : D.IsRelativelyNef sX π)
    {u : RelativeNumericalCurveClasses sX π} (hu : u ∈ relativeClosedConeOfCurves sX π) :
    0 ≤ QDivisor.relativeCurveForm sX π D hD.1 u := by
  have hcont : Continuous (QDivisor.relativeCurveForm sX π D hD.1) := by
    simp only [QDivisor.relativeCurveForm, Finsupp.sum]
    refine continuous_finset_sum_linearMap _ _ fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    rw [LinearMap.coe_smul]
    exact (RelativeNumericalCurveClasses.continuous_degree sX π _).const_smul _
  have hcl : IsClosed {u : RelativeNumericalCurveClasses sX π |
      0 ≤ QDivisor.relativeCurveForm sX π D hD.1 u} := isClosed_le continuous_const hcont
  have hsub : (relativeConeOfCurves sX π : Set (RelativeNumericalCurveClasses sX π)) ⊆
      {u | 0 ≤ QDivisor.relativeCurveForm sX π D hD.1 u} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      rw [Set.mem_setOf_eq, relativeCurveForm_relativeClass]
      exact_mod_cast QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hD hD.1 C hC
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add]
      exact add_nonneg hx hy
    | smul c x _ hx =>
      rw [Set.mem_setOf_eq] at hx ⊢
      have hc : c • x = (c : ℝ) • x := rfl
      rw [hc, map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hu
  exact closure_minimal hsub hcl hu

/-- **Floor-lowered rays are `(K' + B')`-null (the length argument).** Let `(X', B')` be
floor-lowered at level `t₀` with Cartier index `m`, `t₀(6m + 1) < 1`, and `R` a
`(K' + B' - t₀⌊B'⌋)`-negative extremal ray of `NE̅(X'/Z)`. Its image in `NE̅(X')` is an extremal
ray, negative for the klt pair `(X', B' - ⌊B'⌋)` since `D' = K' + B'` is nonnegative and `⌊B'⌋`
positive on `R`; it is spanned by a rational curve `γ` with `0 < -(D' - ⌊B'⌋) · γ ≤ 6`, so
`0 ≤ D' · γ < t₀ ⌊B'⌋ · γ ≤ t₀ (6 + D' · γ)` and `m (D' · γ) ∈ ℤ` vanishes. Hence `D'` vanishes on
`R`. -/
private theorem IsFloorLoweredModel.relativeCurveForm_eq_zero {X Z X' : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z}
    {K : Divisor X} {B : QDivisor X} {m : ℕ} {t₀ : ℚ} {sX' : X' ⟶ Spec (.of ℂ)}
    [QuasiCompact sX'] {g' : X' ⟶ Z} {K' : Divisor X'} {B' : QDivisor X'}
    (h : IsFloorLoweredModel sX sZ f K B m t₀ sX' g' K' B') (hm : 0 < m) (ht₀ : 0 < t₀)
    (ht₀m : t₀ * (6 * m + 1) < 1) {R : Set (RelativeNumericalCurveClasses sX' g')}
    (hR : IsNegativeRelativeExtremalRayOf sX' g'
      (Divisor.toQDivisor K' + (B' - t₀ • Divisor.toQDivisor B'.roundDown)) R) :
    ∀ u ∈ R, QDivisor.relativeCurveForm sX' g' (Divisor.toQDivisor K' + B')
      h.isRelativelyNef.1 u = 0 := by
  obtain ⟨hq, hRext, hneg⟩ := hR
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX' := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  have hgZ : g' ≫ sZ = sX' := h.isContraction.comp_eq
  have ht₀1 : t₀ < 1 := lt_one_of_mul_six_mul_add_one_lt_one ht₀ ht₀m
  have hDq : (Divisor.toQDivisor K' + B').IsQCartier := h.isRelativelyNef.1
  have hTq : (Divisor.toQDivisor B'.roundDown).IsQCartier := isQCartier_roundDown h.isQFactorial B'
  set ι := relativeToAbsolute sX' g' with hιdef
  set cD := QDivisor.curveForm sX' (Divisor.toQDivisor K' + B') hDq with hcD
  set cT := QDivisor.curveForm sX' (Divisor.toQDivisor B'.roundDown) hTq with hcT
  -- the curve forms of `K' + B' - t⌊B'⌋`
  have hform : ∀ (t : ℚ) (hqt : (Divisor.toQDivisor K' + (B' - t • Divisor.toQDivisor
      B'.roundDown)).IsQCartier), QDivisor.curveForm sX' _ hqt = cD - (t : ℝ) • cT := by
    intro t hqt
    have hTt := MMP.Flips.QDivisor.IsQCartier.qsmul hTq (-t)
    have e : Divisor.toQDivisor K' + (B' - t • Divisor.toQDivisor B'.roundDown) =
        (Divisor.toQDivisor K' + B') + (-t) • Divisor.toQDivisor B'.roundDown := by module
    rw [curveForm_congr sX' e hqt (hDq.add hTt),
      MMP.Fourfold.QDivisor.curveForm_add sX' _ _ hDq hTt (hDq.add hTt),
      MMP.Fourfold.QDivisor.curveForm_smul sX' (-t) _ hTq hTt]
    push_cast
    rw [neg_smul, ← sub_eq_add_neg]
  obtain ⟨⟨hRK, -, -, -⟩, v, hv0, hRv⟩ := id hRext
  -- `D' ≥ 0` and `t₀ ⌊B'⌋ > D'` on the nonzero classes of `R`
  have hDnn : ∀ w ∈ R, 0 ≤ cD (ι w) := fun w hw => by
    rw [← relativeCurveForm_apply]
    exact relativeCurveForm_nonneg_of_isRelativelyNef g' h.isRelativelyNef (hRK hw)
  have hneg' : ∀ w ∈ R, w ≠ 0 → cD (ι w) - (t₀ : ℝ) * cT (ι w) < 0 := fun w hw hw0 => by
    have := hneg w hw hw0
    rw [relativeCurveForm_apply, hform t₀ hq] at this
    simpa using this
  -- the image ray in `NE̅(X')` is `(K' + B' - ⌊B'⌋)`-negative
  have hkltΔ : IsKltPair sX' 3 K' (B' - Divisor.toQDivisor B'.roundDown) := by
    have hTt := MMP.Flips.QDivisor.IsQCartier.qsmul hTq (1 - t₀)
    have hpair : IsPairWith sX' 3 K' (B' - Divisor.toQDivisor B'.roundDown) := by
      refine ⟨h.isKltPair.1.1, h.isKltPair.1.2.1, ?_⟩
      have := h.isKltPair.1.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hTt (-1))
      convert this using 1
      module
    refine MMP.Threefold.Mori.IsKltPair.of_add hpair (Δ' := (1 - t₀) • Divisor.toQDivisor
      B'.roundDown) (fun P => ?_) hTt ?_
    · rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
        DivisorWithCoeffs.coeff_roundDown, smul_eq_mul]
      have hb : 0 ≤ B'.coeff P := by simpa [DivisorWithCoeffs.coeff_apply] using h.nonneg P
      have hfl : (0 : ℚ) ≤ ⌊B'.coeff P⌋ := by exact_mod_cast Int.floor_nonneg.mpr hb
      exact mul_nonneg (by linarith) hfl
    · have e : B' - Divisor.toQDivisor B'.roundDown + (1 - t₀) • Divisor.toQDivisor
          B'.roundDown = B' - t₀ • Divisor.toQDivisor B'.roundDown := by module
      rw [e]
      exact h.isKltPair
  have hΔ0 : 0 ≤ B' - Divisor.toQDivisor B'.roundDown := fun P => by
    change 0 ≤ (B' - Divisor.toQDivisor B'.roundDown).coeff P
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown]
    exact sub_nonneg.mpr (Int.floor_le _)
  have hRabs : IsNegativeExtremalRayOf sX' (Divisor.toQDivisor K' +
      (B' - Divisor.toQDivisor B'.roundDown)) (ι '' R) := by
    refine ⟨hkltΔ.1.2.2, isExtremalRay_image_relativeToAbsolute sX' sZ g' hgZ hRext, ?_⟩
    rintro _ ⟨w, hw, rfl⟩ hw0
    have hw0' : w ≠ 0 := fun h0 => hw0 (by rw [h0, map_zero])
    have e1 : Divisor.toQDivisor K' + (B' - Divisor.toQDivisor B'.roundDown) =
        Divisor.toQDivisor K' + (B' - (1 : ℚ) • Divisor.toQDivisor B'.roundDown) := by
      rw [one_smul]
    rw [curveForm_congr sX' e1 _ (e1 ▸ hkltΔ.1.2.2), hform 1]
    have h1 := hneg' w hw hw0'
    have h2 := hDnn w hw
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Rat.cast_one, one_smul] at h1 ⊢
    have ht : (t₀ : ℝ) < 1 := by exact_mod_cast ht₀1
    have ht0 : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
    nlinarith
  -- a rational curve `γ` spanning the image ray, with `0 < -(D' - ⌊B'⌋) · γ ≤ 6`
  obtain ⟨γ, -, hRγ, hpos, hle⟩ :=
    exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed sX' hkltΔ hΔ0 hRabs
  have hwγ : OneCycle.numericalClass sX' (γ.cycle ℝ) ∈ ι '' R := by
    rw [hRγ]
    exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨u₀, hu₀, hιu₀⟩ := hwγ
  have e1 : Divisor.toQDivisor K' + (B' - Divisor.toQDivisor B'.roundDown) =
      Divisor.toQDivisor K' + (B' - (1 : ℚ) • Divisor.toQDivisor B'.roundDown) := by
    rw [one_smul]
  rw [curveForm_congr sX' e1 _ (e1 ▸ hkltΔ.1.2.2), hform 1] at hpos hle
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Rat.cast_one, one_smul] at hpos hle
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hιu₀
    rw [← hιu₀, map_zero, map_zero] at hpos
    simp at hpos
  have hd0 := hDnn u₀ hu₀
  have hdt := hneg' u₀ hu₀ hu₀0
  rw [hιu₀] at hd0 hdt
  -- `m (D' · γ)` is an integer
  obtain ⟨L, hL, hLc⟩ := h.isCartier
  have hint : cD (OneCycle.numericalClass sX' (γ.cycle ℝ)) =
      (((L.degreeOn ℂ sX' γ.ι γ.dim_le hLc : ℚ) / m : ℚ) : ℝ) := by
    rw [hcD, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul ℂ sX' γ.ι γ.dim_le _ hDq hm L hLc hL]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hδm : (m : ℝ) * cD (OneCycle.numericalClass sX' (γ.cycle ℝ)) =
      (L.degreeOn ℂ sX' γ.ι γ.dim_le hLc : ℝ) := by
    rw [hint]
    push_cast
    field_simp
  -- the length bound: `0 ≤ m (D' · γ) < 1`
  have ht0 : (0 : ℝ) < t₀ := by exact_mod_cast ht₀
  have htm : (t₀ : ℝ) * (6 * m + 1) < 1 := by exact_mod_cast ht₀m
  have hlt : (m : ℝ) * cD (OneCycle.numericalClass sX' (γ.cycle ℝ)) < 1 := by
    norm_num at hle
    nlinarith [mul_pos hm' ht0]
  have hdeg : L.degreeOn ℂ sX' γ.ι γ.dim_le hLc = 0 := by
    have h1 : (L.degreeOn ℂ sX' γ.ι γ.dim_le hLc : ℝ) < 1 := hδm ▸ hlt
    have h2 : (0 : ℝ) ≤ L.degreeOn ℂ sX' γ.ι γ.dim_le hLc := hδm ▸ mul_nonneg hm'.le hd0
    have h1' : L.degreeOn ℂ sX' γ.ι γ.dim_le hLc < 1 := by exact_mod_cast h1
    have h2' : 0 ≤ L.degreeOn ℂ sX' γ.ι γ.dim_le hLc := by exact_mod_cast h2
    omega
  have hδ : cD (OneCycle.numericalClass sX' (γ.cycle ℝ)) = 0 := by
    have := hδm
    rw [hdeg, Int.cast_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hm'.ne'
  -- hence `D'` vanishes on the ray
  intro u hu
  rw [relativeCurveForm_apply]
  change cD (ι u) = 0
  have hιu : ι u ∈ ι '' R := ⟨u, hu, rfl⟩
  rw [hRγ] at hιu
  obtain ⟨c, -, hc⟩ := hιu
  rw [← hc, map_smul, hδ, smul_zero]

/-- A nonempty closed subset `F` of a scheme has a maximal point: a point `η ∈ F` with no proper
generization in `F`, the generic point of an irreducible component of `F`. -/
private theorem exists_maximal_mem_of_isClosed {X : Scheme.{0}} {F : Set X} (hF : IsClosed F)
    {x₀ : X} (hx₀ : x₀ ∈ F) : ∃ η ∈ F, ∀ y ∈ F, y ⤳ η → y = η := by
  set C := irreducibleComponent (⟨x₀, hx₀⟩ : F) with hCdef
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hMirr : IsIrreducible (((↑) : F → X) '' C) :=
    hC.image _ continuous_subtype_val.continuousOn
  have hMcl : IsClosed (((↑) : F → X) '' C) :=
    hF.isClosedMap_subtype_val _ isClosed_irreducibleComponent
  have hη := hMirr.isGenericPoint_genericPoint hMcl
  set η := hMirr.genericPoint
  have hηM : η ∈ ((↑) : F → X) '' C := hη.mem
  obtain ⟨η', -, hη'⟩ := hηM
  refine ⟨η, hη' ▸ η'.2, fun y hy hyη => ?_⟩
  have hCsub : C ⊆ closure {(⟨y, hy⟩ : F)} := fun c hc => by
    rw [closure_subtype, Set.image_singleton]
    have hcM : (c : X) ∈ ((↑) : F → X) '' C := ⟨c, hc, rfl⟩
    rw [← hη.def] at hcM
    exact (specializes_iff_mem_closure.mp (hyη.trans (specializes_iff_mem_closure.mpr hcM)))
  have hu := eq_irreducibleComponent (isIrreducible_singleton.closure).2 hCsub
  have hyC : (⟨y, hy⟩ : F) ∈ C := by
    rw [hCdef, ← hu]
    exact subset_closure rfl
  have hyM : y ∈ ((↑) : F → X) '' C := ⟨_, hyC, rfl⟩
  rw [← hη.def] at hyM
  exact (hyη.antisymm (specializes_iff_mem_closure.mpr hyM)).eq

/-- **The base of a relative ray contraction lies compatibly over `ℂ`.** If `g : X ⟶ T` is the
contraction of a relative extremal ray of `X` over `Z`, through `g_T : T ⟶ Z`, then
`g_T ≫ s_Z = s_T`: both agree after composing with `g`, which is an isomorphism on global sections
over the affine `Spec ℂ`. -/
private theorem IsNegativeRelativeRayContraction.comp_eq_of_comp_eq
    {X Z T : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g' : X ⟶ Z}
    {D : QDivisor X} {R : Set (RelativeNumericalCurveClasses sX g')} {g : X ⟶ T} {gT : T ⟶ Z}
    (hc : IsNegativeRelativeRayContraction sX g' sT D R g gT) (hgZ : g' ≫ sZ = sX) :
    gT ≫ sZ = sT := by
  obtain ⟨-, hRC, hNEC⟩ := hc
  apply ext_of_isAffine
  have h1 : (g ≫ gT ≫ sZ).appTop = (g ≫ sT).appTop := by
    rw [← Category.assoc, hRC.comp_eq, hgZ, hNEC.isContraction.comp_eq]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h1
  haveI : IsIso g.appTop := hRC.isIso_app ⊤
  exact (cancel_mono g.appTop).mp h1

/-- **The next model of an elementary step contracts onto the base.** If `X_i` contracts onto
`Z` and `X_i ⤏ X_{i+1}` is an elementary dlt step over `Z` (a divisorial contraction or a flip of
`f_i : X_i ⟶ Z_i`, followed by `f_i⁺ : X_{i+1} ⟶ Z_i`), then `X_{i+1}` contracts onto `Z` and has
the dimension of `X_i`: `f_i⁺` and `Z_i ⟶ Z` are surjective with trivial direct image of the
structure sheaf, the latter since `f_i` and `X_i ⟶ Z` are. -/
private theorem IsElementaryDltStep.isContraction_and_dim_eq {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj) :
    IsContraction sXj sZ gj ∧ topologicalKrullDim Xj = topologicalKrullDim Xi := by
  obtain ⟨⟨-, hRC, hNEC⟩, hcomp, hdf⟩ := hstep
  have hfi : fi ≫ hi = gi := hRC.comp_eq
  have hZin : IsNormalVariety ℂ sZi := hNEC.isNormalVariety_target
  have hXin : IsNormalVariety ℂ sXi := hgi.isNormalVariety_source
  have hfpapp : ∀ U, IsIso (fp.app U) := by
    rcases hdf with ⟨-, -, hiso, -⟩ | hflip
    · intro U; infer_instance
    · exact hflip.isSmall.isIso_app
  have hfpsurj : Function.Surjective fp := by
    rcases hdf with ⟨-, -, hiso, -⟩ | hflip
    · exact (Scheme.homeoOfIso (asIso fp)).surjective
    · haveI := hflip.isSmall.isProper
      exact (Scheme.Hom.surjective_of_isIso_app fp hfpapp).surj
  have hhiapp : ∀ U, IsIso (hi.app U) := fun U => by
    have h1 := hgi.isIso_app U
    rw [← hfi, Scheme.Hom.comp_app] at h1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (hi.app U) (fi.app _) (hRC.isIso_app _) h1
  have hhisurj : Function.Surjective hi := fun z => by
    obtain ⟨x, hx⟩ := hgi.surjective z
    exact ⟨fi x, by rw [← hx, ← hfi, Scheme.Hom.comp_apply]⟩
  refine ⟨⟨hmod.isQFactorial.1, hgi.isNormalVariety_target, hmod.comp_eq,
    hmod.isProjectiveMorphism, fun z => ?_, fun U => ?_⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := hhisurj z
    obtain ⟨x, rfl⟩ := hfpsurj y
    exact ⟨x, by rw [← hcomp, Scheme.Hom.comp_apply]⟩
  · rw [← hcomp, Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hhiapp U) (hfpapp _)
  · haveI : MMP.Mori.IsVariety ℂ sZi := hZin.1
    haveI : MMP.Mori.IsVariety ℂ sXi := hXin.1
    rcases hdf with ⟨hbir, -, hiso, -⟩ | hflip
    · rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso fp)).isHomeomorph]
      exact MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZi sXi hbir
    · rw [hflip.isSmall.dim_eq, hflip.isSmall_source.dim_eq]

/-- Composition of a rational map with morphisms is associative. -/
private theorem rationalMap_compHom_compHom {X Y Z W : Scheme.{0}} (φ : X.RationalMap Y)
    (g : Y ⟶ Z) (h : Z ⟶ W) : (φ.compHom g).compHom h = φ.compHom (g ≫ h) := by
  obtain ⟨f, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- A modification `φ` of a morphism `f` into an isomorphism `f⁺` is the morphism `f ≫ (f⁺)⁻¹`. -/
private theorem eq_toRationalMap_of_compHom_eq {X Y Z : Scheme.{0}} {φ : X.RationalMap Y}
    {f : X ⟶ Z} {fp : Y ⟶ Z} [IsIso fp] (hφ : φ.compHom fp = f.toRationalMap) :
    φ = (f ≫ inv fp).toRationalMap := by
  have h1 : φ = φ.compHom (fp ≫ inv fp) := by
    obtain ⟨g, rfl⟩ := φ.exists_rep
    rw [IsIso.hom_inv_id, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.compHom_id]
  rw [h1, ← rationalMap_compHom_compHom, hφ, ← Scheme.RationalMap.id_compHom,
    rationalMap_compHom_compHom, Scheme.RationalMap.id_compHom]

/-- **The two morphisms of an elementary step are birational.** For an elementary dlt step with
contraction `f_i : X_i ⟶ Z_i` and `f⁺ : X_{i+1} ⟶ Z_i`, both maps are birational, `f⁺` is proper,
and `f⁺` is a morphism of varieties over `ℂ`. -/
private theorem IsElementaryDltStep.isBirationalMorphism_and {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj) :
    IsBirationalMorphism fi ∧ IsBirationalMorphism fp ∧ IsProper fp ∧ fp ≫ sZi = sXj := by
  have hsj : fp ≫ sZi = sXj := by
    rw [← IsNegativeRelativeRayContraction.comp_eq_of_comp_eq
      hstep.isNegativeRelativeRayContraction hgi.comp_eq, ← Category.assoc, hstep.comp_eq,
      hmod.comp_eq]
  obtain ⟨-, -, hdf⟩ := hstep
  rcases hdf with ⟨hbir, -, hiso, -⟩ | hflip
  · exact ⟨hbir, isBirationalMorphism_of_isIso _, inferInstance, hsj⟩
  · exact ⟨hflip.isSmall_source.isBirationalMorphism, hflip.isSmall.isBirationalMorphism,
      hflip.isProper, hsj⟩

/-- **Prime divisors across an elementary step.** For an elementary dlt step
`φ : X_i ⤏ X_{i+1}` with contraction `f_i : X_i ⟶ Z_i` and `f⁺ : X_{i+1} ⟶ Z_i`, a divisorial
contraction or a flip, every prime divisor `P'` of `X_{i+1}` lies over the generic point of a prime
divisor `Q` of `Z_i`, over which also lies a prime divisor `P` of `X_i`, and
`coeff_{P'}(φ_* D) = coeff_P(D)` for every divisor `D`: for a flip, `φ_* = (f⁺)⁻¹_* f_*`, both maps
being isomorphisms over the codimension-one points of `Z_i`; for a divisorial contraction, `f⁺` is
an isomorphism and `φ` is the morphism `f_i ≫ (f⁺)⁻¹`. -/
private theorem IsElementaryDltStep.exists_primeDivisor_map_genericPoint_eq
    {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj)
    (P' : MMP.Mori.PrimeDivisor Xj) :
    ∃ (P : MMP.Mori.PrimeDivisor Xi) (Q : MMP.Mori.PrimeDivisor Zi),
      fi.base P.genericPoint = Q.genericPoint ∧ fp.base P'.genericPoint = Q.genericPoint ∧
      ∀ {S : Type*} [AddCommMonoid S] (D : MMP.Mori.DivisorWithCoeffs S Xi),
        MMP.Mori.RationalMap.transformDivisor φ D P' = D P := by
  obtain ⟨-, -, -, hsj⟩ := IsElementaryDltStep.isBirationalMorphism_and hgi hstep hmod
  obtain ⟨⟨-, -, hNEC⟩, -, hdf⟩ := hstep
  have hZin : IsNormalVariety ℂ sZi := hNEC.isNormalVariety_target
  have hXjn : IsNormalVariety ℂ sXj := hmod.isQFactorial.1
  have hfiC := hNEC.isContraction
  haveI : IsProper fi := hfiC.isProper
  haveI : IsIntegral Zi := hZin.1.toIsIntegral
  have hXi' : IsNormalVariety ℂ (fi ≫ sZi) := by rw [hfiC.comp_eq]; exact hgi.isNormalVariety_source
  rcases hdf with ⟨hbir, -, hiso, hmodif⟩ | hflip
  · -- divisorial: `φ` is the proper birational morphism `f_i ≫ (f_i⁺)⁻¹`
    have hφ := eq_toRationalMap_of_compHom_eq hmodif.2
    have hg : (fi ≫ inv fp) ≫ sXj = fi ≫ sZi := by
      rw [← hsj, Category.assoc, IsIso.inv_hom_id_assoc]
    have hXg : IsNormalVariety ℂ ((fi ≫ inv fp) ≫ sXj) := by rw [hg]; exact hXi'
    haveI : IsProper (fi ≫ inv fp) := inferInstance
    have hgbir : IsBirationalMorphism (fi ≫ inv fp) :=
      isBirationalMorphism_comp hbir (isBirationalMorphism_of_isIso _)
    obtain ⟨E, hE, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hXjn hXg hgbir P'
    have hEP : fi.base E.genericPoint = fp.base P'.genericPoint := by
      rw [← hE, ← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hbreg : fp.base P'.genericPoint ∈ biregularLocus fp :=
      le_biregularLocus (V := ⊤) (show IsIso (fp ∣_ ⊤) from inferInstance) trivial
    have hco : Order.coheight (fp.base P'.genericPoint) = 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus fp hbreg).trans
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P')
    refine ⟨E, AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, ?_, ?_, fun D => ?_⟩
    · exact hEP.trans (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    · exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    · rw [hφ]; exact htr D
  · -- flip: `φ_* = (f_i⁺)⁻¹_* (f_i)_*`
    obtain ⟨V, hV1, hV2, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
    haveI := hV1
    haveI := hV2
    have hsep : IsSeparated (Xj ↘ ⊤_ Scheme) := by
      haveI := hXjn.1.toIsSeparated
      rw [show (Xj ↘ ⊤_ Scheme) = sXj ≫ Limits.terminal.from (Spec (.of ℂ)) from
        Subsingleton.elim _ _]
      infer_instance
    have hV' : fp.base P'.genericPoint ∈ V :=
      hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
    obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq fi fp V P' hV'
    have hco : Order.coheight (fp.base P'.genericPoint) = 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus fp
        (le_biregularLocus (V := V) hV2 hV')).trans
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P')
    refine ⟨P, AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, ?_, ?_, fun D => ?_⟩
    · exact hP.trans (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    · exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
    · rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZin hXi'
        hflip.isSmall_source.isBirationalMorphism V hXV hX'V hflip.isModificationOf.2 D,
        MMP.Mori.flipTransform_apply hZin hXi' hflip.isSmall_source.isBirationalMorphism V hXV hP D]

/-- **The transform of a canonical divisor along an elementary step is canonical.** For a
divisorial contraction `φ = f_i ≫ (f⁺)⁻¹` is a proper birational morphism, and the push-forward
of a canonical divisor along it is canonical; for a flip, `φ_* K_i = (f⁺)⁻¹_* (f_i)_* K_i` is the
divisor of the transported top form. -/
private theorem IsElementaryDltStep.isCanonicalDivisor_transformDivisor {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj) {n : ℕ}
    (hKi : Ki.IsCanonicalDivisor sXi n) (hKj : Kj.IsCanonicalDivisor sXj n) :
    Divisor.IsCanonicalDivisor sXj n (MMP.Mori.RationalMap.transformDivisor φ Ki) := by
  obtain ⟨-, -, -, hsj⟩ := IsElementaryDltStep.isBirationalMorphism_and hgi hstep hmod
  obtain ⟨⟨-, -, hNEC⟩, -, hdf⟩ := hstep
  have hZin : IsNormalVariety ℂ sZi := hNEC.isNormalVariety_target
  have hXjn : IsNormalVariety ℂ sXj := hmod.isQFactorial.1
  have hfiC := hNEC.isContraction
  haveI : IsProper fi := hfiC.isProper
  haveI : IsIntegral Zi := hZin.1.toIsIntegral
  have hXi' : IsNormalVariety ℂ (fi ≫ sZi) := by rw [hfiC.comp_eq]; exact hgi.isNormalVariety_source
  rcases hdf with ⟨hbir, -, hiso, hmodif⟩ | hflip
  · have hφ := eq_toRationalMap_of_compHom_eq hmodif.2
    have hg : (fi ≫ inv fp) ≫ sXj = sXi := by
      rw [← hsj, Category.assoc, IsIso.inv_hom_id_assoc, hfiC.comp_eq]
    have hXg : IsNormalVariety ℂ ((fi ≫ inv fp) ≫ sXj) := by
      rw [hg]; exact hgi.isNormalVariety_source
    haveI : IsProper (fi ≫ inv fp) := inferInstance
    have hgbir : IsBirationalMorphism (fi ≫ inv fp) :=
      isBirationalMorphism_comp hbir (isBirationalMorphism_of_isIso _)
    haveI := hgbir.isDominant
    haveI : LocallyOfFiniteType sXj := hXjn.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType ((fi ≫ inv fp) ≫ sXj) := hXg.1.toLocallyOfFiniteType
    rw [hφ]
    exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hXjn hXg hgbir hKj
      (by rw [hg]; exact hKi)
  · obtain ⟨V, hV1, hV2, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
    haveI := hV1
    haveI := hV2
    have hsep : IsSeparated (Xj ↘ ⊤_ Scheme) := by
      haveI := hXjn.1.toIsSeparated
      rw [show (Xj ↘ ⊤_ Scheme) = sXj ≫ Limits.terminal.from (Spec (.of ℂ)) from
        Subsingleton.elim _ _]
      infer_instance
    rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZin hXi'
      hflip.isSmall_source.isBirationalMorphism V hXV hX'V hflip.isModificationOf.2 Ki]
    have hXj' : IsNormalVariety ℂ (fp ≫ sZi) := by rw [hsj]; exact hXjn
    have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZin hXi' hXj'
      hflip.isSmall_source.isBirationalMorphism hflip.isSmall.isBirationalMorphism V hXV hX'V
      (K := Ki) (by rw [hfiC.comp_eq]; exact hKi)
    rwa [hsj] at this

/-- **Cartier transport across an elementary step.** Let `φ : X_i ⤏ X_{i+1}` be an elementary
dlt step with contraction `f_i : X_i ⟶ Z_i` and `f⁺ : X_{i+1} ⟶ Z_i`, and let `L` be a Cartier
divisor on `X_i` with `L = m(K_i + B_i)` and `𝒪_{X_i}(L) ≅ f_i^* M` for an invertible sheaf `M`
on `Z_i`. Then `m(K_{i+1} + φ_* B_i)` is a Cartier divisor `L'` with `𝒪(L') ≅ f⁺^* M`. Write
`M ≅ 𝒪_{Z_i}(L_Z)`; then `L - f_i^* L_Z = div(f_i^* v)` and `K_{i+1} - φ_* K_i = div(f⁺^* w)` for
rational functions `v`, `w` of `Z_i`, and `L' = f⁺^* L_Z + div(f⁺^* v) + m div(f⁺^* w)`: along a
prime divisor `P'` of `X_{i+1}` over the generic point of a prime divisor `Q` of `Z_i`, both maps
are local isomorphisms and every coefficient is computed at `Q`. -/
private theorem IsElementaryDltStep.exists_isCartier_divisorialSheaf_iso_pullback
    {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj) {n : ℕ}
    (hKi : Ki.IsCanonicalDivisor sXi n) (hKj : Kj.IsCanonicalDivisor sXj n) {Bi : QDivisor Xi}
    {m : ℕ} {L : Divisor Xi} (hL : Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor Ki + Bi))
    (M : Zi.Modules) [SheafOfModules.IsInvertible Zi.presheaf Zi.ringCatSheaf.2 M]
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback fi).obj M) :
    ∃ L' : Divisor Xj, Divisor.toQDivisor L' =
        (m : ℤ) • (Divisor.toQDivisor Kj + MMP.Mori.RationalMap.transformDivisor φ Bi) ∧
      ∃ hL' : L'.IsCartier, Nonempty (L'.divisorialSheaf ≅ (Scheme.Modules.pullback fp).obj M) := by
  obtain ⟨hfib, hfpb, hfpP, hsj⟩ := IsElementaryDltStep.isBirationalMorphism_and hgi hstep hmod
  have hcorr := IsElementaryDltStep.exists_primeDivisor_map_genericPoint_eq hgi hstep hmod
  have hφK := IsElementaryDltStep.isCanonicalDivisor_transformDivisor hgi hstep hmod hKi hKj
  have hNEC := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZin : IsNormalVariety ℂ sZi := hNEC.isNormalVariety_target
  have hXjn : IsNormalVariety ℂ sXj := hmod.isQFactorial.1
  haveI : IsIntegral Zi := hZin.1.toIsIntegral
  haveI : IsNormal Zi := hZin.2
  haveI : LocallyOfFiniteType sZi := hZin.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Zi := LocallyOfFiniteType.isLocallyNoetherian sZi
  haveI : QuasiCompact sZi := hZin.1.toQuasiCompact
  haveI : CompactSpace Zi := QuasiCompact.compactSpace_of_compactSpace sZi
  haveI := hfib.isDominant
  haveI := hfpb.isDominant
  -- `M ≅ 𝒪_{Z_i}(L_Z)` and `L ∼ f_i^* L_Z`
  obtain ⟨LZ, hLZ, ⟨eZ⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso_of_isInvertible M
  have hBi := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fi LZ
  have hBj := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp LZ
  obtain ⟨ei⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso (hD := hLZ) (f := fi)
    (hB := hBi)
  obtain ⟨ej⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso (hD := hLZ) (f := fp)
    (hB := hBj)
  obtain ⟨v, hv⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback fi).mapIso eZ.symm ≪≫ ei.symm)
  obtain ⟨vZ, hvZ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfib v
  -- `K_{i+1} ∼ φ_* K_i`
  obtain ⟨w, hw⟩ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sXj hXjn hKj hφK
  obtain ⟨wZ, hwZ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfpb w
  have hvZ' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp
    (principalDivisor vZ)
  set L' : Divisor Xj := LZ.pullback hLZ hBj +
    principalDivisor (pullbackRationalFunction fp vZ hvZ') +
    (m : ℤ) • principalDivisor (pullbackRationalFunction fp wZ hwZ) with hL'def
  have hLZj : (LZ.pullback hLZ hBj).IsCartier :=
    MMP.Mori.Divisor.IsCartier.isCartier_pullback (hD := hLZ) (f := fp) (hB := hBj)
  have hL'c : L'.IsCartier :=
    (hLZj.add (MMP.Mori.Divisor.isCartier_principalDivisor _)).add
      ((MMP.Mori.Divisor.isCartier_principalDivisor _).zsmul _)
  refine ⟨L', ?_, hL'c, ?_⟩
  · refine DivisorWithCoeffs.ext' fun P' => ?_
    obtain ⟨P, Q, hPQ, hP'Q, htr⟩ := hcorr P'
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hfib hPQ
    haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hfpb hP'Q
    have c1 := MMP.Positivity.coeff_eq_of_isPullback P' Q hP'Q hLZ
      (MMP.Mori.Divisor.isPullback_pullback hLZ hBj)
    have c2 := MMP.Positivity.coeff_eq_of_isPullback P' Q hP'Q
      (MMP.Mori.Divisor.isCartier_principalDivisor vZ)
      (MMP.Mori.Divisor.isPullback_principalDivisor vZ hvZ')
    have c3 := MMP.Positivity.coeff_eq_of_isPullback P' Q hP'Q
      (MMP.Mori.Divisor.isCartier_principalDivisor wZ)
      (MMP.Mori.Divisor.isPullback_principalDivisor wZ hwZ)
    have c4 := MMP.Positivity.coeff_eq_of_isPullback P Q hPQ hLZ
      (MMP.Mori.Divisor.isPullback_pullback hLZ hBi)
    have c5 := MMP.Positivity.coeff_eq_of_isPullback P Q hPQ
      (MMP.Mori.Divisor.isCartier_principalDivisor vZ)
      (MMP.Mori.Divisor.isPullback_principalDivisor vZ hvZ)
    have c6 := congrArg (fun D : Divisor Xi => D.coeff P) hv
    have c7 := congrArg (fun D : Divisor Xj => D.coeff P') hw
    have c8 := congrArg (fun D : QDivisor Xi => D.coeff P) hL
    have t1 : (MMP.Mori.RationalMap.transformDivisor φ Ki).coeff P' = Ki.coeff P := htr Ki
    have t2 : (MMP.Mori.RationalMap.transformDivisor φ Bi).coeff P' = Bi.coeff P := htr Bi
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul] at c6 c7 c8 ⊢
    rw [hL'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, c1, c2, c3, t2]
    rw [c4, c5] at c6
    rw [t1, c3] at c7
    push_cast
    have c6' : (L.coeff P : ℚ) = (LZ.coeff Q : ℚ) + ((principalDivisor vZ).coeff Q : ℚ) := by
      exact_mod_cast (by linarith : L.coeff P = LZ.coeff Q + (principalDivisor vZ).coeff Q)
    have c7' : ((principalDivisor wZ).coeff Q : ℚ) = (Kj.coeff P' : ℚ) - (Ki.coeff P : ℚ) := by
      exact_mod_cast (by linarith : (principalDivisor wZ).coeff Q = Kj.coeff P' - Ki.coeff P)
    simp only [Int.cast_mul, Int.cast_natCast, zsmul_eq_mul] at c8 ⊢
    rw [← c6', c7', c8]
    ring
  · exact ⟨(MMP.Mori.Divisor.LinearlyEquivalent.divisorialSheafIso (D₂ := LZ.pullback hLZ hBj)
      ⟨pullbackRationalFunction fp vZ hvZ' * pullbackRationalFunction fp wZ hwZ ^ (m : ℤ), by
        refine DivisorWithCoeffs.ext' fun E => ?_
        simp only [hL'def, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_add,
          DivisorWithCoeffs.coeff_smul, coeff_principalDivisor, PrimeDivisor.ord_mul,
          PrimeDivisor.ord_zpow, smul_eq_mul]
        ring⟩) ≪≫ ej ≪≫ (Scheme.Modules.pullback fp).mapIso eZ⟩

/-- The base of a relative contraction over `Z` is a projective variety over `ℂ` when `Z` is:
`Z_i ⟶ Z` is projective, and it is a morphism over `ℂ` since `X_i ⟶ Z_i` has `𝒪_{Z_i}` as direct
image of the structure sheaf. -/
private theorem IsNegativeRelativeRayContraction.comp_eq_and_isProjectiveVariety
    {X Z T : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} {g' : X ⟶ Z}
    {D : QDivisor X} {R : Set (RelativeNumericalCurveClasses sX g')} {g : X ⟶ T} {gT : T ⟶ Z}
    (hc : IsNegativeRelativeRayContraction sX g' sT D R g gT) (hgZ : g' ≫ sZ = sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    gT ≫ sZ = sT ∧ MMP.Mori.IsProjectiveVariety ℂ sT := by
  have hT := IsNegativeRelativeRayContraction.comp_eq_of_comp_eq hc hgZ
  refine ⟨hT, (AlgebraicGeometry.isProjectiveVariety_iff ℂ sT).mpr
    ⟨hc.isNegativeExtremalContraction.isNormalVariety_target.1, ?_⟩⟩
  rw [← hT]
  exact hc.isRelativeContractionOfFace.isProjectiveMorphism.comp hZ.isProjective

/-- **Same-index Cartier descent.** On a floor-lowered model, `m(K_i + B_i)` descends along the
contraction `f_i : X_i ⟶ Z_i` of a `(K_i + B_i - t₀⌊B_i⌋)`-negative extremal ray `R` of
`NE̅(X_i/Z)`: its image in `NE̅(X_i)` is a negative extremal face for the klt pair
`(X_i, B_i - t₀⌊B_i⌋)` whose contraction is `f_i` (a curve with class in it has degree zero
against the pull-back of an ample divisor of `Z`, so is contracted over `Z`, and its relative
class lies in `R`), and `m(K_i + B_i)` has degree zero on it by the length argument. -/
private theorem IsFloorLoweredModel.exists_isInvertible_iso_pullback {X Z Xi Zi : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsIntegral Xi]
    [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X} {B : QDivisor X} {m : ℕ} {t₀ : ℚ}
    {sXi : Xi ⟶ Spec (.of ℂ)} [QuasiCompact sXi] {gi : Xi ⟶ Z} {Ki : Divisor Xi}
    {Bi : QDivisor Xi} (h : IsFloorLoweredModel sX sZ f K B m t₀ sXi gi Ki Bi)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hm : 0 < m) (ht₀ : 0 < t₀)
    (ht₀m : t₀ * (6 * m + 1) < 1) {sZi : Zi ⟶ Spec (.of ℂ)}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    (hc : IsNegativeRelativeRayContraction sXi gi sZi
      (Divisor.toQDivisor Ki + (Bi - t₀ • Divisor.toQDivisor Bi.roundDown)) R fi hi)
    {L : Divisor Xi} (hL : Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor Ki + Bi))
    (hLc : L.IsCartier) :
    haveI := hLc.isInvertibleModule_divisorialSheaf
    ∃ M : Zi.Modules, SheafOfModules.IsInvertible Zi.presheaf Zi.ringCatSheaf.2 M ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback fi).obj M) := by
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sXi := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  have hgZ : gi ≫ sZ = sXi := h.isContraction.comp_eq
  obtain ⟨-, hZiproj⟩ := IsNegativeRelativeRayContraction.comp_eq_and_isProjectiveVariety hc hgZ hZ
  have hR := hc.isNegativeRelativeExtremalRayOf
  have hRC := hc.isRelativeContractionOfFace
  have hfiC := hc.isNegativeExtremalContraction.isContraction
  have hnull := h.relativeCurveForm_eq_zero hZ hm ht₀ ht₀m hR
  set ι := relativeToAbsolute sXi gi with hιdef
  have hinj : Function.Injective ι :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sXi gi).2 _
      (isNaturalRelativeMap_relativeToAbsolute sXi gi)
  -- a curve whose class lies in `ι '' R` is contracted by `f_i`
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  have hcontr : ∀ C : ProperCurve sXi, OneCycle.numericalClass sXi (C.cycle ℝ) ∈ ι '' R →
      C.IsContractedBy fi := by
    rintro C ⟨u, hu, hCu⟩
    have h0 : C.degree ℂ ((Scheme.Modules.pullback gi).obj H) = 0 := by
      have e1 := OneCycle.degree_cycle ℝ ((Scheme.Modules.pullback gi).obj H) C
      rw [← NumericalCurveClasses.degree_numericalClass, ← hCu,
        ← NumericalCurveClasses.degree_pushforward gi hgZ H,
        LinearMap.mem_ker.mp (range_relativeToAbsolute_le_ker_pushforward gi hgZ ⟨u, rfl⟩),
        map_zero] at e1
      exact_mod_cast e1.symm
    have hCg := MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero gi hgZ H hHa C h0
    have hrel : C.relativeClass gi hCg = u := hinj (by rw [hCu]; rfl)
    exact (hRC.isContractedBy_iff C hCg).mpr (hrel ▸ hu)
  -- the klt pair `(X_i, B_i - t₀⌊B_i⌋)` and its negative face `ι '' R`
  have hklt := h.isKltPair
  have hΔ : (Bi - t₀ • Divisor.toQDivisor Bi.roundDown).IsEffective := fun P =>
    coeff_sub_smul_roundDown_nonneg (by simpa [DivisorWithCoeffs.coeff_apply] using h.nonneg P)
      (h.coeff_le_one P) (lt_one_of_mul_six_mul_add_one_lt_one ht₀ ht₀m).le
  obtain ⟨hq, hRext, hneg⟩ := hR
  have hext := isExtremalRay_image_relativeToAbsolute sXi sZ gi hgZ hRext
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sXi : Set (NumericalCurveClasses sXi))
      (MMP.Fourfold.QDivisor.curveForm sXi
        (Divisor.toQDivisor Ki + (Bi - t₀ • Divisor.toQDivisor Bi.roundDown)) hklt.1.2.2)
      (ι '' R) := by
    obtain ⟨hface, v, hv0, hRv⟩ := hext
    refine ⟨hface, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨-, w, -, hRw⟩ := hRext
      rw [hRw] at ha hb
      obtain ⟨c, hc0, rfl⟩ := ha
      obtain ⟨d, hd0, rfl⟩ := hb
      refine ⟨(c + d) • w, ?_, by rw [map_smul, map_smul, map_smul, add_smul]⟩
      rw [hRw]
      exact ⟨c + d, add_nonneg hc0 hd0, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩ hu0
      have hu0' : u ≠ 0 := fun h0 => hu0 (by rw [h0, map_zero])
      have := hneg u hu hu0'
      rwa [relativeCurveForm_apply] at this
  have hgF : IsContractionOfFace ℂ sXi sZi (ι '' R) fi :=
    ⟨inferInstance, hZiproj, hfiC.comp_eq, hF.1, fun C => ⟨fun hC => ?_, hcontr C⟩,
      hRC.isIso_app⟩
  swap
  · have hCg : C.IsContractedBy gi := fun x hx => by
      rw [← hRC.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
    exact ⟨C.relativeClass gi hCg, (hRC.isContractedBy_iff C hCg).mp hC, rfl⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hgF
    L.divisorialSheaf fun C hC => by
      have hCf := hcontr C hC
      have hCg : C.IsContractedBy gi := fun x hx => by
        rw [← hRC.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hCf x hx]
      have hD := hnull _ ((hRC.isContractedBy_iff C hCg).mp hCf)
      rw [relativeCurveForm_relativeClass] at hD
      rw [ProperCurve.degree_divisorialSheaf C L hLc]
      have h1 := QDivisor.intersectionNumber_eq_of_smul ℂ sXi C.ι C.dim_le _
        h.isRelativelyNef.1 hm L hLc hL
      have hD' : (Divisor.toQDivisor Ki + Bi).intersectionNumber ℂ sXi C.ι C.dim_le
          h.isRelativelyNef.1 = 0 := by exact_mod_cast hD
      rw [hD'] at h1
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      have : ((L.degreeOn ℂ sXi C.ι C.dim_le hLc : ℤ) : ℚ) = 0 := by
        field_simp at h1
        linarith
      exact_mod_cast this
  exact ⟨M, hM, ⟨e⟩⟩

/-- **The order of a pulled-back rational function.** For a birational morphism `f : X ⟶ Y` of
normal integral schemes and a prime divisor `P` of `X` over the generic point of a prime divisor
`Q` of `Y`, `f` is a local isomorphism at `η_P` and `ord_P(f^*φ) = ord_Q(φ)`. -/
private theorem coeff_principalDivisor_pullbackRationalFunction {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : X ⟶ Y} (hf : IsBirationalMorphism f)
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (principalDivisor φ).supp)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint) :
    (principalDivisor (pullbackRationalFunction f φ hφ)).coeff P =
      (principalDivisor φ).coeff Q := by
  haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hf hPQ
  exact MMP.Positivity.coeff_eq_of_isPullback P Q hPQ
    (MMP.Mori.Divisor.isCartier_principalDivisor φ)
    (MMP.Mori.Divisor.isPullback_principalDivisor φ hφ)

/-- **A point over the generic point of a prime divisor is the generic point of a prime
divisor.** For a birational morphism `f : X ⟶ Y` onto a normal scheme, `f` is a local isomorphism
at a point `x` over the generic point of a prime divisor of `Y`, so `x` has codimension one. -/
private theorem exists_primeDivisor_genericPoint_eq_of_map_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) {x : X} {Q : MMP.Mori.PrimeDivisor Y}
    (hx : f x = Q.genericPoint) : ∃ P : MMP.Mori.PrimeDivisor X, P.genericPoint = x := by
  haveI := MMP.Fourfold.isIso_stalkMap_of_map_eq_genericPoint hf hx
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
    exact_mod_cast h.symm
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco⟩

/-- **At most one prime divisor lies over a prime divisor.** A separated birational morphism onto
a normal scheme is injective over the generic point of a prime divisor, whose local ring is a
discrete valuation ring. -/
private theorem primeDivisor_eq_of_map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} [IsSeparated f]
    (hf : IsBirationalMorphism f) {P₁ P₂ : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h₁ : f P₁.genericPoint = Q.genericPoint) (h₂ : f P₂.genericPoint = Q.genericPoint) :
    P₁ = P₂ := by
  haveI := hf.isDominant
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk Q.genericPoint) := inferInstance
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Fourfold.eq_of_map_eq_of_valuationRing hf.functionFieldMap_bijective h₁ h₂)

/-- **The push-forward along a proper birational morphism at a prime divisor.** For a proper
birational morphism `f : X ⟶ Y` of normal varieties and a prime divisor `P` of `X` over the generic
point of a prime divisor `Q` of `Y`, `coeff_Q(f_* D) = coeff_P(D)`. -/
private theorem transformDivisor_toRationalMap_apply_of_map_genericPoint_eq {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) {f : X ⟶ Y}
    (hX : IsNormalVariety ℂ (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint) (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  obtain ⟨E, hE, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf Q
  haveI : IsSeparated (f ≫ sY) := hX.1.toIsSeparated
  haveI : IsSeparated f := IsSeparated.of_comp f sY
  rw [htr D, primeDivisor_eq_of_map_genericPoint_eq hf hE hPQ]

/-- The valuations of a prime divisor `F` of `V`, seen on `k(Y)` through `a ≫ f = b ≫ f'`,
coincide. -/
private theorem comap_valuationOver_eq_of_comp_eq {V X X' Y : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral X] [IsIntegral X'] [IsIntegral Y]
    (F : MMP.Mori.PrimeDivisor V) {a : V ⟶ X} {b : V ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y}
    [IsDominant a] [IsDominant b] [IsDominant f] [IsDominant f'] (h : a ≫ f = b ≫ f') :
    (F.valuationOver a).comap (functionFieldMap f) =
      (F.valuationOver b).comap (functionFieldMap f') := by
  have key : ∀ (c : V ⟶ Y) [IsDominant c], c = b ≫ f' →
      functionFieldMap c = (functionFieldMap b).comp (functionFieldMap f') := by
    intro c _ hc
    subst hc
    exact functionFieldMap_comp b f'
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply, Valuation.comap_apply, PrimeDivisor.valuationOver_apply,
    PrimeDivisor.valuationOver_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
    ← functionFieldMap_comp, ← key (a ≫ f) h]

/-- **Discrepancies only depend on the valuation.** Two divisors over `X` with the same valuation
of `k(X)` have the same discrepancies: this is the crepant invariance of discrepancies along the
identity of `X`, whose crepant boundary is `Δ` itself. -/
private theorem isDiscrepancy_of_valuation_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {D D' : DivisorOver ℂ sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (hv : D.valuation = D'.valuation) : IsDiscrepancy sX n K Δ D' a := by
  have hP := ha.isPair
  have hK : K.IsCanonicalDivisor sX n := ha.2.1
  have hY : IsNormalVariety ℂ (𝟙 X ≫ sX) := by rw [Category.id_comp]; exact hP.1
  have hid : IsBirationalMorphism (𝟙 X) := isBirationalMorphism_of_isIso _
  have hK' : K.IsCanonicalDivisor (𝟙 X ≫ sX) n := by rw [Category.id_comp]; exact hK
  obtain ⟨-, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP (𝟙 X) hY hid hK hK'
    (Or.inl (isCrepantBoundary_id hP hK hY hid))
  let E : DivisorOver ℂ (𝟙 X ≫ sX) :=
    ⟨D.Y, D.f, by rw [Category.id_comp]; exact D.isNormalVariety, D.isBirationalMorphism, D.E⟩
  have hvE : ∀ D'' : DivisorOver ℂ sX, D''.valuation = D.valuation →
      D''.valuation = E.valuation.comap (functionFieldMap (𝟙 X)) := by
    intro D'' h
    rw [h]
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply, functionFieldMap_id_apply]
    rfl
  exact (hiff E D' (hvE D' hv.symm) a).mp ((hiff E D (hvE D rfl) a).mpr ha)

/-- **The discrepancy of a divisor over a prime divisor.** If a divisor `(Y, f, E)` over `X` has
`f(η_E) = η_P` for a prime divisor `P` of `X`, its discrepancy is `-coeff_P(Δ)`: it has the
valuation of `P`. -/
private theorem eq_neg_coeff_of_isDiscrepancy_of_map_genericPoint_eq {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver ℂ sX}
    {P : MMP.Mori.PrimeDivisor X} (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P :=
  (isDiscrepancy_of_valuation_eq h
    (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P
      hP)).eq_neg_coeff_of_ofPrimeDivisor hX

/-- **Crepant comparison over a common base.** Let `f : X ⟶ Y`, `f' : X' ⟶ Y` be proper birational
morphisms of normal varieties with `f_* Δ = f'_* Δ'`, and `K_X + Δ`, `K_{X'} + Δ'` numerically
trivial over `Y` (nef and anti-nef). For a prime divisor `F` on a common normal model
`a : V ⟶ X`, `b : V ⟶ X'` with `a ≫ f = b ≫ f'`, the discrepancies `a(F, X, Δ)` and
`a(F, X', Δ')` agree: if `F` is exceptional over `Y`, the comparison of discrepancies over `Y`
applies in both directions; otherwise `F` lies over a prime divisor `Q` of `Y`, `a` and `b` map it
onto prime divisors `P`, `P'` over `Q`, and both discrepancies are
`-coeff_P Δ = -coeff_Q f_* Δ = -coeff_{P'} Δ'`. -/
private theorem isDiscrepancy_iff_of_isRelativelyNef {X X' Y V : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] [QuasiCompact sX'] (hY : IsNormalVariety ℂ sY) {f : X ⟶ Y} {f' : X' ⟶ Y}
    [IsProper f] [IsProper f'] (hfs : f ≫ sY = sX) (hfs' : f' ≫ sY = sX')
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') {n : ℕ} {K : Divisor X}
    {K' : Divisor X'} {Δ : QDivisor X} {Δ' : QDivisor X'} (hP : IsPairWith sX n K Δ)
    (hP' : IsPairWith sX' n K' Δ')
    (hΔ : MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      MMP.Mori.RationalMap.transformDivisor (X := X') f'.toRationalMap Δ')
    (hN₁ : QDivisor.IsRelativelyNef sX f (Divisor.toQDivisor K + Δ))
    (hN₂ : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor K + Δ)))
    (hN₁' : QDivisor.IsRelativelyNef sX' f' (Divisor.toQDivisor K' + Δ'))
    (hN₂' : QDivisor.IsRelativelyNef sX' f' (-(Divisor.toQDivisor K' + Δ')))
    {a : V ⟶ X} {b : V ⟶ X'} (hVa : IsNormalVariety ℂ (a ≫ sX))
    (hVb : IsNormalVariety ℂ (b ≫ sX')) (ha : IsBirationalMorphism a)
    (hb : IsBirationalMorphism b) (hab : a ≫ f = b ≫ f') (F : MMP.Mori.PrimeDivisor V) (c : ℚ) :
    IsDiscrepancy sX n K Δ ⟨V, a, hVa, ha, F⟩ c ↔
      IsDiscrepancy sX' n K' Δ' ⟨V, b, hVb, hb, F⟩ c := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsIntegral V := hVa.1.toIsIntegral
  haveI : IsNormal V := hVa.2
  haveI : LocallyOfFiniteType (a ≫ sX) := hVa.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (a ≫ sX)
  haveI := hf.isDominant
  haveI := hf'.isDominant
  haveI := ha.isDominant
  haveI := hb.isDominant
  have hX := hP.1
  have hX' := hP'.1
  obtain ⟨c₁, h₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    (⟨V, a, hVa, ha, F⟩ : DivisorOver ℂ sX)
  obtain ⟨c₂, h₂⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP'.isPair hP'.2.1
    (⟨V, b, hVb, hb, F⟩ : DivisorOver ℂ sX')
  suffices h12 : c₁ = c₂ by
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hc.eq h₁, h12]; exact h₂
    · rw [hc.eq h₂, ← h12]; exact h₁
  by_cases hE : RationalMap.IsExceptional (X := V) (a ≫ f).toRationalMap F
  · have hv : (⟨V, a, hVa, ha, F⟩ : DivisorOver ℂ sX).valuation.comap (functionFieldMap f) =
        (⟨V, b, hVb, hb, F⟩ : DivisorOver ℂ sX').valuation.comap (functionFieldMap f') :=
      comap_valuationOver_eq_of_comp_eq F hab
    have hE' : RationalMap.IsExceptional (X := V) (b ≫ f').toRationalMap F := hab ▸ hE
    exact le_antisymm
      (MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hX hX' hY hfs hfs' hf hf' hP.2.1 hP'.2.1 hΔ
        hN₂ hN₁' (⟨V, a, hVa, ha, F⟩ : DivisorOver ℂ sX) (⟨V, b, hVb, hb, F⟩ : DivisorOver ℂ sX')
        hv hE h₁ h₂)
      (MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hX' hX hY hfs' hfs hf' hf hP'.2.1 hP.2.1
        hΔ.symm hN₂' hN₁ (⟨V, b, hVb, hb, F⟩ : DivisorOver ℂ sX')
        (⟨V, a, hVa, ha, F⟩ : DivisorOver ℂ sX) hv.symm hE' h₂ h₁)
  · -- `F` lies over a prime divisor `Q` of `Y`
    have hVY : IsNormalVariety ℂ ((a ≫ f) ≫ sY) := by rw [Category.assoc, hfs]; exact hVa
    obtain ⟨Q, hQv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hY
      (⟨V, a ≫ f, hVY, isBirationalMorphism_comp ha hf, F⟩ : DivisorOver ℂ sY) hE
    have hQa : f (a F.genericPoint) = Q.genericPoint := by
      have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hQv
      exact this
    have hQb : f' (b F.genericPoint) = Q.genericPoint := by
      rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]; exact hQa
    obtain ⟨P, hPa⟩ := exists_primeDivisor_genericPoint_eq_of_map_eq hf hQa
    obtain ⟨P', hPb⟩ := exists_primeDivisor_genericPoint_eq_of_map_eq hf' hQb
    have e1 := eq_neg_coeff_of_isDiscrepancy_of_map_genericPoint_eq hX
      (D := ⟨V, a, hVa, ha, F⟩) hPa.symm h₁
    have e2 := eq_neg_coeff_of_isDiscrepancy_of_map_genericPoint_eq hX'
      (D := ⟨V, b, hVb, hb, F⟩) hPb.symm h₂
    have hXY : IsNormalVariety ℂ (f ≫ sY) := by rw [hfs]; exact hX
    have hXY' : IsNormalVariety ℂ (f' ≫ sY) := by rw [hfs']; exact hX'
    have e3 := transformDivisor_toRationalMap_apply_of_map_genericPoint_eq hY hXY hf
      (P := P) (by rw [hPa]; exact hQa) Δ
    have e4 := transformDivisor_toRationalMap_apply_of_map_genericPoint_eq hY hXY' hf'
      (P := P') (by rw [hPb]; exact hQb) Δ'
    rw [hΔ, e4] at e3
    rw [e1, e2, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, e3]

/-- **Relative numerical triviality of a pull-back.** If `L = mD` is Cartier with
`𝒪_X(L) ≅ f^* M` for an invertible sheaf `M` on `Y`, then `D` and `-D` are nef over `Y`: on a
curve contracted by `f`, `f^* M` has degree zero. -/
private theorem isRelativelyNef_and_neg_of_divisorialSheaf_iso_pullback {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    (hf : f ≫ sY = sX) (M : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M]
    {D : QDivisor X} {m : ℕ} (hm : 0 < m) {L : Divisor X}
    (hL : Divisor.toQDivisor L = (m : ℤ) • D) (hLc : L.IsCartier)
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M) :
    D.IsRelativelyNef sX f ∧ (-D).IsRelativelyNef sX f := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq : D.IsQCartier := ⟨m, hm0, L, hL, hLc⟩
  have hq' : (-D).IsQCartier := ⟨m, hm0, -L, by rw [map_neg, hL, smul_neg], hLc.neg⟩
  have h0 : ∀ C : ProperCurve sX, C.IsContractedBy f →
      D.intersectionNumber ℂ sX C.ι C.dim_le hq = 0 := by
    intro C hC
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le D hq hm L hLc hL,
      ← ProperCurve.degree_divisorialSheaf C L hLc]
    have : C.degree ℂ L.divisorialSheaf = 0 := by
      rw [show C.degree ℂ L.divisorialSheaf = C.degree ℂ ((Scheme.Modules.pullback f).obj M) from
        degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e]
      exact C.degree_pullback_eq_zero_of_isContractedBy f hf hC M
    rw [this]
    simp
  refine ⟨QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq fun C hC => (h0 C hC).ge,
    QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq' fun C hC => ?_⟩
  have e1 : -D = (-1 : ℚ) • D := (neg_one_smul ℚ D).symm
  have hq'' : ((-1 : ℚ) • D).IsQCartier := e1 ▸ hq'
  rw [intersectionNumber_congr sX C.ι C.dim_le hq' hq'' e1,
    intersectionNumber_smul sX C.ι C.dim_le D hq (-1) hq'', h0 C hC, mul_zero]

/-- **Nefness across a common contraction.** Let `f_i : X_i ⟶ Z_i` be proper surjective and
`f⁺ : X_{i+1} ⟶ Z_i` proper, both over `Z` through `h : Z_i ⟶ Z`, `M` invertible on `Z_i`,
`D` nef over `Z` on `X_i` with `𝒪(mD) ≅ f_i^* M`, and `D'` on `X_{i+1}` with
`𝒪(mD') ≅ f⁺^* M`. Then `D'` is nef over `Z`: a curve `C ⊆ X_{i+1}` over a point of `Z` is
either contracted by `f⁺`, where `(D' · C) = 0`, or maps onto a curve `Γ ⊆ Z_i`, the image of a
curve `C' ⊆ X_i` over a point of `Z`, and then
`m (D' · C) = [k(C) : k(Γ)] deg_Γ M` with `deg_Γ M ≥ 0` since
`0 ≤ m (D · C') = [k(C') : k(Γ)] deg_Γ M`. -/
private theorem isRelativelyNef_of_divisorialSheaf_iso_pullback {Z Xi Xj Zi : Scheme.{0}}
    [IsLocallyNoetherian Xi] [IsNormal Xi] [IsLocallyNoetherian Xj] [IsNormal Xj]
    {sXi : Xi ⟶ Spec (.of ℂ)} [QuasiCompact sXi] [LocallyOfFiniteType sXi]
    {sXj : Xj ⟶ Spec (.of ℂ)} [QuasiCompact sXj] {sZi : Zi ⟶ Spec (.of ℂ)} [IsSeparated sZi]
    [LocallyOfFiniteType sZi] [QuasiCompact sZi] {gi : Xi ⟶ Z} {gj : Xj ⟶ Z} {fi : Xi ⟶ Zi}
    {fp : Xj ⟶ Zi} {hi : Zi ⟶ Z} [IsProper fi] [Surjective fi] [IsProper fp]
    (hfi : fi ≫ sZi = sXi) (hfp : fp ≫ sZi = sXj) (hgi : fi ≫ hi = gi) (hgj : fp ≫ hi = gj)
    (M : Zi.Modules) [SheafOfModules.IsInvertible Zi.presheaf Zi.ringCatSheaf.2 M]
    {D : QDivisor Xi} (hD : D.IsRelativelyNef sXi gi) {m : ℕ} (hm : 0 < m) {L : Divisor Xi}
    (hL : Divisor.toQDivisor L = (m : ℤ) • D) (hLc : L.IsCartier)
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback fi).obj M) {D' : QDivisor Xj}
    {L' : Divisor Xj} (hL' : Divisor.toQDivisor L' = (m : ℤ) • D') (hL'c : L'.IsCartier)
    (e' : L'.divisorialSheaf ≅ (Scheme.Modules.pullback fp).obj M) :
    D'.IsRelativelyNef sXj gj := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sXi
  haveI := QuasiCompact.compactSpace_of_compactSpace sXj
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hL'c.isInvertibleModule_divisorialSheaf
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hq : D.IsQCartier := ⟨m, hm0, L, hL, hLc⟩
  have hq' : D'.IsQCartier := ⟨m, hm0, L', hL', hL'c⟩
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sXj hq' fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sXj C.ι C.dim_le D' hq' hm L' hL'c hL',
    ← ProperCurve.degree_divisorialSheaf C L' hL'c,
    show C.degree ℂ L'.divisorialSheaf = C.degree ℂ ((Scheme.Modules.pullback fp).obj M) from
      degreeOn_eq_of_iso ℂ sXj C.ι C.dim_le e', C.degree_pullback fp hfp M]
  split_ifs with hΓ
  · set Γ : ProperCurve sZi := ⟨fp C.point, hΓ⟩ with hΓdef
    obtain ⟨C', hC'pt, hC'deg⟩ :=
      MMP.Fourfold.exists_properCurve_map_eq sXi sZi fi hfi Γ
    -- `C'` lies over a point of `Z`
    have hC'c : C'.IsContractedBy gi := by
      intro x hx
      have h1 : fi x ∈ closure {fp C.point} := by
        have h0 := image_closure_subset_closure_image fi.continuous ⟨x, hx, rfl⟩
        rwa [Set.image_singleton, hC'pt] at h0
      have h2 : closure {fp C.point} ⊆ fp '' closure {C.point} :=
        closure_minimal (Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩)
          (fp.isClosedMap _ isClosed_closure)
      obtain ⟨y, hy, hyx⟩ := h2 h1
      have hCy := hC y hy
      rw [← hgj, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hCy
      rw [← hgi, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hyx, hC'pt]
      exact hCy
    have key : ∀ (y : Zi) (hy : IsProperCurve sZi y), y = fp C.point →
        (⟨y, hy⟩ : ProperCurve sZi).degree ℂ M = Γ.degree ℂ M := by
      rintro y hy rfl
      rfl
    have h0 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sXi hD hq C' hC'c
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sXi C'.ι C'.dim_le D hq hm L hLc hL,
      ← ProperCurve.degree_divisorialSheaf C' L hLc,
      show C'.degree ℂ L.divisorialSheaf = C'.degree ℂ ((Scheme.Modules.pullback fi).obj M) from
        degreeOn_eq_of_iso ℂ sXi C'.ι C'.dim_le e,
      C'.degree_pullback fi hfi M, dif_pos (by rw [hC'pt]; exact hΓ), key _ _ hC'pt] at h0
    have h1 : (0 : ℤ) ≤ (residueFieldDegree fi C'.point : ℤ) * Γ.degree ℂ M := by
      have := (div_nonneg_iff.mp h0).resolve_right fun h => absurd h.2 (not_le.mpr hmq)
      exact_mod_cast this.1
    have hd' : (0 : ℤ) < residueFieldDegree fi C'.point := by
      exact_mod_cast Nat.pos_of_ne_zero hC'deg
    have h2 : 0 ≤ Γ.degree ℂ M := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg hd' hneg
      omega
    exact div_nonneg (by exact_mod_cast mul_nonneg (by positivity) h2) hmq.le
  · simp

/-- **The canonical divisor across an elementary step.** For an elementary dlt step
`φ : X_i ⤏ X_{i+1}` with canonical divisors `K_i`, `K_{i+1}`, there is a rational function `w` of
`Z_i` such that along every prime divisor `P'` of `X_{i+1}`, over the generic point of a prime
divisor `Q` of `Z_i` over which also lies the prime divisor `P` of `X_i` with
`coeff_{P'}(φ_* D) = coeff_P(D)`, `coeff_{P'}(K_{i+1}) = coeff_P(K_i) + ord_Q(w)`:
`K_{i+1} - φ_* K_i` is principal, `φ_* K_i` being canonical. -/
private theorem IsElementaryDltStep.exists_coeff_eq_coeff_add_coeff_principalDivisor
    {Z Xi Xj Zi : Scheme.{0}}
    [IsIntegral Xi] [IsLocallyNoetherian Xi] [IsNormal Xi] [CompactSpace Xi] [IsIntegral Xj]
    [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj] [IsIntegral Zi]
    [IsLocallyNoetherian Zi] [IsNormal Zi] [CompactSpace Zi] {sZ : Z ⟶ Spec (.of ℂ)}
    {sXi : Xi ⟶ Spec (.of ℂ)} {sXj : Xj ⟶ Spec (.of ℂ)} {gi : Xi ⟶ Z} {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {Ki : Divisor Xi} {Δi : QDivisor Xi}
    {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi} {hi : Zi ⟶ Z}
    {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj} (hgi : IsContraction sXi sZ gi)
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki Δi R fi hi fp φ) {Kj : Divisor Xj}
    {Δj : QDivisor Xj} (hmod : IsRelativeDltModel sXj sZ gj Kj Δj) {n : ℕ}
    (hKi : Ki.IsCanonicalDivisor sXi n) (hKj : Kj.IsCanonicalDivisor sXj n) :
    ∃ wZ : (RationalFunctions Zi)ˣ, ∀ P' : MMP.Mori.PrimeDivisor Xj,
      ∃ (P : MMP.Mori.PrimeDivisor Xi) (Q : MMP.Mori.PrimeDivisor Zi),
        fi P.genericPoint = Q.genericPoint ∧ fp P'.genericPoint = Q.genericPoint ∧
        (∀ {S : Type} [AddCommMonoid S] (D : MMP.Mori.DivisorWithCoeffs S Xi),
          MMP.Mori.RationalMap.transformDivisor φ D P' = D P) ∧
        Kj.coeff P' = Ki.coeff P + (MMP.Mori.principalDivisor wZ).coeff Q := by
  obtain ⟨-, hfpb, -, -⟩ := IsElementaryDltStep.isBirationalMorphism_and hgi hstep hmod
  have hcorr := IsElementaryDltStep.exists_primeDivisor_map_genericPoint_eq hgi hstep hmod
  have hφK := IsElementaryDltStep.isCanonicalDivisor_transformDivisor hgi hstep hmod hKi hKj
  have hNEC := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZin : IsNormalVariety ℂ sZi := hNEC.isNormalVariety_target
  have hXjn : IsNormalVariety ℂ sXj := hmod.isQFactorial.1
  haveI : LocallyOfFiniteType sZi := hZin.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZi := hZin.1.toQuasiCompact
  obtain ⟨w, hw⟩ :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sXj hXjn hKj hφK
  obtain ⟨wZ, hwZ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfpb w
  refine ⟨wZ, fun P' => ?_⟩
  obtain ⟨P, Q, hPQ, hP'Q, htr⟩ := hcorr P'
  refine ⟨P, Q, hPQ, hP'Q, htr, ?_⟩
  have c1 := coeff_principalDivisor_pullbackRationalFunction hfpb wZ hwZ hP'Q
  have c2 := congrArg (fun D : Divisor Xj => D.coeff P') hw
  have t1 : (MMP.Mori.RationalMap.transformDivisor φ Ki).coeff P' = Ki.coeff P := htr Ki
  simp only [DivisorWithCoeffs.coeff_sub] at c2
  rw [t1, c1] at c2
  omega

/-- **Projective common models.** Two projective birational morphisms `q : W ⟶ X` and
`e : Y ⟶ X` from normal varieties onto a projective variety are dominated by a third: there are a
normal variety `V` and projective birational morphisms `v : V ⟶ W`, `w : V ⟶ Y` with
`v ≫ q = w ≫ e`. -/
private theorem exists_isProjectiveVariety_commonModel {X W Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {q : W ⟶ X} {e : Y ⟶ X}
    (hW : IsNormalVariety ℂ (q ≫ sX)) (hY : IsNormalVariety ℂ (e ≫ sX))
    (hq : IsBirationalMorphism q) (he : IsBirationalMorphism e) (hqp : IsProjectiveMorphism q)
    (hep : IsProjectiveMorphism e) :
    ∃ (V : Scheme.{0}) (v : V ⟶ W) (w : V ⟶ Y), IsNormalVariety ℂ (v ≫ q ≫ sX) ∧
      IsBirationalMorphism v ∧ IsBirationalMorphism w ∧ IsProjectiveMorphism v ∧
      IsProjectiveMorphism w ∧ v ≫ q = w ≫ e := by
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsProper e := isProper_of_isProjectiveMorphism e hep
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (q ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sX)
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (e ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (e ≫ sX)
  -- a proper normal common model `Z₀`, then a normal Chow modification `V ⟶ Z₀` of it over `W`
  obtain ⟨Z₀, g₁, g₂, hZ₀, hg₁, hg₂, hb₁, hb₂, hc⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_common_model_two sX q hq hW e he hY
  haveI := hg₁
  haveI := hg₂
  haveI : IsIntegral Z₀ := hZ₀.1.toIsIntegral
  haveI : IsNormal Z₀ := hZ₀.2
  haveI : LocallyOfFiniteType (g₁ ≫ q ≫ sX) := hZ₀.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z₀ := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ q ≫ sX)
  obtain ⟨V, h, hVvar, hVn, hhp, hhb, hhg⟩ :=
    MMP.Resolution.Bridges.exists_isProjective_isBirational_isNormal_chowModification ℂ hZ₀.1
      hW.1 g₁ rfl hg₁ (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb₁)
  haveI := hVvar
  haveI : IsIntegral V := hVvar.toIsIntegral
  haveI := hhp.isProper
  haveI := hhg.isProper
  -- `V` is a projective variety
  have hqs : IsProjective (q ≫ sX) := (hqp.comp hX.isProjective).isProjective
  have hVp : IsProjective (h ≫ g₁ ≫ q ≫ sX) := by
    have := hhg.comp hqs
    simpa only [Category.assoc] using this
  haveI hVq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (h ≫ g₁ ≫ q ≫ sX) :=
    { toIsVariety := hVvar, isQuasiProjective := hVp.isQuasiProjective }
  haveI : AlgebraicGeometry.IsVariety ℂ (q ≫ sX) := hW.1
  haveI : AlgebraicGeometry.IsVariety ℂ (e ≫ sX) := hY.1
  have hcomm : (h ≫ g₂) ≫ e ≫ sX = h ≫ g₁ ≫ q ≫ sX := by
    rw [Category.assoc, ← Category.assoc g₂, ← hc, Category.assoc]
  refine ⟨V, h ≫ g₁, h ≫ g₂, by rw [Category.assoc]; exact ⟨hVvar, hVn⟩,
    MMP.Mori.isBirationalMorphism_comp_of_isBirational g₁ h
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb₁) hhb,
    MMP.Mori.isBirationalMorphism_comp_of_isBirational g₂ h
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb₂) hhb,
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety (h ≫ g₁ ≫ q ≫ sX) (q ≫ sX)
      (h ≫ g₁) (Category.assoc _ _ _),
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety (h ≫ g₁ ≫ q ≫ sX) (e ≫ sX)
      (h ≫ g₂) hcomm,
    by rw [Category.assoc, hc, Category.assoc]⟩

/-- **One step of the floor-lowering program.** Let `(X_i, B_i)` be floor-lowered at level `t₀`
with Cartier index `m`, where `t₀(6m + 1) < 1`, and let `X_i ⤏ X_{i+1}` be an elementary dlt step
over `Z` for `K_i + B_i - t₀⌊B_i⌋`, a divisorial contraction or a flip of an extremal ray `R`,
onto a projective dlt model over `Z`. Then the step is `(K_i + B_i)`-null: a rational curve `γ`
spanning `R` has `-(K_i + B_i - ⌊B_i⌋) · γ ≤ 6`, so `0 ≤ (K_i + B_i) · γ < t₀(6 + (K_i + B_i) · γ)`
and `m(K_i + B_i) · γ ∈ ℤ` vanishes; `m(K_i + B_i)` descends to the target of the contraction, and
`(X_{i+1}, B_{i+1})`, `B_{i+1}` the birational transform of `B_i`, is again floor-lowered, with
`⌊B_{i+1}⌋` the transform of `⌊B_i⌋`. -/
private theorem IsFloorLoweredModel.step {X Z Xi Xj Zi : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsIntegral Xi] [IsLocallyNoetherian Xi]
    [IsNormal Xi]
    [CompactSpace Xi] [IsIntegral Xj] [IsLocallyNoetherian Xj] [IsNormal Xj] [CompactSpace Xj]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {K : Divisor X}
    {B : QDivisor X} {m : ℕ} {t₀ : ℚ} {sXi : Xi ⟶ Spec (.of ℂ)} [QuasiCompact sXi]
    {gi : Xi ⟶ Z} {Ki : Divisor Xi} {Bi : QDivisor Xi}
    (h : IsFloorLoweredModel sX sZ f K B m t₀ sXi gi Ki Bi) (hXB : IsPairWith sX 3 K B)
    (hfZ : f ≫ sZ = sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hm : 0 < m) (ht₀ : 0 < t₀)
    (ht₀m : t₀ * (6 * m + 1) < 1) {sXj : Xj ⟶ Spec (.of ℂ)} [QuasiCompact sXj] {gj : Xj ⟶ Z}
    {sZi : Zi ⟶ Spec (.of ℂ)} {R : Set (RelativeNumericalCurveClasses sXi gi)} {fi : Xi ⟶ Zi}
    {hi : Zi ⟶ Z} {fp : Xj ⟶ Zi} {φ : Xi.RationalMap Xj}
    (hstep : IsElementaryDltStep sXi gi sZi sXj gj Ki
      (Bi - t₀ • Divisor.toQDivisor Bi.roundDown) R fi hi fp φ) {Kj : Divisor Xj}
    (hmod : IsRelativeDltModel sXj sZ gj Kj
      (MMP.Mori.RationalMap.transformDivisor φ (Bi - t₀ • Divisor.toQDivisor Bi.roundDown)))
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sXj) :
    IsFloorLoweredModel sX sZ f K B m t₀ sXj gj Kj (MMP.Mori.RationalMap.transformDivisor φ Bi) ∧
      MMP.Mori.RationalMap.transformDivisor φ (Bi - t₀ • Divisor.toQDivisor Bi.roundDown) =
        MMP.Mori.RationalMap.transformDivisor φ Bi -
          t₀ • Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ Bi).roundDown := by
  obtain ⟨hcon, hdimj⟩ := IsElementaryDltStep.isContraction_and_dim_eq h.isContraction hstep hmod
  have hcorr :=
    IsElementaryDltStep.exists_primeDivisor_map_genericPoint_eq.{0} h.isContraction hstep hmod
  set Bj := MMP.Mori.RationalMap.transformDivisor φ Bi with hBjdef
  have hnonneg : 0 ≤ Bj := by
    intro P'
    obtain ⟨P, -, -, -, hP⟩ := hcorr P'
    rw [Finsupp.coe_zero, Pi.zero_apply, hBjdef, hP Bi]
    exact h.nonneg P
  have hle1 : ∀ P', Bj.coeff P' ≤ 1 := by
    intro P'
    obtain ⟨P, -, -, -, hP⟩ := hcorr P'
    rw [DivisorWithCoeffs.coeff_apply, hBjdef, hP Bi]
    exact h.coeff_le_one P
  have hfloor : MMP.Mori.RationalMap.transformDivisor φ
      (Bi - t₀ • Divisor.toQDivisor Bi.roundDown) = Bj - t₀ • Divisor.toQDivisor Bj.roundDown := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨P, -, -, -, hP⟩ := hcorr P'
    rw [hP (Bi - t₀ • Divisor.toQDivisor Bi.roundDown), Finsupp.sub_apply, Finsupp.sub_apply,
      Finsupp.smul_apply, Finsupp.smul_apply, hBjdef, hP Bi]
    have e1 : Divisor.toQDivisor Bi.roundDown P = ⌊Bi P⌋ := by
      rw [← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toQDivisor,
        DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_apply]
    have e2 : Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ Bi).roundDown P' =
        ⌊Bi P⌋ := by
      rw [← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toQDivisor,
        DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_apply, hP Bi]
    rw [e1, e2]
  -- `(X_{i+1}, B_{i+1} - t₀⌊B_{i+1}⌋)` is the dlt model of the program, with `⌊ ⌋ = 0`
  have hdimj3 : topologicalKrullDim Xj = 3 := hdimj.trans h.dim_eq
  have hKj : Kj.IsCanonicalDivisor sXj 3 := by
    obtain ⟨n, hn⟩ := hmod.isCanonicalDivisor
    have h1 := hn.topologicalKrullDim_eq
    rw [hdimj3] at h1
    have : n = 3 := by exact_mod_cast h1.symm
    exact this ▸ hn
  have hdltj : IsDltPair sXj 3 Kj (Bj - t₀ • Divisor.toQDivisor Bj.roundDown) := by
    have := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sXj hKj _).mp hmod.isDltPair
    rwa [hfloor] at this
  have ht₀1 : t₀ < 1 := lt_one_of_mul_six_mul_add_one_lt_one ht₀ ht₀m
  have hkltj : IsKltPair sXj 3 Kj (Bj - t₀ • Divisor.toQDivisor Bj.roundDown) := by
    refine hdltj.isKltPair_iff_roundDown_eq_zero.mpr (DivisorWithCoeffs.ext' fun P => ?_)
    have hb0 : 0 ≤ Bj.coeff P := by simpa [DivisorWithCoeffs.coeff_apply] using hnonneg P
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact Int.floor_eq_zero_iff.mpr ⟨coeff_sub_smul_roundDown_nonneg hb0 (hle1 P) ht₀1.le,
      coeff_sub_smul_roundDown_lt_one hb0 (hle1 P) ht₀⟩
  -- the step is `(K_i + B_i)`-trivial over `Z_i`: `m(K_i + B_i)` descends to `Z_i` and lifts
  have hc := hstep.isNegativeRelativeRayContraction
  have hgi : fi ≫ hi = gi := hc.isRelativeContractionOfFace.comp_eq
  have hgj : fp ≫ hi = gj := hstep.comp_eq
  have hfiC := hc.isNegativeExtremalContraction.isContraction
  have hfis : fi ≫ sZi = sXi := hfiC.comp_eq
  have hZin : IsNormalVariety ℂ sZi := hc.isNegativeExtremalContraction.isNormalVariety_target
  have hXjn : IsNormalVariety ℂ sXj := hmod.isQFactorial.1
  have hXin : IsNormalVariety ℂ sXi := h.isLcPair.1.1
  obtain ⟨hfib, hfpb, hfpP, hsj⟩ :=
    IsElementaryDltStep.isBirationalMorphism_and h.isContraction hstep hmod
  haveI : IsProper fi := hfiC.isProper
  haveI := hfpP
  haveI := hfib.isDominant
  haveI := hfpb.isDominant
  haveI : Surjective fi :=
    surjective_of_isDominant_of_isClosed_range fi fi.isClosedMap.isClosed_range
  haveI : IsIntegral Zi := hZin.1.toIsIntegral
  haveI : IsNormal Zi := hZin.2
  haveI : LocallyOfFiniteType sZi := hZin.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Zi := LocallyOfFiniteType.isLocallyNoetherian sZi
  haveI : QuasiCompact sZi := hZin.1.toQuasiCompact
  haveI : IsSeparated sZi := hZin.1.toIsSeparated
  haveI : CompactSpace Zi := QuasiCompact.compactSpace_of_compactSpace sZi
  haveI : LocallyOfFiniteType sXi := hXin.1.toLocallyOfFiniteType
  obtain ⟨L, hL, hLc⟩ := h.isCartier
  obtain ⟨M, hM, ⟨e⟩⟩ := h.exists_isInvertible_iso_pullback hZ hm ht₀ ht₀m hc hL hLc
  haveI := hM
  obtain ⟨L', hL', hL'c, ⟨e'⟩⟩ := IsElementaryDltStep.exists_isCartier_divisorialSheaf_iso_pullback
    h.isContraction hstep hmod h.isLcPair.1.2.1 hKj hL M e
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqj : (Divisor.toQDivisor Kj + Bj).IsQCartier := ⟨m, hm0, L', hL', hL'c⟩
  have hPj : IsPairWith sXj 3 Kj Bj := ⟨hXjn, hKj, hqj⟩
  obtain ⟨hNi₁, hNi₂⟩ :=
    isRelativelyNef_and_neg_of_divisorialSheaf_iso_pullback fi hfis M hm hL hLc e
  obtain ⟨hNj₁, hNj₂⟩ :=
    isRelativelyNef_and_neg_of_divisorialSheaf_iso_pullback fp hsj M hm hL' hL'c e'
  have hXi' : IsNormalVariety ℂ (fi ≫ sZi) := by rw [hfis]; exact hXin
  have hXj' : IsNormalVariety ℂ (fp ≫ sZi) := by rw [hsj]; exact hXjn
  -- `f_{i*} B_i = f⁺_* B_{i+1}`
  have hΔ : MMP.Mori.RationalMap.transformDivisor (X := Xi) fi.toRationalMap Bi =
      MMP.Mori.RationalMap.transformDivisor (X := Xj) fp.toRationalMap Bj := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨P', hP', -, htrj⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZin hXj' hfpb Q
    obtain ⟨P₀, Q₀, hP₀, hP'Q₀, htr⟩ := hcorr P'
    obtain rfl : Q₀ = Q :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP'Q₀.symm.trans hP')
    rw [transformDivisor_toRationalMap_apply_of_map_genericPoint_eq hZin hXi' hfib hP₀ Bi,
      htrj Bj, hBjdef, htr Bi]
  -- discrepancies over `X_i` and `X_{i+1}` agree
  have hcrep := fun {V : Scheme.{0}} {a : V ⟶ Xi} {b : V ⟶ Xj} (hVa : IsNormalVariety ℂ (a ≫ sXi))
      (hVb : IsNormalVariety ℂ (b ≫ sXj)) (ha : IsBirationalMorphism a)
      (hb : IsBirationalMorphism b) (hab : a ≫ fi = b ≫ fp) (F : MMP.Mori.PrimeDivisor V)
      (c : ℚ) =>
    isDiscrepancy_iff_of_isRelativelyNef hZin hfis hsj hfib hfpb h.isLcPair.1 hPj hΔ hNi₁ hNi₂
      hNj₁ hNj₂ hVa hVb ha hb hab F c
  refine ⟨⟨hproj, hdimj3, hmod.isQFactorial, hcon, hnonneg, hle1, ?lc, hkltj, ?nef,
    ⟨L', hL', hL'c⟩, ?generic, ?commonModel⟩, hfloor⟩
  case nef =>
    exact isRelativelyNef_of_divisorialSheaf_iso_pullback hfis hsj hgi hgj M h.isRelativelyNef hm
      hL hLc e hL' hL'c e'
  case lc =>
    refine ⟨hPj, MMP.Mori.le_discrep_iff.mpr fun D' c _ hc' => ?_⟩
    -- a model of `D'` dominating `X_i` over `Z_i`
    obtain ⟨ψ, hψ, hψS⟩ := MMP.Mori.exists_isBirational_compHom_eq hfpb hfib
    obtain ⟨Y, g₁, g₂, hYn, hg₁, -, -, hg₂, -, hcomm, P, hPv⟩ :=
      MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
        hXjn hXin fp fi ψ hψ hψS D'
    have hYn' : IsNormalVariety ℂ (g₂ ≫ sXi) := by
      rw [← hfis, ← Category.assoc, ← hcomm, Category.assoc, hsj]; exact hYn
    have hcj := isDiscrepancy_of_valuation_eq hc' hPv.symm
    have hci := (hcrep hYn' hYn hg₂ hg₁ hcomm.symm P c).mpr hcj
    by_cases hex : (⟨Y, g₂, hYn', hg₂, P⟩ : DivisorOver ℂ sXi).IsExceptional
    · exact le_trans h.isLcPair.2 (MMP.Mori.discrep_le hex hci)
    · obtain ⟨P₀, -, hP₀⟩ :=
        MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff h.isLcPair.1 _ hex
      have hcP := hci.eq hP₀
      have h1 := h.coeff_le_one P₀
      have hle' : (-1 : ℚ) ≤ c := by rw [hcP]; linarith
      have hle : ((-1 : ℚ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hle'
      calc (-1 : EReal) = ((-1 : ℝ) : EReal) := by rw [EReal.coe_neg, EReal.coe_one]
        _ ≤ ((c : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by exact_mod_cast hle)
  case generic =>
    intro h2
    obtain ⟨hvert, n, hn, χ, hχ⟩ := h.generic h2
    obtain ⟨wZ, hw⟩ := IsElementaryDltStep.exists_coeff_eq_coeff_add_coeff_principalDivisor
      h.isContraction hstep hmod h.isLcPair.1.2.1 hKj
    obtain ⟨χZ, hχZ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfib χ
    have hψ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp
      (principalDivisor (χZ * wZ ^ (n : ℤ)))
    have hg : ∀ (P : MMP.Mori.PrimeDivisor Xi) (E : MMP.Mori.PrimeDivisor Xj)
        (Q : MMP.Mori.PrimeDivisor Zi), fi P.genericPoint = Q.genericPoint →
        fp E.genericPoint = Q.genericPoint → gi P.genericPoint = gj E.genericPoint := by
      intro P E Q hPQ hEQ
      rw [← hgi, ← hgj, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hPQ, hEQ]
    refine ⟨fun E hE => ?_, n, hn, pullbackRationalFunction fp (χZ * wZ ^ (n : ℤ)) hψ,
      fun E hE => ?_⟩
    · obtain ⟨P, Q, hPQ, hEQ, htr, -⟩ := hw E
      have hBE : Bj.coeff E = Bi.coeff P := htr Bi
      have hfl : Bi.roundDown.coeff P ≠ 0 := by
        rw [DivisorWithCoeffs.coeff_roundDown] at hE ⊢
        rwa [hBE] at hE
      rw [← hg P E Q hPQ hEQ]
      exact hvert P hfl
    · obtain ⟨P, Q, hPQ, hEQ, htr, hKE⟩ := hw E
      have hBE : Bj.coeff E = Bi.coeff P := htr Bi
      have h0 := hχ P (by rw [hg P E Q hPQ hEQ]; exact hE)
      have c1 := coeff_principalDivisor_pullbackRationalFunction hfpb _ hψ hEQ
      have c2 := coeff_principalDivisor_pullbackRationalFunction hfib _ hχZ hPQ
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, zsmul_eq_mul] at h0 ⊢
      rw [c1, hKE, hBE]
      rw [c2] at h0
      simp only [coeff_principalDivisor, PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow,
        smul_eq_mul] at h0 ⊢
      push_cast
      linear_combination h0
  case commonModel =>
    obtain ⟨W, p, q, ΔW, hWX, hWXi, hp, hq, hpP, hqP, hpq, hcX, hcXi⟩ := h.commonModel
    haveI : IsIntegral W := hWXi.1.toIsIntegral
    haveI : IsNormal W := hWXi.2
    haveI : LocallyOfFiniteType (q ≫ sXi) := hWXi.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (q ≫ sXi)
    haveI : QuasiCompact (q ≫ sXi) := hWXi.1.toQuasiCompact
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sXi)
    have hgZ : gi ≫ sZ = sXi := h.isContraction.comp_eq
    have hZiproj :=
      (IsNegativeRelativeRayContraction.comp_eq_and_isProjectiveVariety hc hgZ hZ).2
    haveI : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sXi :=
      { toIsVariety := hXin.1,
        isQuasiProjective := h.isProjectiveVariety.isProjective.isQuasiProjective }
    haveI : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sXj :=
      { toIsVariety := hXjn.1, isQuasiProjective := hproj.isProjective.isQuasiProjective }
    haveI : AlgebraicGeometry.IsVariety ℂ sZi := hZin.1
    have hfiP : IsProjectiveMorphism fi :=
      MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sXi sZi fi hfis
    have hfpP' : IsProjectiveMorphism fp :=
      MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sXj sZi fp hsj
    have hWZ : IsNormalVariety ℂ ((q ≫ fi) ≫ sZi) := by
      rw [Category.assoc, hfis]; exact hWXi
    obtain ⟨V, v, w, hVv, hv, hw, hvp, hwp, hvw⟩ :=
      exists_isProjectiveVariety_commonModel hZiproj hWZ hXj'
        (isBirationalMorphism_comp hq hfib) hfpb (hqP.comp hfiP) hfpP'
    haveI : IsIntegral V := hVv.1.toIsIntegral
    haveI : IsNormal V := hVv.2
    haveI : LocallyOfFiniteType (v ≫ (q ≫ fi) ≫ sZi) := hVv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V :=
      LocallyOfFiniteType.isLocallyNoetherian (v ≫ (q ≫ fi) ≫ sZi)
    have hsW : p ≫ sX = q ≫ sXi := by
      rw [← hfZ, ← Category.assoc, hpq, Category.assoc, hgZ]
    have e0 : v ≫ (q ≫ fi) ≫ sZi = v ≫ q ≫ sXi := by rw [Category.assoc, hfis]
    have hVX : IsNormalVariety ℂ ((v ≫ p) ≫ sX) := by
      rw [Category.assoc, hsW, ← e0]; exact hVv
    have hVXi : IsNormalVariety ℂ ((v ≫ q) ≫ sXi) := by rw [Category.assoc, ← e0]; exact hVv
    have hVXp : IsNormalVariety ℂ (v ≫ p ≫ sX) := by rw [hsW, ← e0]; exact hVv
    have hVXq : IsNormalVariety ℂ (v ≫ q ≫ sXi) := by rw [← e0]; exact hVv
    have hVY : IsNormalVariety ℂ (w ≫ sXj) := by
      rw [← hsj, ← Category.assoc, ← hvw, Category.assoc]; exact hVv
    have hvp' : IsBirationalMorphism (v ≫ p) := isBirationalMorphism_comp hv hp
    have hvq' : IsBirationalMorphism (v ≫ q) := isBirationalMorphism_comp hv hq
    obtain ⟨⟨ΔV, hΔV, -⟩, -⟩ :=
      h.isLcPair.1.isPair.existsUnique_isCrepantBoundary h.isLcPair.1.2.1 (v ≫ q) hVXi hvq'
    obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (q ≫ sXi) hWXi
      (by
        haveI := hXin.1
        haveI := hWXi.1
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sXi (q ≫ sXi) hq,
          h.dim_eq]
        rfl)
    have hKWp : KW.IsCanonicalDivisor (p ≫ sX) 3 := by rw [hsW]; exact hKW
    have hVW : IsCrepantBoundary (q ≫ sXi) 3 KW ΔW v hVXq hv ΔV :=
      (isCrepantBoundary_comp_iff h.isLcPair.1.isPair h.isLcPair.1.2.1 hWXi hq hcXi hKW hVXq hv
        rfl hVXi hvq' ΔV).mp hΔV
    have hVW' : IsCrepantBoundary (p ≫ sX) 3 KW ΔW v hVXp hv ΔV :=
      (isCrepantBoundary_congr hsW hVXp hVXq hv ΔV).mpr hVW
    have hab : (v ≫ q) ≫ fi = w ≫ fp := by rw [Category.assoc]; exact hvw
    refine ⟨V, v ≫ p, w, ΔV, hVX, hVY, hvp', hw, hvp.comp hpP, hwp, ?_,
      (isCrepantBoundary_comp_iff hXB.isPair hXB.2.1 hWX hp hcX hKWp hVXp hv rfl hVX hvp'
        ΔV).mpr hVW', fun F => (hcrep hVXi hVY hvq' hw hab F _).mp (hΔV F)⟩
    calc (v ≫ p) ≫ f = (v ≫ q ≫ fi) ≫ hi := by
          rw [Category.assoc, hpq, ← hgi]; simp only [Category.assoc]
      _ = w ≫ gj := by rw [hvw, Category.assoc, hgj]

/-- **No Mori fibre space endpoint.** A floor-lowered model has no fibre-type contraction over
`Z` of a `(K' + B' - t₀⌊B'⌋)`-negative extremal ray of `NE̅(X'/Z)`. The ray is `(K' + B')`-null by
the length argument of `IsFloorLoweredModel.step`, so `⌊B'⌋` is positive on it. If `dim Z = 3`
the base `T` of the contraction would have dimension `< 3` and dominate `Z`. If `dim Z = 2`, `T`
is a surface generically finite over `Z` and a general fibre curve of `X' ⟶ T` lies over a
general point of `Z`, where the vertical floor `⌊B'⌋` is absent, so `⌊B'⌋` is zero on it. -/
private theorem IsFloorLoweredModel.false_of_isFibreType {X Z X' T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Z] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X']
    [CompactSpace X'] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    {K : Divisor X} {B : QDivisor X} {m : ℕ} {t₀ : ℚ} {sX' : X' ⟶ Spec (.of ℂ)}
    [QuasiCompact sX'] {g' : X' ⟶ Z} {K' : Divisor X'} {B' : QDivisor X'}
    (h : IsFloorLoweredModel sX sZ f K B m t₀ sX' g' K' B')
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hm : 0 < m) (ht₀ : 0 < t₀)
    (ht₀m : t₀ * (6 * m + 1) < 1) (hdimZ : topologicalKrullDim Z = 3 ∨ topologicalKrullDim Z = 2)
    {sT : T ⟶ Spec (.of ℂ)} {R : Set (RelativeNumericalCurveClasses sX' g')} {g : X' ⟶ T}
    {gT : T ⟶ Z}
    (hc : IsNegativeRelativeRayContraction sX' g' sT
      (Divisor.toQDivisor K' + (B' - t₀ • Divisor.toQDivisor B'.roundDown)) R g gT)
    (hdim : topologicalKrullDim T < topologicalKrullDim X') : False := by
  obtain ⟨hR, hRC, hNEC⟩ := hc
  have hgT : g ≫ gT = g' := hRC.comp_eq
  haveI : IsProper gT := isProper_of_isProjectiveMorphism gT hRC.isProjectiveMorphism
  have hsurjT : Function.Surjective gT := fun z => by
    obtain ⟨x, hx⟩ := h.isContraction.surjective z
    exact ⟨g x, by rw [← hx, ← Scheme.Hom.comp_apply, hgT]⟩
  have hdimZT := Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
    gT gT.continuous hsurjT (Or.inl gT.isClosedMap.specializingMap)
  rw [h.dim_eq] at hdim
  rcases hdimZ with h3 | h2
  · -- `T` dominates the threefold base `Z`
    rw [h3] at hdimZT
    exact absurd (lt_of_le_of_lt hdimZT hdim) (lt_irrefl _)
  · -- `dim T = 2`, and a general fibre of `g` misses the vertical floor
    obtain ⟨hvert, -⟩ := h.generic h2
    have hTn : IsNormalVariety ℂ sT := hNEC.isNormalVariety_target
    haveI : IsIntegral T := hTn.1.toIsIntegral
    haveI : IsSeparated sT := hTn.1.toIsSeparated
    haveI : LocallyOfFiniteType sT := hTn.1.toLocallyOfFiniteType
    haveI : QuasiCompact sT := hTn.1.toQuasiCompact
    haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
    haveI : IsProper g := hNEC.isContraction.isProper
    haveI : Surjective g := Scheme.Hom.surjective_of_isIso_app g hNEC.isContraction.isIso_app
    haveI : IsSeparated sX' := h.isProjectiveVariety.toIsVariety.toIsSeparated
    haveI : LocallyOfFiniteType sX' := h.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
    have hcomp : g ≫ sT = sX' := hNEC.isContraction.comp_eq
    -- `dim T = 2 = dim X' - 1`
    have hdT : topologicalKrullDim T = 2 := by
      rw [h2] at hdimZT
      have hne : topologicalKrullDim T ≠ ⊤ := ne_top_of_lt hdim
      have hnb : topologicalKrullDim T ≠ ⊥ := ne_bot_of_le_ne_bot (by decide) hdimZT
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hnb
      have hd' : d ≠ ⊤ := fun h' => hne (by rw [← hd, h']; rfl)
      obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hd'
      rw [← hd] at hdimZT hdim ⊢
      have h1 : (2 : ℕ∞) ≤ (n : ℕ∞) := WithBot.coe_le_coe.mp hdimZT
      have h3 : (n : ℕ∞) < 3 := WithBot.coe_lt_coe.mp hdim
      have h1' : 2 ≤ n := by exact_mod_cast h1
      have h3' : n < 3 := by exact_mod_cast h3
      have : n = 2 := by omega
      subst this
      rfl
    have hdimg : topologicalKrullDim X' = topologicalKrullDim T + 1 := by
      rw [h.dim_eq, hdT]; rfl
    have hTq := isQCartier_roundDown h.isQFactorial B'
    obtain ⟨U, hUd, hU⟩ :=
      MMP.Flips.exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber sX' sT g hcomp
        hdimg (Divisor.toQDivisor B'.roundDown) hTq
    obtain ⟨w, hwU, hwcl⟩ := nonempty_inter_closedPoints hUd.nonempty U.isOpen.isLocallyClosed
    obtain ⟨S, hS, hdeg⟩ := (hU w hwU).2 hwcl
    -- the floor is vertical over `T`, so its degree on the generic fibre of `g` vanishes
    have hgen : gT (genericPoint T) = genericPoint Z := by
      haveI : IsDominant gT := ⟨hsurjT.denseRange⟩
      exact map_genericPoint_of_isDominant gT
    have hdeg0 : MMP.Flips.genericFiberDegree g (Divisor.toQDivisor B'.roundDown) = 0 := by
      refine Finset.sum_eq_zero fun E hE => ?_
      have hE' : B'.roundDown.coeff E ≠ 0 := by
        have := Finsupp.mem_support_iff.mp hE
        intro h0
        apply this
        change (Divisor.toQDivisor B'.roundDown).coeff E = 0
        rw [Divisor.coeff_toQDivisor, h0, Int.cast_zero]
      have hgE : g E.genericPoint ≠ genericPoint T := fun hgE => hvert E hE' (by
        rw [← hgT, Scheme.Hom.comp_apply, hgE, hgen])
      rw [MMP.Flips.genericFiberPointDegree, if_neg hgE, Nat.cast_zero, mul_zero]
    -- every fibre curve has positive floor degree
    have hpos : ∀ C ∈ S, 0 < (Divisor.toQDivisor B'.roundDown).intersectionNumber ℂ sX' C.ι
        C.dim_le hTq := by
      intro C hC
      have hCw : g C.point = w := by
        have hmem : C.point ∈ ProperCurve.point '' (S : Set (ProperCurve sX')) := ⟨C, hC, rfl⟩
        rw [hS] at hmem
        exact hmem.1
      have hγ : C.IsContractedBy g := fun x hx => by
        have hx' := image_closure_subset_closure_image g.continuous ⟨x, hx, rfl⟩
        rw [Set.image_singleton, hCw, hwcl.closure_eq] at hx'
        rw [hCw]
        exact hx'
      have hγ' : C.IsContractedBy g' := fun x hx => by
        rw [← hgT, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hγ x hx]
      -- `D' · C = 0`
      have hD0 : (Divisor.toQDivisor K' + B').intersectionNumber ℂ sX' C.ι C.dim_le
          h.isRelativelyNef.1 = 0 := by
        have := h.relativeCurveForm_eq_zero hZ hm ht₀ ht₀m hR _
          ((hRC.isContractedBy_iff C hγ').mp hγ)
        rw [relativeCurveForm_relativeClass] at this
        exact_mod_cast this
      -- `-(D' - t₀⌊B'⌋) · C > 0`
      have hq := hR.1
      have hnq : (-(Divisor.toQDivisor K' +
          (B' - t₀ • Divisor.toQDivisor B'.roundDown))).IsQCartier := by
        have := MMP.Flips.QDivisor.IsQCartier.qsmul hq (-1)
        rwa [neg_one_smul] at this
      have hamp : MMP.Flips.IsRelativelyAmple g (QDivisor.toRDivisor
          (-(Divisor.toQDivisor K' + (B' - t₀ • Divisor.toQDivisor B'.roundDown)))) := by
        rw [map_neg]
        exact hNEC.isRelativelyAntiAmple
      have hpos' := MMP.Flips.intersectionNumber_pos_of_isRelativelyAmple g hnq hamp C hγ
      have hDq := h.isRelativelyNef.1
      have hE1 := MMP.Flips.QDivisor.IsQCartier.qsmul hDq (-1)
      have hE2 := MMP.Flips.QDivisor.IsQCartier.qsmul hTq t₀
      have e : -(Divisor.toQDivisor K' + (B' - t₀ • Divisor.toQDivisor B'.roundDown)) =
          (-1 : ℚ) • (Divisor.toQDivisor K' + B') + t₀ • Divisor.toQDivisor B'.roundDown := by
        module
      rw [intersectionNumber_congr sX' C.ι C.dim_le hnq (hE1.add hE2) e,
        QDivisor.intersectionNumber_add' ℂ sX' C.ι C.dim_le _ _ hE1 hE2,
        intersectionNumber_smul sX' C.ι C.dim_le _ hDq (-1) hE1,
        intersectionNumber_smul sX' C.ι C.dim_le _ hTq t₀ hE2, hD0] at hpos'
      have : 0 < t₀ * (Divisor.toQDivisor B'.roundDown).intersectionNumber ℂ sX' C.ι C.dim_le hTq
        := by linarith
      exact pos_of_mul_pos_right this ht₀.le
    have hS0 : S = ∅ := by
      by_contra hne
      obtain ⟨C, hC⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have := Finset.sum_pos (fun C hC => hpos C hC) ⟨C, hC⟩
      rw [← hdeg, hdeg0] at this
      exact lt_irrefl _ this
    -- but the fibre over `w` has a maximal point
    obtain ⟨x₀, hx₀⟩ := g.surjective w
    obtain ⟨η, hηF, hηmax⟩ := exists_maximal_mem_of_isClosed (hwcl.preimage g.continuous)
      (x₀ := x₀) hx₀
    have hηS : η ∈ ProperCurve.point '' (S : Set (ProperCurve sX')) := by
      rw [hS]
      exact ⟨hηF, fun y hy hyη => hηmax y hy hyη⟩
    rw [hS0] at hηS
    simp at hηS

/-- **The floor-lowering program.** Let `T = ⌊B⌋`, `m(K + B)` Cartier and
`0 < t₀ < 1/(2(6m+1))`. The klt program for `K + B - t₀T` over `Z` is finite by `P₃`, each of
its steps is `(K + B)`-null (ray length, Cartier descent), and it has no Mori fibre space endpoint.
Its endpoint `(X', B')` is crepant birational to `(X, B)` over `Z`, `K' + B'` and
`K' + B' - t₀⌊B'⌋` are nef over `Z`, `(X', B' - t₀⌊B'⌋)` is klt, and, when `dim Z = 2`, the
floor of `B'` is vertical and `K' + B'` is rationally trivial on the generic fibre. -/
private theorem exists_floorLowered_endpoint
    {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B) (hdlt : IsDltPair sX 3 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
        f.base E.genericPoint ≠ genericPoint Z))
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ (t₀ : ℚ) (_ : 0 < t₀) (_ : t₀ ≤ 1) (X' : Scheme.{0}) (_ : IsIntegral X')
      (_ : IsLocallyNoetherian X')
      (_ : IsNormal X') (_ : CompactSpace X') (sX' : X' ⟶ Spec (.of ℂ)) (_ : QuasiCompact sX')
      (g' : X' ⟶ Z) (K' : Divisor X') (B' : QDivisor X'),
      MMP.Mori.IsProjectiveVariety ℂ sX' ∧ topologicalKrullDim X' = 3 ∧ IsQFactorial sX' ∧
      IsContraction sX' sZ g' ∧ 0 ≤ B' ∧ (∀ P, B'.coeff P ≤ 1) ∧ IsLcPair sX' 3 K' B' ∧
      IsKltPair sX' 3 K' (B' - t₀ • Divisor.toQDivisor B'.roundDown) ∧
      (Divisor.toQDivisor K' + B').IsRelativelyNef sX' g' ∧
      (Divisor.toQDivisor K' + B' - t₀ • Divisor.toQDivisor B'.roundDown).IsRelativelyNef sX' g' ∧
      (topologicalKrullDim Z = 2 →
        (∀ E : MMP.Mori.PrimeDivisor X', B'.roundDown.coeff E ≠ 0 →
          g'.base E.genericPoint ≠ genericPoint Z) ∧
        ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X')ˣ, ∀ E : MMP.Mori.PrimeDivisor X',
          g'.base E.genericPoint = genericPoint Z →
            ((m : ℤ) • (Divisor.toQDivisor K' + B') -
              Divisor.toQDivisor (principalDivisor φ)).coeff E = 0) ∧
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ X') (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWX' : IsNormalVariety ℂ (q ≫ sX'))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g' ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧
          IsCrepantBoundary sX' 3 K' B' q hWX' hq ΔW) := by
  classical
  -- the Cartier index `m` of `K + B` and the level `t₀ = 1 / (2(6m + 1))`
  obtain ⟨m, hm, L₀, hL₀, hL₀c⟩ := hdlt.1.2.2.exists_pos
  set t₀ : ℚ := 1 / (2 * (6 * m + 1)) with ht₀def
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have ht₀ : 0 < t₀ := by positivity
  have ht₀1 : t₀ ≤ 1 := by
    rw [ht₀def, div_le_one (by positivity)]
    nlinarith
  have ht₀m : t₀ * (6 * m + 1) < 1 := by
    rw [ht₀def, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨hdlt₀, -⟩ := isDltPair_and_isKltPair_sub_smul_roundDown hQ hdlt ht₀ ht₀1
  have hdltI := (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hdlt.1.2.1 _).mpr hdlt₀
  have hinit := isFloorLoweredModel_self hX hdimX hQ hZ hf hB hdlt hnef hcase hA hAq hDG M hGM
    hL₀ hL₀c ht₀ ht₀1
  -- the klt program for `K + B - t₀⌊B⌋` over `Z`, finite by `P₃`
  obtain ⟨-, -, P, hPproj, hPn, hPend⟩ :=
    projectiveLowerLogMMP_three.2 X Z sX sZ f K (B - t₀ • Divisor.toQDivisor B.roundDown) hX hZ
      hf.comp_eq (by rw [hdimX]; norm_cast) hQ ⟨3, hdlt.1.2.1⟩ hdltI
  -- every model of the program is floor-lowered
  have key : ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ B' : QDivisor (modelSeq X P.Y i),
      divisorSeq (B - t₀ • Divisor.toQDivisor B.roundDown) P.BY i =
        B' - t₀ • Divisor.toQDivisor B'.roundDown ∧
      ∃ _ : QuasiCompact (modelStr sX P.sY i),
        IsFloorLoweredModel sX sZ f K B m t₀ (modelStr sX P.sY i) (modelMap f P.πY i)
          (divisorSeq K P.KY i) B' := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨B, rfl, inferInstance, hinit⟩
    | succ i ih =>
      intro hi
      have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
      obtain ⟨B', hB', _, hinv⟩ := ih hi'.le
      have hstep := P.isElementaryDltStep i hi'
      rw [hB'] at hstep
      have hmod := P.isRelativeDltModel (i + 1) hi
      have hBY := P.BY_eq i hi'
      rw [hB'] at hBY
      haveI : QuasiCompact (P.sY i) := hmod.isQuasiProjectiveVariety.toQuasiCompact
      have hmod' : IsRelativeDltModel (P.sY i) sZ (P.πY i) (P.KY i)
          (MMP.Mori.RationalMap.transformDivisor (P.φ i)
            (B' - t₀ • Divisor.toQDivisor B'.roundDown)) := by
        rw [← hBY]; exact hmod
      obtain ⟨hinv', htr⟩ :=
        hinv.step hdlt.1 hf.comp_eq hZ hm ht₀ ht₀m hstep hmod' (hPproj.2 (i + 1) hi)
      exact ⟨MMP.Mori.RationalMap.transformDivisor (P.φ i) B', hBY.trans htr, inferInstance,
        hinv'⟩
  -- the endpoint
  obtain ⟨B', hB', _, hinv⟩ := key P.n.toNat (ENat.coe_toNat_le_self _)
  have hnotFinal : ¬ P.hasFinal := by
    intro hfin
    obtain ⟨-, hctr, hlt⟩ := P.final_spec hfin
    rw [hB'] at hctr
    refine hinv.false_of_isFibreType hZ hm ht₀ ht₀m (hcase.imp id fun h => h.1) hctr hlt
  have hnef₀ := hPend.resolve_right hnotFinal
  rw [hB'] at hnef₀
  refine ⟨t₀, ht₀, ht₀1, modelSeq X P.Y P.n.toNat, inferInstance, inferInstance, inferInstance,
    inferInstance, modelStr sX P.sY P.n.toNat, inferInstance, modelMap f P.πY P.n.toNat,
    divisorSeq K P.KY P.n.toNat, B', hinv.isProjectiveVariety, hinv.dim_eq, hinv.isQFactorial,
    hinv.isContraction, hinv.nonneg, hinv.coeff_le_one, hinv.isLcPair, hinv.isKltPair,
    hinv.isRelativelyNef, ?_, hinv.generic, hinv.commonModel⟩
  rw [add_sub_assoc]
  exact MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor hinv.isKltPair.1.2.2 hnef₀

/-- **Lowering the floor of an lc boundary keeps the pair klt.** If `(X, B)` is lc with `B ≥ 0`
and `(X, B - t₀⌊B⌋)` is klt for some `t₀ > 0`, then `(X, B - t⌊B⌋)` is klt for every
`0 < t ≤ t₀`: the discrepancies are affine in the boundary, so
`a(E, B - t⌊B⌋) = (1 - s) a(E, B) + s a(E, B - t₀⌊B⌋)` with `s = t / t₀`. -/
private theorem isKltPair_sub_smul_roundDown {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hB : 0 ≤ B) (hB1 : ∀ P, B.coeff P ≤ 1) (hlc : IsLcPair sX 3 K B)
    {t₀ : ℚ} (ht₀ : 0 < t₀)
    (hklt : IsKltPair sX 3 K (B - t₀ • Divisor.toQDivisor B.roundDown)) {t : ℚ} (ht : 0 < t)
    (htt : t ≤ t₀) : IsKltPair sX 3 K (B - t • Divisor.toQDivisor B.roundDown) := by
  have hQ₀ : (Divisor.toQDivisor K + B).IsQCartier := hlc.1.2.2
  have hQ₁ : (Divisor.toQDivisor K + (B - t₀ • Divisor.toQDivisor B.roundDown)).IsQCartier :=
    hklt.1.2.2
  have hΔ'q : (t₀ • Divisor.toQDivisor B.roundDown).IsQCartier := by
    have := hQ₀.add (MMP.Flips.QDivisor.IsQCartier.qsmul hQ₁ (-1))
    convert this using 1
    module
  have hut : (1 - t / t₀) * t₀ = t₀ - t := by field_simp
  have hBt : B - t • Divisor.toQDivisor B.roundDown = (B - t₀ • Divisor.toQDivisor B.roundDown) +
      (1 - t / t₀) • (t₀ • Divisor.toQDivisor B.roundDown) := by
    rw [smul_smul, hut]; module
  have hBone : B = (B - t₀ • Divisor.toQDivisor B.roundDown) +
      (1 : ℚ) • (t₀ • Divisor.toQDivisor B.roundDown) := by module
  have hs : 0 < t / t₀ := div_pos ht ht₀
  have hs1 : t / t₀ ≤ 1 := (div_le_one ht₀).mpr htt
  refine ⟨⟨hlc.1.1, hlc.1.2.1, ?_⟩, ?_, ?_⟩
  · have := hQ₁.add (MMP.Flips.QDivisor.IsQCartier.qsmul hΔ'q (1 - t / t₀))
    rw [hBt, ← add_assoc]
    exact this
  · obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.mp hklt.2.1
    have hq1' : (-1 : ℚ) < q := by
      have h' : ((-1 : ℝ) : EReal) < ((q : ℝ) : EReal) := by
        rw [EReal.coe_neg, EReal.coe_one]; exact hq1
      exact_mod_cast EReal.coe_lt_coe_iff.mp h'
    refine lt_of_lt_of_le (b := (((-1 + t / t₀ * (q + 1) : ℚ) : ℝ) : EReal)) ?_ ?_
    · have : (-1 : ℚ) < -1 + t / t₀ * (q + 1) := by nlinarith
      rw [← EReal.coe_one, ← EReal.coe_neg]
      exact EReal.coe_lt_coe_iff.mpr (by exact_mod_cast this)
    · rw [le_discrep_iff]
      intro E a hE ha
      obtain ⟨-, hBE, hiff⟩ := hklt.1.isDiscrepancy_add_smul_iff hΔ'q E
      haveI := E.isIntegral
      haveI := E.isLocallyNoetherian
      haveI := E.isNormal
      haveI : CompactSpace E.Y := by
        haveI := E.isNormalVariety.1.toQuasiCompact
        exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
      obtain ⟨B', hB', -⟩ := hΔ'q.existsUnique_isPullback hBE
      obtain ⟨-, hiff⟩ := hiff B' hB'
      have ha₁ : IsDiscrepancy sX 3 K (B - t₀ • Divisor.toQDivisor B.roundDown) E
          (a + (1 - t / t₀) * B'.coeff E.E) := by
        refine (hiff (1 - t / t₀) _).mp ?_
        have e : a + (1 - t / t₀) * B'.coeff E.E - (1 - t / t₀) * B'.coeff E.E = a := by ring
        rw [e, ← hBt]
        exact ha
      have ha₀ : IsDiscrepancy sX 3 K B E
          (a + (1 - t / t₀) * B'.coeff E.E - 1 * B'.coeff E.E) := by
        conv => enter [4]; rw [hBone]
        exact (hiff 1 _).mpr ha₁
      have h₁ : ((q : ℝ) : EReal) < (((a + (1 - t / t₀) * B'.coeff E.E : ℚ) : ℝ) : EReal) :=
        lt_of_lt_of_le hq2 (discrep_le hE ha₁)
      have h₀ : ((-1 : ℝ) : EReal) ≤
          (((a + (1 - t / t₀) * B'.coeff E.E - 1 * B'.coeff E.E : ℚ) : ℝ) : EReal) := by
        rw [EReal.coe_neg, EReal.coe_one]
        exact le_trans hlc.2 (discrep_le hE ha₀)
      have h₁' : q < a + (1 - t / t₀) * B'.coeff E.E := by
        exact_mod_cast EReal.coe_lt_coe_iff.mp h₁
      have h₀' : -1 ≤ a + (1 - t / t₀) * B'.coeff E.E - 1 * B'.coeff E.E := by
        exact_mod_cast EReal.coe_le_coe_iff.mp h₀
      have : -1 + t / t₀ * (q + 1) ≤ a := by
        nlinarith [mul_pos hs (sub_pos.mpr h₁'),
          mul_nonneg (sub_nonneg.mpr hs1) (by linarith : (0 : ℚ) ≤
            a + (1 - t / t₀) * B'.coeff E.E - 1 * B'.coeff E.E + 1)]
      exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast this)
  · exact roundDown_nonpos_iff.mpr fun P => coeff_sub_smul_roundDown_lt_one
      (by simpa [DivisorWithCoeffs.coeff_apply] using hB P) (hB1 P) ht

/-- **Relative nefness is convex.** A combination `a D₀ + b D₁`, `a, b ≥ 0`, of `f`-nef
`ℚ`-Cartier `ℚ`-divisors is `f`-nef. -/
private theorem isRelativelyNef_smul_add_smul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {f : X ⟶ Y} {D₀ D₁ : QDivisor X}
    (h₀ : D₀.IsRelativelyNef sX f) (h₁ : D₁.IsRelativelyNef sX f) {a b : ℚ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : (a • D₀ + b • D₁).IsRelativelyNef sX f := by
  have hq₀ := h₀.1
  have hq₁ := h₁.1
  have ha₀ := MMP.Flips.QDivisor.IsQCartier.qsmul hq₀ a
  have hb₁ := MMP.Flips.QDivisor.IsQCartier.qsmul hq₁ b
  have hq := ha₀.add hb₁
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le _ _ ha₀ hb₁,
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le D₀ hq₀ a,
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le D₁ hq₁ b]
  have e₀ := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX h₀ hq₀ C hC
  have e₁ := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX h₁ hq₁ C hC
  positivity

/-- **A contraction onto a base of the same dimension is birational onto its image.** -/
private theorem isBirationalMorphism_toImage_of_isContraction {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    (hdim : topologicalKrullDim X = topologicalKrullDim Z) : IsBirationalMorphism f.toImage := by
  haveI : IsIntegral Z := hf.isNormalVariety_target.1.toIsIntegral
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sZ) := hf.comp_eq ▸ (inferInstance : LocallyOfFiniteType sX)
    exact locallyOfFiniteType_of_comp f sZ
  haveI : QuasiCompact f := by
    have : QuasiCompact (f ≫ sZ) := hf.comp_eq ▸ (inferInstance : QuasiCompact sX)
    haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
    exact QuasiCompact.of_comp f sZ
  exact MMP.Fourfold.isBirationalMorphism_toImage f
    (hf.isBirationalMorphism_of_topologicalKrullDim_eq hdim)

/-- **Semiampleness of the lowered adjoints on the endpoint.** On the endpoint of the
floor-lowering program, `K' + B' - t⌊B'⌋` is semiample over `Z` for every rational
`0 < t ≤ t₀`: the pair `(X', B' - t⌊B'⌋)` is klt and its adjoint is nef by convexity, so
big-core freeness over the birational base (`dim Z = 3`) or relative klt log-elliptic abundance
(`dim Z = 2`, with the generic fibre adjoint rationally trivial) applies. -/
private theorem isRelativelySemiample_sub_smul_roundDown_of_floorLowered
    {X' Z : Scheme.{0}} [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [IsIntegral Z] {sX' : X' ⟶ Spec (.of ℂ)} [QuasiCompact sX'] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hdim : topologicalKrullDim X' = 3)
    (hQ : IsQFactorial sX') (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {g' : X' ⟶ Z} (hg : IsContraction sX' sZ g') {K' : Divisor X'} {B' : QDivisor X'}
    (hB : 0 ≤ B') (hB1 : ∀ P, B'.coeff P ≤ 1) (hlc : IsLcPair sX' 3 K' B') {t₀ : ℚ}
    (ht₀ : 0 < t₀) (ht₀1 : t₀ ≤ 1)
    (hklt : IsKltPair sX' 3 K' (B' - t₀ • Divisor.toQDivisor B'.roundDown))
    (hnef : (Divisor.toQDivisor K' + B').IsRelativelyNef sX' g')
    (hnef₀ : (Divisor.toQDivisor K' + B' - t₀ • Divisor.toQDivisor B'.roundDown).IsRelativelyNef
      sX' g')
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X')ˣ, ∀ E : MMP.Mori.PrimeDivisor X',
        g'.base E.genericPoint = genericPoint Z →
          ((m : ℤ) • (Divisor.toQDivisor K' + B') -
            Divisor.toQDivisor (principalDivisor φ)).coeff E = 0 ∧ B'.roundDown.coeff E = 0)) :
    ∀ t : ℚ, 0 < t → t ≤ t₀ → QDivisor.IsRelativelySemiample g'
      (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor B'.roundDown) := by
  intro t ht htt
  have hklt_t := isKltPair_sub_smul_roundDown hB hB1 hlc ht₀ hklt ht htt
  have hs : 0 ≤ t / t₀ := (div_pos ht ht₀).le
  have hs1 : t / t₀ ≤ 1 := (div_le_one ht₀).mpr htt
  have hnef_t : (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor B'.roundDown).IsRelativelyNef
      sX' g' := by
    have := isRelativelyNef_smul_add_smul sX' hnef hnef₀ (sub_nonneg.mpr hs1) hs
    convert this using 1
    rw [smul_sub (t / t₀), smul_smul, div_mul_cancel₀ _ ht₀.ne']
    module
  have hBt : 0 ≤ B' - t • Divisor.toQDivisor B'.roundDown := fun P =>
    coeff_sub_smul_roundDown_nonneg (by simpa [DivisorWithCoeffs.coeff_apply] using hB P) (hB1 P)
      (htt.trans ht₀1)
  rcases hcase with h3 | ⟨h2, m, hm, φ, hφ⟩
  · -- `dim Z = 3`: `g'` is birational, so every `ℚ`-Cartier divisor is `g'`-big, and the
    -- relative basepoint-free theorem applies to `L = m(K' + B' - t⌊B'⌋)` with `a = 2 / m`.
    have hbir := isBirationalMorphism_toImage_of_isContraction hX' hZ hg (hdim.trans h3.symm)
    have hq := hnef_t.1
    obtain ⟨m, hm, L, hL, hLc⟩ := hq.exists_pos
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hsetting : IsProjectiveSetting ℂ sX' sZ g' :=
      ⟨inferInstance, inferInstance, hX', hZ, hg.comp_eq⟩
    have hLnef : (Divisor.toQDivisor L).IsRelativelyNef sX' g' := by
      have := isRelativelyNef_smul_add_smul sX' hnef_t hnef_t (Nat.cast_nonneg (α := ℚ) m) le_rfl
      rw [hL, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ]
      simpa using this
    have heq : (2 / (m : ℚ)) • Divisor.toQDivisor L - Divisor.toQDivisor K' -
        (B' - t • Divisor.toQDivisor B'.roundDown) =
        Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor B'.roundDown := by
      rw [hL, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, div_mul_cancel₀ _ hm']
      module
    have hbig : (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor B'.roundDown).IsRelativelyBig
        g' := QDivisor.isRelativelyBig_of_isBirationalMorphism_toImage hX' hZ hg.comp_eq hbir hq
    have ha : (0 : ℚ) < 2 / m := by positivity
    rw [← heq] at hbig hnef_t
    obtain ⟨b₀, hb₀⟩ := exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair hsetting hklt_t hBt
      hLc hLnef ha hnef_t hbig
    exact (MMP.Fourfold.QDivisor.isRelativelySemiample_iff_exists_isRelativelyFreeDivisor g' hm hL
      hLc).mpr
      ⟨b₀ + 1, by omega, hb₀ _ (by omega)⟩
  · -- `dim Z = 2`: the generic fibre adjoint of `K' + B' - t⌊B'⌋` is still rationally trivial,
    -- since `⌊B'⌋` has no horizontal component; relative klt log elliptic abundance applies.
    rw [add_sub_assoc]
    refine isRelativelySemiample_of_isKltPair_of_isRelativelyNef hX' hdim hQ hZ h2 hg hklt_t hBt
      (by rw [← add_sub_assoc]; exact hnef_t) ⟨m, hm, φ, fun E hE => ?_⟩
    obtain ⟨h1, h2⟩ := hφ E hE
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, smul_eq_mul, zsmul_eq_mul,
      Int.cast_natCast] at h1 ⊢
    rw [h2, Int.cast_zero, mul_zero, sub_zero]
    exact h1

/-- Relative semiampleness of the adjoint is a crepant birational invariant over `Z`: if the
threefold pairs `(X, B)` and `(Y, B_Y)` have a common normal model `W`, projective and birational
over both, on which a single `Δ_W` is the crepant boundary of both pairs, then `K_Y + B_Y` is
semiample over `Z` if and only if `K_X + B` is. -/
private theorem isRelativelySemiample_iff_of_isCrepantBoundary
    {X Y Z W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    {f : X ⟶ Z} {g : Y ⟶ Z} (hf : f ≫ sZ = sX) (hg : g ≫ sZ = sY)
    {K : Divisor X} {B : QDivisor X} (hXB : IsPairWith sX 3 K B)
    {KY : Divisor Y} {BY : QDivisor Y} (hYB : IsPairWith sY 3 KY BY)
    (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
    (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    (hpp : IsProjectiveMorphism p) (hqp : IsProjectiveMorphism q) (hpq : p ≫ f = q ≫ g)
    (hcX : IsCrepantBoundary sX 3 K B p hWX hp ΔW)
    (hcY : IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) :
    QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY) ↔
      QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  haveI := hWX.1
  haveI : IsNormal W := hWX.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWX.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := by
    haveI := hWX.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : CompactSpace Y := by
    haveI := hYB.1.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sY
  haveI := isProper_of_isProjectiveMorphism p hpp
  haveI := isProper_of_isProjectiveMorphism q hqp
  have hs : q ≫ sY = p ≫ sX := by
    rw [← hf, ← hg, ← Category.assoc, ← Category.assoc, hpq]
  obtain ⟨m₁, hm₁, τ₁, hτ₁, L₁, hL₁c, hL₁, hiffX⟩ :=
    exists_isRelativelyFreeDivisor_iff_of_isCrepantBoundary hXB p hWX hp hcX f (p ≫ sX) rfl
  obtain ⟨m₂, hm₂, τ₂, hτ₂, L₂, hL₂c, hL₂, hiffY⟩ :=
    exists_isRelativelyFreeDivisor_iff_of_isCrepantBoundary hYB q hWY hq hcY g (p ≫ sX) hs
  rw [hiffX, hiffY, ← hpq]
  have hn : topologicalKrullDim W = (3 : ℕ) := by
    haveI := hXB.1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp,
      hXB.2.1.topologicalKrullDim_eq]
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm hWX hn hτ₁ hτ₂
  have hcoeff : ∀ F : MMP.Mori.PrimeDivisor W,
      ((m₂ : ℤ) * L₁.coeff F : ℚ) = (m₁ : ℤ) * L₂.coeff F + (m₁ * m₂ : ℕ) * F.ord φ := by
    intro F
    have a₁ := congrArg (fun D : QDivisor W => D.coeff F) hL₁
    have a₂ := congrArg (fun D : QDivisor W => D.coeff F) hL₂
    have e := congrArg (fun D : Divisor W => D.coeff F) hφ
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toQDivisor, smul_eq_mul, zsmul_eq_mul, Int.cast_natCast] at a₁ a₂
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at e
    have e' : ((MMP.Mori.divisorOfForm τ₁).coeff F : ℚ) - (MMP.Mori.divisorOfForm τ₂).coeff F =
        F.ord φ := by exact_mod_cast e
    push_cast
    linear_combination (m₂ : ℚ) * a₁ - (m₁ : ℚ) * a₂ + (m₁ : ℚ) * m₂ * e'
  have e₁₂ : (m₂ : ℤ) • L₁ = (m₁ : ℤ) • L₂ + principalDivisor (φ ^ (m₁ * m₂)) := by
    ext F
    have := hcoeff F
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      PrimeDivisor.ord_pow, smul_eq_mul, nsmul_eq_mul]
    exact_mod_cast this
  have e₂₁ : (m₁ : ℤ) • L₂ = (m₂ : ℤ) • L₁ + principalDivisor (φ⁻¹ ^ (m₁ * m₂)) := by
    ext F
    have := hcoeff F
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      PrimeDivisor.ord_pow, PrimeDivisor.ord_inv, smul_eq_mul, nsmul_eq_mul]
    have h' : ((m₁ : ℤ) * L₂.coeff F : ℚ) =
        (m₂ : ℤ) * L₁.coeff F + (m₁ * m₂ : ℕ) * -F.ord φ := by linarith
    exact_mod_cast h'
  exact ⟨exists_isRelativelyFreeDivisor_of_smul_eq_add (p ≫ f) hL₂c hm₂ _ e₂₁,
    exists_isRelativelyFreeDivisor_of_smul_eq_add (p ≫ f) hL₁c hm₁ _ e₁₂⟩

/-- The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {B : QDivisor X} (hB0 : 0 ≤ B) (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp}
    {B' : QDivisor Y} (h : B.IsPullback f hB B') : 0 ≤ B' := by
  obtain ⟨D, D', hDc, hDB, hD, hD', hp⟩ := h.exists_cartierIndex hBq
  have hm : (0 : ℚ) < (B.cartierIndex hBq : ℕ) := by exact_mod_cast QDivisor.cartierIndex_pos hBq
  intro F
  change 0 ≤ B'.coeff F
  have hDF : ∀ G : MMP.Mori.PrimeDivisor Y,
      (D'.coeff G : ℚ) = (B.cartierIndex hBq : ℕ) * B'.coeff G :=
    fun G => by
      have := congrArg (fun E : QDivisor Y => E.coeff G) hD'
      simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using this
  have hDP : ∀ G : MMP.Mori.PrimeDivisor X,
      (D.coeff G : ℚ) = (B.cartierIndex hBq : ℕ) * B.coeff G :=
    fun G => by
      have := congrArg (fun E : QDivisor X => E.coeff G) hD
      simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] using this
  have hnn := coeff_nonneg_of_isPullback_of_isEffectiveOn hDc (V := ⊤)
    (fun G _ => by
      have : (0 : ℚ) ≤ D.coeff G := by
        rw [hDP]
        exact mul_nonneg hm.le (by simpa [DivisorWithCoeffs.coeff_apply] using hB0 G)
      exact_mod_cast this) hp F
    ⟨F.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have : (0 : ℚ) ≤ (B.cartierIndex hBq : ℕ) * B'.coeff F := by rw [← hDF]; exact_mod_cast hnn
  by_contra hneg
  push Not at hneg
  linarith [mul_neg_of_pos_of_neg hm hneg]

/-- **The crepant dlt modification of the endpoint.** Let `(X', B')` be a projective lc
threefold pair, crepant birational to `(X, B)` over `Z`, with `(X', B' - t₀⌊B'⌋)` klt and
`K' + B' - t⌊B'⌋` semiample over `Z` for all `0 < t ≤ t₀`. A projective crepant dlt modification
`e : Y ⟶ X'` with `P = e^*⌊B'⌋` is the asserted model: every exceptional prime of `e` is a zero
place, so `0 < a(F, X', B' - t₀⌊B'⌋) = t₀ ord_F(P)`, and `Supp P = ⌊B_Y⌋`. -/
private theorem exists_pencil_model_of_floorLowered
    {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [QuasiCompact sX'] {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {K : Divisor X} {B : QDivisor X} (hXB : IsPairWith sX 3 K B)
    (hfZ : f ≫ sZ = sX)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hdim : topologicalKrullDim X' = 3)
    (hQ : IsQFactorial sX') {g' : X' ⟶ Z} (hg : IsContraction sX' sZ g')
    {K' : Divisor X'} {B' : QDivisor X'} (hB : 0 ≤ B') (hB1 : ∀ P, B'.coeff P ≤ 1)
    (hlc : IsLcPair sX' 3 K' B')
    {t₀ : ℚ} (ht₀ : 0 < t₀)
    (hklt : IsKltPair sX' 3 K' (B' - t₀ • Divisor.toQDivisor B'.roundDown))
    (hsa : ∀ t : ℚ, 0 < t → t ≤ t₀ → QDivisor.IsRelativelySemiample g'
      (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor B'.roundDown))
    (hW :
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ X') (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWX' : IsNormalVariety ℂ (q ≫ sX'))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g' ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧
          IsCrepantBoundary sX' 3 K' B' q hWX' hq ΔW)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z) (KY : Divisor Y) (BY : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ g ≫ sZ = sY ∧ IsDltPair sY 3 KY BY ∧
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) ∧
      (∃ P : QDivisor Y, 0 ≤ P ∧ P.IsQCartier ∧
        (∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0) ∧
        ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ ≤ δ₀ →
          QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY - δ • P)) := by
  obtain ⟨W, p, q, ΔW, hWX, hWX', hp, hq, hpp, hqp, hpq, hcX, hcX'⟩ := hW
  haveI : IsIntegral W := hWX.1.toIsIntegral
  haveI : IsNormal W := hWX.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWX.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := by
    haveI := hWX.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have hsW : p ≫ sX = q ≫ sX' := by
    rw [← hfZ, ← hg.comp_eq, ← Category.assoc, hpq, Category.assoc]
  have hK' := hlc.1.2.1
  -- the floor `T' = ⌊B'⌋` is `ℚ`-Cartier and effective
  have hT := isQCartier_roundDown hQ B'
  have hb0 : ∀ P, 0 ≤ B'.coeff P := fun P => by simpa [DivisorWithCoeffs.coeff_apply] using hB P
  -- the crepant dlt modification `e : Y ⟶ X'` of `(X', B')`
  obtain ⟨Y, _, _, _, e, he, hYQ, BY, hep, hdltI, hcrepAll, hexc⟩ :=
    projectiveFloorProgramInputs_three.exists_crepant_dltModification sX' hX'
      (by rw [hdim]; norm_cast) (MMP.Threefold.Bridges.isLogCanonicalPair_of_isLcPair hlc hb0 hB1)
  have hYv : IsNormalVariety ℂ (e ≫ sX') := hYQ.1
  haveI : CompactSpace Y := by
    haveI := hYv.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (e ≫ sX')
  haveI : LocallyOfFiniteType (e ≫ sX') := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hlc.1.1.1.toLocallyOfFiniteType
  haveI : IsProper e := isProper_of_isProjectiveMorphism e hep
  have hYproj : MMP.Mori.IsProjectiveVariety ℂ (e ≫ sX') :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hYv.1, hep.comp hX'.isProjective⟩
  have hdimY : topologicalKrullDim Y = (3 : ℕ) := by
    haveI := hlc.1.1.1
    haveI := hYv.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (e ≫ sX') he, hdim]
    rfl
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (e ≫ sX') hYv hdimY
  have hYdlt : IsDltPair (e ≫ sX') 3 KY BY :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (e ≫ sX') hKY BY).mp hdltI
  have hcY : IsCrepantBoundary sX' 3 K' B' e hYv he BY := hcrepAll K' hK'
  -- `P = e^*T'`
  have hBe : ∀ Z : irreducibleComponents Y,
      e (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor B'.roundDown).supp := fun Z => by
    haveI := he.isDominant
    rw [Divisor.supp_toQDivisor]
    exact map_componentGenericPoint_notMem_supp_of_isDominant e _ Z
  set P := (Divisor.toQDivisor B'.roundDown).pullback hT hBe with hPdef
  have hPb : (Divisor.toQDivisor B'.roundDown).IsPullback e hBe P :=
    QDivisor.isPullback_pullback hT hBe
  have hP0 : 0 ≤ P := nonneg_of_isPullback (fun Q => by
    change 0 ≤ (Divisor.toQDivisor B'.roundDown).coeff Q
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown]
    exact_mod_cast Int.floor_nonneg.mpr (hb0 Q)) hT hPb
  have hPq : P.IsQCartier := hPb.isQCartier hT
  have hshift : ∀ δ : ℚ, IsCrepantBoundary sX' 3 K' (B' - δ • Divisor.toQDivisor B'.roundDown) e
      hYv he (BY - δ • P) := fun δ => isCrepantBoundary_sub_smul hlc.1 hYv he hcY hT hPb δ
  -- the support of `P` is the floor of `B_Y`
  have hsupp : ∀ F : MMP.Mori.PrimeDivisor Y, P.coeff F ≠ 0 ↔ BY.roundDown.coeff F ≠ 0 := by
    intro F
    rw [DivisorWithCoeffs.coeff_roundDown]
    by_cases hF : (⟨Y, e, hYv, he, F⟩ : DivisorOver ℂ sX').IsExceptional
    · have h1 : BY.coeff F = 1 := (hexc F hF).2
      have hlt := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hYv he
        (hshift t₀) F
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul, h1] at hlt
      rw [h1, Int.floor_one]
      refine ⟨fun _ => one_ne_zero, fun _ h0 => ?_⟩
      rw [h0, mul_zero, sub_zero] at hlt
      exact lt_irrefl _ hlt
    · obtain ⟨P₁, hc₁, hη₁, -⟩ :=
        MMP.Mori.exists_coeff_eq_of_not_isExceptional hlc.1 hYv he hcY hF
      obtain ⟨P₂, hc₂, hη₂, -⟩ :=
        MMP.Mori.exists_coeff_eq_of_not_isExceptional hklt.1 hYv he (hshift t₀) hF
      have hP₁₂ : P₁ = P₂ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη₁.symm.trans hη₂)
      subst hP₁₂
      rw [coeff_sub_smul_roundDown, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
        smul_eq_mul, hc₁] at hc₂
      have hPF : P.coeff F = ⌊B'.coeff P₁⌋ := mul_left_cancel₀ ht₀.ne' (by linarith)
      rw [hPF, hc₁]
      exact_mod_cast Iff.rfl
  refine ⟨Y, inferInstance, inferInstance, inferInstance, e ≫ sX', e ≫ g', KY, BY, hYproj,
    by rw [Category.assoc, hg.comp_eq], hYdlt, ?_, P, hP0, hPq, hsupp, t₀, ht₀,
    fun δ hδ hδt => ?_⟩
  · -- a projective common model of `X` and `Y`, through `W` and `Y ⟶ X'`
    obtain ⟨V, v, w, hVv, hv, hw, hvp, hwp, hvw⟩ :=
      exists_isProjectiveVariety_commonModel hX' hWX' hYv hq he hqp hep
    haveI : IsIntegral V := hVv.1.toIsIntegral
    haveI : IsNormal V := hVv.2
    haveI : LocallyOfFiniteType (v ≫ q ≫ sX') := hVv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (v ≫ q ≫ sX')
    have hVX : IsNormalVariety ℂ ((v ≫ p) ≫ sX) := by rw [Category.assoc, hsW]; exact hVv
    have hVXp : IsNormalVariety ℂ (v ≫ p ≫ sX) := by rw [hsW]; exact hVv
    have hVX' : IsNormalVariety ℂ ((v ≫ q) ≫ sX') := by rw [Category.assoc]; exact hVv
    have hVY : IsNormalVariety ℂ (w ≫ e ≫ sX') := by
      rw [← Category.assoc, ← hvw, Category.assoc]; exact hVv
    have hvp' : IsBirationalMorphism (v ≫ p) := isBirationalMorphism_comp hv hp
    have hvq' : IsBirationalMorphism (v ≫ q) := isBirationalMorphism_comp hv hq
    obtain ⟨⟨ΔV, hΔV, -⟩, -⟩ :=
      hlc.1.isPair.existsUnique_isCrepantBoundary hK' (v ≫ q) hVX' hvq'
    obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (q ≫ sX') hWX'
      (by
        haveI := hlc.1.1.1
        haveI := hWX'.1
        rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (q ≫ sX') hq,
          hdim]
        rfl)
    have hKWp : KW.IsCanonicalDivisor (p ≫ sX) 3 := by rw [hsW]; exact hKW
    -- `Δ_V` is crepant for `(W, Δ_W)` (with the structure map `q ≫ s_{X'}`), hence for `(X, B)`
    have hVW : IsCrepantBoundary (q ≫ sX') 3 KW ΔW v hVv hv ΔV :=
      (isCrepantBoundary_comp_iff hlc.1.isPair hK' hWX' hq hcX' hKW hVv hv rfl hVX' hvq' ΔV).mp
        hΔV
    have hVW' : IsCrepantBoundary (p ≫ sX) 3 KW ΔW v hVXp hv ΔV :=
      (isCrepantBoundary_congr hsW hVXp hVv hv ΔV).mpr hVW
    refine ⟨V, v ≫ p, w, ΔV, hVX, hVY, hvp', hw, hvp.comp hpp, hwp, ?_,
      (isCrepantBoundary_comp_iff hXB.isPair hXB.2.1 hWX hp hcX hKWp hVXp hv rfl hVX hvp'
        ΔV).mpr hVW', ?_⟩
    · rw [Category.assoc, hpq, ← Category.assoc, hvw, Category.assoc]
    · exact (isCrepantBoundary_comp_iff hlc.1.isPair hK' hYv he hcY hKY hVY hw hvw.symm hVX'
        hvq' ΔV).mp hΔV
  · -- `K_Y + B_Y - δP` is the crepant pull-back of `K' + B' - δ⌊B'⌋`
    have hpairX := (isKltPair_sub_smul_roundDown hB hB1 hlc ht₀ hklt hδ hδt).1
    have hpairY : IsPairWith (e ≫ sX') 3 KY (BY - δ • P) := by
      refine ⟨hYv, hKY, ?_⟩
      have := hYdlt.1.2.2.add (MMP.Flips.QDivisor.IsQCartier.qsmul hPq (-δ))
      convert this using 1
      module
    have hYid : IsNormalVariety ℂ (𝟙 Y ≫ e ≫ sX') := by rw [Category.id_comp]; exact hYv
    have hid : IsBirationalMorphism (𝟙 Y) := isBirationalMorphism_of_isIso _
    have hiff := isRelativelySemiample_iff_of_isCrepantBoundary hX' hYproj hg.comp_eq
      (by rw [Category.assoc, hg.comp_eq]) hpairX hpairY e (𝟙 Y) (BY - δ • P) hYv hYid he hid
      hep (MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 Y))
      (Category.id_comp _).symm (hshift δ) (isCrepantBoundary_id hpairY.isPair hKY hYid hid)
    rw [add_sub_assoc]
    exact hiff.mpr (by rw [← add_sub_assoc]; exact hsa δ hδ hδt)

/-- The floor-lowering program for `K + B - t₀⌊B⌋` over `Z`, followed by a crepant dlt
modification of its endpoint, gives a crepant birational dlt model with a semiample off-floor
pencil. -/
private theorem exists_pencil_model
    {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B) (hdlt : IsDltPair sX 3 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
        f.base E.genericPoint ≠ genericPoint Z))
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z) (KY : Divisor Y) (BY : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ g ≫ sZ = sY ∧ IsDltPair sY 3 KY BY ∧
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) ∧
      (∃ P : QDivisor Y, 0 ≤ P ∧ P.IsQCartier ∧
        (∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0) ∧
        ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ ≤ δ₀ →
          QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY - δ • P)) := by
  obtain ⟨t₀, ht₀, ht₀1, X', _, _, _, _, sX', _, g', K', B', hX', hdim', hQ', hg', hB', hB1',
      hlc', hklt',
      hnef', hnef₀', hgen', hW⟩ :=
    exists_floorLowered_endpoint hX hdimX hQ hZ hf hB hdlt hnef hcase hA hAq hlc hDG M hGM
  have hcase' : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : (RationalFunctions X')ˣ, ∀ E : MMP.Mori.PrimeDivisor X',
        g'.base E.genericPoint = genericPoint Z →
          ((m : ℤ) • (Divisor.toQDivisor K' + B') -
            Divisor.toQDivisor (principalDivisor φ)).coeff E = 0 ∧ B'.roundDown.coeff E = 0) := by
    rcases hcase with h3 | ⟨h2, -⟩
    · exact Or.inl h3
    · obtain ⟨hvert, m, hm, φ, hφ⟩ := hgen' h2
      exact Or.inr ⟨h2, m, hm, φ, fun E hE =>
        ⟨hφ E hE, by_contra fun h => hvert E h hE⟩⟩
  exact exists_pencil_model_of_floorLowered hdlt.1 hf.comp_eq hX' hdim' hQ' hg' hB' hB1' hlc'
    ht₀ hklt' (isRelativelySemiample_sub_smul_roundDown_of_floorLowered hX' hdim' hQ' hZ hg' hB'
      hB1' hlc' ht₀ ht₀1 hklt' hnef' hnef₀' hcase') hW

private theorem solution
    {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B) (hdlt : IsDltPair sX 3 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
        f.base E.genericPoint ≠ genericPoint Z))
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z) (KY : Divisor Y) (BY : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ g ≫ sZ = sY ∧ IsDltPair sY 3 KY BY ∧
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) ∧
      (∃ P : QDivisor Y, 0 ≤ P ∧ P.IsQCartier ∧
        (∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0) ∧
        ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ ≤ δ₀ →
          QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY - δ • P)) ∧
      (QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY) ↔
        QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B)) ∧
      (BY.roundDown = 0 → QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B)) := by
  obtain ⟨Y, _, _, _, sY, g, KY, BY, hYproj, hgZ, hYdlt, ⟨W, p, q, ΔW, hWX, hWY, hp, hq, hpp,
      hqp, hpq, hcX, hcY⟩, ⟨P, hP0, hPq, hPsupp, δ₀, hδ₀, hsa⟩⟩ :=
    exists_pencil_model hX hdimX hQ hZ hf hB hdlt hnef hcase hA hAq hlc hDG M hGM
  have hiff := isRelativelySemiample_iff_of_isCrepantBoundary hX hYproj hf.comp_eq hgZ hdlt.1
    hYdlt.1 p q ΔW hWX hWY hp hq hpp hqp hpq hcX hcY
  refine ⟨Y, inferInstance, inferInstance, inferInstance, sY, g, KY, BY, hYproj, hgZ, hYdlt,
    ⟨W, p, q, ΔW, hWX, hWY, hp, hq, hpp, hqp, hpq, hcX, hcY⟩, ⟨P, hP0, hPq, hPsupp, δ₀, hδ₀, hsa⟩,
    hiff, fun h0 => hiff.mp ?_⟩
  have hP : P = 0 := by
    ext E
    by_contra hE
    exact (hPsupp E).mp hE (by rw [h0]; rfl)
  simpa [hP] using hsa δ₀ hδ₀ le_rfl

end Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil

end

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.Fourfold

/-- **Complemented dlt threefolds with vertical floor have a semiample off-floor pencil.** Let
`(X, B)` be a dlt pair, `B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor, on a `ℚ`-factorial
normal projective threefold over `ℂ`, and
let `f : X ⟶ Z` be a contraction (`MMP.Fourfold.IsContraction`) onto a projective variety `Z`
with `D = K + B` `f`-nef. Suppose `dim Z = 3`, or `dim Z = 2` and every component of `⌊B⌋` is
vertical over `Z`, and that `A ≥ 0` is `ℚ`-Cartier with `(X, B + A)` lc and `D + A ∼_ℚ f^*H`
(`D + A ∼_ℚ G` with `𝒪_X(mG) ≅ f^* M`, `M` invertible). Then there are a projective dlt pair
`(Y, B_Y)` with canonical divisor `K_Y` and a morphism `g : Y ⟶ Z`, crepant birational to
`(X, B)` over `Z` through a common model `W`, and an effective `ℚ`-Cartier `P` on `Y` with
support `⌊B_Y⌋`, such that `K_Y + B_Y - δ P` is semiample over `Z` for all rational
`0 < δ ≤ δ₀`; `K_Y + B_Y` is semiample over `Z` if and only if `D` is; and if `⌊B_Y⌋ = 0` then
`D` is semiample over `Z`. -/
@[mmp "lem_fourfold_complemented_threefold_vertical_floor_pencil"]
public theorem exists_isRelativelySemiample_sub_smul_of_isDltPair_of_add_qLinearlyEquivalent
    {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : IsContraction sX sZ f)
    {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B) (hdlt : IsDltPair sX 3 K B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
      ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
        f.base E.genericPoint ≠ genericPoint Z))
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z) (KY : Divisor Y) (BY : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ g ≫ sZ = sY ∧ IsDltPair sY 3 KY BY ∧
      (∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) ∧
      (∃ P : QDivisor Y, 0 ≤ P ∧ P.IsQCartier ∧
        (∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0) ∧
        ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ ≤ δ₀ →
          QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY - δ • P)) ∧
      (QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY) ↔
        QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B)) ∧
      (BY.roundDown = 0 → QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B)) :=
        by revert X Z sX sZ hX hdimX hQ hZ f hf K B hB hdlt hnef hcase A hA hAq hlc G hDG M hGM; first | exact Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil.solution | exact Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil.solution _ | exact Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil.solution _ _ | exact Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil.solution _ _ _ | exact Proof_lem_fourfold_complemented_threefold_vertical_floor_pencil.solution _ _ _ _

end MMP.Fourfold

