module
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Sections of the round-up of the test boundary in the non-vanishing theorem

Let `(x, q, e, M; f; F_•; b_•; p_•; r_•)` be an adapted resolution of a smooth non-vanishing
datum `(X, D, G, a)` with a tie-breaker `(j', c)` and test boundary
`A = ∑_{j ≠ j'} (-c r_j + b_j - p_j) F_j`. Identifying `K(Y) = K(X)` through `f^*`, every global
section of `𝒪_Y(m f^*D + ⌈A⌉)` is a global section of `𝒪_X(mD + ⌈G⌉)`, for every integer `m`.

## Main results

* `MMP.Mori.IsNonvanishingTieBreaker.exists_functionFieldMap_eq_roundUp`

## Implementation notes

The integer called `b` in the source is `m` here, since `b` names the discrepancies `b_j`. The
pull-back `f^*D` is any divisor `D'` with `D.IsPullback f hD D'`. The inclusion
`H⁰(Y, m f^*D + ⌈A⌉) ⊆ H⁰(X, mD + ⌈G⌉)` inside `K(Y) = K(X)` is stated as: every section `σ` is
`f^* τ` for a section `τ`, with `f^*` the map of function fields `functionFieldMap f`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5, Step 6
-/

public section

universe u

open AlgebraicGeometry hiding IsVariety PrimeDivisor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.Mori.Divisor

/-- The coefficient of `∑ i, b i • F i` at `F j`, for pairwise distinct prime divisors `F i`,
is `b j`. -/
private lemma coeff_sum_single_of_injective {Y : Scheme.{u}} {ι : Type*} [Fintype ι]
    {F : ι → PrimeDivisor Y} (hF : Function.Injective F) (b : ι → ℚ) (j : ι) :
    (∑ i, Finsupp.single (F i) (b i) : QDivisor Y).coeff (F j) = b j := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      fun i _ hij => Finsupp.single_eq_of_ne' (hF.ne hij), Finsupp.single_eq_same]

/-- **Step 6 of the proof of the non-vanishing theorem.** For an adapted resolution
`(x, q, e, M; f; F_•; b_•; p_•; r_•)` of a smooth non-vanishing datum `(X, D, G, a)` with a
tie-breaker `(j', c)` and test boundary `A = tieBreakerBoundary F r b p j' c`, and every integer
`m`, every global section `σ` of `𝒪_Y(m f^*D + ⌈A⌉)` is, in `K(Y) = K(X)`, a global section of
`𝒪_X(mD + ⌈G⌉)`: `σ = f^* τ`. -/
@[mmp "lem_km3a_nonvanishing_roundup_bound"]
public theorem IsNonvanishingTieBreaker.exists_functionFieldMap_eq_roundUp
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ} {M : QDivisor X}
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {s : ℕ} {F : Fin (s + 1) → PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    {j' : Fin (s + 1)} {c : ℚ}
    (h : IsNonvanishingTieBreaker sX n K D G a x q e M f F b p r j' c)
    (hD : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    {D' : Divisor Y} (hD' : D.IsPullback f hD D') (m : ℤ)
    (σ : (m • D' + (tieBreakerBoundary F r b p j' c).roundUp).divisorialSubmodule ⊤) :
    haveI := h.isLogResolution.isBirationalMorphism.isDominant
    ∃ τ : (m • D + G.roundUp).divisorialSubmodule ⊤,
      functionFieldMap f (rationalFunctionsEquivFunctionField X (sectionToRationalFunctions τ)) =
        rationalFunctionsEquivFunctionField Y (sectionToRationalFunctions σ) := by
  have : IsProper f := h.isLogResolution.isProper
  obtain ⟨hYn, hcb⟩ := h.isCrepantBoundary
  refine exists_functionFieldMap_eq_of_isBirationalMorphism sX f h.isProperVariety.toIsVariety
    hYn.1 h.isLogResolution.isBirationalMorphism _ _ (fun P P' hT => ?_) σ
  obtain ⟨hη, hV⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hT
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hV
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    MMP.Positivity.coeff_eq_of_isPullback P' P hη h.isCartier hD',
    DivisorWithCoeffs.coeff_roundUp, add_le_add_iff_left]
  rcases coeff_tieBreakerBoundary h.injective r b p j' c P' with h0 | ⟨j, -, rfl, hcoeff⟩
  · rw [h0, Int.ceil_zero, ← DivisorWithCoeffs.coeff_roundUp]
    exact (h.isKltPair.neg_one_lt_coeff_and_isEffective_roundUp).2 P
  · have hb := (hcb (F j)).eq_neg_coeff_of_map_genericPoint_eq (P := P) hη
    rw [DivisorWithCoeffs.coeff_neg, neg_neg, DivisorWithCoeffs.coeff_neg, neg_neg,
      coeff_sum_single_of_injective h.injective] at hb
    rw [hcoeff, ← hb]
    refine Int.ceil_mono ?_
    linarith [mul_nonneg h.pos_c.le (h.nonneg_r j), h.pos_p j]

end MMP.Mori

end
