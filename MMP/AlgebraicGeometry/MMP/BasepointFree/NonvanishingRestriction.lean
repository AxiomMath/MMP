module

public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingTestDivisorAmple
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.MMP.BasepointFree.NonvanishingRoundUpSections
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp

@[expose] public section

/-!
# Non-vanishing on the tie-breaking divisor gives non-vanishing on `X`

Let `(x, q, e, M; f; F_0, …, F_s; b_•; p_•; r_•)` be an adapted resolution of a smooth
non-vanishing datum `(X, D, G, a)` with a tie-breaker `(j', c)` and test boundary
`A = ∑_{j ≠ j'} (-c r_j + b_j - p_j) F_j`, and put `F = F_{j'}`. If `b ≥ a + c(q - a)` is an
integer and `H⁰(F, 𝒪_Y(b f^*D + ⌈A⌉)|_F) ≠ 0`, then `H⁰(X, bD + ⌈G⌉) ≠ 0`.

Indeed the test divisor `N(b, c) = b f^*D + A - F - K_Y` is ample, so by the round-up form of
Kawamata–Viehweg vanishing `H¹(Y, 𝒪_Y(K_Y + ⌈N(b, c)⌉)) = 0`, and
`K_Y + ⌈N(b, c)⌉ + F = b f^*D + ⌈A⌉`. Hence the restriction
`H⁰(Y, b f^*D + ⌈A⌉) → H⁰(F, 𝒪_Y(b f^*D + ⌈A⌉)|_F)` is onto, so its source is nonzero, and
`H⁰(Y, b f^*D + ⌈A⌉) ⊆ H⁰(X, bD + ⌈G⌉)` inside the common function field.

## Main results

* `MMP.Mori.IsNonvanishingTieBreaker.exists_ne_zero_divisorialSubmodule_of_nontrivial`:
  non-vanishing of `𝒪_Y(b f^*D + ⌈A⌉)|_{F_{j'}}` gives a nonzero global section of
  `𝒪_X(bD + ⌈G⌉)`.

## Implementation notes

The prime divisor `F_{j'}` is the integral closed subscheme `(F j').idealSheaf.subscheme`, over
`k` through `(F j').idealSheaf.subschemeι ≫ f ≫ sX`, and `𝒪_Y(L)|_F` is the pull-back of
`𝒪_Y(L)` along the closed immersion. The pull-back `f^*D` is any `D'` with
`D.IsPullback f hB D'`. The conclusion `H⁰(X, bD + ⌈G⌉) ≠ 0` is spelled as in
`MMP.Mori.HasNonvanishingProperty`: a nonzero element of the global sections
`(b • D + G.roundUp).divisorialSubmodule ⊤`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 6
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **Non-vanishing reduces to the tie-breaking divisor** (Kollár–Mori 3.5, Step 6). Let
`(x, q, e, M; f; F_•; b_•; p_•; r_•)` be an adapted resolution of a smooth non-vanishing datum
`(X, D, G, a)` with a tie-breaker `(j', c)`, let `A = ∑_{j ≠ j'} (-c r_j + b_j - p_j) F_j` be
the test boundary and `ι` the closed immersion of `F = F_{j'}`. Let `D'` be a pull-back of `D`
along `f` and `β ≥ a + c(q - a)` an integer. If `H⁰(F, ι^* 𝒪_Y(β D' + ⌈A⌉)) ≠ 0`, then
`𝒪_X(βD + ⌈G⌉)` has a nonzero global section. -/
@[mmp "lem_km3a_nonvanishing_restriction_reduces"]
theorem IsNonvanishingTieBreaker.exists_ne_zero_divisorialSubmodule_of_nontrivial
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ} {x : X} {q e : ℤ}
    {M : QDivisor X} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} {s : ℕ} {F : Fin (s + 1) → PrimeDivisor Y} {b p r : Fin (s + 1) → ℚ}
    {j' : Fin (s + 1)} {c : ℚ}
    (h : IsNonvanishingTieBreaker sX n K D G a x q e M f F b p r j' c)
    {β : ℤ} (hβ : a + c * (q - a) ≤ β)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D')
    (hne : Nontrivial (cohomologyOverField k ((F j').idealSheaf.subschemeι ≫ f ≫ sX)
      ((Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj
        (β • D' + (tieBreakerBoundary F r b p j' c).roundUp).divisorialSheaf) 0)) :
    ∃ σ : (β • D + G.roundUp).divisorialSubmodule ⊤, σ ≠ 0 := by
  haveI hP : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety_source
  haveI : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  have hKX : K.IsCanonicalDivisor sX n := h.isKltPair.1.2.1
  have hdim : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans hKX.1
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdim
  set A := tieBreakerBoundary F r b p j' c
  set L : Divisor Y := β • D' - KY - Finsupp.single (F j') 1 with hL
  set N : QDivisor Y := (β : ℚ) • Divisor.toQDivisor D' - Divisor.toQDivisor KY +
    ∑ j, Finsupp.single (F j) (-c * r j + b j - p j) with hNdef
  have hNt : IsTieBreakerTestDivisor sX n D f KY F r b p β c N :=
    ⟨hKY, hB, D', hD', rfl⟩
  have hamp : N.IsAmple :=
    h.toIsNonvanishingAdaptedResolution.isAmple_of_isTieBreakerTestDivisor h.pos_c.le
      (h.lt_half.le) hβ hNt
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple (f ≫ sX) hamp
  have hsplit : ∑ j, Finsupp.single (F j) (-c * r j + b j - p j) =
      Finsupp.single (F j') (-1) + A := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), h.eq_neg_one]
    rfl
  have hNeq : N = Divisor.toQDivisor L + A := by
    rw [hNdef, hsplit, hL]
    ext E
    classical
    simp [Divisor.toQDivisor, Finsupp.single_apply]
    simp only [DivisorWithCoeffs.coeff, Finsupp.single_apply]
    split_ifs <;> push_cast <;> ring
  have hsnc : A.IsSNC (f ≫ sX) := by
    classical
    refine h.isSNC.of_support_subset fun E hE => ?_
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hE)
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hj)
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, h.injective.eq_iff]
  rw [hNeq] at hnef hbig
  have hvan := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    (f ≫ sX) hsm hKY L A hsnc hnef hbig 1 one_pos
  have H1 : Subsingleton (cohomologyOverField k (f ≫ sX)
      (KY + (Divisor.toQDivisor L + A).roundUp).divisorialSheaf 1) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (f ≫ sX)
      _ 1).toEquiv.subsingleton
  have hround : (Divisor.toQDivisor L + A).roundUp = L + A.roundUp := by
    ext E
    have h1 := DivisorWithCoeffs.coeff_roundUp (Divisor.toQDivisor L + A) E
    have h2 := DivisorWithCoeffs.coeff_roundUp A E
    have h3 := Divisor.coeff_toQDivisor L E
    simp only [DivisorWithCoeffs.coeff, Finsupp.coe_add, Pi.add_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3, Int.ceil_intCast_add]
  have key : KY + (Divisor.toQDivisor L + A).roundUp + Finsupp.single (F j') 1 =
      β • D' + A.roundUp := by
    rw [hround, hL]; abel
  have hsurj := Divisor.surjective_cohomologyOverFieldMap_restriction (f ≫ sX) hP.toIsVariety
    hsm (KY + (Divisor.toQDivisor L + A).roundUp) (F j') H1
  rw [key] at hsurj
  haveI : Nontrivial (cohomologyOverField k (f ≫ sX) (β • D' + A.roundUp).divisorialSheaf 0) :=
    hsurj.nontrivial
  have hΓ : Nontrivial ((β • D' + A.roundUp).divisorialSubmodule ⊤) :=
    (cohomologyOverFieldZeroLinearIso k (f ≫ sX)
      (β • D' + A.roundUp).divisorialSheaf).toLinearEquiv.toEquiv.symm.nontrivial
  obtain ⟨σ, hσ⟩ := exists_ne (0 : (β • D' + A.roundUp).divisorialSubmodule ⊤)
  obtain ⟨τ, hτ⟩ := h.exists_functionFieldMap_eq_roundUp hB hD' β σ
  refine ⟨τ, fun h0 => Divisor.sectionToRationalFunctions_ne_zero hσ ?_⟩
  subst h0
  apply (rationalFunctionsEquivFunctionField Y).injective
  rw [← hτ, map_zero]
  have h0 : Divisor.sectionToRationalFunctions
      (0 : (β • D + G.roundUp).divisorialSubmodule ⊤) = 0 :=
    map_zero (rationalFunctionsPresheafTopEquiv X)
  rw [h0, map_zero, map_zero]

end MMP.Mori
