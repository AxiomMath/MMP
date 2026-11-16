module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripTestDivisorAmple
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion

@[expose] public section

section

/-!
## Auxiliary lemmas

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, `(j₀, c)` a tie-breaker of a
`(p, q)`-adapted resolution `f : Y ⟶ X` with test boundary `A'`, and `p', q'` integers with
`p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`. Write `B' = f^*(p'H + q'a(K_X + Δ))`
and `F = F_{j₀}`. The test divisor `N = B' + A' - F - K_Y` is ample, hence nef and big, and
`A'` is supported on the snc divisor `∑_j F_j`, so Kawamata–Viehweg vanishing for the round-up
gives `H¹(Y, 𝒪_Y(K_Y + ⌈N⌉)) = 0`, where `K_Y + ⌈N⌉ = B' + ⌈A'⌉ - F`. The long exact sequence
of `0 ⟶ 𝒪_Y(B' + ⌈A'⌉ - F) ⟶ 𝒪_Y(B' + ⌈A'⌉) ⟶ 𝒪_Y(B' + ⌈A'⌉)|_F ⟶ 0` then shows that the
restriction of sections of `𝒪_Y(B' + ⌈A'⌉)` to `F` is surjective.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4 Step 8
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3bStripRestrictionSurjectiveProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- On a smooth variety, if `H¹(Y, 𝒪_Y(D)) = 0` then the restriction
`H⁰(Y, 𝒪_Y(D + F)) ⟶ H⁰(F, i^* 𝒪_Y(D + F))` to a prime divisor `F` is surjective, by the long
exact sequence of `0 ⟶ 𝒪_Y(D) ⟶ 𝒪_Y(D + F) ⟶ i_* i^* 𝒪_Y(D + F) ⟶ 0`. -/
private theorem surjective_restriction_of_subsingleton {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] (hV : MMP.Mori.IsVariety k f)
    (hsm : IsSmoothScheme f) (D : Divisor Y) (F : MMP.Mori.PrimeDivisor Y)
    (hH1 : Subsingleton (cohomologyOverField k f D.divisorialSheaf 1)) :
    Function.Surjective (cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction F.idealSheaf.subschemeι).unit.app
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
        ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
          (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0).inv).hom := by
  obtain ⟨_, hS⟩ := Divisor.IsCartier.shortExact_divisorialSheafInclusion_restriction f hV hsm F
    (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D)
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  generalize cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k F.idealSheaf.subschemeι f
      ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj
        (D + Finsupp.single F (1 : ℤ)).divisorialSheaf) 0 = e
  rw [ModuleCat.hom_comp]
  exact e.toLinearEquiv.symm.surjective.comp fun y => (hgd 0 y).1 (Subsingleton.elim _ _)

/-- The round-down of a `ℚ`-divisor with integral coefficients is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{0}} (D : Divisor X) :
    (Divisor.toQDivisor D).roundDown = D := by
  ext E
  change ((Divisor.toQDivisor D).roundDown).coeff E = D.coeff E
  rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]

/-- For a rationality datum, a pull-back of the integral divisor `p'H + q'a(K_X + Δ)` is a
pull-back of the `ℚ`-divisor `p'H + q'a(K_X + Δ)`: `a(K_X + Δ)` is Cartier, so the strip divisor
is Cartier and its pull-back is computed by either reading. -/
private theorem isPullback_toQDivisor_stripDivisor {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H) {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} (p' q' : ℤ)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hB B') :
    ∃ hb, (p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ)).IsPullback f hb
      (Divisor.toQDivisor B') := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  have hr0 : (a • (Divisor.toQDivisor K + Δ)).roundDown = D₀ := by
    rw [← hD₀, roundDown_toQDivisor]
  have hMQ : Divisor.toQDivisor (stripDivisor K Δ a H p' q') =
      p' • Divisor.toQDivisor H + (q' * a) • (Divisor.toQDivisor K + Δ) := by
    rw [stripDivisor, hr0, map_add, map_zsmul, map_zsmul, hD₀, smul_smul]
  rw [← hMQ]
  refine ⟨_, QDivisor.isPullback_toQDivisor ?_
    (fun Z hZ => hB Z (by rwa [Divisor.supp_toQDivisor] at hZ)) hB'⟩
  rw [stripDivisor, hr0]
  exact (h.isCartier_H.zsmul p').add (hD₀c.zsmul q')

/-- The test boundary of an adapted resolution is supported on `∑_j F_j`, hence is snc. -/
private theorem isSNC_tieBreakerBoundary {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} {p q : ℤ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {f : Y ⟶ X} {s : ℕ} {F : Fin s → MMP.Mori.PrimeDivisor Y}
    {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    (h : IsStripAdaptedResolution sX n K Δ a H p q f F aj pj rj) (r : Fin s → ℚ) (j₀ : Fin s)
    (c : ℚ) : (tieBreakerBoundary F r aj pj j₀ c).IsSNC (f ≫ sX) := by
  refine h.isSNC.of_support_subset fun E hE => ?_
  rw [tieBreakerBoundary, Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hE
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hE
  obtain rfl : F j = E := by
    by_contra hne
    exact hj (Finsupp.single_eq_of_ne' hne)
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finset.sum_eq_single j
    (fun b _ hb => Finsupp.single_eq_of_ne' (h.injective.ne hb)) (by simp)]
  simp

/-- With `N = (B - E - K_Y) + A` for integral `B, E, K_Y`, the round-up satisfies
`K_Y + ⌈N⌉ = B + ⌈A⌉ - E`. -/
private theorem add_roundUp_toQDivisor_sub_sub_add {Y : Scheme.{0}} (B E KY : Divisor Y)
    (A : QDivisor Y) :
    KY + (Divisor.toQDivisor (B - E - KY) + A).roundUp = B + A.roundUp - E := by
  ext P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
    Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
  rw [Int.ceil_intCast_add]
  ring

end MMP.FourfoldProofs.Km3bStripRestrictionSurjectiveProof

end

section

/-!
# Sections in the strip restrict onto the tie-breaking divisor

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, let `p, q > 0` be integers with `aq - rp > 0`, let `(j₀, c)` be a tie-breaker of a
`(p, q)`-adapted resolution `(f; F_•; a_•; p_•; r_•)` with test boundary
`A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j`, and put `F = F_{j₀}`. For integers `p', q'` with
`p' ≥ (1 + c) p`, `q' ≥ (1 + c) q` and `aq' - rp' ≤ aq - rp`, the restriction map
`H⁰(Y, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)) → H⁰(F, 𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)|_F)`
is surjective. Indeed the test divisor `N(p', q') = f^*(p'H + q'a(K_X + Δ)) + A' - F - K_Y` is
ample, so `H¹(Y, 𝒪_Y(K_Y + ⌈N(p', q')⌉)) = 0` by the round-up form of Kawamata–Viehweg
vanishing, and `K_Y + ⌈N(p', q')⌉ + F = f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉`; the restriction
sequence of the smooth prime divisor `F` gives the surjection.

## Main results

* `MMP.Mori.IsStripTieBreaker.surjective_restriction_pullback_add_roundUp`: the restriction of
  sections of `𝒪_Y(f^*(p'H + q'a(K_X + Δ)) + ⌈A'⌉)` to `F_{j₀}` is surjective.

## Implementation notes

The divisor `p'H + q'a(K_X + Δ)` is the integral divisor `MMP.Mori.stripDivisor K Δ a H p' q'`
(for a rationality datum `a(K_X + Δ)` has integral coefficients), and its pull-back is any `B'`
with `(stripDivisor K Δ a H p' q').IsPullback f hB B'`; the statement is made for every such `B'`.
The restriction map is the composite of the map on `H⁰` induced by the unit
`𝒪_Y(L) ⟶ i_* i^* 𝒪_Y(L)` of the closed immersion `i : F ⟶ Y` with the identification
`H⁰(Y, i_* G) ≅ H⁰(F, G)`, both over `k` through `f ≫ sX`. The inequalities `p' ≥ (1 + c) p` and
`q' ≥ (1 + c) q` are read in `ℚ`, and `aq' - rp' ≤ aq - rp` in `ℝ`, since `c` is rational and `r`
real. The ground field is algebraically closed of characteristic zero, as Kawamata–Viehweg
vanishing requires.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.5, 3.4 Step 8
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3bStripRestrictionSurjectiveProof in
/-- **Sections in the strip restrict onto the tie-breaking divisor** (Kollár–Mori 3.4, Step 8).
Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r` of `H` with respect to
`K_X + Δ`, `p, q > 0` integers with `0 < aq - rp`, `(j₀, c)` a tie-breaker of a `(p, q)`-adapted
resolution `(f; F_•; a_•; p_•; r_•)`, `A' = ∑_{j ≠ j₀} (-c r_j + a_j - p_j) F_j` its test
boundary and `i : F_{j₀} ⟶ Y` the closed immersion. Then for integers `p', q'` with
`(1 + c) p ≤ p'`, `(1 + c) q ≤ q'` and `aq' - rp' ≤ aq - rp`, and every pull-back `B'` of
`p'H + q'a(K_X + Δ)` along `f`, the restriction
`H⁰(Y, 𝒪_Y(B' + ⌈A'⌉)) ⟶ H⁰(F_{j₀}, i^* 𝒪_Y(B' + ⌈A'⌉))` is surjective. -/
@[mmp "lem_km3b_strip_restriction_surjective"]
public theorem IsStripTieBreaker.surjective_restriction_pullback_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X} {p q : ℤ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j₀ : Fin s} {c : ℚ}
    (h : IsStripTieBreaker sX n K Δ a H p q f F aj pj rj j₀ c) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hpq : 0 < (a * q : ℝ) - r * p) {p' q' : ℤ}
    (hp' : (1 + c) * p ≤ p') (hq' : (1 + c) * q ≤ q')
    (hpq' : (a * q' : ℝ) - r * p' ≤ a * q - r * p)
    {hB : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp}
    {B' : Divisor Y} (hB' : (stripDivisor K Δ a H p' q').IsPullback f hB B') :
    Function.Surjective (cohomologyOverFieldMap k (f ≫ sX)
        ((Scheme.Modules.pullbackPushforwardAdjunction (F j₀).idealSheaf.subschemeι).unit.app
          (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
          0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (F j₀).idealSheaf.subschemeι
        (f ≫ sX) ((Scheme.Modules.pullback (F j₀).idealSheaf.subschemeι).obj
          (B' + (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c).roundUp).divisorialSheaf)
          0).inv).hom := by
  set A := tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j₀ c
  have hLR := h.isLogResolution
  have hsm : IsSmoothScheme (f ≫ sX) := hLR.isSmoothScheme
  have hYp : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have hYv : MMP.Mori.IsVariety k (f ≫ sX) := hYp.toIsVariety
  have : AlgebraicGeometry.IsVariety k sX := h.isKltPair.1.1.1
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYv
  have : IsProper f := hLR.isProper
  have : IsIntegral Y := h.isCrepantBoundary.1.1.toIsIntegral
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      hLR.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1)
  -- the test divisor `N = (B' - F - K_Y) + A'` is ample, hence nef and big
  obtain ⟨hb, hpb⟩ := isPullback_toQDivisor_stripDivisor h.toIsRationalityDatum p' q' hB'
  have hN : IsStripTestDivisor sX n K Δ a H f KY F aj pj rj j₀ c p' q'
      (Divisor.toQDivisor (B' - Finsupp.single (F j₀) 1 - KY) + A) := ⟨hKY, hb, _, hpb, by
    rw [map_sub, map_sub, MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
    abel⟩
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple (f ≫ sX)
    (h.isAmple_of_isStripTestDivisor hr hpq hp' hq' hpq' hN)
  -- Kawamata–Viehweg vanishing for `K_Y + ⌈N⌉ = B' + ⌈A'⌉ - F`
  have hKV := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    (f ≫ sX) hsm hKY _ A (isSNC_tieBreakerBoundary h.toIsStripAdaptedResolution _ j₀ c) hnef hbig
    1 one_pos
  rw [add_roundUp_toQDivisor_sub_sub_add] at hKV
  have key := surjective_restriction_of_subsingleton (f ≫ sX) hYv hsm
    (B' + A.roundUp - Finsupp.single (F j₀) 1) (F j₀)
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (f ≫ sX) _
      1).toEquiv.subsingleton
  rwa [sub_add_cancel] at key

end MMP.Mori

end
