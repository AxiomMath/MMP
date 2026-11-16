module

public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.MMP.BasepointFree.TestDivisorAmple
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp

@[expose] public section

section

/-!
# Sections of `b f^*D + ⌈A⌉` restrict onto the tie-breaking divisor

Let `(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum
`(X, Δ, D, a)` with a tie-breaker `(j', c)` and test boundary
`A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j`, and put `F = F_{j'}`. For every integer `b ≥ cm + a`
the restriction map `H⁰(Y, 𝒪_Y(b f^*D + ⌈A⌉)) → H⁰(F, 𝒪_Y(b f^*D + ⌈A⌉)|_F)` is surjective.
Indeed the test divisor `N(b, c) = b f^*D - F - K_Y + A` is ample, so by the round-up form of
Kawamata–Viehweg vanishing `H¹(Y, 𝒪_Y(K_Y + ⌈N(b, c)⌉)) = 0`, and
`K_Y + ⌈N(b, c)⌉ + F = b f^*D + ⌈A⌉`; the restriction sequence of the smooth prime divisor `F`
then gives the surjection.

## Main results

* `MMP.Mori.IsBasepointFreeTieBreaker.surjective_restriction_pullback_add_roundUp`: the
  restriction of sections of `𝒪_Y(b f^*D + ⌈A⌉)` to `F_{j'}` is surjective for `b ≥ cm + a`.

## Implementation notes

The restriction map is the composite of the map on `H⁰` induced by the unit
`𝒪_Y(L) ⟶ i_* i^* 𝒪_Y(L)` of the closed immersion `i : F ⟶ Y` of `F_{j'}` with the
identification `H⁰(Y, i_* G) ≅ H⁰(F, G)`, both over `k` through `f ≫ sX`. The pull-back `f^*D`
is any `D'` with `D.IsPullback f hB D'`, and the statement is made for every such `D'`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, 3.2 Step 4
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.Km3aBpfRestrictionOntoProof

/-- A test boundary of an injective family `F` of prime divisors with `∑_j F_j` snc is snc. -/
private theorem isSNC_tieBreakerBoundary {k : Type} [Field k] {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ Spec (.of k)} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {F : ι → MMP.Mori.PrimeDivisor Y} (hF : Function.Injective F)
    (hsnc : DivisorWithCoeffs.IsSNC f (∑ j, Finsupp.single (F j) (1 : ℤ)))
    (r a p : ι → ℚ) (j' : ι) (c : ℚ) : (tieBreakerBoundary F r a p j' c).IsSNC f := by
  classical
  refine hsnc.of_support_subset fun E hE => ?_
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hE)
  obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hj)
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hF.eq_iff]

/-- If the coefficient `-c r_{j'} + a_{j'} - p_{j'}` is `-1`, the test divisor
`b D' - K_Y + ∑_j (-c r_j + a_j - p_j) F_j` is the integral divisor `b D' - K_Y - F_{j'}` plus the
test boundary. -/
private theorem testDivisor_eq_toQDivisor_add_tieBreakerBoundary {Y : Scheme.{0}}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → MMP.Mori.PrimeDivisor Y) (r a p : ι → ℚ)
    (j' : ι) (c : ℚ) (h : -c * r j' + a j' - p j' = -1) (b : ℤ) (D' KY : Divisor Y) :
    (b : ℚ) • Divisor.toQDivisor D' - Divisor.toQDivisor KY +
        ∑ j, Finsupp.single (F j) (-c * r j + a j - p j) =
      Divisor.toQDivisor (b • D' - KY - Finsupp.single (F j') 1) +
        tieBreakerBoundary F r a p j' c := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j'), h]
  change _ + (_ + tieBreakerBoundary F r a p j' c) = _
  generalize tieBreakerBoundary F r a p j' c = A
  classical
  ext E
  simp [Divisor.toQDivisor, Finsupp.single_apply]
  simp only [DivisorWithCoeffs.coeff, Finsupp.single_apply]
  split_ifs <;> push_cast <;> ring

/-- For integral `B, K_Y` and a prime divisor `E`, `K_Y + ⌈(B - K_Y - E) + A⌉ + E = B + ⌈A⌉`. -/
private theorem add_roundUp_toQDivisor_sub_sub_add_single {Y : Scheme.{0}}
    (B KY : Divisor Y) (E : MMP.Mori.PrimeDivisor Y) (A : QDivisor Y) :
    KY + (Divisor.toQDivisor (B - KY - Finsupp.single E 1) + A).roundUp + Finsupp.single E 1 =
      B + A.roundUp := by
  ext P
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
    Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
  rw [Int.ceil_intCast_add]
  ring

/-- On a smooth projective variety `Y` over an algebraically closed field of characteristic `0`
with canonical divisor `K_Y`, let `B` be a divisor, `E` a prime divisor and `A` a `ℚ`-divisor with
snc support. If `(B - E - K_Y) + A` is ample, then sections of `𝒪_Y(B + ⌈A⌉)` restrict onto `E`. -/
private theorem surjective_restriction_of_isAmple {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (f : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k f] [QuasiCompact f]
    (hsm : IsSmoothScheme f) {n : ℕ} {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor f n)
    (B : Divisor Y) (E : MMP.Mori.PrimeDivisor Y) {A : QDivisor Y} (hA : A.IsSNC f)
    (hN : (Divisor.toQDivisor (B - KY - Finsupp.single E 1) + A).IsAmple) :
    Function.Surjective (cohomologyOverFieldMap k f
        ((Scheme.Modules.pullbackPushforwardAdjunction E.idealSheaf.subschemeι).unit.app
          (B + A.roundUp).divisorialSheaf) 0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k E.idealSheaf.subschemeι f
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (B + A.roundUp).divisorialSheaf) 0).inv).hom := by
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple f hN
  have := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    f hsm hKY _ A hA hnef hbig 1 one_pos
  have := Divisor.surjective_cohomologyOverFieldMap_restriction f
    AlgebraicGeometry.IsProjectiveVariety.toIsVariety hsm
    (KY + (Divisor.toQDivisor (B - KY - Finsupp.single E 1) + A).roundUp) E
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _
      1).toEquiv.subsingleton
  rwa [add_roundUp_toQDivisor_sub_sub_add_single] at this

end MMP.FourfoldProofs.Km3aBpfRestrictionOntoProof

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **Sections restrict onto the tie-breaking divisor** (Kollár–Mori 3.2, Step 4). Let
`(f; F_•; a_•; p_•; r_•)` be an `m`-adapted resolution of a basepoint-free datum `(X, Δ, D, a)`
with a tie-breaker `(j', c)`, let `A = ∑_{j ≠ j'} (-c r_j + a_j - p_j) F_j` be its test boundary
and `i : F_{j'} ⟶ Y` the closed immersion. Then for every integer `b ≥ cm + a` and every
pull-back `D'` of `D` along `f`, the restriction
`H⁰(Y, 𝒪_Y(b D' + ⌈A⌉)) ⟶ H⁰(F_{j'}, i^* 𝒪_Y(b D' + ⌈A⌉))` is surjective. -/
@[mmp "lem_km3a_bpf_restriction_onto"]
public theorem IsBasepointFreeTieBreaker.surjective_restriction_pullback_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {D : Divisor X} {a : ℚ} {m : ℕ}
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {s : ℕ} {F : Fin s → PrimeDivisor Y} {aj pj : Fin s → ℚ} {rj : Fin s → ℕ}
    {j' : Fin s} {c : ℚ}
    (h : IsBasepointFreeTieBreaker sX n K Δ D a m f F aj pj rj j' c)
    {b : ℤ} (hb : c * m + a ≤ b)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {D' : Divisor Y} (hD' : D.IsPullback f hB D') :
    Function.Surjective (cohomologyOverFieldMap k (f ≫ sX)
        ((Scheme.Modules.pullbackPushforwardAdjunction (F j').idealSheaf.subschemeι).unit.app
          (b • D' +
            (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c).roundUp).divisorialSheaf)
          0 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (F j').idealSheaf.subschemeι
        (f ≫ sX) ((Scheme.Modules.pullback (F j').idealSheaf.subschemeι).obj
          (b • D' +
            (tieBreakerBoundary F (fun j ↦ (rj j : ℚ)) aj pj j' c).roundUp).divisorialSheaf)
          0).inv).hom := by
  have : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := h.isProjectiveVariety
  have : AlgebraicGeometry.IsProperVariety k sX := h.isProperVariety
  have : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := h.isLogResolution.isSmoothScheme
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      h.isLogResolution.isBirationalMorphism).symm.trans h.isKltPair.1.2.1.1)
  refine MMP.FourfoldProofs.Km3aBpfRestrictionOntoProof.surjective_restriction_of_isAmple (f ≫ sX)
    hsm hKY _ (F j') (MMP.FourfoldProofs.Km3aBpfRestrictionOntoProof.isSNC_tieBreakerBoundary
      h.injective h.isSNC _ aj pj j' c) ?_
  rw [← MMP.FourfoldProofs.Km3aBpfRestrictionOntoProof.testDivisor_eq_toQDivisor_add_tieBreakerBoundary
    _ _ _ _ _ _ h.eq_neg_one]
  exact h.toIsBasepointFreeAdaptedResolution.isAmple_of_isTieBreakerTestDivisor h.pos_c.le hb
    ⟨hKY, hB, D', hD', rfl⟩

end MMP.Mori

end
