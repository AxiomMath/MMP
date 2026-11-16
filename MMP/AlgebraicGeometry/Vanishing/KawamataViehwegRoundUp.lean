module

public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUpSnc

/-!
# Kawamata–Viehweg vanishing for round-ups

Let `Y` be a smooth projective variety over an algebraically closed field `k` of
characteristic zero, `L` a (Cartier) divisor on `Y` and `Δ = ∑ dᵢ Dᵢ` a `ℚ`-divisor whose
support is a simple normal crossing divisor. If `D = L + Δ` is nef and big, then
`H^i(Y, 𝒪_Y(K_Y + ⌈D⌉)) = 0` for every `i > 0`.

Since `L` is integral, the fractional part of `D` is supported on that of `Δ`, so `{D}` is snc
and `MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_roundUp`
gives `H^i(Y, ω_Y ⊗ 𝒪_Y(⌈D⌉)) = 0` for `i > 0`. On the smooth `Y` every divisor is Cartier, and
`𝒪_Y(K_Y) ≅ ω_Y = ⋀ⁿ Ω_{Y/k}` because the smooth locus is all of `Y`; so
`𝒪_Y(K_Y + ⌈D⌉) ≅ 𝒪_Y(K_Y) ⊗ 𝒪_Y(⌈D⌉) ≅ ω_Y ⊗ 𝒪_Y(⌈D⌉)`, which gives the claim.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp`:
  `H^i(Y, 𝒪_Y(K_Y + ⌈L + Δ⌉)) = 0` for `i > 0`.

## Implementation notes

The boundary `∑ dᵢ Dᵢ` with distinct prime divisors `Dᵢ` is a single `ℚ`-divisor `Δ`, and the
condition that `∑ Dᵢ` be snc is `MMP.Mori.DivisorWithCoeffs.IsSNC` of `Δ`, which asks it of
the components with nonzero coefficient; this is implied by the source's condition
(`MMP.Mori.DivisorWithCoeffs.IsSNC.of_support_subset`). On the smooth variety `Y` every Weil
divisor is Cartier, so `L` is a `MMP.Mori.Divisor`. The canonical divisor `K_Y` is any `K` with
`MMP.Mori.Divisor.IsCanonicalDivisor`. `H^i(Y, ℱ)` for `i : ℤ` is
`Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree zero.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 3.1
-/

@[expose] public section

section

namespace MMP.FourfoldProofs.Km3aVanishingRoundupProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

/-- Adding an integral divisor does not change fractional parts, so the fractional part of
`L + Δ` is supported on the support of `Δ`. -/
private lemma support_fract_toQDivisor_add_subset {X : Scheme.{0}} (L : Divisor X)
    (Δ : QDivisor X) : (Divisor.toQDivisor L + Δ).fract.support ⊆ Δ.support := by
  intro E
  simp only [Finsupp.mem_support_iff]
  contrapose!
  intro h
  have hL : Divisor.toQDivisor L E = (L E : ℚ) := Divisor.coeff_toQDivisor L E
  simpa [DivisorWithCoeffs.coeff_apply, h, hL] using
    DivisorWithCoeffs.coeff_fract (Divisor.toQDivisor L + Δ) E

/-- On a smooth variety `X` of dimension `n`, a canonical divisor `K` has
`𝒪_X(K) ≅ ⋀ⁿ Ω_{X/k}`. -/
private lemma nonempty_divisorialSheaf_iso_exteriorPower {k : Type} [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} [MMP.Mori.IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) :=
  MMP.Flips.nonempty_iso_of_restrict_iso hsm (hK.iso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _ ≪≫
      Scheme.Modules.exteriorPowerPullbackIso (smoothLocus f).ι _ n ≪≫
      (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
        (Scheme.Hom.etaleRelativeDifferentialsIso (smoothLocus f).ι f _ rfl)).symm)

end MMP.FourfoldProofs.Km3aVanishingRoundupProof

end

section

public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- **Kawamata–Viehweg vanishing for round-ups** (Kollár–Mori, Theorem 3.1). Let `Y` be a smooth
projective variety of dimension `n` over an algebraically closed field `k` of characteristic
zero, `K` a canonical divisor of `Y`, `L` a divisor and `Δ` a `ℚ`-divisor on `Y` with simple
normal crossing support. If `D = L + Δ` is nef and big, then `H^i(Y, 𝒪_Y(K + ⌈D⌉)) = 0` for every
`i > 0`. -/
@[mmp "thm_km3a_vanishing_roundup"]
public theorem subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor f n)
    (L : Divisor Y) (Δ : QDivisor Y) (hΔ : Δ.IsSNC f)
    (hnef : (Divisor.toQDivisor L + Δ).IsNef k f) (hbig : (Divisor.toQDivisor L + Δ).IsBig k f)
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf) i) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨eK⟩ :=
    FourfoldProofs.Km3aVanishingRoundupProof.nonempty_divisorialSheaf_iso_exteriorPower hsm hK
  set R := (Divisor.toQDivisor L + Δ).roundUp
  let e := ((MMP.Fourfold.isCartier_of_isSmoothScheme hsm K).divisorialSheafTensorIso
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm R)).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso eK).app R.divisorialSheaf
  refine ((DerivedCategory.homologyFunctor _ i).mapIso ((derivedGlobalSectionsOver f).mapIso
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso e))).toLinearEquiv.toEquiv
    |>.subsingleton_congr.mpr ?_
  exact subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_roundUp f hsm
    hK.topologicalKrullDim_eq _ hnef hbig
    (hΔ.of_support_subset (FourfoldProofs.Km3aVanishingRoundupProof.support_fract_toQDivisor_add_subset
      L Δ)) i hi

end MMP.Mori

end
