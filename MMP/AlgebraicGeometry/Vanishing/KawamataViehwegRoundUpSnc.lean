module

public import MMP.AlgebraicGeometry.Vanishing.KawamataViehweg

/-!
# Kawamata–Viehweg vanishing for the round up of a nef and big `ℚ`-divisor

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero, and `M` a nef and big `ℚ`-divisor on `X` whose fractional part `{M}`
has simple normal crossing support. Then `H^i(X, ω_X ⊗ 𝒪_X(⌈M⌉)) = 0` for every `i > 0`, where
`ω_X = ⋀ⁿ Ω_{X/k}`, i.e. `H^i(X, 𝒪_X(K_X + ⌈M⌉)) = 0`.

Writing `⌈M⌉ = M + Δ` with `Δ = ⌈M⌉ - M`, the divisor `Δ` has coefficients in `[0, 1)` and the
same support as `{M}`, so `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg`
gives `H^q(X, 𝒪_X(-⌈M⌉)) = 0` for `q < n`, and Serre duality turns this into the claim.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_roundUp`:
  the vanishing above.

## Implementation notes

The fractional support of `M` is the set of prime divisors along which the coefficient of `M`
is not an integer, which is the support of `MMP.Mori.DivisorWithCoeffs.fract M`; the hypothesis
is `MMP.Mori.DivisorWithCoeffs.IsSNC` of `{M}`. `H^i(X, ℱ)` for `i : ℤ` is
`Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree zero, which is sheaf
cohomology for `i ≥ 0`, and `𝒪_X(K_X + ⌈M⌉)` is `ω_X ⊗ 𝒪_X(⌈M⌉)`, with `𝒪_X(⌈M⌉)` the divisorial
sheaf of `⌈M⌉`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64
-/

@[expose] public section

/-!
## Proof: Vanishing for the round-up of a nef and big `ℚ`-divisor

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field of
characteristic zero and `M` a nef and big `ℚ`-divisor whose fractional part has simple normal
crossing support. Then `H^i(X, ω_X ⊗ 𝒪_X(⌈M⌉)) = 0` for every `i > 0`.

The boundary `Δ = ⌈M⌉ - M` has coefficients in `[0, 1)` and support that of `{M}`, so
Kawamata–Viehweg vanishing gives `H^{n-i}(X, 𝒪_X(-⌈M⌉)) = 0`, and Serre duality turns this into
the claim.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Cor. 2.68
-/

namespace MMP.FourfoldProofs.MmpKmRoundUpVanishingProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- **Serre duality for divisors on a smooth projective variety.** For a divisor `D` on a smooth
projective variety `X` of dimension `n`, `H^i(X, 𝒪_X(-D)) = 0` if and only if
`H^{n-i}(X, ω_X ⊗ 𝒪_X(D)) = 0`. -/
private theorem subsingleton_divisorialSheaf_neg_iff [MMP.Mori.IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : Divisor X) (i : ℤ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (-D).divisorialSheaf) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
              D.divisorialSheaf)) (n - i)) := by
  have hD := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm D
  haveI := hD.isInvertibleModule_divisorialSheaf
  letI : HasDerivedCategory (ModuleCat.{0} k) := ModuleCat.hasDerivedCategory
  -- `𝒪_X(-D) ≅ 𝒪_X(D)^∨`, since `𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X(D - D) = 𝒪_X`.
  let e : (-D).divisorialSheaf ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.divisorialSheaf :=
    Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
      X.ringCatSheaf.property D.divisorialSheaf (-D).divisorialSheaf
      (hD.divisorialSheafTensorIso (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) ≪≫
        eqToIso (congrArg Divisor.divisorialSheaf (add_neg_cancel D)) ≪≫
        Divisor.divisorialSheafZeroIso)
  rw [← subsingleton_dual_iff_subsingleton_exteriorPower_tensor f hsm n hn]
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).mapIso
    ((derivedGlobalSectionsOver f).mapIso ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      e))).toLinearEquiv.toEquiv.subsingleton_congr

/-- The coefficients of `⌈M⌉ - M`. -/
private theorem toQDivisor_roundUp_sub_apply (M : QDivisor X) (E : MMP.Mori.PrimeDivisor X) :
    (Divisor.toQDivisor M.roundUp - M) E = ⌈M E⌉ - M E :=
  rfl

end MMP.FourfoldProofs.MmpKmRoundUpVanishingProof

public section

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.MmpKmRoundUpVanishingProof
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- **Kawamata–Viehweg vanishing for a round up** (Kollár–Mori, Theorem 2.64). Let `X` be a
smooth projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero and `M` a nef and big `ℚ`-divisor on `X` whose fractional part has simple
normal crossing support. Then `H^i(X, ω_X ⊗ 𝒪_X(⌈M⌉)) = 0` for every `i > 0`, where
`ω_X = ⋀ⁿ Ω_{X/k}`. -/
@[mmp "lem_mmp_km_round_up_vanishing"]
public theorem subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} (hn : topologicalKrullDim X = n)
    (M : QDivisor X) (hMnef : M.IsNef k f) (hMbig : M.IsBig k f) (hM : M.fract.IsSNC f)
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
            M.roundUp.divisorialSheaf)) i) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have h := (subsingleton_divisorialSheaf_neg_iff f hsm hn M.roundUp (n - i)).1 <|
    subsingleton_derivedCohomologyOverField_divisorialSheaf_neg f hsm hn M.roundUp M
      (Divisor.toQDivisor M.roundUp - M) hMnef hMbig
      (hM.of_support_subset fun E hE => by
        rw [Finsupp.mem_support_iff, toQDivisor_roundUp_sub_apply, sub_ne_zero] at hE
        rw [Finsupp.mem_support_iff]
        change Int.fract (M E) ≠ 0
        exact fun h => hE (by obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.1 h; simp [← hz]))
      (fun E => (toQDivisor_roundUp_sub_apply M E).symm ▸ sub_nonneg.2 (Int.le_ceil (M E)))
      (fun E => by rw [toQDivisor_roundUp_sub_apply]; linarith [Int.ceil_lt_add_one (M E)])
      (by
        rw [add_sub_cancel]
        exact QDivisor.NumericallyEquivalent.refl (QDivisor.isQCartier_toQDivisor
          (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _)))
      (n - i) (by omega)
  rwa [sub_sub_cancel] at h

end MMP.Mori

end
