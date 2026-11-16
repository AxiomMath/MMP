module

public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero

/-!
# Kodaira vanishing in the form `H^i(X, 𝒪_X(B)) = 0` for `B - K_X` ample

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero, `K` a canonical divisor of `X` and `B` a divisor on `X` such that `B - K` is ample. Then
`H^i(X, 𝒪_X(B)) = 0` for every `i > 0`. Writing `L = 𝒪_X(B - K)`, one has
`𝒪_X(B) ≅ ω_X ⊗ L`, and the statement is Serre dual to Kodaira vanishing
`H^{n-i}(X, L^{-1}) = 0` for `i > 0`.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_of_isAmple_sub`:
  `H^i(X, 𝒪_X(B)) = 0` for `i > 0` when `B - K_X` is ample.

## Implementation notes

* `H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField f` of `ℱ` placed in
  degree zero, as in `MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple`.
* `K_X` is any divisor `K` with `MMP.Mori.Divisor.IsCanonicalDivisor f n K`; that predicate
  also records `dim X = n`.
* "`B - K` is ample" means that `𝒪_X(B - K)` is an ample invertible sheaf: `B - K` is Cartier
  and `MMP.Mori.Divisor.IsAmple` holds. On a smooth variety every divisor is Cartier, so the
  Cartier condition is part of the meaning of ampleness of `𝒪_X(B - K)`, not an extra hypothesis.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 2.47 and the proof of Proposition 2.57
-/

@[expose] public section

section

/-!
## Proof: Kodaira vanishing in the form `H^i(X, 𝒪_X(B)) = 0` for `B - K_X` ample

On a smooth projective variety `X` of dimension `n` every divisor is Cartier and
`𝒪_X(K_X) ≅ ω_X = ⋀ⁿ Ω_{X/k}`. For `L = 𝒪_X(B - K_X)` ample, `ω_X ⊗ L ≅ 𝒪_X(B)`, and
`H^i(X, ω_X ⊗ L)` is Serre dual to `H^{n-i}(X, L^{-1})`, which vanishes for `i > 0` by Kodaira
vanishing.

## References

* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Theorem 2.47
-/

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km2cKodairaVanishingDualProof

variable {k : Type} [Field k] {X : Scheme.{0}} {f : X ⟶ Spec (.of k)}

/-- On a smooth `k`-scheme a canonical divisor computes the canonical sheaf:
`𝒪_X(K_X) ≅ ⋀ⁿ Ω_{X/k}`. -/
private theorem nonempty_divisorialSheaf_iso_relativeDifferentialForms
    [IsLocallyNoetherian X] [IsNormal X] (hsm : IsSmoothScheme f) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms f n) := by
  have hc : (smoothLocus f).ι ≫ f = ((smoothLocus f).ι ≫ f) ≫ 𝟙 _ := (Category.comp_id _).symm
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale (smoothLocus f).ι f _ (𝟙 _) hc n
  exact MMP.Flips.nonempty_iso_of_restrict_iso hsm <| hK.iso ≪≫
    (asIso (Scheme.Hom.relativeDifferentialFormsMap (smoothLocus f).ι f _ (𝟙 _) hc n)).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _).symm

/-- Cohomology `H^i(X, -)` of a sheaf placed in degree zero is invariant under isomorphism. -/
private theorem subsingleton_derivedCohomologyOverField_congr {M N : X.Modules} (e : M ≅ N)
    (i : ℤ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj M) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj N) i) :=
  ((derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) i).mapIso
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso e)).toLinearEquiv.toEquiv.subsingleton_congr

end MMP.FourfoldProofs.Km2cKodairaVanishingDualProof

end

section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

open MMP.FourfoldProofs.Km2cKodairaVanishingDualProof in
/-- **Kodaira vanishing, Serre-dual form** (Kollár--Mori, Theorem 2.47, as used in the proof of
Proposition 2.57). Let `X` be a smooth projective variety over an algebraically closed field `k`
of characteristic zero, `K` a canonical divisor of `X`, and `B` a divisor on `X` such that
`B - K` is ample. Then `H^i(X, 𝒪_X(B)) = 0` for every `i > 0`. -/
@[mmp "lem_km2c_kodaira_vanishing_dual"]
public theorem subsingleton_derivedCohomologyOverField_divisorialSheaf_of_isAmple_sub
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ} (K B : Divisor X)
    (hK : K.IsCanonicalDivisor f n) (hA : ∃ h : (B - K).IsCartier, (B - K).IsAmple h)
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj B.divisorialSheaf) i) := by
  obtain ⟨hC, hamp⟩ := hA
  have := hC.isInvertibleModule_divisorialSheaf
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_relativeDifferentialForms hsm hK
  have hv := subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple f hsm n
    hK.topologicalKrullDim_eq (B - K).divisorialSheaf hamp (n - i) (by omega)
  rw [subsingleton_dual_iff_subsingleton_exteriorPower_tensor f hsm n hK.topologicalKrullDim_eq,
    sub_sub_cancel] at hv
  refine (subsingleton_derivedCohomologyOverField_congr
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).mapIso eK.symm).app _ ≪≫
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm K).divisorialSheafTensorIso hC ≪≫
      eqToIso (by rw [add_sub_cancel])) i).1 hv

end MMP.Mori

end
