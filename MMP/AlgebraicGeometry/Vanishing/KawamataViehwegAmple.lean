module

public import MMP.AlgebraicGeometry.Positivity.FinitePullbackAmple
public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero

/-!
# Kawamata–Viehweg vanishing for an ample `ℚ`-divisor

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero, and `B` a divisor on `X` which is numerically equivalent to `M + Δ`,
where `M` is an ample `ℚ`-divisor and `Δ = ∑ aᵢ Dᵢ` is a `ℚ`-divisor with simple normal
crossing support and coefficients `0 ≤ aᵢ < 1`. Then `H^i(X, 𝒪_X(-B)) = 0` for every `i < n`.

This is the case of the Kawamata–Viehweg theorem
(`MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg`) in which `M` is
ample. It follows from Kodaira vanishing by the covering trick: a finite cover `Z → X` on which
`B` pulls back to a divisor numerically equivalent to the ample pull-back of `M`, and whose
cohomology contains that of `𝒪_X(-B)` as a direct summand.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_of_isAmple`: the
  vanishing above.

## Implementation notes

The boundary `∑ aᵢ Dᵢ` with distinct prime divisors `Dᵢ` is a single `ℚ`-divisor `Δ`, and the
source's condition that the `Dᵢ` be smooth with snc sum is `MMP.Mori.DivisorWithCoeffs.IsSNC`
of `Δ`, asked of the components with nonzero coefficient; components with coefficient zero do
not contribute to `Δ`, and being snc passes to subsets of the components
(`MMP.Mori.DivisorWithCoeffs.IsSNC.of_support_subset`).

`H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree
zero; it is sheaf cohomology in degrees `i ≥ 0` and vanishes in negative degrees, so the
conclusion is stated for every integer `i < n`. The sheaf `𝒪_X(-B)` is the divisorial sheaf of
`-B`, invertible since `X` is smooth.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 3
-/

@[expose] public section

section

/-!
## Proof: Kawamata–Viehweg vanishing for an ample `ℚ`-divisor

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field of
characteristic zero and `B ≡ M + Δ` with `M` an ample `ℚ`-divisor and `Δ` an snc `ℚ`-divisor
with coefficients in `[0, 1)`. The covering trick
(`MMP.Mori.exists_isFinite_retract_cohomologyOverField_divisorialSheaf_neg`) gives a finite
surjective `p : Z ⟶ X` from a smooth projective variety and a divisor `B_Z ≡ p^*M` with
`H^i(X, 𝒪_X(-B))` a retract of `H^i(Z, 𝒪_Z(-B_Z))`. The divisor `B_Z` is Cartier and ample
(`MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_isPullback_of_isFinite`), so Kodaira
vanishing (`MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple`) gives
`H^i(Z, 𝒪_Z(-B_Z)) = 0` for `i < n`, and hence `H^i(X, 𝒪_X(-B)) = 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 3
-/

namespace MMP.FourfoldProofs.Km2cKawamataViehwegAmpleCaseProof

open CategoryTheory MMP.Mori
open AlgebraicGeometry hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- `H^m(X, ℱ) = 0` in negative degrees `m < 0`. -/
private theorem subsingleton_derivedCohomologyOverField_of_neg (F : X.Modules) {m : ℤ}
    (hm : m < 0) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) := by
  letI : Linear k X.Modules := Scheme.Modules.linearOverBase f
  letI : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  haveI := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) 0 m (-m) (by omega)
  haveI : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Stacks.Ample.unitModule X))
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) m) :=
    ⟨fun a b => by
      rw [DerivedCategory.TStructure.t.zero a 0 (-m) (by omega),
        DerivedCategory.TStructure.t.zero b 0 (-m) (by omega)]⟩
  exact (Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit f
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) m).some.toEquiv.subsingleton

/-- On a smooth projective variety, `H^i(X, 𝒪_X(-D)) = H^i(X, 𝒪_X(D)^∨)` for a divisor `D`,
since `𝒪_X(-D)` is the inverse of the invertible sheaf `𝒪_X(D)`. -/
private theorem subsingleton_divisorialSheaf_neg_iff_dualSheaf [MMP.Mori.IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X]
    (D : Divisor X) (hD : D.IsCartier) (i : ℤ) :
    haveI := hD.isInvertibleModule_divisorialSheaf
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (-D).divisorialSheaf) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.divisorialSheaf)) i) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  letI : HasDerivedCategory (ModuleCat.{0} k) := ModuleCat.hasDerivedCategory
  let e : (-D).divisorialSheaf ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf D.divisorialSheaf :=
    Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.sheaf.obj
      X.ringCatSheaf.property D.divisorialSheaf (-D).divisorialSheaf
      (hD.divisorialSheafTensorIso (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _) ≪≫
        eqToIso (congrArg Divisor.divisorialSheaf (add_neg_cancel D)) ≪≫
        Divisor.divisorialSheafZeroIso)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{0} k) i).mapIso
    ((derivedGlobalSectionsOver f).mapIso ((DerivedCategory.singleFunctor X.Modules 0).mapIso
      e))).toLinearEquiv.toEquiv.subsingleton_congr

/-- **Kodaira vanishing for divisors.** On a smooth projective variety of dimension `n` over an
algebraically closed field of characteristic zero, `H^i(X, 𝒪_X(-D)) = 0` for `i < n` and every
ample Cartier divisor `D`. -/
private theorem subsingleton_divisorialSheaf_neg_of_isAmple [IsAlgClosed k] [CharZero k]
    [MMP.Mori.IsProjectiveVariety k f] (hsm : IsSmoothScheme f) [IsLocallyNoetherian X]
    [CompactSpace X] [IsNormal X] {n : ℕ} (hn : topologicalKrullDim X = n) (D : Divisor X)
    (hD : D.IsCartier) (hamp : D.IsAmple hD) (i : ℤ) (hi : i < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (-D).divisorialSheaf) i) :=
  haveI := hD.isInvertibleModule_divisorialSheaf
  (subsingleton_divisorialSheaf_neg_iff_dualSheaf f hsm D hD i).2 <|
    subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple f hsm n hn _ hamp i hi

end MMP.FourfoldProofs.Km2cKawamataViehwegAmpleCaseProof

end

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

open MMP.FourfoldProofs.Km2cKawamataViehwegAmpleCaseProof in
/-- **Kawamata–Viehweg vanishing, ample case** (Kollár–Mori, proof of Theorem 2.64). Let `X` be
a smooth projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero and `B` a divisor on `X` numerically equivalent to `M + Δ`, where `M` is an
ample `ℚ`-divisor and `Δ` is a `ℚ`-divisor with simple normal crossing support whose
coefficients lie in `[0, 1)`. Then `H^i(X, 𝒪_X(-B)) = 0` for every `i < n`. -/
@[mmp "lem_km2c_kawamata_viehweg_ample_case"]
public theorem subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_of_isAmple
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProjectiveVariety k f] (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {n : ℕ} (hn : topologicalKrullDim X = n) (B : Divisor X) (M Δ : QDivisor X)
    (hM : M.IsAmple) (hΔ : Δ.IsSNC f) (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor B).NumericallyEquivalent k f (M + Δ)) (i : ℤ) (hi : i < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj (-B).divisorialSheaf) i) := by
  rcases lt_or_ge i 0 with hi0 | hi0
  · exact subsingleton_derivedCohomologyOverField_of_neg f _ hi0
  lift i to ℕ using hi0
  haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
  obtain ⟨Z, p, _, _, hZp, hZs, _, _, BZ, MZ, hMp, hpM, hBZ, hret⟩ :=
    exists_isFinite_retract_cohomologyOverField_divisorialSheaf_neg k f B M Δ hΔ
      (fun P => ⟨hΔ0 P, hΔ1 P⟩) hB
  haveI : MMP.Mori.IsProjectiveVariety k (p ≫ f) := hZp
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (p ≫ f)
  have hsmZ : IsSmoothScheme (p ≫ f) := (isSmoothScheme_iff _).2 hZs
  have hBZc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsmZ BZ
  haveI := subsingleton_divisorialSheaf_neg_of_isAmple (p ≫ f) hsmZ
    ((topologicalKrullDim_eq_of_isFinite_of_isDominant p).trans hn) BZ hBZc
    (QDivisor.isAmple_of_numericallyEquivalent_isPullback_of_isFinite f (p ≫ f) p rfl hM hMp hpM
      hBZ 1 one_pos BZ (by rw [Nat.cast_one, one_smul]) hBZc) i hi
  haveI := (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k (p ≫ f)
    (-BZ).divisorialSheaf i).toEquiv.subsingleton
  obtain ⟨r⟩ := hret i
  haveI := ((ModuleCat.mono_iff_injective r.i).1 inferInstance).subsingleton
  exact (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f
    (-B).divisorialSheaf i).symm.toEquiv.subsingleton

end MMP.Mori

end
