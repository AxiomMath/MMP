module

public import MMP.AlgebraicGeometry.Vanishing.ResolutionHigherDirectImages
public import MMP.AlgebraicGeometry.Positivity.LogResolutionAmpleApproximation
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# Vanishing for `ω_X ⊗ 𝒪_X(B)` with `B` nef and big

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero, and `B` a divisor on `X` which is nef (`deg_C 𝒪_X(B) ≥ 0` for every
closed curve `C ⊆ X`) and big (`h⁰(X, 𝒪_X(mB)) > c mⁿ` for some `c > 0` and all large `m`).
Then `H^i(X, ω_X ⊗ 𝒪_X(B)) = 0` for every `i > 0`, where `ω_X = ⋀ⁿ Ω_{X/k}`.

The proof passes to a log resolution `f : Y ⟶ X` on which `f^*B ≡ A + Δ` with `A` ample and `Δ`
an snc `ℚ`-divisor with coefficients in `[0, 1)`, uses the vanishing
`MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback`
on `Y` together with the vanishing of `R^j f_* ω_Y` for `j > 0`, and concludes by
`f_* ω_Y ≅ ω_X` and the Leray spectral sequence.

## Main results

* `subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_of_isNef_of_isBig`:
  the vanishing above.

## Implementation notes

`H^i(X, ℱ)` for `i : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree
zero, which is sheaf cohomology for `i ≥ 0`. The sheaf `𝒪_X(B)` is the divisorial sheaf of `B`;
nefness of `B` (`MMP.Mori.Divisor.IsNef`) includes that `B` is Cartier, which on a smooth `X`
holds for every divisor.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

@[expose] public section

section

/-!
## Proof: Vanishing for `ω_X ⊗ 𝒪_X(B)` with `B` nef and big

Let `X` be a smooth projective variety of dimension `n` over an algebraically closed field `k`
of characteristic zero and `B` a nef and big divisor on `X`. Then
`H^i(X, ω_X ⊗ 𝒪_X(B)) = 0` for `i > 0`.

There is a log resolution `g : Y ⟶ X`, an effective snc `ℚ`-divisor `E'` and ample `A'_N` with
`g^*B ≡ A'_N + (1/N) E'` for all `N > 0`; `Y` is projective, being proper over `k` with an
ample invertible sheaf. For `N` larger than every coefficient of `E'`, `Δ = (1/N) E'` has
coefficients in `[0, 1)`, so `R^j g_* ω_Y = 0` for `j > 0` and, by the projection formula,
`R^j g_*(ω_Y ⊗ g^*𝒪_X(B)) = 0`. The Leray spectral sequence collapses:
`H^i(Y, ω_Y ⊗ 𝒪_Y(g^*B)) ≅ H^i(X, g_* ω_Y ⊗ 𝒪_X(B))`. The left side vanishes for `i > 0`, and
`g_* ω_Y ≅ ω_X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.Mori hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km2cKvNefBigLineBundleProof

/-- Vanishing of hypercohomology of `ℱ[0]` over `k` is vanishing of the sheaf cohomology
`Hᵐ(X, ℱ)`. -/
private theorem subsingleton_derivedCohomologyOverField_iff_isZero {k : Type} [Field k]
    {X : Scheme.{0}} (s : X ⟶ Spec (.of k)) (M : X.Modules) (m : ℕ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField s
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) (m : ℤ)) ↔
      IsZero ((Hfunctor X.ringCatSheaf ⊤ m).obj M) := by
  rw [← (Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k s M
      m).toLinearEquiv.toEquiv.subsingleton_congr,
    (cohomologyOverFieldAddEquivHgroup k s M m).toEquiv.subsingleton_congr]
  exact ⟨fun _ => AddCommGrpCat.isZero_of_subsingleton _, AddCommGrpCat.subsingleton_of_isZero⟩

/-- Twisting by the pull-back of an invertible sheaf preserves the vanishing of a higher direct
image: by the projection formula `R^q g_*(ℳ ⊗ g^*ℒ) ≅ R^q g_* ℳ ⊗ ℒ`. -/
private theorem isZero_rightDerived_pushforward_tensor_pullback {X Y : Scheme.{0}} (g : Y ⟶ X)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {M : Y.Modules} {q : ℕ}
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived q).obj M)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived q).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
        M).obj ((Scheme.Modules.pullback g).obj L))) := by
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 inferInstance
  haveI : (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules X L).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X _
  exact ((Functor.map_isZero (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules
      X L) (h.of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ q).app M).symm)).of_iso
    (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso g L M q)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _)

/-- The projection formula in degree zero: `g_*(ℳ ⊗ g^*ℒ) ≅ g_* ℳ ⊗ ℒ`. -/
private noncomputable def pushforwardTensorPullbackIso {X Y : Scheme.{0}} (g : Y ⟶ X)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (M : Y.Modules) :
    (Scheme.Modules.pushforward g).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
          M).obj ((Scheme.Modules.pullback g).obj L)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
        ((Scheme.Modules.pushforward g).obj M)).obj L :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 inferInstance
  let e0 := (Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf
  let e1 := (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) 0)
  (e0.app _).symm ≪≫ e1.app _ ≪≫
    Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso g L M ((0 : ℕ) : ℤ) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).mapIso
      ((e1.app M).symm ≪≫ e0.app M)).app L

/-- For `N` exceeding every coefficient of a nonnegative `ℚ`-valued finsupp `E`, the
coefficients of `N⁻¹ • E` lie in `[0, 1)`. -/
private theorem exists_inv_smul_mem_Ico {α : Type*} (E : α →₀ ℚ) (hE : ∀ a, 0 ≤ E a) :
    ∃ N : ℕ, 0 < N ∧ ∀ a, 0 ≤ ((N : ℚ)⁻¹ • E) a ∧ ((N : ℚ)⁻¹ • E) a < 1 := by
  refine ⟨⌈∑ a ∈ E.support, E a⌉₊ + 1, Nat.succ_pos _, fun a => ?_⟩
  have hle : E a ≤ ∑ a ∈ E.support, E a := by
    by_cases ha : a ∈ E.support
    · exact Finset.single_le_sum (fun a _ => hE a) ha
    · rw [Finsupp.notMem_support_iff.1 ha]
      exact Finset.sum_nonneg fun a _ => hE a
  rw [Finsupp.smul_apply, smul_eq_mul]
  refine ⟨mul_nonneg (by positivity) (hE a), (inv_mul_lt_one₀ (by positivity)).2 ?_⟩
  push_cast
  linarith [Nat.le_ceil (∑ a ∈ E.support, E a)]

/-- A projective variety carries an ample Cartier divisor. -/
private theorem exists_isCartier_isAmple {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] :
    ∃ H : Divisor X, ∃ hH : H.IsCartier, H.IsAmple hH := by
  have hX := (AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›
  haveI : IsIntegral X := hX.1.toIsIntegral
  obtain ⟨-, L, hLinv, hLamp⟩ :=
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX hX.2.isHQuasiProjective
  have hL : Stacks.Ample.IsAmple X L :=
    Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sX L hLamp
  obtain ⟨I, hI, -, -, n, hn, ⟨eX⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hL isClosed_empty
      (Set.notMem_empty (genericPoint X))
  obtain ⟨H, -, hHc, ⟨eH⟩, -⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor I hI
  haveI := hHc.isInvertibleModule_divisorialSheaf
  exact ⟨H, hHc, (Stacks.RelativeVeryAmple.isAmple_congr _ _ (eX ≪≫ eH.symm)).mp
    (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hL)⟩

end MMP.FourfoldProofs.Km2cKvNefBigLineBundleProof

end

section

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.FourfoldProofs.Km2cKvNefBigLineBundleProof
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- **Vanishing for nef and big divisors** (Kollár–Mori, proof of Theorem 2.64). Let `X` be a
smooth projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero and `B` a nef and big divisor on `X`. Then `H^i(X, ω_X ⊗ 𝒪_X(B)) = 0` for
every `i > 0`, where `ω_X = ⋀ⁿ Ω_{X/k}`. -/
@[mmp "lem_km2c_kv_nef_big_line_bundle"]
public theorem
    subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_of_isNef_of_isBig
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} (hn : topologicalKrullDim X = n)
    (B : Divisor X) (hnef : B.IsNef k f) (hbig : B.IsBig k f) (i : ℤ) (hi : 0 < i) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
            B.divisorialSheaf)) i) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k f := inferInstance
  have hX := (AlgebraicGeometry.isProjectiveVariety_iff k f).1 ‹_›
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : QuasiCompact f := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hX.2
  -- the log resolution `g : Y ⟶ X` and the ample approximation `g^*B ≡ A'_N + N⁻¹ • E'`
  obtain ⟨Y, g, hg, _, _, _, hBg, gB, E', A', hgB, hE'0, hE'snc, hA'⟩ :=
    exists_isLogResolution_numericallyEquivalent_isAmple_add_smul f B hnef hbig 0
  obtain ⟨hYN, hdim, -⟩ := hg.toIsSmoothResolution.isNormalVariety ⟨hX.1, inferInstance⟩
  have hgb : IsBirationalMorphism g := hg.isBirationalMorphism
  haveI : IsProper g := hg.isProper
  have hYsm : IsSmoothScheme (g ≫ f) := hg.isSmoothScheme
  haveI : AlgebraicGeometry.IsVariety k (g ≫ f) := hYN.1
  -- `Y` is projective, being proper and carrying an ample invertible sheaf
  haveI : AlgebraicGeometry.IsProjectiveVariety k (g ≫ f) := by
    obtain ⟨⟨m, -, D, -, hDc, hDa⟩, -⟩ := hA' 1 one_pos
    haveI := hDc.isInvertibleModule_divisorialSheaf
    exact (AlgebraicGeometry.isProjectiveVariety_iff k _).2 ⟨hYN.1,
      Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.isProjectiveMorphism_of_isAmple _ _ hDa⟩
  have hnY : topologicalKrullDim Y = n := hdim.trans hn
  -- `Δ = N⁻¹ • E'` is snc with coefficients in `[0, 1)`
  obtain ⟨N, hNpos, hΔ⟩ := exists_inv_smul_mem_Ico E' hE'0
  obtain ⟨hA, hB⟩ := hA' N hNpos
  have hΔsnc : ((N : ℚ)⁻¹ • E').IsSNC (g ≫ f) := hE'snc.of_support_subset Finsupp.support_smul
  -- `R^q g_* ω_Y = 0` for `q > 0`
  have hR := fun q hq => isZero_rightDerived_pushforward_exteriorPower_of_numericallyEquivalent
    f hsm g hYsm hgb hnY B hBg gB hgB (A' N) _ hA hΔsnc (fun E => (hΔ E).1) (fun E => (hΔ E).2)
      hB q hq
  -- `H^i(Y, ω_Y ⊗ 𝒪_Y(g^*B)) = 0`, the vanishing on `Y` with an ample `H` on `X` and `r = 0`
  obtain ⟨H, hHc, hHamp⟩ := exists_isCartier_isAmple f
  haveI : IsDominant g := hgb.isDominant
  have hHg : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ H.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g H Z
  obtain ⟨gH, hgH⟩ := hHc.exists_isPullback hHg
  have hT := subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback
    f hsm g hYsm hgb hnY B H ⟨1, one_pos, H, by simp, hHc, hHamp⟩ hBg hHg gB gH hgB hgH (A' N) _
      hA hΔsnc (fun E => (hΔ E).1) (fun E => (hΔ E).2) hB 0 i hi
  rw [Nat.cast_zero, zero_smul, add_zero] at hT
  -- transport to `X` along the Leray isomorphism and `g_* ω_Y ≅ ω_X`
  have hBc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm B
  haveI := hBc.isInvertibleModule_divisorialSheaf
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  replace hT := (subsingleton_derivedCohomologyOverField_iff_isZero _ _ m).1 hT
  refine (subsingleton_derivedCohomologyOverField_iff_isZero _ _ m).2 ?_
  set TY := Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf
  set TX := Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf
  set ωY := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (g ≫ f)) n
  have eω : (Scheme.Modules.pushforward g).obj ωY ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n := by
    haveI : Smooth f := (isSmoothScheme_iff f).1 hsm
    haveI : Smooth (g ≫ f) := (isSmoothScheme_iff _).1 hYsm
    haveI : SmoothOfRelativeDimension n f :=
      MMP.Intersection.smoothOfRelativeDimension_of_isVariety f n hn
    exact (@asIso _ _ _ _ _ (isIso_homEquiv_relativeDifferentialFormsMap_of_isBirationalMorphism
      f (g ≫ f) n g hgb rfl)).symm
  exact ((hT.of_iso ((Hfunctor Y.ringCatSheaf ⊤ m).mapIso
      ((TY.obj ωY).mapIso (hgB.divisorialSheafIso (hBc := hBc)).symm))).of_iso
    (Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages g
      (fun q hq => isZero_rightDerived_pushforward_tensor_pullback g _ (hR q hq)) m).symm).of_iso
    ((Hfunctor X.ringCatSheaf ⊤ m).mapIso
      (pushforwardTensorPullbackIso g B.divisorialSheaf ωY ≪≫ (TX.mapIso eω).app _).symm)

end MMP.Mori

end

end
