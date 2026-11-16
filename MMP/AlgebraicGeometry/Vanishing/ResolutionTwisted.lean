module

public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegAmple

/-!
# Twisted vanishing on a resolution

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero, `B` a divisor and `H` an ample divisor on `X`, and `f : Y ⟶ X` a birational morphism from
a smooth projective variety `Y` of dimension `n` such that `f^*B ≡ A + Δ`, where `A` is an ample
`ℚ`-divisor and `Δ = ∑ eⱼ Eⱼ` is a `ℚ`-divisor with simple normal crossing support and
coefficients `0 ≤ eⱼ < 1`. Then `H^q(Y, ω_Y ⊗ 𝒪_Y(f^*B + r f^*H)) = 0` for every `q > 0` and
every `r ≥ 0`, where `ω_Y = ⋀^n Ω_{Y/k}`.

This is the vanishing on the resolution in Kollár–Mori's proof of the Kawamata–Viehweg theorem
for nef and big divisors: `f^*(B + rH) ≡ (A + r f^*H) + Δ` with `A + r f^*H` ample, so
`MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg` and Serre duality
(`MMP.Mori.subsingleton_dual_iff_subsingleton_exteriorPower_tensor`) apply on `Y`.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback`:
  the vanishing above.

## Implementation notes

* The pull-backs `f^*B` and `f^*H` are divisors `fB`, `fH` on `Y` with
  `MMP.Mori.Divisor.IsPullback`; since `X` is smooth, `B` and `H` are Cartier and the pull-backs
  are unique (`MMP.Mori.Divisor.IsPullback.eq`), and `f^*(B + rH) = f^*B + r f^*H`
  (`MMP.Mori.Divisor.IsPullback.add`, `MMP.Mori.Divisor.IsPullback.zsmul`).
* The structure morphism of `Y` is `f ≫ sX`, so `f` is a morphism over `k`.
* `H^q(Y, ℱ)` for `q : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in degree
  zero, which is sheaf cohomology for `q ≥ 0`.
* The boundary `∑ eⱼ Eⱼ` with distinct prime divisors `Eⱼ` is a single `ℚ`-divisor `Δ` with
  `MMP.Mori.DivisorWithCoeffs.IsSNC`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

@[expose] public section

section

/-!
## Proof: Twisted vanishing on a resolution

Let `f : Y ⟶ X` be a birational morphism of smooth projective varieties over an algebraically
closed field of characteristic zero, `B` a divisor and `H` an ample divisor on `X`, and suppose
`f^*B ≡ A + Δ` with `A` an ample `ℚ`-divisor and `Δ` an snc `ℚ`-divisor with coefficients in
`[0, 1)`. Then `f^*(B + rH) ≡ (A + r f^*H) + Δ`, where `A + r f^*H` is ample because `f^*H` is
nef, so the Kawamata–Viehweg vanishing in the ample case and Serre duality on `Y` give
`H^q(Y, ω_Y ⊗ 𝒪_Y(f^*B + r f^*H)) = 0` for `q > 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

open CategoryTheory AlgebraicGeometry
open MMP.Mori hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km2cKvResolutionTwistedVanishingProof

/-- An ample invertible sheaf has nonnegative degree along every proper curve mapping to `T`. -/
private theorem degreeOn_nonneg_of_isAmple {k : Type} [Field k] {C T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] [LocallyOfFiniteType sT] (φ : C ⟶ T)
    [AlgebraicGeometry.IsCurve k (φ ≫ sT)] [IsProper (φ ≫ sT)] (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] (hL : Stacks.Ample.IsAmple T L) :
    0 ≤ degreeOn k sT φ (IsCurve.topologicalKrullDim_eq_one (f := φ ≫ sT)).le L := by
  by_cases hpt : ∃ x : T, Set.range φ = {x}
  · rw [degreeOn_eq_zero_of_range_eq_singleton sT φ L hpt]
  · rw [degreeOn_eq_degreeOver_mul sT φ L hpt]
    have : IsProper φ := IsProper.of_comp φ sT
    have : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    have : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hpt
    have h1 := isAmple_pullback_of_isFinite φ.imageι L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple T L).mpr hL)
    have := MMP.Mori.isInvertible_pullback_obj φ.imageι L
    have h2 := invertibleCurveDegree_pos_of_isAmple_of_isCurve k (φ.imageι ≫ sT)
      (topologicalKrullDim_image_le_one sT φ) _ h1
    exact mul_nonneg (by positivity) h2.le

/-- The pull-back of an ample Cartier divisor along a morphism from an integral scheme is nef. -/
private theorem isNef_of_isPullback_of_isAmple {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (f : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [QuasiCompact (f ≫ sX)] {G : Divisor X} (hGc : G.IsCartier) (hG : G.IsAmple hGc)
    {hGf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ G.supp}
    {G' : Divisor Y} (h : G.IsPullback f hGf G') :
    G'.IsNef k (f ≫ sX) := by
  have hG'c : G'.IsCartier := h.isCartier hGc
  refine ⟨hG'c, fun C i _ _ _ hC => ?_⟩
  have := hGc.isInvertibleModule_divisorialSheaf
  have := hG'c.isInvertibleModule_divisorialSheaf
  have : IsProper ((i ≫ f) ≫ sX) := by rw [Category.assoc]; infer_instance
  have : AlgebraicGeometry.IsCurve k ((i ≫ f) ≫ sX) := by
    rw [Category.assoc]
    exact { topologicalKrullDim_eq_one := hC }
  have h1 : G'.degreeOn k (f ≫ sX) i hC.le hG'c = degreeOn k sX (i ≫ f)
      (IsCurve.topologicalKrullDim_eq_one (f := (i ≫ f) ≫ sX)).le G.divisorialSheaf := by
    rw [← degreeOn_pullback_eq_degreeOn_comp (f ≫ sX) sX f i rfl]
    exact degreeOn_eq_of_iso k (f ≫ sX) i hC.le (h.divisorialSheafIso (hBc := hGc))
  rw [h1]
  exact degreeOn_nonneg_of_isAmple sX (i ≫ f) _ hG

/-- A Cartier divisor with a nef positive multiple is nef. -/
private theorem isNef_of_isNef_nsmul {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : D.IsCartier) {m : ℕ} (hm : 0 < m) (h : (m • D).IsNef k sX) :
    D.IsNef k sX := by
  refine ⟨hD, fun C i _ _ _ hC => ?_⟩
  have := h.2 C i hC
  rw [Divisor.degreeOn_nsmul' k sX i hC.le D hD m] at this
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using this) (by exact_mod_cast hm)

/-- A nonnegative multiple of a nef Cartier divisor is nef. -/
private theorem isNef_nsmul {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {D : Divisor X} (hD : D.IsNef k sX)
    (r : ℕ) : (r • D).IsNef k sX := by
  refine ⟨hD.1.nsmul r, fun C i _ _ _ hC => ?_⟩
  rw [Divisor.degreeOn_nsmul' k sX i hC.le D hD.1 r]
  exact mul_nonneg (by positivity) (hD.2 C i hC)

/-- **Ample plus nef is ample.** On a normal projective variety, the sum of an ample `ℚ`-divisor
and a nef Cartier divisor is ample. -/
private theorem isAmple_add_toQDivisor_of_isNef {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] [IsNormal X] [IsLocallyNoetherian X]
    [CompactSpace X] [QuasiCompact sX] {A : QDivisor X} (hA : A.IsAmple) {E : Divisor X}
    (hE : E.IsNef k sX) : (A + Divisor.toQDivisor E).IsAmple := by
  obtain ⟨a, ha, DA, hDA, hDAc, -⟩ := id hA
  have hAq : A.IsQCartier :=
    ⟨a, by exact_mod_cast ha.ne', ⟨DA, by rw [hDA, natCast_zsmul, Nat.cast_smul_eq_nsmul], hDAc⟩⟩
  have hD : Divisor.toQDivisor (DA + a • E) = (a : ℚ) • (A + Divisor.toQDivisor E) := by
    rw [map_add, hDA, map_nsmul, smul_add, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact ⟨a, ha, DA + a • E, hD, hDAc.add (hE.1.nsmul a),
    QDivisor.isAmple_of_numericallyEquivalent_add_of_isNef sX hA
      ((QDivisor.isNef_toQDivisor_iff E hE.1).2 hE)
      (QDivisor.NumericallyEquivalent.refl (hAq.add (QDivisor.isQCartier_toQDivisor hE.1)))
      a ha _ hD _⟩

/-- **Serre duality for divisors on a smooth projective variety.** For a divisor `D` on a smooth
projective variety `X` of dimension `n`, `H^i(X, 𝒪_X(-D)) = 0` if and only if
`H^{n-i}(X, ω_X ⊗ 𝒪_X(D)) = 0`. -/
private theorem subsingleton_divisorialSheaf_neg_iff {k : Type} [Field k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f]
    (hsm : IsSmoothScheme f) [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : Divisor X) (i : ℤ) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj (-D).divisorialSheaf) i) ↔
      Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} X.toRingedSpace.sheaf).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n)).obj
              D.divisorialSheaf)) (n - i)) := by
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  haveI := (hcart D).isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_divisorialSheaf_iso_dualSheaf_neg hcart (-D)
  rw [neg_neg] at e
  rw [← subsingleton_dual_iff_subsingleton_exteriorPower_tensor f hsm n hn]
  exact ((derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) i).mapIso
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso e)).toLinearEquiv.toEquiv.subsingleton_congr

end MMP.FourfoldProofs.Km2cKvResolutionTwistedVanishingProof

end

section

public section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.SmallDerivedModel
open MMP.FourfoldProofs.Km2cKvResolutionTwistedVanishingProof

namespace MMP.Mori

/-- **Twisted vanishing on a resolution** (Kollár–Mori, proof of Theorem 2.64). Let `X` be a smooth
projective variety over an algebraically closed field `k` of characteristic zero, `B` a divisor
and `H` an ample divisor on `X`, and `f : Y ⟶ X` a birational morphism from a smooth projective
variety `Y` of dimension `n` with `f^*B ≡ A + Δ`, where `A` is an ample `ℚ`-divisor and `Δ` a
`ℚ`-divisor with snc support and coefficients in `[0, 1)`. Then
`H^q(Y, ω_Y ⊗ 𝒪_Y(f^*B + r f^*H)) = 0` for all `q > 0` and `r ≥ 0`. -/
@[mmp "lem_km2c_kv_resolution_twisted_vanishing"]
public theorem subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] (hXsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {Y : Scheme.{0}} (f : Y ⟶ X) [IsProjectiveVariety k (f ≫ sX)] (hYsm : IsSmoothScheme (f ≫ sX))
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hf : IsBirationalMorphism f)
    {n : ℕ} (hn : topologicalKrullDim Y = n)
    (B H : Divisor X) (hH : (Divisor.toQDivisor H).IsAmple)
    (hBf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp)
    (hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp)
    (fB fH : Divisor Y) (hfB : B.IsPullback f hBf fB) (hfH : H.IsPullback f hHf fH)
    (A Δ : QDivisor Y) (hA : A.IsAmple) (hΔ : Δ.IsSNC (f ≫ sX))
    (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor fB).NumericallyEquivalent k (f ≫ sX) (A + Δ))
    (r : ℕ) (q : ℤ) (hq : 0 < q) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField (f ≫ sX)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (f ≫ sX)) n)).obj
            (fB + (r : ℤ) • fH).divisorialSheaf)) q) := by
  have hYv := ((AlgebraicGeometry.isProjectiveVariety_iff k (f ≫ sX)).1 ‹_›).1
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI := ((AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›).1.toIsSeparated
  haveI := ((AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›).1.toLocallyOfFiniteType
  haveI : IsDominant f := hf.isDominant
  have hcartY := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm
  -- `r f^*H` is nef: some multiple `m H` is an ample Cartier divisor, with nef pull-back `m f^*H`
  obtain ⟨m, hm, DH, hDH, hDHc, hDHamp⟩ := hH
  have hDHeq : DH = (m : ℤ) • H := Divisor.toQDivisor_injective (by
    rw [hDH, map_zsmul, natCast_zsmul]
    exact Nat.cast_smul_eq_nsmul ℚ m _)
  have hpb : DH.IsPullback f
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f DH)
      ((m : ℤ) • fH) :=
    (hfH.zsmul (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hXsm H) (m : ℤ) (fun Z =>
      MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z)).of_eq
        hDHeq.symm
  have hrnef : (r • fH).IsNef k (f ≫ sX) := isNef_nsmul _ (isNef_of_isNef_nsmul _ (hcartY fH) hm
    (by simpa only [natCast_zsmul] using isNef_of_isPullback_of_isAmple sX f hDHc hDHamp hpb)) r
  -- `f^*(B + rH) ≡ (A + r f^*H) + Δ`, with `A + r f^*H` ample
  have hnum : (Divisor.toQDivisor (fB + (r : ℤ) • fH)).NumericallyEquivalent k (f ≫ sX)
      ((A + Divisor.toQDivisor (r • fH)) + Δ) := by
    rw [add_right_comm, map_add, natCast_zsmul]
    exact numericallyEquivalent_add_right k (f ≫ sX) hB
      (QDivisor.isQCartier_toQDivisor (hcartY (r • fH)))
  -- Kawamata–Viehweg vanishing on `Y` and Serre duality
  have hS := (subsingleton_divisorialSheaf_neg_iff (f ≫ sX) hYsm hn _ (n - q)).1 <|
    subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_of_isAmple (f ≫ sX) hYsm hn _ _ Δ
      (isAmple_add_toQDivisor_of_isNef (f ≫ sX) hA hrnef) hΔ hΔ0 hΔ1 hnum (n - q) (by omega)
  rwa [sub_sub_cancel] at hS

end MMP.Mori

end

end
