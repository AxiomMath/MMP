module

public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback

/-!
# Ampleness of a `ℚ`-divisor numerically equivalent to a finite pull-back of an ample one

Let `p : Z ⟶ X` be a finite surjective morphism of normal projective varieties over a field `k`
and `M` an ample `ℚ`-divisor on `X`. Choose `m > 0` with `mM` an ample Cartier divisor `D_M`.
The pull-back `p^* D_M = m p^*M` is Cartier with `𝒪_Z(p^* D_M) ≅ p^* 𝒪_X(D_M)`, which is ample
as the pull-back of an ample invertible sheaf along a finite morphism; so `p^*M` is ample.
Ampleness of `ℚ`-Cartier `ℚ`-divisors being a numerical property, every `ℚ`-divisor
`B_Z ≡ p^*M` on `Z` is ample: `𝒪_Z(e B_Z)` is ample for every integer `e > 0` such that
`e B_Z` is Cartier.

## Main results

* `MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_isPullback_of_isFinite`

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 2.64
* [R. Hartshorne, *Algebraic geometry*][Har77], III Ex. 5.7(d)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori.QDivisor

/-- The pull-back of an ample `ℚ`-divisor along a finite morphism is ample. -/
private theorem IsPullback.isAmple_of_isFinite {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    [IsNormal X] [IsNormal Z] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [CompactSpace X] [CompactSpace Z]
    (p : Z ⟶ X) [IsFinite p] {M : QDivisor X} (hM : M.IsAmple)
    (hMp : ∀ C : irreducibleComponents Z, p (componentGenericPoint Z C) ∉ M.supp)
    {P : QDivisor Z} (hP : M.IsPullback p hMp P) : P.IsAmple := by
  obtain ⟨m, hm, DM, hDM, hDMc, hamp⟩ := hM
  have hDMz : Divisor.toQDivisor DM = (m : ℤ) • M := by
    rw [← Int.cast_smul_eq_zsmul ℚ]; exact_mod_cast hDM
  obtain ⟨D', hD', hpb⟩ := hP m hm DM hDMz hDMc
  have hD'c : D'.IsCartier := hpb.pullback_eq hDMc ▸ hDMc.isCartier_pullback _ _
  refine ⟨m, hm, D', by rw [hD', ← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl, hD'c, ?_⟩
  obtain ⟨iso⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hDMc p fun C hC => hMp C <| by
    rwa [QDivisor.supp_eq_of_toQDivisor_eq (m := (m : ℤ)) (by exact_mod_cast hm.ne') hDMz] at hC
  rw [hpb.pullback_eq hDMc] at iso
  haveI := hDMc.isInvertibleModule_divisorialSheaf
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ iso.symm).mp <|
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple Z _).mp <|
      isAmple_pullback_of_isFinite p _ <|
        (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).mpr hamp

/-- Let `p : Z ⟶ X` be a finite surjective morphism of normal projective varieties over `k`,
`M` an ample `ℚ`-divisor on `X` with pull-back `P = p^*M`, and `B` a `ℚ`-divisor on `Z`
numerically equivalent to `P`. Then `B` is ample: for every integer `e > 0` and every Cartier
divisor `D` with `D = e B`, the invertible sheaf `𝒪_Z(D)` is ample. -/
@[mmp "lem_km2c_finite_pullback_ample"]
public theorem isAmple_of_numericallyEquivalent_isPullback_of_isFinite {k : Type} [Field k]
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] [IsProjectiveVariety k sZ] [IsNormal X] [IsNormal Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] [CompactSpace X] [CompactSpace Z]
    (p : Z ⟶ X) (hp : p ≫ sX = sZ) [IsFinite p] [Surjective p]
    {M : QDivisor X} (hM : M.IsAmple)
    (hMp : ∀ C : irreducibleComponents Z, p (componentGenericPoint Z C) ∉ M.supp)
    {P : QDivisor Z} (hP : M.IsPullback p hMp P)
    {B : QDivisor Z} (hB : B.NumericallyEquivalent k sZ P)
    (e : ℕ) (he : 0 < e) (D : Divisor Z) (hD : Divisor.toQDivisor D = (e : ℚ) • B)
    (hDc : D.IsCartier) :
    D.IsAmple hDc :=
  isAmple_of_numericallyEquivalent_add_of_isNef sZ (hP.isAmple_of_isFinite p hM hMp)
    ⟨isQCartier_zero, fun _ _ _ _ _ _ => (MMP.Fourfold.intersectionNumber_zero ..).ge⟩
    (by rwa [add_zero]) e he D hD hDc

end MMP.Mori.QDivisor
