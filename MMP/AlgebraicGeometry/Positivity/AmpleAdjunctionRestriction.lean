module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso

/-!
# Restricting an adjoint ample `ℚ`-divisor to a smooth prime divisor

Let `Y` be a smooth projective variety over a field `k`, `F ⊂ Y` a smooth prime divisor,
`P` a Cartier divisor on `Y` and `B` a `ℚ`-divisor on `Y` of which `F` is not a component, such
that `P + B - F - K_Y` is ample. If `P_F` is a Cartier divisor on `F` with
`𝒪_F(P_F) ≅ 𝒪_Y(P)|_F`, then `P_F + B|_F - K_F` is ample. This is the adjunction
`(K_Y + F)|_F = K_F` combined with the fact that the restriction of an ample divisor is ample.

## Main results

* `MMP.Mori.QDivisor.isAmple_add_restrictPrimeDivisor_sub_of_isAmple`: the restriction statement.

## Implementation notes

The prime divisor `F` is a `PrimeDivisor Y`, regarded as the integral closed subscheme
`F.idealSheaf.subscheme` with inclusion `F.idealSheaf.subschemeι`; "`F` is smooth" is
`IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)`. The restriction `B|_F` is
`MMP.Mori.DivisorWithCoeffs.restrictPrimeDivisor`, and `𝒪_Y(P)|_F` is the pull-back of the
divisorial sheaf along the inclusion. Canonical divisors are `MMP.Mori.Divisor.IsCanonicalDivisor`,
of dimension `n + 1` on `Y` and `n` on `F`. The base field is arbitrary.

Write `E ↝ E'` when `𝒪_F(E') ≅ ι^* 𝒪_Y(E)`. This relation is additive and can be cancelled
(every invertible sheaf on the smooth variety `F` is divisorial, and isomorphic divisorial sheaves
on `F` come from linearly equivalent divisors). It holds for `(m B, (m B)|_F)`, for `(P, P_F)`
and, by adjunction, for `(K_Y + P + F, K_F + P_F)`. Combining these gives
`m (P + B - F - K_Y) ↝ m (P_F + B|_F - K_F)`, and the restriction of an ample invertible sheaf to
the closed subscheme `F` is ample.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.3, Step 5, and of Theorem 3.4, Step 6
-/

@[expose] public section

open CategoryTheory MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsProjectiveVariety

namespace MMP.FourfoldProofs.Km3aRestrictedAmpleAdjunctionProof

section Restricts

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {F : PrimeDivisor Y} [IsLocallyNoetherian F.idealSheaf.subscheme]
  [IsNormal F.idealSheaf.subscheme] [CompactSpace F.idealSheaf.subscheme]

/-- `E ↝ E'`: the divisorial sheaf of `E'` on `F` is the restriction of that of `E`. -/
private def Restricts (F : PrimeDivisor Y) [IsLocallyNoetherian F.idealSheaf.subscheme]
    [IsNormal F.idealSheaf.subscheme] (E : Divisor Y) (E' : Divisor F.idealSheaf.subscheme) :
    Prop :=
  Nonempty (E'.divisorialSheaf ≅
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj E.divisorialSheaf)

private theorem Restricts.add (hY : ∀ D : Divisor Y, D.IsCartier)
    (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier) {a b : Divisor Y}
    {a' b' : Divisor F.idealSheaf.subscheme} (ha : Restricts F a a') (hb : Restricts F b b') :
    Restricts F (a + b) (a' + b') := by
  obtain ⟨ea⟩ := ha
  obtain ⟨eb⟩ := hb
  exact ⟨((hF a').divisorialSheafTensorIso (hF b')).symm ≪≫
    MonoidalCategory.tensorIso ea eb ≪≫
    (Stacks.RelativeVeryAmple.pullbackTensorModulesIso F.idealSheaf.subschemeι _ _).symm ≪≫
    (Scheme.Modules.pullback F.idealSheaf.subschemeι).mapIso
      ((hY a).divisorialSheafTensorIso (hY b))⟩

/-- Cancellation: if `a + b ↝ X` and `a ↝ a'`, then `b ↝ X - a'`. -/
private theorem Restricts.cancel [IsIntegral F.idealSheaf.subscheme]
    (hY : ∀ D : Divisor Y, D.IsCartier) (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier)
    (hinv : ∀ L : F.idealSheaf.subscheme.Modules,
      Stacks.Ample.IsInvertibleModule F.idealSheaf.subscheme L →
        ∃ G : Divisor F.idealSheaf.subscheme, Nonempty (G.divisorialSheaf ≅ L))
    {a b : Divisor Y} {a' X : Divisor F.idealSheaf.subscheme}
    (h : Restricts F (a + b) X) (ha : Restricts F a a') : Restricts F b (X - a') := by
  have := (hY b).isInvertibleModule_divisorialSheaf
  obtain ⟨G, ⟨eG⟩⟩ := hinv ((Scheme.Modules.pullback F.idealSheaf.subschemeι).obj b.divisorialSheaf)
    inferInstance
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := Restricts.add hY hF ha ⟨eG⟩
  have hl : X.LinearlyEquivalent (a' + G) :=
    MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e ≪≫ e'.symm)
  have hl' : (X - a').LinearlyEquivalent G := by
    have := hl.add (Divisor.LinearlyEquivalent.refl (-a'))
    rwa [← sub_eq_add_neg, add_neg_cancel_comm] at this
  exact ⟨hl'.divisorialSheafIso ≪≫ eG⟩

/-- Positive multiples: if `a ↝ a'` then `j • a ↝ j • a'` for `j ≥ 1`. -/
private theorem Restricts.nsmul (hY : ∀ D : Divisor Y, D.IsCartier)
    (hF : ∀ D : Divisor F.idealSheaf.subscheme, D.IsCartier) {a : Divisor Y}
    {a' : Divisor F.idealSheaf.subscheme} (ha : Restricts F a a') {j : ℕ} (hj : 1 ≤ j) :
    Restricts F (j • a) (j • a') := by
  induction j, hj using Nat.le_induction with
  | base => simpa using ha
  | succ j _ ih => simpa [succ_nsmul] using ih.add hY hF ha

/-- The restriction of an ample divisor is ample: if `D ↝ D'` and `D` is ample, so is `D'`. -/
private theorem Restricts.isAmple {D : Divisor Y} {D' : Divisor F.idealSheaf.subscheme}
    (h : Restricts F D D') {hD : D.IsCartier} (hD' : D'.IsCartier) (hA : D.IsAmple hD) :
    D'.IsAmple hD' := by
  obtain ⟨e⟩ := h
  have := hD.isInvertibleModule_divisorialSheaf
  have := hD'.isInvertibleModule_divisorialSheaf
  exact Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple _ _ <|
    Scheme.Modules.isAmple_of_iso e.symm <| Scheme.Modules.isAmple_pullback_of_isClosedImmersion
      _ _ <| Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple Y _ hA

end Restricts

/-- The adjoint restriction: if `F` is not a component of `E` and `P ↝ P_F`, then
`m (P - F - K_Y) + E ↝ m (P_F - K_F) + E|_F`. -/
private theorem Restricts.adjoint {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (CommRingCat.of k)) [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsSmoothVariety k sY] (F : PrimeDivisor Y)
    [IsLocallyNoetherian F.idealSheaf.subscheme] [IsNormal F.idealSheaf.subscheme]
    [CompactSpace F.idealSheaf.subscheme] [IsSmoothVariety k (F.idealSheaf.subschemeι ≫ sY)]
    {n : ℕ} {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY (n + 1)) {KF : Divisor F.idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor (F.idealSheaf.subschemeι ≫ sY) n) {P : Divisor Y}
    (hP : P.IsCartier) {PF : Divisor F.idealSheaf.subscheme} (hPF : Restricts F P PF)
    {E : Divisor Y} (hEF : E.coeff F = 0) {m : ℕ} (hm : 1 ≤ m) :
    Restricts F (m • (P - Finsupp.single F 1 - KY) + E)
      (m • (PF - KF) + E.restrictPrimeDivisor F) := by
  have : IsIntegral F.idealSheaf.subscheme := F.integral
  have hsY : IsSmoothScheme sY := (isSmoothScheme_iff _).mpr inferInstance
  have hsF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY) :=
    (isSmoothScheme_iff _).mpr inferInstance
  obtain ⟨hcY, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  obtain ⟨hcF, -, -, -, hinv, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (F.idealSheaf.subschemeι ≫ sY)
  have hadj : Restricts F (KY + P + Finsupp.single F 1) (KF + PF) := by
    obtain ⟨eA⟩ := Divisor.nonempty_pullback_divisorialSheaf_iso_of_isCanonicalDivisor sY
      inferInstance hsY hKY F hsF hP
    obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hsF hKF
    obtain ⟨eP⟩ := hPF
    exact ⟨((hcF KF).divisorialSheafTensorIso (hcF PF)).symm ≪≫
      MonoidalCategory.tensorIso eK eP ≪≫ eA.symm⟩
  have hE : Restricts F E (E.restrictPrimeDivisor F) :=
    (Divisor.isCartier_restrictPrimeDivisor_of_isSmoothVariety k sY F E hEF).2.1
  have h : Restricts F (m • (KY + P + Finsupp.single F 1) + (m • (P - Finsupp.single F 1 - KY) + E))
      (m • PF + m • PF + E.restrictPrimeDivisor F) := by
    convert ((hPF.nsmul hcY hcF hm).add hcY hcF (hPF.nsmul hcY hcF hm)).add hcY hcF hE using 1
    module
  convert h.cancel hcY hcF hinv (hadj.nsmul hcY hcF hm) using 1
  module

end MMP.FourfoldProofs.Km3aRestrictedAmpleAdjunctionProof

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

namespace QDivisor

/-- **Restriction of an adjoint ample divisor to a smooth prime divisor.** Let `Y` be a smooth
projective variety of dimension `n + 1` over `k` with canonical divisor `K_Y`, `F` a prime divisor
of `Y` which is smooth over `k`, with canonical divisor `K_F`, `P` a Cartier divisor and `B` a
`ℚ`-divisor on `Y` with `B.coeff F = 0` such that `P + B - F - K_Y` is ample, and `P_F` a Cartier
divisor on `F` with `𝒪_F(P_F) ≅ ι^* 𝒪_Y(P)`. Then `P_F + B|_F - K_F` is ample. -/
@[mmp "lem_km3a_restricted_ample_adjunction"]
public theorem isAmple_add_restrictPrimeDivisor_sub_of_isAmple {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hY : IsSmoothScheme sY)
    (F : PrimeDivisor Y) [IsLocallyNoetherian F.idealSheaf.subscheme]
    [IsNormal F.idealSheaf.subscheme] [CompactSpace F.idealSheaf.subscheme]
    (hF : IsSmoothScheme (F.idealSheaf.subschemeι ≫ sY)) {n : ℕ}
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY (n + 1))
    {KF : Divisor F.idealSheaf.subscheme}
    (hKF : KF.IsCanonicalDivisor (F.idealSheaf.subschemeι ≫ sY) n)
    {P : Divisor Y} (hP : P.IsCartier) {B : QDivisor Y} (hBF : B.coeff F = 0)
    (hA : (Divisor.toQDivisor P + B - Divisor.toQDivisor (Finsupp.single F 1) -
      Divisor.toQDivisor KY).IsAmple)
    {PF : Divisor F.idealSheaf.subscheme} (_hPF : PF.IsCartier)
    (ePF : Nonempty (PF.divisorialSheaf ≅
      (Scheme.Modules.pullback F.idealSheaf.subschemeι).obj P.divisorialSheaf)) :
    (Divisor.toQDivisor PF + B.restrictPrimeDivisor F - Divisor.toQDivisor KF).IsAmple := by
  obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hA
  obtain ⟨E, rfl⟩ : ∃ E, D = m • (P - Finsupp.single F 1 - KY) + E :=
    ⟨_, (add_sub_cancel _ _).symm⟩
  have hE : Divisor.toQDivisor E = (m : ℚ) • B := by
    simp only [map_add, map_sub, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at hD
    linear_combination (norm := module) hD
  have hEF : E.coeff F = 0 := by
    have h := congrArg (fun Q : QDivisor Y => Q.coeff F) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hBF, smul_zero] at h
    exact_mod_cast h
  have : IsSmoothVariety k sY := (isSmoothVariety_iff k sY).2 ⟨inferInstance,
    (isSmoothScheme_iff _).mp hY⟩
  have : IsIntegral F.idealSheaf.subscheme := F.integral
  have : Smooth (F.idealSheaf.subschemeι ≫ sY) := (isSmoothScheme_iff _).mp hF
  have : IsSmoothVariety k (F.idealSheaf.subschemeι ≫ sY) := { toSmooth := inferInstance }
  obtain ⟨hcF, -⟩ :=
    Divisor.cartier_weil_dictionary_of_isSmoothVariety k (F.idealSheaf.subschemeι ≫ sY)
  refine ⟨m, hm, m • (PF - KF) + E.restrictPrimeDivisor F, ?_, hcF _,
    (MMP.FourfoldProofs.Km3aRestrictedAmpleAdjunctionProof.Restricts.adjoint sY F hKY hKF hP ePF hEF
      hm).isAmple _ hDa⟩
  rw [map_add, ← Divisor.restrictPrimeDivisor_toQDivisor E F hEF, hE,
    ← Int.cast_natCast (R := ℚ) m, Int.cast_smul_eq_zsmul,
    DivisorWithCoeffs.restrictPrimeDivisor_zsmul B F hBF]
  simp only [map_nsmul, map_sub, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
    Int.cast_natCast]
  module

end QDivisor

end MMP.Mori
