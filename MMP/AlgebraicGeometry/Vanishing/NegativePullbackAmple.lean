module

public import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehweg

/-!
# Vanishing of `H^j(X, 𝒪_X(-r f^*D))` on a resolution, for `D` ample

Let `Y` be a projective variety of dimension `n` over an algebraically closed field `k` of
characteristic zero, `f : X ⟶ Y` a projective resolution and `D` an ample Cartier divisor on `Y`.
Then `H^j(X, 𝒪_X(-r f^*D)) = 0` for every `j < n` and every `r > 0`.

For `r > 0` the divisor `r f^*D = f^*(rD)` is nef (its degree on a curve `C ⊆ X` is zero if
`f(C)` is a point and `deg(C → f(C)) (D · f(C)) > 0` otherwise) and big (`rD` is ample and `f`
is birational), so Kawamata–Viehweg vanishing
(`MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg`) on the smooth
projective variety `X` gives the vanishing.

## Main results

* `MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_zsmul_pullback`:
  `H^j(X, 𝒪_X(-r f^*D)) = 0` for `j < n` and `r > 0`.

## Implementation notes

* `Y` carries its structure morphism `sY : Y ⟶ Spec k` and `X` the composite `f ≫ sY`; a
  projective resolution is `MMP.Mori.IsSmoothResolution sY f` together with
  `AlgebraicGeometry.IsProjective f`.
* Divisors and the pull-back of a Cartier divisor (`MMP.Mori.Divisor.IsPullback`) are defined on
  normal schemes, so `Y` is normal; `f^*D` is any divisor `B` on `X` with
  `D.IsPullback f hDf B`, which is unique (`MMP.Mori.Divisor.IsPullback.eq`).
* `H^j(X, ℱ)` for `j : ℤ` is `Stacks.Duality.derivedCohomologyOverField` of `ℱ` placed in
  degree zero.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], proof of
  Lemma 5.12, equation (5.1).
-/

@[expose] public section

namespace MMP.FourfoldProofs.Km5dVanishingNegPullbackAmpleProof

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

/-- A birational morphism from a reduced scheme to an integral scheme has integral source. -/
private theorem isIntegral_of_isBirationalMorphism {X Y : Scheme.{0}} [IsReduced X]
    [IsIntegral Y] (f : X ⟶ Y) (hf : IsBirationalMorphism f) : IsIntegral X := by
  obtain ⟨e, -⟩ := hf
  haveI : IrreducibleSpace e.target := Subtype.irreducibleSpace
    ⟨e.dense_target.nonempty,
      (IrreducibleSpace.isIrreducible_univ Y).2.open_subset e.target.isOpen (Set.subset_univ _)⟩
  haveI : IrreducibleSpace e.source :=
    (Homeomorph.irreducibleSpace_iff (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e.iso))).mpr
      ‹_›
  haveI : IrreducibleSpace X := (irreducibleSpace_def X).mpr (show IsIrreducible Set.univ from
    e.dense_source.closure_eq ▸ (isIrreducible_iff_irreducibleSpace.mpr ‹_›).closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

section Scaling

variable {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  (sX : X ⟶ Spec (.of k))

/-- A positive multiple of a big divisor is big. -/
private theorem isBig_zsmul {D : Divisor X} (hD : D.IsBig k sX) {r : ℤ} (hr : 0 < r) :
    (r • D).IsBig k sX := by
  obtain ⟨d, hd, c, hc, k₀, hk⟩ := hD
  refine ⟨d, hd, c, hc, max k₀ 1, fun l hl => ?_⟩
  have hl1 : 1 ≤ l := le_of_max_le_right hl
  have h := hk (l * r) ((le_of_max_le_left hl).trans (le_mul_of_one_le_right (by omega) hr))
  rw [mul_smul] at h
  refine lt_of_le_of_lt ?_ h
  gcongr
  exact_mod_cast le_mul_of_one_le_right (by omega) hr

/-- If the `ℚ`-divisor of `B` is big, so is that of `r • B` for `r > 0`. -/
private theorem isBig_toQDivisor_zsmul {B : Divisor X}
    (hB : (Divisor.toQDivisor B).IsBig k sX) {r : ℤ} (hr : 0 < r) :
    (Divisor.toQDivisor (r • B)).IsBig k sX := by
  obtain ⟨m, hm, D₀, hD₀, hD₀c, hbig⟩ := hB
  exact ⟨m, hm, r • D₀, by rw [map_zsmul, map_zsmul, hD₀, smul_comm], hD₀c.zsmul _,
    isBig_zsmul sX hbig hr⟩

/-- If the `ℚ`-divisor of a Cartier divisor `B` is nef, so is that of `r • B` for `r : ℕ`. -/
private theorem isNef_toQDivisor_natCast_zsmul [QuasiCompact sX] {B : Divisor X}
    (hBc : B.IsCartier)
    (hB : (Divisor.toQDivisor B).IsNef k sX) (r : ℕ) :
    (Divisor.toQDivisor ((r : ℤ) • B)).IsNef k sX := by
  obtain ⟨_, h⟩ := (QDivisor.isNef_toQDivisor_iff B hBc).mp hB
  refine (QDivisor.isNef_toQDivisor_iff _ (hBc.zsmul _)).mpr ⟨hBc.zsmul _, fun C i _ _ _ hC => ?_⟩
  rw [Divisor.degreeOn_congr (natCast_zsmul B r) (hBc.zsmul _) (hBc.nsmul r),
    Divisor.degreeOn_nsmul' k sX i hC.le B hBc r]
  exact mul_nonneg (Int.natCast_nonneg r) (h C i hC)

end Scaling

end MMP.FourfoldProofs.Km5dVanishingNegPullbackAmpleProof

public section

open CategoryTheory AlgebraicGeometry MMP.FourfoldProofs.Km5dVanishingNegPullbackAmpleProof
open scoped Stacks.SmallDerivedModel

namespace MMP.Mori

/-- Let `Y` be a normal projective variety of dimension `n` over an algebraically closed field
`k` of characteristic zero, `f : X ⟶ Y` a projective resolution, `D` an ample Cartier divisor on
`Y` and `B = f^*D` its pull-back (`MMP.Mori.Divisor.IsPullback`). Then
`H^j(X, 𝒪_X(-r B)) = 0` for every `j < n` and every `r > 0`. -/
@[mmp "lem_km5d_vanishing_neg_pullback_ample"]
public theorem subsingleton_derivedCohomologyOverField_divisorialSheaf_neg_zsmul_pullback
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {n : ℕ} (hn : topologicalKrullDim Y = n)
    {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (f : X ⟶ Y) (hres : IsSmoothResolution sY f) (hproj : IsProjective f)
    (D : Divisor Y) (hDc : D.IsCartier) (hD : D.IsAmple hDc)
    (hDf : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp)
    (B : Divisor X) (hB : D.IsPullback f hDf B)
    (r : ℕ) (hr : 0 < r) (j : ℤ) (hj : j < n) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField (f ≫ sY)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (-((r : ℤ) • B)).divisorialSheaf) j) := by
  have hYv : AlgebraicGeometry.IsVariety k sY := inferInstance
  have hYp : IsProjectiveMorphism sY :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety k sY).isProjective
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsIntegral X := isIntegral_of_isBirationalMorphism f hres.isBirationalMorphism
  haveI := hres.isProper
  haveI := hDc.isInvertibleModule_divisorialSheaf
  have hfp : IsProjectiveMorphism f :=
    isProjectiveMorphism_of_isQuasiProjective f D.divisorialSheaf hD
      (isQuasiProjective_of_isProjective hproj)
  have hXp : IsProjectiveMorphism (f ≫ sY) := hfp.comp hYp
  have hXv : AlgebraicGeometry.IsVariety k (f ≫ sY) := {}
  haveI : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sY) := ⟨hXp⟩
  haveI : Smooth (f ≫ sY) := (isSmoothScheme_iff _).mp hres.isSmoothScheme
  have hBc : B.IsCartier := hB.isCartier hDc
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isBirationalMorphism (f ≫ sY) sY hXv hXp
    hYv hYp f rfl hfp hres.isBirationalMorphism D.divisorialSheaf hD 1 one_pos B hBc
    (hB.divisorialSheafIso (hBc := hDc)) (Divisor.toQDivisor B) (by simp)
  exact subsingleton_derivedCohomologyOverField_divisorialSheaf_neg (f ≫ sY)
    hres.isSmoothScheme
    (hn ▸ (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (f ≫ sY)
      hres.isBirationalMorphism).symm)
    ((r : ℤ) • B) (Divisor.toQDivisor ((r : ℤ) • B)) 0
    (isNef_toQDivisor_natCast_zsmul _ hBc hnef r)
    (isBig_toQDivisor_zsmul _ hbig (by exact_mod_cast hr))
    (DivisorWithCoeffs.isSNC_zero _) (fun _ => le_rfl) (fun _ => zero_lt_one)
    (by rw [add_zero]; exact .refl (QDivisor.isQCartier_toQDivisor (hBc.zsmul _))) j hj

end MMP.Mori

end

end
