module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FormalLifting
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle

/-!
# Formal algebraization of line bundles on the generic fibre

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), `A = 𝒪_{Y,η_T}` the
local ring of `Y` at the generic point of `T`, with maximal ideal `𝔪`, `Z = Ỹ ×_Y Spec A`
(`MMP.Fourfold.pointSettingLocalization`) and `F_n = Z ×_A A/𝔪^{n+1}`
(`MMP.Fourfold.pointSettingThickening`). Every line bundle `L` on `F_0` is the restriction of a
line bundle `L̂` on the base change `Z_Â = Z ×_A Â` of `Z` to the `𝔪`-adic completion `Â` of `A`,
along the closed immersion `F_0 ⟶ Z_Â` induced by `Â ⟶ Â/𝔪Â = A/𝔪`.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_isInvertible_pullback_iso`

## Implementation notes

* The completion `Â` is `AdicCompletion 𝔪 A`. The map `F_0 ⟶ Z_Â` is the identity on `Z` and,
  on the second factor, the spectrum of the projection `AdicCompletion.evalₐ 𝔪 1 : Â ⟶ A/𝔪`,
  so the restriction of `L̂` to `F_0` is its pull-back along that map.
* A line bundle is an invertible module (`SheafOfModules.IsInvertible`), and "is the restriction
  of" is an isomorphism of modules on `F_0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori

namespace MMP.Fourfold.FormalAlgebraization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Completion

variable (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The kernel of `Â ⟶ R/𝔪^n` is `𝔪̂^n`. -/
private theorem ker_evalₐ_eq_pow (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom =
      IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n := by
  have hk := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  ext x
  rw [RingHom.mem_ker]
  conv_rhs => rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map, hk,
    LinearMap.mem_ker]
  have eq : IsLocalRing.maximalIdeal R ^ n • (⊤ : Ideal R) = IsLocalRing.maximalIdeal R ^ n := by
    simp
  change AdicCompletion.evalₐ _ n x = 0 ↔ _
  rw [← AdicCompletion.factor_eval_eq_evalₐ (h := le_of_eq eq)]
  exact map_eq_zero_iff _ (Ideal.quotEquivOfEq eq).injective

/-- The isomorphism `Â/𝔪̂^n ≅ R/𝔪^n` induced by `AdicCompletion.evalₐ`. -/
private noncomputable def quotientPowEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n ≃+*
      R ⧸ IsLocalRing.maximalIdeal R ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ_eq_pow R n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ _ n))

end Completion

/-- The evaluations `Â ⟶ R/I^{n+1}` are compatible with the projections
`R/I^{n+2} ⟶ R/I^{n+1}`. -/
private theorem factor_evalₐ_succ {R : Type} [CommRing R] (I : Ideal R) (n : ℕ)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
        I ^ (n + 1 + 1) ≤ I ^ (n + 1)) (AdicCompletion.evalₐ I (n + 1 + 1) x) =
      AdicCompletion.evalₐ I (n + 1) x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ (h := by simp),
    ← AdicCompletion.factor_eval_eq_evalₐ (h := by simp), AdicCompletion.eval_apply,
    AdicCompletion.eval_apply, ← x.prop (Nat.le_succ (n + 1))]
  generalize x.val (n + 1 + 1) = z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [AdicCompletion.transitionMap_ideal_mk]
  exact (congrArg _ (Submodule.factor_mk _ y)).trans
    ((Ideal.Quotient.factor_mk _ y).trans (Submodule.factor_mk _ y).symm)

section Tower

variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {X : Scheme.{0}}
  (g : X ⟶ Spec (.of R))

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "R̂" => AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- The thickening `X ×_R R/𝔪^{n+1}` of the closed fibre of `g`. -/
private noncomputable abbrev thickening (n : ℕ) : Scheme.{0} :=
  pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))

/-- The base change `X ×_R R̂` of `g` to the completion. -/
private noncomputable abbrev completion : Scheme.{0} :=
  pullback g (Spec.map (CommRingCat.ofHom (algebraMap R R̂)))

/-- The map `X ×_R R/𝔪^{n+1} ⟶ X ×_R R̂` induced by `R̂ ⟶ R/𝔪^{n+1}`. -/
private noncomputable def thickeningToCompletion (n : ℕ) : thickening g n ⟶ completion g :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (n + 1)).toRingHom)) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by
      rw [Category.comp_id]
      exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
        ((AdicCompletion.evalₐ 𝔪 (n + 1)).commutes x).symm))).trans (Spec.map_comp _ _))

/-- The map `X ×_R R/𝔪^{n+1} ⟶ Spec (R̂/𝔪̂^{n+1})` through `quotientPowEquiv`. -/
private noncomputable def thickeningToAdic (n : ℕ) :
    thickening g n ⟶ adicThickening R̂ (IsLocalRing.maximalIdeal R̂) n :=
  pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (quotientPowEquiv R (n + 1)).toRingHom)

/-- The closed immersion `X ×_R R/𝔪^{n+1} ⟶ X ×_R R/𝔪^{n+2}`. -/
private noncomputable def thickeningSucc (n : ℕ) : thickening g n ⟶ thickening g (n + 1) :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : 𝔪 ^ (n + 1 + 1) ≤ 𝔪 ^ (n + 1)))))
    (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm) (by
      rw [Category.comp_id, ← Spec.map_comp]
      rfl)

/-- The thickening maps commute with the maps to the completion. -/
private theorem thickeningSucc_comp (n : ℕ) :
    thickeningSucc g n ≫ thickeningToCompletion g (n + 1) = thickeningToCompletion g n := by
  apply pullback.hom_ext
  · simp [thickeningSucc, thickeningToCompletion]
  · simp only [thickeningSucc, thickeningToCompletion, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact factor_evalₐ_succ 𝔪 n x

/-- The thickening `X ×_R R/𝔪^{n+1}` is the adic thickening `X_R̂ ×_R̂ R̂/𝔪̂^{n+1}`. -/
private theorem isPullback_thickeningToCompletion (n : ℕ) :
    IsPullback (thickeningToCompletion g n) (thickeningToAdic g n) (pullback.snd _ _)
      (adicThickeningι R̂ (IsLocalRing.maximalIdeal R̂) n) := by
  let e := quotientPowEquiv R (n + 1)
  haveI : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have hbot : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))
      (Spec.map (CommRingCat.ofHom e.toRingHom)) (𝟙 _)
      (adicThickeningι R̂ (IsLocalRing.maximalIdeal R̂) n ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R̂))) :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.comp_id, adicThickeningι, ← Spec.map_comp, ← Spec.map_comp]
      rfl⟩
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback _ _)
  · rw [thickeningToCompletion, pullback.lift_fst, Category.comp_id]
    exact (IsPullback.of_hasPullback g _).paste_vert hbot
  · rw [thickeningToCompletion, pullback.lift_snd, thickeningToAdic, Category.assoc,
      adicThickeningι, ← Spec.map_comp]
    rfl

/-- The thickenings `X ×_R R/𝔪^{n+1}` form a cartesian tower over the adic thickenings of `R̂`. -/
private theorem isPullback_thickeningSucc (n : ℕ) :
    IsPullback (thickeningSucc g n) (thickeningToAdic g n) (thickeningToAdic g (n + 1))
      (adicThickeningSucc R̂ (IsLocalRing.maximalIdeal R̂) n) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_thickeningToCompletion g (n + 1))
  · rw [thickeningSucc_comp, adicThickeningSucc_ι]
    exact isPullback_thickeningToCompletion g n
  · simp only [thickeningSucc, thickeningToAdic, pullback.lift_snd_assoc, Category.assoc,
      adicThickeningSucc, ← Spec.map_comp]
    congr 2
    ext z
    exact factor_evalₐ_succ 𝔪 n z

end Tower

/-- **Algebraization of a compatible system of line bundles.** Over a projective
`fX : X ⟶ Spec A` with `A` an `I`-adically complete noetherian ring, a compatible system of
invertible modules on a cartesian tower of thickenings `X_n = X ×_A A/I^{n+1}` is the system of
restrictions of one invertible module on `X`. -/
private theorem exists_isInvertibleModule_of_compatible_tower (A : Type) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{0}}
    {fX : X ⟶ Spec (.of A)} (hfX : IsProjectiveMorphism fX) {Xn : ℕ → Scheme.{0}}
    (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (k : ∀ n, Xn n ⟶ X) (hk : ∀ n, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n))
    (Ls : ∀ n, (Xn n).Modules) (hLs : ∀ n, Stacks.Ample.IsInvertibleModule (Xn n) (Ls n))
    (φ : ∀ n, (Scheme.Modules.pullback (i n)).obj (Ls (n + 1)) ≅ Ls n) :
    ∃ (M : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X M),
      Nonempty ((Scheme.Modules.pullback (k 0)).obj M ≅ Ls 0) := by
  haveI := isProper_of_isProjectiveMorphism fX hfX
  obtain ⟨M, hcoh, e, -⟩ :=
    Stacks.AmpleFormalSystemLineBundle.exists_coherent_of_restriction_isEquivalence A I fX
      q i k hk hkcart Ls hLs φ
      (Stacks.AmpleFormalSystemTheorem.adicTowerModuleAlgebraization_of_canonicalTower A I q i
        hcart (Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization A I)
        fX hfX k hk hkcart)
  exact ⟨M, Stacks.AdicTowerInvert.adicTowerInvertibility A I q fX hfX k hkcart M hcoh
    (fun n ↦ Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_of_iso (e n) (hLs n)),
    ⟨(e 0).symm⟩⟩

end MMP.Fourfold.FormalAlgebraization

namespace MMP.Fourfold.IsLocalSetting

open FormalAlgebraization in
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
/-- In a local setting `(Y, Θ, T, π)`, with `A = 𝒪_{Y,η_T}`, `Z = Ỹ ×_Y Spec A` and
`F_0 = Z ×_A A/𝔪`, every line bundle `L` on `F_0` is the restriction of a line bundle `L̂` on
`Z ×_A Â`, `Â` the `𝔪`-adic completion of `A`, along the map `F_0 ⟶ Z ×_A Â` induced by
`Â ⟶ A/𝔪`. -/
@[mmp "lem_oai4_c2_formal_algebraization"]
public theorem exists_isInvertible_pullback_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π)
    (L : (pointSettingThickening π (localSettingGenericPoint T) 0).Modules)
    [SheafOfModules.IsInvertible (pointSettingThickening π (localSettingGenericPoint T) 0).presheaf
      (pointSettingThickening π (localSettingGenericPoint T) 0).ringCatSheaf.2 L] :
    let A := Y.presheaf.stalk (localSettingGenericPoint T)
    let 𝔪 := IsLocalRing.maximalIdeal A
    let ZA : Scheme.{0} := pullback (pullback.snd π (Y.fromSpecStalk (localSettingGenericPoint T)))
      (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion 𝔪 A))))
    let ι : pointSettingThickening π (localSettingGenericPoint T) 0 ⟶ ZA :=
      pullback.map _ _ _ _ (𝟙 _)
        (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ 𝔪 (0 + 1)).toRingHom)) (𝟙 _)
        (by simp) (by
          rw [Category.comp_id]
          exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
            ((AdicCompletion.evalₐ 𝔪 (0 + 1)).commutes x).symm))).trans (Spec.map_comp _ _))
    ∃ (Lh : ZA.Modules) (_ : SheafOfModules.IsInvertible ZA.presheaf ZA.ringCatSheaf.2 Lh),
      Nonempty ((Scheme.Modules.pullback ι).obj Lh ≅ L) := by
  intro A 𝔪 ZA ι
  let g : _ ⟶ Spec (.of A) := pullback.snd π (Y.fromSpecStalk (localSettingGenericPoint T))
  obtain ⟨Ls, hLs, rfl, hφ⟩ := exists_isInvertible_pullback_thickening_iso h L
  exact exists_isInvertibleModule_of_compatible_tower (AdicCompletion 𝔪 A) _
    ((h.isResolution.2.2.2.1.baseChange _).baseChange _) (thickeningToAdic g) (thickeningSucc g)
    (isPullback_thickeningSucc g) (thickeningToCompletion g) (thickeningSucc_comp g)
    (isPullback_thickeningToCompletion g) Ls hLs (fun n ↦ (hφ n).some)

end MMP.Fourfold.IsLocalSetting
