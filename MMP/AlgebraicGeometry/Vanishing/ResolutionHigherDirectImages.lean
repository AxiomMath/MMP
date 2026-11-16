module

public import MMP.AlgebraicGeometry.Vanishing.ResolutionTwisted
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.UnramifiedOffZeroScheme

/-!
# Vanishing of the higher direct images of the canonical sheaf of a resolution

Let `X` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero, `B` a divisor on `X`, and `f : Y ⟶ X` a birational morphism from a smooth projective
variety `Y` of dimension `n` such that `f^*B ≡ A + Δ`, where `A` is an ample `ℚ`-divisor and
`Δ = ∑ eⱼ Eⱼ` is a `ℚ`-divisor with simple normal crossing support and coefficients
`0 ≤ eⱼ < 1`. Then `R^j f_* ω_Y = 0` for every `j > 0`, where `ω_Y = ⋀ⁿ Ω_{Y/k}`.

For `H` ample on `X`, the twisted vanishing
`MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback`
gives `H^j(Y, ω_Y ⊗ 𝒪_Y(f^*B) ⊗ f^*𝒪_X(H)^r) = 0` for `j > 0` and `r ≥ 0`, so the higher direct
images of `ω_Y ⊗ f^*𝒪_X(B)` vanish; the projection formula then removes the twist by `𝒪_X(B)`.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_exteriorPower_of_numericallyEquivalent`: the
  vanishing above.

## Implementation notes

* The pull-back `f^*B` is a divisor `fB` on `Y` with `MMP.Mori.Divisor.IsPullback`; since `X` is
  smooth, `B` is Cartier and the pull-back is unique (`MMP.Mori.Divisor.IsPullback.eq`).
* The structure morphism of `Y` is `f ≫ sX`, so `f` is a morphism over `k`.
* `R^j f_*` is the `j`-th right derived functor of `Scheme.Modules.pushforward f`.
* The boundary `∑ eⱼ Eⱼ` with distinct prime divisors `Eⱼ` is a single `ℚ`-divisor `Δ` with
  `MMP.Mori.DivisorWithCoeffs.IsSNC`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

@[expose] public section

section

/-!
## Proof: Vanishing of the higher direct images of the canonical sheaf of a resolution

Let `f : Y ⟶ X` be a birational morphism of smooth projective varieties over an algebraically
closed field of characteristic zero, and `B` a divisor on `X` with `f^*B ≡ A + Δ`, where `A` is
ample and `Δ` is an snc `ℚ`-divisor with coefficients in `[0, 1)`. Choose an ample divisor `H` on
`X`. The twisted vanishing gives `H^j(Y, ω_Y ⊗ 𝒪_Y(f^*B) ⊗ (f^*𝒪_X(H))^{⊗ r}) = 0` for `j > 0`
and all `r ≥ 0`, so the higher direct images of `ω_Y ⊗ 𝒪_Y(f^*B) ≅ ω_Y ⊗ f^*𝒪_X(B)` vanish. By
the projection formula they are `R^j f_* ω_Y ⊗ 𝒪_X(B)`, and since `𝒪_X(B)` is invertible,
`R^j f_* ω_Y = 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Thm. 2.64, Step 4
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open MMP.Mori hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (twistModule tensorRightModules)

namespace MMP.FourfoldProofs.Km2cKvResolutionHigherDirectImagesProof

/-- Tensoring with an invertible module reflects vanishing. -/
private theorem isZero_of_isZero_tensorModules {X : Scheme.{0}} (L : X.Modules)
    [IsInvertibleModule X L] (G : X.Modules) (h : IsZero (tensorModules X G L)) : IsZero G := by
  haveI : (tensorRightModules X L).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  rw [IsZero.iff_id_eq_zero]
  exact (tensorRightModules X L).map_injective (by simpa using h.eq_of_src _ _)

/-- Vanishing of hypercohomology over the base field of a module in degree zero is vanishing of
the corresponding right derived functor of global sections. -/
private theorem isZero_rightDerived_evaluation_of_subsingleton {k : Type} [Field k]
    {Y : Scheme.{0}} (s : Y ⟶ Spec (.of k)) (G : Y.Modules) (j : ℕ)
    (h : Subsingleton (Stacks.Duality.derivedCohomologyOverField s
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G) (j : ℤ))) :
    IsZero (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived j).obj
      G) := by
  have : Subsingleton (cohomologyOverField k s G j) :=
    (Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k s G j).toLinearEquiv
      |>.toEquiv.subsingleton
  exact @ModuleCat.isZero_of_subsingleton _ _ _ this

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

/-- `𝒪_X(n H + F) ≅ 𝒪_X(F) ⊗ 𝒪_X(H)^{⊗ n}` for Cartier divisors `H` and `F`. -/
private theorem nonempty_divisorialSheaf_nsmul_add_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {H F : Divisor X} (hH : H.IsCartier) (hF : F.IsCartier)
    (n : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    Nonempty ((n • H + F).divisorialSheaf ≅
      tensorModules X F.divisorialSheaf (tensorPowModule X H.divisorialSheaf (n : ℤ))) := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  induction n with
  | zero =>
    exact ⟨eqToIso (by rw [zero_smul, zero_add]) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor X _).symm ≪≫
      tensorModulesMapIso X (Iso.refl _) (Stacks.Ample.tensorPowModuleZeroIso X _).symm⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [succ_nsmul, add_right_comm]) ≪≫
      (((hH.nsmul n).add hF).divisorialSheafTensorIso hH).symm ≪≫
      tensorModulesMapIso X e (Stacks.Ample.tensorPowModuleOneIso X _).symm ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X _ _ _ ≪≫
      tensorModulesMapIso X (Iso.refl _)
        (Stacks.Ample.tensorPowModuleAddIso X _ (n : ℤ) 1 ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by omega))⟩

/-- The two pull-back functors on modules agree. -/
private noncomputable def pullbackModuleIso {X Y : Scheme.{0}} (f : Y ⟶ X) (L : X.Modules) :
    pullbackModule f L ≅ (Scheme.Modules.pullback f).obj L :=
  (Adjunction.leftAdjointUniq
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app L

/-- The twist of `ω ⊗ 𝒪_Y(D)` by the pull-back of `𝒪_X(H)` is `ω ⊗ 𝒪_Y(D + r f^*H)`. -/
private noncomputable def twistModuleIso {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y]
    (f : Y ⟶ X) {H : Divisor X} (hH : H.IsCartier)
    {hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp}
    {fH : Divisor Y} (hfH : H.IsPullback f hHf fH) (hfHc : fH.IsCartier)
    {D : Divisor Y} (hD : D.IsCartier) (ω : Y.Modules) (r : ℕ) :
    haveI := hH.isInvertibleModule_divisorialSheaf
    twistModule Y (pullbackModule f H.divisorialSheaf)
        (tensorModules Y ω D.divisorialSheaf) r ≅
      tensorModules Y ω (D + (r : ℤ) • fH).divisorialSheaf :=
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hfHc.isInvertibleModule_divisorialSheaf
  tensorModulesMapIso Y (Iso.refl _)
      (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorPowModuleIsoOfIsoInt Y _ _
        (pullbackModuleIso f _ ≪≫ (hfH.divisorialSheafIso (hBc := hH)).symm) r) ≪≫
    Stacks.TensorSheafSpellingIso.tensorModulesAssociator Y _ _ _ ≪≫
    tensorModulesMapIso Y (Iso.refl ω)
      (nonempty_divisorialSheaf_nsmul_add_iso hfHc hD r).some.symm ≪≫
    eqToIso (by rw [add_comm, natCast_zsmul])

/-- Projection formula cancellation: for an invertible `L` on `X`, vanishing of
`R^j f_*(ℱ ⊗ f^*L) ≅ R^j f_*ℱ ⊗ L` gives vanishing of `R^j f_*ℱ`. -/
private theorem isZero_rightDerived_pushforward_of_isZero_tensor_pullback {X Y : Scheme.{0}}
    (f : Y ⟶ X) (L : X.Modules) [IsInvertibleModule X L] (M : Y.Modules) (j : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj
      (tensorModules Y M ((Scheme.Modules.pullback f).obj L)))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj M) := by
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).2 inferInstance
  exact (isZero_of_isZero_tensorModules L _ ((h.of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ j).app _).symm).of_iso
      (Stacks.ProjectionFormula.higherDirectImageProjectionFormulaIso f L M j).symm)).of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso _ j).app M)

end MMP.FourfoldProofs.Km2cKvResolutionHigherDirectImagesProof

open MMP.FourfoldProofs.Km2cKvResolutionHigherDirectImagesProof

namespace MMP.Mori

/-- **Higher direct images of `ω_Y` on a resolution** (Kollár–Mori, proof of Theorem 2.64). Let
`X` be a smooth projective variety over an algebraically closed field `k` of characteristic zero,
`B` a divisor on `X`, and `f : Y ⟶ X` a birational morphism from a smooth projective variety `Y`
of dimension `n` with `f^*B ≡ A + Δ`, where `A` is an ample `ℚ`-divisor and `Δ` a `ℚ`-divisor
with snc support and coefficients in `[0, 1)`. Then `R^j f_* ω_Y = 0` for every `j > 0`, where
`ω_Y = ⋀ⁿ Ω_{Y/k}`. -/
@[mmp "lem_km2c_kv_resolution_higher_direct_images"]
public theorem isZero_rightDerived_pushforward_exteriorPower_of_numericallyEquivalent
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX] (hXsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {Y : Scheme.{0}} (f : Y ⟶ X) [IsProjectiveVariety k (f ≫ sX)] (hYsm : IsSmoothScheme (f ≫ sX))
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hf : IsBirationalMorphism f)
    {n : ℕ} (hn : topologicalKrullDim Y = n) (B : Divisor X)
    (hBf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp)
    (fB : Divisor Y) (hfB : B.IsPullback f hBf fB)
    (A Δ : QDivisor Y) (hA : A.IsAmple) (hΔ : Δ.IsSNC (f ≫ sX))
    (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor fB).NumericallyEquivalent k (f ≫ sX) (A + Δ))
    (j : ℕ) (hj : 0 < j) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (f ≫ sX)) n)) := by
  have hX := (AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›
  have hY := (AlgebraicGeometry.isProjectiveVariety_iff k (f ≫ sX)).1 ‹_›
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hf.isDominant
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hX.2
  haveI : IsProper (f ≫ sX) := isProper_of_isProjectiveMorphism _ hY.2
  haveI : IsProper f := IsProper.of_comp f sX
  have hcartX := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hXsm
  have hcartY := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm
  -- an ample divisor `H` on `X` and its pull-back `f^*H`
  obtain ⟨H, hHc, hHamp⟩ := exists_isCartier_isAmple sX
  have hHf : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ H.supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f H Z
  obtain ⟨fH, hfH⟩ := hHc.exists_isPullback hHf
  haveI := hHc.isInvertibleModule_divisorialSheaf
  haveI := (hcartX B).isInvertibleModule_divisorialSheaf
  haveI := (hcartY fB).isInvertibleModule_divisorialSheaf
  set ω := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (f ≫ sX)) n
  haveI : (Scheme.Hom.relativeDifferentials (f ≫ sX)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _
  haveI : ω.IsCoherent := Scheme.Modules.isCoherent_exteriorPower _ n
  haveI : fB.divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible Y _
  haveI : (tensorModules Y ω fB.divisorialSheaf).IsCoherent :=
    isCoherent_tensorBifunctorObj ω fB.divisorialSheaf inferInstance inferInstance
  -- `R^j f_*(ω_Y ⊗ 𝒪_Y(f^*B)) = 0`, since every twist by `f^*𝒪_X(H)` has vanishing `H^j`
  have hRF := isZero_rightDerived_pushforward_of_eventually_isZero_cohomology_twist k sX f
    H.divisorialSheaf hHamp (tensorModules Y ω fB.divisorialSheaf) j <|
    Filter.Eventually.of_forall fun r =>
      (isZero_rightDerived_evaluation_of_subsingleton (f ≫ sX) _ j
        (subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_pullback
          sX hXsm f hYsm hf hn B H ⟨1, one_pos, H, by simp, hHc, hHamp⟩ hBf hHf fB fH hfB hfH
          A Δ hA hΔ hΔ0 hΔ1 hB r j (by exact_mod_cast hj))).of_iso
      (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived j).mapIso
        (twistModuleIso f hHc hfH (hcartY fH) (hcartY fB) ω r))
  -- `𝒪_Y(f^*B) ≅ f^*𝒪_X(B)`, and the projection formula removes the twist
  exact isZero_rightDerived_pushforward_of_isZero_tensor_pullback f B.divisorialSheaf ω j
    (hRF.of_iso (((Scheme.Modules.pushforward f).rightDerived j).mapIso
      (tensorModulesMapIso Y (Iso.refl ω) (hfB.divisorialSheafIso (hBc := hcartX B))).symm))

end MMP.Mori

end

end
