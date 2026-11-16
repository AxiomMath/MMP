module

public import MMP.AlgebraicGeometry.Positivity.NefAddPullbackAmple
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehweg
import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackAdd

/-!
# Relative Kawamata–Viehweg vanishing for a birational morphism

Let `f : Y ⟶ X` be a birational morphism of projective varieties over an algebraically closed
field `k` of characteristic zero, with `Y` smooth of dimension `n`, and let `B` be a divisor on
`Y` numerically equivalent to `M + Δ`, where `M` is a nef `ℚ`-divisor and `Δ = ∑ aᵢ Dᵢ` is a
`ℚ`-divisor with simple normal crossing support and coefficients `0 ≤ aᵢ < 1`. Then
`R^i f_* (ω_Y ⊗ 𝒪_Y(B)) = 0` for every `i > 0`, where `ω_Y = ⋀ⁿ Ω_{Y/k}`.

No bigness of `M` is assumed: for `H` ample on `X` and `r > 0` the `ℚ`-divisor `M + r f^*H` is
nef and big because `f` is birational, so the absolute theorem
`MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_neg` and Serre duality give
`H^i(Y, ω_Y ⊗ 𝒪_Y(B) ⊗ f^*𝒪_X(rH)) = 0` for `i > 0`, and
`MMP.Mori.isZero_rightDerived_pushforward_of_eventually_isZero_cohomology_twist` turns this into
the vanishing of the higher direct images.

## Main results

* `MMP.Mori.isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf`: the vanishing
  above.

## Implementation notes

* `X` and `Y` carry structure morphisms `sX`, `sY` to `Spec k`, and `f ≫ sX = sY` says that `f`
  is a morphism over `k`.
* `R^i f_*` is the `i`-th right derived functor of `Scheme.Modules.pushforward f`.
* The boundary `∑ aᵢ Dᵢ` with distinct prime divisors `Dᵢ` is a single `ℚ`-divisor `Δ` with
  `MMP.Mori.DivisorWithCoeffs.IsSNC`, which asks snc of the components with nonzero coefficient;
  this agrees with the source's condition since snc passes to subsets of the components.
* Kollár–Mori print the conclusion as `R^i f_*(ω_Y ⊗ M) = 0`; it is meant for the line bundle
  `L = 𝒪_Y(B)`, which is what their proof gives, and the case of an integral nef `M` is `B = M`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Cor. 2.68
-/

@[expose] public section

section

/-!
## Proof: Relative Kawamata–Viehweg vanishing for a birational morphism

Let `f : Y ⟶ X` be a birational morphism of projective varieties over an algebraically closed
field of characteristic zero, with `Y` smooth of dimension `n`, and `B` a divisor on `Y` with
`B ≡ M + Δ`, `M` nef and `Δ` an snc boundary with coefficients in `[0, 1)`. For an ample Cartier
divisor `H` on `X` with pull-back `G = f^*H` and every `r > 0`, `M + r G` is nef and big, so
Kawamata–Viehweg vanishing and Serre duality give `H^q(Y, ω_Y ⊗ 𝒪_Y(B + r G)) = 0` for `q > 0`.
Since `𝒪_Y(B + r G) ≅ 𝒪_Y(B) ⊗ (f^*𝒪_X(H))^{⊗ r}`, the higher direct images
`R^q f_*(ω_Y ⊗ 𝒪_Y(B))` vanish.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Cor. 2.68
-/

open CategoryTheory AlgebraicGeometry
open MMP.Mori hiding IsProjectiveVariety
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km2cRelativeKawamataViehwegProof

open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (twistModule)

/-- On an integral Noetherian scheme every Cartier divisor has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, MMP.Intersection.IsWeilDivisorOfCartier A w := by
  letI : IsNoetherian X := ⟨⟩
  have h0 : ∀ s ∈ MMP.Intersection.cartierSupport A, Order.coheight s = 0 → False := by
    intro s hs h0
    have : Ring.KrullDimLE 0 (X.presheaf.stalk s) := krullDimLE_of_coheight_le (by simp [h0])
    have : IsArtinianRing (X.presheaf.stalk s) := isArtinianRing_iff_krullDimLE_zero.mpr this
    exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing A s hs
  have hfin := finite_setOf_genericPoint_mem
    (MMP.Intersection.isClosed_cartierSupport A) h0
  refine ⟨Finsupp.ofSupportFinite (fun P => MMP.Intersection.primeDivisorOrder P A)
    (hfin.subset fun P hP => ?_), fun P => ?_⟩
  · by_contra h
    have hg : (MMP.Intersection.primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((MMP.Intersection.isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset
      fun h' => h ?_)
    show P.genericPoint ∈ MMP.Intersection.cartierSupport A
    rw [← hg]
    exact MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact MMP.Intersection.isOrderAlong_primeDivisorOrder A P

/-- A projective variety carries a Cartier divisor whose sheaf is ample. -/
private theorem exists_isAmple_cartierSheaf {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [hX : IsProjectiveVariety k sX] :
    ∃ H : X.CartierDivisor, IsAmple X (MMP.CartierDivisor.sheaf H) := by
  haveI : IsIntegral X := hX.toIsIntegral
  obtain ⟨L, hL, hLa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hX
  obtain ⟨H, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  exact ⟨H, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hLa)⟩

/-- The positive tensor powers of the divisorial sheaf of a Cartier divisor `G` are the
divisorial sheaves of the multiples of `G`. -/
private theorem nonempty_tensorPowModule_iso_divisorialSheaf {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (G : Divisor X) (hG : G.IsCartier) [IsInvertibleModule X G.divisorialSheaf] (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X G.divisorialSheaf ((n + 1 : ℕ) : ℤ) ≅
      (((n + 1 : ℕ) : ℤ) • G).divisorialSheaf) := by
  induction n with
  | zero => exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by norm_num) ≪≫
      Stacks.Ample.tensorPowModuleOneIso X _ ≪≫
      eqToIso (by rw [Nat.cast_one, one_smul])⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hG.zsmul _).divisorialSheafTensorIso hG ≪≫
      eqToIso (by congr 1; push_cast; simp only [add_smul, one_smul])⟩

/-- **Kawamata–Viehweg vanishing for `ω_Y ⊗ 𝒪_Y(D)`.** On a smooth projective variety `Y` of
dimension `n` over an algebraically closed field of characteristic zero, if `D ≡ N + Δ` with `N`
nef and big and `Δ` an snc boundary with coefficients in `[0, 1)`, then
`H^i(Y, ω_Y ⊗ 𝒪_Y(D)) = 0` for `i > 0`. -/
private theorem isZero_cohomology_exteriorPower_tensor_divisorialSheaf
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] (hYsm : IsSmoothScheme sY)
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} (hn : topologicalKrullDim Y = n)
    (D : Divisor Y) (N Δ : QDivisor Y) (hNnef : N.IsNef k sY) (hNbig : N.IsBig k sY)
    (hΔ : Δ.IsSNC sY) (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hD : (Divisor.toQDivisor D).NumericallyEquivalent k sY (N + Δ)) (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)).rightDerived i).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials sY) n)).obj
          D.divisorialSheaf)) := by
  haveI : IsProper sY := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sY))).isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm
  haveI := (hcart D).isInvertibleModule_divisorialSheaf
  have hKV := subsingleton_derivedCohomologyOverField_divisorialSheaf_neg sY hYsm hn D N Δ
    hNnef hNbig hΔ hΔ0 hΔ1 hD ((n : ℤ) - i) (by omega)
  obtain ⟨e⟩ := nonempty_divisorialSheaf_iso_dualSheaf_neg hcart (-D)
  rw [neg_neg] at e
  have hS := (subsingleton_dual_iff_subsingleton_exteriorPower_tensor sY hYsm n hn
    D.divisorialSheaf ((n : ℤ) - i)).1
    ((Equiv.subsingleton_congr ((derivedGlobalSectionsOver sY ⋙
      DerivedCategory.homologyFunctor (ModuleCat k) ((n : ℤ) - i)).mapIso
        ((DerivedCategory.singleFunctor Y.Modules 0).mapIso e)).toLinearEquiv.toEquiv).1 hKV)
  rw [sub_sub_cancel] at hS
  exact @ModuleCat.isZero_of_subsingleton _ _ _
    ((Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k sY _ i).toLinearEquiv
      |>.toEquiv.subsingleton)

end MMP.FourfoldProofs.Km2cRelativeKawamataViehwegProof

end

section

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open MMP.FourfoldProofs.Km2cRelativeKawamataViehwegProof
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (twistModule)

/-- **Relative Kawamata–Viehweg vanishing** (Kollár–Mori, Corollary 2.68). Let `f : Y ⟶ X` be a
birational morphism of projective varieties over an algebraically closed field `k` of
characteristic zero, with `Y` smooth of dimension `n`, and `B` a divisor on `Y` numerically
equivalent to `M + Δ`, where `M` is a nef `ℚ`-divisor and `Δ` a `ℚ`-divisor with snc support and
coefficients in `[0, 1)`. Then `R^i f_*(ω_Y ⊗ 𝒪_Y(B)) = 0` for every `i > 0`. -/
@[mmp "lem_km2c_relative_kawamata_viehweg"]
public theorem isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsProjectiveVariety k sX]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] (hYsm : IsSmoothScheme sY)
    [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hf : IsBirationalMorphism f)
    {n : ℕ} (hn : topologicalKrullDim Y = n)
    (B : Divisor Y) (M Δ : QDivisor Y) (hM : M.IsNef k sY) (hΔ : Δ.IsSNC sY)
    (hΔ0 : ∀ E, 0 ≤ Δ E) (hΔ1 : ∀ E, Δ E < 1)
    (hB : (Divisor.toQDivisor B).NumericallyEquivalent k sY (M + Δ)) (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials sY) n)).obj
          B.divisorialSheaf)) := by
  have hXv : AlgebraicGeometry.IsVariety k sX :=
    ((AlgebraicGeometry.isProjectiveVariety_iff k sX).1 ‹_›).1
  have hYv : AlgebraicGeometry.IsVariety k sY :=
    ((AlgebraicGeometry.isProjectiveVariety_iff k sY).1 ‹_›).1
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI := hXv.toLocallyOfFiniteType
  haveI : IsProper sX := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX))).isProper
  haveI : IsProper sY := (IsProjectiveMorphism.isProjective
    (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sY))).isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsProper f := by
    haveI : IsProper (f ≫ sX) := hfs ▸ inferInstance
    exact IsProper.of_comp f sX
  haveI : IsDominant f := hf.isDominant
  have hcart : ∀ D : Divisor Y, D.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm
  obtain ⟨H, hHamp⟩ := exists_isAmple_cartierSheaf sX
  have hH : ¬ Set.range f ⊆ MMP.Intersection.cartierSupport H := fun h =>
    MMP.CartierDivisor.genericPoint_notMem_cartierSupport H
      (map_genericPoint_of_isDominant f ▸ h ⟨genericPoint Y, rfl⟩)
  obtain ⟨G, hG⟩ :=
    exists_isWeilDivisorOfCartier (MMP.CartierDivisor.pullback f H hH)
  have hGc : G.IsCartier := hG.isCartier
  let eG : G.divisorialSheaf ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf H) :=
    hG.sheafIsoDivisorialSheaf.symm ≪≫ MMP.CartierDivisor.pullbackSheafIso f H hH
  set ω := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials sY) n
  set F := ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
    ω).obj B.divisorialSheaf
  haveI : (show Y.Modules from F).IsCoherent := by
    haveI := hYv.toLocallyOfFiniteType
    haveI := Scheme.Hom.isCoherent_relativeDifferentials sY
    haveI : ω.IsCoherent := Scheme.Modules.isCoherent_exteriorPower _ n
    haveI := (hcart B).isInvertibleModule_divisorialSheaf
    exact AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Y ω
      B.divisorialSheaf
  refine isZero_rightDerived_pushforward_of_eventually_isZero_cohomology_twist k sX f
    (MMP.CartierDivisor.sheaf H) hHamp F i ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hr
  haveI := hGc.isInvertibleModule_divisorialSheaf
  obtain ⟨eP⟩ := nonempty_tensorPowModule_iso_divisorialSheaf G hGc m
  let e : twistModule Y (pullbackModule f (MMP.CartierDivisor.sheaf H)) F
      ((m + 1 : ℕ) : ℤ) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} Y.toRingedSpace.sheaf).obj
        ω).obj (B + ((m + 1 : ℕ) : ℤ) • G).divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl F)
        (Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso Y _ _ eG.symm (m + 1) ≪≫ eP) ≪≫
      Stacks.SheafOfModules.tensorSheafAssociator Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) ω B.divisorialSheaf _ ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl ω)
        ((hcart B).divisorialSheafTensorIso (hcart _))
  refine Limits.IsZero.of_iso ?_ ((Functor.rightDerived _ i).mapIso e)
  have hNB := hM.isNef_and_isBig_add_smul_pullback f hfs hf H hHamp hH hG
    (r := ((m + 1 : ℕ) : ℚ)) (by positivity)
  have hEq : Divisor.toQDivisor (((m + 1 : ℕ) : ℤ) • G) =
      ((m + 1 : ℕ) : ℚ) • Divisor.toQDivisor G := by
    rw [map_zsmul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  refine isZero_cohomology_exteriorPower_tensor_divisorialSheaf sY hYsm hn _ _ Δ hNB.1 hNB.2
    hΔ hΔ0 hΔ1 ?_ i hi
  rw [map_add, add_right_comm, ← hEq]
  exact numericallyEquivalent_add_right k sY hB (QDivisor.isQCartier_toQDivisor (hcart _))

end MMP.Mori

end

end
