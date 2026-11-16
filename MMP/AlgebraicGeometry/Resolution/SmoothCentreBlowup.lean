module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothFibreTwist
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Resolution.OrderRestriction
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorGeneration
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.RestrictMeromorphic

/-!
# Blow-ups of smooth varieties along smooth centres

Let `Y` be a smooth variety over a field `k` and `π : Bl_Z Y ⟶ Y` the blow-up of a smooth
irreducible centre `Z` of codimension `c ≥ 2`. This file collects the basic geometry of `π`:
`Bl_Z Y` is a smooth variety, `π` is projective, birational and an isomorphism off `Z`, the
exceptional divisor `E` is a smooth prime divisor whose fibres over `Z` are `ℙ^{c-1}` with
`𝒪(E)` restricting to `𝒪(-1)`, `Pic (Bl_Z Y) = π^* Pic Y ⊕ ℤ [𝒪(E)]`,
`K_{Bl_Z Y} ∼ π^*K_Y + (c - 1)E`, and `π_* 𝒪 = 𝒪` with `R^i π_* 𝒪 = 0` for `i > 0`. It treats
the special case of a closed point (and, on a surface, the pull-back of `ℚ`-divisors), centres
adapted to an snc divisor, blow-ups of arbitrary proper closed subschemes of a variety, and the
behaviour of reflexive rank-one modules under flat local maps.

## Main results

* `MMP.Threefold.Resolution.pullback_blowUpToBase_vanishingIdeal_singleton_eq_add`:
  `π^*C = π⁻¹_* C + (mult_p C) F` for the blow-up of a point of a smooth surface.
* `MMP.Threefold.Resolution.bijective_pullbackClassHom_add_zsmul_picardClass_exceptionalIdeal`:
  the Picard group of a smooth blow-up.
* `MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_canonicalDivisor_picardGroup`:
  the full package for a smooth blow-up.
* `MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_vanishingIdeal_singleton`:
  the blow-up of a closed point of a smooth variety.
* `MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational_of_support_ne_top`:
  the blow-up of a variety in a proper closed subscheme.
* `MMP.isReflexive_baseChange_and_free_iff_of_flat_of_rank_eq_one`: reflexive rank-one modules
  along a flat local map.
* `MMP.Flips.ResolutionInputs`
  `.smooth_blowUp_and_isSNCDivisor_birationalInverseTransform_add_exceptional`:
  blowing up a smooth centre adapted to an snc divisor.
* `MMP.LcBpf.isIso_c_and_isZero_rightDerived_of_multiplicativeClosure_smoothBlowup`:
  `𝒪 ≅ R π_* 𝒪` for finite compositions of smooth blow-ups.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [R. Hartshorne, *Algebraic Geometry*][Hartshorne]
-/

/-!
## Pull-back of a `ℚ`-divisor under the blow-up of a point of a smooth surface

Let `Y` be a smooth surface over an algebraically closed field `k`, `p ∈ Y` a closed point,
`π : Y' ⟶ Y` the blow-up of the reduced point `p` and `F = π⁻¹(p)_red` the exceptional curve.
For every `ℚ`-divisor `C` on `Y`, the pull-back is the strict transform plus the multiplicity of
`C` at `p` times the exceptional curve:
`π^*C = π⁻¹_* C + (mult_p C) F`.

### Main results

* `MMP.Threefold.Resolution.pullback_blowUpToBase_vanishingIdeal_singleton_eq_add`:
  the formula above, in the form of
  `MMP.Threefold.Resolution.pullback_qDivisor_blowUp_singleton`.

### Implementation notes

* The surface is a variety `Y` over `k`, smooth over `k` in the sense of `IsSmoothScheme`, with
  `topologicalKrullDim Y = 2`. The exceptional curve is any prime divisor `F` of `Y'` whose ideal
  sheaf is `exceptionalIdeal` of the ideal of `p`; the ideal sheaf determines it.
* `π^*C` is `MMP.Mori.QDivisor.pullback` (every `ℚ`-divisor on a smooth surface is
  `ℚ`-Cartier, and `π` is dominant), `π⁻¹_* C` is `MMP.Mori.inverseTransformDivisor` and
  `mult_p C` is `MMP.Mori.DivisorWithCoeffs.multiplicityAt`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 4.5
-/

section

universe u uProof

open CategoryTheory AlgebraicGeometry MMP.Threefold.Resolution

namespace MMP.Threefold.Resolution

@[expose] public section

/-- **Pull-back of a `ℚ`-divisor through the blow-up of a point of a smooth surface.** Let `Y`
be a surface smooth over an algebraically closed field `k`, `p ∈ Y` a closed point,
`π : Y' ⟶ Y` the blow-up of the reduced point `p`, and `F` the exceptional curve, the prime
divisor of `Y'` with ideal sheaf `exceptionalIdeal`. Then for every `ℚ`-divisor `C` on `Y`,
`π^*C = π⁻¹_* C + (mult_p C) F`. -/
@[mmp "lem_mmp_foundation_km4a_point_blowup_divisor_multiplicity"]
public theorem pullback_blowUpToBase_vanishingIdeal_singleton_eq_add
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {p : Y} (hp : IsClosed ({p} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (C : Mori.QDivisor Y) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hp)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hp)).2
    haveI := compactSpace_blowUp_singleton hY hYd hp
    Mori.QDivisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) C
        (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs C)
        (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hp C) =
      Mori.inverseTransformDivisor
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) C +
        Finsupp.single F (C.multiplicityAt p) :=
  pullback_qDivisor_blowUp_singleton hY hYs hYd hp hF C

end

end MMP.Threefold.Resolution

end

/-!
## The Picard group of the blow-up of a smooth centre

Let `Y` be a smooth variety over a field `k`, `Z ⊆ Y` a smooth irreducible closed subscheme of
codimension `c ≥ 2`, `π : V = Bl_Z Y ⟶ Y` the blow-up and `E = π⁻¹(Z)` its exceptional divisor.
Then `Pic V = π^* Pic Y ⊕ ℤ [𝒪_V(E)]`: the homomorphism
`Pic Y × ℤ → Pic V`, `(L, n) ↦ π^*L + n [𝒪_V(E)]` is an isomorphism.

Surjectivity: an invertible sheaf on the integral scheme `V` is `𝒪_V(D)` for a Cartier divisor
`D`; the push-forward of its non-exceptional part is Cartier on the locally factorial `Y`, and
subtracting its pull-back leaves a multiple of `E`. Injectivity: restricting `π^*L + n E` to a
line in a fibre `ℙ^{c-1}` of `E ⟶ Z` gives degree `-n`, so `n = 0`; and `π^*L` trivial forces
`L` trivial, since `π` is an isomorphism off `Z`, of codimension `≥ 2`.

### Main results

* `MMP.Threefold.Resolution.bijective_pullbackClassHom_add_zsmul_picardClass_exceptionalIdeal`:
  `(L, n) ↦ π^*L + n [𝒪_V(E)]` is a bijection `Pic Y × ℤ → Pic V`.

### Implementation notes

The direct sum decomposition is stated as bijectivity of the canonical additive map
`Pic Y × ℤ → Pic V`; that map is additive by construction, so this is the same as an
isomorphism of abelian groups `Pic Y × ℤ ≃+ Pic V` restricting to `π^*` on the first factor
and to `n ↦ n [𝒪_V(E)]` on the second. The centre is given by its ideal sheaf `I` with
`MMP.Resolution.IsSmoothBlowup`; `Pic` is `Stacks.Picard.ofScheme`, `π^*` is
`Stacks.Picard.pullbackClassHom` of the underlying morphism of ringed spaces, and
`[𝒪_V(E)]` is `Stacks.Divisors.picardClass` of the exceptional ideal
`MMP.Resolution.exceptionalIdeal I`, an effective Cartier divisor.

### References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.19]
* [R. Hartshorne, *Algebraic geometry*, Exercise II.8.5]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution MMP.Threefold.Resolution

namespace MMP.Proofs.lem_mmp_threefold_smooth_blowup_picard

/-- The pull-back of Picard classes along a morphism of schemes, read on `Scheme.picardGroup`,
is `Stacks.Picard.pullbackClassHom` of the underlying morphism of ringed spaces. -/
private theorem pullbackPicardHom_apply_eq_pullbackClassHom {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (x : Y.picardGroup) :
    Stacks.SheafOfModules.pullbackPicardHom φ x =
      Stacks.Picard.pullbackClassHom φ.toLRSHom.toShHom x := by
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq Y.presheaf Y.ringCatIsSheaf x
  rw [Stacks.Picard.pullbackClassHom_apply]
  exact (Stacks.SheafOfModules.pullbackPicardHom_picardClass φ L hL).trans
    (Stacks.Picard.pullbackClass_classOf φ.toLRSHom.toShHom L hL).symm

/-- The Picard group of the spectrum of a field is trivial. -/
private theorem subsingleton_picardGroup_spec_field (K : Type u) [Field K] :
    Subsingleton (Spec (.of K)).picardGroup :=
  Scheme.subsingleton_picardGroup _ fun L hL =>
    have := hL; Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd K L

/-- If `π^*L + n [𝒪_V(E)]` is trivial then `n = 0`: restrict to a fibre `ℙ^{c-1}` of `E ⟶ Z`,
where `π^*L` becomes trivial and `𝒪_V(E)` becomes `𝒪(-1)`. -/
private theorem eq_zero_of_pullbackClassHom_add_zsmul_picardClass_eq_zero
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : AlgebraicGeometry.IsVariety k sY) (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (L : Stacks.Picard.ofScheme Y) (n : ℤ) :
    haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
    Stacks.Picard.pullbackClassHom (blowUpToBase I).toLRSHom.toShHom L +
        n • Stacks.Divisors.picardClass (exceptionalIdeal I) = 0 → n = 0 := by
  intro hL
  obtain ⟨c, hcc, hfib⟩ :=
    exists_fiber_iso_projSpace_pullback_invertibleSheaf_exceptionalIdeal sY I h hirr hc
  have hc2 : 2 ≤ c := by
    have : ((2 : ℕ) : ℕ∞) ≤ (c : ℕ∞) := by rw [hcc]; exact_mod_cast hc
    exact_mod_cast this
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  have : Smooth (I.subschemeι ≫ sY) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ h.2
  have : IsIntegral I.subscheme := isIntegral_subscheme_of_isIrreducible sY I h.2 hirr
  obtain ⟨z⟩ : Nonempty I.subscheme := inferInstance
  set K := I.subscheme.residueField z
  haveI : IsDomain K := inferInstanceAs (IsDomain (I.subscheme.residueField z))
  obtain ⟨e, he, ⟨ι⟩⟩ := hfib z
  set g := (Stacks.AlgebraicGeometry.exceptionalSubschemeMap I).fiberι z ≫
    (exceptionalIdeal I).subschemeι
  set ε := e ≪≫ MMP.Intersection.ProjSpace.isoPolyGrading K m
  have hinv (j : ℤ) : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)).presheaf
      (AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)).ringCatIsSheaf
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K) j) :=
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf _
      (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading _ m) j
  -- `g^* 𝒪_V(E) ≅ ε^* 𝒪(-1)`
  have ι' : (Scheme.Modules.pullback g).obj
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I)) ≅
      (Scheme.Modules.pullback ε.hom).obj (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K) (-1)) :=
    ι ≪≫ (Scheme.Modules.pullback e.hom).mapIso
        (MMP.Intersection.ProjSpace.twistingSheafIsoPullback K m (-1)).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).app _
  have h2 : Stacks.SheafOfModules.pullbackPicardClass g
      (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I))
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard _) =
      Stacks.SheafOfModules.pullbackPicardClass ε.hom
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K) (-1)) (hinv (-1)) :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
      ⟨(AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback g).app _ ≪≫ ι' ≪≫
        ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback ε.hom).app _).symm⟩
  set ψ := ε.inv ≫ g
  -- `π ∘ ψ` factors through `Spec κ(z)`, whose Picard group vanishes
  have hA : Stacks.Picard.schemePullbackClass ψ
      (Stacks.Picard.schemePullbackClass (blowUpToBase I) L) = 0 := by
    have hfac : ψ ≫ blowUpToBase I = (ε.inv ≫
        (Stacks.AlgebraicGeometry.exceptionalSubschemeMap I).fiberToSpecResidueField z) ≫
          (I.subscheme.fromSpecResidueField z ≫ I.subschemeι) := by
      simp only [ψ, g, Category.assoc]
      rw [← Scheme.Hom.fiber_fac_assoc,
        Scheme.IdealSheafData.subschemeMap_subschemeι]
    haveI := subsingleton_picardGroup_spec_field K
    rw [Stacks.Picard.schemePullbackClass_comp, hfac, ← Stacks.Picard.schemePullbackClass_comp,
      Subsingleton.elim (Stacks.Picard.schemePullbackClass
        (I.subscheme.fromSpecResidueField z ≫ I.subschemeι) L) 0]
    exact map_zero (Stacks.Picard.schemePullbackClassHom _)
  -- `ψ^* [𝒪_V(E)] = [𝒪(-1)]`
  have hB : Stacks.Picard.schemePullbackClass ψ
      (Stacks.Divisors.picardClass (exceptionalIdeal I)) =
        Stacks.PicardUFD.twistPicardHom K m (-1) := by
    have hg : Stacks.Picard.schemePullbackClass g
        (Stacks.Divisors.picardClass (exceptionalIdeal I)) =
          Stacks.Picard.schemePullbackClass ε.hom (Stacks.PicardUFD.twistPicardHom K m (-1)) :=
      (pullbackPicardHom_apply_eq_pullbackClassHom g _).symm.trans
        ((Stacks.SheafOfModules.pullbackPicardHom_picardClass g _ _).trans
          (h2.trans ((Stacks.SheafOfModules.pullbackPicardHom_picardClass ε.hom _ _).symm.trans
            (pullbackPicardHom_apply_eq_pullbackClassHom ε.hom _))))
    rw [← Stacks.Picard.schemePullbackClass_comp, hg, Stacks.Picard.schemePullbackClass_comp,
      ε.inv_hom_id, Stacks.Picard.schemePullbackClass_id]
  have h3 := congrArg (Stacks.Picard.schemePullbackClassHom ψ) hL
  rw [map_add, map_zsmul, map_zero] at h3
  change Stacks.Picard.schemePullbackClass ψ
      (Stacks.Picard.schemePullbackClass (blowUpToBase I) L) +
    n • Stacks.Picard.schemePullbackClass ψ (Stacks.Divisors.picardClass (exceptionalIdeal I)) =
      0 at h3
  rw [hA, hB, zero_add, ← map_zsmul, ← map_zero (Stacks.PicardUFD.twistPicardHom K m)] at h3
  have h4 := Stacks.PicardUFD.twistPicardHom_injective K m (by omega) h3
  simpa using h4

/-- **Line bundles extend uniquely across codimension two on a normal scheme.** Two invertible
modules on a normal integral locally Noetherian scheme which become isomorphic on an open
subscheme whose complement has codimension `≥ 2` are isomorphic: their Weil divisor classes agree
on `U`, hence on `X` since `Cl X ≅ Cl U`, and the first Chern class `Pic X → Cl X` is injective. -/
private theorem nonempty_iso_of_restrict_iso {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (L M : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (e : L.restrict U.ι ≅ M.restrict U.ι) : Nonempty (L ≅ M) := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    hM.toAlgebraicGeometry
  haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  haveI : IsDominant U.ι := isDominant_opensι (U := U)
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hw : weilDivisorClassOfInvertibleSheaf X L = weilDivisorClassOfInvertibleSheaf X M :=
    (weilDivisorClassRestrictEquiv U hU).injective (by
      rw [weilDivisorClassOfInvertibleSheaf_restrict U hU L,
        weilDivisorClassOfInvertibleSheaf_restrict U hU M]
      exact weilDivisorClassOfInvertibleSheaf_congr _ _ e)
  refine (Stacks.SheafOfModules.picardClass_eq_iff X.sheaf.obj X.ringCatSheaf.property _ _
    hL hM).mp (picardToWeilDivisorClassGroup_injective X ?_)
  change weilDivisorClassOfPicardClass X _ = weilDivisorClassOfPicardClass X _
  rw [weilDivisorClassOfPicardClass_picardClass X L, weilDivisorClassOfPicardClass_picardClass X M]
  exact hw

/-- On a normal integral locally Noetherian scheme, restriction of Picard classes to an open
subscheme whose complement has codimension `≥ 2` is injective. -/
private theorem schemePullbackClass_opensι_injective {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    Function.Injective (Stacks.Picard.schemePullbackClass U.ι) := by
  intro x y hxy
  obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf x
  obtain ⟨M, hM, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf y
  have h' : Stacks.SheafOfModules.pullbackPicardClass U.ι L hL =
      Stacks.SheafOfModules.pullbackPicardClass U.ι M hM :=
    (Stacks.SheafOfModules.pullbackPicardHom_picardClass U.ι L hL).symm.trans
      ((pullbackPicardHom_apply_eq_pullbackClassHom U.ι _).trans (hxy.trans
        ((pullbackPicardHom_apply_eq_pullbackClassHom U.ι _).symm.trans
          (Stacks.SheafOfModules.pullbackPicardHom_picardClass U.ι M hM))))
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 h'
  obtain ⟨f⟩ := nonempty_iso_of_restrict_iso U hU L M hL hM
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L ≪≫
      ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback U.ι).app L).symm ≪≫ e ≪≫
      (AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback U.ι).app M ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm)
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨f⟩

/-- If the irreducible support of `I` has codimension `≥ 2`, so does the closure of every point
outside the complement of the support. -/
private theorem two_le_codimension_of_notMem_compl_support {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (x : Y) (hx : x ∉ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens)) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) :=
  hc.trans (Order.coheight_anti (show closure {x} ⊆ (I.support : Set Y) from
    closure_minimal (Set.singleton_subset_iff.2 (by simpa using hx)) I.support.isClosed))

/-- `π^*` is injective on Picard groups: `π` is an isomorphism over `Y ∖ Z`, `Z` has codimension
`≥ 2` and `Y` is normal. -/
private theorem pullbackClassHom_blowUpToBase_injective
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : AlgebraicGeometry.IsVariety k sY) (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    Function.Injective (Stacks.Picard.pullbackClassHom (blowUpToBase I).toLRSHom.toShHom) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ h.1
  haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI := AlgebraicGeometry.isNormal_of_smooth sY
  set U : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hU := two_le_codimension_of_notMem_compl_support I hirr hc
  haveI := isIso_blowUp_restrict_compl_support I
  have hs : (inv (blowUpToBase I ∣_ U) ≫ (blowUpToBase I ⁻¹ᵁ U).ι) ≫ blowUpToBase I = U.ι := by
    rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  intro x y hxy
  apply schemePullbackClass_opensι_injective U hU
  have h' := congrArg (Stacks.Picard.schemePullbackClass
    (inv (blowUpToBase I ∣_ U) ≫ (blowUpToBase I ⁻¹ᵁ U).ι)) hxy
  change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ x) =
    Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ y) at h'
  rwa [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp, hs] at h'

/-- The restriction of the Picard class of an invertible module to an open subscheme is the
class of its restriction. -/
private theorem schemePullbackClass_opensι_picardClass {X : Scheme.{u}} (U : X.Opens)
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (hLU : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatIsSheaf
      (L.restrict U.ι)) :
    Stacks.Picard.schemePullbackClass U.ι
        (Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL) =
      Stacks.SheafOfModules.picardClass U.toScheme.presheaf U.toScheme.ringCatIsSheaf
        (L.restrict U.ι) hLU :=
  (pullbackPicardHom_apply_eq_pullbackClassHom U.ι _).symm.trans
    ((Stacks.SheafOfModules.pullbackPicardHom_picardClass U.ι L hL).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
        ⟨(AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback U.ι).app L ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm⟩))

section Extension

attribute [local instance] AlgebraicGeometry.schemePicardGroupAddCommGroup

/-- **Line bundles extend across codimension two on a locally factorial scheme.** On an integral
locally Noetherian scheme whose local rings are unique factorization domains, every invertible
module on an open subscheme whose complement has codimension `≥ 2` is the restriction of an
invertible module: `Pic X ≅ Cl X ≅ Cl U`, and `Pic U → Cl U` is injective. -/
private theorem exists_restrict_iso_of_forall_uniqueFactorizationMonoid {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (N : U.toScheme.Modules)
    (hN : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatIsSheaf N) :
    ∃ (L : X.Modules) (_ : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L),
      Nonempty (L.restrict U.ι ≅ N) := by
  haveI : IsNormal X := isNormal_of_forall_uniqueFactorizationMonoid_stalk X hufd
  haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  haveI : IsDominant U.ι := isDominant_opensι (U := U)
  haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  haveI : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property N := hN.toAlgebraicGeometry
  set c := (picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid X hufd).symm
    ((weilDivisorClassRestrictEquiv U hU).symm (weilDivisorClassOfInvertibleSheaf U.toScheme N))
    with hcdef
  obtain ⟨L, hL, hLc⟩ : ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L),
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL = c :=
    Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf c
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  refine ⟨L, hL, ?_⟩
  have hLU : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatIsSheaf
      (L.restrict U.ι) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have hw : weilDivisorClassOfInvertibleSheaf X L =
      (weilDivisorClassRestrictEquiv U hU).symm
        (weilDivisorClassOfInvertibleSheaf U.toScheme N) := by
    have h :=
      congrArg (picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid X hufd) hLc
    rw [hcdef, AddEquiv.apply_symm_apply] at h
    exact (weilDivisorClassOfPicardClass_picardClass X L).symm.trans h
  refine (Stacks.SheafOfModules.picardClass_eq_iff U.toScheme.sheaf.obj
    U.toScheme.ringCatSheaf.property _ _ hLU hN).mp
    (picardToWeilDivisorClassGroup_injective U.toScheme ?_)
  exact (weilDivisorClassOfPicardClass_picardClass U.toScheme (L.restrict U.ι)).trans
    ((weilDivisorClassOfInvertibleSheaf_restrict U hU L).symm.trans ((congrArg _ hw).trans
      ((AddEquiv.apply_symm_apply _ _).trans
        (weilDivisorClassOfPicardClass_picardClass U.toScheme N).symm)))

end Extension

/-- **An invertible module trivial off an integral effective Cartier divisor `E` is a multiple
of `𝒪_X(E)`**, on a normal integral locally Noetherian scheme: a trivializing section off `E`
is a regular meromorphic section whose Weil divisor is supported on `E`. -/
private theorem exists_zsmul_picardClass_eq_of_isTrivial_restrict {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (E : X.IdealSheafData) [IsIntegral E.subscheme]
    [hE : Stacks.Divisors.IsEffectiveCartierDivisor E]
    (htriv : Stacks.SheafOfModules.IsTrivial
      (Scheme.Opens.toScheme (Closeds.compl (E.support : Closeds X))).presheaf
      (Scheme.Opens.toScheme (Closeds.compl (E.support : Closeds X))).ringCatIsSheaf
      (L.restrict (Scheme.Opens.ι (Closeds.compl (E.support : Closeds X))))) :
    ∃ n : ℤ, n • Stacks.Divisors.picardClass E =
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL := by
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L := hL.toAlgebraicGeometry _ _ _
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  obtain ⟨e0⟩ := htriv
  set U := Closeds.compl (E.support : Closeds X)
  let e : L.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U) :=
    Stacks.AlgebraicGeometry.TwistMapsInvertible.overIsoUnitOfRestrictIsoUnit L U e0
  obtain ⟨t, htb⟩ : ∃ t : Γ(L, U),
      ∀ (y : X) (hy : y ∈ U), Stacks.Divisors.IsStalkBasis L y (L.presheaf.germ U y hy t) :=
    ⟨(Stacks.Divisors.frameSections X L e).symm 1,
      fun y hy => Stacks.ChernCap42.isStalkBasis_germ_frameSections L e y hy⟩
  have hηU : genericPoint X ∈ U := genericPoint_mem_compl_support E hE
  have hs := isRegularMeromorphicSection_of_isStalkBasis_genericPoint L t hηU (htb _ hηU)
  have hdiv : ∀ W : PrimeDivisor X, W ≠ PrimeDivisor.ofEffectiveCartier E hE →
      (weilDivisorOfMeromorphicSection X L _ hs).val W = 0 := fun W hW =>
    orderOfVanishingMeromorphic_eq_zero_of_isStalkBasis L t htb hηU hs W
      (genericPoint_mem_compl_support_of_ne hE W hW)
  refine ⟨(weilDivisorOfMeromorphicSection X L _ hs).val
    (PrimeDivisor.ofEffectiveCartier E hE), ?_⟩
  set n : ℤ :=
    (weilDivisorOfMeromorphicSection X L _ hs).val (PrimeDivisor.ofEffectiveCartier E hE) with hn
  refine picardToWeilDivisorClassGroup_injective X ?_
  have h1 : weilDivisorClassOfPicardClass X (n • Stacks.Divisors.picardClass E) =
      n • weilDivisorClassOfPicardClass X (Stacks.Divisors.picardClass E) :=
    map_zsmul (picardToWeilDivisorClassGroup X) n (Stacks.Divisors.picardClass E)
  have h2 : weilDivisorClassOfPicardClass X (Stacks.Divisors.picardClass E) =
      ((PrimeDivisor.ofEffectiveCartier E hE).toWeilDivisor : weilDivisorClassGroup X) :=
    (weilDivisorClassOfPicardClass_picardClass X (Stacks.Divisors.modulesInvertibleSheaf E)).trans
      (weilDivisorClassOfInvertibleSheaf_eq_toWeilDivisor E)
  have h3 : weilDivisorClassOfPicardClass X
        (Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL) =
      ((weilDivisorOfMeromorphicSection X L _ hs : WeilDivisor X) :
        weilDivisorClassGroup X) :=
    (weilDivisorClassOfPicardClass_picardClass X L).trans
      (weilDivisorClassOfInvertibleSheaf_eq X L _ hs)
  change weilDivisorClassOfPicardClass X (n • Stacks.Divisors.picardClass E) =
    weilDivisorClassOfPicardClass X
      (Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL)
  rw [h1, h2, h3,
    eq_zsmul_toWeilDivisor_of_forall_eq_zero (weilDivisorOfMeromorphicSection X L _ hs) hdiv,
    ← hn]
  exact (map_zsmul (QuotientAddGroup.mk' (principalWeilDivisors X)) n
    (PrimeDivisor.ofEffectiveCartier E hE).toWeilDivisor).symm

/-- On a normal integral locally Noetherian scheme, a Picard class trivial off an integral
effective Cartier divisor `E` is a multiple of `[𝒪_X(E)]`. -/
private theorem exists_zsmul_picardClass_eq_of_schemePullbackClass_eq_zero {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (E : X.IdealSheafData)
    [IsIntegral E.subscheme] [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (M : Stacks.Picard.ofScheme X)
    (hM : Stacks.Picard.schemePullbackClass
      (Scheme.Opens.ι (Closeds.compl (E.support : Closeds X))) M = 0) :
    ∃ n : ℤ, n • Stacks.Divisors.picardClass E = M := by
  obtain ⟨M0, hM0, rfl⟩ : ∃ (M0 : X.Modules)
      (hM0 : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M0),
      Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M0 hM0 = M :=
    Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf M
  set W : X.Opens := Closeds.compl (E.support : Closeds X)
  have hM0U : Stacks.SheafOfModules.IsInvertible W.toScheme.presheaf W.toScheme.ringCatIsSheaf
      (M0.restrict (Scheme.Opens.ι W)) := by
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property M0 := hM0.toAlgebraicGeometry
    exact Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  refine exists_zsmul_picardClass_eq_of_isTrivial_restrict M0 hM0 E
    ((Scheme.picardClass_eq_zero_iff W.toScheme _ hM0U).1 ?_)
  exact (schemePullbackClass_opensι_picardClass W M0 hM0 hM0U).symm.trans hM

/-- Every class on `V` is `π^*L + n [𝒪_V(E)]`. -/
private theorem exists_pullbackClassHom_add_zsmul_picardClass_eq
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : AlgebraicGeometry.IsVariety k sY) (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
    ∀ M, ∃ p : Stacks.Picard.ofScheme Y × ℤ,
      Stacks.Picard.pullbackClassHom (blowUpToBase I).toLRSHom.toShHom p.1 +
        p.2 • Stacks.Divisors.picardClass (exceptionalIdeal I) = M := by
  haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  intro M
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ h.1
  haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    le_trans (by norm_num) hc
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1
  haveI := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    sY I h).1
  haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  haveI : IsIntegral (exceptionalIdeal I).subscheme :=
    MMP.Resolution.isIntegral_exceptionalDivisor sY I h hirr hc1
  set U : Y.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hU := two_le_codimension_of_notMem_compl_support I hirr hc
  haveI := isIso_blowUp_restrict_compl_support I
  set W := blowUpToBase I ⁻¹ᵁ U
  set φ := blowUpToBase I ∣_ U
  have hφ : W.ι ≫ blowUpToBase I = φ ≫ U.ι := (morphismRestrict_ι _ _).symm
  -- extend the restriction of `M` to `V ∖ E ≅ Y ∖ Z` across `Z`
  obtain ⟨N, hN, hNc⟩ := Stacks.SheafOfModules.exists_picardClass_eq U.toScheme.presheaf
    U.toScheme.ringCatIsSheaf (Stacks.Picard.schemePullbackClass (inv φ ≫ W.ι) M)
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_restrict_iso_of_forall_uniqueFactorizationMonoid
    (uniqueFactorizationMonoid_stalk_of_smooth sY) U hU N hN
  set x := Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf L hL
  have hLU : Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatIsSheaf
      (L.restrict U.ι) := by
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
      hL.toAlgebraicGeometry
    exact Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  have hx : Stacks.Picard.schemePullbackClass U.ι x =
      Stacks.Picard.schemePullbackClass (inv φ ≫ W.ι) M := by
    rw [schemePullbackClass_opensι_picardClass U L hL hLU, ← hNc]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨eL⟩
  -- `M - π^*L` is trivial off `E`
  set M' := M - Stacks.Picard.schemePullbackClass (blowUpToBase I) x
  have hW : Stacks.Picard.schemePullbackClass W.ι M' = 0 := by
    have : Stacks.Picard.schemePullbackClass W.ι
        (Stacks.Picard.schemePullbackClass (blowUpToBase I) x) =
        Stacks.Picard.schemePullbackClass W.ι M := by
      rw [Stacks.Picard.schemePullbackClass_comp, hφ, ← Stacks.Picard.schemePullbackClass_comp,
        hx, Stacks.Picard.schemePullbackClass_comp, IsIso.hom_inv_id_assoc]
    change Stacks.Picard.schemePullbackClassHom W.ι M' = 0
    rw [map_sub, sub_eq_zero]
    exact this.symm
  have hWE : W = (exceptionalIdeal I).support.compl :=
    preimage_compl_support_eq_compl_support_exceptionalIdeal I
  obtain ⟨n, hn⟩ := exists_zsmul_picardClass_eq_of_schemePullbackClass_eq_zero
    (exceptionalIdeal I) M' (by
      rw [← (blowUp I).isoOfEq_hom_ι hWE.symm, ← Stacks.Picard.schemePullbackClass_comp, hW]
      exact map_zero (Stacks.Picard.schemePullbackClassHom _))
  refine ⟨(x, n), ?_⟩
  change Stacks.Picard.schemePullbackClass (blowUpToBase I) x + n • _ = M
  rw [hn]
  exact add_sub_cancel _ M

end MMP.Proofs.lem_mmp_threefold_smooth_blowup_picard

namespace MMP.Threefold.Resolution

@[expose] public section

open MMP.Proofs.lem_mmp_threefold_smooth_blowup_picard in
/-- **The Picard group of a smooth blow-up.** Let `Y` be a smooth variety over `k` and
`Z = V(I)` a smooth irreducible closed subscheme of codimension `≥ 2`, with blow-up
`π : V ⟶ Y` and exceptional divisor `E`. Then `Pic V = π^* Pic Y ⊕ ℤ [𝒪_V(E)]`: the map
`(L, n) ↦ π^*L + n [𝒪_V(E)]` from `Pic Y × ℤ` to `Pic V` is bijective. -/
@[mmp "lem_mmp_threefold_smooth_blowup_picard"]
public theorem bijective_pullbackClassHom_add_zsmul_picardClass_exceptionalIdeal
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : AlgebraicGeometry.IsVariety k sY) (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
    Function.Bijective fun p : Stacks.Picard.ofScheme Y × ℤ =>
      Stacks.Picard.pullbackClassHom (blowUpToBase I).toLRSHom.toShHom p.1 +
        p.2 • Stacks.Divisors.picardClass (exceptionalIdeal I) := by
  haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  have key : Function.Injective
      ((Stacks.Picard.pullbackClassHom (blowUpToBase I).toLRSHom.toShHom).coprod
        (zmultiplesHom _ (Stacks.Divisors.picardClass (exceptionalIdeal I)))) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    simp only [AddMonoidHom.coprod_apply, zmultiplesHom_apply] at hx
    have hn := eq_zero_of_pullbackClassHom_add_zsmul_picardClass_eq_zero sY hY I h hirr hc
      x.1 x.2 hx
    rw [hn, zero_smul, add_zero] at hx
    exact Prod.ext (pullbackClassHom_blowUpToBase_injective sY hY I h hirr hc
      (hx.trans (map_zero _).symm)) hn
  refine ⟨fun p q hpq => key ?_,
    exists_pullbackClassHom_add_zsmul_picardClass_eq sY hY I h hirr hc⟩
  simpa only [AddMonoidHom.coprod_apply, zmultiplesHom_apply] using hpq

end

end MMP.Threefold.Resolution

end

/-!
## The blow-up of a smooth variety along a smooth centre

Let `Y` be a smooth variety over a field `k`, `Z ⊆ Y` a smooth irreducible closed subscheme of
codimension `c ≥ 2` with ideal sheaf `I`, and `π : X = Bl_Z Y ⟶ Y` the blow-up. Then `X` is a
smooth variety; `π` is projective, birational and an isomorphism over `Y ∖ Z`; the exceptional
divisor `E = π⁻¹(Z)` is smooth and a prime divisor; for every `z ∈ Z` the fibre over `z` is
`ℙ^{c-1}_{κ(z)}`, on which `𝒪_X(E)` restricts to `𝒪(-1)`; `K_X ∼ π^*K_Y + (c - 1)E`; and
`Pic X = π^* Pic Y ⊕ ℤ [𝒪_X(E)]`. If `Y` is projective, so is `X`.

### Main results

* `MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_canonicalDivisor_picardGroup`: the
  statement above.

### Implementation notes

* The centre is given by its ideal sheaf `I` with `MMP.Resolution.IsSmoothBlowup` (both `Y` and
  `Z = V(I)` smooth over `k`); `X` is `AlgebraicGeometry.blowUp I`, `π` is `blowUpToBase I`, and
  `E` is the closed subscheme cut out by `exceptionalIdeal I`, the scheme-theoretic inverse image
  `I 𝒪_X` of the centre.
* Projectivity of `π` is `AlgebraicGeometry.IsProjective` (EGA's notion, Stacks 01W8);
  projectivity of the varieties is `MMP.Mori.IsProjectiveVariety`. Birationality is
  `MMP.Mori.IsBirationalMorphism`.
* The fibre `π⁻¹(z)` over `z ∈ Z` is the fibre of `E ⟶ Z` over `z`, a `κ(z)`-scheme, identified
  with `MMP.Intersection.ProjSpace κ(z) (ULift (Fin c))` (`c` homogeneous coordinates) over
  `Spec κ(z)`; `𝒪(-1)` is the twisting sheaf of the polynomial grading. Over an algebraically
  closed field and a closed point `z` this is `ℙ^{c-1}_k`.
* `K_X ∼ π^*K_Y + (c - 1)E` is stated for every canonical divisor `K_Y` of `Y`
  (`MMP.Mori.Divisor.IsCanonicalDivisor`): the divisor `π^*K_Y + (c - 1)E`, with `π^*` the
  pull-back `MMP.Mori.Divisor.pullback` of Cartier divisors, is a canonical divisor of `X`, and
  every canonical divisor of `X` is linearly equivalent to it.
* The Picard decomposition is the bijectivity of
  `(L, n) ↦ π^*L + n [𝒪_X(E)] : Pic Y × ℤ → Pic X`, with `π^*` the pull-back homomorphism
  `Stacks.SheafOfModules.pullbackPicardHom` and `[𝒪_X(E)]` the class
  `Stacks.Divisors.picardClass` of the effective Cartier divisor `E`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.4, 2.29
* [Stacks Project, Tags 01W8, 02OS, 0C4P]
-/

section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP MMP.Threefold.Resolution MMP.Mori MMP.Resolution Stacks.AlgebraicGeometry

namespace MMP.Proofs.lem_mmp_foundation_km_smooth_blowup_full_package

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a smooth scheme every point, in particular the generic point of every prime divisor, lies
in the smooth locus. -/
private theorem genericPoint_mem_smoothLocus {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} (hS : IsSmoothScheme sX) (Γ : Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ smoothLocus sX := by
  rw [show smoothLocus sX = ⊤ from hS]; trivial

/-- **The pull-back of a nonzero rational form along a smooth blow-up is nonzero.** Along any
prime divisor `F` of the blow-up a generator of the top forms of `𝒪_{Y,π(F)}` maps to `g` times a
generator of the top forms of `𝒪_{X,F}` with `g ≠ 0`, so the coefficient of `π^*τ` is the image of
the (nonzero) coefficient of `τ` times `g^m`. -/
private theorem pullbackRationalPluriForms_blowUpToBase_ne_zero {k : Type v} [Field k]
    {Y : Scheme.{v}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] (I : Y.IdealSheafData)
    (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y)) {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc1 : 1 ≤ c) {d : ℕ} (hd : topologicalKrullDim Y = d) {m : ℤ}
    {τ : RationalPluriForms sY d m} (hτ : τ ≠ 0) :
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr (hc ▸ by exact_mod_cast hc1)
    haveI := isDominant_blowUpToBase I hirr (hc ▸ by exact_mod_cast hc1)
    pullbackRationalPluriForms sY (blowUpToBase I) τ ≠ 0 := by
  have hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast hc1
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  have := isDominant_blowUpToBase I hirr hc1'
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  set f := blowUpToBase I
  set F : MMP.Mori.PrimeDivisor (blowUp I) := exceptionalPrimeDivisor sY I h hirr hc1'
  obtain ⟨σA, hσA, h0A, σB, hσB, h0B, g, hrel, hg, -⟩ :=
    exists_topForms_rel I sY h hirr hc hc1 hd F
  let := stalkAlgebra sY (f F.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (f F.genericPoint)
  let := stalkAlgebra (f ≫ sY) F.genericPoint
  let := functionFieldAlgebra (f ≫ sY)
  have := isScalarTower_stalk_functionField (f ≫ sY) F.genericPoint
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  let := (f.stalkMap F.genericPoint).hom.toAlgebra
  have := isScalarTower_stalkMap sY f F.genericPoint
  let : Algebra (Y.presheaf.stalk (f F.genericPoint)) (blowUp I).functionField :=
    ((algebraMap Y.functionField (blowUp I).functionField).comp
      (algebraMap (Y.presheaf.stalk (f F.genericPoint)) Y.functionField)).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f F.genericPoint)) Y.functionField
      (blowUp I).functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (Y.presheaf.stalk (f F.genericPoint)) F.localRing
      (blowUp I).functionField :=
    IsScalarTower.of_algebraMap_eq fun a => functionFieldMap_algebraMap_stalk f F.genericPoint a
  have : IsScalarTower k (Y.presheaf.stalk (f F.genericPoint)) (blowUp I).functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k Y.functionField (blowUp I).functionField,
        IsScalarTower.algebraMap_apply k (Y.presheaf.stalk (f F.genericPoint)) Y.functionField]
      rfl
  have hcoeff := formCoeff_pullbackForms_of_topFormsMap_eq_smul (K := Y.functionField)
    (K' := (blowUp I).functionField) hσA h0A hσB h0B hrel hg τ
  have hne : formCoeff (k := k) (Y.presheaf.stalk (f F.genericPoint)) hσA h0A τ ≠ 0 :=
    fun h0 => hτ ((formCoeff_eq_zero_iff hσA h0A τ).mp h0)
  intro h0
  change pullbackForms (K := Y.functionField) (K' := (blowUp I).functionField) m τ = 0 at h0
  rw [h0, (formCoeff_eq_zero_iff hσB h0B _).mpr rfl] at hcoeff
  exact mul_ne_zero ((map_ne_zero _).mpr hne) (zpow_ne_zero _ hg) hcoeff.symm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
/-- **The divisor of a top form on a smooth variety is canonical.** On a variety `X` smooth over
`k` of dimension `n`, the divisor of a nonzero rational `n`-form `τ` is a canonical divisor, and
every canonical divisor is linearly equivalent to it: a canonical divisor `K₀` exists and is
`div ω` for a rational top form `ω`, the top forms are a line so `τ = f • ω`, and then
`div τ = div f + div ω`. -/
private theorem isCanonicalDivisor_divisorOfForm_of_smooth {k : Type v} [Field k]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] [Smooth sX]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sX n ∧
      ∀ K : Divisor X, K.IsCanonicalDivisor sX n → K.LinearlyEquivalent (divisorOfForm τ) := by
  have hS : IsSmoothScheme sX := (MMP.Mori.isSmoothScheme_iff (f := sX)).mpr inferInstance
  have hsm := genericPoint_mem_smoothLocus hS
  have hX : IsNormalVariety k sX := ⟨inferInstance, inferInstance⟩
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sX hS hn
  obtain ⟨ω, hω0, hω⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hX hsm hK₀
  let := functionFieldAlgebra sX
  have h1 := MMP.Positivity.finrank_topForms_functionField_eq_one hX hsm hn
  let b : Module.Basis Unit X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]) :=
    Module.basisUnique Unit h1
  set cω := (ZTensorPower.basis b 1).repr ω () with hcω_def
  set cτ := (ZTensorPower.basis b 1).repr τ () with hcτ_def
  have hcω : cω ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hcτ : cτ ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  have hτω : τ = (cτ * cω⁻¹) • ω := (ZTensorPower.basis b 1).ext_elem fun i => by
    obtain rfl : i = () := rfl
    change cτ = (ZTensorPower.basis b 1).repr ((cτ * cω⁻¹) •
      (show ZTensorPower X.functionField (⋀[X.functionField]^n Ω[X.functionField⁄k]) 1 from ω)) ()
    rw [(ZTensorPower.basis b 1).repr.map_smul, Finsupp.smul_apply, smul_eq_mul]
    change cτ = cτ * cω⁻¹ * cω
    rw [mul_assoc, inv_mul_cancel₀ hcω, mul_one]
  have hf : cτ * cω⁻¹ ≠ 0 := mul_ne_zero hcτ (inv_ne_zero hcω)
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hf
  have hlin : (divisorOfForm τ).LinearlyEquivalent K₀ := by
    refine ⟨φ, ?_⟩
    ext Γ
    let := stalkAlgebra sX Γ.genericPoint
    have := isScalarTower_stalk_functionField sX Γ.genericPoint
    have hsmul : Γ.ordForm ((cτ * cω⁻¹) • ω) =
        X.ord (cτ * cω⁻¹) Γ.genericPoint + Γ.ordForm ω :=
      ordAt_smul (k := k) Γ.ord_mul_of_ne_zero (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
        (exists_topForms_generator_stalk sX hn Γ.genericPoint) hf hω0
    rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, coeff_divisorOfForm, ← hω Γ,
      hτω, hsmul]
    ring
  exact ⟨hK₀.of_linearlyEquivalent hlin, fun K hK =>
    MMP.Flips.linearlyEquivalent_of_isCanonicalDivisor hS hK (hK₀.of_linearlyEquivalent hlin)⟩

end MMP.Proofs.lem_mmp_foundation_km_smooth_blowup_full_package

namespace MMP.Threefold.Resolution

@[expose] public section

attribute [local instance] MvPolynomial.gradedAlgebra

open MMP.Proofs.lem_mmp_foundation_km_smooth_blowup_full_package
  MMP.Proofs.lem_mmp_threefold_smooth_blowup_picard in
/-- **The blow-up of a smooth variety along a smooth centre.** Let `Y` be a smooth variety over
`k`, `Z = V(I)` a smooth irreducible closed subscheme of codimension `c ≥ 2`, and
`π : X = Bl_Z Y ⟶ Y` the blow-up. Then `X` is a variety smooth over `k`; `π` is projective,
birational and an isomorphism over `Y ∖ Z`; if `Y` is a projective variety, so is `X`; the
exceptional divisor `E = π⁻¹(Z)` is smooth over `k`; for every `z ∈ Z` the fibre of `E ⟶ Z`
over `z` is `ℙ^{c-1}_{κ(z)}` over `κ(z)`, with `𝒪_X(E)` restricting to `𝒪(-1)`; the map
`(L, n) ↦ π^*L + n [𝒪_X(E)]` is an isomorphism `Pic Y × ℤ ≅ Pic X`; and `E` is a prime divisor
such that, for every canonical divisor `K_Y` of `Y`, `π^*K_Y + (c - 1)E` is a canonical divisor
of `X` to which every canonical divisor of `X` is linearly equivalent. -/
@[mmp "lem_mmp_foundation_km_smooth_blowup_full_package"]
public theorem isVariety_smooth_blowUpToBase_canonicalDivisor_picardGroup
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc2 : 2 ≤ c) :
    haveI : IsIntegral Y := hY.toIsIntegral
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    haveI : Smooth sY := smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    haveI hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
      hc ▸ by exact_mod_cast le_trans (by norm_num) hc2
    haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc1
    haveI := isDominant_blowUpToBase I hirr hc1
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
    haveI := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
    haveI := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
    Mori.IsVariety k (blowUpToBase I ≫ sY) ∧ Smooth (blowUpToBase I ≫ sY) ∧
      IsProjective (blowUpToBase I) ∧ IsBirationalMorphism (blowUpToBase I) ∧
      IsIso (blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens)) ∧
      (Mori.IsProjectiveVariety k sY → Mori.IsProjectiveVariety k (blowUpToBase I ≫ sY)) ∧
      Smooth ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ sY) ∧
      (∀ z : I.subscheme,
        ∃ e : (exceptionalSubschemeMap I).fiber z ≅
            MMP.Intersection.ProjSpace (I.subscheme.residueField z) (ULift.{u} (Fin c)),
          e.hom ≫ MMP.Intersection.ProjSpace.toSpec (I.subscheme.residueField z) _ =
              (exceptionalSubschemeMap I).fiberToSpecResidueField z ∧
            Nonempty ((Scheme.Modules.pullback ((exceptionalSubschemeMap I).fiberι z ≫
                (exceptionalIdeal I).subschemeι)).obj
                  (Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I)) ≅
              (Scheme.Modules.pullback e.hom).obj
                (ProjectiveSpectrum.Proj.twistingSheaf
                  (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin c))
                    (I.subscheme.residueField z)) (-1)))) ∧
      Function.Bijective ((Stacks.SheafOfModules.pullbackPicardHom (blowUpToBase I)).coprod
        (zmultiplesHom _
          (Stacks.Divisors.picardClass (exceptionalIdeal I) : (blowUp I).picardGroup))) ∧
      ∃ E : Mori.PrimeDivisor (blowUp I), E.idealSheaf = exceptionalIdeal I ∧
        ∀ (n : ℕ) (KY : Mori.Divisor Y), KY.IsCanonicalDivisor sY n →
          (KY.pullback (MMP.Fourfold.isCartier_of_isSmoothScheme h.1 KY)
              (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (blowUpToBase I)
                KY) +
            ((c : ℤ) - 1) • Finsupp.single E 1).IsCanonicalDivisor (blowUpToBase I ≫ sY) n ∧
          ∀ KX : Mori.Divisor (blowUp I), KX.IsCanonicalDivisor (blowUpToBase I ≫ sY) n →
            KX.LinearlyEquivalent
              (KY.pullback (MMP.Fourfold.isCartier_of_isSmoothScheme h.1 KY)
                (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (blowUpToBase I)
                  KY) +
              ((c : ℤ) - 1) • Finsupp.single E 1) := by
  have : IsIntegral Y := hY.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sY
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast le_trans (by norm_num) hc2
  have hc2' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast hc2
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have := isDominant_blowUpToBase I hirr hc1
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  have := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  obtain ⟨hsm, hproj, hbir, hiso, -, hprojY⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h hirr hc2'
  obtain ⟨hE, -, -⟩ := smooth_exceptionalDivisor_and_fiber_iso_projSpace sY I h hirr hc2'
  obtain ⟨c', hc', hfib⟩ :=
    exists_fiber_iso_projSpace_pullback_invertibleSheaf_exceptionalIdeal sY I h hirr hc2'
  obtain rfl : c = c' := by exact_mod_cast hc.trans hc'.symm
  have : IsProjective (blowUpToBase I) := hproj
  have hvar : AlgebraicGeometry.IsVariety k (blowUpToBase I ≫ sY) := {}
  refine ⟨hvar, hsm, hproj, hbir, hiso, fun hP => ?_, hE, hfib, ?_, ?_⟩
  · have : AlgebraicGeometry.IsProjective sY := (isProjectiveVariety_iff_isProjective k sY).mp hP
    exact (isProjectiveVariety_iff_isProjective k _).mpr (hprojY this)
  · convert bijective_pullbackClassHom_add_zsmul_picardClass_exceptionalIdeal sY hY I h hirr hc2'
      using 1
    funext p
    simp only [AddMonoidHom.coprod_apply, zmultiplesHom_apply]
    rw [pullbackPicardHom_apply_eq_pullbackClassHom]
  · refine ⟨exceptionalPrimeDivisor sY I h hirr hc1, rfl, fun n KY hKY => ?_⟩
    have hn := hKY.topologicalKrullDim_eq
    obtain ⟨ω, hω0, hω⟩ :=
      MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus
        ⟨hY, inferInstance⟩ (genericPoint_mem_smoothLocus h.1) hKY
    obtain rfl : KY = divisorOfForm ω := by
      ext Γ
      rw [coeff_divisorOfForm]
      exact (hω Γ).symm
    have hc1n : 1 ≤ c := by omega
    rw [← divisorOfForm_pullbackRationalPluriForms_blowUpToBase I sY h hirr hc hc1n hn ω hω0]
    exact isCanonicalDivisor_divisorOfForm_of_smooth (blowUpToBase I ≫ sY)
      (topologicalKrullDim_blowUp sY I h hirr hc1 hn)
      (pullbackRationalPluriForms_blowUpToBase_ne_zero sY I h hirr hc hc1n hn hω0)

end

end MMP.Threefold.Resolution

end

/-!
## The blow-up of a smooth variety at a closed point

Let `X` be a smooth variety of dimension `d ≥ 2` over an algebraically closed field `k`, let
`x ∈ X` be a closed point and `π : B_x X ⟶ X` the blow-up of the reduced point `x`. Then `B_x X`
is a variety smooth over `k`; `π` is projective, birational and an isomorphism over `X ∖ {x}`;
the exceptional subscheme `E_x = π⁻¹(x)` is reduced, has underlying set `π⁻¹{x}`, is a prime
divisor of `B_x X` and is isomorphic over `k` to `ℙ^{d-1}_k`; and `B_x X` is projective when `X`
is.

### Main results

* `MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_vanishingIdeal_singleton`: the
  statement above.

### Implementation notes

* The point `x` is given with the closedness of `{x}`; its ideal sheaf is
  `Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`, so `B_x X` is `AlgebraicGeometry.blowUp` of
  it and `π` is `blowUpToBase`. The fibre `π⁻¹(x)` is the closed subscheme cut out by
  `exceptionalIdeal`, the inverse-image ideal `𝔪_x 𝒪_{B_x X}`; saying it is the ideal sheaf of a
  prime divisor says that this scheme-theoretic fibre is reduced and irreducible of
  codimension one.
* Projectivity of `π` is `AlgebraicGeometry.IsProjective` (EGA, Stacks 01W8); projectivity of
  the varieties is `MMP.Mori.IsProjectiveVariety`; birationality is
  `MMP.Mori.IsBirationalMorphism`.
* `ℙ^{d-1}_k` is `MMP.Intersection.ProjSpace k (ULift (Fin d))` (`d` homogeneous coordinates),
  and the isomorphism lies over `Spec k`.
* The dimension is `topologicalKrullDim X = d`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 0.4
* [Stacks Project, Tags 01W8, 0C4P]
-/

section

universe u uProof

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP.Mori

namespace MMP.Proofs.lem_mmp_foundation_km_smooth_point_blowup

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.ProjectiveCohomology in
/-- Projective space is invariant under isomorphisms of the coefficient field, over `Spec`. -/
private noncomputable def projSpaceCongr {K L : Type uProof} [Field K] [Field L] (φ : K ≃+* L)
    (ι : Type uProof) : MMP.Intersection.ProjSpace L ι ≅ MMP.Intersection.ProjSpace K ι where
  hom := Proj.map (polyGradedMap ι φ.toRingHom) (irrelevant_le_map_polyGradedMap ι _)
  inv := Proj.map (polyGradedMap ι φ.symm.toRingHom) (irrelevant_le_map_polyGradedMap ι _)
  hom_inv_id := by
    rw [← Proj.map_comp]
    refine (MMP.Intersection.projMap_congr _ _ _ _ ?_).trans Proj.map_id
    exact GradedRingHom.ext fun p => by
      simp [polyGradedMap, MvPolynomial.map_map, MvPolynomial.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    refine (MMP.Intersection.projMap_congr _ _ _ _ ?_).trans Proj.map_id
    exact GradedRingHom.ext fun p => by
      simp [polyGradedMap, MvPolynomial.map_map, MvPolynomial.map_id]

private theorem projSpaceCongr_hom_toSpec {K L : Type uProof} [Field K] [Field L] (φ : K ≃+* L)
    (ι : Type uProof) : (projSpaceCongr φ ι).hom ≫ MMP.Intersection.ProjSpace.toSpec K ι =
      MMP.Intersection.ProjSpace.toSpec L ι ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [projSpaceCongr, MMP.Intersection.ProjSpace.toSpec, MMP.Intersection.ProjSpace.toSpec,
    Proj.map_toSpecZero_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine RingHom.ext fun a => Subtype.ext ?_
  simp [Stacks.ProjectiveCohomology.polyGradedMap]

/-- A closed point of a variety of dimension `d` over an algebraically closed field has local
ring of dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_isClosed {k : Type uProof} [Field k] [IsAlgClosed k]
    {Y : Scheme.{uProof}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) {d : ℕ}
    (hdim : topologicalKrullDim Y = d) (q : Y) (hq : IsClosed ({q} : Set Y)) :
    ringKrullDim (Y.presheaf.stalk q) = d := by
  have := hY.toIsIntegral
  have := hY.toLocallyOfFiniteType
  have : IsDominant sY := ⟨by
    have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    exact Function.Surjective.denseRange (fun s => ⟨Classical.arbitrary Y, Subsingleton.elim _ _⟩)⟩
  have hcat : Scheme.IsUniversallyCatenary (Spec (.of k)) :=
    Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field k (𝟙 _)
  have key := fun y => ringKrullDim_stalk_add_trdeg_residueField_eq sY hcat y
  have h0 := fun y : Y => MMP.Mori.SurfaceAux.ringKrullDim_stalk_spec_field (sY y)
  letI : ∀ y : Y, Algebra ((Spec (.of k)).residueField (sY y)) (Y.residueField y) :=
    fun y => (sY.residueFieldMap y).hom.toAlgebra
  obtain ⟨T, hT⟩ : ∃ T : WithBot ℕ∞, ∀ y, ringKrullDim (Y.presheaf.stalk y) +
      ((Cardinal.toNat (Algebra.trdeg ((Spec (.of k)).residueField (sY y)) (Y.residueField y)) :
        ℕ) : WithBot ℕ∞) = T :=
    ⟨_, fun y => (key y).trans (by rw [h0 y, zero_add])⟩
  have hle : ∀ y, ringKrullDim (Y.presheaf.stalk y) ≤ T := fun y =>
    (le_add_of_nonneg_right (by positivity)).trans_eq (hT y)
  have hdimT : topologicalKrullDim Y ≤ T := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact iSup_le hle
  have hq0 := MMP.Mori.SurfaceAux.trdeg_residue_eq_zero sY q hq
  have hTq := hT q
  rw [hq0] at hTq
  simp at hTq
  have h2 : ringKrullDim (Y.presheaf.stalk q) ≤ d := by
    rw [← hdim, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup (fun y : Y => ringKrullDim (Y.presheaf.stalk y)) q
  rw [hdim] at hdimT
  exact le_antisymm h2 (hTq ▸ hdimT)

/-- The closed point `{x}` of a variety of dimension `d` over an algebraically closed field has
codimension `d`. -/
private theorem codimension_support_vanishingIdeal_singleton {k : Type uProof} [Field k]
    [IsAlgClosed k] {X : Scheme.{uProof}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX)
    {d : ℕ} (hd : topologicalKrullDim X = d) {x : X} (hx : IsClosed ({x} : Set X))
    (hirr : IsIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support : Set X)) :
    codimension (⟨_, hirr,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support.isClosed⟩ :
        IrreducibleCloseds X) = d := by
  have heq : (⟨_, hirr,
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support.isClosed⟩ :
        IrreducibleCloseds X) = IrreducibleCloseds.closureSingleton x := by
    ext1
    exact (MMP.Threefold.Resolution.support_vanishingIdeal_singleton hx).trans
      hx.closure_eq.symm
  rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  have h := ringKrullDim_stalk_eq_of_isClosed sX hX hd x hx
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

open Stacks.AlgebraicGeometry in
/-- If the centre of a blow-up maps isomorphically to `Spec k`, the exceptional subscheme is the
fibre over the unique point of the centre, so an identification of that fibre with
`ℙ^{c-1}_{κ(z)}` over `κ(z)` gives one of the exceptional subscheme with `ℙ^{c-1}_k` over `k`. -/
private theorem exists_iso_projSpace_of_isIso_subschemeι_comp {k : Type uProof} [Field k]
    {X : Scheme.{uProof}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    [hg : IsIso (I.subschemeι ≫ sX)] {c : ℕ} (z : I.subscheme)
    (e₂ : (exceptionalSubschemeMap I).fiber z ≅
      MMP.Intersection.ProjSpace (I.subscheme.residueField z) (ULift.{uProof} (Fin c)))
    (he₂ : e₂.hom ≫ MMP.Intersection.ProjSpace.toSpec (I.subscheme.residueField z) _ =
      (exceptionalSubschemeMap I).fiberToSpecResidueField z) :
    ∃ e : (exceptionalIdeal I).subscheme ≅ MMP.Intersection.ProjSpace k (ULift.{uProof} (Fin c)),
      e.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ =
        (exceptionalIdeal I).subschemeι ≫ blowUpToBase I ≫ sX := by
  have : Subsingleton I.subscheme :=
    (asIso (I.subschemeι ≫ sX)).hom.homeomorph.injective.subsingleton
  -- `Spec κ(z) ⟶ I.subscheme` is a surjective flat monomorphism, hence an isomorphism.
  have : Flat (I.subscheme.fromSpecResidueField z ≫ I.subschemeι ≫ sX) :=
    Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral _
  have : Flat (I.subscheme.fromSpecResidueField z) := by
    rw [show I.subscheme.fromSpecResidueField z =
      (I.subscheme.fromSpecResidueField z ≫ I.subschemeι ≫ sX) ≫ inv (I.subschemeι ≫ sX) by simp]
    infer_instance
  have : Surjective (I.subscheme.fromSpecResidueField z) :=
    ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hj : IsIso (I.subscheme.fromSpecResidueField z) := Flat.isIso_of_surjective_of_mono _
  have hjg : IsIso (I.subscheme.fromSpecResidueField z ≫ I.subschemeι ≫ sX) :=
    IsIso.comp_isIso' hj hg
  have : IsIso ((exceptionalSubschemeMap I).fiberι z) :=
    inferInstanceAs (IsIso (Limits.pullback.fst _ _))
  let φ : k ≃+* I.subscheme.residueField z :=
    (Scheme.Spec.preimageIso (@asIso _ _ _ _ _ hjg)).unop.commRingCatIsoToRingEquiv
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) =
      I.subscheme.fromSpecResidueField z ≫ I.subschemeι ≫ sX := by
    change Scheme.Spec.map (Scheme.Spec.preimage _) = _
    exact Scheme.Spec.map_preimage _
  refine ⟨(asIso ((exceptionalSubschemeMap I).fiberι z)).symm ≪≫ e₂ ≪≫ projSpaceCongr φ _, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, projSpaceCongr_hom_toSpec, hφ]
  rw [reassoc_of% he₂, ← Scheme.Hom.fiber_fac_assoc, IsIso.inv_hom_id_assoc,
    exceptionalSubschemeMap, Scheme.IdealSheafData.subschemeMap_subschemeι_assoc]

end MMP.Proofs.lem_mmp_foundation_km_smooth_point_blowup

namespace MMP.Threefold.Resolution

@[expose] public section

open MMP.Proofs.lem_mmp_foundation_km_smooth_point_blowup in
/-- **The blow-up of a smooth variety at a closed point.** Let `X` be a variety of dimension
`d ≥ 2`, smooth over an algebraically closed field `k`, let `x ∈ X` be a closed point, and let
`π : B_x X ⟶ X` be the blow-up of the reduced point `x`. Then `B_x X` is a variety smooth over
`k`; `π` is projective, birational, and an isomorphism over `X ∖ {x}`; if `X` is a projective
variety, so is `B_x X`; and there is a prime divisor `E` of `B_x X` whose ideal sheaf is the
inverse-image ideal `exceptionalIdeal` of `x` and whose support is `π⁻¹{x}`, and the
exceptional subscheme is isomorphic over `k` to `ℙ^{d-1}_k`. -/
@[mmp "lem_mmp_foundation_km_smooth_point_blowup"]
public theorem isVariety_smooth_blowUpToBase_vanishingIdeal_singleton
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k sX) [Smooth sX] {d : ℕ} (hd : topologicalKrullDim X = d)
    (hd2 : 2 ≤ d) {x : X} (hx : IsClosed ({x} : Set X)) :
    Mori.IsVariety k (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX) ∧
      Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX) ∧
      IsProjective (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) ∧
      IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) ∧
      IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ∣_
        (⟨{x}ᶜ, hx.isOpen_compl⟩ : X.Opens)) ∧
      (Mori.IsProjectiveVariety k sX → Mori.IsProjectiveVariety k
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX)) ∧
      ∃ E : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)),
        E.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ∧
        ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).support :
            Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))) =
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ⁻¹' {x} ∧
        ∃ e : (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).subscheme ≅
            MMP.Intersection.ProjSpace k (ULift.{u} (Fin d)),
          e.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ =
            (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).subschemeι ≫
              blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) ≫ sX := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  have : IsIntegral X := hX.toIsIntegral
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hsb : MMP.Resolution.IsSmoothBlowup sX I :=
    isSmoothBlowup_vanishingIdeal_singleton sX (MMP.Resolution.isSmoothScheme_of_smooth sX) hx
  have hsupp : (I.support : Set X) = {x} := support_vanishingIdeal_singleton hx
  have hirr := isIrreducible_support_vanishingIdeal_singleton hx
  have hcod := codimension_support_vanishingIdeal_singleton sX hX hd hx hirr
  have hc2 : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) :=
    hcod ▸ by exact_mod_cast hd2
  obtain ⟨hsmooth, hproj, hbir, hiso, -, hprojvar⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sX I hsb hirr hc2
  obtain ⟨-, ⟨F, hF⟩, c, hc, hfib⟩ :=
    smooth_exceptionalDivisor_and_fiber_iso_projSpace sX I hsb hirr hc2
  obtain rfl : c = d := by exact_mod_cast hc.trans hcod
  -- `I ≠ ⊥`, for otherwise `X = {x}` would have dimension `0 < c`.
  have hIne : I ≠ ⊥ := by
    rintro hI
    have huniv : (Set.univ : Set X) = {x} := by
      rw [← hsupp, hI, Scheme.IdealSheafData.support_bot]; rfl
    have : Subsingleton X := Set.subsingleton_univ_iff.mp (huniv ▸ Set.subsingleton_singleton)
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hd] at h0
    have : c ≤ 0 := by exact_mod_cast h0
    omega
  have : AlgebraicGeometry.IsVariety k sX := hX
  have hvar := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
    sX I hIne).1
  have hopen : (⟨{x}ᶜ, hx.isOpen_compl⟩ : X.Opens) =
      ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ := by
    ext1
    exact congrArg compl hsupp.symm
  have : IsIso (I.subschemeι ≫ sX) := by
    have := isIso_subschemeι_ker_pointOfClosedPoint_comp k sX hx
    rwa [ker_pointOfClosedPoint_eq_vanishingIdeal, ← closeds_singleton_eq_closure hx] at this
  obtain ⟨z, -⟩ : x ∈ Set.range I.subschemeι := by rw [I.range_subschemeι, hsupp]; rfl
  obtain ⟨e₂, he₂⟩ := hfib z
  have : AlgebraicGeometry.IsVariety k (blowUpToBase I ≫ sX) := hvar
  exact ⟨hvar, hsmooth, hproj, hbir, hopen ▸ hiso,
    fun hP => (isProjectiveVariety_iff_isProjective k _).mpr
      (hprojvar ((isProjectiveVariety_iff_isProjective k sX).mp hP)),
    F, hF, Set.ext fun q => hF ▸ mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hx hF q,
    exists_iso_projSpace_of_isIso_subschemeι_comp sX I z e₂ he₂⟩

end

end MMP.Threefold.Resolution

end

/-!
## The blow-up of a variety in a proper closed subscheme

Let `X` be a variety over a field `k`, with structure morphism `f : X ⟶ Spec k`, and let
`Z ⊆ X` be a closed subscheme, given by its quasi-coherent ideal sheaf `I`, whose underlying
closed set `I.support` is not all of `X`. Then the blow-up `B_Z X`, with structure morphism
`blowUpToBase I ≫ f`, is a variety over `k`, and `π_{Z,X} = blowUpToBase I` is projective and
birational.

### Main results

* `MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational_of_support_ne_top`

### Implementation notes

A closed subscheme `Z` of `X` is its ideal sheaf `I : X.IdealSheafData`, and "`Z ≠ X` as sets"
is `I.support ≠ ⊤`. The blow-up `B_Z X` is `AlgebraicGeometry.blowUp I`, the relative `Proj` of
the Rees algebra `⊕ₙ Iⁿ`.

### References

* [Kol07], §2 (blow-ups of closed subschemes)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

section

universe u v

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips.ResolutionInputs

@[expose] public section

/-- **The blow-up of a variety in a proper closed subscheme.** Let `X` be a variety over `k`
with structure morphism `f`, and `Z ⊆ X` a closed subscheme with ideal sheaf `I` whose support
is not all of `X`. Then `B_Z X`, with structure morphism `blowUpToBase I ≫ f`, is a variety
over `k`, and `blowUpToBase I : B_Z X ⟶ X` is projective and birational. -/
@[mmp "lem_mmp_foundation_kr_f_blowup_variety_projective"]
public theorem isVariety_blowUp_and_isProjective_and_isBirational_of_support_ne_top
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (I : X.IdealSheafData) (hZ : I.support ≠ ⊤) :
    IsVariety k (blowUpToBase I ≫ f) ∧ IsProjective (blowUpToBase I) ∧
      IsBirational (blowUpToBase I) := by
  have : IsIntegral X := ‹IsVariety k f›.toIsIntegral
  exact isVariety_blowUp_and_isProjective_and_isBirational f I
    (mt Scheme.IdealSheafData.support_eq_top_iff.mpr hZ)

end

end MMP.Flips.ResolutionInputs

end

/-!
## Reflexive rank-one modules along a flat local map

Let `A → B` be a flat local homomorphism of Noetherian integrally closed local domains, and let
`M` be a finite reflexive `A`-module of rank one. Then the base change `B ⊗[A] M` is a reflexive
`B`-module of rank one, and it is free exactly when `M` is free. Base change is compatible with
the reflexive tensor product `(M ⊗ N)^{**}`, which is the group law of the divisor class group
`Cl(A)` (classes of finite reflexive rank-one modules), and two such modules become isomorphic
over `B` only if they are already isomorphic over `A`; so base change induces an injective
homomorphism `Cl(A) → Cl(B)`. Finally, for a divisorial fractional ideal `I ⊆ K = Frac A` (the
module `A(D)` of a Weil divisor `D`), the multiplication map `B ⊗[A] I → L = Frac B` is
injective and its image `I · B` is again reflexive: it is the divisorial module of the flat
pullback of `D`.

### Main results

* `MMP.isReflexive_baseChange_and_free_iff_of_flat_of_rank_eq_one`: the five assertions above.

### Implementation notes

The class group is not given a type of its own: the group structure is the reflexive tensor
product `Module.Dual A (Module.Dual A (M ⊗[A] N))`, and injectivity on classes is stated as
reflection of isomorphisms between finite reflexive rank-one modules. Rank is `Module.rank`,
which over a domain is the dimension of the generic fibre. A Weil divisor `D` enters through its
divisorial fractional ideal, a finite reflexive `A`-submodule `I` of `K`; the pullback divisor is
read off the image of `LinearMap.liftBaseChange B` of the inclusion `I → L`.
-/

section

universe uA uB uK uL uM

open TensorProduct

namespace MMP.Proofs.lem_mmp_foundation_reflexive_rank_one_flat_local_descent

/-- For a flat `A`-algebra `B` and a finitely presented `A`-module `P`, the canonical
isomorphism `B ⊗[A] Hom_A(P, A) ≃ Hom_B(B ⊗[A] P, B)`. -/
private noncomputable def dualBaseChange (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Type*) [AddCommGroup P] [Module A P]
    [Module.FinitePresentation A P] :
    B ⊗[A] Module.Dual A P ≃ₗ[B] Module.Dual B (B ⊗[A] P) :=
  (Module.FinitePresentation.isBaseChange_map A P A B).equiv ≪≫ₗ
    LinearEquiv.congrRight (AlgebraTensorModule.rid A B B)

/-- `dualBaseChange` sends `b ⊗ f` to `b' ⊗ p ↦ b b' f(p)`. -/
private theorem dualBaseChange_tmul_tmul (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (P : Type*) [AddCommGroup P] [Module A P]
    [Module.FinitePresentation A P] (b b' : B) (f : Module.Dual A P) (p : P) :
    dualBaseChange A B P (b ⊗ₜ f) (b' ⊗ₜ p) = b * (b' * algebraMap A B (f p)) := by
  simp only [dualBaseChange, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul]
  change AlgebraTensorModule.rid A B B ((b • (LinearMap.baseChangeHom A B P A f)) (b' ⊗ₜ p)) = _
  simp [Algebra.smul_def]
  ring

/-- Flat base change over a Noetherian ring preserves reflexivity of finite modules. -/
private theorem isReflexive_baseChange (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [IsNoetherianRing A] (P : Type*) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.IsReflexive A P] : Module.IsReflexive B (B ⊗[A] P) := by
  have := Module.finitePresentation_of_finite A P
  have := Module.finitePresentation_of_finite A (Module.Dual A P)
  let e := dualBaseChange A B P
  let e' := dualBaseChange A B (Module.Dual A P)
  have key : Module.Dual.eval B (B ⊗[A] P) =
      e.symm.dualMap.toLinearMap ∘ₗ e'.toLinearMap ∘ₗ
        ((Module.Dual.eval A P).baseChange B) := by
    refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext fun b => ?_)
    refine LinearMap.ext fun p => ?_
    refine LinearMap.ext fun l => ?_
    obtain ⟨x, rfl⟩ := e.surjective l
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply,
      TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.baseChange_tmul, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply,
      Module.Dual.eval_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' f =>
      rw [dualBaseChange_tmul_tmul, dualBaseChange_tmul_tmul]
      simp only [Module.Dual.eval_apply]
      ring
    | add x y hx hy => simp [map_add, hx, hy]
  refine ⟨?_⟩
  rw [key]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  refine (LinearEquiv.bijective _).comp ((LinearEquiv.bijective _).comp ?_)
  exact (LinearEquiv.ofBijective _ (Module.bijective_dual_eval A P)).baseChange A B _ _ |>.bijective

/-- Base change between domains whose fraction fields form a compatible tower preserves rank
one, the rank being the dimension of the generic fibre. -/
private theorem rank_baseChange_eq {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra A B] (K : Type uK) (L : Type uL) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (M : Type uM) [AddCommGroup M] [Module A M] (hM : Module.rank A M = 1) :
    Module.rank B (B ⊗[A] M) = 1 := by
  have := IsLocalization.tensorProduct_isLocalizedModule (M := B ⊗[A] M) (nonZeroDivisors B) L
  have := IsLocalization.tensorProduct_isLocalizedModule (M := M) (nonZeroDivisors A) K
  have h1 := IsLocalizedModule.lift_rank_eq (nonZeroDivisors B)
    (TensorProduct.mk B L (B ⊗[A] M) 1) le_rfl
  have h2 := IsLocalizedModule.lift_rank_eq (nonZeroDivisors A)
    (TensorProduct.mk A K M 1) le_rfl
  rw [← IsFractionRing.rank_right_eq B L] at h1
  rw [← IsFractionRing.rank_right_eq A K] at h2
  have e1 := (AlgebraTensorModule.cancelBaseChange A B L L M).lift_rank_eq
  have e2 := (AlgebraTensorModule.cancelBaseChange A K L L M).lift_rank_eq
  have h3 : Module.rank L (L ⊗[K] (K ⊗[A] M)) = Cardinal.lift (Module.rank K (K ⊗[A] M)) :=
    Module.rank_baseChange
  rw [h3] at e2
  have k2 : Module.rank K (K ⊗[A] M) = 1 := by simpa [hM] using h2
  have k3 : Module.rank L (L ⊗[A] M) = 1 := by simpa [k2] using e2.symm
  have k4 : Module.rank L (L ⊗[B] (B ⊗[A] M)) = 1 := by simpa [k3] using e1
  simpa [k4] using h1.symm

/-- For a finite `A`-submodule `I` of `Frac A` and a flat `A`-algebra `B`, the multiplication
map `B ⊗[A] I → Frac B` is injective: clearing a denominator identifies it with `B ⊗[A] I → B`. -/
private theorem injective_liftBaseChange {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Flat A B] (K L : Type*) [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule A K) [Module.Finite A I] :
    Function.Injective (LinearMap.liftBaseChange B
      (((Algebra.linearMap K L).restrictScalars A).comp I.subtype)) := by
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A)
    (Module.Finite.iff_fg.mp ‹_›)
  choose g hg using fun x : I => hdI x x.2
  have hinj := IsFractionRing.injective A K
  let g' : I →ₗ[A] A :=
    { toFun := g
      map_add' := fun x y => hinj (by simp [hg, smul_add])
      map_smul' := fun a x => hinj (by simp [hg, Algebra.smul_def]; ring) }
  have hd0 : algebraMap A K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hg' : Function.Injective g' := fun x y hxy => by
    have := congrArg (algebraMap A K) hxy
    simp only [g', LinearMap.coe_mk, AddHom.coe_mk, hg, Algebra.smul_def] at this
    exact Subtype.ext (mul_left_cancel₀ hd0 this)
  have key : ∀ t, algebraMap A L d * LinearMap.liftBaseChange B
      (((Algebra.linearMap K L).restrictScalars A).comp I.subtype) t =
      algebraMap B L (AlgebraTensorModule.rid A B B (g'.baseChange B t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
      have hx := congrArg (algebraMap K L) (hg x)
      simp only [g', LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul,
        AlgebraTensorModule.rid_tmul, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def,
        map_mul, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
        Submodule.coe_subtype, Algebra.linearMap_apply] at hx ⊢
      rw [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L (g x), hx,
        IsScalarTower.algebraMap_apply A K L d]
      ring
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  have hdL : algebraMap A L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (algebraMap K L).injective.ne_iff.mpr hd0 |>.trans_eq (map_zero _)
  intro s t hst
  have h := key s
  rw [hst, key t] at h
  have h2 := (IsFractionRing.injective B L) h
  have h3 := (AlgebraTensorModule.rid A B B).injective h2
  rw [LinearMap.baseChange_eq_ltensor] at h3
  exact ((Module.Flat.lTensor_preserves_injective_linearMap g' hg') h3).symm

/-- Freeness of a finite module descends along a flat local homomorphism of local rings. -/
private theorem free_of_free_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Free B (B ⊗[A] M)] : Module.Free A M := by
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  have := Module.Flat.of_flat_tensorProduct A M B
  exact Module.free_of_flat_of_isLocalRing

/-- An endomorphism of a finite torsion-free module of rank one over an integrally closed
domain is multiplication by a scalar. -/
private theorem exists_eq_smul_id_of_rank_eq_one {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] {P : Type*} [AddCommGroup P] [Module B P] [Module.Finite B P]
    [Module.IsTorsionFree B P] (hP : Module.rank B P = 1) (ψ : P →ₗ[B] P) :
    ∃ c : B, ψ = c • LinearMap.id := by
  let L := FractionRing B
  let j := TensorProduct.mk B L P 1
  have : IsLocalizedModule (nonZeroDivisors B) j :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors B) L
  have hj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors B) j).mp hm
    exact (smul_eq_zero_iff_right (nonZeroDivisors.coe_ne_zero s)).mp hs
  have hrank := IsLocalizedModule.lift_rank_eq (nonZeroDivisors B) j le_rfl
  rw [← IsFractionRing.rank_right_eq B L, hP] at hrank
  have hfin : Module.finrank L (L ⊗[B] P) = 1 :=
    Module.finrank_eq_of_rank_eq (by simpa using hrank)
  obtain ⟨x, hx, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hfin (ψ.baseChange L)
  have hjψ : ∀ p, x • j p = j (ψ p) := fun p => by
    have := congrArg (fun f => f (j p)) hx
    simpa [j] using this.symm
  have hint : IsIntegral B x := by
    refine isIntegral_of_smul_mem_submodule (LinearMap.range j) ?_ ?_ x ?_
    · intro h
      have : Nontrivial P := by
        rw [← rank_pos_iff_nontrivial (R := B), hP]; exact zero_lt_one
      obtain ⟨p, hp⟩ := exists_ne (0 : P)
      have h0 := LinearMap.range_eq_bot.mp h
      exact hp (hj (by simp [h0]))
    · rw [LinearMap.range_eq_map]
      exact (Module.Finite.fg_top (R := B) (M := P)).map j
    · rintro _ ⟨p, rfl⟩
      exact ⟨ψ p, (hjψ p).symm⟩
  obtain ⟨c, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨c, LinearMap.ext fun p => hj ?_⟩
  rw [← hjψ, LinearMap.smul_apply, LinearMap.id_apply, map_smul, algebraMap_smul]

/-- Over an integrally closed domain, if `P` is finite torsion-free of rank one and `e : P ≃ Q`,
then `Hom(P, Q)` is free of rank one on `e`: every linear map `P → Q` is a unique multiple
of `e`. -/
private theorem bijective_toSpanSingleton_of_rank_eq_one {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] {P Q : Type*} [AddCommGroup P] [Module B P] [Module.Finite B P]
    [Module.IsTorsionFree B P] [AddCommGroup Q] [Module B Q] (hP : Module.rank B P = 1)
    (e : P ≃ₗ[B] Q) : Function.Bijective (LinearMap.toSpanSingleton B _ e.toLinearMap) := by
  have : Nontrivial P := by rw [← rank_pos_iff_nontrivial (R := B), hP]; exact zero_lt_one
  obtain ⟨p₀, hp₀⟩ := exists_ne (0 : P)
  refine ⟨fun c d h => ?_, fun g => ?_⟩
  · have h0 : (c - d) • p₀ = 0 := e.injective <| by
      simpa [sub_smul, sub_eq_zero] using congrArg (fun f : P →ₗ[B] Q => f p₀) h
    exact sub_eq_zero.mp ((smul_eq_zero_iff_left hp₀).mp h0)
  · obtain ⟨c, hc⟩ := exists_eq_smul_id_of_rank_eq_one hP (e.symm.toLinearMap ∘ₗ g)
    exact ⟨c, LinearMap.ext fun p => by simpa using (congrArg (fun f => e (f p)) hc).symm⟩

/-- Base change along a flat local map reflects isomorphisms of finite reflexive rank-one
modules over Noetherian integrally closed local domains. -/
private theorem nonempty_linearEquiv_of_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsIntegrallyClosed B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    {M N : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsReflexive A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.IsReflexive A N]
    (hPr : Module.rank B (B ⊗[A] M) = 1) (e : (B ⊗[A] M) ≃ₗ[B] (B ⊗[A] N)) :
    Nonempty (M ≃ₗ[A] N) := by
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  have := Module.finitePresentation_of_finite A M
  have := isReflexive_baseChange A B M
  let E := LinearEquiv.ofBijective _ (bijective_toSpanSingleton_of_rank_eq_one hPr e)
  have hE : ∀ c, E c = c • e.toLinearMap := fun _ => rfl
  -- `Hom_A(M, N)` is free of rank one, since its base change is `Hom_B(B ⊗ M, B ⊗ N) ≅ B`
  have hbc := Module.FinitePresentation.isBaseChange_map A M N B
  let EH : B ⊗[A] (M →ₗ[A] N) ≃ₗ[B] B := hbc.equiv ≪≫ₗ E.symm
  have : Module.Free B (B ⊗[A] (M →ₗ[A] N)) := Module.Free.of_equiv EH.symm
  have : Module.Free A (M →ₗ[A] N) := free_of_free_baseChange (B := B) _
  have hH : Module.finrank A (M →ₗ[A] N) = 1 := by
    rw [← Module.finrank_baseChange (R := B), EH.finrank_eq, Module.finrank_self]
  let b := Module.finBasisOfFinrankEq A (M →ₗ[A] N) hH
  let φ := b 0
  -- `e` is a multiple of the base change of `φ`, and conversely
  obtain ⟨c, hc⟩ := E.surjective (φ.baseChange B)
  obtain ⟨d, hd⟩ : ∃ d : B, e.toLinearMap = d • φ.baseChange B := by
    obtain ⟨t, ht⟩ := hbc.equiv.surjective e.toLinearMap
    refine ⟨(b.baseChange B).repr t 0, ?_⟩
    conv_lhs => rw [← ht, ← (b.baseChange B).sum_repr t]
    rw [Fin.sum_univ_one, Module.Basis.baseChange_apply, map_smul, IsBaseChange.equiv_tmul,
      one_smul]
    rfl
  have hdc : d * c = 1 := E.injective <| by
    rw [hE, hE, mul_smul, ← hE, hc, ← hd, one_smul]
  have hu : IsUnit c := IsUnit.of_mul_eq_one_right d hdc
  have hφB : Function.Bijective (φ.baseChange B) := by
    rw [← hc, hE]
    exact (MulAction.bijective hu.unit).comp e.bijective
  rw [LinearMap.baseChange_eq_ltensor, Module.FaithfullyFlat.lTensor_bijective_iff_bijective]
    at hφB
  exact ⟨LinearEquiv.ofBijective φ hφB⟩

end MMP.Proofs.lem_mmp_foundation_reflexive_rank_one_flat_local_descent

namespace MMP

@[expose] public section

open MMP.Proofs.lem_mmp_foundation_reflexive_rank_one_flat_local_descent in
/-- Let `A → B` be a flat local map of Noetherian integrally closed local domains with fraction
fields `K → L`, and `M` a finite reflexive `A`-module of rank one. Then `B ⊗[A] M` is reflexive
of rank one; it is free iff `M` is; base change commutes with the reflexive tensor product and
reflects isomorphisms of finite reflexive rank-one modules (so `Cl(A) → Cl(B)` is an injective
homomorphism); and for every finite reflexive `A`-submodule `I` of `K` the multiplication map
`B ⊗[A] I → L` is injective with reflexive image `I · B`. -/
@[mmp "lem_mmp_foundation_reflexive_rank_one_flat_local_descent"]
public theorem isReflexive_baseChange_and_free_iff_of_flat_of_rank_eq_one
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsIntegrallyClosed A] [IsIntegrallyClosed B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsReflexive A M]
    (hM : Module.rank A M = 1) :
    (Module.IsReflexive B (B ⊗[A] M) ∧ Module.rank B (B ⊗[A] M) = 1) ∧
    (Module.Free B (B ⊗[A] M) ↔ Module.Free A M) ∧
    (∀ (N : Type*) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.IsReflexive A N],
      Module.rank A N = 1 →
      Nonempty (B ⊗[A] Module.Dual A (Module.Dual A (M ⊗[A] N)) ≃ₗ[B]
        Module.Dual B (Module.Dual B ((B ⊗[A] M) ⊗[B] (B ⊗[A] N))))) ∧
    (∀ (N : Type*) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.IsReflexive A N],
      Module.rank A N = 1 →
      (Nonempty ((B ⊗[A] M) ≃ₗ[B] (B ⊗[A] N)) ↔ Nonempty (M ≃ₗ[A] N))) ∧
    (∀ (I : Submodule A K) [Module.Finite A I] [Module.IsReflexive A I],
      Function.Injective (LinearMap.liftBaseChange B
          (((Algebra.linearMap K L).restrictScalars A).comp I.subtype)) ∧
        Module.IsReflexive B (LinearMap.range (LinearMap.liftBaseChange B
          (((Algebra.linearMap K L).restrictScalars A).comp I.subtype)))) := by
  refine ⟨⟨isReflexive_baseChange A B M, rank_baseChange_eq K L M hM⟩,
    ⟨fun _ => free_of_free_baseChange (B := B) M, fun _ => inferInstance⟩, ?_, ?_, ?_⟩
  · intro N _ _ _ _ _
    have := Module.finitePresentation_of_finite A (M ⊗[A] N)
    have := Module.finitePresentation_of_finite A (Module.Dual A (M ⊗[A] N))
    exact ⟨dualBaseChange A B (Module.Dual A (M ⊗[A] N)) ≪≫ₗ
      (dualBaseChange A B (M ⊗[A] N)).symm.dualMap ≪≫ₗ
      (AlgebraTensorModule.distribBaseChange A B M N).dualMap.dualMap⟩
  · intro N _ _ _ _ _
    exact ⟨fun ⟨e⟩ => nonempty_linearEquiv_of_baseChange (rank_baseChange_eq K L M hM) e,
      fun ⟨e⟩ => ⟨e.baseChange A B M N⟩⟩
  · intro I _ _
    have hinj := injective_liftBaseChange K L I (B := B)
    refine ⟨hinj, ?_⟩
    have := isReflexive_baseChange A B I
    exact Module.equiv (LinearEquiv.ofInjective _ hinj)

end

end MMP

end

/-!
## Blowing up a smooth centre adapted to an snc divisor

Let `Y` be a smooth variety of dimension `n` over a field `k`, `B₁, …, B_s` distinct smooth prime
divisors with `B₁ + ⋯ + B_s` snc, and `Z = V(I) ⊆ Y` a smooth irreducible closed subscheme of
codimension `c ≥ 2`, `s ≤ c`, adapted to the `Bᵢ`: at every closed point `z ∈ Z` there is a regular
system of parameters `x₁, …, xₙ` of `𝒪_{Y,z}` with `Bᵢ = (xᵢ = 0)` for `i ≤ s` and
`Z = (x₁ = ⋯ = x_c = 0)` near `z`. Let `π : Y' = Bl_Z Y ⟶ Y` be the blow-up and `F = π⁻¹(Z)`.
Then `Y'` is smooth, `F` is a prime divisor, `π^*Bᵢ = π⁻¹_*Bᵢ + F`, and
`π⁻¹_*B₁ + ⋯ + π⁻¹_*B_s + F` is an snc divisor.

### Main results

* `MMP.Flips.ResolutionInputs`
  `.smooth_blowUp_and_isSNCDivisor_birationalInverseTransform_add_exceptional`:
  the statement above.

### Implementation notes

* The centre is given by its ideal sheaf `I`, with `MMP.Resolution.IsSmoothBlowup` (`Y` and `V(I)`
  smooth over `k`); `Y'` is `AlgebraicGeometry.blowUp I`, `π` is `blowUpToBase I`, and `F` is the
  prime divisor whose ideal sheaf is `exceptionalIdeal I = I 𝒪_{Y'}`.
* The coordinate hypothesis is imposed at closed points of `Z`, where `𝒪_{Y,z}` has dimension
  `n`; the condition near a point is the equality of ideals in the stalk `𝒪_{Y,z}`.
* `π^*Bᵢ` is the pull-back of the Cartier divisor `Bᵢ` (`MMP.Mori.Divisor.IsPullback`), and
  `π⁻¹_*` is `MMP.Flips.birationalInverseTransform`.

### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.1
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MMP MMP.Flips MMP.Flips.ResolutionInputs MMP.Mori MMP.Resolution

namespace MMP.Proofs.lem_mmp_foundation_snc_adapted_centre_blowup

/-- The generic point of a prime divisor does not lie on a centre of codimension at least two. -/
private theorem genericPoint_notMem_support {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (P : Mori.PrimeDivisor Y) : P.genericPoint ∉ (I.support : Set Y) := by
  intro hP
  have hle : (IrreducibleCloseds.closureSingleton P.genericPoint) ≤
      (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    change closure {P.genericPoint} ⊆ (I.support : Set Y)
    exact I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)
  have h1 := Order.coheight_anti hle
  have h2 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 :=
    P.codimension_closureSingleton_genericPoint
  change codimension _ ≤ codimension _ at h1
  rw [h2] at h1
  have := hc.trans h1
  norm_num at this

/-- A prime divisor is not contained in a centre of codimension at least two. -/
private theorem not_support_subset {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (P : Mori.PrimeDivisor Y) : ¬ (P.idealSheaf.support : Set Y) ⊆ I.support :=
  fun h => genericPoint_notMem_support I hirr hc P
    (h (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P))

/-- The closed points of the centre lie on a prime divisor whose ideal at each of them is proper,
so the whole centre does (the closed points of a scheme of finite type over a field being dense
in every closed set). -/
private theorem support_subset_of_forall_isClosed {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (I : Y.IdealSheafData)
    (B : Mori.PrimeDivisor Y)
    (hB : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      IdealSheafData.stalk B.idealSheaf z ≠ ⊤) :
    (I.support : Set Y) ⊆ B.support := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  by_contra hne
  have hlc : IsLocallyClosed ((I.support : Set Y) \ B.support) := by
    rw [Set.sdiff_eq]
    exact I.support.isClosed.isLocallyClosed.inter
      B.idealSheaf.support.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints (Set.sdiff_nonempty.2 hne) hlc
  exact hB x hx.1 hxc ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ x).mpr hx.2)

open Classical in
/-- The coefficient of `P` in `∑ⱼ Gⱼ` for an injective family `G` of prime divisors. -/
private theorem sum_single_apply {X : Scheme.{u}} {ι : Type*} [Fintype ι]
    {G : ι → Mori.PrimeDivisor X} (hG : Function.Injective G) (P : Mori.PrimeDivisor X) :
    (∑ j, Finsupp.single (G j) (1 : ℤ)) P = if P ∈ Set.range G then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  split_ifs with hP
  · obtain ⟨i, rfl⟩ := hP
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Finsupp.single_apply, ite_eq_right_iff]
      exact fun h => absurd (hG h) hji
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, ite_eq_right_iff]
    exact fun h => absurd ⟨j, h⟩ hP

/-- The adapted coordinates at the closed points of the centre make every `Bᵢ` contain it. -/
private theorem support_subset_of_forall_isClosed_of_coordinates {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {n : ℕ}
    (I : Y.IdealSheafData) {c s : ℕ} {B : Fin s → Mori.PrimeDivisor Y}
    (hcoord : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      ∃ x : Fin n → Y.presheaf.stalk z, IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c})) (i : Fin s) :
    (I.support : Set Y) ⊆ (B i).support := by
  refine support_subset_of_forall_isClosed sY I (B i) fun z hz hzc => ?_
  obtain ⟨x, hx, hxB, -⟩ := hcoord z hz hzc
  obtain ⟨j, -, hj⟩ := hxB i
  rw [hj, Ne, Ideal.span_singleton_eq_top]
  intro hu
  have hm : x j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z) := by
    rw [← hx.1]; exact Ideal.subset_span ⟨j, rfl⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp hm hu

/-! ### Birational transforms along the blow-up -/

/-- The blow-up of a centre of codimension at least two in a variety is a variety, and the
blow-up morphism is proper. -/
private theorem isVariety_blowUp_and_isProper {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY) (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y)) :
    Mori.IsVariety k (blowUpToBase I ≫ sY) ∧ IsProper (blowUpToBase I) := by
  have : AlgebraicGeometry.IsVariety k sY := hY
  have hI : I ≠ ⊥ := by
    rintro rfl
    have h0 : codimension (⟨(⊥ : Y.IdealSheafData).support, hirr,
        (⊥ : Y.IdealSheafData).support.isClosed⟩ : IrreducibleCloseds Y) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ => fun x _ => by
        change x ∈ ((⊥ : Y.IdealSheafData).support : Set Y)
        rw [Scheme.IdealSheafData.support_bot]; trivial
    rw [h0] at hc
    norm_num at hc
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact ⟨(MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sY I
    hI).1, TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)⟩

/-- Every prime divisor `P` of `Y` has a strict transform `P'` on the blow-up of a centre of
codimension at least two, with `π(η_{P'}) = η_P`. -/
private theorem exists_inverseTransformPrimeDivisor_eq_some {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (P : Mori.PrimeDivisor Y) :
    ∃ P' : Mori.PrimeDivisor (blowUp I),
      inverseTransformPrimeDivisor (blowUpToBase I) P = some P' ∧
        blowUpToBase I P'.genericPoint = P.genericPoint := by
  have hη := genericPoint_notMem_support I hirr hc P
  obtain ⟨ξ, hξ⟩ := exists_blowUpToBase_eq_of_notMem_support I hη
  have hV : blowUpToBase I ξ ∈ biregularLocus (blowUpToBase I) :=
    le_biregularLocus (isIso_blowUp_restrict_compl_support I) (by rwa [hξ])
  have hcoh : Order.coheight ξ = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus _ hV, hξ, P.coheight_genericPoint]
  have hg : Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh) =
      ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh, ?_, ?_⟩
  · refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint ?_ ?_
    · rw [hg, hξ]
    · rwa [hg]
  · rw [hg, hξ]

/-- A point of the blow-up lies on a prime divisor `F` with ideal the exceptional ideal exactly
when its image lies on the centre. -/
private theorem mem_support_iff_of_idealSheaf_eq_exceptionalIdeal {Y : Scheme.{u}}
    {I : Y.IdealSheafData} {F : Mori.PrimeDivisor (blowUp I)}
    (hF : F.idealSheaf = exceptionalIdeal I) (q : blowUp I) :
    q ∈ F.support ↔ blowUpToBase I q ∈ (I.support : Set Y) := by
  change q ∈ (F.idealSheaf.support : Set _) ↔ _
  rw [hF, exceptionalIdeal, Scheme.IdealSheafData.support_comap]
  rfl

/-- A prime divisor of the blow-up whose generic point maps to that of a prime divisor of `Y` is
not the exceptional divisor, the centre having codimension at least two. -/
private theorem ne_of_map_genericPoint_eq {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    {F : Mori.PrimeDivisor (blowUp I)} (hF : F.idealSheaf = exceptionalIdeal I)
    {P : Mori.PrimeDivisor Y} {P' : Mori.PrimeDivisor (blowUp I)}
    (hP' : blowUpToBase I P'.genericPoint = P.genericPoint) : P' ≠ F := by
  rintro rfl
  have := (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hF _).mp
    (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P')
  rw [hP'] at this
  exact genericPoint_notMem_support I hirr hc P this

/-! ### The order of a smooth divisor along the centre -/

/-- The ideal of a prime divisor with invertible ideal sheaf is generated, in each local ring, by
a nonzerodivisor. -/
private theorem exists_stalk_eq_span_nonZeroDivisor {X : Scheme.{u}} (P : Mori.PrimeDivisor X)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf) (x : X) :
    ∃ g ∈ nonZeroDivisors (X.presheaf.stalk x),
      IdealSheafData.stalk P.idealSheaf x = Ideal.span {g} := by
  obtain ⟨W, hW, hxW, s, hs, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hP x
  refine ⟨_, Stacks.Divisors.germ_mem_nonZeroDivisors hW hs x hxW, ?_⟩
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf x ⟨W, hW⟩ hxW, hspan,
    Ideal.map_span, Set.image_singleton]

/-- **A smooth prime divisor containing `Z` has order one along `Z`.** At the generic point of
`Z`, the quotient of the regular local ring `𝒪_{Y,Z}` by the ideal `(g)` of `B` is the regular
local ring of `B`, of dimension `< dim 𝒪_{Y,Z}`, so its cotangent space is smaller. -/
private theorem idealOrder_stalk_genericPoint_eq_one {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] (hYs : IsSmoothScheme sY)
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y))
    (B : Mori.PrimeDivisor Y) (hBsm : IsSmoothScheme (B.idealSheaf.subschemeι ≫ sY))
    (hZB : (I.support : Set Y) ⊆ B.support) :
    idealOrder (IdealSheafData.stalk B.idealSheaf hirr.genericPoint) = 1 := by
  have hmem : hirr.genericPoint ∈ (B.idealSheaf.support : Set Y) :=
    ((hirr.isGenericPoint_genericPoint I.support.isClosed).mem_closed_set_iff
      B.idealSheaf.support.isClosed).mpr hZB
  rw [← B.idealSheaf.range_subschemeι] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [← hw]
  have : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme hYs
  have : Smooth (B.idealSheaf.subschemeι ≫ sY) :=
    Threefold.Resolution.smooth_of_isSmoothScheme hBsm
  have : IsRegularLocalRing (Y.presheaf.stalk (B.idealSheaf.subschemeι w)) :=
    isRegularLocalRing_stalk_of_smooth_over_field sY _
  have hS : IsRegularLocalRing (B.idealSheaf.subscheme.presheaf.stalk w) :=
    isRegularLocalRing_stalk_of_smooth_over_field (B.idealSheaf.subschemeι ≫ sY) w
  refine MMP.Resolution.Kollar.multAt_eq_one_of_finrank_cotangentSpace_lt B.idealSheaf w ?_
  obtain ⟨g, hg, hspan⟩ := exists_stalk_eq_span_nonZeroDivisor B
    (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs B)
    (B.idealSheaf.subschemeι w)
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hg
  rw [← hspan] at h1
  have : IsNoetherianRing (B.idealSheaf.subscheme.presheaf.stalk w) :=
    IsRegularLocalRing.toIsNoetherian
  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace _).mp hS
  have he := ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv B.idealSheaf w)
  calc _ < ((Module.finrank (IsLocalRing.ResidueField (B.idealSheaf.subscheme.presheaf.stalk w))
          (IsLocalRing.CotangentSpace (B.idealSheaf.subscheme.presheaf.stalk w)) : ℕ) :
          WithBot ℕ∞) + 1 := by
        exact_mod_cast Nat.lt_succ_self _
    _ ≤ _ := by rwa [hfin, ← he]

/-! ### The pull-back of a smooth divisor containing the centre -/

/-- **`π^*B = π⁻¹_*B + F`** for a smooth prime divisor `B` containing the centre `Z`: along `F`
the order of `π^*B` is the order of `B` along `Z`, which is one, and off `F` the blow-up is an
isomorphism. -/
private theorem isPullback_single_eq_add {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY) (I : Y.IdealSheafData)
    (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian (blowUp I)] [IsNormal (blowUp I)]
    (F : Mori.PrimeDivisor (blowUp I)) (hF : F.idealSheaf = exceptionalIdeal I)
    (B : Mori.PrimeDivisor Y) (hBsm : IsSmoothScheme (B.idealSheaf.subschemeι ≫ sY))
    (hZB : (I.support : Set Y) ⊆ B.support) {B' : Mori.PrimeDivisor (blowUp I)}
    (hB' : inverseTransformPrimeDivisor (blowUpToBase I) B = some B')
    (hBi : ∀ Z : irreducibleComponents (blowUp I),
      blowUpToBase I (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single B 1 : Divisor Y)) :
    Divisor.IsPullback (blowUpToBase I) (Finsupp.single B 1 : Divisor Y) hBi
      (Finsupp.single B' 1 + Finsupp.single F 1) := by
  classical
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have hYs := h.1
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    le_trans (by norm_num) hc
  obtain ⟨hvar, -⟩ := isVariety_blowUp_and_isProper sY hY I hirr hc
  have : CompactSpace (blowUp I) := by
    have : QuasiCompact (blowUpToBase I ≫ sY) := hvar.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I ≫ sY)
  have hCc : Divisor.IsCartier (Finsupp.single B 1 : Divisor Y) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hYs B
  have hCe := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs B
  obtain ⟨B'', hB''⟩ := hCc.exists_isPullback hBi
  suffices hBeq : B'' = Finsupp.single B' 1 + Finsupp.single F 1 from hBeq ▸ hB''
  have hπB' := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hB').1
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hF
  have hB'F : B' ≠ F := ne_of_map_genericPoint_eq I hirr hc hF hπB'
  ext E
  obtain ⟨n, hn, hcoef⟩ :=
    MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder B hCe hB'' E
  rw [hcoef, DivisorWithCoeffs.coeff_add]
  by_cases hEF : E = F
  · subst hEF
    rw [DivisorWithCoeffs.coeff_single_of_ne hB'F, DivisorWithCoeffs.coeff_single_self, zero_add]
    have hord := orderAlong_comap_blowUpToBase_eq sY I h hirr hc1 B.idealSheaf
    have hE : exceptionalPrimeDivisor sY I h hirr hc1 = E :=
      Mori.PrimeDivisor.ext_idealSheaf (by rw [hF]; rfl)
    simp only [orderAlong, multAt] at hord
    rw [MMP.Threefold.Resolution.isIrreducible_genericPoint_eq _
      (isIrreducible_support_exceptionalPrimeDivisor sY I h hirr hc1), hE, hn,
      idealOrder_stalk_genericPoint_eq_one sY hYs I hirr B hBsm hZB] at hord
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) (hord.trans Nat.cast_one.symm) : n = 1)
  · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEF), add_zero]
    have hηF : E.genericPoint ∉ F.support := fun h' =>
      hEF (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support h').symm
    have hx : blowUpToBase I E.genericPoint ∉ (I.support : Set Y) := fun h' =>
      hηF ((hFmem _).mpr h')
    have hxV : blowUpToBase I E.genericPoint ∈ biregularLocus (blowUpToBase I) :=
      le_biregularLocus (isIso_blowUp_restrict_compl_support I) hx
    have hiso := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus _ hxV
    rw [AlgebraicGeometry.IdealSheafData.stalk_comap] at hn
    have hn' : idealOrder (IdealSheafData.stalk B.idealSheaf
        (blowUpToBase I E.genericPoint)) = n := by
      rw [← hn]
      exact (MMP.Threefold.Resolution.idealOrder_map_ringEquiv
        (asIso (Scheme.Hom.stalkMap _ E.genericPoint)).commRingCatIsoToRingEquiv _).symm
    by_cases hxC : blowUpToBase I E.genericPoint = B.genericPoint
    · have hEB : B' = E := Option.some.inj (hB'.symm.trans
        (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hxC
          hxV))
      subst hEB
      rw [DivisorWithCoeffs.coeff_single_self]
      have key : ∀ z (hz : z = B.genericPoint),
          idealOrder (IdealSheafData.stalk B.idealSheaf z) = 1 := by
        rintro z rfl
        have := B.isDiscreteValuationRing_localRing
        rw [MMP.Threefold.Resolution.stalk_idealSheaf_genericPoint_eq_maximalIdeal B hCe,
          MMP.Threefold.Resolution.idealOrder_maximalIdeal]
      rw [key _ hxC] at hn'
      exact_mod_cast (Nat.cast_injective (R := ℕ∞) (hn'.symm.trans Nat.cast_one.symm) : n = 1)
    · have hB'E : B' ≠ E := by
        rintro rfl
        exact hxC hπB'
      rw [DivisorWithCoeffs.coeff_single_of_ne hB'E]
      have hxnC : blowUpToBase I E.genericPoint ∉ B.idealSheaf.support := by
        intro hm
        refine hxC (B.eq_genericPoint_of_mem_support hm ?_)
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus _ hxV]
        exact E.coheight_genericPoint
      rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hxnC,
        MMP.Threefold.Resolution.idealOrder_top] at hn'
      exact_mod_cast (Nat.cast_injective (R := ℕ∞) (hn'.symm.trans Nat.cast_zero.symm) : n = 0)

/-! ### Strict transforms and coordinates on the blow-up -/

/-- A closed subscheme smooth over a field is reduced. -/
private theorem isReduced_subscheme_of_isSmoothScheme {X : Scheme.{u}} {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k))
    (T : X.IdealSheafData) (hT : IsSmoothScheme (T.subschemeι ≫ s)) : IsReduced T.subscheme := by
  have : Smooth (T.subschemeι ≫ s) := Threefold.Resolution.smooth_of_isSmoothScheme hT
  have hreg := isRegular_of_smooth_over_field (T.subschemeι ≫ s)
  have : ∀ x : T.subscheme, _root_.IsReduced (T.subscheme.presheaf.stalk x) := fun x => by
    have := hreg.isRegularLocalRing_stalk x
    have := IsRegularLocalRing.isDomain (T.subscheme.presheaf.stalk x)
    exact isReduced_of_noZeroDivisors
  exact isReduced_of_isReduced_stalk _

/-- An ideal sheaf whose closed subscheme is smooth over a field contains the ideal sheaf of every
closed subscheme whose support contains its support. -/
private theorem le_of_support_subset {X : Scheme.{u}} {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k))
    (T : X.IdealSheafData) (hT : IsSmoothScheme (T.subschemeι ≫ s)) (E : X.IdealSheafData)
    (h : (T.support : Set X) ⊆ E.support) : E ≤ T := by
  have := isReduced_subscheme_of_isSmoothScheme s T hT
  rw [← MMP.Mori.vanishingIdeal_support_eq_self T]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

/-- If `E ≤ Z`, the centre `Z` restricted to the closed subscheme `E` is smooth when `Z` is. -/
private theorem isSmoothScheme_comap_subschemeι {X : Scheme.{u}} {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k))
    (Z E : X.IdealSheafData) (hZ : IsSmoothScheme (Z.subschemeι ≫ s)) (hEZ : E ≤ Z) :
    IsSmoothScheme ((Z.comap E.subschemeι).subschemeι ≫ E.subschemeι ≫ s) := by
  have hiso : IsIso (Limits.pullback.snd E.subschemeι Z.subschemeι) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hEZ]; infer_instance
  have e : (Z.comap E.subschemeι).subschemeι ≫ E.subschemeι ≫ s =
      ((Z.comapIso E.subschemeι).hom ≫ Limits.pullback.snd _ _) ≫ Z.subschemeι ≫ s := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      Limits.pullback.condition_assoc]
  rw [e]
  have : Smooth (Z.subschemeι ≫ s) := Threefold.Resolution.smooth_of_isSmoothScheme hZ
  exact MMP.Resolution.isSmoothScheme_of_smooth _

/-- **The strict transform of a smooth integral subscheme along a smooth centre is smooth**, over
any field. Let `Z ⊆ X` be a closed subscheme smooth over `k` and `E ⊆ X` an integral closed
subscheme smooth over `k` with `E ≤ Z` (so `Z ⊆ E`) and `E ⊄ Z`. Then the closure of
`π⁻¹(E ∖ Z)` in the blow-up `π : B_Z X → X`, with its reduced structure, is smooth over `k`: it is
the blow-up of `E` along `Z`. -/
private theorem isSmoothScheme_strictTransform {X : Scheme.{u}} {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k))
    (Z E : X.IdealSheafData) (hZ : IsSmoothScheme (Z.subschemeι ≫ s)) [IsIntegral E.subscheme]
    (hE : IsSmoothScheme (E.subschemeι ≫ s)) (hEZ : E ≤ Z)
    (hnot : ¬ (E.support : Set X) ⊆ Z.support) :
    IsSmoothScheme ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase Z ⁻¹' ((E.support : Set X) \ Z.support)))).subschemeι ≫
        blowUpToBase Z ≫ s) := by
  obtain ⟨-, hker⟩ :=
    MMP.Resolution.Bridges.range_canonicalLift_eq_closure_and_ker_eq_vanishingIdeal
      E.subschemeι Z (by rwa [E.range_subschemeι])
  rw [E.range_subschemeι] at hker
  rw [← hker]
  set f := MMP.Resolution.canonicalLift E.subschemeι Z
  have : IsClosedImmersion f := MMP.Resolution.Bridges.isClosedImmersion_canonicalLift _ Z
  have hb : IsSmoothBlowup (E.subschemeι ≫ s) (Z.comap E.subschemeι) :=
    ⟨hE, isSmoothScheme_comap_subschemeι s Z E hZ hEZ⟩
  have hsm := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
    _ _ hb).1
  have e : f.ker.subschemeι ≫ blowUpToBase Z ≫ s =
      inv f.toImage ≫ blowUpToBase (Z.comap E.subschemeι) ≫ E.subschemeι ≫ s := by
    rw [IsIso.eq_inv_comp, ← Category.assoc (blowUpToBase _) E.subschemeι s,
      ← MMP.Resolution.canonicalLift_comp_blowUpToBase, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun g => (g ≫ blowUpToBase Z) ≫ s) (Scheme.Hom.toImage_imageι f)
  rw [e]
  exact MMP.Resolution.isSmoothScheme_of_smooth _

/-- The transform of an irreducible closed set `A ⊄ Z` under the inverse of the blow-up of `Z` is
the closure of the preimage of `A ∖ Z`. -/
private theorem coe_inverseTransform_blowUpToBase {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A : Closeds X) (hA : IsIrreducible (A : Set X)) (hnot : ¬ (A : Set X) ⊆ Z.support) :
    (MMP.Mori.inverseTransform (blowUpToBase Z) A : Set (blowUp Z)) =
      closure (blowUpToBase Z ⁻¹' ((A : Set X) \ Z.support)) := by
  have hZB : ∀ x, x ∉ (Z.support : Set X) → x ∈ MMP.Mori.biregularLocus (blowUpToBase Z) :=
    fun x hx => MMP.Mori.le_biregularLocus (isIso_blowUp_restrict_compl_support Z) hx
  rw [MMP.Mori.inverseTransform, Closeds.coe_closure]
  apply subset_antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro w ⟨hwA, hwB⟩
    have hg := hA.isGenericPoint_genericPoint_closure
    rw [A.isClosed.closure_eq] at hg
    have hηw : hA.genericPoint ⤳ blowUpToBase Z w := hg.specializes hwA
    have hηZ : hA.genericPoint ∉ (Z.support : Set X) := fun h =>
      hnot ((hg.mem_closed_set_iff Z.support.isClosed).mp h)
    have hηB : hA.genericPoint ∈ MMP.Mori.biregularLocus (blowUpToBase Z) :=
      hηw.mem_open (MMP.Mori.biregularLocus (blowUpToBase Z)).isOpen hwB
    obtain ⟨ξ, hξ⟩ := exists_blowUpToBase_eq_of_notMem_support Z hηZ
    have hξw : ξ ⤳ w := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus
      (blowUpToBase Z) (by rwa [hξ]) hwB (by rwa [hξ])
    have hξT : ξ ∈ blowUpToBase Z ⁻¹' ((A : Set X) \ Z.support) := by
      change blowUpToBase Z ξ ∈ (A : Set X) \ Z.support
      rw [hξ]
      exact ⟨hg.mem, hηZ⟩
    exact closure_mono (Set.singleton_subset_iff.mpr hξT)
      (specializes_iff_mem_closure.mp hξw)
  · exact closure_mono fun w hw => ⟨hw.1, hZB _ hw.2⟩

private theorem fromSpecStalk_preimage_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (S : Set Y) : X.fromSpecStalk x ⁻¹' (f ⁻¹' S) =
      PrimeSpectrum.comap (f.stalkMap x).hom ⁻¹' (Y.fromSpecStalk (f x) ⁻¹' S) := by
  have h := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  refine Set.ext fun p => ?_
  change f (X.fromSpecStalk x p) ∈ S ↔
    Y.fromSpecStalk (f x) (PrimeSpectrum.comap (f.stalkMap x).hom p) ∈ S
  rw [← Scheme.Hom.comp_apply, ← h]
  rfl

private theorem map_fromSpecStalk_mem_support_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (I : Y.IdealSheafData) {g : Y.presheaf.stalk (f x)}
    (hg : IdealSheafData.stalk I (f x) = Ideal.span {g}) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    f (X.fromSpecStalk x p) ∈ I.support ↔ (f.stalkMap x).hom g ∈ p.asIdeal := by
  have := Set.ext_iff.1 (fromSpecStalk_preimage_preimage f x I.support) p
  change f (X.fromSpecStalk x p) ∈ (I.support : Set Y) ↔ _
  refine this.trans ?_
  change Y.fromSpecStalk (f x) (PrimeSpectrum.comap (f.stalkMap x).hom p) ∈ (I.support : Set Y) ↔ _
  rw [fromSpecStalk_mem_support_iff_stalk_le, hg, Ideal.span_singleton_le_iff_mem]
  rfl

private theorem blowUpToBase_mem_support_of_mem_closure {Y : Scheme.{u}} (Z I : Y.IdealSheafData)
    {y : blowUp Z}
    (h : y ∈ closure (blowUpToBase Z ⁻¹' ((I.support : Set Y) \ (Z.support : Set Y)))) :
    blowUpToBase Z y ∈ I.support := by
  have hs : blowUpToBase Z ⁻¹' ((I.support : Set Y) \ (Z.support : Set Y)) ⊆
      blowUpToBase Z ⁻¹' (I.support : Set Y) := fun _ hz => hz.1
  exact closure_minimal hs (I.support.isClosed.preimage (blowUpToBase Z).continuous) h

private theorem blowUpToBase_fromSpecStalk_mem_support_iff {Y : Scheme.{u}}
    (Z : Y.IdealSheafData) (x' : blowUp Z) {n N : ℕ}
    {z : Fin n → Y.presheaf.stalk (blowUpToBase Z x')} {w : Fin N → (blowUp Z).presheaf.stalk x'}
    {m : Fin n} {i₀ : Fin N} {σ : Fin n → Fin N} {J U : Finset (Fin n)}
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hmJ : m ∈ J) (hwi₀ : w i₀ = ((blowUpToBase Z).stalkMap x').hom (z m))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → ((blowUpToBase Z).stalkMap x').hom (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ ((blowUpToBase Z).stalkMap x').hom (z j) = u * w i₀)
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    blowUpToBase Z ((blowUp Z).fromSpecStalk x' p) ∈ Z.support ↔ w i₀ ∈ p.asIdeal := by
  refine (Set.ext_iff.1 (fromSpecStalk_preimage_preimage (blowUpToBase Z) x' Z.support) p).trans
    ((Set.ext_iff.1 (preimage_fromSpecStalk_support Z (blowUpToBase Z x'))
      (PrimeSpectrum.comap ((blowUpToBase Z).stalkMap x').hom p)).trans ?_)
  rw [hJ]
  refine (PrimeSpectrum.mem_zeroLocus _ _).trans ?_
  rw [SetLike.coe_subset_coe, Ideal.span_le]
  constructor
  · intro h
    rw [hwi₀]
    exact h ⟨m, hmJ, rfl⟩
  · rintro h _ ⟨j, hj, rfl⟩
    change ((blowUpToBase Z).stalkMap x').hom (z j) ∈ p.asIdeal
    by_cases hjm : j = m
    · rwa [hjm, ← hwi₀]
    by_cases hjU : j ∈ U
    · obtain ⟨u, -, hu⟩ := hunit j hjU
      rw [hu]
      exact Ideal.mul_mem_left _ _ h
    · rw [hin j hj hjm hjU]
      exact Ideal.mul_mem_left _ _ h

private theorem fromSpecStalk_span_mem_preimage_sdiff {Y : Scheme.{u}} {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    [IsLocallyNoetherian (blowUp Z)] {n N : ℕ}
    {z : Fin n → Y.presheaf.stalk (blowUpToBase Z x')} {w : Fin N → (blowUp Z).presheaf.stalk x'}
    {m : Fin n} {i₀ : Fin N} {σ : Fin n → Fin N} {J U : Finset (Fin n)}
    (hw : IsRegularSystemOfParameters w)
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hmJ : m ∈ J) (hwi₀ : w i₀ = ((blowUpToBase Z).stalkMap x').hom (z m))
    (hout : ∀ j ∉ J, w (σ j) = ((blowUpToBase Z).stalkMap x').hom (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → ((blowUpToBase Z).stalkMap x').hom (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ ((blowUpToBase Z).stalkMap x').hom (z j) = u * w i₀)
    (hσ₀ : ∀ j, j ≠ m → j ∉ U → σ j ≠ i₀) {l : Λ} {j : Fin n}
    (hj : IdealSheafData.stalk (D l) (blowUpToBase Z x') = Ideal.span {z j})
    (hjm : j ≠ m) (hjU : j ∉ U) :
    (blowUp Z).fromSpecStalk x' ⟨Ideal.span {w (σ j)},
      span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩ ∈
      blowUpToBase Z ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y)) := by
  refine ⟨(map_fromSpecStalk_mem_support_iff (blowUpToBase Z) x' (D l) hj _).2 ?_, fun hZ' =>
    notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw (hσ₀ _ hjm hjU)
      ((blowUpToBase_fromSpecStalk_mem_support_iff Z x' hJ hmJ hwi₀ hin hunit _).1 hZ')⟩
  have h : w (σ j) ∈ Ideal.span {w (σ j)} := Ideal.subset_span rfl
  by_cases hjJ : j ∈ J
  · rw [hin j hjJ hjm hjU]
    exact Ideal.mul_mem_right _ _ h
  · rw [← hout j hjJ]
    exact h

private theorem fromSpecStalk_mem_closure_preimage_sdiff_iff {Y : Scheme.{u}} {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    [IsLocallyNoetherian (blowUp Z)] [TopologicalSpace.NoetherianSpace (blowUp Z)] {n N : ℕ}
    {z : Fin n → Y.presheaf.stalk (blowUpToBase Z x')} {w : Fin N → (blowUp Z).presheaf.stalk x'}
    {m : Fin n} {i₀ : Fin N} {σ : Fin n → Fin N} {J U : Finset (Fin n)}
    (hw : IsRegularSystemOfParameters w)
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hmJ : m ∈ J) (hwi₀ : w i₀ = ((blowUpToBase Z).stalkMap x').hom (z m))
    (hout : ∀ j ∉ J, w (σ j) = ((blowUpToBase Z).stalkMap x').hom (z j))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → ((blowUpToBase Z).stalkMap x').hom (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ ((blowUpToBase Z).stalkMap x').hom (z j) = u * w i₀)
    (hσ₀ : ∀ j, j ≠ m → j ∉ U → σ j ≠ i₀) {l : Λ} {j : Fin n}
    (hj : IdealSheafData.stalk (D l) (blowUpToBase Z x') = Ideal.span {z j})
    (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')) :
    (blowUp Z).fromSpecStalk x' p ∈
        closure (blowUpToBase Z ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y))) ↔
      (j ≠ m ∧ j ∉ U) ∧ w (σ j) ∈ p.asIdeal := by
  have hE := blowUpToBase_fromSpecStalk_mem_support_iff Z x' hJ hmJ hwi₀ hin hunit
  constructor
  · intro hp
    have hp' : (blowUp Z).fromSpecStalk x' p ∈ closure (blowUpToBase Z ⁻¹'
        ((D l).support : Set Y) ∩ (blowUpToBase Z ⁻¹' (Z.support : Set Y))ᶜ) := by
      rwa [← Set.preimage_compl, ← Set.preimage_inter, ← Set.sdiff_eq]
    obtain ⟨s, hs, hsp⟩ := exists_mem_specializes_of_mem_closure
      ((D l).support.isClosed.preimage (blowUpToBase Z).continuous)
      ((Z.support.isClosed.preimage (blowUpToBase Z).continuous).isOpen_compl) hp'
    have hgen : (blowUp Z).fromSpecStalk x' p ⤳ x' := Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ : s ∈ Set.range ((blowUp Z).fromSpecStalk x') := by
      rw [Scheme.range_fromSpecStalk]
      exact hsp.trans hgen
    have hqp : q.asIdeal ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes q p).2
      ((((blowUp Z).fromSpecStalk x').isEmbedding.isInducing.specializes_iff).1 hsp)
    have h1 : ((blowUpToBase Z).stalkMap x').hom (z j) ∈ q.asIdeal :=
      (map_fromSpecStalk_mem_support_iff (blowUpToBase Z) x' (D l) hj q).1 hs.1
    have h0 : w i₀ ∉ q.asIdeal := fun h => hs.2 ((hE q).2 h)
    have hgood : j ≠ m ∧ j ∉ U := by
      refine ⟨fun hjm => h0 ?_, fun hjU => h0 ?_⟩
      · rwa [hwi₀, ← hjm]
      · obtain ⟨u, hu, hu'⟩ := hunit j hjU
        rw [hu'] at h1
        exact (q.isPrime.mem_or_mem h1).resolve_left fun h' =>
          q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
    refine ⟨hgood, hqp ?_⟩
    by_cases hjJ : j ∈ J
    · rw [hin j hjJ hgood.1 hgood.2] at h1
      exact (q.isPrime.mem_or_mem h1).resolve_right h0
    · rwa [hout j hjJ]
  · rintro ⟨⟨hjm, hjU⟩, hp⟩
    have hle : (⟨Ideal.span {w (σ j)},
        span_singleton_isPrime_of_isRegularSystemOfParameters hw _⟩ :
        PrimeSpectrum _) ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hp
    exact (((PrimeSpectrum.le_iff_specializes _ _).1 hle).map
      ((blowUp Z).fromSpecStalk x').continuous).mem_closed isClosed_closure (subset_closure
        (fromSpecStalk_span_mem_preimage_sdiff D Z x' hw hJ hmJ hwi₀ hout hin hunit hσ₀ hj
          hjm hjU))

private theorem stalk_blowUpTransformFamily_inl_eq_span {Y : Scheme.{u}} {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    [IsLocallyNoetherian (blowUp Z)] (l : Λ) {N : ℕ}
    {w : Fin N → (blowUp Z).presheaf.stalk x'} (hw : IsRegularSystemOfParameters w) (t : Fin N)
    (h : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), (blowUp Z).fromSpecStalk x' p ∈
      closure (blowUpToBase Z ⁻¹' (((D l).support : Set Y) \ (Z.support : Set Y))) ↔
        w t ∈ p.asIdeal) :
    IdealSheafData.stalk (blowUpTransformFamily D Z (Sum.inl l)) x' = Ideal.span {w t} := by
  change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal _) x' = _
  rw [stalk_vanishingIdeal_eq, ← hw.vanishingIdeal_zeroLocus_singleton t]
  congr 1
  ext p
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  exact h p

private theorem stalk_comap_blowUpToBase_eq_span {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (x' : blowUp Z) {n N : ℕ}
    {z : Fin n → Y.presheaf.stalk (blowUpToBase Z x')} {w : Fin N → (blowUp Z).presheaf.stalk x'}
    {m : Fin n} {i₀ : Fin N} {σ : Fin n → Fin N} {J U : Finset (Fin n)}
    (hJ : IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hmJ : m ∈ J) (hwi₀ : w i₀ = ((blowUpToBase Z).stalkMap x').hom (z m))
    (hin : ∀ j ∈ J, j ≠ m → j ∉ U → ((blowUpToBase Z).stalkMap x').hom (z j) = w (σ j) * w i₀)
    (hunit : ∀ j ∈ U, ∃ u, IsUnit u ∧ ((blowUpToBase Z).stalkMap x').hom (z j) = u * w i₀) :
    IdealSheafData.stalk (Z.comap (blowUpToBase Z)) x' = Ideal.span {w i₀} := by
  rw [IdealSheafData.stalk_comap, hJ, Ideal.map_span]
  refine le_antisymm (Ideal.span_le.2 ?_) ?_
  · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    change ((blowUpToBase Z).stalkMap x').hom (z j) ∈ Ideal.span {w i₀}
    by_cases hjm : j = m
    · rw [hjm, ← hwi₀]
      exact Ideal.subset_span rfl
    by_cases hjU : j ∈ U
    · obtain ⟨v, -, hv⟩ := hunit j hjU
      rw [hv]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [hin j hj hjm hjU]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_singleton_le_iff_mem, hwi₀]
    exact Ideal.subset_span ⟨z m, ⟨m, hmJ, rfl⟩, rfl⟩

private theorem eq_of_fromSpecStalk_span_mem {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [CompactSpace Y] {Λ : Type*} (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData)
    (x' : blowUp Z) [IsLocallyNoetherian (blowUp Z)]
    (hsep : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∀ a b,
      y ∈ (D a).support → y ∈ (D b).support → a = b)
    {N : ℕ} {w : Fin N → (blowUp Z).presheaf.stalk x'} (hw : IsRegularSystemOfParameters w)
    (t : Fin N) {a b : Λ}
    (ha : (blowUp Z).fromSpecStalk x' ⟨Ideal.span {w t},
      span_singleton_isPrime_of_isRegularSystemOfParameters hw t⟩ ∈
      blowUpToBase Z ⁻¹' (((D a).support : Set Y) \ (Z.support : Set Y)))
    (hb : blowUpToBase Z ((blowUp Z).fromSpecStalk x' ⟨Ideal.span {w t},
      span_singleton_isPrime_of_isRegularSystemOfParameters hw t⟩) ∈ (D b).support) :
    a = b := by
  set P₀ : PrimeSpectrum ((blowUp Z).presheaf.stalk x') :=
    ⟨Ideal.span {w t}, span_singleton_isPrime_of_isRegularSystemOfParameters hw t⟩
  set g := (blowUp Z).fromSpecStalk x' P₀
  have hiso : IsIso ((blowUpToBase Z).stalkMap g) :=
    isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase Z)
      (isIso_blowUpToBase_restrict_compl_support Z)
      (show g ∈ blowUpToBase Z ⁻¹ᵁ Z.support.compl from ha.2)
  have hdim : ringKrullDim (Y.presheaf.stalk (blowUpToBase Z g)) =
      ringKrullDim ((blowUp Z).presheaf.stalk g) :=
    ringKrullDim_eq_of_ringEquiv (asIso ((blowUpToBase Z).stalkMap g)).commRingCatIsoToRingEquiv
  have hdim2 : ringKrullDim ((blowUp Z).presheaf.stalk g) =
      (P₀.asIdeal.height : WithBot ℕ∞) := ringKrullDim_stalk_fromSpecStalk (blowUp Z) x' P₀
  have hd1 : ringKrullDim (Y.presheaf.stalk (blowUpToBase Z g)) ≤ 1 := by
    rw [hdim, hdim2]
    exact_mod_cast hw.height_span_singleton_le_one t
  exact hsep _ hd1 a b ha.1 hb

private theorem exists_coordinates_blowUpTransformFamily_of_mem_support {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [CompactSpace Y] {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    (hx : blowUpToBase Z x' ∈ Z.support)
    (hZx : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (D i).support} → Fin n) (J : Finset (Fin n)),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (D i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
        Function.Injective c ∧
        IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hsep : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∀ a b,
      y ∈ (D a).support → y ∈ (D b).support → a = b) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  classical
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z)
  have : IsNoetherian (blowUp Z) := {}
  have hTsub' : ∀ l, x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support →
      blowUpToBase Z x' ∈ (D l).support := fun l h =>
    blowUpToBase_mem_support_of_mem_closure Z (D l)
      (by rwa [← coe_support_blowUpTransformFamily_inl D Z l])
  have hclosed : (blowUp Z).fromSpecStalk x' (IsLocalRing.closedPoint _) = x' :=
    Scheme.fromSpecStalk_closedPoint
  obtain ⟨n, z, c, J, hz, hc, -, hJ⟩ := hZx
  obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, -, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    exists_chart_coordinates Z x' hx hz hJ
  have hP₀ := fun l (hl : blowUpToBase Z x' ∈ (D l).support) =>
    fromSpecStalk_span_mem_preimage_sdiff D Z x' hw hJ hmJ hwi₀ hout hin hunit hσ₀
      (l := l) (hc ⟨l, hl⟩)
  have hKS := fun l (hl : blowUpToBase Z x' ∈ (D l).support) =>
    fromSpecStalk_mem_closure_preimage_sdiff_iff D Z x' hw hJ hmJ hwi₀ hout hin hunit hσ₀
      (l := l) (hc ⟨l, hl⟩)
  have hgoodT : ∀ l (h : x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support),
      c ⟨l, hTsub' l h⟩ ≠ m ∧ c ⟨l, hTsub' l h⟩ ∉ U := by
    intro l h
    refine ((hKS l (hTsub' l h) (IsLocalRing.closedPoint _)).1 ?_).1
    rwa [hclosed, ← coe_support_blowUpTransformFamily_inl D Z l]
  let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N := fun i =>
    match i with
    | ⟨Sum.inl l, h⟩ => σ (c ⟨l, hTsub' l h⟩)
    | ⟨Sum.inr _, _⟩ => i₀
  refine ⟨N, w, c', hw, ?_, ?_⟩
  · rintro ⟨(l | u), h⟩
    · refine stalk_blowUpTransformFamily_inl_eq_span D Z x' l hw _ fun p => ?_
      rw [hKS l (hTsub' l h) p]
      exact and_iff_right (hgoodT l h)
    · change IdealSheafData.stalk (Z.comap (blowUpToBase Z)) x' = Ideal.span {w i₀}
      exact stalk_comap_blowUpToBase_eq_span Z x' hJ hmJ hwi₀ hin hunit
  · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
    · change σ (c ⟨a, hTsub' a ha⟩) = σ (c ⟨b, hTsub' b hb⟩) at hab
      have hPb := hP₀ b (hTsub' b hb) (hgoodT b hb).1 (hgoodT b hb).2
      rw [← hab] at hPb
      obtain rfl := eq_of_fromSpecStalk_span_mem D Z x' hsep hw _
        (hP₀ a (hTsub' a ha) (hgoodT a ha).1 (hgoodT a ha).2) hPb.1
      rfl
    · change σ (c ⟨a, hTsub' a ha⟩) = i₀ at hab
      exact absurd hab (hσ₀ _ (hgoodT a ha).1 (hgoodT a ha).2)
    · change i₀ = σ (c ⟨b, hTsub' b hb⟩) at hab
      exact absurd hab.symm (hσ₀ _ (hgoodT b hb).1 (hgoodT b hb).2)
    · rfl

private theorem exists_coordinates_blowUpTransformFamily_of_notMem_support {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [CompactSpace Y] {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    (hx : blowUpToBase Z x' ∉ Z.support)
    (hDx : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (D i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (D i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
        Function.Injective c) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  classical
  have : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z)
  obtain ⟨n, z, c, hz, hc, hinj⟩ := hDx
  have hTsub' : ∀ l, x' ∈ (blowUpTransformFamily D Z (Sum.inl l)).support →
      blowUpToBase Z x' ∈ (D l).support := fun l h =>
    blowUpToBase_mem_support_of_mem_closure Z (D l)
      (by rwa [← coe_support_blowUpTransformFamily_inl D Z l])
  have hgen : ∀ p : PrimeSpectrum ((blowUp Z).presheaf.stalk x'),
      (blowUp Z).fromSpecStalk x' p ⤳ x' :=
    fun p => Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
  have hiso : IsIso ((blowUpToBase Z).stalkMap x') :=
    isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase Z)
      (isIso_blowUpToBase_restrict_compl_support Z)
      (show x' ∈ blowUpToBase Z ⁻¹ᵁ Z.support.compl from hx)
  let e := (asIso ((blowUpToBase Z).stalkMap x')).commRingCatIsoToRingEquiv
  have hw : IsRegularSystemOfParameters fun i => ((blowUpToBase Z).stalkMap x').hom (z i) :=
    isRegularSystemOfParameters_map_ringEquiv e hz
  have hnotE : ∀ u, x' ∉ (blowUpTransformFamily D Z (Sum.inr u)).support := by
    intro u h
    rw [← SetLike.mem_coe, coe_support_blowUpTransformFamily_inr] at h
    exact hx h
  let c' : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin n := fun i =>
    match i with
    | ⟨Sum.inl l, h⟩ => c ⟨l, hTsub' l h⟩
    | ⟨Sum.inr u, h⟩ => absurd h (hnotE u)
  refine ⟨n, fun i => ((blowUpToBase Z).stalkMap x').hom (z i), c', hw, ?_, ?_⟩
  · rintro ⟨(l | u), h⟩
    · have hl := map_fromSpecStalk_mem_support_iff (blowUpToBase Z) x' (D l) (hc ⟨l, hTsub' l h⟩)
      refine stalk_blowUpTransformFamily_inl_eq_span D Z x' l hw _ fun p =>
        ⟨fun hp => (hl p).1 (blowUpToBase_mem_support_of_mem_closure Z (D l) hp), fun hp => ?_⟩
      refine subset_closure ⟨(hl p).2 hp, fun hZ' => ?_⟩
      exact (hgen p).mem_open
        ((Z.support.isClosed.isOpen_compl).preimage (blowUpToBase Z).continuous) hx hZ'
    · exact absurd h (hnotE u)
  · rintro ⟨(a | u), ha⟩ ⟨(b | v), hb⟩ hab
    · obtain rfl : a = b := congrArg Subtype.val (hinj hab)
      rfl
    · exact absurd hb (hnotE v)
    · exact absurd ha (hnotE u)
    · exact absurd ha (hnotE u)

/- The next lemma gives coordinates on the blow-up of a transform family, in a pointwise form: only
the coordinates at the image point are used, and the separation of two members of the family at a
point of dimension at most one replaces the snc condition there. -/
/-- **Local coordinates on the blow-up at a point.** Let `π : B_ZY → Y` be the blow-up of `Z`
and `x' ∈ B_ZY`. If `Z` has simple normal crossings with the family `D` at `π x'` (when
`π x' ∈ Z`), the members of `D` through `π x'` are coordinate hyperplanes (when `π x' ∉ Z`),
and no two members of `D` meet at a point of `Y ∖ Z` of dimension at most one, then at `x'` the
members through `x'` of the transformed family are coordinate hyperplanes. -/
private theorem exists_coordinates_blowUpTransformFamily_of_forall {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [CompactSpace Y] {Λ : Type*}
    (D : Λ → Y.IdealSheafData) (Z : Y.IdealSheafData) (x' : blowUp Z)
    (hZx : blowUpToBase Z x' ∈ Z.support → ∃ (n : ℕ)
      (z : Fin n → Y.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (D i).support} → Fin n) (J : Finset (Fin n)),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (D i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
        Function.Injective c ∧
        IdealSheafData.stalk Z (blowUpToBase Z x') = Ideal.span (z '' (J : Set (Fin n))))
    (hDx : blowUpToBase Z x' ∉ Z.support → ∃ (n : ℕ)
      (z : Fin n → Y.presheaf.stalk (blowUpToBase Z x'))
      (c : {i // blowUpToBase Z x' ∈ (D i).support} → Fin n),
      IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (D i.1) (blowUpToBase Z x') = Ideal.span {z (c i)}) ∧
        Function.Injective c)
    (hsep : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∀ a b,
      y ∈ (D a).support → y ∈ (D b).support → a = b) :
    ∃ (N : ℕ) (w : Fin N → (blowUp Z).presheaf.stalk x')
      (c : {i // x' ∈ (blowUpTransformFamily D Z i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily D Z i.1) x' = Ideal.span {w (c i)}) ∧
        Function.Injective c := by
  by_cases hx : blowUpToBase Z x' ∈ Z.support
  · exact exists_coordinates_blowUpTransformFamily_of_mem_support D Z x' hx (hZx hx) hsep
  · exact exists_coordinates_blowUpTransformFamily_of_notMem_support D Z x' hx (hDx hx)

/-- In the `x_j`-chart of the blow-up (`x_i = x_j u_i` for `i < c`, `i ≠ j`) the pull-back of
`Bᵢ = (xᵢ = 0)` has equation `x_j u_i` when `i ≠ j` and `x_j` when `i = j`; in both cases its
order along `F = (x_j = 0)` is one and its remaining part is the strict transform of `Bᵢ`, so
`π^*Bᵢ = π⁻¹_*Bᵢ + F`. -/
private theorem isPullback_single_eq_birationalInverseTransform_add_exceptional
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    {n : ℕ}
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc2 : 2 ≤ c) {s : ℕ} (B : Fin s → Mori.PrimeDivisor Y)
    (hBsm : ∀ i, IsSmoothScheme ((B i).idealSheaf.subschemeι ≫ sY))
    (hcoord : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      ∃ x : Fin n → Y.presheaf.stalk z, IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c})) :
    haveI : IsIntegral Y := hY.toIsIntegral
    haveI : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    have hc' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
      hc ▸ by exact_mod_cast hc2
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
    let T : Mori.Divisor Y →+ Mori.Divisor (blowUp I) := birationalInverseTransform
      (blowUpToBase I)
      (Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h hirr
        hc').2.2.1
    ∀ F : Mori.PrimeDivisor (blowUp I), F.idealSheaf = exceptionalIdeal I →
      ∀ i, ∃ hBi, Mori.Divisor.IsPullback (blowUpToBase I) (Finsupp.single (B i) 1) hBi
        (T (Finsupp.single (B i) 1) + Finsupp.single F 1) := by
  intro hc' T F hF i
  have : IsIntegral Y := hY.toIsIntegral
  have : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sY
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hZB := support_subset_of_forall_isClosed_of_coordinates sY I hcoord i
  obtain ⟨B', hB', hη⟩ := exists_inverseTransformPrimeDivisor_eq_some I hirr hc' (B i)
  obtain ⟨hvar, hprop⟩ := isVariety_blowUp_and_isProper sY hY I hirr hc'
  have hbir := (Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h
    hirr hc').2.2.1
  have hT : T (Finsupp.single (B i) 1) = Finsupp.single B' 1 :=
    Mori.RationalMap.transformDivisor_single_of_eq_some
      (MMP.Flips.transformPrimeDivisor_inverse_of_map_genericPoint_eq ⟨hY, inferInstance⟩ _ hvar
        hbir hη) 1
  have : IsDominant (blowUpToBase I) := hbir.isDominant
  have : IrreducibleSpace (blowUp I) := by have := hvar.toIsIntegral; infer_instance
  refine ⟨MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' _ _, ?_⟩
  rw [hT]
  exact isPullback_single_eq_add sY hY I h hirr hc' F hF (B i) (hBsm i) hZB hB' _

/-- Members of an injective family of prime divisors meeting at a point of dimension at most one
coincide. -/
private theorem eq_of_mem_support_of_ringKrullDim_le_one {Y : Scheme.{u}} {ι : Type*}
    {B : ι → Mori.PrimeDivisor Y} (hB : Function.Injective B) {y : Y}
    (hy : ringKrullDim (Y.presheaf.stalk y) ≤ 1) {a b : ι}
    (ha : y ∈ (B a).idealSheaf.support) (hb : y ∈ (B b).idealSheaf.support) : a = b := by
  have hcoh : Order.coheight y ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hy
    exact_mod_cast hy
  have h1 : ∀ i, y ∈ (B i).idealSheaf.support → y = (B i).genericPoint := fun i hi => by
    refine (B i).eq_genericPoint_of_mem_support hi (le_antisymm hcoh ?_)
    have hle : y ≤ (B i).genericPoint := by
      have : y ∈ closure {(B i).genericPoint} := by
        rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hi
      exact specializes_iff_mem_closure.mpr this
    rw [← (B i).coheight_genericPoint]
    exact Order.coheight_anti hle
  exact hB (AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((h1 a ha).symm.trans (h1 b hb)))

/-- The member of `blowUpTransformFamily` indexed by a prime divisor `P` away from the centre is
the ideal sheaf of the inverse transform of `P`. -/
private theorem blowUpTransformFamily_inl_eq {Y : Scheme.{u}} {ι : Type*}
    (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (B : ι → Mori.PrimeDivisor Y) (i : ι) {P' : Mori.PrimeDivisor (blowUp I)}
    (hP' : inverseTransformPrimeDivisor (blowUpToBase I) (B i) = some P') :
    blowUpTransformFamily (fun i => (B i).idealSheaf) I (Sum.inl i) = P'.idealSheaf := by
  have hA : IsIrreducible ((B i).idealSheaf.support : Set Y) := by
    change IsIrreducible ((B i).support : Set Y)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  rw [(inverseTransformPrimeDivisor_eq_some_iff.mp hP').2, inverseTransformIdeal,
    blowUpTransformFamily, Sum.elim_inl]
  congr 1
  apply Closeds.ext
  rw [coe_inverseTransform_blowUpToBase I _ hA (not_support_subset I hirr hc (B i)),
    Closeds.coe_closure]

/-- A reduced divisor `∑ⱼ Gⱼ` is snc when its components are smooth and are members of a family
of ideal sheaves which, at every closed point, is cut out by members of a regular system of
parameters. -/
private theorem isSNCDivisor_sum_single_of_coordinates {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {ι κ : Type*} [Fintype ι] {G : ι → Mori.PrimeDivisor X}
    (hG : Function.Injective G) {Dt : κ → X.IdealSheafData} {idx : ι → κ}
    (hidx_inj : Function.Injective idx) (hidx : ∀ j, Dt (idx j) = (G j).idealSheaf)
    (hsm : ∀ j, IsSmoothScheme ((G j).idealSheaf.subschemeι ≫ sX))
    (hcoord : ∀ p : X, IsClosed ({p} : Set X) → ∃ (N : ℕ) (w : Fin N → X.presheaf.stalk p)
      (cc : {i // p ∈ (Dt i).support} → Fin N), IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (Dt i.1) p = Ideal.span {w (cc i)}) ∧ Function.Injective cc) :
    IsSNCDivisor sX (∑ j, Finsupp.single (G j) (1 : ℤ)) := by
  classical
  have hsupp : ∀ P, P ∈ (∑ j, Finsupp.single (G j) (1 : ℤ)).support ↔ P ∈ Set.range G := by
    intro P
    rw [Finsupp.mem_support_iff, sum_single_apply hG]
    split_ifs with hP <;> simp [hP]
  refine ⟨fun P => ?_, fun P hP => ?_, fun p hp => ?_⟩
  · rw [DivisorWithCoeffs.coeff_apply, sum_single_apply hG]
    split_ifs <;> simp
  · obtain ⟨j, rfl⟩ := (hsupp P).1 hP
    exact hsm j
  · obtain ⟨N, w, cc, hw, hcc, hinj⟩ := hcoord p hp
    choose jE hjE using fun E : {E : Mori.PrimeDivisor X //
        E ∈ (∑ j, Finsupp.single (G j) (1 : ℤ)).support ∧ p ∈ E.support} => (hsupp E.1).1 E.2.1
    have hmemE : ∀ E, p ∈ (Dt (idx (jE E))).support := by
      intro E
      rw [hidx, hjE]
      exact E.2.2
    refine ⟨N, w, fun E => cc ⟨idx (jE E), hmemE E⟩, hw, ?_, ?_⟩
    · intro E E' hEE'
      have h1 : idx (jE E) = idx (jE E') := congrArg Subtype.val (hinj hEE')
      exact Subtype.ext (by rw [← hjE E, ← hjE E', hidx_inj h1])
    · intro E
      have := hcc ⟨idx (jE E), hmemE E⟩
      rwa [hidx, hjE] at this

private theorem injective_option_elim {α β : Type*} (b : β) {g : α → β}
    (hg : Function.Injective g) (hb : ∀ a, g a ≠ b) :
    Function.Injective fun j : Option α => j.elim b g := by
  rintro (_ | a) (_ | a') h
  · rfl
  · exact absurd h.symm (hb a')
  · exact absurd h (hb a)
  · exact congrArg some (hg h)

/-- Over a point of the centre, in the `x_j`-chart the exceptional divisor is `(x_j = 0)` and the
strict transform of `Bᵢ` is `(u_i = 0)` (absent when `i = j`), all members of the regular system
of parameters `x_j, (u_i)_{i ≠ j}, (x_l)_{l ≥ c}`; off the centre `π` is an isomorphism and the
coordinates of `B₁ + ⋯ + B_s` serve. Hence `π⁻¹_*(B₁ + ⋯ + B_s) + F` is snc. -/
private theorem exists_coordinates_blowUpTransformFamily_of_coordinates {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [CompactSpace Y] {n c s : ℕ}
    (I : Y.IdealSheafData) (B : Fin s → Mori.PrimeDivisor Y) (hB : Function.Injective B)
    (hsnc : IsSNCDivisor sY (∑ i, Finsupp.single (B i) 1))
    (hcoord : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      ∃ x : Fin n → Y.presheaf.stalk z, IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c}))
    (p : blowUp I) (hπp : IsClosed ({blowUpToBase I p} : Set Y)) :
    ∃ (N : ℕ) (w : Fin N → (blowUp I).presheaf.stalk p)
      (cc : {i // p ∈ (blowUpTransformFamily (fun i => (B i).idealSheaf) I i).support} → Fin N),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (blowUpTransformFamily (fun i => (B i).idealSheaf) I i.1) p =
          Ideal.span {w (cc i)}) ∧ Function.Injective cc := by
  classical
  have hBsupp : ∀ i, B i ∈ (∑ i, Finsupp.single (B i) (1 : ℤ)).support := fun i => by
    rw [Finsupp.mem_support_iff, sum_single_apply hB]
    simp
  refine exists_coordinates_blowUpTransformFamily_of_forall _ I p (fun hx => ?_) (fun _ => ?_)
    (fun _ hy _ _ ha hb => eq_of_mem_support_of_ringKrullDim_le_one hB hy ha hb)
  · obtain ⟨x, hx1, hxB, hxI⟩ := hcoord _ hx hπp
    choose j hj hjB using hxB
    refine ⟨n, x, fun i => j i.1, Finset.univ.filter (fun l : Fin n => (l : ℕ) < c), hx1,
      fun i => hjB i.1, fun a b hab => ?_, ?_⟩
    · have h1 : (j a.1 : ℕ) = j b.1 := congrArg Fin.val hab
      rw [hj, hj] at h1
      exact Subtype.ext (Fin.ext h1)
    · rw [hxI]
      congr 2
      ext l
      simp
  · obtain ⟨m, z, σ, hz, hσ, hzσ⟩ := hsnc.2.2 (blowUpToBase I p) hπp
    exact ⟨m, z, fun i => σ ⟨B i.1, hBsupp i.1, i.2⟩, hz, fun i => hzσ ⟨B i.1, hBsupp i.1, i.2⟩,
      fun a b hab => Subtype.ext (hB (congrArg Subtype.val (hσ hab)))⟩

private theorem isSNCDivisor_birationalInverseTransform_add_exceptional
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    {n : ℕ}
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc2 : 2 ≤ c) {s : ℕ} (B : Fin s → Mori.PrimeDivisor Y)
    (hB : Function.Injective B)
    (hBsm : ∀ i, IsSmoothScheme ((B i).idealSheaf.subschemeι ≫ sY))
    (hsnc : IsSNCDivisor sY (∑ i, Finsupp.single (B i) 1))
    (hcoord : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      ∃ x : Fin n → Y.presheaf.stalk z, IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c})) :
    haveI : IsIntegral Y := hY.toIsIntegral
    haveI : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    have hc' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
      hc ▸ by exact_mod_cast hc2
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
    let T : Mori.Divisor Y →+ Mori.Divisor (blowUp I) := birationalInverseTransform
      (blowUpToBase I)
      (Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h hirr
        hc').2.2.1
    ∀ F : Mori.PrimeDivisor (blowUp I), F.idealSheaf = exceptionalIdeal I →
      IsSNCDivisor (blowUpToBase I ≫ sY)
          (T (∑ i, Finsupp.single (B i) 1) + Finsupp.single F 1) := by
  intro hc' T F hF
  classical
  have : IsIntegral Y := hY.toIsIntegral
  have : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sY
  have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hZB := support_subset_of_forall_isClosed_of_coordinates sY I hcoord
  obtain ⟨hvar, hprop⟩ := isVariety_blowUp_and_isProper sY hY I hirr hc'
  have hbir := (Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h
    hirr hc').2.2.1
  choose B' hB' hη using fun i => exists_inverseTransformPrimeDivisor_eq_some I hirr hc' (B i)
  have hT : ∀ i, T (Finsupp.single (B i) 1) = Finsupp.single (B' i) 1 := fun i =>
    Mori.RationalMap.transformDivisor_single_of_eq_some
      (MMP.Flips.transformPrimeDivisor_inverse_of_map_genericPoint_eq ⟨hY, inferInstance⟩ _ hvar
        hbir (hη i)) 1
  have hB'F : ∀ i, B' i ≠ F := fun i => ne_of_map_genericPoint_eq I hirr hc' hF (hη i)
  let G : Option (Fin s) → Mori.PrimeDivisor (blowUp I) := fun j => j.elim F B'
  have hG : Function.Injective G := injective_option_elim F (fun a b hab =>
    hB (AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((hη a).symm.trans
      ((congrArg (fun P : Mori.PrimeDivisor (blowUp I) => blowUpToBase I P.genericPoint) hab).trans
        (hη b))))) hB'F
  have hD' : T (∑ i, Finsupp.single (B i) 1) + Finsupp.single F 1 =
      ∑ j, Finsupp.single (G j) (1 : ℤ) := by
    rw [map_sum, Fintype.sum_option]
    simp only [hT, G, Option.elim]
    exact add_comm _ _
  rw [hD']
  let D : Fin s → Y.IdealSheafData := fun i => (B i).idealSheaf
  have hfam : ∀ i, blowUpTransformFamily D I (Sum.inl i) = (B' i).idealSheaf := fun i =>
    blowUpTransformFamily_inl_eq I hirr hc' B i (hB' i)
  let idx : Option (Fin s) → Fin s ⊕ Unit := fun j => j.elim (Sum.inr ()) Sum.inl
  have hidx_inj : Function.Injective idx :=
    injective_option_elim _ Sum.inl_injective fun _ => Sum.inl_ne_inr
  have hidx : ∀ j, blowUpTransformFamily D I (idx j) = (G j).idealSheaf := by
    rintro (_ | i)
    · change I.comap (blowUpToBase I) = F.idealSheaf
      rw [hF]
    · exact hfam i
  have hsm : ∀ j, IsSmoothScheme ((G j).idealSheaf.subschemeι ≫ blowUpToBase I ≫ sY) := by
    rintro (_ | i)
    · change IsSmoothScheme (F.idealSheaf.subschemeι ≫ blowUpToBase I ≫ sY)
      rw [hF]
      have := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).2.1
      exact MMP.Resolution.isSmoothScheme_of_smooth _
    · change IsSmoothScheme ((B' i).idealSheaf.subschemeι ≫ blowUpToBase I ≫ sY)
      rw [← hfam i, blowUpTransformFamily, Sum.elim_inl]
      have : IsIntegral (B i).idealSheaf.subscheme := (B i).integral
      exact isSmoothScheme_strictTransform sY I (B i).idealSheaf h.2 (hBsm i)
        (le_of_support_subset sY I h.2 _ (hZB i)) (not_support_subset I hirr hc' (B i))
  refine isSNCDivisor_sum_single_of_coordinates _ hG hidx_inj hidx hsm fun p hp =>
    exists_coordinates_blowUpTransformFamily_of_coordinates sY I B hB hsnc hcoord p ?_
  rw [← Set.image_singleton]
  exact (blowUpToBase I).isClosedMap _ hp

end MMP.Proofs.lem_mmp_foundation_snc_adapted_centre_blowup

namespace MMP.Flips.ResolutionInputs

@[expose] public section

open MMP.Proofs.lem_mmp_foundation_snc_adapted_centre_blowup in
/-- **Blowing up a smooth centre adapted to an snc divisor.** Let `Y` be a smooth variety of
dimension `n` over `k`, `B₁, …, B_s` distinct smooth prime divisors with `B₁ + ⋯ + B_s` snc, and
`Z = V(I)` a smooth irreducible closed subscheme of codimension `c ≥ 2` with `s ≤ c`, such that at
every closed point `z ∈ Z` there is a regular system of parameters `x₁, …, xₙ` of `𝒪_{Y,z}` with
`Bᵢ = (xᵢ = 0)` and `Z = (x₁ = ⋯ = x_c = 0)` near `z`. Let `π : Y' ⟶ Y` be the blow-up of `Z`.
Then `Y'` is smooth over `k`, `F = π⁻¹(Z)` is a prime divisor, `π^*Bᵢ = π⁻¹_*Bᵢ + F` for every
`i`, and `π⁻¹_*(B₁ + ⋯ + B_s) + F` is an snc divisor. -/
@[mmp "lem_mmp_foundation_snc_adapted_centre_blowup"]
public theorem smooth_blowUp_and_isSNCDivisor_birationalInverseTransform_add_exceptional
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    {n : ℕ} (hn : topologicalKrullDim Y = n)
    (I : Y.IdealSheafData) (h : IsSmoothBlowup sY I) (hirr : IsIrreducible (I.support : Set Y))
    {c : ℕ}
    (hc : (c : ℕ∞) = codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    (hc2 : 2 ≤ c) {s : ℕ} (hsc : s ≤ c) (B : Fin s → Mori.PrimeDivisor Y)
    (hB : Function.Injective B)
    (hBsm : ∀ i, IsSmoothScheme ((B i).idealSheaf.subschemeι ≫ sY))
    (hsnc : IsSNCDivisor sY (∑ i, Finsupp.single (B i) 1))
    (hcoord : ∀ z ∈ (I.support : Set Y), IsClosed ({z} : Set Y) →
      ∃ x : Fin n → Y.presheaf.stalk z, IsRegularSystemOfParameters x ∧
        (∀ i : Fin s, ∃ j : Fin n, (j : ℕ) = i ∧
          IdealSheafData.stalk (B i).idealSheaf z = Ideal.span {x j}) ∧
        IdealSheafData.stalk I z = Ideal.span (x '' {j | (j : ℕ) < c})) :
    haveI : IsIntegral Y := hY.toIsIntegral
    haveI : Smooth sY := Threefold.Resolution.smooth_of_isSmoothScheme h.1
    haveI : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI := AlgebraicGeometry.isNormal_of_smooth sY
    have hc' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
      hc ▸ by exact_mod_cast hc2
    haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1
    haveI : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sY)
    haveI := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sY)
    let T : Mori.Divisor Y →+ Mori.Divisor (blowUp I) := birationalInverseTransform
      (blowUpToBase I)
      (Threefold.Resolution.smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h hirr
        hc').2.2.1
    Smooth (blowUpToBase I ≫ sY) ∧
      ∃ F : Mori.PrimeDivisor (blowUp I), F.idealSheaf = exceptionalIdeal I ∧
        (∀ i, ∃ hBi, Mori.Divisor.IsPullback (blowUpToBase I) (Finsupp.single (B i) 1) hBi
          (T (Finsupp.single (B i) 1) + Finsupp.single F 1)) ∧
        IsSNCDivisor (blowUpToBase I ≫ sY)
          (T (∑ i, Finsupp.single (B i) 1) + Finsupp.single F 1) := by
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast le_trans (by norm_num) hc2
  exact ⟨(Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sY I h).1,
    exceptionalPrimeDivisor sY I h hirr hc1, rfl,
    isPullback_single_eq_birationalInverseTransform_add_exceptional sY hY I h hirr hc hc2 B
      hBsm hcoord _ rfl,
    isSNCDivisor_birationalInverseTransform_add_exceptional sY hY I h hirr hc hc2 B hB
      hBsm hsnc hcoord _ rfl⟩

end

end MMP.Flips.ResolutionInputs

end

/-!
## Blow-ups of smooth varieties along smooth centres have trivial higher direct images

Let `V` be a smooth variety over a field `k` and `b : V' = Bl_Z V ⟶ V` the blow-up along a smooth
closed subscheme `Z ≠ V`. The canonical unit `𝒪_V ⟶ R b_* 𝒪_{V'}` is an isomorphism: the
structure-sheaf map `𝒪_V ⟶ b_* 𝒪_{V'}` is an isomorphism and `R^i b_* 𝒪_{V'} = 0` for `i > 0`.
Both properties are stable under composition (by the Leray spectral sequence), so the same holds
for every finite composition of such blow-ups.

### Main results

* `MMP.LcBpf.isIso_c_and_isZero_rightDerived_of_multiplicativeClosure_smoothBlowup`: for every
  finite composition `b` of blow-ups of smooth `k`-varieties along smooth proper centres,
  `b.c : 𝒪_V ⟶ b_* 𝒪_{V'}` is an isomorphism and `R^i b_* 𝒪_{V'} = 0` for all `i > 0`.

### Implementation notes

* The isomorphism `𝒪_V ≅ R b_* 𝒪_{V'}` in the derived category is expressed through its
  cohomology sheaves: in degree `0` it is the canonical map `b.c` of `b` (the comorphism
  `𝒪_V ⟶ b_* 𝒪_{V'}`), in positive degrees `R^i b_*` is the right derived functor
  `(Scheme.Modules.pushforward b).rightDerived i` evaluated at the structure sheaf
  `SheafOfModules.unit`.
* A single blow-up is a morphism isomorphic over `V` to `blowUpToBase I` for an ideal sheaf `I`
  with `MMP.Resolution.IsSmoothBlowup` (`V` and `V(I)` smooth over `k`), `V` a variety and
  `V(I) ≠ V`. Finite compositions are the members of
  `CategoryTheory.MorphismProperty.multiplicativeClosure` of this class; the `k`-structure is
  chosen afresh at each step.
* The base field is arbitrary: the computation is étale-local and characteristic-free.

### References

* [R. Hartshorne, *Algebraic Geometry*][Hartshorne], V.3.4
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.10
-/

section

universe u uProof

open CategoryTheory AlgebraicGeometry
open MMP.Resolution

namespace MMP.LcBpf

public section

/-- The structure-sheaf map `𝒪_Z ⟶ (f ≫ g)_* 𝒪_X` of a composite is an isomorphism when those
of the factors are. -/
theorem isIso_c_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsIso f.c)
    (hg : IsIso g.c) : IsIso (f ≫ g).c := by
  erw [PresheafedSpace.comp_c]
  exact IsIso.comp_isIso' hg (Functor.map_isIso _ _)

section Leray

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Higher direct images of the structure sheaf along a composite.** If `𝒪_Y ⟶ f_* 𝒪_X` is an
isomorphism, `R^i f_* 𝒪_X = 0` and `R^i g_* 𝒪_Y = 0` for all `i > 0`, then
`R^i (f ≫ g)_* 𝒪_X = 0` for every `i > 0`. -/
theorem isZero_rightDerived_comp_of_isIso_c {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso f.c)
    (hfR : ∀ i : ℕ, 0 < i → Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (hgR : ∀ i : ℕ, 0 < i → Limits.IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj
      (SheafOfModules.unit Y.ringCatSheaf)))
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.AffineHigherDirectImage in
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let K := (derivedPushforward f.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj OX)
  have hK : ∀ j : ℤ, j ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj K) := by
    intro j hj
    obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso f OX j
    refine Limits.IsZero.of_iso ?_ e
    rcases lt_or_gt_of_ne hj with h | h
    · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
        (Scheme.Modules.pushforward f) j h OX
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, by omega⟩
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (Scheme.Modules.pushforward f) m OX).1 (hfR m (by omega))
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun j hj => hK j (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun j hj => hK j (by omega)
  obtain ⟨Y0, ⟨eK⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  have hc := isIso_unitToPushforwardObjUnit_of_isIso_c f hf
  let eY0 : Y0 ≅ SheafOfModules.unit Y.ringCatSheaf :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app Y0).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules 0).mapIso eK.symm ≪≫
      (nonempty_homologyFunctor_derivedPushforward_iso f OX 0).some ≪≫
      Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso (Scheme.Modules.pushforward f) OX ≪≫
      (@asIso Y.Modules _ _ _ _ hc).symm
  let L := (derivedPushforward g.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf))
  let eL : (derivedPushforward (f ≫ g).toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj OX) ≅ L :=
    ((derivedPushforwardCompIso f.toLRSHom.toShHom g.toLRSHom.toShHom).app _).symm ≪≫
      (derivedPushforward g.toLRSHom.toShHom).mapIso
        (eK ≪≫ (DerivedCategory.singleFunctor Y.Modules 0).mapIso eY0)
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward (f ≫ g)) i OX).2 ?_
  obtain ⟨e₁⟩ := nonempty_homologyFunctor_derivedPushforward_iso (f ≫ g) OX i
  obtain ⟨e₂⟩ := nonempty_homologyFunctor_derivedPushforward_iso g
    (SheafOfModules.unit Y.ringCatSheaf) i
  refine Limits.IsZero.of_iso ?_ (e₁.symm ≪≫
    (DerivedCategory.homologyFunctor Z.Modules i).mapIso eL ≪≫ e₂)
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (Scheme.Modules.pushforward g) i
    (SheafOfModules.unit Y.ringCatSheaf)).1 (hgR i hi)

end Leray

end

end MMP.LcBpf

open MMP.LcBpf

namespace MMP.Proofs.lem_mmp_lc_bpf_smooth_blowup_unit

/-- The unit `𝒪_V ⟶ R b_* 𝒪_{V'}` is an isomorphism, expressed through cohomology sheaves. -/
private def UnitIsIso {V' V : Scheme.{uProof}} (b : V' ⟶ V) : Prop :=
  IsIso b.c ∧
    ∀ i : ℕ, 0 < i →
      Limits.IsZero (((Scheme.Modules.pushforward b).rightDerived i).obj
        (SheafOfModules.unit V'.ringCatSheaf))

/-- The identity functor of an abelian category with enough injectives has vanishing right
derived functors in positive degrees. -/
private theorem isZero_id_rightDerived_succ {C : Type*} [Category C] [Abelian C]
    [HasInjectiveResolutions C] (n : ℕ) (X : C) :
    Limits.IsZero (((𝟭 C).rightDerived (n + 1)).obj X) :=
  let I := injectiveResolution X
  Limits.IsZero.of_iso (I.cocomplex_exactAt_succ n).isZero_homology
    (I.isoRightDerivedObj (𝟭 C) (n + 1))

private theorem unitIsIso_id (V : Scheme.{uProof}) : UnitIsIso (𝟙 V) := by
  refine ⟨?_, fun i hi => ?_⟩
  · erw [PresheafedSpace.id_c]
    exact IsIso.id _
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hi
    let e := Scheme.Modules.pushforwardId V
    let φ : (Scheme.Modules.pushforward (𝟙 V)).rightDerived (n + 1) ≅
        (𝟭 V.Modules).rightDerived (n + 1) :=
      { hom := NatTrans.rightDerived e.hom (n + 1)
        inv := NatTrans.rightDerived e.inv (n + 1)
        hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
        inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id] }
    simpa using (isZero_id_rightDerived_succ (C := V.Modules) n _).of_iso (φ.app _)

private theorem unitIsIso_comp {X Y Z : Scheme.{uProof}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UnitIsIso f) (hg : UnitIsIso g) : UnitIsIso (f ≫ g) :=
  ⟨isIso_c_comp f g hf.1 hg.1, isZero_rightDerived_comp_of_isIso_c f g hf.1 hf.2 hg.2⟩

/-- The structure-sheaf map of a blow-up of a smooth variety along a proper smooth centre is an
isomorphism: a smooth variety is normal, integral and Noetherian, and the centre is a nonzero
ideal. -/
private theorem isIso_c_smoothBlowup (k : Type uProof) [Field k] {W' W : Scheme.{uProof}}
    (g : W' ⟶ W) (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (hI : IsSmoothBlowup sW I) (hsupp : I.support ≠ ⊤)
    (e : W' ≅ blowUp I) (he : e.hom ≫ blowUpToBase I = g) : IsIso g.c := by
  have : AlgebraicGeometry.IsVariety k sW := hW
  have : IsIntegral W := hW.toIsIntegral
  obtain ⟨_, h2⟩ := (isRegular_iff_regular_stalks W).1
    (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hI.1)
  have : IsNormal W := isNormal_of_forall_isRegularLocalRing h2
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsNoetherian W := {}
  have hne : I ≠ ⊥ := fun h => hsupp (by rw [h, Scheme.IdealSheafData.support_bot])
  subst he
  exact isIso_c_comp _ _ inferInstance (isIso_c_blowUpToBase_of_isNormal I hne)

section LocalCohomology

/-! ### The blow-up of a local ring along a regular sequence

For `x = x_0, …, x_c` a regular sequence generating `I` in a Noetherian ring `A`, the exceptional
divisor `E` of `X = Bl_I Spec A` is `ℙ^c_{A/I}` with `𝒪_X(m)|_E = 𝒪(m)`, so the sequences
`0 → 𝒪_X(m+1) → 𝒪_X(m) → i_*𝒪_E(m) → 0` and Serre vanishing give `Hᵖ(X, 𝒪_X) = 0` for `p > 0`
by descending induction on `m`. -/

open Limits Stacks.Cohomology.Basis
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

/-- `Hᵖ(X, F₂)` vanishes when `Hᵖ(X, F₁)` and `Hᵖ(X, F₃)` do. -/
private theorem isZero_Hgroup_X₂_of_shortExact (X : Scheme.{uProof})
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (p : ℕ) (hp : 0 < p)
    (h₁ : IsZero (Hgroup X.ringCatSheaf ⊤ p S.X₁))
    (h₃ : IsZero (Hgroup X.ringCatSheaf ⊤ p S.X₃)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p S.X₂) := by
  have hD := Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived X.ringCatSheaf
    (⊤ : X.Opens)
  refine (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
    X.ringCatSheaf hD hp _).1 ?_
  exact Stacks.AlgebraicGeometry.LerayAffineBase.isZero_obj_X₂ _ hS p
    ((Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
      X.ringCatSheaf hD hp _).2 h₁)
    ((Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj
      X.ringCatSheaf hD hp _).2 h₃)

/-- Cohomology vanishing ascends along a closed immersion. -/
private theorem isZero_Hgroup_pushforward_of_isZero_Hgroup {X Y : Scheme.{uProof}} (f : X ⟶ Y)
    [IsClosedImmersion f] (F : X.Modules) (hF : F.IsQuasicoherent) (i : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ i F)) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F)) := by
  have := hF
  refine (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F)).1 ?_
  have h2 := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf ⊤ i F).2 h
  have h3 : IsZero ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i).obj F)) := by
    rw [ModuleCat.isZero_iff_subsingleton] at h2 ⊢
    exact h2
  exact (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward f F i).isZero_iff.1 h3

variable {A : Type uProof} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The twists `i^*𝒪(m)`, `m ≥ 0`, of the exceptional divisor have no higher cohomology. -/
private theorem isZero_Hgroup_exceptional_twist {n : ℕ} (x : Fin (n + 1) → A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn x))
    (I : Ideal A) (hI : I = Ideal.span (Set.range x)) (m : ℤ) (hm : 0 ≤ m) (p : ℕ)
    (hp : 0 < p) :
    IsZero (Hgroup (Stacks.Blowup.blowUpSpec I).ringCatSheaf ⊤ p
      ((Scheme.Modules.pushforward (Stacks.Blowup.exceptionalIdealData I).subschemeι).obj
        ((Scheme.Modules.pullback (Stacks.Blowup.exceptionalIdealData I).subschemeι).obj
          (Stacks.Blowup.blowUpTwist I m)))) := by
  have hx : ∀ i, x i ∈ I := fun i => hI ▸ Ideal.subset_span ⟨i, rfl⟩
  have hbij : Function.Bijective (AssociatedGraded.polyGradedHom I x hx) :=
    AssociatedGraded.bijective_polyGradedHom _ _ _ hI.symm
      ((Stacks.RingTheory.RegularIdealSheaf.bijective_associatedGradedMap_iff _).1
        ((Stacks.RingTheory.RegularIdealSheaf.isQuasiRegular_ofFn_iff _).1
          (Stacks.AlgebraicGeometry.RegularIdealSheaf.isQuasiRegular_ofFn_of_isWeaklyRegular _
            hreg))).injective
  let ρ := Stacks.Blowup.exceptionalIsoProjectiveSpace I x hx hI.symm hbij
  have hcomp := Stacks.Blowup.subschemeι_comp_blowUpSpecToProjSpace I x hx hI hbij
  let e := Stacks.Blowup.pullbackExceptionalTwistIso I x hx hI ρ hcomp m
  have hqc : ((Scheme.Modules.pullback (Stacks.Blowup.exceptionalIdealData I).subschemeι).obj
      (Stacks.Blowup.blowUpTwist I m)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ _
      (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf _ m)
  refine isZero_Hgroup_pushforward_of_isZero_Hgroup _ _ hqc p ?_
  have hP : IsZero (Hgroup (AlgebraicGeometry.Proj
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (A ⧸ I))).ringCatSheaf
      ⊤ p (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (A ⧸ I)) m)) :=
    Stacks.ProjectiveSpace.SerreVanishing.isZero_Hgroup_twistingSheaf_of_pos (A ⧸ I) n m hm p hp
  have hE := (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff ρ _ p).2 hP
  exact hE.of_iso
    ((Hfunctor (Stacks.Blowup.exceptionalIdealData I).subscheme.ringCatSheaf ⊤ p).mapIso e)

/-- Descending induction: the nonnegative twists of the blow-up have no higher cohomology. -/
private theorem isZero_Hgroup_blowUpTwist_natCast {n : ℕ} (x : Fin (n + 1) → A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn x))
    (I : Ideal A) (hI : I = Ideal.span (Set.range x)) (m : ℕ) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (Stacks.Blowup.blowUpSpec I).ringCatSheaf ⊤ p
      (Stacks.Blowup.blowUpTwist I (m : ℤ))) := by
  obtain ⟨q₀, hq₀⟩ := Stacks.Blowup.exists_forall_isZero_Hgroup_twistingSheaf_reesGrading I
  suffices key : ∀ k m : ℕ, q₀ ≤ m + k →
      IsZero (Hgroup (Stacks.Blowup.blowUpSpec I).ringCatSheaf ⊤ p
        (Stacks.Blowup.blowUpTwist I (m : ℤ))) from key q₀ m (by omega)
  intro k
  induction k with
  | zero => exact fun m hm => hq₀ m (by omega) p hp
  | succ k ih =>
    intro m hm
    obtain ⟨h, hS⟩ := Stacks.Blowup.shortExact_twist_exceptional I
      (m := ((m + 1 : ℕ) : ℤ)) (n := (m : ℤ)) (by push_cast; rfl)
    exact isZero_Hgroup_X₂_of_shortExact _ hS p hp (ih (m + 1) (by omega))
      (isZero_Hgroup_exceptional_twist x hreg I hI m (by positivity) p hp)

/-- **The blow-up of a Noetherian ring in an ideal generated by a regular sequence has no higher
structure-sheaf cohomology.** -/
private theorem isZero_Hgroup_blowUp_ofIdealTop_of_isWeaklyRegular {n : ℕ} (x : Fin (n + 1) → A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn x))
    (I : Ideal A) (hI : I = Ideal.span (Set.range x)) (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I))).ringCatSheaf ⊤ p
      (SheafOfModules.unit (blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I))).ringCatSheaf)) := by
  obtain ⟨e⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase (R := A) (K := I)
  have hei : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let e' : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
      blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)) :=
    @asIso _ _ _ _ e.hom.left hei
  have h0 := isZero_Hgroup_blowUpTwist_natCast x hreg I hI 0 p hp
  have h : IsZero (Hgroup (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).ringCatSheaf ⊤ p
      (SheafOfModules.unit
        (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).ringCatSheaf)) :=
    h0.of_iso ((Hfunctor (AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I)).ringCatSheaf ⊤
      p).mapIso (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
        (Stacks.Blowup.reesGrading I)).symm)
  refine (Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e' _ p).mp (h.of_iso ?_)
  exact (Hfunctor (AlgebraicGeometry.Proj
    (Stacks.Blowup.reesGrading I)).ringCatSheaf ⊤ p).mapIso
      (Scheme.Modules.pullbackUnitIso e'.hom)

open Stacks.AlgebraicGeometry.RegularIdealSheaf in
/-- Near a point of a smooth centre, its ideal is generated by a weakly regular sequence. -/
private theorem exists_affineOpen_isWeaklyRegular_of_smoothBlowup (k : Type uProof) [Field k]
    {W : Scheme.{uProof}} (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (hI : MMP.Resolution.IsSmoothBlowup sW I) (y : W)
    (hy : y ∈ I.support) :
    ∃ (U : W.affineOpens) (_ : y ∈ U.1) (r : ℕ) (f : Fin r → Γ(W, U.1)),
      RingTheory.Sequence.IsWeaklyRegular Γ(W, U.1) (List.ofFn f) ∧
        I.ideal U = Ideal.span (Set.range f) := by
  have : AlgebraicGeometry.IsVariety k sW := hW
  have : LocallyOfFinitePresentation sW :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth sW := (MMP.Mori.isSmoothScheme_iff sW).1 hI.1
  have : LocallyOfFiniteType (I.subschemeι ≫ sW) := inferInstance
  have : LocallyOfFinitePresentation (I.subschemeι ≫ sW) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : Smooth (I.subschemeι ≫ sW) := (MMP.Mori.isSmoothScheme_iff _).1 hI.2
  set i := I.subschemeι
  have hi : IsRegularImmersion i :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i sW
  have hreg : IsRegularIdealSheaf W.toRingedSpace (definingIdealOfHom i) := by
    have hfac : i.liftCoborder ≫ i.coborderRange.ι = i := i.liftCoborder_ι
    have : IsClosedImmersion (i.liftCoborder ≫ i.coborderRange.ι) := by
      rw [hfac]
      infer_instance
    have h := (Stacks.AlgebraicGeometry.isRegularIdealSheaf_comp_open_iff i.liftCoborder
      i.coborderRange.ι).mpr hi
    rwa [hfac] at h
  have hy' : y ∈ Set.range i.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hy
  obtain ⟨z, rfl⟩ := hy'
  obtain ⟨U, hzU, r, f, hwr, hker⟩ :=
    Stacks.AlgebraicGeometry.exists_affine_isWeaklyRegular_generators i hreg z
  refine ⟨U, hzU, r, f, hwr, ?_⟩
  rw [← hker, ← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]

/-- The blow-up of the local ring of a smooth variety at a point of a smooth centre has no
higher structure-sheaf cohomology. -/
private theorem isZero_Hgroup_blowUp_comap_fromSpecStalk (k : Type uProof) [Field k]
    {W : Scheme.{uProof}} (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (hI : MMP.Resolution.IsSmoothBlowup sW I) (y : W)
    (hy : y ∈ I.support) (q : ℕ) (hq : 0 < q) :
    IsZero (Hgroup (blowUp (I.comap (W.fromSpecStalk y))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (I.comap (W.fromSpecStalk y))).ringCatSheaf)) := by
  have : AlgebraicGeometry.IsVariety k sW := hW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  obtain ⟨U, hyU, r, f, hwr, hIU⟩ :=
    exists_affineOpen_isWeaklyRegular_of_smoothBlowup k sW I hW hI y hy
  let g := W.presheaf.germ U.1 y hyU
  have hst : IdealSheafData.stalk I y = Ideal.span (Set.range (g.hom ∘ f)) := by
    rw [IdealSheafData.stalk_eq_map_germ I y U hyU, hIU, Ideal.map_span, Set.range_comp]
  rw [Stacks.ResolutionOfSurfaces.comap_fromSpecStalk_eq_ofIdealTop]
  cases r with
  | zero =>
    have hbot : Scheme.IdealSheafData.ofIdealTop ((IdealSheafData.stalk I y).map
        (Scheme.ΓSpecIso (W.presheaf.stalk y)).inv.hom) = ⊥ := by
      refine Scheme.IdealSheafData.ext_of_isAffine ?_
      rw [Scheme.IdealSheafData.ofIdealTop_ideal, hst, Set.range_eq_empty, Ideal.span_empty,
        Ideal.map_bot, Ideal.map_bot]
      rfl
    rw [hbot]
    have := isEmpty_blowUp_bot (Spec (W.presheaf.stalk y))
    exact Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine _ _ q hq
  | succ n =>
    let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨y, hyU⟩
    have hloc := U.2.isLocalization_stalk ⟨y, hyU⟩
    have : Module.Flat Γ(W, U.1) (W.presheaf.stalk y) :=
      IsLocalization.flat _ (U.2.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    have hreg' : RingTheory.Sequence.IsWeaklyRegular (W.presheaf.stalk y)
        (List.ofFn (g.hom ∘ f)) := by
      have := hwr.of_flat (S := W.presheaf.stalk y)
      rw [List.map_ofFn] at this
      exact this
    exact isZero_Hgroup_blowUp_ofIdealTop_of_isWeaklyRegular (g.hom ∘ f) hreg' _ hst q hq

end LocalCohomology

section Globalization

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.Basis TopologicalSpace Stacks.AlgebraicGeometry.TopDegreeBaseChange
  Stacks.Cohomology.AffineBase Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
/-- `R^q g_* 𝒪 = 0` for a blow-up `g` of a variety once the blow-ups of its local rings at the
points of the centre have no positive-degree structure-sheaf cohomology. -/
private theorem isZero_rightDerivedPlus_of_local (k : Type uProof) [Field k]
    {W' W : Scheme.{uProof}} (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (e : W' ≅ blowUp I) (q : ℕ) (hq : 0 < q)
    (hloc : ∀ y ∈ I.support, Limits.IsZero (Hgroup
      (blowUp (I.comap (W.fromSpecStalk y))).ringCatSheaf ⊤ q
      (SheafOfModules.unit (blowUp (I.comap (W.fromSpecStalk y))).ringCatSheaf))) :
    Limits.IsZero (((Scheme.Modules.pushforward (e.hom ≫ blowUpToBase I)).rightDerivedPlus q).obj
      (SheafOfModules.unit W'.ringCatSheaf)) := by
  have : AlgebraicGeometry.IsVariety k sW := hW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : IsProper (blowUpToBase I) := inferInstance
  have : IsProper (e.hom ≫ blowUpToBase I) := inferInstance
  have : QuasiCompact (e.hom ≫ blowUpToBase I) := inferInstance
  have : IsSeparated (e.hom ≫ blowUpToBase I) := inferInstance
  have : QuasiSeparated (e.hom ≫ blowUpToBase I) := IsSeparated.instQuasiSeparated _
  have hqc : (SheafOfModules.unit W'.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have hF : (((Scheme.Modules.pushforward (e.hom ≫ blowUpToBase I)).rightDerivedPlus q).obj
      (SheafOfModules.unit W'.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus _ _ hqc q
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ (fun y => ?_)
  by_cases hy : y ∈ I.support
  · let b := W.fromSpecStalk y
    have : Flat b := flat_fromSpecStalk W y
    obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap b I
    set p := blowUpToBase (I.comap b)
    have : IsProper p := inferInstance
    have hqc₁ : (SheafOfModules.unit (blowUp (I.comap b)).ringCatSheaf).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
    have hp : Limits.IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp (I.comap b)).ringCatSheaf)) :=
      isZero_rightDerivedPlus_pushforward_of_isZero_cohomology p q _
        ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup _ _ q).2 (hloc y hy))
    have hsq : IsPullback e.inv (blowUpToBase I) (e.hom ≫ blowUpToBase I) (𝟙 W) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have hpb' : IsPullback (h ≫ e.inv) p (e.hom ≫ blowUpToBase I) b := by
      simpa using hpb.flip.paste_horiz hsq
    have hpull : Limits.IsZero ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward (e.hom ≫ blowUpToBase I)).rightDerivedPlus q).obj
          (SheafOfModules.unit W'.ringCatSheaf))) := by
      have h₁ : Limits.IsZero (((Scheme.Modules.pushforward p).rightDerivedPlus q).obj
          ((Scheme.Modules.pullback (h ≫ e.inv)).obj (SheafOfModules.unit W'.ringCatSheaf))) :=
        hp.of_iso (((Scheme.Modules.pushforward p).rightDerivedPlus q).mapIso
          (Scheme.Modules.pullbackUnitIso (h ≫ e.inv)))
      exact h₁.of_iso (Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso hpb'
        (SheafOfModules.unit W'.ringCatSheaf) q)
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    obtain ⟨e', -⟩ := exists_fromSpecStalkSectionsStalkLinearEquiv
      (((Scheme.Modules.pushforward (e.hom ≫ blowUpToBase I)).rightDerivedPlus q).obj
        (SheafOfModules.unit W'.ringCatSheaf)) y hU hyU
    have hsub : Subsingleton (Γ((Scheme.Modules.pullback b).obj
        (((Scheme.Modules.pushforward (e.hom ≫ blowUpToBase I)).rightDerivedPlus q).obj
          (SheafOfModules.unit W'.ringCatSheaf)), ⊤)) := by
      have := (SheafOfModules.evaluation _ (Opposite.op ⊤)).map_isZero hpull
      exact (ModuleCat.isZero_iff_subsingleton.mp this)
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact e'.symm.toEquiv.subsingleton
  · let V : W.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
    have hyV : y ∈ V := hy
    have hiso : IsIso ((e.hom ≫ blowUpToBase I) ∣_ V) := by
      rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' (inferInstanceAs (IsIso (e.hom ∣_ _)))
        (isIso_blowUp_restrict_compl_support I)
    have : IsAffineHom ((e.hom ≫ blowUpToBase I) ∣_ V) := inferInstance
    have : ((Scheme.Modules.restrictFunctor ((e.hom ≫ blowUpToBase I) ⁻¹ᵁ V).ι).obj
        (SheafOfModules.unit W'.ringCatSheaf)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ _
    exact isZero_stalk_of_isZero_rightDerivedPlus_restrict _ V y hyV _ (by positivity)
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom _ _ q
        (by exact_mod_cast hq))

/-- `R^i b_* 𝒪 = 0` for `i > 0`, by flat base change to the local rings of `W`. -/
private theorem isZero_rightDerived_smoothBlowup (k : Type uProof) [Field k]
    {W' W : Scheme.{uProof}} (g : W' ⟶ W) (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (hI : IsSmoothBlowup sW I)
    (e : W' ≅ blowUp I) (he : e.hom ≫ blowUpToBase I = g) (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj
      (SheafOfModules.unit W'.ringCatSheaf)) := by
  subst he
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ i _).2
    (isZero_rightDerivedPlus_of_local k sW I hW e i hi
      fun y hy => isZero_Hgroup_blowUp_comap_fromSpecStalk k sW I hW hI y hy i hi)

end Globalization

private theorem unitIsIso_smoothBlowup (k : Type uProof) [Field k] {W' W : Scheme.{uProof}}
    (g : W' ⟶ W) (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData)
    (hW : MMP.Mori.IsVariety k sW) (hI : IsSmoothBlowup sW I) (hsupp : I.support ≠ ⊤)
    (e : W' ≅ blowUp I) (he : e.hom ≫ blowUpToBase I = g) : UnitIsIso g :=
  ⟨isIso_c_smoothBlowup k g sW I hW hI hsupp e he,
    isZero_rightDerived_smoothBlowup k g sW I hW hI e he⟩

end MMP.Proofs.lem_mmp_lc_bpf_smooth_blowup_unit

namespace MMP.LcBpf

@[expose] public section

open MMP.Proofs.lem_mmp_lc_bpf_smooth_blowup_unit in
/-- **Structure-sheaf vanishing for smooth-centre blow-ups.** Let `b : V' ⟶ V` be a finite
composition of blow-ups `blowUpToBase I` of smooth varieties over `k` along smooth closed
subschemes `V(I) ≠ V` (up to isomorphism over the base). Then the canonical map
`b.c : 𝒪_V ⟶ b_* 𝒪_{V'}` is an isomorphism and `R^i b_* 𝒪_{V'} = 0` for every `i > 0`; that is,
the unit `𝒪_V ⟶ R b_* 𝒪_{V'}` is an isomorphism. -/
@[mmp "lem_mmp_lc_bpf_smooth_blowup_unit"]
public theorem isIso_c_and_isZero_rightDerived_of_multiplicativeClosure_smoothBlowup
    (k : Type u) [Field k] {V' V : Scheme.{u}} (b : V' ⟶ V)
    (hb : MorphismProperty.multiplicativeClosure
      (fun (W' W : Scheme.{u}) (g : W' ⟶ W) =>
        ∃ (sW : W ⟶ Spec (.of k)) (I : W.IdealSheafData),
          Mori.IsVariety k sW ∧ IsSmoothBlowup sW I ∧ I.support ≠ ⊤ ∧
            ∃ e : W' ≅ blowUp I, e.hom ≫ blowUpToBase I = g) b) :
    IsIso b.c ∧
      ∀ i : ℕ, 0 < i →
        Limits.IsZero (((Scheme.Modules.pushforward b).rightDerived i).obj
          (SheafOfModules.unit V'.ringCatSheaf)) := by
  show UnitIsIso b
  induction hb with
  | of g hg =>
    obtain ⟨sW, I, hW, hI, hsupp, e, he⟩ := hg
    exact unitIsIso_smoothBlowup k g sW I hW hI hsupp e he
  | id x => exact unitIsIso_id x
  | comp_of f g _ hg ih =>
    obtain ⟨sW, I, hW, hI, hsupp, e, he⟩ := hg
    exact unitIsIso_comp f g ih (unitIsIso_smoothBlowup k g sW I hW hI hsupp e he)

end

end MMP.LcBpf

end
