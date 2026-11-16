module
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
public import MMP.AlgebraicGeometry.Normalization.IntegralScheme
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic

/-!
# Foundations for the resolution of surface and threefold singularities

This file collects foundational facts used in the resolution of singularities of surfaces
and threefolds.

* On the blow-up `π : X = Bl_Z Y ⟶ Y` of a smooth variety along a smooth irreducible centre of
  codimension `c ≥ 2`, a nonzero rational top form `σ` satisfies
  `div_X(π^*σ) = π^*div_Y(σ) + (c - 1)E`, `E` the exceptional divisor.
* The blow-up of a closed point of a smooth surface over an algebraically closed field is a
  smooth surface whose exceptional curve `F` is a `(-1)`-curve, and `π^*K_Y + F` is a canonical
  divisor of the blow-up.
* A Noetherian normal domain is the intersection, in its fraction field, of its localizations at
  height-one primes.
* Twisting a graded algebra by an invertible sheaf does not change its relative `Proj`.
* The normalization `ν : X̃ ⟶ X` of a variety is finite, surjective and birational from a normal
  variety, an isomorphism over the (open) normal locus, universal for dominant morphisms from
  normal integral schemes, and projective when `X` is.

## Main results

* `Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms`:
  the smooth blow-up and the divisor of a pulled-back top form.
* `Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve`:
  the exceptional curve of a point blow-up of a smooth surface is a `(-1)`-curve.
* `Threefold.Resolution.isCanonicalDivisor_pullback_add_single_blowUp_singleton`:
  `K_{Y'} = π^*K_Y + F`.
* `Threefold.iInf_localization_height_eq_one_eq_bot`: `A = ⋂_{ht 𝔭 = 1} A_𝔭`.
* `exists_iso_relativeProjToBase_twist`: `Proj_S(𝒜 ⊗ ℒ) ≅ Proj_S(𝒜)` over `S`.
* `Threefold.normalization_spec`: the properties of the normalization of a variety.

## Implementation notes

* The centre of a blow-up is given by its ideal sheaf; the exceptional divisor is the prime
  divisor whose ideal sheaf is `AlgebraicGeometry.exceptionalIdeal`. Divisors on a smooth scheme
  are Cartier, so `π^*` on divisors is `MMP.Mori.Divisor.pullback`.
* The localization `A_𝔭` is realised inside the fraction field as
  `Localization.subalgebra.ofField`, so the intersection is an infimum of `A`-subalgebras.
* The normal locus is open by commutative algebra: when the integral closure `A'` of a domain `A`
  is a finite `A`-module, the generators of `A'` acquire at a normal prime `𝔭` a common
  denominator `f ∉ 𝔭`, and then `A_𝔮` is integrally closed whenever `f ∉ 𝔮`. Projectivity of
  `X̃` comes from an ample invertible module on `X`: a finite morphism to a base carrying one is
  H-projective, and H-projective morphisms compose. Automorphisms lift by the universal property
  applied to `ν ≫ σ` and `ν ≫ σ⁻¹`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98]
* [J. Kollár, *Flips and abundance for algebraic threefolds*][KollarFlips]
* [R. Hartshorne, *Algebraic geometry*][Har77], II, Exercise 8.5 and V, Proposition 3.3
* [Stacks Project, Tags 031T, 02NC, 035N, 01W8](https://stacks.math.columbia.edu)
-/

@[expose] public section

universe u

/-! ## Smooth blow-ups -/

namespace MMP.Threefold.Resolution

section SmoothBlowup

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Resolution

/-- **The divisor of a pulled-back top form on a smooth blow-up.** Let `Y` be a smooth variety of
dimension `n` over `k`, `Z = V(I)` a smooth irreducible closed subscheme of codimension `c ≥ 2`,
and `π : X = Bl_Z Y ⟶ Y` the blow-up. Then `X` is a variety smooth over `k`; `π` is projective,
birational and an isomorphism over `Y ∖ Z`; if `Y` is a projective variety, so is `X`; and the
exceptional divisor `E = π⁻¹(Z)` is a prime divisor of `X` such that for every nonzero rational
`n`-form `σ` on `Y`, `div_X(π^*σ) = π^*div_Y(σ) + (c - 1)E`. -/
@[mmp "lem_mmp_foundation_fa_smooth_blowup_canonical_form"]
public theorem isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : Mori.IsVariety k sY)
    {n : ℕ} (hn : topologicalKrullDim Y = n)
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
    Mori.IsVariety k (blowUpToBase I ≫ sY) ∧ Smooth (blowUpToBase I ≫ sY) ∧
      IsProjective (blowUpToBase I) ∧ IsBirationalMorphism (blowUpToBase I) ∧
      IsIso (blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens)) ∧
      (Mori.IsProjectiveVariety k sY → Mori.IsProjectiveVariety k (blowUpToBase I ≫ sY)) ∧
      ∃ E : Mori.PrimeDivisor (blowUp I), E.idealSheaf = exceptionalIdeal I ∧
        ∀ σ : RationalPluriForms sY n 1, σ ≠ 0 →
          divisorOfForm (pullbackRationalPluriForms sY (blowUpToBase I) σ) =
            (divisorOfForm σ).pullback (MMP.Fourfold.isCartier_of_isSmoothScheme h.1 _)
                (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant
                  (blowUpToBase I) _) +
              ((c : ℤ) - 1) • Finsupp.single E 1 := by
  have : IsIntegral Y := hY.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : Smooth sY := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smooth sY
  have hc2' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) :=
    hc ▸ by exact_mod_cast hc2
  have hc1 := one_le_two.trans hc2'
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  obtain ⟨hsm, hproj, hbir, hiso, -, hprojY⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sY I h hirr hc2'
  have : IsProjective (blowUpToBase I) := hproj
  have hvar : AlgebraicGeometry.IsVariety k (blowUpToBase I ≫ sY) := {}
  exact ⟨hvar, hsm, hproj, hbir, hiso, fun hP => (isProjectiveVariety_iff_isProjective k _).mpr
      (@hprojY ((isProjectiveVariety_iff_isProjective k sY).mp hP)),
    exceptionalPrimeDivisor sY I h hirr hc1, rfl,
    divisorOfForm_pullbackRationalPluriForms_blowUpToBase I sY h hirr hc (by omega) hn⟩

end SmoothBlowup

/-! ## The blow-up of a point of a smooth surface -/

section PointBlowup

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Threefold.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The support of a prime divisor on the blow-up whose ideal sheaf is the exceptional ideal is
the preimage of the centre. -/
private lemma coe_support_eq_preimage_support {Y : Scheme.{u}} {I : Y.IdealSheafData}
    [IsLocallyNoetherian (blowUp I)] [IsNormal (blowUp I)] (F : MMP.Mori.PrimeDivisor (blowUp I))
    (hF : F.idealSheaf = exceptionalIdeal I) :
    (F.support : Set (blowUp I)) = blowUpToBase I ⁻¹' (I.support : Set Y) := by
  have h := congrArg (fun J : Scheme.IdealSheafData _ => SetLike.coe J.support)
    ((vanishingIdeal_closure_genericPoint_eq_idealSheaf F).trans hF)
  simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, h]
  simp [exceptionalIdeal, Scheme.IdealSheafData.support_comap]

/-- **The exceptional curve of a point blow-up of a smooth surface.** Let `Y` be a surface
smooth over an algebraically closed field `k`, `p ∈ Y` a closed point and `π : Y' ⟶ Y` the
blow-up of the reduced point `p`. Then `Y'` is a surface smooth over `k`; `π` is projective,
birational and an isomorphism over `Y ∖ {p}`; and there is a prime divisor `F` of `Y'`, with
ideal sheaf the inverse-image ideal `exceptionalIdeal` of `p` and support `π⁻¹{p}`, which is a
`(-1)`-curve: `F ≅ ℙ¹_k` over `k` and `(F · F) = -1`. -/
@[mmp "lem_mmp_foundation_km_surface_point_blowup"]
public theorem isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : Mori.IsVariety k sY) [Smooth sY] (hYd : topologicalKrullDim Y = 2) {p : Y}
    (hp : IsClosed ({p} : Set Y)) :
    Mori.IsVariety k (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) ∧
      Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY) ∧
      topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) = 2 ∧
      IsProjective (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) ∧
      Mori.IsBirationalMorphism (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) ∧
      IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∣_
        (⟨{p}ᶜ, hp.isOpen_compl⟩ : Y.Opens)) ∧
      ∃ F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)),
        F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ∧
        (F.support : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) =
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⁻¹' {p} ∧
        haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
          (isSmoothScheme_blowUp_singleton hY ((Mori.isSmoothScheme_iff sY).mpr ‹_›)
            hYd hp)).1
        haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
          (isSmoothScheme_blowUp_singleton hY ((Mori.isSmoothScheme_iff sY).mpr ‹_›)
            hYd hp)).2
        haveI := (isVariety_blowUp_singleton hY hYd hp).toQuasiCompact
        Mori.IsMinusOneCurve (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sY)
          F := by
  have hYs : MMP.Mori.IsSmoothScheme sY := (MMP.Mori.isSmoothScheme_iff sY).mpr ‹_›
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hp
  have hirr := isIrreducible_support_vanishingIdeal_singleton hp
  have hcodim := codimension_vanishingIdeal_singleton_eq_two hY hYd hp
  obtain ⟨-, hproj, -, -, -, -⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sY _ hsb hirr hcodim.ge
  obtain ⟨hsm, -, hbir, hiso, F, hF, ⟨e, he⟩, hFC, hself⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hY hYs hYd hp
  have hsmY' := isSmoothScheme_blowUp_singleton hY hYs hYd hp
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmY').1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsmY').2
  have := (isVariety_blowUp_singleton hY hYd hp).toQuasiCompact
  refine ⟨isVariety_blowUp_singleton hY hYd hp, hsm,
    topologicalKrullDim_blowUp sY _ hsb hirr (by rw [hcodim]; norm_num) hYd, hproj, hbir, hiso,
    F, hF, by rw [coe_support_eq_preimage_support F hF, support_vanishingIdeal_singleton hp],
    vanishingIdeal_closure_genericPoint_eq_idealSheaf F ▸ hFC.isProper, ?_, ?_⟩
  · rw [hF]
    refine ⟨(projectiveLineIsoProjectiveSpaceOver k ≪≫
      (MMP.Intersection.ProjSpace.isoProjectiveSpaceOver k 1).symm) ≪≫ e.symm, ?_⟩
    rw [← he]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← MMP.Intersection.ProjSpace.isoProjectiveSpaceOver_hom_over k 1, Iso.inv_hom_id_assoc,
      projectiveLineIsoProjectiveSpaceOver_hom_fst]
  · have hint := MMP.Mori.isIntersectionNumber_of_properCurve (k := k) _
      (isQCartier_single_of_isSmoothScheme hsmY' F) ⟨F.genericPoint, hFC⟩ F rfl
    rwa [hself _ rfl, toQDivisor_single, Int.cast_one] at hint

/-- The pull-back of a nonzero `m`-canonical form along an extension admitting a pull-back
generator is nonzero. -/
private theorem pullbackForms_ne_zero {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) {m : ℤ} {τ : PluriForms k K d m}
    (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- The pull-back of a nonzero rational form along a blow-up along an irreducible centre of
positive codimension is nonzero. -/
private theorem pullbackRationalPluriForms_blowUpToBase_ne_zero {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (I : Y.IdealSheafData) (hirr : IsIrreducible (I.support : Set Y))
    (hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y))
    [IsIntegral (blowUp I)] [IsDominant (blowUpToBase I)] {d : ℕ}
    (hd : topologicalKrullDim Y = d) {m : ℤ} {σ : RationalPluriForms sY d m} (hσ : σ ≠ 0) :
    pullbackRationalPluriForms sY (blowUpToBase I) σ ≠ 0 := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (blowUpToBase I ≫ sY)
  let := functionFieldMapAlgebra (blowUpToBase I)
  have := isScalarTower_functionFieldMap sY (blowUpToBase I)
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY (blowUpToBase I)
    (isBirationalMorphism_blowUpToBase I hirr hc).functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hd)
  exact pullbackForms_ne_zero hω hσ

/-- On a smooth variety of dimension `n`, the divisor of a nonzero rational `n`-form is a
canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) (hXs : IsSmoothScheme sX)
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sX n := by
  obtain ⟨K, hK⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme _ _ _ _ _ k _ _ hX hXs n hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul ⟨hX, inferInstance⟩ hK hτ

section

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- **The canonical divisor of the blow-up of a point of a smooth surface.** Let `Y` be a smooth
surface over an algebraically closed field `k`, `y ∈ Y` a closed point, `π : Y' ⟶ Y` the blow-up
of `y` and `F` its exceptional curve. For every canonical divisor `K_Y` of `Y`, the divisor
`π^* K_Y + F` is a canonical divisor of `Y'`. -/
@[mmp "lem_mmp_threefold_surface_blowup_canonical"]
public theorem isCanonicalDivisor_pullback_add_single_blowUp_singleton
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    {F : Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    {K : Divisor Y}
    (hK : haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
      haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
      K.IsCanonicalDivisor sY 2) :
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      (isSmoothScheme_blowUp_singleton hY hYs hYd hy)).2
    haveI := compactSpace_blowUp_singleton hY hYd hy
    (Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) K
        (MMP.Fourfold.isCartier_of_isSmoothScheme hYs K)
        (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy K) +
      Finsupp.single F 1).IsCanonicalDivisor
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) 2 := by
  have : IsIntegral Y := hY.toIsIntegral
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : CompactSpace Y := have := hY.toQuasiCompact; QuasiCompact.compactSpace_of_compactSpace sY
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs).2
  have hsm := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hc1 := one_le_codimension_vanishingIdeal_singleton hYd hy
  have hvar := isVariety_blowUp_singleton hY hYd hy
  have hYs' := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').1
  have := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').2
  have := compactSpace_blowUp_singleton hY hYd hy
  have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := hvar.toIsIntegral
  have := isDominant_blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) hirr hc1
  obtain ⟨σ, hσ0, hσ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq ⟨hY, inferInstance⟩ hK
  obtain rfl : divisorOfForm σ = K := Finsupp.ext hσ
  obtain rfl : MMP.Resolution.exceptionalPrimeDivisor sY _ hsm hirr hc1 = F := by
    rcases F with ⟨J, _, _⟩
    cases hF
    rfl
  have hcan := isCanonicalDivisor_divisorOfForm hvar hYs'
    (topologicalKrullDim_blowUp sY _ hsm hirr hc1 (d := 2) (by exact_mod_cast hYd))
    (pullbackRationalPluriForms_blowUpToBase_ne_zero sY _ hirr hc1 (by exact_mod_cast hYd) hσ0)
  rw [divisorOfForm_pullbackRationalPluriForms_blowUpToBase _ sY hsm hirr
    (c := 2) (codimension_vanishingIdeal_singleton_eq_two hY hYd hy).symm (by norm_num) (d := 2)
    (by exact_mod_cast hYd) σ hσ0] at hcan
  convert hcan using 2
  norm_num

end

end PointBlowup

end MMP.Threefold.Resolution

/-! ## Normal domains -/

namespace MMP.Threefold

/-- A Noetherian integrally closed domain `A` is, inside its fraction field `K`, the
intersection of its localizations `A_𝔭` at the primes `𝔭` of height one. -/
@[mmp "lem_mmp_threefold_normal_height_one_intersection"]
public theorem iInf_localization_height_eq_one_eq_bot
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    (⨅ 𝔭 : PrimeSpectrum A, ⨅ _ : 𝔭.asIdeal.height = 1,
      Localization.subalgebra.ofField K _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ :=
  (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot K).2.1

/-! ## The normalization of a variety -/

section Normalization

open CategoryTheory AlgebraicGeometry nonZeroDivisors

/-- At a prime `𝔭` with `A_𝔭` integrally closed, an element of the fraction field of `A` that is
integral over `A` acquires a denominator outside `𝔭`. -/
private lemma exists_mul_eq_algebraMap_of_isIntegral {A : Type*} [CommRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] (hp : IsIntegrallyClosed (Localization.AtPrime p))
    (b : FractionRing A) (hb : IsIntegral A b) :
    ∃ u ∉ p, ∃ a : A, algebraMap A (FractionRing A) a = algebraMap A _ u * b := by
  letI : Algebra (Localization.AtPrime p) (FractionRing A) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ p.primeCompl A⁰
        p.primeCompl_le_nonZeroDivisors
  have : IsScalarTower A (Localization.AtPrime p) (FractionRing A) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
      p.primeCompl_le_nonZeroDivisors
  have : IsFractionRing (Localization.AtPrime p) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ _
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Localization.AtPrime p)).mp
    (hb.tower_top (A := Localization.AtPrime p))
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  refine ⟨u, u.2, a, ?_⟩
  rw [← hy, IsScalarTower.algebraMap_apply A (Localization.AtPrime p),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A) u, ← map_mul,
    mul_comm, IsLocalization.mk'_spec]

/-- If `f` multiplies every element of the fraction field of `A` integral over `A` into `A`,
then `A_𝔮` is integrally closed for every prime `𝔮` not containing `f`. -/
private lemma isIntegrallyClosed_atPrime_of_mul {A : Type*} [CommRing A] [IsDomain A]
    (f : A) (hf : ∀ b : FractionRing A, IsIntegral A b →
      ∃ a : A, algebraMap A (FractionRing A) a = algebraMap A _ f * b)
    (q : Ideal A) [q.IsPrime] (hfq : f ∉ q) :
    IsIntegrallyClosed (Localization.AtPrime q) := by
  letI : Algebra (Localization.AtPrime q) (FractionRing A) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ q.primeCompl A⁰
        q.primeCompl_le_nonZeroDivisors
  have : IsScalarTower A (Localization.AtPrime q) (FractionRing A) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
      q.primeCompl_le_nonZeroDivisors
  have : IsFractionRing (Localization.AtPrime q) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl _ _
  refine (isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} hx ↦ ?_
  obtain ⟨s, hs⟩ := hx.exists_multiple_integral_of_isLocalization q.primeCompl
  obtain ⟨a, ha⟩ := hf _ hs
  let t : q.primeCompl := ⟨f * s, q.primeCompl.mul_mem hfq s.2⟩
  refine ⟨IsLocalization.mk' _ a t, ?_⟩
  have ht : algebraMap A (FractionRing A) (t : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (q.primeCompl_le_nonZeroDivisors t.2)
  have key : algebraMap (Localization.AtPrime q) (FractionRing A) (IsLocalization.mk' _ a t) *
      algebraMap A (FractionRing A) (t : A) = algebraMap A (FractionRing A) a := by
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime q) (FractionRing A) (t : A),
      ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
  rw [ha, Submonoid.smul_def, Algebra.smul_def] at key
  apply mul_right_cancel₀ ht
  rw [key]
  simp only [t, map_mul]
  ring

/-- **Openness of the normal locus, algebraically.** For a domain `A` whose integral closure in
its fraction field is a finite `A`-module, and a prime `𝔭` with `A_𝔭` integrally closed, there
is `f ∉ 𝔭` such that `A_𝔮` is integrally closed for every prime `𝔮` not containing `f`. -/
private lemma exists_notMem_forall_isIntegrallyClosed_atPrime {A : Type*} [CommRing A]
    [IsDomain A] [Module.Finite A (integralClosure A (FractionRing A))]
    (p : Ideal A) [p.IsPrime] (hp : IsIntegrallyClosed (Localization.AtPrime p)) :
    ∃ f ∉ p, ∀ (q : Ideal A) [q.IsPrime], f ∉ q →
      IsIntegrallyClosed (Localization.AtPrime q) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A (FractionRing A))
  choose u hu a ha using fun b : integralClosure A (FractionRing A) ↦
    exists_mul_eq_algebraMap_of_isIntegral p hp b b.2
  refine ⟨∏ b ∈ s, u b, ?_, fun q _ hq ↦ isIntegrallyClosed_atPrime_of_mul _ ?_ q hq⟩
  · exact (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).not.mpr
      (by simpa using fun b _ ↦ hu b)
  · intro x hx
    suffices H : ∀ y : integralClosure A (FractionRing A), ∃ a' : A,
        algebraMap A (FractionRing A) a' = algebraMap A _ (∏ b ∈ s, u b) * y from H ⟨x, hx⟩
    intro y
    have hmem : y ∈ Submodule.span A (s : Set _) := by rw [hs]; trivial
    induction hmem using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc⟩ : u y ∣ ∏ b ∈ s, u b := Finset.dvd_prod_of_mem _ hy
      refine ⟨c * a y, ?_⟩
      rw [hc, map_mul, map_mul, ha, mul_comm (algebraMap A _ (u y)) (algebraMap A _ c),
        mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a₁, h₁⟩ := hy
      obtain ⟨a₂, h₂⟩ := hz
      exact ⟨a₁ + a₂, by simp [map_add, h₁, h₂, mul_add]⟩
    | smul r y _ hy =>
      obtain ⟨a₁, h₁⟩ := hy
      refine ⟨r * a₁, ?_⟩
      rw [SetLike.val_smul, Algebra.smul_def, map_mul, h₁]
      ring

/-- The local ring of `X` at a point of an affine open `V` is integrally closed exactly when the
localization of `Γ(X, V)` at the corresponding prime is. -/
private lemma isIntegrallyClosed_stalk_iff {X : Scheme.{u}} (V : X.affineOpens) (y : X)
    (hy : y ∈ V.1) :
    IsIntegrallyClosed (X.presheaf.stalk y) ↔
      IsIntegrallyClosed (Localization.AtPrime (V.2.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  letI := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  haveI := V.2.isLocalization_stalk ⟨y, hy⟩
  let e := IsLocalization.algEquiv (V.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk y) (Localization.AtPrime (V.2.primeIdealOf ⟨y, hy⟩).asIdeal)
  exact ⟨fun h ↦ h.of_equiv e.toRingEquiv, fun h ↦ h.of_equiv e.symm.toRingEquiv⟩

/-- **The normal locus of an integral Japanese scheme is open.** -/
private lemma isOpen_setOf_isIntegrallyClosed_stalk (X : Scheme.{u}) [IsIntegral X]
    (hJ : IsJapaneseScheme X) : IsOpen {x : X | IsIntegrallyClosed (X.presheaf.stalk x)} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨V, hxV, hV⟩ := hJ x
  haveI : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  haveI : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  haveI : Module.Finite Γ(X, V.1) (integralClosure Γ(X, V.1) (FractionRing Γ(X, V.1))) :=
    hV.finite (FractionRing Γ(X, V.1))
  obtain ⟨f, hfx, hf⟩ := exists_notMem_forall_isIntegrallyClosed_atPrime
    (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal ((isIntegrallyClosed_stalk_iff V x hxV).mp hx)
  refine ⟨X.basicOpen f, fun y hy ↦ ?_, (X.basicOpen f).isOpen,
    (MMP.Intersection.notMem_primeIdealOf_iff_mem_basicOpen V.2 hxV f).mp hfx⟩
  have hyV : y ∈ V.1 := X.basicOpen_le f hy
  exact (isIntegrallyClosed_stalk_iff V y hyV).mpr
    (hf _ ((MMP.Intersection.notMem_primeIdealOf_iff_mem_basicOpen V.2 hyV f).mpr hy))

/-- An open subscheme of an integral scheme all of whose local rings are integrally closed is
normal. -/
private lemma isNormal_of_forall_isIntegrallyClosed {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (hU : ∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsNormal U.toScheme := by
  refine ⟨fun z ↦ ?_, fun z ↦ ?_⟩
  · haveI : Nonempty U := ⟨z⟩
    infer_instance
  · have : IsIntegrallyClosed (X.presheaf.stalk z.1) := hU _ z.2
    exact this.of_equiv (U.stalkIso z).commRingCatIsoToRingEquiv.symm

/-- If `ν : W ⟶ X` has unique lifts of `ν ≫ σ.hom`, `ν ≫ σ.inv` and `ν` through itself, then
`σ : X ≅ X` lifts uniquely to an automorphism of `W` over `ν`. -/
private lemma existsUnique_iso_hom_comp_eq {C : Type*} [Category C] {W X : C} (ν : W ⟶ X)
    (σ : X ≅ X) (h₁ : ∃! g : W ⟶ W, g ≫ ν = ν ≫ σ.hom) (h₂ : ∃! g : W ⟶ W, g ≫ ν = ν ≫ σ.inv)
    (h₀ : ∃! g : W ⟶ W, g ≫ ν = ν) : ∃! τ : W ≅ W, τ.hom ≫ ν = ν ≫ σ.hom := by
  obtain ⟨t₁, ht₁, hu₁⟩ := h₁
  obtain ⟨t₂, ht₂, -⟩ := h₂
  have hid {a b : W ⟶ W} {f g : X ⟶ X} (hfg : f ≫ g = 𝟙 X) (ha : a ≫ ν = ν ≫ f)
      (hb : b ≫ ν = ν ≫ g) : a ≫ b = 𝟙 W :=
    h₀.unique (by rw [Category.assoc, hb, reassoc_of% ha, hfg, Category.comp_id])
      (Category.id_comp _)
  exact ⟨⟨t₁, t₂, hid σ.hom_inv_id ht₁ ht₂, hid σ.inv_hom_id ht₂ ht₁⟩, ht₁,
    fun τ hτ ↦ Iso.ext (hu₁ _ hτ)⟩

/-- **The normalization of a variety.** Let `X` be a variety over a field `k` through
`s : X ⟶ Spec k`, and `ν : X̃ ⟶ X` its normalization (`AlgebraicGeometry.Scheme.normalization`).
Then:
* `X̃` is a normal variety over `k` through `ν ≫ s`, and `ν` is finite, surjective and birational;
* there is an open `U ⊆ X` whose points are exactly those with integrally closed local ring
  (the normal locus), and `ν` restricts to an isomorphism `ν⁻¹(U) ≅ U`;
* every dominant morphism `h : W ⟶ X` from a normal integral scheme factors uniquely as
  `g ≫ ν`;
* every automorphism `σ` of `X` lifts to a unique automorphism `τ` of `X̃` with
  `τ ≫ ν = ν ≫ σ`;
* if `X` is a projective variety over `k`, then so is `X̃`. -/
@[mmp "lem_mmp_threefold_normalization_package"]
public theorem normalization_spec {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsVariety k s] :
    let hX := MMP.finite_irreducibleComponents_of_isIntegral X
    let ν : X.normalizationScheme hX ⟶ X := X.normalization hX
    (IsVariety k (ν ≫ s) ∧ IsNormal (X.normalizationScheme hX) ∧
      IsFinite ν ∧ Surjective ν ∧ MMP.Mori.IsBirationalMorphism ν) ∧
    (∃ U : X.Opens, (U : Set X) = {x | IsIntegrallyClosed (X.presheaf.stalk x)} ∧
      IsIso (ν ∣_ U)) ∧
    (∀ (W : Scheme.{u}) [IsIntegral W] [IsNormal W] (h : W ⟶ X) [IsDominant h],
      ∃! g : W ⟶ X.normalizationScheme hX, g ≫ ν = h) ∧
    (∀ σ : X ≅ X, ∃! τ : X.normalizationScheme hX ≅ X.normalizationScheme hX,
      τ.hom ≫ ν = ν ≫ σ.hom) ∧
    (IsProjectiveVariety k s → IsProjectiveVariety k (ν ≫ s)) := by
  intro hX ν
  have hJ : IsJapaneseScheme X := isJapaneseScheme_of_isNagataScheme X
    (isNagataScheme_of_locallyOfFiniteType_over_field k s)
  have hfin : IsFinite ν := normalization_isFinite X hJ
  have hsurj : Surjective ν := Scheme.surjective_normalization X hX
  have hnorm : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
  have hvar : IsVariety k (ν ≫ s) := { }
  let U : X.Opens := ⟨_, isOpen_setOf_isIntegrallyClosed_stalk X hJ⟩
  have hUiso : IsIso (ν ∣_ U) := Scheme.isIso_normalization_restrict_of_isNormal X hX U
    (isNormal_of_forall_isIntegrallyClosed U fun _ hx ↦ hx)
  have hgen : genericPoint X ∈ U := Field.instIsIntegrallyClosed X.functionField
  have hbir : MMP.Mori.IsBirationalMorphism ν := by
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE ν (ν ⁻¹ᵁ U) U ?_ ⟨_, hgen⟩ le_rfl ?_
    · obtain ⟨z, hz⟩ := hsurj.surj (genericPoint X)
      exact ⟨z, show ν z ∈ U from hz ▸ hgen⟩
    · simpa [Scheme.Hom.resLE] using hUiso
  have hUP : ∀ (W : Scheme.{u}) [IsIntegral W] [IsNormal W] (h : W ⟶ X) [IsDominant h],
      ∃! g : W ⟶ X.normalizationScheme hX, g ≫ ν = h := by
    intro W _ _ h _
    refine Scheme.existsUnique_lift_normalization hX h fun ⟨η, hη⟩ ↦ ?_
    obtain rfl : η = genericPoint W := by rwa [genericPoints_eq_singleton] at hη
    change h (genericPoint W) ∈ genericPoints X
    rw [genericPoint_eq_of_isDominant h, genericPoints_eq_singleton]
    rfl
  refine ⟨⟨hvar, hnorm, hfin, hsurj, hbir⟩, ⟨U, rfl, hUiso⟩, hUP,
    fun σ ↦ existsUnique_iso_hom_comp_eq ν σ (hUP _ _) (hUP _ _) (hUP _ _), fun hp ↦ ?_⟩
  obtain ⟨L, _, hL⟩ := exists_isAmple_of_isProjectiveMorphism s
    (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    hp.isProjective
  exact (isProjectiveVariety_iff k (ν ≫ s)).mpr
    ⟨hvar, (isProjectiveMorphism_of_isFinite ν L hL).comp hp.isProjective⟩

end Normalization

end MMP.Threefold

/-! ## Twisting a relative `Proj` -/

namespace MMP

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjGlue
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist (twist)

/-- **Twisting by an invertible sheaf does not change `Proj`, over the base.** For a
quasi-coherent graded `𝒪_S`-algebra `𝒜` and an invertible `𝒪_S`-module `ℒ`, there is an
isomorphism `Proj_S(𝒜 ⊗ ℒ) ≅ Proj_S(𝒜)` commuting with the structure morphisms to `S`. -/
@[mmp "lem_mmp_threefold_proj_twist"]
public theorem exists_iso_relativeProjToBase_twist {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)
    (L : S.Modules) [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L] :
    ∃ f : relativeProj (twist 𝒜 L).toGradedAlgebra ≅ relativeProj 𝒜.toGradedAlgebra,
      f.hom ≫ relativeProjToBase 𝒜.toGradedAlgebra =
        relativeProjToBase (twist 𝒜 L).toGradedAlgebra :=
  Stacks.AlgebraicGeometry.RelativeProjTwist.exists_iso_relativeProjToBase_twist 𝒜 L

end MMP

end
