module

public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Resolution.SmoothCentreBlowup
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.ResolutionVanishing
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceComp
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Generic relative SNC data along the singular curve of a local setting

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`): `Y` a normal projective
`ℚ`-factorial terminal complex fourfold, `T ⊆ Sing Y` an irreducible curve and `π : Ỹ → Y` a
projective resolution, an isomorphism over `Y_reg`. After shrinking `T` to a dense open, the
geometry of `Y` along `T` becomes a family over a curve: there are an open neighbourhood
`X ⊆ Y` of a dense open of `T`, a nonempty open `B ⊆ 𝔸¹` and a morphism `t : X → B` over `ℂ`
such that `T ∩ X → B` is finite étale, and a projective smooth resolution
`f = π_X ∘ β : Z → X`, with `β` a smooth blow-up sequence of `π⁻¹X`, which is an isomorphism
off `T ∩ X`, for which `E = (f⁻¹T)_red` is an SNC divisor, `Z` and every stratum of `E` are
smooth over `B`, and `E → B` is proper. Moreover every closed slice `X_b` is normal, with
singular locus inside the finite set `T_b`.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_relativeSNC_resolution`: the relative SNC data.

## Implementation notes

* An open of the projective `Y` is quasi-projective, so the neighbourhood `X` is an open
  `X : Y.Opens`; it is a neighbourhood of the dense open `T ∩ X` of `T` exactly when
  `T ∩ X` is nonempty, as `T` is irreducible. The curve `B` is an open of Mathlib's affine line
  `𝔸(Unit; Spec ℂ)`, and `t` is a morphism over `ℂ`.
* `T ∩ X` and `E` carry their reduced structures, the closed subschemes cut out by their
  vanishing ideals (`Scheme.IdealSheafData.vanishingIdeal`).
* `β` is a `MMP.Resolution.ClosedBlowupSequence` of `π⁻¹X` that is smooth over `ℂ`
  (`MMP.Resolution.ClosedBlowupSequence.IsSmooth`: every intermediate scheme and every centre is
  smooth), and `f` is its composite `toBase` followed by the restriction `π ∣_ X`.
* The SNC divisor `E` is given by its components: a finite set `s` of prime divisors of `Z`
  whose supports cover `f⁻¹(T ∩ X)` and whose reduced sum is SNC
  (`MMP.Mori.DivisorWithCoeffs.IsSNC`). The stratum of a nonempty `J ⊆ s` is the scheme-theoretic
  intersection of the components in `J`, the closed subscheme of the ideal sheaf `⨆ P ∈ J, I_P`.
* A slice is the scheme-theoretic fibre `X_b = t⁻¹(b)` over a closed point `b`, and its singular
  locus is taken over `κ(b)`; `T_b` is the preimage of `T` in it.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_mmp_conductor_generic_curve_snc_data

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Charts along the curve -/

/-- The closed subset `T ∩ X` of an open `X ⊆ Y`. -/
private abbrev traceCloseds {Y : Scheme.{0}} (T : IrreducibleCloseds Y) (X : Y.Opens) :
    Closeds (X : Scheme.{0}) :=
  ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩

/-- A *curve chart* of `T` on an open `X ⊆ Y`: a morphism `t : X ⟶ B` over `ℂ` to an open
`B ⊆ 𝔸¹` with `T ∩ X ⟶ B` finite étale. -/
private def IsCurveChart {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y)
    (X : Y.Opens) (B : (𝔸(Unit; Spec (.of ℂ))).Opens) (t : (X : Scheme.{0}) ⟶ B) : Prop :=
  t ≫ B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = X.ι ≫ sY ∧
    IsFinite ((Scheme.IdealSheafData.vanishingIdeal (traceCloseds T X)).subschemeι ≫ t) ∧
    Etale ((Scheme.IdealSheafData.vanishingIdeal (traceCloseds T X)).subschemeι ≫ t)

/-- An open of the complex affine line is Noetherian. -/
private theorem isNoetherian_opens_line (B : (𝔸(Unit; Spec (.of ℂ))).Opens) :
    IsNoetherian (B : Scheme.{0}) := by
  haveI : IsLocallyNoetherian (𝔸(Unit; Spec (.of ℂ))) :=
    isLocallyNoetherian_of_isOpenImmersion (AffineSpace.SpecIso Unit (.of ℂ)).hom
  haveI : IsNoetherian (𝔸(Unit; Spec (.of ℂ))) := ⟨⟩
  haveI : CompactSpace (B : Scheme.{0}) := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (B : Set (𝔸(Unit; Spec (.of ℂ)))))
  exact ⟨⟩

/-- The function field of a nonempty open of the complex affine line is perfect. -/
private theorem perfectField_functionField_opens_line (B : (𝔸(Unit; Spec (.of ℂ))).Opens)
    [h : Nonempty B] [IsIntegral (B : Scheme.{0})] :
    PerfectField (B : Scheme.{0}).functionField := by
  haveI : Nonempty (⊤ : (B : Scheme.{0}).Opens) := ⟨⟨h.some, trivial⟩⟩
  let f : ℂ →+* (B : Scheme.{0}).functionField :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))).appTop ≫
      (B : Scheme.{0}).germToFunctionField ⊤).hom
  haveI : CharZero (B : Scheme.{0}).functionField := charZero_of_injective_ringHom f.injective
  infer_instance

/-- The generic point of `T` has coheight three. -/
private theorem coheight_localSettingGenericPoint
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) : Order.coheight (localSettingGenericPoint T) = 3 := by
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    (localSettingGenericPoint T)
  rw [(isGenericPoint_localSettingGenericPoint T).def, h.topologicalKrullDim_eq,
    h.topologicalKrullDim_curve] at hd
  generalize Order.coheight (localSettingGenericPoint T) = c at hd ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd hd (by decide)
  | coe c =>
    have h2 : (((1 + c : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa using hd
    have : 1 + c = 4 := ENat.coe_inj.mp (WithBot.coe_injective h2)
    exact_mod_cast (by omega : c = 3)

/-- Near the generic point of `T`, the singular locus of `Y` is contained in `T`. -/
private theorem exists_opens_singularLocus_subset
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    ∃ U : Y.Opens, localSettingGenericPoint T ∈ U ∧ (U : Set Y) ∩ singularLocus sY ⊆ T := by
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  haveI : IsProper sY := (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨n, K, hK, -⟩ := h.isKltTerminalPair.1.1.isPair.2
  have hcod := (IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    h.isKltTerminalPair (isQCartier_of_isQFactorial sY h.isQFactorial Θ) hK
    (isQCartier_of_isQFactorial sY h.isQFactorial _)).2
  rw [le_closedsCodimension_iff] at hcod
  have hT3 : codimension T = 3 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint]
    exact coheight_localSettingGenericPoint h
  obtain ⟨S, hS, hSeq⟩ := NoetherianSpace.exists_finset_irreducible (singularLocus sY)
  classical
  let S' := S.filter (fun Z : Closeds Y => localSettingGenericPoint T ∉ (Z : Set Y))
  let C : Closeds Y := ⟨⋃ Z ∈ S', (Z : Set Y), isClosed_biUnion_finset fun Z _ => Z.isClosed⟩
  have hC : (C : Set Y) = ⋃ Z ∈ S', (Z : Set Y) := rfl
  refine ⟨C.compl, ?_, ?_⟩
  · change localSettingGenericPoint T ∉ (C : Set Y)
    rw [hC]
    simp only [S', Set.mem_iUnion, Finset.mem_filter, not_exists, not_and]
    intro Z _; tauto
  · rintro y ⟨hyC, hySing⟩
    change y ∉ (C : Set Y) at hyC
    have hy : y ∈ ((S.sup id : Closeds Y) : Set Y) := by rw [← hSeq]; exact hySing
    rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hy
    simp only [Function.comp_apply, id, Set.mem_iUnion] at hy
    obtain ⟨Z, hZS, hyZ⟩ := hy
    by_cases hη : localSettingGenericPoint T ∈ (Z : Set Y)
    · let W : IrreducibleCloseds Y := ⟨Z, hS ⟨Z, hZS⟩, Z.isClosed⟩
      have hWsub : (W : Set Y) ⊆ singularLocus sY := by
        rw [hSeq]; exact (Finset.le_sup (f := id) hZS : Z ≤ S.sup id)
      have hTW : T ≤ W := by
        change (T : Set Y) ⊆ Z
        rw [← (isGenericPoint_localSettingGenericPoint T).def]
        exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
      have hW3 := hcod W hWsub
      have hTW' : T = W := by
        by_contra hne
        have hlt : T < W := lt_of_le_of_ne hTW hne
        have hfin : Order.coheight W < ⊤ :=
          lt_of_le_of_lt (Order.coheight_anti hTW) (by rw [← codimension_eq_coheight, hT3]; decide)
        have := Order.coheight_strictAnti hlt hfin
        rw [← codimension_eq_coheight, ← codimension_eq_coheight, hT3] at this
        exact absurd (lt_of_le_of_lt hW3 this) (lt_irrefl _)
      rw [hTW']; exact hyZ
    · exact absurd (by rw [hC]; exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hZS, hη⟩) hyZ) hyC

/-- Restricting a closed subscheme along an open immersion `e : X' ⟶ X` lying over an open
immersion `ι : B'' ⟶ B` by a cartesian square: the restricted closed subscheme maps to `B''` by
a base change of `Z ⟶ X ⟶ B` along `ι`. -/
private theorem isPullback_comap_subschemeι_comp {X' X B'' B : Scheme.{0}} (e : X' ⟶ X)
    (t' : X' ⟶ B'') (t : X ⟶ B) (ι : B'' ⟶ B) (sq : IsPullback t' e ι t)
    (I : X.IdealSheafData) (K : X'.IdealSheafData) (hK : K = I.comap e) :
    ∃ q, IsPullback (K.subschemeι ≫ t') q ι (I.subschemeι ≫ t) := by
  subst hK
  have sq1 : IsPullback (I.comap e).subschemeι
      ((I.comapIso e).hom ≫ Limits.pullback.snd e I.subschemeι) e I.subschemeι :=
    (IsPullback.of_hasPullback e I.subschemeι).of_iso' (I.comapIso e) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact ⟨_, sq1.paste_horiz sq⟩

/-- **Noether normalization of a curve.** A one-dimensional finitely generated domain over a
field is finite over a polynomial ring in one variable. -/
private theorem exists_finite_injective_mvPolynomial_unit {k S : Type} [Field k] [CommRing S]
    [IsDomain S] [Algebra k S] [Algebra.FiniteType k S] (hdim : ringKrullDim S = 1) :
    ∃ φ : MvPolynomial Unit k →ₐ[k] S, Function.Injective φ ∧ φ.toRingHom.Finite := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k S
  have hfin' : g.toRingHom.Finite := hfin
  have hs : s = 1 := by
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) S := ⟨RingHom.IsIntegral.of_finite hfin'⟩
    haveI : FaithfulSMul (MvPolynomial (Fin s) k) S :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have h1 := Algebra.IsIntegral.ringKrullDim_eq (MvPolynomial (Fin s) k) S
    rw [hdim, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1
  subst hs
  let e : MvPolynomial Unit k ≃ₐ[k] MvPolynomial (Fin 1) k :=
    MvPolynomial.renameEquiv k (Equiv.ofUnique Unit (Fin 1))
  refine ⟨g.comp e.toAlgHom, hinj.comp e.injective, ?_⟩
  exact hfin'.comp (RingHom.Finite.of_surjective _ e.surjective)

/-- **Generic étaleness.** Let `R ⊆ S` be a finite extension of domains, `R` Noetherian of
characteristic zero. Then `R_r ⟶ S_r` is étale for some `r ≠ 0`. -/
private theorem exists_ne_zero_etale_awayMap {R S : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [CharZero R] :
    ∃ r : R, r ≠ 0 ∧ (Localization.awayMap (algebraMap R S) r).Etale := by
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have hinjL : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (IsFractionRing.injective S (FractionRing S)).comp hinj
  have : FaithfulSMul R (FractionRing S) :=
    (faithfulSMul_iff_algebraMap_injective R _).mpr hinjL
  letI := FractionRing.liftAlgebra R (FractionRing S)
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := inferInstance
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing S) := inferInstance
  haveI : Algebra.FormallyEtale (FractionRing R) (FractionRing S) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale R (FractionRing R) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  haveI : Algebra.FormallyEtale R (FractionRing S) :=
    Algebra.FormallyEtale.comp R (FractionRing R) (FractionRing S)
  have hbot : (⊥ : Ideal S).primeCompl = nonZeroDivisors S := by
    ext x; simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsLocalization (⊥ : Ideal S).primeCompl (FractionRing S) := by
    rw [hbot]; infer_instance
  let e : Localization.AtPrime (⊥ : Ideal S) ≃ₐ[S] FractionRing S :=
    IsLocalization.algEquiv (⊥ : Ideal S).primeCompl _ _
  haveI : Algebra.IsEtaleAt R (⊥ : Ideal S) :=
    Algebra.FormallyEtale.of_equiv (e.symm.restrictScalars R)
  haveI : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal S)
  have hf0 : f ≠ 0 := fun h => hf (by simp [h])
  have hcomap : (Ideal.span {f}).comap (algebraMap R S) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  refine ⟨r, hr0, ?_⟩
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (show algebraMap R S r ∈ Ideal.span {f} from hr)
  have hloc : Algebra.Etale R (Localization.Away (algebraMap R S r)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    refine subset_trans ?_ (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr hfet)
    rw [← ha]
    exact PrimeSpectrum.basicOpen_mul_le_right a f
  letI := (Localization.awayMap (algebraMap R S) r).toAlgebra
  haveI : IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
        IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FormallyEtale (Localization.Away r) (Localization.Away (algebraMap R S r)) :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  haveI : Algebra.FinitePresentation (Localization.Away r)
      (Localization.Away (algebraMap R S r)) :=
    Algebra.FinitePresentation.of_finiteType.mp
      (Algebra.FiniteType.of_restrictScalars_finiteType R _ _)
  exact ⟨inferInstance, inferInstance⟩

/-- A pre-chart `t₀ : V ⟶ 𝔸¹` over `ℂ`, finite on `T ∩ V` and étale on it over an open `B`,
restricts to a curve chart on `V ∩ t₀⁻¹ B`. -/
private theorem isCurveChart_of_restrict {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} (V : Y.Opens) (t₀ : (V : Scheme.{0}) ⟶ 𝔸(Unit; Spec (.of ℂ)))
    (hover : t₀ ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = V.ι ≫ sY)
    (hfin : IsFinite ((Scheme.IdealSheafData.vanishingIdeal (traceCloseds T V)).subschemeι ≫ t₀))
    (B : (𝔸(Unit; Spec (.of ℂ))).Opens)
    (het : Etale
      (((Scheme.IdealSheafData.vanishingIdeal (traceCloseds T V)).subschemeι ≫ t₀) ∣_ B)) :
    ∃ t : (V.ι ''ᵁ (t₀ ⁻¹ᵁ B) : Scheme.{0}) ⟶ B, IsCurveChart sY T (V.ι ''ᵁ (t₀ ⁻¹ᵁ B)) B t := by
  have hle : V.ι ''ᵁ (t₀ ⁻¹ᵁ B) ≤ V := V.ι_image_le _
  let t : (V.ι ''ᵁ (t₀ ⁻¹ᵁ B) : Scheme.{0}) ⟶ B := (V.ι.isoImage (t₀ ⁻¹ᵁ B)).inv ≫ (t₀ ∣_ B)
  have hinv : (V.ι.isoImage (t₀ ⁻¹ᵁ B)).inv ≫ (t₀ ⁻¹ᵁ B).ι = Y.homOfLE hle :=
    Scheme.Opens.isoImage_ι_inv_ι _ _
  have hcomm : t ≫ B.ι = Y.homOfLE hle ≫ t₀ := by
    simp only [t, Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, hinv]
  have sq : IsPullback t (Y.homOfLE hle) B.ι t₀ :=
    (isPullback_morphismRestrict t₀ B).of_iso (V.ι.isoImage _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp [t])
      (by rw [← hinv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]) (by simp) (by simp)
  have hK : Scheme.IdealSheafData.vanishingIdeal (traceCloseds T (V.ι ''ᵁ (t₀ ⁻¹ᵁ B))) =
      (Scheme.IdealSheafData.vanishingIdeal (traceCloseds T V)).comap (Y.homOfLE hle) := by
    symm
    refine (MMP.Resolution.IsReducedFlatBaseChange.of_smooth _).comap_vanishingIdeal _ _ ?_
    ext x
    change (V.ι ''ᵁ (t₀ ⁻¹ᵁ B)).ι x ∈ (T : Set Y) ↔ V.ι (Y.homOfLE hle x) ∈ (T : Set Y)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  obtain ⟨q, sqT⟩ := isPullback_comap_subschemeι_comp _ t t₀ _ sq _ _ hK
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hcomm, Category.assoc, hover, ← Category.assoc, Scheme.homOfLE_ι]
  · exact MorphismProperty.of_isPullback (P := @IsFinite) sqT.flip hfin
  · have hpb2 := isPullback_morphismRestrict
      ((Scheme.IdealSheafData.vanishingIdeal (traceCloseds T V)).subschemeι ≫ t₀) B
    rw [← IsPullback.isoIsPullback_hom_fst _ _ sqT hpb2]
    infer_instance

/-- A morphism property respecting isomorphisms holds for the restriction of `i ≫ g ≫ j`, with
`i`, `j` isomorphisms, exactly when it holds for the restriction of `g`. -/
private theorem morphismProperty_restrict_iso_comp_iff (P : MorphismProperty Scheme.{0})
    [P.RespectsIso] {X' X Z Z' : Scheme.{0}} (i : X' ⟶ X) [IsIso i] (g : X ⟶ Z) (j : Z ⟶ Z')
    [IsIso j] (U : Z'.Opens) : P ((i ≫ g ≫ j) ∣_ U) ↔ P (g ∣_ (j ⁻¹ᵁ U)) := by
  rw [morphismRestrict_comp, morphismRestrict_comp]
  exact (P.cancel_left_of_respectsIso (i ∣_ (g ≫ j) ⁻¹ᵁ U) _).trans
    (P.cancel_right_of_respectsIso _ (j ∣_ U))

/-- `Spec R ⟵ Spec S` is étale over `D(r)` exactly when `R_r ⟶ S_r` is étale. -/
private theorem etale_restrict_basicOpen_iff {R S : CommRingCat.{0}} (φ : R ⟶ S) (r : R) :
    Etale (Spec.map φ ∣_ (PrimeSpectrum.basicOpen r)) ↔
      (Localization.awayMap φ.hom r).Etale := by
  rw [MorphismProperty.arrow_mk_iso_iff (P := @Etale) (SpecMapRestrictBasicOpenIso φ r),
    HasRingHomProperty.Spec_iff (P := @Etale)]
  rfl

/-- The trace of the generic point of `T` on an open `V` has closure of dimension one. -/
private theorem topologicalKrullDim_closure_localSettingGenericPoint_opens
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) (V : Y.Opens) (hηV : localSettingGenericPoint T ∈ V) :
    topologicalKrullDim (closure {(⟨_, hηV⟩ : (V : Scheme.{0}))} : Set (V : Scheme.{0})) =
      1 := by
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  set η := localSettingGenericPoint T
  set ηV : (V : Scheme.{0}) := ⟨η, hηV⟩
  haveI : Nonempty V := ⟨ηV⟩
  have hcoh : Order.coheight η = 3 := coheight_localSettingGenericPoint h
  have hcohV : Order.coheight ηV = 3 := by
    rwa [← coheight_eq_of_isOpenImmersion V.ι]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (V.ι ≫ sY) ηV
  rw [hcohV, Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens ℂ sY V,
    h.topologicalKrullDim_eq] at hd
  generalize topologicalKrullDim (closure {ηV} : Set (V : Scheme.{0})) = c at hd ⊢
  induction c using WithBot.recBotCoe with
  | bot => exact absurd hd (by decide)
  | coe c =>
    induction c using ENat.recTopCoe with
    | top => exact absurd hd (by decide)
    | coe c =>
      have h2 : (((c + 3 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using hd
      have : c + 3 = 4 := ENat.coe_inj.mp (WithBot.coe_injective h2)
      exact_mod_cast (by omega : c = 1)

/-- The morphism to `𝔸¹` given by a global function `a` is a morphism over `ℂ`. -/
private theorem toSpecΓ_comp_specMap_eval₂Hom_over {V : Scheme.{0}} (s : V ⟶ Spec (.of ℂ))
    (a : Γ(V, ⊤)) :
    (V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop).hom fun _ : Unit => a)) ≫
      (AffineSpace.SpecIso Unit (.of ℂ)).inv) ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = s := by
  set ψ := MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop).hom fun _ : Unit => a
  have hC : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ) ≫ CommRingCat.ofHom ψ =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop := by
    ext x
    simp [ψ]
  simp only [Category.assoc, AffineSpace.SpecIso_inv_over]
  have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ)) =
      Spec.map s.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hC).trans (Spec.map_comp _ _))
  calc V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ))
      = V.toSpecΓ ≫ Spec.map s.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv :=
        congrArg (fun k => V.toSpecΓ ≫ k) h1
    _ = s ≫ (Spec (.of ℂ)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (.of ℂ)).inv := by
          rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
    _ = s := by simp

/-- A curve chart of `T` inside a given neighbourhood of its generic point. -/
private theorem exists_isCurveChart
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) (U : Y.Opens) (hU : localSettingGenericPoint T ∈ U) :
    ∃ (X : Y.Opens) (B : (𝔸(Unit; Spec (.of ℂ))).Opens) (t : (X : Scheme.{0}) ⟶ B),
      X ≤ U ∧ localSettingGenericPoint T ∈ X ∧ IsCurveChart sY T X B t := by
  classical
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  set η := localSettingGenericPoint T with hηdef
  obtain ⟨V, hV, hηV, hVU⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ η ∈ V ∧ V ≤ U := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
    exact ⟨V, hV, hηV, hVU⟩
  haveI : IsAffine (V : Scheme.{0}) := hV
  haveI : Nonempty V := ⟨⟨η, hηV⟩⟩
  set I := Scheme.IdealSheafData.vanishingIdeal (traceCloseds T V) with hIdef
  haveI : IsAffine I.subscheme := (IsClosedImmersion.isAffine_surjective_of_isAffine I.subschemeι).1
  have hsurj : Function.Surjective I.subschemeι.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine I.subschemeι).2
  let ηV : (V : Scheme.{0}) := ⟨η, hηV⟩
  have hTV : (traceCloseds T V : Set (V : Scheme.{0})) = closure {ηV} := by
    change V.ι ⁻¹' (T : Set Y) = _
    rw [← (isGenericPoint_localSettingGenericPoint T).def,
      V.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage V.ι.continuous]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hx => Subtype.ext hx, fun hx => by rw [hx]; rfl⟩
  have hrange : Set.range I.subschemeι = closure {ηV} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      hTV]
  obtain ⟨ηW, hηW⟩ : ηV ∈ Set.range I.subschemeι := by rw [hrange]; exact subset_closure rfl
  have hgenW : closure ({ηW} : Set I.subscheme) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    rw [← specializes_iff_mem_closure]
    refine I.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp ?_
    rw [hηW, specializes_iff_mem_closure, ← hrange]
    exact ⟨w, rfl⟩
  haveI : IrreducibleSpace I.subscheme :=
    (irreducibleSpace_def _).mpr
      (by rw [Set.top_eq_univ, ← hgenW]; exact isIrreducible_singleton.closure)
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty I.subscheme := ⟨ηW⟩
  -- the coordinate ring of the curve
  set sW := I.subschemeι ≫ V.ι ≫ sY with hsW
  let S := Γ(I.subscheme, ⊤)
  letI : Algebra ℂ S := ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appTop).hom.toAlgebra
  haveI : Algebra.FiniteType ℂ S := by
    have h1 : RingHom.FiniteType sW.appTop.hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    change RingHom.FiniteType (sW.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom)
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective)
  have hdimV : topologicalKrullDim (closure {ηV} : Set (V : Scheme.{0})) = 1 :=
    topologicalKrullDim_closure_localSettingGenericPoint_opens h V hηV
  have hdim : ringKrullDim S = 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    change topologicalKrullDim (Spec Γ(I.subscheme, ⊤)) = 1
    rw [← IsHomeomorph.topologicalKrullDim_eq _
        (Scheme.homeoOfIso (Scheme.isoSpec I.subscheme)).isHomeomorph,
      IsHomeomorph.topologicalKrullDim_eq _
        I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph, hrange, hdimV]
  -- Noether normalization and generic étaleness
  obtain ⟨φ, hφinj, hφfin⟩ := exists_finite_injective_mvPolynomial_unit (k := ℂ) (S := S) hdim
  letI : Algebra (MvPolynomial Unit ℂ) S := φ.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial Unit ℂ) S := hφfin
  obtain ⟨r, hr0, hret⟩ :=
    exists_ne_zero_etale_awayMap (R := MvPolynomial Unit ℂ) (S := S)
      (show Function.Injective φ from hφinj)
  -- the coordinate on `V`
  obtain ⟨a, ha⟩ := hsurj (φ (MvPolynomial.X ()))
  let fV : ℂ →+* Γ((V : Scheme.{0}), ⊤) := ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (V.ι ≫ sY).appTop).hom
  let ψ : MvPolynomial Unit ℂ →+* Γ((V : Scheme.{0}), ⊤) := MvPolynomial.eval₂Hom fV fun _ => a
  let e := AffineSpace.SpecIso Unit (.of ℂ)
  let t₀ : (V : Scheme.{0}) ⟶ 𝔸(Unit; Spec (.of ℂ)) :=
    (V : Scheme.{0}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv
  have hover : t₀ ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = V.ι ≫ sY :=
    toSpecΓ_comp_specMap_eval₂Hom_over (V.ι ≫ sY) a
  have hψφ : CommRingCat.ofHom ψ ≫ I.subschemeι.appTop = CommRingCat.ofHom φ.toRingHom := by
    ext1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · change I.subschemeι.appTop (ψ (MvPolynomial.C c)) = φ (MvPolynomial.C c)
      rw [MvPolynomial.algHom_C]
      simp only [ψ, fV, MvPolynomial.eval₂Hom_C]
      change _ = ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sW.appTop) c
      simp only [sW, Scheme.Hom.comp_appTop]
      rfl
    · change I.subschemeι.appTop (ψ (MvPolynomial.X i)) = φ (MvPolynomial.X i)
      simp only [ψ, MvPolynomial.eval₂Hom_X']
      rw [ha]
  have hg : I.subschemeι ≫ t₀ =
      I.subscheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv := by
    simp only [t₀]
    rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc]
    congr 1
    rw [← Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map hψφ)
  have hfin : IsFinite (I.subschemeι ≫ t₀) := by
    rw [hg]
    haveI : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite I.subscheme.toSpecΓ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso @IsFinite _ e.inv).mpr
        ((IsFinite.SpecMap_iff _).mpr hφfin))
  let B : (𝔸(Unit; Spec (.of ℂ))).Opens := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hB : e.inv ⁻¹ᵁ B = PrimeSpectrum.basicOpen r := by
    ext x
    change e.hom (e.inv x) ∈ PrimeSpectrum.basicOpen r ↔ x ∈ PrimeSpectrum.basicOpen r
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have het : Etale ((I.subschemeι ≫ t₀) ∣_ B) := by
    rw [hg, morphismProperty_restrict_iso_comp_iff (P := @Etale),
      MorphismProperty.arrow_mk_iso_iff (P := @Etale) (morphismRestrictEq _ hB)]
    exact (etale_restrict_basicOpen_iff (CommRingCat.ofHom φ.toRingHom) r).mpr hret
  obtain ⟨t, ht⟩ := isCurveChart_of_restrict V t₀ hover hfin B het
  refine ⟨V.ι ''ᵁ (t₀ ⁻¹ᵁ B), B, t, (V.ι_image_le _).trans hVU, ⟨ηV, ?_, rfl⟩, ht⟩
  -- the generic point of `T` lies over `D(r)`
  have hηWgen : ηW = genericPoint I.subscheme :=
    (show IsGenericPoint ηW ⊤ from hgenW).eq (genericPoint_spec _)
  have hspec : I.subscheme.toSpecΓ ηW = genericPoint (Spec Γ(I.subscheme, ⊤)) := by
    rw [hηWgen]; exact genericPoint_eq_of_isOpenImmersion _
  have h1 : t₀ ηV = e.inv (Spec.map (CommRingCat.ofHom φ.toRingHom)
      (I.subscheme.toSpecΓ ηW)) := by
    rw [← hηW, ← Scheme.Hom.comp_apply, hg]
    rfl
  have h2 : e.hom (t₀ ηV) = Spec.map (CommRingCat.ofHom φ.toRingHom)
      (I.subscheme.toSpecΓ ηW) := by
    rw [h1, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  change e.hom (t₀ ηV) ∈ PrimeSpectrum.basicOpen r
  rw [h2, hspec, genericPoint_eq_bot_of_affine]
  change r ∉ (⊥ : Ideal S).comap φ.toRingHom
  rwa [Ideal.comap_bot_of_injective φ.toRingHom hφinj]

/-- The image under a chart of the generic point of `T` is the generic point of the base. -/
private theorem IsCurveChart.apply_genericPoint {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {X : Y.Opens} {B : (𝔸(Unit; Spec (.of ℂ))).Opens}
    {t : (X : Scheme.{0}) ⟶ B} (hc : IsCurveChart sY T X B t)
    (hη : localSettingGenericPoint T ∈ X) [IsIntegral (B : Scheme.{0})] :
    t ⟨_, hη⟩ = genericPoint B := by
  set ιT := (Scheme.IdealSheafData.vanishingIdeal (traceCloseds T X)).subschemeι
  haveI : Etale (ιT ≫ t) := hc.2.2
  have hopen : IsOpen (Set.range (ιT ≫ t)) := (ιT ≫ t).isOpenMap.isOpen_range
  have hηT : (⟨localSettingGenericPoint T, hη⟩ : (X : Scheme.{0})) ∈ Set.range ιT := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (isGenericPoint_localSettingGenericPoint T).mem
  obtain ⟨w, hw⟩ := hηT
  have hgen : genericPoint B ∈ Set.range (ιT ≫ t) :=
    ((genericPoint_spec B).mem_open_set_iff hopen).mpr ⟨_, trivial, ⟨w, rfl⟩⟩
  obtain ⟨z, hz⟩ := hgen
  have hz' : ιT z ∈ (traceCloseds T X : Set (X : Scheme.{0})) := by
    have : ιT z ∈ Set.range ιT := ⟨z, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hsp : (⟨localSettingGenericPoint T, hη⟩ : (X : Scheme.{0})) ⤳ ιT z := by
    refine X.ι.isOpenEmbedding.isInducing.specializes_iff.mp ?_
    rw [specializes_iff_mem_closure]
    have := (isGenericPoint_localSettingGenericPoint T).def
    change X.ι (ιT z) ∈ closure {localSettingGenericPoint T}
    rw [this]; exact hz'
  have h1 : t ⟨_, hη⟩ ⤳ genericPoint B := by
    rw [← hz, Scheme.Hom.comp_apply]; exact hsp.map t.continuous
  exact (h1.antisymm ((genericPoint_spec B).specializes trivial)).eq

/-- A curve chart restricts over a nonempty open of its base. -/
private theorem IsCurveChart.exists_restrict {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {X : Y.Opens} {B : (𝔸(Unit; Spec (.of ℂ))).Opens}
    {t : (X : Scheme.{0}) ⟶ B} (hc : IsCurveChart sY T X B t)
    (hη : localSettingGenericPoint T ∈ X) (B' : (B : Scheme.{0}).Opens)
    (hB' : (B' : Set B).Nonempty) :
    ∃ (X' : Y.Opens) (t' : (X' : Scheme.{0}) ⟶ B.ι ''ᵁ B') (hX' : X' ≤ X),
      localSettingGenericPoint T ∈ X' ∧ IsCurveChart sY T X' (B.ι ''ᵁ B') t' ∧
      t' ≫ (B.ι ''ᵁ B').ι = Y.homOfLE hX' ≫ t ≫ B.ι ∧ X.ι ⁻¹ᵁ X' = t ⁻¹ᵁ B' := by
  haveI : Nonempty B := ⟨t ⟨_, hη⟩⟩
  have htη : t ⟨_, hη⟩ ∈ B' := by
    rw [hc.apply_genericPoint hη]
    exact ((genericPoint_spec B).mem_open_set_iff B'.isOpen).mpr (by simpa using hB')
  have hle : X.ι ''ᵁ (t ⁻¹ᵁ B') ≤ X := X.ι_image_le _
  let t' : (X.ι ''ᵁ (t ⁻¹ᵁ B') : Scheme.{0}) ⟶ B.ι ''ᵁ B' :=
    (X.ι.isoImage (t ⁻¹ᵁ B')).inv ≫ (t ∣_ B') ≫ (B.ι.isoImage B').hom
  have hinv : (X.ι.isoImage (t ⁻¹ᵁ B')).inv ≫ (t ⁻¹ᵁ B').ι = Y.homOfLE hle :=
    Scheme.Opens.isoImage_ι_inv_ι _ _
  have hcomm : t' ≫ (B.ι ''ᵁ B').ι = Y.homOfLE hle ≫ t ≫ B.ι := by
    simp only [t', Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι_assoc]
    rw [← Category.assoc, hinv]
  have sq : IsPullback t' (Y.homOfLE hle) ((𝔸(Unit; Spec (.of ℂ))).homOfLE (B.ι_image_le B')) t :=
    (isPullback_morphismRestrict t B').of_iso (X.ι.isoImage _) (B.ι.isoImage B') (Iso.refl _)
      (Iso.refl _) (by simp [t'])
      (by rw [← hinv, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id])
      (by simp [← cancel_mono B.ι]) (by simp)
  have hK : Scheme.IdealSheafData.vanishingIdeal (traceCloseds T (X.ι ''ᵁ (t ⁻¹ᵁ B'))) =
      (Scheme.IdealSheafData.vanishingIdeal (traceCloseds T X)).comap (Y.homOfLE hle) := by
    symm
    refine (MMP.Resolution.IsReducedFlatBaseChange.of_smooth _).comap_vanishingIdeal _ _ ?_
    ext x
    change (X.ι ''ᵁ (t ⁻¹ᵁ B')).ι x ∈ (T : Set Y) ↔ X.ι (Y.homOfLE hle x) ∈ (T : Set Y)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  obtain ⟨q, sqT⟩ := isPullback_comap_subschemeι_comp _ t' t _ sq _ _ hK
  refine ⟨X.ι ''ᵁ (t ⁻¹ᵁ B'), t', hle, ⟨⟨_, hη⟩, htη, rfl⟩, ⟨?_, ?_, ?_⟩, hcomm,
    X.ι.preimage_image_eq _⟩
  · rw [← Category.assoc, hcomm, Category.assoc, Category.assoc, hc.1, ← Category.assoc,
      Scheme.homOfLE_ι]
  · haveI := hc.2.1
    exact MorphismProperty.of_isPullback (P := @IsFinite) sqT.flip inferInstance
  · haveI := hc.2.2
    exact MorphismProperty.of_isPullback (P := @Etale) sqT.flip inferInstance

/-! ### Principalization of the ideal of the curve -/

/-- The marked triple `(π⁻¹X, I_{π⁻¹T}, 1, ∅)` over `ℂ`. -/
private noncomputable abbrev principalizationTriple {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    (π : Yt ⟶ Y) (T : IrreducibleCloseds Y) (X : Y.Opens) : MMP.Resolution.MarkedTriple.{0} where
  X := π ⁻¹ᵁ X
  I := Scheme.IdealSheafData.vanishingIdeal
    ⟨((π ⁻¹ᵁ X).ι ≫ π) ⁻¹' (T : Set Y), T.isClosed.preimage ((π ⁻¹ᵁ X).ι ≫ π).continuous⟩
  E := MMP.Resolution.OrderedDivisor.empty _
  k := ℂ
  sX := (π ⁻¹ᵁ X).ι ≫ π ≫ sY
  m := 1

/-- A smooth blow-up sequence of order `≥ m` is a smooth blow-up sequence. -/
private theorem isSmooth_of_isOrderGeMarkedTripleSeq {k : Type} [Field k] :
    ∀ {X : Scheme.{0}} (B : MMP.Resolution.ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (a : MMP.Resolution.MarkedIdeal X) (E : MMP.Resolution.OrderedDivisor X),
      B.IsOrderGeMarkedTripleSeq s a E → B.IsSmooth s
  | _, .nil _, _, _, _, _ => trivial
  | _, .cons _ B, _, _, _, hB =>
    ⟨hB.1.2.1, hB.2.1, isSmooth_of_isOrderGeMarkedTripleSeq B _ _ _ hB.2.2.2.2.2⟩

/-- A closed subscheme of an irreducible scheme whose components have positive codimension is not
the whole scheme. -/
private theorem support_ne_top_of_hasComponentsOfPositiveCodim {X : Scheme.{0}} [IrreducibleSpace X]
    (Z : X.IdealSheafData)
    (hZ : MMP.Resolution.HasComponentsOfPositiveCodim (Z.support : Set X)) : Z.support ≠ ⊤ := by
  intro htop
  have hu : (Z.support : Set X) = Set.univ := by rw [htop]; rfl
  have hcomp : (Set.univ : Set X) ∈ MMP.Resolution.componentsOf (Z.support : Set X) := by
    rw [hu]
    exact ⟨⟨IrreducibleSpace.isIrreducible_univ X, le_rfl⟩, fun _ hy _ => hy.2⟩
  have h1 := hZ _ hcomp
  have hmax : IsMax (MMP.Resolution.irreducibleClosure hcomp.1.1) := fun b _ => by
    change (b : Set X) ⊆ closure Set.univ
    rw [closure_univ]
    exact Set.subset_univ _
  rw [codimension_eq_coheight, Order.coheight_eq_zero.mpr hmax] at h1
  exact absurd h1 (by decide)

/-- The composite of a smooth blow-up sequence of order `≥ m` of a variety is a composite of
blow-ups of varieties along proper smooth centres. -/
private theorem multiplicativeClosure_smoothBlowup_toBase :
    ∀ {X : Scheme.{0}} (B : MMP.Resolution.ClosedBlowupSequence X) (s : X ⟶ Spec (.of ℂ))
      (a : MMP.Resolution.MarkedIdeal X) (E : MMP.Resolution.OrderedDivisor X),
      B.IsOrderGeMarkedTripleSeq s a E → AlgebraicGeometry.IsVariety ℂ s →
      MorphismProperty.multiplicativeClosure
        (fun (W' W : Scheme.{0}) (g : W' ⟶ W) => ∃ (sW : W ⟶ Spec (.of ℂ))
          (I : W.IdealSheafData), MMP.Mori.IsVariety ℂ sW ∧ MMP.Resolution.IsSmoothBlowup sW I ∧
            I.support ≠ ⊤ ∧ ∃ e : W' ≅ blowUp I, e.hom ≫ blowUpToBase I = g) B.toBase
  | X, .nil _, _, _, _, _, _ => MorphismProperty.multiplicativeClosure.id X
  | X, .cons Z B, s, a, E, hB, hX => by
    haveI : IsIntegral X := hX.toIsIntegral
    have hsupp : Z.support ≠ ⊤ := support_ne_top_of_hasComponentsOfPositiveCodim Z hB.2.2.1
    have hZ : Z ≠ ⊥ := fun h => hsupp (by rw [h, Scheme.IdealSheafData.support_bot])
    have hbl := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      s Z hZ).1
    exact MorphismProperty.multiplicativeClosure.comp_of _ _
      (multiplicativeClosure_smoothBlowup_toBase B _ _ _ hB.2.2.2.2.2 hbl)
      ⟨s, Z, hX, ⟨hB.1.2.1, hB.2.1⟩, hsupp, Iso.refl _, by simp⟩

/-- Vanishing of a higher direct image of the structure sheaf restricts to opens of the base. -/
private theorem isZero_rightDerived_restrict {X Y : Scheme.{0}} (π : X ⟶ Y) (V : Y.Opens) (i : ℕ)
    (h : Limits.IsZero (((Scheme.Modules.pushforward π).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    Limits.IsZero (((Scheme.Modules.pushforward (π ∣_ V)).rightDerived i).obj
      (SheafOfModules.unit (π ⁻¹ᵁ V : Scheme.{0}).ringCatSheaf)) := by
  have e := (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso
    π V i).app (SheafOfModules.unit X.ringCatSheaf)
  have h2 : Limits.IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (((Scheme.Modules.pushforward π).rightDerived i).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    Functor.map_isZero _ h
  exact (h2.of_iso e).of_iso (((Scheme.Modules.pushforward (π ∣_ V)).rightDerived i).mapIso
    (Scheme.Modules.restrictUnitIso (π ⁻¹ᵁ V).ι).symm)

/-- Marked order-one reduction of the ideal of `π⁻¹T` on `π⁻¹X`, for an open `X` meeting `T` whose
singular points lie on `T`: a smooth blow-up sequence giving a projective resolution of `X`, an
isomorphism off `T`, with `R^i f_* 𝒪_Z = 0` for `i > 0` and `(f⁻¹T)_red` an snc divisor. -/
private theorem principalization_spec
    (F : MMP.Resolution.OrderGeBlowupSequenceFunctor.{0}
      (MMP.Resolution.markedTriplesOfDim Set.univ 1))
    (hF : MMP.Resolution.IsOrderReductionFunctorMarked 1 Set.univ F)
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) (X : Y.Opens) (hX : (X : Set Y) ∩ singularLocus sY ⊆ T)
    (hη : localSettingGenericPoint T ∈ X) :
    ∃ ht : principalizationTriple sY π T X ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1,
      (F.toFun _ ht).IsSmooth ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) ∧
      let f : (F.toFun _ ht).target ⟶ (X : Scheme.{0}) := (F.toFun _ ht).toBase ≫ (π ∣_ X)
      IsProjectiveMorphism f ∧ IsSmoothResolution (X.ι ≫ sY) f ∧
      (∀ U : (X : Scheme.{0}).Opens,
        (U : Set (X : Scheme.{0})) = (traceCloseds T X : Set (X : Scheme.{0}))ᶜ → IsIso (f ∣_ U)) ∧
      AlgebraicGeometry.IsVariety ℂ (f ≫ X.ι ≫ sY) ∧
      (∀ i > 0, Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
        (SheafOfModules.unit (F.toFun _ ht).target.ringCatSheaf))) ∧
      ∃ s : Finset (MMP.Mori.PrimeDivisor (F.toFun _ ht).target),
        (⋃ P ∈ s, (P.support : Set (F.toFun _ ht).target)) =
          f ⁻¹' (traceCloseds T X : Set (X : Scheme.{0})) ∧
        DivisorWithCoeffs.IsSNC (f ≫ X.ι ≫ sY) (∑ P ∈ s, Finsupp.single P (1 : ℤ)) := by
  classical
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  obtain ⟨-, hYtv, hYtsm, hπproj, hπbir⟩ := h.isResolution
  haveI : AlgebraicGeometry.IsVariety ℂ (π ≫ sY) := hYtv
  haveI : IsIntegral Yt := hYtv.toIsIntegral
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ hπproj
  -- `π` is an isomorphism over `X ∖ T`
  set U₀ : Y.Opens := X ⊓ smoothLocus sY with hU₀
  haveI : IsIso (π ∣_ smoothLocus sY) := h.isBiregular
  haveI hπU₀ : IsIso (π ∣_ U₀) :=
    MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le (V := smoothLocus sY) π inf_le_right
  have hgenX : genericPoint Y ∈ X :=
    ((genericPoint_spec Y).mem_open_set_iff X.isOpen).mpr ⟨_, trivial, hη⟩
  have hgensm : genericPoint Y ∈ smoothLocus sY := by
    rw [smoothLocus_eq_smoothLocus]
    exact sY.genericPoint_mem_smoothLocus_of_perfectField
  have hU₀ne : (U₀ : Set Y).Nonempty := ⟨genericPoint Y, hgenX, hgensm⟩
  haveI : Nonempty (π ⁻¹ᵁ X : Scheme.{0}) := by
    obtain ⟨y, hy⟩ := MMP.Resolution.nonempty_preimage_of_isIso_restrict π U₀ hU₀ne
    exact ⟨⟨y, hy.1⟩⟩
  haveI : IsLocallyNoetherian Yt := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : CompactSpace Yt := QuasiCompact.compactSpace_of_compactSpace (π ≫ sY)
  haveI : IsNoetherian Yt := ⟨⟩
  haveI hXtv : AlgebraicGeometry.IsVariety ℂ ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ (π ≫ sY) (π ⁻¹ᵁ X)
  haveI : IsIntegral (π ⁻¹ᵁ X : Scheme.{0}) := hXtv.toIsIntegral
  have hXtsm : IsSmoothScheme ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) := by
    haveI : Smooth (π ≫ sY) := (isSmoothScheme_iff _).mp hYtsm
    exact (isSmoothScheme_iff _).mpr inferInstance
  -- the generic point of `Ỹ` lies over the generic point of `Y`, which is not on `T`
  have hπgen : π (genericPoint Yt) = genericPoint Y := by
    obtain ⟨y, hy⟩ : ∃ y : Yt, π y = genericPoint Y := by
      let x : (U₀ : Scheme.{0}) := ⟨genericPoint Y, show genericPoint Y ∈ U₀ from ⟨hgenX, hgensm⟩⟩
      have hx : (π ∣_ U₀) ((inv (π ∣_ U₀)) x) = x := by
        rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
      refine ⟨(π ⁻¹ᵁ U₀).ι ((inv (π ∣_ U₀)) x), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hx]
      rfl
    have h1 : π (genericPoint Yt) ⤳ genericPoint Y := by
      rw [← hy]; exact ((genericPoint_spec Yt).specializes trivial).map π.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes trivial)).eq
  have hgenT : genericPoint Y ∉ (T : Set Y) := by
    intro hmem
    have hTuniv : (T : Set Y) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      have := ((genericPoint_spec Y).specializes (Set.mem_univ y))
      exact T.isClosed.stableUnderSpecialization this hmem
    have := h.topologicalKrullDim_curve
    rw [hTuniv, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq,
      h.topologicalKrullDim_eq] at this
    exact absurd this (by decide)
  set Ct : Closeds (π ⁻¹ᵁ X : Scheme.{0}) :=
    ⟨((π ⁻¹ᵁ X).ι ≫ π) ⁻¹' (T : Set Y), T.isClosed.preimage ((π ⁻¹ᵁ X).ι ≫ π).continuous⟩
    with hCt
  set I := Scheme.IdealSheafData.vanishingIdeal Ct with hI
  have hgenCt : genericPoint (π ⁻¹ᵁ X : Scheme.{0}) ∉ I.support := by
    change genericPoint (π ⁻¹ᵁ X : Scheme.{0}) ∉
      ((Scheme.IdealSheafData.vanishingIdeal Ct).support : Set (π ⁻¹ᵁ X : Scheme.{0}))
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change ((π ⁻¹ᵁ X).ι ≫ π) (genericPoint _) ∉ (T : Set Y)
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hπgen]
    exact hgenT
  haveI : IsEmpty (Fin (principalizationTriple sY π T X).E.s) := by
    change IsEmpty (Fin 0); infer_instance
  have ht : principalizationTriple sY π T X ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1 :=
    ⟨⟨inferInstance, hXtsm, inferInstance, inferInstance,
      TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      MMP.Resolution.isNonzeroAtGenericPoints_of_genericPoint_notMem I hgenCt,
      ⟨fun i => i.elim0, MMP.Resolution.isSNCFamily_of_isEmpty _ hXtsm _⟩⟩, rfl,
      MMP.Resolution.hasDimensionIn_univ_of_locallyOfFiniteType ((π ⁻¹ᵁ X).ι ≫ π ≫ sY)⟩
  refine ⟨ht, ?_⟩
  generalize hβ : F.toFun _ ht = β
  have hB : β.IsOrderGeMarkedTripleSeq ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) ⟨I, 1⟩
      (MMP.Resolution.OrderedDivisor.empty _) := hβ ▸ F.isOrderGeMarkedTripleSeq _ ht
  have hmax : MMP.Resolution.maxOrder (β.markedTransform ⟨I, 1⟩).I < 1 := hβ ▸ hF.1 _ ht
  have hexc : I.comap β.toBase = β.exceptionalIdeal := by
    rw [MMP.Resolution.ClosedBlowupSequence.comap_toBase_eq_markedTransform_mul_exceptionalIdeal
      β _ ⟨I, 1⟩ _ rfl hB, MMP.Resolution.eq_top_of_maxOrder_lt_one hmax,
      ← Scheme.IdealSheafData.one_eq_top, one_mul]
  refine ⟨isSmooth_of_isOrderGeMarkedTripleSeq _ _ _ _ hB, ?_⟩
  -- the resolution `f`
  set f : β.target ⟶ (X : Scheme.{0}) := β.toBase ≫ (π ∣_ X) with hf
  have hfX : f ≫ X.ι = β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π := by
    rw [hf, Category.assoc, morphismRestrict_ι]
  have hsf : f ≫ X.ι ≫ sY = β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY := by
    rw [← Category.assoc, hfX]; simp only [Category.assoc]
  have hmemT : ∀ y : (π ⁻¹ᵁ X : Scheme.{0}), (π ∣_ X) y ∈ (traceCloseds T X : Set _) ↔
      y ∈ (Ct : Set _) := by
    intro y
    change X.ι ((π ∣_ X) y) ∈ (T : Set Y) ↔ π ((π ⁻¹ᵁ X).ι y) ∈ (T : Set Y)
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hcos : (⟨I, 1⟩ : MMP.Resolution.MarkedIdeal _).cosupport ⊆ (Ct : Set _) := by
    intro y hy
    have := MMP.Resolution.MarkedIdeal.cosupport_one_subset_support I hy
    rwa [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  -- `f` is an isomorphism off `T`
  have hiso : ∀ U : (X : Scheme.{0}).Opens,
      (U : Set (X : Scheme.{0})) = (traceCloseds T X : Set (X : Scheme.{0}))ᶜ → IsIso (f ∣_ U) := by
    intro U hU
    have hUsm : X.ι ''ᵁ U ≤ smoothLocus sY := by
      rintro _ ⟨x, hx, rfl⟩
      by_contra hns
      have hxT : X.ι x ∈ (T : Set Y) := hX ⟨x.2, hns⟩
      have hx' : x ∈ (U : Set (X : Scheme.{0})) := hx
      rw [hU] at hx'
      exact hx' hxT
    haveI : IsIso (π ∣_ (X.ι ''ᵁ U)) :=
      MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le π hUsm
    haveI : IsIso ((π ∣_ X) ∣_ U) :=
      ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
        (morphismRestrictRestrict π X U)).2 ‹_›
    haveI : IsIso (β.toBase ∣_ (π ∣_ X) ⁻¹ᵁ U) :=
      MMP.Resolution.ClosedBlowupSequence.isIso_toBase_restrict_of_disjoint_cosupport β _ ⟨I, 1⟩ _
        hB _ (Set.disjoint_left.2 fun y hy hyU => by
          have hyU' : (π ∣_ X) y ∈ (U : Set (X : Scheme.{0})) := hyU
          rw [hU] at hyU'
          exact hyU' ((hmemT y).2 (hcos hy)))
    exact MMP.Resolution.isIso_restrict_comp β.toBase (π ∣_ X) U
  -- the complement of `T` in `X`
  set U₁ : (X : Scheme.{0}).Opens := (traceCloseds T X).compl with hU₁
  have hgenU₁ : (⟨genericPoint Y, hgenX⟩ : (X : Scheme.{0})) ∈ U₁ := hgenT
  have hU₁ne : (U₁ : Set (X : Scheme.{0})).Nonempty := ⟨_, hgenU₁⟩
  haveI hfU₁ : IsIso (f ∣_ U₁) := hiso U₁ rfl
  haveI : Nonempty β.target := by
    obtain ⟨z, -⟩ := MMP.Resolution.nonempty_preimage_of_isIso_restrict f U₁ hU₁ne
    exact ⟨z⟩
  have hZv : AlgebraicGeometry.IsVariety ℂ (β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY) :=
    MMP.Resolution.ClosedBlowupSequence.isVariety_toBase β _ hXtv inferInstance
  have hZv' : AlgebraicGeometry.IsVariety ℂ (f ≫ X.ι ≫ sY) := hsf ▸ hZv
  haveI := hZv'
  haveI : IsIntegral β.target := hZv.toIsIntegral
  haveI : Nonempty (X : Scheme.{0}) := ⟨⟨_, hη⟩⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (X.ι ≫ sY) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ sY X
  have hβproj := MMP.Resolution.ClosedBlowupSequence.isProjective_toBase β
  haveI : IsProper β.toBase := hβproj.isProper
  haveI : IsProper f := by rw [hf]; infer_instance
  have hT3 := MMP.Resolution.ClosedBlowupSequence.isTriple_target_of_isOrderGeMarkedTripleSeq
    β _ _ _ hB
  -- projectivity
  have hproj : IsProjectiveMorphism f := by
    have hYtqp : IsQuasiProjective (π ≫ sY) :=
      Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _
        (hπproj.comp hYproj.isProjective).isHQuasiProjective
    have hXtqp : IsQuasiProjective ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) :=
      IsQuasiProjective.comp _ _ (isQuasiProjective_of_isImmersion _) hYtqp
    have hZqp : IsQuasiProjective (f ≫ X.ι ≫ sY) := by
      rw [hsf]
      exact IsQuasiProjective.comp _ _ (isQuasiProjective_of_isProjective hβproj) hXtqp
    haveI : IsQuasiProjectiveVariety ℂ (f ≫ X.ι ≫ sY) :=
      (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hZv', hZqp⟩
    exact MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
      (f ≫ X.ι ≫ sY) (X.ι ≫ sY) f rfl
  refine ⟨hproj, ⟨inferInstance,
    MMP.Resolution.isBirationalMorphism_of_isIso_restrict f U₁ hU₁ne, hsf ▸ hT3.2.1⟩,
    hiso, hZv', ?_, ?_⟩
  · -- `R^i f_* 𝒪_Z = 0` for `i > 0`
    have hc := MMP.LcBpf.isIso_c_and_isZero_rightDerived_of_multiplicativeClosure_smoothBlowup ℂ
      β.toBase (multiplicativeClosure_smoothBlowup_toBase β _ _ _ hB hXtv)
    haveI := hc.1
    have h₁ := isIso_unitToPushforwardObjUnit_of_isIso_c β.toBase hc.1
    haveI : CompactSpace (π ⁻¹ᵁ X : Scheme.{0}) :=
      QuasiCompact.compactSpace_of_compactSpace ((π ⁻¹ᵁ X).ι ≫ π ≫ sY)
    intro i hi
    have hπ := (h.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived).2 i hi
    exact (isZero_rightDerived_restrict π X i hπ).of_iso
      (Stacks.Curves.StableModel.rightDerivedCompUnitIso β.toBase (π ∣_ X) h₁ hc.2 i)
  · -- the snc divisor `(f⁻¹ T)_red`
    have hsupp : (β.orderedTotalTransform (MMP.Resolution.OrderedDivisor.empty _)).support =
        f ⁻¹' (traceCloseds T X : Set (X : Scheme.{0})) := by
      apply Set.Subset.antisymm
      · intro z hz
        rcases
          MMP.Resolution.ClosedBlowupSequence.support_orderedTotalTransform_subset β _ _ _ hB hz
          with h0 | h1
        · simp [MMP.Resolution.OrderedDivisor.support, MMP.Resolution.OrderedDivisor.empty] at h0
        · show f z ∈ (traceCloseds T X : Set _)
          rw [hf, Scheme.Hom.comp_apply]
          exact (hmemT _).2 (hcos h1)
      · intro z hz
        have hz' : β.toBase z ∈ (Ct : Set _) := by
          have hz2 : f z ∈ (traceCloseds T X : Set _) := hz
          rw [hf, Scheme.Hom.comp_apply] at hz2
          exact (hmemT _).1 hz2
        refine MMP.Resolution.ClosedBlowupSequence.support_exceptionalIdeal_subset β _ _ _ hB ?_
        rw [← hexc, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hI,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hz'
    have hE := hT3.2.2.2.2.2.2
    haveI : IsLocallyNoetherian β.target :=
      LocallyOfFiniteType.isLocallyNoetherian (β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY)
    haveI : CompactSpace β.target :=
      QuasiCompact.compactSpace_of_compactSpace (β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY)
    haveI : IsNoetherian β.target := ⟨⟩
    have hcl : IsClosed (f ⁻¹' (traceCloseds T X : Set (X : Scheme.{0}))) :=
      (traceCloseds T X).isClosed.preimage f.continuous
    have hsncC : MMP.Resolution.IsSNCClosedSubset (β.toBase ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY)
        (f ⁻¹' (traceCloseds T X : Set (X : Scheme.{0}))) := by
      rw [← hsupp]; exact MMP.Resolution.IsSNCFamily.isSNCClosedSubset_iUnion hE.2
    rcases MMP.Resolution.isSNCSubset_of_isSNCClosedSubset _ (S := ⟨_, hcl⟩) hsncC with
      h0 | ⟨s, hs, hsnc⟩
    · refine ⟨∅, ?_, ?_⟩
      · have : (f ⁻¹' (traceCloseds T X : Set (X : Scheme.{0}))) = ∅ := by
          have := congrArg (fun C : Closeds β.target => (C : Set β.target)) h0
          simpa using this
        simpa using this.symm
      · rw [hsf]
        simpa using MMP.Resolution.IsSNCFamily.isSNC hE.2 (0 : DivisorWithCoeffs ℤ β.target)
          (by simp)
    · exact ⟨s, hs, hsf ▸ hsnc⟩

/-- Order reduction commutes with shrinking `X`. -/
private theorem principalization_restrict
    (F : MMP.Resolution.OrderGeBlowupSequenceFunctor.{0}
      (MMP.Resolution.markedTriplesOfDim Set.univ 1))
    (hF : MMP.Resolution.IsOrderReductionFunctorMarked 1 Set.univ F)
    {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    {X' X : Y.Opens} (hle : X' ≤ X)
    (ht : principalizationTriple sY π T X ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1)
    (ht' : principalizationTriple sY π T X' ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1) :
    F.toFun _ ht' = (F.toFun _ ht).pullbackReduced
      (Yt.homOfLE (Scheme.Hom.preimage_mono π hle)) := by
  set h := Yt.homOfLE (Scheme.Hom.preimage_mono π hle)
  haveI : IsOpenImmersion h := by unfold h; infer_instance
  have hcomp : h ≫ (π ⁻¹ᵁ X).ι = (π ⁻¹ᵁ X').ι := Scheme.homOfLE_ι _ _
  have he : (principalizationTriple sY π T X).pullback h = principalizationTriple sY π T X' := by
    have hI : (Scheme.IdealSheafData.vanishingIdeal
        ⟨((π ⁻¹ᵁ X).ι ≫ π) ⁻¹' (T : Set Y), T.isClosed.preimage ((π ⁻¹ᵁ X).ι ≫ π).continuous⟩).comap
          h = Scheme.IdealSheafData.vanishingIdeal
        ⟨((π ⁻¹ᵁ X').ι ≫ π) ⁻¹' (T : Set Y),
          T.isClosed.preimage ((π ⁻¹ᵁ X').ι ≫ π).continuous⟩ := by
      refine (MMP.Resolution.IsReducedFlatBaseChange.of_smooth h).comap_vanishingIdeal _ _ ?_
      ext x
      rw [← hcomp]; rfl
    have hE : (MMP.Resolution.OrderedDivisor.empty (π ⁻¹ᵁ X : Scheme.{0})).comap h =
        MMP.Resolution.OrderedDivisor.empty _ := by
      simp only [MMP.Resolution.OrderedDivisor.comap, MMP.Resolution.OrderedDivisor.empty]
      congr 1
      funext i
      exact i.elim0
    have hsX : h ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY = (π ⁻¹ᵁ X').ι ≫ π ≫ sY := by
      rw [← Category.assoc, hcomp]
    simp only [principalizationTriple, MMP.Resolution.MarkedTriple.pullback,
      MMP.Resolution.FieldBlowupTriple.pullback]
    rw [hI, hE]
    congr 2
  have hY : (principalizationTriple sY π T X).pullback h ∈
      MMP.Resolution.markedTriplesOfDim Set.univ 1 := he ▸ ht'
  have hlft : LocallyOfFiniteType (h ≫ (principalizationTriple sY π T X).sX) := by
    change LocallyOfFiniteType (h ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY)
    rw [← Category.assoc, hcomp]
    exact ht'.1.2.2.1
  have hqc : QuasiCompact (h ≫ (principalizationTriple sY π T X).sX) := by
    change QuasiCompact (h ≫ (π ⁻¹ᵁ X).ι ≫ π ≫ sY)
    rw [← Category.assoc, hcomp]
    exact ht'.1.2.2.2.1
  have key := hF.2.1.2 _ ht _ h inferInstance hlft hqc hY
  have hcongr : ∀ (t₁ t₂ : MMP.Resolution.MarkedTriple.{0}) (e : t₁ = t₂)
      (h₁ : t₁ ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1)
      (h₂ : t₂ ∈ MMP.Resolution.markedTriplesOfDim Set.univ 1),
      HEq (F.toFun t₁ h₁) (F.toFun t₂ h₂) := by
    rintro t₁ _ rfl h₁ h₂; rfl
  refine eq_of_heq ((hcongr _ _ he.symm ht' hY).trans (heq_of_eq (key.trans ?_)))
  exact MMP.Resolution.ClosedBlowupSequence.reduction_pullback _ _

/-! ### Generic smoothness over the curve -/

/-- Let `R` be a domain with perfect fraction field `K` and `A` a finite type `R`-algebra. At a
prime `q` of `A` lying over `0`, if `A_q` is regular then it is formally smooth over `R`. -/
private theorem formallySmooth_localization_atPrime_of_isRegularLocalRing {R A K : Type*}
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Field K]
    [Algebra R K] [IsFractionRing R K] [PerfectField K] (q : Ideal A) [q.IsPrime]
    (hq : q.comap (algebraMap R A) = ⊥) [IsRegularLocalRing (Localization.AtPrime q)] :
    Algebra.FormallySmooth R (Localization.AtPrime q) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := A)
  set M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let AK := TensorProduct R K A
  have hdisj : Disjoint (M : Set A) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrq
    have : r ∈ q.comap (algebraMap R A) := hrq
    rw [hq] at this
    exact nonZeroDivisors.ne_zero hr this
  let p' : Ideal AK := q.map (algebraMap A AK)
  haveI hp' : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M AK q ‹_› hdisj
  have hcomap : p'.comap (algebraMap A AK) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M AK ‹_› hdisj
  haveI : Algebra.IsSeparableExtension K p'.ResidueField :=
    Algebra.isSeparableExtension_of_perfectField K p'.ResidueField
  haveI : IsLocalization.AtPrime (Localization.AtPrime p') q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime p') p'
    have h2 : (p'.comap (algebraMap A AK)).primeCompl = q.primeCompl := by
      ext x; simp [hcomap]
    change IsLocalization _ _ at this
    change IsLocalization _ _
    rwa [h2] at this
  let e : Localization.AtPrime p' ≃ₐ[A] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  haveI : IsRegularLocalRing (Localization.AtPrime p') :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  have hsm : Algebra.IsSmoothAt K p' :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing p' (Localization.AtPrime p')).mpr inferInstance
  have : Algebra.FormallySmooth K (Localization.AtPrime p') := hsm
  have : Algebra.FormallySmooth R K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallySmooth R (Localization.AtPrime p') := Algebra.FormallySmooth.comp R K _
  exact Algebra.FormallySmooth.of_equiv (e.restrictScalars R)

/-- A morphism locally of finite presentation to an integral scheme with perfect function field
is smooth at every point with regular local ring lying over the generic point. -/
private theorem mem_smoothLocus_of_eq_genericPoint {W B : Scheme.{0}} [IsIntegral B]
    [PerfectField B.functionField] (g : W ⟶ B) [LocallyOfFinitePresentation g] {w : W}
    (hw : g w = genericPoint B) (hreg : IsRegularLocalRing (W.presheaf.stalk w)) :
    w ∈ g.smoothLocus := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g w)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage g.continuous)
  have := g.finitePresentation_appLE hU hV hVU
  algebraize [(g.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  haveI : Nonempty U := ⟨⟨g w, hxU⟩⟩
  haveI : IsFractionRing Γ(B, U) B.functionField :=
    functionField_isFractionRing_of_isAffineOpen B U hU
  letI : Algebra Γ(W, V) (W.presheaf.stalk w) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hxV⟩
  haveI := hV.isLocalization_stalk ⟨w, hxV⟩
  let e := IsLocalization.algEquiv (hV.primeIdealOf ⟨w, hxV⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Localization.AtPrime (hV.primeIdealOf ⟨w, hxV⟩).asIdeal)
  haveI : IsRegularLocalRing (Localization.AtPrime (hV.primeIdealOf ⟨w, hxV⟩).asIdeal) :=
    IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  have hq : (hV.primeIdealOf ⟨w, hxV⟩).asIdeal.comap (algebraMap Γ(B, U) Γ(W, V)) = ⊥ := by
    have h1 := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
    have h2 : hU.primeIdealOf ⟨g w, hVU hxV⟩ = hU.primeIdealOf
        ⟨genericPoint B, ((genericPoint_spec B).mem_open_set_iff U.isOpen).mpr
          (by simpa using ‹Nonempty U›)⟩ := by
      congr 1; exact Subtype.ext hw
    rwa [h2, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at h1
  exact formallySmooth_localization_atPrime_of_isRegularLocalRing (K := B.functionField) _ hq

/-- **Generic smoothness.** A quasi-compact morphism locally of finite type from a scheme with
regular local rings to a Noetherian integral scheme with perfect function field is smooth over a
nonempty open of the target. -/
private theorem exists_preimage_le_smoothLocus {W B : Scheme.{0}} [IsIntegral B] [IsNoetherian B]
    [PerfectField B.functionField] (g : W ⟶ B) [LocallyOfFiniteType g] [QuasiCompact g]
    (hreg : ∀ w, IsRegularLocalRing (W.presheaf.stalk w)) :
    ∃ U : B.Opens, (U : Set B).Nonempty ∧ g ⁻¹ᵁ U ≤ g.smoothLocus := by
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsNoetherian W := ⟨⟩
  set C : Set W := (g.smoothLocus : Set W)ᶜ
  have hC : Topology.IsConstructible C :=
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible g.smoothLocus.isOpen).compl
  have hS : Topology.IsConstructible (g '' C) := g.isConstructible_image hC
  have hξ : genericPoint B ∉ g '' C := by
    rintro ⟨w, hwC, hw⟩
    exact hwC (mem_smoothLocus_of_eq_genericPoint g hw (hreg w))
  have hdense : Dense (g '' C)ᶜ := by
    refine Dense.mono (Set.singleton_subset_iff.mpr hξ) ?_
    rw [dense_iff_closure_eq]
    exact (genericPoint_spec B).def
  obtain ⟨U, hUo, hUd, hUS⟩ := hS.compl.exists_isOpen_dense_subset hdense
  refine ⟨⟨U, hUo⟩, hUd.nonempty, fun w hw => ?_⟩
  by_contra hwC
  exact hUS hw ⟨w, hwC, rfl⟩

/-- Smoothness descends along open immersions on both sides: if `h ≫ ι = j ≫ g` with `j` and `ι`
open immersions and `g` smooth at every point of the image of `j`, then `h` is smooth. -/
private theorem smooth_of_comp_eq_of_mem_smoothLocus {Z' Z B' B : Scheme.{0}} (j : Z' ⟶ Z)
    [IsOpenImmersion j] (g : Z ⟶ B) [LocallyOfFinitePresentation g] (h : Z' ⟶ B')
    (ι : B' ⟶ B) [IsOpenImmersion ι] (hcomm : h ≫ ι = j ≫ g)
    (hsm : ∀ z, j z ∈ g.smoothLocus) : Smooth h := by
  have h1 : (j ≫ g).smoothLocus = ⊤ := by
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.mpr fun z _ => hsm z
  haveI : Smooth (j ≫ g) := (Scheme.Hom.smoothLocus_eq_top_iff).mp h1
  have h2 : Smooth (h ≫ ι) := hcomm ▸ inferInstance
  haveI : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
    (@Smooth : MorphismProperty Scheme.{0}) (fun f U hf => by
      haveI := hf; exact (inferInstance : Smooth (f ∣_ U)))).of_postcomp h ι
    (inferInstance : IsOpenImmersion ι) h2

/-- The ideal sheaf of a prime divisor of an open subscheme `j : Z' ⟶ Z` is the restriction of
the ideal sheaf of its closure in `Z`. -/
private theorem idealSheaf_eq_comap_primeDivisorMap {Z' Z : Scheme.{0}} (j : Z' ⟶ Z)
    [IsOpenImmersion j] (P : MMP.Mori.PrimeDivisor Z') :
    P.idealSheaf = (OpenWeilRestriction.primeDivisorMap j P).idealSheaf.comap j := by
  conv_lhs => rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
  conv_rhs => rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf
      (OpenWeilRestriction.primeDivisorMap j P)]
  symm
  refine (MMP.Resolution.IsReducedFlatBaseChange.of_smooth j).comap_vanishingIdeal _ _ ?_
  change P.support = j ⁻¹' (OpenWeilRestriction.primeDivisorMap j P).support
  rw [PrimeDivisor.support_eq_closure, PrimeDivisor.support_eq_closure,
    OpenWeilRestriction.genericPoint_primeDivisorMap,
    j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
    show ({j P.genericPoint} : Set Z) = j '' {P.genericPoint} from Set.image_singleton.symm,
    Set.preimage_image_eq _ j.isOpenEmbedding.injective]

/-- A prime divisor whose support lies in a finite union of prime divisors is one of them. -/
private theorem mem_of_support_subset_biUnion {Z : Scheme.{0}} {P : MMP.Mori.PrimeDivisor Z}
    {s : Finset (MMP.Mori.PrimeDivisor Z)}
    (hP : (P.support : Set Z) ⊆ ⋃ Q ∈ s, (Q.support : Set Z)) : P ∈ s := by
  have hg : P.genericPoint ∈ (P.support : Set Z) := by
    rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨Q, hQs, hQ⟩ := Set.mem_iUnion₂.mp (hP hg)
  have hsp : Q.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, ← PrimeDivisor.support_eq_closure]; exact hQ
  have hle : P.genericPoint ≤ Q.genericPoint := Scheme.le_iff_specializes.mpr hsp
  have heq : P.genericPoint = Q.genericPoint := by
    by_contra hne
    have hlt : P.genericPoint < Q.genericPoint := lt_of_le_not_ge hle fun h =>
      hne ((Scheme.le_iff_specializes.mp h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt
      (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; decide)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
    exact lt_irrefl _ this
  rwa [PrimeDivisor.genericPoint_injective heq]

/-- Smoothness of a closed subscheme descends to its restriction to an open subscheme. -/
private theorem smooth_comap_subschemeι_of_mem_smoothLocus {Z' Z B' B : Scheme.{0}}
    (j : Z' ⟶ Z) [IsOpenImmersion j] (I : Z.IdealSheafData) (g : Z ⟶ B) (h : Z' ⟶ B')
    (ι : B' ⟶ B) [IsOpenImmersion ι] (hcomm : h ≫ ι = j ≫ g)
    [LocallyOfFinitePresentation (I.subschemeι ≫ g)]
    (hsm : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range j →
      z ∈ (I.subschemeι ≫ g).smoothLocus) (K : Z'.IdealSheafData) (hK : K = I.comap j) :
    Smooth (K.subschemeι ≫ h) := by
  subst hK
  let j' : (I.comap j).subscheme ⟶ I.subscheme :=
    (I.comapIso j).hom ≫ Limits.pullback.snd j I.subschemeι
  have hj' : j' ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
    simp only [j', Category.assoc, ← Limits.pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  refine smooth_of_comp_eq_of_mem_smoothLocus j' (I.subschemeι ≫ g) _ ι ?_ fun z => hsm _ ?_
  · rw [Category.assoc, hcomm, ← Category.assoc, ← hj', Category.assoc]
  · refine ⟨(I.comap j).subschemeι z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hj', Scheme.Hom.comp_apply]

/-- The relative SNC data without the slice clause and the properness of `E → B`, together with
the vanishing `R^i f_* 𝒪_Z = 0` the normal-slice lemma consumes. -/
private theorem exists_relativeSNC_resolution_core
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    ∃ (X : Y.Opens) (B : (𝔸(Unit; Spec (.of ℂ))).Opens) (t : (X : Scheme.{0}) ⟶ B),
      ((X : Set Y) ∩ T).Nonempty ∧
      t ≫ B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = X.ι ≫ sY ∧
      let TX : Closeds (X : Scheme.{0}) := ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩
      let ιT := (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι
      IsFinite (ιT ≫ t) ∧ Etale (ιT ≫ t) ∧
      ∃ β : MMP.Resolution.ClosedBlowupSequence (π ⁻¹ᵁ X : Scheme.{0}),
        β.IsSmooth ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) ∧
        let f : β.target ⟶ (X : Scheme.{0}) := β.toBase ≫ (π ∣_ X)
        IsProjectiveMorphism f ∧ IsSmoothResolution (X.ι ≫ sY) f ∧
        (∀ U : (X : Scheme.{0}).Opens,
          (U : Set (X : Scheme.{0})) = (TX : Set (X : Scheme.{0}))ᶜ → IsIso (f ∣_ U)) ∧
        Smooth (f ≫ t) ∧
        AlgebraicGeometry.IsVariety ℂ (f ≫ X.ι ≫ sY) ∧
        (∀ i > 0, Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
          (SheafOfModules.unit β.target.ringCatSheaf))) ∧
        ∃ s : Finset (MMP.Mori.PrimeDivisor β.target),
          (⋃ P ∈ s, (P.support : Set β.target)) = f ⁻¹' (TX : Set (X : Scheme.{0})) ∧
          DivisorWithCoeffs.IsSNC (f ≫ X.ι ≫ sY) (∑ P ∈ s, Finsupp.single P (1 : ℤ)) ∧
          (∀ J ⊆ s, J.Nonempty → Smooth ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f ≫ t)) := by
  classical
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  haveI : IsProper sY := (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  /- Step 1: a curve chart near `η_T` on which `Sing Y ⊆ T`. -/
  obtain ⟨U, hηU, hUsing⟩ := exists_opens_singularLocus_subset h
  obtain ⟨X₀, B₀, t₀, hX₀U, hη₀, hc₀⟩ := exists_isCurveChart h U hηU
  have hsing₀ : (X₀ : Set Y) ∩ singularLocus sY ⊆ T := fun y hy => hUsing ⟨hX₀U hy.1, hy.2⟩
  /- Step 2: principalization of the ideal of `T` on `π⁻¹X₀`. -/
  obtain ⟨F, -, hF⟩ := MMP.Resolution.exists_isOrderReductionFunctorMarked_bmoFamily.{0} 1 le_rfl
  obtain ⟨ht₀, -, hproj₀, hres₀, -, hvar₀, -, s₀, hs₀, hsnc₀⟩ :=
    principalization_spec F hF h X₀ hsing₀ hη₀
  generalize hβ₀ : F.toFun _ ht₀ = β₀ at *
  set f₀ : β₀.target ⟶ (X₀ : Scheme.{0}) := β₀.toBase ≫ (π ∣_ X₀) with hf₀
  haveI : Nonempty B₀ := ⟨t₀ ⟨localSettingGenericPoint T, hη₀⟩⟩
  haveI := isNoetherian_opens_line B₀
  haveI := perfectField_functionField_opens_line B₀
  haveI : IsProper f₀ := isProper_of_isProjectiveMorphism _ hproj₀
  haveI : LocallyOfFiniteType t₀ := by
    have : LocallyOfFiniteType (t₀ ≫ B₀.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) := by
      rw [hc₀.1]; infer_instance
    exact LocallyOfFiniteType.of_comp this
  have hZreg : ∀ z, IsRegularLocalRing (β₀.target.presheaf.stalk z) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk _).mp
      ((MMP.Mori.isSmoothScheme_iff _).mp hres₀.isSmoothScheme)
  /- Step 3: generic smoothness of `Z₀` and of its strata over `B₀`. -/
  obtain ⟨B₁, hB₁, hsm₁⟩ := exists_preimage_le_smoothLocus (f₀ ≫ t₀) hZreg
  have hstrat : ∀ J : Finset (MMP.Mori.PrimeDivisor β₀.target), ∃ BJ : (B₀ : Scheme.{0}).Opens,
      (BJ : Set B₀).Nonempty ∧ (J ⊆ s₀ →
        ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f₀ ≫ t₀) ⁻¹ᵁ BJ ≤
          ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f₀ ≫ t₀).smoothLocus) := by
    intro J
    by_cases hJ : J ⊆ s₀
    · have hJsupp : J ⊆ (∑ P ∈ s₀, Finsupp.single P (1 : ℤ)).support := fun P hP => by
        rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
        simp [Finsupp.single_apply, hJ hP]
      have hsmJ := MMP.Fourfold.smooth_iSup_idealSheaf_of_isSNC (f₀ ≫ X₀.ι ≫ sY) hsnc₀ J hJsupp
      have hregJ :=
        (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk _).mp hsmJ
      obtain ⟨BJ, hBJ, hsmBJ⟩ :=
        exists_preimage_le_smoothLocus ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f₀ ≫ t₀) hregJ
      exact ⟨BJ, hBJ, fun _ => hsmBJ⟩
    · exact ⟨⊤, ⟨t₀ ⟨localSettingGenericPoint T, hη₀⟩, trivial⟩, fun h' => absurd h' hJ⟩
  choose BJ hBJne hBJ using hstrat
  set B' : (B₀ : Scheme.{0}).Opens := B₁ ⊓ s₀.powerset.inf BJ with hB'def
  have hB'J : ∀ J ⊆ s₀, B' ≤ BJ J := fun J hJ =>
    inf_le_right.trans (Finset.inf_le (Finset.mem_powerset.mpr hJ))
  have hgen : ∀ V : (B₀ : Scheme.{0}).Opens, (V : Set B₀).Nonempty → genericPoint B₀ ∈ V :=
    fun V hV => ((genericPoint_spec B₀).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hB' : (B' : Set B₀).Nonempty := by
    refine ⟨genericPoint B₀, ?_⟩
    refine ⟨hgen B₁ hB₁, ?_⟩
    exact Finset.inf_induction (p := fun V : (B₀ : Scheme.{0}).Opens => genericPoint B₀ ∈ V)
      trivial (fun _ ha _ hb => ⟨ha, hb⟩) (fun J _ => hgen _ (hBJne J))
  /- Step 4: restrict the chart and the resolution over `B'`. -/
  obtain ⟨X', t', hX'le, hη', hc', htcomm, hpre⟩ := hc₀.exists_restrict hη₀ B' hB'
  have hsing' : (X' : Set Y) ∩ singularLocus sY ⊆ T := fun y hy => hsing₀ ⟨hX'le hy.1, hy.2⟩
  obtain ⟨k, hk⟩ : ∃ k, Yt.homOfLE (Scheme.Hom.preimage_mono π hX'le) = k := ⟨_, rfl⟩
  obtain ⟨ht', rest⟩ := principalization_spec F hF h X' hsing' hη'
  rw [principalization_restrict F hF hX'le ht₀ ht', hβ₀, hk] at rest
  obtain ⟨hsm', hproj', hres', hiso', hvar', hvan', s', hs', hsnc'⟩ := rest
  haveI : IsOpenImmersion k := by rw [← hk]; infer_instance
  haveI : Flat k := by rw [← hk]; infer_instance
  have hpb := MMP.Resolution.Kollar.isPullback_pullbackReduced_toBase_of_flat β₀ k
  set j := β₀.pullbackReducedHom k with hj
  haveI : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb ‹IsOpenImmersion k›
  set f' := (β₀.pullbackReduced k).toBase ≫ (π ∣_ X') with hf'
  have hkπ : k ≫ (π ∣_ X₀) = (π ∣_ X') ≫ Y.homOfLE hX'le := by
    rw [← cancel_mono X₀.ι]
    simp [← hk, Category.assoc, morphismRestrict_ι]
  have hjf : j ≫ f₀ = f' ≫ Y.homOfLE hX'le := by
    rw [hf₀, hf', ← Category.assoc, ← hpb.w, Category.assoc, hkπ, Category.assoc]
  have hle' : B₀.ι ''ᵁ B' ≤ B₀ := by
    rintro _ ⟨b, -, rfl⟩; exact b.2
  set ι := (𝔸(Unit; Spec (.of ℂ))).homOfLE hle' with hιdef
  have hcommg : (f' ≫ t') ≫ ι = j ≫ (f₀ ≫ t₀) := by
    rw [← cancel_mono B₀.ι]
    simp only [Category.assoc, hιdef, Scheme.homOfLE_ι, htcomm]
    rw [← Category.assoc j f₀, hjf]
    simp only [hf', Category.assoc]
  have hX'mem : ∀ x : (X' : Scheme.{0}), t₀ (Y.homOfLE hX'le x) ∈ B' := by
    intro x
    have : Y.homOfLE hX'le x ∈ X₀.ι ⁻¹ᵁ X' := by
      change X₀.ι (Y.homOfLE hX'le x) ∈ X'
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; exact x.2
    rw [hpre] at this; exact this
  have hinB' : ∀ z, (f₀ ≫ t₀) (j z) ∈ B' := by
    intro z
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, hjf, Category.assoc, Scheme.Hom.comp_apply]
    exact hX'mem _
  have hTX : ∀ x : (X' : Scheme.{0}), Y.homOfLE hX'le x ∈ (traceCloseds T X₀ : Set _) ↔
      x ∈ (traceCloseds T X' : Set _) := by
    intro x
    change X₀.ι (Y.homOfLE hX'le x) ∈ (T : Set Y) ↔ X'.ι x ∈ (T : Set Y)
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  refine ⟨X', B₀.ι ''ᵁ B', t',
    ⟨localSettingGenericPoint T, hη', (isGenericPoint_localSettingGenericPoint T).mem⟩,
    hc'.1, hc'.2.1, hc'.2.2, β₀.pullbackReduced k, hsm', hproj', hres', hiso', ?_, hvar', hvan',
    s', hs', hsnc', ?_⟩
  · exact smooth_of_comp_eq_of_mem_smoothLocus j (f₀ ≫ t₀) (f' ≫ t') ι hcommg
      fun z => hsm₁ (show (f₀ ≫ t₀) (j z) ∈ B₁ from (inf_le_left : B' ≤ B₁) (hinB' z))
  · intro J' hJ's _
    set J := J'.image (OpenWeilRestriction.primeDivisorMap j) with hJdef
    have hJs₀ : J ⊆ s₀ := by
      intro P hP
      obtain ⟨P', hP'J, rfl⟩ := Finset.mem_image.mp hP
      refine mem_of_support_subset_biUnion ?_
      rw [hs₀, PrimeDivisor.support_eq_closure, OpenWeilRestriction.genericPoint_primeDivisorMap]
      refine (IsClosed.closure_subset_iff ((traceCloseds T X₀).isClosed.preimage
        f₀.continuous)).mpr (Set.singleton_subset_iff.mpr ?_)
      have hg' : P'.genericPoint ∈ f' ⁻¹' (traceCloseds T X' : Set _) := by
        rw [← hs']
        refine Set.mem_biUnion (hJ's hP'J) ?_
        rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      change f₀ (j P'.genericPoint) ∈ (traceCloseds T X₀ : Set _)
      rw [← Scheme.Hom.comp_apply, hjf, Scheme.Hom.comp_apply, hTX]
      exact hg'
    have hideal : (⨆ P' ∈ J', P'.idealSheaf) = (⨆ P ∈ J, P.idealSheaf).comap j := by
      rw [hJdef, Finset.iSup_finset_image, (Scheme.IdealSheafData.map_gc j).l_iSup₂]
      exact iSup_congr fun P' => iSup_congr fun _ => idealSheaf_eq_comap_primeDivisorMap j P'
    haveI hLJ : LocallyOfFinitePresentation ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f₀ ≫ t₀) :=
      inferInstance
    refine smooth_comap_subschemeι_of_mem_smoothLocus j (⨆ P ∈ J, P.idealSheaf) (f₀ ≫ t₀)
      (f' ≫ t') ι hcommg ?_ _ hideal
    rintro z ⟨z', hz'⟩
    refine hBJ J hJs₀ ?_
    change ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f₀ ≫ t₀) z ∈ BJ J
    rw [Scheme.Hom.comp_apply, ← hz']
    exact hB'J J hJs₀ (hinB' z')

/-- A submersive presentation of the polynomial ring `ℂ[x]`: one variable, no relations. -/
private noncomputable def submersivePresentationLine :
    Algebra.SubmersivePresentation ℂ (MvPolynomial Unit ℂ) Unit Empty where
  __ := Algebra.Generators.mvPolynomial ℂ Unit
  relation := Empty.elim
  span_range_relation_eq_ker := by
    simp [Algebra.Generators.ker_mvPolynomial, Set.range_eq_empty]
  map := Empty.elim
  map_inj := Function.injective_of_subsingleton _
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Matrix.det_isEmpty]

/-- The complex affine line is smooth of relative dimension one over `ℂ`. -/
private theorem smoothOfRelativeDimension_line :
    SmoothOfRelativeDimension 1 (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
  have h0 : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    change (algebraMap ℂ (MvPolynomial Unit ℂ)).IsStandardSmoothOfRelativeDimension 1
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact submersivePresentationLine.isStandardSmoothOfRelativeDimension
      (by simp [Algebra.Presentation.dimension])
  have he : (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = (AffineSpace.SpecIso Unit (.of ℂ)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ)) := by
    rw [← AffineSpace.SpecIso_inv_over (n := Unit) (CommRingCat.of ℂ), Iso.hom_inv_id_assoc]
  rw [he]
  simpa using smoothOfRelativeDimension_comp (n := 0) (m := 1)
    (AffineSpace.SpecIso Unit (.of ℂ)).hom
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial Unit ℂ)))

/-- The reduced preimage `(f⁻¹ T)_red` of a closed subset `T ⊆ X` is proper over `B` when `f` is
proper and `T_red ⟶ X ⟶ B` is finite. -/
private theorem isProper_vanishingIdeal_preimage_comp {Z X B : Scheme.{0}} (f : Z ⟶ X)
    (t : X ⟶ B) [IsProper f] (TX : Closeds X)
    [IsFinite ((Scheme.IdealSheafData.vanishingIdeal TX).subschemeι ≫ t)] :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal
      ⟨f ⁻¹' (TX : Set X), TX.isClosed.preimage f.continuous⟩).subschemeι ≫ f ≫ t) := by
  set E : Closeds Z := ⟨f ⁻¹' (TX : Set X), TX.isClosed.preimage f.continuous⟩
  have H : Scheme.IdealSheafData.vanishingIdeal TX ≤
      (Scheme.IdealSheafData.vanishingIdeal E).map f := by
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    rw [Closeds.closure_le]
    exact Set.image_preimage_subset _ _
  have hfac := Scheme.IdealSheafData.subschemeMap_subschemeι _ _ f H
  have : IsProper (Scheme.IdealSheafData.subschemeMap _ _ f H) := by
    have : IsProper (Scheme.IdealSheafData.subschemeMap _ _ f H ≫
        (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι) := by
      rw [hfac]; infer_instance
    exact IsProper.of_comp _ ((Scheme.IdealSheafData.vanishingIdeal TX).subschemeι)
  rw [← Category.assoc, ← hfac, Category.assoc]
  infer_instance

/-- The relative SNC data of `exists_relativeSNC_resolution_core`, together with the slice clause
and the properness of `E → B`. -/
private theorem exists_relativeSNC_resolution_of_principalization
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    ∃ (X : Y.Opens) (B : (𝔸(Unit; Spec (.of ℂ))).Opens) (t : (X : Scheme.{0}) ⟶ B),
      ((X : Set Y) ∩ T).Nonempty ∧
      t ≫ B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = X.ι ≫ sY ∧
      let TX : Closeds (X : Scheme.{0}) := ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩
      let ιT := (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι
      IsFinite (ιT ≫ t) ∧ Etale (ιT ≫ t) ∧
      (∀ b : B, IsClosed {b} →
        IsNormal (t.fiber b) ∧ (t.fiberι b ⁻¹' (TX : Set (X : Scheme.{0}))).Finite ∧
        (singularLocus (t.fiberToSpecResidueField b) : Set (t.fiber b)) ⊆
          t.fiberι b ⁻¹' (TX : Set (X : Scheme.{0}))) ∧
      ∃ β : MMP.Resolution.ClosedBlowupSequence (π ⁻¹ᵁ X : Scheme.{0}),
        β.IsSmooth ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) ∧
        let f : β.target ⟶ (X : Scheme.{0}) := β.toBase ≫ (π ∣_ X)
        IsProjectiveMorphism f ∧ IsSmoothResolution (X.ι ≫ sY) f ∧
        (∀ U : (X : Scheme.{0}).Opens,
          (U : Set (X : Scheme.{0})) = (TX : Set (X : Scheme.{0}))ᶜ → IsIso (f ∣_ U)) ∧
        Smooth (f ≫ t) ∧
        ∃ s : Finset (MMP.Mori.PrimeDivisor β.target),
          (⋃ P ∈ s, (P.support : Set β.target)) = f ⁻¹' (TX : Set (X : Scheme.{0})) ∧
          DivisorWithCoeffs.IsSNC (f ≫ X.ι ≫ sY) (∑ P ∈ s, Finsupp.single P (1 : ℤ)) ∧
          (∀ J ⊆ s, J.Nonempty → Smooth ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f ≫ t)) ∧
          IsProper ((Scheme.IdealSheafData.vanishingIdeal
            ⟨f ⁻¹' (TX : Set (X : Scheme.{0})),
              TX.isClosed.preimage f.continuous⟩).subschemeι ≫ f ≫ t) := by
  obtain ⟨X, B, t, hne, hover, hfin, het, β, hβ, hproj, hres, hiso,
    hsm, hZvar, hfi, s, hs1, hs2, hs3⟩ := exists_relativeSNC_resolution_core h
  haveI : IsProper (β.toBase ≫ (π ∣_ X)) := isProper_of_isProjectiveMorphism _ hproj
  refine ⟨X, B, t, hne, hover, hfin, het, ?_, β, hβ, hproj, hres, hiso, hsm, s, hs1, hs2, hs3,
    isProper_vanishingIdeal_preimage_comp _ t _⟩
  intro b hb
  haveI := smoothOfRelativeDimension_line
  haveI : SmoothOfRelativeDimension 1 (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) := by
    simpa using smoothOfRelativeDimension_comp (n := 0) (m := 1) B.ι
      (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))
  haveI : SmoothOfRelativeDimension 1
      ((Scheme.IdealSheafData.vanishingIdeal (⟨X.ι ⁻¹' (T : Set Y),
        T.isClosed.preimage X.ι.continuous⟩ : Closeds (X : Scheme.{0}))).subschemeι ≫
          X.ι ≫ sY) := by
    rw [← hover]
    simpa using smoothOfRelativeDimension_comp (n := 0) (m := 1)
      ((Scheme.IdealSheafData.vanishingIdeal (⟨X.ι ⁻¹' (T : Set Y),
        T.isClosed.preimage X.ι.continuous⟩ : Closeds (X : Scheme.{0}))).subschemeι ≫ t)
      (B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)))
  haveI : Nonempty X := ⟨⟨hne.some, hne.some_mem.1⟩⟩
  have hYproj := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sY :=
    (instIsProperVarietyOfIsProjectiveVariety ℂ sY).toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ (X.ι ≫ sY) :=
    Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι ℂ sY X
  have hdim : topologicalKrullDim (X : Scheme.{0}) = 4 := by
    rw [Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens ℂ sY X,
      h.topologicalKrullDim_eq]
  have hf0 : ∀ U : (X : Scheme.{0}).Opens, IsIso ((β.toBase ≫ (π ∣_ X)).app U) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      ((β.toBase ≫ (π ∣_ X)) ≫ X.ι ≫ sY) (X.ι ≫ sY) hZvar ⟨inferInstance, inferInstance⟩
      (β.toBase ≫ (π ∣_ X)) hres.isBirationalMorphism).1
  set TX : Closeds (X : Scheme.{0}) :=
    ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩ with hTX
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι =
      (TX : Set (X : Scheme.{0})) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have key := isNormal_fiber_of_isZero_rightDerived_pushforward
    (sX := X.ι ≫ sY) (sB := B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ))) hdim
    (β.toBase ≫ (π ∣_ X)) hproj hres.isBirationalMorphism hf0 hfi
    (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι (hrange ▸ hiso) t hover
    s (hrange ▸ hs1) hs2 hs3 b hb
  rw [hrange] at key
  exact ⟨key.1, key.2.2.1, key.2.2.2.2.2.2⟩

end Proof_lem_mmp_conductor_generic_curve_snc_data

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Generic relative SNC data in a local setting.** For a local setting `(Y, Θ, T, π)` there
are an open `X ⊆ Y` meeting `T`, an open `B` of the affine line and a morphism `t : X → B` over
`ℂ` with `T ∩ X → B` finite étale, and a smooth blow-up sequence `β` of `π⁻¹X` such that
`f = β.toBase ≫ (π ∣_ X) : Z → X` is a projective smooth resolution, an isomorphism off
`T ∩ X`, `Z` is smooth over `B`, `E = (f⁻¹T)_red` is an SNC divisor whose strata are smooth over
`B`, and `E → B` is proper. Moreover every closed slice `X_b` is normal and its singular locus
lies in the finite set `T_b`. -/
@[mmp "lem_mmp_conductor_generic_curve_snc_data"]
public theorem IsLocalSetting.exists_relativeSNC_resolution
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    ∃ (X : Y.Opens) (B : (𝔸(Unit; Spec (.of ℂ))).Opens) (t : (X : Scheme.{0}) ⟶ B),
      ((X : Set Y) ∩ T).Nonempty ∧
      t ≫ B.ι ≫ (𝔸(Unit; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = X.ι ≫ sY ∧
      let TX : Closeds (X : Scheme.{0}) := ⟨X.ι ⁻¹' (T : Set Y), T.isClosed.preimage X.ι.continuous⟩
      let ιT := (Scheme.IdealSheafData.vanishingIdeal TX).subschemeι
      IsFinite (ιT ≫ t) ∧ Etale (ιT ≫ t) ∧
      (∀ b : B, IsClosed {b} →
        IsNormal (t.fiber b) ∧ (t.fiberι b ⁻¹' (TX : Set (X : Scheme.{0}))).Finite ∧
        (singularLocus (t.fiberToSpecResidueField b) : Set (t.fiber b)) ⊆
          t.fiberι b ⁻¹' (TX : Set (X : Scheme.{0}))) ∧
      ∃ β : MMP.Resolution.ClosedBlowupSequence (π ⁻¹ᵁ X : Scheme.{0}),
        β.IsSmooth ((π ⁻¹ᵁ X).ι ≫ π ≫ sY) ∧
        let f : β.target ⟶ (X : Scheme.{0}) := β.toBase ≫ (π ∣_ X)
        IsProjectiveMorphism f ∧ IsSmoothResolution (X.ι ≫ sY) f ∧
        (∀ U : (X : Scheme.{0}).Opens,
          (U : Set (X : Scheme.{0})) = (TX : Set (X : Scheme.{0}))ᶜ → IsIso (f ∣_ U)) ∧
        Smooth (f ≫ t) ∧
        ∃ s : Finset (MMP.Mori.PrimeDivisor β.target),
          (⋃ P ∈ s, (P.support : Set β.target)) = f ⁻¹' (TX : Set (X : Scheme.{0})) ∧
          DivisorWithCoeffs.IsSNC (f ≫ X.ι ≫ sY) (∑ P ∈ s, Finsupp.single P (1 : ℤ)) ∧
          (∀ J ⊆ s, J.Nonempty → Smooth ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f ≫ t)) ∧
          IsProper ((Scheme.IdealSheafData.vanishingIdeal
            ⟨f ⁻¹' (TX : Set (X : Scheme.{0})),
              TX.isClosed.preimage f.continuous⟩).subschemeι ≫ f ≫ t) :=
  Proof_lem_mmp_conductor_generic_curve_snc_data.exists_relativeSNC_resolution_of_principalization h

end MMP.Fourfold
