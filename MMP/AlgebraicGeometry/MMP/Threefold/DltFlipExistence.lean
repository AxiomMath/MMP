module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.KltFlipExistence
import MMP.AlgebraicGeometry.MMP.Flip.NegativeAdjointTransfer
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Flips of projective dlt threefolds

Let `(X, B)` be a rational `ℚ`-factorial projective dlt complex threefold, with canonical
divisor `K`, and let `f : X ⟶ W` be the contraction of a `(K + B)`-negative extremal ray `R` of
`NE̅(X)`. If `f` is small, then the `(K + B)`-flip of `f` exists: there is a normal variety `X⁺`
with a proper birational morphism `f⁺ : X⁺ ⟶ W`, small, such that
`K_{X⁺} + B⁺ = (f⁺)⁻¹_* f_* (K + B)` is `ℚ`-Cartier and `f⁺`-ample.

The proof replaces `B` by the klt boundary `B - t⌊B⌋` for small rational `t > 0`, which is still
negative on `R`, takes the klt flip, and transfers it back to `K + B`.

## Main results

* `MMP.Fourfold.IsContractionOfRay.exists_isFlip`: small contractions of negative extremal rays
  of rational `ℚ`-factorial projective dlt complex threefolds have flips.

## Implementation notes

The pair is `MMP.Fourfold.IsFloorPair sX 3 K B`, and the flip is `MMP.Mori.IsFlip`. Its
flipping-contraction part, `-(K + B)` being `f`-ample, is part of the conclusion and is not
assumed: for the contraction of a `(K + B)`-negative extremal ray it follows from the relative
Kleiman criterion. The target `W` is not assumed to be projective.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_thm_fourfold_projective_dlt_flip_3

/-! ### Projective morphisms to projective varieties -/

section Projective

/-- A projective variety carries an ample invertible sheaf. -/
private theorem exists_isAmple {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- A proper morphism between projective varieties is projective. -/
private theorem isProjectiveMorphism_of_isProper {V Z : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) [IsProper p] :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 5 2
  exact h.mp ⟨inferInstance, exists_isAmple hV⟩

/-- A proper morphism to a projective variety with a relatively ample Cartier divisor is
projective. -/
private theorem isProjectiveMorphism_of_isRelativelyAmple {V Z : Scheme.{0}} [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) [IsProper p] {L : Divisor V}
    (hL : L.IsCartier) (hamp : L.IsRelativelyAmple p hL) : IsProjectiveMorphism p := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  rw [Divisor.isRelativelyAmple_iff] at hamp
  have h := (isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 6 2
  exact h.mp ⟨inferInstance, L.divisorialSheaf, inferInstance,
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover p _
        inferInstance).mpr hamp⟩

end Projective

/-! ### Targets of morphisms with `ψ_* 𝒪_X = 𝒪_Z` -/

section Contraction

variable {X Z : Scheme.{0}} (ψ : X ⟶ Z) (hψ : ∀ V : Z.Opens, IsIso (ψ.app V))

include hψ

/-- If every `ψ.app V` is an isomorphism, nonempty opens have nonempty preimages. -/
private theorem nonempty_preimage_of_isIso_app (V : Z.Opens) [Nonempty V] :
    Nonempty (ψ ⁻¹ᵁ V) := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hbot : ψ ⁻¹ᵁ V = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => hne.false ⟨x, hx⟩
  haveI := Scheme.component_nontrivial Z V
  haveI := hψ V
  haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by
    rw [hbot]
    infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
  exact hab ((ConcreteCategory.bijective_of_isIso (ψ.app V)).1 (Subsingleton.elim _ _))

/-- The target of a morphism from an integral scheme with `ψ_* 𝒪_X = 𝒪_Z` is integral. -/
private theorem isIntegral_of_isIso_app [IsIntegral X] : IsIntegral Z where
  nonempty := ⟨ψ (Nonempty.some inferInstance)⟩
  component_integral V _ := by
    haveI := nonempty_preimage_of_isIso_app ψ hψ V
    haveI := hψ V
    exact Function.Injective.isDomain (ψ.app V).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app V)).1

/-- A morphism with `ψ_* 𝒪_X = 𝒪_Z` is dominant. -/
private theorem isDominant_of_isIso_app : IsDominant ψ := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨z, hz⟩ => ?_⟩
  haveI : Nonempty (⟨V, hV⟩ : Z.Opens) := ⟨⟨z, hz⟩⟩
  obtain ⟨⟨x, hx⟩⟩ := nonempty_preimage_of_isIso_app ψ hψ ⟨V, hV⟩
  exact ⟨ψ x, hx, x, rfl⟩

end Contraction

/-! ### Contractions of extremal rays over the base point -/

section Absolute

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure sX C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- On `N₁(X/S)` the curve form is the absolute one composed with the natural map. -/
private theorem relativeCurveForm_eq_comp [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {S : Scheme.{0}} (f : X ⟶ S) (D : QDivisor X) (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- The image of an extremal ray under a linear isomorphism is an extremal ray of the image. -/
private theorem isExtremalRay_image {P Q : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup Q]
    [Module ℝ Q] (f : P ≃ₗ[ℝ] Q) {A R : Set P}
    (h : IsExtremalRay ℝ A R) : IsExtremalRay ℝ (f '' A) (f '' R) := by
  obtain ⟨⟨hRA, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := h
  refine ⟨⟨Set.image_mono hRA, ⟨⟨0, hR0, map_zero f⟩, ?_⟩, ?_, ?_⟩, f v,
    fun h => hv0 (f.injective (by rw [h, map_zero])), ?_⟩
  · rintro _ ⟨r, hr, rfl⟩ c hc
    exact ⟨c • r, hRs r hr c hc, map_smul _ _ _⟩
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    exact ⟨r + r', hRadd r hr r' hr', map_add _ _ _⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨r, hr, hrab⟩
    have : a + b = r := f.injective (by rw [hrab, map_add])
    obtain ⟨haR, hbR⟩ := hRext a ha b hb (this ▸ hr)
    exact ⟨⟨a, haR, rfl⟩, ⟨b, hbR, rfl⟩⟩
  · rw [hRv]
    ext w
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, map_smul _ _ _⟩

/-- The base point `Spec ℂ` is a projective variety over itself. -/
private theorem isProjectiveVariety_id_spec :
    AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
  (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
    ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      MMP.isProjectiveMorphism_of_isClosedImmersion _⟩

/-- An extremal ray of `NE̅(X)` pulls back along `relativeToAbsolute` to an extremal ray of the
relative closed cone of curves over the base point. -/
private theorem isExtremalRay_preimage_relativeToAbsolute [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R) :
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _)
      (relativeToAbsolute sX sX ⁻¹' R) := by
  haveI := isProjectiveVariety_id_spec
  have hbij := relativeToAbsolute_bijective sX
  let e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij
  have h := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of ℂ))) sX
    (Category.comp_id sX)
  rw [hbij.2.range_eq, Set.inter_univ] at h
  have hcone : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← h]
    exact e.symm_image_image _
  change IsExtremalRay ℝ _ (e ⁻¹' R)
  rw [← e.image_symm_eq_preimage, ← hcone]
  exact isExtremalRay_image e.symm hR

end Absolute

/-- Two contractions of the same extremal ray of `NE̅(X)` agree up to an isomorphism of their
targets over `k`. -/
private theorem exists_isIso_comp_eq_of_isContractionOfRay {k : Type} [Field k]
    {X Z Z' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {sZ : Z ⟶ Spec (.of k)} {sZ' : Z' ⟶ Spec (.of k)} {f : X ⟶ Z} {f' : X ⟶ Z'}
    (hf : IsContractionOfRay sX sZ R f) (hf' : IsContractionOfRay sX sZ' R f') :
    ∃ φ : Z ⟶ Z', IsIso φ ∧ f ≫ φ = f' ∧ φ ≫ sZ' = sZ := by
  have factor {W W' : Scheme.{0}} {sW : W ⟶ Spec (.of k)} {sW' : W' ⟶ Spec (.of k)} {g : X ⟶ W}
      {g' : X ⟶ W'} (hg : IsContractionOfRay sX sW R g) (hg' : IsContractionOfRay sX sW' R g') :
      ∃! h : W ⟶ W', g ≫ h = g' :=
    existsUnique_comp_eq_of_isContractionOfRay hX hg'.isProjectiveMorphism hg'.comp_eq hR
      (fun C hC => (hg'.isContractedBy_iff C).mpr hC) hg
  obtain ⟨φ, hφ, -⟩ := factor hf hf'
  obtain ⟨ψ, hψ, -⟩ := factor hf' hf
  have hφi : IsIso φ :=
    ⟨ψ, (factor hf hf).unique (by rw [← Category.assoc, hφ, hψ]) (Category.comp_id f),
      (factor hf' hf').unique (by rw [← Category.assoc, hψ, hφ]) (Category.comp_id f')⟩
  have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
  refine ⟨φ, hφi, hφ, (MMP.existsUnique_comp_eq_of_isIso_c f sX fun _ _ _ =>
    Subsingleton.elim (α := PrimeSpectrum k) _ _).unique ?_ hf.comp_eq⟩
  rw [← Category.assoc, hφ, hf'.comp_eq]

/-- **The dlt contraction theorem over the base point.** A `(K + B)`-negative extremal ray `R` of
a projective `ℚ`-factorial dlt complex pair `(X, B)` has a contraction `ψ : X ⟶ Z` onto a
projective variety. The ray is moved to `N₁(X / Spec ℂ)` along the bijection
`relativeToAbsolute`, where the relative dlt contraction theorem applies. -/
private theorem exists_isContractionOfRay_isProjectiveVariety {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hdlt : MMP.Intersection.IsDltPair sX B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hXn : IsNormalVariety ℂ sX) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (ψ : X ⟶ Z),
      MMP.Mori.IsProjectiveVariety ℂ sZ ∧ IsContractionOfRay sX sZ R ψ := by
  obtain ⟨m, hKm⟩ := hK
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
  haveI := isProjectiveVariety_id_spec
  have hFray := isExtremalRay_preimage_relativeToAbsolute sX hR.2.1
  obtain ⟨Z, ψ, g, hψ⟩ := MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace
    (𝟙 (Spec (.of ℂ))) sX (Category.comp_id sX)
    ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKm B).mp hdlt) hQ hFray.1
    hFray.1.2.2.1 fun z hz hz0 => by
      rw [relativeCurveForm_eq_comp]
      exact hR.2.2 (relativeToAbsolute sX sX z) hz fun h =>
        hz0 ((relativeToAbsolute_bijective sX).1 (by rw [h, map_zero]))
  have happ := hψ.isIso_app
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hψ.isProjectiveMorphism
  have hZv : MMP.Mori.IsVariety ℂ g := (MMP.Mori.isVariety_iff ℂ g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety ℂ g :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ g).mpr ⟨hZv, hψ.isProjectiveMorphism⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  haveI : IsProper (ψ ≫ g) := by
    rw [hψ.comp_eq]
    infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  refine ⟨Z, g, ψ, hZp,
    { isNormalVariety_source := hXn
      isNormalVariety_target := ⟨hZv, MMP.Mori.isNormal_of_isIso_c g ψ hZv
        (by
          rw [hψ.comp_eq]
          exact hXp.toIsVariety)⟩
      comp_eq := hψ.comp_eq
      isProjectiveMorphism := isProjectiveMorphism_of_isProper hXp hZp ψ
      surjective := ψ.surjective
      isIso_app := happ
      isContractedBy_iff := fun C => ?_ }⟩
  rw [hψ.isContractedBy_iff C (isContractedBy_structure sX C)]
  exact Iff.of_eq (congrArg (· ∈ R) (isNaturalRelativeMap_relativeToAbsolute sX sX _))

/-- **The target of the contraction of a negative extremal ray is projective.** Let `(X, B)` be
a projective `ℚ`-factorial dlt complex pair and `f : X ⟶ W` the contraction of a
`(K + B)`-negative extremal ray `R`. Then `W` is projective, being isomorphic over `ℂ` to the
target of the contraction given by `exists_isContractionOfRay_isProjectiveVariety`. -/
private theorem isProjectiveVariety_of_isContractionOfRay {X W : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    {f : X ⟶ W} (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hdlt : MMP.Intersection.IsDltPair sX B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sW R f) : MMP.Mori.IsProjectiveVariety ℂ sW := by
  obtain ⟨Z, sZ, ψ, hZ, hψ⟩ :=
    exists_isContractionOfRay_isProjectiveVariety hXp hQ hK hdlt hR hf.isNormalVariety_source
  obtain ⟨n, i, hi, hic⟩ := hZ.isProjective
  obtain ⟨φ, _, -, hφ⟩ := exists_isIso_comp_eq_of_isContractionOfRay hXp hR.2.1 hf hψ
  exact (AlgebraicGeometry.isProjectiveVariety_iff ℂ sW).mpr
    ⟨hf.isNormalVariety_target.1, n, φ ≫ i, inferInstance, by rw [Category.assoc, hic, hφ]⟩

/-! ### Strict transforms of `ℚ`-divisors -/

/-- Regarding a divisor as a `ℚ`-divisor commutes with moving its prime divisors. -/
private theorem toQDivisor_mapPrimeDivisors {X Y : Scheme}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | single E n =>
    have h1 : ∀ {Z : Scheme} (F : MMP.Mori.PrimeDivisor Z) (m : ℤ),
        Divisor.toQDivisor (Finsupp.single F m) = Finsupp.single F (m : ℚ) := fun F m => by
      simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
        DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, Int.coe_castAddHom]
    rw [h1, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [h1]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem toQDivisor_flipTransform {X Y X' : Scheme} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    Divisor.toQDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toQDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, toQDivisor_mapPrimeDivisors]

/-- The strict transform of a log canonical divisor `K + D`. -/
private theorem flipTransform_add {X Y X' : Scheme} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (K : Divisor X) (D : QDivisor X) :
    flipTransform f fp (Divisor.toQDivisor K + D) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D := by
  rw [map_add, toQDivisor_flipTransform]

/-! ### Flips -/

section Flips

variable {X W X' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
  {sX' : X' ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X'] {K : Divisor X} {D : QDivisor X}
  {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W} {fp : X' ⟶ W}

/-- A projective `(K + D)`-flip in the sense of `MMP.Mori.IsFlip` of the small contraction of an
extremal ray is a `(K + D)`-flip in the sense of `MMP.Fourfold.IsFlipOf`. -/
private theorem isFlipOf_of_isFlip (hf : IsContractionOfRay sX sW R f)
    (hsmall : IsSmallMorphism sX sW f) (h : MMP.Mori.IsFlip sX sW sX' K D f fp)
    (hproj : IsProjectiveMorphism fp) :
    IsFlipOf sX sW sX' (Divisor.toQDivisor K + D) f fp where
  isQCartier := h.isFlippingContraction.isQCartier
  isContraction := hf.toIsContraction
  isSmallMorphism := hsmall
  hasRelativelyAmpleMultiple := h.isFlippingContraction.hasRelativelyAmpleMultiple
  isSmallMorphism_flip :=
    { isNormalVariety_source := h.isNormalVariety
      isNormalVariety_target := hsmall.isNormalVariety_target
      comp_eq := h.comp_eq
      isProper := h.isProper
      isBirationalMorphism := h.isBirationalMorphism
      two_le_codimension := h.two_le_codimension }
  isProjectiveMorphism_flip := hproj
  isQCartier_flip := by
    rw [flipTransform_add]
    exact h.isQCartier
  hasRelativelyAmpleMultiple_flip := by
    rw [flipTransform_add]
    exact h.hasRelativelyAmpleMultiple

/-- A `(K + D)`-flip in the sense of `MMP.Fourfold.IsFlipOf` is a `(K + D)`-flip in the sense of
`MMP.Mori.IsFlip`, for `K` a canonical divisor. -/
private theorem isFlip_of_isFlipOf (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (h : IsFlipOf sX sW sX' (Divisor.toQDivisor K + D) f fp) :
    MMP.Mori.IsFlip sX sW sX' K D f fp where
  isFlippingContraction :=
    { isNormalVariety_source := h.isSmallMorphism.isNormalVariety_source
      isNormalVariety_target := h.isSmallMorphism.isNormalVariety_target
      comp_eq := h.isSmallMorphism.comp_eq
      isCanonicalDivisor := hK
      isQCartier := h.isQCartier
      isProper := h.isSmallMorphism.isProper
      isBirationalMorphism := h.isSmallMorphism.isBirationalMorphism
      two_le_codimension := h.isSmallMorphism.two_le_codimension
      hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
  isNormalVariety := h.isSmallMorphism_flip.isNormalVariety_source
  comp_eq := h.isSmallMorphism_flip.comp_eq
  isProper := h.isSmallMorphism_flip.isProper
  isBirationalMorphism := h.isSmallMorphism_flip.isBirationalMorphism
  isQCartier := by
    rw [← flipTransform_add]
    exact h.isQCartier_flip
  hasRelativelyAmpleMultiple := by
    rw [← flipTransform_add]
    exact h.hasRelativelyAmpleMultiple_flip
  two_le_codimension := h.isSmallMorphism_flip.two_le_codimension

/-- The small contraction of a `(K + D)`-negative extremal ray of a projective variety onto a
projective variety is a `(K + D)`-flipping contraction: `-(K + D)` is relatively ample by the
relative Kleiman criterion. -/
private theorem isFlippingContraction_of_isContractionOfRay
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hWp : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hf : IsContractionOfRay sX sW R f)
    (hsmall : IsSmallMorphism sX sW f)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + D) R) :
    IsFlippingContraction sX sW K D f where
  isNormalVariety_source := hsmall.isNormalVariety_source
  isNormalVariety_target := hsmall.isNormalVariety_target
  comp_eq := hsmall.comp_eq
  isCanonicalDivisor := hK
  isQCartier := hR.1
  isProper := hsmall.isProper
  isBirationalMorphism := hsmall.isBirationalMorphism
  two_le_codimension := hsmall.two_le_codimension
  hasRelativelyAmpleMultiple :=
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sW hf.isNormalVariety_source hXp hWp hK
      hR.1 hR.2.1 (fun v hv hv0 => by
        simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hR.2.2 v hv hv0)
      f hf.comp_eq fun C hC => (hf.isContractedBy_iff C).mp hC

end Flips

private theorem solution : ∀
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    (hXB : IsFloorPair sX 3 K B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sW R f) (hsmall : IsSmallMorphism sX sW f),
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ W), MMP.Mori.IsFlip sX sW sX' K B f fp := by
  intro X _ _ _ _ sX K B W sW R f hXB hR hf hsmall
  obtain ⟨hXp, hdim, hQ, hK, hdlt⟩ := hXB
  have hWp := isProjectiveVariety_of_isContractionOfRay hXp hQ hK hdlt hR hf
  obtain ⟨ε, -, hC, hRC⟩ :=
    IsProjectiveQFactorialDltPair.exists_isKltPair_sub_smul_roundDown ⟨hXp, hQ, hK, hdlt⟩ hR
  obtain ⟨X', _, _, _, sX', fp, hflip⟩ := exists_isFlip_of_isKltPair sX K _ hXp hdim hQ hK hC sW R
    f hRC hf (isFlippingContraction_of_isContractionOfRay hXp hWp hK hf hsmall hRC)
  obtain ⟨-, -, L, hLc, -, hLamp⟩ := hflip.hasRelativelyAmpleMultiple
  haveI := hflip.isProper
  exact ⟨X', _, _, _, sX', fp, isFlip_of_isFlipOf hK
    (IsFlipOf.of_isNegativeExtremalRayOf hXp hQ hC hK hRC hf hR hRC
      (isFlipOf_of_isFlip hf hsmall hflip
        (isProjectiveMorphism_of_isRelativelyAmple hWp fp hLc hLamp)))⟩

end Proof_thm_fourfold_projective_dlt_flip_3

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Flips of projective dlt threefolds.** Let `X` be a normal projective `ℚ`-factorial complex
threefold with canonical divisor `K` and `(X, B)` dlt with `B` a `ℚ`-divisor
(`MMP.Fourfold.IsFloorPair sX 3 K B`), and let `f : X ⟶ W` be the contraction of a
`(K + B)`-negative extremal ray `R`. If `f` is small, then `f` has a `(K + B)`-flip
`f⁺ : X⁺ ⟶ W`. -/
@[mmp "thm_fourfold_projective_dlt_flip_3"]
public theorem IsContractionOfRay.exists_isFlip
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    (hXB : IsFloorPair sX 3 K B)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sW R f) (hsmall : IsSmallMorphism sX sW f) :
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ W), IsFlip sX sW sX' K B f fp :=
  Proof_thm_fourfold_projective_dlt_flip_3.solution hXB hR hf hsmall

end MMP.Fourfold
