module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Threefold.DltFlipExistence
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
import MMP.AlgebraicGeometry.MMP.Threefold.DltProgramTermination
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.MMP.ConeTheorem.LcVerticalNegativeRay
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The projective log minimal model program for threefolds

For every morphism `X ⟶ S` of projective complex varieties and every `ℚ`-factorial dlt pair
`(X, B)` with rational boundary of dimension at most three, every `(K_X + B)`-negative extremal
ray of `NE̅(X/S)` has a contraction over `S` onto a projective variety and, when that contraction
is small, a flip with projective source; and every projective elementary dlt program from
`(X, B)` over `S` has finitely many birational steps. That is, the property
`MMP.Fourfold.ProjectiveLowerLogMMP 3` holds.

The proof translates dlt into the Kollár–Mori form, obtains negative rays from the relative cone
theorem and their contractions from the relative contraction theorem, takes flips from the
existence of dlt flips of projective threefolds, bounds the divisorial steps by the absolute
Picard number, and excludes an infinite tail of flips by termination of threefold flips.

## Main results

* `MMP.Fourfold.projectiveLowerLogMMP_three`: the property `P_3`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §3.7 and §6.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_thm_mmp_threefold_log_mmp

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Morphisms -/

section Morphisms

/-- Two morphisms `Z ⟶ Spec R` agreeing after `f : X ⟶ Z` agree, when `f` induces an isomorphism
`Γ(Z, 𝒪_Z) ≅ Γ(X, 𝒪_X)`: morphisms into an affine scheme are ring maps into global sections. -/
private theorem eq_of_comp_eq_of_isIso_appTop {X Z : Scheme.{0}} {R : CommRingCat.{0}}
    (f : X ⟶ Z) [IsIso f.appTop] {a b : Z ⟶ Spec R} (h : f ≫ a = f ≫ b) : a = b := by
  apply (ΓSpec.adjunction.homEquiv Z (Opposite.op R)).symm.injective
  have h' := congrArg (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm h
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm] at h'
  have : IsIso (Scheme.Γ.rightOp.map f) := by
    change IsIso (f.appTop).op
    infer_instance
  exact (cancel_epi _).mp h'

section IsoApp

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
  haveI : Subsingleton Γ(X, ψ ⁻¹ᵁ V) := by rw [hbot]; infer_instance
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

end IsoApp

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

/-- A curve contracted by `f` is contracted by `f ≫ h`. -/
private theorem isContractedBy_comp {X Y W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {C : ProperCurve sX} {f : X ⟶ Y} (h : Y ⟶ W) (hC : C.IsContractedBy f) :
    C.IsContractedBy (f ≫ h) := fun x hx => by
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- The target of a morphism from a projective variety onto `Z`, with `ψ_* 𝒪_X = 𝒪_Z` and a
projective morphism `g : Z ⟶ S` to a projective variety with `g ∘ ψ = π`, is a projective normal
variety, and `ψ` is a projective surjective morphism. -/
private theorem isProjectiveVariety_of_isIso_app {X Z S : Scheme.{0}} [IsIntegral X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    {π : X ⟶ S} (hπ : π ≫ sS = sX) {ψ : X ⟶ Z} {g : Z ⟶ S}
    (happ : ∀ V : Z.Opens, IsIso (ψ.app V)) (hg : IsProjectiveMorphism g) (hψg : ψ ≫ g = π) :
    MMP.Mori.IsProjectiveVariety ℂ (g ≫ sS) ∧ IsNormalVariety ℂ (g ≫ sS) ∧
      ψ ≫ g ≫ sS = sX ∧ IsProjectiveMorphism ψ ∧ Function.Surjective ψ ∧ IsProper ψ := by
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hg
  haveI : IsProper sS := isProper_of_isProjectiveMorphism _ hS.isProjective
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  have hfsZ : ψ ≫ g ≫ sS = sX := by rw [← Category.assoc, hψg, hπ]
  have hZv : MMP.Mori.IsVariety ℂ (g ≫ sS) := (MMP.Mori.isVariety_iff ℂ _).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety ℂ (g ≫ sS) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hZv, hg.comp hS.isProjective⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsNormal Z := MMP.Mori.isNormal_of_isIso_c (g ≫ sS) ψ hZv
    (by rw [hfsZ]; exact hX.toIsVariety)
  haveI : IsProper (ψ ≫ g) := by
    rw [hψg]
    haveI : IsProper (π ≫ sS) := by rw [hπ]; infer_instance
    exact IsProper.of_comp π sS
  haveI : IsProper ψ := IsProper.of_comp ψ g
  have hsurj : Function.Surjective ψ := by
    intro z
    have h1 : closure (Set.range ψ) = Set.univ := ψ.denseRange.closure_range
    rw [ψ.isClosedMap.isClosed_range.closure_eq] at h1
    exact Set.range_eq_univ.mp h1 z
  exact ⟨hZp, ⟨hZv, inferInstance⟩, hfsZ, isProjectiveMorphism_of_isProper hX hZp ψ, hsurj,
    inferInstance⟩

end Morphisms

/-! ### Rays -/

section Rays

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An extremal ray containing a nonzero `w` is `ℝ_{≥0} w`. -/
private theorem eq_setOf_smul_of_isExtremalRay {N R : Set V} (hR : IsExtremalRay ℝ N R) {w : V}
    (hw : w ∈ R) (hw0 : w ≠ 0) : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w = u} := by
  obtain ⟨-, v, -, rfl⟩ := hR
  obtain ⟨a, ha, rfl⟩ := hw
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; exact hw0 (zero_smul _ _))
  ext u
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / a, div_nonneg hc ha, by rw [smul_smul, div_mul_cancel₀ _ ha'.ne']⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * a, mul_nonneg hc ha, by rw [smul_smul]⟩

/-- Let `φ : W → V` be injective and linear, and `A ⊆ W` a cone with `φ(A) = N ∩ φ(W)`. The
preimage of an extremal ray `R ⊆ φ(W)` of `N` is an extremal ray of `A`. -/
private theorem isExtremalRay_preimage {W : Type*} [AddCommGroup W] [Module ℝ W]
    (φ : W →ₗ[ℝ] V) (hφ : Function.Injective φ) {A : Set W} {N R : Set V}
    (hA : φ '' A = N ∩ Set.range φ) (hR : IsExtremalRay ℝ N R) (hRr : R ⊆ Set.range φ) :
    IsExtremalRay ℝ A (φ ⁻¹' R) := by
  obtain ⟨⟨hRN, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := hR
  have hAN : ∀ a ∈ A, φ a ∈ N := fun a ha =>
    (show φ a ∈ N ∩ Set.range φ from hA ▸ Set.mem_image_of_mem φ ha).1
  have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨v', rfl⟩ := hRr hvR
  refine ⟨⟨fun x hx => ?_, ⟨?_, fun x hx c hc => ?_⟩, fun x hx y hy => ?_,
    fun x hx y hy hxy => ?_⟩, v', fun h => hv0 (by rw [h, map_zero]), ?_⟩
  · obtain ⟨a, ha, hax⟩ : φ x ∈ φ '' A := hA ▸ ⟨hRN hx, x, rfl⟩
    rwa [← hφ hax]
  · show φ 0 ∈ R
    rw [map_zero]; exact hR0
  · show φ (c • x) ∈ R
    rw [map_smul]; exact hRs _ hx c hc
  · show φ (x + y) ∈ R
    rw [map_add]; exact hRadd _ hx _ hy
  · have hxy' : φ x + φ y ∈ R := by rw [← map_add]; exact hxy
    exact hRext _ (hAN x hx) _ (hAN y hy) hxy'
  · ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [hRv]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, hφ (by rw [map_smul, h])⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩

end Rays

/-- Over the base point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is bijective. -/
private theorem relativeToAbsolute_bijective {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Function.Bijective (relativeToAbsolute sX sX) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX sX z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (mem_relativeNumericallyTrivial.mpr ((Submodule.Quotient.mk_eq_zero _).mp hz))
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    have hZ : Z ∈ relativeOneCycles sX sX :=
      (Finsupp.mem_supported ℝ Z).mpr fun C _ => isContractedBy_structure C
    exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
      isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) : Function.Injective (relativeToAbsolute sX π) :=
  (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX π).2 _
    (isNaturalRelativeMap_relativeToAbsolute sX π)

/-- The natural map sends the relative class of a contracted curve to its class. -/
private theorem relativeToAbsolute_relativeClass {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) (C : ProperCurve sX) (hC : C.IsContractedBy π) :
    relativeToAbsolute sX π (C.relativeClass π hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
  isNaturalRelativeMap_relativeToAbsolute sX π ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩

/-! ### Divisors -/

section Divisors

variable {X Y : Scheme.{0}}

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {D : QDivisor X} {m : ℤ} (hm : m ≠ 0) {L : Divisor X}
    (hL : Divisor.toQDivisor L = m • D) :
    QDivisor.toRDivisor D = ((m : ℝ)⁻¹) • Divisor.toRDivisor L := by
  ext E
  have h := congrArg (fun D : QDivisor X => D.coeff E) hL
  simp only [Divisor.coeff_toQDivisor] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  rw [mul_comm]
  exact_mod_cast h.symm

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (f : R →+ S) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X' : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- The strict transform of a log canonical divisor `K + D`. -/
private theorem flipTransform_add {X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (K : Divisor X) (D : QDivisor X) :
    flipTransform f fp (Divisor.toQDivisor K + D) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp D := by
  rw [map_add]
  congr 1
  exact flipTransform_mapCoeffsAddMonoidHom f fp _ K

/-- The strict transform commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem flipTransform_toRDivisor {X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : QDivisor X) :
    flipTransform f fp (QDivisor.toRDivisor D) = QDivisor.toRDivisor (flipTransform f fp D) :=
  flipTransform_mapCoeffsAddMonoidHom f fp _ D

end Divisors

/-! ### Nefness -/

section Nef

variable {X Y : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- A `ℚ`-Cartier `ℚ`-divisor which is `f`-nef is `f`-nef as an `ℝ`-divisor. -/
private theorem isRelativelyNef_toRDivisor {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (h : D.IsRelativelyNef sX f) :
    MMP.Flips.IsRelativelyNef ℂ sX f (QDivisor.toRDivisor D) := by
  set c := D.cartierIndex hD
  have hc : (0 : ℚ) < c := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set M : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hM : M.IsCartier := (D.cartierIndexSMul hD).2
  have hMD := QDivisor.toQDivisor_cartierIndexSMul D hD
  have hDR : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 : ℝ) / c) • Divisor.toRDivisor M := by
    rw [Fin.sum_univ_one, toRDivisor_eq_inv_smul (m := (c : ℤ)) (by exact_mod_cast hc.ne') hMD]
    congr 1
    push_cast
    ring
  refine ⟨1, fun _ => (1 : ℝ) / c, fun _ => M, fun _ => hM, hDR, fun C hC x hx => ?_⟩
  rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX C _ _ (fun _ => hM) hDR hx]
  have h0 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX h hD C hC
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq ℂ sX C.ι C.dim_le D hD M hM
    (by rw [hMD])] at h0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have h1 : (0 : ℝ) ≤ (((M.degreeOn ℂ sX C.ι C.dim_le hM : ℚ) / c : ℚ) : ℝ) := by
    exact_mod_cast h0
  push_cast at h1
  rw [div_mul_eq_mul_div, one_mul]
  exact h1

end Nef

/- ### The relative Picard number of the contraction of a ray -/

/-- **A morphism whose contracted curves span one line has relative Picard number one.** If
`C₀` is contracted by `c`, its class is nonzero, and every curve contracted by `c` has class a
multiple of that of `C₀`, then `ρ(X/Z) = 1`: the numerically `c`-trivial divisors are the kernel
of the nonzero linear form `B ↦ (B · C₀)`. -/
private theorem relativePicardNumber_eq_one_of_forall_isContractedBy {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) (c : X ⟶ Z) (C₀ : ProperCurve sX)
    (hC₀ : C₀.IsContractedBy c) (hw₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ)) :
    MMP.Flips.relativePicardNumber sX c = 1 := by
  set ψ : KCartierDivisor ℝ X →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ)
  have hψ (B) : ψ B = (C₀.cycle ℝ).intersectionNumber B := rfl
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX c = LinearMap.ker ψ := by
    ext B
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker, hψ]
    refine ⟨fun hB => hB C₀ hC₀, fun hB C hC => ?_⟩
    obtain ⟨t, hzt⟩ := hray C hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hzt, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hB, smul_zero]
  have hdeg (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
      NumericalCurveClasses.degree sX L (OneCycle.numericalClass sX (C₀.cycle ℝ)) =
        (C₀.degree k L : ℝ) := by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_apply, ProperCurve.cycle,
      Finsupp.sum_single_index (by simp), one_mul]
  -- `ψ ≠ 0`: the class of `C₀` is detected by an invertible sheaf, i.e. a Cartier divisor
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, ψ B₀ ≠ 0 := by
    have hnt : C₀.cycle ℝ ∉ OneCycle.numericallyTrivial sX := fun hmem =>
      hw₀ ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
    rw [OneCycle.mem_numericallyTrivial] at hnt
    push Not at hnt
    obtain ⟨L', hL', hdeg'⟩ := hnt
    obtain ⟨E', ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L'
    refine ⟨KCartierDivisor.ofCartier ℝ E', ?_⟩
    rw [hψ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      ← NumericalCurveClasses.degree_numericalClass, hdeg]
    rw [← NumericalCurveClasses.degree_numericalClass, hdeg] at hdeg'
    rwa [ProperCurve.degree, ← degreeOn_eq_of_iso k sX C₀.ι C₀.dim_le e']
  have hsurj : Function.Surjective ψ := fun y =>
    ⟨(y / ψ B₀) • B₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hB₀]⟩
  have hrank :=
    ((Submodule.quotEquivOfEq _ _ hker).trans (ψ.quotKerEquivOfSurjective hsurj)).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
  rw [MMP.Flips.relativePicardNumber, hrank, map_one]

/-! ### Models -/

section Model

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

/-- The hypotheses of `P₃` on a model: `π : X ⟶ S` is a morphism of projective complex
varieties, `X` has dimension at most three and is `ℚ`-factorial, `K` is a canonical divisor and
`(X, B)` is dlt. -/
private structure Good (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (π : X ⟶ S)
    (K : Divisor X) (B : QDivisor X) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ sX
  isProjectiveVariety_base : MMP.Mori.IsProjectiveVariety ℂ sS
  comp_eq : π ≫ sS = sX
  dim_le : topologicalKrullDim X ≤ 3
  isQFactorial : IsQFactorial sX
  isCanonicalDivisor : ∃ m : ℕ, K.IsCanonicalDivisor sX m
  isDltPair : MMP.Intersection.IsDltPair sX B

variable {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
  {B : QDivisor X}

/-- The dlt pair of a model in the sense of Kollár–Mori. -/
private theorem Good.exists_isDltPair (h : Good sX sS π K B) :
    ∃ m : ℕ, K.IsCanonicalDivisor sX m ∧ MMP.Mori.IsDltPair sX m K B := by
  obtain ⟨m, hKm⟩ := h.isCanonicalDivisor
  exact ⟨m, hKm, (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKm B).mp h.isDltPair⟩

/-- The adjoint of a model is `ℚ`-Cartier. -/
private theorem Good.isQCartier (h : Good sX sS π K B) :
    (Divisor.toQDivisor K + B).IsQCartier := by
  obtain ⟨m, -, hΔ⟩ := h.exists_isDltPair
  exact hΔ.1.2.2

/-- **A negative extremal ray of `NE̅(X/S)` is spanned by a curve.** By the dlt relative cone
theorem a generator of `R` lies in `NE̅(X/S)_{K+B ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`; the first summand
vanishes on `R`, and some `[Cⱼ] ≠ 0` lies in `R`. -/
private theorem Good.exists_curve (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsNegativeRelativeExtremalRayOf sX π (Divisor.toQDivisor K + B) R) :
    ∃ (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy π),
      C₀.relativeClass π hC₀ ∈ R ∧ C₀.relativeClass π hC₀ ≠ 0 := by
  classical
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := h.isProjectiveVariety_base
  obtain ⟨m, -, hΔ⟩ := h.exists_isDltPair
  obtain ⟨ι, -, C, hC, -, -, hdec⟩ :=
    MMP.Mori.IsDltPair.exists_relativeClosedConeOfCurves_eq_add_hull sS π h.comp_eq hΔ
      h.isQFactorial
  obtain ⟨hq, ⟨⟨hFA, ⟨-, hFs⟩, -, hFext⟩, v, hv0, hFv⟩, hneg⟩ := hR
  set H := PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass π (hC j))
  have hHN : ∀ y ∈ H, y ∈ (relativeClosedConeOfCurves sX π : Set _) := fun y hy => by
    change y ∈ (relativeClosedConeOfCurves sX π : Set _)
    rw [hdec]
    exact ⟨0, ⟨(relativeClosedConeOfCurves sX π).zero_mem, by simp⟩, y, hy, zero_add y⟩
  have hvF : v ∈ R := hFv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hvN : v ∈ (relativeClosedConeOfCurves sX π : Set _) := hFA hvF
  rw [hdec] at hvN
  obtain ⟨a, ⟨haN, ha0⟩, h', hh, hah⟩ := hvN
  replace hah : a + h' = v := hah
  obtain ⟨haF, hhF⟩ := hFext a haN h' (hHN h' hh) (hah ▸ hvF)
  have ha : a = 0 := by
    by_contra ha
    exact absurd ha0 (not_le.mpr (hneg a haF ha))
  have key : ∀ y ∈ H, y ∈ R → y = 0 ∨ ∃ j, (C j).relativeClass π (hC j) ∈ R ∧
      (C j).relativeClass π (hC j) ≠ 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro hj
      by_cases h0 : (C j).relativeClass π (hC j) = 0
      · exact Or.inl h0
      · exact Or.inr ⟨j, hj, h0⟩
    | zero => exact fun _ => Or.inl rfl
    | add x y hx hy ihx ihy =>
      intro hxy
      obtain ⟨hxF, hyF⟩ := hFext x (hHN x hx) y (hHN y hy) hxy
      rcases ihx hxF with h1 | h1
      · rcases ihy hyF with h2 | h2
        · exact Or.inl (by rw [h1, h2, add_zero])
        · exact Or.inr h2
      · exact Or.inr h1
    | smul c x hx ihx =>
      intro hcx
      by_cases hc : c = 0
      · exact Or.inl (by rw [hc, zero_smul])
      · have hxF : x ∈ R := by
          have hc' : (0 : ℝ) < c := lt_of_le_of_ne c.2 fun h => hc (Subtype.ext h.symm)
          have h1 := hFs _ hcx ((c : ℝ)⁻¹) (inv_pos.mpr hc')
          have h2 : ((c : ℝ)⁻¹) • (c • x) = x := by
            rw [show c • x = (c : ℝ) • x from rfl, smul_smul, inv_mul_cancel₀ hc'.ne', one_smul]
          rwa [h2] at h1
        rcases ihx hxF with h1 | h1
        · exact Or.inl (by rw [h1, smul_zero])
        · exact Or.inr h1
  rcases key h' hh hhF with h0 | ⟨j, hjF, hj0⟩
  · exact absurd (by rw [← hah, ha, h0, add_zero]) hv0
  exact ⟨C j, hC j, hjF, hj0⟩

/-- A curve whose class is a multiple of the class of a curve contracted by `π` is contracted by
`π`: the pull-back of an ample invertible sheaf of `S` has degree zero on it. -/
private theorem Good.isContractedBy_of_numericalClass_eq (h : Good sX sS π K B)
    {C₀ C : ProperCurve sX} (hC₀ : C₀.IsContractedBy π) {c : ℝ}
    (hc : OneCycle.numericalClass sX (C.cycle ℝ) =
      c • OneCycle.numericalClass sX (C₀.cycle ℝ)) : C.IsContractedBy π := by
  have hS := h.isProjectiveVariety_base
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sS := hS.toIsVariety.toLocallyOfFiniteType
  obtain ⟨H, _, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hS
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero π h.comp_eq H hHa C ?_
  have h0 := ProperCurve.degree_pullback_eq_zero_of_isContractedBy π h.comp_eq C₀ hC₀ H
  have h1 := congrArg (NumericalCurveClasses.degree sX ((Scheme.Modules.pullback π).obj H)) hc
  rw [map_smul, NumericalCurveClasses.degree_numericalClass,
    NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, OneCycle.degree_cycle,
    h0] at h1
  have h2 : ((C.degree ℂ ((Scheme.Modules.pullback π).obj H) : ℤ) : ℝ) = 0 := by
    rw [h1]; simp
  exact_mod_cast h2

/-- **The ray and its contraction, absolutely.** Let `(ψ, g)` contract a negative extremal ray
`R` of `NE̅(X/S)` over `S`. Then the target of `ψ` is a projective normal variety (over `ℂ` by
`g ≫ sS`), the image `φ(R)` of `R` in `N₁(X)` is a negative extremal ray of `NE̅(X)` contracted by
`ψ`, and `ψ` is a negative extremal contraction for `K + B`. -/
private theorem Good.core (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsNegativeRelativeExtremalRayOf sX π (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} {ψ : X ⟶ Z} {g : Z ⟶ S} (hψ : IsRelativeContractionOfFace π R ψ g) :
    MMP.Mori.IsProjectiveVariety ℂ (g ≫ sS) ∧
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) (relativeToAbsolute sX π '' R) ∧
      IsContractionOfRay sX (g ≫ sS) (relativeToAbsolute sX π '' R) ψ ∧
      MMP.Flips.IsNegativeExtremalContraction ℂ sX (g ≫ sS)
        (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) ψ ∧
      ∃ C₀ : ProperCurve sX, C₀.IsContractedBy ψ ∧
        OneCycle.numericalClass sX (C₀.cycle ℝ) ∈ relativeToAbsolute sX π '' R ∧
        OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0 := by
  have hX := h.isProjectiveVariety
  have hS := h.isProjectiveVariety_base
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  have hXv : IsNormalVariety ℂ sX := h.isQFactorial.1
  set φ := relativeToAbsolute sX π with hφ
  have hφinj := relativeToAbsolute_injective sX π
  obtain ⟨hq, hray, hneg⟩ := hR
  obtain ⟨hZp, hZn, hfsZ, hψp, hsurj, hψpr⟩ := isProjectiveVariety_of_isIso_app hX hS h.comp_eq
    hψ.isIso_app hψ.isProjectiveMorphism hψ.comp_eq
  -- the spanning curve
  obtain ⟨C₀, hC₀π, hC₀R, hC₀0⟩ := h.exists_curve ⟨hq, hray, hneg⟩
  have hReq := eq_setOf_smul_of_isExtremalRay hray hC₀R hC₀0
  set w₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hw₀
  have hφC₀ : φ (C₀.relativeClass π hC₀π) = w₀ := relativeToAbsolute_relativeClass sX π C₀ hC₀π
  have hw₀0 : w₀ ≠ 0 := fun h0 => hC₀0 (hφinj (by rw [hφC₀, h0, map_zero]))
  have hφR : φ '' R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • w₀ = u} := by
    rw [hReq]
    ext u
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul, hφC₀]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • C₀.relativeClass π hC₀π, ⟨c, hc, rfl⟩, by rw [map_smul, hφC₀]⟩
  -- the absolute ray
  have hrayA : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (φ '' R) := isExtremalRay_image_relativeToAbsolute sX sS π h.comp_eq hray
  have hnegA : ∀ u ∈ φ '' R, u ≠ 0 →
      QDivisor.curveForm sX (Divisor.toQDivisor K + B) hq u < 0 := by
    rintro _ ⟨r, hr, rfl⟩ hu0
    have := hneg r hr fun h0 => hu0 (by rw [h0, map_zero])
    rwa [QDivisor.relativeCurveForm_eq_comp] at this
  have hRA : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) (φ '' R) :=
    ⟨hq, hrayA, hnegA⟩
  -- the contraction of the absolute ray
  have hcontr : ∀ C : ProperCurve sX,
      C.IsContractedBy ψ ↔ OneCycle.numericalClass sX (C.cycle ℝ) ∈ φ '' R := by
    intro C
    constructor
    · intro hCψ
      have hCπ : C.IsContractedBy π := hψ.comp_eq ▸ isContractedBy_comp g hCψ
      exact ⟨_, (hψ.isContractedBy_iff C hCπ).mp hCψ, relativeToAbsolute_relativeClass sX π C hCπ⟩
    · intro hCR
      obtain ⟨c, -, hc⟩ := (show OneCycle.numericalClass sX (C.cycle ℝ) ∈
        {u | ∃ c : ℝ, 0 ≤ c ∧ c • w₀ = u} from hφR ▸ hCR)
      have hCπ : C.IsContractedBy π := h.isContractedBy_of_numericalClass_eq hC₀π hc.symm
      refine (hψ.isContractedBy_iff C hCπ).mpr ?_
      obtain ⟨r, hr, hrC⟩ := hCR
      rwa [← hφinj (hrC.trans (relativeToAbsolute_relativeClass sX π C hCπ).symm)]
  have hfR : IsContractionOfRay sX (g ≫ sS) (φ '' R) ψ :=
    { isNormalVariety_source := hXv
      isNormalVariety_target := hZn
      comp_eq := hfsZ
      isProjectiveMorphism := hψp
      surjective := hsurj
      isIso_app := hψ.isIso_app
      isContractedBy_iff := hcontr }
  have hC₀ψ : C₀.IsContractedBy ψ := (hcontr C₀).mpr ⟨_, hC₀R, hφC₀⟩
  -- the negative extremal contraction
  have hρ : MMP.Flips.relativePicardNumber sX ψ = 1 :=
    relativePicardNumber_eq_one_of_forall_isContractedBy sX ψ C₀ hC₀ψ hw₀0
      fun C hC => by
        obtain ⟨t, -, ht⟩ := (show OneCycle.numericalClass sX (C.cycle ℝ) ∈
          {u | ∃ c : ℝ, 0 ≤ c ∧ c • w₀ = u} from hφR ▸ (hcontr C).mp hC)
        exact ⟨t, ht⟩
  obtain ⟨mK, hKm⟩ := h.isCanonicalDivisor
  have hamp : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple ψ :=
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX (g ≫ sS) hXv hX hZp ⟨mK, hKm⟩ hq hrayA
      (fun v hv hv0 => by
        have := hnegA v hv hv0
        simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using this)
      ψ hfsZ fun C hC => (hcontr C).mp hC
  haveI : IsProper ψ := hψpr
  have hanti : MMP.Flips.IsRelativelyAntiAmple ψ (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) := by
    rw [MMP.Flips.IsRelativelyAntiAmple, ← map_neg]
    exact hamp.isRelativelyAmple_toRDivisor
  refine ⟨hZp, hRA, hfR, ?_, C₀, hC₀ψ, ⟨_, hC₀R, hφC₀⟩, hw₀0⟩
  exact
    { isNormalVariety_source := hXv
      isNormalVariety_target := hZn
      isCartierCombination := isCartierCombination_toRDivisor hq
      isContraction := ⟨hZn.1, hXv.1, hfsZ, hψpr, hψ.isIso_app⟩
      isRelativelyAntiAmple := hanti
      relativePicardNumber_eq_one := hρ }

/-- The contraction of a negative extremal ray of `NE̅(X/S)` over `S` exists. -/
private theorem Good.exists_contraction (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)}
    (hR : IsNegativeRelativeExtremalRayOf sX π (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (g : Z ⟶ S),
      IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := h.isProjectiveVariety_base
  obtain ⟨m, -, hΔ⟩ := h.exists_isDltPair
  obtain ⟨hq, hray, hneg⟩ := hR
  obtain ⟨Z, ψ, g, hψ⟩ := MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace sS π h.comp_eq
    hΔ h.isQFactorial hray.1 hray.1.2.2.1 hneg
  exact ⟨Z, g ≫ sS, ψ, g, ⟨⟨hq, hray, hneg⟩, hψ, (h.core ⟨hq, hray, hneg⟩ hψ).2.2.2.1⟩⟩

/-- The structure morphism of the target of the contraction of a negative extremal ray is the
one over `S`. -/
private theorem Good.sZ_eq (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)} {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {g : Z ⟶ S}
    (hc : IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g) :
    sZ = g ≫ sS := by
  have hcon := hc.isNegativeExtremalContraction.isContraction
  haveI : IsIso f.appTop := hcon.isIso_app ⊤
  exact eq_of_comp_eq_of_isIso_appTop f (by
    rw [hcon.comp_eq, ← Category.assoc, hc.isRelativeContractionOfFace.comp_eq, h.comp_eq])

/-- The contraction of a negative extremal ray `R` of `NE̅(X/S)` is the contraction, onto a
projective variety, of the negative extremal ray `φ(R)` of `NE̅(X)`. -/
private theorem Good.absolute (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)} {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {g : Z ⟶ S}
    (hc : IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g) :
    MMP.Mori.IsProjectiveVariety ℂ sZ ∧
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) (relativeToAbsolute sX π '' R) ∧
      IsContractionOfRay sX sZ (relativeToAbsolute sX π '' R) f ∧
      ∃ C₀ : ProperCurve sX, C₀.IsContractedBy f ∧
        OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0 := by
  obtain rfl := h.sZ_eq hc
  obtain ⟨h1, h2, h3, -, C₀, h5, -, h6⟩ :=
    h.core hc.isNegativeRelativeExtremalRayOf hc.isRelativeContractionOfFace
  exact ⟨h1, h2, h3, C₀, h5, h6⟩

end Model

/-! ### Small contractions and flips -/

section Small

variable {X Z : Scheme.{0}}

/-- **A small contraction is an isomorphism off codimension two.** -/
private theorem exists_closeds_isIso_of_isSmall [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j :=
    (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

/-- A small contraction in the sense of *Flips and abundance* has an exceptional set of
codimension at least two. -/
private theorem isSmallMorphism_of_isSmall [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hZ : IsNormalVariety ℂ sZ)
    (h : MMP.Flips.IsSmall ℂ sZ sX f) : IsSmallMorphism sX sZ f := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := exists_closeds_isIso_of_isSmall h
  refine ⟨⟨h.isVariety_source, inferInstance⟩, hZ, h.comp_eq, h.isProper,
    h.isBirationalMorphism, ?_⟩
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  refine hV x ?_
  by_contra hxV
  have hb : f x ∈ biregularLocus f := le_biregularLocus hiso (hle hxV)
  exact (MMP.Mori.mem_exceptionalSet.mp hx) hb

/-- A small morphism (exceptional set of codimension `≥ 2`) with `𝒪_Z ≅ f_* 𝒪_X` is a small
birational contraction. -/
private theorem isSmall_of_isSmallMorphism {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f) (happ : ∀ U : Z.Opens, IsIso (f.app U)) :
    MMP.Flips.IsSmall ℂ sZ sX f := by
  have := hf.isNormalVariety_target.2
  have := hf.isProper
  have := hf.isNormalVariety_source.1
  have := hf.isNormalVariety_target.1
  have hbc : MMP.Flips.IsBirationalContraction ℂ sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h := hf.two_le_codimension
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h ⊢
  intro x hx
  refine h x fun hx' => hx ⟨f ⁻¹ᵁ biregularLocus f, by simpa [exceptionalSet] using hx', ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

end Small

section Flip

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
  {B : QDivisor X}

/-- **In dimension at most two the contraction of a negative extremal ray is never small.** The
generic point `η` of a curve contracted by `f` lies in the exceptional set of `f`: on a
neighbourhood of `η` where `f` is an open immersion, `f` would be injective on a closed point of
the curve and `η`. So its coheight, `dim X - 1 ≤ 1`, would be at least two. -/
private theorem Good.not_isSmall (h : Good sX sS π K B) (hdim : topologicalKrullDim X ≠ 3)
    {R : Set (RelativeNumericalCurveClasses sX π)} {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {g : Z ⟶ S}
    (hc : IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g) :
    ¬ MMP.Flips.IsSmall ℂ sZ sX f := by
  intro hs
  obtain ⟨-, -, -, C₀, hC₀f, -⟩ := h.absolute hc
  haveI : IsNormal Z := hc.isNegativeExtremalContraction.isNormalVariety_target.2
  have hX := h.isProjectiveVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set η := C₀.point
  -- the curve `{η}⁻` has dimension at least one
  have hrange : Set.range C₀.ι = closure ({η} : Set X) := by
    unfold ProperCurve.ι curveSubschemeAtι
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hCdim : (1 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({η} : Set X)) := by
    rw [← C₀.dim_eq]
    have hmem : ∀ x, C₀.ι x ∈ closure ({η} : Set X) := fun x => hrange ▸ ⟨x, rfl⟩
    exact (C₀.ι.isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le
  -- `η` is not a closed point
  have hηnc : ¬ IsClosed ({η} : Set X) := fun hcl => by
    rw [hcl.closure_eq] at hCdim
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({η} : Set X)
    exact absurd (hCdim.trans h0) (by decide)
  -- `η` lies in the exceptional set of `f`
  have hηE : η ∈ (MMP.Flips.exceptionalCloseds f : Set X) := by
    change ¬ _
    rintro ⟨V, hηV, hV⟩
    have hcl : closure (closure ({η} : Set X) ∩ closedPoints X) = closure ({η} : Set X) :=
      closure_inter_closedPoints isClosed_closure
    have hηc : η ∈ closure (closure ({η} : Set X) ∩ closedPoints X) := by
      rw [hcl]; exact subset_closure rfl
    obtain ⟨c, hcV, hcCs, hcc⟩ := mem_closure_iff.mp hηc V V.isOpen hηV
    have hfc : f c = f η := hC₀f c hcCs
    let c' : V.toScheme := ⟨c, hcV⟩
    let η' : V.toScheme := ⟨η, hηV⟩
    have hinj := (V.ι ≫ f).isOpenEmbedding.injective (a₁ := c') (a₂ := η') (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact hfc)
    have hcη : c = η := congrArg Subtype.val hinj
    exact hηnc (hcη ▸ hcc)
  -- so its coheight is at least two, while `dim {η}⁻ + coheight η = dim X ≤ 3`
  have h2 : (2 : ℕ∞) ≤ Order.coheight η :=
    MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      ((MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet
        hs.toIsBirationalContraction).mp hs) η hηE
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX η
  have h3 : (3 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [← hsum]
    have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight η : WithBot ℕ∞) := by
      exact_mod_cast h2
    calc (3 : WithBot ℕ∞) = 1 + ((2 : ℕ∞) : WithBot ℕ∞) := rfl
      _ ≤ _ := add_le_add hCdim h2'
  exact hdim (le_antisymm h.dim_le h3)

/-- **Flips of small contractions.** A small contraction of a negative extremal ray of
`NE̅(X/S)` has a flip with projective source. -/
private theorem Good.exists_flip (h : Good sX sS π K B)
    {R : Set (RelativeNumericalCurveClasses sX π)} {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {g : Z ⟶ S}
    (hc : IsNegativeRelativeRayContraction sX π sZ (Divisor.toQDivisor K + B) R f g)
    (hs : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X')
      (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z) (φ : X.RationalMap X'),
      MMP.Mori.IsProjectiveVariety ℂ sX' ∧
      MMP.Flips.IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ ∧
      MMP.Mori.IsFlip sX sZ sX' K B f fp ∧ IsProjectiveMorphism fp ∧
      MMP.Mori.RationalMap.transformDivisor φ B = flipTransform f fp B := by
  by_cases hdim : topologicalKrullDim X = 3
  swap
  · exact absurd hs (h.not_isSmall hdim hc)
  obtain ⟨hZp, hneg, hcr, -⟩ := h.absolute hc
  have hE := hc.isNegativeExtremalContraction
  have hZn : IsNormalVariety ℂ sZ := hE.isNormalVariety_target
  have hsmall : IsSmallMorphism sX sZ f := isSmallMorphism_of_isSmall hZn hs
  obtain ⟨X', _, _, _, sX', fp, hflip⟩ := IsContractionOfRay.exists_isFlip
    ⟨h.isProjectiveVariety, hdim, h.isQFactorial, h.isCanonicalDivisor, h.isDltPair⟩ hneg hcr
    hsmall
  have hX'n : IsNormalVariety ℂ sX' := hflip.isNormalVariety
  haveI : IsIntegral X' := hX'n.1.toIsIntegral
  haveI : IsProper fp := hflip.isProper
  -- `f⁺` is projective, so `X⁺` is a projective variety
  obtain ⟨-, -, L, hLc, -, hLamp⟩ := hflip.hasRelativelyAmpleMultiple
  have hfpp : IsProjectiveMorphism fp := isProjectiveMorphism_of_isRelativelyAmple hZp fp hLc hLamp
  have hX'p : MMP.Mori.IsProjectiveVariety ℂ sX' := by
    rw [MMP.Mori.isProjectiveVariety_iff]
    refine ⟨hX'n.1, ?_⟩
    rw [← hflip.comp_eq]
    exact hfpp.comp hZp.isProjective
  -- the flip as a birational map
  obtain ⟨V, hV1, hV2, hXV, hX'V, -⟩ := hflip.exists_opens_isIso
  haveI := hV1
  haveI := hV2
  have hgen : ∀ (T : Scheme.{0}) [IsIntegral T], Order.coheight (genericPoint T) ≤ 1 :=
    fun T _ => (Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z).trans_le
      zero_le_one
  let e : X.PartialIso X' :=
    ⟨f ⁻¹ᵁ V, (f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ (hgen X)⟩,
      fp ⁻¹ᵁ V, (fp ⁻¹ᵁ V).isOpen.dense ⟨_, hX'V _ (hgen X')⟩,
      asIso (f ∣_ V) ≪≫ (asIso (fp ∣_ V)).symm⟩
  have he_fac : e.iso.hom ≫ e.target.ι ≫ fp = e.source.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V)) ≫ (fp ⁻¹ᵁ V).ι ≫ fp = _
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
  set φ : X.RationalMap X' := e.toRationalMap
  have hover : MMP.Flips.RationalMap.IsOver f fp φ := by
    rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
    change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
      X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
    rw [Category.assoc, he_fac]
    simp
  have hfr : IsFlipRationalMap sX sZ sX' K B f fp φ := ⟨hflip, hover⟩
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D :=
    fun D => hfr.transformDivisor_eq_flipTransform D
  have htrE : MMP.Mori.RationalMap.transformDivisor φ
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) =
      QDivisor.toRDivisor (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B) := by
    rw [htr, flipTransform_toRDivisor, flipTransform_add]
  -- `f⁺` is a small birational contraction
  have hfpS : IsSmallMorphism sX' sZ fp :=
    { isNormalVariety_source := hX'n
      isNormalVariety_target := hZn
      comp_eq := hflip.comp_eq
      isProper := hflip.isProper
      isBirationalMorphism := hflip.isBirationalMorphism
      two_le_codimension := hflip.two_le_codimension }
  have hfpapp := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX' sZ
    hX'n.1 hZn fp hflip.isBirationalMorphism).1
  refine ⟨X', inferInstance, inferInstance, inferInstance, inferInstance, sX', fp, φ, hX'p,
    { isNormalVariety_source := hE.isNormalVariety_source
      isNormalVariety_target := hZn
      isNormalVariety_flip := hX'n
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := ⟨⟨e, rfl⟩, hover⟩
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver
        hE.isNormalVariety_source f fp φ hover
      isSmall := isSmall_of_isSmallMorphism hfpS hfpapp
      isCartierCombination_transform := by
        rw [htrE]; exact isCartierCombination_toRDivisor hflip.isQCartier
      isRelativelyAmple_transform := by
        rw [htrE]; exact hflip.hasRelativelyAmpleMultiple.isRelativelyAmple_toRDivisor
      isSmall_source := hs }, hflip, hfpp, htr B⟩

end Flip

/-! ### Termination -/

section Termination

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
  {B : QDivisor X}

/-- If every point of codimension at most one of `Z` maps into the open `V`, the complement of
the preimage of `V` has codimension at least two. -/
private theorem two_le_closedsCodimension_compl_preimage {Y Z : Scheme.{0}} (h : Z ⟶ Y)
    {V : Y.Opens} (hZ : ∀ x : Z, Order.coheight x ≤ 1 → h x ∈ V) :
    2 ≤ closedsCodimension (h ⁻¹ᵁ V).compl := by
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  by_contra hlt
  exact hx (hZ x (Order.le_of_lt_add_one (not_le.mp hlt)))

/-- **Two `ℚ`-factorial projective varieties over a common base, isomorphic over an open of the
base containing the images of all their points of codimension at most one, have the same
Picard number.** -/
private theorem picardNumber_eq_of_isIso_morphismRestrict {X X' Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsQFactorial sX) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hX' : IsQFactorial sX')
    (hX'p : MMP.Mori.IsProjectiveVariety ℂ sX') {g : X ⟶ Y} {gp : X' ⟶ Y}
    (hc : g ≫ sY = sX) (hc' : gp ≫ sY = sX') (V : Y.Opens) [IsIso (g ∣_ V)] [IsIso (gp ∣_ V)]
    (hgV : ∀ x : X, Order.coheight x ≤ 1 → g x ∈ V)
    (hgpV : ∀ x : X', Order.coheight x ≤ 1 → gp x ∈ V) :
    picardNumber sX = picardNumber sX' := by
  have h1 : ((g ⁻¹ᵁ V).compl.compl : X.Opens) = g ⁻¹ᵁ V := by ext; simp
  have h2 : ((gp ⁻¹ᵁ V).compl.compl : X'.Opens) = gp ⁻¹ᵁ V := by ext; simp
  refine MMP.Fourfold.picardNumber_eq_of_isoInCodimOne sX sX' hX hXp hX' hX'p _ _
    (two_le_closedsCodimension_compl_preimage g hgV)
    (two_le_closedsCodimension_compl_preimage gp hgpV)
    (X.isoOfEq h1 ≪≫ asIso (g ∣_ V) ≪≫ (asIso (gp ∣_ V)).symm ≪≫ X'.isoOfEq h2.symm) ?_
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← hc', ← hc, Scheme.isoOfEq_hom_ι_assoc, ← morphismRestrict_ι_assoc,
    IsIso.inv_hom_id_assoc, morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]

/-- One step of a projective program: the next model is a model of the same dimension, whose
Picard number is one less after a divisorial contraction and the same after a flip. -/
private theorem Good.step {X' Z : Scheme.{0}} [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] (h : Good sX sS π K B) {sX' : X' ⟶ Spec (.of ℂ)}
    {π' : X' ⟶ S} {K' : Divisor X'} {B' : QDivisor X'} {sZ : Z ⟶ Spec (.of ℂ)}
    {R : Set (RelativeNumericalCurveClasses sX π)} {f : X ⟶ Z} {g : Z ⟶ S} {fp : X' ⟶ Z}
    {φ : X.RationalMap X'}
    (hst : IsElementaryDltStep sX π sZ sX' π' K B R f g fp φ)
    (hm : IsRelativeDltModel sX' sS π' K' B') (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') :
    Good sX' sS π' K' B' ∧ topologicalKrullDim X' = topologicalKrullDim X ∧
      ((MMP.Flips.IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ →
          picardNumber sX' = picardNumber sX) ∧
        (¬ MMP.Flips.IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ →
          picardNumber sX' + 1 = picardNumber sX)) := by
  have hc := hst.isNegativeRelativeRayContraction
  obtain ⟨hZp, hneg, hcr, -⟩ := h.absolute hc
  have hsZ := h.sZ_eq hc
  have hE := hc.isNegativeExtremalContraction
  have hsX' : sX' = fp ≫ sZ := by
    rw [← hm.comp_eq, ← hst.comp_eq, hsZ, Category.assoc]
  -- the dimension
  have hdim : topologicalKrullDim X' = topologicalKrullDim X := by
    rcases hst.divisorial_or_flip with ⟨hfb, -, hiso, -⟩ | hflip
    · haveI := hiso
      have h1 : topologicalKrullDim X' = topologicalKrullDim Z :=
        IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso fp)).isHomeomorph
      have hZv : AlgebraicGeometry.IsVariety ℂ sZ := hZp.toIsVariety
      have hXv : AlgebraicGeometry.IsVariety ℂ sX := h.isProjectiveVariety.toIsVariety
      rw [h1, ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb]
    · exact hflip.isSmall.dim_eq.trans hflip.isSmall_source.dim_eq.symm
  refine ⟨⟨hX', h.isProjectiveVariety_base, hm.comp_eq, hdim ▸ h.dim_le, hm.isQFactorial,
    hm.isCanonicalDivisor, hm.isDltPair⟩, hdim, fun hflip => ?_, fun hnf => ?_⟩
  · -- a flip preserves the Picard number
    obtain ⟨V, hV1, hV2, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hflip.isSmall_source hflip.isSmall
    haveI := hV1
    haveI := hV2
    exact (picardNumber_eq_of_isIso_morphismRestrict sZ h.isQFactorial h.isProjectiveVariety
      hm.isQFactorial hX' hE.isContraction.comp_eq hsX'.symm V hXV hX'V).symm
  · -- a divisorial contraction drops it by one
    obtain ⟨hfb, -, hiso, -⟩ := hst.divisorial_or_flip.resolve_right hnf
    haveI := hiso
    obtain ⟨m, hKm, hΔ⟩ := h.exists_isDltPair
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := h.isProjectiveVariety
    haveI : QuasiCompact sX := h.isProjectiveVariety.toIsVariety.toQuasiCompact
    have hg : IsContractionOfFace ℂ sX sX' (relativeToAbsolute sX π '' R) (f ≫ inv fp) :=
      { isProjectiveVariety_source := h.isProjectiveVariety
        isProjectiveVariety_target := hX'
        comp_eq := by rw [Category.assoc, hsX', IsIso.inv_hom_id_assoc, hcr.comp_eq]
        isExtremalFace := hneg.2.1.1
        isContractedBy_iff := fun C => by
          rw [← hcr.isContractedBy_iff C]
          constructor
          · intro hC x hx
            have e1 : ∀ y, fp ((f ≫ inv fp) y) = f y := fun y => by
              rw [← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
            rw [← e1 x, ← e1 C.point, hC x hx]
          · intro hC x hx
            rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
        isIso_app := fun U => by
          rw [Scheme.Hom.comp_app]
          exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (hcr.isIso_app _) }
    exact MMP.Mori.IsDltPair.picardNumber_add_one_eq_of_isContractionOfFace hΔ h.isQFactorial
      hneg.2.1 hneg.2.2 hg

/-- Along a projective program, every model is a model of the dimension of `X`. -/
private theorem Good.program (h : Good sX sS π K B) (P : RelativeDltProgram sX sS π K B)
    (hP : P.IsProjective) (i : ℕ) (hi : (i : ℕ∞) ≤ P.n) :
    Good (modelStr sX P.sY i) sS (modelMap π P.πY i) (divisorSeq K P.KY i)
        (divisorSeq B P.BY i) ∧
      topologicalKrullDim (modelSeq X P.Y i) = topologicalKrullDim X := by
  induction i with
  | zero => exact ⟨h, rfl⟩
  | succ i ih =>
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    obtain ⟨hg, hd⟩ := ih hi'.le
    obtain ⟨hg', hd', -⟩ := hg.step (P.isElementaryDltStep i hi') (P.isRelativeDltModel (i + 1) hi)
      (hP.2 (i + 1) hi)
    exact ⟨hg', hd'.trans hd⟩

/-- An antitone sequence of natural numbers is eventually constant. -/
private theorem exists_forall_ge_eq_of_antitone {c : ℕ → ℕ} (hc : Antitone c) :
    ∃ N, ∀ i, N ≤ i → c i = c N := by
  classical
  have hex : ∃ k, ∃ i, c i = k := ⟨_, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun i hi => le_antisymm (hc hi) ?_⟩
  rw [hN]
  exact Nat.find_min' hex ⟨i, rfl⟩

/-- The tail of an infinite program from the model `X_N` on. -/
private noncomputable def RelativeDltProgram.tail (P : RelativeDltProgram sX sS π K B)
    (hn : P.n = ⊤) (N : ℕ) :
    RelativeDltProgram (modelStr sX P.sY N) sS (modelMap π P.πY N) (divisorSeq K P.KY N)
      (divisorSeq B P.BY N) where
  n := ⊤
  Y j := P.Y (N + j)
  sY j := P.sY (N + j)
  isIntegral _ := inferInstance
  compactSpace _ := inferInstance
  isLocallyNoetherian _ := inferInstance
  isNormal _ := inferInstance
  πY j := P.πY (N + j)
  KY j := P.KY (N + j)
  BY j := P.BY (N + j)
  R j := match j with
    | 0 => P.R N
    | j + 1 => P.R (N + (j + 1))
  Z j := P.Z (N + j)
  sZ j := P.sZ (N + j)
  f j := match j with
    | 0 => P.f N
    | j + 1 => P.f (N + (j + 1))
  gZ j := P.gZ (N + j)
  fp j := P.fp (N + j)
  φ j := match j with
    | 0 => P.φ N
    | j + 1 => P.φ (N + (j + 1))
  isRelativeDltModel j _ := match j with
    | 0 => P.isRelativeDltModel N (hn ▸ le_top)
    | j + 1 => P.isRelativeDltModel (N + (j + 1)) (hn ▸ le_top)
  isElementaryDltStep j _ := match j with
    | 0 => P.isElementaryDltStep N (hn ▸ ENat.coe_lt_top _)
    | j + 1 => P.isElementaryDltStep (N + (j + 1)) (hn ▸ ENat.coe_lt_top _)
  BY_eq j _ := match j with
    | 0 => P.BY_eq N (hn ▸ ENat.coe_lt_top _)
    | j + 1 => P.BY_eq (N + (j + 1)) (hn ▸ ENat.coe_lt_top _)
  hasFinal := False
  finalRay := ∅
  T := S
  sT := sS
  gT := 𝟙 S
  g := modelMap (modelMap π P.πY N) (fun j => P.πY (N + j)) _
  final_spec h := h.elim

/-- **Termination.** Every projective program from a model is finite. -/
private theorem Good.n_ne_top (h : Good sX sS π K B) (P : RelativeDltProgram sX sS π K B)
    (hP : P.IsProjective) : P.n ≠ ⊤ := by
  intro hn
  have hlt (i : ℕ) : (i : ℕ∞) < P.n := hn ▸ ENat.coe_lt_top i
  have hgood (i : ℕ) := h.program P hP i (hlt i).le
  have hstep (i : ℕ) := (hgood i).1.step (P.isElementaryDltStep i (hlt i))
    (P.isRelativeDltModel (i + 1) (hlt (i + 1)).le) (hP.2 (i + 1) (hlt (i + 1)).le)
  have hfin (i : ℕ) : picardNumber (modelStr sX P.sY i) ≠ ⊤ := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (modelStr sX P.sY i) :=
      (hgood i).1.isProjectiveVariety
    exact (MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety _).ne
  set ρ : ℕ → ℕ := fun i => (picardNumber (modelStr sX P.sY i)).toNat with hρ
  have hρc (i : ℕ) : (ρ i : ℕ∞) = picardNumber (modelStr sX P.sY i) := ENat.coe_toNat (hfin i)
  -- the Picard number does not increase, and drops at the non-flip steps
  have hle (i : ℕ) : ρ (i + 1) ≤ ρ i ∧
      (¬ MMP.Flips.IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
        (P.f i) (P.fp i) (P.φ i) → ρ (i + 1) < ρ i) := by
    obtain ⟨-, -, hfl, hdv⟩ := hstep i
    have e : ∀ a b : ℕ, (a : ℕ∞) = b → a = b := fun a b h => by exact_mod_cast h
    by_cases hF : MMP.Flips.IsFlip ℂ (modelStr sX P.sY i) (P.sZ i) (P.sY i)
        (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY i) + divisorSeq B P.BY i))
        (P.f i) (P.fp i) (P.φ i)
    · have := hfl hF
      have h1 : ρ (i + 1) = ρ i := e _ _ (by rw [hρc, hρc]; exact this)
      exact ⟨h1.le, fun h' => absurd hF h'⟩
    · have := hdv hF
      have h1 : ρ (i + 1) + 1 = ρ i := e _ _ (by push_cast; rw [hρc, hρc]; exact this)
      exact ⟨by omega, fun _ => by omega⟩
  obtain ⟨N, hN⟩ := exists_forall_ge_eq_of_antitone (antitone_nat_of_succ_le fun i => (hle i).1)
  have hflip (j : ℕ) : MMP.Flips.IsFlip ℂ (modelStr sX P.sY (N + j)) (P.sZ (N + j))
      (P.sY (N + j))
      (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY (N + j)) +
        divisorSeq B P.BY (N + j))) (P.f (N + j)) (P.fp (N + j)) (P.φ (N + j)) := by
    by_contra hF
    have h1 := (hle (N + j)).2 hF
    rw [hN (N + j + 1) (by omega), hN (N + j) (by omega)] at h1
    exact lt_irrefl _ h1
  by_cases hdim : topologicalKrullDim X = 3
  · -- in dimension three, the tail from `X_N` is an infinite program of flips
    have hPt : (RelativeDltProgram.tail P hn N).IsProjective := by
      refine ⟨hP.1, fun j _ => ?_⟩
      rcases j with _ | j
      · exact hP.2 N (hlt N).le
      · exact hP.2 (N + (j + 1)) (hlt _).le
    refine RelativeDltProgram.IsProjective.n_ne_top_of_isFlip hPt
      ((hgood N).2.trans hdim) (fun j _ => ?_) rfl
    rcases j with _ | j
    · exact hflip 0
    · exact hflip (j + 1)
  · -- in dimension at most two there are no flips
    have := hflip 0
    exact (hgood N).1.not_isSmall (fun h3 => hdim ((hgood N).2.symm.trans h3))
      (P.isElementaryDltStep N (hlt N)).isNegativeRelativeRayContraction this.isSmall_source

end Termination

/-! ### Existence of a maximal program -/

section Existence

variable {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {π : X ⟶ S} {K : Divisor X}
  {B : QDivisor X}

/-- A model is a model of a relative elementary dlt program over `S`. -/
private theorem Good.isRelativeDltModel (h : Good sX sS π K B) :
    IsRelativeDltModel sX sS π K B := by
  have hX := h.isProjectiveVariety
  have hS := h.isProjectiveVariety_base
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hX.isProjective
  haveI : IsSeparated sS := hS.toIsVariety.toIsSeparated
  haveI : IsProper (π ≫ sS) := by rw [h.comp_eq]; infer_instance
  haveI : IsProper π := IsProper.of_comp π sS
  exact ⟨AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sS,
    AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sX, h.comp_eq,
    isProjectiveMorphism_of_isProper hX hS π, h.isQFactorial, h.isCanonicalDivisor,
    h.isDltPair⟩

/-- A normal complex variety of dimension `n` has a canonical divisor: the divisor of a nonzero
rational top form. -/
private theorem exists_isCanonicalDivisor {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : IsNormalVariety ℂ sY) {n : ℕ} (hn : topologicalKrullDim Y = n) :
    ∃ K : Divisor Y, K.IsCanonicalDivisor sY n := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sY
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hY hn
  exact ⟨topFormDivisor sY (show RationalTopForms sY n from b ()),
    MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hY hn (b.ne_zero ())⟩

/-- A projective `(K + D)`-flip in the sense of `MMP.Mori.IsFlip` of the small contraction of an
extremal ray is a `(K + D)`-flip in the sense of `MMP.Fourfold.IsFlipOf`. -/
private theorem isFlipOf_of_isFlip {W X' : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {D : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W} {fp : X' ⟶ W}
    (hf : IsContractionOfRay sX sW R f) (hsmall : IsSmallMorphism sX sW f)
    (h : MMP.Mori.IsFlip sX sW sX' K D f fp) (hproj : IsProjectiveMorphism fp) :
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
  isQCartier_flip := by rw [flipTransform_add]; exact h.isQCartier
  hasRelativelyAmpleMultiple_flip := by rw [flipTransform_add]; exact h.hasRelativelyAmpleMultiple

variable (sS) in
/-- A model over `S`, bundled. -/
private structure St where
  W : Scheme.{0}
  [isIntegral : IsIntegral W]
  [compactSpace : CompactSpace W]
  [isLocallyNoetherian : IsLocallyNoetherian W]
  [isNormal : IsNormal W]
  sW : W ⟶ Spec (.of ℂ)
  πW : W ⟶ S
  K : Divisor W
  B : QDivisor W
  good : Good sW sS πW K B

attribute [local instance] St.isIntegral St.compactSpace St.isLocallyNoetherian St.isNormal

/-- The adjoint of a bundled model is nef over `S`. -/
private def St.IsNef (s : St sS) : Prop :=
  MMP.Flips.IsRelativelyNef ℂ s.sW s.πW (QDivisor.toRDivisor (Divisor.toQDivisor s.K + s.B))

/-- The data of a step from a bundled model. -/
private structure Raw (s : St sS) where
  t : St sS
  R : Set (RelativeNumericalCurveClasses s.sW s.πW)
  Z : Scheme.{0}
  sZ : Z ⟶ Spec (.of ℂ)
  f : s.W ⟶ Z
  g : Z ⟶ S
  fp : t.W ⟶ Z
  φ : s.W.RationalMap t.W

/-- The data of a step form an elementary dlt step, with the transformed boundary. -/
private def Raw.IsStep {s : St sS} (r : Raw s) : Prop :=
  IsElementaryDltStep s.sW s.πW r.sZ r.t.sW r.t.πW s.K s.B r.R r.f r.g r.fp r.φ ∧
    r.t.B = MMP.Mori.RationalMap.transformDivisor r.φ s.B

/-- The data of a final contraction from `W` over `S`. -/
private structure Final {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) (πW : W ⟶ S) where
  R : Set (RelativeNumericalCurveClasses sW πW)
  T : Scheme.{0}
  sT : T ⟶ Spec (.of ℂ)
  gT : T ⟶ S
  g : W ⟶ T

/-- A final contraction is the contraction of a negative extremal ray of fibre type. -/
private def Final.IsFibre {W : Scheme.{0}} [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} {πW : W ⟶ S} (KW : Divisor W) (BW : QDivisor W)
    (q : Final sW πW) : Prop :=
  IsNegativeRelativeRayContraction sW πW q.sT (Divisor.toQDivisor KW + BW) q.R q.g q.gT ∧
    topologicalKrullDim q.T < topologicalKrullDim W

/-- A bundled model has a fibre-type contraction of a negative extremal ray. -/
private def St.HasFibre (s : St sS) : Prop := ∃ q : Final s.sW s.πW, q.IsFibre s.K s.B

/-- The program stops at a bundled model: its adjoint is nef or it has a fibre-type
contraction. -/
private def St.Stops (s : St sS) : Prop := s.IsNef ∨ s.HasFibre

/-- **A further step.** A model whose adjoint is not nef over `S` admits an elementary dlt step,
or a fibre-type contraction of a negative extremal ray. -/
private theorem St.exists_step (s : St sS) (hn : ¬ s.IsNef) :
    (∃ r : Raw s, r.IsStep) ∨ s.HasFibre := by
  classical
  have h := s.good
  have hX := h.isProjectiveVariety
  have hS := h.isProjectiveVariety_base
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s.sW := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : AlgebraicGeometry.IsVariety ℂ s.sW := hX.toIsVariety
  haveI : QuasiCompact s.sW := hX.toIsVariety.toQuasiCompact
  have hXv : IsNormalVariety ℂ s.sW := h.isQFactorial.1
  obtain ⟨m, hKm, -⟩ := h.exists_isDltPair
  have hq := h.isQCartier
  -- the adjoint is not nef over `S` as a `ℚ`-divisor
  have hn' : ¬ (Divisor.toQDivisor s.K + s.B).IsRelativelyNef s.sW s.πW := fun hnef =>
    hn (isRelativelyNef_toRDivisor hq hnef)
  -- a vertical negative extremal ray of `NE̅(W)`
  obtain ⟨R₀, hR₀, hR₀π⟩ := exists_isNegativeExtremalRayOf_isContractedBy_of_not_isRelativelyNef
    hX hS h.isCanonicalDivisor h.isDltPair.1 h.isRelativeDltModel.isProjectiveMorphism h.comp_eq
    hn'
  -- it is spanned by the class of a curve, by the relative case over the base point
  haveI hpt : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨(MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
        MMP.isProjectiveMorphism_of_isClosedImmersion _⟩
  have hgood0 : Good s.sW (𝟙 (Spec (.of ℂ))) s.sW s.K s.B :=
    ⟨hX, hpt, Category.comp_id _, h.dim_le, h.isQFactorial, h.isCanonicalDivisor, h.isDltPair⟩
  set e := relativeToAbsolute s.sW s.sW with he
  have hebij := relativeToAbsolute_bijective s.sW
  have hR₀' : IsNegativeRelativeExtremalRayOf s.sW s.sW (Divisor.toQDivisor s.K + s.B)
      (e ⁻¹' R₀) := by
    refine ⟨hq, isExtremalRay_preimage e hebij.1
      (image_relativeClosedConeOfCurves_eq_inter_range s.sW (𝟙 (Spec (.of ℂ))) s.sW
        (Category.comp_id _)) hR₀.2.1 (by rw [hebij.2.range_eq]; exact Set.subset_univ _),
      fun z hz hz0 => ?_⟩
    rw [QDivisor.relativeCurveForm_eq_comp]
    exact hR₀.2.2 _ hz fun h0 => hz0 (hebij.1 (by rw [h0, map_zero]))
  obtain ⟨C₁, hC₁s, hC₁R, hC₁0⟩ := hgood0.exists_curve hR₀'
  have hw₁ : e (C₁.relativeClass s.sW hC₁s) = OneCycle.numericalClass s.sW (C₁.cycle ℝ) :=
    relativeToAbsolute_relativeClass _ _ _ _
  have hC₁R₀ : OneCycle.numericalClass s.sW (C₁.cycle ℝ) ∈ R₀ := hw₁ ▸ hC₁R
  have hC₁0' : OneCycle.numericalClass s.sW (C₁.cycle ℝ) ≠ 0 := fun h0 =>
    hC₁0 (hebij.1 (by rw [hw₁, h0, map_zero]))
  have hR₀eq := eq_setOf_smul_of_isExtremalRay hR₀.2.1 hC₁R₀ hC₁0'
  have hC₁π : C₁.IsContractedBy s.πW := hR₀π C₁ hC₁R₀
  -- the relative ray `φ⁻¹(R₀)` of `NE̅(W/S)`
  set φ := relativeToAbsolute s.sW s.πW with hφ
  have hφinj := relativeToAbsolute_injective s.sW s.πW
  have hR₀r : R₀ ⊆ Set.range φ := by
    rw [hR₀eq]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c • C₁.relativeClass s.πW hC₁π, by
      rw [map_smul, relativeToAbsolute_relativeClass]⟩
  have hR : IsNegativeRelativeExtremalRayOf s.sW s.πW (Divisor.toQDivisor s.K + s.B)
      (φ ⁻¹' R₀) :=
    ⟨hq, isExtremalRay_preimage φ hφinj
      (image_relativeClosedConeOfCurves_eq_inter_range s.sW sS s.πW h.comp_eq) hR₀.2.1 hR₀r,
      fun z hz hz0 => by
        rw [QDivisor.relativeCurveForm_eq_comp]
        exact hR₀.2.2 _ hz fun h0 => hz0 (hφinj (by rw [h0, map_zero]))⟩
  -- its contraction, and the trichotomy
  obtain ⟨Z, sZ, f, g, hc⟩ := h.exists_contraction hR
  obtain ⟨hZp, hnegA, hcr, -⟩ := h.absolute hc
  have hsZ := h.sZ_eq hc
  have hface : IsContractionOfFace ℂ s.sW sZ (φ '' (φ ⁻¹' R₀)) f :=
    { isProjectiveVariety_source := hX
      isProjectiveVariety_target := hZp
      comp_eq := hcr.comp_eq
      isExtremalFace := hnegA.2.1.1
      isContractedBy_iff := hcr.isContractedBy_iff
      isIso_app := hcr.isIso_app }
  obtain ⟨htri, -, -, hds⟩ :=
    MMP.Mori.IsContractionOfFace.trichotomy_of_isExtremalRay h.isQFactorial hnegA.2.1 hface
  have hZn : IsNormalVariety ℂ sZ := hcr.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hcr.isProjectiveMorphism
  rcases htri with hfib | hdiv | hsm
  · -- a contraction of fibre type
    exact Or.inr ⟨⟨φ ⁻¹' R₀, Z, sZ, g, f⟩, hc, hfib.dim_lt⟩
  · -- a divisorial contraction
    left
    have hfb := hdiv.isBirationalMorphism
    have hdimZ : topologicalKrullDim Z = topologicalKrullDim s.W :=
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ s.sW hfb
    obtain ⟨KZ, hKZ⟩ := exists_isCanonicalDivisor hZn (hdimZ.trans hKm.topologicalKrullDim_eq)
    have hnotsmall : ¬ IsSmallMorphism s.sW sZ f := fun hs' =>
      hds ⟨hdiv, ⟨hXv, hnegA.2.1, hface, hfb, hs'.two_le_codimension⟩⟩
    have hpres := IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair
      (Δ' := flipTransform f (𝟙 Z) s.B)
      { isProjectiveQFactorialDltPair := ⟨hX, h.isQFactorial, h.isCanonicalDivisor, h.isDltPair⟩
        isNegativeExtremalRayOf := hnegA
        isContractionOfRay := hcr
        isBirationalMorphism := hfb
        comp_eq := Category.id_comp sZ
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inr ⟨hnotsmall, inferInstance⟩ }
    have hBZ : flipTransform f (𝟙 Z) s.B =
        MMP.Mori.RationalMap.transformDivisor f.toRationalMap s.B := by
      simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Fourfold.inverseTransformDivisor_id]
    let t : St sS := ⟨Z, sZ, g, KZ, flipTransform f (𝟙 Z) s.B,
      ⟨hZp, hS, hsZ.symm, hdimZ ▸ h.dim_le, hpres.1, ⟨m, hKZ⟩, hpres.2⟩⟩
    have hover : MMP.Flips.RationalMap.IsOver f (𝟙 Z) f.toRationalMap := by
      rw [MMP.Flips.RationalMap.IsOver, Scheme.Hom.toRationalMap,
        ← Scheme.RationalMap.compHom_toRationalMap]
      congr 1
    exact ⟨⟨t, φ ⁻¹' R₀, Z, sZ, f, g, 𝟙 Z, f.toRationalMap⟩,
      ⟨{ isNegativeRelativeRayContraction := hc
         comp_eq := Category.id_comp g
         divisorial_or_flip := Or.inl ⟨hfb, hdiv.exists_primeDivisor, inferInstance, hfb,
           hover⟩ }, hBZ⟩⟩
  · -- a small contraction, and its flip
    left
    have hsmall : IsSmallMorphism s.sW sZ f :=
      ⟨hXv, hZn, hcr.comp_eq, inferInstance, hsm.isBirationalMorphism, hsm.two_le_codimension⟩
    have hs : MMP.Flips.IsSmall ℂ sZ s.sW f := isSmall_of_isSmallMorphism hsmall hcr.isIso_app
    obtain ⟨X', _, _, _, _, sX', fp, ψ, hX'p, hflip, hflipM, hfpp, htr⟩ := h.exists_flip hc hs
    have hpres := IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair
      (Δ' := flipTransform f fp s.B)
      { isProjectiveQFactorialDltPair := ⟨hX, h.isQFactorial, h.isCanonicalDivisor, h.isDltPair⟩
        isNegativeExtremalRayOf := hnegA
        isContractionOfRay := hcr
        isBirationalMorphism := hsm.isBirationalMorphism
        comp_eq := hflipM.comp_eq
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inl ⟨hsmall, isFlipOf_of_isFlip hcr hsmall hflipM hfpp⟩ }
    have hdimX' : topologicalKrullDim X' = topologicalKrullDim s.W :=
      hflip.isSmall.dim_eq.trans hflip.isSmall_source.dim_eq.symm
    have hcomp' : (fp ≫ g) ≫ sS = sX' := by rw [Category.assoc, ← hsZ, hflipM.comp_eq]
    have hdlt' : MMP.Intersection.IsDltPair sX' (MMP.Mori.RationalMap.transformDivisor ψ s.B) := by
      rw [htr]; exact hpres.2
    let t : St sS := ⟨X', sX', fp ≫ g, flipTransform f fp s.K,
      MMP.Mori.RationalMap.transformDivisor ψ s.B,
      ⟨hX'p, hS, hcomp', hdimX' ▸ h.dim_le, hpres.1,
        ⟨m, MMP.Mori.IsFlip.isCanonicalDivisor_flipTransform hKm hflipM⟩, hdlt'⟩⟩
    exact ⟨⟨t, φ ⁻¹' R₀, Z, sZ, f, g, fp, ψ⟩, ⟨⟨hc, rfl, Or.inr hflip⟩, rfl⟩⟩

/-- The next step of the program from a bundled model (a step whenever one exists). -/
private noncomputable def next (s : St sS) : Raw s := by
  classical
  exact if h : ∃ r : Raw s, r.IsStep then h.choose
    else ⟨s, ∅, S, sS, s.πW, 𝟙 S, s.πW, Scheme.Hom.toRationalMap (𝟙 s.W)⟩

private theorem next_isStep (s : St sS) (h : ∃ r : Raw s, r.IsStep) : (next s).IsStep := by
  classical
  rw [next, dif_pos h]
  exact h.choose_spec

/-- The final contraction at a bundled model (of fibre type whenever one exists). -/
private noncomputable def final (s : St sS) : Final s.sW s.πW := by
  classical
  exact if h : s.HasFibre then h.choose else ⟨∅, S, sS, 𝟙 S, s.πW⟩

private theorem final_isFibre (s : St sS) (h : s.HasFibre) : (final s).IsFibre s.K s.B := by
  classical
  rw [final, dif_pos h]
  exact h.choose_spec

/-- The models of the program. -/
private noncomputable def seq (s₀ : St sS) : ℕ → St sS
  | 0 => s₀
  | i + 1 => (next (seq s₀ i)).t

/-- **Existence.** A model has a finite projective program ending with a relatively nef adjoint
or a Mori fibre space. -/
private theorem Good.exists_program (h : Good sX sS π K B) :
    ∃ P : RelativeDltProgram sX sS π K B, P.IsProjective ∧ P.n ≠ ⊤ ∧
      (MMP.Flips.IsRelativelyNef ℂ (modelStr sX P.sY P.n.toNat) (modelMap π P.πY P.n.toNat)
          (QDivisor.toRDivisor (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) +
            divisorSeq B P.BY P.n.toNat)) ∨ P.hasFinal) := by
  classical
  let s₀ : St sS := ⟨X, sX, π, K, B, h⟩
  let Sq : ℕ → St sS := seq s₀
  let nn : ℕ∞ := if hex : ∃ i, (Sq i).Stops then (Nat.find hex : ℕ∞) else ⊤
  have hstop : ∀ i : ℕ, (i : ℕ∞) < nn → ¬ (Sq i).Stops := by
    intro i hi hs
    by_cases hex : ∃ i, (Sq i).Stops
    · have hi' : (i : ℕ∞) < Nat.find hex := by
        have : nn = Nat.find hex := dif_pos hex
        rwa [this] at hi
      exact Nat.find_min hex (by exact_mod_cast hi') hs
    · exact hex ⟨i, hs⟩
  have hstep : ∀ i : ℕ, (i : ℕ∞) < nn → ∃ r : Raw (Sq i), r.IsStep := fun i hi =>
    ((Sq i).exists_step fun hn => hstop i hi (Or.inl hn)).resolve_right
      fun hf => hstop i hi (Or.inr hf)
  let Yi : ℕ → Scheme.{0} := fun i => (Sq (i + 1)).W
  let sYi : ∀ i, Yi i ⟶ Spec (.of ℂ) := fun i => (Sq (i + 1)).sW
  let πYi : ∀ i, Yi i ⟶ S := fun i => (Sq (i + 1)).πW
  let KYi : ∀ i, Divisor (Yi i) := fun i => (Sq (i + 1)).K
  let BYi : ∀ i, QDivisor (Yi i) := fun i => (Sq (i + 1)).B
  haveI hYi1 : ∀ i, IsIntegral (Yi i) := fun i => (Sq (i + 1)).isIntegral
  haveI hYi2 : ∀ i, CompactSpace (Yi i) := fun i => (Sq (i + 1)).compactSpace
  haveI hYi3 : ∀ i, IsLocallyNoetherian (Yi i) := fun i => (Sq (i + 1)).isLocallyNoetherian
  haveI hYi4 : ∀ i, IsNormal (Yi i) := fun i => (Sq (i + 1)).isNormal
  let finalAt : ∀ i : ℕ, Final (modelStr sX sYi i) (modelMap π πYi i) := fun i => match i with
    | 0 => final (Sq 0)
    | j + 1 => final (Sq (j + 1))
  have hfinalAt : ∀ i : ℕ, (Sq i).HasFibre →
      (finalAt i).IsFibre (divisorSeq K KYi i) (divisorSeq B BYi i) := by
    intro i hi
    rcases i with _ | j
    · exact final_isFibre (Sq 0) hi
    · exact final_isFibre (Sq (j + 1)) hi
  let P : RelativeDltProgram sX sS π K B :=
    { n := nn
      Y := Yi
      sY := sYi
      isIntegral := hYi1
      compactSpace := hYi2
      isLocallyNoetherian := hYi3
      isNormal := hYi4
      πY := πYi
      KY := KYi
      BY := BYi
      R := fun i => match i with
        | 0 => (next (Sq 0)).R
        | j + 1 => (next (Sq (j + 1))).R
      Z := fun i => (next (Sq i)).Z
      sZ := fun i => (next (Sq i)).sZ
      f := fun i => match i with
        | 0 => (next (Sq 0)).f
        | j + 1 => (next (Sq (j + 1))).f
      gZ := fun i => (next (Sq i)).g
      fp := fun i => (next (Sq i)).fp
      φ := fun i => match i with
        | 0 => (next (Sq 0)).φ
        | j + 1 => (next (Sq (j + 1))).φ
      isRelativeDltModel := fun i _ => match i with
        | 0 => h.isRelativeDltModel
        | j + 1 => (Sq (j + 1)).good.isRelativeDltModel
      isElementaryDltStep := fun i hi => match i, hi with
        | 0, hi => (next_isStep (Sq 0) (hstep 0 hi)).1
        | j + 1, hi => (next_isStep (Sq (j + 1)) (hstep (j + 1) hi)).1
      BY_eq := fun i hi => match i, hi with
        | 0, hi => (next_isStep (Sq 0) (hstep 0 hi)).2
        | j + 1, hi => (next_isStep (Sq (j + 1)) (hstep (j + 1) hi)).2
      hasFinal := (Sq nn.toNat).HasFibre
      finalRay := (finalAt nn.toNat).R
      T := (finalAt nn.toNat).T
      sT := (finalAt nn.toNat).sT
      gT := (finalAt nn.toNat).gT
      g := (finalAt nn.toNat).g
      final_spec := fun hF => by
        refine ⟨fun htop => ?_, hfinalAt _ hF⟩
        have hex : ∃ i, (Sq i).Stops := ⟨_, Or.inr hF⟩
        have : nn = Nat.find hex := dif_pos hex
        rw [this] at htop
        exact ENat.coe_ne_top _ htop }
  have hP : P.IsProjective := by
    refine ⟨h.isProjectiveVariety_base, fun i _ => ?_⟩
    rcases i with _ | j
    · exact h.isProjectiveVariety
    · exact (Sq (j + 1)).good.isProjectiveVariety
  have hn : P.n ≠ ⊤ := h.n_ne_top P hP
  have hex : ∃ i, (Sq i).Stops := by
    by_contra hex
    exact hn (dif_neg hex)
  refine ⟨P, hP, hn, ?_⟩
  have hnn : P.n = Nat.find hex := dif_pos hex
  have hs : (Sq (Nat.find hex)).Stops := Nat.find_spec hex
  have htoNat : P.n.toNat = Nat.find hex := by rw [hnn]; rfl
  rcases hs with hnef | hF
  · left
    rw [htoNat]
    generalize Nat.find hex = m at hnef ⊢
    rcases m with _ | m
    · exact hnef
    · exact hnef
  · right
    change (Sq nn.toNat).HasFibre
    have : nn.toNat = Nat.find hex := htoNat
    rw [this]
    exact hF

end Existence

private theorem solution : MMP.Fourfold.ProjectiveLowerLogMMP 3 := by
  refine ⟨by norm_num, ?_⟩
  intro X S _ _ _ _ sX sS π K B hX hS hπ hdim hQ hK hdlt
  have h : Good sX sS π K B := ⟨hX, hS, hπ, by exact_mod_cast hdim, hQ, hK, hdlt⟩
  refine ⟨fun R hR => ?_, fun P hP => h.n_ne_top P hP, h.exists_program⟩
  obtain ⟨Z, sZ, f, g, hc⟩ := h.exists_contraction hR
  refine ⟨Z, sZ, f, g, hc, (h.absolute hc).1, fun hs => ?_⟩
  obtain ⟨X', _, _, _, _, sX', fp, φ, hX', hflip, -⟩ := h.exists_flip hc hs
  exact ⟨X', _, _, _, sX', fp, φ, hX', hflip⟩

end Proof_thm_mmp_threefold_log_mmp

end

namespace MMP.Fourfold

/-- **The projective three-dimensional rational log minimal model program.** The property
`ProjectiveLowerLogMMP 3` holds: in dimension at most three, negative extremal rays of
projective rational `ℚ`-factorial dlt pairs have contractions and, when small, flips, and every
projective elementary dlt program terminates. -/
@[mmp "thm_mmp_threefold_log_mmp"]
public theorem projectiveLowerLogMMP_three : ProjectiveLowerLogMMP 3 :=
  by first | exact Proof_thm_mmp_threefold_log_mmp.solution | exact Proof_thm_mmp_threefold_log_mmp.solution _ | exact Proof_thm_mmp_threefold_log_mmp.solution _ _ | exact Proof_thm_mmp_threefold_log_mmp.solution _ _ _ | exact Proof_thm_mmp_threefold_log_mmp.solution _ _ _ _

end MMP.Fourfold
