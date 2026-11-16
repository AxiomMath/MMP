module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.AmpleModelSmall
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModelGraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.GoodOverContraction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Contraction.LcRay
public import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelBirational
public import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelAdjointAmple
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.Divisor.FloorSectionAlgebraFG
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra
public import MMP.AlgebraicGeometry.Cohomology.FormalFunctionsDegreeZero
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Continuation of the program through every birational contraction

Let `(X, B)` be a projective log canonical fourfold pair over `ℂ` with rational boundary, `K` a
canonical divisor, `D = K + B`, `R` a `D`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Z` the
contraction of `R`, assumed birational. Then the program can always be continued at `f`: there
is a small projective birational morphism `f⁺ : X⁺ ⟶ Z` (possibly an isomorphism) such that
`(X⁺, B⁺, f⁺)`, with `B⁺` the strict transform of `f_* B`, is a permitted step for
`(X, B, R, f)`. The model `X⁺` is the relative ample model over `Z` of a log minimal model of
`(X/Z, B)` whose log canonical divisor is semiample over `Z`.

## Main results

* `MMP.Fourfold.IsContractionOfRay.exists_isPermittedStep`: every birational contraction of a
  `(K + B)`-negative extremal ray of a projective lc fourfold pair over `ℂ` admits a permitted
  step.

## Implementation notes

The contraction `f` is only assumed to be a contraction of `R` in the sense of
`MMP.Fourfold.IsContractionOfRay` (a projective surjective morphism of normal varieties with
`f_* 𝒪_X = 𝒪_Z` contracting exactly the curves with class in `R`). That `Z` is projective,
`ρ(X/Z) = 1` and `-D` is `f`-ample are part of the conclusion, as fields of
`MMP.Fourfold.IsPermittedStep`. The boundary `B⁺` is not a separate witness: in
`MMP.Fourfold.IsPermittedStep` it is pinned to the strict transform `flipTransform f f⁺ B`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite MMP.Mori MMP.Fourfold

universe u

namespace Proof_prop_oai4_continuation

/-- Pull-backs along `f' ≫ g` of invertible sheaves are pull-backs along `f'`, so
`f^* N¹(Z)_ℝ ⊆ f'^* N¹(Z')_ℝ` when `f = f' ≫ g`. -/
private theorem pullbackNumericalClasses_le_of_comp_eq {X Z Z' : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    {f : X ⟶ Z} {f' : X ⟶ Z'} {g : Z' ⟶ Z} (h : f' ≫ g = f) :
    pullbackNumericalClasses sX f ≤ pullbackNumericalClasses sX f' := by
  refine Submodule.span_mono ?_
  rintro d ⟨E, M, hM, ⟨i⟩, rfl⟩
  exact ⟨E, (Scheme.Modules.pullback g).obj M,
    Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback g M,
    ⟨i ≪≫ (Scheme.Modules.pullbackCongr h.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp f' g).app M).symm⟩, rfl⟩

/-- Relative ampleness over `Z'` along `f ≫ e`, for an isomorphism `e : Z ⟶ Z'`, is relative
ampleness over `Z` along `f`. -/
private theorem isRelativelyAmple_of_comp_isIso {X Z Z' : Scheme.{0}} (f : X ⟶ Z) (e : Z ⟶ Z')
    [IsIso e] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (h : MMP.Mori.IsRelativelyAmple (f ≫ e) L) : MMP.Mori.IsRelativelyAmple f L := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h (e y)
  exact ⟨e ⁻¹ᵁ V, hV.preimage_of_isIso e, hyV, hA⟩

/-- **Two contractions of one extremal ray have isomorphic targets.** If `f : X ⟶ Z` and
`f' : X ⟶ Z'` both contract the extremal ray `R`, the comparison `a : Z ⟶ Z'` with `f ≫ a = f'`
is an isomorphism: its inverse is the comparison the other way, by uniqueness of factorizations
through a contraction. -/
private theorem isIso_of_isContractionOfRay {X Z Z' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sZ' : Z' ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) {f' : X ⟶ Z'}
    (hf' : IsContractionOfRay sX sZ' R f') {a : Z ⟶ Z'} (ha : f ≫ a = f') : IsIso a := by
  have hc : ∀ {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {g : X ⟶ W},
      IsContractionOfRay sX sW R g → ∀ C : ProperCurve sX,
        OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.IsContractedBy g :=
    fun hg C hC => (hg.isContractedBy_iff C).mpr hC
  have hu : ∀ {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {g : X ⟶ W},
      IsContractionOfRay sX sW R g → ∀ e : W ⟶ W, g ≫ e = g → e = 𝟙 W := fun hg e he => by
    obtain ⟨c, -, hu⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hg.isProjectiveMorphism
      hg.comp_eq hR (hc hg) hg
    exact (hu e he).trans (hu _ (Category.comp_id _)).symm
  obtain ⟨b, hb, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR (hc hf) hf'
  exact ⟨⟨b, hu hf _ (by rw [← Category.assoc, ha, hb]),
    hu hf' _ (by rw [← Category.assoc, hb, ha])⟩⟩

/-- **Comparison with the contraction of the ray.** Two contractions `f : X ⟶ Z`,
`f' : X ⟶ Z'` of the same extremal ray `R` of a projective variety differ by an isomorphism of
targets over `ℂ`, so the projectivity of `Z'`, `ρ(X/Z') = 1` and the `f'`-ampleness of a divisor
pass to `f`. -/
private theorem contraction_data_of_isContractionOfRay {X Z Z' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sZ' : Z' ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) {f' : X ⟶ Z'}
    (hf' : IsContractionOfRay sX sZ' R f') (hZ' : MMP.Mori.IsProjectiveVariety ℂ sZ')
    (hρ : relativePicardNumberN1 sX f' = 1) {D : QDivisor X}
    (hamp : D.HasRelativelyAmpleMultiple f') :
    MMP.Mori.IsProjectiveVariety ℂ sZ ∧ relativePicardNumberN1 sX f = 1 ∧
      D.HasRelativelyAmpleMultiple f := by
  obtain ⟨a, ha, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf'.isProjectiveMorphism
    hf'.comp_eq hR (fun C hC => (hf'.isContractedBy_iff C).mpr hC) hf
  have : IsIso a := isIso_of_isContractionOfRay hX hR hf hf' ha
  have hsZ : sZ = a ≫ sZ' := by
    have : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
    have : IsIso f.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ f.c fun U => hf.isIso_app U.unop
    obtain ⟨t, -, hs⟩ := MMP.existsUnique_comp_eq_of_isIso_c f sX
      fun _ _ _ => Subsingleton.elim _ _
    exact (hs _ hf.comp_eq).trans (hs _ (show f ≫ a ≫ sZ' = sX by rw [← Category.assoc, ha, hf'.comp_eq])).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [MMP.Mori.isProjectiveVariety_iff]
    refine ⟨hf.isNormalVariety_target.1, ?_⟩
    obtain ⟨n, i, hi, hif⟩ := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ').mp hZ').2
    exact ⟨n, a ≫ i, inferInstance, by rw [hsZ, Category.assoc, hif]⟩
  · rw [← hρ, relativePicardNumberN1, relativePicardNumberN1,
      le_antisymm (pullbackNumericalClasses_le_of_comp_eq sX ha)
        (pullbackNumericalClasses_le_of_comp_eq sX
          (show f' ≫ inv a = f by rw [← ha, Category.assoc, IsIso.hom_inv_id, Category.comp_id]))]
  · obtain ⟨m, hm, L, hL, hLD, hLa⟩ := hamp
    refine ⟨m, hm, L, hL, hLD, ?_⟩
    have := hL.isInvertibleModule_divisorialSheaf
    exact isRelativelyAmple_of_comp_isIso f a _ (ha ▸ hLa)

/-- The contraction `f` has projective target, relative Picard number one and `-D` `f`-ample. -/
private theorem contraction_data {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) :
    MMP.Mori.IsProjectiveVariety ℂ sZ ∧ relativePicardNumberN1 sX f = 1 ∧
      (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f := by
  obtain ⟨Z', sZ', f', hf', hZ', hρ, hamp⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf sX hX hdim hK hB hR
  exact contraction_data_of_isContractionOfRay hX hR.2.1 hf hf' hZ' hρ hamp

section Semiample

section Orders

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- The generic point of `Y` specializes to the generic point of the component `Z`. -/
private theorem specializes_genericPoint (Z : irreducibleComponents Y) :
    componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

/-- The generic point of the component `Z` specializes to the generic point of `Y`. -/
private theorem genericPoint_specializes (Z : irreducibleComponents Y) :
    genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private noncomputable def toRationalFunctions : Y.functionField →+* RationalFunctions Y :=
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

/-- The component of the image of a rational function at `Z` is its specialization. -/
private theorem stalkSpecializes_toRationalFunctions (Z : irreducibleComponents Y)
    (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

variable [IsLocallyNoetherian Y] [IsNormal Y]

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

end Orders

/-! #### Relatively free Cartier divisors -/

section RelativelyFree

/-- **Local equations of a relatively free Cartier divisor.** Let `E` be a Cartier divisor with
Weil divisor `B` on a normal integral locally Noetherian scheme, `f`-free for `f : Y ⟶ Z`. Every
`x ∈ Y` has an open `U' ∋ f(x)` and a unit `ψ` of `K(Y)` with `B + div ψ` effective on `f⁻¹U'`
and zero along every prime divisor through `x`: `ψ` is a section of `𝒪_Y(E)` over `f⁻¹U'`
generating it at `x`. -/
private theorem exists_isLocalEquation_of_isRelativelyFreeCartier {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Z) {E : Y.CartierDivisor}
    {B : Divisor Y} (hEB : MMP.Intersection.IsWeilDivisorOfCartier E B)
    (hfree : IsRelativelyFreeCartier f E)
    (x : Y) : ∃ (U' : Z.Opens) (_ : f x ∈ U') (ψ : (RationalFunctions Y)ˣ),
      (∀ P : MMP.Mori.PrimeDivisor Y, (P.support ∩ f ⁻¹ᵁ U').Nonempty →
        0 ≤ B.coeff P + P.ord ψ) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, x ∈ P.support → B.coeff P + P.ord ψ = 0 := by
  classical
  set L := MMP.CartierDivisor.sheaf E
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hepiL : Epi (adj.counit.app L) := by
    have hnat := adj.counit.naturality (Iso.refl (MMP.CartierDivisor.sheaf E)).hom
    have heq : adj.counit.app L = (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map
        (Iso.refl (MMP.CartierDivisor.sheaf E)).hom ≫
          adj.counit.app (MMP.CartierDivisor.sheaf E) ≫
          (Iso.refl (MMP.CartierDivisor.sheaf E)).inv := by
      rw [← Category.assoc, hnat, Functor.id_map, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have hE : Epi (adj.counit.app (MMP.CartierDivisor.sheaf E)) := hfree
    rw [heq]
    infer_instance
  have : Epi ((adj.homEquiv ((Scheme.Modules.pushforward f).obj L) L).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj L))) := by
    rw [Stacks.Tag01VMVeryAmple.homEquiv_symm_id]; exact hepiL
  obtain ⟨V', -, bsec, hxb⟩ := Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint
    f (𝟙 ((Scheme.Modules.pushforward f).obj L)) x
  set W' := f ⁻¹ᵁ V' with hW'
  let b : Γ(L, W') := bsec
  have hxb' : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L W' b := hxb
  obtain ⟨hxW', hgerm⟩ := hxb'
  set σ := MMP.CartierDivisorSheaf.sectionVal b
  -- a local equation of `E` at `x`, and `σ = r g⁻¹` with `r` a unit at `x`
  obtain ⟨U, hxU, g, hg⟩ := MMP.Intersection.exists_isLocalEquationOn E x
  set U1 := U ⊓ W'
  have hxU1 : x ∈ U1 := ⟨hxU, hxW'⟩
  have hg1 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE (inf_le_left : U1 ≤ U)) hg
  set g1 := MMP.Intersection.resUnit (homOfLE (inf_le_left : U1 ≤ U)) g
  set b1 : Γ(L, U1) := L.presheaf.map (homOfLE (inf_le_right : U1 ≤ W')).op b with hb1
  obtain ⟨r, hr⟩ := (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg1
      (MMP.CartierDivisorSheaf.sectionVal b1)).1
    (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b1)
  have hb1r : b1 = r • MMP.CartierDivisor.invSection hg1 := by
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    exact hr.symm
  have hru : IsUnit (Y.presheaf.germ U1 x hxU1 r) := by
    by_contra hnu
    apply hgerm
    have h1 : L.presheaf.germ W' x hxW' b = L.presheaf.germ U1 x hxU1 b1 := by
      rw [hb1]
      exact (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) L.presheaf
        (homOfLE (inf_le_right : U1 ≤ W')) x hxU1 b).symm
    rw [h1, hb1r, Stacks.ModuleStalk.germ_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  -- on `U2 = D(r)` the section `σ` is a unit of `𝓜_Y`
  set U2 := Y.basicOpen r
  have hU21 : U2 ≤ U1 := Y.basicOpen_le r
  have hU2W : U2 ≤ W' := hU21.trans inf_le_right
  have hxU2 : x ∈ U2 := (Scheme.mem_basicOpen Y r x hxU1).mpr hru
  set r2 : Γ(Y, U2) := Y.presheaf.map (homOfLE hU21).op r
  have hr2 : IsUnit r2 := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace r
  have hg2 := MMP.Intersection.isLocalEquationOn_resUnit (homOfLE hU21) hg1
  set g2 := MMP.Intersection.resUnit (homOfLE hU21) g1
  set σ2 := Y.totalQuotientSheaf.obj.map (homOfLE hU2W).op σ
  have hσ2 : σ2 = MMP.Intersection.toTotalQuotient U2 r2 * ((g2⁻¹ : _ˣ) : _) := by
    have h := congrArg (Y.totalQuotientSheaf.obj.map (homOfLE hU21).op) hr
    rw [map_mul, ← MMP.Intersection.toTotalQuotient_res] at h
    refine Eq.trans ?_ h.symm
    erw [hb1, MMP.CartierDivisorSheaf.sectionVal_map, MMP.Intersection.totalQuotient_map_map]
    rfl
  have hσ2u : IsUnit σ2 := by
    rw [hσ2]
    exact (hr2.map (MMP.Intersection.toTotalQuotient U2)).mul (Units.isUnit _)
  -- the rational function `φ` of `σ`
  set ξ := genericPoint Y
  have hξ : ∀ (O : Y.Opens) (y : Y), y ∈ O → ξ ∈ O := fun O y hy =>
    ((genericPoint_spec Y).specializes trivial : ξ ⤳ y).mem_open O.isOpen hy
  have hξW' : ξ ∈ W' := hξ W' x hxW'
  set φ := totalQuotientStalkToFunctionField ξ (Y.totalQuotientSheaf.presheaf.germ W' ξ hξW' σ)
  have hσgerm : ∀ (y : Y) (hy : y ∈ W'), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ W' y hy σ) = φ := by
    intro y hy
    have hsp : ξ ⤳ y := (genericPoint_spec Y).specializes trivial
    rw [← MMP.Intersection.totalQuotientStalkToFunctionField_stalkSpecializes hsp,
      TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hσ2germ : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy σ2) = φ := by
    intro y hy
    rw [TopCat.Presheaf.germ_res_apply]
    exact hσgerm y (hU2W hy)
  have hφ : φ ≠ 0 := by
    rw [← hσ2germ x hxU2]
    exact ((hσ2u.map (Y.totalQuotientSheaf.presheaf.germ U2 x hxU2).hom).map
      (totalQuotientStalkToFunctionField x).hom).ne_zero
  -- `B + div φ ≥ 0` on `W'`
  have : Nonempty W' := ⟨⟨x, hxW'⟩⟩
  have hge := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hEB W' hφ σ
    hσgerm).1 (MMP.CartierDivisor.sectionVal_mem_lineBundleSections b)
  -- `-B + div φ⁻¹ ≥ 0` on `U2`, as `σ⁻¹` is a section of `𝒪_Y(-E)` there
  have hnegEB : MMP.Intersection.IsWeilDivisorOfCartier (-E) (-B) := fun P => by
    have h := MMP.Intersection.isOrderAlong_primeDivisorOrder (-E) P
    rwa [map_neg, (hEB P).primeDivisorOrder_eq, ← DivisorWithCoeffs.coeff_neg] at h
  set τ : Y.totalQuotientSheaf.obj.obj (op U2) := (hσ2u.unit⁻¹).val
  have hτσ : τ * σ2 = 1 := hσ2u.val_inv_mul
  have hτmem : τ ∈ MMP.Intersection.lineBundleSections (-E) U2 := by
    refine (MMP.Intersection.mem_lineBundleSections_iff_of_isLocalEquationOn' hg2.inv τ).2
      ⟨((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)), ?_⟩
    rw [inv_inv]
    have h1 : MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
        MMP.Intersection.toTotalQuotient U2 r2 = 1 := by
      rw [← map_mul, hr2.val_inv_mul, map_one]
    calc _ = (MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) * (g2 : _)) *
          (σ2 * τ) := by rw [mul_comm σ2 τ, hτσ, mul_one]
      _ = τ * ((MMP.Intersection.toTotalQuotient U2 ((hr2.unit⁻¹ : _ˣ) : Γ(Y, U2)) *
          MMP.Intersection.toTotalQuotient U2 r2) * ((g2 : _) * ((g2⁻¹ : _ˣ) : _))) := by
            rw [hσ2]; ring
      _ = τ := by rw [h1, Units.mul_inv, mul_one, mul_one]
  have hτgerm : ∀ (y : Y) (hy : y ∈ U2), totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy τ) = φ⁻¹ := by
    intro y hy
    have h := congrArg (fun t => totalQuotientStalkToFunctionField y
      (Y.totalQuotientSheaf.presheaf.germ U2 y hy t)) hτσ
    simp only [map_mul, map_one, hσ2germ y hy] at h
    exact eq_inv_of_mul_eq_one_left h
  have : Nonempty U2 := ⟨⟨x, hxU2⟩⟩
  have hle := (MMP.Intersection.mem_lineBundleSections_iff_forall_zero_le_ord_add hnegEB U2
    (inv_ne_zero hφ) τ hτgerm).1 hτmem
  have hordinv : ∀ y : Y, Scheme.ord φ⁻¹ y = -Scheme.ord φ y := fun y => by
    have h := Scheme.ord_mul (x := y) hφ (inv_ne_zero hφ)
    rw [mul_inv_cancel₀ hφ, Scheme.ord_one] at h
    omega
  -- the unit `ψ` of `K(Y)`
  let ψ : (RationalFunctions Y)ˣ :=
    ⟨toRationalFunctions φ, toRationalFunctions φ⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hφ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hφ, map_one]⟩
  have hψ : ∀ P : MMP.Mori.PrimeDivisor Y, P.ord ψ = Scheme.ord φ P.genericPoint :=
    fun P => ord_toRationalFunctions P hφ ψ rfl
  refine ⟨V', hxW', ψ, fun P hP => ?_, fun P hxP => ?_⟩
  · rw [hψ, add_comm]
    exact hge P hP
  · have h1 := hge P ⟨x, hxP, hxW'⟩
    have h2 := hle P ⟨x, hxP, hxU2⟩
    rw [hordinv, DivisorWithCoeffs.coeff_neg] at h2
    rw [hψ]
    omega

end RelativelyFree

/-! #### The Weil divisor of a Cartier divisor -/

section Weil

open MMP.Intersection

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{u}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Weil

/-- A `ℚ`-divisor semiample over `Z` has a positive multiple which is a Cartier divisor generated
over `Z`. -/
private theorem exists_isRelativelyFreeDivisor_of_isRelativelySemiample {M Z : Scheme.{u}}
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z}
    {L : QDivisor M} (hL : QDivisor.IsRelativelySemiample π L) :
    ∃ k : ℕ, 0 < k ∧ ∃ D : Divisor M, Divisor.toQDivisor D = (k : ℚ) • L ∧ D.IsCartier ∧
      IsRelativelyFreeDivisor π D := by
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hL
  have : IsNoetherian M := {}
  obtain ⟨B, hEB⟩ := exists_isWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) hint)
  refine ⟨q, hq, B, ?_, hEB.isCartier, isRelativelyFreeDivisor_of_forall_exists π fun x => ?_⟩
  · refine Finsupp.ext fun P => ?_
    change (Divisor.toQDivisor B).coeff P = ((q : ℚ) • L).coeff P
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hEB P]
  · exact exists_isLocalEquation_of_isRelativelyFreeCartier π hEB hfree x

end Semiample

section PushforwardAlgebra

variable {M Z : Scheme.{0}} [IsLocallyNoetherian M] [IsNormal M] (π : M ⟶ Z) (D : Divisor M)

/-- The degree-`n` piece `π_* 𝒪_M(nD)` (zero in negative degrees). -/
private noncomputable def pushPiece (n : ℤ) : Z.Modules :=
  (Scheme.Modules.pushforward π).obj (Divisor.sectionAlgebraPiece D n)

/-- The multiplication `π_* 𝒪_M(iD) × π_* 𝒪_M(jD) → π_* 𝒪_M((i + j)D)`. -/
private noncomputable def pushMul (i j : ℤ) :
    SheafOfModules.BilinearMap (pushPiece π D i) (pushPiece π D j) (pushPiece π D (i + j)) where
  app U := (Divisor.sectionAlgebraMul D i j).app (op (π ⁻¹ᵁ U.unop))
  map_smul_left U r x y := (Divisor.sectionAlgebraMul D i j).map_smul_left _ (π.app U.unop r) x y
  map_smul_right U r x y :=
    (Divisor.sectionAlgebraMul D i j).map_smul_right _ (π.app U.unop r) x y
  naturality f x y := (Divisor.sectionAlgebraMul D i j).naturality _ x y

/-- The unit of `⨁_n π_* 𝒪_M(nD)`. -/
private noncomputable def pushOne : (pushPiece π D 0).sections :=
  ⟨fun U => (Divisor.sectionAlgebraOne D).eval (op (π ⁻¹ᵁ U.unop)),
    fun _ => (Divisor.sectionAlgebraOne D).2 _⟩

/-- The sheaf of graded `𝒪_Z`-algebras `⨁_{n ≥ 0} π_* 𝒪_M(nD)`. -/
private noncomputable def pushAlgebra : SheafOfModules.GradedAlgebra Z.ringCatSheaf where
  piece := pushPiece π D
  mul := pushMul π D
  one := pushOne π D
  mul_assoc i j k U x y z :=
    (Divisor.sectionGradedAlgebra D).mul_assoc i j k (op (π ⁻¹ᵁ U.unop)) x y z
  one_mul i U x := (Divisor.sectionGradedAlgebra D).one_mul i (op (π ⁻¹ᵁ U.unop)) x
  mul_one i U x := (Divisor.sectionGradedAlgebra D).mul_one i (op (π ⁻¹ᵁ U.unop)) x

/-- `⨁_{n ≥ 0} π_* 𝒪_M(nD)` as a divisorial section algebra of `D` along `π`. -/
private noncomputable def pushSectionAlgebra [CompactSpace M] [QuasiCompact π]
    [QuasiSeparated π] : DivisorialSectionAlgebra π D where
  algebra := pushAlgebra π D
  mul_comm i j U a b := Divisor.sectionGradedAlgebra_mul_comm D i j (op (π ⁻¹ᵁ U.unop)) a b
  negative_isZero n hn :=
    (Scheme.Modules.pushforward π).map_isZero (Divisor.isZero_sectionAlgebraPiece_of_neg D n hn)
  isQuasicoherent _ :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs π _
  sectionEquiv i hi U := Divisor.sectionAlgebraEquiv D i hi (π ⁻¹ᵁ U)
  sectionEquiv_restrict i hi U V h a := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rfl
  sectionEquiv_smul i hi U r a := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rfl
  sectionEquiv_mul i j hi hj U a b := by
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rfl
  sectionEquiv_one U := rfl

end PushforwardAlgebra

section InducedMorphism

variable {M Z : Scheme.{0}} [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} {D : Divisor M}
  (A : DivisorialSectionAlgebra π D)

/-- Sections of equal degrees which are `HEq` have the same rational function. -/
private theorem sectionEquiv_heq {i j : ℤ} (h : i = j) (hi : 0 ≤ i) (hj : 0 ≤ j) (U : Z.Opens)
    (a : (A.algebra.piece i).val.obj (op U)) (b : (A.algebra.piece j).val.obj (op U))
    (hab : HEq a b) :
    (A.sectionEquiv i hi U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      (A.sectionEquiv j hj U b : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  subst h; cases hab; rfl

/-- A homogeneous section lies in its homogeneous piece of the section ring. -/
private theorem of_mem {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n) :
    DirectSum.of (A.situation.sectionPieces U) n a ∈ A.situation.sectionRingGrading U n :=
  ⟨a, rfl⟩

/-- The rational function of a homogeneous section of degree `n`. -/
private noncomputable def pieceEval (U : Z.Opens) (n : ℕ) :
    A.situation.sectionPieces U n →+ (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)) :=
  ((((n : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ U)).subtype.toAddMonoidHom.comp
      (A.sectionEquiv n (Int.natCast_nonneg n) U).toAddMonoidHom)

/-- The total evaluation `⨁_n 𝒜_n(U) → 𝒦_M(π⁻¹U)`, adding the rational functions of the
homogeneous components. -/
private noncomputable def evalK (U : Z.Opens) :
    A.situation.sectionRing U →+* (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)) :=
  DirectSum.toSemiring (pieceEval A U) (by
      have h1 := (A.situation.sectionRingStructure.one_homogeneous U)
      change ((A.sectionEquiv 0 le_rfl U
        (GradedMonoid.GOne.one : A.situation.sectionPieces U 0) :
          (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) = 1
      rw [h1, A.sectionEquiv_one])
    (by
      intro i j a b
      change ((A.sectionEquiv _ _ U _ : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) =
        (A.sectionEquiv _ _ U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) *
        (A.sectionEquiv _ _ U b : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
      rw [← A.sectionEquiv_mul i j (Int.natCast_nonneg i) (Int.natCast_nonneg j) U a b]
      exact sectionEquiv_heq A (by push_cast; rfl) _ _ U _ _
        (A.situation.sectionRingStructure.mul_homogeneous U i j a b))

/-- The total evaluation of a homogeneous section is its rational function. -/
private theorem evalK_of (U : Z.Opens) (n : ℕ) (a : A.situation.sectionPieces U n) :
    evalK A U (DirectSum.of _ n a) =
      (A.sectionEquiv n (Int.natCast_nonneg n) U a :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  simp only [evalK, DirectSum.toSemiring_of]
  rfl

/-- On the generating locus of `a`, the restriction of `a` is a unit of `𝒦_M`. -/
private theorem isUnit_generatingLocus {i : ℤ} (hi : 0 ≤ i) {U : Z.Opens}
    (a : (A.algebra.piece i).val.obj (op U)) :
    IsUnit ((rationalFunctionsPresheaf M).map (homOfLE (A.generatingLocus_le hi a)).op
      (A.sectionEquiv i hi U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) := by
  refine Pi.isUnit_iff.mpr ?_
  rintro ⟨Zc, hZc⟩
  obtain ⟨W, ⟨hWU, b, -, hab⟩, hW⟩ := TopologicalSpace.Opens.mem_sSup.mp hZc
  have := congrFun hab ⟨Zc, hW⟩
  exact ⟨⟨_, _, this, by rw [mul_comm]; exact this⟩, rfl⟩

/-- The lift of `g` along a localization away from `f` takes `t / fᵐ` to `g(t) g(f)⁻ᵐ`. -/
private theorem lift_mk_mul_pow {R P : Type*} [CommRing R] [CommRing P] (f : R) (g : R →+* P)
    (hg : IsUnit (g f)) (t : R) (m : ℕ) :
    IsLocalization.Away.lift f hg
        (Localization.mk t (⟨f ^ m, m, rfl⟩ : Submonoid.powers f) : Localization.Away f) *
      g f ^ m = g t := by
  have h := congrArg (IsLocalization.Away.lift f hg)
    (IsLocalization.mk'_spec (Localization.Away f) t (⟨f ^ m, m, rfl⟩ : Submonoid.powers f))
  rw [map_mul, IsLocalization.Away.lift, IsLocalization.lift_eq, IsLocalization.lift_eq,
    map_pow] at h
  rw [Localization.mk_eq_mk']
  exact h

/-- The lift along a localization away from `f` takes `y / 1` to `g(y)`. -/
private theorem lift_mk_one {R P : Type*} [CommRing R] [CommRing P] (f : R) (g : R →+* P)
    (hg : IsUnit (g f)) (y : R) :
    IsLocalization.Away.lift f hg (Localization.mk y 1 : Localization.Away f) = g y := by
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift, IsLocalization.lift_eq]

/-- The map `𝒜(U)_(a) → 𝒦_M(M_a)`, `t / aᵐ ↦ t a⁻ᵐ`. -/
private noncomputable def psiK {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n) :
    HomogeneousLocalization.Away (A.situation.sectionRingGrading U) (DirectSum.of _ n a) →+*
      (rationalFunctionsPresheaf M).obj
        (op (A.generatingLocus (Int.natCast_nonneg n) a)) :=
  (IsLocalization.Away.lift (DirectSum.of _ n a)
      (g := ((rationalFunctionsPresheaf M).map
        (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op).hom.comp (evalK A U))
      (by
        rw [RingHom.comp_apply, evalK_of]
        exact isUnit_generatingLocus A _ a)).comp
    (algebraMap _ (Localization.Away (DirectSum.of (A.situation.sectionPieces U) n a)))

/-- `ψ̃_a(y / aᵐ) aᵐ = y` in `𝒦_M(M_a)`. -/
private theorem psiK_mk' {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n) (m : ℕ)
    (y : A.situation.sectionRing U) (hy : y ∈ A.situation.sectionRingGrading U (m • n)) :
    psiK A a (HomogeneousLocalization.Away.mk _ ⟨a, rfl⟩ m y hy) *
        (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op
          (evalK A U (DirectSum.of _ n a)) ^ m =
      (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op (evalK A U y) :=
  lift_mk_mul_pow (DirectSum.of (A.situation.sectionPieces U) n a)
    (((rationalFunctionsPresheaf M).map
        (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op).hom.comp (evalK A U))
    (by rw [RingHom.comp_apply, evalK_of]; exact isUnit_generatingLocus A _ a) y m

/-- `ψ̃_a(t / aᵐ) aᵐ = t` in `𝒦_M(M_a)`, for a homogeneous section `t`. -/
private theorem psiK_mk {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n) (m : ℕ)
    (t : A.situation.sectionPieces U (m • n)) :
    psiK A a (HomogeneousLocalization.Away.mk _ ⟨a, rfl⟩ m (DirectSum.of _ (m • n) t) ⟨t, rfl⟩) *
        (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op
          (A.sectionEquiv n (Int.natCast_nonneg n) U a :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ^ m =
      (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op
          (A.sectionEquiv _ (Int.natCast_nonneg _) U t :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  have := psiK_mk' A a m _ ⟨t, rfl⟩
  rwa [evalK_of, evalK_of] at this

/-- On the generating locus `M_a`, the rational functions `t a⁻ᵐ` are sections of `𝒪_M(0)`. -/
private theorem isDivisorialSection_psiK {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n)
    (x : HomogeneousLocalization.Away (A.situation.sectionRingGrading U) (DirectSum.of _ n a)) :
    (0 : Divisor M).IsDivisorialSection (A.generatingLocus (Int.natCast_nonneg n) a)
      (psiK A a x) := by
  obtain ⟨m, y, hy, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (A.situation.sectionRingGrading U) (of_mem A a) x
  obtain ⟨t, rfl⟩ := hy
  intro E hE
  obtain ⟨y, hyE, hyW⟩ := hE
  obtain ⟨W, ⟨hWU, b, hb, hab⟩, hyW'⟩ := TopologicalSpace.Opens.mem_sSup.mp hyW
  have hEW : (E.support ∩ W).Nonempty := ⟨y, hyE, hyW'⟩
  have hEU : (E.support ∩ π ⁻¹ᵁ U).Nonempty := ⟨y, hyE, hWU hyW'⟩
  set c : ↥(irreducibleComponents M) := E.component
  have hcW := E.componentGenericPoint_mem_of_nonempty hEW
  have hcL := E.componentGenericPoint_mem_of_nonempty
    (⟨y, hyE, hyW⟩ : (E.support ∩ A.generatingLocus (Int.natCast_nonneg n) a).Nonempty)
  have hcU := E.componentGenericPoint_mem_of_nonempty hEU
  have h1 := congrFun (psiK_mk A a m t) ⟨c, hcL⟩
  have h2 := congrFun hab ⟨c, hcW⟩
  change _ * (A.sectionEquiv n (Int.natCast_nonneg n) U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
    ⟨c, hcU⟩ ^ m = (A.sectionEquiv _ (Int.natCast_nonneg _) U t : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
    ⟨c, hcU⟩ at h1
  change (A.sectionEquiv n (Int.natCast_nonneg n) U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
    ⟨c, hcU⟩ * b ⟨c, hcW⟩ = 1 at h2
  have hφ : psiK A a (HomogeneousLocalization.Away.mk _ ⟨a, rfl⟩ m
      (DirectSum.of _ (m • n) t) ⟨t, rfl⟩) ⟨c, hcL⟩ =
      (A.sectionEquiv _ (Int.natCast_nonneg _) U t : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨c, hcU⟩ *
        b ⟨c, hcW⟩ ^ m := by
    rw [← h1, mul_assoc, ← mul_pow, h2, one_pow, mul_one]
  rw [hφ]
  have ht := (A.sectionEquiv _ (Int.natCast_nonneg (m • n)) U t).2 E hEU
  have hb' := (hb E hEW).pow m
  convert ht.mul hb' using 1
  simp only [DivisorWithCoeffs.coeff_zero, neg_zero, DivisorWithCoeffs.coeff_neg,
    DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  push_cast
  ring

/-- The ring map `ψ_a : 𝒜(U)_(a) → 𝒪_M(M_a)`, `t / aᵐ ↦ t a⁻ᵐ`. -/
private noncomputable def psi [IsIntegral M] {U : Z.Opens} {n : ℕ}
    (a : A.situation.sectionPieces U n) :
    HomogeneousLocalization.Away (A.situation.sectionRingGrading U) (DirectSum.of _ n a) →+*
      Γ(M, A.generatingLocus (Int.natCast_nonneg n) a) :=
  (RingEquiv.ofBijective
      ((toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))).hom.rangeRestrict
      ⟨fun s t hst => toRationalFunctionsPresheaf_app_injective _ (congrArg Subtype.val hst),
        RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((psiK A a).codRestrict _ fun x => (isDivisorialSection_psiK A a x).exists_eq)

/-- The rational function of `ψ_a(x)` is `ψ̃_a(x)`. -/
private theorem toRationalFunctions_psi [IsIntegral M] {U : Z.Opens} {n : ℕ}
    (a : A.situation.sectionPieces U n) (x) :
    (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
      (psi A a x) = psiK A a x := by
  set e := RingEquiv.ofBijective
      ((toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))).hom.rangeRestrict
      ⟨fun s t hst => toRationalFunctionsPresheaf_app_injective _ (congrArg Subtype.val hst),
        RingHom.rangeRestrict_surjective _⟩
  have := e.apply_symm_apply ((psiK A a).codRestrict _
    (fun x => (isDivisorialSection_psiK A a x).exists_eq) x)
  exact congrArg Subtype.val this

variable [IsIntegral M]

/-- Ring maps out of `𝒜(U)_(f)` into the regular functions on an open of `M` agree when they
agree on every fraction `y / fᵐ`, read in `𝒦_M`. -/
private theorem away_hom_ext {U : Z.Opens} {f : A.situation.sectionRing U} {n : ℕ}
    (hf : f ∈ A.situation.sectionRingGrading U n) {W : M.Opens}
    (φ₁ φ₂ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U) f →+* Γ(M, W))
    (h : ∀ (m : ℕ) (y : A.situation.sectionRing U)
      (hy : y ∈ A.situation.sectionRingGrading U (m • n)),
      (toRationalFunctionsPresheaf M).app (op W) (φ₁ (HomogeneousLocalization.Away.mk _ hf m y hy)) =
        (toRationalFunctionsPresheaf M).app (op W)
          (φ₂ (HomogeneousLocalization.Away.mk _ hf m y hy))) :
    φ₁ = φ₂ := by
  ext x
  obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hf x
  exact toRationalFunctionsPresheaf_app_injective _ (h m y hy)

/-- Cancellation of a power of a unit. -/
private theorem eq_of_mul_pow_eq {R : Type*} [CommRing R] {u x y t : R} (hu : IsUnit u) (m : ℕ)
    (hx : x * u ^ m = t) (hy : y * u ^ m = t) : x = y :=
  (hu.pow m).mul_left_injective (hx.trans hy.symm)

/-- `ψ_a(y / aᵐ) aᵐ = y` in `𝒦_M(M_a)`. -/
private theorem psi_spec {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n) (m : ℕ)
    (y : A.situation.sectionRing U) (hy : y ∈ A.situation.sectionRingGrading U (m • n)) :
    (toRationalFunctionsPresheaf M).app (op (A.generatingLocus (Int.natCast_nonneg n) a))
        (psi A a (HomogeneousLocalization.Away.mk _ ⟨a, rfl⟩ m y hy)) *
        (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op
          (evalK A U (DirectSum.of _ n a)) ^ m =
      (rationalFunctionsPresheaf M).map
          (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op (evalK A U y) := by
  rw [toRationalFunctions_psi]
  exact psiK_mk' A a m y hy

/-- The morphism `M_a ⟶ Proj_Z 𝒜` induced on the generating locus of a homogeneous section `a` of
positive degree over an affine open `U`: `M_a ⟶ Spec 𝒪_M(M_a) ⟶ Spec 𝒜(U)_(a) = D₊(a)`. -/
private noncomputable def qa (U : Z.affineOpens) {n : ℕ} (hn : 0 < n)
    (a : A.situation.sectionPieces U.1 n) :
    (A.generatingLocus (Int.natCast_nonneg n) a).toScheme ⟶ A.model :=
  (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (psi A a)) ≫
    Proj.awayι (A.situation.sectionRingGrading U.1) (DirectSum.of _ n a) ⟨a, rfl⟩ hn ≫
    A.situation.relativeProjChart U

/-- The rational function of a product of homogeneous sections is the product. -/
private theorem evalK_of_eq_mul {U : Z.Opens} {n k : ℕ} {a : A.situation.sectionPieces U n}
    {c : A.situation.sectionPieces U k} {p : A.situation.sectionPieces U (n + k)}
    (hp : DirectSum.of _ (n + k) p = DirectSum.of _ n a * DirectSum.of _ k c) :
    (A.sectionEquiv _ (Int.natCast_nonneg _) U p :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      (A.sectionEquiv _ (Int.natCast_nonneg _) U a :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) *
      (A.sectionEquiv _ (Int.natCast_nonneg _) U c :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) := by
  have := congrArg (evalK A U) hp
  rwa [map_mul, evalK_of, evalK_of, evalK_of] at this

/-- The total evaluation of a product of homogeneous sections is the product. -/
private theorem evalK_of_eq_mul' {U : Z.Opens} {n k : ℕ} {a : A.situation.sectionPieces U n}
    {c : A.situation.sectionPieces U k} {p : A.situation.sectionPieces U (n + k)}
    (hp : DirectSum.of _ (n + k) p = DirectSum.of _ n a * DirectSum.of _ k c) :
    evalK A U (DirectSum.of _ (n + k) p) =
      evalK A U (DirectSum.of _ n a) * evalK A U (DirectSum.of _ k c) := by
  rw [hp, map_mul]

/-- The generating locus of a product lies in the generating locus of each factor. -/
private theorem generatingLocus_le_of_eq_mul {U : Z.Opens} {n k : ℕ}
    (a : A.situation.sectionPieces U n) (c : A.situation.sectionPieces U k)
    (p : A.situation.sectionPieces U (n + k))
    (hp : DirectSum.of _ (n + k) p = DirectSum.of _ n a * DirectSum.of _ k c) :
    A.generatingLocus (Int.natCast_nonneg _) p ≤ A.generatingLocus (Int.natCast_nonneg n) a := by
  refine sSup_le_sSup ?_
  rintro W ⟨hWU, b, hb, hpb⟩
  refine ⟨hWU, (rationalFunctionsPresheaf M).map (homOfLE hWU).op
    (A.sectionEquiv _ (Int.natCast_nonneg _) U c :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) * b, ?_, ?_⟩
  · have h := ((A.sectionEquiv _ (Int.natCast_nonneg k) U c).2.map (homOfLE hWU)).mul hb
    have hD : ((k : ℤ) • D + -(((n + k : ℕ) : ℤ) • D)) = -((n : ℤ) • D) := by
      push_cast; rw [add_smul]; abel
    rw [hD] at h
    exact h
  · rw [← mul_assoc, ← map_mul, ← evalK_of_eq_mul A hp]
    exact hpb

/-- `ψ_{ac}` after `𝒜(U)_(a) → 𝒜(U)_(ac)` is `ψ_a` restricted to `M_{ac}`. -/
private theorem psi_comp_awayMap {U : Z.Opens} {n k : ℕ} (a : A.situation.sectionPieces U n)
    (c : A.situation.sectionPieces U k) (p : A.situation.sectionPieces U (n + k))
    (hp : DirectSum.of _ (n + k) p = DirectSum.of _ n a * DirectSum.of _ k c) :
    (psi A p).comp (HomogeneousLocalization.awayMap _ (of_mem A c) hp) =
      (M.presheaf.map (homOfLE (generatingLocus_le_of_eq_mul A a c p hp)).op).hom.comp
        (psi A a) := by
  have hle := generatingLocus_le_of_eq_mul A a c p hp
  have hpU := A.generatingLocus_le (Int.natCast_nonneg (n + k)) p
  set r : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)) ⟶
      (rationalFunctionsPresheaf M).obj (op (A.generatingLocus (Int.natCast_nonneg (n + k)) p)) :=
    (rationalFunctionsPresheaf M).map (homOfLE hpU).op with hr
  have hunit := isUnit_generatingLocus A (Int.natCast_nonneg (n + k)) p
  rw [← evalK_of, hp, map_mul, map_mul] at hunit
  have hu : IsUnit (r (evalK A U (DirectSum.of _ n a))) := isUnit_of_mul_isUnit_left hunit
  have hv : IsUnit (r (evalK A U (DirectSum.of _ k c))) := isUnit_of_mul_isUnit_right hunit
  refine away_hom_ext A (of_mem A a) _ _ fun m y hy => ?_
  refine eq_of_mul_pow_eq hu m (t := r (evalK A U y)) ?_ ?_
  · rw [RingHom.comp_apply, HomogeneousLocalization.awayMap_mk]
    have hmem : y * DirectSum.of (A.situation.sectionPieces U) k c ^ m ∈
        A.situation.sectionRingGrading U (m • (n + k)) := by
      rw [smul_add]
      exact SetLike.mul_mem_graded hy (SetLike.pow_mem_graded m (of_mem A c))
    have h := psi_spec A p m _ hmem
    rw [evalK_of_eq_mul' A hp, map_mul, map_mul, map_pow] at h
    apply (hv.pow m).mul_left_injective
    dsimp only
    rw [mul_assoc, ← mul_pow]
    exact h
  · rw [RingHom.comp_apply, toRationalFunctionsPresheaf_app_map]
    have h := congrArg ((rationalFunctionsPresheaf M).map (homOfLE hle).op) (psi_spec A a m y hy)
    rw [map_mul, map_pow] at h
    exact h

/-- The morphism of a product `p = ac` is the morphism of `a` restricted to `M_p ⊆ M_a`. -/
private theorem qa_eq_of_eq_mul (U : Z.affineOpens) {n k : ℕ} (hn : 0 < n)
    (a : A.situation.sectionPieces U.1 n) (c : A.situation.sectionPieces U.1 k)
    (p : A.situation.sectionPieces U.1 (n + k))
    (hp : DirectSum.of _ (n + k) p = DirectSum.of _ n a * DirectSum.of _ k c) :
    M.homOfLE (generatingLocus_le_of_eq_mul A a c p hp) ≫ qa A U hn a =
      qa A U (hn.trans_le (n.le_add_right k)) p := by
  have h1 : M.homOfLE (generatingLocus_le_of_eq_mul A a c p hp) ≫
      (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (psi A a)) =
      (A.generatingLocus (Int.natCast_nonneg _) p).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (psi A p)) ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.awayMap _ (of_mem A c) hp)) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext1
    exact (psi_comp_awayMap A a c p hp).symm
  have h2 := Proj.SpecMap_awayMap_awayι (A.situation.sectionRingGrading U.1) (of_mem A a) hn
    (of_mem A c) hp
  rw [qa, qa, ← h2, reassoc_of% h1]
  exact congrArg _ (congrArg _ (Category.assoc _ _ _).symm)

/-! ### Restriction to a smaller affine open of the base -/

/-- The restriction of a homogeneous section along `V ≤ U`. -/
private noncomputable abbrev resPiece {U V : Z.Opens} (h : V ≤ U) {n : ℕ} (a : A.situation.sectionPieces U n) :
    A.situation.sectionPieces V n :=
  (A.algebra.piece (n : ℤ)).val.map (homOfLE h).op a

/-- The total evaluation commutes with restriction along `V ≤ U`. -/
private theorem evalK_comp_gradedSectionRestriction {U V : Z.Opens} (h : V ≤ U) :
    (evalK A V).comp (A.situation.gradedSectionRestriction V U h).toRingHom =
      ((rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono h)).op).hom.comp
        (evalK A U) := by
  refine DirectSum.ringHom_ext fun i x => ?_
  simp only [RingHom.comp_apply]
  erw [Stacks.RelativeProj.Situation.gradedSectionRestriction_of]
  refine (evalK_of A V i _).trans ?_
  rw [evalK_of, A.sectionEquiv_restrict]
  rfl

/-- The total evaluation of a restriction is the restriction of the total evaluation. -/
private theorem evalK_gradedSectionRestriction {U V : Z.Opens} (h : V ≤ U)
    (y : A.situation.sectionRing U) :
    evalK A V (A.situation.gradedSectionRestriction V U h y) =
      (rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono h)).op (evalK A U y) :=
  congrArg (fun F => F y) (evalK_comp_gradedSectionRestriction A h)

/-- Restriction of a homogeneous section in the section ring. -/
private theorem gradedSectionRestriction_of_eq {U V : Z.Opens} (h : V ≤ U) {n : ℕ}
    (a : A.situation.sectionPieces U n) :
    A.situation.gradedSectionRestriction V U h (DirectSum.of _ n a) =
      DirectSum.of _ n (resPiece A h a) :=
  Stacks.RelativeProj.Situation.gradedSectionRestriction_of A.situation V U h n a

/-- The generating locus of a restriction lies in the generating locus of the section. -/
private theorem generatingLocus_resPiece_le {U V : Z.Opens} (h : V ≤ U) {n : ℕ}
    (a : A.situation.sectionPieces U n) :
    A.generatingLocus (Int.natCast_nonneg n) (resPiece A h a) ≤
      A.generatingLocus (Int.natCast_nonneg n) a := by
  refine sSup_le_sSup ?_
  rintro W ⟨hWV, b, hb, hab⟩
  refine ⟨hWV.trans (π.preimage_mono h), b, hb, ?_⟩
  rw [A.sectionEquiv_restrict] at hab
  exact hab

/-- Over `V`, the generating locus of `a` lies in that of its restriction. -/
private theorem inf_preimage_le_generatingLocus_resPiece {U V : Z.Opens} (h : V ≤ U) {n : ℕ}
    (a : A.situation.sectionPieces U n) :
    A.generatingLocus (Int.natCast_nonneg n) a ⊓ π ⁻¹ᵁ V ≤
      A.generatingLocus (Int.natCast_nonneg n) (resPiece A h a) := by
  rintro x ⟨hxa, hxV⟩
  obtain ⟨W, ⟨hWU, b, hb, hab⟩, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hxa
  refine TopologicalSpace.Opens.mem_sSup.mpr ⟨W ⊓ π ⁻¹ᵁ V, ⟨inf_le_right,
    (rationalFunctionsPresheaf M).map (homOfLE inf_le_left).op b,
    hb.map (homOfLE inf_le_left), ?_⟩, hxW, hxV⟩
  rw [A.sectionEquiv_restrict]
  have := congrArg ((rationalFunctionsPresheaf M).map
    (homOfLE (inf_le_left : W ⊓ π ⁻¹ᵁ V ≤ W)).op) hab
  rw [map_mul, map_one] at this
  exact this

/-- `D₊(a|_V) ⟶ Proj 𝒜(V) ⟶ Proj 𝒜(U)` is `Spec` of the restriction `𝒜(U)_(a) → 𝒜(V)_(a|_V)`
followed by `D₊(a) ⟶ Proj 𝒜(U)`. -/
private theorem exists_awayι_comp_projInclusionMap {U V : Z.affineOpens} (h : V ≤ U) {n : ℕ}
    (hn : 0 < n) (a : A.situation.sectionPieces U.1 n) :
    ∃ φ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1) (DirectSum.of _ n a) →+*
        HomogeneousLocalization.Away (A.situation.sectionRingGrading V.1)
          (DirectSum.of _ n (resPiece A h a)),
      Proj.awayι _ _ (of_mem A (resPiece A h a)) hn ≫
          A.situation.projInclusionMap V.1 U.1 h V.2 U.2 =
        Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ _ (of_mem A a) hn ∧
      ∀ (m : ℕ) (y : A.situation.sectionRing U.1)
        (hy : y ∈ A.situation.sectionRingGrading U.1 (m • n)),
        φ (HomogeneousLocalization.Away.mk _ (of_mem A a) m y hy) =
          HomogeneousLocalization.Away.mk _ (of_mem A (resPiece A h a)) m
            (A.situation.gradedSectionRestriction V.1 U.1 h y)
            ((A.situation.gradedSectionRestriction V.1 U.1 h).map_mem hy) := by
  have key : ∀ (t : A.situation.sectionRing V.1) (ht : t ∈ A.situation.sectionRingGrading V.1 n),
      A.situation.gradedSectionRestriction V.1 U.1 h (DirectSum.of _ n a) = t →
      ∃ φ : HomogeneousLocalization.Away (A.situation.sectionRingGrading U.1)
          (DirectSum.of _ n a) →+* HomogeneousLocalization.Away (A.situation.sectionRingGrading V.1) t,
        Proj.awayι _ t ht hn ≫ A.situation.projInclusionMap V.1 U.1 h V.2 U.2 =
          Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ _ (of_mem A a) hn ∧
        ∀ (m : ℕ) (y : A.situation.sectionRing U.1)
          (hy : y ∈ A.situation.sectionRingGrading U.1 (m • n)),
          φ (HomogeneousLocalization.Away.mk _ (of_mem A a) m y hy) =
            HomogeneousLocalization.Away.mk _ ht m
              (A.situation.gradedSectionRestriction V.1 U.1 h y)
              ((A.situation.gradedSectionRestriction V.1 U.1 h).map_mem hy) := by
    rintro t ht rfl
    exact ⟨HomogeneousLocalization.Away.map _ _,
      Proj.awayι_comp_map _ _ hn _ (of_mem A a),
      fun m y hy => HomogeneousLocalization.Away.map_mk _ _ _ _ _ _⟩
  exact key _ _ (gradedSectionRestriction_of_eq A h a)

/-- The morphism of the restriction `a|_V` is the morphism of `a` restricted to `M_{a|_V}`. -/
private theorem qa_resPiece {U V : Z.affineOpens} (h : V ≤ U) {n : ℕ} (hn : 0 < n)
    (a : A.situation.sectionPieces U.1 n) :
    M.homOfLE (generatingLocus_resPiece_le A h a) ≫ qa A U hn a = qa A V hn (resPiece A h a) := by
  obtain ⟨φ, hφ, hφmk⟩ := exists_awayι_comp_projInclusionMap A h hn a
  have hle := generatingLocus_resPiece_le A h a
  have hring : (psi A (resPiece A h a)).comp φ =
      (M.presheaf.map (homOfLE hle).op).hom.comp (psi A a) := by
    have hu : IsUnit ((rationalFunctionsPresheaf M).map
        (homOfLE ((A.generatingLocus_le (Int.natCast_nonneg n) (resPiece A h a)).trans
          (π.preimage_mono h))).op (evalK A U.1 (DirectSum.of _ n a))) := by
      rw [evalK_of]
      exact (isUnit_generatingLocus A (Int.natCast_nonneg n) a).map
        ((rationalFunctionsPresheaf M).map (homOfLE hle).op).hom
    refine away_hom_ext A (of_mem A a) _ _ fun m y hy => ?_
    refine eq_of_mul_pow_eq hu m (t := (rationalFunctionsPresheaf M).map
        (homOfLE ((A.generatingLocus_le (Int.natCast_nonneg n) (resPiece A h a)).trans
          (π.preimage_mono h))).op (evalK A U.1 y)) ?_ ?_
    · rw [RingHom.comp_apply, hφmk]
      have hs := psi_spec A (resPiece A h a) m _
        ((A.situation.gradedSectionRestriction V.1 U.1 h).map_mem hy)
      have e1 : evalK A V.1 (DirectSum.of _ n (resPiece A h a)) =
          (rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono h)).op
            (evalK A U.1 (DirectSum.of _ n a)) := by
        rw [← gradedSectionRestriction_of_eq, evalK_gradedSectionRestriction]
      rw [e1] at hs
      refine hs.trans ?_
      exact congrArg _ (evalK_gradedSectionRestriction A h y)
    · rw [RingHom.comp_apply, toRationalFunctionsPresheaf_app_map]
      have hs := congrArg ((rationalFunctionsPresheaf M).map (homOfLE hle).op)
        (psi_spec A a m y hy)
      rw [map_mul, map_pow] at hs
      exact hs
  have h1 : M.homOfLE hle ≫ (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (psi A a)) =
      (A.generatingLocus (Int.natCast_nonneg n) (resPiece A h a)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (psi A (resPiece A h a))) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext1
    exact hring.symm
  have h2 := reassoc_of% hφ
  rw [qa, qa, reassoc_of% h1, ← A.situation.relativeProjChart_transition h]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (h2 (A.situation.relativeProjChart U)).symm)

/-! ### Gluing -/

omit [IsLocallyNoetherian M] [IsNormal M] [IsIntegral M] in
/-- Two morphisms out of an open subscheme `O` agree if they agree on a neighbourhood `W ≤ O` of
every point of `O`. -/
private theorem eq_of_forall_homOfLE {Y : Scheme.{0}} {O : M.Opens} (f g : O.toScheme ⟶ Y)
    (H : ∀ x ∈ O, ∃ (W : M.Opens) (h : W ≤ O), x ∈ W ∧ M.homOfLE h ≫ f = M.homOfLE h ≫ g) :
    f = g := by
  refine Scheme.hom_ext_of_forall f g fun x => ?_
  obtain ⟨W, hWO, hxW, hW⟩ := H x.1 x.2
  refine ⟨O.ι ⁻¹ᵁ W, hxW, ?_⟩
  have e : (O.ι ⁻¹ᵁ W).ι = (O.ι.isoImage (O.ι ⁻¹ᵁ W)).hom ≫
      (M.isoOfEq (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWO])).hom ≫
        M.homOfLE hWO := by
    rw [← cancel_mono O.ι]
    simp
  rw [e, Category.assoc, Category.assoc, hW, Category.assoc, Category.assoc]

/-- `qa_eq_of_eq_mul` for a product of any degree `d = n + k`. -/
private theorem exists_qa_eq_of_eq_mul (U : Z.affineOpens) {n k d : ℕ} (hd : n + k = d)
    (hn : 0 < n) (hd0 : 0 < d) (a : A.situation.sectionPieces U.1 n)
    (c : A.situation.sectionPieces U.1 k) (p : A.situation.sectionPieces U.1 d)
    (hp : DirectSum.of _ d p = DirectSum.of _ n a * DirectSum.of _ k c) :
    ∃ hle : A.generatingLocus (Int.natCast_nonneg d) p ≤
        A.generatingLocus (Int.natCast_nonneg n) a,
      M.homOfLE hle ≫ qa A U hn a = qa A U hd0 p := by
  subst hd
  exact ⟨_, qa_eq_of_eq_mul A U hn a c p hp⟩

/-- The generating loci of two factors meet inside the generating locus of the product. -/
private theorem inf_le_generatingLocus_of_eq_mul {U : Z.Opens} {n k d : ℕ} (hd : n + k = d)
    (a : A.situation.sectionPieces U n) (c : A.situation.sectionPieces U k)
    (p : A.situation.sectionPieces U d)
    (hp : DirectSum.of _ d p = DirectSum.of _ n a * DirectSum.of _ k c) :
    A.generatingLocus (Int.natCast_nonneg n) a ⊓ A.generatingLocus (Int.natCast_nonneg k) c ≤
      A.generatingLocus (Int.natCast_nonneg d) p := by
  subst hd
  rintro x ⟨hxa, hxc⟩
  obtain ⟨W, ⟨hWU, b, hb, hab⟩, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hxa
  obtain ⟨W', ⟨hW'U, b', hb', hcb⟩, hxW'⟩ := TopologicalSpace.Opens.mem_sSup.mp hxc
  refine TopologicalSpace.Opens.mem_sSup.mpr ⟨W ⊓ W', ⟨inf_le_left.trans hWU,
    (rationalFunctionsPresheaf M).map (homOfLE inf_le_left).op b *
      (rationalFunctionsPresheaf M).map (homOfLE inf_le_right).op b', ?_, ?_⟩, hxW, hxW'⟩
  · have h := (hb.map (homOfLE (inf_le_left : W ⊓ W' ≤ W))).mul
      (hb'.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')))
    have hD : (-((n : ℤ) • D) + -((k : ℤ) • D)) = -(((n + k : ℕ) : ℤ) • D) := by
      push_cast; rw [add_smul]; abel
    rw [hD] at h
    exact h
  · rw [evalK_of_eq_mul A hp, map_mul]
    set ra := (rationalFunctionsPresheaf M).map
      (homOfLE ((inf_le_left : W ⊓ W' ≤ W).trans hWU)).op
      (A.sectionEquiv _ (Int.natCast_nonneg n) U a :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
    set rc := (rationalFunctionsPresheaf M).map
      (homOfLE ((inf_le_left : W ⊓ W' ≤ W).trans hWU)).op
      (A.sectionEquiv _ (Int.natCast_nonneg k) U c :
        (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))
    set rb := (rationalFunctionsPresheaf M).map (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op b
    set rb' := (rationalFunctionsPresheaf M).map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op b'
    have h1 : ra * rb = 1 := by
      have := congrArg ((rationalFunctionsPresheaf M).map
        (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op) hab
      rw [map_mul, map_one] at this
      exact this
    have h2 : rc * rb' = 1 := by
      have := congrArg ((rationalFunctionsPresheaf M).map
        (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op) hcb
      rw [map_mul, map_one] at this
      exact this
    change ra * rc * (rb * rb') = 1
    calc ra * rc * (rb * rb') = (ra * rb) * (rc * rb') := by ring
      _ = 1 := by rw [h1, h2, one_mul]

/-- The homogeneous sections of positive degree over the affine opens of `Z`, indexing the cover
of `M` by generating loci. -/
private abbrev GenIdx : Type :=
  Σ (U : Z.affineOpens) (n : {n : ℕ // 0 < n}), A.situation.sectionPieces U.1 n.1

/-- The generating locus of an index. -/
private noncomputable abbrev genLocus (i : GenIdx A) : M.Opens :=
  A.generatingLocus (Int.natCast_nonneg i.2.1.1) i.2.2

/-- The morphism on the generating locus of an index. -/
private noncomputable abbrev genHom (i : GenIdx A) : (genLocus A i).toScheme ⟶ A.model :=
  qa A i.1 i.2.1.2 i.2.2

/-- The morphisms on two generating loci agree on their intersection. -/
private theorem genHom_compat (i j : GenIdx A) :
    M.homOfLE (inf_le_left : genLocus A i ⊓ genLocus A j ≤ genLocus A i) ≫ genHom A i =
      M.homOfLE (inf_le_right : genLocus A i ⊓ genLocus A j ≤ genLocus A j) ≫ genHom A j := by
  obtain ⟨U, ⟨n, hn⟩, a⟩ := i
  obtain ⟨U', ⟨m, hm⟩, b⟩ := j
  refine eq_of_forall_homOfLE _ _ fun x hx => ?_
  have hxU : π x ∈ U.1 ⊓ U'.1 := ⟨A.generatingLocus_le _ a hx.1, A.generatingLocus_le _ b hx.2⟩
  obtain ⟨V₀, hV₀, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hxU
  set V : Z.affineOpens := ⟨V₀, hV₀⟩
  have hVU : V ≤ U := hVle.trans inf_le_left
  have hVU' : V ≤ U' := hVle.trans inf_le_right
  set a' := resPiece A (U := U.1) (V := V.1) hVU a
  set b' := resPiece A (U := U'.1) (V := V.1) hVU' b
  obtain ⟨p, hp⟩ := SetLike.mul_mem_graded (of_mem A a') (of_mem A b')
  have hp' : DirectSum.of _ (n + m) p = DirectSum.of _ m b' * DirectSum.of _ n a' := by
    rw [hp, mul_comm]
  obtain ⟨hle1, h1⟩ := exists_qa_eq_of_eq_mul A V rfl hn (Nat.add_pos_left hn m) a' b' p hp
  obtain ⟨hle2, h2⟩ := exists_qa_eq_of_eq_mul A V (add_comm m n) hm (Nat.add_pos_left hn m)
    b' a' p hp'
  have hC1 := qa_resPiece A hVU hn a
  have hC2 := qa_resPiece A hVU' hm b
  have hxa' : x ∈ A.generatingLocus _ a' :=
    inf_preimage_le_generatingLocus_resPiece A hVU a ⟨hx.1, hxV⟩
  have hxb' : x ∈ A.generatingLocus _ b' :=
    inf_preimage_le_generatingLocus_resPiece A hVU' b ⟨hx.2, hxV⟩
  have hxp := inf_le_generatingLocus_of_eq_mul A rfl a' b' p hp ⟨hxa', hxb'⟩
  refine ⟨A.generatingLocus _ p, le_inf (hle1.trans (generatingLocus_resPiece_le A hVU a))
    (hle2.trans (generatingLocus_resPiece_le A hVU' b)), hxp, ?_⟩
  rw [Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]
  calc M.homOfLE _ ≫ qa A U hn a
      = M.homOfLE hle1 ≫ M.homOfLE (generatingLocus_resPiece_le A hVU a) ≫ qa A U hn a := by
        rw [Scheme.homOfLE_homOfLE_assoc]
    _ = qa A V (Nat.add_pos_left hn m) p := by rw [hC1, h1]
    _ = M.homOfLE hle2 ≫ M.homOfLE (generatingLocus_resPiece_le A hVU' b) ≫ qa A U' hm b := by
        rw [hC2, h2]
    _ = M.homOfLE _ ≫ qa A U' hm b := by rw [Scheme.homOfLE_homOfLE_assoc]

/-! ### The generating loci of degree-one sections cover `M` -/

omit [IsLocallyNoetherian M] [IsNormal M] [IsIntegral M] in
/-- A section of a quasi-coherent module over a basic open `D(g)` of an affine open `U`, times a
power of `g`, extends to `U`. -/
private theorem exists_pow_smul_eq_restrict {X : Scheme.{0}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U)) (σ : Γ(F, X.basicOpen g)) :
    ∃ (m : ℕ) (a : Γ(F, U)), F.presheaf.map (homOfLE (X.basicOpen_le g)).op a =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ m • σ := by
  let _ : Module Γ(X, U) Γ(F, X.basicOpen g) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
    ⟨fun r s m => by
      change ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom r • s) • m = _
      rw [smul_assoc]; rfl⟩
  let ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen g) :=
    { toFun := fun a => F.presheaf.map (homOfLE (X.basicOpen_le g)).op a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => (Scheme.Modules.map_smul F (homOfLE (X.basicOpen_le g)) r a) }
  have hloc := isLocalizedModule_restrict_basicOpen F hU g ρ (fun _ => rfl)
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, h⟩ := hloc.surj σ
  refine ⟨m, a, ?_⟩
  change ρ a = _
  rw [← h]
  change (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom (g ^ m) • σ = _
  rw [map_pow]

/-- Every point over an affine open `U` lies in the generating locus of a degree-one section over
`U`, when `D` is Cartier and generated over `Z`. -/
private theorem exists_mem_generatingLocus [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) {U : Z.Opens} (hU : IsAffineOpen U) {x : M}
    (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ a : (A.algebra.piece (1 : ℤ)).val.obj (op U), x ∈ A.generatingLocus zero_le_one a := by
  classical
  obtain ⟨U', hxU', ψ, hA, hB⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree π hDC hfree x
  obtain ⟨g, hgle, hxg⟩ := hU.exists_basicOpen_le (V := U ⊓ U') ⟨π x, hx, hxU'⟩ hx
  set Dg := Z.basicOpen g with hDg
  have hDgU : Dg ≤ U := Z.basicOpen_le g
  let ψK : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)) :=
    fun Y => (ψ : RationalFunctions M) Y.1
  have hψK : ψK ∈ ((1 : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ Dg) := by
    intro E hE
    refine Or.inr ?_
    change WithZero.exp _ ≤ E.valuation ((ψ : RationalFunctions M) E.component)
    rw [E.valuation_component, WithZero.exp_le_exp]
    have := hA E (hE.mono (Set.inter_subset_inter_right _
      (π.preimage_mono (hgle.trans inf_le_right))))
    simp only [one_smul]
    linarith
  let σ := (A.sectionEquiv 1 zero_le_one Dg).symm ⟨ψK, hψK⟩
  have := A.isQuasicoherent 1
  obtain ⟨m, a, ha⟩ := exists_pow_smul_eq_restrict (A.algebra.piece (1 : ℤ)) hU g σ
  refine ⟨a, ?_⟩
  -- the restriction of `a` to `π⁻¹ Dg` is `π^* g ^ m ψ`
  have hres := A.sectionEquiv_restrict 1 zero_le_one hDgU a
  set gD := Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op g
  have hkey : (rationalFunctionsPresheaf M).map (homOfLE (π.preimage_mono hDgU)).op
      (A.sectionEquiv 1 zero_le_one U a : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) =
      π.app Dg (gD ^ m) • ψK := by
    have h1 := congrArg (fun z => (A.sectionEquiv 1 zero_le_one Dg z :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)))) ha
    simp only at h1
    have h2 := A.sectionEquiv_smul 1 zero_le_one Dg (gD ^ m) σ
    calc _ = ((A.sectionEquiv 1 zero_le_one Dg
            ((A.algebra.piece 1).val.map (homOfLE hDgU).op a) :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)))) := by rw [hres]; rfl
      _ = _ := h1
      _ = ((π.app Dg (gD ^ m) • A.sectionEquiv 1 zero_le_one Dg σ :
            ((1 : ℤ) • D).divisorialSubmodule (π ⁻¹ᵁ Dg)) :
            (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg))) := congrArg Subtype.val h2
      _ = _ := by simp only [σ, AddEquiv.apply_symm_apply]; rfl
  -- `π^* g` is a unit on `π⁻¹ Dg`
  set v : Γ(M, π ⁻¹ᵁ Dg) := π.app Dg gD
  have hv : IsUnit v := (RingedSpace.isUnit_res_basicOpen Z.toRingedSpace g).map (π.app Dg).hom
  set w : Γ(M, π ⁻¹ᵁ Dg) := ((hv.unit⁻¹ : (Γ(M, π ⁻¹ᵁ Dg))ˣ) : Γ(M, π ⁻¹ᵁ Dg))
  have hvw : v * w = 1 := hv.mul_val_inv
  let E0 : Divisor M := principalDivisor ψ + (1 : ℤ) • D
  have hE0 : ∀ E, E0.coeff E = E.ord ψ + D.coeff E := fun E => by
    simp [E0, DivisorWithCoeffs.coeff_add]
  let W : M.Opens := π ⁻¹ᵁ Dg ⊓ ⟨(E0.supp : Set M)ᶜ, E0.isClosed_supp.isOpen_compl⟩
  have hWDg : W ≤ π ⁻¹ᵁ Dg := inf_le_left
  have hWU : W ≤ π ⁻¹ᵁ U := hWDg.trans (π.preimage_mono hDgU)
  have hxW : x ∈ W := by
    refine ⟨hxg, fun h => ?_⟩
    obtain ⟨E, hne, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    apply hne
    rw [hE0, add_comm]
    exact hB E hxE
  let β : (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ Dg)) :=
    fun Y => M.presheaf.germ (π ⁻¹ᵁ Dg) _ Y.2 (w ^ m) * ((ψ⁻¹ : (RationalFunctions M)ˣ) :
      RationalFunctions M) Y.1
  let b := (rationalFunctionsPresheaf M).map (homOfLE hWDg).op β
  have hb : b ∈ (-((1 : ℤ) • D)).divisorialSubmodule W := by
    intro E hE
    have hcoeff : E0.coeff E = 0 := by
      by_contra hne
      obtain ⟨y, hyE, hyW⟩ := hE
      exact hyW.2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hyE⟩)
    rw [hE0] at hcoeff
    have h1 := Divisor.isDivisorialSection_algebraMap (D := 0) le_rfl (w ^ m) E
      (hE.mono (Set.inter_subset_inter_right _ hWDg))
    have h2 : E.OrdGE (D.coeff E) (((ψ⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M)
        E.component) := by
      refine Or.inr ?_
      rw [E.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_inv]
      linarith
    have := h1.mul h2
    convert this using 1
    · simp
    · rfl
  refine (le_sSup ⟨hWU, b, hb, ?_⟩ : W ≤ A.generatingLocus zero_le_one a) hxW
  funext Y
  have hY : componentGenericPoint M Y.1 ∈ π ⁻¹ᵁ Dg := hWDg Y.2
  have hk := congrFun hkey ⟨Y.1, hY⟩
  change (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y.1, _⟩ * β ⟨Y.1, hY⟩ = 1
  rw [MMP.Mori.rationalFunctions_smul_apply] at hk
  have hk' : (A.sectionEquiv 1 zero_le_one U a :
      (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U))) ⟨Y.1, hWU Y.2⟩ =
      M.presheaf.germ (π ⁻¹ᵁ Dg) _ hY (v ^ m) * (ψ : RationalFunctions M) Y.1 := by
    rw [map_pow] at hk
    exact hk
  rw [hk']
  change _ * (M.presheaf.germ (π ⁻¹ᵁ Dg) _ hY (w ^ m) * ((ψ⁻¹ : (RationalFunctions M)ˣ) :
      RationalFunctions M) Y.1) = 1
  calc _ = M.presheaf.germ (π ⁻¹ᵁ Dg) _ hY ((v * w) ^ m) *
        (((ψ * ψ⁻¹ : (RationalFunctions M)ˣ) : RationalFunctions M) Y.1) := by
          rw [mul_pow, map_mul, Units.val_mul, Pi.mul_apply]; ring
    _ = 1 := by rw [hvw, one_pow, map_one, mul_inv_cancel, Units.val_one, Pi.one_apply, one_mul]

/-- The generating loci of the homogeneous sections of positive degree cover `M`. -/
private theorem isOpenCover_genLocus [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) : TopologicalSpace.IsOpenCover (genLocus A) := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨V₀, hV₀, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show π x ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨a, ha⟩ := exists_mem_generatingLocus A hDC hfree hV₀ (x := x) hxV
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V₀, hV₀⟩, ⟨1, one_pos⟩, a⟩, ha⟩

/-- The open cover of `M` by the generating loci. -/
private noncomputable abbrev genCover [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) : M.OpenCover :=
  M.openCoverOfIsOpenCover (genLocus A) (isOpenCover_genLocus A hDC hfree)

/-- The gluing condition for the morphisms on the generating loci. -/
private theorem genHom_pullback_compat [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) (i j : GenIdx A) :
    Limits.pullback.fst ((genCover A hDC hfree).f i) ((genCover A hDC hfree).f j) ≫ genHom A i =
      Limits.pullback.snd _ _ ≫ genHom A j := by
  have hpb := isPullback_opens_inf (genLocus A i) (genLocus A j)
  change Limits.pullback.fst (genLocus A i).ι (genLocus A j).ι ≫ genHom A i =
    Limits.pullback.snd (genLocus A i).ι (genLocus A j).ι ≫ genHom A j
  rw [← cancel_epi hpb.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  exact genHom_compat A i j

/-- **The morphism `q : M ⟶ Proj_Z ⨁ π_* 𝒪_M(nD)` induced by the algebra.** -/
private noncomputable def inducedHom [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) : M ⟶ A.model :=
  (genCover A hDC hfree).glueMorphisms (genHom A) (genHom_pullback_compat A hDC hfree)

/-- The induced morphism restricts on each generating locus to its morphism there. -/
private theorem ι_inducedHom [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) (i : GenIdx A) :
    (genLocus A i).ι ≫ inducedHom A hDC hfree = genHom A i :=
  (genCover A hDC hfree).ι_glueMorphisms _ _ i

/-! ### The induced morphism lies over `Z` -/

omit [IsIntegral M] in
/-- The rational function of the image of a function on the base is its pull-back along `π`. -/
private theorem evalK_sectionRingBaseMap (U : Z.Opens) (r : Z.ringCatSheaf.obj.obj (op U)) :
    evalK A U (A.situation.sectionRingBaseMap U r) =
      (toRationalFunctionsPresheaf M).app (op (π ⁻¹ᵁ U)) (π.app U (show Γ(Z, U) from r)) := by
  have h := A.situation.sectionRingStructure.baseMap_apply U r
  have h1 : A.situation.sectionRingBaseMap U r =
      DirectSum.of (A.situation.sectionPieces U) 0 (r • A.algebra.one.eval (op U)) := h
  rw [h1, evalK_of]
  have h2 := A.sectionEquiv_smul 0 le_rfl U r (A.algebra.one.eval (op U))
  have h3 := A.sectionEquiv_one U
  funext Zc
  change ((A.sectionEquiv 0 le_rfl U (r • A.algebra.one.eval (op U)) :
    (rationalFunctionsPresheaf M).obj (op (π ⁻¹ᵁ U)))) Zc = _
  rw [h2, Submodule.coe_smul, rationalFunctions_smul_apply, h3]
  exact mul_one _

/-- `ψ̃_a` on degree-zero fractions `y / 1`. -/
private theorem psiK_fromZeroRingHom {U : Z.Opens} {n : ℕ} (a : A.situation.sectionPieces U n)
    (y : A.situation.sectionRingGrading U 0) :
    psiK A a (HomogeneousLocalization.fromZeroRingHom _ _ y) =
      (rationalFunctionsPresheaf M).map
        (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op (evalK A U y) :=
  lift_mk_one (DirectSum.of (A.situation.sectionPieces U) n a)
    (((rationalFunctionsPresheaf M).map
        (homOfLE (A.generatingLocus_le (Int.natCast_nonneg n) a)).op).hom.comp (evalK A U))
    (by rw [RingHom.comp_apply, evalK_of]; exact isUnit_generatingLocus A _ a) (y : _)

/-- In degree zero, `ψ_a` is the restriction of `π^♯`. -/
private theorem sectionRingZeroMap_comp_psi {U : Z.Opens} {n : ℕ}
    (a : A.situation.sectionPieces U n) :
    A.situation.sectionRingZeroMap U ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫
        CommRingCat.ofHom (psi A a) =
      π.appLE U (A.generatingLocus (Int.natCast_nonneg n) a)
        (A.generatingLocus_le (Int.natCast_nonneg n) a) := by
  ext r : 2
  apply toRationalFunctionsPresheaf_app_injective
  change (toRationalFunctionsPresheaf M).app _ (psi A a (HomogeneousLocalization.fromZeroRingHom _ _
    (A.situation.sectionRingZeroMap U r))) = _
  rw [toRationalFunctions_psi, psiK_fromZeroRingHom, Scheme.Hom.appLE,
    CommRingCat.comp_apply, toRationalFunctionsPresheaf_app_map]
  congr 1
  have hc : ((A.situation.sectionRingZeroMap U r : A.situation.sectionRingGrading U 0) :
      A.situation.sectionRing U) = A.situation.sectionRingBaseMap U r :=
    congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe _
      ⟨_, A.situation.sectionRingBaseMap_mem_zero U r⟩)
  rw [hc]
  exact evalK_sectionRingBaseMap A U r

/-- The morphism on a generating locus lies over `Z`. -/
private theorem genHom_toBase (i : GenIdx A) :
    genHom A i ≫ A.toBase = (genLocus A i).ι ≫ π := by
  obtain ⟨U, ⟨n, hn⟩, a⟩ := i
  have e1 := (A.situation.relativeProjChart_isPullback U).w
  have e2 := Proj.awayι_toSpecZero_assoc (A.situation.sectionRingGrading U.1)
    (DirectSum.of _ n a) (of_mem A a) hn
    (Spec.map (A.situation.sectionRingZeroMap U.1) ≫ U.2.isoSpec.inv ≫ U.1.ι)
  have e3 : (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (psi A a)) ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _)) ≫
      Spec.map (A.situation.sectionRingZeroMap U.1) =
      (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
        Spec.map (π.appLE U.1 (A.generatingLocus (Int.natCast_nonneg n) a)
          (A.generatingLocus_le (Int.natCast_nonneg n) a)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (_ ≫ ·) (congrArg Spec.map
      ((Category.assoc _ _ _).trans (sectionRingZeroMap_comp_psi A a)))
  have e4 := Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc π U.1
    (A.generatingLocus (Int.natCast_nonneg n) a) (A.generatingLocus_le (Int.natCast_nonneg n) a)
    (U.2.isoSpec.inv ≫ U.1.ι)
  calc genHom A ⟨U, ⟨n, hn⟩, a⟩ ≫ A.toBase
      = (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (psi A a)) ≫
          Proj.awayι _ _ (of_mem A a) hn ≫
          (A.situation.relativeProjChart U ≫ A.situation.relativeProjToBase) := by
        simp only [genHom, qa, Category.assoc]; rfl
    _ = (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (psi A a)) ≫
          (Proj.awayι _ _ (of_mem A a) hn ≫ Proj.toSpecZero _ ≫
            Spec.map (A.situation.sectionRingZeroMap U.1) ≫ U.2.isoSpec.inv ≫ U.1.ι) := by
        rw [e1]; rfl
    _ = (A.generatingLocus (Int.natCast_nonneg n) a).toSpecΓ ≫
          Spec.map (π.appLE U.1 (A.generatingLocus (Int.natCast_nonneg n) a)
            (A.generatingLocus_le (Int.natCast_nonneg n) a)) ≫ U.2.isoSpec.inv ≫ U.1.ι := by
        rw [e2, ← reassoc_of% e3]
    _ = (genLocus A ⟨U, ⟨n, hn⟩, a⟩).ι ≫ π := by
        have e5 := IsAffineOpen.toSpecΓ_isoSpec_inv_assoc U.2 U.1.ι
        rw [e4, e5, Scheme.Hom.resLE_comp_ι]

/-- The glued morphism is the morphism induced by the algebra. -/
private theorem isInducedMorphism_inducedHom [CompactSpace M] (hDC : D.IsCartier)
    (hfree : IsRelativelyFreeDivisor π D) : A.IsInducedMorphism (inducedHom A hDC hfree) where
  comp_toBase := (genCover A hDC hfree).hom_ext _ _ fun (i : GenIdx A) => by
    change (genLocus A i).ι ≫ _ ≫ _ = (genLocus A i).ι ≫ π
    rw [reassoc_of% (ι_inducedHom A hDC hfree i)]
    exact genHom_toBase A i
  factors U n hn a := ⟨psi A a, ι_inducedHom A hDC hfree ⟨U, ⟨n, hn⟩, a⟩, fun m t => by
    have := psi_spec A a m _ (of_mem A t)
    rwa [evalK_of, evalK_of] at this⟩

end InducedMorphism

/-- **Existence of the relative ample model.** For `π : M ⟶ Z` projective and `L` semiample over
`Z`, choose `k > 0` with `D = kL` Cartier and `π`-generated; then `Proj_Z ⨁_n π_* 𝒪_M(nD)` with the
morphism induced by the algebra is the relative ample model of `L` over `Z`. -/
private theorem exists_isRelativeAmpleModel {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M]
    [IsLocallyNoetherian M] [IsNormal M] {π : M ⟶ Z} (hπ : IsProjectiveMorphism π)
    {L : QDivisor M} (hL : QDivisor.IsRelativelySemiample π L) :
    ∃ (V : Scheme.{0}) (p : V ⟶ Z) (q : M ⟶ V), IsRelativeAmpleModel π L p q := by
  obtain ⟨k, hk, D, hD, hDC, hfree⟩ := exists_isRelativelyFreeDivisor_of_isRelativelySemiample hL
  have : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : QuasiSeparated π := IsSeparated.instQuasiSeparated π
  have : QuasiCompact π := inferInstance
  let A := pushSectionAlgebra π D
  refine ⟨A.model, A.toBase, inducedHom A hDC hfree, k, hk, D, hD, hDC, hfree, A, Iso.refl _,
    Category.id_comp _, ?_⟩
  rw [Iso.refl_hom, Category.comp_id]
  exact isInducedMorphism_inducedHom A hDC hfree

/-- **The strict transform of a canonical divisor along a small model is canonical.** Let
`f : X ⟶ Z` be a proper birational morphism of normal complex varieties and `p : V ⟶ Z` a small
morphism. If `K` is a canonical divisor of `X`, then `(p)⁻¹_* f_* K` is a canonical divisor of
`V`: writing `f_* K = div(ω)` for a rational top form `ω` on `Z`, it is `div(p^* ω)`, since `p`
is a local isomorphism over the generic points of the prime divisors of `Z` under the prime
divisors of `V`. -/
private theorem isCanonicalDivisor_flipTransform {X Z V : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral V] [CompactSpace V]
    [IsLocallyNoetherian V] [IsNormal V] {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} [IsProper f] (hfb : IsBirationalMorphism f) (hX : IsNormalVariety ℂ (f ≫ sZ))
    {p : V ⟶ Z} (hp : IsSmallMorphism (p ≫ sZ) sZ p) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor (f ≫ sZ) n) :
    Divisor.IsCanonicalDivisor (p ≫ sZ) n (flipTransform f p K) := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : QuasiCompact sZ := hZ.1.toQuasiCompact
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have hV := hp.isNormalVariety_source
  have : LocallyOfFiniteType (f ≫ sZ) := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sZ) := hV.1.toLocallyOfFiniteType
  have hpb := hp.isBirationalMorphism
  have : IsProper p := hp.isProper
  have : IsDominant f := hfb.isDominant
  have : IsDominant p := hpb.isDominant
  have := hZ.1
  have := hX.1
  have := hV.1
  have hnZ : topologicalKrullDim Z = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (f ≫ sZ) hfb).trans
      hK.topologicalKrullDim_eq
  have hnV : topologicalKrullDim V = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (p ≫ sZ) hpb).symm.trans
      hnZ
  obtain ⟨ω, hω0, hω⟩ :=
    Oai4C1.Main.exists_divisorOfForm_eq_transformDivisor hZ hX hfb hnZ hK
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (p ≫ sZ) hV hnV
  have hbij := hpb.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  have hτ0 := Oai4C1.Main.pullbackRationalPluriForms_ne_zero p hbij hd hω0
  have hle := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hτ0
  rw [one_zsmul] at hle
  have hsurj : Function.Surjective p := Surjective.surj
  have : IsSeparated (Z ↘ Limits.terminal Scheme) := isSeparated_toTerminal_of_isNormalVariety hZ
  have heq : divisorOfForm (pullbackRationalPluriForms sZ p ω) = flipTransform f p K := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
      exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfb hp P
    have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
    have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
    have hbir : Q.genericPoint ∈ biregularLocus p := by
      rw [← hPQ']
      by_contra hne
      have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hp.two_le_codimension
        (mem_exceptionalSet.mpr hne)
      rw [P.coheight_genericPoint] at this
      exact absurd this (by decide)
    have := Q.isDiscreteValuationRing_localRing
    have := isIso_stalkMap_of_map_eq_genericPoint hpb hPQ'
    rw [flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective hsurj hPmQ' hPQ'
      hbir K]
    change P.ordForm _ = _
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hbij hd P Q hPQ' ω]
    change (divisorOfForm ω) Q = _
    rw [hω, RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f Pm Q).mpr hPmQ')
      (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
        eq_of_map_eq_of_valuationRing hfb.functionFieldMap_bijective
          ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E' Q).mp hE') hPmQ')]
  rw [← heq]
  exact hK₀.of_linearlyEquivalent hle

private theorem solution : ∀ {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (hfb : IsBirationalMorphism f),
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X')
      (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z),
      IsPermittedStep sX sZ sX' K B R f fp := by
  intro X Z _ _ _ _ sX sZ hX hdim K hK B hB R hR f hf hfb
  obtain ⟨n, hKn⟩ := hK
  have hn : n = 4 := by
    have := hKn.topologicalKrullDim_eq
    rw [hdim] at this
    exact_mod_cast this.symm
  subst hn
  obtain ⟨hZ, hρ, hamp⟩ := contraction_data hX hdim hKn hB hR hf
  have : LocallyOfFiniteType sX := hX.toIsVariety.toLocallyOfFiniteType
  obtain ⟨M, _, _, _, _, sM, _, _, πM, KM, BM, φ, hlm⟩ :=
    IsLogCanonicalPair.exists_isGoodLogMinimalModel_of_isContraction hX hdim hB ⟨4, hKn⟩ hZ
      hf.toIsContraction hfb hamp
  obtain ⟨V, p, q, hV⟩ := exists_isRelativeAmpleModel hlm.isProjectiveMorphism_model
    hlm.isRelativelySemiample
  have h : IsAmpleModelDatum sX sZ sM K B f KM BM φ πM q p
      (RationalMap.transformDivisor (X := M) q.toRationalMap BM) :=
    ⟨hX, hdim, hB, ⟨4, hKn⟩, hf.toIsContraction, hfb, hZ, hamp, hlm, hV, rfl⟩
  have hsm := h.isSmallMorphism
  have hVn := hsm.isNormalVariety_source
  have : IsIntegral V := hVn.1.toIsIntegral
  have : IsNormal V := hVn.2
  have : LocallyOfFiniteType (p ≫ sZ) := hVn.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sZ) := hVn.1.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sZ)
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sZ)
  obtain ⟨hpproj, -⟩ := h.isProjectiveMorphism_and_isBirationalMorphism
  have hBV := h.boundary_eq_flipTransform
  have : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hKV := isCanonicalDivisor_flipTransform hf.isNormalVariety_target hfb
    (hf.comp_eq ▸ hf.isNormalVariety_source) hsm (n := 4) (K := K) (hf.comp_eq ▸ hKn)
  have hlc := h.isLogCanonicalPair_ampleModel
  have hampV := (h.isQCartier_and_hasRelativelyAmpleMultiple hKV).2
  rw [hBV] at hlc hampV
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, p ≫ sZ, p,
    ⟨hX, hB, ⟨4, hKn⟩, hR, hf, hZ, hρ, hamp, hfb, ?_, hsm, hpproj, hlc, hampV⟩⟩
  exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr
    ⟨hVn.1, hpproj.comp ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).2⟩

end Proof_prop_oai4_continuation

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Continuation through every birational contraction.** Let `X` be a projective fourfold
over `ℂ`, `K` a canonical divisor, `B` a `ℚ`-divisor with `(X, B)` log canonical, `R` a
`(K + B)`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Z` a birational contraction of `R`.
Then there are a normal projective variety `X⁺` and a small projective birational morphism
`f⁺ : X⁺ ⟶ Z` such that `(X⁺, B⁺, f⁺)` is a permitted step for `(X, B, R, f)`
(`MMP.Fourfold.IsPermittedStep`). -/
@[mmp "prop_oai4_continuation"]
public theorem IsContractionOfRay.exists_isPermittedStep {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) (hfb : IsBirationalMorphism f) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X')
      (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z),
      IsPermittedStep sX sZ sX' K B R f fp :=
        by revert X Z sX sZ hX hdim K hK B hB R hR f hf hfb; first | exact Proof_prop_oai4_continuation.solution | exact Proof_prop_oai4_continuation.solution _ | exact Proof_prop_oai4_continuation.solution _ _ | exact Proof_prop_oai4_continuation.solution _ _ _ | exact Proof_prop_oai4_continuation.solution _ _ _ _

end MMP.Fourfold

