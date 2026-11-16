module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.Morphisms.HProjective
import MMP.AlgebraicGeometry.MMP.Contraction.DltContractionQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.QFactorial
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionDlt
import MMP.AlgebraicGeometry.MMP.Contraction.DltRelativeContractionExists
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization

/-!
# Elementary steps of projective dlt pairs preserve `ℚ`-factoriality and dlt

Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair with rational boundary `Δ` and canonical
divisor `K`, over an algebraically closed field of characteristic zero, and let `R` be a
`(K + Δ)`-negative extremal ray of `NE̅(X)` whose contraction `f : X ⟶ V` is birational. The
elementary step `(X, Δ) ⇢ (X', Δ')` of `R` is the `(K + Δ)`-flip of `f` when `f` is small and the
divisorial contraction `(V, f_* Δ)` otherwise, with `Δ'` the birational transform of `Δ`. Then
`X'` is `ℚ`-factorial and `(X', Δ')` is dlt.

The target `V` is projective: the dlt contraction theorem contracts `R` onto a projective
variety, and two contractions of one extremal ray agree up to isomorphism. So `f` is a
contraction of `R` in the sense of Kollár–Mori.

* If `f` is small, `f⁺` is a flip of `f`; flips of `ℚ`-factorial dlt pairs are `ℚ`-factorial,
  and flips preserve dlt pairs.
* Otherwise `f⁺` is an isomorphism, and `g = f ≫ (f⁺)⁻¹ : X ⟶ X'` is a contraction of `R` which
  is neither of fibre type (it is birational) nor small (its exceptional set is that of `f`), so
  it is a divisorial contraction by the trichotomy of extremal contractions. Divisorial
  contractions of projective `ℚ`-factorial dlt pairs preserve `ℚ`-factoriality and dlt, and the
  birational transform `g_* Δ` is `(f⁺)⁻¹_* f_* Δ = Δ'`.

## Main results

* `MMP.Fourfold.IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair`: the statement above.

## Implementation notes

The step is `MMP.Fourfold.IsProjectiveElementaryDltStep`: the target of the step is presented
by a morphism `f⁺ : X' ⟶ V`, a flip of `f` in the small case and an isomorphism otherwise, and
`Δ' = (f⁺)⁻¹_* f_* Δ`. In the non-small case `Ex(f)` is a prime divisor, since `X` is
`ℚ`-factorial and `R` is extremal, so this branch is the divisorial contraction of the source.
The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Prop. 2.5, 3.36,
  3.37, Cor. 3.44.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-! ### Projective morphisms between projective varieties -/

section Projective

variable {k : Type} [Field k]

/-- A projective variety carries an ample invertible sheaf. -/
private theorem exists_isAmple {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- A proper morphism between projective varieties is projective. -/
private theorem isProjectiveMorphism_of_isProper {V Z : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} (hV : MMP.Mori.IsProjectiveVariety k sV)
    (hZ : MMP.Mori.IsProjectiveVariety k sZ) (p : V ⟶ Z) [IsProper p] :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p (exists_isAmple hZ)).out 5 2
  exact h.mp ⟨inferInstance, exists_isAmple hV⟩

/-- A scheme isomorphic over `k` to a projective variety is a projective variety. -/
private theorem isProjectiveVariety_of_isIso {V X' : Scheme.{0}} [IsIntegral X']
    {sV : V ⟶ Spec (.of k)} (hV : MMP.Mori.IsProjectiveVariety k sV) (e : X' ⟶ V) [IsIso e] :
    MMP.Mori.IsProjectiveVariety k (e ≫ sV) := by
  have hVv := hV.toIsVariety
  have : IsSeparated sV := hVv.toIsSeparated
  have : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have : QuasiCompact sV := hVv.toQuasiCompact
  refine (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
    ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩, ?_⟩
  exact (MMP.isProjectiveMorphism_of_isClosedImmersion e).comp hV.isProjective

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

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- Every proper curve is contracted by the structure morphism. -/
private theorem isContractedBy_structure (C : ProperCurve sX) : C.IsContractedBy sX :=
  fun _ _ => Subsingleton.elim _ _

/-- Over the base point, the natural map `N₁(X / Spec k) → N₁(X)` is bijective. -/
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

/-- The base point `Spec k` is a projective variety over `k`. -/
private theorem isProjectiveVariety_id_spec :
    AlgebraicGeometry.IsProjectiveVariety k (𝟙 (Spec (.of k))) :=
  (AlgebraicGeometry.isProjectiveVariety_iff k _).mpr
    ⟨(MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      MMP.isProjectiveMorphism_of_isClosedImmersion _⟩

variable {sX}

/-- Over the base point, the preimage of an extremal ray of `NE̅(X)` under the isomorphism
`N₁(X / Spec k) ≃ N₁(X)` is an extremal ray of the relative closed cone of curves. -/
private theorem isExtremalRay_preimage_relativeToAbsolute [IsAlgClosed k] [CharZero k]
    [AlgebraicGeometry.IsProjectiveVariety k sX] {R : Set (NumericalCurveClasses sX)}
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R) :
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _)
      (LinearEquiv.ofBijective (relativeToAbsolute sX sX)
        (relativeToAbsolute_bijective sX) ⁻¹' R) := by
  haveI := isProjectiveVariety_id_spec (k := k)
  have hbij := relativeToAbsolute_bijective sX
  let e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) hbij
  have h := image_relativeClosedConeOfCurves_eq_inter_range sX (𝟙 (Spec (.of k))) sX
    (Category.comp_id sX)
  rw [hbij.2.range_eq, Set.inter_univ] at h
  have hcone : e.symm '' (closedConeOfCurves sX : Set _) =
      (relativeClosedConeOfCurves sX sX : Set _) := by
    rw [← h]
    exact e.symm_image_image _
  rw [← e.image_symm_eq_preimage, ← hcone]
  exact MMP.ProgramBaseChange.isExtremalRay_image e.symm hRay

/-- Two contractions of the same extremal ray of `NE̅(X)` agree up to an isomorphism of their
targets over `k`. -/
private theorem exists_isIso_comp_eq_of_isContractionOfRay
    {Z Z' : Scheme.{0}} (hX : MMP.Mori.IsProjectiveVariety k sX)
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

/-- **The target of the contraction of a negative extremal ray is projective.** Let `(X, Δ)` be
a projective `ℚ`-factorial dlt pair over an algebraically closed field of characteristic zero and
`f : X ⟶ W` the contraction of a `(K + Δ)`-negative extremal ray `R`. Then `W` is a projective
variety. -/
private theorem isProjectiveVariety_of_isContractionOfRay [IsAlgClosed k] [CharZero k]
    {W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sW : W ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hQ : IsQFactorial sX)
    (hdlt : MMP.Mori.IsDltPair sX n K Δ)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R)
    (hf : IsContractionOfRay sX sW R f) : MMP.Mori.IsProjectiveVariety k sW := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _ hXp.isProjective
  haveI := isProjectiveVariety_id_spec (k := k)
  let e := LinearEquiv.ofBijective (relativeToAbsolute sX sX) (relativeToAbsolute_bijective sX)
  obtain ⟨_, hRay, hneg⟩ := hR
  have hFray : IsExtremalRay ℝ (relativeClosedConeOfCurves sX sX : Set _) (e ⁻¹' R) :=
    isExtremalRay_preimage_relativeToAbsolute hRay
  obtain ⟨Z, ψ, g, hψ⟩ := MMP.Mori.IsDltPair.exists_isRelativeContractionOfFace
    (𝟙 (Spec (.of k))) sX (Category.comp_id sX) hdlt hQ hFray.1
    hFray.1.2.2.1 fun z hz hz0 => by
      rw [QDivisor.relativeCurveForm_eq_comp]
      exact hneg (e z) hz fun h => hz0 (e.injective (by rw [h, map_zero]))
  have happ := hψ.isIso_app
  haveI : IsIntegral Z := isIntegral_of_isIso_app ψ happ
  have hgp := hψ.isProjectiveMorphism
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  have hZv : MMP.Mori.IsVariety k g := (MMP.Mori.isVariety_iff k g).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZp : MMP.Mori.IsProjectiveVariety k g :=
    (AlgebraicGeometry.isProjectiveVariety_iff k g).mpr ⟨hZv, hgp⟩
  haveI : IsDominant ψ := isDominant_of_isIso_app ψ happ
  haveI : IsIso ψ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ ψ.c fun U => happ U.unop
  haveI : IsProper (ψ ≫ g) := by
    rw [hψ.comp_eq]
    infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ g
  have hsurj : Function.Surjective ψ := by
    intro z
    have h1 : closure (Set.range ψ) = Set.univ := ψ.denseRange.closure_range
    rw [ψ.isClosedMap.isClosed_range.closure_eq] at h1
    exact Set.range_eq_univ.mp h1 z
  have hψR : IsContractionOfRay sX g R ψ :=
    { isNormalVariety_source := hf.isNormalVariety_source
      isNormalVariety_target := ⟨hZv, MMP.Mori.isNormal_of_isIso_c g ψ hZv
        (hψ.comp_eq ▸ hXp.toIsVariety)⟩
      comp_eq := hψ.comp_eq
      isProjectiveMorphism := isProjectiveMorphism_of_isProper hXp hZp ψ
      surjective := hsurj
      isIso_app := happ
      isContractedBy_iff := fun C => by
        rw [hψ.isContractedBy_iff C (isContractedBy_structure sX C)]
        change e (C.relativeClass sX _) ∈ R ↔ _
        rw [show e (C.relativeClass sX _) = OneCycle.numericalClass sX (C.cycle ℝ) from
          isNaturalRelativeMap_relativeToAbsolute sX sX _] }
  obtain ⟨φ, _, -, hφg⟩ := exists_isIso_comp_eq_of_isContractionOfRay hXp hRay hf hψR
  obtain ⟨m, i, hi, hic⟩ := hgp
  exact (AlgebraicGeometry.isProjectiveVariety_iff k sW).mpr
    ⟨hf.isNormalVariety_target.1, m, φ ≫ i, inferInstance, by rw [Category.assoc, hic, hφg]⟩

end Absolute

/-! ### Flips -/

section Flip

variable {k : Type} [Field k] {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- A `(K + B)`-flip in the sense of `MMP.Fourfold.IsFlipOf`, with `K` a canonical divisor, is a
flip in the sense of `MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFlipOf (hK : K.IsCanonicalDivisor sX n)
    (h : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    MMP.Mori.IsFlip sX sZ sX' K B f fp := by
  have hD : Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B =
      flipTransform f fp (Divisor.toQDivisor K + B) := by
    rw [map_add, MMP.Mori.flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := h.isSmallMorphism.isNormalVariety_source
          isNormalVariety_target := h.isSmallMorphism.isNormalVariety_target
          comp_eq := h.isSmallMorphism.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := h.isQCartier
          isProper := h.isSmallMorphism.isProper
          isBirationalMorphism := h.isSmallMorphism.isBirationalMorphism
          two_le_codimension := h.isSmallMorphism.two_le_codimension
          hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
      isNormalVariety := h.isSmallMorphism_flip.isNormalVariety_source
      comp_eq := h.isSmallMorphism_flip.comp_eq
      isProper := h.isSmallMorphism_flip.isProper
      isBirationalMorphism := h.isSmallMorphism_flip.isBirationalMorphism
      isQCartier := hD ▸ h.isQCartier_flip
      hasRelativelyAmpleMultiple := hD ▸ h.hasRelativelyAmpleMultiple_flip
      two_le_codimension := h.isSmallMorphism_flip.two_le_codimension }

end Flip

/-! ### Composing with an isomorphism -/

section Iso

variable {X Y Y' : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ Y') [IsIso e]

/-- On points, `e⁻¹ (e y) = y` for an isomorphism `e`. -/
private theorem inv_apply_apply (y : Y) : inv e (e y) = y := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
  rfl

/-- An open `W` of `Y'` is `(f ≫ e)`-biregular iff `e⁻¹(W)` is `f`-biregular. -/
private theorem isBiregular_comp_iff_of_isIso (W : Y'.Opens) :
    IsBiregular (f ≫ e) W ↔ IsBiregular f (e ⁻¹ᵁ W) := by
  have : IsIso (e ∣_ W) := IsZariskiLocalAtTarget.restrict
    (P := MorphismProperty.isomorphisms Scheme) (inferInstanceAs (IsIso e)) W
  unfold IsBiregular
  rw [morphismRestrict_comp]
  exact ⟨fun h => @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ this h,
    fun h => @IsIso.comp_isIso _ _ _ _ _ _ _ h this⟩

/-- Composing with an isomorphism does not change the exceptional set. -/
private theorem exceptionalSet_comp_of_isIso : exceptionalSet (f ≫ e) = exceptionalSet f := by
  refine SetLike.coe_injective (Set.ext fun x => ?_)
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_exceptionalSet, mem_exceptionalSet, not_iff_not,
    Scheme.Hom.comp_apply]
  refine ⟨fun hx => le_biregularLocus ((isBiregular_comp_iff_of_isIso f e _).mp
    (isBiregular_biregularLocus (f ≫ e))) hx, fun hx => ?_⟩
  have hpre : e ⁻¹ᵁ ((inv e) ⁻¹ᵁ biregularLocus f) = biregularLocus f := by
    ext y
    change (inv e) (e y) ∈ biregularLocus f ↔ y ∈ biregularLocus f
    rw [inv_apply_apply]
  have h : IsBiregular (f ≫ e) ((inv e) ⁻¹ᵁ biregularLocus f) := by
    rw [isBiregular_comp_iff_of_isIso, hpre]
    exact isBiregular_biregularLocus f
  refine le_biregularLocus h ?_
  change (inv e) (e (f x)) ∈ biregularLocus f
  rwa [inv_apply_apply]

/-- A curve is contracted by `f ≫ e` iff it is contracted by `f`. -/
private theorem isContractedBy_comp_iff_of_isIso {k : Type} [Field k] {sX : X ⟶ Spec (.of k)}
    (C : ProperCurve sX) : C.IsContractedBy (f ≫ e) ↔ C.IsContractedBy f := by
  unfold ProperCurve.IsContractedBy
  simp only [Scheme.Hom.comp_apply, e.isOpenEmbedding.injective.eq_iff]

/-- A morphism `f` defines a partial map on all of its source, sending `x` to `f x`. -/
private theorem toPartialMap_hom_apply (x : X) (hx : x ∈ f.toPartialMap.domain) :
    f.toPartialMap.hom ⟨x, hx⟩ = f x :=
  rfl

variable [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Y' ↘ ⊤_ Scheme)]

/-- The strict transform of a prime divisor under `f ≫ e` is the image under `e` of its strict
transform under `f`. -/
private theorem transformPrimeDivisor_comp_of_isIso (P : MMP.Mori.PrimeDivisor X) :
    RationalMap.transformPrimeDivisor (f ≫ e).toRationalMap P =
      (RationalMap.transformPrimeDivisor f.toRationalMap P).bind
        (inverseTransformPrimeDivisor (inv e)) := by
  have htop : biregularLocus (inv e) = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff (inv e)).mpr inferInstance))
  have hcoh (y : Y) (hy : Order.coheight y = 1) : Order.coheight (e y) = 1 := by
    rwa [← coheight_eq_of_isOpenImmersion (inv e), inv_apply_apply]
  have hcoh' (y : Y') (hy : Order.coheight y = 1) : Order.coheight ((inv e) y) = 1 := by
    rwa [← coheight_eq_of_isOpenImmersion e, MMP.Resolution.Kollar.apply_inv_apply]
  have hdom : P.genericPoint ∈ f.toPartialMap.domain := by simp [Scheme.Hom.toPartialMap]
  have hdom' : P.genericPoint ∈ (f ≫ e).toPartialMap.domain := by
    simp [Scheme.Hom.toPartialMap]
  cases hQ : RationalMap.transformPrimeDivisor f.toRationalMap P with
  | none =>
    simp only [Option.bind_none]
    by_contra hne
    obtain ⟨Q', hQ'⟩ := Option.ne_none_iff_exists'.mp hne
    have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hQ' _ rfl hdom'
    rw [toPartialMap_hom_apply, Scheme.Hom.comp_apply] at hη
    let Q : MMP.Mori.PrimeDivisor Y :=
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne ((inv e) Q'.genericPoint)
        (hcoh' _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q'))
    have hQη : Q.genericPoint = f P.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).trans
        (by rw [hη, inv_apply_apply])
    have := MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (E := Q) f.toPartialMap
      rfl hdom
      (by rwa [toPartialMap_hom_apply])
    rw [hQ] at this
    simp at this
  | some Q =>
    have hη := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hQ _ rfl hdom
    rw [toPartialMap_hom_apply] at hη
    let Q' : MMP.Mori.PrimeDivisor Y' :=
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e Q.genericPoint)
        (hcoh _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q))
    have hQ'η : Q'.genericPoint = e Q.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have h1 : inverseTransformPrimeDivisor (inv e) Q = some Q' := by
      refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        ?_ (by rw [htop]; trivial)
      rw [hQ'η, inv_apply_apply]
    rw [Option.bind_some, h1]
    refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (f ≫ e).toPartialMap rfl
      hdom' ?_
    rw [toPartialMap_hom_apply, hQ'η, hη, Scheme.Hom.comp_apply]

/-- For an isomorphism `f⁺ : X' ⟶ Y`, the birational transform of a divisor along
`f ≫ (f⁺)⁻¹` is `(f⁺)⁻¹_* f_* D`. -/
private theorem transformDivisor_comp_inv_eq_flipTransform {X' : Scheme.{0}} (fp : X' ⟶ Y)
    [IsIso fp] [IsSeparated (X' ↘ ⊤_ Scheme)] {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (f ≫ inv fp).toRationalMap D = flipTransform f fp D := by
  have h : ∀ P, RationalMap.transformPrimeDivisor (f ≫ inv fp).toRationalMap P =
      (RationalMap.transformPrimeDivisor f.toRationalMap P).bind
        (inverseTransformPrimeDivisor fp) := fun P => by
    rw [transformPrimeDivisor_comp_of_isIso f (inv fp) P, IsIso.inv_inv]
  simp only [flipTransform, AddMonoidHom.comp_apply, RationalMap.transformDivisor,
    inverseTransformDivisor, MMP.Fourfold.mapPrimeDivisors_mapPrimeDivisors]
  exact congrArg (fun φ => DivisorWithCoeffs.mapPrimeDivisors φ D) (funext h)

end Iso

/-! ### The divisorial case -/

section Divisorial

variable {k : Type} [Field k]

/-- A `k`-scheme with separated structure morphism is separated. -/
private theorem isSeparated_toTerminal {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] : IsSeparated (Y ↘ ⊤_ Scheme) := by
  rw [show (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of k)) from
    Subsingleton.elim _ _]
  infer_instance

/-- **A non-small birational contraction of an extremal ray is divisorial.** Let `f : X ⟶ V`
be a birational contraction of an extremal ray `R` of a projective `ℚ`-factorial variety which
is not small, and `f⁺ : X' ⟶ V` an isomorphism. Then `f ≫ (f⁺)⁻¹` is a divisorial contraction
of `R`. -/
private theorem isDivisorialContraction_comp_inv [IsAlgClosed k] [CharZero k]
    {X V X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hX'p : MMP.Mori.IsProjectiveVariety k sX')
    (hXQ : IsQFactorial sX)
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hfR : IsContractionOfRay sX sV R f) (hfbir : IsBirationalMorphism f)
    (hcomp : fp ≫ sV = sX') (hns : ¬ IsSmallMorphism sX sV f) :
    IsDivisorialContraction k sX sX' R (f ≫ inv fp) := by
  have hVn := hfR.isNormalVariety_target
  haveI : IsIntegral V := hVn.1.toIsIntegral
  haveI : AlgebraicGeometry.IsVariety k sX := hXp.toIsVariety
  haveI : AlgebraicGeometry.IsVariety k sX' := hX'p.toIsVariety
  have hgF : IsContractionOfFace k sX sX' R (f ≫ inv fp) :=
    { isProjectiveVariety_source := hXp
      isProjectiveVariety_target := hX'p
      comp_eq := by rw [Category.assoc, ← hcomp, IsIso.inv_hom_id_assoc, hfR.comp_eq]
      isExtremalFace := hRay.1
      isContractedBy_iff := fun C =>
        (isContractedBy_comp_iff_of_isIso f (inv fp) C).trans (hfR.isContractedBy_iff C)
      isIso_app := fun U => by
        have := hfR.isIso_app (inv fp ⁻¹ᵁ U)
        rw [Scheme.Hom.comp_app]
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance this }
  rcases (IsContractionOfFace.trichotomy_of_isExtremalRay hXQ hRay hgF).1 with hfib | hdiv | hsm
  · refine absurd hfib.dim_lt ?_
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' sX
      (MMP.Mori.isBirationalMorphism_comp hfbir (isBirationalMorphism_of_isIso (inv fp)))]
    exact lt_irrefl _
  · exact hdiv
  · exact absurd
      { isNormalVariety_source := hfR.isNormalVariety_source
        isNormalVariety_target := hVn
        comp_eq := hfR.comp_eq
        isProper := isProper_of_isProjectiveMorphism _ hfR.isProjectiveMorphism
        isBirationalMorphism := hfbir
        two_le_codimension :=
          exceptionalSet_comp_of_isIso f (inv fp) ▸ hsm.two_le_codimension } hns

end Divisorial

/-- **Elementary steps of projective dlt pairs preserve `ℚ`-factoriality and dlt.** Over an
algebraically closed field of characteristic zero, let `(X, Δ) ⇢ (X', Δ')` be the elementary step
of a `(K + Δ)`-negative extremal ray of a projective `ℚ`-factorial dlt pair `(X, Δ)` with rational
boundary (the flip of its contraction when that is small, the divisorial contraction otherwise),
with `Δ'` the birational transform of `Δ`. Then `X'` is `ℚ`-factorial and `(X', Δ')` is dlt. -/
@[mmp "thm_fourfold_projective_dlt_step_preserved"]
public theorem IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X V X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {K : Divisor X} {Δ : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V}
    {fp : X' ⟶ V} {Δ' : QDivisor X'}
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ') :
    IsQFactorial sX' ∧ MMP.Intersection.IsDltPair sX' Δ' := by
  obtain ⟨⟨hXp, hXQ, ⟨n, hK⟩, hdltI⟩, hRneg, hfR, hfbir, hcomp, rfl, hcase⟩ := h
  have hdlt : MMP.Mori.IsDltPair sX n K Δ :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK Δ).mp hdltI
  have hVp := isProjectiveVariety_of_isContractionOfRay hXp hXQ hdlt hRneg hfR
  have ⟨_, hRay, hneg⟩ := hRneg
  have hface : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R :=
    ⟨hRay.1, hRay.1.2.2.1, hneg⟩
  rcases hcase with ⟨-, hflipOf⟩ | ⟨hns, hiso⟩
  · -- the flip case
    haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hXp
    haveI : QuasiCompact sX := hXp.toIsVariety.toQuasiCompact
    haveI : IsNormal V := hfR.isNormalVariety_target.2
    haveI : LocallyOfFiniteType sV := hfR.isNormalVariety_target.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
    have hflip := isFlip_of_isFlipOf hK hflipOf
    have hM' := hflip.isDltPair hdlt
    exact ⟨MMP.Mori.isQFactorial_of_isFlip hXQ hdlt hRay hface
      { isProjectiveVariety_source := hXp
        isProjectiveVariety_target := hVp
        comp_eq := hfR.comp_eq
        isExtremalFace := hRay.1
        isContractedBy_iff := hfR.isContractedBy_iff
        isIso_app := hfR.isIso_app } hflip,
      (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX' hM'.1.2.1 _).mpr hM'⟩
  · -- the divisorial case: `f ≫ (f⁺)⁻¹` is a divisorial contraction of `R`
    haveI := hiso
    have hX'p : MMP.Mori.IsProjectiveVariety k sX' := by
      rw [← hcomp]
      exact isProjectiveVariety_of_isIso hVp fp
    have hdiv := isDivisorialContraction_comp_inv hXp hX'p hXQ hRay hfR hfbir hcomp hns
    have : IsSeparated sV := hfR.isNormalVariety_target.1.toIsSeparated
    have : IsSeparated sX' := hX'p.toIsVariety.toIsSeparated
    haveI := isSeparated_toTerminal sV
    haveI := isSeparated_toTerminal sX'
    have hM' := IsDivisorialContraction.isDltPair_transformDivisor hXQ hRneg hdiv hdlt
    rw [transformDivisor_comp_inv_eq_flipTransform f fp Δ] at hM'
    exact ⟨isQFactorial_of_isDltPair_of_isDivisorialContraction_or_isFiberTypeContraction
      hXQ hdlt hface (Or.inl hdiv),
      (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX' hM'.1.2.1 _).mpr hM'⟩

end MMP.Fourfold

end
