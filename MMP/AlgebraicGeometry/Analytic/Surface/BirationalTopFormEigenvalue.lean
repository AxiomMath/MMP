module
import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AbsoluteForms
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryAlgebra
import MMP.AlgebraicTopology.ComplexProjectiveSpace.Cohomology
import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.AlgebraicGeometry.Analytic.Surface.TopFormBettiClass
import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti
import MMP.AlgebraicTopology.PoincareDuality.Excision
import MMP.AlgebraicTopology.PoincareDuality.Localize
import MMP.AlgebraicTopology.PoincareDuality.PuncturedLow
import MMP.AlgebraicTopology.PoincareDuality.CompactApprox
import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
import StacksFrontier.AlgebraicGeometry.Modules.PushforwardUnitHomEquiv
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.DeRham.LogFormsCriterion
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Analytic.PluriformIntegrableGauge
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Chow.FieldSituation
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting

/-!
# Eigenvalues of birational self-maps on holomorphic two-forms of a surface

Let `Z` be a smooth projective complex surface, not necessarily connected, and let
`g : Z ⇢ Z` be a birational self-map. Suppose a nonzero regular two-form `ω ∈ H⁰(Z, Ω²_{Z/ℂ})`
satisfies `g^* ω = μ ω`. Resolve the graph of `g` by `p, q : W → Z`. Then `r_p ∘ q^*` is an
integral endomorphism of `H²(Z, ℤ)/torsion ≅ ℤ^{b₂(Z)}`, and the Betti class of `ω` is a
nonzero eigenvector of it with eigenvalue `μ`. So `μ` is an algebraic integer of degree at
most `b₂(Z)`. Every field automorphism of `ℂ` carries the data to a conjugate surface, map and
form, with eigenvalue the conjugate of `μ`. The integral `∫ ω ∧ ω̄ > 0` is invariant under
birational pull-back, so every conjugate of `μ` has absolute value one. The uniform bound
`MMP.Fourfold.exists_pow_eq_one_of_bounded_degree_unit_conjugates` then gives `μ ^ N = 1` for
an integer `N > 0` that depends only on a bound for `b₂(Z)`.

## Main results

* `MMP.Fourfold.exists_pow_eq_one_of_birational_surface_top_form_eigenvalue`: for every `b`
  there is `N > 0` such that, on every smooth projective complex surface with
  `dim_ℚ H²(Z^an; ℚ) ≤ b`, every eigenvalue `μ` of a birational self-map on a nonzero
  holomorphic two-form is an algebraic integer of degree at most `b`, all of whose conjugates
  have absolute value one, and `μ ^ N = 1`.
* `MMP.Fourfold.pluriformPullback_injective`: over a field of characteristic zero, pull-back
  of rational pluriforms along a homomorphism of function fields of integral schemes of the same
  dimension is injective; `MMP.Fourfold.pullbackForms_injective` is its field-theoretic form,
  along an extension with a pull-back generator.

## Implementation notes

* A birational self-map `g : Z ⇢ Z` is represented by an open immersion `f : U ⟶ Z` over `ℂ`,
  where `U ⊆ Z` is a dense open and the image of `f` is dense. Every birational self-map of a
  reduced scheme of finite type has such a representative, which is an isomorphism between
  dense opens. The components of `Z` may be permuted.
* `g^* ω = μ ω` is stated on `U`. The pull-back `f^* ω` of `ω` along `f` equals `μ` times the
  restriction `ι^* ω` along the inclusion `ι : U ⟶ Z`, as sections of `Ω²_{U/ℂ}`. A form is
  pulled back by the unit of `f^* ⊣ f_*`, followed by the canonical map
  `f^* Ω²_{Z/ℂ} ⟶ Ω²_{U/ℂ}` (`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`).
* `H²(Z, ℚ)` is the singular cohomology `MMP.relativeSingularCohomology` of the
  complex points `MMP.Analytic.ComplexPoints.analyticSpace sZ`. The statement is uniform over
  every surface with `b₂ ≤ b`, not only those with `b₂ = b`.

## References

* [K. Ueno, *Classification theory of algebraic varieties and compact complex spaces*],
  LNM 439, §14.
-/

open CategoryTheory AlgebraicGeometry Opposite MMP.Analytic.ComplexPoints MMP

namespace MMP.Fourfold

open IntermediateField

/-! ### Conjugates are images under field automorphisms of `ℂ` -/

/-- Every root in `ℂ` of the minimal polynomial of an algebraic number `μ` is the image of `μ`
under a field automorphism of `ℂ`. -/
private theorem exists_ringEquiv_apply_eq {μ : ℂ} (hμ : IsIntegral ℚ μ) {z : ℂ}
    (hz : z ∈ (minpoly ℚ μ).rootSet ℂ) : ∃ σ : ℂ ≃+* ℂ, σ μ = z := by
  classical
  set F := ℚ⟮μ⟯ with hF
  have hroot : z ∈ (minpoly ℚ μ).aroots ℂ := by
    rw [Polynomial.mem_rootSet] at hz
    rw [Polynomial.mem_roots_map_of_injective (algebraMap ℚ ℂ).injective (minpoly.ne_zero hμ)]
    exact hz.2
  let τ : F →ₐ[ℚ] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hμ).symm ⟨z, hroot⟩
  have hτ : τ (IntermediateField.AdjoinSimple.gen ℚ μ) = z :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hμ _
  let F' : IntermediateField ℚ ℂ := τ.fieldRange
  let e₀ : F ≃+* F' := (AlgEquiv.ofInjectiveField τ).toRingEquiv
  have hFc : Cardinal.mk F ≤ Cardinal.aleph0 := by
    have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional hμ
    simpa using Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
  have hF'c : Cardinal.mk F' ≤ Cardinal.aleph0 := by
    rw [← Cardinal.mk_congr e₀.toEquiv]; exact hFc
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F ℂ
  obtain ⟨s', hs'⟩ := exists_isTranscendenceBasis F' ℂ
  obtain ⟨e⟩ := Cardinal.eq.1
    ((IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hFc hC).symm.trans
      (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs' hF'c hC))
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs'
  let E : Algebra.adjoin F (Set.range ((↑) : s → ℂ)) ≃+*
      Algebra.adjoin F' (Set.range ((↑) : s' → ℂ)) :=
    hs.1.aevalEquiv.symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv _ e₀).trans
        ((MvPolynomial.renameEquiv F' e).toRingEquiv.trans hs'.1.aevalEquiv.toRingEquiv))
  have hE : ∀ r : F, E (algebraMap F _ r) = algebraMap F' _ (e₀ r) := by
    intro r
    simp only [E, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    simp only [MvPolynomial.mapEquiv_apply]
    simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C,
      MvPolynomial.rename_C]
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ E, ?_⟩
  have h := IsAlgClosure.equivOfEquiv_algebraMap ℂ ℂ E
    (algebraMap F _ (IntermediateField.AdjoinSimple.gen ℚ μ))
  rw [hE] at h
  rw [← hτ]
  convert h using 1
  · rfl
  · rfl

/-! ### Pull-back of global forms along commutative squares -/

section FormPull

variable {X X' X'' S S' S'' : Scheme.{0}}

/-- The pull-back `f^* ω` of a global relative `n`-form along a commutative square
`f ≫ p = p' ≫ g`: the unit of `f^* ⊣ f_*` followed by the canonical map
`f^* Ω^n_{X/S} ⟶ Ω^n_{X'/S'}`. -/
private noncomputable def formPull (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    (h : f ≫ p = p' ≫ g) (n : ℤ)
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    (Scheme.Hom.relativeDifferentialForms p' n).val.obj (op ⊤) :=
  (Scheme.Hom.relativeDifferentialFormsMap f p p' g h n).app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app ⊤ ω)

private theorem formPull_congr {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂) (p : X ⟶ S) (p' : X' ⟶ S')
    {g₁ g₂ : S' ⟶ S} (e' : g₁ = g₂) (h₁ : f₁ ≫ p = p' ≫ g₁) (h₂ : f₂ ≫ p = p' ≫ g₂) (n : ℤ)
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    formPull f₁ p p' g₁ h₁ n ω = formPull f₂ p p' g₂ h₂ n ω := by
  subst e e'
  rfl

/-- Pull-back of forms along a composite of two commutative squares is the composite of the
pull-backs. -/
private theorem formPull_comp (f : X' ⟶ X) (f' : X'' ⟶ X') (p : X ⟶ S) (p' : X' ⟶ S')
    (p'' : X'' ⟶ S'') (g : S' ⟶ S) (g' : S'' ⟶ S') (g'' : S'' ⟶ S)
    (h : f ≫ p = p' ≫ g) (h' : f' ≫ p' = p'' ≫ g') (h'' : (f' ≫ f) ≫ p = p'' ≫ g'') (n : ℤ)
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    formPull (f' ≫ f) p p'' g'' h'' n ω =
      formPull f' p' p'' g' h' n (formPull f p p' g h n ω) := by
  unfold formPull
  rw [Scheme.Hom.relativeDifferentialFormsMap_comp f f' p p' p'' g g' g'' h h' h'' n]
  have key := SheafOfModules.Hom.congr_val_app
    (pullbackComp_unit f' f (Scheme.Hom.relativeDifferentialForms p n)) (op ⊤) ω
  have nat := SheafOfModules.Hom.congr_val_app
    ((Scheme.Modules.pullbackPushforwardAdjunction f').unit.naturality
      (Scheme.Hom.relativeDifferentialFormsMap f p p' g h n)) (op ⊤)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app ⊤ ω)
  have e := (congrArg (fun x => ((Scheme.Modules.pullback f').map
    (Scheme.Hom.relativeDifferentialFormsMap f p p' g h n)).val.app (op ⊤) x) key).trans nat.symm
  exact congrArg
    (fun y => (Scheme.Hom.relativeDifferentialFormsMap f' p' p'' g' h' n).val.app (op ⊤) y) e

/-- Pull-back of forms is semilinear along `f^♯` on global sections. -/
private theorem formPull_smul (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    (h : f ≫ p = p' ≫ g) (n : ℤ) (a : X.ringCatSheaf.obj.obj (op ⊤))
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    formPull f p p' g h n (a • ω) =
      (show X'.ringCatSheaf.obj.obj (op ⊤) from f.appTop a) • formPull f p p' g h n ω := by
  unfold formPull
  have := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    (Scheme.Hom.relativeDifferentialForms p n)).val.app (op ⊤) |>.hom.map_smul a ω
  erw [this]
  exact (Scheme.Hom.relativeDifferentialFormsMap f p p' g h n).val.app (op ⊤) |>.hom.map_smul _ _

/-- Pull-back of forms along an identity square with an invertible base is injective. -/
private theorem formPull_id_injective (p : X ⟶ S) (p' : X ⟶ S') (g : S' ⟶ S) [IsIso g]
    (h : 𝟙 X ≫ p = p' ≫ g) (n : ℤ) : Function.Injective (formPull (𝟙 X) p p' g h n) := by
  intro ω₁ ω₂ e
  haveI : IsIso (Scheme.Hom.relativeDifferentialsMap (𝟙 X) p p' g h) :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isIso _ _ _ _ _
  haveI : IsIso (Scheme.Hom.relativeDifferentialFormsMap (𝟙 X) p p' g h n) :=
    Scheme.Hom.isIso_relativeDifferentialFormsMap _ _ _ _ _ inferInstance n
  set F := Scheme.Hom.relativeDifferentialFormsMap (𝟙 X) p p' g h n with hF
  have hinv : ∀ x, (CategoryTheory.inv F).val.app (op ⊤) (F.val.app (op ⊤) x) = x :=
    fun x => SheafOfModules.Hom.congr_val_app (IsIso.hom_inv_id F) (op ⊤) x
  have e' := congrArg ((CategoryTheory.inv F).val.app (op ⊤)) e
  unfold formPull at e'
  erw [hinv, hinv] at e'
  have := congrArg (((Scheme.Modules.pullbackId X).hom.app _).val.app (op ⊤)) e'
  exact (Scheme.Modules.pullbackId_hom_app_unit _ ⊤ ω₁).symm.trans
    (this.trans (Scheme.Modules.pullbackId_hom_app_unit _ ⊤ ω₂))

end FormPull

/-- The eigen-relation `f^* ω = μ · ι^* ω` on `U` for a two-form `ω` on `Z`. -/
private def IsFormEigen {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (U : Z.Opens)
    (f : U.toScheme ⟶ Z) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) : Prop :=
  formPull f sZ (U.ι ≫ sZ) (𝟙 _) (by simp [hf]) 2 ω =
    (show U.toScheme.ringCatSheaf.obj.obj (op ⊤) from
        (U.ι ≫ sZ).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
      formPull U.ι sZ (U.ι ≫ sZ) (𝟙 _) (by simp) 2 ω

private theorem formPull_zero {X X' S S' : Scheme.{0}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (h : f ≫ p = p' ≫ g) (n : ℤ) : formPull f p p' g h n 0 = 0 := by
  unfold formPull
  erw [map_zero, map_zero]
  rfl

/-! ### Forms on integral smooth schemes are determined on dense opens -/

section DenseOpen

/-- An exterior power of a projective module is projective. -/
private theorem projective_exteriorPower {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Projective R M] (n : ℕ) : Module.Projective R (⋀[R]^n M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

/-- The forms of a smooth morphism over an affine open of the source mapping to an affine open of
the target form a projective module. -/
private theorem projective_sections_forms {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (W : X.affineOpens) (V : S.affineOpens) (e : W.1 ≤ f ⁻¹ᵁ V.1) (d : ℕ) :
    Module.Projective Γ(X, W.1) Γ(Scheme.Hom.relativeDifferentialForms f (d : ℤ), W.1) := by
  have hsm : (f.appLE V.1 W.1 e).hom.Smooth := HasRingHomProperty.appLE (P := @Smooth) f
    inferInstance V W e
  letI := (f.appLE V.1 W.1 e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(S, V.1) Γ(X, W.1) := hsm
  haveI : Module.Projective Γ(X, W.1) (CommRingCat.KaehlerDifferential (f.appLE V.1 W.1 e)) :=
    inferInstanceAs (Module.Projective Γ(X, W.1) Ω[Γ(X, W.1)⁄Γ(S, V.1)])
  haveI := projective_exteriorPower (R := Γ(X, W.1))
    (M := CommRingCat.KaehlerDifferential (f.appLE V.1 W.1 e)) d
  exact Module.Projective.of_equiv
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f W.2 V.2 e d).toLinearEquiv.symm

/-- On an integral scheme, a global section of a quasi-coherent module on whose affine sections
nonzero functions act injectively, vanishing on a nonempty open, vanishes. -/
private theorem eq_zero_of_res_eq_zero_of_isSMulRegular {X : Scheme.{0}} [IsIntegral X]
    (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ (W : X.affineOpens), (W.1 : Set X).Nonempty → ∀ (g : Γ(X, W.1)), g ≠ 0 →
      IsSMulRegular Γ(M, W.1) g)
    (s : Γ(M, ⊤)) {O : X.Opens} (hO : (O : Set X).Nonempty)
    (hs : M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op s = 0) : s = 0 := by
  refine (Scheme.Modules.isSheaf M).section_ext (U := op ⊤) (t := 0) fun x _ => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  obtain ⟨y, hyW, hyO⟩ := nonempty_preirreducible_inter W.isOpen O.isOpen ⟨x, hxW⟩ hO
  obtain ⟨g, hgle, hyg⟩ := hW.exists_basicOpen_le ⟨y, hyO⟩ hyW
  refine ⟨W, le_top, hxW, ?_⟩
  rw [map_zero]
  have hz : M.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen g ≤ W)).op
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      show homOfLE (inf_le_left : W ⊓ X.basicOpen g ≤ W) ≫ homOfLE (le_top : W ≤ ⊤) =
        homOfLE (inf_le_right.trans hgle : W ⊓ X.basicOpen g ≤ O) ≫ homOfLE (le_top : O ≤ ⊤)
        from rfl,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  obtain ⟨k, hk⟩ := Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact M g W
    hW.isCompact le_rfl _ hz
  have hid : X.presheaf.map (homOfLE (le_refl W)).op g = g := by simp
  rw [hid] at hk
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [X.basicOpen_zero] at hyg
    exact hyg
  exact hM ⟨W, hW⟩ ⟨x, hxW⟩ (g ^ k) (pow_ne_zero _ hg0) (hk.trans (smul_zero _).symm)

/-- On an integral scheme smooth over an affine base, a global form vanishing on a nonempty open
vanishes. -/
private theorem eq_zero_of_res_eq_zero {X S : Scheme.{0}} [IsIntegral X] (f : X ⟶ S) [Smooth f]
    [IsAffine S] (d : ℕ) (s : Γ(Scheme.Hom.relativeDifferentialForms f (d : ℤ), ⊤))
    {O : X.Opens} (hO : (O : Set X).Nonempty)
    (hs : (Scheme.Hom.relativeDifferentialForms f (d : ℤ)).presheaf.map
      (homOfLE (le_top : O ≤ ⊤)).op s = 0) : s = 0 := by
  haveI := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f d
  refine eq_zero_of_res_eq_zero_of_isSMulRegular _ (fun W hWne g hg => ?_) s hO hs
  haveI : Nonempty W.1 := hWne.to_subtype
  haveI : IsDomain Γ(X, W.1) := inferInstance
  haveI := projective_sections_forms f W ⟨⊤, isAffineOpen_top S⟩ (by simp) d
  exact Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero hg)

/-- Pull-back of a form along the inclusion of an open is zero only if the restriction of the
form to that open is zero. -/
private theorem res_eq_zero_of_formPull_ι_eq_zero {X S : Scheme.{0}} (p : X ⟶ S) (O : X.Opens)
    (n : ℤ) (η : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤))
    (h : formPull O.ι p (O.ι ≫ p) (𝟙 _) (by simp) n η = 0) :
    (Scheme.Hom.relativeDifferentialForms p n).presheaf.map
      (homOfLE (O.ι.image_preimage_le ⊤)).op η = 0 := by
  have hc : O.ι ≫ p = (O.ι ≫ p) ≫ 𝟙 S := (Category.comp_id _).symm
  have hF : IsIso (Scheme.Hom.relativeDifferentialFormsMap O.ι p (O.ι ≫ p) (𝟙 S) hc n) :=
    Scheme.Hom.isIso_relativeDifferentialFormsMap _ _ _ _ _ inferInstance n
  let e := @asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap O.ι p (O.ι ≫ p) (𝟙 S) hc n) hF
  have hinv : ∀ x, e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) x) = x :=
    fun x => SheafOfModules.Hom.congr_val_app e.hom_inv_id (op ⊤) x
  have h1 := congrArg (e.inv.val.app (op ⊤)) h
  unfold formPull at h1
  erw [hinv, map_zero] at h1
  have key := SheafOfModules.Hom.congr_val_app (Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction O.ι) (Scheme.Modules.pullbackPushforwardAdjunction O.ι)
    (Scheme.Hom.relativeDifferentialForms p n)) (op ⊤) η
  have h2 : ((Scheme.Modules.restrictFunctorIsoPullback O.ι).hom.app
      (Scheme.Hom.relativeDifferentialForms p n)).app (O.ι ⁻¹ᵁ ⊤)
      ((Scheme.Hom.relativeDifferentialForms p n).presheaf.map
        (homOfLE (O.ι.image_preimage_le ⊤)).op η) = 0 :=
    key.trans h1
  have hiso := SheafOfModules.Hom.congr_val_app
    ((Scheme.Modules.restrictFunctorIsoPullback O.ι).hom_inv_id_app
      (Scheme.Hom.relativeDifferentialForms p n)) (op (O.ι ⁻¹ᵁ ⊤))
    ((Scheme.Hom.relativeDifferentialForms p n).presheaf.map
        (homOfLE (O.ι.image_preimage_le ⊤)).op η)
  refine hiso.symm.trans ?_
  change ((Scheme.Modules.restrictFunctorIsoPullback O.ι).inv.app
      (Scheme.Hom.relativeDifferentialForms p n)).app (O.ι ⁻¹ᵁ ⊤)
          (((Scheme.Modules.restrictFunctorIsoPullback O.ι).hom.app
      (Scheme.Hom.relativeDifferentialForms p n)).app (O.ι ⁻¹ᵁ ⊤)
      ((Scheme.Hom.relativeDifferentialForms p n).presheaf.map
        (homOfLE (O.ι.image_preimage_le ⊤)).op η)) = 0
  rw [h2, map_zero]

private theorem formPull_sub {X X' S S' : Scheme.{0}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (h : f ≫ p = p' ≫ g) (n : ℤ)
    (ω₁ ω₂ : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    formPull f p p' g h n (ω₁ - ω₂) = formPull f p p' g h n ω₁ - formPull f p p' g h n ω₂ := by
  unfold formPull
  erw [map_sub, map_sub]
  rfl

/-- **Forms are determined on a nonempty open.** On an integral scheme smooth over `ℂ`, two
global forms with the same pull-back to a nonempty open are equal. -/
private theorem eq_of_formPull_ι_eq {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Spec (.of ℂ))
    [Smooth s] (O : X.Opens) (hO : (O : Set X).Nonempty)
    (ω₁ ω₂ : (Scheme.Hom.relativeDifferentialForms s 2).val.obj (op ⊤))
    (h : formPull O.ι s (O.ι ≫ s) (𝟙 _) (by simp) 2 ω₁ =
      formPull O.ι s (O.ι ≫ s) (𝟙 _) (by simp) 2 ω₂) : ω₁ = ω₂ := by
  rw [← sub_eq_zero]
  have h0 := res_eq_zero_of_formPull_ι_eq_zero s O 2 (ω₁ - ω₂)
    (by rw [formPull_sub, h, sub_self])
  refine eq_zero_of_res_eq_zero (d := 2) s _ (O := O.ι ''ᵁ (O.ι ⁻¹ᵁ ⊤)) ?_ h0
  obtain ⟨x, hx⟩ := hO
  exact ⟨x, ⟨x, hx⟩, trivial, rfl⟩

end DenseOpen

/-! ### Transport along a field automorphism -/

/-- The conjugate of the data by a field automorphism `σ` of `ℂ`: the same scheme, open and map,
with structure morphism twisted by `Spec σ`, carries a nonzero two-form with eigenvalue
`σ μ`. -/
private theorem exists_isFormEigen_conj (σ : ℂ ≃+* ℂ) {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ) (U : Z.Opens)
    (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) :
    ∃ (sZ' : Z ⟶ Spec (.of ℂ)) (_ : IsProjectiveMorphism sZ')
      (_ : SmoothOfRelativeDimension 2 sZ') (hf' : f ≫ sZ' = U.ι ≫ sZ')
      (ω' : (Scheme.Hom.relativeDifferentialForms sZ' 2).val.obj (op ⊤)),
      ω' ≠ 0 ∧ IsFormEigen sZ' U f hf' ω' (σ μ) := by
  let φ : Spec (.of ℂ) ⟶ Spec (.of ℂ) :=
    Spec.map (RingEquiv.toCommRingCatIso σ.symm).hom
  haveI : IsIso φ := inferInstance
  have hφμ : φ.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv (σ μ)) = (Scheme.ΓSpecIso (.of ℂ)).inv μ := by
    have := congrArg (fun χ => χ (σ μ))
      (Scheme.ΓSpecIso_inv_naturality (RingEquiv.toCommRingCatIso σ.symm).hom)
    have h2 : ((RingEquiv.toCommRingCatIso σ.symm).hom ≫ (Scheme.ΓSpecIso (.of ℂ)).inv) (σ μ) =
        (Scheme.ΓSpecIso (.of ℂ)).inv μ := by
      rw [CommRingCat.comp_apply]
      congr 1
      exact σ.symm_apply_apply μ
    exact this.symm.trans h2
  have hS' : SmoothOfRelativeDimension 2 (sZ ≫ φ) := by
    haveI : SmoothOfRelativeDimension 0 φ := inferInstance
    simpa using (inferInstance : SmoothOfRelativeDimension (2 + 0) (sZ ≫ φ))
  have hf' : f ≫ sZ ≫ φ = U.ι ≫ sZ ≫ φ := by rw [reassoc_of% hf]
  let Θ : ∀ {X : Scheme.{0}} (s : X ⟶ Spec (.of ℂ)),
      (Scheme.Hom.relativeDifferentialForms s 2).val.obj (op ⊤) →
        (Scheme.Hom.relativeDifferentialForms (s ≫ φ) 2).val.obj (op ⊤) :=
    fun s => formPull (𝟙 _) s (s ≫ φ) (inv φ) (by simp) 2
  refine ⟨sZ ≫ φ, IsProjectiveMorphism.of_iso (Iso.refl Z) (asIso φ) (by simp) hP, hS', hf',
    Θ sZ ω, fun h0 => hω (formPull_id_injective _ _ _ _ _
      (h0.trans (formPull_zero _ _ _ _ _ _).symm)), ?_⟩
  have e1 : formPull f (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (𝟙 _) (by simp [hf']) 2 (Θ sZ ω) =
      Θ (U.ι ≫ sZ) (formPull f sZ (U.ι ≫ sZ) (𝟙 _) (by simp [hf]) 2 ω) := by
    refine (formPull_comp (𝟙 Z) f sZ (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (inv φ) (𝟙 _) (inv φ)
      (by simp) (by simp [hf']) (by simp [hf])  2 ω).symm.trans ?_
    refine (formPull_congr (show f ≫ 𝟙 Z = 𝟙 _ ≫ f by simp) _ _ rfl _ (by simp [hf]) 2 ω).trans ?_
    exact formPull_comp f (𝟙 _) sZ (U.ι ≫ sZ) (U.ι ≫ sZ ≫ φ) (𝟙 _) (inv φ) (inv φ)
      (by simp [hf]) (by simp) (by simp [hf]) 2 ω
  have e2 : formPull U.ι (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (𝟙 _) (by simp) 2 (Θ sZ ω) =
      Θ (U.ι ≫ sZ) (formPull U.ι sZ (U.ι ≫ sZ) (𝟙 _) (by simp) 2 ω) := by
    refine (formPull_comp (𝟙 Z) U.ι sZ (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (inv φ) (𝟙 _) (inv φ)
      (by simp) (by simp) (by simp) 2 ω).symm.trans ?_
    refine (formPull_congr (show U.ι ≫ 𝟙 Z = 𝟙 _ ≫ U.ι by simp) _ _ rfl _ (by simp) 2 ω).trans ?_
    exact formPull_comp U.ι (𝟙 _) sZ (U.ι ≫ sZ) (U.ι ≫ sZ ≫ φ) (𝟙 _) (inv φ) (inv φ)
      (by simp) (by simp) (by simp) 2 ω
  change formPull f (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (𝟙 _) _ 2 (Θ sZ ω) =
    _ • formPull U.ι (sZ ≫ φ) (U.ι ≫ sZ ≫ φ) (𝟙 _) _ 2 (Θ sZ ω)
  rw [e1, e2, he]
  refine (formPull_smul _ _ _ _ _ _ _ _).trans ?_
  congr 1
  change Scheme.Hom.appTop (𝟙 U.toScheme) (Scheme.Hom.appTop (U.ι ≫ sZ) _) =
    Scheme.Hom.appTop ((U.ι ≫ sZ) ≫ φ) _
  rw [Scheme.Hom.comp_appTop (U.ι ≫ sZ) φ, CommRingCat.comp_apply, hφμ]
  simp

/-! ### Roots of algebraic numbers -/

/-- If `μ ^ k` is algebraic for some `k > 0`, then so is `μ`, and its degree is at most `k` times
the degree of `μ ^ k`. -/
private theorem isIntegral_and_natDegree_minpoly_le_of_pow {μ : ℂ} {k : ℕ} (hk : 0 < k)
    (h : IsIntegral ℚ (μ ^ k)) :
    IsIntegral ℚ μ ∧ (minpoly ℚ μ).natDegree ≤ k * (minpoly ℚ (μ ^ k)).natDegree := by
  have hμ : IsIntegral ℚ μ := IsIntegral.of_pow hk h
  refine ⟨hμ, ?_⟩
  set K := ℚ⟮μ ^ k⟯
  have hμK : IsIntegral K μ := hμ.tower_top
  have h3 : (minpoly K μ).natDegree ≤ k := by
    have hp : (Polynomial.X ^ k - Polynomial.C (⟨μ ^ k, mem_adjoin_simple_self ℚ _⟩ : K)).Monic :=
      Polynomial.monic_X_pow_sub_C _ hk.ne'
    have hroot : Polynomial.aeval μ
        (Polynomial.X ^ k - Polynomial.C (⟨μ ^ k, mem_adjoin_simple_self ℚ _⟩ : K)) = 0 := by
      simp
    have := Polynomial.natDegree_le_natDegree (minpoly.min K μ hp hroot)
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  haveI : FiniteDimensional ℚ K := adjoin.finiteDimensional h
  haveI : FiniteDimensional K K⟮μ⟯ := adjoin.finiteDimensional hμK
  have htower := Module.finrank_mul_finrank ℚ K K⟮μ⟯
  have hle : ℚ⟮μ⟯ ≤ (K⟮μ⟯).restrictScalars ℚ := by
    rw [adjoin_le_iff]; simpa using mem_adjoin_simple_self K μ
  have h5 : Module.finrank ℚ ℚ⟮μ⟯ ≤ Module.finrank ℚ K⟮μ⟯ := by
    haveI : FiniteDimensional ℚ K⟮μ⟯ := Module.Finite.trans K _
    haveI : FiniteDimensional ℚ ((K⟮μ⟯).restrictScalars ℚ) := this
    exact IntermediateField.finrank_le_of_le_right hle
  rw [← adjoin.finrank hμ, ← adjoin.finrank h]
  rw [← adjoin.finrank hμK] at h3
  nlinarith [h3, htower, h5]

/-! ### Periods of two-dimensional classes over integral cycles -/

section PeriodsCore

open MMP SingularChain SingularCochain Finsupp

/-- **Integrality from a stable lattice.** If `μ` maps the `ℤ`-span of `v : Fin n → ℂ` into
itself and `v ≠ 0`, then `μ` is an algebraic integer of degree at most `n`. -/
private lemma isIntegral_of_smul_mem_span {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0) (μ : ℂ)
    (h : ∀ i, μ * v i ∈ Submodule.span ℤ (Set.range v)) :
    IsIntegral ℤ μ ∧ (minpoly ℚ μ).natDegree ≤ n := by
  classical
  choose M hM using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (h i)
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of M
  have hAv : (A.map (Int.castRingHom ℂ)).mulVec v = μ • v := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, A, Pi.smul_apply,
      smul_eq_mul]
    rw [← hM i]
    simp [zsmul_eq_mul]
  have hdet : (Matrix.scalar (Fin n) μ - A.map (Int.castRingHom ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hAv]
    simp [Matrix.scalar_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hroot : Polynomial.aeval μ A.charpoly = 0 := by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  refine ⟨⟨A.charpoly, Matrix.charpoly_monic A, hroot⟩, ?_⟩
  calc (minpoly ℚ μ).natDegree ≤ (A.charpoly.map (Int.castRingHom ℚ)).natDegree :=
        Polynomial.natDegree_le_of_dvd
          (minpoly.dvd _ _ (by rwa [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]))
          ((Matrix.charpoly_monic A).map _).ne_zero
    _ = n := by rw [(Matrix.charpoly_monic A).natDegree_map, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin]

section Periods

variable {Y : TopCat.{0}}

/-- Change of coefficients of chains along an additive map. -/
private noncomputable def achain {R S : Type*} [CommRing R] [CommRing S] (f : R →+ S) {n : ℕ} :
    Chain R Y n →+ Chain S Y n :=
  Finsupp.mapRange.addMonoidHom f

private lemma achain_single {R S : Type*} [CommRing R] [CommRing S] (f : R →+ S) {n : ℕ}
    (σ : Simplex Y n) (a : R) : achain f (single σ a) = single σ (f a) :=
  Finsupp.mapRange_single (hf := map_zero f)

private lemma bd_achain {R S : Type*} [CommRing R] [CommRing S] (f : R →+ S) {n : ℕ}
    (c : Chain R Y (n + 1)) : bd S n (achain f c) = achain f (bd R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single σ a =>
    rw [achain_single, show (single σ (f a) : Chain S Y (n + 1)) = f a • single σ 1 by
        rw [smul_single, smul_eq_mul, mul_one],
      show (single σ a : Chain R Y (n + 1)) = a • single σ 1 by
        rw [smul_single, smul_eq_mul, mul_one], map_smul, map_smul, bd_single, bd_single]
    simp only [Finset.smul_sum, smul_single, smul_eq_mul, map_sum, achain_single, mul_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h | h
    · have h' : (-1 : R) ^ (i : ℕ) = 1 := by exact_mod_cast congrArg (Int.cast (R := R)) h
      have h'' : (-1 : S) ^ (i : ℕ) = 1 := by exact_mod_cast congrArg (Int.cast (R := S)) h
      rw [h', h'', mul_one, mul_one]
    · have h' : (-1 : R) ^ (i : ℕ) = -1 := by exact_mod_cast congrArg (Int.cast (R := R)) h
      have h'' : (-1 : S) ^ (i : ℕ) = -1 := by exact_mod_cast congrArg (Int.cast (R := S)) h
      rw [h', h'', mul_neg_one, mul_neg_one, map_neg]

/-- Change of coefficients of chains along a ring homomorphism. -/
private noncomputable def rchain {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} :
    Chain R Y n →+ Chain S Y n :=
  achain f.toAddMonoidHom

private lemma rchain_single {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (σ : Simplex Y n) (a : R) : rchain f (single σ a) = single σ (f a) :=
  achain_single f.toAddMonoidHom σ a

private lemma rchain_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (c : Chain R Y n) (σ : Simplex Y n) : rchain f c σ = f (c σ) := rfl

private lemma rchain_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) {n : ℕ} (c : Chain R Y n) : rchain g (rchain f c) = rchain (g.comp f) c := by
  ext σ; rfl

private lemma bd_rchain {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (c : Chain R Y (n + 1)) : bd S n (rchain f c) = rchain f (bd R n c) :=
  bd_achain f.toAddMonoidHom c

private lemma rchain_mapDomain {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {Y' : TopCat.{0}} (g : Y' ⟶ Y) {n : ℕ} (c : Chain R Y' n) :
    rchain f (Finsupp.mapDomain g.hom.comp c) = Finsupp.mapDomain g.hom.comp (rchain f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, Finsupp.mapDomain_add]
  | single σ a => rw [Finsupp.mapDomain_single, rchain_single, rchain_single,
      Finsupp.mapDomain_single]

/-- An integral chain, as a chain with complex coefficients. -/
private noncomputable abbrev cplx {n : ℕ} : Chain ℤ Y n →+ Chain ℂ Y n := rchain (Int.castRingHom ℂ)

private lemma bd_cplx {n : ℕ} (c : Chain ℤ Y (n + 1)) : bd ℂ n (cplx c) = cplx (bd ℤ n c) :=
  bd_rchain _ c

private lemma cplx_mapDomain {Y' : TopCat.{0}} (g : Y' ⟶ Y) {n : ℕ} (c : Chain ℤ Y' n) :
    cplx (Finsupp.mapDomain g.hom.comp c) = Finsupp.mapDomain g.hom.comp (cplx c) :=
  rchain_mapDomain _ g c

private lemma bd_mapDomain {R : Type*} [CommRing R] {Y' Z : Type*} [TopologicalSpace Y']
    [TopologicalSpace Z] (g : C(Y', Z)) {n : ℕ} (c : Chain R Y' (n + 1)) :
    bd R n (Finsupp.mapDomain g.comp c) = Finsupp.mapDomain g.comp (bd R n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [Finsupp.mapDomain_add, map_add, hc, hd, map_add, Finsupp.mapDomain_add]
  | single σ a =>
    rw [Finsupp.mapDomain_single,
      show (single σ a : Chain R Y' (n + 1)) = a • single σ 1 by rw [smul_single, smul_eq_mul,
          mul_one],
      show (single (g.comp σ) a : Chain R Z (n + 1)) = a • single (g.comp σ) 1 by
        rw [smul_single, smul_eq_mul, mul_one],
      map_smul, map_smul, bd_single, bd_single, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_finset_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, ContinuousMap.comp_assoc]

/-- The integral `2`-cycles of a space. -/
private noncomputable abbrev cycles2 (Y : TopCat.{0}) : Submodule ℤ (Chain ℤ Y 2) :=
  LinearMap.ker (bd ℤ 1)

private lemma eval_relCoboundaries_cplx_eq_zero (c : cycles2 Y) :
    ∀ φ ∈ relCoboundaries ℂ (∅ : Set Y) 2, eval φ (cplx c.1) = 0 := by
  rintro _ ⟨ψ, -, rfl⟩
  rw [eval_coboundary, bd_cplx, show bd ℤ 1 c.1 = 0 from c.2, map_zero, map_zero]

/-- The period `⟨x, c⟩ ∈ ℂ` of a class `x ∈ H²(Y; ℂ)` over an integral `2`-cycle `c`. -/
private noncomputable def period (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2) :
    cycles2 Y →+ ℂ where
  toFun c := relEval (cplx c.1) (eval_relCoboundaries_cplx_eq_zero c)
    (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
  map_zero' := by
    obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
      (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
    simp only [← hφ, relEval_mk, ZeroMemClass.coe_zero, map_zero]
  map_add' c d := by
    obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
      (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
    simp only [← hφ, relEval_mk, Submodule.coe_add, map_add]

private lemma period_eq_eval (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2)
    (φ : relCocycles ℂ (∅ : Set Y) 2)
    (hφ : relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x = Submodule.Quotient.mk φ)
    (c : cycles2 Y) : period x c = eval φ.1 (cplx c.1) := by
  simp only [period, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hφ, relEval_mk]

private lemma period_smul (a : ℂ) (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2)
    (c : cycles2 Y) : period (a • x) c = a * period x c := by
  simp only [period, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, smul_eq_mul]

/-- Push-forward of integral `2`-cycles along a continuous map. -/
private noncomputable def pushCycles {Y' : TopCat.{0}} (g : Y' ⟶ Y) : cycles2 Y' →ₗ[ℤ] cycles2 Y :=
  ((Finsupp.lmapDomain ℤ ℤ g.hom.comp).comp (cycles2 Y').subtype).codRestrict _ fun c => by
    change bd ℤ 1 (Finsupp.mapDomain g.hom.comp c.1) = 0
    rw [bd_mapDomain, show bd ℤ 1 c.1 = 0 from c.2, Finsupp.mapDomain_zero]

private lemma pushCycles_coe {Y' : TopCat.{0}} (g : Y' ⟶ Y) (c : cycles2 Y') :
    (pushCycles g c).1 = Finsupp.mapDomain g.hom.comp c.1 := rfl

/-- **Naturality of periods**: `⟨g^* x, c⟩ = ⟨x, g_* c⟩`. -/
private lemma period_map {Y' : TopCat.{0}} (g : Y' ⟶ Y)
    (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2) (c : cycles2 Y') :
    period ((relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) g (Set.empty_subset _) 2).hom x) c
      = period x (pushCycles g c) := by
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
  have h1 : relativeSingularCohomologyEquiv ℂ (∅ : Set Y') 2
      ((relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) g (Set.empty_subset _) 2).hom x) =
      relCohomologyMap ℂ g (Set.empty_subset _) 2
        (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x) :=
    relativeSingularCohomologyEquiv_map g (Set.empty_subset _) 2 x
  rw [← hφ, relCohomologyMap_mk] at h1
  rw [period_eq_eval _ _ h1, period_eq_eval _ _ hφ.symm, pushCycles_coe, cplx_mapDomain,
    eval_cochainPullback]

private lemma eval_rchain {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (φ : Simplex Y n → R) (c : Chain R Y n) :
    SingularCochain.eval (f ∘ φ) (rchain f c) = f (SingularCochain.eval φ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, hc, hd, map_add, map_add]
  | single σ a => simp [rchain_single, SingularCochain.eval, linearCombination_single, smul_eq_mul]

/-- **Duality over a field**: a chain on which every cocycle vanishes is a boundary. -/
private lemma exists_bd_eq_of_forall_eval_eq_zero {K : Type} [Field K] {n : ℕ}
    (c : Chain K Y (n + 1))
    (h : ∀ χ : Simplex Y (n + 1) → K, coboundary K (n + 1) χ = 0 → SingularCochain.eval χ c = 0) :
    ∃ b, bd K (n + 1) b = c := by
  by_contra hb
  have hmem : c ∉ LinearMap.range (bd K (n + 1)) := fun ⟨b, hb'⟩ => hb ⟨b, hb'⟩
  obtain ⟨g, hgc, hg⟩ := Submodule.exists_le_ker_of_notMem hmem
  refine hgc ?_
  let χ : Simplex Y (n + 1) → K := fun σ => g (single σ 1)
  have hχ : ∀ d, SingularCochain.eval χ d = g d := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d e hd he => rw [map_add, map_add, hd, he]
    | single σ a =>
      rw [show (single σ a : Chain K Y (n + 1)) = a • single σ 1 by
        rw [smul_single, smul_eq_mul, mul_one], map_smul, map_smul]
      simp [χ, SingularCochain.eval, linearCombination_single]
  rw [← hχ]
  refine h χ ?_
  funext σ
  have := hg (LinearMap.mem_range_self (bd K (n + 1)) (single σ 1))
  rw [LinearMap.mem_ker, ← hχ, ← eval_coboundary] at this
  simpa [SingularCochain.eval, linearCombination_single] using this

/-- Clearing denominators in a rational chain. -/
private lemma exists_rchain_int_eq_smul {n : ℕ} (e : Chain ℚ Y n) :
    ∃ N : ℕ, 0 < N ∧ ∃ d : Chain ℤ Y n, rchain (Int.castRingHom ℚ) d = (N : ℚ) • e := by
  induction e using Finsupp.induction_linear with
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add e e' he he' =>
    obtain ⟨N, hN, d, hd⟩ := he
    obtain ⟨N', hN', d', hd'⟩ := he'
    refine ⟨N * N', Nat.mul_pos hN hN', (N' : ℤ) • d + (N : ℤ) • d', ?_⟩
    rw [map_add, map_zsmul, map_zsmul, hd, hd', smul_add, ← Int.cast_smul_eq_zsmul ℚ,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
    congr 2 <;> push_cast <;> ring
  | single σ q =>
    refine ⟨q.den, q.den_pos, single σ q.num, ?_⟩
    rw [rchain_single, smul_single, smul_eq_mul]
    congr 1
    simp [Rat.mul_den_eq_num]

/-- **Complex cycles are spanned by integral ones**: a complex cochain vanishing on all integral
cycles vanishes on all complex cycles. -/
private lemma eval_eq_zero_of_forall_int {n : ℕ} (φ : Simplex Y (n + 1) → ℂ)
    (hφ : ∀ d : Chain ℤ Y (n + 1), bd ℤ n d = 0 → SingularCochain.eval φ (cplx d) = 0)
    (c : Chain ℂ Y (n + 1)) (hc : bd ℂ n c = 0) : SingularCochain.eval φ c = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace ℚ ℂ
  have key : ∀ i, SingularCochain.eval φ (rchain (algebraMap ℚ ℂ)
      (achain (B.coord i).toAddMonoidHom c)) = 0 := by
    intro i
    obtain ⟨N, hN, d, hd⟩ := exists_rchain_int_eq_smul (achain (B.coord i).toAddMonoidHom c)
    have hcyc : bd ℚ n (achain (B.coord i).toAddMonoidHom c) = 0 := by
      rw [bd_achain, hc, map_zero]
    have hdcyc : bd ℤ n d = 0 := by
      have : rchain (Int.castRingHom ℚ) (bd ℤ n d) = 0 := by
        rw [← bd_rchain, hd, map_smul, hcyc, smul_zero]
      ext σ
      have := congrArg (fun e => e σ) this
      simpa [rchain_apply] using this
    have h1 := hφ d hdcyc
    have h2 : cplx d = (N : ℂ) • rchain (algebraMap ℚ ℂ) (achain (B.coord i).toAddMonoidHom c) := by
      have : cplx d = rchain (algebraMap ℚ ℂ) (rchain (Int.castRingHom ℚ) d) := by
        rw [rchain_comp]; congr 1
      rw [this, hd]
      ext σ
      simp [rchain_apply]
    rw [h2, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN.ne')
  let I : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ) :=
    c.support.biUnion fun σ => (B.repr (c σ)).support
  have hc' : c = ∑ i ∈ I, B i • rchain (algebraMap ℚ ℂ) (achain (B.coord i).toAddMonoidHom c) := by
    ext σ
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      rchain_apply, smul_eq_mul]
    have hsub : (B.repr (c σ)).support ⊆ I := by
      by_cases hσ : σ ∈ c.support
      · exact Finset.subset_biUnion_of_mem (fun σ => (B.repr (c σ)).support) hσ
      · rw [Finsupp.notMem_support_iff.1 hσ, map_zero, Finsupp.support_zero]
        exact Finset.empty_subset _
    conv_lhs => rw [← B.linearCombination_repr (c σ)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, mul_comm]
    rfl
  rw [hc', map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, key, smul_zero]

/-- A nonzero class `x ∈ H²(Y; ℂ)` has a nonzero period over some integral `2`-cycle. -/
private lemma exists_period_ne_zero {x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2}
    (hx : x ≠ 0) : ∃ c : cycles2 Y, period x c ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
  have hcob : φ.1 ∈ relCoboundaries ℂ (∅ : Set Y) (1 + 1) := by
    refine MMP.Topology.mem_relCoboundaries_of_forall_eval_eq_zero ∅ 1 fun c hc => ?_
    refine eval_eq_zero_of_forall_int φ.1 (fun d hd => ?_) c (eq_zero_of_mem_inside_empty_set hc)
    have := h ⟨d, hd⟩
    rwa [period_eq_eval _ _ hφ.symm] at this
  apply hx
  apply (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2).injective
  rw [map_zero, ← hφ]
  exact (Submodule.Quotient.mk_eq_zero _).2 hcob

/-- Periods vanish on boundaries. -/
private lemma period_bd (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2)
    (w : Chain ℤ Y 3) : period x ⟨bd ℤ 2 w, by
      change bd ℤ 1 (bd ℤ 2 w) = 0; exact bd_bd 1 w⟩ = 0 := by
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
  rw [period_eq_eval _ _ hφ.symm]
  change SingularCochain.eval φ.1 (cplx (bd ℤ 2 w)) = 0
  rw [← bd_cplx, ← eval_coboundary, show coboundary ℂ 2 φ.1 = 0 from φ.2.2]
  simp [SingularCochain.eval]

private lemma vanishing_compl_univ {R : Type*} [CommRing R] (n : ℕ) (φ : Simplex Y n → R) :
    φ ∈ vanishing R n (Set.univ : Set Y)ᶜ := fun σ hσ =>
  absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp)

/-- A rational `2`-cycle on which a spanning family of cocycles vanishes is killed by every
rational cocycle. -/
private lemma eval_eq_zero_of_span_eq_top {ι : Type*} [Fintype ι]
    (v : ι → MMP.Analytic.singularCohomology ℚ Y 2) (hv : Submodule.span ℚ (Set.range v) = ⊤)
    (ψ' : ι → relCocycles ℚ (Set.univ : Set Y)ᶜ 2)
    (hvψ : ∀ j, relativeSingularCohomologyEquiv ℚ (Set.univ : Set Y)ᶜ 2 (v j) =
      Submodule.Quotient.mk (ψ' j))
    {rc : Chain ℚ Y 2} (hrc : bd ℚ 1 rc = 0) (hψ : ∀ j, SingularCochain.eval (ψ' j).1 rc = 0)
    {χ : Simplex Y 2 → ℚ} (hχ : coboundary ℚ 2 χ = 0) : SingularCochain.eval χ rc = 0 := by
  have hχmem : χ ∈ relCocycles ℚ (Set.univ : Set Y)ᶜ 2 := ⟨vanishing_compl_univ 2 χ, hχ⟩
  let y := (relativeSingularCohomologyEquiv ℚ (Set.univ : Set Y)ᶜ 2).symm
    (Submodule.Quotient.mk ⟨χ, hχmem⟩)
  have hy : y ∈ Submodule.span ℚ (Set.range v) := by
    rw [hv]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hy
  have h2 := congrArg (relativeSingularCohomologyEquiv ℚ (Set.univ : Set Y)ᶜ 2) ha
  simp only [y, LinearEquiv.apply_symm_apply, map_sum, map_smul, hvψ] at h2
  have h3 : Submodule.Quotient.mk (p := (relCoboundaries ℚ (Set.univ : Set Y)ᶜ 2).comap
      (relCocycles ℚ (Set.univ : Set Y)ᶜ 2).subtype)
      (⟨χ, hχmem⟩ - ∑ j, a j • ψ' j) = 0 := by
    rw [Submodule.Quotient.mk_sub, ← h2, sub_eq_zero]
    simp only [← Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  obtain ⟨β, -, hβ⟩ := (Submodule.Quotient.mk_eq_zero _).1 h3
  have h5 : SingularCochain.eval (χ - ∑ j, a j • (ψ' j).1) rc = 0 := by
    have : χ - ∑ j, a j • (ψ' j).1 = coboundary ℚ 1 β := by
      rw [hβ]; simp
    rw [this, eval_coboundary, hrc, map_zero]
  rw [← evalAt_apply, map_sub, map_sum] at h5
  simpa [evalAt_apply, hψ] using h5

/-- The image of a `ℤ`-spanning set of `H²(Y; ℤ)` under a base change to `ℚ` spans
`H²(Y; ℚ)`. -/
private lemma span_image_eq_top_of_isBaseChange
    (ρ : MMP.Analytic.singularCohomology ℤ Y 2 →ₗ[ℤ] MMP.Analytic.singularCohomology ℚ Y 2)
    (hbc : IsBaseChange ℚ ρ) {G : Set (MMP.Analytic.singularCohomology ℤ Y 2)}
    (hG : Submodule.span ℤ G = ⊤) : Submodule.span ℚ (ρ '' G) = ⊤ := by
  refine eq_top_iff.2 fun n _ =>
    hbc.inductionOn n (motive := (· ∈ Submodule.span ℚ (ρ '' G))) (fun m => ?_) (fun s n hn => Submodule.smul_mem _ s hn) (fun _ _ => add_mem)
  have hm : m ∈ Submodule.span ℤ G := by rw [hG]; trivial
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_of_tower_mem _ a hx

/-- The periods of a class vanish on an integral `2`-cycle whose rationalization is killed by
every rational cocycle. -/
private lemma period_eq_zero_of_forall_eval_rchain
    (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2) (c : cycles2 Y)
    (hQ : ∀ χ : Simplex Y 2 → ℚ, coboundary ℚ 2 χ = 0 →
      SingularCochain.eval χ (rchain (Int.castRingHom ℚ) c.1) = 0) :
    period x c = 0 := by
  obtain ⟨b, hb⟩ := exists_bd_eq_of_forall_eval_eq_zero (n := 1) _ hQ
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv ℂ (∅ : Set Y) 2 x)
  rw [period_eq_eval _ _ hφ.symm]
  have hcplx : cplx c.1 = bd ℂ 2 (rchain (algebraMap ℚ ℂ) b) := by
    rw [bd_rchain, hb, rchain_comp]
    rfl
  rw [hcplx, ← eval_coboundary, show coboundary ℂ 2 φ.1 = 0 from φ.2.2]
  simp [SingularCochain.eval]

/-- **Finiteness of periods.** If `H²(Y; ℤ)` is finitely generated and `H²(Y; ℤ) → H²(Y; ℚ)` is a
base change, then the periods of all complex classes factor through a homomorphism from the
integral `2`-cycles to `ℤ^r`, `r ≤ dim H²(Y; ℚ)`. -/
private lemma exists_linearMap_period_eq_zero
    [hfin : Module.Finite ℤ (MMP.Analytic.singularCohomology ℤ Y 2)]
    (ρ : MMP.Analytic.singularCohomology ℤ Y 2 →ₗ[ℤ] MMP.Analytic.singularCohomology ℚ Y 2)
    (hρ : ∀ h, ρ h = MMP.Analytic.singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 h)
    (hbc : IsBaseChange ℚ ρ) :
    ∃ r ≤ Module.finrank ℚ (MMP.Analytic.singularCohomology ℚ Y 2),
      ∃ Ψ : cycles2 Y →ₗ[ℤ] (Fin r → ℤ),
        ∀ x c, Ψ c = 0 → period x c = 0 := by
  classical
  obtain ⟨G, hG⟩ := hfin.fg_top
  let T : Set (MMP.Analytic.singularCohomology ℚ Y 2) := ρ '' (G : Set _)
  have hT : T.Finite := (G.finite_toSet).image _
  have hspanT : Submodule.span ℚ T = ⊤ := span_image_eq_top_of_isBaseChange ρ hbc hG
  obtain ⟨t, htT, hspant, hli⟩ := exists_linearIndependent ℚ T
  have htf : t.Finite := hT.subset htT
  haveI : Fintype t := htf.fintype
  haveI : FiniteDimensional ℚ (MMP.Analytic.singularCohomology ℚ Y 2) :=
    Module.finite_def.2 ⟨hT.toFinset, by rw [Set.Finite.coe_toFinset, hspanT]⟩
  set r := Fintype.card t
  have hr : r ≤ Module.finrank ℚ (MMP.Analytic.singularCohomology ℚ Y 2) :=
    hli.fintype_card_le_finrank
  let e : Fin r ≃ t := (Fintype.equivFin t).symm
  have hv : ∀ j, ∃ h ∈ (G : Set _), ρ h = (e j : MMP.Analytic.singularCohomology ℚ Y 2) :=
    fun j => htT (e j).2
  choose h _ hh using hv
  have hrep : ∀ j, ∃ ψ : relCocycles ℤ (Set.univ : Set Y)ᶜ 2,
      relativeSingularCohomologyEquiv ℤ (Set.univ : Set Y)ᶜ 2 (h j) = Submodule.Quotient.mk ψ :=
    fun j => (Submodule.Quotient.mk_surjective _ _).imp fun _ h => h.symm
  choose ψ hψ using hrep
  refine ⟨r, hr, LinearMap.pi fun j => (SingularCochain.eval (ψ j).1).comp (cycles2 Y).subtype,
    fun x c hc => ?_⟩
  have hc' : ∀ j, SingularCochain.eval (ψ j).1 c.1 = 0 := fun j => congrFun hc j
  set rc := rchain (Int.castRingHom ℚ) c.1 with hrc
  have hrc_cyc : bd ℚ 1 rc = 0 := by
    rw [hrc, bd_rchain, show bd ℤ 1 c.1 = 0 from c.2, map_zero]
  have hej : ∀ j, relativeSingularCohomologyEquiv ℚ (Set.univ : Set Y)ᶜ 2
      (e j : MMP.Analytic.singularCohomology ℚ Y 2) = Submodule.Quotient.mk
        (MMP.Analytic.singularCohomology.relCocyclesMap (Int.castRingHom ℚ) _ 2 (ψ j)) := by
    intro j
    rw [← hh j, hρ]
    simp only [MMP.Analytic.singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.apply_symm_apply, hψ]
    rfl
  have hrange : Set.range (fun j => (e j : MMP.Analytic.singularCohomology ℚ Y 2)) = t :=
    (e.surjective.range_comp Subtype.val).trans Subtype.range_coe
  set ψ' := fun j => MMP.Analytic.singularCohomology.relCocyclesMap (Int.castRingHom ℚ)
    (Set.univ : Set Y)ᶜ 2 (ψ j) with hψ'
  have h6 : ∀ j, SingularCochain.eval (ψ' j).1 rc = 0 := by
    intro j
    have : (ψ' j).1 = (Int.castRingHom ℚ) ∘ (ψ j).1 := rfl
    rw [this, hrc, eval_rchain, hc' j, map_zero]
  exact period_eq_zero_of_forall_eval_rchain x c fun χ hχ =>
    eval_eq_zero_of_span_eq_top _ (by rw [hrange, hspant, hspanT]) ψ' hej hrc_cyc h6 hχ

/-- **Integrality from periods.** Let `x ≠ 0` be a class in `H²(Y; ℂ)` whose periods factor through
a homomorphism `Ψ` from the integral `2`-cycles to `ℤ^r`. If multiplication by `μ` preserves the
group of periods of `x`, then `μ` is an algebraic integer of degree at most `r`. -/
private lemma isIntegral_of_period_mul_mem
    {x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) Y ∅ 2}
    (hx : x ≠ 0) {r : ℕ} (Ψ : cycles2 Y →ₗ[ℤ] (Fin r → ℤ))
    (hΨ : ∀ c, Ψ c = 0 → period x c = 0) (μ : ℂ)
    (hstab : ∀ c, ∃ c', period x c' = μ * period x c) :
    IsIntegral ℤ μ ∧ (minpoly ℚ μ).natDegree ≤ r := by
  classical
  let N := LinearMap.range Ψ
  obtain ⟨t, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin r)) N
  have ht : t ≤ r := by
    have h1 := Submodule.finrank_le N
    rw [Module.finrank_eq_card_basis b, Module.finrank_fin_fun] at h1
    simpa using h1
  let θ : N →ₗ[ℤ] ℂ :=
    (LinearMap.ker Ψ).liftQ (period x).toIntLinearMap (fun c hc => hΨ c hc) ∘ₗ
      Ψ.quotKerEquivRange.symm.toLinearMap
  have hθ : ∀ c, θ ⟨Ψ c, LinearMap.mem_range_self Ψ c⟩ = period x c := by
    intro c
    simp only [θ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let v : Fin t → ℂ := fun i => θ (b i)
  have hmem : ∀ c, period x c ∈ Submodule.span ℤ (Set.range v) := by
    intro c
    rw [← hθ c, ← b.linearCombination_repr ⟨Ψ c, _⟩, Finsupp.linearCombination_apply,
        map_finsuppSum]
    exact Submodule.sum_mem _ fun i _ => by
      simp only [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hv : v ≠ 0 := by
    obtain ⟨c, hc⟩ := exists_period_ne_zero hx
    intro h0
    have := hmem c
    rw [h0] at this
    have hsub : Set.range (0 : Fin t → ℂ) ⊆ {0} := by rintro _ ⟨i, rfl⟩; rfl
    have h2 := Submodule.span_mono (R := ℤ) hsub this
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at h2
    exact hc h2
  refine (isIntegral_of_smul_mem_span v hv μ fun i => ?_).imp id fun h => h.trans ht
  obtain ⟨c, hc⟩ := (b i).2
  obtain ⟨c', hc'⟩ := hstab c
  have : v i = period x c := by
    rw [← hθ c]
    show θ (b i) = θ ⟨Ψ c, _⟩
    rw [show (⟨Ψ c, LinearMap.mem_range_self Ψ c⟩ : N) = b i from Subtype.ext hc]
  rw [this, ← hc']
  exact hmem c'

end Periods

/-- `H₂(ℂ², ℂ² - p; ℤ) = 0`. -/
private lemma relVanishing_fin_two_complex (p : Fin 2 → ℂ) :
    RelVanishing ℤ (Fin 2 → ℂ) 1 {p} := by
  have hdim : Module.finrank ℝ (Fin 4 → ℝ) = Module.finrank ℝ (Fin 2 → ℂ) := by
    rw [Module.finrank_fin_fun, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  let L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 2 → ℂ) := ContinuousLinearEquiv.ofFinrankEq hdim
  let h : (Fin 4 → ℝ) ≃ₜ (Fin 2 → ℂ) := L.toHomeomorph.trans (Homeomorph.addRight p)
  have h0 : h '' {0} = {p} := by
    rw [Set.image_singleton]
    simp [h]
  rw [← h0]
  exact RelVanishing.of_homeomorph h (relVanishing_singleton_zero_low 4 1 (by norm_num))

/-- On the complex points of a smooth complex surface, `H₂(X, X - x; ℤ) = 0` at every point. -/
private lemma relVanishing_singleton_complexPoints {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [SmoothOfRelativeDimension 2 sX] [IsSeparated sX] (x : MMP.Analytic.ComplexPoints sX) :
    RelVanishing ℤ (MMP.Analytic.ComplexPoints sX) 1 {x} := by
  obtain ⟨c, hc⟩ := MMP.Analytic.ComplexPoints.EtaleCoordinateChart.exists_mem_W (n := 2) x
  let e := c.toOpenPartialHomeomorph
  have hxs : {x} ⊆ e.source := by
    rw [Set.singleton_subset_iff,
        MMP.Analytic.ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph]
    exact hc
  refine RelVanishing.of_openPartialHomeomorph e isClosed_singleton hxs ?_
  rw [Set.image_singleton]
  exact RelVanishing.subtype e.open_target isClosed_singleton
    (Set.singleton_subset_iff.2 (e.map_source (hxs rfl))) (relVanishing_fin_two_complex _)

/-- Mayer–Vietoris over a finite set of points. -/
private lemma relVanishing_of_finite {Y : Type*} [TopologicalSpace Y] [T1Space Y] (F : Set Y)
    (hF : F.Finite) (h : ∀ x ∈ F, RelVanishing ℤ Y 1 {x}) : RelVanishing ℤ Y 1 F := by
  induction F, hF using Set.Finite.induction_on with
  | empty => exact relVanishing_empty 1
  | @insert x F hxF hF ih =>
    rw [Set.insert_eq]
    refine RelVanishing.union isClosed_singleton hF.isClosed (h x (Set.mem_insert _ _))
      (ih fun y hy => h y (Set.mem_insert_of_mem _ hy)) ?_
    rw [Set.singleton_inter_eq_empty.2 hxF]
    exact relVanishing_empty 2

section Moving

private lemma subtypeVal_comp_injective {Y : TopCat.{0}} (U : Set Y) (n : ℕ) :
    Function.Injective fun τ : Simplex (TopCat.of U) n => (ContinuousMap.subtypeVal U).comp τ := by
  intro τ τ' h
  ext t
  exact congrArg (fun σ : Simplex Y n => σ t) h

/-- A chain lying in a subset is the push-forward of a chain of the subspace. -/
private lemma exists_mapDomain_eq_of_mem_inside {Y : TopCat.{0}} {U : Set Y} {n : ℕ}
    {c : Chain ℤ Y n}
    (hc : c ∈ inside ℤ n U) :
    ∃ c' : Chain ℤ (TopCat.of U) n,
      Finsupp.mapDomain (ContinuousMap.subtypeVal U).comp c' = c := by
  have hinj := subtypeVal_comp_injective U n
  refine ⟨Finsupp.comapDomain _ c hinj.injOn, Finsupp.mapDomain_comapDomain _ hinj _ ?_⟩
  intro σ hσ
  exact ⟨⟨fun t => ⟨σ t, hc hσ ⟨t, rfl⟩⟩, by fun_prop⟩, by ext; rfl⟩

/-- **Periods of an eigenclass.** Let `P, Q : X_W → X` be continuous maps and `F ⊆ X` a set with
`H₂(X, X - F; ℤ) = 0` over whose complement `P` has a continuous section `s`. If a class
`x ∈ H²(X; ℂ)` satisfies `Q^* x = μ P^* x`, then multiplication by `μ` preserves the periods of
`x` over integral `2`-cycles. -/
private lemma exists_period_eq_mul {X XW : TopCat.{0}} (P Q : XW ⟶ X) {F : Set X}
    (hF : RelVanishing ℤ X 1 F) (s : TopCat.of ↥Fᶜ ⟶ XW)
    (hs : ∀ y, P (s y) = y.1)
    (x : relativeSingularCohomology ℂ (ModuleCat.of ℂ ℂ) X ∅ 2) (μ : ℂ)
    (hxy : (relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) Q (Set.empty_subset _) 2).hom x =
      μ • (relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) P (Set.empty_subset _) 2).hom x)
    (c : cycles2 X) : ∃ c', period x c' = μ * period x c := by
  obtain ⟨w, hw⟩ := hF c.1 (by rw [show bd ℤ 1 c.1 = 0 from c.2]; exact zero_mem _)
  have hmem : c.1 - bd ℤ 2 w ∈ cycles2 X := by
    change bd ℤ 1 _ = 0
    rw [map_sub, show bd ℤ 1 c.1 = 0 from c.2, bd_bd, sub_zero]
  obtain ⟨c₀', hc₀'⟩ := exists_mapDomain_eq_of_mem_inside hw
  have hcyc : bd ℤ 1 c₀' = 0 := by
    have h1 : Finsupp.mapDomain (ContinuousMap.subtypeVal (Fᶜ : Set X)).comp (bd ℤ 1 c₀') = 0 := by
      rw [← bd_mapDomain, hc₀', map_sub, show bd ℤ 1 c.1 = 0 from c.2, bd_bd, sub_zero]
    exact Finsupp.mapDomain_injective (subtypeVal_comp_injective (Fᶜ : Set X) 1)
      (h1.trans (Finsupp.mapDomain_zero).symm)
  let c₁ : cycles2 XW := pushCycles s ⟨c₀', hcyc⟩
  have hP : pushCycles P c₁ = ⟨c.1 - bd ℤ 2 w, hmem⟩ := by
    apply Subtype.ext
    change Finsupp.mapDomain P.hom.comp (Finsupp.mapDomain s.hom.comp c₀') = _
    rw [← Finsupp.mapDomain_comp]
    refine Eq.trans ?_ hc₀'
    congr 1
    funext τ
    ext t
    exact hs (τ t)
  refine ⟨pushCycles Q c₁, ?_⟩
  have hc : c = ⟨c.1 - bd ℤ 2 w, hmem⟩ + ⟨bd ℤ 2 w, by
      change bd ℤ 1 (bd ℤ 2 w) = 0; exact bd_bd 1 w⟩ := Subtype.ext (by simp)
  have hper : period x c = period x ⟨c.1 - bd ℤ 2 w, hmem⟩ := by
    conv_lhs => rw [hc]
    rw [map_add, period_bd, add_zero]
  rw [← period_map, hxy, period_smul, period_map, hP, hper]

end Moving

end PeriodsCore

/-! ### Eigen-maps between surfaces -/

section EigenMap

/-- Pull-back of a constant multiple of a form. -/
private theorem formPull_const_smul {X X' S : Scheme.{0}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S)
    (h : f ≫ p = p' ≫ 𝟙 S) (n : ℤ) (c : Γ(S, ⊤))
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    formPull f p p' (𝟙 S) h n ((show X.ringCatSheaf.obj.obj (op ⊤) from p.appTop c) • ω) =
      (show X'.ringCatSheaf.obj.obj (op ⊤) from p'.appTop c) • formPull f p p' (𝟙 S) h n ω := by
  rw [formPull_smul]
  have h' : f ≫ p = p' := by simpa using h
  have : f.appTop (p.appTop c) = p'.appTop c := by
    rw [← h', Scheme.Hom.comp_appTop]; rfl
  exact congrArg (· • formPull f p p' (𝟙 S) h n ω) this

/-- An open immersion `f : U ⟶ Y` from a nonempty open `U ⊆ X` over `ℂ` multiplying a two-form:
`f^* ω_Y = μ · ω_X|_U`. -/
private structure EigenMap {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (ωX : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤))
    (ωY : (Scheme.Hom.relativeDifferentialForms sY 2).val.obj (op ⊤)) (μ : ℂ) where
  U : X.Opens
  nonempty : (U : Set X).Nonempty
  f : U.toScheme ⟶ Y
  isOpenImmersion : IsOpenImmersion f
  comm : f ≫ sY = U.ι ≫ sX
  eigen : formPull f sY (U.ι ≫ sX) (𝟙 _) (by simp [comm]) 2 ωY =
    (show U.toScheme.ringCatSheaf.obj.obj (op ⊤) from
        (U.ι ≫ sX).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
      formPull U.ι sX (U.ι ≫ sX) (𝟙 _) (by simp) 2 ωX

variable {X Y W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
  {sW : W ⟶ Spec (.of ℂ)} {ωX : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤)}
  {ωY : (Scheme.Hom.relativeDifferentialForms sY 2).val.obj (op ⊤)}
  {ωW : (Scheme.Hom.relativeDifferentialForms sW 2).val.obj (op ⊤)}

/-- The identity eigen-map, with eigenvalue one. -/
private noncomputable def EigenMap.id [Nonempty X] (sX : X ⟶ Spec (.of ℂ))
    (ωX : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤)) :
    EigenMap sX sX ωX ωX 1 where
  U := ⊤
  nonempty := ⟨Classical.arbitrary X, trivial⟩
  f := (⊤ : X.Opens).ι
  isOpenImmersion := inferInstance
  comm := rfl
  eigen := by
    rw [map_one, map_one]
    exact (((Scheme.Hom.relativeDifferentialForms ((⊤ : X.Opens).ι ≫ sX) 2).val.obj
      (op ⊤)).isModule.one_smul _).symm

/-- The eigenvalue relation for a composite of two eigen-maps. -/
private theorem eigen_comp {μ ν : ℂ} (Ua : X.Opens) (fa : Ua.toScheme ⟶ Y) [IsOpenImmersion fa]
    (ca : fa ≫ sY = Ua.ι ≫ sX)
    (ea : formPull fa sY (Ua.ι ≫ sX) (𝟙 _) (by simp [ca]) 2 ωY =
      (show Ua.toScheme.ringCatSheaf.obj.obj (op ⊤) from
          (Ua.ι ≫ sX).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
        formPull Ua.ι sX (Ua.ι ≫ sX) (𝟙 _) (by simp) 2 ωX)
    (Ub : Y.Opens) (fb : Ub.toScheme ⟶ W) (cb : fb ≫ sW = Ub.ι ≫ sY)
    (eb : formPull fb sW (Ub.ι ≫ sY) (𝟙 _) (by simp [cb]) 2 ωW =
      (show Ub.toScheme.ringCatSheaf.obj.obj (op ⊤) from
          (Ub.ι ≫ sY).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv ν)) •
        formPull Ub.ι sY (Ub.ι ≫ sY) (𝟙 _) (by simp) 2 ωY)
    (h : ((Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv ≫ (fa ∣_ Ub) ≫ fb) ≫ sW =
      ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) ≫ 𝟙 _) :
    formPull ((Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv ≫ (fa ∣_ Ub) ≫ fb) sW
        ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) (𝟙 _) h 2 ωW =
      (show (Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).toScheme.ringCatSheaf.obj.obj (op ⊤) from
          ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv (ν * μ))) •
        formPull (Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι sX ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) (𝟙 _) (by simp) 2
          ωX := by
  have c1 : (fa ⁻¹ᵁ Ub).ι ≫ fa = (fa ∣_ Ub) ≫ Ub.ι := (morphismRestrict_ι _ _).symm
  have c2 : (Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv ≫ (fa ⁻¹ᵁ Ub).ι ≫ Ua.ι =
      (Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι := Scheme.Hom.isoImage_inv_ι _ _
  have s1 : (fa ∣_ Ub) ≫ (Ub.ι ≫ sY) = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ := by
    rw [Category.comp_id, ← Category.assoc, ← c1, Category.assoc, ca]
  have s2 : (Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv ≫ ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) =
      ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) ≫ 𝟙 _ := by
    rw [Category.comp_id, ← c2]; simp only [Category.assoc]
  have s3 : fb ≫ sW = (Ub.ι ≫ sY) ≫ 𝟙 _ := by rw [Category.comp_id, cb]
  have s4 : ((fa ∣_ Ub) ≫ fb) ≫ sW = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ := by
    rw [Category.assoc, s3, Category.comp_id, s1]
  have e1 := formPull_comp ((fa ∣_ Ub) ≫ fb) (Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv sW
    ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) _ (𝟙 _) (𝟙 _) (𝟙 _) s4 s2 h 2 ωW
  have e2 := formPull_comp fb (fa ∣_ Ub) sW (Ub.ι ≫ sY) _ (𝟙 _) (𝟙 _) (𝟙 _) s3 s1 s4 2 ωW
  rw [e1, e2, eb, formPull_const_smul _ _ _ s1, formPull_const_smul _ _ _ s2]
  have s5 : Ub.ι ≫ sY = (Ub.ι ≫ sY) ≫ 𝟙 _ := (Category.comp_id _).symm
  have s6 : ((fa ∣_ Ub) ≫ Ub.ι) ≫ sY = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ := by
    rw [Category.assoc, s1]
  have s7 : ((fa ⁻¹ᵁ Ub).ι ≫ fa) ≫ sY = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ := by
    rw [c1, s6]
  have s8 : fa ≫ sY = (Ua.ι ≫ sX) ≫ 𝟙 _ := by rw [Category.comp_id, ca]
  have s9 : (fa ⁻¹ᵁ Ub).ι ≫ (Ua.ι ≫ sX) = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ :=
    (Category.comp_id _).symm
  have s10 : Ua.ι ≫ sX = (Ua.ι ≫ sX) ≫ 𝟙 _ := (Category.comp_id _).symm
  have s11 : ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι) ≫ sX = ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) ≫ 𝟙 _ := by
    rw [Category.assoc, Category.comp_id]
  have s12 : ((Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv ≫ (fa ⁻¹ᵁ Ub).ι ≫ Ua.ι) ≫ sX =
      ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) ≫ 𝟙 _ := by rw [c2, Category.comp_id]
  have e3 := (formPull_comp Ub.ι (fa ∣_ Ub) sY (Ub.ι ≫ sY) _ (𝟙 _) (𝟙 _) (𝟙 _) s5 s1 s6 2
    ωY).symm
  have e4 := formPull_congr c1.symm sY ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) rfl s6 s7 2 ωY
  have e5 := formPull_comp fa (fa ⁻¹ᵁ Ub).ι sY (Ua.ι ≫ sX) _ (𝟙 _) (𝟙 _) (𝟙 _) s8 s9 s7 2 ωY
  rw [e3, e4, e5, ea, formPull_const_smul _ _ _ s9, formPull_const_smul _ _ _ s2]
  have e6 := (formPull_comp Ua.ι (fa ⁻¹ᵁ Ub).ι sX (Ua.ι ≫ sX) _ (𝟙 _) (𝟙 _) (𝟙 _) s10 s9 s11 2
    ωX).symm
  have e7 := (formPull_comp ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι) (Ua.ι.isoImage (fa ⁻¹ᵁ Ub)).inv sX
    ((fa ⁻¹ᵁ Ub).ι ≫ Ua.ι ≫ sX) _ (𝟙 _) (𝟙 _) (𝟙 _) s11 s2 s12 2 ωX).symm
  have e8 := formPull_congr c2 sX ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) rfl s12 (by simp) 2 ωX
  rw [e6]
  simp only [e7, e8]
  have key : ∀ (A B : (Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).toScheme.ringCatSheaf.obj.obj (op ⊤))
      (x : (Scheme.Hom.relativeDifferentialForms ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) 2).val.obj
        (op ⊤)), A • B • x = (A * B) • x := fun A B x =>
    (((Scheme.Hom.relativeDifferentialForms ((Ua.ι ''ᵁ (fa ⁻¹ᵁ Ub)).ι ≫ sX) 2).val.obj
      (op ⊤)).isModule.mul_smul A B x).symm
  refine (key _ _ _).trans ?_
  congr 1
  simp only [map_mul]
  rfl

/-- The composite of two eigen-maps: `g ∘ f` on `f⁻¹(V)`, with eigenvalue `ν μ`. -/
private noncomputable def EigenMap.comp [IsIntegral Y] {μ ν : ℂ} (a : EigenMap sX sY ωX ωY μ)
    (b : EigenMap sY sW ωY ωW ν) : EigenMap sX sW ωX ωW (ν * μ) :=
  haveI := a.isOpenImmersion
  haveI := b.isOpenImmersion
  have hcomm : ((a.U.ι.isoImage (a.f ⁻¹ᵁ b.U)).inv ≫ (a.f ∣_ b.U) ≫ b.f) ≫ sW =
      (a.U.ι ''ᵁ (a.f ⁻¹ᵁ b.U)).ι ≫ sX := by
    rw [Category.assoc, Category.assoc, b.comm, ← Category.assoc (a.f ∣_ b.U),
      morphismRestrict_ι, Category.assoc, a.comm, ← Scheme.Hom.isoImage_inv_ι_assoc]
  { U := a.U.ι ''ᵁ (a.f ⁻¹ᵁ b.U)
    nonempty := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter a.f.isOpenEmbedding.isOpen_range b.U.isOpen
        (by obtain ⟨x, hx⟩ := a.nonempty; exact ⟨a.f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩) b.nonempty
      obtain ⟨⟨x, rfl⟩, hxb⟩ := hy
      exact ⟨_, x, hxb, rfl⟩
    f := (a.U.ι.isoImage (a.f ⁻¹ᵁ b.U)).inv ≫ (a.f ∣_ b.U) ≫ b.f
    isOpenImmersion := inferInstance
    comm := hcomm
    eigen := eigen_comp a.U a.f a.comm a.eigen b.U b.f b.comm b.eigen _ }

/-- A form whose pull-back along an open immersion from a nonempty scheme vanishes, on an
integral smooth scheme, vanishes. -/
private theorem eq_zero_of_formPull_eq_zero [IsIntegral X] [Smooth sX] {T : Scheme.{0}}
    [Nonempty T] (sT : T ⟶ Spec (.of ℂ)) (h : T ⟶ X) [IsOpenImmersion h]
    (hh : h ≫ sX = sT ≫ 𝟙 _) (η : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤))
    (h0 : formPull h sX sT (𝟙 _) hh 2 η = 0) : η = 0 := by
  let O := h.opensRange
  let e := h.isoOpensRange
  have he : e.hom ≫ O.ι = h := Scheme.Hom.isoOpensRange_hom_ι h
  have h1 : O.ι ≫ sX = (O.ι ≫ sX) ≫ 𝟙 _ := (Category.comp_id _).symm
  have h2 : e.hom ≫ (O.ι ≫ sX) = sT ≫ 𝟙 _ := by rw [← Category.assoc, he, hh]
  have h3 : (e.hom ≫ O.ι) ≫ sX = sT ≫ 𝟙 _ := by rw [he, hh]
  have hc := formPull_comp O.ι e.hom sX (O.ι ≫ sX) sT (𝟙 _) (𝟙 _) (𝟙 _) h1 h2 h3 2 η
  rw [formPull_congr he sX sT rfl h3 hh] at hc
  rw [hc] at h0
  have h4 : e.inv ≫ sT = (O.ι ≫ sX) ≫ 𝟙 _ := by
    have h2' : e.hom ≫ O.ι ≫ sX = sT := by simpa using h2
    rw [Category.comp_id, ← h2', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h5 : (e.inv ≫ e.hom) ≫ (O.ι ≫ sX) = (O.ι ≫ sX) ≫ 𝟙 _ := by
    rw [Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  have h6 : 𝟙 O.toScheme ≫ (O.ι ≫ sX) = (O.ι ≫ sX) ≫ 𝟙 _ := by simp
  have hc2 := formPull_comp e.hom e.inv (O.ι ≫ sX) sT (O.ι ≫ sX) (𝟙 _) (𝟙 _) (𝟙 _) h2 h4 h5 2
    (formPull O.ι sX (O.ι ≫ sX) (𝟙 _) h1 2 η)
  rw [h0, formPull_zero, formPull_congr (Iso.inv_hom_id e) _ _ rfl h5 h6] at hc2
  have h7 := formPull_id_injective (O.ι ≫ sX) (O.ι ≫ sX) (𝟙 _) h6 2
    (hc2.trans (formPull_zero _ _ _ _ h6 2).symm)
  haveI : Nonempty O := ⟨e.hom (Classical.arbitrary T)⟩
  exact eq_of_formPull_ι_eq sX O ⟨_, (Classical.arbitrary O).2⟩ η 0
    (h7.trans (formPull_zero _ _ _ _ _ _).symm)

end EigenMap

/-! ### Components -/

section Components

variable {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} {U : Z.Opens} {f : U.toScheme ⟶ Z}
  [IsOpenImmersion f] {hf : f ≫ sZ = U.ι ≫ sZ}
  {ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)} {μ : ℂ}

/-- The restriction of a two-form to an open. -/
private noncomputable abbrev resForm (sZ : Z ⟶ Spec (.of ℂ)) (O : Z.Opens)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    (Scheme.Hom.relativeDifferentialForms (O.ι ≫ sZ) 2).val.obj (op ⊤) :=
  formPull O.ι sZ (O.ι ≫ sZ) (𝟙 _) (by simp) 2 ω

/-- The eigen-map between two opens `O, O'` induced by `f`, when `f(O ∩ U) ⊆ O'`. -/
private noncomputable def componentEigenMap (he : IsFormEigen sZ U f hf ω μ) (O O' : Z.Opens)
    (hO : ((O.ι ⁻¹ᵁ U : O.toScheme.Opens) : Set O.toScheme).Nonempty)
    (hrange : Set.range ((O.ι ∣_ U) ≫ f) ⊆ (O' : Set Z)) :
    EigenMap (O.ι ≫ sZ) (O'.ι ≫ sZ) (resForm sZ O ω) (resForm sZ O' ω) μ :=
  have hr : Set.range ((O.ι ∣_ U) ≫ f) ⊆ Set.range O'.ι := by
    rw [Scheme.Opens.range_ι]; exact hrange
  have hfac : IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr ≫ O'.ι = (O.ι ∣_ U) ≫ f :=
    IsOpenImmersion.lift_fac _ _ _
  have hcomm : IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr ≫ O'.ι ≫ sZ =
      (O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ := by
    rw [← Category.assoc, hfac, Category.assoc, hf, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  { U := O.ι ⁻¹ᵁ U
    nonempty := hO
    f := IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr
    isOpenImmersion := by
      haveI : IsOpenImmersion (IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr ≫ O'.ι) := by
        rw [hfac]; infer_instance
      exact IsOpenImmersion.of_comp _ O'.ι
    comm := hcomm
    eigen := by
      have s0 : O'.ι ≫ sZ = (O'.ι ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
      have s1 : IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr ≫ (O'.ι ≫ sZ) =
          ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by rw [Category.comp_id, hcomm]
      have s2 : (IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr ≫ O'.ι) ≫ sZ =
          ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by rw [Category.assoc, s1]
      have s3 : ((O.ι ∣_ U) ≫ f) ≫ sZ = ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by rw [← hfac, s2]
      have s4 : f ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _ := by rw [Category.comp_id, hf]
      have s5 : (O.ι ∣_ U) ≫ (U.ι ≫ sZ) = ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by
        rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, Category.assoc]
      have s6 : U.ι ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
      have s7 : ((O.ι ∣_ U) ≫ U.ι) ≫ sZ = ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by
        rw [Category.assoc, s5]
      have s8 : ((O.ι ⁻¹ᵁ U).ι ≫ O.ι) ≫ sZ = ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ := by
        rw [Category.assoc, Category.comp_id]
      have s9 : O.ι ≫ sZ = (O.ι ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
      have s10 : (O.ι ⁻¹ᵁ U).ι ≫ (O.ι ≫ sZ) = ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      have e1 := (formPull_comp O'.ι (IsOpenImmersion.lift O'.ι ((O.ι ∣_ U) ≫ f) hr) sZ
        (O'.ι ≫ sZ) _ (𝟙 _) (𝟙 _) (𝟙 _) s0 s1 s2 2 ω).symm
      have e2 := formPull_congr hfac sZ ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) rfl s2 s3 2 ω
      have e3 := formPull_comp f (O.ι ∣_ U) sZ (U.ι ≫ sZ) _ (𝟙 _) (𝟙 _) (𝟙 _) s4 s5 s3 2 ω
      have e4 := (formPull_comp U.ι (O.ι ∣_ U) sZ (U.ι ≫ sZ) _ (𝟙 _) (𝟙 _) (𝟙 _) s6 s5 s7 2
        ω).symm
      have e5 := formPull_congr (morphismRestrict_ι O.ι U) sZ ((O.ι ⁻¹ᵁ U).ι ≫ O.ι ≫ sZ) rfl
        s7 s8 2 ω
      have e6 := formPull_comp O.ι (O.ι ⁻¹ᵁ U).ι sZ (O.ι ≫ sZ) _ (𝟙 _) (𝟙 _) (𝟙 _) s9 s10 s8 2 ω
      unfold resForm
      simp only [e1, e2, e3]
      unfold IsFormEigen at he
      rw [he, formPull_const_smul _ _ _ s5]
      simp only [e4, e5, e6] }

end Components

/-! ### Decomposition into components -/

section Decomp

open CategoryTheory.Limits

/-- **A normal Noetherian scheme is a finite disjoint union of normal integral schemes**: there are
finitely many open immersions `Yᵢ ⟶ Y` from normal integral schemes, with pairwise disjoint images
covering `Y`. -/
private theorem exists_fin_components (Y : Scheme.{0}) [IsNormal Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] :
    ∃ (k : ℕ) (Yc : Fin k → Scheme.{0}) (_ : ∀ i, IsNormal (Yc i)) (_ : ∀ i, IsIntegral (Yc i))
      (j : ∀ i, Yc i ⟶ Y) (_ : ∀ i, IsOpenImmersion (j i)),
      (∀ i i', i ≠ i' → Disjoint (Set.range (j i)) (Set.range (j i'))) ∧
      ∀ y : Y, ∃ i, y ∈ Set.range (j i) := by
  classical
  have : IsNoetherian Y := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Y := inferInstance
  have hfin : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    fun U _ => @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ _
      (TopologicalSpace.NoetherianSpace.set _)
  obtain ⟨ι, Yc, hNo, hInt, ⟨φ⟩⟩ := (isNormal_iff_exists_iso_coproduct hfin).mp inferInstance
  let j : ∀ c, Yc c ⟶ Y := fun c => Sigma.ι Yc c ≫ φ.inv
  have hdisj : ∀ c c', c ≠ c' → Disjoint (Set.range (j c)) (Set.range (j c')) := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨x', hx'⟩
    have h1 : (Sigma.ι Yc c') x' = (Sigma.ι Yc c) x := by
      change (Sigma.ι Yc c' ≫ φ.inv) x' = (Sigma.ι Yc c ≫ φ.inv) x at hx'
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hx'
      exact φ.inv.isOpenEmbedding.injective hx'
    have := (sigmaι_eq_iff Yc c' c x' x).mp h1
    exact hcc' (congrArg Sigma.fst this).symm
  have hcov : ∀ y : Y, ∃ c, y ∈ Set.range (j c) := by
    intro y
    obtain ⟨⟨c, x⟩, hx⟩ := (sigmaMk Yc).surjective (φ.hom y)
    refine ⟨c, x, ?_⟩
    rw [sigmaMk_mk] at hx
    change (Sigma.ι Yc c ≫ φ.inv) x = y
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hopen : ∀ c, IsOpen (Set.range (j c)) := fun c => (j c).isOpenEmbedding.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun c => Set.range (j c)) hopen
    (fun y _ => Set.mem_iUnion.mpr (hcov y))
  have hι : Finite ι := by
    refine Finite.of_injective (fun c : ι => (⟨c, ?_⟩ : t)) fun c c' h => congrArg Subtype.val h
    obtain ⟨x⟩ : Nonempty (Yc c) := inferInstance
    obtain ⟨c', hc', hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (j c x)))
    by_contra hct
    have hne : c ≠ c' := fun h => hct (h ▸ hc')
    exact Set.disjoint_left.mp (hdisj c c' hne) ⟨x, rfl⟩ hx
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, fun i => Yc (e.symm i), fun i => hNo _, fun i => hInt _,
    fun i => j (e.symm i), fun i => inferInstance, fun i i' hii' => hdisj _ _ ?_, fun y => ?_⟩
  · exact fun h => hii' (e.symm.injective h)
  · obtain ⟨c, hc⟩ := hcov y
    obtain ⟨i, rfl⟩ := e.symm.surjective c
    exact ⟨i, hc⟩

/-- **A smooth projective surface is a finite disjoint union of clopen integral opens.** -/
private theorem exists_integral_opens (Y : Scheme.{0}) [IsNormal Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] :
    ∃ (r : ℕ) (O : Fin r → Y.Opens), (∀ i, IsIntegral (O i).toScheme) ∧
      (∀ i i', i ≠ i' → Disjoint (O i : Set Y) (O i')) ∧ (∀ y : Y, ∃ i, y ∈ O i) := by
  obtain ⟨r, Yc, -, hInt, j, hj, hdisj, hcov⟩ := exists_fin_components Y
  refine ⟨r, fun i => (j i).opensRange, fun i => ?_, hdisj, hcov⟩
  haveI := hInt i
  haveI := hj i
  haveI : IrreducibleSpace (j i).opensRange.toScheme := by
    have hirr : IsIrreducible (Set.range (j i)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ (Yc i)).image _ (j i).continuous.continuousOn
    exact Subtype.irreducibleSpace hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Decomp

/-! ### Second Betti numbers of disjoint clopen pieces -/

section BettiSum

/-- `H²` of a one-point space vanishes. -/
private theorem subsingleton_H2_punit :
    Subsingleton (relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of PUnit.{1})
      (∅ : Set PUnit) 2) := by
  have := MMP.Topology.subsingleton_cohomology_of_unique ℚ (TopCat.of PUnit.{1}) 1
  unfold cohomologyWithSupports at this
  rwa [Set.compl_univ] at this

/-- The map on `H²` of a constant map vanishes. -/
private theorem H2_map_const_eq_zero {A B : TopCat.{0}} (b : B)
    (x : relativeSingularCohomology ℚ (.of ℚ ℚ) B ∅ 2) :
    (relativeSingularCohomology.map ℚ (.of ℚ ℚ) (TopCat.ofHom (ContinuousMap.const A b))
      (A := ∅) (A' := ∅) (fun _ h => h) 2).hom x = 0 := by
  let t : A ⟶ TopCat.of PUnit.{1} := TopCat.ofHom (ContinuousMap.const A PUnit.unit)
  let c : TopCat.of PUnit.{1} ⟶ B := TopCat.ofHom (ContinuousMap.const _ b)
  have hfac : TopCat.ofHom (ContinuousMap.const A b) = t ≫ c := rfl
  have hc := relativeSingularCohomology.map_comp ℚ (.of ℚ ℚ) t c (A'' := ∅) (A' := ∅) (A := ∅)
    (fun _ h => h) (fun _ h => h) 2
  have h0 : (relativeSingularCohomology.map ℚ (.of ℚ ℚ) c (A := ∅) (A' := ∅)
      (fun _ h => h) 2).hom x = 0 := by
    haveI := subsingleton_H2_punit
    exact Subsingleton.elim _ _
  have e : (relativeSingularCohomology.map ℚ (.of ℚ ℚ) (TopCat.ofHom (ContinuousMap.const A b))
      (A := ∅) (A' := ∅) (fun _ h => h) 2).hom x =
      (relativeSingularCohomology.map ℚ (.of ℚ ℚ) t (A := ∅) (A' := ∅) (fun _ h => h) 2).hom
        ((relativeSingularCohomology.map ℚ (.of ℚ ℚ) c (A := ∅) (A' := ∅)
          (fun _ h => h) 2).hom x) := by
    rw [← ModuleCat.comp_apply, ← hc]
    simp only [hfac]
  rw [e, h0, map_zero]

/-- **Second Betti numbers add over retracts with constant cross terms.** -/
private theorem sum_finrank_le_of_retractions {Z : TopCat.{0}} {ι : Type} [Fintype ι]
    [DecidableEq ι] (Y : ι → TopCat.{0}) (ρ : ∀ i, Y i ⟶ Z) (r : ∀ i, Z ⟶ Y i)
    (hr : ∀ i, ρ i ≫ r i = 𝟙 _)
    (hc : ∀ i i', i ≠ i' → ∃ y, ρ i' ≫ r i = TopCat.ofHom (ContinuousMap.const _ y))
    (hfin : Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) Z ∅ 2)) :
    ∑ i, Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (Y i) ∅ 2) ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) Z ∅ 2) := by
  classical
  let M : ∀ {A B : TopCat.{0}} (g : A ⟶ B), relativeSingularCohomology ℚ (.of ℚ ℚ) B ∅ 2 →ₗ[ℚ]
      relativeSingularCohomology ℚ (.of ℚ ℚ) A ∅ 2 := fun g =>
    (relativeSingularCohomology.map ℚ (.of ℚ ℚ) g (A := ∅) (A' := ∅) (fun _ h => h) 2).hom
  have hcomp : ∀ {A B C : TopCat.{0}} (g : A ⟶ B) (g' : B ⟶ C) x,
      M (g ≫ g') x = M g (M g' x) := by
    intro A B C g g' x
    have := relativeSingularCohomology.map_comp ℚ (.of ℚ ℚ) g g' (A'' := ∅) (A' := ∅) (A := ∅)
      (fun _ h => h) (fun _ h => h) 2
    change (relativeSingularCohomology.map ℚ (.of ℚ ℚ) (g ≫ g') (A := ∅) (A' := ∅)
      (fun _ h => h) 2).hom x = _
    rw [this]
    rfl
  have hid : ∀ {A : TopCat.{0}} x, M (𝟙 A) x = x := by
    intro A x
    have := relativeSingularCohomology.map_id ℚ (.of ℚ ℚ) A ∅ 2
    change (relativeSingularCohomology.map ℚ (.of ℚ ℚ) (𝟙 A) (A := ∅) (A' := ∅)
      (fun _ h => h) 2).hom x = x
    rw [this]
    rfl
  let Φ : relativeSingularCohomology ℚ (.of ℚ ℚ) Z ∅ 2 →ₗ[ℚ]
      ∀ i, relativeSingularCohomology ℚ (.of ℚ ℚ) (Y i) ∅ 2 := LinearMap.pi fun i => M (ρ i)
  have hsurj : Function.Surjective Φ := by
    intro y
    refine ⟨∑ i, M (r i) (y i), funext fun i' => ?_⟩
    change M (ρ i') (∑ i, M (r i) (y i)) = y i'
    rw [map_sum, Finset.sum_eq_single i']
    · rw [← hcomp, hr, hid]
    · intro i _ hi
      obtain ⟨y₀, hy₀⟩ := hc i i' hi
      rw [← hcomp, hy₀]
      exact H2_map_const_eq_zero y₀ _
    · exact fun h => absurd (Finset.mem_univ _) h
  have hfinY : ∀ i, Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (Y i) ∅ 2) := by
    intro i
    refine Module.Finite.of_surjective (M (ρ i)) fun x => ⟨M (r i) x, ?_⟩
    rw [← hcomp, hr, hid]
  have := LinearMap.finrank_le_finrank_of_surjective hsurj
  rwa [Module.finrank_pi_fintype] at this

open MMP.Analytic MMP.Analytic.ComplexPoints in
/-- A clopen piece of the complex points is a retract, collapsing the rest to a point. -/
private theorem exists_retraction {Y' Y : Scheme.{0}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (hcl : IsClosed (Set.range j)) (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType (j ≫ sY)]
    [Nonempty Y'] [CompactSpace Y'] :
    ∃ (r : analyticSpace sY ⟶ analyticSpace (j ≫ sY)) (y₀ : analyticSpace (j ≫ sY)),
      analyticMap j rfl ≫ r = 𝟙 _ ∧
        ∀ y : analyticSpace sY, y ∉ Set.range (analyticMap j rfl) → r y = y₀ := by
  classical
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := Y')).exists_closed_singleton Set.univ_nonempty
  let y₀ : ComplexPoints (j ≫ sY) :=
    ⟨pointOfClosedPoint (j ≫ sY) x₀ hx₀, pointOfClosedPoint_comp _ _ _⟩
  let ρ := realize j (sX := j ≫ sY) rfl
  have hρ : Topology.IsOpenEmbedding ρ := isOpenEmbedding_realize_of_isOpenImmersion j rfl
  have hrange : Set.range ρ = {y : ComplexPoints sY | y.toScheme ∈ j.opensRange} :=
    range_realize_of_isOpenImmersion j rfl
  have hclopen : IsClopen (Set.range ρ) := by
    rw [hrange]
    exact ⟨isClosed_setOf_toScheme_mem hcl, isOpen_setOf_toScheme_mem j.opensRange.isOpen⟩
  let r : ComplexPoints sY → ComplexPoints (j ≫ sY) := fun y =>
    if hy : y ∈ Set.range ρ then hy.choose else y₀
  have hr : ∀ x, r (ρ x) = x := fun x => by
    have hy : ρ x ∈ Set.range ρ := ⟨x, rfl⟩
    simp only [r, hy, dite_true]
    exact hρ.injective hy.choose_spec
  have hrc : Continuous r := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases hy : y ∈ Set.range ρ
    · have hon : ContinuousOn r (Set.range ρ) := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (fun y : Set.range ρ => r y) = hρ.isEmbedding.toHomeomorph.symm := by
          funext ⟨y', x', hx'⟩
          subst hx'
          change r (ρ x') = hρ.isEmbedding.toHomeomorph.symm ⟨ρ x', _⟩
          rw [hr]
          exact (hρ.isEmbedding.toHomeomorph.symm_apply_eq.mpr rfl).symm
        change Continuous (fun y : Set.range ρ => r y)
        rw [this]
        exact hρ.isEmbedding.toHomeomorph.symm.continuous
      exact hon.continuousAt (hclopen.isOpen.mem_nhds hy)
    · have : r =ᶠ[nhds y] fun _ => y₀ := by
        filter_upwards [hclopen.compl.isOpen.mem_nhds hy] with y' hy'
        simp only [r]
        split_ifs with h
        · exact absurd h hy'
        · rfl
      exact (continuousAt_const).congr this.symm
  refine ⟨TopCat.ofHom ⟨r, hrc⟩, y₀, by ext x; exact congrArg (fun z => z.hom) (hr x),
    fun y hy => ?_⟩
  change r y = y₀
  have hy' : y ∉ Set.range ρ := hy
  simp only [r, hy', dite_false]

open MMP.Analytic in
/-- **Second Betti numbers add over disjoint clopen opens.** -/
private theorem sum_finrank_le_of_opens {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sZ] {r k : ℕ} (O : Fin r → Z.Opens)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (O i : Set Z) (O i'))
    (hcl : ∀ i, IsClosed (O i : Set Z)) [∀ i, Nonempty (O i)] [∀ i, CompactSpace (O i)]
    (c : Fin k → Fin r) (hc : Function.Injective c)
    (hfin : Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2)) :
    ∑ j, Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
        (analyticSpace ((O (c j)).ι ≫ sZ)) ∅ 2) ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  classical
  have hret : ∀ j, ∃ (ret : analyticSpace sZ ⟶ analyticSpace ((O (c j)).ι ≫ sZ))
      (y₀ : analyticSpace ((O (c j)).ι ≫ sZ)), analyticMap (O (c j)).ι rfl ≫ ret = 𝟙 _ ∧
        ∀ y, y ∉ Set.range (analyticMap (O (c j)).ι rfl) → ret y = y₀ := fun j =>
    exists_retraction (O (c j)).ι (by rw [Scheme.Opens.range_ι]; exact hcl _) sZ
  choose ret y₀ hret1 hret2 using hret
  refine sum_finrank_le_of_retractions _ (fun j => analyticMap (O (c j)).ι rfl) ret hret1
    (fun j j' hjj' => ⟨y₀ j, ?_⟩) hfin
  ext x
  refine congrArg (fun z => z.hom) (hret2 j _ ?_)
  rintro ⟨x', hx'⟩
  have h1 : (analyticMap (O (c j)).ι rfl x').toScheme ∈ O (c j) := by
    have := MMP.Analytic.ComplexPoints.range_realize_of_isOpenImmersion (O (c j)).ι
      (sU := (O (c j)).ι ≫ sZ) rfl
    have hm : realize (O (c j)).ι (sX := (O (c j)).ι ≫ sZ) rfl x' ∈
        Set.range (realize (O (c j)).ι (sX := (O (c j)).ι ≫ sZ) rfl) := ⟨x', rfl⟩
    rw [this] at hm
    have hm' : (realize (O (c j)).ι (sX := (O (c j)).ι ≫ sZ) rfl x').toScheme ∈
        (O (c j)).ι.opensRange := hm
    rw [Scheme.Opens.opensRange_ι] at hm'
    exact hm'
  have h2 : (analyticMap (O (c j')).ι rfl x).toScheme ∈ O (c j') := by
    have := MMP.Analytic.ComplexPoints.range_realize_of_isOpenImmersion (O (c j')).ι
      (sU := (O (c j')).ι ≫ sZ) rfl
    have hm : realize (O (c j')).ι (sX := (O (c j')).ι ≫ sZ) rfl x ∈
        Set.range (realize (O (c j')).ι (sX := (O (c j')).ι ≫ sZ) rfl) := ⟨x, rfl⟩
    rw [this] at hm
    have hm' : (realize (O (c j')).ι (sX := (O (c j')).ι ≫ sZ) rfl x).toScheme ∈
        (O (c j')).ι.opensRange := hm
    rw [Scheme.Opens.opensRange_ι] at hm'
    exact hm'
  rw [hx'] at h1
  exact Set.disjoint_left.mp (hdisj _ _ (fun h => hjj' (hc h).symm)) h2 h1

end BettiSum

/-! ### Reduction to an integral component -/

section ReductionHelpers

/-- The pieces of a finite disjoint open cover are closed. -/
private theorem isClosed_of_disjoint_cover {Z : Scheme.{0}} {r : ℕ} (O : Fin r → Z.Opens)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (O i : Set Z) (O i')) (hcov : ∀ y : Z, ∃ i, y ∈ O i)
    (i : Fin r) : IsClosed (O i : Set Z) := by
  have : (O i : Set Z)ᶜ = ⋃ i' ∈ {i' | i' ≠ i}, (O i' : Set Z) := by
    ext y
    refine ⟨fun hy => ?_, fun hy hyi => ?_⟩
    · obtain ⟨i', hi'⟩ := hcov y
      exact Set.mem_iUnion₂.2 ⟨i', fun h => hy (h ▸ hi'), hi'⟩
    · obtain ⟨i', hi', hy'⟩ := Set.mem_iUnion₂.1 hy
      exact Set.disjoint_left.mp (hdisj i i' (Ne.symm hi')) hyi hy'
  rw [← isOpen_compl_iff, this]
  exact isOpen_biUnion fun i' _ => (O i').isOpen

/-- A form vanishing on every piece of an open cover vanishes. -/
private theorem eq_zero_of_resForm_eq_zero {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {r : ℕ}
    (O : Fin r → Z.Opens) (hcov : ∀ y : Z, ∃ i, y ∈ O i)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤))
    (h : ∀ i, resForm sZ (O i) ω = 0) : ω = 0 := by
  have h0 : ∀ i, (Scheme.Hom.relativeDifferentialForms sZ 2).presheaf.map
      (homOfLE ((O i).ι.image_preimage_le ⊤)).op ω = 0 := fun i =>
    res_eq_zero_of_formPull_ι_eq_zero sZ (O i) 2 ω (h i)
  have hcover : (⊤ : Z.Opens) ≤ iSup fun i => (O i).ι ''ᵁ ((O i).ι ⁻¹ᵁ ⊤) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨y, hi⟩, trivial, rfl⟩
  have key : ∀ (a b : Γ(Scheme.Hom.relativeDifferentialForms sZ 2, ⊤)),
      (∀ i, (Scheme.Hom.relativeDifferentialForms sZ 2).presheaf.map
        (homOfLE ((O i).ι.image_preimage_le ⊤)).op a =
        (Scheme.Hom.relativeDifferentialForms sZ 2).presheaf.map
          (homOfLE ((O i).ι.image_preimage_le ⊤)).op b) → a = b := fun a b =>
    TopCat.Sheaf.eq_of_locally_eq'
      ⟨_, Scheme.Modules.isSheaf (Scheme.Hom.relativeDifferentialForms sZ 2)⟩
      (fun i => (O i).ι ''ᵁ ((O i).ι ⁻¹ᵁ ⊤)) ⊤ (fun i => homOfLE ((O i).ι.image_preimage_le ⊤))
      hcover a b
  exact key ω 0 fun i => (h0 i).trans (map_zero _).symm

/-- Multiplication by a nonzero constant is injective on forms. -/
private theorem eq_zero_of_const_smul_eq_zero {X : Scheme.{0}} (s : X ⟶ Spec (.of ℂ))
    (sX : X ⟶ Spec (.of ℂ)) {μ : ℂ} (hμ : μ ≠ 0)
    (x : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤))
    (h : (show X.ringCatSheaf.obj.obj (op ⊤) from
      s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) • x = 0) : x = 0 := by
  let M := (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤)
  have hu : (show X.ringCatSheaf.obj.obj (op ⊤) from
      s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ⁻¹)) *
      (show X.ringCatSheaf.obj.obj (op ⊤) from s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) = 1 := by
    change s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ⁻¹) *
      s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ) = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hμ, map_one, map_one]
  calc x = (1 : X.ringCatSheaf.obj.obj (op ⊤)) • x := (M.isModule.one_smul x).symm
    _ = _ := by rw [← hu, M.isModule.mul_smul, h, M.isModule.smul_zero]

end ReductionHelpers

/-! ### Reduction to an integral surface -/

open MMP.Analytic in
/-- The second rational cohomology of a complex projective scheme is finite-dimensional. -/
private theorem finite_relativeSingularCohomology_two {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (hP : IsProjectiveMorphism sZ) :
    Module.Finite ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  obtain ⟨-, hZ, hbc⟩ :=
    MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism _ hP
  have := hZ 2
  have h1 : Module.Finite ℚ (MMP.Analytic.singularCohomology ℚ (analyticSpace sZ) 2) :=
    Module.Finite.equiv (hbc 2).equiv
  rw [← Set.compl_univ]
  exact h1

/-- An eigen-map with eigenvalue zero forces the target form to vanish. -/
private theorem EigenMap.eq_zero_of_eigenvalue_eq_zero {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [Smooth sY]
    {ωX : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤)}
    {ωY : (Scheme.Hom.relativeDifferentialForms sY 2).val.obj (op ⊤)}
    (G : EigenMap sX sY ωX ωY 0) : ωY = 0 := by
  haveI : Nonempty G.U := ⟨⟨_, G.nonempty.some_mem⟩⟩
  haveI := G.isOpenImmersion
  have h := G.eigen
  rw [map_zero, map_zero] at h
  have h' := h.trans (((Scheme.Hom.relativeDifferentialForms (G.U.ι ≫ sX)
    2).val.obj (op ⊤)).isModule.zero_smul _)
  exact eq_zero_of_formPull_eq_zero (sX := sY) _ G.f _ _ h'

/-- For an eigen-map with nonzero eigenvalue, the source form vanishes if the target form does. -/
private theorem EigenMap.eq_zero_of_target_eq_zero {X Y : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} [Smooth sX] {sY : Y ⟶ Spec (.of ℂ)}
    {ωX : (Scheme.Hom.relativeDifferentialForms sX 2).val.obj (op ⊤)}
    {ωY : (Scheme.Hom.relativeDifferentialForms sY 2).val.obj (op ⊤)} {μ : ℂ}
    (G : EigenMap sX sY ωX ωY μ) (hμ : μ ≠ 0) (h0 : ωY = 0) : ωX = 0 := by
  have key : ∀ (hh : G.f ≫ sY = (G.U.ι ≫ sX) ≫ 𝟙 _) x,
      x = 0 → formPull G.f sY _ (𝟙 _) hh 2 x = 0 := by
    rintro hh x rfl
    exact formPull_zero _ _ _ _ _ _
  have h1 := eq_zero_of_const_smul_eq_zero _ _ hμ _ (G.eigen.symm.trans (key _ _ h0))
  exact eq_of_formPull_ι_eq sX G.U G.nonempty _ 0 (h1.trans (formPull_zero _ _ _ _ _ _).symm)

/-- An open of a scheme which is integral as a scheme is preirreducible. -/
private theorem isPreirreducible_of_isIntegral {Z : Scheme.{0}} (O : Z.Opens)
    [IsIntegral O.toScheme] : IsPreirreducible (O : Set Z) := by
  have := (IrreducibleSpace.isIrreducible_univ O.toScheme).image O.ι O.ι.continuous.continuousOn
  rw [Set.image_univ, Scheme.Opens.range_ι] at this
  exact this.isPreirreducible

/-- A dense open `U` meets every open `O` that is integral (hence nonempty) as a scheme. -/
private theorem nonempty_preimage_of_dense {Z : Scheme.{0}} {U : Z.Opens}
    (hU : Dense (U : Set Z)) (O : Z.Opens) [IsIntegral O.toScheme] :
    ((O.ι ⁻¹ᵁ U : O.toScheme.Opens) : Set O.toScheme).Nonempty := by
  obtain ⟨x⟩ : Nonempty O.toScheme := inferInstance
  obtain ⟨z, hzO, hzU⟩ := hU.inter_open_nonempty O O.isOpen ⟨x.1, x.2⟩
  exact ⟨⟨z, hzO⟩, hzU⟩

/-- Composing eigen-maps `O i → O (τ i)` along a cycle `τ^[p] i = i` gives an eigen-map of
`O i` to itself with eigenvalue `μ ^ p`. -/
private theorem nonempty_eigenMap_of_iterate_eq {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    {r : ℕ} (O : Fin r → Z.Opens) (hInt : ∀ i, IsIntegral (O i).toScheme)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) {μ : ℂ} (τ : Fin r → Fin r)
    (G : ∀ i, EigenMap ((O i).ι ≫ sZ) ((O (τ i)).ι ≫ sZ) (resForm sZ (O i) ω)
      (resForm sZ (O (τ i)) ω) μ) {p : ℕ} {i : Fin r} (hp : τ^[p] i = i) :
    Nonempty (EigenMap ((O i).ι ≫ sZ) ((O i).ι ≫ sZ) (resForm sZ (O i) ω)
      (resForm sZ (O i) ω) (μ ^ p)) := by
  have hiter : ∀ m i, Nonempty (EigenMap ((O i).ι ≫ sZ) ((O (τ^[m] i)).ι ≫ sZ)
      (resForm sZ (O i) ω) (resForm sZ (O (τ^[m] i)) ω) (μ ^ m)) := by
    intro m
    induction m with
    | zero =>
      intro i
      haveI := hInt i
      rw [pow_zero]
      exact ⟨EigenMap.id _ _⟩
    | succ m ih =>
      intro i
      obtain ⟨E⟩ := ih (τ i)
      haveI := hInt (τ i)
      rw [pow_succ]
      exact ⟨(G i).comp E⟩
  have : ∀ i', τ^[p] i = i' → Nonempty (EigenMap ((O i).ι ≫ sZ) ((O i').ι ≫ sZ)
      (resForm sZ (O i) ω) (resForm sZ (O i') ω) (μ ^ p)) := by
    rintro i' rfl
    exact hiter p i
  exact this _ hp

/-- Along a `τ`-cycle of length `p` through `i₀` in a disjoint closed cover of a projective
surface, some piece on the cycle has `p · b₂ ≤ b₂(Z)`. -/
private theorem exists_iterate_mul_finrank_le {Z : Scheme.{0}} [CompactSpace Z]
    (sZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sZ] (hP : IsProjectiveMorphism sZ)
    {r : ℕ} (O : Fin r → Z.Opens)
    (hInt : ∀ i, IsIntegral (O i).toScheme)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (O i : Set Z) (O i'))
    (hcl : ∀ i, IsClosed (O i : Set Z)) (τ : Fin r → Fin r) (i₀ : Fin r) {p : ℕ}
    (hp : p = Function.minimalPeriod τ i₀) (hp0 : 0 < p) :
    ∃ j : ℕ, p * Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
        (analyticSpace ((O (τ^[j] i₀)).ι ≫ sZ)) ∅ 2) ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  haveI : ∀ i, Nonempty (O i) := fun i => by
    haveI := hInt i
    obtain ⟨x⟩ : Nonempty (O i).toScheme := inferInstance
    exact ⟨x⟩
  haveI : ∀ i, CompactSpace (O i) := fun i => isCompact_iff_compactSpace.mp (hcl i).isCompact
  let b : Fin p → ℕ := fun j => Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ)
    (analyticSpace ((O (τ^[j] i₀)).ι ≫ sZ)) ∅ 2)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ b ⟨⟨0, hp0⟩, Finset.mem_univ _⟩
  refine ⟨j₀, ?_⟩
  have hinj : Function.Injective fun j : Fin p => τ^[j] i₀ := fun a c h =>
    Fin.ext (Function.iterate_injOn_Iio_minimalPeriod (hp ▸ a.2) (hp ▸ c.2) h)
  calc p * b j₀ = ∑ _j : Fin p, b j₀ := by simp
    _ ≤ ∑ j, b j := Finset.sum_le_sum fun j _ => hj₀ j (Finset.mem_univ _)
    _ ≤ _ := sum_finrank_le_of_opens sZ O hdisj hcl _ hinj
      (finite_relativeSingularCohomology_two sZ hP)

/-- Given a cover of `Z` by disjoint clopen integral opens `O i`, a morphism `f : U ⟶ Z` maps
the part of `U` in a piece `O i` (if nonempty) into a single piece `O i'`. -/
private theorem exists_range_subset_opens {Z : Scheme.{0}} {r : ℕ} (O : Fin r → Z.Opens)
    (hInt : ∀ i, IsIntegral (O i).toScheme) (hclopen : ∀ i, IsClopen (O i : Set Z))
    (hcov : ∀ y : Z, ∃ i, y ∈ O i) {U : Z.Opens} (f : U.toScheme ⟶ Z) (i : Fin r)
    (hUO : (((O i).ι ⁻¹ᵁ U : (O i).toScheme.Opens) : Set (O i).toScheme).Nonempty) :
    ∃ i', Set.range ((O i).ι ∣_ U ≫ f) ⊆ (O i' : Set Z) := by
  haveI := hInt i
  obtain ⟨x₀, hx₀⟩ := hUO
  haveI : Nonempty ((O i).ι ⁻¹ᵁ U) := ⟨⟨x₀, hx₀⟩⟩
  haveI : IsIntegral ((O i).ι ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion ((O i).ι ⁻¹ᵁ U).ι
  obtain ⟨i', hi'⟩ := hcov (((O i).ι ∣_ U ≫ f) ⟨x₀, hx₀⟩)
  refine ⟨i', ?_⟩
  have hpre : _root_.IsPreconnected (Set.range ((O i).ι ∣_ U ≫ f)) := by
    rw [← Set.image_univ]
    exact IsPreirreducible.isPreconnected (IsIrreducible.isPreirreducible
      (IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _
        ((O i).ι ∣_ U ≫ f).continuous.continuousOn))
  exact hpre.subset_isClopen (hclopen i') ⟨_, ⟨⟨x₀, hx₀⟩, rfl⟩, hi'⟩

/-- For disjoint preirreducible opens `O i` and an open immersion `f : U ⟶ Z` meeting every
piece, an assignment `τ` with `f (U ∩ O i) ⊆ O (τ i)` is injective. -/
private theorem injective_of_range_subset_opens {Z : Scheme.{0}} {r : ℕ} (O : Fin r → Z.Opens)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (O i : Set Z) (O i'))
    (hirr : ∀ i, IsPreirreducible (O i : Set Z)) {U : Z.Opens} (f : U.toScheme ⟶ Z)
    [IsOpenImmersion f]
    (hUO : ∀ i, (((O i).ι ⁻¹ᵁ U : (O i).toScheme.Opens) : Set (O i).toScheme).Nonempty)
    (τ : Fin r → Fin r) (hτ : ∀ i, Set.range ((O i).ι ∣_ U ≫ f) ⊆ (O (τ i) : Set Z)) :
    Function.Injective τ := by
  intro i i' hii
  by_contra hne
  obtain ⟨x, hx⟩ := hUO i
  obtain ⟨x', hx'⟩ := hUO i'
  have ho : IsOpen (Set.range ((O i).ι ∣_ U ≫ f)) :=
    ((O i).ι ∣_ U ≫ f).isOpenEmbedding.isOpen_range
  have ho' : IsOpen (Set.range ((O i').ι ∣_ U ≫ f)) :=
    ((O i').ι ∣_ U ≫ f).isOpenEmbedding.isOpen_range
  obtain ⟨z, -, ⟨a, rfl⟩, ⟨b, hb⟩⟩ := hirr (τ i) _ _ ho ho'
    ⟨_, hτ i ⟨⟨x, hx⟩, rfl⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    ⟨_, by rw [hii]; exact hτ i' ⟨⟨x', hx'⟩, rfl⟩, ⟨⟨x', hx'⟩, rfl⟩⟩
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hb
  have h1 := congrArg Subtype.val (f.isOpenEmbedding.injective hb)
  rw [morphismRestrict_base_coe, morphismRestrict_base_coe] at h1
  have ha : (O i).ι a.1 ∈ O i := a.1.2
  have hb' : (O i').ι b.1 ∈ O i' := b.1.2
  rw [h1] at hb'
  exact Set.disjoint_left.mp (hdisj i i' hne) ha hb'

/-- **Reduction to a connected component.** Some iterate `g^k` of the birational self-map maps a
connected component `Z₁` of `Z` on which `ω` does not vanish to itself, with eigenvalue `μ ^ k`
on `ω|_{Z₁}`; the component can be chosen with `k · b₂(Z₁) ≤ b₂(Z)`. -/
private theorem exists_isIntegral_isFormEigen_pow {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ) (U : Z.Opens)
    (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) :
    ∃ (Z₁ : Scheme.{0}) (s₁ : Z₁ ⟶ Spec (.of ℂ)) (_ : IsIntegral Z₁)
      (_ : IsProjectiveMorphism s₁) (_ : SmoothOfRelativeDimension 2 s₁) (k : ℕ) (_ : 0 < k)
      (U₁ : Z₁.Opens) (_ : Dense (U₁ : Set Z₁)) (f₁ : U₁.toScheme ⟶ Z₁)
      (_ : IsOpenImmersion f₁) (_ : Dense (Set.range f₁.base)) (hf₁ : f₁ ≫ s₁ = U₁.ι ≫ s₁)
      (ω₁ : (Scheme.Hom.relativeDifferentialForms s₁ 2).val.obj (op ⊤)),
      ω₁ ≠ 0 ∧ IsFormEigen s₁ U₁ f₁ hf₁ ω₁ (μ ^ k) ∧
      k * Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace s₁) ∅ 2) ≤
        Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  classical
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have hXs : MMP.Mori.IsSmoothScheme sZ := (MMP.Mori.isSmoothScheme_iff sZ).2 inferInstance
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs
  obtain ⟨r, O, hInt, hdisj, hcov⟩ := exists_integral_opens Z
  have hcl := isClosed_of_disjoint_cover O hdisj hcov
  have hclopen : ∀ i, IsClopen (O i : Set Z) := fun i => ⟨hcl i, (O i).isOpen⟩
  have hirr i := @isPreirreducible_of_isIntegral _ (O i) (hInt i)
  have hUO i := @nonempty_preimage_of_dense _ _ hU (O i) (hInt i)
  choose τ hτ using fun i => exists_range_subset_opens O hInt hclopen hcov f i (hUO i)
  let G : ∀ i, EigenMap ((O i).ι ≫ sZ) ((O (τ i)).ι ≫ sZ) (resForm sZ (O i) ω)
      (resForm sZ (O (τ i)) ω) μ := fun i => componentEigenMap he (O i) (O (τ i)) (hUO i) (hτ i)
  have hτinj := injective_of_range_subset_opens O hdisj hirr f hUO τ hτ
  have hμ : μ ≠ 0 := by
    rintro rfl
    exact hω (eq_zero_of_resForm_eq_zero sZ O hcov ω fun j => by
      obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.1 hτinj) j
      haveI := hInt (τ i)
      exact (G i).eq_zero_of_eigenvalue_eq_zero)
  have hprop : ∀ i, resForm sZ (O i) ω ≠ 0 → resForm sZ (O (τ i)) ω ≠ 0 := fun i hi h0 => by
    haveI := hInt i
    exact hi ((G i).eq_zero_of_target_eq_zero hμ h0)
  obtain ⟨i₀, hi₀⟩ := not_forall.mp fun h => hω (eq_zero_of_resForm_eq_zero sZ O hcov ω h)
  obtain ⟨p, hp⟩ : ∃ p, p = Function.minimalPeriod τ i₀ := ⟨_, rfl⟩
  have hp0 : 0 < p := hp ▸ Function.minimalPeriod_pos_of_mem_periodicPts (hτinj.mem_periodicPts i₀)
  have hnz : ∀ m, resForm sZ (O (τ^[m] i₀)) ω ≠ 0 := by
    intro m
    induction m with
    | zero => exact hi₀
    | succ m ih => rw [Function.iterate_succ_apply']; exact hprop _ ih
  obtain ⟨j₀, hj₀⟩ := exists_iterate_mul_finrank_le sZ hP O hInt hdisj hcl τ i₀ hp hp0
  have hper : τ^[p] (τ^[j₀] i₀) = τ^[j₀] i₀ := by
    have : τ^[p] i₀ = i₀ := by rw [hp]; exact Function.iterate_minimalPeriod
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, this]
  obtain ⟨E⟩ := nonempty_eigenMap_of_iterate_eq sZ O hInt ω τ G hper
  haveI := hInt (τ^[j₀] i₀)
  haveI := E.isOpenImmersion
  haveI : Nonempty E.U := ⟨⟨_, E.nonempty.some_mem⟩⟩
  haveI : IsClosedImmersion (O (τ^[j₀] i₀)).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl _)
  haveI hsm : SmoothOfRelativeDimension (0 + 2) ((O (τ^[j₀] i₀)).ι ≫ sZ) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 2) _ _
  refine ⟨(O (τ^[j₀] i₀)).toScheme, (O (τ^[j₀] i₀)).ι ≫ sZ, inferInstance,
    (MMP.isProjectiveMorphism_of_isClosedImmersion _).comp hP, hsm, p, hp0, E.U,
    E.U.isOpen.dense E.nonempty, E.f, inferInstance,
    E.f.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _), E.comm,
    resForm sZ (O (τ^[j₀] i₀)) ω, hnz _, E.eigen, hj₀⟩

/-! ### Towers of point blowups -/

section Tower

/-- Precomposing a variety's structure morphism with an isomorphism gives a variety. -/
private lemma isVariety_iso_comp {k : Type} [Field k] {X Y : Scheme.{0}} (e : X ≅ Y)
    (g : Y ⟶ Spec (.of k)) (h : MMP.Mori.IsVariety k g) : MMP.Mori.IsVariety k (e.hom ≫ g) := by
  rw [MMP.Mori.isVariety_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  haveI := h1
  haveI : Nonempty X := ⟨e.inv (Nonempty.some (inferInstance : Nonempty Y))⟩
  exact ⟨isIntegral_of_isOpenImmersion e.hom, inferInstance, inferInstance, inferInstance⟩

/-- The restriction of a morphism that is an isomorphism over `U` to a smaller open `V ⊆ U` is an
isomorphism. -/
private lemma isIso_restrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have e := morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V)
  have hV : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hVU]
  rw [hV] at e
  exact (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e |>.1 inferInstance

private lemma isIso_restrict_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (U : Y.Opens) :
    IsIso (e.hom ∣_ U) :=
  inferInstance

private lemma ofOpSequence_map_zero_succ {S : ℕ → Scheme.{0}} (σ : ∀ i, S (i + 1) ⟶ S i) (j : ℕ) :
    (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le (j + 1))).op =
      σ j ≫ (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op := by
  have h := (Functor.ofOpSequence σ).map_comp (homOfLE (Nat.le_add_right j 1)).op
    (homOfLE (Nat.zero_le j)).op
  erw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h

/-- One step of the tower of point blowups: blowing up a closed point of a smooth projective
surface over `Z` preserves the properties recorded in `tower_props`. -/
private lemma blowUp_step_props {Z Y Y' : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) [IsProper sZ]
    (π : Y ⟶ Z) (hv : MMP.Mori.IsVariety ℂ (π ≫ sZ)) (hs : Smooth (π ≫ sZ))
    (hdim : topologicalKrullDim Y = 2) (hproj : IsProjective π) (T : Set Z) (hTf : T.Finite)
    (hTc : ∀ t ∈ T, IsClosed ({t} : Set Z)) (hT : IsClosed T)
    (hiso : IsIso (π ∣_ ⟨Tᶜ, hT.isOpen_compl⟩)) (p : Y) (hp : IsClosed ({p} : Set Y))
    (σ : Y' ⟶ Y) (φ : Y' ≅ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hσ : σ = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :
    MMP.Mori.IsVariety ℂ ((σ ≫ π) ≫ sZ) ∧ Smooth ((σ ≫ π) ≫ sZ) ∧
      topologicalKrullDim Y' = 2 ∧ IsProjective (σ ≫ π) ∧
      ∃ T : Set Z, T.Finite ∧ (∀ t ∈ T, IsClosed ({t} : Set Z)) ∧ ∃ hT : IsClosed T,
        IsIso ((σ ≫ π) ∣_ ⟨Tᶜ, hT.isOpen_compl⟩) := by
  haveI := hs
  obtain ⟨hbv, hbs, hbd, hbp, -, hbiso, -⟩ :=
    Threefold.Resolution.isProjective_blowUpToBase_vanishingIdeal_singleton_and_isMinusOneCurve
      (π ≫ sZ) hv hdim hp
  haveI : SmoothOfRelativeDimension 0 φ.hom := inferInstance
  haveI : Smooth φ.hom := SmoothOfRelativeDimension.smooth 0 φ.hom
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated sZ
  have hπp : IsProper π := hproj.isProper
  have hclosed : IsClosed ({π p} : Set Z) := by
    have := π.isClosedMap _ hp
    rwa [Set.image_singleton] at this
  refine ⟨?_, ?_, ?_, ?_, T ∪ {π p}, hTf.union (Set.finite_singleton _),
    fun t ht => ht.elim (hTc t) (fun h => by rw [Set.mem_singleton_iff.1 h]; exact hclosed),
    hT.union hclosed, ?_⟩
  · rw [hσ, Category.assoc, Category.assoc]
    exact isVariety_iso_comp φ _ (by rwa [← Category.assoc] at hbv)
  · rw [hσ, Category.assoc, Category.assoc]
    haveI : Smooth (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫
        π ≫ sZ) := by rwa [← Category.assoc] at hbs
    infer_instance
  · rw [← hbd]
    exact IsHomeomorph.topologicalKrullDim_eq _ (φ.hom.homeomorph).isHomeomorph
  · rw [hσ]
    exact IsProjective.comp (IsProjective.comp_iso φ hbp) hproj
  · rw [morphismRestrict_comp]
    have hA : IsIso (π ∣_ ⟨(T ∪ {π p})ᶜ, (hT.union hclosed).isOpen_compl⟩) :=
      @isIso_restrict_of_le _ _ π ⟨Tᶜ, hT.isOpen_compl⟩ _
        (fun x hx => fun h => hx (Or.inl h)) hiso
    have hle : π ⁻¹ᵁ ⟨(T ∪ {π p})ᶜ, (hT.union hclosed).isOpen_compl⟩ ≤
        ⟨{p}ᶜ, hp.isOpen_compl⟩ := by
      intro x hx hxp
      apply hx
      right
      rw [Set.mem_singleton_iff.1 hxp]
      rfl
    have hB : IsIso (σ ∣_ π ⁻¹ᵁ ⟨(T ∪ {π p})ᶜ, (hT.union hclosed).isOpen_compl⟩) := by
      rw [hσ, morphismRestrict_comp]
      have hb := @isIso_restrict_of_le _ _ (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          ⟨{p}, hp⟩)) _ _ hle hbiso
      exact IsIso.comp_isIso' (isIso_restrict_of_iso φ _) hb
    exact IsIso.comp_isIso' hB hA

/-- **The tower of point blowups.** Every stage of a tower of blowups at closed points of a smooth
projective surface is a smooth projective surface, mapping to the base by a projective morphism
which is an isomorphism off a finite closed set. -/
private lemma tower_props {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (hvar : MMP.Mori.IsVariety ℂ sZ)
    [Smooth sZ] [IsProper sZ] (hd : topologicalKrullDim Z = 2)
    {n : ℕ} (S : ℕ → Scheme.{0}) (σ : ∀ i, S (i + 1) ⟶ S i) (e : S 0 ≅ Z)
    (p : ∀ j : Fin n, S j) (hp : ∀ j : Fin n, IsClosed ({p j} : Set (S j)))
    (hσ : ∀ j : Fin n, ∃ φ : S (j + 1) ≅
        blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩),
      σ j = φ.hom ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p j}, hp j⟩)) :
    ∀ j, j ≤ n →
      MMP.Mori.IsVariety ℂ
          (((Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op ≫ e.hom) ≫ sZ) ∧
      Smooth (((Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op ≫ e.hom) ≫ sZ) ∧
      topologicalKrullDim (S j) = 2 ∧
      IsProjective ((Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op ≫ e.hom) ∧
      ∃ T : Set Z, T.Finite ∧ (∀ t ∈ T, IsClosed ({t} : Set Z)) ∧ ∃ hT : IsClosed T,
        IsIso (((Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op ≫ e.hom) ∣_
          ⟨Tᶜ, hT.isOpen_compl⟩) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le 0)).op ≫ e.hom = e.hom :=
      (congrArg (· ≫ e.hom) ((Functor.ofOpSequence σ).map_id (Opposite.op 0))).trans
        (Category.id_comp _)
    rw [h0]
    show MMP.Mori.IsVariety ℂ (e.hom ≫ sZ) ∧ Smooth (e.hom ≫ sZ) ∧ topologicalKrullDim (S 0) = 2 ∧
      IsProjective e.hom ∧ ∃ T : Set Z, T.Finite ∧ (∀ t ∈ T, IsClosed ({t} : Set Z)) ∧
        ∃ hT : IsClosed T,
        IsIso (e.hom ∣_ ⟨Tᶜ, hT.isOpen_compl⟩)
    haveI : SmoothOfRelativeDimension 0 e.hom := inferInstance
    haveI : Smooth e.hom := SmoothOfRelativeDimension.smooth 0 e.hom
    refine ⟨isVariety_iso_comp e sZ hvar, inferInstance, ?_, ?_, ∅, Set.finite_empty,
      fun t ht => absurd ht (Set.notMem_empty t), isClosed_empty, ?_⟩
    · rw [← hd]
      exact IsHomeomorph.topologicalKrullDim_eq _ (e.hom.homeomorph).isHomeomorph
    · exact (MMP.isProjectiveMorphism_of_isClosedImmersion e.hom).isProjective
    · infer_instance
  | succ j ih =>
    intro hj
    obtain ⟨hv, hs, hdim, hproj, T, hTf, hTc, hT, hiso⟩ := ih (Nat.le_of_succ_le hj)
    let π : S j ⟶ Z := (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le j)).op ≫ e.hom
    have hdec : (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le (j + 1))).op ≫ e.hom =
        σ j ≫ π :=
      (congrArg (· ≫ e.hom) (ofOpSequence_map_zero_succ σ j)).trans (Category.assoc _ _ _)
    rw [hdec]
    obtain ⟨φ, hφ⟩ := hσ ⟨j, hj⟩
    exact blowUp_step_props sZ π hv hs hdim hproj T hTf hTc hT hiso _ (hp ⟨j, hj⟩) (σ j) φ hφ

/-- The point of `X` under a `ℂ`-point is closed. -/
private theorem isClosed_singleton_toScheme {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : MMP.Analytic.ComplexPoints sX) : IsClosed ({x.toScheme} : Set X) := by
  have : IsClosedImmersion x.hom := isClosedImmersion_of_comp_eq_id sX x.hom x.2
  convert x.hom.isClosedEmbedding.isClosed_range using 1
  ext y
  constructor
  · rintro rfl; exact ⟨default, rfl⟩
  · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q default]; rfl

/-- At a closed point of a scheme locally of finite type over `ℂ` the residue field is `ℂ`. -/
private theorem isIso_fromSpecResidueField_comp {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (p : X) (hp : IsClosed ({p} : Set X)) :
    IsIso (X.fromSpecResidueField p ≫ sX) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hp
  have hfin : IsFinite (X.fromSpecResidueField p ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField p ≫ sX)] at hfin ⊢
  rw [IsFinite.SpecMap_iff] at hfin
  have : IsIso (Spec.preimage (X.fromSpecResidueField p ≫ sX)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (IsAlgClosed.ringHom_bijective_of_isIntegral _ hfin.to_isIntegral)
  infer_instance

/-- A `ℂ`-point over `p` is determined by `p`. -/
private theorem hom_eq_inv_comp_fromSpecResidueField {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (x : MMP.Analytic.ComplexPoints sX) (p : X) (hxp : x.toScheme = p)
    [IsIso (X.fromSpecResidueField p ≫ sX)] :
    x.hom = inv (X.fromSpecResidueField p ≫ sX) ≫ X.fromSpecResidueField p := by
  have h := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ X x.hom
  have hc : x.hom (IsLocalRing.closedPoint ℂ) = p := by
    rw [← hxp]; exact congrArg x.hom (Subsingleton.elim _ _)
  revert h
  generalize Scheme.descResidueField (Scheme.stalkClosedPointTo x.hom) = d
  generalize x.hom (IsLocalRing.closedPoint ℂ) = q at hc d ⊢
  subst hc
  intro h
  have h2 := x.hom_comp_structure
  rw [← h, Category.assoc] at h2
  have hd : Spec.map d = inv (X.fromSpecResidueField q ≫ sX) := by
    rw [← Category.comp_id (Spec.map d), ← IsIso.hom_inv_id (X.fromSpecResidueField q ≫ sX),
      ← Category.assoc, h2, Category.id_comp]
  rw [← h, hd]

/-- A `ℂ`-point of a scheme locally of finite type over `ℂ` is determined by its image point. -/
private theorem toScheme_injective {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] :
    Function.Injective (MMP.Analytic.ComplexPoints.toScheme (sX := sX)) := by
  intro x y hxy
  have := isIso_fromSpecResidueField_comp sX _ (isClosed_singleton_toScheme x)
  ext1
  rw [hom_eq_inv_comp_fromSpecResidueField x _ rfl,
    hom_eq_inv_comp_fromSpecResidueField y _ hxy.symm]

end Tower

/-- A form eigen-relation `f^* ω = μ · ω` on `U` lifts to `g^* ω = μ · π^* ω` on `W` along a
resolution `g = f ∘ π` over `U`, when `π⁻¹ U` is nonempty. -/
private theorem formPull_eq_smul_of_resolution {Z W : Scheme.{0}} [IsIntegral W]
    (sZ : Z ⟶ Spec (.of ℂ)) (U : Z.Opens) (f : U.toScheme ⟶ Z) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ)
    (he : IsFormEigen sZ U f hf ω μ) (π g : W ⟶ Z) [Smooth (π ≫ sZ)] (hg1 : g ≫ sZ = π ≫ sZ)
    (hg2 : (π ⁻¹ᵁ U).ι ≫ g = (π ∣_ U) ≫ f) {w : W} (hwU : w ∈ π ⁻¹ᵁ U) :
    formPull g sZ (π ≫ sZ) (𝟙 _) (by simp [hg1]) 2 ω =
      (show W.ringCatSheaf.obj.obj (op ⊤) from
          (π ≫ sZ).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
        formPull π sZ (π ≫ sZ) (𝟙 _) (by simp) 2 ω := by
  have hOne : ((π ⁻¹ᵁ U : W.Opens) : Set W).Nonempty := ⟨w, hwU⟩
  set O := π ⁻¹ᵁ U with hO
  have hsqπ : π ≫ sZ = (π ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
  have hsqg : g ≫ sZ = (π ≫ sZ) ≫ 𝟙 _ := by rw [hg1, Category.comp_id]
  have hsqO : O.ι ≫ (π ≫ sZ) = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
  have hA : (O.ι ≫ g) ≫ sZ = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := by
    rw [Category.assoc, hg1, Category.comp_id]
  have hB : ((π ∣_ U) ≫ f) ≫ sZ = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := by
    rw [← hg2, hA]
  have hC : (π ∣_ U) ≫ (U.ι ≫ sZ) = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.comp_id]
  have hD : ((π ∣_ U) ≫ U.ι) ≫ sZ = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := by
    rw [Category.assoc, hC]
  have hE : (O.ι ≫ π) ≫ sZ = (O.ι ≫ π ≫ sZ) ≫ 𝟙 _ := by
    rw [Category.assoc, Category.comp_id]
  have hfU : f ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _ := by simp [hf]
  have hιU : U.ι ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _ := (Category.comp_id _).symm
  refine eq_of_formPull_ι_eq (π ≫ sZ) O hOne _ _ ?_
  rw [← formPull_comp g O.ι sZ (π ≫ sZ) (O.ι ≫ π ≫ sZ) (𝟙 _) (𝟙 _) (𝟙 _) hsqg hsqO hA 2 ω,
    formPull_congr hg2 sZ (O.ι ≫ π ≫ sZ) rfl hA hB 2 ω,
    formPull_comp f (π ∣_ U) sZ (U.ι ≫ sZ) (O.ι ≫ π ≫ sZ) (𝟙 _) (𝟙 _) (𝟙 _) hfU hC hB 2 ω]
  have he' : formPull f sZ (U.ι ≫ sZ) (𝟙 _) hfU 2 ω =
      (show U.toScheme.ringCatSheaf.obj.obj (op ⊤) from
        (U.ι ≫ sZ).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
      formPull U.ι sZ (U.ι ≫ sZ) (𝟙 _) hιU 2 ω := he
  rw [he', formPull_smul, formPull_smul,
    ← formPull_comp U.ι (π ∣_ U) sZ (U.ι ≫ sZ) (O.ι ≫ π ≫ sZ) (𝟙 _) (𝟙 _) (𝟙 _) hιU hC hD 2 ω,
    formPull_congr (morphismRestrict_ι π U) sZ (O.ι ≫ π ≫ sZ) rfl hD hE 2 ω,
    formPull_comp π O.ι sZ (π ≫ sZ) (O.ι ≫ π ≫ sZ) (𝟙 _) (𝟙 _) (𝟙 _) hsqπ hsqO hE 2 ω]
  congr 1
  change Scheme.Hom.appTop (π ∣_ U) (Scheme.Hom.appTop (U.ι ≫ sZ) _) =
    Scheme.Hom.appTop O.ι (Scheme.Hom.appTop (π ≫ sZ) _)
  have h1 : (π ∣_ U) ≫ U.ι ≫ sZ = O.ι ≫ π ≫ sZ := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have h3 : ∀ {A B : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ Spec (.of ℂ)) (x : Γ(Spec (.of ℂ), ⊤)),
      Scheme.Hom.appTop a (Scheme.Hom.appTop b x) = Scheme.Hom.appTop (a ≫ b) x := by
    intro A B a b x; rw [Scheme.Hom.comp_appTop]; rfl
  rw [h3, h3, h1]

/-- **The point-blowup resolution of a birational self-map.** On an integral smooth projective
surface `Z`, the birational map `f : U ⟶ Z` is resolved by a tower of point blowups `π : W ⟶ Z`
and a morphism `g : W ⟶ Z` with `g = f ∘ π` over `U`. Here `W` is a smooth projective surface, `π`
is an isomorphism off a finite closed set `T`, and some point of `W` maps into `U ∖ T`. -/
private theorem exists_pointBlowup_resolution {Z : Scheme.{0}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hf : f ≫ sZ = U.ι ≫ sZ) :
    ∃ (W : Scheme.{0}) (π g : W ⟶ Z) (T : Set Z) (hT : IsClosed T),
      g ≫ sZ = π ≫ sZ ∧ (π ⁻¹ᵁ U).ι ≫ g = (π ∣_ U) ≫ f ∧
      MMP.Mori.IsVariety ℂ (π ≫ sZ) ∧ Smooth (π ≫ sZ) ∧ topologicalKrullDim W = 2 ∧
      IsProjectiveMorphism (π ≫ sZ) ∧ T.Finite ∧ IsIso (π ∣_ ⟨Tᶜ, hT.isOpen_compl⟩) ∧
      ∃ w : W, π w ∈ U ∧ π w ∉ T := by
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  have hvar : MMP.Mori.IsVariety ℂ sZ := (MMP.Mori.isVariety_iff ℂ sZ).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hd : topologicalKrullDim Z = 2 := by
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible ℂ Z sZ x,
      topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 sZ x]
    rfl
  have hPV : MMP.Mori.IsProjectiveVariety ℂ sZ :=
    (MMP.Mori.isProjectiveVariety_iff ℂ sZ).2 ⟨hvar, hP⟩
  have hXs : MMP.Mori.IsSmoothScheme sZ := (MMP.Mori.isSmoothScheme_iff sZ).2 inferInstance
  obtain ⟨n, S, σ, e, pt, hpt, hσ, ⟨g, hg1, hg2⟩, -⟩ :=
    MMP.Fourfold.exists_pointBlowups_comp_eq_of_partialMap ℂ sZ sZ hPV hXs hd hP ⟨U, hU, f⟩ hf
  obtain ⟨hv, hs, hdW, hprojπ, T, hTf, hTc, hT, hiso⟩ :=
    tower_props sZ hvar hd S σ e pt hpt hσ n le_rfl
  let π : S n ⟶ Z := (Functor.ofOpSequence σ).map (homOfLE (Nat.zero_le n)).op ≫ e.hom
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated sZ
  -- the generic point is not one of the finitely many closed points of `T`
  have hη : genericPoint Z ∉ T := fun hη => by
    have huniv : ({genericPoint Z} : Set Z) = Set.univ := by
      rw [← (hTc _ hη).closure_eq]; exact genericPoint_spec Z
    haveI : Subsingleton Z := ⟨fun a b => by
      have ha : a ∈ ({genericPoint Z} : Set Z) := huniv ▸ Set.mem_univ a
      have hb : b ∈ ({genericPoint Z} : Set Z) := huniv ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have := topologicalKrullDim_zero_of_discreteTopology Z
    rw [hd] at this
    exact absurd this (by decide)
  have hηU : genericPoint Z ∈ U := by
    obtain ⟨u, hu⟩ := hU.nonempty
    exact ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 ⟨u, trivial, hu⟩
  change IsIso (π ∣_ ⟨Tᶜ, hT.isOpen_compl⟩) at hiso
  let V : Z.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let w := (inv (π ∣_ V)) ⟨genericPoint Z, hη⟩
  have hw : π w.1 = genericPoint Z := by
    have h2 : (π ∣_ V) w = ⟨genericPoint Z, hη⟩ := by
      change ((inv (π ∣_ V)) ≫ (π ∣_ V)) _ = _
      rw [IsIso.inv_hom_id]
      rfl
    rw [← morphismRestrict_base_coe π V w, h2]
  refine ⟨S n, π, g, T, hT, hg1, hg2, hv, hs, hdW,
    isProjectiveMorphism_of_isProjective_of_isAffine _ (IsProjective.comp hprojπ hP.isProjective),
    hTf, hiso, w.1, hw ▸ hηU, hw ▸ hη⟩

/-! ### Integrality on an integral surface -/

/-- **Resolution of the graph.** On an integral surface, the birational self-map is resolved by a
smooth projective surface `W` with two morphisms `p, q : W ⟶ Z`, `q^* ω = μ p^* ω`, such that the
complex realization of `p` has a continuous section over the complement of a finite set. -/
private theorem exists_resolution_of_isFormEigen {Z : Scheme.{0}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ)
    (he : IsFormEigen sZ U f hf ω μ) :
    ∃ (W : Scheme.{0}) (sW : W ⟶ Spec (.of ℂ)) (_ : IsProjectiveMorphism sW)
      (_ : SmoothOfRelativeDimension 2 sW) (p q : W ⟶ Z) (hp : p ≫ sZ = sW) (hq : q ≫ sZ = sW)
      (F : Set (MMP.Analytic.ComplexPoints sZ)),
      F.Finite ∧
      formPull q sZ sW (𝟙 _) (by simp [hq]) 2 ω =
        (show W.ringCatSheaf.obj.obj (op ⊤) from sW.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
          formPull p sZ sW (𝟙 _) (by simp [hp]) 2 ω ∧
      ∃ s : TopCat.of ↥Fᶜ ⟶ analyticSpace sW, ∀ y, analyticMap p hp (s y) = y.1 := by
  obtain ⟨W, π, g, T, hT, hg1, hg2, hv, hs, hdW, hPW, hTf, hiso, w, hwU, -⟩ :=
    exists_pointBlowup_resolution sZ hP hS U hU f hf
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  haveI := hv
  haveI := hs
  refine ⟨W, π ≫ sZ, hPW, MMP.Intersection.smoothOfRelativeDimension_of_isVariety (π ≫ sZ) 2 hdW,
    π, g, rfl, hg1, {y : MMP.Analytic.ComplexPoints sZ | y.toScheme ∈ T},
    hTf.preimage toScheme_injective.injOn, ?_, ?_⟩
  · haveI : IsIntegral W := hv.toIsIntegral
    exact formPull_eq_smul_of_resolution sZ U f hf ω μ he π g hg1 hg2 hwU
  · haveI := hiso
    have hH := MMP.Analytic.ComplexPoints.isHomeomorph_restrictPreimage_realize
      (sX := π ≫ sZ) (sY := sZ) π rfl ⟨Tᶜ, hT.isOpen_compl⟩
    let h := hH.homeomorph
    have hmem : ∀ y : ↥({y : MMP.Analytic.ComplexPoints sZ | y.toScheme ∈ T}ᶜ),
        y.1 ∈ {y : MMP.Analytic.ComplexPoints sZ |
          y.toScheme ∈ (⟨Tᶜ, hT.isOpen_compl⟩ : Z.Opens)} := fun y => y.2
    refine ⟨TopCat.ofHom ⟨fun y => (h.symm ⟨y.1, hmem y⟩).1, ?_⟩, fun y => ?_⟩
    · exact continuous_subtype_val.comp (h.symm.continuous.comp
        (continuous_subtype_val.subtype_mk _))
    · exact congrArg Subtype.val (h.apply_symm_apply ⟨y.1, hmem y⟩)

universe u

/-! ### Rational forms of global forms -/

/-- Every nonempty open of a scheme contains a nonempty affine open. -/
private theorem exists_affineOpens_le {Y : Scheme.{u}} (V : Y.Opens) {y : Y} (hy : y ∈ V) :
    ∃ W : Y.affineOpens, (W : Y.Opens) ≤ V ∧ y ∈ (W : Y.Opens) := by
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy
  exact ⟨⟨W, hW⟩, hWV, hyW⟩

/-- A chosen nonempty affine open of a nonempty scheme. -/
private noncomputable def someAffine (X : Scheme.{u}) [Nonempty X] : X.affineOpens :=
  (exists_affineOpens_le (⊤ : X.Opens) (Set.mem_univ (Classical.arbitrary X))).choose

private theorem nonempty_someAffine (X : Scheme.{u}) [Nonempty X] :
    Nonempty (someAffine X : X.Opens) :=
  ⟨⟨_, (exists_affineOpens_le (⊤ : X.Opens) (Set.mem_univ (Classical.arbitrary X))).choose_spec.2⟩⟩

attribute [local instance] nonempty_someAffine

/-! ### Pulling back algebraic forms, on affine opens -/

section AlgebraicPullback

open KaehlerDifferential Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {k : Type u} [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sX' : X' ⟶ Spec (.of k)) (g : X' ⟶ X) (hg : g ≫ sX = sX')

/-- Every open lies over the top open. -/
private theorem le_preimage_top {Y Y' : Scheme.{u}} (f : Y ⟶ Y') (U : Y.Opens) : U ≤ f ⁻¹ᵁ ⊤ := by
  simp

include hg in
/-- `k → Γ(X, W) → Γ(X', W')` is a scalar tower along `g^♯`. -/
private theorem isScalarTower_appLE {W : X.Opens} {W' : X'.Opens} (h : W' ≤ g ⁻¹ᵁ W) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    IsScalarTower k Γ(X, W) Γ(X', W') := by
  subst hg
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra (g ≫ sX) W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  exact (congrArg (fun t ↦ ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom)
    (Scheme.Hom.appLE_comp_appLE g sX ⊤ W W' (by simp) h)).symm

set_option maxRecDepth 20000 in
include hg in
/-- The pull-back of `d c₁ ∧ ⋯ ∧ d c_q`, restricted to `W'`, is `d (g^♯ c₁) ∧ ⋯ ∧ d (g^♯ c_q)`. -/
private theorem formsSectionsIso_hom_map_deRhamFormsPushforwardSections_ιMulti_d (q : ℕ)
    (W : X.affineOpens) (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (c : Fin q → Γ(X, W)) :
    (formsSectionsIso sX' W'.2 (isAffineOpen_top _) (le_preimage_top sX' _) q).hom
        ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op
          (deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q
            ((formsSectionsIso sX W.2 (isAffineOpen_top _)
                (le_preimage_top sX _) q).inv
              (exteriorPower.ιMulti Γ(X, W) q fun i ↦
                CommRingCat.KaehlerDifferential.d (c i))))) =
      exteriorPower.ιMulti Γ(X', W') q fun i ↦
        CommRingCat.KaehlerDifferential.d ((g.appLE W W' h).hom (c i)) := by
  have e1 := formsSectionsIso_inv_ιMulti_d sX W.2 (isAffineOpen_top _)
    (le_preimage_top sX _) q c
  have e2 := Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft g sX sX' (𝟙 _)
    (by rw [hg, Category.comp_id]) (op (W : X.Opens)) q c
  have e3 := Stacks.GradedAlgebra.homogeneousProdLeft_naturality
    (Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra (homOfLE h).op q
    (fun i ↦ SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
      ((g.app W).hom (c i)))
  have e4 := formsSectionsIso_inv_ιMulti_d sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q fun i ↦ (g.appLE W W' h).hom (c i)
  have e5 : ∀ i, ((Scheme.Hom.deRhamAlgebras sX').exteriorPower 1).val.map (homOfLE h).op
      (SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (g ⁻¹ᵁ (W : X.Opens)))
        ((g.app W).hom (c i))) =
      SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras sX') (op (W' : X'.Opens))
        ((g.appLE W W' h).hom (c i)) := fun i ↦
    SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras sX') (homOfLE h).op _
  refine (congrArg (fun t ↦ (formsSectionsIso sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op (deRhamFormsPushforwardSections g sX sX' (𝟙 _)
        (by rw [hg, Category.comp_id]) q t))) e1).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
      (homOfLE h).op t)) e2).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom t) e3).trans ?_
  refine (congrArg (fun t ↦ (formsSectionsIso sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom
      ((Scheme.Hom.deRhamAlgebras sX').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op (W' : X'.Opens)) q t)) (funext e5)).trans ?_
  refine (congrArg (formsSectionsIso sX' W'.2 (isAffineOpen_top _)
    (le_preimage_top sX' _) q).hom e4.symm).trans ?_
  exact Iso.inv_hom_id_apply _ _

include hg in
/-- The pull-back of forms over `W`, restricted to `W'`, read through the affine comparisons and
the change of base `kaehlerSpecEquiv`. -/
private noncomputable def pullAffine (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))) :
    letI := MMP.Mori.sectionAlgebra sX' W'
    ⋀[Γ(X', W')]^q (Ω[Γ(X', W')⁄k]) :=
  letI := MMP.Mori.sectionAlgebra sX' W'
  exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX' W').toLinearMap
    ((formsSectionsIso sX' W'.2 (isAffineOpen_top _)
        (le_preimage_top sX' _) q).hom
      ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map (homOfLE h).op
        (deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q
          ((formsSectionsIso sX W.2 (isAffineOpen_top _)
              (le_preimage_top sX _) q).inv y))))

/-- `pullAffine` agrees with the map of Kähler forms at `0`. -/
private theorem pullAffine_zero (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
      pullAffine sX sX' g hg q W W' h 0 =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap 0) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  unfold pullAffine
  rw [map_zero, show deRhamFormsPushforwardSections g sX sX' (𝟙 _)
      (by rw [hg, Category.comp_id]) q 0 = 0 from
    map_zero (((Scheme.Hom.deRhamFormsPushforwardHom g sX sX' (𝟙 _)
      (by rw [hg, Category.comp_id])).app (q : ℤ)).val.app (op (W : X.Opens))).hom]
  simp only [map_zero]

/-- `pullAffine` is additive. -/
private theorem pullAffine_add (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (y z : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))) :
    pullAffine sX sX' g hg q W W' h (y + z) =
      pullAffine sX sX' g hg q W W' h y + pullAffine sX sX' g hg q W W' h z := by
  unfold pullAffine
  simp only [map_add, deRhamFormsPushforwardSections_add]

/-- `pullAffine` agrees with the map of Kähler forms on sums of elements where it agrees. -/
private theorem pullAffine_add_eq (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ y z : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) →
      pullAffine sX sX' g hg q W W' h z = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap z) →
      pullAffine sX sX' g hg q W W' h (y + z) = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (y + z)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ y z hy hz
  have hG : mapExteriorPower k Γ(X, W) Γ(X', W') q
      (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (y + z)) =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) +
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap z) := by
    rw [map_add (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap) y z,
      map_add (mapExteriorPower k Γ(X, W) Γ(X', W') q)]
  rw [pullAffine_add, hG]
  exact congrArg₂ _ hy hz

/-- `pullAffine` agrees with the map of Kähler forms on multiples of elements where it agrees. -/
private theorem pullAffine_smul_eq (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ (b : Γ(X, W))
      (y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _)))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) →
      pullAffine sX sX' g hg q W W' h (b • y) = mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap (b • y)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ b y hy
  unfold pullAffine at hy ⊢
  simp only [map_smul, deRhamFormsPushforwardSections_smul, Scheme.Modules.map_smul]
  rw [hy]
  exact (algebraMap_smul Γ(X', W') b _).symm

/-- `pullAffine` agrees with the map of Kähler forms on wedges of differentials. -/
private theorem pullAffine_ιMulti_d (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
    (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')], ∀ c : Fin q → Γ(X, W),
      pullAffine sX sX' g hg q W W' h (exteriorPower.ιMulti Γ(X, W) q fun i ↦
          CommRingCat.KaehlerDifferential.d (c i)) =
        mapExteriorPower k Γ(X, W) Γ(X', W') q
          (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap
            (exteriorPower.ιMulti Γ(X, W) q fun i ↦ CommRingCat.KaehlerDifferential.d (c i))) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _ c
  unfold pullAffine
  rw [formsSectionsIso_hom_map_deRhamFormsPushforwardSections_ιMulti_d sX sX' g hg q W W' h c]
  simp only [exteriorPower.map_apply_ιMulti, Function.comp_def, LinearEquiv.coe_coe,
    MMP.DeRham.kaehlerBaseEquiv_d, mapExteriorPower_ιMulti, map_D]
  rfl

/-- The pull-back of forms, restricted to `W'`, read through the affine comparisons. -/
private theorem pullAffine_eq (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    ∀ y : ⋀[Γ(X, W)]^q ↑(CommRingCat.KaehlerDifferential (sX.appLE ⊤ W (le_preimage_top sX _))),
      pullAffine sX sX' g hg q W W' h y = mapExteriorPower k Γ(X, W) Γ(X', W') q
        (exteriorPower.map q (MMP.DeRham.kaehlerSpecEquiv sX W).toLinearMap y) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  exact eq_of_smul_ιMulti_d (sX.appLE ⊤ W (le_preimage_top sX _)) q _ _
    (pullAffine_zero sX sX' g hg q W W' h) (pullAffine_add_eq sX sX' g hg q W W' h)
    (pullAffine_smul_eq sX sX' g hg q W W' h) (pullAffine_ιMulti_d sX sX' g hg q W W' h)

include hg in
/-- **The pull-back of a form on an affine open, restricted to an affine open, is the map of
Kähler forms along `g^♯`.** -/
private theorem formsAlgEquiv_map_deRhamFormsPushforwardSections (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (η : Γ(sX.relativeDifferentialForms (q : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    MMP.DeRham.formsAlgEquiv sX' q W' ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE h).op (deRhamFormsPushforwardSections g sX sX' (𝟙 _)
          (by rw [hg, Category.comp_id]) q η)) =
      mapExteriorPower k Γ(X, W) Γ(X', W') q (MMP.DeRham.formsAlgEquiv sX q W η) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  obtain ⟨y, rfl⟩ : ∃ y, (formsSectionsIso sX W.2 (isAffineOpen_top _)
      (le_preimage_top sX _) q).inv y = η :=
    ⟨(formsSectionsIso sX W.2 (isAffineOpen_top _)
      (le_preimage_top sX _) q).hom η, by simp⟩
  rw [MMP.DeRham.formsAlgEquiv_apply, MMP.DeRham.formsAlgEquiv_apply, Iso.inv_hom_id_apply]
  have e := pullAffine_eq sX sX' g hg q W W' h y
  unfold pullAffine at e
  refine Eq.trans ?_ e
  congr!

include hg in
/-- **The pull-back of a global form, on affine opens, is the map of Kähler forms along `g^♯`.** -/
private theorem formsAlgEquiv_res_pullback (q : ℕ) (W : X.affineOpens)
    (W' : X'.affineOpens) (h : (W' : X'.Opens) ≤ g ⁻¹ᵁ (W : X.Opens))
    (ω : Γ(sX.relativeDifferentialForms (q : ℤ), ⊤)) :
    letI := MMP.Mori.sectionAlgebra sX W
    letI := MMP.Mori.sectionAlgebra sX' W'
    letI : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
    ∀ [IsScalarTower k Γ(X, W) Γ(X', W')],
    MMP.DeRham.formsAlgEquiv sX' q W' ((sX'.relativeDifferentialForms (q : ℤ)).presheaf.map
        (homOfLE (le_top : (W' : X'.Opens) ≤ ⊤)).op
        ((Scheme.Hom.relativeDifferentialFormsMap g sX sX' (𝟙 _) (by rw [hg, Category.comp_id])
          (q : ℤ)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app _).app ⊤ ω))) =
      mapExteriorPower k Γ(X, W) Γ(X', W') q (MMP.DeRham.formsAlgEquiv sX q W
        ((sX.relativeDifferentialForms (q : ℤ)).presheaf.map
          (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω)) := by
  let := MMP.Mori.sectionAlgebra sX W
  let := MMP.Mori.sectionAlgebra sX' W'
  let : Algebra Γ(X, W) Γ(X', W') := (g.appLE W W' h).hom.toAlgebra
  intro _
  rw [← formsAlgEquiv_map_deRhamFormsPushforwardSections sX sX' g hg q W W' h]
  congr 1
  have hΦ : ∀ η : Γ(sX.relativeDifferentialForms (q : ℤ), W),
      deRhamFormsPushforwardSections g sX sX' (𝟙 _) (by rw [hg, Category.comp_id]) q η =
        Scheme.Hom.relativeDifferentialFormsPullback g sX sX' (𝟙 _)
          (by rw [hg, Category.comp_id]) (q : ℤ) W η := by
    intro η
    rw [deRhamFormsPushforwardSections_apply, ← Scheme.Hom.homEquiv_relativeDifferentialFormsMap]
    rfl
  have e := Scheme.Hom.relativeDifferentialFormsPullback_map g sX sX' (𝟙 _)
    (by rw [hg, Category.comp_id]) (q : ℤ) (le_top : (W : X.Opens) ≤ ⊤) ω
  rw [hΦ, e, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end AlgebraicPullback

section RatForm

open KaehlerDifferential MMP.Mori

/-- `topFormsMap` after a map of Kähler forms along a tower is `topFormsMap`. -/
private theorem topFormsMap_mapExteriorPower {k A B : Type u} {K : Type*} [CommRing k]
    [CommRing A] [CommRing B]
    [CommRing K] [Algebra k A] [Algebra k B] [Algebra k K] [Algebra A B] [Algebra A K]
    [Algebra B K] [IsScalarTower k A B] [IsScalarTower k A K] [IsScalarTower k B K]
    [IsScalarTower A B K] (d : ℕ) (x : ⋀[A]^d Ω[A⁄k]) :
    topFormsMap k B K d (mapExteriorPower k A B d x) = topFormsMap k A K d x := by
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A d (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    rw [mapExteriorPower_ιMulti, topFormsMap_ιMulti, topFormsMap_ιMulti]
    simp only [MMP.Threefold.Mori.Helpers.kaehler_map_comp']
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul B a, LinearMap.map_smul, algebraMap_smul, hx, map_smul]

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- The image in `Ω^n_{k(X)/k}` of a global form, read on a nonempty affine open. -/
private noncomputable def chartForm (n : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    letI := functionFieldAlgebra sX
    ⋀[X.functionField]^n Ω[X.functionField⁄k] :=
  letI := sectionAlgebra sX W
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_section_functionField sX (W : X.Opens)
  topFormsMap k Γ(X, W) X.functionField n
    (MMP.DeRham.formsAlgEquiv sX n W ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map
      (homOfLE le_top).op ω))

set_option maxRecDepth 20000 in
private theorem chartForm_of_le (n : ℕ) {W W' : X.affineOpens} [Nonempty (W : X.Opens)]
    [Nonempty (W' : X.Opens)] (h : (W' : X.Opens) ≤ W)
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    chartForm sX n W' ω = chartForm sX n W ω := by
  let := sectionAlgebra sX W
  let := sectionAlgebra sX W'
  let := functionFieldAlgebra sX
  let : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  have := MMP.Flips.ResolutionInputs.isScalarTower_section_res sX h
  have := isScalarTower_section_functionField sX (W : X.Opens)
  have := isScalarTower_section_functionField sX (W' : X.Opens)
  have : IsScalarTower Γ(X, W) Γ(X, W') X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change X.germToFunctionField W a = X.germToFunctionField W' (X.presheaf.map (homOfLE h).op a)
    simp only [Scheme.germToFunctionField]
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]
  have e := MMP.DeRham.formsAlgEquiv_restrict sX n h
    ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map
      (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω)
  have hres : (sX.relativeDifferentialForms (n : ℤ)).presheaf.map (homOfLE h).op
      ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map
        (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω) =
      (sX.relativeDifferentialForms (n : ℤ)).presheaf.map
        (homOfLE (le_top : (W' : X.Opens) ≤ ⊤)).op ω := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hres] at e
  exact (congrArg (topFormsMap k Γ(X, W') X.functionField n) e).trans
    (topFormsMap_mapExteriorPower n _)

/-- `f^♯` on sections followed by the germ at the generic point is the germ followed by the map of
function fields. -/
private theorem functionFieldMap_germToFunctionField {T : Scheme.{u}} [IsIntegral T] (h : T ⟶ X)
    [IsDominant h] {W : X.Opens} {W' : T.Opens} [Nonempty W] [Nonempty W'] (hle : W' ≤ h ⁻¹ᵁ W)
    (a : Γ(X, W)) :
    functionFieldMap h (X.germToFunctionField W a) =
      T.germToFunctionField W' (h.appLE W W' hle a) := by
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty W')
  have hfy : h y ∈ W := hle hy
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hfy,
    MMP.Mori.functionFieldMap_algebraMap_stalk,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := T) hy]
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.germ_stalkMap, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

set_option maxRecDepth 20000 in
/-- **Naturality of chart forms**: for a dominant morphism `h : T ⟶ X` of integral schemes over
`k`, the chart form of `h^* ω` is the image of the chart form of `ω` under `k(X) → k(T)`. -/
private theorem chartForm_formPull {T : Scheme.{u}} [IsIntegral T] (h : T ⟶ X) [IsDominant h]
    (n : ℕ)
    (W : X.affineOpens) (W' : T.affineOpens) [Nonempty (W : X.Opens)] [Nonempty (W' : T.Opens)]
    (hle : (W' : T.Opens) ≤ h ⁻¹ᵁ (W : X.Opens))
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (h ≫ sX)
    letI := functionFieldMapAlgebra h
    haveI := isScalarTower_functionFieldMap sX h
    chartForm (h ≫ sX) n W' ((Scheme.Hom.relativeDifferentialFormsMap h sX (h ≫ sX) (𝟙 _)
          (by rw [Category.comp_id]) (n : ℤ)).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _).app ⊤ ω)) =
      topFormsMap k X.functionField T.functionField n (chartForm sX n W ω) := by
  let := sectionAlgebra sX W
  let := sectionAlgebra (h ≫ sX) W'
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  let : Algebra Γ(X, W) Γ(T, W') := (h.appLE W W' hle).hom.toAlgebra
  have hST : IsScalarTower k Γ(X, W) Γ(T, W') := isScalarTower_appLE sX (h ≫ sX) h rfl hle
  have := isScalarTower_section_functionField sX (W : X.Opens)
  have := isScalarTower_section_functionField (h ≫ sX) (W' : T.Opens)
  let : Algebra Γ(X, W) T.functionField := ((algebraMap X.functionField T.functionField).comp
    (algebraMap Γ(X, W) X.functionField)).toAlgebra
  have h2 : IsScalarTower Γ(X, W) X.functionField T.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h3 : IsScalarTower k Γ(X, W) T.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k X.functionField T.functionField,
      IsScalarTower.algebraMap_apply k Γ(X, W) X.functionField]
    rfl
  have h1 : IsScalarTower Γ(X, W) Γ(T, W') T.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    exact functionFieldMap_germToFunctionField h hle a
  have e := formsAlgEquiv_res_pullback sX (h ≫ sX) h rfl n W W' hle ω
  change topFormsMap k Γ(T, W') T.functionField n (MMP.DeRham.formsAlgEquiv (h ≫ sX) n W' _) = _
  rw [e, topFormsMap_mapExteriorPower]
  exact (MMP.Threefold.Mori.Helpers.topFormsMap_comp _).symm

/-- Chart forms do not depend on the chart. -/
private theorem chartForm_eq (n : ℕ) (W W' : X.affineOpens) [Nonempty (W : X.Opens)]
    [Nonempty (W' : X.Opens)] (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    chartForm sX n W' ω = chartForm sX n W ω := by
  obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty (W : X.Opens))
  obtain ⟨⟨x', hx'⟩⟩ := (inferInstance : Nonempty (W' : X.Opens))
  obtain ⟨y, hyW, hyW'⟩ := nonempty_preirreducible_inter (W : X.Opens).isOpen
    (W' : X.Opens).isOpen ⟨x, hx⟩ ⟨x', hx'⟩
  obtain ⟨W₀, hW₀, hyW₀⟩ := exists_affineOpens_le ((W : X.Opens) ⊓ W') ⟨hyW, hyW'⟩
  haveI : Nonempty (W₀ : X.Opens) := ⟨⟨y, hyW₀⟩⟩
  rw [← chartForm_of_le sX n (hW₀.trans inf_le_right) ω,
    chartForm_of_le sX n (hW₀.trans inf_le_left) ω]

/-- **The rational form of a global form**: its image in `Ω^n_{k(X)/k}`, as a rational
`1`-canonical form. -/
private noncomputable def ratForm (n : ℕ) (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    RationalPluriForms sX n (1 : ℕ) :=
  letI := functionFieldAlgebra sX
  MMP.Fourfold.formPow (chartForm sX n (someAffine X) ω) 1

private theorem ratForm_eq (n : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    ratForm sX n ω =
      (letI := functionFieldAlgebra sX; MMP.Fourfold.formPow (chartForm sX n W ω) 1) := by
  unfold ratForm
  rw [chartForm_eq sX n W (someAffine X) ω]

end RatForm

section Regular

open MMP.Mori MMP.Fourfold

/-- The order of the image of an integral top form is nonnegative. -/
private theorem ordAt_formPow_topFormsMap_nonneg {k A K : Type*} [CommRing k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {v : K → ℤ} (hv : ∀ a : A, 0 ≤ v (algebraMap A K a)) (x : ⋀[A]^d Ω[A⁄k]) :
    0 ≤ ordAt (m := ((1 : ℕ) : ℤ)) A v (formPow (topFormsMap k A K d x) 1) := by
  classical
  unfold ordAt
  split_ifs with h
  · obtain ⟨hσ, h0⟩ := h.choose_spec
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := x))
    rw [← ha, map_smul, ← algebraMap_smul K a, formPow_smul, pow_one, formCoeff,
      ← topFormsBasis_apply hσ h0 (), repr_smul_formPow]
    exact hv a
  · exact le_rfl

/-- Elements of a local ring have nonnegative order. -/
private theorem ord_algebraMap_stalk_nonneg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (a : X.presheaf.stalk x) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.germ_exist (x := x) a
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxV]
  by_cases hs : s = 0
  · subst hs; simp
  have h1 := Scheme.ord_le_smul hxV hs (1 : X.functionField)
  have h2 : X.ord (1 : X.functionField) x = 0 := by
    have := Scheme.ord_of_isUnit (U := V) (f := 1) isUnit_one hxV
    rwa [map_one] at this
  rw [h2] at h1
  convert h1 using 2
  rw [Algebra.smul_def, mul_one]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

set_option maxRecDepth 20000 in
open KaehlerDifferential Stacks.AlgebraicGeometry.AffineOpenDeRham in
/-- **Global forms are regular**: the rational form of a global `n`-form has nonnegative order
along every prime divisor. -/
private theorem ordForm_ratForm_nonneg [IsLocallyNoetherian X] (n : ℕ)
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) (Γ' : MMP.Mori.PrimeDivisor X) :
    0 ≤ Γ'.ordForm (ratForm sX n ω) := by
  obtain ⟨W, -, hW⟩ := exists_affineOpens_le (⊤ : X.Opens) (Set.mem_univ Γ'.genericPoint)
  haveI : Nonempty (W : X.Opens) := ⟨⟨_, hW⟩⟩
  rw [ratForm_eq sX n W ω]
  let := stalkAlgebra sX Γ'.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ'.genericPoint
  let := sectionAlgebra sX W
  have := isScalarTower_section_functionField sX (W : X.Opens)
  let : Algebra Γ(X, W) Γ'.localRing :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨_, hW⟩ : (W : X.Opens))
  have := isScalarTower_section_stalk sX W ⟨_, hW⟩
  have : IsScalarTower Γ(X, W) Γ'.localRing X.functionField :=
    functionField_isScalarTower X W ⟨_, hW⟩
  have e : chartForm sX n W ω = topFormsMap k Γ'.localRing X.functionField n
      (mapExteriorPower k Γ(X, W) Γ'.localRing n
        (MMP.DeRham.formsAlgEquiv sX n W ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map
          (homOfLE le_top).op ω))) := (topFormsMap_mapExteriorPower n _).symm
  rw [e]
  exact ordAt_formPow_topFormsMap_nonneg (fun a => ord_algebraMap_stalk_nonneg _ a) _

open KaehlerDifferential Stacks.AlgebraicGeometry.AffineOpenDeRham in
/-- Over a domain with flat top forms, `Ω^d_{A/k} → Ω^d_{K/k}` is injective. -/
private theorem topFormsMap_injective {k A K : Type u} [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] (d : ℕ)
    [Module.Flat A (⋀[A]^d Ω[A⁄k])] : Function.Injective (topFormsMap k A K d) := by
  have hloc := MMP.DeRham.isLocalizedModule_mapExteriorPower_of_isLocalization (A := k) (L := A)
    (L' := K) (nonZeroDivisors A) d
  have heq : ∀ x, mapExteriorPower k A K d x = topFormsMap k A K d x := fun x =>
    (MMP.Fourfold.topFormsMap_self (k := k) _).symm.trans (topFormsMap_mapExteriorPower d x)
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← heq, ← map_zero (mapExteriorPower k A K d)] at hx
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hx
  rw [smul_zero] at hc
  exact (Module.Flat.isSMulRegular_of_isRegular
    (IsRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c))).right_eq_zero_of_smul hc

/-- A tensor power of exponent one of a nonzero vector is nonzero. -/
private theorem formPow_one_ne_zero {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ}
    {c : ⋀[K]^d Ω[K⁄k]} (hc : c ≠ 0) :
    (MMP.Fourfold.formPow c 1 : PluriForms k K d (1 : ℕ)) ≠ 0 := by
  intro h
  apply hc
  have := congrArg (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k])
    (0 : Fin 1)) h
  exact (PiTensorProduct.subsingletonEquiv_apply_tprod (R := K) (0 : Fin 1) _).symm.trans
    (this.trans (LinearEquiv.map_zero _))

set_option maxRecDepth 20000 in
/-- **Nonzero global forms have nonzero rational forms**, on a smooth integral scheme, once a
restriction to a nonempty affine open is nonzero. -/
private theorem ratForm_ne_zero [Smooth sX] (n : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤))
    (hω : (sX.relativeDifferentialForms (n : ℤ)).presheaf.map
      (homOfLE (le_top : (W : X.Opens) ≤ ⊤)).op ω ≠ 0) :
    ratForm sX n ω ≠ 0 := by
  rw [ratForm_eq sX n W ω]
  let := functionFieldAlgebra sX
  refine formPow_one_ne_zero ?_
  let := sectionAlgebra sX W
  have := isScalarTower_section_functionField sX (W : X.Opens)
  have : Algebra.Smooth k Γ(X, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra sX W.2
  have := projective_exteriorPower (R := Γ(X, W)) (M := Ω[Γ(X, W)⁄k]) n
  have : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W W.2
  intro h0
  apply hω
  have h1 := topFormsMap_injective (k := k) (A := Γ(X, W)) (K := X.functionField) n
    (h0.trans (map_zero _).symm)
  exact (MMP.DeRham.formsAlgEquiv sX n W).injective (h1.trans (map_zero _).symm)

/-- Pull-back of a form of exponent one along an extension with a pull-back generator. -/
private theorem pullbackForms_formPow_one {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K]
    [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {ω₀ : ⋀[K]^d Ω[K⁄k]}
    (hω₀ : IsPullbackGenerator K' ω₀) (x : ⋀[K]^d Ω[K⁄k]) :
    pullbackForms (K' := K') ((1 : ℕ) : ℤ) (MMP.Fourfold.formPow x 1) =
      MMP.Fourfold.formPow (topFormsMap k K K' d x) 1 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hω₀.1 ▸ Submodule.mem_top (x := x))
  rw [MMP.Fourfold.formPow_smul, pow_one, MMP.Fourfold.pullbackForms_smul_formPow hω₀, map_smul,
    ← algebraMap_smul K' a, MMP.Fourfold.formPow_smul, pow_one]

/-- A nonempty open of the target has a nonempty preimage under a dominant morphism. -/
private theorem exists_affineOpens_le_preimage {T : Scheme.{u}} (h : T ⟶ X) [IsDominant h]
    (W : X.Opens) [Nonempty W] :
    ∃ W' : T.affineOpens, (W' : T.Opens) ≤ h ⁻¹ᵁ W ∧ Nonempty (W' : T.Opens) := by
  obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty W)
  obtain ⟨y, hy⟩ : (h ⁻¹ᵁ W : Set T).Nonempty := by
    obtain ⟨y, hy⟩ := h.denseRange.exists_mem_open W.isOpen ⟨x, hx⟩
    exact ⟨y, hy⟩
  obtain ⟨W', hW', hyW'⟩ := exists_affineOpens_le (h ⁻¹ᵁ W) hy
  exact ⟨W', hW', ⟨⟨y, hyW'⟩⟩⟩

/-- **Naturality of rational forms** under a dominant morphism of integral schemes of the same
dimension over a field of characteristic zero. -/
private theorem pullbackRationalPluriForms_ratForm [CharZero k] {T : Scheme.{u}} [IsIntegral T]
    (h : T ⟶ X) [IsDominant h] [LocallyOfFiniteType sX] [LocallyOfFiniteType (h ≫ sX)] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hT : topologicalKrullDim T = d)
    (ω : Γ(sX.relativeDifferentialForms (d : ℤ), ⊤)) :
    pullbackRationalPluriForms sX h (ratForm sX d ω) =
      ratForm (h ≫ sX) d ((Scheme.Hom.relativeDifferentialFormsMap h sX (h ≫ sX) (𝟙 _)
          (by rw [Category.comp_id]) (d : ℤ)).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _).app ⊤ ω)) := by
  obtain ⟨W', hW', hne⟩ := exists_affineOpens_le_preimage h (someAffine X : X.Opens)
  rw [ratForm_eq sX d (someAffine X), ratForm_eq (h ≫ sX) d W',
    chartForm_formPull sX h d (someAffine X) W' hW']
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (h ≫ sX)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sX h
  have := essFiniteType_functionField (sX := sX)
  have := MMP.Fourfold.trdeg_functionField_eq (sX := sX) (sX' := h ≫ sX) hX hT
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator (K := X.functionField) (K' := T.functionField)
    this
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hX)
  exact pullbackForms_formPow_one hω₀ _

set_option maxRecDepth 20000 in
/-- Rational forms are linear for the constants. -/
private theorem ratForm_const_smul (n : ℕ) (μ : k)
    (η : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    ratForm sX n ((sX.appTop ((Scheme.ΓSpecIso (.of k)).inv μ) : Γ(X, ⊤)) • η) =
      μ • ratForm sX n η := by
  unfold ratForm chartForm
  let := sectionAlgebra sX (someAffine X)
  let := functionFieldAlgebra sX
  have := isScalarTower_section_functionField sX ((someAffine X) : X.Opens)
  rw [Scheme.Modules.map_smul, map_smul, map_smul, ← algebraMap_smul X.functionField,
    MMP.Fourfold.formPow_smul, pow_one]
  have e : algebraMap Γ(X, (someAffine X : X.Opens)) X.functionField
      (X.presheaf.map (homOfLE (le_top : (someAffine X : X.Opens) ≤ ⊤)).op
        (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv μ))) = algebraMap k X.functionField μ := by
    rw [IsScalarTower.algebraMap_apply k Γ(X, (someAffine X : X.Opens)) X.functionField]
    rfl
  rw [e]
  rfl

end Regular

section Canonical

open MMP.Mori MMP.Fourfold

/-- **A smooth variety is a canonical pair** with the empty boundary: every exceptional divisor
over it has log discrepancy at least one (in fact at least two). -/
private theorem isRealCanonicalPair_zero {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {d : ℕ} (hd : 2 ≤ d)
    (hdim : topologicalKrullDim X = d) :
    IsRealCanonicalPair sX (QDivisor.toRDivisor 0) := by
  have : LocallyOfFinitePresentation sX := by
    have := hX.1; infer_instance
  haveI := hX.1
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hdim
  refine ⟨hX, fun P hP => (hP (by simp)).elim, ⟨d, K₀, hK₀, ?_⟩, fun n E a hE ha => ?_⟩
  · refine ⟨1, fun _ => 1, fun _ => K₀, fun _ => isCartier_of_isSmoothScheme hsm _, fun Γ => ?_⟩
    simp [DivisorWithCoeffs.coeff_apply]
  · obtain ⟨-, -, -, -, ⟨K, hK, -⟩, -⟩ := id ha
    have hn : (n : WithBot ℕ∞) = d := hK.topologicalKrullDim_eq.symm.trans hdim
    have hn' : n = d := by exact_mod_cast hn
    subst hn'
    have hP : MMP.Mori.IsPair sX (0 : QDivisor X) := ⟨hX, n, K, hK, by
      rw [add_zero]; exact QDivisor.isQCartier_toQDivisor (isCartier_of_isSmoothScheme hsm _)⟩
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E
    have h1 := discrep_le hE hc
    have hsnc : DivisorWithCoeffs.IsSNC sX
        (∑ E ∈ (∅ : Finset (MMP.Mori.PrimeDivisor X)), Finsupp.single E (1 : ℤ)) := by
      simpa using DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) sX hsm
    have h3 := discrep_eq_of_isSNC sX hX hsm hd hK (Δ := (0 : QDivisor X))
      (S := ∅) (by simp) hsnc (by simp)
    rw [h3] at h1
    simp only [Finset.notMem_empty, iInf_false, iInf_top, le_top, inf_of_le_right, top_inf_eq]
      at h1
    have h2 : (1 : ℝ) ≤ c := by exact_mod_cast EReal.coe_le_coe_iff.mp h1
    rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
    linarith

end Canonical

section Hom

open MMP.Mori MMP.Fourfold

variable {k : Type u} [Field k] {X T : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral T]

/-- The `k`-homomorphism of function fields `k(X) → k(T)` of a dominant morphism `h : T ⟶ X`
over `k`. -/
private noncomputable def ffHom (h : T ⟶ X) [IsDominant h] (hT : h ≫ sX = sT) :
    FunctionFieldHom sT sX :=
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sT
  { toRingHom := functionFieldMap h
    commutes' := fun c => by
      subst hT
      letI := functionFieldMapAlgebra h
      have := isScalarTower_functionFieldMap sX h
      exact (IsScalarTower.algebraMap_apply k X.functionField T.functionField c).symm }

private theorem pluriformPullback_ffHom (h : T ⟶ X) [IsDominant h] {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pluriformPullback (h ≫ sX) sX (ffHom h rfl) d m τ = pullbackRationalPluriForms sX h τ := rfl

/-- Pull-back of pluriforms along an extension with a pull-back generator is injective. -/
public theorem pullbackForms_injective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {ω₀ : ⋀[K]^d Ω[K⁄k]}
    (hω₀ : IsPullbackGenerator K' ω₀) (m : ℤ) :
    Function.Injective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro τ₁ τ₂ he
  rw [pullbackForms_eq hω₀, pullbackForms_eq hω₀, pullbackFormsAlong, pullbackFormsAlong] at he
  have h1 := smul_left_injective K'
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) m).ne_zero ()) he
  have h2 := (algebraMap K K').injective h1
  exact (ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) m).ext_elem
    fun i => by cases i; exact h2

/-- Over a field of characteristic zero, pull-back of rational pluriforms along a homomorphism
of function fields of integral schemes locally of finite type of the same dimension is injective. -/
public theorem pluriformPullback_injective {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [CharZero k]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hX' : topologicalKrullDim X' = d)
    (φ : FunctionFieldHom sX sX') (m : ℤ) :
    Function.Injective (pluriformPullback sX sX' φ d m) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_functionFieldHom hX hX' φ
  exact pullbackForms_injective hω₀ m

/-- Naturality of rational forms, for any structure morphism of the source. -/
private theorem pluriformPullback_ffHom_ratForm [CharZero k] (h : T ⟶ X) [IsDominant h]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sT] (hT : h ≫ sX = sT)
    (hh : h ≫ sX = sT ≫ 𝟙 _) {d : ℕ}
    (hX : topologicalKrullDim X = d) (hTd : topologicalKrullDim T = d)
    (ω : Γ(sX.relativeDifferentialForms (d : ℤ), ⊤)) :
    pluriformPullback sT sX (ffHom h hT) d ((1 : ℕ) : ℤ) (ratForm sX d ω) =
      ratForm sT d ((Scheme.Hom.relativeDifferentialFormsMap h sX sT (𝟙 _) hh (d : ℤ)).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app _).app ⊤ ω)) := by
  subst hT
  exact pullbackRationalPluriForms_ratForm sX h hX hTd ω

/-- **Pull-back of regular forms along a projective birational morphism of smooth varieties**
is regular, and only regular forms pull back to regular forms (the sections `H⁰(K)`). -/
private theorem pluriformPullback_mem_iff [PerfectField k] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace X] [CompactSpace T] [CharZero k]
    (h : T ⟶ X) [IsDominant h] (hT : h ≫ sX = sT) [Smooth sX] [Smooth sT]
    (hXv : MMP.Mori.IsVariety k sX) (hTv : MMP.Mori.IsVariety k sT)
    (hb : MMP.Mori.IsBirationalMorphism h)
    (hp : IsProjectiveMorphism h) {d : ℕ} (hd : 2 ≤ d) (hdim : topologicalKrullDim X = d)
    (τ : RationalPluriForms sX d ((1 : ℕ) : ℤ)) :
    pluriformPullback sT sX (ffHom h hT) d ((1 : ℕ) : ℤ) τ ∈
        logPluricanonicalSections sT d 1 0 ↔ τ ∈ logPluricanonicalSections sX d 1 0 := by
  subst hT
  have hsmX : IsSmoothScheme sX := (isSmoothScheme_iff sX).2 inferInstance
  have hsmT : IsSmoothScheme (h ≫ sX) := (isSmoothScheme_iff _).2 inferInstance
  have hXn : IsNormalVariety k sX := ⟨hXv, inferInstance⟩
  haveI := hXv
  haveI := hTv
  have hdT : topologicalKrullDim T = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (h ≫ sX) hb).symm.trans hdim
  have hK : ∀ {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
      [CompactSpace Y] {sY : Y ⟶ Spec (.of k)}, MMP.Mori.IsVariety k sY → IsSmoothScheme sY →
      topologicalKrullDim Y = d → ∃ K : Divisor Y, K.IsCanonicalDivisor sY d ∧
        (((1 : ℕ) : ℤ) • (Divisor.toQDivisor K + 0)).IsCartierDivisor := by
    intro Y _ _ _ _ sY hv hs hY
    haveI := hv
    obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sY hs hY
    refine ⟨K, hK, ?_⟩
    rw [add_zero, Nat.cast_one, one_smul]
    exact QDivisor.isCartierDivisor_toQDivisor.mpr (isCartier_of_isSmoothScheme hs _)
  have hbij := bijOn_pullbackRationalPluriForms_logPluricanonicalSections sX h hXv hTv hb hp d 1
    0 le_rfl (isRealCanonicalPair_zero hXn hsmX hd hdim) 0 le_rfl 0 (map_zero _) le_rfl
    (hK hXv hsmX hdim) (hK hTv hsmT hdT)
  rw [pluriformPullback_ffHom]
  refine ⟨fun hτ => ?_, fun hτ => hbij.mapsTo hτ⟩
  obtain ⟨τ', hτ', he⟩ := hbij.surjOn hτ
  have hinj := pluriformPullback_injective (sX := h ≫ sX) (sX' := sX) hdT hdim (ffHom h rfl)
    ((1 : ℕ) : ℤ)
  rwa [← hinj he]

end Hom

section Birational

open MMP.Mori MMP.Fourfold

/-- A morphism of integral schemes restricting to an open immersion on a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_ι_comp {P Z : Scheme.{u}} [IsIntegral P]
    [IsIntegral Z] (g : P ⟶ Z) (W : P.Opens) (hW : (W : Set P).Nonempty)
    [IsOpenImmersion (W.ι ≫ g)] : MMP.Mori.IsBirationalMorphism g := by
  let V : Z.Opens := (W.ι ≫ g).opensRange
  have hUV : W ≤ g ⁻¹ᵁ V := by
    intro w hw
    exact ⟨⟨w, hw⟩, rfl⟩
  have hc : g.resLE V W hUV ≫ V.ι = W.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have : IsOpenImmersion (g.resLE V W hUV ≫ V.ι) := by rw [hc]; infer_instance
  have : IsOpenImmersion (g.resLE V W hUV) := IsOpenImmersion.of_comp _ V.ι
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g W V hW ?_ hUV ?_
  · obtain ⟨w, hw⟩ := hW
    exact ⟨_, ⟨w, hw⟩, rfl⟩
  · rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
    obtain ⟨w, rfl⟩ := hz
    refine ⟨w, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hc]
    rfl

/-- Varieties with isomorphic function fields have the same dimension. -/
private theorem topologicalKrullDim_eq_of_bijective {k : Type u} [Field k] {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (sX : X ⟶ Spec (.of k)) (h : T ⟶ X) [IsDominant h]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (h ≫ sX)]
    (hb : Function.Bijective (functionFieldMap h)) :
    topologicalKrullDim T = topologicalKrullDim X := by
  rw [← toENat_trdeg_functionField (sX := h ≫ sX), ← toENat_trdeg_functionField (sX := sX),
    trdeg_functionField_eq_of_bijective sX h hb]

/-- A smooth projective variety with the empty boundary is an snc subboundary pair. -/
private theorem isSNCSubboundaryPair_zero {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hsm : IsSmoothScheme sX) :
    IsSNCSubboundaryPair sX 0 := by
  have : LocallyOfFinitePresentation sX := by
    have := hX.1; infer_instance
  exact ⟨hX, hsm, DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) sX hsm,
    fun P => by simp⟩

end Birational

section Eigen

open MMP.Mori MMP.Fourfold

variable {k : Type u} [Field k] {Z : Scheme.{u}} [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)}
  {U : Z.Opens} [Nonempty U] [IsDominant U.ι] (f : U.toScheme ⟶ Z) [IsDominant f]
  (hf : f ≫ sZ = U.ι ≫ sZ)

/-- The birational self-map `ι⁻¹ ∘ f` of an integral scheme given by an open immersion `f` of an
open `U`, on function fields: `(ι^*)⁻¹ ∘ f^* : k(Z) → k(Z)`. -/
private noncomputable def ffEquiv (hbf : Function.Bijective (functionFieldMap f))
    (hbι : Function.Bijective (functionFieldMap U.ι)) : FunctionFieldEquiv sZ sZ :=
  letI := functionFieldAlgebra sZ
  letI := functionFieldAlgebra (U.ι ≫ sZ)
  (AlgEquiv.ofBijective (ffHom f hf) hbf).trans
    (AlgEquiv.ofBijective (ffHom (sT := U.ι ≫ sZ) U.ι rfl) hbι).symm

private theorem ffHom_ι_comp_ffEquiv (hbf : Function.Bijective (functionFieldMap f))
    (hbι : Function.Bijective (functionFieldMap U.ι)) :
    letI := functionFieldAlgebra sZ
    letI := functionFieldAlgebra (U.ι ≫ sZ)
    (ffHom (sT := U.ι ≫ sZ) U.ι rfl).comp (ffEquiv f hf hbf hbι).toHom = ffHom f hf := by
  letI := functionFieldAlgebra sZ
  letI := functionFieldAlgebra (U.ι ≫ sZ)
  ext x
  exact (AlgEquiv.ofBijective (ffHom (sT := U.ι ≫ sZ) U.ι rfl) hbι).apply_symm_apply _

/-- **The eigenvalue relation on rational forms**: if `f^* ω = μ ι^* ω` on `U`, then the
birational self-map `ι⁻¹ ∘ f` multiplies the rational form of `ω` by `μ`. -/
private theorem pluriformPullback_ffEquiv_ratForm [CharZero k] [LocallyOfFiniteType sZ]
    [LocallyOfFiniteType (U.ι ≫ sZ)] {d : ℕ}
    (hZ : topologicalKrullDim Z = d) (hU : topologicalKrullDim U = d)
    (hbf : Function.Bijective (functionFieldMap f))
    (hbι : Function.Bijective (functionFieldMap U.ι))
    (ω : Γ(sZ.relativeDifferentialForms (d : ℤ), ⊤)) (μ : k)
    (h₁ : f ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _) (h₂ : U.ι ≫ sZ = (U.ι ≫ sZ) ≫ 𝟙 _)
    (he : (Scheme.Hom.relativeDifferentialFormsMap f sZ (U.ι ≫ sZ) (𝟙 _) h₁ (d : ℤ)).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app ⊤ ω) =
      ((U.ι ≫ sZ).appTop ((Scheme.ΓSpecIso (.of k)).inv μ) : Γ(U.toScheme, ⊤)) •
        (Scheme.Hom.relativeDifferentialFormsMap U.ι sZ (U.ι ≫ sZ) (𝟙 _) h₂ (d : ℤ)).app ⊤
          (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app _).app ⊤ ω)) :
    pluriformPullback sZ sZ (ffEquiv f hf hbf hbι).toHom d ((1 : ℕ) : ℤ) (ratForm sZ d ω) =
      μ • ratForm sZ d ω := by
  apply pluriformPullback_injective hU hZ (ffHom (sT := U.ι ≫ sZ) U.ι rfl)
  rw [pluriformPullback_comp hU hZ hZ, ffHom_ι_comp_ffEquiv, map_smul,
    pluriformPullback_ffHom_ratForm f hf h₁ hZ hU, he, ratForm_const_smul,
    pluriformPullback_ffHom_ratForm U.ι rfl h₂ hZ hU]

/-- On a resolution `π, g : W ⟶ Z` of the birational map, with `g = f ∘ π` over `U`, the
function-field map of `g` is that of `π` after `ι⁻¹ ∘ f`. -/
private theorem ffHom_eq_comp_ffEquiv {W : Scheme.{u}} [IsIntegral W] {sW : W ⟶ Spec (.of k)}
    (π g : W ⟶ Z) [IsDominant π] [IsDominant g] (hπ : π ≫ sZ = sW) (hg : g ≫ sZ = sW)
    [Nonempty (π ⁻¹ᵁ U)] (hg2 : (π ⁻¹ᵁ U).ι ≫ g = (π ∣_ U) ≫ f)
    (hbf : Function.Bijective (functionFieldMap f))
    (hbι : Function.Bijective (functionFieldMap U.ι)) :
    letI := functionFieldAlgebra sZ
    letI := functionFieldAlgebra sW
    ffHom g hg = (ffHom π hπ).comp (ffEquiv f hf hbf hbι).toHom := by
  letI := functionFieldAlgebra sZ
  letI := functionFieldAlgebra sW
  letI := functionFieldAlgebra (U.ι ≫ sZ)
  have : IsDominant (π ⁻¹ᵁ U).ι := MMP.Fourfold.isDominant_ι_of_nonempty _
  have : IsDominant ((π ∣_ U) ≫ U.ι) := by rw [morphismRestrict_ι]; infer_instance
  have : IsDominant (π ∣_ U) := IsDominant.of_comp_of_isOpenImmersion _ U.ι
  have hb' : Function.Bijective (functionFieldMap (π ⁻¹ᵁ U).ι) :=
    functionFieldMap_bijective_of_isOpenImmersion _ ⊤ ⟨Classical.arbitrary _, trivial⟩
  have hσ := congrArg (fun φ : FunctionFieldHom (U.ι ≫ sZ) sZ => φ)
    (ffHom_ι_comp_ffEquiv f hf hbf hbι)
  ext x
  apply hb'.1
  change functionFieldMap (π ⁻¹ᵁ U).ι (functionFieldMap g x) =
    functionFieldMap (π ⁻¹ᵁ U).ι (functionFieldMap π ((ffEquiv f hf hbf hbι) x))
  have hx : functionFieldMap U.ι ((ffEquiv f hf hbf hbι) x) = functionFieldMap f x :=
    DFunLike.congr_fun hσ x
  open MMP.Positivity.DivisorOver in
  rw [functionFieldMap_functionFieldMap_apply, functionFieldMap_functionFieldMap_apply,
    functionFieldMap_congr hg2, functionFieldMap_congr (morphismRestrict_ι π U).symm,
    ← functionFieldMap_functionFieldMap_apply, ← functionFieldMap_functionFieldMap_apply, hx]

end Eigen

/-! ### Unit modulus on an integral surface -/

/-- The rational form of a regular two-form is a regular (log-pluricanonical) section. -/
private theorem ratForm_mem_logPluricanonicalSections {Z : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (sZ : Z ⟶ Spec (.of ℂ))
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) :
    ratForm sZ 2 ω ∈ MMP.Fourfold.logPluricanonicalSections sZ 2 1 0 := by
  rw [MMP.Fourfold.mem_logPluricanonicalSections,
    MMP.Mori.mem_pluricanonicalSections_of_ne_bot (by simp)]
  intro Γ _ _
  simpa using ordForm_ratForm_nonneg sZ 2 ω Γ

/-- On a smooth projective integral surface, pulling back along the birational self-map
`ffEquiv f hf hbf hbι` preserves the regular two-forms. -/
private theorem pluriformPullback_ffEquiv_mem {Z : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (sZ : Z ⟶ Spec (.of ℂ)) [Smooth sZ]
    (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ) (U : Z.Opens)
    (hU : Dense (U : Set Z)) [Nonempty U] [IsDominant U.ι] (f : U.toScheme ⟶ Z)
    [IsOpenImmersion f] [IsDominant f] (hf : f ≫ sZ = U.ι ≫ sZ) (hvar : MMP.Mori.IsVariety ℂ sZ)
    (hd : topologicalKrullDim Z = 2) (hbf : Function.Bijective (functionFieldMap f))
    (hbι : Function.Bijective (functionFieldMap U.ι)) :
    ∀ s ∈ MMP.Fourfold.logPluricanonicalSections sZ 2 1 0,
      MMP.Fourfold.pluriformPullback sZ sZ (ffEquiv f hf hbf hbι).toHom 2 ((1 : ℕ) : ℤ) s ∈
        MMP.Fourfold.logPluricanonicalSections sZ 2 1 0 := by
  intro s0 hs0
  obtain ⟨W, π, g, T, hT, hg1, hg2, hv, hs, hdW, hPW, -, hiso, w, hwU, hwT⟩ :=
    exists_pointBlowup_resolution sZ hP hS U hU f hf
  haveI := hv
  haveI := hs
  haveI : IsIntegral W := hv.toIsIntegral
  haveI : IsProper (π ≫ sZ) := isProper_of_isProjectiveMorphism _ hPW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (π ≫ sZ)
  obtain ⟨hLNW, hNW⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    ((MMP.Mori.isSmoothScheme_iff _).2 inferInstance : MMP.Mori.IsSmoothScheme (π ≫ sZ))
  haveI := hLNW
  haveI := hNW
  let V : Z.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let W' : W.Opens := π ⁻¹ᵁ (U ⊓ V)
  have hW'ne : (W' : Set W).Nonempty := ⟨w, hwU, hwT⟩
  haveI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨w, hwU⟩⟩
  haveI := hiso
  haveI : IsIso (π ∣_ (U ⊓ V)) := isIso_restrict_of_le π inf_le_right
  have hW'π : IsOpenImmersion (W'.ι ≫ π) := by
    rw [← morphismRestrict_ι]; infer_instance
  have hle : W' ≤ π ⁻¹ᵁ U := fun x hx => hx.1
  have ha : IsOpenImmersion (W.homOfLE hle ≫ π ∣_ U) := by
    have h1 : (W.homOfLE hle ≫ π ∣_ U) ≫ U.ι = W'.ι ≫ π := by
      rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    have : IsOpenImmersion ((W.homOfLE hle ≫ π ∣_ U) ≫ U.ι) := by rw [h1]; exact hW'π
    exact IsOpenImmersion.of_comp _ U.ι
  have hW'g : IsOpenImmersion (W'.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι _ hle, Category.assoc, hg2, ← Category.assoc]
    infer_instance
  have hbπ : MMP.Mori.IsBirationalMorphism π :=
    isBirationalMorphism_of_isOpenImmersion_ι_comp π W' hW'ne
  have hbg : MMP.Mori.IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_ι_comp g W' hW'ne
  haveI : IsDominant π := hbπ.isDominant
  haveI : IsDominant g := hbg.isDominant
  have hpπ : IsProjectiveMorphism π := IsProjectiveMorphism.of_comp π sZ hPW
  have hpg : IsProjectiveMorphism g := IsProjectiveMorphism.of_comp g sZ (by rw [hg1]; exact hPW)
  have hrel := ffHom_eq_comp_ffEquiv f hf π g rfl hg1 hg2 hbf hbι
  have hgs := (pluriformPullback_mem_iff g hg1 hvar hv hbg hpg le_rfl hd s0).2 hs0
  rw [hrel, ← MMP.Fourfold.pluriformPullback_comp hdW hd hd] at hgs
  exact (pluriformPullback_mem_iff π rfl hvar hv hbπ hpπ le_rfl hd _).1 hgs

/-- On an integral surface, an eigenvalue of a birational self-map on a nonzero two-form has
absolute value one: the integral `∫ |ω|²` is invariant. -/
private theorem norm_eq_one_of_isFormEigen_of_isIntegral {Z : Scheme.{0}} [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of ℂ))
    (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ) (U : Z.Opens)
    (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) : ‖μ‖ = 1 := by
  classical
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  haveI : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  haveI hvar : MMP.Mori.IsVariety ℂ sZ := (MMP.Mori.isVariety_iff ℂ sZ).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hd : topologicalKrullDim Z = 2 := by
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible ℂ Z sZ x,
      topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 sZ x]
    rfl
  have hPV : MMP.Mori.IsProjectiveVariety ℂ sZ :=
    (MMP.Mori.isProjectiveVariety_iff ℂ sZ).2 ⟨hvar, hP⟩
  have hXs : MMP.Mori.IsSmoothScheme sZ := (MMP.Mori.isSmoothScheme_iff sZ).2 inferInstance
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hXs
  haveI : Nonempty U := hU.nonempty.to_subtype
  haveI : IsDominant U.ι := MMP.Fourfold.isDominant_ι_of_nonempty U
  haveI : IsDominant f := ⟨hfd⟩
  have hbf : Function.Bijective (functionFieldMap f) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion f ⊤ ⟨Classical.arbitrary _, trivial⟩
  have hbι : Function.Bijective (functionFieldMap U.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary _, trivial⟩
  have hdU : topologicalKrullDim U = 2 := (topologicalKrullDim_eq_of_bijective sZ U.ι hbι).trans hd
  unfold IsFormEigen formPull at he
  have heig := pluriformPullback_ffEquiv_ratForm (d := 2) f hf hd hdU hbf hbι ω μ _ _ he
  have hmem := ratForm_mem_logPluricanonicalSections sZ ω
  have hne : ratForm sZ 2 ω ≠ 0 := by
    haveI := nonempty_someAffine Z
    refine ratForm_ne_zero sZ 2 (someAffine Z) ω fun h0 => hω ?_
    exact eq_zero_of_res_eq_zero sZ 2 ω ⟨_, (Classical.arbitrary ((someAffine Z : Z.Opens))).2⟩ h0
  let σ := ffEquiv f hf hbf hbι
  have hσV := pluriformPullback_ffEquiv_mem sZ hP hS U hU f hf hvar hd hbf hbι
  obtain ⟨p, -, hpos, hsmul, hinv, -⟩ := MMP.Fourfold.exists_gauge_logPluricanonicalSections
    (m := 1) hd (isSNCSubboundaryPair_zero hPV hXs) (fun P => by simp) one_pos
    (fun P => ⟨0, by simp⟩)
  let s : MMP.Fourfold.logPluricanonicalSections sZ 2 1 0 := ⟨ratForm sZ 2 ω, hmem⟩
  have h1 := hinv σ hσV s
  have h2 : (⟨_, hσV s s.2⟩ : MMP.Fourfold.logPluricanonicalSections sZ 2 1 0) = μ • s :=
    Subtype.ext heig
  rw [h2, hsmul] at h1
  have hp := hpos s (fun h => hne (congrArg Subtype.val h))
  have h3 : ‖μ‖ ^ (2 : ℝ) = 1 := by
    have : ‖μ‖ ^ (2 / ((1 : ℕ) : ℝ) : ℝ) = 1 :=
      mul_right_cancel₀ hp.ne' (h1.trans (one_mul _).symm)
    simpa using this
  rw [Real.rpow_two] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

/-- On an integral surface, an eigenvalue of a birational self-map on a nonzero two-form is an
algebraic integer of degree at most `b₂(Z)`. -/
private theorem isIntegral_and_natDegree_le_of_isFormEigen_of_isIntegral {Z : Scheme.{0}}
    [IsIntegral Z]
    (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) :
    IsIntegral ℤ μ ∧ (minpoly ℚ μ).natDegree ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  obtain ⟨W, sW, hPW, hSW, p, q, hp, hq, F, hF, hform, s, hs⟩ :=
    exists_resolution_of_isFormEigen sZ hP hS U hU f hfd hf ω μ he
  obtain ⟨cl, hinj, hsmul, hnat⟩ := MMP.Fourfold.exists_injective_topFormBettiClass
  set x := cl sZ hP hS ω with hx
  have hx0 : x ≠ 0 := fun h0 => hω (hinj sZ hP hS (h0.trans (map_zero _).symm))
  have hxy : (relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) (analyticMap q hq)
        (Set.empty_subset _) 2).hom x =
      μ • (relativeSingularCohomology.map ℂ (ModuleCat.of ℂ ℂ) (analyticMap p hp)
        (Set.empty_subset _) 2).hom x := by
    rw [hx, ← hnat sW sZ hPW hSW hP hS q hq ω, ← hnat sW sZ hPW hSW hP hS p hp ω]
    exact (congrArg (cl sW hPW hSW) hform).trans (hsmul sW hPW hSW μ _)
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hP
  have hRV : MMP.SingularChain.RelVanishing ℤ (analyticSpace sZ) 1 F :=
    relVanishing_of_finite F hF fun y _ => relVanishing_singleton_complexPoints y
  have hstab := exists_period_eq_mul (analyticMap p hp) (analyticMap q hq) hRV s hs x μ hxy
  obtain ⟨-, hfin, hbc⟩ :=
    MMP.Analytic.exists_homotopyEquiv_singularChainComplex_of_isProjectiveMorphism sZ hP
  haveI := hfin 2
  obtain ⟨r, hr, Ψ, hΨ⟩ := exists_linearMap_period_eq_zero _ (fun _ => rfl) (hbc 2)
  obtain ⟨hint, hdeg⟩ := isIntegral_of_period_mul_mem hx0 Ψ (hΨ x) μ hstab
  refine ⟨hint, hdeg.trans (hr.trans_eq ?_)⟩
  rw [MMP.Analytic.singularCohomology, cohomologyWithSupports.univ]
  rfl

/-! ### The general case -/

/-- An eigenvalue of a birational self-map on a nonzero two-form has absolute value one. -/
private theorem norm_eq_one_of_isFormEigen {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ) (U : Z.Opens)
    (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) : ‖μ‖ = 1 := by
  obtain ⟨Z₁, s₁, _, hP₁, hS₁, k, hk, U₁, hU₁, f₁, _, hfd₁, hf₁, ω₁, hω₁, he₁, -⟩ :=
    exists_isIntegral_isFormEigen_pow sZ hP hS U hU f hfd hf ω μ hω he
  have h := norm_eq_one_of_isFormEigen_of_isIntegral s₁ hP₁ hS₁ U₁ hU₁ f₁ hfd₁ hf₁ ω₁ _ hω₁ he₁
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg μ) hk.ne').1 h

/-- An eigenvalue of a birational self-map on a nonzero two-form is an algebraic integer of
degree at most `b₂(Z)`. -/
private theorem isIntegral_and_natDegree_le_of_isFormEigen {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of ℂ)) (hP : IsProjectiveMorphism sZ) (hS : SmoothOfRelativeDimension 2 sZ)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (f : U.toScheme ⟶ Z) [IsOpenImmersion f]
    (hfd : Dense (Set.range f.base)) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) (hω : ω ≠ 0)
    (he : IsFormEigen sZ U f hf ω μ) :
    IsIntegral ℤ μ ∧ (minpoly ℚ μ).natDegree ≤
      Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) := by
  obtain ⟨Z₁, s₁, _, hP₁, hS₁, k, hk, U₁, hU₁, f₁, _, hfd₁, hf₁, ω₁, hω₁, he₁, hb⟩ :=
    exists_isIntegral_isFormEigen_pow sZ hP hS U hU f hfd hf ω μ hω he
  obtain ⟨hint, hdeg⟩ :=
    isIntegral_and_natDegree_le_of_isFormEigen_of_isIntegral s₁ hP₁ hS₁ U₁ hU₁ f₁ hfd₁ hf₁ ω₁ _
      hω₁ he₁
  refine ⟨IsIntegral.of_pow hk hint, ?_⟩
  obtain ⟨-, hle⟩ := isIntegral_and_natDegree_minpoly_le_of_pow hk (hint.tower_top (A := ℚ))
  calc _ ≤ k * (minpoly ℚ (μ ^ k)).natDegree := hle
    _ ≤ k * _ := Nat.mul_le_mul_left k hdeg
    _ ≤ _ := hb

/-- **Birational self-maps of a surface act on holomorphic two-forms by roots of unity of bounded
order.** For every `b : ℕ` there is `N > 0` with the following property. Let `sZ : Z ⟶ Spec ℂ`
be a smooth projective surface, possibly disconnected, with `dim_ℚ H²(Z^an; ℚ) ≤ b`. Let
`f : U ⟶ Z` be an open immersion over `ℂ` from a dense open `U ⊆ Z` with dense image, that is,
a birational self-map of `Z`. Suppose `ω ∈ H⁰(Z, Ω²_{Z/ℂ})` is nonzero and `f^* ω = μ ω` on
`U`. Then `μ` is an algebraic integer of degree at most `b`, all of its conjugates have
absolute value one, and `μ ^ N = 1`. -/
@[mmp "lem_fourfold_birational_surface_top_form_eigenvalue"]
public theorem exists_pow_eq_one_of_birational_surface_top_form_eigenvalue (b : ℕ) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)), IsProjectiveMorphism sZ →
        SmoothOfRelativeDimension 2 sZ →
        Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sZ) ∅ 2) ≤ b →
        ∀ (U : Z.Opens), Dense (U : Set Z) →
        ∀ (f : U.toScheme ⟶ Z) [IsOpenImmersion f], Dense (Set.range f.base) →
        ∀ (hf : f ≫ sZ = U.ι ≫ sZ)
          (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ), ω ≠ 0 →
          (Scheme.Hom.relativeDifferentialFormsMap f sZ (U.ι ≫ sZ) (𝟙 _) (by simp [hf]) 2).app ⊤
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app ⊤ ω) =
            (show U.toScheme.ringCatSheaf.obj.obj (op ⊤) from
                (U.ι ≫ sZ).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
              (show (Scheme.Hom.relativeDifferentialForms (U.ι ≫ sZ) 2).val.obj (op ⊤) from
                (Scheme.Hom.relativeDifferentialFormsMap U.ι sZ (U.ι ≫ sZ) (𝟙 _) (by simp) 2).app ⊤
                  (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app _).app ⊤ ω)) →
          IsIntegral ℤ μ ∧ (minpoly ℚ μ).natDegree ≤ b ∧
            (∀ z ∈ (minpoly ℚ μ).rootSet ℂ, ‖z‖ = 1) ∧ μ ^ N = 1 := by
  obtain ⟨N, hN, hNu⟩ :=
    MMP.Fourfold.exists_pow_eq_one_of_bounded_degree_unit_conjugates (A := ℂ) b
  refine ⟨N, hN, ?_⟩
  intro Z sZ hP hS hb U hU f _ hfd hf ω μ hω heq
  have he : IsFormEigen sZ U f hf ω μ := heq
  obtain ⟨hint, hdeg⟩ := isIntegral_and_natDegree_le_of_isFormEigen sZ hP hS U hU f hfd hf ω μ hω he
  have hroots : ∀ z ∈ (minpoly ℚ μ).rootSet ℂ, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨σ, rfl⟩ := exists_ringEquiv_apply_eq (hint.tower_top (A := ℚ)) hz
    obtain ⟨sZ', hP', hS', hf', ω', hω', he'⟩ :=
      exists_isFormEigen_conj σ sZ hP hS U hU f hfd hf ω μ hω he
    exact norm_eq_one_of_isFormEigen sZ' hP' hS' U hU f hfd hf' ω' (σ μ) hω' he'
  have hμ : μ ≠ 0 := by
    intro h0
    have := norm_eq_one_of_isFormEigen sZ hP hS U hU f hfd hf ω μ hω he
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact ⟨hint, hdeg.trans hb, hroots, hNu μ hμ hint (hdeg.trans hb) hroots⟩

end MMP.Fourfold
