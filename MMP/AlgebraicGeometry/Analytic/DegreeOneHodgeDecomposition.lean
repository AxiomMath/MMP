module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Curve.OneFormCupPositivity
public import MMP.AlgebraicGeometry.Analytic.Surface.CurveSliceCupProduct
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.DegreeOneSymmetry
public import MMP.AlgebraicGeometry.Bertini.FreeSystemIrreducible
public import MMP.AlgebraicGeometry.DeRham.PushforwardFormsDegreeOne
public import MMP.AlgebraicGeometry.Modules.VanishingAlongZeroScheme
public import MMP.AlgebraicGeometry.Positivity.AmpleCurveNegativePowers
public import MMP.AlgebraicGeometry.Positivity.AmpleSystemImageDimension
public import MMP.AlgebraicGeometry.Positivity.NegativeAmpleTwistSections

section

/-!
# The degree-one Hodge decomposition of a smooth projective curve or surface

Let `X` be a smooth projective complex variety of dimension `n ∈ {1, 2}`, with complex
realization `X^an`. A global holomorphic one-form `ω ∈ H⁰(X, Ω¹_X)` is closed, and so has a
de Rham class `[ω] ∈ H¹(X^an; ℂ)`: the class of the singular cocycle which, on a
continuously differentiable `1`-simplex `σ` inside the `ℂ`-points of an affine open `U` on
which `ω = ∑ⱼ fⱼ dgⱼ`, is the line integral
`∫_σ ω = ∫₀¹ ∑ⱼ fⱼ(σ t) (gⱼ ∘ σ)'(t) dt`.
These classes form the subspace `H^{1,0}(X)`, and with its image under complex conjugation of
coefficients they decompose
`H¹(X^an; ℂ) = H^{1,0}(X) ⊕ \overline{H^{1,0}(X)}`.
For an ample line bundle `A` with first Chern class `c = c₁(A)`, the Hermitian form
`i ∫_X α ∪ \overline{β} ∪ c^{n-1}` is positive on nonzero holomorphic classes, and
`α ∪ β ∪ c^{n-1} = 0` for two holomorphic classes, by type. Pull-back along morphisms of such
varieties, in particular restriction to smooth curves on a surface, preserves the decomposition.

## Main results

* `MMP.Analytic.hodgeDecomposition_one_of_isProjectiveVariety`: holomorphic one-forms are
  closed, have unique de Rham classes, these give the decomposition above, the polarization
  is positive, holomorphic classes pair to zero, and pull-back preserves both summands.

## Implementation notes

* `H¹(X^an; ℂ)` is `MMP.Analytic.analyticSingularCohomology ℂ _ 1`, products are taken in the
  cup-product ring `MMP.CohomologyRing`, and conjugation is the change of
  coefficients `MMP.Analytic.singularCohomology.mapCoeff (starRingEnd ℂ)`.
* The de Rham class is characterised by its values on the continuously differentiable
  `1`-simplices lying in affine charts, parametrised by `stdSimplexHomeomorphUnitInterval`
  from the vertex `0` to the vertex `1`; singular cohomology is computed by such small smooth
  simplices, so these values determine the class.
* Since `X^an` is a connected compact complex manifold of dimension `n`, `H^{2n}(X^an; ℂ)` is
  one-dimensional and spanned by `c^n`, with `∫_X c^n = A^n > 0`. The positivity of
  `i ∫_X ω ∧ \overline{ω} ∧ A^{n-1}` is therefore stated without an integration map, as
  `i • ([ω] ∪ \overline{[ω]} ∪ c^{n-1}) = t • c^n` with `t > 0`; the Fubini–Study
  normalisation of `c` is a positive multiple and does not change the sign of `t`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [P. Griffiths, J. Harris, *Principles of algebraic geometry*][GriffithsHarris], §0.6–0.7.
-/

open CategoryTheory AlgebraicGeometry Opposite MMP
open MMP.SingularChain MMP.SingularCochain
open MMP.Analytic MMP.Fourfold.Polarization
open MMP.Analytic.CurveCupPositivity (stdSimplex_apply_nonneg stdSimplex_two_add)

namespace MMP.FourfoldProofs.MmpConductorSurfaceH1PolarizationProof

/-! ### Line integrals of algebraic one-forms -/

section LineIntegral

open Set

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]

private theorem evalHom_algebraMap (U : V.Opens)
    (x : ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) (c : ℂ) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
    ComplexPoints.evalHom U x (algebraMap ℂ Γ(V, U) c) = c :=
  ComplexPoints.evalHom_baseRingHom U x c

/-- Two presentations `∑ fⱼ dgⱼ = ∑ f'ₖ dg'ₖ` of one algebraic one-form on `U` have the same line
integral along a `C¹` path: at each interior time, `h ↦ (h ∘ p)'(t)` is a derivation, so it
factors through the Kähler differentials. -/
private theorem lineInt_congr {U : V.Opens} {m m' : ℕ} {f g : Fin m → Γ(V, U)}
    {f' g' : Fin m' → Γ(V, U)}
    (h : letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
      ∑ j, f j • KaehlerDifferential.D ℂ Γ(V, U) (g j) =
        ∑ k, f' k • KaehlerDifferential.D ℂ Γ(V, U) (g' k))
    {p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U} (hC : IsC1Path p) :
    lineInt p f g = lineInt p f' g' := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
  have hb := evalHom_algebraMap (V := V) U
  have key : ∀ t ∈ Ioo (0 : ℝ) 1, ∑ j, ComplexPoints.eval U (f j) (p t) *
        deriv (fun s ↦ ComplexPoints.eval U (g j) (p s)) t =
      ∑ k, ComplexPoints.eval U (f' k) (p t) *
        deriv (fun s ↦ ComplexPoints.eval U (g' k) (p s)) t := by
    intro t ht
    have hd : ∀ h : Γ(V, U),
        DifferentiableAt ℝ (fun s ↦ ComplexPoints.evalHom U (p s) h) t := fun h ↦ by
      simpa only [ComplexPoints.evalHom_apply] using
        ((hC h).differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).differentiableAt
          (Icc_mem_nhds ht.1 ht.2)
    letI : Module Γ(V, U) ℂ := Module.compHom ℂ (ComplexPoints.evalHom U (p t))
    have e : ∀ (a : Γ(V, U)) (z : ℂ), a • z = ComplexPoints.evalHom U (p t) a * z :=
      fun _ _ ↦ rfl
    haveI : IsScalarTower ℂ Γ(V, U) ℂ := ⟨fun c a z ↦ by
      rw [e, e, Algebra.smul_def, map_mul, hb, smul_eq_mul, mul_assoc]⟩
    let D : Derivation ℂ Γ(V, U) ℂ :=
      { toFun := fun h ↦ deriv (fun s ↦ ComplexPoints.evalHom U (p s) h) t
        map_add' := fun a b ↦ by
          simp only [map_add]
          exact deriv_fun_add (hd a) (hd b)
        map_smul' := fun c a ↦ by
          simp only [Algebra.smul_def, map_mul, hb, RingHom.id_apply, smul_eq_mul]
          exact deriv_const_mul c (hd a)
        map_one_eq_zero' := by
          simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one]
          exact deriv_const _ _
        leibniz' := fun a b ↦ by
          simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, e, smul_eq_mul]
          rw [deriv_fun_mul (hd a) (hd b)]
          ring }
    have hl := congrArg D.liftKaehlerDifferential h
    simp only [map_sum, map_smul, Derivation.liftKaehlerDifferential_comp_D, e] at hl
    simpa only [D, Derivation.mk_coe, LinearMap.coe_mk, AddHom.coe_mk,
      ComplexPoints.evalHom_apply] using hl
  rw [lineInt, lineInt, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo key

/-- Concatenating presentations adds line integrals. -/
private theorem lineInt_append {U : V.Opens}
    {p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U} (hC : IsC1Path p) {m m' : ℕ}
    (f g : Fin m → Γ(V, U)) (f' g' : Fin m' → Γ(V, U)) :
    lineInt p (Fin.append f f') (Fin.append g g') = lineInt p f g + lineInt p f' g' := by
  rw [lineInt, lineInt, lineInt, ← intervalIntegral.integral_add
    (intervalIntegrable_lineInt hC f g) (intervalIntegrable_lineInt hC f' g')]
  congr 1
  ext t
  simp [Fin.sum_univ_add]

/-- Negating the coefficients negates the line integral. -/
private theorem lineInt_neg {U : V.Opens}
    (p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) {m : ℕ}
    (f g : Fin m → Γ(V, U)) :
    lineInt p (-f) g = -lineInt p f g := by
  rw [lineInt, lineInt, ← intervalIntegral.integral_neg]
  congr 1
  ext t
  simp only [Pi.neg_apply, ← ComplexPoints.evalHom_apply, map_neg, neg_mul,
    Finset.sum_neg_distrib]

/-- Scaling the coefficients by a constant scales the line integral. -/
private theorem lineInt_smul {U : V.Opens}
    (p : ℝ → ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) U) {m : ℕ}
    (f g : Fin m → Γ(V, U)) (c : ℂ) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
    lineInt p (fun j ↦ algebraMap ℂ Γ(V, U) c * f j) g = c * lineInt p f g := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U
  rw [lineInt, lineInt, ← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  simp only [← ComplexPoints.evalHom_apply, map_mul, evalHom_algebraMap, Finset.mul_sum,
    mul_assoc]

/-- A presentation of the restricted form in `⋀¹` is one of its image in `Ω`. -/
private theorem oneEquiv_eq_of_rep
    (ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (U : V.affineOpens) {m : ℕ} (f g : Fin m → Γ(V, U))
    (h : letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens);
        MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
          (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
    exteriorPower.oneEquiv Γ(V, U) Ω[Γ(V, U)⁄ℂ] (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
      (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op ω)) = ∑ j, f j • KaehlerDifferential.D ℂ Γ(V, U) (g j) := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  rw [h, map_sum]
  simp only [map_smul, exteriorPower.oneEquiv_ιMulti]

set_option maxRecDepth 8000 in
/-- De Rham classes are compatible with differences. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.sub
    {ω η : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (ha : IsDR V ω a)
    (hb : IsDR V η b) : IsDR V (ω - η) (a - b) := by
  obtain ⟨φ, hφ, rfl, hφi⟩ := ha
  obtain ⟨ψ, hψ, rfl, hψi⟩ := hb
  refine ⟨φ - ψ, sub_mem hφ hψ, (ofCocycle_sub hφ hψ).symm, ?_⟩
  intro U m f g hrep σ hσ hC
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  obtain ⟨m₁, f₁, g₁, h₁⟩ := exists_rep ω U
  obtain ⟨m₂, f₂, g₂, h₂⟩ := exists_rep η U
  rw [Pi.sub_apply, hφi U m₁ f₁ g₁ h₁ σ hσ hC, hψi U m₂ f₂ g₂ h₂ σ hσ hC, sub_eq_add_neg,
    ← lineInt_neg, ← lineInt_append hC]
  refine lineInt_congr ?_ hC
  have e := oneEquiv_eq_of_rep (ω - η) U f g hrep
  rw [map_sub, map_sub, map_sub, oneEquiv_eq_of_rep ω U f₁ g₁ h₁,
    oneEquiv_eq_of_rep η U f₂ g₂ h₂] at e
  rw [Fin.sum_univ_add, ← e]
  simp [sub_eq_add_neg, neg_smul]

/-- Restriction of regular functions carries constants to constants. -/
private theorem presheaf_map_algebraMap (U : V.Opens) (c : ℂ) :
    V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (@algebraMap ℂ Γ(V, ⊤) _ _ (MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) ⊤) c) =
      @algebraMap ℂ Γ(V, U) _ _ (MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) U) c := by
  have e₁ : (⊤ : V.Opens) ≤ (V ↘ Spec (.of ℂ)) ⁻¹ᵁ ⊤ := by simp
  have e₂ : U ≤ (V ↘ Spec (.of ℂ)) ⁻¹ᵁ ⊤ := by simp
  have h : (V ↘ Spec (.of ℂ)).appLE ⊤ ⊤ e₁ ≫ V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
      (V ↘ Spec (.of ℂ)).appLE ⊤ U e₂ := Scheme.Hom.appLE_map _ _ _
  change (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ ((V ↘ Spec (.of ℂ)).appLE ⊤ ⊤ e₁ ≫
      V.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op))).hom c =
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (V ↘ Spec (.of ℂ)).appLE ⊤ U e₂).hom c
  rw [h]

set_option maxRecDepth 8000 in
/-- De Rham classes are compatible with multiplication by constants. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.smul
    {ω : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (ha : IsDR V ω a) (c : ℂ) :
    IsDR V (@algebraMap ℂ Γ(V, ⊤) _ _ (MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) ⊤) c • ω)
      (c • a) := by
  obtain ⟨φ, hφ, rfl, hφi⟩ := ha
  refine ⟨c • φ, Submodule.smul_mem _ c hφ, (ofCocycle_smul hφ c).symm, ?_⟩
  intro U m f g hrep σ hσ hC
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
  obtain ⟨m₁, f₁, g₁, h₁⟩ := exists_rep ω U
  rw [Pi.smul_apply, smul_eq_mul, hφi U m₁ f₁ g₁ h₁ σ hσ hC, ← lineInt_smul]
  refine lineInt_congr ?_ hC
  have e := oneEquiv_eq_of_rep _ U f g hrep
  rw [Scheme.Modules.map_smul, presheaf_map_algebraMap, map_smul, map_smul,
    oneEquiv_eq_of_rep ω U f₁ g₁ h₁] at e
  rw [← e, Finset.smul_sum]
  simp only [smul_smul]

set_option maxRecDepth 8000 in
/-- The zero form has the zero class. -/
private theorem isDR_zero :
    IsDR V 0 (0 : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1) := by
  refine ⟨0, zero_mem _, ?_, ?_⟩
  · simpa using (ofCocycle_smul (Y := Analytification.space (V ↘ Spec (.of ℂ))) (zero_mem _)
      (0 : ℂ)).symm
  · intro U m f g hrep σ hσ hC
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens)
    have e := oneEquiv_eq_of_rep 0 U f g hrep
    rw [map_zero, map_zero, map_zero] at e
    rw [Pi.zero_apply, lineInt_congr (f' := fun _ : Fin 0 ↦ 0) (g' := fun _ : Fin 0 ↦ 0)
      (by rw [← e]; simp) hC]
    simp [lineInt]

/-- De Rham classes are compatible with sums. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.add
    {ω η : Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1} (ha : IsDR V ω a)
    (hb : IsDR V η b) : IsDR V (ω + η) (a + b) := by
  simpa using ha.sub (isDR_zero.sub hb)

end LineIntegral

/-! ### Conjugation and pull-back of classes -/

section Conj

/-- Conjugating coefficients twice is the identity on `H¹`. -/
private theorem mapCoeff_star_star {Y : TopCat.{0}} (a : singularCohomology ℂ Y 1) :
    singularCohomology.mapCoeff (starRingEnd ℂ) 1
      (singularCohomology.mapCoeff (starRingEnd ℂ) 1 a) = a := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 1 a
  rw [singularCohomology.mapCoeff_ofCocycle, singularCohomology.mapCoeff_ofCocycle]
  exact cohomologyWithSupports.ofCocycle_congr
    (by ext σ; simp [singularCohomology.cochainMap_apply]) _ _

/-- Pull-back of the class of a cocycle is the class of the pulled-back cocycle. -/
private theorem pullback_ofCocycle {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) {φ : Simplex Y 1 → ℂ}
    (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set Y) 1) :
    (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ ((1 : ℕ) : ℤ)).hom
      (cohomologyWithSupports.ofCocycle ℂ Y 1 φ hφ) =
      cohomologyWithSupports.ofCocycle ℂ Y' 1 (cochainPullback ℂ g 1 φ)
        (cochainPullback_mem_relCocycles g (fun _ hx ↦ hx) hφ) := by
  apply (relativeSingularCohomologyEquiv ℂ (Set.univᶜ : Set Y') 1).injective
  have key := relativeSingularCohomologyEquiv_map (R := ℂ) g (A' := (Set.univᶜ : Set Y'))
    (A := (Set.univᶜ : Set Y)) (fun _ hx ↦ absurd (Set.mem_univ _) hx) 1
    (cohomologyWithSupports.ofCocycle ℂ Y 1 φ hφ)
  refine key.trans ?_
  simp only [cohomologyWithSupports.ofCocycle, LinearEquiv.apply_symm_apply]
  rfl

/-- Pull-back commutes with conjugation of coefficients. -/
private theorem pullback_mapCoeff_star {Y' Y : TopCat.{0}} (g : Y' ⟶ Y)
    (a : singularCohomology ℂ Y 1) :
    (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ ((1 : ℕ) : ℤ)).hom
      (singularCohomology.mapCoeff (starRingEnd ℂ) 1 a) =
      singularCohomology.mapCoeff (Y := Y') (starRingEnd ℂ) 1
        ((cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ) g Set.univ ((1 : ℕ) : ℤ)).hom a) := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq 1 a
  rw [singularCohomology.mapCoeff_ofCocycle, pullback_ofCocycle, pullback_ofCocycle]
  erw [singularCohomology.mapCoeff_ofCocycle]
  rfl

end Conj

/-! ### Pull-back of one-forms -/

section PullbackForms

open Stacks.AlgebraicGeometry.AffineOpenDeRham

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

private theorem comp_eq_comp_id {f : Y ⟶ X} (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ)) :
    f ≫ (X ↘ Spec (.of ℂ)) = (Y ↘ Spec (.of ℂ)) ≫ 𝟙 _ := by
  rw [hf, Category.comp_id]

/-- The pull-back `f^*ω` of a global one-form along a morphism over `ℂ`. -/
private noncomputable def pullbackForm (f : Y ⟶ X) (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ))
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    Γ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤) :=
  ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
    (homOfLE (fun _ _ ↦ trivial : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤)).op
    (deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
      (comp_eq_comp_id hf) 1 ω)

/-- The comparison of forms sends the exact form `d a` to `d a`. -/
private theorem formsAlgEquiv_symm_ιMulti_D {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    (W : V.affineOpens) (a : Γ(V, W)) :
    letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (W : V.Opens)
    (MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 W).symm
        (exteriorPower.ιMulti Γ(V, W) 1 fun _ ↦ KaehlerDifferential.D ℂ Γ(V, W) a) =
      (formsSectionsIso (V ↘ Spec (.of ℂ)) W.2 (isAffineOpen_top _) (by simp) 1).inv
        (exteriorPower.ιMulti Γ(V, W) 1 fun _ ↦ CommRingCat.KaehlerDifferential.d a) := by
  letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (W : V.Opens)
  rw [LinearEquiv.symm_apply_eq, MMP.DeRham.formsAlgEquiv_apply]
  erw [Iso.inv_hom_id_apply]
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext x
  simp only [Function.comp_apply, LinearEquiv.coe_coe]
  exact (MMP.DeRham.kaehlerBaseEquiv_d _ _ _ a).symm

/-- **Pull-back of an exact one-form, restricted to an affine open**: `f^*(d a)|_V = d (f^♯ a)`. -/
private theorem map_pushforward_formsSectionsIso_inv (f : Y ⟶ X)
    (hcomm : f ≫ (X ↘ Spec (.of ℂ)) = (Y ↘ Spec (.of ℂ)) ≫ 𝟙 _)
    (U : X.affineOpens) (V : Y.affineOpens) (e : (V : Y.Opens) ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE e).op
      (deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _) hcomm 1
        ((formsSectionsIso (X ↘ Spec (.of ℂ)) U.2 (isAffineOpen_top _) (by simp) 1).inv
          (exteriorPower.ιMulti Γ(X, U) 1 fun _ ↦ CommRingCat.KaehlerDifferential.d a))) =
      (formsSectionsIso (Y ↘ Spec (.of ℂ)) V.2 (isAffineOpen_top _) (by simp) 1).inv
        (exteriorPower.ιMulti Γ(Y, V) 1 fun _ ↦
          CommRingCat.KaehlerDifferential.d (f.appLE U V e a)) := by
  have h1 := formsSectionsIso_inv_ιMulti_d (X ↘ Spec (.of ℂ)) U.2 (isAffineOpen_top _)
    (by simp : (U : X.Opens) ≤ (X ↘ Spec (.of ℂ)) ⁻¹ᵁ ⊤) 1 (fun _ ↦ a)
  have h2 := formsSectionsIso_inv_ιMulti_d (Y ↘ Spec (.of ℂ)) V.2 (isAffineOpen_top _)
    (by simp : (V : Y.Opens) ≤ (Y ↘ Spec (.of ℂ)) ⁻¹ᵁ ⊤) 1 (fun _ ↦ f.appLE U V e a)
  beta_reduce at h1 h2
  first
  | rw [h1, h2]
  | erw [h1, h2]
  first
  | (unfold deRhamFormsPushforwardSections
     erw [Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft])
  | erw [deRhamFormsPushforwardSections_apply,
      Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft]
  | erw [Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft]
  refine ((Scheme.Hom.deRhamAlgebras (Y ↘ Spec (.of ℂ))).exterior.toPresheafGradedAlgebra.homogeneousProdLeft_naturality
    (homOfLE e).op 1 _).trans ?_
  congr 1
  funext i
  first
  | exact AlgebraicGeometry.SheafOfModules.exactOne_map _ _ _
  | exact (PresheafOfModules.naturality_apply (Scheme.Modules.exteriorGenerator
        (Scheme.Hom.relativeDifferentials (Y ↘ Spec (.of ℂ)))).val (homOfLE e).op _).symm.trans
      (congrArg _ ((Scheme.Hom.universalRelativeDerivation (Y ↘ Spec (.of ℂ))).d_map _ _).symm)
  | exact (PresheafOfModules.naturality_apply (Scheme.Modules.exteriorGenerator
        (Scheme.Hom.relativeDifferentials (Y ↘ Spec (.of ℂ)))).val (homOfLE e).op _).symm.trans
      (congrArg _ (PresheafOfModules.Derivation.d_map _ _ _).symm)

/-- Restricting the pull-back of a global form to `V ⊆ f⁻¹U` factors through the pull-back of its
restriction to `U`. -/
private theorem map_pullbackForm (f : Y ⟶ X) (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ))
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE le_top).op (pullbackForm f hf ω) =
      ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE e).op
        (deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
          (comp_eq_comp_id hf) 1
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω)) := by
  have hnat : deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
        (comp_eq_comp_id hf) 1
        (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op ω) =
      ((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
        (homOfLE (fun _ _ ↦ trivial : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ ⊤)).op
        (deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
          (comp_eq_comp_id hf) 1 ω) :=
    PresheafOfModules.naturality_apply
      ((Scheme.Hom.deRhamFormsPushforwardHom f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
        (comp_eq_comp_id hf)).app ((1 : ℕ) : ℤ)).val (homOfLE (le_top : U ≤ ⊤)).op ω
  rw [hnat, pullbackForm, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The pull-back of local forms is additive over finite sums. -/
private theorem deRhamFormsPushforwardSections_sum (f : Y ⟶ X)
    (hcomm : f ≫ (X ↘ Spec (.of ℂ)) = (Y ↘ Spec (.of ℂ)) ≫ 𝟙 _) {U : X.Opens} {ι : Type*}
    (t : Finset ι) (x : ι → Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), U)) :
    deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _) hcomm 1
        (∑ j ∈ t, x j) =
      ∑ j ∈ t, deRhamFormsPushforwardSections f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
        hcomm 1 (x j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := deRhamFormsPushforwardSections_add f (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) (𝟙 _)
      hcomm 1 (U := U) 0 0
    rw [add_zero] at h0
    simpa using h0
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    exact deRhamFormsPushforwardSections_add f _ _ _ hcomm 1 _ _

/-- **Presentations of a pulled-back one-form.** If `ω|_U = ∑ aⱼ dbⱼ` on an affine open `U` of
`X`, then `(f^*ω)|_V = ∑ f^♯aⱼ d(f^♯bⱼ)` on every affine open `V ⊆ f⁻¹U` of `Y`. -/
private theorem formsAlgEquiv_pullbackForm (f : Y ⟶ X)
    (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ))
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (U : X.affineOpens) (V : Y.affineOpens) (e : (V : Y.Opens) ≤ f ⁻¹ᵁ U) {k : ℕ}
    (a b : Fin k → Γ(X, U))
    (h : letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens);
        MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U
          (((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
            (homOfLE le_top).op ω) =
          ∑ j, a j • exteriorPower.ιMulti Γ(X, U) 1
            (fun _ ↦ KaehlerDifferential.D ℂ Γ(X, U) (b j))) :
    letI := MMP.Mori.sectionAlgebra (Y ↘ Spec (.of ℂ)) (V : Y.Opens)
    MMP.DeRham.formsAlgEquiv (Y ↘ Spec (.of ℂ)) 1 V
        (((Y ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE le_top).op (pullbackForm f hf ω)) =
      ∑ j, f.appLE U V e (a j) • exteriorPower.ιMulti Γ(Y, V) 1
        (fun _ ↦ KaehlerDifferential.D ℂ Γ(Y, V) (f.appLE U V e (b j))) := by
  letI := MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) (U : X.Opens)
  letI := MMP.Mori.sectionAlgebra (Y ↘ Spec (.of ℂ)) (V : Y.Opens)
  -- `ω|_U = ∑ aⱼ d bⱼ` in the sheaf of forms
  have hω : ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
      (homOfLE le_top).op ω =
      ∑ j, a j • (formsSectionsIso (X ↘ Spec (.of ℂ)) U.2 (isAffineOpen_top _) (by simp) 1).inv
        (exteriorPower.ιMulti Γ(X, U) 1 fun _ ↦ CommRingCat.KaehlerDifferential.d (b j)) := by
    apply (MMP.DeRham.formsAlgEquiv (X ↘ Spec (.of ℂ)) 1 U).injective
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, ← formsAlgEquiv_symm_ιMulti_D, LinearEquiv.apply_symm_apply]
  rw [map_pullbackForm f hf ω U V e, hω, deRhamFormsPushforwardSections_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [deRhamFormsPushforwardSections_smul, Scheme.Modules.map_smul, map_smul]
  erw [map_pushforward_formsSectionsIso_inv f (comp_eq_comp_id hf) U V e (b j)]
  refine congrArg₂ (· • ·) rfl ?_
  rw [← formsAlgEquiv_symm_ιMulti_D, LinearEquiv.apply_symm_apply]

/-- Values of pulled-back functions at a point are values at its image. -/
private theorem eval_appLE {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ X)
    (hf : f ≫ sX = sY) {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : Γ(X, U))
    (y : ComplexPoints sY) (hy : y ∈ ComplexPoints.chart (sX := sY) V)
    (hy' : ComplexPoints.realize f hf y ∈ ComplexPoints.chart (sX := sX) U) :
    ComplexPoints.eval V (f.appLE U V e h) ⟨y, hy⟩ =
      ComplexPoints.eval U h ⟨ComplexPoints.realize f hf y, hy'⟩ := by
  simp only [ComplexPoints.eval]
  change (Scheme.ΓSpecIso (.of ℂ)).hom ((f.appLE U V e ≫ y.hom.appLE V ⊤ hy.ge) h) = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

/-- A point of `V(ℂ)` maps into `U(ℂ)` when `V ⊆ f⁻¹U`. -/
private theorem realize_mem_chart {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ X)
    (hf : f ≫ sX = sY) {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) {y : ComplexPoints sY}
    (hy : y ∈ ComplexPoints.chart (sX := sY) V) :
    ComplexPoints.realize f hf y ∈ ComplexPoints.chart (sX := sX) U := by
  rw [ComplexPoints.mem_chart_iff] at hy ⊢
  exact e hy

/-- Straight segments of an étale coordinate ball are `C¹` chart simplices: regular functions are
analytic in étale coordinates. -/
private theorem isC1Path_segSimplex {m : ℕ} {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [SmoothOfRelativeDimension m (Z ↘ Spec (.of ℂ))]
    (c : ComplexPoints.EtaleCoordinateChart (Z ↘ Spec (.of ℂ)) m) (V : Z.Opens)
    {D : Set (Fin m → ℂ)} (hD : Convex ℝ D) (hDt : D ⊆ c.toOpenPartialHomeomorph.target)
    (hDV : ∀ v ∈ D, c.toOpenPartialHomeomorph.symm v ∈
      ComplexPoints.chart (sX := Z ↘ Spec (.of ℂ)) V)
    {a b : Fin m → ℂ} (ha : a ∈ D) (hb : b ∈ D)
    (hmem : ∀ s, segSimplex (Y := Analytification.space (Z ↘ Spec (.of ℂ)))
      c.toOpenPartialHomeomorph hD hDt ha hb s ∈ ComplexPoints.chart (sX := Z ↘ Spec (.of ℂ)) V) :
    IsC1Path (simplexPath V (segSimplex (Y := Analytification.space (Z ↘ Spec (.of ℂ)))
      c.toOpenPartialHomeomorph hD hDt ha hb) hmem) := by
  intro h
  obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd V h
  have hLD : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → (1 - t) • a + t • b ∈ D :=
    fun t ht ↦ segment_mem hD ha hb ht.1 ht.2
  have hL : ContDiff ℝ 1 fun t : ℝ ↦ (1 - t) • a + t • b :=
    ((contDiff_const.sub contDiff_id).smul contDiff_const).add (contDiff_id.smul contDiff_const)
  refine ContDiffOn.congr (f := fun t ↦ G ((1 - t) • a + t • b)) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · exact (((hG _ ⟨hDt (hLD t ht), hDV _ (hLD t ht)⟩).contDiffAt.restrict_scalars ℝ).comp t
      hL.contDiffAt).contDiffWithinAt
  · simp only [simplexPath, segSimplex, ContinuousMap.coe_mk, symm_projIcc_apply_one ht]
    have hv := hDt (hLD t ht)
    rw [hGe _ (c.toOpenPartialHomeomorph_symm_mem hv), c.toOpenPartialHomeomorph.right_inv hv]

end PullbackForms

/-! ### Gluing local primitives, and products of holomorphic classes on a curve -/

section Gluing

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- On `ℂ¹`, a function whose real derivative is `∑ⱼ Hfⱼ • d Hgⱼ` with `Hgⱼ` holomorphic is
holomorphic: its real derivative is complex linear. -/
private theorem analyticAt_of_hasFDerivAt_sum {D : Set (Fin 1 → ℂ)} (hDo : IsOpen D) {m : ℕ}
    (Hf Hg : Fin m → (Fin 1 → ℂ) → ℂ) (hg : ∀ j, ∀ z ∈ D, AnalyticAt ℂ (Hg j) z)
    {Φ : (Fin 1 → ℂ) → ℂ} (hΦ : ∀ z ∈ D, HasFDerivAt Φ (∑ j, Hf j z • fderiv ℝ (Hg j) z) z)
    {z : Fin 1 → ℂ} (hz : z ∈ D) : AnalyticAt ℂ Φ z := by
  have hd : DifferentiableOn ℂ Φ D := fun w hw ↦ by
    have hcoe : ⇑(∑ j, Hf j w • fderiv ℂ (Hg j) w) = ⇑(∑ j, Hf j w • fderiv ℝ (Hg j) w) := by
      ext u
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [(hg j w hw).differentiableAt.fderiv_restrictScalars ℝ]
      rfl
    have h : HasFDerivAt Φ (∑ j, Hf j w • fderiv ℂ (Hg j) w) w := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero, hcoe]
      exact hasFDerivAt_iff_isLittleO_nhds_zero.1 (hΦ w hw)
    exact h.differentiableAt.differentiableWithinAt
  let φ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hd' : DifferentiableOn ℂ (Φ ∘ φ.symm) (φ.symm ⁻¹' D) :=
    hd.comp (φ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).differentiableOn fun _ h ↦ h
  have ha := hd'.analyticAt ((hDo.preimage φ.symm.continuous).mem_nhds
    (show φ.symm (φ z) ∈ D by simpa using hz))
  have hΦφ : Φ = (Φ ∘ φ.symm) ∘ φ := by ext; simp
  rw [hΦφ]
  exact ha.comp ((φ : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt z)

/-- Two `ℂ`-linear forms on `ℂ¹` are proportional: `L u M v = L v M u`. -/
private theorem fin_one_antisymm (L M : (Fin 1 → ℂ) →L[ℂ] ℂ) (u v : Fin 1 → ℂ) :
    L u * M v - L v * M u = 0 := by
  have hu : u = u 0 • (fun _ ↦ 1) := by ext i; fin_cases i; simp
  have hv : v = v 0 • (fun _ ↦ 1) := by ext i; fin_cases i; simp
  rw [hu, hv]
  simp only [map_smul, smul_eq_mul]
  ring

/-- `H` is a primitive of `F dG` on `B`: at every time `t` with `q t ∈ B` of a path `q` along
which the regular functions of an affine chart are differentiable, `G ∘ q` is differentiable and
`(H ∘ q)'(t) = F(q t) (G ∘ q)'(t)`. -/
private def IsRelPrimitive (B : Set (ComplexPoints (X ↘ Spec (.of ℂ))))
    (F G H : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ) : Prop :=
  ∀ (U : X.affineOpens) (q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ))) (t : ℝ), ContinuousAt q t →
    q t ∈ B → q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (U : X.Opens) →
    (∀ h : Γ(X, U), DifferentiableAt ℝ (fun t ↦ evalT (U : X.Opens) h (q t)) t) →
    DifferentiableAt ℝ (fun s ↦ G (q s)) t ∧
      HasDerivAt (fun s ↦ H (q s)) (F (q t) * deriv (fun s ↦ G (q s)) t) t

/-- **Local primitives on a curve.** On a smooth curve, every point has an open neighbourhood
carrying local primitives `F`, `G` of two closed one-forms and a primitive `H` of `F dG`: in a
one-dimensional étale coordinate, `F dG` is a holomorphic one-form, hence closed. -/
private theorem exists_local_primitive_triple [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (hdω : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0)
    (hdη : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) η = 0)
    (x : ComplexPoints (X ↘ Spec (.of ℂ))) :
    ∃ (B : Set (ComplexPoints (X ↘ Spec (.of ℂ)))) (F G H : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ),
      IsOpen B ∧ x ∈ B ∧ IsLocalPrimitive ω B F ∧ IsLocalPrimitive η B G ∧
        IsRelPrimitive B F G H := by
  obtain ⟨c, V, r, hr, hxe, hball⟩ := exists_chartBall (n := 1) isOpen_univ (Set.mem_univ x)
  set e := c.toOpenPartialHomeomorph
  set D := Metric.ball (e x) r
  have hD : Convex ℝ D := convex_ball _ _
  have hDo : IsOpen D := Metric.isOpen_ball
  have hDV : D ⊆ e.target ∩
      e.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) :=
    fun z hz ↦ ⟨(hball hz).1, (hball hz).2.1⟩
  have hH : ∀ h : Γ(X, V), ∀ z ∈ D, AnalyticAt ℂ (fun w ↦ evalT (V : X.Opens) h (e.symm w)) z :=
    fun h z hz ↦ analyticAt_evalT_symm c V h (hDV hz)
  obtain ⟨m₁, f₁, g₁, h₁⟩ := exists_rep ω V
  obtain ⟨m₂, f₂, g₂, h₂⟩ := exists_rep η V
  obtain ⟨Φ₁, hΦ₁⟩ := exists_hasFDerivAt_sum_smul_fderiv hD hDo
    (fun j w ↦ evalT (V : X.Opens) (f₁ j) (e.symm w))
    (fun j w ↦ evalT (V : X.Opens) (g₁ j) (e.symm w)) (fun j ↦ hH (f₁ j)) (fun j ↦ hH (g₁ j))
    (fun z hz u v ↦ sum_fderiv_antisymm_chart ω hdω c V f₁ g₁ h₁ (hDV hz) u v)
  obtain ⟨Φ₂, hΦ₂⟩ := exists_hasFDerivAt_sum_smul_fderiv hD hDo
    (fun j w ↦ evalT (V : X.Opens) (f₂ j) (e.symm w))
    (fun j w ↦ evalT (V : X.Opens) (g₂ j) (e.symm w)) (fun j ↦ hH (f₂ j)) (fun j ↦ hH (g₂ j))
    (fun z hz u v ↦ sum_fderiv_antisymm_chart η hdη c V f₂ g₂ h₂ (hDV hz) u v)
  have hA₁ : ∀ z ∈ D, AnalyticAt ℂ Φ₁ z := fun z hz ↦
    analyticAt_of_hasFDerivAt_sum hDo _ _ (fun j ↦ hH (g₁ j)) hΦ₁ hz
  have hA₂ : ∀ z ∈ D, AnalyticAt ℂ Φ₂ z := fun z hz ↦
    analyticAt_of_hasFDerivAt_sum hDo _ _ (fun j ↦ hH (g₂ j)) hΦ₂ hz
  obtain ⟨Ψ, hΨ⟩ := exists_hasFDerivAt_sum_smul_fderiv (m := 1) hD hDo (fun _ ↦ Φ₁)
    (fun _ ↦ Φ₂) (fun _ ↦ hA₁) (fun _ ↦ hA₂) fun z hz u v ↦ by
      simp only [Fin.sum_univ_one]
      rw [(hA₁ z hz).differentiableAt.fderiv_restrictScalars ℝ,
        (hA₂ z hz).differentiableAt.fderiv_restrictScalars ℝ]
      exact fin_one_antisymm _ _ u v
  refine ⟨e.source ∩ e ⁻¹' D, fun y ↦ Φ₁ (e y), fun y ↦ Φ₂ (e y), fun y ↦ Ψ (e y),
    e.isOpen_inter_preimage hDo, ⟨hxe, Metric.mem_ball_self hr⟩,
    isLocalPrimitive_comp ω c V hDV f₁ g₁ h₁ hΦ₁, isLocalPrimitive_comp η c V hDV f₂ g₂ h₂ hΦ₂,
    ?_⟩
  intro U q t hq hqB hqU hC
  have hW : q t ∈ c.W := c.source_toOpenPartialHomeomorph ▸ hqB.1
  have hw := hasDerivAt_chart_comp c U hq hW hqU hC
  have hG := ((hA₂ _ hqB.2).differentiableAt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hw
  refine ⟨hG.differentiableAt, ?_⟩
  refine ((hΨ _ hqB.2).comp_hasDerivAt t hw).congr_deriv ?_
  have hGd : deriv (fun s ↦ Φ₂ (e (q s))) t =
      fderiv ℝ Φ₂ (e (q t)) (deriv (fun t' ↦ e (q t')) t) := hG.deriv
  show (∑ _j : Fin 1, Φ₁ (e (q t)) • fderiv ℝ Φ₂ (e (q t))) (deriv (fun t' ↦ e (q t')) t) =
    Φ₁ (e (q t)) * deriv (fun s ↦ Φ₂ (e (q s))) t
  rw [hGd, Fin.sum_univ_one, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Two primitives of `F dG` differ locally by a multiple of `G`.** If `(F₁, G₁, H₁)` and
`(F₂, G₂, H₂)` are local primitives of `ω`, `η` and `F dG` on `B₁` and `B₂`, then
`H₁ - H₂ - (F₁ - F₂) G₁` is locally constant on `B₁ ∩ B₂`: there `F₁ - F₂` and `G₁ - G₂` are
locally constant, and along straight segments of an étale ball the derivative of the difference
vanishes. -/
private theorem eventually_eq_of_isRelPrimitive {n : ℕ}
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    {B₁ B₂ : Set (ComplexPoints (X ↘ Spec (.of ℂ)))}
    {F₁ F₂ G₁ G₂ H₁ H₂ : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ} (hB₁ : IsOpen B₁) (hB₂ : IsOpen B₂)
    (hF₁ : IsLocalPrimitive ω B₁ F₁) (hF₂ : IsLocalPrimitive ω B₂ F₂)
    (hG₁ : IsLocalPrimitive η B₁ G₁) (hG₂ : IsLocalPrimitive η B₂ G₂)
    (hH₁ : IsRelPrimitive B₁ F₁ G₁ H₁) (hH₂ : IsRelPrimitive B₂ F₂ G₂ H₂)
    {w : ComplexPoints (X ↘ Spec (.of ℂ))} (hw : w ∈ B₁ ∩ B₂) :
    ∀ᶠ z in nhds w, H₁ z - H₂ z - (F₁ z - F₂ z) * G₁ z =
      H₁ w - H₂ w - (F₁ w - F₂ w) * G₁ w := by
  have hF := eventually_sub_eq_of_isLocalPrimitive (n := n) ω hB₁ hB₂ hF₁ hF₂ hw
  have hG := eventually_sub_eq_of_isLocalPrimitive (n := n) η hB₁ hB₂ hG₁ hG₂ hw
  obtain ⟨N, hNsub, hNo, hwN⟩ := mem_nhds_iff.1 ((hF.and hG).and ((hB₁.inter hB₂).mem_nhds hw))
  obtain ⟨c, V, r, hr, hwe, hball⟩ := exists_chartBall (n := n) hNo hwN
  set e := c.toOpenPartialHomeomorph
  set k := F₁ w - F₂ w with hk
  filter_upwards [e.open_source.mem_nhds hwe,
    e.continuousAt hwe (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] with z hz hzD
  let L : ℝ → Fin n → ℂ := fun t ↦ e w + t • (e z - e w)
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  have hLd : Differentiable ℝ L := by fun_prop
  set S : Set ℝ := L ⁻¹' Metric.ball (e w) r
  have hSo : IsOpen S := Metric.isOpen_ball.preimage hLc
  have hSc : _root_.IsPreconnected S := by
    refine Convex.isPreconnected fun s hs t ht a b ha hb hab ↦ ?_
    obtain rfl : b = 1 - a := by linarith
    have := convex_ball (e w) r hs ht ha hb hab
    simp only [S, L, Set.mem_preimage] at this ⊢
    convert this using 1
    module
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, L, Set.mem_preimage, zero_smul, add_zero]
    exact Metric.mem_ball_self hr
  have h1 : (1 : ℝ) ∈ S := by
    simp only [S, L, Set.mem_preimage, one_smul, add_sub_cancel]
    exact hzD
  let q : ℝ → ComplexPoints (X ↘ Spec (.of ℂ)) := fun t ↦ e.symm (L t)
  have hqN : ∀ t ∈ S, q t ∈ N := fun t ht ↦ (hball ht).2.2
  have hqV : ∀ t ∈ S, q t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) (V : X.Opens) :=
    fun t ht ↦ (hball ht).2.1
  have hqc : ∀ t ∈ S, ContinuousAt q t := fun t ht ↦
    (e.continuousAt_symm (hball ht).1).comp hLc.continuousAt
  have hdiff : ∀ t ∈ S, ∀ h : Γ(X, V),
      DifferentiableAt ℝ (fun t ↦ evalT (V : X.Opens) h (q t)) t := by
    intro t ht h
    obtain ⟨G, hGa, hGe⟩ := c.exists_analyticOnNhd V h
    have hev : (fun t ↦ G (L t)) =ᶠ[nhds t] fun t ↦ evalT (V : X.Opens) h (q t) := by
      filter_upwards [hSo.mem_nhds ht] with t' ht'
      have hv := (hball ht').1
      rw [evalT_of_mem _ (hqV t' ht'), ComplexPoints.evalHom_apply,
        hGe _ (c.toOpenPartialHomeomorph_symm_mem hv) (hqV t' ht'), e.right_inv hv]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev.symm
    exact ((hGa _ ⟨(hball ht).1, hqV t ht⟩).differentiableAt.restrictScalars ℝ).comp t (hLd t)
  let K : ℝ → ℂ := fun t ↦ H₁ (q t) - H₂ (q t) - k * G₁ (q t)
  have hK : ∀ t ∈ S, HasDerivAt K 0 t := by
    intro t ht
    have hB : q t ∈ B₁ ∩ B₂ := (hNsub (hqN t ht)).2
    obtain ⟨hG₁d, hH₁d⟩ := hH₁ V q t (hqc t ht) hB.1 (hqV t ht) (hdiff t ht)
    obtain ⟨-, hH₂d⟩ := hH₂ V q t (hqc t ht) hB.2 (hqV t ht) (hdiff t ht)
    have hFk : F₁ (q t) - F₂ (q t) = k := (hNsub (hqN t ht)).1.1
    have hGe : deriv (fun s ↦ G₂ (q s)) t = deriv (fun s ↦ G₁ (q s)) t := by
      have hev : (fun s ↦ G₂ (q s)) =ᶠ[nhds t] fun s ↦ G₁ (q s) - (G₁ w - G₂ w) := by
        filter_upwards [hSo.mem_nhds ht] with s hs
        have := (hNsub (hqN s hs)).1.2
        linear_combination -this
      rw [hev.deriv_eq, deriv_sub_const]
    refine ((hH₁d.sub hH₂d).sub (hG₁d.hasDerivAt.const_mul k)).congr_deriv ?_
    rw [hGe]
    linear_combination (deriv (fun s ↦ G₁ (q s)) t) * hFk
  have hconst := hSo.is_const_of_deriv_eq_zero hSc
    (fun t ht ↦ (hK t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hK t ht).deriv) h0 h1
  have hq0 : q 0 = w := by
    show e.symm (e w + (0 : ℝ) • (e z - e w)) = w
    rw [zero_smul, add_zero, e.left_inv hwe]
  have hq1 : q 1 = z := by
    show e.symm (e w + (1 : ℝ) • (e z - e w)) = z
    rw [one_smul, add_sub_cancel, e.left_inv hz]
  have hFz : F₁ z - F₂ z = k := by
    have := (hNsub (hqN 1 h1)).1.1
    rwa [hq1] at this
  have e0 : K 0 = H₁ w - H₂ w - k * G₁ w := by simp only [K, hq0]
  have e1 : K 1 = H₁ z - H₂ z - k * G₁ z := by simp only [K, hq1]
  rw [hFz, ← e1, ← e0]
  exact hconst.symm

end Gluing

/-! ### The maximum principle for real parts -/

section MaxPrinciple

open _root_.Topology Filter

/-- If the real part of a holomorphic function has a local maximum, it is locally constant:
`‖exp Ψ‖ = exp (re Ψ)` and the maximum modulus principle. -/
private theorem eventually_re_eq_of_isLocalMax_re {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ψ : E → ℂ} {D : Set E} (hD : IsOpen D) (hΨ : DifferentiableOn ℂ Ψ D)
    {z : E} (hz : z ∈ D) (hmax : IsLocalMax (fun w ↦ (Ψ w).re) z) :
    ∀ᶠ w in 𝓝 z, (Ψ w).re = (Ψ z).re := by
  have hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun w ↦ Complex.exp (Ψ w)) w := by
    filter_upwards [hD.mem_nhds hz] with w hw
    exact ((hΨ w hw).differentiableAt (hD.mem_nhds hw)).cexp
  have hm : IsLocalMax (fun w ↦ ‖Complex.exp (Ψ w)‖) z := by
    filter_upwards [hmax] with w hw
    simp only [Complex.norm_exp]
    exact Real.exp_le_exp.2 hw
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hd hm] with w hw
  have := congrArg (fun t ↦ ‖t‖) hw
  simp only [Complex.norm_exp] at this
  exact Real.exp_injective this

/-- A holomorphic function whose real part is locally constant has derivative zero. -/
private theorem fderiv_eq_zero_of_eventually_re_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ψ : E → ℂ} {z : E} (hΨ : DifferentiableAt ℂ Ψ z)
    (hc : ∀ᶠ w in 𝓝 z, (Ψ w).re = (Ψ z).re) : fderiv ℂ Ψ z = 0 := by
  have h1 : HasFDerivAt (fun w ↦ (Ψ w).re)
      (Complex.reCLM.comp ((fderiv ℂ Ψ z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hΨ.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (fun w ↦ (Ψ w).re) (0 : E →L[ℝ] ℝ) z :=
    (hasFDerivAt_const ((Ψ z).re) z).congr_of_eventuallyEq hc
  have h3 := h1.unique h2
  ext v
  have a := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h3
  have b := congrArg (fun L : E →L[ℝ] ℝ ↦ L (Complex.I • v)) h3
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, ContinuousLinearMap.zero_apply, map_smul, smul_eq_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at a b
  apply Complex.ext
  · simpa using a
  · simpa using b

/-- **The maximum principle on a compact connected space.** A function which near every point
is, in some chart, the real part of a holomorphic function plus a constant, is constant. -/
private theorem eq_of_forall_locally_re {Y E : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [NormedAddCommGroup E] [NormedSpace ℂ E] (u : Y → ℝ)
    (hloc : ∀ y : Y, ∃ (e : OpenPartialHomeomorph Y E) (D : Set E) (Ψ : E → ℂ) (c : ℝ),
      y ∈ e.source ∧ e y ∈ D ∧ IsOpen D ∧ DifferentiableOn ℂ Ψ D ∧
        ∀ w ∈ e.source ∩ e ⁻¹' D, u w = (Ψ (e w)).re + c) :
    ∀ y y', u y = u y' := by
  have hcont : Continuous u := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    obtain ⟨e, D, Ψ, c, hy, hyD, hD, hΨ, hu⟩ := hloc y
    have hn : e.source ∩ e ⁻¹' D ∈ 𝓝 y :=
      (e.isOpen_inter_preimage hD).mem_nhds ⟨hy, hyD⟩
    have h1 : ContinuousAt (fun w ↦ (Ψ (e w)).re + c) y :=
      ((Complex.continuous_re.continuousAt.comp
        ((hΨ _ hyD).continuousWithinAt.continuousAt (hD.mem_nhds hyD))).comp
          (e.continuousAt hy)).add continuousAt_const
    exact h1.congr (by filter_upwards [hn] with w hw; exact (hu w hw).symm)
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  set S := {y | u y = u y₀}
  have hSc : IsClosed S := isClosed_eq hcont continuous_const
  have hSo : IsOpen S := by
    refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
    obtain ⟨e, D, Ψ, c, hys, hyD, hD, hΨ, hu⟩ := hloc y
    have hn : e.source ∩ e ⁻¹' D ∈ 𝓝 y :=
      (e.isOpen_inter_preimage hD).mem_nhds ⟨hys, hyD⟩
    have hmax : IsLocalMax (fun w ↦ (Ψ w).re) (e y) := by
      have hT : e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' D) ∈ 𝓝 (e y) :=
        (e.isOpen_inter_preimage_symm (e.isOpen_inter_preimage hD)).mem_nhds
          ⟨e.map_source hys, by simp [e.left_inv hys, hys, hyD]⟩
      filter_upwards [hT] with z hz
      have h1 := hu _ hz.2
      have h2 := hu y ⟨hys, hyD⟩
      rw [e.right_inv hz.1] at h1
      have h3 := hy₀ (Set.mem_univ (e.symm z))
      have h4 : u y = u y₀ := hy
      simp only [Set.mem_setOf_eq] at h3
      linarith
    have hev := eventually_re_eq_of_isLocalMax_re hD hΨ hyD hmax
    have hev' : ∀ᶠ w in 𝓝 y, (Ψ (e w)).re = (Ψ (e y)).re := e.continuousAt hys hev
    filter_upwards [hev', hn] with w h1 h2
    show u w = u y₀
    rw [← (show u y = u y₀ from hy), hu w h2, hu y ⟨hys, hyD⟩, h1]
  have hS : S = Set.univ :=
    (isClopen_iff.1 ⟨hSc, hSo⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨y₀, rfl⟩)
  intro y y'
  have a : y ∈ S := hS ▸ Set.mem_univ y
  have b : y' ∈ S := hS ▸ Set.mem_univ y'
  exact a.trans b.symm

end MaxPrinciple

/-! ### The holomorphic and antiholomorphic subspaces -/

section Decomposition

open Stacks.Chow (integralComponentAt)
open Stacks.Intersection.ExteriorProductProjections
  (relativeDimension_eq_of_topologicalKrullDim_closure integralComponentAt_subschemeι_genericPoint)

variable {n : ℕ} {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]

variable (X) in
/-- The inclusion of `Hⁱ(X^an; ℂ)` into the cohomology ring. -/
private noncomputable abbrev inclH (i : ℕ) :
    analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) i →+
      CohomologyRing ℂ (Analytification.space (X ↘ Spec (.of ℂ))) :=
  DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
    (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) i

/-- The complex first Chern class of an invertible module, in the cohomology ring. -/
private noncomputable abbrev chernH (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    CohomologyRing ℂ (Analytification.space (X ↘ Spec (.of ℂ))) :=
  inclH X 2 (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))

set_option maxRecDepth 8000 in
/-- **Existence of de Rham classes.** Every global one-form has a de Rham class: its line
integrals along `C¹` chart simplices extend to a singular cocycle (local holomorphic primitives
of the closed form, continued along simplices). -/
private theorem exists_isDR (hn : n = 1 ∨ n = 2)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ α, IsDR X ω α := by
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨-, -, hcl⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  have hd : (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0 :=
    (hcl X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).2 ω
  choose B F hBo hmem hprim using fun x ↦ exists_local_primitive (n := n) ω hd x
  obtain ⟨φ, hφ, h, -⟩ := isDR_of_isLocalPrimitive (n := n) ω B F hBo hmem hprim
  exact ⟨_, h⟩

/-- **On a curve, holomorphic classes cup to zero.** With local primitives `F`, `G` of the two
forms and a primitive `H` of `F dG` on a common ball, the cup product cocycle is, on small
simplices, the coboundary of `τ ↦ -(H(τ₁) - H(τ₀) - F(τ₀)(G(τ₁) - G(τ₀)))`, a cochain which is
independent of the ball. -/
private theorem cupNatUniv_eq_zero_of_isDR (h1 : n = 1)
    {ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (ha : IsDR X ω a)
    (hb : IsDR X η b) :
    cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a b = 0 := by
  subst h1
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨-, -, hcl⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  have hd := (hcl X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).2
  choose B F G H hBo hmem hF hG hH using fun x ↦
    exists_local_primitive_triple ω η (hd ω) (hd η) x
  obtain ⟨φ, hφ, hφDR, hφv⟩ := isDR_of_isLocalPrimitive (n := 1) ω B F hBo hmem hF
  obtain ⟨ψ, hψ, hψDR, hψv⟩ := isDR_of_isLocalPrimitive (n := 1) η B G hBo hmem hG
  rw [IsDR.unique (Or.inl rfl) ha hφDR, IsDR.unique (Or.inl rfl) hb hψDR,
    cupNatUniv_ofCocycle _ 1 1 hφ hψ]
  -- the correction cochain
  let θ : ComplexPoints (X ↘ Spec (.of ℂ)) →
      Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1 → ℂ := fun y τ ↦
    H y (τ (stdSimplex.vertex 1)) - H y (τ (stdSimplex.vertex 0)) -
      F y (τ (stdSimplex.vertex 0)) * (G y (τ (stdSimplex.vertex 1)) - G y (τ (stdSimplex.vertex 0)))
  obtain ⟨Θ, hΘ⟩ := exists_cochain_of_forall_eq (Y := Analytification.space (X ↘ Spec (.of ℂ)))
    B θ fun τ y₁ y₂ h₁ h₂ ↦ by
      have h₁₂ : Set.range τ ⊆ B y₁ ∩ B y₂ := Set.subset_inter h₁ h₂
      have eF := apply_vertex_eq_of_eventually τ (f := fun z ↦ F y₁ z - F y₂ z) h₁₂
        (fun w hw ↦ eventually_sub_eq_of_isLocalPrimitive (n := 1) ω (hBo y₁) (hBo y₂) (hF y₁)
          (hF y₂) hw) 1 0
      have eG := apply_vertex_eq_of_eventually τ (f := fun z ↦ G y₁ z - G y₂ z) h₁₂
        (fun w hw ↦ eventually_sub_eq_of_isLocalPrimitive (n := 1) η (hBo y₁) (hBo y₂) (hG y₁)
          (hG y₂) hw) 1 0
      have eK := apply_vertex_eq_of_eventually τ
        (f := fun z ↦ H y₁ z - H y₂ z - (F y₁ z - F y₂ z) * G y₁ z) h₁₂
        (fun w hw ↦ eventually_eq_of_isRelPrimitive (n := 1) ω η (hBo y₁) (hBo y₂) (hF y₁)
          (hF y₂) (hG y₁) (hG y₂) (hH y₁) (hH y₂) hw) 1 0
      simp only [θ]
      linear_combination eK + G y₁ (τ (stdSimplex.vertex 1)) * eF -
        F y₂ (τ (stdSimplex.vertex 0)) * eG
  have hφ0 : coboundary ℂ 1 φ = 0 := LinearMap.mem_ker.1 hφ.2
  have hψ0 : coboundary ℂ 1 ψ = 0 := LinearMap.mem_ker.1 hψ.2
  set χ := cup 1 1 (1 + 1) rfl φ ψ + coboundary ℂ 1 Θ with hχdef
  have hχ : χ ∈ relCocycles ℂ
      (Set.univᶜ : Set (Analytification.space (X ↘ Spec (.of ℂ)))) (1 + 1) := by
    refine ⟨fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp), LinearMap.mem_ker.2 ?_⟩
    rw [hχdef, map_add, coboundary_cup, hφ0, hψ0, coboundary_coboundary]
    simp
  have heq : cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) (cup 1 1 (1 + 1) rfl φ ψ)
      (cup_mem_relCocycles_compl_univ rfl hφ hψ) =
      cohomologyWithSupports.ofCocycle ℂ _ (1 + 1) χ hχ := by
    simp only [cohomologyWithSupports.ofCocycle]
    congr 1
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    refine Submodule.mem_map.2 ⟨-Θ, fun σ hσ ↦ absurd (hσ ⟨stdSimplex.vertex 0, rfl⟩) (by simp),
      ?_⟩
    show coboundary ℂ 1 (-Θ) = cup 1 1 (1 + 1) rfl φ ψ - χ
    rw [hχdef, map_neg]
    abel
  rw [heq]
  refine ofCocycle_eq_zero_of_forall_small hχ fun y ↦ ⟨B y, hBo y, hmem y, fun σ hσ ↦ ?_⟩
  have hface : ∀ k : Fin 3, Set.range (σ.comp (face 1 k)) ⊆ B y :=
    fun k _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  have hfr : Set.range (σ.comp (smap (front 1 (1 + 1) (by omega)))) ⊆ B y :=
    fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  have hbk : Set.range (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) ⊆ B y :=
    fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩
  rw [hχdef, Pi.add_apply, cup_apply, hφv _ y hfr, hψv _ y hbk, coboundary_apply,
    Fin.sum_univ_three, hΘ _ y (hface 0), hΘ _ y (hface 1), hΘ _ y (hface 2)]
  have vf0 : (σ.comp (smap (front 1 (1 + 1) (by omega)))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vf1 : (σ.comp (smap (front 1 (1 + 1) (by omega)))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vb0 : (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have vb1 : (σ.comp (smap (back 1 (1 + 1) 1 (by omega)))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (stdSimplex.map_vertex _ _)
  have v00 : (σ.comp (face 1 (0 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (face_vertex (0 : Fin 3) (0 : Fin 2))
  have v01 : (σ.comp (face 1 (0 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (face_vertex (0 : Fin 3) (1 : Fin 2))
  have v10 : (σ.comp (face 1 (1 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (face_vertex (1 : Fin 3) (0 : Fin 2))
  have v11 : (σ.comp (face 1 (1 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (2 : Fin 3)) := congrArg σ (face_vertex (1 : Fin 3) (1 : Fin 2))
  have v20 : (σ.comp (face 1 (2 : Fin 3))) (stdSimplex.vertex 0) =
      σ (stdSimplex.vertex (0 : Fin 3)) := congrArg σ (face_vertex (2 : Fin 3) (0 : Fin 2))
  have v21 : (σ.comp (face 1 (2 : Fin 3))) (stdSimplex.vertex 1) =
      σ (stdSimplex.vertex (1 : Fin 3)) := congrArg σ (face_vertex (2 : Fin 3) (1 : Fin 2))
  simp only [θ]
  rw [vf0, vf1, vb0, vb1, v00, v01, v10, v11, v20, v21]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul]
  ring

set_option maxRecDepth 8000 in
/-- **Pull-back of de Rham classes.** The pull-back of a de Rham class of `ω` is a de Rham class
of the pulled-back form `f^* ω`. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.pullback (hn : n = 1 ∨ n = 2) {m : ℕ}
    (hm : m = 1 ∨ m = 2)
    (Y : Scheme.{0}) [Y.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension m (Y ↘ Spec (.of ℂ))]
    (f : Y ⟶ X) (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ))
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (hα : IsDR X ω α) :
    IsDR Y (pullbackForm f hf ω) ((cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
      (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
      Set.univ ((1 : ℕ) : ℤ)).hom α) := by
  obtain ⟨β, hβ⟩ := exists_isDR (n := m) (X := Y) hm (pullbackForm f hf ω)
  suffices hpb : (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
      (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
      Set.univ ((1 : ℕ) : ℤ)).hom α = β by rwa [hpb]
  obtain ⟨φ, hφ, rfl, hφi⟩ := hα
  obtain ⟨φ', hφ', rfl, hφi'⟩ := hβ
  set g : Analytification.space (Y ↘ Spec (.of ℂ)) ⟶ Analytification.space (X ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩ with hg
  rw [pullback_ofCocycle]
  have hpφ : cochainPullback ℂ g 1 φ ∈
      relCocycles ℂ (Set.univᶜ : Set (Analytification.space (Y ↘ Spec (.of ℂ)))) 1 :=
    cochainPullback_mem_relCocycles g (fun _ hx ↦ hx) hφ
  suffices key : cohomologyWithSupports.ofCocycle ℂ (Analytification.space (Y ↘ Spec (.of ℂ))) 1
      (cochainPullback ℂ g 1 φ - φ') (sub_mem hpφ hφ') = 0 by
    rw [ofCocycle_sub hpφ hφ'] at key
    exact sub_eq_zero.1 key
  refine ofCocycle_eq_zero_of_forall_small _ fun y ↦ ?_
  -- an affine chart `U ∋ f(y)` of `X` and an affine chart `y ∈ V ⊆ f⁻¹U` of `Y`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ComplexPoints.realize f hf y).toScheme) isOpen_univ
  have hyfU : y.toScheme ∈ ((f ⁻¹ᵁ U : Y.Opens) : Set Y) := hxU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyfU (f ⁻¹ᵁ U).isOpen
  have e : V ≤ f ⁻¹ᵁ U := hVU
  -- a ball in étale coordinates of `Y` at `y`, inside `V(ℂ)`
  obtain ⟨c, hyc⟩ := ComplexPoints.EtaleCoordinateChart.exists_mem_W
    (sX := Y ↘ Spec (.of ℂ)) (n := m) y
  set E := c.toOpenPartialHomeomorph
  have hsrc : E.source = c.W := c.source_toOpenPartialHomeomorph
  have hyE : y ∈ E.source := hsrc ▸ hyc
  set S := E.target ∩ E.symm ⁻¹' ComplexPoints.chart (sX := Y ↘ Spec (.of ℂ)) V
  have hSo : IsOpen S := E.isOpen_inter_preimage_symm (ComplexPoints.isOpen_chart _ V)
  have hyS : E y ∈ S :=
    ⟨E.map_source hyE, by
      rw [Set.mem_preimage, E.left_inv hyE]
      exact ComplexPoints.mem_chart_iff.2 hyV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo (E y) hyS
  have hD : Convex ℝ (Metric.ball (E y) r) := convex_ball _ _
  have hDt : Metric.ball (E y) r ⊆ E.target := fun v hv ↦ (hball hv).1
  refine ⟨E.source ∩ E ⁻¹' Metric.ball (E y) r, E.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hyE, Metric.mem_ball_self hr⟩, fun σ hσ ↦ ?_⟩
  have hδ : coboundary ℂ 1 (cochainPullback ℂ g 1 φ - φ') = 0 := by
    have h1 := LinearMap.mem_ker.1 hφ.2
    have h2 := LinearMap.mem_ker.1 hφ'.2
    rw [map_sub, coboundary_cochainPullback, h1, h2, map_zero, sub_zero]
  refine eq_zero_of_forall_segSimplex (Y := Analytification.space (Y ↘ Spec (.of ℂ))) E hD hDt
    hδ (fun a b ha hb ↦ ?_) σ (fun s ↦ hσ ⟨s, rfl⟩)
  -- on a segment, both cocycles are the line integral of a presentation of `ω` on `U`
  set s := segSimplex (Y := Analytification.space (Y ↘ Spec (.of ℂ))) E hD hDt ha hb
  have hsV : ∀ t, s t ∈ ComplexPoints.chart (sX := Y ↘ Spec (.of ℂ)) V := fun t ↦
    (hball (segment_mem hD ha hb (stdSimplex_apply_nonneg t 1)
      (by linarith [stdSimplex_apply_nonneg t 0, stdSimplex_two_add t]))).2
  have hC : IsC1Path (simplexPath V s hsV) :=
    isC1Path_segSimplex c V hD hDt (fun v hv ↦ (hball hv).2) ha hb hsV
  obtain ⟨k, fa, fb, hrep⟩ := exists_rep ω ⟨U, hU⟩
  have hrepY := formsAlgEquiv_pullbackForm f hf ω ⟨U, hU⟩ ⟨V, hV⟩ e fa fb hrep
  have hgsU : ∀ t, (g.hom.comp s) t ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) U :=
    fun t ↦ realize_mem_chart f hf e (hsV t)
  have hev : ∀ (h : Γ(X, U)) (t : ℝ),
      ComplexPoints.eval U h (simplexPath U (g.hom.comp s) hgsU t) =
        ComplexPoints.eval V (f.appLE U V e h) (simplexPath V s hsV t) :=
    fun h t ↦ (eval_appLE f hf e h _ (hsV _) _).symm
  have hCX : IsC1Path (simplexPath U (g.hom.comp s) hgsU) := fun h ↦ by
    simp only [hev]
    exact hC _
  rw [Pi.sub_apply, cochainPullback_apply, hφi ⟨U, hU⟩ k fa fb hrep _ hgsU hCX,
    hφi' ⟨V, hV⟩ k (fun j ↦ f.appLE U V e (fa j)) (fun j ↦ f.appLE U V e (fb j)) hrepY s hsV hC,
    sub_eq_zero]
  simp only [lineInt, hev]

/-- A class of degree `i` is a class of every degree `j = i`. -/
private theorem exists_inclH_eq_of_eq {i j : ℕ} (h : i = j)
    (x : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) i) :
    ∃ y : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) j, inclH X i x = inclH X j y := by
  subst h
  exact ⟨x, rfl⟩

/-- `a ∪ b ∪ c₁(L)^{n-1}` is homogeneous of degree `2n`. -/
private theorem exists_inclH_eq_mul_mul_pow (hn : 1 ≤ n)
    (a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ y : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * n),
      inclH X 1 a * inclH X 1 b * chernH L ^ (n - 1) = inclH X (2 * n) y := by
  rw [DirectSum.of_mul_of, DirectSum.ofPow, DirectSum.of_mul_of]
  exact exists_inclH_eq_of_eq (by simp only [smul_eq_mul]; omega) _

/-- `c₁(L)ⁿ` is homogeneous of degree `2n`. -/
private theorem exists_inclH_eq_pow (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ y : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * n),
      chernH L ^ n = inclH X (2 * n) y := by
  rw [DirectSum.ofPow]
  exact exists_inclH_eq_of_eq (by rw [smul_eq_mul, mul_comm]) _

/-- A smooth projective variety carries an ample invertible module. -/
private theorem exists_isAmple :
    ∃ (L : X.Modules) (hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      haveI := hL; MMP.Intersection.IsAmple ℂ L := by
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    (t := X ↘ Spec (.of ℂ)) inferInstance
  have : Stacks.Ample.IsInvertibleModule X H := hH
  exact ⟨H, hH, MMP.Intersection.isAmple_of_stacksIsAmple ℂ H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X H).2 hHa)⟩

/-- **Changes of coefficients factoring through an additive map.** If `g = r ∘ f` for ring
homomorphisms `f : R → S`, `g : R → T` and an additive `r : S → T`, then `f_* x = 0` implies
`g_* x = 0`: `r` carries a cochain bounding `f ∘ φ` to one bounding `g ∘ φ`. -/
private theorem mapCoeff_eq_zero_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (r : S →+ T) (hr : ∀ a, r (f a) = g a) {Y : TopCat.{0}} {k : ℕ}
    (x : singularCohomology R Y k) (h : singularCohomology.mapCoeff f k x = 0) :
    singularCohomology.mapCoeff g k x = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq k x
  rw [singularCohomology.mapCoeff_ofCocycle, ofCocycle_eq_zero_iff] at h ⊢
  cases k with
  | zero =>
    change _ ∈ (⊥ : Submodule S _) at h
    change _ ∈ (⊥ : Submodule T _)
    rw [Submodule.mem_bot] at h ⊢
    funext σ
    have := congrFun h σ
    simp only [singularCohomology.cochainMap_apply, Pi.zero_apply] at this ⊢
    rw [← hr, this, map_zero]
  | succ k =>
    obtain ⟨χ, hχ, he⟩ := h
    refine ⟨r ∘ χ, fun σ hσ ↦ by simp [hχ σ hσ], ?_⟩
    funext σ
    have := congrFun he σ
    simp only [singularCohomology.cochainMap_apply, coboundary_apply] at this ⊢
    rw [← hr, ← this, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases neg_one_pow_eq_or ℤ (i : ℕ) with h1 | h1
    · have e1 : ((-1 : S) ^ (i : ℕ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → S) h1
      have e2 : ((-1 : T) ^ (i : ℕ)) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → T) h1
      simp [e1, e2]
    · have e1 : ((-1 : S) ^ (i : ℕ)) = -1 := by exact_mod_cast congrArg (Int.cast : ℤ → S) h1
      have e2 : ((-1 : T) ^ (i : ℕ)) = -1 := by exact_mod_cast congrArg (Int.cast : ℤ → T) h1
      simp [e1, e2]

/-- A smooth projective variety of dimension one is a curve. -/
private theorem isCurve_of_eq_one (h1 : n = 1) : IsCurve ℂ (X ↘ Spec (.of ℂ)) := by
  subst h1
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  exact (isCurve_iff ℂ _).2 ⟨hV, by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 1⟩

/-- **An ample class on a curve with nonzero rational Chern class.** On a smooth projective
curve there is an ample invertible module `L` with `c₁(L) ≠ 0` in `H²(X^an; ℚ)`: its degree is
positive. -/
private theorem exists_isAmple_mapCoeff_ne_zero (h1 : n = 1) :
    ∃ (L : X.Modules) (hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      haveI := hL; MMP.Intersection.IsAmple ℂ L ∧
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) ≠ 0 := by
  haveI := isProper_structureMorphism (X := X)
  haveI := isCurve_of_eq_one (X := X) h1
  have hdim1 : topologicalKrullDim X = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := ℂ) (X ↘ Spec (.of ℂ))
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    (t := X ↘ Spec (.of ℂ)) inferInstance
  have hpos :=
    invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (X ↘ Spec (.of ℂ)) hdim1.le H hHa
  have : Stacks.Ample.IsInvertibleModule X H := hH
  refine ⟨H, hH, MMP.Intersection.isAmple_of_stacksIsAmple ℂ H
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X H).2 hHa), fun h0 ↦ ?_⟩
  haveI : IsComplexScheme X :=
    MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  have hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  exact hpos.ne' (MMP.Fourfold.invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero
    (by haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
        exact MMP.Flips.isSmoothScheme_of_smooth _) hdim1
    inferInstance H h0)

/-- A class over `ℤ` which is nonzero rationally is nonzero over `ℂ`: a `ℚ`-linear retraction
`ℂ → ℚ` carries a cochain bounding its complex image to one bounding its rational image. -/
private theorem mapCoeff_complex_ne_zero {Y : TopCat.{0}} {k : ℕ} {x : singularCohomology ℤ Y k}
    (h : singularCohomology.mapCoeff (Int.castRingHom ℚ) k x ≠ 0) :
    singularCohomology.mapCoeff (Int.castRingHom ℂ) k x ≠ 0 := fun h0 ↦ by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.2 fun a b h ↦ (algebraMap ℚ ℂ).injective h)
  exact h (mapCoeff_eq_zero_of_comp (Int.castRingHom ℂ) (Int.castRingHom ℚ) g.toAddMonoidHom
    (fun a ↦ by simpa using LinearMap.congr_fun hg (a : ℚ)) x h0)

/-- Change of coefficients along a composite of ring maps is the composite. -/
private theorem mapCoeff_mapCoeff {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) {Y : TopCat.{0}} {k : ℕ} (x : singularCohomology R Y k) :
    singularCohomology.mapCoeff g k (singularCohomology.mapCoeff f k x) =
      singularCohomology.mapCoeff (g.comp f) k x := by
  obtain ⟨φ, hφ, rfl⟩ := cohomologyWithSupports.exists_ofCocycle_eq k x
  rw [singularCohomology.mapCoeff_ofCocycle, singularCohomology.mapCoeff_ofCocycle,
    singularCohomology.mapCoeff_ofCocycle]
  exact cohomologyWithSupports.ofCocycle_congr
    (by ext σ; simp [singularCohomology.cochainMap_apply]) _ _

/-- **Ample classes on a curve lie on one ray.** On a smooth projective curve the first Chern
classes of two ample invertible modules are positive rational multiples of one another in
`H²(X^an; ℂ)`: in the line `H²(X^an; ℚ)` the degree formula `c₁(N) ∩ [X] = deg N · [pt]` gives
`deg L₀ · c₁(L) = deg L · c₁(L₀)`, and ample modules have positive degree. -/
private theorem exists_pos_rat_smul_chern_curve (h1 : n = 1) (L₀ L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₀]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL₀ : MMP.Intersection.IsAmple ℂ L₀) (hL : MMP.Intersection.IsAmple ℂ L) :
    ∃ q : ℚ, 0 < q ∧
      singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) =
        (q : ℂ) • singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (algebraicFirstChernClass L₀) := by
  subst h1
  haveI := isProper_structureMorphism (X := X)
  haveI := isCurve_of_eq_one (X := X) rfl
  have hdim1 : topologicalKrullDim X = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := ℂ) (X ↘ Spec (.of ℂ))
  haveI : IsComplexScheme X :=
    MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  have hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  have hsm := MMP.Flips.isSmoothScheme_of_smooth (X ↘ Spec (.of ℂ))
  -- ample modules have positive degree
  have hdeg : ∀ (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N],
      MMP.Intersection.IsAmple ℂ N →
        0 < invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le N := by
    intro N _ hN
    have : Stacks.Ample.IsInvertibleModule X N := ‹_›
    exact invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (X ↘ Spec (.of ℂ)) hdim1.le N
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X N).1 (MMP.Intersection.IsAmple.stacksIsAmple hN))
  -- capping with `[X]` and pushing to the point
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (genericPoint X) = ((1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ (by rw [hdim1]; rfl)
  let p0 : Spec (.of ℂ) := Classical.choice inferInstance
  let Ψ := fun c : analyticSingularCohomology ℚ (X ↘ Spec (.of ℂ)) 2 ↦
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (X ↘ Spec (.of ℂ))))
      (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * 0 : ℕ)).hom
      (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ X))
        (by norm_num : ((2 * 1 : ℕ) : ℤ) - 2 = ((2 * 0 : ℕ) : ℤ))
        (borelMooreHomology.capProductPullback ℚ
          (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
            TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
          Set.univ 2 ((2 * 1 : ℕ) : ℤ) c
          (Chow.pointCycleClass ℚ (genericPoint X) hξ)))
  have hΨ : ∀ (q : ℚ) c, Ψ (q • c) = q • Ψ c := fun q c ↦ by
    simp only [Ψ, LinearMap.map_smul₂, map_smul, LinearMap.smul_apply]
  have hΨc : ∀ (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N],
      Ψ (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N)) =
        (invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le N : ℚ) •
          Chow.pointCycleClass ℚ p0 (MMP.Fourfold.relativeDimension_spec_eq_zero p0) :=
    fun N _ ↦ MMP.Fourfold.pushforward_capProductPullback_eq_invertibleCurveDegree_smul hsm hdim1
      inferInstance N (genericPoint X) hξ p0
  -- the class of the point is torsion free
  have hpt : ∀ r : ℚ, r • Chow.pointCycleClass ℚ p0
      (MMP.Fourfold.relativeDimension_spec_eq_zero p0) = 0 → r = 0 :=
    fun _ hr ↦ MMP.Fourfold.eq_zero_of_smul_pointCycleClass_spec_eq_zero p0 hr
  have hd₀ : (0 : ℚ) < invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L₀ := by
    exact_mod_cast hdeg L₀ hL₀
  have hd : (0 : ℚ) < invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L := by
    exact_mod_cast hdeg L hL
  -- `c₁(L₀) ≠ 0` in the line `H²(X^an; ℚ)`
  have hc₀ : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L₀) ≠ 0 := by
    intro h0
    have h := hΨc L₀
    rw [h0] at h
    simp only [Ψ, LinearMap.map_zero₂, LinearMap.zero_apply, map_zero] at h
    exact hd₀.ne' (hpt _ h.symm)
  haveI := finiteDimensional_analyticSingularCohomology (X := X) ℚ (2 * 1)
  obtain ⟨q, hq⟩ := exists_smul_eq_of_finrank_le_one
    (finrank_analyticSingularCohomology_two_mul_le_one (n := 1) (X := X) ℚ) hc₀
    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
  have e1 := hΨc L
  rw [← hq, hΨ, hΨc L₀, smul_smul] at e1
  have h3 := hpt (q * invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L₀ -
    invertibleCurveDegree ℂ (X ↘ Spec (.of ℂ)) hdim1.le L) (by rw [sub_smul, e1, sub_self])
  refine ⟨q, by nlinarith, ?_⟩
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  have h4 := congrArg (singularCohomology.mapCoeff (algebraMap ℚ ℂ) 2) hq
  rw [map_smulₛₗ, mapCoeff_mapCoeff, mapCoeff_mapCoeff, hcomp, eq_ratCast] at h4
  exact h4.symm

omit [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] in
/-- `X^an` is compact: it is homeomorphic to `X(ℂ)`, which is compact since `X` is proper. -/
private theorem compactSpace_complexPoints :
    CompactSpace (ComplexPoints (X ↘ Spec (.of ℂ))) := by
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  haveI : IsComplexScheme X :=
    MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  have e := MMP.specOverSpec_over_self (K := ℂ)
  haveI : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) := ⟨by rw [e, Category.comp_id]⟩
  have hsub : Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) := ⟨fun p q ↦ UnderlyingSpace.ext (by
    have h1 := p.toHom_comp_over
    have h2 := q.toHom_comp_over
    rw [e, Category.comp_id] at h1 h2
    rw [h1, h2])⟩
  have hp := UnderlyingSpace.isProperMap_map (K := ℂ) (X ↘ Spec (.of ℂ))
  haveI : CompactSpace (UnderlyingSpace ℂ X) := by
    refine ⟨?_⟩
    have := hp.isCompact_preimage (Set.subsingleton_of_subsingleton (s := Set.univ)).isCompact
    simpa using this
  exact ComplexPoints.homeomorphUnderlyingSpace.symm.compactSpace

/-- **A holomorphic class which is antiholomorphic has locally constant primitives.** If
`[ω] = \overline{[η]}`, the cocycles of local primitives `F` of `ω` and `G` of `η` satisfy
`φ - \overline{ψ} = δh`, so near every point `h = F - \overline{G} + const`. Its real part
`Re (F - G) + const` and its imaginary part `Re (-i (F + G)) + const` are then constant on the
compact connected `X^an` by the maximum principle, so `F ± G`, and hence `F`, have derivative
zero. -/
private theorem forall_exists_isChartPrimitive_fderiv_eq_zero (hn : n = 1 ∨ n = 2)
    {ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (ha : IsDR X ω a)
    (hb : IsDR X η b) (hab : a = conjH X b) (x : ComplexPoints (X ↘ Spec (.of ℂ))) :
    ∃ (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (D : Set (Fin n → ℂ))
      (Φ : (Fin n → ℂ) → ℂ), x ∈ c.toOpenPartialHomeomorph.source ∧
      c.toOpenPartialHomeomorph x ∈ D ∧ IsOpen D ∧ IsChartPrimitive ω c D Φ ∧
      ∀ z ∈ D, HasFDerivAt Φ (0 : (Fin n → ℂ) →L[ℝ] ℂ) z := by
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨-, -, hcl⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  have hd := (hcl X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).2
  choose c D Φ₁ Φ₂ hxs hxD hDo hDc hDt hΦ₁ hΦ₂ hP₁ hP₂ hcp using
    fun y ↦ exists_chartPrimitive_pair (n := n) ω η (hd ω) (hd η) y
  let E : ComplexPoints (X ↘ Spec (.of ℂ)) → OpenPartialHomeomorph _ (Fin n → ℂ) :=
    fun y ↦ (c y).toOpenPartialHomeomorph
  let B : ComplexPoints (X ↘ Spec (.of ℂ)) → Set (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    fun y ↦ (E y).source ∩ E y ⁻¹' D y
  have hBo : ∀ y, IsOpen (B y) := fun y ↦ (E y).isOpen_inter_preimage (hDo y)
  have hBm : ∀ y, y ∈ B y := fun y ↦ ⟨hxs y, hxD y⟩
  have hsymmB : ∀ y, ∀ w ∈ D y, (E y).symm w ∈ B y := fun y w hw ↦
    ⟨(E y).map_target (hDt y hw), by
      change E y ((E y).symm w) ∈ D y
      rwa [(E y).right_inv (hDt y hw)]⟩
  obtain ⟨φ, hφ, hφDR, hφv⟩ := isDR_of_isLocalPrimitive (n := n) ω B
    (fun y w ↦ Φ₁ y (E y w)) hBo hBm hP₁
  obtain ⟨ψ, hψ, hψDR, hψv⟩ := isDR_of_isLocalPrimitive (n := n) η B
    (fun y w ↦ Φ₂ y (E y w)) hBo hBm hP₂
  rw [IsDR.unique hn ha hφDR, IsDR.unique hn hb hψDR, singularCohomology.mapCoeff_ofCocycle,
    ← sub_eq_zero, ← ofCocycle_sub, ofCocycle_eq_zero_iff] at hab
  obtain ⟨χ, -, hχ⟩ := hab
  -- the function `h` on points
  let H : ComplexPoints (X ↘ Spec (.of ℂ)) → ℂ := fun y ↦ χ (ContinuousMap.const _ y)
  have hconst : ∀ (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1) (i : Fin 2),
      σ.comp (face 0 i) = ContinuousMap.const _ (σ (stdSimplex.vertex (i.succAbove 0))) := by
    intro σ i
    refine ContinuousMap.ext fun t ↦ ?_
    have ht : t = stdSimplex.vertex 0 := by
      apply Subtype.ext
      funext j
      have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
      subst hj
      have h1 := t.2.2
      rw [Fin.sum_univ_one] at h1
      first
      | (rw [h1]; simp [stdSimplex.vertex])
      | (rw [h1]; simp [stdSimplex.vertex_coe])
      | (rw [h1]; rfl)
      | simp_all [stdSimplex.vertex]
    show σ (face 0 i t) = σ _
    rw [ht]
    exact congrArg σ (stdSimplex.map_vertex _ _)
  have hrel : ∀ (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) 1) (y : _),
      Set.range σ ⊆ B y →
        H (σ (stdSimplex.vertex 1)) - H (σ (stdSimplex.vertex 0)) =
          (Φ₁ y (E y (σ (stdSimplex.vertex 1))) - Φ₁ y (E y (σ (stdSimplex.vertex 0)))) -
            starRingEnd ℂ (Φ₂ y (E y (σ (stdSimplex.vertex 1))) -
              Φ₂ y (E y (σ (stdSimplex.vertex 0)))) := by
    intro σ y hσ
    have h := congrFun hχ σ
    rw [← hφv σ y hσ, ← hψv σ y hσ]
    have hc : (singularCohomology.cochainMap (starRingEnd ℂ) 1) ψ σ = starRingEnd ℂ (ψ σ) :=
      rfl
    simp only [Pi.sub_apply, coboundary_apply, Fin.sum_univ_two, hconst, hc] at h
    simpa [H, sub_eq_add_neg] using h
  -- `H = F - conj G + const` on each ball
  have hloc : ∀ y, ∀ w ∈ B y, H w = H y + ((Φ₁ y (E y w) - starRingEnd ℂ (Φ₂ y (E y w))) -
      (Φ₁ y (E y y) - starRingEnd ℂ (Φ₂ y (E y y)))) := by
    intro y w hw
    let σ := segSimplex (Y := Analytification.space (X ↘ Spec (.of ℂ))) (E y) (hDc y) (hDt y)
      (hxD y) hw.2
    have hσ : Set.range σ ⊆ B y := by
      rintro _ ⟨s, rfl⟩
      have hm := segment_mem (hDc y) (hxD y) hw.2 (stdSimplex_apply_nonneg s 1)
        (by linarith [stdSimplex_apply_nonneg s 0, stdSimplex_two_add s])
      exact hsymmB y _ hm
    have e1 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 = 1 := by
      simp [stdSimplex.vertex_coe]
    have e0 : (stdSimplex.vertex (S := ℝ) (0 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 = 0 := by
      simp [stdSimplex.vertex_coe]
    have hv1 : σ (stdSimplex.vertex 1) = w := by
      simp only [σ, segSimplex, ContinuousMap.coe_mk, e1, sub_self, zero_smul, one_smul,
        zero_add]
      exact (E y).left_inv hw.1
    have hv0 : σ (stdSimplex.vertex 0) = y := by
      simp only [σ, segSimplex, ContinuousMap.coe_mk, e0, sub_zero, one_smul, zero_smul,
        add_zero]
      exact (E y).left_inv (hxs y)
    have := hrel σ y hσ
    rw [hv1, hv0, map_sub] at this
    linear_combination this
  haveI := compactSpace_complexPoints (X := X)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI : ConnectedSpace (ComplexPoints (X ↘ Spec (.of ℂ))) :=
    MMP.Fourfold.connectedSpace_analyticSpace (X ↘ Spec (.of ℂ))
  -- the real and imaginary parts are constant
  have hre := eq_of_forall_locally_re (fun w ↦ (H w).re) fun y ↦
    ⟨E y, D y, fun z ↦ Φ₁ y z - Φ₂ y z,
      (H y).re - (Φ₁ y (E y y) - Φ₂ y (E y y)).re, hxs y, hxD y, hDo y, (hΦ₁ y).sub (hΦ₂ y),
      fun w hw ↦ by rw [hloc y w hw]; simp; ring⟩
  have him := eq_of_forall_locally_re (fun w ↦ (H w).im) fun y ↦
    ⟨E y, D y, fun z ↦ -Complex.I * (Φ₁ y z + Φ₂ y z),
      (H y).im - (-Complex.I * (Φ₁ y (E y y) + Φ₂ y (E y y))).re, hxs y, hxD y, hDo y,
      ((hΦ₁ y).add (hΦ₂ y)).const_mul _,
      fun w hw ↦ by rw [hloc y w hw]; simp; ring⟩
  refine ⟨c x, D x, Φ₁ x, hxs x, hxD x, hDo x, hcp x, fun z hz ↦ ?_⟩
  -- on `D x`, the real parts of `Φ₁ - Φ₂` and `-i (Φ₁ + Φ₂)` are constant
  have hval : ∀ w ∈ D x, H ((E x).symm w) = H x + ((Φ₁ x w - starRingEnd ℂ (Φ₂ x w)) -
      (Φ₁ x (E x x) - starRingEnd ℂ (Φ₂ x (E x x)))) := fun w hw ↦ by
    rw [hloc x _ (hsymmB x w hw), (E x).right_inv (hDt x hw)]
  have hdz₁ := (hΦ₁ x z hz).differentiableAt ((hDo x).mem_nhds hz)
  have hdz₂ := (hΦ₂ x z hz).differentiableAt ((hDo x).mem_nhds hz)
  have e₁ := fderiv_eq_zero_of_eventually_re_eq (Ψ := fun z ↦ Φ₁ x z - Φ₂ x z) (hdz₁.sub hdz₂)
    (by
      filter_upwards [(hDo x).mem_nhds hz] with w hw
      have h1 := hre ((E x).symm w) ((E x).symm z)
      simp only [hval w hw, hval z hz] at h1
      simp only [Complex.add_re, Complex.sub_re, Complex.conj_re] at h1 ⊢
      linarith)
  have e₂ := fderiv_eq_zero_of_eventually_re_eq
    (Ψ := fun z ↦ -Complex.I * (Φ₁ x z + Φ₂ x z)) ((hdz₁.add hdz₂).const_mul _)
    (by
      filter_upwards [(hDo x).mem_nhds hz] with w hw
      have h1 := him ((E x).symm w) ((E x).symm z)
      simp only [hval w hw, hval z hz] at h1
      simp only [Complex.add_im, Complex.sub_im, Complex.conj_im, Complex.mul_re,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.add_re] at h1 ⊢
      linarith)
  rw [fderiv_fun_sub hdz₁ hdz₂] at e₁
  rw [((hdz₁.hasFDerivAt.fun_add hdz₂.hasFDerivAt).const_mul (-Complex.I)).fderiv] at e₂
  have h0 : fderiv ℂ (Φ₁ x) z = 0 := by
    have e₃ : fderiv ℂ (Φ₁ x) z + fderiv ℂ (Φ₂ x) z = 0 :=
      (smul_eq_zero.1 e₂).resolve_left (neg_ne_zero.2 Complex.I_ne_zero)
    rw [sub_eq_zero] at e₁
    rw [← e₁, ← two_smul ℂ] at e₃
    exact (smul_eq_zero.1 e₃).resolve_left two_ne_zero
  have := hdz₁.hasFDerivAt.restrictScalars ℝ
  rw [h0] at this
  simpa using this

/-- **A holomorphic class which is also antiholomorphic comes from the zero form**, by the
maximum principle (`forall_exists_isChartPrimitive_fderiv_eq_zero`) and
`eq_zero_of_forall_isChartPrimitive`. -/
private theorem eq_zero_of_isDR_of_eq_conjH_form (hn : n = 1 ∨ n = 2)
    {ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (ha : IsDR X ω a)
    (hb : IsDR X η b) (hab : a = conjH X b) :
    ω = 0 :=
  eq_zero_of_forall_isChartPrimitive
    (fun x ↦ forall_exists_isChartPrimitive_fderiv_eq_zero hn ha hb hab x)

/-! ### The integral over a surface, through a curve slice -/

section SliceBertini

open MMP.Threefold.Bridges

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- A dense open of the coefficient space `𝔸ᴺ⁺¹_k` over an infinite field contains a `k`-point
`c` at which a given nonzero polynomial does not vanish. -/
private theorem exists_coefficientPoint_mem_and_eval_ne_zero {k : Type} [Field k] [Infinite k]
    {N : ℕ} (U : (coefficientSpace k N).Opens) (hU : Dense (U : Set (coefficientSpace k N)))
    {g : MvPolynomial (Fin (N + 1)) k} (hg : g ≠ 0) :
    ∃ c : Fin (N + 1) → k, coefficientPoint c ∈ U ∧ MvPolynomial.eval c g ≠ 0 := by
  haveI : Nonempty (coefficientSpace k N) := ⟨coefficientPoint 0⟩
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.2
  have hf : f ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (Submodule.zero_mem _)
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (f * g) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hf hg (MvPolynomial.funext fun c => by simpa using h c)
  rw [map_mul] at hc
  refine ⟨c, hfU ?_, right_ne_zero_of_mul hc⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => left_ne_zero_of_mul hc h

/-- For a nonzero `k`-linear map `φ` out of `kᴺ⁺¹` there is a nonzero polynomial (a linear form
vanishing on the kernel of `φ`) whose non-vanishing forces `φ c ≠ 0`. -/
private theorem exists_polynomial_ne_zero_of_linearMap_ne_zero {k : Type} [Field k] {N : ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] (φ : (Fin (N + 1) → k) →ₗ[k] M) (hφ : φ ≠ 0) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → φ c ≠ 0 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, φ c₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  obtain ⟨ψ, hψc, hψK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := LinearMap.ker φ) (x := c₀) (by simpa using hc₀) inferInstance
  set ℓ : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (ψ (Pi.single j 1)) * MvPolynomial.X j
  have hev : ∀ c, MvPolynomial.eval c ℓ = ψ c := by
    intro c
    conv_rhs => rw [pi_eq_sum_univ c]
    simp only [ℓ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨ℓ, fun h => hψc (by rw [← hev, h, map_zero]), fun c hc hφc => hc ?_⟩
  rw [hev]
  have : ψ c ∈ (LinearMap.ker φ).map ψ := ⟨c, hφc, rfl⟩
  rw [hψK] at this
  exact this

/-- **A smooth integral member of a large power of an ample line bundle on a surface.** -/
private theorem exists_integral_smooth_zeroScheme (h2 : n = 2) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (m₀ : ℕ) :
    ∃ m : ℕ, m₀ < m ∧ ∃ s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤), s ≠ 0 ∧
      IsIntegral (@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subscheme ∧
      Smooth ((@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι ≫
          (X ↘ Spec (.of ℂ))) := by
  classical
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : IsProper (X ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := X)
  haveI hvar : IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hvar.toIsIntegral
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  obtain ⟨N, -, F, c, hN1, hdvd, -, -, hcov⟩ :=
    Stacks.SectionExtension.exists_common_degree_affine_cover L hL (n := m₀ + 1) (by omega) 0
  have hNm : m₀ < N := by
    obtain ⟨t, rfl⟩ := hdvd
    rcases t with _ | t
    · omega
    · nlinarith
  choose σ hσ using fun i => Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L N (c i)
  let E := Fintype.equivFin {y : X // y ∈ F}
  haveI : Stacks.Ample.IsInvertibleModule X (Stacks.Ample.tensorPowModule X L (N : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L N
  let s : Fin (Fintype.card {y : X // y ∈ F} + 1) →
      Γ(Stacks.Ample.tensorPowModule X L (N : ℤ), ⊤) :=
    Fin.cons 0 fun j => σ (E.symm j)
  have hsingle : ∀ i, systemSection (k := ℂ) s (Pi.single (E i).succ 1) = σ i := fun i => by
    simp [systemSection, Fintype.linearCombination_apply_single, s]
  have hloc : ∀ x : X, ∃ i, x ∈ Stacks.Ample.nonvanishingLocus _ (σ i) := by
    intro x
    have hx : x ∈ (⨆ i, Stacks.AmpleFiniteAvoidance.nvOpen L (c i)) := hcov trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    rw [hσ i, ← Stacks.AmpleFiniteAvoidance.coe_nvOpen]
    exact hi
  have hs : ⨆ c : Fin (Fintype.card {y : X // y ∈ F} + 1) → ℂ,
      Stacks.NonvanishingOpen.nonvanishingOpen X _ (systemSection s c) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨i, hi⟩ := hloc x
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (E i).succ 1, ?_⟩
    rwa [Stacks.NonvanishingOpen.mem_nonvanishingOpen, hsingle]
  have hφ : systemSection (k := ℂ) s ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hloc (Classical.arbitrary X)
    rwa [← hsingle i, h0, LinearMap.zero_apply, Stacks.Ample.nonvanishingLocus_zero] at hi
  have hLN : Stacks.Ample.IsAmple X (Stacks.Ample.tensorPowModule X L (N : ℤ)) :=
    Stacks.AmplePowers.isAmple_tensorPowModule_of_isAmple L N hN1 hL
  have hdim := MMP.Mori.two_le_topologicalKrullDim_range_morphismOfGeneratingSections (k := ℂ)
    hLN s hs (by rw [hdimX]; exact_mod_cast le_rfl)
  let ιY : (i : PEmpty.{1}) → (i.elim : Scheme.{0}) ⟶ X := fun i => i.elim
  haveI : ∀ i, IsImmersion (ιY i) := fun i => i.elim
  haveI : ∀ i, Smooth (ιY i ≫ X ↘ Spec (.of ℂ)) := fun i => i.elim
  obtain ⟨⟨U₁, hU₁d, hU₁⟩, -⟩ := exists_dense_open_smooth_zeroScheme s hs ιY
  obtain ⟨⟨U₂, hU₂d, hU₂⟩, -⟩ := exists_dense_open_geometricallyIntegral_zeroScheme s hs hdim
  have hUd : Dense (((U₁ ⊓ U₂ : (coefficientSpace ℂ (Fintype.card {y : X // y ∈ F})).Opens)) :
      Set (coefficientSpace ℂ (Fintype.card {y : X // y ∈ F}))) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact hU₁d.inter_of_isOpen_left hU₂d U₁.2
  obtain ⟨ℓ, hℓ, hℓφ⟩ := exists_polynomial_ne_zero_of_linearMap_ne_zero _ hφ
  obtain ⟨c', hcU, hc⟩ := exists_coefficientPoint_mem_and_eval_ne_zero _ hUd hℓ
  exact ⟨N, hNm, systemSection s c', hℓφ c' hc, (hU₂ c' hcU.2).2,
    (hU₁ c' hcU.1).1 inferInstance⟩

end SliceBertini

section SliceForms

open scoped MMP.SubschemeOver

/-- An isomorphism transports the vanishing of global sections. -/
private theorem subsingleton_sections_of_iso {Y : Scheme.{0}} {F G : Y.Modules} (e : F ≅ G)
    [Subsingleton Γ(G, ⊤)] : Subsingleton Γ(F, ⊤) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ x : Γ(F, ⊤), (e.hom ≫ e.inv).val.app (op ⊤) x = x := fun x => by
    rw [e.hom_inv_id]; rfl
  rw [← h a, ← h b]
  haveI : Subsingleton (G.val.obj (op ⊤)) := ‹Subsingleton Γ(G, ⊤)›
  exact congrArg (e.inv.val.app (op ⊤)) (Subsingleton.elim _ _)

/-- `ℰ ≅ (ℰ ⊗ L^{⊗ -m}) ⊗ L^{⊗ m}`. -/
private noncomputable def twistIso {Y : Scheme.{0}} (ℰ L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] (m : ℤ) :
    ℰ ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj ℰ (Stacks.Ample.tensorPowModule Y L (-m)))
      (Stacks.Ample.tensorPowModule Y L m) :=
  (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) ℰ).symm ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl ℰ)
      (Stacks.Ample.tensorPowModuleAddIso Y L (-m) m ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr Y L (neg_add_cancel m) ≪≫
        Stacks.Ample.tensorPowModuleZeroIso Y L).symm ≪≫
    (Stacks.TensorSheafSpellingIso.tensorModulesAssociator Y _ _ _).symm

/-- The zero scheme of a nonzero section of an invertible module on a smooth projective surface,
when integral, is a curve. -/
private theorem topologicalKrullDim_zeroScheme_eq_one (h2 : n = 2) (M : X.Modules)
    [hMinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] (s : Γ(M, ⊤))
    (hs0 : s ≠ 0) [hint : IsIntegral (AlgebraicGeometry.zeroScheme X M s).subscheme] :
    topologicalKrullDim (AlgebraicGeometry.zeroScheme X M s).subscheme = 1 := by
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI hVX : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hVX.toIsIntegral
  haveI : IsComplexScheme X := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  haveI : IsNormal X := isNormal_of_smooth_over_field (X ↘ Spec (.of ℂ))
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  let Z := AlgebraicGeometry.zeroScheme X M s
  have ht : (Stacks.SheafOfModules.sectionsOfTop M s).eval (Opposite.op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hreg := isRegularSection_of_eval_top_ne_zero M (Stacks.SheafOfModules.sectionsOfTop M s)
    (by rwa [ht])
  have hZ := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X M _).2 hreg
  rw [ht] at hZ
  let P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofEffectiveCartier Z hZ
  have hV : integralComponentAt P.genericPoint = Z :=
    integralComponentAt_subschemeι_genericPoint Z
  have hcoh : Order.coheight P.genericPoint = 1 := by
    rw [← Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
    exact P.codimension_one
  have h := MMP.height_add_coheight_eq_krullDim ℂ P.genericPoint
  rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at h
  change _ = topologicalKrullDim X at h
  rw [hdimX, hcoh] at h
  show topologicalKrullDim Z.subscheme = _
  rw [Z.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    Scheme.IdealSheafData.range_subschemeι, ← hV, Stacks.Chow.coe_support_integralComponentAt,
    AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_height]
  generalize Order.height P.genericPoint = a at h ⊢
  induction a using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe a =>
    have h' : (((a + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rwa [Nat.cast_add, Nat.cast_one]
    have ha := Nat.cast_injective (R := ℕ∞) (WithBot.coe_injective h')
    obtain rfl : a = 1 := by omega
    rfl

/-- **The conormal sequence of a smooth zero scheme.** Let `Z = Z(s)` be the zero scheme of a
nonzero section `s` of `L^{⊗ m}`, smooth over `ℂ`, with `Γ(Z, (L^{⊗ -m})|_Z) = 0`. If a global
one-form `ω` pulls back to zero on `Z`, its restriction to `Z` as a section of `Ω_X|_Z` vanishes:
the kernel of `Ω_X|_Z ⟶ Ω_Z` is the conormal sheaf `I/I² ≅ (L^{⊗ -m})|_Z`. -/
private theorem unit_app_eq_zero_of_pullbackForm_eq_zero (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (m : ℕ)
    (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)) (hs0 : s ≠ 0)
    (hsm : Smooth ((@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι ≫
          (X ↘ Spec (.of ℂ))))
    (hcon : Subsingleton Γ((Scheme.Modules.pullback (@AlgebraicGeometry.zeroScheme X
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι).obj
          (Stacks.Ample.tensorPowModule X L (-(m : ℤ))), ⊤))
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
    (h : pullbackForm (@AlgebraicGeometry.zeroScheme X
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι rfl ω = 0) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (@AlgebraicGeometry.zeroScheme X
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι).unit.app
          ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ))).val.app (op ⊤) ω = 0 := by
  haveI hVX : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hVX.toIsIntegral
  letI hMinv := Stacks.Ample.isInvertibleModule_tensorPowModule X L m
  haveI : Stacks.Ample.IsInvertibleModule X (Stacks.Ample.tensorPowModule X L (-(m : ℤ))) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L _
  -- `L^{⊗ -m} ≅ (L^{⊗ m})^∨`
  let eN : Stacks.Ample.tensorPowModule X L (-(m : ℤ)) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
    Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _
      (Stacks.Ample.tensorPowModuleAddIso X L (m : ℤ) (-(m : ℤ)) ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr X L (add_neg_cancel (m : ℤ)) ≪≫
        Stacks.Ample.tensorPowModuleZeroIso X L)
  have hC := MMP.DeRham.subsingleton_conormal_sections_zeroScheme (X ↘ Spec (.of ℂ))
    (Stacks.Ample.tensorPowModule X L (m : ℤ)) s hs0 _ eN hcon
  exact MMP.DeRham.unit_app_eq_zero_of_deRhamFormsPushforwardSections_eq_zero
    (X ↘ Spec (.of ℂ)) _ _ rfl _ hsm hC ω h

/-- **A one-form survives on every smooth integral member of a large power of an ample line
bundle on a surface.** -/
private theorem exists_pullbackForm_ne_zero (h2 : n = 2) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → 0 < m → ∀ s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤),
      s ≠ 0 →
      IsIntegral (@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subscheme →
      Smooth ((@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι ≫
          (X ↘ Spec (.of ℂ))) →
      ω ≠ 0 → pullbackForm (@AlgebraicGeometry.zeroScheme X
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι rfl ω ≠ 0 := by
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : IsProper (X ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := X)
  haveI hVX : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hVX.toIsIntegral
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  let ℰ := (X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)
  haveI hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0} ℰ :=
    AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms _ 1
  obtain ⟨m₀, hm₀⟩ := MMP.Mori.exists_subsingleton_sections_tensor_tensorPowModule_neg
    (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _) 2 hdimX (by norm_num) ℰ L hL
  refine ⟨m₀, fun m hm hm0 s hs0 hint hsm hω h0 => hω ?_⟩
  haveI hNinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Ample.tensorPowModule X L (m : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L m
  haveI hM : Stacks.Ample.IsInvertibleModule X (Stacks.Ample.tensorPowModule X L (-(m : ℤ))) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L _
  have hMf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (Stacks.Ample.tensorPowModule X L (-(m : ℤ))) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  haveI hEf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{0, 0, 0}
      (Scheme.Modules.tensorObj ℰ (Stacks.Ample.tensorPowModule X L (-(m : ℤ)))) :=
    Stacks.Chow.isFiniteLocallyFree_tensor hE hMf
  haveI : Subsingleton
      Γ(Scheme.Modules.tensorObj ℰ (Stacks.Ample.tensorPowModule X L (-(m : ℤ))), ⊤) := hm₀ m hm
  let Z := AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ)) s
  haveI := hint
  -- `Γ(Z, (L^{⊗ -m})|_Z) = 0`: `L|_Z` is ample on the integral proper curve `Z`
  have hdimZ : topologicalKrullDim Z.subscheme = 1 :=
    topologicalKrullDim_zeroScheme_eq_one rfl _ s hs0
  haveI : IsProper (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) := inferInstance
  haveI hLZ : Stacks.Ample.IsInvertibleModule Z.subscheme
      ((Scheme.Modules.pullback Z.subschemeι).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback Z.subschemeι L
  have hLZa : Stacks.Ample.IsAmple Z.subscheme ((Scheme.Modules.pullback Z.subschemeι).obj L) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).2
      (Scheme.Modules.isAmple_pullback_of_isClosedImmersion Z.subschemeι L
        ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL))
  haveI := MMP.Mori.subsingleton_sections_tensorPowModule_of_isAmple_of_neg
    (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) hdimZ _ hLZa (n := -(m : ℤ)) (by omega)
  have hcon := subsingleton_sections_of_iso
    (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso
      Z.subschemeι L (-(m : ℤ)))
  exact MMP.Mori.eq_zero_of_pullback_eq_zero_of_iso (Stacks.Ample.tensorPowModule X L (m : ℤ)) s
    hs0 _ (twistIso ℰ L m) ω (unit_app_eq_zero_of_pullbackForm_eq_zero L m s hs0 hsm hcon ω h0)

end SliceForms

open scoped MMP.SubschemeOver in
/-- **A smooth ample curve on which a one-form is nonzero** (Bertini and the conormal sequence).
-/
private theorem exists_zeroScheme_slice (h2 : n = 2) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsAmple ℂ L)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ (m : ℕ) (_ : 0 < m) (s : Γ(Stacks.Ample.tensorPowModule X L (m : ℤ), ⊤)), s ≠ 0 ∧
      IsIntegral (@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subscheme ∧
      Smooth ((@AlgebraicGeometry.zeroScheme X (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι ≫
          (X ↘ Spec (.of ℂ))) ∧
      (ω ≠ 0 → pullbackForm (@AlgebraicGeometry.zeroScheme X
        (Stacks.Ample.tensorPowModule X L (m : ℤ))
        (Stacks.Ample.isInvertibleModule_tensorPowModule X L m) s).subschemeι rfl ω ≠ 0) := by
  have hLs : Stacks.Ample.IsAmple X L := hL.stacksIsAmple
  obtain ⟨m₀, hm₀⟩ := exists_pullbackForm_ne_zero h2 L hLs ω
  obtain ⟨m, hm, s, hs0, hint, hsm⟩ := exists_integral_smooth_zeroScheme h2 L hLs m₀
  exact ⟨m, by omega, s, hs0, hint, hsm, hm₀ m hm.le (by omega) s hs0 hint hsm⟩

/-- `c₁(M^{⊗ d}) = d c₁(M)` for `d ≥ 1`. -/
private theorem algebraicFirstChernClass_tensorPowModule {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M] (d : ℕ) (hd : 1 ≤ d) :
    algebraicFirstChernClass (Stacks.Ample.tensorPowModule Y M d) =
      (d : ℤ) • algebraicFirstChernClass M := by
  induction d, hd using Nat.le_induction with
  | base =>
    rw [Nat.cast_one, algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleOneIso Y M),
      one_smul]
  | succ d hd ih =>
    rw [← algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleAddIso Y M d 1 ≪≫
        Stacks.RelativeVeryAmple.tensorPowModuleCongr Y M (by push_cast; ring)),
      algebraicFirstChernClass_sheafTensor, ih,
      algebraicFirstChernClass_eq_of_iso (Stacks.Ample.tensorPowModuleOneIso Y M)]
    push_cast
    rw [add_zsmul, one_zsmul]

open scoped MMP.SubschemeOver in
/-- **A smooth ample prime divisor of a surface.** For an ample invertible module `L` on a smooth
projective surface `X` and a global one-form `ω`, there is a prime divisor `P` of `X` whose
closure is a smooth projective curve, with `𝒪_X(P)` invertible and `c₁(𝒪_X(P)) = m c₁(L)` in
`H²(X^an; ℚ)` for some `m > 0`, on which `ω` restricts to a nonzero form if it is nonzero. -/
private theorem exists_primeDivisor_slice (h2 : n = 2) [IsComplexScheme X] [IsLocallyNoetherian X]
    [IsNormal X] (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ (P : MMP.Mori.PrimeDivisor X)
      (hP : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) P.genericPoint = ((1 : ℕ) : ℤ))
      (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))) (m : ℕ),
      0 < m ∧
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
          (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X))) =
        (m : ℚ) • singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L) ∧
      IsProjectiveVariety ℂ ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) ∧
      SmoothOfRelativeDimension 1 ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) ∧
      (ω ≠ 0 → pullbackForm (integralComponentAt P.genericPoint).subschemeι rfl ω ≠ 0) := by
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : IsProper (X ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := X)
  haveI hVX : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hVX.toIsIntegral
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of ℂ))
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  obtain ⟨m, hm, s, hs0, hint, hsm, hω⟩ := exists_zeroScheme_slice (X := X) rfl L hL ω
  let M := Stacks.Ample.tensorPowModule X L (m : ℤ)
  haveI hMinv : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L m
  let Z := AlgebraicGeometry.zeroScheme X M s
  haveI := hint
  -- `Z` is an effective Cartier divisor, with `𝒪_X(Z) ≅ M`
  have ht : (Stacks.SheafOfModules.sectionsOfTop M s).eval (Opposite.op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hreg := isRegularSection_of_eval_top_ne_zero M (Stacks.SheafOfModules.sectionsOfTop M s)
    (by rwa [ht])
  have hZ := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X M _).2 hreg
  have eZ := invertibleSheafIsoZeroSchemeOfIsRegularSection M _ hreg
  rw [ht] at hZ eZ
  -- the prime divisor `P = Z`
  let P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofEffectiveCartier Z hZ
  have hV : integralComponentAt P.genericPoint = Z :=
    integralComponentAt_subschemeι_genericPoint Z
  -- `𝒪_X(P) ≅ M`
  have hsmX := MMP.Flips.isSmoothScheme_of_smooth (X ↘ Spec (.of ℂ))
  have hcart := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsmX P
  haveI hPinv := hcart.isInvertibleModule_divisorialSheaf
  haveI hPinv' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X)) := hPinv
  obtain ⟨eP⟩ := MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' P
    hZ hcart
  let e : MMP.Mori.Divisor.divisorialSheaf (Finsupp.single P 1 : MMP.Mori.Divisor X) ≅ M :=
    eP ≪≫ eZ.symm
  -- the dimension of `Z`
  have hdimV : topologicalKrullDim Z.subscheme = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_zeroScheme_eq_one rfl M s hs0]
    rfl
  haveI hVZ : AlgebraicGeometry.IsVariety ℂ (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) := {}
  refine ⟨P, ?_, hPinv', m, hm, ?_, ?_, ?_, ?_⟩
  · exact relativeDimension_eq_of_topologicalKrullDim_closure ℂ _ _ 1 (by
        rw [← Stacks.Chow.coe_support_integralComponentAt, hV,
          ← Scheme.IdealSheafData.range_subschemeι, ← Z.subschemeι.isClosedEmbedding.isEmbedding
            |>.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
        exact hdimV)
  · rw [algebraicFirstChernClass_eq_of_iso e,
      algebraicFirstChernClass_tensorPowModule L m hm, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ,
      Int.cast_natCast]
  · change IsProjectiveVariety ℂ
      ((integralComponentAt P.genericPoint).subschemeι ≫ (X ↘ Spec (.of ℂ)))
    rw [hV]
    obtain ⟨n, j, hj, hjp⟩ := (inferInstance : IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))).isProjective
    haveI := hj
    exact (⟨⟨n, Z.subschemeι ≫ j, inferInstance, by rw [Category.assoc, hjp]⟩⟩ :
      IsProjectiveVariety ℂ (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))))
  · change SmoothOfRelativeDimension 1
      ((integralComponentAt P.genericPoint).subschemeι ≫ (X ↘ Spec (.of ℂ)))
    rw [hV]
    haveI : Smooth (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) := hsm
    haveI : MMP.Mori.IsVariety ℂ (Z.subschemeι ≫ (X ↘ Spec (.of ℂ))) := hVZ
    exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 1 hdimV
  · have key : ∀ W : X.IdealSheafData, W = Z →
        (ω ≠ 0 → @pullbackForm X W.subscheme _ (MMP.SubschemeOver.overSubscheme W)
          W.subschemeι rfl ω ≠ 0) := by
      rintro W rfl
      exact hω
    exact key _ hV

/-- **A rational curve slice of a surface.** For an ample invertible module `L` on a smooth
projective surface `X` and a global one-form `ω`, there is a closed immersion `i : C → X` of a
smooth projective curve over `ℂ` such that every class `y ∈ H²(X^an; ℚ)` whose restriction to
`C` is `r i^* c₁(L)` has `y ∪ c₁(L) = r c₁(L)²`, `c₁(L)² ≠ 0` in `H⁴(X^an; ℚ)`, and `ω`
restricts to a nonzero form on `C` if it is nonzero. -/
private theorem exists_ratSlice (h2 : n = 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : MMP.Intersection.IsAmple ℂ L)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ (C : Scheme.{0}) (_ : C.Over (Spec (.of ℂ))) (_ : IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ)))
      (_ : SmoothOfRelativeDimension 1 (C ↘ Spec (.of ℂ))) (i : C ⟶ X) (_ : IsClosedImmersion i)
      (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ)),
      (∀ (y : analyticSingularCohomology ℚ (X ↘ Spec (.of ℂ)) 2) (r : ℚ),
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom y =
          r • (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) →
        cupNatUniv ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2 y
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) =
          r • cupNatUniv ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))) ∧
      cupNatUniv ℚ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L))
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) ≠ 0 ∧
      (ω ≠ 0 → pullbackForm i hi ω ≠ 0) := by
  subst h2
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 2 _
  haveI : IsProper (X ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := X)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI : IsComplexScheme X := MMP.Fourfold.isComplexScheme_of_isProjectiveVariety X inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  haveI : IsNormal X := isNormal_of_smooth_over_field (X ↘ Spec (.of ℂ))
  haveI : SmoothOfRelativeDimension (1 + 1) (X ↘ Spec (.of ℂ)) :=
    ‹SmoothOfRelativeDimension 2 (X ↘ Spec (.of ℂ))›
  have hsm := MMP.Flips.isSmoothScheme_of_smooth (X ↘ Spec (.of ℂ))
  have hdim : topologicalKrullDim X = ((1 + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 2
  have hξ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (genericPoint X) = ((1 + 1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ hdim
  obtain ⟨P, hP, hinv, m, hm, hc, hproj, hsmooth, hω⟩ :=
    exists_primeDivisor_slice (X := X) rfl L hL ω
  have : IsIntegral (integralComponentAt P.genericPoint).subscheme :=
    Stacks.Chow.isIntegral_integralComponentAt _
  have : IrreducibleSpace (integralComponentAt P.genericPoint).subscheme :=
    irreducibleSpace_of_isIntegral _
  haveI := hproj
  haveI := hsmooth
  haveI : IsProper ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) :=
    isProper_structureMorphism (X := (integralComponentAt P.genericPoint).subscheme)
  haveI : IsCurve ℂ ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) :=
    isCurve_of_eq_one (X := (integralComponentAt P.genericPoint).subscheme) (n := 1) rfl
  haveI : Smooth ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hdimC : topologicalKrullDim (integralComponentAt P.genericPoint).subscheme = 1 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension
      ((integralComponentAt P.genericPoint).subscheme ↘ Spec (.of ℂ)) 1
  have : Stacks.Ample.IsInvertibleModule X L := ‹_›
  refine ⟨(integralComponentAt P.genericPoint).subscheme, inferInstance, hproj, hsmooth,
    (integralComponentAt P.genericPoint).subschemeι, inferInstance, rfl, fun y r hy ↦ ?_, ?_,
    hω⟩
  · exact MMP.Analytic.SurfaceSlice.cupNatUniv_eq_smul_of_primeDivisor inferInstance hsm hdim P hP
      (genericPoint X) hξ L hm hc y r hy
  · exact MMP.Analytic.SurfaceSlice.cupNatUniv_ne_zero_of_primeDivisor inferInstance hsm hdim P hP
      (genericPoint X) hξ L hc (MMP.Flips.isSmoothScheme_of_smooth _) hdimC inferInstance
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).1 hL.stacksIsAmple)

/-- **A curve slice of a surface.** For an ample invertible module `L` on a smooth projective
surface `X` and a global one-form `ω`, there is a smooth projective curve `i : C → X` over `ℂ`
such that ample modules on `X` restrict to ample modules on `C`, every class `y ∈ H²(X^an; ℂ)`
whose restriction to `C` is `r i^* c₁(L)` has `y ∪ c₁(L) = r c₁(L)²`, `c₁(L)² ≠ 0`, and `ω`
restricts to a nonzero form on `C` if it is nonzero. -/
private theorem exists_curveSlice (h2 : n = 2) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (hL : MMP.Intersection.IsAmple ℂ L)
    (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) :
    ∃ (C : Scheme.{0}) (_ : C.Over (Spec (.of ℂ))) (_ : IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ)))
      (_ : SmoothOfRelativeDimension 1 (C ↘ Spec (.of ℂ))) (i : C ⟶ X)
      (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ)),
      (∀ (L' : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'],
        MMP.Intersection.IsAmple ℂ L' →
        ∃ (N : C.Modules) (_ : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N),
          MMP.Intersection.IsAmple ℂ N ∧
          (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L')) =
            singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass N)) ∧
      (∀ (y : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 2) (r : ℂ),
        (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom y =
          r • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) →
        cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2 y
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) =
          r • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))) ∧
      cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) ≠ 0 ∧
      (ω ≠ 0 → pullbackForm i hi ω ≠ 0) := by
  obtain ⟨C, _, _, _, i, _, hi, hG, hc, hω⟩ := exists_ratSlice h2 L hL ω
  haveI : IsProper (X ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := X)
  haveI : IsProper (C ↘ Spec (.of ℂ)) := isProper_structureMorphism (X := C)
  subst h2
  have hc' : cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
      (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) ≠ 0 := by
    rw [← MMP.Analytic.SurfaceSlice.mapCoeff_cupNatUniv] at hc ⊢
    exact mapCoeff_complex_ne_zero hc
  haveI : FiniteDimensional ℂ (singularCohomology ℂ (Analytification.space (X ↘ Spec (.of ℂ)))
      (2 + 2)) := finiteDimensional_analyticSingularCohomology (X := X) ℂ (2 * 2)
  refine ⟨C, inferInstance, inferInstance, inferInstance, i, hi,
    fun L' _ hL' ↦ MMP.Analytic.SurfaceSlice.exists_isAmple_pullback_eq_chern i hi L' hL',
    fun y r hy ↦ MMP.Analytic.SurfaceSlice.cupNatUniv_eq_smul_of_rat _ _
      (finrank_analyticSingularCohomology_two_mul_le_one (X := X) (n := 2) ℂ) hc hG y r hy,
    hc', hω⟩

section ChernSub

open Stacks.Ample Stacks.RelativeVeryAmple

/-- A section `t` of `G` and a section `s` of `P` with affine nonvanishing locus `U` give, through
`G ⊗ P ≅ N`, a section of `N` not vanishing at a point `x ∈ X_t ∩ U`, with affine nonvanishing
locus. -/
private theorem exists_affine_nonvanishing_tensor {Y : Scheme.{0}} (G P N : Y.Modules)
    [IsInvertibleModule Y G] [IsInvertibleModule Y P] [IsInvertibleModule Y N]
    (e : tensorModules Y G P ≅ N)
    (t : G.sections) (s : Γ(P, ⊤)) (U : Y.Opens)
    (hUs : (U : Set Y) = nonvanishingLocus _ s) (hU : IsAffineOpen U) {x : Y}
    (hxt : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := Y.toRingedSpace) _ t)
    (hxU : x ∈ U) :
    ∃ f : Γ(N, ⊤), x ∈ nonvanishingLocus _ f ∧
        IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen Y _ f) := by
  set s₀ := Stacks.SheafOfModules.sectionsOfTop _ s
  set v := SheafOfModules.sectionsMap e.hom (tensorSections G _ t s₀)
  have h2 : ∀ z : Y, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := Y.toRingedSpace) G t ↔
      z ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y G (t.eval (Opposite.op ⊤)) := fun z =>
    Set.ext_iff.1 (Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Y G t) z
  have h1 : ∀ z : Y, z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := Y.toRingedSpace) _ s₀ ↔
      z ∈ U := fun z => by
    rw [Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop, ← hUs]
    rfl
  have hmem : ∀ z : Y,
      z ∈ nonvanishingLocus N (v.eval (Opposite.op ⊤)) ↔
      z ∈ U ∧ z ∈ Stacks.NonvanishingOpen.nonvanishingOpen Y G (t.eval (Opposite.op ⊤)) := by
    intro z
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval]
    exact (nonvanishingLocus_iso e (tensorSections G _ t s₀) z).trans
      ((tensorSections_nonvanishing_iff t s₀ z).trans (and_comm.trans (and_congr (h1 z) (h2 z))))
  refine ⟨v.eval (Opposite.op ⊤), (hmem x).2 ⟨hxU, (h2 x).1 hxt⟩, ?_⟩
  convert Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (M := G) (s := t.eval (Opposite.op ⊤)) hU using 1
  ext z
  exact hmem z

/-- `(M ⊗ L^{⊗ j}) ⊗ L^{⊗ k} ≅ M ⊗ L^{⊗ (j + k)}`. -/
private noncomputable def splitIso {Y : Scheme.{0}} (L M : Y.Modules) [IsInvertibleModule Y L]
    (j k : ℕ) :
    tensorModules Y (tensorModules Y M (tensorPowModule Y L (j : ℤ)))
      (tensorPowModule Y L (k : ℤ)) ≅ tensorModules Y M (tensorPowModule Y L ((j + k : ℕ) : ℤ)) :=
  Stacks.TensorSheafSpellingIso.tensorModulesAssociator Y _ _ _ ≪≫
    tensorModulesMapIso Y (Iso.refl _)
      (tensorPowModuleAddIso Y _ (j : ℤ) (k : ℤ) ≪≫ tensorPowModuleCongr Y _ (by push_cast; ring))

/-- If `L` is ample and `M` is invertible, then `M ⊗ L^{⊗ m}` is ample for `m ≫ 0`. -/
private theorem eventually_isAmple_tensorModules_tensorPowModule {Y : Scheme.{0}}
    (L M : Y.Modules) [IsInvertibleModule Y L] [IsInvertibleModule Y M] (hL : IsAmple Y L) :
    ∀ᶠ m : ℕ in Filter.atTop, IsAmple Y (tensorModules Y M (tensorPowModule Y L (m : ℤ))) := by
  have : SheafOfModules.IsFiniteType.{0, 0, 0} M :=
    Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule M
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hL).2 M inferInstance inferInstance
  haveI : CompactSpace Y := hL.1
  choose k hk s U hUs hxU hUaff using hL.2
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : Y ↦ ((U x : Y.Opens) : Set Y))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine Filter.eventually_atTop.2 ⟨T.sup k + n₀.toNat, fun m hm => ?_⟩
  refine Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus _ fun x => ?_
  obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
  have hsup : k y ≤ T.sup k := Finset.le_sup hyT
  obtain ⟨j, rfl⟩ : ∃ j, m = j + k y := ⟨m - k y, by omega⟩
  obtain ⟨σ, -⟩ := hn₀ j (by omega)
  set G := tensorModules Y M (tensorPowModule Y L (j : ℤ))
  haveI : SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property G :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) _ _
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory Y
  let i := Stacks.TensorSheafSpellingIso.monoidalTensorIso Y M
    (tensorPowModule Y L (j : ℤ))
  haveI : @Epi (SheafOfModules.{0} Y.ringCatSheaf) _ _ _ i.hom :=
    @IsIso.epi_of_iso _ _ _ _ i.hom i.isIso_hom
  obtain ⟨a, ha⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing G (σ.ofEpi i.hom) x
  exact exists_affine_nonvanishing_tensor G _ _ (splitIso L M j (k y)) _ (s y) (U y) (hUs y)
    (hUaff y) ha hxy

end ChernSub

/-- **Every invertible module is a difference of ample ones**, on Chern classes:
`c₁(L) = c₁(A) - c₁(B)` with `A`, `B` ample (`A = L ⊗ H^k`, `B = H^k` for `H` ample, `k ≫ 0`). -/
private theorem exists_chern_eq_sub (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ (A : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A)
      (B : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B),
      MMP.Intersection.IsAmple ℂ A ∧ MMP.Intersection.IsAmple ℂ B ∧
      singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) =
        singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass A) -
          singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass B) := by
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety
    (t := X ↘ Spec (.of ℂ)) inferInstance
  haveI : Stacks.Ample.IsInvertibleModule X H := hH
  haveI : Stacks.Ample.IsInvertibleModule X L := ‹_›
  have hHs : Stacks.Ample.IsAmple X H := (Stacks.AmpleBridge.isAmple_iff_isAmple X H).2 hHa
  obtain ⟨m, hmA, hm⟩ := ((eventually_isAmple_tensorModules_tensorPowModule H L hHs).and
    (Filter.eventually_ge_atTop 1)).exists
  set B := Stacks.Ample.tensorPowModule X H (m : ℤ)
  haveI hB : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B := inferInstance
  haveI hA : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj L).obj B) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.2 L B
  refine ⟨_, hA, B, hB, MMP.Intersection.isAmple_of_stacksIsAmple ℂ _ hmA,
    MMP.Intersection.isAmple_of_stacksIsAmple ℂ B
      (Stacks.AmplePowers.isAmple_tensorPowModule_of_isAmple H m hm hHs), ?_⟩
  rw [algebraicFirstChernClass_sheafTensor, map_add, add_sub_cancel_right]

/-- On a curve slice, the restrictions of the first Chern classes of two ample modules lie on one
positive ray. -/
private theorem exists_pos_rat_pullback_chern {C : Scheme.{0}} [C.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (C ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of ℂ))]
    (i : C ⟶ X) (hi : i ≫ (X ↘ Spec (.of ℂ)) = C ↘ Spec (.of ℂ))
    (hN : ∀ (L' : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'],
        MMP.Intersection.IsAmple ℂ L' →
        ∃ (N : C.Modules) (_ : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 N),
          MMP.Intersection.IsAmple ℂ N ∧
          (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L')) =
            singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass N))
    (L₁ L₂ : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L₂]
    (h₁ : MMP.Intersection.IsAmple ℂ L₁) (h₂ : MMP.Intersection.IsAmple ℂ L₂) :
    ∃ q : ℚ, 0 < q ∧
      (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
        (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
        Set.univ ((2 : ℕ) : ℤ)).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L₂)) =
      (q : ℂ) • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
        (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
        Set.univ ((2 : ℕ) : ℤ)).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L₁)) := by
  obtain ⟨N₁, _, hA₁, e₁⟩ := hN L₁ h₁
  obtain ⟨N₂, _, hA₂, e₂⟩ := hN L₂ h₂
  obtain ⟨q, hq, e⟩ := exists_pos_rat_smul_chern_curve (X := C) (n := 1) rfl N₁ N₂ hA₁ hA₂
  refine ⟨q, hq, ?_⟩
  rw [e₁, e₂]
  exact e

set_option maxRecDepth 8000 in
/-- **The integral over a surface.** On a smooth projective surface, a linear functional on
`H⁴(X^an; ℂ)` normalised on `c₁(L₀)²` for one ample `L₀`, through curve slices. -/
private theorem exists_integral_two (h2 : n = 2) :
    ∃ I : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * n) →ₗ[ℂ] ℂ,
      (∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        MMP.Intersection.IsAmple ℂ L → ∀ y, chernH L ^ n = inclH X (2 * n) y →
          ∃ r : ℝ, 0 < r ∧ I y = r) ∧
      (∀ (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
        (α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1), ω ≠ 0 → IsDR X ω α →
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
          MMP.Intersection.IsAmple ℂ L → ∀ y,
            Complex.I • (inclH X 1 α * inclH X 1 (conjH X α) * chernH L ^ (n - 1)) =
              inclH X (2 * n) y → ∃ r : ℝ, 0 < r ∧ I y = r) ∧
      (n = 2 → ∀ a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1,
        (∃ ω, IsDR X ω a) → (∃ η, IsDR X η b) →
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (y),
          inclH X 1 a * inclH X 1 b * chernH L ^ (n - 1) = inclH X (2 * n) y → I y = 0) := by
  subst h2
  -- the classes `y` of the three statements
  have hsq : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (y),
      chernH L ^ 2 = inclH X (2 * 2) y →
        y = cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) :=
    fun L _ y hy ↦ DirectSum.of_injective (β := fun i : ℕ ↦ cohomologyWithSupports ℂ
      (ModuleCat.of ℂ ℂ) (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) (2 * 2)
      (by rw [← hy, pow_two, DirectSum.of_mul_of]; rfl)
  have hmix : ∀ (a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) (L : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (y),
      inclH X 1 a * inclH X 1 b * chernH L ^ (2 - 1) = inclH X (2 * 2) y →
        y = cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a b)
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) :=
    fun a b L _ y hy ↦ DirectSum.of_injective (β := fun i : ℕ ↦ cohomologyWithSupports ℂ
      (ModuleCat.of ℂ ℂ) (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) (2 * 2)
      (by rw [← hy, show 2 - 1 = 1 from rfl, pow_one, DirectSum.of_mul_of, DirectSum.of_mul_of]; rfl)
  -- the normalisation
  obtain ⟨L₀, hL₀, hA₀⟩ := exists_isAmple (X := X)
  obtain ⟨C₀, _, _, _, i₀, hi₀, hN₀, hG₀, hw₀, -⟩ := exists_curveSlice (X := X) rfl L₀ hA₀ 0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hw₀
  -- positivity on squares of ample classes
  have hpos : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      MMP.Intersection.IsAmple ℂ L → ∃ r : ℝ, 0 < r ∧
        f (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))) = r := by
    intro L _ hL
    obtain ⟨q, hq, hqe⟩ := exists_pos_rat_pullback_chern i₀ hi₀ hN₀ L₀ L hA₀ hL
    have e₁ := hG₀ _ (q : ℂ) hqe
    obtain ⟨C, _, _, _, i, hi, hN, hG, -, -⟩ := exists_curveSlice (X := X) rfl L hL 0
    obtain ⟨q', hq', hq'e⟩ := exists_pos_rat_pullback_chern i hi hN L L₀ hL hA₀
    have e₂ := hG _ (q' : ℂ) hq'e
    rw [MMP.Analytic.SurfaceSlice.cupNatUniv_two_comm, e₁] at e₂
    have hq'0 : (q' : ℂ) ≠ 0 := by exact_mod_cast hq'.ne'
    refine ⟨((q / q' : ℚ) : ℝ), by exact_mod_cast div_pos hq hq', ?_⟩
    have e₃ : cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L))
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) =
        ((q : ℂ) / q') • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L₀))
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L₀)) := by
      rw [div_eq_inv_mul, mul_smul, e₂, smul_smul, inv_mul_cancel₀ hq'0, one_smul]
    rw [e₃, map_smul, hf, smul_eq_mul, mul_one]
    push_cast
    rfl
  refine ⟨f, fun L _ hL y hy ↦ ?_, fun ω α hω hα L _ hL y hy ↦ ?_, fun _ a b ha hb L _ y hy ↦ ?_⟩
  · rw [hsq L y hy]
    exact hpos L hL
  · -- `i [ω] ∪ \overline{[ω]} ∪ c₁(L)` through a slice on which `ω` does not vanish
    obtain ⟨C, _, _, _, i, hi, hN, hG, -, hωC⟩ := exists_curveSlice (X := X) rfl L hL ω
    obtain ⟨N, _, hAN, eN⟩ := hN L hL
    have hαC := IsDR.pullback (X := X) (n := 2) (Or.inr rfl) (Or.inl rfl) C i hi hα
    obtain ⟨s, hs, es⟩ := exists_pos_smul_cup_curve (X := C) (n := 1) rfl
      (hωC hω) hαC N hAN
    have hpb : (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
        (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
        Set.univ ((1 + 1 : ℕ) : ℤ)).hom
        (Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α)) =
        (s : ℂ) • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
          (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
          Set.univ ((2 : ℕ) : ℤ)).hom
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) := by
      rw [map_smul, MMP.Analytic.SurfaceSlice.pullback_cupNatUniv, pullback_mapCoeff_star]
      erw [eN]
      exact es
    have e := hG _ (s : ℂ) hpb
    obtain ⟨t, ht, ft⟩ := hpos L hL
    have hy' : y = Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
        (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α))
        (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L)) := by
      have := hmix α (conjH X α) L (Complex.I⁻¹ • y) (by
        rw [DirectSum.of_smul, ← hy, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul])
      rw [← this, smul_smul, mul_inv_cancel₀ Complex.I_ne_zero, one_smul]
    refine ⟨s * t, mul_pos hs ht, ?_⟩
    rw [hy', ← LinearMap.smul_apply, ← map_smul]
    erw [e]
    rw [map_smul, ft, smul_eq_mul]
    push_cast
    ring
  · -- holomorphic classes pair to zero against an ample class, on a slice
    obtain ⟨ω, ha⟩ := ha
    obtain ⟨η, hb⟩ := hb
    have hv : ∀ (A : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A],
        MMP.Intersection.IsAmple ℂ A →
        cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 2 2
          (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a b)
          (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass A)) = 0 := by
      intro A _ hA
      obtain ⟨C, _, _, _, i, hi, -, hG, -, -⟩ := exists_curveSlice (X := X) rfl A hA 0
      have hpb : (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
          (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
          Set.univ ((1 + 1 : ℕ) : ℤ)).hom
          (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a b) =
          (0 : ℂ) • (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
            (TopCat.ofHom ⟨ComplexPoints.realize i hi, ComplexPoints.continuous_realize i hi⟩)
            Set.univ ((2 : ℕ) : ℤ)).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass A)) := by
        rw [zero_smul, MMP.Analytic.SurfaceSlice.pullback_cupNatUniv]
        exact cupNatUniv_eq_zero_of_isDR (X := C) (n := 1) rfl
          (IsDR.pullback (X := X) (n := 2) (Or.inr rfl) (Or.inl rfl) C i hi ha)
          (IsDR.pullback (X := X) (n := 2) (Or.inr rfl) (Or.inl rfl) C i hi hb)
      have := hG _ 0 hpb
      rw [zero_smul] at this
      exact this
    obtain ⟨A, _, B, _, hA, hB, e⟩ := exists_chern_eq_sub L
    rw [hmix a b L y hy, e, map_sub, hv A hA, hv B hB, sub_zero, map_zero]

/-- **The integral over `X^an`.** There is a linear functional `∫_X` on `H^{2n}(X^an; ℂ)`, the
pairing with the fundamental class, which is a positive real number on `c₁(L)ⁿ` for `L` ample
and on `i [ω] ∪ \overline{[ω]} ∪ c₁(L)^{n-1}` for `ω ≠ 0`, and which on a surface vanishes on
`[ω] ∪ [η] ∪ c₁(L)`. The Fubini–Study form represents a multiple of `c₁(L)`, and by Stokes these
are the integrals of the nonnegative top forms `Θⁿ` and `i ω ∧ ω̄ ∧ Θ^{n-1}`, the second positive
where `ω ≠ 0`, and of the form `ω ∧ η ∧ Θ` of type `(3, 1)`. -/
private theorem exists_integral (hn : n = 1 ∨ n = 2) :
    ∃ I : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * n) →ₗ[ℂ] ℂ,
      (∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        MMP.Intersection.IsAmple ℂ L → ∀ y, chernH L ^ n = inclH X (2 * n) y →
          ∃ r : ℝ, 0 < r ∧ I y = r) ∧
      (∀ (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤))
        (α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1), ω ≠ 0 → IsDR X ω α →
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
          MMP.Intersection.IsAmple ℂ L → ∀ y,
            Complex.I • (inclH X 1 α * inclH X 1 (conjH X α) * chernH L ^ (n - 1)) =
              inclH X (2 * n) y → ∃ r : ℝ, 0 < r ∧ I y = r) ∧
      (n = 2 → ∀ a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1,
        (∃ ω, IsDR X ω a) → (∃ η, IsDR X η b) →
        ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (y),
          inclH X 1 a * inclH X 1 b * chernH L ^ (n - 1) = inclH X (2 * n) y → I y = 0) := by
  rcases hn with h1 | h2
  · subst h1
    obtain ⟨L₀, hL₀, hA₀, hq₀⟩ := exists_isAmple_mapCoeff_ne_zero (X := X) rfl
    have hc₀ : (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L₀) :
        analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) (2 * 1)) ≠ 0 :=
      mapCoeff_complex_ne_zero hq₀
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hc₀
    refine ⟨f, ?_, ?_, fun h ↦ absurd h (by norm_num)⟩
    · intro L _ hL y hy
      obtain ⟨q, hq, e⟩ := exists_pos_rat_smul_chern_curve rfl L₀ L hA₀ hL
      have hyL : y = singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) :=
        DirectSum.of_injective (β := fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
          (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) (2 * 1)
          (by rw [← hy, pow_one])
      refine ⟨(q : ℝ), by exact_mod_cast hq, ?_⟩
      rw [hyL, e, map_smul, hf, smul_eq_mul, mul_one, Complex.ofReal_ratCast]
    · intro ω α hω hα L _ hL y hy
      obtain ⟨s, hs, e⟩ := exists_pos_smul_cup_curve rfl hω hα L₀ hA₀
      have hyc : y = Complex.I •
          cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α) :=
        DirectSum.of_injective (β := fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
          (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) (2 * 1) (by
            rw [← hy, Nat.sub_self, pow_zero, mul_one, DirectSum.of_mul_of, ← DirectSum.of_smul]
            rfl)
      refine ⟨s, hs, ?_⟩
      rw [hyc, e, map_smul, hf, smul_eq_mul, mul_one]
  · exact exists_integral_two h2

/-- **Vanishing by type.** Two holomorphic classes pair to zero against `c₁(L)^{n-1}`: the form
`ω ∧ η ∧ Θ^{n-1}` has type `(n + 1, n - 1)`. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.mul_mul_pow_eq_zero (hn : n = 1 ∨ n = 2)
    {a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1}
    (ha : ∃ ω, IsDR X ω a) (hb : ∃ η, IsDR X η b) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    inclH X 1 a * inclH X 1 b * chernH L ^ (n - 1) = 0 := by
  rcases hn with rfl | rfl
  · obtain ⟨ω, hω⟩ := ha
    obtain ⟨η, hη⟩ := hb
    rw [Nat.sub_self, pow_zero, mul_one, DirectSum.of_mul_of]
    show DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
      (Analytification.space (X ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) (1 + 1)
        (cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 a b) = 0
    rw [cupNatUniv_eq_zero_of_isDR rfl hω hη, map_zero]
  · obtain ⟨I, hIc, -, hIv⟩ := exists_integral (X := X) (n := 2) (Or.inr rfl)
    obtain ⟨y, hy⟩ := exists_inclH_eq_mul_mul_pow (n := 2) (by norm_num) a b L
    obtain ⟨L₀, hL₀, hA⟩ := exists_isAmple (X := X)
    obtain ⟨yc, hyc⟩ := exists_inclH_eq_pow (X := X) (n := 2) L₀
    obtain ⟨rc, hrc, hIyc⟩ := hIc L₀ hA yc hyc
    have hyc0 : yc ≠ 0 := by
      rintro rfl
      rw [map_zero] at hIyc
      exact hrc.ne' (by exact_mod_cast hIyc.symm)
    haveI := finiteDimensional_analyticSingularCohomology (X := X) ℂ (2 * 2)
    obtain ⟨s, rfl⟩ := exists_smul_eq_of_finrank_le_one
      (finrank_analyticSingularCohomology_two_mul_le_one ℂ) hyc0 y
    have h0 := hIv rfl a b ha hb L _ hy
    rw [map_smul, hIyc, smul_eq_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [hy, h0, zero_smul, map_zero]
    · exact absurd h0 (by exact_mod_cast hrc.ne')

/-- **Positivity of the polarization.** For `ω ≠ 0` and `L` ample, `i [ω] ∪ \overline{[ω]} ∪
c₁(L)^{n-1}` is a positive multiple of `c₁(L)^n`: the Fubini–Study form represents a multiple of
`c₁(L)`, and `i ω ∧ ω̄ ∧ Θ^{n-1}` is a nonnegative top form, positive where `ω ≠ 0`. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.exists_pos (hn : n = 1 ∨ n = 2)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (hω : ω ≠ 0) (hα : IsDR X ω α)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L) :
    ∃ t : ℝ, 0 < t ∧ Complex.I • (inclH X 1 α * inclH X 1 (conjH X α) * chernH L ^ (n - 1)) =
      (t : ℂ) • chernH L ^ n := by
  obtain ⟨I, hIc, hIa, -⟩ := exists_integral (X := X) hn
  obtain ⟨y, hy⟩ := exists_inclH_eq_mul_mul_pow (n := n) (by omega) α (conjH X α) L
  obtain ⟨yc, hyc⟩ := exists_inclH_eq_pow (X := X) (n := n) L
  obtain ⟨rc, hrc, hIyc⟩ := hIc L hL yc hyc
  have hyI : Complex.I • (inclH X 1 α * inclH X 1 (conjH X α) * chernH L ^ (n - 1)) =
      inclH X (2 * n) (Complex.I • y) := by
    rw [hy, DirectSum.of_smul]
  obtain ⟨ra, hra, hIya⟩ := hIa ω α hω hα L hL _ hyI
  have hyc0 : yc ≠ 0 := by
    rintro rfl
    rw [map_zero] at hIyc
    exact hrc.ne' (by exact_mod_cast hIyc.symm)
  haveI := finiteDimensional_analyticSingularCohomology (X := X) ℂ (2 * n)
  obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_le_one
    (finrank_analyticSingularCohomology_two_mul_le_one ℂ) hyc0 (Complex.I • y)
  have hsr : (ra : ℂ) = s * rc := by rw [← hIya, ← hs, map_smul, hIyc, smul_eq_mul]
  have hrc0 : (rc : ℂ) ≠ 0 := by exact_mod_cast hrc.ne'
  refine ⟨ra / rc, div_pos hra hrc, ?_⟩
  rw [hyI, ← hs, DirectSum.of_smul, ← hyc]
  congr 1
  push_cast
  rw [hsr, mul_div_cancel_right₀ _ hrc0]

/-- A form whose de Rham class vanishes is zero. -/
private theorem _root_.MMP.Fourfold.Polarization.IsDR.eq_zero (hn : n = 1 ∨ n = 2)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    (hω : IsDR X ω 0) : ω = 0 :=
  eq_zero_of_isDR_of_eq_conjH_form hn hω isDR_zero (map_zero _).symm

/-- **Serre duality on a curve**: `h¹(𝒪_X) = h⁰(ω_X) = h⁰(Ω¹_X)`. -/
private theorem finrank_cohomologyOverField_unit_one_le (h1 : n = 1) :
    Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))) 0) := by
  subst h1
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : IsProper (X ↘ Spec (.of ℂ)) :=
    isProper_of_isProjectiveMorphism _ (IsProjectiveVariety.isProjective (k := ℂ))
  haveI hV : AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsIntegral X := hV.toIsIntegral
  haveI := isCurve_of_eq_one (X := X) (n := 1) rfl
  have hΓ := finrank_globalSections_eq_one ℂ (X ↘ Spec (.of ℂ))
  haveI : Nontrivial Γ(X, ⊤) := by
    letI : Algebra ℂ Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X ↘ Spec (.of ℂ)).appTop).hom.toAlgebra
    exact Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [hΓ]; exact one_pos)
  haveI : IsIso ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X ↘ Spec (.of ℂ)).appTop) :=
    Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one _ hΓ
  rw [finrank_cohomologyOverField_zero_relativeDifferentials_eq_genus,
    genus_eq_finrank_structureSheafCohomology]
  exact ((structureSheafCohomologyIsoCohomologyOverField ℂ (X ↘ Spec (.of ℂ)) 1).toLinearEquiv
    |>.finrank_eq).symm.le

/-- **Holomorphic one-forms inject into `H¹`**: `ω ↦ [ω]` is a linear injection
`H⁰(X, Ω¹_X) → H¹(X^an; ℂ)` (`IsDR.eq_zero`), so `h⁰(Ω¹_X)` is at most the dimension of the
holomorphic classes. -/
private theorem finrank_cohomologyOverField_zero_le_finrank_span_isDR (hn : n = 1 ∨ n = 2) :
    Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))) 0) ≤
      Module.finrank ℂ (Submodule.span ℂ {α | ∃ ω, IsDR X ω α}) := by
  haveI := finiteDimensional_analyticSingularCohomology (X := X) ℂ 1
  set Ω := Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))
  choose cls hcls using fun ω ↦ exists_isDR (X := X) hn ω
  have hu : ∀ ω α, IsDR X ω α → cls ω = α := fun ω α h ↦ IsDR.unique hn (hcls ω) h
  haveI : IsIso (Scheme.Modules.exteriorGenerator Ω) :=
    (SheafOfModules.algebras _ Ω).isIso_exteriorGenerator
  let gen : Γ(Ω, ⊤) → Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤) :=
    fun s ↦ (Scheme.Modules.exteriorGenerator Ω).app ⊤ s
  have hgen : Function.Injective gen := by
    haveI : IsIso ((Scheme.Modules.exteriorGenerator Ω).app ⊤) :=
      Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance ⊤
    exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  let E := (cohomologyOverFieldZeroLinearIso ℂ (X ↘ Spec (.of ℂ)) Ω).toLinearEquiv
  let Φ : cohomologyOverField ℂ (X ↘ Spec (.of ℂ)) Ω 0 →ₗ[ℂ]
      analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1 :=
    { toFun := fun h ↦ cls (gen (E h))
      map_add' := fun a b ↦ by
        refine hu _ _ ?_
        rw [map_add]
        have : gen (E a + E b) = gen (E a) + gen (E b) :=
          map_add ((Scheme.Modules.exteriorGenerator Ω).app ⊤).hom _ _
        rw [this]
        exact (hcls _).add (hcls _)
      map_smul' := fun c a ↦ by
        refine hu _ _ ?_
        rw [map_smul]
        have : gen (c • E a) = @algebraMap ℂ Γ(X, ⊤) _ _
            (MMP.Mori.sectionAlgebra (X ↘ Spec (.of ℂ)) ⊤) c • gen (E a) :=
          Scheme.Modules.Hom.app_smul _ _ _
        rw [this]
        exact (hcls _).smul c }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h h0
    have h1 : IsDR X (gen (E h)) 0 := by
      have h0' : cls (gen (E h)) = 0 := h0
      have := hcls (gen (E h))
      rwa [h0'] at this
    have h2 := IsDR.eq_zero hn h1
    have h3 : E h = 0 := hgen (h2.trans (map_zero ((Scheme.Modules.exteriorGenerator Ω).app ⊤).hom).symm)
    exact E.map_eq_zero_iff.1 h3
  have hrange : LinearMap.range Φ ≤ Submodule.span ℂ {α | ∃ ω, IsDR X ω α} := by
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨_, hcls _⟩
  calc Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ)) Ω 0)
      = Module.finrank ℂ (LinearMap.range Φ) := (LinearMap.finrank_range_of_inj hΦ).symm
    _ ≤ _ := Submodule.finrank_mono hrange

/-- **The first Betti number is at most twice the number of holomorphic classes**:
`b₁ = h⁰(Ω¹) + h¹(𝒪_X)` and `h¹(𝒪_X) ≤ h⁰(Ω¹)`. -/
private theorem finrank_le_two_mul_finrank_span_isDR (hn : n = 1 ∨ n = 2) :
    Module.finrank ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) ≤
      2 * Module.finrank ℂ (Submodule.span ℂ {α | ∃ ω, IsDR X ω α}) := by
  haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨-, -, h⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
  have hb : Module.finrank ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) = _ :=
    (h X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).1
  have e1 : Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank ℂ (cohomologyOverField ℂ (X ↘ Spec (.of ℂ))
        (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of ℂ))) 0) := by
    rcases hn with h1 | h2
    · exact finrank_cohomologyOverField_unit_one_le h1
    · exact MMP.Analytic.finrank_cohomologyOverField_unit_one_le_of_surface h2
  have e2 := finrank_cohomologyOverField_zero_le_finrank_span_isDR (X := X) hn
  omega

/-- A holomorphic class which is also antiholomorphic is zero. -/
private theorem eq_zero_of_isDR_of_eq_conjH (hn : n = 1 ∨ n = 2)
    {ω η : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (ha : IsDR X ω a)
    (hb : IsDR X η b) (hab : a = conjH X b) : a = 0 := by
  have hω := eq_zero_of_isDR_of_eq_conjH_form hn ha hb hab
  subst hω
  exact IsDR.unique hn ha isDR_zero

/-- **The degree-one Hodge decomposition.** Every class in `H¹(X^an; ℂ)` is `a + \overline{b}`
for de Rham classes `a`, `b` of a unique pair of forms. -/
private theorem existsUnique_decomposition (hn : n = 1 ∨ n = 2)
    (α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) :
    ∃! p : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤) ×
        Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤),
      ∃ a b, IsDR X p.1 a ∧ IsDR X p.2 b ∧ α = a + conjH X b := by
  -- the holomorphic classes
  let W : Submodule ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) :=
    { carrier := {a | ∃ ω, IsDR X ω a}
      add_mem' := by
        rintro a b ⟨ω, hω⟩ ⟨η, hη⟩
        exact ⟨ω - (0 - η), by simpa using hω.sub (isDR_zero.sub hη)⟩
      zero_mem' := ⟨0, isDR_zero⟩
      smul_mem' := by
        rintro c a ⟨ω, hω⟩
        exact ⟨_, hω.smul c⟩ }
  -- the antiholomorphic classes
  let W' : Submodule ℂ (analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1) :=
    { carrier := {a | ∃ b ∈ W, a = conjH X b}
      add_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨b + b', W.add_mem hb hb', (map_add _ _ _).symm⟩
      zero_mem' := ⟨0, W.zero_mem, (map_zero _).symm⟩
      smul_mem' := by
        rintro c _ ⟨b, hb, rfl⟩
        refine ⟨starRingEnd ℂ c • b, W.smul_mem _ hb, ?_⟩
        rw [map_smulₛₗ, Complex.conj_conj] }
  haveI := finiteDimensional_analyticSingularCohomology (X := X) ℂ 1
  have hdim := finrank_le_two_mul_finrank_span_isDR (X := X) hn
  have hspan : Submodule.span ℂ {α | ∃ ω, IsDR X ω α} = W := Submodule.span_eq W
  rw [hspan] at hdim
  have hinf : W ⊓ W' = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨⟨ω, hω⟩, ⟨b, ⟨η, hη⟩, hab⟩⟩
    exact eq_zero_of_isDR_of_eq_conjH hn hω hη hab
  -- `conj` is a real-linear injection of `W` into `W'`
  have hle : Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    let c : W →ₗ[ℝ] W' :=
      { toFun := fun b ↦ ⟨conjH X b, b, b.2, rfl⟩
        map_add' := fun b b' ↦ Subtype.ext (map_add _ _ _)
        map_smul' := fun r b ↦ Subtype.ext (by
          change conjH X ((r : ℂ) • (b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1)) =
            (r : ℂ) • conjH X b
          rw [map_smulₛₗ, Complex.conj_ofReal]) }
    have hc : Function.Injective c := fun b b' h ↦ by
      have h' := congrArg (fun x : W' ↦ conjH X (x : analyticSingularCohomology ℂ _ 1)) h
      simp only [c, LinearMap.coe_mk, AddHom.coe_mk, mapCoeff_star_star] at h'
      exact Subtype.ext h'
    have := LinearMap.finrank_le_finrank_of_injective hc
    rw [finrank_real_of_complex, finrank_real_of_complex] at this
    omega
  have htop : W ⊔ W' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hinf, finrank_bot] at h1
    exact le_antisymm (Submodule.finrank_le _) (by omega)
  have hα : α ∈ W ⊔ W' := htop ▸ Submodule.mem_top
  obtain ⟨y, ⟨ω, hω⟩, z, ⟨b, ⟨η, hη⟩, rfl⟩, hyz⟩ := Submodule.mem_sup.1 hα
  refine ⟨(ω, η), ⟨y, b, hω, hη, hyz.symm⟩, ?_⟩
  rintro ⟨ω', η'⟩ ⟨a', b', hω', hη', he⟩
  have hsub : y - a' = conjH X (b' - b) := by
    rw [map_sub]
    have := hyz.trans he
    linear_combination (norm := abel_nf) this
  have h0 : y - a' = 0 :=
    eq_zero_of_isDR_of_eq_conjH hn (hω.sub hω') (hη'.sub hη) hsub
  have hb0 : b' - b = 0 := by
    have := congrArg (conjH X) hsub
    rwa [h0, map_zero, mapCoeff_star_star, eq_comm] at this
  have e1 := IsDR.eq_zero hn (h0 ▸ hω.sub hω')
  have e2 := IsDR.eq_zero hn (hb0 ▸ hη'.sub hη)
  ext
  · exact (sub_eq_zero.1 e1).symm
  · exact sub_eq_zero.1 e2

end Decomposition

end MMP.FourfoldProofs.MmpConductorSurfaceH1PolarizationProof

namespace MMP.Analytic

open MMP.FourfoldProofs.MmpConductorSurfaceH1PolarizationProof

set_option maxRecDepth 8000 in
/-- **The degree-one Hodge decomposition and its polarization on a smooth projective curve or
surface.** Let `X` be a smooth projective complex variety of dimension `n = 1` or `n = 2`.
Call `α ∈ H¹(X^an; ℂ)` a de Rham class of the global one-form `ω` if it is the class of a
cocycle whose value on every continuously differentiable `1`-simplex `σ` in the `ℂ`-points of an
affine open `U` with `ω|_U = ∑ⱼ fⱼ dgⱼ` is `∫₀¹ ∑ⱼ fⱼ(σ t) (gⱼ ∘ σ)'(t) dt`. Then:
* every global one-form is closed;
* every global one-form has exactly one de Rham class;
* every `α ∈ H¹(X^an; ℂ)` is `[ω] + \overline{[η]}` for exactly one pair of forms `(ω, η)`;
* for holomorphic classes `α, β` and every line bundle with Chern class `c`,
  `α ∪ β ∪ c^{n-1} = 0`;
* for `ω ≠ 0` and an ample line bundle `L` with `c = c₁(L)`,
  `i • ([ω] ∪ \overline{[ω]} ∪ c^{n-1}) = t • c^n` for some real `t > 0`, that is,
  `i ∫_X ω ∧ \overline{ω} ∧ c^{n-1} > 0`;
* pull-back along a morphism `f : Y ⟶ X` over `ℂ` from a smooth projective variety of
  dimension one or two carries holomorphic classes to holomorphic classes and conjugates of
  holomorphic classes to conjugates of holomorphic classes. -/
@[mmp "thm_mmp_conductor_surface_h1_polarization"]
public theorem hodgeDecomposition_one_of_isProjectiveVariety {n : ℕ} (hn : n = 1 ∨ n = 2)
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] :
    let IsDeRhamClass : ∀ (V : Scheme.{0}) [V.Over (Spec (.of ℂ))],
        Γ((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤) →
          analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 → Prop :=
      fun V _ ω α ↦
        ∃ (φ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1 → ℂ)
          (hφ : φ ∈ relCocycles ℂ (Set.univᶜ : Set (Analytification.space (V ↘ Spec (.of ℂ)))) 1),
          α = cohomologyWithSupports.ofCocycle ℂ _ 1 φ hφ ∧
          ∀ (U : V.affineOpens) (m : ℕ) (f g : Fin m → Γ(V, U)),
            (letI := MMP.Mori.sectionAlgebra (V ↘ Spec (.of ℂ)) (U : V.Opens);
              MMP.DeRham.formsAlgEquiv (V ↘ Spec (.of ℂ)) 1 U
                (((V ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
                  (homOfLE le_top).op ω) =
                ∑ j, f j • exteriorPower.ιMulti Γ(V, U) 1
                  (fun _ ↦ KaehlerDifferential.D ℂ Γ(V, U) (g j))) →
            ∀ (σ : Simplex (Analytification.space (V ↘ Spec (.of ℂ))) 1)
              (hσ : ∀ s, σ s ∈ ComplexPoints.chart (sX := V ↘ Spec (.of ℂ)) (U : V.Opens)),
              (∀ h : Γ(V, U), ContDiffOn ℝ 1 (fun t : ℝ ↦ ComplexPoints.eval (U : V.Opens) h
                ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)),
                  hσ _⟩) (Set.Icc 0 1)) →
              φ σ = ∫ t in (0 : ℝ)..1, ∑ j,
                ComplexPoints.eval (U : V.Opens) (f j)
                  ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one t)),
                    hσ _⟩ *
                deriv (fun s : ℝ ↦ ComplexPoints.eval (U : V.Opens) (g j)
                  ⟨σ (stdSimplexHomeomorphUnitInterval.symm (Set.projIcc 0 1 zero_le_one s)),
                    hσ _⟩) t
    let conj : ∀ (V : Scheme.{0}) [V.Over (Spec (.of ℂ))],
        analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 →
          analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) 1 :=
      fun V _ ↦ singularCohomology.mapCoeff (Y := Analytification.space (V ↘ Spec (.of ℂ)))
        (starRingEnd ℂ) 1
    let incl : ∀ (V : Scheme.{0}) [V.Over (Spec (.of ℂ))] (i : ℕ),
        analyticSingularCohomology ℂ (V ↘ Spec (.of ℂ)) i →
          CohomologyRing ℂ (Analytification.space (V ↘ Spec (.of ℂ))) :=
      fun V _ i ↦ DirectSum.of (fun i : ℕ ↦ cohomologyWithSupports ℂ (ModuleCat.of ℂ ℂ)
        (Analytification.space (V ↘ Spec (.of ℂ))) Set.univ (i : ℕ)) i
    (∀ ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤),
      (((X ↘ Spec (.of ℂ)).deRhamComplex).d 1 2).val.app (op ⊤) ω = 0) ∧
    (∀ ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤),
      ∃! α, IsDeRhamClass X ω α) ∧
    (∀ α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1,
      ∃! p : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤) ×
          Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤),
        ∃ a b, IsDeRhamClass X p.1 a ∧ IsDeRhamClass X p.2 b ∧ α = a + conj X b) ∧
    (∀ (a b : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1),
      (∃ ω, IsDeRhamClass X ω a) → (∃ η, IsDeRhamClass X η b) →
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        incl X 1 a * incl X 1 b * incl X 2 (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
          (algebraicFirstChernClass L)) ^ (n - 1) = 0) ∧
    (∀ (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) (α),
      ω ≠ 0 → IsDeRhamClass X ω α →
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        MMP.Intersection.IsAmple ℂ L →
        ∃ t : ℝ, 0 < t ∧
          Complex.I • (incl X 1 α * incl X 1 (conj X α) *
              incl X 2 (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
                (algebraicFirstChernClass L)) ^ (n - 1)) =
            (t : ℂ) • incl X 2 (singularCohomology.mapCoeff (Int.castRingHom ℂ) 2
                (algebraicFirstChernClass L)) ^ n) ∧
    (∀ {m : ℕ} (_ : m = 1 ∨ m = 2) (Y : Scheme.{0}) [Y.Over (Spec (.of ℂ))]
      [IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))]
      [SmoothOfRelativeDimension m (Y ↘ Spec (.of ℂ))]
      (f : Y ⟶ X) (hf : f ≫ (X ↘ Spec (.of ℂ)) = Y ↘ Spec (.of ℂ))
      (ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)) (α),
      IsDeRhamClass X ω α →
      (∃ η, IsDeRhamClass Y η ((cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
          (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
          Set.univ ((1 : ℕ) : ℤ)).hom α)) ∧
      ∃ η β, IsDeRhamClass Y η β ∧
        (cohomologyWithSupports.pullback ℂ (ModuleCat.of ℂ ℂ)
          (TopCat.ofHom ⟨ComplexPoints.realize f hf, ComplexPoints.continuous_realize f hf⟩)
          Set.univ ((1 : ℕ) : ℤ)).hom (conj X α) = conj Y β) := by
  intro IsDeRhamClass conj incl
  refine ⟨?closed, ?deRhamClass, ?decomposition, ?vanishing, ?positivity, ?pullback⟩
  case closed =>
    haveI : Smooth (X ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
    obtain ⟨-, -, h⟩ := exists_deRhamCohomology_linearEquiv_singularCohomology
    exact (h X (X ↘ Spec (.of ℂ)) (MMP.Flips.isSmoothScheme_of_smooth _)).2
  case deRhamClass =>
    intro ω
    obtain ⟨α, hα⟩ := exists_isDR hn ω
    exact ⟨α, hα, fun β hβ ↦ IsDR.unique hn hβ hα⟩
  case decomposition => exact existsUnique_decomposition hn
  case vanishing =>
    intro a b ha hb L _
    exact IsDR.mul_mul_pow_eq_zero hn ha hb L
  case positivity =>
    intro ω α hω hα L _ hL
    exact IsDR.exists_pos hn hω hα L hL
  case pullback =>
    intro m hm Y _ _ _ f hf ω α hα
    have hη := IsDR.pullback hn hm Y f hf hα
    exact ⟨⟨_, hη⟩, _, _, hη, pullback_mapCoeff_star _ α⟩

end MMP.Analytic

end
