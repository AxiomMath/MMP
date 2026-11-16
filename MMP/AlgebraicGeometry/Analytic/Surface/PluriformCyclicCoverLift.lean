module

public import Mathlib
public import MMP.Attr
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Analytic.Surface.BirationalTopFormEigenvalue
import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
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
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.DeRham.FormsSectionsAlgebra
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
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
import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
public import MMP.AlgebraicGeometry.StalkValuationRing

/-!
# Lifting a pluriform eigenvector to a top form on its cyclic cover

Let `X` be a smooth projective complex surface, `B` an snc `ℚ`-divisor with all coefficients
less than one, `m > 0` with `mB` integral, and `s ≠ 0` a section of `m(K_X + B)`. Let
`Y_s = ⨆ᵢ Yᵢ` be a resolution of the degree-`m` cyclic cover `z^m = s`, with root form
`ω_s = z · p^* η` (`s = f η^{⊗m}`, `z^m = f`). If a birational self-map `g` of `X` satisfies
`g^* s = λ s` and `ρ^m = λ`, then `z ↦ ρ z · η / g^* η` lifts `g^*` to an automorphism of the
generic algebra `k(X)[z]/(z^m - f) ≅ ∏ᵢ k(Yᵢ)`. It may permute the factors, and it is a
birational self-map of the whole of `Y_s` whose pull-back sends `ω_s` to `ρ ω_s`. Applying the
uniform bound on eigenvalues of birational self-maps on holomorphic two-forms
(`MMP.Fourfold.exists_pow_eq_one_of_birational_surface_top_form_eigenvalue`) to `Y_s`, whose
second Betti number is at most `b`, gives `ρ^N = 1` and hence `λ^N = 1`, with `N > 0` depending
only on `b`.

## Main results

* `MMP.Fourfold.exists_pow_eq_one_of_pluriformPullback_eq_smul`: for every `b` there is `N > 0`
  such that, whenever `Y_s` as above has `b₂(Y_s) ≤ b`, every birational self-map `g` of `X` with
  `g^* s = λ s` lifts, for each `ρ` with `ρ^m = λ`, to a birational self-map of `Y_s` with
  pull-back sending `ω_s` to `ρ ω_s`, and `λ^N = 1`.

## Implementation notes

* `Y_s` is given by its components, as in
  `MMP.Fourfold.exists_cyclicCover_resolution_finrank_le`: a finite family of integral smooth
  projective surfaces `Yᵢ` with dominant `pᵢ : Yᵢ ⟶ X`, holomorphic two-forms `ωᵢ` with
  `ωᵢ^{⊗m} = pᵢ^* s`, and `zᵢ = ωᵢ / pᵢ^* η` generating `∏ᵢ k(Yᵢ)` over `k(X)` with
  `∑ᵢ [k(Yᵢ) : k(X)] = m`. The statement holds for every such resolution.
* A birational map is recorded by its pull-back on function fields
  (`MMP.Fourfold.FunctionFieldEquiv`). A birational self-map of `⨆ᵢ Yᵢ` is a permutation `π` of
  the components with `ℂ`-isomorphisms `σᵢ : k(Y_{π i}) ≃ k(Yᵢ)`. That it lies over `g` means
  `σᵢ ∘ p_{π i}^* = pᵢ^* ∘ g^*` on `k(X)`. That it sends `ω_s` to `ρ ω_s` means
  `σᵢ^* ω_{π i} = ρ ωᵢ` for every `i`.

## References

* [K. Ueno, *Classification theory of algebraic varieties and compact complex spaces*],
  LNM 439, §14.
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollar-mori], § 2.4.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite MMP.Analytic.ComplexPoints MMP
  MMP.Mori

namespace MMP.Fourfold

section FormPull

variable {X X' S S' : Scheme.{0}}

/-- The pull-back `f^* ω` of a global relative `n`-form along a commutative square
`f ≫ p = p' ≫ g`: the unit of `f^* ⊣ f_*` followed by the canonical map
`f^* Ω^n_{X/S} ⟶ Ω^n_{X'/S'}`. -/
private noncomputable def formPull (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
    (h : f ≫ p = p' ≫ g) (n : ℤ)
    (ω : (Scheme.Hom.relativeDifferentialForms p n).val.obj (op ⊤)) :
    (Scheme.Hom.relativeDifferentialForms p' n).val.obj (op ⊤) :=
  (Scheme.Hom.relativeDifferentialFormsMap f p p' g h n).app ⊤
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app ⊤ ω)

end FormPull

/-- The eigen-relation `f^* ω = μ · ι^* ω` on `U` for a two-form `ω` on `Z`. -/
private def IsFormEigen {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (U : Z.Opens)
    (f : U.toScheme ⟶ Z) (hf : f ≫ sZ = U.ι ≫ sZ)
    (ω : (Scheme.Hom.relativeDifferentialForms sZ 2).val.obj (op ⊤)) (μ : ℂ) : Prop :=
  formPull f sZ (U.ι ≫ sZ) (𝟙 _) (by simp [hf]) 2 ω =
    (show U.toScheme.ringCatSheaf.obj.obj (op ⊤) from
        (U.ι ≫ sZ).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv μ)) •
      formPull U.ι sZ (U.ι ≫ sZ) (𝟙 _) (by simp) 2 ω

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
  let := (f.appLE V.1 W.1 e).hom.toAlgebra
  have : Algebra.Smooth Γ(S, V.1) Γ(X, W.1) := hsm
  have : Module.Projective Γ(X, W.1) (CommRingCat.KaehlerDifferential (f.appLE V.1 W.1 e)) :=
    inferInstanceAs (Module.Projective Γ(X, W.1) Ω[Γ(X, W.1)⁄Γ(S, V.1)])
  have := projective_exteriorPower (R := Γ(X, W.1))
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
  rw [show X.presheaf.map (homOfLE (le_refl W)).op g = g by simp] at hk
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
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f d
  refine eq_zero_of_res_eq_zero_of_isSMulRegular _ (fun W hWne g hg => ?_) s hO hs
  have : Nonempty W.1 := hWne.to_subtype
  have : IsDomain Γ(X, W.1) := inferInstance
  have := projective_sections_forms f W ⟨⊤, isAffineOpen_top S⟩ (by simp) d
  exact Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero hg)

end DenseOpen

/-! ### Rational forms of global forms -/

/-- Every point of an open `V` lies in an affine open contained in `V`. -/
private theorem exists_affineOpens_le {Y : Scheme.{u}} (V : Y.Opens) {y : Y} (hy : y ∈ V) :
    ∃ W : Y.affineOpens, (W : Y.Opens) ≤ V ∧ y ∈ (W : Y.Opens) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
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
private theorem pullAffine_zero_eq (q : ℕ) (W : X.affineOpens) (W' : X'.affineOpens)
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
    (pullAffine_zero_eq sX sX' g hg q W W' h) (pullAffine_add_eq sX sX' g hg q W W' h)
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

open KaehlerDifferential

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

/-- The image in `Ω^n_{k(X)/k}` of a form over a nonempty affine open `W`. -/
private noncomputable def chartVal (n : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (x : Γ(sX.relativeDifferentialForms (n : ℤ), W)) :
    letI := functionFieldAlgebra sX
    ⋀[X.functionField]^n Ω[X.functionField⁄k] :=
  letI := sectionAlgebra sX W
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_section_functionField sX (W : X.Opens)
  topFormsMap k Γ(X, W) X.functionField n (MMP.DeRham.formsAlgEquiv sX n W x)

/-- The image in `Ω^n_{k(X)/k}` does not change under restriction to a smaller affine open. -/
private theorem chartVal_res (n : ℕ) {W W' : X.affineOpens} [Nonempty (W : X.Opens)]
    [Nonempty (W' : X.Opens)] (h : (W' : X.Opens) ≤ W)
    (x : Γ(sX.relativeDifferentialForms (n : ℤ), W)) :
    chartVal sX n W' ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map (homOfLE h).op x) =
      chartVal sX n W x := by
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
  have e := MMP.DeRham.formsAlgEquiv_restrict sX n h x
  exact (congrArg (topFormsMap k Γ(X, W') X.functionField n) e).trans
    (topFormsMap_mapExteriorPower n _)

/-- The image in `Ω^n_{k(X)/k}` of a global form, read on a nonempty affine open. -/
private noncomputable def chartForm (n : ℕ) (W : X.affineOpens) [Nonempty (W : X.Opens)]
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    letI := functionFieldAlgebra sX
    ⋀[X.functionField]^n Ω[X.functionField⁄k] :=
  chartVal sX n W ((sX.relativeDifferentialForms (n : ℤ)).presheaf.map (homOfLE le_top).op ω)

private theorem chartForm_of_le (n : ℕ) {W W' : X.affineOpens} [Nonempty (W : X.Opens)]
    [Nonempty (W' : X.Opens)] (h : (W' : X.Opens) ≤ W)
    (ω : Γ(sX.relativeDifferentialForms (n : ℤ), ⊤)) :
    chartForm sX n W' ω = chartForm sX n W ω := by
  rw [chartForm, chartForm, ← chartVal_res sX n h, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

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
  have : Nonempty (W₀ : X.Opens) := ⟨⟨y, hyW₀⟩⟩
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

/-- Elements of a local ring have nonnegative order. -/
private theorem ord_algebraMap_stalk_nonneg {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (a : X.presheaf.stalk x) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.exists_germ_eq (x := x) a
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxV]
  by_cases hs : s = 0
  · simp [hs]
  have h1 := Scheme.ord_le_smul hxV hs (1 : X.functionField)
  have h2 : X.ord (1 : X.functionField) x = 0 := by
    have := Scheme.ord_of_isUnit (U := V) (f := 1) isUnit_one hxV
    rwa [map_one] at this
  rw [h2] at h1
  convert h1 using 2
  rw [Algebra.smul_def, mul_one]
  rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

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

/-- The map `c ↦ c^{⊗1}` from `Ω^d_{K/k}` to `1`-pluriforms is injective. -/
private theorem formPow_one_injective {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ} :
    Function.Injective
      (fun c : ⋀[K]^d Ω[K⁄k] => (formPow c 1 : PluriForms k K d (1 : ℕ))) := by
  intro a b h
  have := congrArg (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Fin 1 => ⋀[K]^d Ω[K⁄k])
    (0 : Fin 1)) h
  simpa [formPow, PiTensorProduct.subsingletonEquiv_apply_tprod] using this

/-- A tensor power of exponent one of a nonzero vector is nonzero. -/
private theorem formPow_one_ne_zero {k K : Type*} [CommRing k] [Field K] [Algebra k K] {d : ℕ}
    {c : ⋀[K]^d Ω[K⁄k]} (hc : c ≠ 0) :
    (MMP.Fourfold.formPow c 1 : PluriForms k K d (1 : ℕ)) ≠ 0 := fun h =>
  hc (formPow_one_injective (k := k) (h.trans (by
    change (0 : PluriForms k K d (1 : ℕ)) = MMP.Fourfold.formPow 0 1
    rw [← zero_smul K (0 : ⋀[K]^d Ω[K⁄k]), MMP.Fourfold.formPow_smul, zero_pow one_ne_zero,
      zero_smul])))

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

omit [IsIntegral X] in
/-- A nonempty open of the target has a nonempty preimage under a dominant morphism. -/
private theorem exists_affineOpens_le_preimage {T : Scheme.{u}} (h : T ⟶ X) [IsDominant h]
    (W : X.Opens) [Nonempty W] :
    ∃ W' : T.affineOpens, (W' : T.Opens) ≤ h ⁻¹ᵁ W ∧ Nonempty (W' : T.Opens) := by
  obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty W)
  obtain ⟨y, hy⟩ : (h ⁻¹ᵁ W : Set T).Nonempty := h.denseRange.exists_mem_open W.isOpen ⟨x, hx⟩
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
  unfold ratForm chartForm chartVal
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

section Hom

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
      let := functionFieldMapAlgebra h
      have := isScalarTower_functionFieldMap sX h
      exact (IsScalarTower.algebraMap_apply k X.functionField T.functionField c).symm }

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

end Hom

section Algebra

open Polynomial

/-- A unital ring endomorphism of a finite product of fields factors, on each coordinate `i`,
through a single coordinate `π0 i`, the one whose idempotent `Pi.single (π0 i) 1` maps to `1`. -/
private theorem exists_coord_ringHom_apply {ι : Type*} [Finite ι] [DecidableEq ι]
    {L : ι → Type*} [∀ i, Field (L i)] (Φ : (∀ i, L i) →+* (∀ i, L i)) :
    ∃ π0 : ι → ι, (∀ i, Φ (Pi.single (π0 i) 1) i = 1) ∧
      ∀ x i, Φ x i = Φ (Pi.single (π0 i) (x (π0 i))) i := by
  classical
  have := Fintype.ofFinite ι
  let e : ι → ∀ i, L i := fun j => Pi.single j 1
  have hsum : ∀ i, ∑ j, Φ (e j) i = 1 := by
    intro i
    have : ∑ j, e j = 1 := by
      ext l
      simp [e, Finset.sum_apply]
    rw [← Finset.sum_apply, ← map_sum, this, map_one, Pi.one_apply]
  have hex : ∀ i, ∃ j, Φ (e j) i ≠ 0 := by
    intro i
    by_contra! h
    simpa [h] using hsum i
  choose π0 hπ0 using hex
  have hidem : ∀ j i, Φ (e j) i * Φ (e j) i = Φ (e j) i := by
    intro j i
    rw [← Pi.mul_apply, ← map_mul]
    simp only [e, ← Pi.single_mul, mul_one]
  have hone : ∀ i, Φ (e (π0 i)) i = 1 := by
    intro i
    have h := hidem (π0 i) i
    have h' : Φ (e (π0 i)) i * (Φ (e (π0 i)) i - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact absurd h0 (hπ0 i)
    · exact sub_eq_zero.mp h1
  have hred : ∀ x i, Φ x i = Φ (Pi.single (π0 i) (x (π0 i))) i := by
    intro x i
    have hx : x - Pi.single (π0 i) (x (π0 i)) = x * (1 - e (π0 i)) := by
      ext l
      rcases eq_or_ne l (π0 i) with rfl | h
      · simp [e]
      · simp [e, h]
    have := congrArg (fun y => Φ y i) hx
    simp only [map_sub, map_mul, Pi.sub_apply, Pi.mul_apply, map_one, Pi.one_apply, hone,
      sub_self, mul_zero] at this
    exact sub_eq_zero.mp this
  exact ⟨π0, hone, hred⟩

/-- A ring automorphism of a finite product of fields permutes the factors: the coordinate `i` of
the image only depends on the coordinate `π i` of the argument, through an isomorphism of
fields. -/
private theorem exists_perm_ringEquiv_apply {ι : Type*} [Finite ι]
    {L : ι → Type*} [∀ i, Field (L i)] (Φ : (∀ i, L i) ≃+* (∀ i, L i)) :
    ∃ (π : Equiv.Perm ι) (σ : ∀ i, L (π i) ≃+* L i), ∀ x i, Φ x i = σ i (x (π i)) := by
  classical
  obtain ⟨π0, hone, hred⟩ := exists_coord_ringHom_apply Φ.toRingHom
  let e : ι → ∀ i, L i := fun j => Pi.single j 1
  let σ0 : ∀ i, L (π0 i) →+* L i := fun i =>
    { toFun := fun y => Φ (Pi.single (π0 i) y) i
      map_one' := hone i
      map_mul' := fun y y' => by
        change Φ (Pi.single _ (y * y')) i = Φ (Pi.single _ y) i * Φ (Pi.single _ y') i
        rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul]
      map_zero' := by
        change Φ (Pi.single _ 0) i = 0
        simp
      map_add' := fun y y' => by
        change Φ (Pi.single _ (y + y')) i = Φ (Pi.single _ y) i + Φ (Pi.single _ y') i
        rw [← Pi.add_apply, ← map_add, ← Pi.single_add] }
  have hσ0 : ∀ x i, Φ x i = σ0 i (x (π0 i)) := hred
  have hsurj : Function.Surjective π0 := by
    intro j
    by_contra! h
    have h0 : Φ (e j) = 0 := by
      ext i
      rw [hσ0, Pi.zero_apply]
      simp [e, Ne.symm (h i)]
    have : e j = 0 := Φ.injective (h0.trans (map_zero Φ).symm)
    have := congrFun this j
    simp [e] at this
  have hσbij : ∀ i, Function.Bijective (σ0 i) := by
    intro i
    refine ⟨(σ0 i).injective, fun y => ?_⟩
    refine ⟨Φ.symm (Pi.single i y) (π0 i), ?_⟩
    rw [← hσ0, RingEquiv.apply_symm_apply]
    simp
  exact ⟨Equiv.ofBijective π0 ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩,
    fun i => RingEquiv.ofBijective (σ0 i) (hσbij i), fun x i => hσ0 x i⟩

/-- Ring homomorphisms out of an algebra generated by `z` agree once they agree on the base and
on `z`. -/
private theorem ringHom_ext_of_adjoin_eq_top {K A B : Type*} [CommRing K] [CommRing A]
    [Semiring B] [Algebra K A] {z : A} (hz : Algebra.adjoin K {z} = ⊤) {Φ Ψ : A →+* B}
    (h1 : ∀ a, Φ (algebraMap K A a) = Ψ (algebraMap K A a)) (h2 : Φ z = Ψ z) : Φ = Ψ := by
  ext x
  have hx : x ∈ Algebra.adjoin K {z} := hz ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rwa [Set.mem_singleton_iff.mp hy]
  | algebraMap a => exact h1 a
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

/-- An algebra of dimension `m` over a field `K` generated by an `m`-th root `z` of `f ∈ K` is
`K[T]/(T^m - f)`; so a ring homomorphism `g : K → K` extends to it by `z ↦ w` for every `m`-th
root `w` of `g f`. -/
private theorem exists_ringHom_of_adjoin_eq_top {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] {m : ℕ} (hm : 0 < m) (hdim : Module.finrank K A = m) {z : A}
    (hz : Algebra.adjoin K {z} = ⊤) {f : K} (hzf : z ^ m = algebraMap K A f) (g : K →+* K)
    (w : A) (hw : w ^ m = algebraMap K A (g f)) :
    ∃ Φ : A →+* A, (∀ a, Φ (algebraMap K A a) = algebraMap K A (g a)) ∧ Φ z = w := by
  have hmon : (Polynomial.X ^ m - Polynomial.C f).Monic := monic_X_pow_sub_C f hm.ne'
  have hdeg : (Polynomial.X ^ m - Polynomial.C f).natDegree = m := natDegree_X_pow_sub_C
  have haev : aeval z (Polynomial.X ^ m - Polynomial.C f) = 0 := by simp [hzf]
  let φ := AdjoinRoot.liftAlgHom (Polynomial.X ^ m - Polynomial.C f) (Algebra.ofId K A) z haev
  have hroot : φ (AdjoinRoot.root _) = z := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurj : Function.Surjective φ := by
    have : (⊤ : Subalgebra K A) ≤ φ.range := by
      rw [← hz, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact ⟨AdjoinRoot.root _, hroot⟩
    exact fun _ => this Algebra.mem_top
  have : FiniteDimensional K A := Module.finite_of_finrank_pos (hdim ▸ hm)
  have hfr : Module.finrank K (AdjoinRoot (Polynomial.X ^ m - Polynomial.C f)) =
      Module.finrank K A := by
    rw [(AdjoinRoot.powerBasis' hmon).finrank, AdjoinRoot.powerBasis'_dim, hdeg, hdim]
  have : FiniteDimensional K (AdjoinRoot (Polynomial.X ^ m - Polynomial.C f)) :=
    (AdjoinRoot.powerBasis' hmon).finite
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr (f := φ.toLinearMap)).mpr hsurj
  let e := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hev : eval₂ ((algebraMap K A).comp g) w (Polynomial.X ^ m - Polynomial.C f) = 0 := by
    simp [hw]
  refine ⟨(AdjoinRoot.lift ((algebraMap K A).comp g) w hev).comp e.symm.toRingEquiv.toRingHom,
    fun a => ?_, ?_⟩
  · change AdjoinRoot.lift _ w hev (e.symm (algebraMap K A a)) = _
    rw [AlgEquiv.commutes]
    exact AdjoinRoot.lift_of hev
  · change AdjoinRoot.lift _ w hev (e.symm z) = w
    rw [show e.symm z = AdjoinRoot.root _ from (AlgEquiv.symm_apply_eq _).mpr hroot.symm]
    exact AdjoinRoot.lift_root hev

/-- **Lifting automorphisms to a cyclic algebra.** Let `A` be an algebra of dimension `m` over a
field `K`, generated by `z` with `z^m = f ∈ K`. If an automorphism `g` of `K` satisfies
`g f = u^m f` for a unit `u`, then `g` extends to an automorphism of `A` with `z ↦ u z`. -/
private theorem exists_ringEquiv_of_adjoin_eq_top {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] {m : ℕ} (hm : 0 < m) (hdim : Module.finrank K A = m) {z : A}
    (hz : Algebra.adjoin K {z} = ⊤) {f : K} (hzf : z ^ m = algebraMap K A f) (g : K ≃+* K)
    {u : K} (hu : u ≠ 0) (hgu : g f = u ^ m * f) :
    ∃ Φ : A ≃+* A, (∀ a, Φ (algebraMap K A a) = algebraMap K A (g a)) ∧
      Φ z = algebraMap K A u * z := by
  obtain ⟨Φ, hΦa, hΦz⟩ := exists_ringHom_of_adjoin_eq_top hm hdim hz hzf g.toRingHom
    (algebraMap K A u * z) (by rw [mul_pow, hzf, ← map_pow, ← map_mul, ← hgu]; rfl)
  have hu' : g.symm u ≠ 0 := by simpa using hu
  have hf : g.symm f = (g.symm u)⁻¹ ^ m * f := by
    have := congrArg g.symm hgu
    rw [RingEquiv.symm_apply_apply, map_mul, map_pow] at this
    rw [inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hu'), ← this]
  obtain ⟨Ψ, hΨa, hΨz⟩ := exists_ringHom_of_adjoin_eq_top hm hdim hz hzf g.symm.toRingHom
    (algebraMap K A (g.symm u)⁻¹ * z) (by rw [mul_pow, hzf, ← map_pow, ← map_mul, ← hf]; rfl)
  have h1 : Ψ.comp Φ = RingHom.id A := by
    refine ringHom_ext_of_adjoin_eq_top hz (fun a => ?_) ?_
    · simp [hΦa, hΨa]
    · simp only [RingHom.coe_comp, Function.comp_apply, hΦz, map_mul, hΨa, hΨz, RingHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp [hu']
  have h2 : Φ.comp Ψ = RingHom.id A := by
    refine ringHom_ext_of_adjoin_eq_top hz (fun a => ?_) ?_
    · simp [hΦa, hΨa]
    · simp only [RingHom.coe_comp, Function.comp_apply, hΨz, map_mul, hΦa, hΦz, RingHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp [hu]
  exact ⟨RingEquiv.ofRingHom Φ Ψ h2 h1, hΦa, hΦz⟩

end Algebra

section Lift

variable {k : Type u} [Field k] {X X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']

/-- Pluriform pull-back is semilinear along the homomorphism of function fields. -/
private theorem pluriformPullback_smul_left (φ : FunctionFieldHom sX sX') {d : ℕ} {m : ℤ}
    (c : X'.functionField) (τ : RationalPluriForms sX' d m) :
    pluriformPullback sX sX' φ d m (c • τ) = φ c • pluriformPullback sX sX' φ d m τ := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_smul (K := X'.functionField) (K' := X.functionField) c τ

/-- Along a homomorphism of function fields of varieties of the same dimension in characteristic
zero, the pull-back of `e ω'^{⊗a}` is `φ(e) c^a ω^{⊗a}`, for generators `ω'`, `ω` of the lines of
top forms and a fixed `c ≠ 0`. -/
private theorem exists_pluriformPullback_smul_formPow_eq [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    {ω' : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k]}
    (hω' : letI := functionFieldAlgebra sX'; Submodule.span X'.functionField {ω'} = ⊤)
    (hω'0 : ω' ≠ 0)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]}
    (hω : letI := functionFieldAlgebra sX; Submodule.span X.functionField {ω} = ⊤) :
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX
    ∃ c : X.functionField, c ≠ 0 ∧ ∀ (a : ℕ) (e : X'.functionField),
      pluriformPullback sX sX' φ d a (e • formPow ω' a) = (φ e * c ^ a) • formPow ω a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have hgen := isPullbackGenerator_functionFieldHom hX hX' φ hω' hω'0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hω ▸ Submodule.mem_top (x := topFormsMap k X'.functionField X.functionField d ω'))
  refine ⟨c, ?_, fun a e => ?_⟩
  · rintro rfl
    exact hgen.2.2 (by rw [← hc, zero_smul])
  · rw [pluriformPullback_smul_formPow φ hgen a e, ← hc, formPow_smul, smul_smul]

/-- Along a homomorphism of function fields of varieties of the same dimension in characteristic
zero, the pull-back of `e ω'^{⊗a}` is `φ(e) c^a ω^{⊗a}` for a top form `ω` with nonzero powers and
a fixed `c ≠ 0`. -/
private theorem exists_formPow_ne_zero_pluriformPullback_eq [CharZero k]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    {ω' : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k]}
    (hω' : letI := functionFieldAlgebra sX'; Submodule.span X'.functionField {ω'} = ⊤)
    (hω'0 : ω' ≠ 0) :
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX
    ∃ (ω : ⋀[X.functionField]^d Ω[X.functionField⁄k]) (c : X.functionField), c ≠ 0 ∧
      (∀ a : ℕ, (formPow ω a : RationalPluriForms sX d a) ≠ 0) ∧
      ∀ (a : ℕ) (e : X'.functionField),
        pluriformPullback sX sX' φ d a (e • formPow ω' a) = (φ e * c ^ a) • formPow ω a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  obtain ⟨B⟩ := exists_basis_topForms (sX := sX) hX
  have hB : Submodule.span X.functionField {B ()} = ⊤ := by
    have := B.span_eq
    rwa [Set.range_unique] at this
  obtain ⟨c, hc0, hc⟩ := exists_pluriformPullback_smul_formPow_eq hX hX' φ hω' hω'0 hB
  refine ⟨B (), c, hc0, fun a => ?_, hc⟩
  have := (ZTensorPower.basis B a).ne_zero ()
  rwa [ZTensorPower.basis_natCast] at this

end Lift

/-- If `b c^m = ρ^m f` with `b, c ≠ 0`, then `b = u^m f` for the nonzero `u = ρ c⁻¹`. -/
private theorem eq_pow_mul_of_mul_pow_eq {K : Type*} [Field K] {m : ℕ} (hm : 0 < m)
    {b c f l ρ : K} (hb : b ≠ 0) (hc : c ≠ 0) (h : b * c ^ m = l * f) (hρ : ρ ^ m = l) :
    ρ * c⁻¹ ≠ 0 ∧ b = (ρ * c⁻¹) ^ m * f := by
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hρ
    rw [← hρ, zero_mul] at h
    exact mul_ne_zero hb (pow_ne_zero _ hc) h
  refine ⟨mul_ne_zero hρ0 (inv_ne_zero hc), ?_⟩
  rw [mul_pow, inv_pow, hρ]
  field_simp
  linear_combination h

/-- **The lift of a pluriform eigenvector to the cyclic cover.** In the setting of the cyclic
cover `z^m = s`, a birational self-map `g` with `g^* s = λ s` and a root `ρ^m = λ` lift to a
permutation `π` of the components with isomorphisms `σᵢ : k(Y_{π i}) ≃ k(Yᵢ)` over `g^*`,
multiplying the root forms by `ρ`. -/
private theorem exists_perm_lift {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : topologicalKrullDim X = 2)
    {m : ℕ} (hm : 0 < m) (s : RationalPluriForms sX 2 m) (hs0 : s ≠ 0)
    {k : ℕ} (Y : Fin k → Scheme.{0}) [∀ i, IsIntegral (Y i)]
    (p : ∀ i, Y i ⟶ X) [∀ i, IsDominant (p i)] [∀ i, LocallyOfFiniteType (p i ≫ sX)]
    (hY : ∀ i, topologicalKrullDim (Y i) = 2) :
      letI := fun i => functionFieldAlgebra (p i ≫ sX)
      ∀ ω : ∀ i, ⋀[(Y i).functionField]^2 Ω[(Y i).functionField⁄ℂ],
        (∀ i, (formPow (ω i) m : RationalPluriForms (p i ≫ sX) 2 m) =
          pullbackRationalPluriForms sX (p i) s) →
        letI := functionFieldAlgebra sX
        letI := fun i => functionFieldMapAlgebra (p i)
        ∀ η : ⋀[X.functionField]^2 Ω[X.functionField⁄ℂ], η ≠ 0 →
        ∀ z : ∀ i, (Y i).functionField,
          (∀ i, (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) =
            z i • pullbackRationalPluriForms sX (p i)
              (show RationalPluriForms sX 2 (1 : ℕ) from formPow η 1)) →
          Algebra.adjoin X.functionField {z} = ⊤ →
          Module.finrank X.functionField (∀ i, (Y i).functionField) = m →
        ∀ (g : FunctionFieldEquiv sX sX) (lam : ℂ),
          pluriformPullback sX sX g.toHom 2 m s = lam • s →
          (∀ ρ : ℂ, ρ ^ m = lam →
            ∃ (π : Equiv.Perm (Fin k))
              (σ : ∀ i, FunctionFieldEquiv (p i ≫ sX) (p (π i) ≫ sX)),
              (∀ i (f : X.functionField),
                σ i (algebraMap X.functionField (Y (π i)).functionField f) =
                  algebraMap X.functionField (Y i).functionField (g f)) ∧
              ∀ i, pluriformPullback (p i ≫ sX) (p (π i) ≫ sX) (σ i).toHom 2 (1 : ℕ)
                  (formPow (ω (π i)) 1) =
                ρ • (show RationalPluriForms (p i ≫ sX) 2 (1 : ℕ) from formPow (ω i) 1)) := by
  let := fun i => functionFieldAlgebra (p i ≫ sX)
  let := functionFieldAlgebra sX
  let := fun i => functionFieldMapAlgebra (p i)
  intro ω hωm η hη0 z hz hadj hdeg g lam hg ρ hρ
  classical
  let φ : ∀ i, FunctionFieldHom (p i ≫ sX) sX := fun i => ffHom (sX := sX) (p i) rfl
  have hpb : ∀ i {a : ℤ} (τ : RationalPluriForms sX 2 a),
      pullbackRationalPluriForms sX (p i) τ = pluriformPullback (p i ≫ sX) sX (φ i) 2 a τ :=
    fun i a τ => rfl
  -- the line of top forms of `k(X)`
  obtain ⟨B₀⟩ := exists_basis_topForms (sX := sX) hX
  have hfin : Module.finrank X.functionField (⋀[X.functionField]^2 Ω[X.functionField⁄ℂ]) = 1 :=
    Module.finrank_eq_card_basis B₀ |>.trans (by simp)
  have hspan : Submodule.span X.functionField {η} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero η hη0).mp hfin
  let B := basisOfSpanSingleton hspan hη0
  have hB : B () = η := basisOfSpanSingleton_apply _ _ _
  -- `s = f η^{⊗m}`
  set f : X.functionField := (ZTensorPower.basis B m).repr s ()
  have hsf : s = f • (formPow η m : RationalPluriForms sX 2 m) := by
    have := eq_repr_smul_formPow B s
    rwa [hB] at this
  have hηpow : ∀ a : ℕ, (formPow η a : RationalPluriForms sX 2 a) ≠ 0 := fun a => by
    have := (ZTensorPower.basis B a).ne_zero ()
    rwa [ZTensorPower.basis_natCast, hB] at this
  have hf0 : f ≠ 0 := fun h => hs0 <| by
    rw [hsf, h]
    exact zero_smul _ _
  -- the pull-backs to the components
  choose ηY cY hcY0 hηY0 hpbη using fun i =>
    exists_formPow_ne_zero_pluriformPullback_eq (hY i) hX (φ i) hspan hη0
  have hωz : ∀ i, ω i = (z i * cY i) • ηY i := by
    intro i
    apply formPow_one_injective (k := ℂ)
    have h := hz i
    rw [hpb, ← one_smul X.functionField (formPow η 1), hpbη, map_one, one_mul, pow_one] at h
    change (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) = formPow _ 1
    rw [formPow_smul, pow_one, mul_smul]
    exact h
  have hzm : ∀ i, z i ^ m = φ i f := by
    intro i
    have h := hωm i
    rw [hpb, hsf, hpbη, hωz, formPow_smul, mul_pow] at h
    exact mul_right_cancel₀ (pow_ne_zero _ (hcY0 i)) (smul_left_injective _ (hηY0 i m) h)
  -- `g^* η = c η`
  obtain ⟨c, hc0, hpbg⟩ := exists_pluriformPullback_smul_formPow_eq hX hX g.toHom hspan hη0 hspan
  -- `g f · c^m = λ f`
  have hgf : g f * c ^ m = algebraMap ℂ X.functionField lam * f := by
    rw [hsf, hpbg] at hg
    have h' : ((g f * c ^ m) • formPow η m : RationalPluriForms sX 2 m) =
        (algebraMap ℂ X.functionField lam * f) • formPow η m := by
      refine hg.trans ?_
      rw [mul_smul]
      rfl
    exact smul_left_injective _ (hηpow m) h'
  set ρK := algebraMap ℂ X.functionField ρ with hρK_def
  have hρK : ρK ^ m = algebraMap ℂ X.functionField lam := by rw [hρK_def, ← map_pow, hρ]
  obtain ⟨hu0, hgu⟩ := eq_pow_mul_of_mul_pow_eq hm (by simpa using hf0) hc0 hgf hρK
  set u := ρK * c⁻¹ with hu_def
  -- the lift to the cyclic algebra
  have hzf : z ^ m = algebraMap X.functionField (∀ i, (Y i).functionField) f := by
    funext i
    rw [Pi.pow_apply, hzm]
    rfl
  obtain ⟨Φ, hΦa, hΦz⟩ := exists_ringEquiv_of_adjoin_eq_top hm hdeg hadj hzf
    g.toRingEquiv hu0 hgu
  obtain ⟨π, σ0, hσ0⟩ := exists_perm_ringEquiv_apply Φ
  have hover : ∀ i a, σ0 i (algebraMap X.functionField (Y (π i)).functionField a) =
      algebraMap X.functionField (Y i).functionField (g a) := by
    intro i a
    have := hσ0 (algebraMap X.functionField _ a) i
    rwa [hΦa, eq_comm] at this
  let σ : ∀ i, FunctionFieldEquiv (p i ≫ sX) (p (π i) ≫ sX) := fun i =>
    { σ0 i with
      commutes' := fun c => by
        have h1 := isScalarTower_functionFieldMap sX (p (π i))
        have h2 := isScalarTower_functionFieldMap sX (p i)
        change σ0 i (algebraMap ℂ _ c) = algebraMap ℂ _ c
        rw [IsScalarTower.algebraMap_apply ℂ X.functionField (Y (π i)).functionField, hover,
          AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply] }
  refine ⟨π, σ, hover, fun i => ?_⟩
  have hcomp : (σ i).toHom.comp (φ (π i)) = (φ i).comp g.toHom := by
    ext a
    exact hover i a
  have hσz : FunctionFieldEquiv.toHom (p i ≫ sX) (p (π i) ≫ sX) (σ i) (z (π i)) =
      φ i u * z i := by
    have := hσ0 z i
    rwa [hΦz, eq_comm] at this
  have hg1 : pluriformPullback sX sX g.toHom 2 (1 : ℕ) (formPow η 1) =
      c • (show RationalPluriForms sX 2 (1 : ℕ) from formPow η 1) := by
    have := hpbg 1 1
    rwa [one_smul, map_one, one_mul, pow_one] at this
  rw [hz (π i), pluriformPullback_smul_left, hpb, pluriformPullback_comp (hY i) (hY (π i)) hX,
    hcomp, ← pluriformPullback_comp (hY i) hX hX, hg1, pluriformPullback_smul_left]
  dsimp only
  rw [hz i]
  dsimp only
  rw [hσz, smul_smul, RationalPluriForms.smul_def, smul_smul]
  congr 1
  have hρ' : algebraMap ℂ (Y i).functionField ρ = φ i ρK := ((φ i).commutes ρ).symm
  have hc' : φ i c ≠ 0 := (map_ne_zero (φ i)).mpr hc0
  rw [hρ', hu_def, map_mul, map_inv₀]
  field_simp

section Hartogs

open KaehlerDifferential

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]

/-- Along a prime divisor `Γ` whose generic point lies in the affine open `W`, a rational top form
with nonnegative order along every prime divisor becomes, after multiplication by some `u ∉ 𝔭_Γ`,
the image of an algebraic form of `Γ(Y, W)`. -/
private theorem exists_topFormsMap_eq_smul_of_genericPoint_mem [Smooth sY] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [PerfectField k] {n : ℕ} (hn : topologicalKrullDim Y = n)
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄k])
    (hω : letI := functionFieldAlgebra sY
      ∀ Γ : MMP.Mori.PrimeDivisor Y,
        0 ≤ Γ.ordForm (show RationalPluriForms sY n (1 : ℕ) from formPow ω 1))
    (hω0 : letI := functionFieldAlgebra sY; ω ≠ 0) (W : Y.affineOpens) [Nonempty (W : Y.Opens)]
    (Γ : MMP.Mori.PrimeDivisor Y) (hη : Γ.genericPoint ∈ (W : Y.Opens)) :
    letI := sectionAlgebra sY W
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_section_functionField sY (W : Y.Opens)
    ∃ u ∈ (W.2.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl,
      ∃ p' : ⋀[Γ(Y, W)]^n Ω[Γ(Y, W)⁄k], topFormsMap k Γ(Y, W) Y.functionField n p' = u • ω := by
  classical
  let := sectionAlgebra sY W
  let := functionFieldAlgebra sY
  have := isScalarTower_section_functionField sY (W : Y.Opens)
  have : Algebra.Smooth k Γ(Y, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra sY W.2
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W W.2
  have := finiteType_sectionAlgebra sY W.2
  let := stalkAlgebra sY Γ.genericPoint
  have := isScalarTower_stalk_functionField sY Γ.genericPoint
  let : Algebra Γ(Y, W) Γ.localRing :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨_, hη⟩ : (W : Y.Opens))
  have := isScalarTower_section_stalk sY W ⟨_, hη⟩
  have : IsScalarTower Γ(Y, W) Γ.localRing Y.functionField :=
    functionField_isScalarTower Y W ⟨_, hη⟩
  have hlocO := W.2.isLocalization_stalk ⟨_, hη⟩
  -- a generator of the top forms of the local ring along `Γ`
  obtain ⟨hfree, hfin⟩ := Γ.free_kaehlerDifferential_localRing (sX := sY)
  have := essFiniteType_functionField (sX := sY)
  have hK : Module.finrank Y.functionField Ω[Y.functionField⁄k] = n :=
    (finrank_kaehlerDifferential_eq_trdeg k Y.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have hO : Module.finrank Γ.localRing Ω[Γ.localRing⁄k] = n :=
    (finrank_kaehlerDifferential_eq_of_isFractionRing (K := Y.functionField)).symm.trans hK
  obtain ⟨σ, hσ, h0⟩ := exists_topForms_generator_of_free (K := Y.functionField) hO
  -- `ω = c σ` with `c` regular along `Γ`
  set cω := formCoeff Γ.localRing hσ h0
    (formPow ω 1 : PluriForms k Y.functionField n (1 : ℕ)) with hcω
  have hωc : ω = cω • topFormsMap k Γ.localRing Y.functionField n σ := by
    apply formPow_one_injective (k := k)
    have := formCoeff_smul_basis hσ h0 (formPow ω 1 : PluriForms k Y.functionField n (1 : ℕ))
    rw [ZTensorPower.basis_natCast, topFormsBasis_apply] at this
    change (formPow ω 1 : PluriForms k Y.functionField n (1 : ℕ)) = formPow _ 1
    rw [formPow_smul, pow_one]
    exact this.symm
  have hord : 0 ≤ Y.ord cω Γ.genericPoint := by
    have := hω Γ
    rwa [Γ.ordForm_eq _ hσ h0] at this
  have hcω0 : cω ≠ 0 := by
    rintro h
    apply hω0
    rw [hωc, h, zero_smul]
  obtain ⟨c', hc'⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord
    Γ.genericPoint hcω0 (fun Γ' hΓ' => by
      have hsp : Γ'.genericPoint ⤳ Γ.genericPoint := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hΓ'
      rw [MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes hsp]
      exact hord)
  -- `c' σ` comes from `Ω^n_{Γ(Y, W)}` after inverting `u ∉ 𝔭`
  have hlocF := MMP.DeRham.isLocalizedModule_mapExteriorPower_of_isLocalization (A := k)
    (L := Γ(Y, W)) (L' := Γ.localRing) (W.2.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl n
  obtain ⟨⟨p', u⟩, hpu⟩ := IsLocalizedModule.surj (W.2.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl
    (mapExteriorPower k Γ(Y, W) Γ.localRing n) (c' • σ)
  refine ⟨u.1, u.2, p', ?_⟩
  rw [← topFormsMap_mapExteriorPower (B := Γ.localRing) n p']
  change topFormsMap k Γ.localRing Y.functionField n
    (mapExteriorPower k Γ(Y, W) Γ.localRing n p') = _
  rw [← hpu, LinearMap.map_smul_of_tower, map_smul, ← algebraMap_smul Y.functionField c',
    hc', ← hωc]
  rfl

/-- A quotient `x / u` with `u ∉ 𝔭_Γ` has nonnegative order along the prime divisor `Γ`. -/
private theorem zero_le_ord_div_of_mem_primeCompl [IsLocallyNoetherian Y] (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)]
    (Γ : MMP.Mori.PrimeDivisor Y) (hη : Γ.genericPoint ∈ (W : Y.Opens)) (x : Γ(Y, W))
    {u : Γ(Y, W)} (hu : u ∈ (W.2.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl) :
    0 ≤ Y.ord (algebraMap Γ(Y, W) Y.functionField x / algebraMap Γ(Y, W) Y.functionField u)
      Γ.genericPoint := by
  let : Algebra Γ(Y, W) Γ.localRing :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨_, hη⟩ : (W : Y.Opens))
  have : IsScalarTower Γ(Y, W) Γ.localRing Y.functionField :=
    functionField_isScalarTower Y W ⟨_, hη⟩
  have hlocO := W.2.isLocalization_stalk ⟨_, hη⟩
  have hu' : IsUnit (algebraMap Γ(Y, W) Γ.localRing u) := IsLocalization.map_units
    (M := (W.2.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl) Γ.localRing ⟨u, hu⟩
  have hu0 : algebraMap Γ(Y, W) Y.functionField u ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply Γ(Y, W) Γ.localRing Y.functionField]
    exact (hu'.map _).ne_zero
  have hval : algebraMap Γ(Y, W) Y.functionField x / algebraMap Γ(Y, W) Y.functionField u =
      algebraMap Γ.localRing Y.functionField
        (algebraMap Γ(Y, W) Γ.localRing x * ↑hu'.unit⁻¹) := by
    rw [div_eq_iff hu0, IsScalarTower.algebraMap_apply Γ(Y, W) Γ.localRing Y.functionField u,
      ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, ← IsScalarTower.algebraMap_apply]
  rw [hval]
  exact ord_algebraMap_stalk_nonneg _ _

/-- On a normal integral scheme, a quotient `x / t` of sections over a nonempty affine open `W`
with nonnegative order along every prime divisor meeting `W` is a section: `t ∣ x` in `Γ(Y, W)`. -/
private theorem exists_mul_eq_of_forall_zero_le_ord [IsLocallyNoetherian Y] [IsNormal Y]
    (W : Y.affineOpens) [Nonempty (W : Y.Opens)] (x t : Γ(Y, W))
    (ht0 : algebraMap Γ(Y, W) Y.functionField t ≠ 0)
    (hreg : ∀ Γ : MMP.Mori.PrimeDivisor Y, (Γ.support ∩ (W : Y.Opens)).Nonempty →
      0 ≤ Y.ord (algebraMap Γ(Y, W) Y.functionField x /
        algebraMap Γ(Y, W) Y.functionField t) Γ.genericPoint) :
    ∃ a : Γ(Y, W), t * a = x := by
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W W.2
  obtain ⟨a, ha⟩ := MMP.Threefold.Bridges.exists_germToFunctionField_eq_of_forall_zero_le_ord
    (W : Y.Opens) (algebraMap Γ(Y, W) Y.functionField x /
      algebraMap Γ(Y, W) Y.functionField t) hreg
  refine ⟨a, IsFractionRing.injective Γ(Y, W) Y.functionField ?_⟩
  have ha' : algebraMap Γ(Y, W) Y.functionField a = _ := ha
  rw [map_mul, ha', mul_div_cancel₀ _ ht0]

/-- In a direct summand of `R^N`, an element all of whose coordinates are divisible by `t` is
divisible by `t`. -/
private theorem exists_eq_smul_of_forall_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {N : ℕ} (r : (Fin N → R) →ₗ[R] M) (s : M →ₗ[R] Fin N → R) (hrs : r ∘ₗ s = .id)
    (p : M) (t : R) (h : ∀ j, ∃ a, t * a = s p j) : ∃ y, p = t • y := by
  choose a ha using h
  refine ⟨r a, ?_⟩
  have hsp : s p = t • a := funext fun j => (ha j).symm
  have := congrArg r hsp
  rwa [← LinearMap.comp_apply, hrs, LinearMap.id_apply, map_smul] at this

/-- Cancelling a scalar whose image in the field `K` is nonzero, on a `K`-vector space. -/
private theorem eq_of_smul_eq_smul_of_algebraMap_ne_zero {A K M : Type*} [CommRing A] [Field K]
    [Algebra A K] [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M] {t : A}
    (ht : algebraMap A K t ≠ 0) {x y : M} (h : t • x = t • y) : x = y := by
  rw [← algebraMap_smul K t x, ← algebraMap_smul K t y] at h
  exact smul_right_injective M ht h

/-- **Algebraic Hartogs for top forms, on an affine open.** On a normal integral scheme smooth over
a perfect field, a rational top form with nonnegative order along every prime divisor is, on every
nonempty affine open `W`, the image of an algebraic form of `Γ(Y, W)`. -/
private theorem exists_topFormsMap_eq [Smooth sY] [LocallyOfFiniteType sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [PerfectField k] {n : ℕ} (hn : topologicalKrullDim Y = n)
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄k])
    (hω : letI := functionFieldAlgebra sY
      ∀ Γ : MMP.Mori.PrimeDivisor Y,
        0 ≤ Γ.ordForm (show RationalPluriForms sY n (1 : ℕ) from formPow ω 1))
    (W : Y.affineOpens) [Nonempty (W : Y.Opens)] :
    letI := sectionAlgebra sY W
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_section_functionField sY (W : Y.Opens)
    ∃ y : ⋀[Γ(Y, W)]^n Ω[Γ(Y, W)⁄k], topFormsMap k Γ(Y, W) Y.functionField n y = ω := by
  classical
  let := sectionAlgebra sY W
  let := functionFieldAlgebra sY
  have := isScalarTower_section_functionField sY (W : Y.Opens)
  rcases eq_or_ne ω 0 with rfl | hω0
  · exact ⟨0, map_zero _⟩
  have : Algebra.Smooth k Γ(Y, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra sY W.2
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W W.2
  have := projective_exteriorPower (R := Γ(Y, W)) (M := Ω[Γ(Y, W)⁄k]) n
  have := finiteType_sectionAlgebra sY W.2
  obtain ⟨N, r, s, -, -, hrs⟩ := Module.Finite.exists_comp_eq_id_of_projective Γ(Y, W)
    (⋀[Γ(Y, W)]^n Ω[Γ(Y, W)⁄k])
  have hloc := MMP.DeRham.isLocalizedModule_mapExteriorPower_of_isLocalization (A := k)
    (L := Γ(Y, W)) (L' := Y.functionField) (nonZeroDivisors Γ(Y, W)) n
  have heq : ∀ x, mapExteriorPower k Γ(Y, W) Y.functionField n x =
      topFormsMap k Γ(Y, W) Y.functionField n x := fun x =>
    (MMP.Fourfold.topFormsMap_self (k := k) _).symm.trans (topFormsMap_mapExteriorPower n x)
  have hinj := topFormsMap_injective (k := k) (A := Γ(Y, W)) (K := Y.functionField) n
  obtain ⟨⟨p, t⟩, hpt⟩ := IsLocalizedModule.surj (nonZeroDivisors Γ(Y, W))
    (mapExteriorPower k Γ(Y, W) Y.functionField n) ω
  rw [heq] at hpt
  have ht0 : algebraMap Γ(Y, W) Y.functionField t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
  -- the coordinates of `p / t` have nonnegative order along the prime divisors meeting `W`
  have hreg : ∀ j (Γ : MMP.Mori.PrimeDivisor Y), (Γ.support ∩ (W : Y.Opens)).Nonempty →
      0 ≤ Y.ord (algebraMap Γ(Y, W) Y.functionField (s p j) /
        algebraMap Γ(Y, W) Y.functionField t) Γ.genericPoint := by
    intro j Γ hΓ
    have hη : Γ.genericPoint ∈ (W : Y.Opens) := Γ.genericPoint_mem_of_nonempty hΓ
    obtain ⟨u, hu, p', e1⟩ := exists_topFormsMap_eq_smul_of_genericPoint_mem sY hn ω hω hω0 W Γ hη
    have e2 : t.1 • p' = u • p := by
      apply hinj
      rw [map_smul, map_smul, e1, ← hpt, smul_comm]
      rfl
    have e3 : t.1 * s p' j = u * s p j := by
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using congrArg (fun q => s q j) e2
    have hu0 : algebraMap Γ(Y, W) Y.functionField u ≠ 0 := by
      refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ?_)
      rintro rfl
      exact Ideal.mem_primeCompl_iff.mp hu (zero_mem _)
    have hval : algebraMap Γ(Y, W) Y.functionField (s p j) /
        algebraMap Γ(Y, W) Y.functionField t =
          algebraMap Γ(Y, W) Y.functionField (s p' j) / algebraMap Γ(Y, W) Y.functionField u := by
      rw [div_eq_div_iff ht0 hu0, ← map_mul, ← map_mul, mul_comm (s p j), mul_comm (s p' j), e3]
    rw [hval]
    exact zero_le_ord_div_of_mem_primeCompl W Γ hη (s p' j) hu
  obtain ⟨y, hy⟩ := exists_eq_smul_of_forall_mul_eq r s hrs p t.1 fun j =>
    exists_mul_eq_of_forall_zero_le_ord W (s p j) t.1 ht0 (hreg j)
  refine ⟨y, ?_⟩
  rw [hy, map_smul] at hpt
  have hpt' : t.1 • ω = t.1 • topFormsMap k Γ(Y, W) Y.functionField n y := hpt
  exact (eq_of_smul_eq_smul_of_algebraMap_ne_zero (K := Y.functionField) ht0 hpt').symm

end Hartogs

section Gluing

open KaehlerDifferential

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]

/-- On a smooth integral scheme, a form over a nonempty affine open is determined by its image in
`Ω^n_{k(Y)/k}`. -/
private theorem chartVal_injective [Smooth sY] (n : ℕ) (W : Y.affineOpens)
    [Nonempty (W : Y.Opens)] : Function.Injective (chartVal sY n W) := by
  let := sectionAlgebra sY W
  let := functionFieldAlgebra sY
  have := isScalarTower_section_functionField sY (W : Y.Opens)
  have : Algebra.Smooth k Γ(Y, W) := MMP.Flips.ResolutionInputs.smooth_sectionAlgebra sY W.2
  have := projective_exteriorPower (R := Γ(Y, W)) (M := Ω[Γ(Y, W)⁄k]) n
  have : IsFractionRing Γ(Y, W) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y W W.2
  exact (topFormsMap_injective (k := k) (A := Γ(Y, W)) (K := Y.functionField) n).comp
    (MMP.DeRham.formsAlgEquiv sY n W).injective

/-- **Algebraic Hartogs for top forms.** On a normal integral scheme smooth over a perfect field,
a rational top form with nonnegative order along every prime divisor is the rational form of a
global form. -/
private theorem exists_ratForm_eq [Smooth sY] [LocallyOfFiniteType sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [PerfectField k] {n : ℕ} (hn : topologicalKrullDim Y = n)
    (ω : letI := functionFieldAlgebra sY; ⋀[Y.functionField]^n Ω[Y.functionField⁄k])
    (hω : letI := functionFieldAlgebra sY
      ∀ Γ : MMP.Mori.PrimeDivisor Y,
        0 ≤ Γ.ordForm (show RationalPluriForms sY n (1 : ℕ) from formPow ω 1)) :
    ∃ s : Γ(sY.relativeDifferentialForms (n : ℤ), ⊤),
      ratForm sY n s = (letI := functionFieldAlgebra sY; formPow ω 1) := by
  classical
  have hloc : ∀ (W : Y.affineOpens) [Nonempty (W : Y.Opens)], ∃ x, chartVal sY n W x = ω := by
    intro W _
    obtain ⟨y, hy⟩ := exists_topFormsMap_eq sY hn ω hω W
    refine ⟨(MMP.DeRham.formsAlgEquiv sY n W).symm y, ?_⟩
    unfold chartVal
    rw [LinearEquiv.apply_symm_apply]
    exact hy
  let ι := {W : Y.affineOpens // Nonempty (W : Y.Opens)}
  choose x hx using fun W : ι => @hloc W.1 W.2
  let M := sY.relativeDifferentialForms (n : ℤ)
  have key : ∀ (W : ι) (V : Y.affineOpens) [Nonempty (V : Y.Opens)]
      (h : (V : Y.Opens) ≤ W.1), chartVal sY n V (M.presheaf.map (homOfLE h).op (x W)) = ω := by
    intro W V _ h
    have := W.2
    exact (chartVal_res sY n h (x W)).trans (hx W)
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf (fun W : ι => (W.1 : Y.Opens)) x := by
    intro W W'
    apply (Scheme.Modules.isSheaf M).section_ext
    intro y hy
    obtain ⟨V, hV, hyV⟩ := exists_affineOpens_le _ hy
    have : Nonempty (V : Y.Opens) := ⟨⟨y, hyV⟩⟩
    refine ⟨V, hV, hyV, ?_⟩
    apply chartVal_injective sY n V
    have e : ∀ (W₀ : ι) (i : (W.1 : Y.Opens) ⊓ W'.1 ⟶ W₀.1),
        M.presheaf.map (homOfLE hV).op (M.presheaf.map i.op (x W₀)) =
          M.presheaf.map (homOfLE (hV.trans (leOfHom i))).op (x W₀) := by
      intro W₀ i
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [e, e, key, key]
  have hcover : (⊤ : Y.Opens) ≤ iSup fun W : ι => (W.1 : Y.Opens) := by
    intro y _
    obtain ⟨W, -, hy⟩ := exists_affineOpens_le (⊤ : Y.Opens) (Set.mem_univ y)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, ⟨⟨y, hy⟩⟩⟩, hy⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
    (fun W : ι => (W.1 : Y.Opens)) ⊤ (fun W => homOfLE le_top) hcover x hcompat
  refine ⟨s, ?_⟩
  rw [ratForm_eq sY n (someAffine Y), chartForm]
  let := functionFieldAlgebra sY
  change formPow (chartVal sY n (someAffine Y) (M.presheaf.map (homOfLE le_top).op s)) 1 = _
  rw [hs ⟨someAffine Y, inferInstance⟩, hx ⟨someAffine Y, inferInstance⟩]

end Gluing

/-- On an integral scheme smooth over `ℂ`, a global two-form is determined by its rational form. -/
private theorem ratForm_injective {Y : Scheme.{0}} [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ))
    [Smooth sY] : Function.Injective (ratForm sY 2) := by
  let := functionFieldAlgebra sY
  intro a b h
  have h1 : chartForm sY 2 (someAffine Y) a = chartForm sY 2 (someAffine Y) b :=
    formPow_one_injective (k := ℂ) h
  rw [chartForm, chartForm] at h1
  have h2 := chartVal_injective sY 2 (someAffine Y) h1
  rw [← sub_eq_zero]
  obtain ⟨⟨y, hy⟩⟩ := nonempty_someAffine Y
  refine eq_zero_of_res_eq_zero (d := 2) sY (a - b) (O := (someAffine Y : Y.Opens)) ⟨y, hy⟩ ?_
  rw [map_sub, h2, sub_self]

section Spread

variable {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}

/-- `Spec ℂ(X) ⟶ X ⟶ Spec ℂ` is `Spec` of the `ℂ`-algebra structure of `ℂ(X)`. -/
private lemma fromSpecStalk_genericPoint_comp :
    X.fromSpecStalk (genericPoint X) ≫ sX =
      Spec.map (CommRingCat.ofHom
        (@algebraMap ℂ X.functionField _ _ (functionFieldAlgebra sX))) := by
  rw [MMP.fromSpecStalk_comp_eq]
  rfl

/-- A morphism from an open `D ∋ η` agreeing at the generic point with `Spec σ` maps the generic
point to the generic point. -/
private lemma map_genericPoint_of_fromSpecStalkOfMem_comp_eq {D : X.Opens}
    (hη : genericPoint X ∈ D) {φ : D.toScheme ⟶ X} {σ : X.functionField →+* X.functionField}
    (hP : D.fromSpecStalkOfMem (genericPoint X) hη ≫ φ =
      Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecStalk (genericPoint X)) :
    φ ⟨genericPoint X, hη⟩ = genericPoint X := by
  have hpt : D.fromSpecStalkOfMem (genericPoint X) hη (IsLocalRing.closedPoint _) =
      ⟨genericPoint X, hη⟩ := by
    apply Subtype.ext
    change (D.fromSpecStalkOfMem (genericPoint X) hη ≫ D.ι) (IsLocalRing.closedPoint _) = _
    rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
  have e := congr($hP (IsLocalRing.closedPoint X.functionField))
  change φ (D.fromSpecStalkOfMem (genericPoint X) hη (IsLocalRing.closedPoint _)) =
      X.fromSpecStalk (genericPoint X)
        (Spec.map (CommRingCat.ofHom σ) (IsLocalRing.closedPoint X.functionField)) at e
  have : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  rwa [hpt, Subsingleton.elim (Spec.map _ (IsLocalRing.closedPoint X.functionField))
    (IsLocalRing.closedPoint X.functionField), Scheme.fromSpecStalk_closedPoint] at e

/-- On function fields, a morphism factoring through a morphism `φ` from an open `D ∋ η` agreeing
at the generic point with `Spec σ` is `σ` followed by the inclusion. -/
private lemma functionFieldMap_eq_comp_of_fromSpecStalkOfMem_comp_eq {D : X.Opens}
    (hη : genericPoint X ∈ D) {φ : D.toScheme ⟶ X} {σ : X.functionField →+* X.functionField}
    (hP : D.fromSpecStalkOfMem (genericPoint X) hη ≫ φ =
      Spec.map (CommRingCat.ofHom σ) ≫ X.fromSpecStalk (genericPoint X))
    {V : Scheme.{0}} [IsIntegral V] (a : V ⟶ D.toScheme) {g₁ g₂ : V ⟶ X}
    [IsDominant g₁] [IsDominant g₂] (h₁ : a ≫ D.ι = g₁) (h₂ : a ≫ φ = g₂) :
    functionFieldMap g₂ = (functionFieldMap g₁).comp σ := by
  have ha : V.fromSpecStalk (genericPoint V) ≫ a =
      Spec.map (CommRingCat.ofHom (functionFieldMap g₁)) ≫
        D.fromSpecStalkOfMem (genericPoint X) hη := by
    rw [← cancel_mono D.ι, Category.assoc, h₁, Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, functionFieldMap_fromSpecStalk]
  have h : Spec.map (CommRingCat.ofHom (functionFieldMap g₂)) ≫
        X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom ((functionFieldMap g₁).comp σ)) ≫
        X.fromSpecStalk (genericPoint X) := by
    rw [functionFieldMap_fromSpecStalk, ← h₂, ← Category.assoc, ha, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, Category.assoc, hP]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp h))

/-- **A birational self-map is an isomorphism between dense opens.** For a `ℂ`-automorphism `σ`
of `ℂ(X)` there are an integral `U` and dominant open immersions `j₁ j₂ : U ⟶ X` over `ℂ` with
`j₂^* = j₁^* ∘ σ` on function fields. -/
private theorem exists_isOpenImmersion_functionFieldMap_eq [LocallyOfFiniteType sX]
    (σ : FunctionFieldEquiv sX sX) :
    letI := functionFieldAlgebra sX
    ∃ (U : Scheme.{0}) (_ : IsIntegral U) (j₁ j₂ : U ⟶ X) (_ : IsOpenImmersion j₁)
      (_ : IsOpenImmersion j₂) (_ : IsDominant j₁) (_ : IsDominant j₂),
      j₂ ≫ sX = j₁ ≫ sX ∧
        functionFieldMap j₂ = (functionFieldMap j₁).comp σ.toRingEquiv.toRingHom := by
  let := functionFieldAlgebra sX
  have hα : (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      X.fromSpecStalk (genericPoint X)) ≫ sX = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [Category.assoc, fromSpecStalk_genericPoint_comp, ← Spec.map_comp]
    congr 1
    ext c
    exact σ.commutes c
  let P := Scheme.PartialMap.ofFromSpecStalk sX sX _ hα
  have hη : genericPoint X ∈ P.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sX _ hα
  have hP : P.domain.fromSpecStalkOfMem (genericPoint X) hη ≫ P.hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ X.fromSpecStalk (genericPoint X) :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sX _ hα
  have hPs : P.hom ≫ sX = P.domain.ι ≫ sX := Scheme.PartialMap.ofFromSpecStalk_comp sX sX _ hα
  have : Nonempty P.domain := ⟨⟨_, hη⟩⟩
  have : IsIntegral P.domain.toScheme := isIntegral_of_isOpenImmersion P.domain.ι
  have : IsDominant P.domain.ι :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion P.domain.ι
  have hgen : P.hom ⟨genericPoint X, hη⟩ = genericPoint X :=
    map_genericPoint_of_fromSpecStalkOfMem_comp_eq hη hP
  have : IsDominant P.hom := ⟨Dense.mono
    (Set.singleton_subset_iff.mpr (Set.mem_range.mpr ⟨_, hgen⟩))
    (dense_iff_closure_eq.mpr (genericPoint_spec X).def)⟩
  have key : ∀ (V : Scheme.{0}) [IsIntegral V] (a : V ⟶ P.domain.toScheme) (g₁ g₂ : V ⟶ X)
      [IsDominant g₁] [IsDominant g₂], a ≫ P.domain.ι = g₁ → a ≫ P.hom = g₂ →
      functionFieldMap g₂ = (functionFieldMap g₁).comp σ.toRingEquiv.toRingHom :=
    fun _ _ a _ _ _ _ h₁ h₂ => functionFieldMap_eq_comp_of_fromSpecStalkOfMem_comp_eq hη hP a h₁ h₂
  -- `P.hom` is birational
  have hbij : Function.Bijective (functionFieldMap P.hom) := by
    rw [key P.domain (𝟙 _) P.domain.ι P.hom (Category.id_comp _) (Category.id_comp _)]
    exact (MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion P.domain.ι ⊤
      ⟨Classical.arbitrary _, trivial⟩).comp σ.bijective
  let e := X.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant P.hom).symm)
  have : IsIso (e.hom ≫ P.hom.stalkMap (genericPoint P.domain)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (P.hom.stalkMap (genericPoint P.domain)) := IsIso.of_isIso_comp_left e.hom _
  have hbir : AlgebraicGeometry.IsBirational P.hom := by
    rw [isBirational_iff]
    simp only [genericPoints_eq_singleton, Set.bijOn_singleton, Set.mem_singleton_iff, forall_eq]
    exact ⟨map_genericPoint_of_isDominant P.hom, inferInstance⟩
  have : Finite (irreducibleComponents P.domain.toScheme) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  have : LocallyOfFiniteType (P.hom ≫ sX) := hPs ▸ inferInstance
  have : LocallyOfFiniteType P.hom := LocallyOfFiniteType.of_comp (g := sX) ‹_›
  obtain ⟨U, V, hUV, hU, -, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational P.hom hbir
    (Or.inl ⟨inferInstance, inferInstance⟩)
  have : Nonempty U := hU.nonempty.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have h₂ : U.ι ≫ P.hom = P.hom.resLE V U hUV ≫ V.ι := (Scheme.Hom.resLE_comp_ι _ _).symm
  have : IsOpenImmersion (U.ι ≫ P.hom) := by
    rw [h₂]
    infer_instance
  have : IsDominant (U.ι ≫ P.domain.ι) :=
    MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have : IsDominant (U.ι ≫ P.hom) := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  exact ⟨U, inferInstance, U.ι ≫ P.domain.ι, U.ι ≫ P.hom, inferInstance, inferInstance,
    inferInstance, inferInstance, by rw [Category.assoc, hPs, Category.assoc],
    key U U.ι _ _ rfl rfl⟩

end Spread

/-- If a dominant morphism `h : T ⟶ X` of integral schemes locally of finite type over `k` is
bijective on function fields, then `T` and `X` have the same dimension. -/
private theorem topologicalKrullDim_eq_of_bijective {k : Type u} [Field k] {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] (sX : X ⟶ Spec (.of k)) (h : T ⟶ X) [IsDominant h]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (h ≫ sX)]
    (hb : Function.Bijective (functionFieldMap h)) :
    topologicalKrullDim T = topologicalKrullDim X := by
  rw [← MMP.Mori.toENat_trdeg_functionField (sX := h ≫ sX),
    ← MMP.Mori.toENat_trdeg_functionField (sX := sX),
    MMP.Mori.trdeg_functionField_eq_of_bijective sX h hb]

/-- An integral scheme smooth of relative dimension two over `ℂ` has dimension two. -/
private theorem topologicalKrullDim_eq_two {Z : Scheme.{0}} [IsIntegral Z] (sZ : Z ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 2 sZ] : topologicalKrullDim Z = 2 := by
  have : Smooth sZ := SmoothOfRelativeDimension.smooth 2 sZ
  obtain ⟨x⟩ : Nonempty Z := inferInstance
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible ℂ Z sZ x,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 sZ x]
  rfl

/-- Eigenvalues of birational self-maps on rational two-forms without poles of a smooth projective
complex surface are roots of unity of uniformly bounded order. -/
private theorem exists_pow_eq_one_of_pluriformPullback_eq_smul_formPow (b : ℕ) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
        (sY : Y ⟶ Spec (.of ℂ)), IsProjectiveMorphism sY → SmoothOfRelativeDimension 2 sY →
        Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace sY) ∅ 2) ≤ b →
        letI := functionFieldAlgebra sY
        ∀ ω : ⋀[Y.functionField]^2 Ω[Y.functionField⁄ℂ], ω ≠ 0 →
          (formPow ω 1 : RationalPluriForms sY 2 (1 : ℕ)) ∈ logPluricanonicalSections sY 2 1 0 →
        ∀ (τ : FunctionFieldEquiv sY sY) (μ : ℂ),
          pluriformPullback sY sY τ.toHom 2 (1 : ℕ) (formPow ω 1) =
            μ • (show RationalPluriForms sY 2 (1 : ℕ) from formPow ω 1) →
          (minpoly ℚ μ).natDegree ≤ b ∧ μ ^ N = 1 := by
  obtain ⟨N, hN, hE⟩ := MMP.Fourfold.exists_pow_eq_one_of_birational_surface_top_form_eigenvalue b
  refine ⟨N, hN, ?_⟩
  intro Y _ _ _ sY hP hS hb
  let := functionFieldAlgebra sY
  intro ω hω0 hωmem τ μ hτ
  have : Smooth sY := SmoothOfRelativeDimension.smooth 2 sY
  have hd : topologicalKrullDim Y = 2 := topologicalKrullDim_eq_two sY
  -- the global two-form
  have hω' : ∀ Γ : MMP.Mori.PrimeDivisor Y,
      0 ≤ Γ.ordForm (show RationalPluriForms sY 2 (1 : ℕ) from formPow ω 1) := by
    intro Γ
    have hΓ : (Γ.support ∩ (⊤ : Y.Opens)).Nonempty :=
      ⟨Γ.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl, trivial⟩
    have h := ((mem_logPluricanonicalSections sY).mp hωmem).2 Γ hΓ (formPow_one_ne_zero hω0)
    simpa using h
  obtain ⟨s, hs⟩ := exists_ratForm_eq sY hd ω hω'
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply formPow_one_ne_zero hω0
    rw [← hs]
    have h0 : chartForm sY 2 (someAffine Y) 0 = 0 := by
      rw [chartForm, map_zero]
      unfold chartVal
      rw [map_zero, map_zero]
    unfold ratForm
    rw [h0, ← zero_smul Y.functionField ω, formPow_smul, pow_one, zero_smul]
  -- the birational self-map as an isomorphism between dense opens
  obtain ⟨U', _, j₁, j₂, _, _, _, _, e, hff⟩ := exists_isOpenImmersion_functionFieldMap_eq τ
  let O : Y.Opens := j₁.opensRange
  let iso : U' ≅ O.toScheme := j₁.isoOpensRange
  let f : O.toScheme ⟶ Y := iso.inv ≫ j₂
  have hO : O.ι = iso.inv ≫ j₁ := by
    rw [← Scheme.Hom.isoOpensRange_hom_ι j₁, Iso.inv_hom_id_assoc]
  have hf : f ≫ sY = O.ι ≫ sY := by
    rw [hO, Category.assoc, Category.assoc, e]
  have : Nonempty O := ⟨⟨j₁ (Classical.arbitrary U'), ⟨_, rfl⟩⟩⟩
  have : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have : IsDominant O.ι := MMP.Fourfold.isDominant_ι_of_nonempty O
  have : IsDominant f := inferInstanceAs (IsDominant (iso.inv ≫ j₂))
  have hbι : Function.Bijective (functionFieldMap O.ι) :=
    MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion O.ι ⊤ ⟨Classical.arbitrary _, trivial⟩
  have hdO : topologicalKrullDim O = 2 :=
    (topologicalKrullDim_eq_of_bijective sY O.ι hbι).trans hd
  have hOd : Dense (O : Set Y) := by
    change Dense (Set.range j₁.base)
    exact j₁.denseRange
  have hfd : Dense (Set.range f.base) := f.denseRange
  -- the eigenvalue relation on global forms
  let := functionFieldAlgebra (O.ι ≫ sY)
  have hffO : ffHom f hf = (ffHom (sT := O.ι ≫ sY) O.ι rfl).comp τ.toHom := by
    refine AlgHom.ext fun x => ?_
    change functionFieldMap f x = functionFieldMap O.ι (τ x)
    have h1 : functionFieldMap f x = functionFieldMap iso.inv (functionFieldMap j₂ x) :=
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply iso.inv j₂ x).symm
    have h2 : functionFieldMap O.ι (τ x) =
        functionFieldMap iso.inv (functionFieldMap j₁ (τ x)) := by
      rw [MMP.Positivity.DivisorOver.functionFieldMap_congr hO]
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply iso.inv j₁ _).symm
    rw [h1, h2, hff]
    rfl
  have hrat : pluriformPullback sY sY τ.toHom 2 (1 : ℕ) (ratForm sY 2 s) =
      μ • ratForm sY 2 s := by rwa [hs]
  have heq : IsFormEigen sY O f hf s μ := by
    apply ratForm_injective (O.ι ≫ sY)
    calc _ = pluriformPullback (O.ι ≫ sY) sY (ffHom f hf) 2 ((1 : ℕ) : ℤ) (ratForm sY 2 s) :=
          (pluriformPullback_ffHom_ratForm f hf (by rw [hf, Category.comp_id]) hd hdO s).symm
      _ = μ • pluriformPullback (O.ι ≫ sY) sY (ffHom (sT := O.ι ≫ sY) O.ι rfl) 2 ((1 : ℕ) : ℤ)
            (ratForm sY 2 s) := by
          rw [hffO, ← pluriformPullback_comp hdO hd hd, hrat, map_smul]
      _ = μ • ratForm (O.ι ≫ sY) 2 _ := congrArg (fun t => μ • t)
          (pluriformPullback_ffHom_ratForm O.ι rfl (by rw [Category.comp_id]) hd hdO s)
      _ = _ := (ratForm_const_smul (O.ι ≫ sY) 2 μ _).symm
  obtain ⟨-, hdeg, -, hpow⟩ := hE sY hP hS hb O hOd f hfd hf s μ hs0 heq
  exact ⟨hdeg, hpow⟩

/-- **Composing a lift around the cycles of a permutation.** If isomorphisms of function fields
`σᵢ : k(Z_{π i}) ≃ k(Zᵢ)` multiply the forms `ω_{π i}` and `ωᵢ` by `ρ`, then their composite along
`i, π i, …, π^r i` multiplies `ω_{π^r i}` and `ωᵢ` by `ρ^r`. -/
private theorem exists_pluriformPullback_eq_pow_smul {k : Type u} [Field k] [CharZero k]
    {ι : Type*} {Z : ι → Scheme.{u}} [∀ i, IsIntegral (Z i)] {t : ∀ i, Z i ⟶ Spec (.of k)}
    [∀ i, LocallyOfFiniteType (t i)] {d : ℕ} (hZ : ∀ i, topologicalKrullDim (Z i) = d)
    {π : Equiv.Perm ι} (σ : ∀ i, FunctionFieldEquiv (t i) (t (π i))) (ρ : k) :
    letI := fun i => functionFieldAlgebra (t i)
    ∀ ω : ∀ i, ⋀[(Z i).functionField]^d Ω[(Z i).functionField⁄k],
      (∀ i, pluriformPullback (t i) (t (π i)) (σ i).toHom d (1 : ℕ) (formPow (ω (π i)) 1) =
        ρ • (show RationalPluriForms (t i) d (1 : ℕ) from formPow (ω i) 1)) →
      ∀ (r : ℕ) (i j : ι), j = (π ^ r) i →
        ∃ τ : FunctionFieldEquiv (t i) (t j),
          pluriformPullback (t i) (t j) τ.toHom d (1 : ℕ) (formPow (ω j) 1) =
            ρ ^ r • (show RationalPluriForms (t i) d (1 : ℕ) from formPow (ω i) 1) := by
  let := fun i => functionFieldAlgebra (t i)
  intro ω hσ r
  induction r with
  | zero =>
    intro i j hj
    rw [pow_zero, Equiv.Perm.one_apply] at hj
    subst hj
    exact ⟨1, (pluriformPullback_one (hZ j) _ _).trans (by rw [pow_zero, one_smul])⟩
  | succ r ih =>
    intro i j hj
    rw [pow_succ, Equiv.Perm.mul_apply] at hj
    obtain ⟨τ, hτ⟩ := ih (π i) j hj
    refine ⟨τ.trans (σ i), ?_⟩
    refine (pluriformPullback_comp (hZ i) (hZ (π i)) (hZ j) _ (σ i).toHom τ.toHom _).symm.trans ?_
    rw [hτ, map_smul, hσ i, smul_smul, pow_succ]

/-- **Pluriform eigenvalues lift to cyclic covers, and are roots of unity of bounded order.**
For every `b : ℕ` there is `N > 0` with the following property. Let `X` be a smooth projective
complex surface, `B` an snc `ℚ`-divisor with all coefficients less than one, `m > 0` with `mB`
integral, and `s ≠ 0` in `H⁰(X, m(K_X + B))`. Let `Yᵢ`, `pᵢ`, `ωᵢ` be a resolution of the
degree-`m` cyclic cover of `s` with its root forms, as in
`MMP.Fourfold.exists_cyclicCover_resolution_finrank_le`, with `∑ᵢ b₂(Yᵢ) ≤ b`. Let `g` be a
birational self-map of `X` with `g^* s = λ s`. Then
* for every `ρ` with `ρ^m = λ` there is a birational self-map of `⨆ᵢ Yᵢ` lying over `g`, given
  by a permutation `π` of the components and isomorphisms `σᵢ : k(Y_{π i}) ≃ k(Yᵢ)`, whose
  pull-back sends `ω_{π i}` to `ρ ωᵢ`;
* `λ ^ N = 1`. -/
@[mmp "lem_fourfold_surface_pluriform_cyclic_eigenvalue_lift"]
public theorem exists_pow_eq_one_of_pluriformPullback_eq_smul (b : ℕ) :
    ∃ N : ℕ, 0 < N ∧
    ∀ {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
      {sX : X ⟶ Spec (.of ℂ)} (_hn : topologicalKrullDim X = 2) {B : QDivisor X}
      (_hXB : IsSNCSubboundaryPair sX B) (_hB : ∀ P, B.coeff P < 1)
      {m : ℕ} (_hm : 0 < m) (_hmB : ∀ P, ∃ a : ℤ, (m : ℚ) * B.coeff P = a)
      (s : RationalPluriForms sX 2 m) (_hs : s ∈ logPluricanonicalSections sX 2 m B)
      (_hs0 : s ≠ 0)
      {k : ℕ} (Y : Fin k → Scheme.{0}) [∀ i, IsIntegral (Y i)]
      [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
      (p : ∀ i, Y i ⟶ X) [∀ i, IsDominant (p i)],
      (∀ i, IsProjectiveMorphism (p i ≫ sX)) → (∀ i, SmoothOfRelativeDimension 2 (p i ≫ sX)) →
      ∑ i, Module.finrank ℚ
          (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i ≫ sX)) ∅ 2) ≤ b →
      letI := fun i => functionFieldAlgebra (p i ≫ sX)
      ∀ ω : ∀ i, ⋀[(Y i).functionField]^2 Ω[(Y i).functionField⁄ℂ],
        (∀ i, ω i ≠ 0) →
        (∀ i, (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) ∈
          logPluricanonicalSections (p i ≫ sX) 2 1 0) →
        (∀ i, (formPow (ω i) m : RationalPluriForms (p i ≫ sX) 2 m) =
          pullbackRationalPluriForms sX (p i) s) →
        letI := functionFieldAlgebra sX
        letI := fun i => functionFieldMapAlgebra (p i)
        ∀ η : ⋀[X.functionField]^2 Ω[X.functionField⁄ℂ], η ≠ 0 →
        ∀ z : ∀ i, (Y i).functionField,
          (∀ i, (formPow (ω i) 1 : RationalPluriForms (p i ≫ sX) 2 (1 : ℕ)) =
            z i • pullbackRationalPluriForms sX (p i)
              (show RationalPluriForms sX 2 (1 : ℕ) from formPow η 1)) →
          Algebra.adjoin X.functionField {z} = ⊤ →
          Module.finrank X.functionField (∀ i, (Y i).functionField) = m →
        ∀ (g : FunctionFieldEquiv sX sX) (lam : ℂ),
          pluriformPullback sX sX g.toHom 2 m s = lam • s →
          (∀ ρ : ℂ, ρ ^ m = lam →
            ∃ (π : Equiv.Perm (Fin k))
              (σ : ∀ i, FunctionFieldEquiv (p i ≫ sX) (p (π i) ≫ sX)),
              (∀ i (f : X.functionField),
                σ i (algebraMap X.functionField (Y (π i)).functionField f) =
                  algebraMap X.functionField (Y i).functionField (g f)) ∧
              ∀ i, pluriformPullback (p i ≫ sX) (p (π i) ≫ sX) (σ i).toHom 2 (1 : ℕ)
                  (formPow (ω (π i)) 1) =
                ρ • (show RationalPluriForms (p i ≫ sX) 2 (1 : ℕ) from formPow (ω i) 1)) ∧
          lam ^ N = 1 := by
  obtain ⟨N₀, hN₀, hB⟩ := exists_pow_eq_one_of_pluriformPullback_eq_smul_formPow b
  refine ⟨b.factorial * N₀, Nat.mul_pos (Nat.factorial_pos b) hN₀, ?_⟩
  intro X _ _ _ sX hn B hXB _ m hm _ s _ hs0 k Y _ _ _ p _ hP hS hb
  let := fun i => functionFieldAlgebra (p i ≫ sX)
  intro ω hω0 hωreg hωm
  let := functionFieldAlgebra sX
  let := fun i => functionFieldMapAlgebra (p i)
  intro η hη0 z hz hadj hdeg g lam hg
  have := hXB.isProjectiveVariety.1
  have hdimY : ∀ i, topologicalKrullDim (Y i) = 2 := fun i => by
    have := hS i
    exact topologicalKrullDim_eq_two (p i ≫ sX)
  have : ∀ i, LocallyOfFiniteType (p i ≫ sX) := fun i => by
    have := hS i
    have := SmoothOfRelativeDimension.smooth 2 (p i ≫ sX)
    infer_instance
  have hlift := exists_perm_lift hn hm s hs0 Y p hdimY ω hωm η hη0 z hz hadj hdeg g lam hg
  refine ⟨hlift, ?_⟩
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq lam hm
  obtain ⟨π, σ, -, hσω⟩ := hlift ρ hρ
  -- there is at least one component
  have hk : 0 < k := Nat.pos_of_ne_zero <| by
    rintro rfl
    rw [Module.finrank_zero_of_subsingleton] at hdeg
    omega
  -- every component has `b₂ ≥ 1`, so there are at most `b` components
  have hb₂ : ∀ i, 1 ≤ Module.finrank ℚ
      (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i ≫ sX)) ∅ 2) := by
    intro i
    obtain ⟨N', -, hB'⟩ := exists_pow_eq_one_of_pluriformPullback_eq_smul_formPow
      (Module.finrank ℚ (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i ≫ sX)) ∅ 2))
    have := (hB' (p i ≫ sX) (hP i) (hS i) le_rfl (ω i) (hω0 i) (hωreg i) 1 1
      ((pluriformPullback_one (hdimY i) _ _).trans (one_smul _ _).symm)).1
    rwa [minpoly.one, ← Polynomial.C_1, Polynomial.natDegree_X_sub_C] at this
  have hkb : k ≤ b := by
    calc k = ∑ _i : Fin k, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hb₂ i
      _ ≤ b := hb
  have hπ : π ^ k.factorial = 1 := by
    have := pow_card_eq_one (G := Equiv.Perm (Fin k)) (x := π)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨τ, hτ⟩ := exists_pluriformPullback_eq_pow_smul hdimY σ ρ ω hσω k.factorial i₀ i₀
    (by rw [hπ]; rfl)
  have hb₀ : Module.finrank ℚ
      (relativeSingularCohomology ℚ (.of ℚ ℚ) (analyticSpace (p i₀ ≫ sX)) ∅ 2) ≤ b :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)).trans hb
  have hρpow := (hB (p i₀ ≫ sX) (hP i₀) (hS i₀) hb₀ (ω i₀) (hω0 i₀) (hωreg i₀) τ
    (ρ ^ k.factorial) hτ).2
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hkb
  rw [← hρ, ← pow_mul, show m * (b.factorial * N₀) = k.factorial * N₀ * (m * q) by
    rw [hq]; ring, pow_mul, pow_mul ρ k.factorial N₀, hρpow, one_pow]

end MMP.Fourfold
