module

public import MMP.Attr
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogForms
public import MMP.AlgebraicGeometry.DeRham.Logarithmic.RelativeLogDeRhamComplex
public import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.DeRhamTypeComplexHypercohomology
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ConcreteTotalKFlat
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperSmoothFiniteTypeSubring
public import StacksFrontier.AlgebraicGeometry.Limits.StageBaseChangeOpens
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsPushforwardComp
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CoveringResolution

/-!
# Spreading out a projective SNC pair and constancy of its fibre dimensions

Let `π : X ⟶ Spec ℂ` be smooth projective of relative dimension `n` and `D` a relative SNC divisor
on `X`. A model of `(X, D)` over a smooth `ℤ`-domain `R ⊆ ℂ` is a smooth projective
`g : 𝒳 ⟶ Spec R` with a relative SNC divisor `𝒟` whose base change along `Spec ℂ ⟶ Spec R` is
`(X, D)`. After inverting one nonzero element of `R`, every Hodge dimension
`dim H^j(Ω^p(log D))` and every logarithmic de Rham dimension `dim ℍ^j(Ω^•(log D))`, with or
without the twist by the reduced boundary, is the same on the complex fibre and on every residue
fibre of the model. This file contains the following ingredients of that statement.

* *Base change of cohomology.* For a bounded complex of flat modules with flat cohomology, the
  cohomology commutes with every base change. Over a Noetherian domain, inverting one nonzero
  element makes the cohomology of a bounded complex of flat modules with finite cohomology free,
  so its fibre dimensions are the generic ones.
* *Charts.* A weak chart of a closed set is an affine open with coordinates whose differentials
  form a basis of the relative Kähler differentials, the product of the first `r` of which cuts
  out the closed set. Weak charts pull back along cartesian squares, and near every point
  of a divisor with a weak chart there is a chart of a relative snc divisor.
* *Logarithmic forms as modules.* The logarithmic forms `I · Ω^p_{X/S}(log D)` form an
  `𝒪_X`-submodule of `j_*Ω^p_{U/S}`, with `U = X ∖ D`. On a chart they are free on the
  logarithmic coordinate forms `θ_K`, so they are quasi-coherent, and coherent when `X` is
  locally Noetherian.

## Main definitions

* `homologyAt`: the homology `ker g ⧸ range f` of a composable pair of linear maps.
* `WeakChart`: a weak chart of a closed set for a morphism of schemes.
* `G1.SNCChart`: a chart of a relative snc divisor at a point.
* `G1.LogChart`: logarithmic coordinate data whose forms `θ_K` are a basis of the logarithmic
  forms.
* `G1.logModule`: the `𝒪_X`-module `I · Ω^p_{X/S}(log D)`.
* `G1.logCx`: the logarithmic de Rham complex, with terms the logarithmic forms.

## Main results

* `homologyBaseChangeEquivOfFlat`: the cohomology of a bounded complex of flat modules with flat
  cohomology commutes with base change.
* `exists_finrank_homology_baseChange_eq`: generic constancy of the fibre dimensions of the
  cohomology of a bounded complex of flat modules over a Noetherian domain.
* `WeakChart.exists_baseChange`: weak charts pull back along cartesian squares.
* `exists_snc_chart`: a chart of a relative snc divisor at every point of a weak chart.
* `G1.logModule_isQuasicoherent`, `G1.logModule_isCoherent`: the logarithmic forms are
  quasi-coherent, and coherent over a locally Noetherian scheme.
* `G1.exists_iso_relativeLogDeRhamComplex_X`: the terms of the logarithmic de Rham complex are
  the modules `G1.logModule`, read over `f⁻¹𝒪_S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Mori.Divisor.LogSpreadingProof

/-- Two elements with the same inverse are equal. -/
theorem eq_of_mul_eq_one {R : Type*} [CommMonoid R] {a b x : R} (ha : a * x = 1)
    (hb : b * x = 1) : a = b :=
  left_inv_eq_right_inv ha (by rwa [mul_comm])

/-! ### Algebra: base change of cohomology of flat complexes -/

section AlgebraFlat

open TensorProduct

variable {A : Type*} [CommRing A]

/-- The kernel of a surjection between flat modules is flat. -/
theorem flat_of_exact {N M P : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] [Module.Flat A M] [Module.Flat A P]
    (i : N →ₗ[A] M) (hi : Function.Injective i) (f : M →ₗ[A] P) (hf : Function.Surjective f)
    (hex : Function.Exact i f) : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have h1 : Function.Injective (i.rTensor I) := by
    have := LinearMap.lTensor_injective_of_exact_of_flat f hf i hi hex I
    have he : i.rTensor I = (TensorProduct.comm A I M).toLinearMap ∘ₗ i.lTensor I ∘ₗ
        (TensorProduct.comm A N I).toLinearMap := by
      ext x y; rfl
    rw [he]
    simpa using this
  have h2 : Function.Injective (LinearMap.lTensor M I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h3 : (i.rTensor A) ∘ₗ (LinearMap.lTensor N I.subtype) =
      (LinearMap.lTensor M I.subtype) ∘ₗ (i.rTensor I) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have h4 : Function.Injective ((i.rTensor A) ∘ₗ (LinearMap.lTensor N I.subtype)) := by
    rw [h3]
    exact h2.comp h1
  exact Function.Injective.of_comp h4

/-- A linear map is exact against the inclusion of its kernel, with its image as target. -/
theorem exact_ker_subtype_rangeRestrict {M P : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (g : M →ₗ[A] P) :
    Function.Exact (LinearMap.ker g).subtype g.rangeRestrict :=
  fun x => by simp [Subtype.ext_iff]

variable (K : Type*) [CommRing K] [Algebra A K]
  {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂]

/-- The homology `ker g ⧸ range f` of a composable pair, as a module. -/
abbrev homologyAt (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂) : Type _ :=
  LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype

/-- If the inclusion of `range g` stays injective after base change to `K`, the kernel of the base
change of `g` is the image of the base change of `ker g`. -/
theorem baseChange_ker_eq_range (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂)
    (hinj : Function.Injective ((LinearMap.range g).subtype.baseChange K)) :
    LinearMap.ker (g.baseChange K) =
      LinearMap.range ((LinearMap.ker g).subtype.baseChange K) := by
  have hg : g = (LinearMap.range g).subtype ∘ₗ g.rangeRestrict := rfl
  have hk : LinearMap.ker (g.baseChange K) = LinearMap.ker (g.rangeRestrict.baseChange K) := by
    conv_lhs => rw [hg, LinearMap.baseChange_comp]
    exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj)
  rw [hk]
  ext x
  exact lTensor_exact K (exact_ker_subtype_rangeRestrict g) (LinearMap.surjective_rangeRestrict g) x

/-- For `g ∘ f = 0`, the range of the base change of `f` is the image in `K ⊗ M₁` of the base
change of `range f`, viewed inside `ker g`. -/
theorem range_baseChange_eq_map (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂) (hfg : g ∘ₗ f = 0) :
    LinearMap.range (f.baseChange K) =
      Submodule.map ((LinearMap.ker g).subtype.baseChange K)
        (LinearMap.range (((LinearMap.range f).comap (LinearMap.ker g).subtype).subtype.baseChange
          K)) := by
  set Z := LinearMap.ker g
  set T := (LinearMap.range f).comap Z.subtype
  have hfZ : ∀ x, f x ∈ Z := fun x => by
    simp [Z, LinearMap.mem_ker, ← LinearMap.comp_apply, hfg]
  let f₀ : M₀ →ₗ[A] Z := LinearMap.codRestrict Z f hfZ
  let f' : M₀ →ₗ[A] T := LinearMap.codRestrict T f₀ (fun x => by
    simp only [T, Submodule.mem_comap, Submodule.coe_subtype, f₀, LinearMap.codRestrict_apply]
    exact ⟨x, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨⟨z, hz⟩, hzT⟩
    obtain ⟨x, hx⟩ := hzT
    exact ⟨x, Subtype.ext (Subtype.ext hx)⟩
  have hfac : f = Z.subtype ∘ₗ T.subtype ∘ₗ f' := by ext x; rfl
  have hsurj : Function.Surjective (f'.baseChange K) := LinearMap.baseChange_surjective K hf'
  rw [hfac, LinearMap.baseChange_comp, LinearMap.baseChange_comp, ← LinearMap.comp_assoc,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj),
    LinearMap.range_comp]

/-- If `range g` is flat, the inclusion of `ker g` stays injective after base change to `K`. -/
theorem injective_baseChange_ker_subtype (g : M₁ →ₗ[A] M₂) [Module.Flat A (LinearMap.range g)] :
    Function.Injective ((LinearMap.ker g).subtype.baseChange K) :=
  LinearMap.lTensor_injective_of_exact_of_flat g.rangeRestrict
    (LinearMap.surjective_rangeRestrict g) _ Subtype.val_injective
    (exact_ker_subtype_rangeRestrict g) K

/-- **Homology commutes with base change** at a spot where the outgoing map has flat image
whose inclusion stays injective after base change. -/
noncomputable def homologyAtBaseChangeEquiv (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂)
    (hfg : g ∘ₗ f = 0) (hZ : Function.Injective ((LinearMap.ker g).subtype.baseChange K))
    (hinj : Function.Injective ((LinearMap.range g).subtype.baseChange K)) :
    homologyAt (f.baseChange K) (g.baseChange K) ≃ₗ[K] K ⊗[A] homologyAt f g := by
  set Z := LinearMap.ker g
  set T := (LinearMap.range f).comap Z.subtype
  let e1 : K ⊗[A] Z ≃ₗ[K] LinearMap.ker (g.baseChange K) :=
    (LinearEquiv.ofInjective _ hZ).trans
      (LinearEquiv.ofEq _ _ (baseChange_ker_eq_range K f g hinj).symm)
  have he1 : ∀ x, (e1 x : K ⊗[A] M₁) = Z.subtype.baseChange K x := fun x => rfl
  let S := (LinearMap.range (f.baseChange K)).comap (LinearMap.ker (g.baseChange K)).subtype
  let S' := LinearMap.range (T.subtype.baseChange K)
  have hS : S'.map e1.toLinearMap = S := by
    ext y
    simp only [Submodule.mem_map, S, Submodule.mem_comap, Submodule.coe_subtype,
      range_baseChange_eq_map K f g hfg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (he1 x).symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext ((he1 x).trans hxy)⟩
  have hker : S' = LinearMap.ker (T.mkQ.baseChange K) := by
    ext x
    have := congrArg (fun N : Submodule A _ => x ∈ N) (lTensor_mkQ K T)
    exact (Eq.to_iff this).symm
  exact (Submodule.Quotient.equiv S S' e1.symm (by
      rw [← hS]
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e1 x, ⟨x, hx, rfl⟩, by simp⟩)).trans
    ((Submodule.Quotient.equiv S' _ (LinearEquiv.refl _ _) (by simpa using hker)).trans
      ((T.mkQ.baseChange K).quotKerEquivOfSurjective
        (LinearMap.baseChange_surjective K (Submodule.mkQ_surjective T))))

/-- Isomorphic composable pairs have isomorphic homology. -/
noncomputable def homologyAtCongr {R : Type*} [CommRing R] {N₀ N₁ N₂ P₀ P₁ P₂ : Type*}
    [AddCommGroup N₀] [Module R N₀] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂]
    [Module R N₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂] (f : N₀ →ₗ[R] N₁) (g : N₁ →ₗ[R] N₂) (f' : P₀ →ₗ[R] P₁)
    (g' : P₁ →ₗ[R] P₂) (e₀ : N₀ ≃ₗ[R] P₀) (e₁ : N₁ ≃ₗ[R] P₁) (e₂ : N₂ ≃ₗ[R] P₂)
    (h₁ : f' ∘ₗ e₀.toLinearMap = e₁.toLinearMap ∘ₗ f)
    (h₂ : g' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ g) :
    homologyAt f g ≃ₗ[R] homologyAt f' g' := by
  have k₁ : ∀ x, f' (e₀ x) = e₁ (f x) := fun x => LinearMap.congr_fun h₁ x
  have k₂ : ∀ x, g' (e₁ x) = e₂ (g x) := fun x => LinearMap.congr_fun h₂ x
  have hsymm : ∀ y, g' y = 0 → g (e₁.symm y) = 0 := fun y hy => by
    have := k₂ (e₁.symm y)
    rw [LinearEquiv.apply_symm_apply, hy] at this
    exact e₂.injective (by rw [← this, map_zero])
  have hk : (LinearMap.ker g).map e₁.toLinearMap = LinearMap.ker g' := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [k₂, hx, map_zero]
    · exact fun hy => ⟨e₁.symm y, hsymm y hy, by simp⟩
  let ek : LinearMap.ker g ≃ₗ[R] LinearMap.ker g' :=
    (e₁.submoduleMap (LinearMap.ker g)).trans (LinearEquiv.ofEq _ _ hk)
  have hek : ∀ x, (ek x : P₁) = e₁ x := fun x => rfl
  refine Submodule.Quotient.equiv _ _ ek ?_
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨z, hz⟩, hxy⟩
    refine ⟨e₀ z, ?_⟩
    rw [k₁, hz, ← hek, hxy]
  · rintro ⟨z, hz⟩
    refine ⟨⟨e₁.symm y, LinearMap.mem_ker.mpr (hsymm y (LinearMap.mem_ker.mp hy))⟩,
      ⟨e₀.symm z, ?_⟩, ?_⟩
    · apply e₁.injective
      rw [← k₁, LinearEquiv.apply_symm_apply, hz]
      simp
    · apply Subtype.ext
      rw [hek]
      simp

section Complex

variable {A : Type*} [CommRing A] (M : ℤ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  (d : ∀ i, M i →ₗ[A] M (i + 1))

/-- `range (d i)`, seen inside `ker (d (i+1))`, is isomorphic to `range (d i)`. -/
noncomputable def rangeEquivComap (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (i : ℤ) :
    LinearMap.range (d i) ≃ₗ[A]
      (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype :=
  (Submodule.comapSubtypeEquivOfLe (LinearMap.range_le_ker_iff.mpr (hdd i))).symm

/-- For a complex of flat modules that is contractible in degrees at least `b` and has flat
cohomology, the image and the kernel of every differential are flat. -/
theorem flat_range_ker_of_flat_homology (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hflat : ∀ i, Module.Flat A (M i)) (b : ℤ) (h : ∀ j, M (j + 1) →ₗ[A] M j)
    (hh : ∀ j, b ≤ j → ∀ x, d j (h j x) + h (j + 1) (d (j + 1) x) = x)
    (hH : ∀ i, Module.Flat A (homologyAt (d i) (d (i + 1)))) (i : ℤ) :
    Module.Flat A (LinearMap.range (d i)) ∧ Module.Flat A (LinearMap.ker (d i)) := by
  have hker : ∀ j, b ≤ j → Module.Flat A (LinearMap.ker (d (j + 1))) := by
    intro j hj
    have hx : ∀ x ∈ LinearMap.ker (d (j + 1)), d j (h j x) = x := fun x hx => by
      have := hh j hj x
      rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at this
    let r : M (j + 1) →ₗ[A] LinearMap.ker (d (j + 1)) :=
      ((d j) ∘ₗ (h j)).codRestrict _ fun y => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.comp_apply (d (j + 1)), hdd,
          LinearMap.zero_apply]
    exact Module.Flat.of_retract (LinearMap.ker (d (j + 1))).subtype r
      (LinearMap.ext fun x => Subtype.ext (hx x.1 x.2))
  have hbase : ∀ i, b + 1 ≤ i →
      Module.Flat A (LinearMap.range (d i)) ∧ Module.Flat A (LinearMap.ker (d i)) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by ring⟩
    refine ⟨?_, hker j (by omega)⟩
    have heq : LinearMap.range (d (j + 1)) = LinearMap.ker (d (j + 1 + 1)) := by
      refine le_antisymm (LinearMap.range_le_ker_iff.mpr (hdd _)) fun x hx => ⟨h (j + 1) x, ?_⟩
      have := hh (j + 1) (by omega) x
      rwa [LinearMap.mem_ker.mp hx, map_zero, add_zero] at this
    have := hker (j + 1) (by omega)
    rw [heq]
    infer_instance
  have hstep : ∀ i, (Module.Flat A (LinearMap.range (d (i + 1))) ∧
      Module.Flat A (LinearMap.ker (d (i + 1)))) →
      Module.Flat A (LinearMap.range (d i)) ∧ Module.Flat A (LinearMap.ker (d i)) := by
    intro i ⟨_, hk⟩
    have hT : Module.Flat A ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) :=
      flat_of_exact _ Subtype.val_injective _ (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _)
    have hr : Module.Flat A (LinearMap.range (d i)) :=
      Module.Flat.of_linearEquiv (rangeEquivComap M d hdd i)
    refine ⟨hr, ?_⟩
    exact flat_of_exact _ Subtype.val_injective _ (LinearMap.surjective_rangeRestrict _)
      (exact_ker_subtype_rangeRestrict _)
  have hn : ∀ n : ℕ, Module.Flat A (LinearMap.range (d (b + 1 - n))) ∧
      Module.Flat A (LinearMap.ker (d (b + 1 - n))) := by
    intro n
    induction n with
    | zero => exact hbase _ (by simp)
    | succ n ih =>
      have hstep' : ∀ i j : ℤ, j = i + 1 → (Module.Flat A (LinearMap.range (d j)) ∧
          Module.Flat A (LinearMap.ker (d j))) →
          Module.Flat A (LinearMap.range (d i)) ∧ Module.Flat A (LinearMap.ker (d i)) := by
        intro i j hj; subst hj; exact hstep i
      exact hstep' _ _ (by push_cast; ring) ih
  rcases le_or_gt (b + 1) i with hi | hi
  · exact hbase i hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = b + 1 - n := ⟨(b + 1 - i).toNat, by omega⟩
    exact hn n

variable (K : Type*) [CommRing K] [Algebra A K]

/-- For a complex of flat modules that is contractible in degrees at least `b` and has flat
cohomology, the inclusion of the image of every differential stays injective after base change
to `K`. -/
theorem injective_baseChange_range_subtype (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hflat : ∀ i, Module.Flat A (M i)) (b : ℤ) (h : ∀ j, M (j + 1) →ₗ[A] M j)
    (hh : ∀ j, b ≤ j → ∀ x, d j (h j x) + h (j + 1) (d (j + 1) x) = x)
    (hH : ∀ i, Module.Flat A (homologyAt (d i) (d (i + 1)))) (i : ℤ) :
    Function.Injective ((LinearMap.range (d i)).subtype.baseChange K) := by
  set T := (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype
  have hfac : (LinearMap.range (d i)).subtype =
      (LinearMap.ker (d (i + 1))).subtype ∘ₗ T.subtype ∘ₗ
        (rangeEquivComap M d hdd i).toLinearMap := by
    ext x; rfl
  have h1 : Function.Injective ((LinearMap.ker (d (i + 1))).subtype.baseChange K) := by
    have := (flat_range_ker_of_flat_homology M d hdd hflat b h hh hH (i + 1)).1
    exact injective_baseChange_ker_subtype K _
  have h2 : Function.Injective (T.subtype.baseChange K) :=
    LinearMap.lTensor_injective_of_exact_of_flat T.mkQ (Submodule.mkQ_surjective _) T.subtype
      Subtype.val_injective (LinearMap.exact_subtype_mkQ _) K
  have h3 : Function.Injective ((rangeEquivComap M d hdd i).toLinearMap.baseChange K) := by
    have : ((rangeEquivComap M d hdd i).toLinearMap.baseChange K) =
        ((rangeEquivComap M d hdd i).baseChange A K _ _).toLinearMap := rfl
    rw [this]
    exact LinearEquiv.injective _
  rw [hfac, LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  exact h1.comp (h2.comp h3)

/-- **Homology of a bounded above complex of flat modules with flat homology commutes with
every base change.** -/
noncomputable def homologyBaseChangeEquivOfFlat (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hflat : ∀ i, Module.Flat A (M i)) (b : ℤ) (h : ∀ j, M (j + 1) →ₗ[A] M j)
    (hh : ∀ j, b ≤ j → ∀ x, d j (h j x) + h (j + 1) (d (j + 1) x) = x)
    (hH : ∀ i, Module.Flat A (homologyAt (d i) (d (i + 1)))) (i : ℤ) :
    homologyAt ((d i).baseChange K) ((d (i + 1)).baseChange K) ≃ₗ[K]
      K ⊗[A] homologyAt (d i) (d (i + 1)) :=
  have := (flat_range_ker_of_flat_homology M d hdd hflat b h hh hH (i + 1)).1
  homologyAtBaseChangeEquiv K (d i) (d (i + 1)) (hdd i) (injective_baseChange_ker_subtype K _)
    (injective_baseChange_range_subtype M d K hdd hflat b h hh hH (i + 1))

end Complex

/-- **Homology commutes with flat base change.** -/
noncomputable def homologyAtBaseChangeEquivOfFlat {A : Type*} [CommRing A] (K : Type*)
    [CommRing K] [Algebra A K] [Module.Flat A K] {M₀ M₁ M₂ : Type*} [AddCommGroup M₀]
    [Module A M₀] [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    (f : M₀ →ₗ[A] M₁) (g : M₁ →ₗ[A] M₂) (hfg : g ∘ₗ f = 0) :
    homologyAt (f.baseChange K) (g.baseChange K) ≃ₗ[K] K ⊗[A] homologyAt f g :=
  homologyAtBaseChangeEquiv K f g hfg
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

section Main

variable {R : Type*} [CommRing R] (M : ℤ → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (d : ∀ i, M i →ₗ[R] M (i + 1))

/-- The tensor product of an algebra with a subsingleton module is a subsingleton. -/
theorem subsingleton_tensor_right (A N : Type*) [CommRing A] [Algebra R A] [AddCommGroup N]
    [Module R N] [Subsingleton N] : Subsingleton (A ⊗[R] N) :=
  inferInstance

/-- The homology of a composable pair whose middle term is a subsingleton is a subsingleton. -/
theorem subsingleton_homologyAt {N₀ N₁ N₂ : Type*} [AddCommGroup N₀] [Module R N₀]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Subsingleton N₁]
    (f : N₀ →ₗ[R] N₁) (g : N₁ →ₗ[R] N₂) : Subsingleton (homologyAt f g) := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on
  induction y using Submodule.Quotient.induction_on
  congr 1
  exact Subsingleton.elim _ _

/-- For a complex of flat modules contractible in degrees at least `b` whose cohomology is free
after localizing at a prime `p`, the dimension of the cohomology of its base change to a field `L`
in which every element outside `p` is nonzero is the rank of the localized cohomology. -/
theorem finrank_homology_baseChange_eq_of_free (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hflat : ∀ i, Module.Flat R (M i)) (b : ℤ) (h : ∀ j, M (j + 1) →ₗ[R] M j)
    (hh : ∀ j, b ≤ j → ∀ x, d j (h j x) + h (j + 1) (d (j + 1) x) = x)
    (p : Ideal R) [p.IsPrime]
    (hfree : ∀ i, Module.Free (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] homologyAt (d i) (d (i + 1))))
    (L : Type*) [Field L] [Algebra R L] (hL : ∀ x ∉ p, algebraMap R L x ≠ 0) (i : ℤ) :
    Module.finrank L (homologyAt ((d i).baseChange L) ((d (i + 1)).baseChange L)) =
      Module.finrank (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[R] homologyAt (d i) (d (i + 1))) := by
  set A := Localization.AtPrime p
  letI : Algebra A L := (IsLocalization.lift (M := p.primeCompl) (S := A)
    (g := algebraMap R L) (fun y => (Ne.isUnit (hL y y.2)))).toAlgebra
  haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) (S := A) _ x).symm)
  let M' : ℤ → Type _ := fun i => A ⊗[R] M i
  let d' : ∀ i, M' i →ₗ[A] M' (i + 1) := fun i => (d i).baseChange A
  have hdd' : ∀ i, d' (i + 1) ∘ₗ d' i = 0 := fun i => by
    change (d (i + 1)).baseChange A ∘ₗ (d i).baseChange A = 0
    rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]
  have hflat' : ∀ i, Module.Flat A (M' i) := fun i => inferInstance
  let h' : ∀ j, M' (j + 1) →ₗ[A] M' j := fun j => (h j).baseChange A
  have hh' : ∀ j, b ≤ j → ∀ x, d' j (h' j x) + h' (j + 1) (d' (j + 1) x) = x := by
    intro j hj x
    have hlin : d j ∘ₗ h j + h (j + 1) ∘ₗ d (j + 1) = LinearMap.id :=
      LinearMap.ext fun y => hh j hj y
    have := congrArg (fun φ => (φ.baseChange A) x) hlin
    simpa [LinearMap.baseChange_add, LinearMap.baseChange_comp] using this
  let eH : ∀ i, homologyAt (d' i) (d' (i + 1)) ≃ₗ[A] A ⊗[R] homologyAt (d i) (d (i + 1)) :=
    fun i => homologyAtBaseChangeEquivOfFlat A (d i) (d (i + 1)) (hdd i)
  haveI hfree' : ∀ i, Module.Free A (homologyAt (d' i) (d' (i + 1))) := fun i =>
    Module.Free.of_equiv (eH i).symm
  have hH' : ∀ i, Module.Flat A (homologyAt (d' i) (d' (i + 1))) := fun i => inferInstance
  let e₁ := homologyBaseChangeEquivOfFlat M' d' L hdd' hflat' b h' hh' hH' i
  let ec : ∀ j, L ⊗[R] M j ≃ₗ[L] L ⊗[A] M' j := fun j =>
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A L L (M j)).symm
  have hc : ∀ j, ((d' j).baseChange L) ∘ₗ (ec j).toLinearMap =
      (ec (j + 1)).toLinearMap ∘ₗ (d j).baseChange L := by
    intro j
    apply LinearMap.restrictScalars_injective R
    ext x
    rfl
  let e₂ := homologyAtCongr ((d i).baseChange L) ((d (i + 1)).baseChange L)
    ((d' i).baseChange L) ((d' (i + 1)).baseChange L) (ec i) (ec (i + 1)) (ec (i + 1 + 1))
    (hc i) (hc (i + 1))
  rw [(e₂.trans e₁).finrank_eq, Module.finrank_baseChange, (eH i).finrank_eq]

/-- The fraction field of a domain is its localization at the zero ideal. -/
theorem isLocalization_atPrime_bot_fractionRing [IsDomain R] :
    IsLocalization.AtPrime (FractionRing R) (⊥ : Ideal R) := by
  have h : (⊥ : Ideal R).primeCompl = nonZeroDivisors R := by
    ext x
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime
  rw [h]
  infer_instance

/-- **Generic constancy of the fibre cohomology of a bounded complex of flat modules.** Over a
Noetherian domain `R`, for a bounded complex of flat modules with finite cohomology there is a
nonzero `s` such that for every field `L` over `R` in which `s` does not vanish, the dimension of
the cohomology of the base change to `L` is the generic one. -/
theorem exists_finrank_homology_baseChange_eq [IsDomain R] [IsNoetherianRing R]
    (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (hflat : ∀ i, Module.Flat R (M i)) (a b : ℤ)
    (ha : ∀ i, i < a → Subsingleton (M i)) (h : ∀ j, M (j + 1) →ₗ[R] M j)
    (hh : ∀ j, b ≤ j → ∀ x, d j (h j x) + h (j + 1) (d (j + 1) x) = x)
    (hfin : ∀ i, Module.Finite R (homologyAt (d i) (d (i + 1)))) :
    ∃ s : R, s ≠ 0 ∧ ∀ (L : Type*) [Field L] [Algebra R L], algebraMap R L s ≠ 0 → ∀ i,
      Module.finrank L (homologyAt ((d i).baseChange L) ((d (i + 1)).baseChange L)) =
        Module.finrank (FractionRing R) (homologyAt ((d i).baseChange (FractionRing R))
          ((d (i + 1)).baseChange (FractionRing R))) := by
  classical
  have hsub : ∀ i, i ∉ Finset.Icc (a - 1) (b - 1) →
      Subsingleton (homologyAt (d i) (d (i + 1))) := by
    intro i hi
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · have : Subsingleton (M (i + 1)) := ha _ (by omega)
      exact subsingleton_homologyAt _ _
    · refine ⟨fun x y => ?_⟩
      have hz : ∀ z : homologyAt (d i) (d (i + 1)), z = 0 := by
        intro z
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨h i z.1, ?_⟩
          have := hh i (by omega) z.1
          rwa [LinearMap.mem_ker.mp z.2, map_zero, add_zero] at this
      rw [hz x, hz y]
  let U : Set (PrimeSpectrum R) :=
    ⋂ i ∈ Finset.Icc (a - 1) (b - 1), Module.freeLocus R (homologyAt (d i) (d (i + 1)))
  have hUo : IsOpen U := by
    refine isOpen_biInter_finset fun i _ => ?_
    have := Module.finitePresentation_of_finite R (homologyAt (d i) (d (i + 1)))
    exact Module.isOpen_freeLocus
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hηU : η ∈ U := by
    refine Set.mem_iInter₂.mpr fun i _ => ?_
    have := isLocalization_atPrime_bot_fractionRing (R := R)
    exact (Module.mem_freeLocus_iff_tensor η (FractionRing R)).mpr inferInstance
  obtain ⟨_, ⟨s, rfl⟩, hηs, hsU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηU hUo
  have hs0 : s ≠ 0 := by
    intro h
    simp [η, h, PrimeSpectrum.basicOpen] at hηs
  refine ⟨s, hs0, fun L _ _ hLs i => ?_⟩
  let p : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R L), RingHom.ker_isPrime _⟩
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hpU : p ∈ U := hsU ((PrimeSpectrum.mem_basicOpen _ _).mpr
    (by simpa [p, RingHom.mem_ker] using hLs))
  have hfree : ∀ i, Module.Free (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] homologyAt (d i) (d (i + 1))) := by
    intro i
    by_cases hi : i ∈ Finset.Icc (a - 1) (b - 1)
    · exact (Module.mem_freeLocus_iff_tensor p _).mp (Set.mem_iInter₂.mp hpU i hi)
    · have := hsub i hi
      exact Module.Free.of_subsingleton _ _
  rw [finrank_homology_baseChange_eq_of_free M d hdd hflat b h hh p.asIdeal hfree L
      (fun x hx => by simpa [p] using hx) i,
    finrank_homology_baseChange_eq_of_free M d hdd hflat b h hh p.asIdeal hfree (FractionRing R)
      (fun x hx => ?_) i]
  have hx0 : x ≠ 0 := fun h => hx (h ▸ p.asIdeal.zero_mem)
  exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0

/-- **Cohomology of a complex obtained by base change.** If a complex `M₁` over `L` receives
termwise base change maps from a complex `M₀` over `R`, compatible with the differentials, its
cohomology is that of `L ⊗[R] M₀`. -/
noncomputable def homologyAtEquivOfIsBaseChange {L : Type*} [CommRing L] [Algebra R L]
    {M₀ M₁ : ℤ → Type*} [∀ i, AddCommGroup (M₀ i)] [∀ i, Module R (M₀ i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module L (M₁ i)] [∀ i, Module R (M₁ i)]
    [∀ i, IsScalarTower R L (M₁ i)]
    (d₀ : ∀ i, M₀ i →ₗ[R] M₀ (i + 1)) (d₁ : ∀ i, M₁ i →ₗ[L] M₁ (i + 1))
    (Φ : ∀ i, M₀ i →ₗ[R] M₁ i) (hΦ : ∀ i, IsBaseChange L (Φ i))
    (hc : ∀ i x, Φ (i + 1) (d₀ i x) = d₁ i (Φ i x)) (i : ℤ) :
    homologyAt ((d₀ i).baseChange L) ((d₀ (i + 1)).baseChange L) ≃ₗ[L]
      homologyAt (d₁ i) (d₁ (i + 1)) := by
  have key : ∀ j, d₁ j ∘ₗ (hΦ j).equiv.toLinearMap =
      (hΦ (j + 1)).equiv.toLinearMap ∘ₗ (d₀ j).baseChange L := by
    intro j
    refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul, map_smul, hc]
  exact homologyAtCongr _ _ _ _ (hΦ i).equiv (hΦ (i + 1)).equiv (hΦ (i + 1 + 1)).equiv
    (key i) (key (i + 1))

end Main

end AlgebraFlat

/-! ### Algebra: coordinates of a smooth algebra -/

section AlgebraCoordinates

open TensorProduct

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The quotient by one of a system of coordinates is formally smooth. -/
theorem formallySmooth_quotient_span_coord [Algebra.FormallySmooth R B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (i : Fin n) : Algebra.FormallySmooth R (B ⧸ Ideal.span {t i}) := by
  set I := Ideal.span {t i}
  have hker : RingHom.ker (algebraMap B (B ⧸ I)) = I := Ideal.mk_ker
  rw [Algebra.FormallySmooth.iff_split_injection (P := B) Ideal.Quotient.mk_surjective]
  set J := RingHom.ker (algebraMap B (B ⧸ I))
  have htJ : t i ∈ J := by rw [hker]; exact Ideal.subset_span rfl
  let c₀ : J.Cotangent := J.toCotangent ⟨t i, htJ⟩
  let g : B →ₗ[B] J.Cotangent := LinearMap.toSpanSingleton B _ c₀
  have hsmul : ∀ x : B, x ∈ J → x • c₀ = 0 := by
    intro x hx
    have : x • c₀ = J.toCotangent ⟨x * t i, J.mul_mem_left x htJ⟩ := by
      rw [← map_smul]; rfl
    rw [this, Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul hx htJ
  have hg : I ≤ LinearMap.ker g := by
    intro x hx
    rw [LinearMap.mem_ker]
    exact hsmul x (by rw [hker]; exact hx)
  let g' : (B ⧸ I) →ₗ[B] J.Cotangent := Submodule.liftQ I g hg
  refine ⟨g' ∘ₗ (TensorProduct.rid B (B ⧸ I)).toLinearMap ∘ₗ
    LinearMap.lTensor (B ⧸ I) (b.coord i), ?_⟩
  ext z
  obtain ⟨⟨x, hx⟩, rfl⟩ := J.toCotangent_surjective z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    KaehlerDifferential.kerCotangentToTensor_toCotangent, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  have hxI : x ∈ I := by rw [← hker]; exact hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hxI
  rw [show KaehlerDifferential.kerCotangentToTensor R B (B ⧸ I) (J.toCotangent ⟨y * t i, hx⟩) =
    1 ⊗ₜ KaehlerDifferential.D R B (y * t i) from rfl, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, Derivation.leibniz, map_add, map_smul, map_smul, ← hb i,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul,
    mul_one]
  have hg1 : g' 1 = c₀ := by
    change g (1 : B) = c₀
    simp [g]
  rw [hg1, add_smul, map_smul, smul_eq_mul, hsmul _ (J.mul_mem_right _ htJ), add_zero,
    ← map_smul]
  rfl

/-- Two distinct coordinates vanishing at a prime cannot divide each other near that prime. -/
theorem mul_ne_mul_of_basis_D {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (𝔭 : Ideal B) [𝔭.IsPrime] {i k : Fin n} (hik : i ≠ k) (hi : t i ∈ 𝔭) (hk : t k ∈ 𝔭)
    {s c : B} (hs : s ∉ 𝔭) : s * t i ≠ c * t k := by
  intro h
  have hD := congrArg (fun x => b.coord i (KaehlerDifferential.D R B x)) h
  simp only [Derivation.leibniz, map_add, map_smul, ← hb, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hD
  rw [Finsupp.single_apply, if_neg hik.symm, mul_zero, zero_add] at hD
  apply hs
  have : s = t k * (b.repr (KaehlerDifferential.D R B c)) i -
      t i * (b.repr (KaehlerDifferential.D R B s)) i := by
    linear_combination hD
  rw [this]
  exact 𝔭.sub_mem (𝔭.mul_mem_right _ hk) (𝔭.mul_mem_right _ hi)

omit [Algebra R B] in
/-- In a Noetherian ring, an element outside every minimal prime of a radical ideal `J` is a
non-zero-divisor modulo `J`. -/
theorem mem_of_mul_mem_of_forall_minimalPrimes [IsNoetherianRing B] {J : Ideal B}
    (hJ : J.IsRadical) {a x : B} (hx : ∀ 𝔮 ∈ J.minimalPrimes, x ∉ 𝔮) (h : a * x ∈ J) :
    a ∈ J := by
  rw [← hJ.radical, ← Ideal.sInf_minimalPrimes] at h ⊢
  rw [Ideal.mem_sInf] at h ⊢
  intro 𝔮 h𝔮
  exact (h𝔮.1.1.mem_or_mem (h h𝔮)).resolve_right (hx 𝔮 h𝔮)

omit [Algebra R B] in
/-- At a minimal prime `𝔮` of a radical ideal `J` of a Noetherian ring, every element of `𝔮`
times some element outside `𝔮` lies in `J`. -/
theorem exists_mul_mem_of_mem_minimalPrimes_of_isRadical [IsNoetherianRing B] {J : Ideal B}
    (hJ : J.IsRadical) {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ J.minimalPrimes) {x : B} (hx : x ∈ 𝔮) :
    ∃ y ∉ 𝔮, x * y ∈ J := by
  classical
  have hfin : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing B J
  have hp : 𝔮.IsPrime := h𝔮.1.1
  have hsep : ∀ 𝔮' ∈ J.minimalPrimes, 𝔮' ≠ 𝔮 → ∃ y ∈ 𝔮', y ∉ 𝔮 := by
    intro 𝔮' h𝔮' hne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (le_antisymm hcon (h𝔮.2 ⟨h𝔮'.1.1, h𝔮'.1.2⟩ hcon))
  choose! yf hyf₁ hyf₂ using hsep
  let F := (hfin.toFinset.erase 𝔮)
  refine ⟨∏ 𝔮' ∈ F, yf 𝔮', ?_, ?_⟩
  · intro hmem
    haveI := hp
    obtain ⟨𝔮', h𝔮'F, hmem'⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    obtain ⟨hne, h𝔮'm⟩ := Finset.mem_erase.mp h𝔮'F
    exact hyf₂ 𝔮' ((Set.Finite.mem_toFinset _).mp h𝔮'm) hne hmem'
  · rw [← hJ.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔮'' h𝔮''
    by_cases he : 𝔮'' = 𝔮
    · subst he; exact Ideal.mul_mem_right _ _ hx
    · refine Ideal.mul_mem_left _ _ ?_
      have hmem : 𝔮'' ∈ F := Finset.mem_erase.mpr ⟨he, (Set.Finite.mem_toFinset _).mpr h𝔮''⟩
      rw [← Finset.mul_prod_erase F _ hmem]
      exact Ideal.mul_mem_right _ _ (hyf₁ 𝔮'' h𝔮'' he)

/-- A coordinate lies in no minimal prime of the (radical) ideal of another coordinate. -/
theorem notMem_of_mem_minimalPrimes_span_coord [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    {i k : Fin n} (hik : i ≠ k) (hrad : (Ideal.span {t k}).IsRadical)
    {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ (Ideal.span {t k}).minimalPrimes) : t i ∉ 𝔮 := by
  intro hi
  have hp : 𝔮.IsPrime := h𝔮.1.1
  have hk : t k ∈ 𝔮 := h𝔮.1.2 (Ideal.subset_span rfl)
  obtain ⟨y, hy, hmem⟩ := exists_mul_mem_of_mem_minimalPrimes_of_isRadical hrad h𝔮 hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact mul_ne_mul_of_basis_D t b hb 𝔮 hik hi hk hy (by rw [mul_comm, ← hc])

/-- **The ideal of a product of distinct coordinates is the intersection of their ideals**, when
each coordinate ideal is radical; in particular it is radical. -/
theorem span_prod_eq_iInf_of_basis_D [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) (hrad : ∀ k ∈ S, (Ideal.span {t k}).IsRadical) :
    Ideal.span {∏ i ∈ S, t i} = ⨅ i ∈ S, Ideal.span {t i} := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hkS ih =>
    rw [Finset.prod_insert hkS, Finset.iInf_insert,
      ← ih (fun j hj => hrad j (Finset.mem_insert_of_mem hj))]
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_mul_right _ _
      · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_mul_left _ _
    · intro x ⟨hxk, hxS⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hxS
      have ha : a ∈ Ideal.span {t k} := by
        refine mem_of_mul_mem_of_forall_minimalPrimes (hrad k (Finset.mem_insert_self _ _))
          (fun 𝔮 h𝔮 hmem => ?_) hxk
        haveI hp : 𝔮.IsPrime := h𝔮.1.1
        obtain ⟨i, hiS, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
        exact notMem_of_mem_minimalPrimes_span_coord t b hb
          (fun h : i = k => hkS (h ▸ hiS)) (hrad k (Finset.mem_insert_self _ _)) h𝔮 hi
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩

/-- For coordinates `t` whose differentials form a Kähler basis, the ideal of a product of
distinct coordinates with radical ideals is radical. -/
theorem isRadical_span_prod_of_basis_D [IsNoetherianRing B] {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (S : Finset (Fin n)) (hrad : ∀ k ∈ S, (Ideal.span {t k}).IsRadical) :
    (Ideal.span {∏ i ∈ S, t i}).IsRadical := by
  rw [span_prod_eq_iInf_of_basis_D t b hb S hrad]
  intro x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  intro i hi
  exact hrad i hi (by
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hm i) hi⟩)

omit [Algebra R B] in
/-- An ideal with regular quotient is radical. -/
theorem isRadical_of_isRegularRing_quotient (I : Ideal B) [IsRegularRing (B ⧸ I)] :
    I.IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  refine isReduced_ofLocalizationMaximal _ (fun P _ => ?_)
  have := IsRegularLocalRing.isDomain (Localization.AtPrime P)
  infer_instance

/-- The quotient of a smooth algebra over a regular ring by a coordinate is regular. -/
theorem isRegularRing_quotient_span_coord [IsRegularRing R] [Algebra.Smooth R B] {n : ℕ}
    (t : Fin n → B) (b : Module.Basis (Fin n) B Ω[B⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R B (t i)) (i : Fin n) :
    IsRegularRing (B ⧸ Ideal.span {t i}) := by
  have := formallySmooth_quotient_span_coord t b hb i
  have : Algebra.FinitePresentation R (B ⧸ Ideal.span {t i}) :=
    Algebra.FinitePresentation.quotient ⟨{t i}, by simp⟩
  have : Algebra.Smooth R (B ⧸ Ideal.span {t i}) := ⟨inferInstance, inferInstance⟩
  exact Algebra.isRegularRing_of_smooth R _

omit [Algebra R B] in
/-- If `B ⧸ I` is regular, at most one minimal prime of `I` lies below a given prime. -/
theorem minimalPrimes_eq_of_le_of_isRegularRing (I : Ideal B) [IsRegularRing (B ⧸ I)]
    (𝔭 : Ideal B) [𝔭.IsPrime] {𝔮₁ 𝔮₂ : Ideal B} (h₁ : 𝔮₁ ∈ I.minimalPrimes)
    (h₂ : 𝔮₂ ∈ I.minimalPrimes) (h₁𝔭 : 𝔮₁ ≤ 𝔭) (h₂𝔭 : 𝔮₂ ≤ 𝔭) : 𝔮₁ = 𝔮₂ := by
  have hI𝔭 : I ≤ 𝔭 := h₁.1.2.trans h₁𝔭
  set A := B ⧸ I
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔭 := by rw [Ideal.mk_ker]; exact hI𝔭
  haveI hP : (𝔭.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  set P := 𝔭.map (Ideal.Quotient.mk I)
  have := IsRegularLocalRing.isDomain (Localization.AtPrime P)
  set κ := RingHom.ker (algebraMap A (Localization.AtPrime P))
  haveI : κ.IsPrime := RingHom.ker_isPrime _
  have key : ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≤ 𝔭 → 𝔮 = κ.comap (Ideal.Quotient.mk I) := by
    intro 𝔮 h𝔮 h𝔮𝔭
    haveI : 𝔮.IsPrime := h𝔮.1.1
    have hker𝔮 : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔮 := by rw [Ideal.mk_ker]; exact h𝔮.1.2
    have hle : κ.comap (Ideal.Quotient.mk I) ≤ 𝔮 := by
      intro x hx
      have hx' : algebraMap A (Localization.AtPrime P) (Ideal.Quotient.mk I x) = 0 := hx
      obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).mp hx'
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      have hs' : s' ∉ 𝔭 := by
        intro h; exact hs (Ideal.mem_map_of_mem _ h)
      have : s' * x ∈ 𝔮 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hsx
        exact h𝔮.1.2 hsx
      exact ((Ideal.IsPrime.mem_or_mem inferInstance this).resolve_left
        (fun h => hs' (h𝔮𝔭 h)))
    refine le_antisymm ?_ hle
    exact h𝔮.2 ⟨Ideal.IsPrime.comap _, by
      intro x hx
      show algebraMap A _ (Ideal.Quotient.mk I x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]⟩ hle
  rw [key 𝔮₁ h₁ h₁𝔭, key 𝔮₂ h₂ h₂𝔭]

omit [Algebra R B] in
/-- Away from the other minimal primes, a radical ideal agrees with its minimal prime. -/
theorem mul_mem_of_mem_minimalPrimes_of_forall_ne {I : Ideal B} (hI : I.IsRadical)
    {𝔮₀ : Ideal B} (h𝔮₀ : 𝔮₀ ∈ I.minimalPrimes) {h : B}
    (hh : ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≠ 𝔮₀ → h ∈ 𝔮) {x : B} (hx : x ∈ 𝔮₀) : x * h ∈ I := by
  rw [← hI.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro 𝔮 h𝔮
  by_cases he : 𝔮 = 𝔮₀
  · subst he
    exact Ideal.mul_mem_right _ _ hx
  · exact Ideal.mul_mem_left _ _ (hh 𝔮 h𝔮 he)

omit [Algebra R B] in
/-- An element outside a prime `𝔭` lying in every minimal prime of `I` other than a given
one. -/
theorem exists_notMem_forall_minimalPrimes_ne [IsNoetherianRing B] {I : Ideal B} (𝔭 : Ideal B)
    [𝔭.IsPrime] {𝔮₀ : Ideal B} (huniq : ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≤ 𝔭 → 𝔮 = 𝔮₀) :
    ∃ h ∉ 𝔭, ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≠ 𝔮₀ → h ∈ 𝔮 := by
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hsep : ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≠ 𝔮₀ → ∃ a ∈ 𝔮, a ∉ 𝔭 := by
    intro 𝔮 h𝔮 hne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (huniq 𝔮 h𝔮 hcon)
  choose! af haf₁ haf₂ using hsep
  let F := hfin.toFinset.filter (· ≠ 𝔮₀)
  refine ⟨∏ 𝔮 ∈ F, af 𝔮, ?_, ?_⟩
  · intro hmem
    obtain ⟨𝔮, h𝔮F, hmem'⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    obtain ⟨h𝔮m, hne⟩ := Finset.mem_filter.mp h𝔮F
    exact haf₂ 𝔮 ((Set.Finite.mem_toFinset _).mp h𝔮m) hne hmem'
  · intro 𝔮 h𝔮 hne
    have hmem : 𝔮 ∈ F := Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr h𝔮, hne⟩
    rw [← Finset.mul_prod_erase F _ hmem]
    exact Ideal.mul_mem_right _ _ (haf₁ 𝔮 h𝔮 hne)

/-- A Kähler basis by differentials of elements survives a formally étale extension. -/
theorem exists_basis_D_of_formallyEtale {S T : Type*} [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {n : ℕ}
    (t : Fin n → S) (b : Module.Basis (Fin n) S Ω[S⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R S (t i)) :
    ∃ b' : Module.Basis (Fin n) T Ω[T⁄R],
      ∀ i, b' i = KaehlerDifferential.D R T (algebraMap S T (t i)) := by
  refine ⟨(b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T),
    fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    ← KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearEquiv.apply_symm_apply]

/-- A coordinate vanishing at a prime is not killed by an element outside the prime. -/
theorem mul_ne_zero_of_basis_D {n : ℕ} (t : Fin n → B)
    (b : Module.Basis (Fin n) B Ω[B⁄R]) (hb : ∀ i, b i = KaehlerDifferential.D R B (t i))
    (𝔭 : Ideal B) [𝔭.IsPrime] {i : Fin n} (hi : t i ∈ 𝔭) {s : B} (hs : s ∉ 𝔭) :
    s * t i ≠ 0 := by
  intro h
  have hD := congrArg (fun x => b.coord i (KaehlerDifferential.D R B x)) h
  simp only [Derivation.leibniz, map_add, map_smul, ← hb, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero] at hD
  apply hs
  have : s = - (t i * (b.repr (KaehlerDifferential.D R B s)) i) := by linear_combination hD
  rw [this]
  exact 𝔭.neg_mem (𝔭.mul_mem_right _ hi)

/-- A minimal prime of a coordinate ideal in a Noetherian ring has height one. -/
theorem height_eq_one_of_mem_minimalPrimes_span_coord [IsNoetherianRing B] {n : ℕ}
    (t : Fin n → B) (b : Module.Basis (Fin n) B Ω[B⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R B (t i)) {i : Fin n} {𝔮 : Ideal B}
    (h𝔮 : 𝔮 ∈ (Ideal.span {t i}).minimalPrimes)
    (hdom : ∀ (P : Ideal B) [P.IsPrime], IsDomain (Localization.AtPrime P)) :
    𝔮.height = 1 := by
  haveI : 𝔮.IsPrime := h𝔮.1.1
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ h𝔮) ?_
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  intro h0
  rw [Ideal.height_eq_zero_iff] at h0
  have := hdom 𝔮
  set κ := RingHom.ker (algebraMap B (Localization.AtPrime 𝔮))
  haveI : κ.IsPrime := RingHom.ker_isPrime _
  have hκ : κ ≤ 𝔮 := by
    intro x hx
    obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl _ x).mp hx
    exact ((Ideal.IsPrime.mem_or_mem inferInstance (hmx ▸ 𝔮.zero_mem)).resolve_left hm)
  have hκ𝔮 : κ = 𝔮 := le_antisymm hκ (h0.2 ⟨inferInstance, bot_le⟩ hκ)
  have hti : t i ∈ κ := hκ𝔮 ▸ h𝔮.1.2 (Ideal.subset_span rfl)
  obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff 𝔮.primeCompl _ (t i)).mp hti
  exact mul_ne_zero_of_basis_D t b hb 𝔮 (h𝔮.1.2 (Ideal.subset_span rfl)) hm hmx

end AlgebraCoordinates

/-- `ℍ^j(Y, K)` over `Γ(T, ⊤)`, for a bounded below complex of `h⁻¹𝒪_T`-modules on `Y`. -/
noncomputable def Hc {Y T : Scheme.{0}} (h : Y ⟶ T)
    (K : CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf)))) (j : ℤ) :
    ModuleCat.{0} Γ(T, ⊤) :=
  let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))
      (op ⊤)).rightDerivedFunctorPlus
  let M := (DerivedCategory.homologyFunctor _ j).obj
    (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj K)))
  (ModuleCat.restrictScalars.{0} (show Γ(T, ⊤) →+*
      ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf).obj.obj (op ⊤) from
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
      T.sheaf).hom.app (op ⊤)).hom)).obj M

/-- The Hodge complex `Ω^p(log D)` (twisted by `-D` if `twist`) placed in degree `0`. -/
noncomputable def hodgeCx {Y T : Scheme.{0}} (n : ℕ) (f : Y ⟶ T)
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y) (hD : D.IsRelativeSNC n f)
    (twist : Bool) (p : ℕ) :
    CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj T.sheaf))) :=
  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    ((MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD
      (bif twist then D.suppIdeal else ⊤)).X p),
    0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩

/-- The logarithmic de Rham complex (twisted by `-D` if `twist`), extended by zero to `ℤ`. -/
noncomputable def deRhamCx {Y T : Scheme.{0}} (n : ℕ) (f : Y ⟶ T)
    [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y) (hD : D.IsRelativeSNC n f)
    (twist : Bool) :
    CochainComplex.Plus (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj T.sheaf))) :=
  ⟨(MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD
    (bif twist then D.suppIdeal else ⊤)).extend ComplexShape.embeddingUpNat,
    0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩

/-- A *weak chart* of a closed set `Z` for `g : 𝒳 ⟶ S`: an affine open `W` with relative
coordinates `t` (over the global sections of `S`) whose differentials form a basis, such that
`Z ∩ W` is the zero locus of the product of the first `r` coordinates. -/
structure WeakChart {𝒳 S : Scheme.{0}} (g : 𝒳 ⟶ S) (n : ℕ) (Z : Set 𝒳) where
  /-- The affine open of the chart. -/
  W : 𝒳.affineOpens
  /-- The coordinates on `W`. -/
  t : Fin n → Γ(𝒳, W)
  /-- The number of boundary coordinates. -/
  r : ℕ
  /-- There are at most `n` boundary coordinates. -/
  hr : r ≤ n
  /-- The differentials of the coordinates form a basis of the relative Kähler differentials. -/
  basis : letI := (g.appLE ⊤ W le_top).hom.toAlgebra
    ∃ b : Module.Basis (Fin n) Γ(𝒳, W) Ω[Γ(𝒳, W)⁄Γ(S, ⊤)],
      ∀ i, b i = KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) (t i)
  /-- On `W`, the set `Z` is the zero locus of the product of the boundary coordinates. -/
  zero : Z ∩ (W : Set 𝒳) = 𝒳.zeroLocus {∏ i : Fin r, t (Fin.castLE hr i)} ∩ (W : Set 𝒳)

/-- A basis of Kähler differentials given by the differentials of elements is preserved by base
change. -/
theorem exists_basis_D_of_isPushout {R S A B : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {n : ℕ} (t : Fin n → A) (b : Module.Basis (Fin n) A Ω[A⁄R])
    (hb : ∀ i, b i = KaehlerDifferential.D R A (t i)) :
    ∃ b' : Module.Basis (Fin n) B Ω[B⁄S],
      ∀ i, b' i = KaehlerDifferential.D S B (algebraMap A B (t i)) := by
  refine ⟨(b.baseChange B).map (KaehlerDifferential.tensorKaehlerEquiv R S A B), fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb,
    KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]

/-- Equal morphisms of schemes have equal maps `appLE` on sections. -/
theorem appLE_eq_of_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (hab : a = b) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ a ⁻¹ᵁ U) (e' : V ≤ b ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V e' := by
  subst hab; rfl

/-- **Weak charts pull back.** Along a cartesian square, the preimage of a weak chart over an
affine open of the new base is a weak chart of the preimage of the closed set, with the pulled
back coordinates. -/
theorem WeakChart.exists_baseChange {n : ℕ} {𝒳 S Y T : Scheme.{0}} [IsAffine S]
    [IsAffine T] {g : 𝒳 ⟶ S} {Z : Set 𝒳} (c : WeakChart g n Z) {q : Y ⟶ 𝒳} {f : Y ⟶ T}
    {φ : T ⟶ S} (H : IsPullback q f g φ) :
    ∃ c' : WeakChart f n (q.base ⁻¹' Z),
      (c'.W : Y.Opens) = q ⁻¹ᵁ (c.W : 𝒳.Opens) ⊓ f ⁻¹ᵁ ⊤ ∧ c'.r = c.r ∧
      ∃ hle : (c'.W : Y.Opens) ≤ q ⁻¹ᵁ (c.W : 𝒳.Opens),
        ∀ i, c'.t i = (q.appLE c.W c'.W hle).hom (c.t i) := by
  set W' : Y.Opens := q ⁻¹ᵁ (c.W : 𝒳.Opens) ⊓ f ⁻¹ᵁ ⊤
  have hV' : (⊤ : T.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top
  have hW'aff : IsAffineOpen W' :=
    IsAffineOpen.inf_preimage_of_isPullback H (isAffineOpen_top S) c.W.2 le_top
      (isAffineOpen_top T) hV' rfl
  have e₁ : W' ≤ q ⁻¹ᵁ (c.W : 𝒳.Opens) := inf_le_left
  have e' : W' ≤ f ⁻¹ᵁ ⊤ := inf_le_right
  let t' : Fin n → Γ(Y, W') := fun i => (q.appLE c.W W' e₁).hom (c.t i)
  have hbasis : letI := (f.appLE ⊤ W' e').hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W') Ω[Γ(Y, W')⁄Γ(T, ⊤)],
        ∀ i, b i = KaehlerDifferential.D Γ(T, ⊤) Γ(Y, W') (t' i) := by
    letI : Algebra Γ(S, ⊤) Γ(𝒳, c.W) := (g.appLE ⊤ c.W le_top).hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := (φ.appLE ⊤ ⊤ hV').hom.toAlgebra
    letI : Algebra Γ(𝒳, c.W) Γ(Y, W') := (q.appLE c.W W' e₁).hom.toAlgebra
    letI : Algebra Γ(T, ⊤) Γ(Y, W') := (f.appLE ⊤ W' e').hom.toAlgebra
    letI : Algebra Γ(S, ⊤) Γ(Y, W') :=
      (g.appLE ⊤ c.W le_top ≫ q.appLE c.W W' e₁).hom.toAlgebra
    haveI : IsScalarTower Γ(S, ⊤) Γ(𝒳, c.W) Γ(Y, W') :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hcomm : φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e' =
        g.appLE ⊤ c.W le_top ≫ q.appLE c.W W' e₁ := by
      rw [Scheme.Hom.appLE_comp_appLE f φ ⊤ ⊤ W' hV' e',
        Scheme.Hom.appLE_comp_appLE q g ⊤ c.W W' le_top e₁]
      exact appLE_eq_of_eq H.w.symm _ _
    haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, W') :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        change _ = (φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e').hom x
        rw [hcomm]; rfl)
    haveI : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(𝒳, c.W) Γ(Y, W') :=
      algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) c.W.2 le_top
        (isAffineOpen_top T) hV' rfl
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨b, hb⟩ := c.basis
    exact exists_basis_D_of_isPushout c.t b hb
  refine ⟨⟨⟨W', hW'aff⟩, t', c.r, c.hr, hbasis, ?_⟩, rfl, rfl, e₁, fun i => rfl⟩
  have hprod : (∏ i : Fin c.r, t' (Fin.castLE c.hr i)) =
      (q.appLE c.W W' e₁).hom (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) := by
    simp [t', map_prod]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.mem_zeroLocus_iff,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hyZ, hyW⟩
    refine ⟨?_, hyW⟩
    have hqW : q.base y ∈ (c.W : Set 𝒳) := e₁ hyW
    have h₀ : q.base y ∈ Z ∩ (c.W : Set 𝒳) := ⟨hyZ, hqW⟩
    rw [c.zero] at h₀
    have h₁ := (Scheme.mem_zeroLocus_iff _ _ _).mp h₀.1 _ rfl
    intro hy
    rw [hprod, Scheme.basicOpen_appLE] at hy
    exact h₁ hy.2
  · rintro ⟨hy, hyW⟩
    refine ⟨?_, hyW⟩
    have hqW : q.base y ∈ (c.W : Set 𝒳) := e₁ hyW
    have : q.base y ∈ Z ∩ (c.W : Set 𝒳) := by
      rw [c.zero]
      refine ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, hqW⟩
      rintro _ rfl hqb
      apply hy
      rw [hprod, Scheme.basicOpen_appLE]
      exact ⟨hyW, hqb⟩
    exact this.1

/-! ### Points of an affine open and primes of its ring of sections -/

section AffinePoints

variable {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)

/-- The point of an affine open `W` attached to a prime of `Γ(Y, W)` lies in `W`. -/
theorem fromSpec_mem (P : PrimeSpectrum Γ(Y, W)) : hW.fromSpec P ∈ W := by
  rw [← SetLike.mem_coe, ← hW.range_fromSpec]; exact ⟨P, rfl⟩

/-- Distinct primes of `Γ(Y, W)` give distinct points of `Y`. -/
theorem fromSpec_injective : Function.Injective hW.fromSpec :=
  hW.fromSpec.isOpenEmbedding.injective

/-- The point of `P` specializes to the point of `Q` if and only if `P ≤ Q`. -/
theorem fromSpec_specializes_iff (P Q : PrimeSpectrum Γ(Y, W)) :
    hW.fromSpec P ⤳ hW.fromSpec Q ↔ P ≤ Q :=
  (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff (x := P) (y := Q)).trans
    (PrimeSpectrum.le_iff_specializes P Q).symm

/-- The prime of `Γ(Y, W)` attached to the point of a prime `P` is `P`. -/
theorem primeIdealOf_fromSpec (P : PrimeSpectrum Γ(Y, W)) :
    hW.primeIdealOf ⟨hW.fromSpec P, fromSpec_mem hW P⟩ = P :=
  fromSpec_injective hW (hW.fromSpec_primeIdealOf _)

/-- The point of a prime `P` lies in the basic open of `s` if and only if `s ∉ P`. -/
theorem fromSpec_mem_basicOpen (P : PrimeSpectrum Γ(Y, W)) (s : Γ(Y, W)) :
    hW.fromSpec P ∈ Y.basicOpen s ↔ s ∉ P.asIdeal := by
  change P ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen s ↔ _
  rw [hW.fromSpec_preimage_basicOpen]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The coheight of the point of a prime `P` is the height of `P`. -/
theorem coheight_fromSpec (P : PrimeSpectrum Γ(Y, W)) :
    Order.coheight (hW.fromSpec P) = P.asIdeal.height := by
  have h1 := ringKrullDim_stalk_eq_coheight (hW.fromSpec P)
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hW.fromSpec P, fromSpec_mem hW P⟩
  have := hW.isLocalization_stalk' P (fromSpec_mem hW P)
  have h2 := @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ P.asIdeal _ _ _
    (TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hW.fromSpec P, fromSpec_mem hW P⟩) this
  exact_mod_cast h1.symm.trans h2

/-- Localizing a radical ideal away from its other minimal primes gives a prime ideal, whose
primes above correspond to the primes above the remaining minimal prime. -/
theorem isPrime_map_and_le_iff {B Bh : Type*} [CommRing B] [CommRing Bh] [Algebra B Bh]
    {h : B} [IsLocalization.Away h Bh] {J 𝔮 : Ideal B} (hJ : J.IsRadical)
    (h𝔮 : 𝔮 ∈ J.minimalPrimes) (hh : ∀ 𝔮' ∈ J.minimalPrimes, 𝔮' ≠ 𝔮 → h ∈ 𝔮')
    (h𝔮h : h ∉ 𝔮) :
    J.map (algebraMap B Bh) = 𝔮.map (algebraMap B Bh) ∧ (J.map (algebraMap B Bh)).IsPrime ∧
      ∀ Q : Ideal Bh, Q.IsPrime →
        (J.map (algebraMap B Bh) ≤ Q ↔ 𝔮 ≤ Q.comap (algebraMap B Bh)) := by
  haveI : 𝔮.IsPrime := h𝔮.1.1
  have hunit : IsUnit (algebraMap B Bh h) := IsLocalization.Away.algebraMap_isUnit h
  have hdisj : Disjoint (Submonoid.powers h : Set B) 𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ hm
    exact h𝔮h (Ideal.IsPrime.mem_of_pow_mem inferInstance m hm)
  have heq : J.map (algebraMap B Bh) = 𝔮.map (algebraMap B Bh) := by
    refine le_antisymm (Ideal.map_mono h𝔮.1.2) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have : algebraMap B Bh x * algebraMap B Bh h ∈ J.map (algebraMap B Bh) := by
      simpa only [map_mul] using Ideal.mem_map_of_mem (algebraMap B Bh)
        (mul_mem_of_mem_minimalPrimes_of_forall_ne hJ h𝔮 hh hx)
    change algebraMap B Bh x ∈ J.map (algebraMap B Bh)
    obtain ⟨u, hu⟩ := hunit
    have h2 := Ideal.mul_mem_right (↑u⁻¹ : Bh) _ this
    rwa [← hu, mul_assoc, Units.mul_inv, mul_one] at h2
  have hprime : (J.map (algebraMap B Bh)).IsPrime := by
    rw [heq]
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) Bh 𝔮 inferInstance hdisj
  refine ⟨heq, hprime, fun Q hQ => ?_⟩
  rw [heq, Ideal.map_le_iff_le_comap]

/-- The vanishing ideal of the zero locus of one element. -/
theorem vanishingIdeal_zeroLocus_singleton {R : Type*} [CommRing R] (s : R) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus {s}) = (Ideal.span {s}).radical := by
  rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

/-- The points of the spectrum of the sections over a basic open, read in the ambient affine
open. -/
theorem fromSpec_basicOpen_apply {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (h : Γ(Y, W)) (Q : PrimeSpectrum Γ(Y, Y.basicOpen h)) :
    (hW.basicOpen h).fromSpec Q = hW.fromSpec
      (PrimeSpectrum.comap (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom Q) := by
  rw [← hW.map_fromSpec (hW.basicOpen h) (homOfLE (Y.basicOpen_le h)).op]
  rfl

/-- The ideal of a prime divisor on an affine open. -/
theorem idealSheaf_ideal_eq {Y : Scheme.{0}} (E : AlgebraicGeometry.PrimeDivisor Y)
    (U : Y.affineOpens) :
    E.idealSheaf.ideal U = PrimeSpectrum.vanishingIdeal
      (U.2.fromSpec ⁻¹' closure {AlgebraicGeometry.PrimeDivisor.genericPoint E}) := by
  have h := Stacks.Chow.integralComponentAt_genericPointOf E.idealSheaf E.integral
  conv_lhs => rw [← h]
  rw [Stacks.Chow.integralComponentAt, Scheme.IdealSheafData.vanishingIdeal_ideal]
  rfl

/-- **The ideal of a component on a basic open.** -/
theorem idealSheaf_ideal_basicOpen_eq {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    {h T : Γ(Y, W)} (hJ : (Ideal.span {T}).IsRadical) {𝔮 : Ideal Γ(Y, W)}
    (h𝔮 : 𝔮 ∈ (Ideal.span {T}).minimalPrimes)
    (hh : ∀ 𝔮' ∈ (Ideal.span {T}).minimalPrimes, 𝔮' ≠ 𝔮 → h ∈ 𝔮') (h𝔮h : h ∉ 𝔮)
    (E : AlgebraicGeometry.PrimeDivisor Y)
    (hE : AlgebraicGeometry.PrimeDivisor.genericPoint E = hW.fromSpec ⟨𝔮, h𝔮.1.1⟩) :
    E.idealSheaf.ideal ⟨Y.basicOpen h, hW.basicOpen h⟩ =
      Ideal.span {(Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom T} := by
  set ρ := (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom
  letI : Algebra Γ(Y, W) Γ(Y, Y.basicOpen h) := ρ.toAlgebra
  haveI : IsLocalization.Away h Γ(Y, Y.basicOpen h) := hW.isLocalization_basicOpen h
  obtain ⟨-, hprime, hle⟩ := isPrime_map_and_le_iff (Bh := Γ(Y, Y.basicOpen h)) hJ h𝔮 hh h𝔮h
  have hspan : (Ideal.span {T}).map (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen h)) =
      Ideal.span {ρ T} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  rw [hspan] at hprime hle
  have hset : ∀ Q : PrimeSpectrum Γ(Y, Y.basicOpen h),
      (hW.basicOpen h).fromSpec Q ∈ closure {hW.fromSpec ⟨𝔮, h𝔮.1.1⟩} ↔
        Q ∈ PrimeSpectrum.zeroLocus {ρ T} := by
    intro Q
    rw [← specializes_iff_mem_closure, fromSpec_basicOpen_apply hW h Q,
      fromSpec_specializes_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    change 𝔮 ≤ Ideal.comap ρ Q.asIdeal ↔ ρ T ∈ Q.asIdeal
    exact (hle Q.asIdeal Q.isPrime).symm.trans
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; rfl)
  have hset' : ((hW.basicOpen h).fromSpec ⁻¹' closure {hW.fromSpec ⟨𝔮, h𝔮.1.1⟩} :
      Set (PrimeSpectrum Γ(Y, Y.basicOpen h))) = PrimeSpectrum.zeroLocus {ρ T} :=
    Set.ext hset
  rw [idealSheaf_ideal_eq, hE]
  calc PrimeSpectrum.vanishingIdeal ((hW.basicOpen h).fromSpec ⁻¹' closure
        {hW.fromSpec ⟨𝔮, h𝔮.1.1⟩}) = PrimeSpectrum.vanishingIdeal
          (PrimeSpectrum.zeroLocus {ρ T}) := congrArg _ hset'
    _ = _ := by rw [vanishingIdeal_zeroLocus_singleton, hprime.radical]

/-- **The vanishing ideal of a closed set cut out on an affine open by one function**, on a
basic open of that affine open. -/
theorem vanishingIdeal_ideal_basicOpen_eq {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (h s : Γ(Y, W)) (Z : TopologicalSpace.Closeds Y)
    (hZ : (Z : Set Y) ∩ W = Y.zeroLocus {s} ∩ W) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨Y.basicOpen h, hW.basicOpen h⟩ =
      (Ideal.span {(Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom s}).radical := by
  set ρ := (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom
  have hset : ∀ Q : PrimeSpectrum Γ(Y, Y.basicOpen h),
      (hW.basicOpen h).fromSpec Q ∈ (Z : Set Y) ↔ Q ∈ PrimeSpectrum.zeroLocus {ρ s} := by
    intro Q
    have hQW : (hW.basicOpen h).fromSpec Q ∈ W :=
      Y.basicOpen_le h (fromSpec_mem (hW.basicOpen h) Q)
    have h1 : (hW.basicOpen h).fromSpec Q ∈ (Z : Set Y) ↔
        (hW.basicOpen h).fromSpec Q ∈ Y.zeroLocus {s} :=
      ⟨fun hz => (hZ.subset ⟨hz, hQW⟩).1, fun hz => (hZ.symm.subset ⟨hz, hQW⟩).1⟩
    rw [h1, Scheme.mem_zeroLocus_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [fromSpec_basicOpen_apply hW h Q, fromSpec_mem_basicOpen, not_not]
    rfl
  have hset' : ((hW.basicOpen h).fromSpec ⁻¹' (Z : Set Y) :
      Set (PrimeSpectrum Γ(Y, Y.basicOpen h))) = PrimeSpectrum.zeroLocus {ρ s} :=
    Set.ext hset
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  calc PrimeSpectrum.vanishingIdeal ((hW.basicOpen h).fromSpec ⁻¹' (Z : Set Y)) =
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus {ρ s}) := congrArg _ hset'
    _ = _ := vanishingIdeal_zeroLocus_singleton _

end AffinePoints

/-! ### Simple normal crossings charts from weak charts -/

section SNCCharts

/-- The global sections of the spectrum of a regular ring form a regular ring. -/
theorem isRegularRing_Γ_top {A : CommRingCat.{0}} [IsRegularRing A] :
    IsRegularRing Γ(Spec A, ⊤) :=
  IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv

/-- For a smooth `f : Y ⟶ Spec A`, the sections over an affine open of `Y` are smooth over the
global sections of `Spec A`. -/
theorem smooth_appLE_top {Y : Scheme.{0}} {A : CommRingCat.{0}} (f : Y ⟶ Spec A)
    [Smooth f] (W : Y.affineOpens) :
    letI := (f.appLE ⊤ W le_top).hom.toAlgebra
    Algebra.Smooth Γ(Spec A, ⊤) Γ(Y, W) :=
  (f.smooth_appLE (isAffineOpen_top _) W.2 le_top).toAlgebra

/-- The pullback of a global section of `S` to `W' ≤ W` is the restriction of its pullback to
`W`. -/
theorem appLE_top_comp_map {Y S : Scheme.{0}} (f : Y ⟶ S) {W W' : Y.Opens}
    (h : W' ≤ W) (x : Γ(S, ⊤)) :
    (f.appLE ⊤ W' le_top).hom x =
      (Y.presheaf.map (homOfLE h).op).hom ((f.appLE ⊤ W le_top).hom x) :=
  (congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_map f (U := ⊤) (V := W) le_top
    (homOfLE h).op)).symm

/-- **An explicit snc chart inside a weak chart.** At a point `y` of a weak chart `c`, a basic
open `D(g) ∋ y` of `c.W` with the coordinates of `c` restricted and permuted by `σ` is a chart of
`D`: the first `r''` coordinates are the boundary coordinates of `c` vanishing at `y`, and the
other boundary coordinates of `c` are units on `D(g)`. -/
theorem exists_snc_chart_explicit {n : ℕ} {Y : Scheme.{0}} {A : CommRingCat.{0}}
    [IsRegularRing A] (f : Y ⟶ Spec A) [SmoothOfRelativeDimension n f]
    (D : MMP.Mori.Divisor Y)
    (hcomp : ∀ ξ : Y, ξ ∈ (D.supp : Set Y) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set Y)) (y : Y) (hy : y ∈ (c.W : Set Y)) :
    ∃ (g : Γ(Y, c.W)) (σ : Equiv.Perm (Fin n)) (r'' : ℕ) (hr'' : r'' ≤ n)
      (j : Fin r'' → MMP.Mori.PrimeDivisor Y),
      y ∈ Y.basicOpen g ∧
      (∀ m : Fin r'', ∃ k : Fin c.r, σ (Fin.castLE hr'' m) = Fin.castLE c.hr k) ∧
      (∀ k : Fin c.r, (∀ m : Fin r'', σ (Fin.castLE hr'' m) ≠ Fin.castLE c.hr k) →
        IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (Fin.castLE c.hr k)))) ∧
      (letI := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
        ∃ b : Module.Basis (Fin n) Γ(Y, Y.basicOpen g) Ω[Γ(Y, Y.basicOpen g)⁄Γ(Spec A, ⊤)],
          ∀ i, b i = KaehlerDifferential.D Γ(Spec A, ⊤) Γ(Y, Y.basicOpen g)
            (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (σ i)))) ∧
      Function.Injective j ∧
      (∀ m, j m ∈ D.support ∧ y ∈ (j m).support ∧
        (j m).idealSheaf.ideal ⟨Y.basicOpen g, c.W.2.basicOpen g⟩ = Ideal.span
          {Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (σ (Fin.castLE hr'' m)))}) ∧
      D.suppIdeal.ideal ⟨Y.basicOpen g, c.W.2.basicOpen g⟩ = Ideal.span
        {∏ m, Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (σ (Fin.castLE hr'' m)))} := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  set hW := c.W.2
  set B := Γ(Y, c.W)
  letI : Algebra Γ(Spec A, ⊤) B := (f.appLE ⊤ c.W le_top).hom.toAlgebra
  obtain ⟨b, hb⟩ := c.basis
  haveI : Algebra.Smooth Γ(Spec A, ⊤) B := smooth_appLE_top f c.W
  haveI : IsRegularRing Γ(Spec A, ⊤) := isRegularRing_Γ_top
  haveI : IsRegularRing B := Algebra.isRegularRing_of_smooth Γ(Spec A, ⊤) B
  set P := hW.primeIdealOf ⟨y, hy⟩
  have hyP : hW.fromSpec P = y := hW.fromSpec_primeIdealOf ⟨y, hy⟩
  set 𝔭 := P.asIdeal
  set T : Fin c.r → B := fun k => c.t (Fin.castLE c.hr k)
  have hreg : ∀ k, IsRegularRing (B ⧸ Ideal.span {T k}) := fun k =>
    isRegularRing_quotient_span_coord c.t b hb (Fin.castLE c.hr k)
  have hrad : ∀ k, (Ideal.span {T k}).IsRadical := fun k =>
    have := hreg k
    isRadical_of_isRegularRing_quotient _
  set S : Finset (Fin c.r) := Finset.univ.filter (fun k => T k ∈ 𝔭)
  have hq : ∀ k, ∃ 𝔮 : Ideal B, k ∈ S → 𝔮 ∈ (Ideal.span {T k}).minimalPrimes ∧ 𝔮 ≤ 𝔭 := by
    intro k
    by_cases hk : k ∈ S
    · have hle : Ideal.span {T k} ≤ 𝔭 := by
        rw [Ideal.span_le, Set.singleton_subset_iff]; exact (Finset.mem_filter.mp hk).2
      obtain ⟨𝔮, h𝔮, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hle
      exact ⟨𝔮, fun _ => ⟨h𝔮, h𝔮le⟩⟩
    · exact ⟨⊥, fun h => absurd h hk⟩
  choose 𝔮 h𝔮 using hq
  have huniq : ∀ k ∈ S, ∀ 𝔮' ∈ (Ideal.span {T k}).minimalPrimes, 𝔮' ≤ 𝔭 → 𝔮' = 𝔮 k :=
    fun k hk 𝔮' h𝔮' h𝔮'le =>
      have := hreg k
      minimalPrimes_eq_of_le_of_isRegularRing _ 𝔭 h𝔮' (h𝔮 k hk).1 h𝔮'le (h𝔮 k hk).2
  have hh : ∀ k, ∃ h : B, k ∈ S → h ∉ 𝔭 ∧
      ∀ 𝔮' ∈ (Ideal.span {T k}).minimalPrimes, 𝔮' ≠ 𝔮 k → h ∈ 𝔮' := by
    intro k
    by_cases hk : k ∈ S
    · obtain ⟨h, h1, h2⟩ := exists_notMem_forall_minimalPrimes_ne 𝔭 (huniq k hk)
      exact ⟨h, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose hk hhk using hh
  set h : B := (∏ k ∈ S, hk k) * ∏ k ∈ Finset.univ \ S, T k
  haveI h𝔭prime : 𝔭.IsPrime := P.isPrime
  have hh𝔭 : h ∉ 𝔭 := by
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h1 | h1
    · obtain ⟨k, hkS, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact ((hhk k hkS).1) hk'
    · obtain ⟨k, hkS, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (Finset.mem_sdiff.mp hkS).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩)
  set W'' : Y.affineOpens := ⟨Y.basicOpen h, hW.basicOpen h⟩
  have hyW'' : y ∈ (W'' : Y.Opens) := by
    rw [← hyP]; exact (fromSpec_mem_basicOpen hW P h).mpr hh𝔭
  set B'' := Γ(Y, W'')
  let ρ : B →+* B'' := (Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op).hom
  letI : Algebra B B'' := ρ.toAlgebra
  haveI : IsLocalization.Away h B'' := hW.isLocalization_basicOpen h
  letI : Algebra Γ(Spec A, ⊤) B'' := (f.appLE ⊤ W'' le_top).hom.toAlgebra
  haveI : IsScalarTower Γ(Spec A, ⊤) B B'' := IsScalarTower.of_algebraMap_eq (fun x =>
    appLE_top_comp_map f (Y.basicOpen_le h) x)
  haveI : Algebra.FormallyEtale B B'' :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers h)
  obtain ⟨b'', hb''⟩ := exists_basis_D_of_formallyEtale (R := Γ(Spec A, ⊤)) (T := B'') c.t b hb
  have hρh : IsUnit (ρ h) := IsLocalization.Away.algebraMap_isUnit h
  have hTdvd : ∀ k ∉ S, T k ∣ h := fun k hk =>
    (Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)).trans
      (dvd_mul_left _ _)
  have hunitT : ∀ k ∉ S, IsUnit (ρ (T k)) := fun k hk =>
    isUnit_of_dvd_unit (map_dvd ρ (hTdvd k hk)) hρh
  have hkdvd : ∀ k ∈ S, hk k ∣ h := fun k hk =>
    (Finset.dvd_prod_of_mem _ hk).trans (dvd_mul_right _ _)
  have hk𝔮 : ∀ k ∈ S, ∀ 𝔮' ∈ (Ideal.span {T k}).minimalPrimes, 𝔮' ≠ 𝔮 k → h ∈ 𝔮' :=
    fun k hk 𝔮' h1 h2 => by
      obtain ⟨c', hc'⟩ := hkdvd k hk
      rw [hc']; exact Ideal.mul_mem_right _ _ ((hhk k hk).2 𝔮' h1 h2)
  have h𝔮h : ∀ k ∈ S, h ∉ 𝔮 k := fun k hk hm => hh𝔭 ((h𝔮 k hk).2 hm)
  have hspanT : ∀ k, (Ideal.span {T k}).map (algebraMap B B'') = Ideal.span {ρ (T k)} :=
    fun k => by rw [Ideal.map_span, Set.image_singleton]; rfl
  have hprimeT : ∀ k ∈ S, (Ideal.span {ρ (T k)}).IsPrime := fun k hk => by
    rw [← hspanT]
    exact (isPrime_map_and_le_iff (Bh := B'') (hrad k) (h𝔮 k hk).1 (hk𝔮 k hk)
      (h𝔮h k hk)).2.1
  set r'' := S.card
  have hr'' : r'' ≤ n := (Finset.card_le_univ S).trans (by simpa using c.hr)
  let e : Fin r'' ≃ S := S.equivFin.symm
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun m : Fin r'' => Fin.castLE hr'' m)
    (fun m => Fin.castLE c.hr (e m).1) (Fin.castLE_injective hr'')
    (fun a b hab => e.injective (Subtype.ext (Fin.castLE_injective c.hr hab)))
  let t'' : Fin n → B'' := fun i => ρ (c.t (σ i))
  have ht'' : ∀ m, t'' (Fin.castLE hr'' m) = ρ (T (e m).1) := fun m => by
    simp only [t'', hσ]; rfl
  have hdom : ∀ (Q : Ideal B) [Q.IsPrime], IsDomain (Localization.AtPrime Q) := fun Q _ => by
    haveI := IsRegularRing.isRegularLocalRing_localization (R := B) Q
    exact IsRegularLocalRing.isDomain _
  have hξ : ∀ k (hkS : k ∈ S), ∃ E : MMP.Mori.PrimeDivisor Y, E ∈ D.support ∧
      AlgebraicGeometry.PrimeDivisor.genericPoint E =
        hW.fromSpec ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩ := by
    intro k hkS
    have hcoh : Order.coheight (hW.fromSpec ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩) = 1 :=
      (coheight_fromSpec hW ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩).trans
        (height_eq_one_of_mem_minimalPrimes_span_coord c.t b hb (h𝔮 k hkS).1 hdom)
    have hsupp : hW.fromSpec ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩ ∈ (D.supp : Set Y) := by
      have hmem : hW.fromSpec ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩ ∈
          Y.zeroLocus {∏ i : Fin c.r, c.t (Fin.castLE c.hr i)} ∩ (c.W : Set Y) := by
        refine ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, fromSpec_mem hW _⟩
        rintro _ rfl
        refine (fromSpec_mem_basicOpen hW ⟨𝔮 k, (h𝔮 k hkS).1.1.1⟩ _).not.mpr (not_not.mpr ?_)
        exact (Ideal.IsPrime.prod_mem_iff (hp := (h𝔮 k hkS).1.1.1)).mpr
          ⟨k, Finset.mem_univ _, (h𝔮 k hkS).1.1.2 (Ideal.subset_span rfl)⟩
      rw [← c.zero] at hmem
      exact hmem.1
    obtain ⟨E, hE, hEg⟩ := hcomp _ hsupp hcoh
    exact ⟨E, hE, hEg⟩
  choose E hEsupp hEgen using hξ
  let j : Fin r'' → MMP.Mori.PrimeDivisor Y := fun m => E (e m).1 (e m).2
  have hjinj : Function.Injective j := by
    intro m m' hmm
    have hg := congrArg AlgebraicGeometry.PrimeDivisor.genericPoint hmm
    simp only [j, hEgen] at hg
    have h𝔮eq : 𝔮 (e m).1 = 𝔮 (e m').1 :=
      congrArg PrimeSpectrum.asIdeal (fromSpec_injective hW hg)
    by_contra hne
    have hne' : (e m).1 ≠ (e m').1 := fun h' => hne (e.injective (Subtype.ext h'))
    apply notMem_of_mem_minimalPrimes_span_coord c.t b hb (i := Fin.castLE c.hr (e m').1)
      (k := Fin.castLE c.hr (e m).1) (fun h' => hne' (Fin.castLE_injective c.hr h').symm)
      (hrad (e m).1) (h𝔮 (e m).1 (e m).2).1
    rw [h𝔮eq]
    exact (h𝔮 (e m').1 (e m').2).1.1.2 (Ideal.subset_span rfl)
  have hjcomp : ∀ m, j m ∈ D.support ∧ y ∈ (j m).support ∧
      (j m).idealSheaf.ideal W'' = Ideal.span {t'' (Fin.castLE hr'' m)} := by
    intro m
    refine ⟨hEsupp _ _, ?_, ?_⟩
    · change y ∈ AlgebraicGeometry.PrimeDivisor.support (E (e m).1 (e m).2)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hEgen, ← hyP,
        ← specializes_iff_mem_closure]
      exact (fromSpec_specializes_iff hW _ _).mpr (h𝔮 (e m).1 (e m).2).2
    · rw [ht'']
      exact idealSheaf_ideal_basicOpen_eq hW (hrad _) (h𝔮 _ (e m).2).1 (hk𝔮 _ (e m).2)
        (h𝔮h _ (e m).2) _ (hEgen _ _)
  haveI : IsNoetherianRing B'' :=
    IsLocalization.isNoetherianRing (Submonoid.powers h) B'' inferInstance
  have hjsupp : D.suppIdeal.ideal W'' = Ideal.span {∏ m, t'' (Fin.castLE hr'' m)} := by
    have h1 := vanishingIdeal_ideal_basicOpen_eq hW h
      (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) D.supp c.zero
    change (Scheme.IdealSheafData.vanishingIdeal D.supp).ideal W'' = _
    rw [h1]
    have hprod : ρ (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) =
        (∏ k ∈ S, ρ (T k)) * ∏ k ∈ Finset.univ \ S, ρ (T k) := by
      rw [map_prod, ← Finset.prod_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset (Finset.subset_univ S)]
    have hu : IsUnit (∏ k ∈ Finset.univ \ S, ρ (T k)) :=
      Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k hk => hunitT k (Finset.mem_sdiff.mp hk).2)
    have hprod' : ∏ m, t'' (Fin.castLE hr'' m) = ∏ k ∈ S, ρ (T k) := by
      simp only [ht'']
      rw [← Finset.prod_coe_sort S]
      exact Equiv.prod_comp e (fun k : S => ρ (T k))
    rw [hprod, Ideal.span_singleton_mul_right_unit hu, hprod']
    have hS' : ∏ k ∈ S, ρ (T k) = ∏ i ∈ S.map (Fin.castLEEmb c.hr), ρ (c.t i) := by
      rw [Finset.prod_map]; rfl
    rw [hS']
    refine (isRadical_span_prod_of_basis_D (B := B'') (fun i => ρ (c.t i)) b'' hb'' _
      (fun i hi => ?_)).radical
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
    exact (hprimeT k hk).isRadical
  refine ⟨h, σ, r'', hr'', j, hyW'', fun m => ⟨(e m).1, hσ m⟩, fun k hk => hunitT k ?_,
    ⟨b''.reindex σ.symm, fun i => ?_⟩, hjinj, hjcomp, hjsupp⟩
  · intro hkS
    exact hk (e.symm ⟨k, hkS⟩) (by rw [hσ, Equiv.apply_symm_apply])
  · rw [Module.Basis.reindex_apply, Equiv.symm_symm, hb'']
    rfl

/-- **An snc chart at every point of a weak chart.** -/
theorem exists_snc_chart {n : ℕ} {Y : Scheme.{0}} {A : CommRingCat.{0}}
    [IsRegularRing A] (f : Y ⟶ Spec A) [SmoothOfRelativeDimension n f]
    (D : MMP.Mori.Divisor Y)
    (hcomp : ∀ ξ : Y, ξ ∈ (D.supp : Set Y) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set Y)) (y : Y) (hy : y ∈ (c.W : Set Y)) :
    ∃ (W : Y.affineOpens) (V : (Spec A).affineOpens)
      (e : (W : Y.Opens) ≤ f ⁻¹ᵁ (V : (Spec A).Opens)) (t : Fin n → Γ(Y, W)),
      y ∈ (W : Y.Opens) ∧
      (letI := (f.appLE V W e).hom.toAlgebra
        ∃ b : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄Γ(Spec A, V)],
          ∀ i, b i = KaehlerDifferential.D Γ(Spec A, V) Γ(Y, W) (t i)) ∧
      ∃ (r : ℕ) (hr : r ≤ n) (j : Fin r → MMP.Mori.PrimeDivisor Y), Function.Injective j ∧
        (∀ i, j i ∈ D.support ∧ y ∈ (j i).support ∧
          (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)}) ∧
        D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)} := by
  obtain ⟨g, σ, r'', hr'', j, hyg, -, -, hb, hj, hjD, hDW⟩ :=
    exists_snc_chart_explicit f D hcomp c y hy
  exact ⟨⟨Y.basicOpen g, c.W.2.basicOpen g⟩, ⟨⊤, isAffineOpen_top _⟩, le_top,
    fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (σ i)), hyg, hb, r'', hr'', j,
    hj, hjD, hDW⟩

/-- Transport a weak chart along an equality of closed sets. -/
def WeakChart.ofEq {𝒳 S : Scheme.{0}} {g : 𝒳 ⟶ S} {n : ℕ} {Z Z' : Set 𝒳}
    (c : WeakChart g n Z) (h : Z = Z') : WeakChart g n Z' where
  W := c.W
  t := c.t
  r := c.r
  hr := c.hr
  basis := c.basis
  zero := h ▸ c.zero

/-- Two points of coheight one, one specializing to the other, are equal. -/
theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{0}} {a b : Y} (hab : a ⤳ b)
    (ha : Order.coheight a = 1) (hb : Order.coheight b = 1) : a = b := by
  by_contra hne
  have hlt : b < a := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hab)
    (fun h => hne (hab.antisymm (Scheme.le_iff_specializes.mp h)).eq)
  have := Order.coheight_add_one_le hlt
  rw [ha, hb] at this
  exact absurd this (by decide)

/-- **Every point of the snc locus of a weak chart is a specialization of a point of coheight
one**, the generic point of a minimal prime of one of the coordinate ideals. -/
theorem exists_coheight_one_specializes {n : ℕ} {Y : Scheme.{0}} {A : CommRingCat.{0}}
    [IsRegularRing A] (f : Y ⟶ Spec A) [SmoothOfRelativeDimension n f] {Z : Set Y}
    (c : WeakChart f n Z) (z : Y) (hz : z ∈ Z) (hzW : z ∈ (c.W : Set Y)) :
    ∃ 𝔮 : PrimeSpectrum Γ(Y, c.W), (∃ k : Fin c.r,
      𝔮.asIdeal ∈ (Ideal.span {c.t (Fin.castLE c.hr k)}).minimalPrimes) ∧
      c.W.2.fromSpec 𝔮 ⤳ z ∧ Order.coheight (c.W.2.fromSpec 𝔮) = 1 ∧ c.W.2.fromSpec 𝔮 ∈ Z := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  letI : Algebra Γ(Spec A, ⊤) Γ(Y, c.W) := (f.appLE ⊤ c.W le_top).hom.toAlgebra
  obtain ⟨b, hb⟩ := c.basis
  haveI : Algebra.Smooth Γ(Spec A, ⊤) Γ(Y, c.W) := smooth_appLE_top f c.W
  haveI : IsRegularRing Γ(Spec A, ⊤) := isRegularRing_Γ_top
  haveI : IsRegularRing Γ(Y, c.W) := Algebra.isRegularRing_of_smooth Γ(Spec A, ⊤) _
  have hdom : ∀ (Q : Ideal Γ(Y, c.W)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) :=
    fun Q _ => by
      haveI := IsRegularRing.isRegularLocalRing_localization (R := Γ(Y, c.W)) Q
      exact IsRegularLocalRing.isDomain _
  set P := c.W.2.primeIdealOf ⟨z, hzW⟩
  have hzP : c.W.2.fromSpec P = z := c.W.2.fromSpec_primeIdealOf ⟨z, hzW⟩
  have hprodP : ∀ Q : PrimeSpectrum Γ(Y, c.W), c.W.2.fromSpec Q ∈ Z ↔
      (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ∈ Q.asIdeal := by
    intro Q
    have hQW := fromSpec_mem c.W.2 Q
    constructor
    · intro hQ
      have hmem : c.W.2.fromSpec Q ∈ Z ∩ (c.W : Set Y) := ⟨hQ, hQW⟩
      rw [c.zero] at hmem
      have := (Scheme.mem_zeroLocus_iff _ _ _).mp hmem.1 _ rfl
      exact not_not.mp ((fromSpec_mem_basicOpen c.W.2 Q _).not.mp this)
    · intro hQ
      have hmem : c.W.2.fromSpec Q ∈
          Y.zeroLocus {∏ i : Fin c.r, c.t (Fin.castLE c.hr i)} ∩ (c.W : Set Y) := by
        refine ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, hQW⟩
        rintro _ rfl
        exact (fromSpec_mem_basicOpen c.W.2 Q _).not.mpr (not_not.mpr hQ)
      rw [← c.zero] at hmem
      exact hmem.1
  have hzprod : (∏ i : Fin c.r, c.t (Fin.castLE c.hr i)) ∈ P.asIdeal := by
    rw [← hprodP, hzP]; exact hz
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).mp hzprod
  have hle : Ideal.span {c.t (Fin.castLE c.hr k)} ≤ P.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hk
  obtain ⟨𝔮, h𝔮, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨⟨𝔮, h𝔮.1.1⟩, ⟨k, h𝔮⟩, ?_, ?_, ?_⟩
  · rw [← hzP]; exact (fromSpec_specializes_iff c.W.2 _ _).mpr h𝔮le
  · exact (coheight_fromSpec c.W.2 _).trans
      (height_eq_one_of_mem_minimalPrimes_span_coord c.t b hb h𝔮 hdom)
  · rw [hprodP]
    exact (Ideal.IsPrime.prod_mem_iff (hp := h𝔮.1.1)).mpr
      ⟨k, Finset.mem_univ _, h𝔮.1.2 (Ideal.subset_span rfl)⟩

/-- The sections of a scheme smooth over a regular ring, over an affine open, form a Noetherian
ring. -/
theorem isNoetherianRing_Γ_of_smooth {Y : Scheme.{0}} {A : CommRingCat.{0}}
    [IsRegularRing A] (f : Y ⟶ Spec A) [Smooth f] (W : Y.affineOpens) :
    IsNoetherianRing Γ(Y, W) := by
  letI : Algebra Γ(Spec A, ⊤) Γ(Y, W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Spec A, ⊤) Γ(Y, W) := smooth_appLE_top f W
  haveI : IsRegularRing Γ(Spec A, ⊤) := isRegularRing_Γ_top
  haveI : IsRegularRing Γ(Y, W) := Algebra.isRegularRing_of_smooth Γ(Spec A, ⊤) _
  infer_instance

end SNCCharts

/-! ### Logarithmic forms as quasi-coherent modules -/

section LogForms

open TopologicalSpace

universe u

namespace G1

variable {X S : Scheme.{u}}

/-- The graded presheaf algebra of relative differential forms of `g`. -/
noncomputable abbrev TB (g : X ⟶ S) :=
  (Scheme.Hom.relativeDifferentialFormsAlgebra g).toPresheafGradedAlgebra

/-- The complement of the support of `D`. -/
abbrev LU (D : MMP.Mori.Divisor X) : X.Opens := D.supp.compl

/-- The form `d a` of a function `a` on an open of `X ∖ D`, as an element of degree one. -/
noncomputable def dOne (f : X ⟶ S) (D : MMP.Mori.Divisor X) (V : (LU D).toScheme.Opens)
    (a : Γ((LU D).toScheme, V)) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece 1).val.obj (op V) :=
  (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((LU D).ι ≫ f))).val.app
    (op V) ((Scheme.Hom.universalRelativeDerivation ((LU D).ι ≫ f)).d (X := op V) a)

/-- The local generators of the logarithmic subring over an affine open `W'`. -/
noncomputable def gens (f : X ⟶ S) (D : MMP.Mori.Divisor X) (W' : X.affineOpens) :
    Set ((TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  Set.range (fun g : Γ(X, W') => (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g)) ∪
    Set.range (fun g : Γ(X, W') =>
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W').hom g))) ∪
    { η | ∃ E ∈ D.support, ∃ t : Γ(X, W'), E.idealSheaf.ideal W' = Ideal.span {t} ∧
      ∃ s : Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (W' : X.Opens)), s * ((LU D).ι.app W').hom t = 1 ∧
        η = (TB ((LU D).ι ≫ f)).structureMap _ s *
          (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W').hom t)) }

/-- The condition defining a logarithmic form on an affine open `W'`. -/
def Br (f : X ⟶ S) (D : MMP.Mori.Divisor X) (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
      (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) : Prop :=
  (TB ((LU D).ι ≫ f)).incl p ω ∈ AddSubgroup.closure { η | ∃ g ∈ I.ideal W',
    ∃ ζ ∈ Subring.closure (gens f D W'),
      η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ }

/-- A form on `W ∖ D` is a logarithmic form if and only if every point of `W` has an affine open
neighbourhood in `W` on which the restricted form satisfies `Br`. -/
theorem mem_relativeLogForms_iff (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f]
    (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ)
    (W : X.Opens) (ω) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W ↔
      ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
        Br f D I p W'
          (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map
          ((Opens.map (LU D).ι.base).map (homOfLE h)).op ω) := Iff.rfl

/-- Restricting a function on `W` to `U ∩ W` commutes with restriction to `W' ≤ W`. -/
theorem app_restrict {U : X.Opens} {W W' : X.Opens} (h : W' ≤ W) (g : Γ(X, W)) :
    U.toScheme.presheaf.map ((Opens.map U.ι.base).map (homOfLE h)).op ((U.ι.app W).hom g) =
      (U.ι.app W').hom (X.presheaf.map (homOfLE h).op g) :=
  (congrArg (fun φ => φ.hom g) (U.ι.naturality (homOfLE h).op)).symm

section Restrict

variable (f : X ⟶ S) (D : MMP.Mori.Divisor X)

/-- Restriction of forms on `X ∖ D` commutes with the structure map from functions. -/
theorem totalRestrict_structureMap {O O' : (LU D).toScheme.Opens} (φ : op O ⟶ op O')
    (c : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).totalRestrict φ ((TB ((LU D).ι ≫ f)).structureMap _ c) =
      (TB ((LU D).ι ≫ f)).structureMap _ ((LU D).toScheme.presheaf.map φ c) :=
  (TB ((LU D).ι ≫ f)).structureMap_naturality _ c

/-- The restriction of `d a` is `d` of the restriction of `a`. -/
theorem totalRestrict_incl_dOne {O O' : (LU D).toScheme.Opens} (φ : op O ⟶ op O')
    (a : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).totalRestrict φ ((TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a)) =
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O' ((LU D).toScheme.presheaf.map φ a)) :=
  ((TB ((LU D).ι ≫ f)).totalRestrict_incl _ 1 _).trans (congrArg ((TB ((LU D).ι ≫ f)).incl 1)
    ((PresheafOfModules.naturality_apply
      (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials ((LU D).ι ≫ f))).val φ
        _).symm.trans (congrArg _
      ((Scheme.Hom.universalRelativeDerivation ((LU D).ι ≫ f)).d_map φ a).symm)))

/-- The restriction to `W'' ≤ W'` of a local generator over `W'` is a local generator over
`W''`. -/
theorem totalRestrict_mem_gens {W' W'' : X.affineOpens} (h : (W'' : X.Opens) ≤ W')
    {z} (hz : z ∈ gens f D W') :
    (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h)).op z ∈
      gens f D W'' := by
  rcases hz with (⟨g, rfl⟩ | ⟨g, rfl⟩) | ⟨E, hE, t, ht, s, hs, rfl⟩
  · refine Or.inl (Or.inl ⟨X.presheaf.map (homOfLE h).op g, ?_⟩)
    exact ((totalRestrict_structureMap f D _ _).trans
      (congrArg _ (app_restrict h g))).symm
  · refine Or.inl (Or.inr ⟨X.presheaf.map (homOfLE h).op g, ?_⟩)
    exact ((totalRestrict_incl_dOne f D _ _).trans
      (congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict h g))).symm
  · refine Or.inr ⟨E, hE, X.presheaf.map (homOfLE h).op t, ?_,
      (LU D).toScheme.presheaf.map ((Opens.map (LU D).ι.base).map (homOfLE h)).op s, ?_, ?_⟩
    · rw [← E.idealSheaf.map_ideal h, ht, Ideal.map_span, Set.image_singleton]
      rfl
    · rw [← app_restrict h t, ← map_mul, hs, map_one]
    · refine ((TB ((LU D).ι ≫ f)).totalRestrict_mul _ _ _).trans ?_
      refine congrArg₂ (· * ·) (totalRestrict_structureMap f D _ _) ?_
      exact (totalRestrict_incl_dOne f D _ _).trans
        (congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict h t))

/-- The condition `Br` on an affine open `W'` is preserved by restriction to `W'' ≤ W'`. -/
theorem Br_restrict (I : X.IdealSheafData) (p : ℤ) {W' W'' : X.affineOpens}
    (h : (W'' : X.Opens) ≤ W') {ω} (hω : Br f D I p W' ω) :
    Br f D I p W'' (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map
      ((Opens.map (LU D).ι.base).map (homOfLE h)).op ω) := by
  let φ := ((Opens.map (LU D).ι.base).map (homOfLE h)).op
  let R := (TB ((LU D).ι ≫ f)).totalRestrictRingHom φ
  have hR : ∀ z, R z = (TB ((LU D).ι ≫ f)).totalRestrict φ z := fun z =>
    (TB ((LU D).ι ≫ f)).totalRestrictRingHom_apply φ z
  have hgens : Subring.closure (gens f D W') ≤ (Subring.closure (gens f D W'')).comap R :=
    Subring.closure_le.mpr fun z hz => by
      show R z ∈ Subring.closure (gens f D W'')
      rw [hR]
      exact Subring.subset_closure (totalRestrict_mem_gens f D h hz)
  have e : (TB ((LU D).ι ≫ f)).incl p
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map φ ω) =
      R ((TB ((LU D).ι ≫ f)).incl p ω) :=
    ((hR _).trans ((TB ((LU D).ι ≫ f)).totalRestrict_incl φ p ω)).symm
  unfold Br
  rw [e]
  have hcl : AddSubgroup.closure { η | ∃ g ∈ I.ideal W',
      ∃ ζ ∈ Subring.closure (gens f D W'),
        η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ } ≤
      (AddSubgroup.closure { η | ∃ g ∈ I.ideal W'',
        ∃ ζ ∈ Subring.closure (gens f D W''),
          η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W'').hom g) * ζ }).comap
        R.toAddMonoidHom := by
    refine AddSubgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨g, hg, ζ, hζ, rfl⟩
    refine AddSubgroup.subset_closure ⟨X.presheaf.map (homOfLE h).op g,
      I.ideal_le_comap_ideal h hg, R ζ, hgens hζ, ?_⟩
    change R _ = _
    refine (map_mul R _ _).trans (congrArg (· * R ζ) ((hR _).trans
      ((totalRestrict_structureMap f D φ _).trans (congrArg _ (app_restrict h g)))))
  exact hcl hω

/-- The additive subgroup generated by the products `g · ζ`, with `g` in the ideal `I` over `W'`
and `ζ` in the subring generated by `gens f D W'`. -/
noncomputable def BrSet (I : X.IdealSheafData) (W' : X.affineOpens) :
    AddSubgroup ((TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens)))) :=
  AddSubgroup.closure { η | ∃ g ∈ I.ideal W', ∃ ζ ∈ Subring.closure (gens f D W'),
    η = (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom g) * ζ }

/-- A form satisfies `Br` if and only if its image in the total algebra lies in `BrSet`. -/
theorem Br_iff (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) (ω) :
    Br f D I p W' ω ↔ (TB ((LU D).ι ≫ f)).incl p ω ∈ BrSet f D I W' := Iff.rfl

/-- The zero form satisfies `Br`. -/
theorem Br_zero (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) : Br f D I p W' 0 := by
  rw [Br_iff, (TB ((LU D).ι ≫ f)).incl_zero]
  exact zero_mem _

/-- The forms satisfying `Br` are closed under addition. -/
theorem Br_add (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) {ω ω'}
    (h : Br f D I p W' ω) (h' : Br f D I p W' ω') : Br f D I p W' (ω + ω') := by
  rw [Br_iff, (TB ((LU D).ι ≫ f)).incl_add]
  exact add_mem h h'

/-- The forms satisfying `Br` are closed under negation. -/
theorem Br_neg (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) {ω}
    (h : Br f D I p W' ω) : Br f D I p W' (-ω) := by
  rw [Br_iff]
  have : (TB ((LU D).ι ≫ f)).incl p (-ω) = -(TB ((LU D).ι ≫ f)).incl p ω :=
    eq_neg_of_add_eq_zero_left (by
      rw [← (TB ((LU D).ι ≫ f)).incl_add, neg_add_cancel, (TB ((LU D).ι ≫ f)).incl_zero])
  rw [this]
  exact neg_mem h

/-- `BrSet` is stable under multiplication by functions on `W'`. -/
theorem structureMap_mul_mem_BrSet (I : X.IdealSheafData) (W' : X.affineOpens) (c : Γ(X, W'))
    {z} (hz : z ∈ BrSet f D I W') :
    (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom c) * z ∈ BrSet f D I W' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨g, hg, ζ, hζ, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨c * g, I.ideal W' |>.mul_mem_left c hg, ζ, hζ, ?_⟩
    rw [map_mul ((LU D).ι.app W').hom c g, ← mul_assoc]
    congr 1
    exact (map_mul ((TB ((LU D).ι ≫ f)).structureMap _) _ _).symm
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/-- In the total algebra of forms, the scalar multiple `c • x` is the product of the image of `c`
with `x`. -/
theorem incl_smul_eq (p : ℤ) {O : (LU D).toScheme.Opens}
    (c : (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj (op O))
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj (op O)) :
    (TB ((LU D).ι ≫ f)).incl p (c • x) =
      (TB ((LU D).ι ≫ f)).structureMap _ c * (TB ((LU D).ι ≫ f)).incl p x := by
  refine ((TB ((LU D).ι ≫ f)).incl_smul p c x).trans ?_
  change _ = c • (1 : (TB ((LU D).ι ≫ f)).Total (op O)) * _
  rw [(TB ((LU D).ι ≫ f)).smul_mul_eq, one_mul]

/-- The forms satisfying `Br` are closed under multiplication by functions on `W'`. -/
theorem Br_smul (I : X.IdealSheafData) (p : ℤ) (W' : X.affineOpens) (c : Γ(X, W')) {ω}
    (h : Br f D I p W' ω) :
    Br f D I p W' ((show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W').hom c) • ω) := by
  rw [Br_iff, incl_smul_eq]
  exact structureMap_mul_mem_BrSet f D I W' c h

/-- The restriction maps of the sheaf of forms on `X ∖ D`, indexed by opens of `X`. -/
noncomputable abbrev rs (p : ℤ) {W W' : X.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
        (op ((LU D).ι ⁻¹ᵁ W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
      (op ((LU D).ι ⁻¹ᵁ W')) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.map
    ((Opens.map (LU D).ι.base).map (homOfLE h)).op ω

/-- Restricting along `W' ≤ W` and then `W'' ≤ W'` is restricting along `W'' ≤ W`. -/
theorem rs_rs (p : ℤ) {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (ω) :
    rs f D p h' (rs f D p h ω) = rs f D p (h'.trans h) ω :=
  (PresheafOfModules.map_comp_apply _ ((Opens.map (LU D).ι.base).map (homOfLE h)).op
    ((Opens.map (LU D).ι.base).map (homOfLE h')).op ω).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω)

end Restrict

section RLF

variable (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
  (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData) (p : ℤ)

/-- `mem_relativeLogForms_iff`, with the restriction written through `rs`. -/
theorem mem_relativeLogForms_iff' (W : X.Opens) (ω) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W ↔
      ∀ x ∈ W, ∃ (W' : X.affineOpens) (h : (W' : X.Opens) ≤ W), x ∈ (W' : X.Opens) ∧
        Br f D I p W' (rs f D p h ω) := Iff.rfl

/-- Every point of an open `W` has an affine open neighbourhood contained in `W`. -/
theorem exists_affineOpens_le {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ W' : X.affineOpens, x ∈ (W' : X.Opens) ∧ (W' : X.Opens) ≤ W := by
  obtain ⟨W', hW', hxW', hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨⟨W', hW'⟩, hxW', hle⟩

/-- The restriction of a logarithmic form on `W` to `V ≤ W` is a logarithmic form. -/
theorem relativeLogForms_restrict {W V : X.Opens} (h : V ≤ W) {ω}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    rs f D p h ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p V := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x (h hx)
  obtain ⟨W'', hxW'', hle⟩ := exists_affineOpens_le (X := X) (show x ∈ (W' : X.Opens) ⊓ V from
    ⟨hxW', hx⟩)
  refine ⟨W'', hle.trans inf_le_right, hxW'', ?_⟩
  have e : rs f D p (hle.trans inf_le_right) (rs f D p h ω) =
      rs f D p (hle.trans inf_le_left) (rs f D p hW' ω) := by
    rw [rs_rs, rs_rs]
  rw [e]
  exact Br_restrict f D I p (hle.trans inf_le_left) hb

/-- A form on `W` whose restrictions to the members of an open cover of `W` are logarithmic is
logarithmic. -/
theorem relativeLogForms_of_local {W : X.Opens} {ω}
    (H : ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧
      rs f D p h ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p V) :
    ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hω⟩ := H x hx
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hxV
  refine ⟨W', hW'.trans hV, hxW', ?_⟩
  rw [← rs_rs f D p hV hW']
  exact hb

/-- The zero form is logarithmic. -/
theorem zero_mem_relativeLogForms (W : X.Opens) :
    0 ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hxW', hle⟩ := exists_affineOpens_le (X := X) hx
  refine ⟨W', hle, hxW', ?_⟩
  rw [show rs f D p hle 0 = 0 from map_zero _]
  exact Br_zero f D I p W'

/-- The sum of two logarithmic forms is logarithmic. -/
theorem add_mem_relativeLogForms {W : X.Opens} {ω ω'}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W)
    (hω' : ω' ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    ω + ω' ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W₁, h₁, hx₁, hb₁⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  obtain ⟨W₂, h₂, hx₂, hb₂⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω' x hx
  obtain ⟨W'', hxW'', hle⟩ := exists_affineOpens_le (X := X)
    (show x ∈ (W₁ : X.Opens) ⊓ W₂ from ⟨hx₁, hx₂⟩)
  refine ⟨W'', hle.trans (inf_le_left.trans h₁), hxW'', ?_⟩
  rw [show rs f D p (hle.trans (inf_le_left.trans h₁)) (ω + ω') =
      rs f D p (hle.trans (inf_le_left.trans h₁)) ω +
        rs f D p (hle.trans (inf_le_left.trans h₁)) ω' from map_add _ _ _]
  refine Br_add f D I p W'' ?_ ?_
  · rw [← rs_rs f D p h₁ (hle.trans inf_le_left)]
    exact Br_restrict f D I p _ hb₁
  · rw [show hle.trans (inf_le_left.trans h₁) = (hle.trans inf_le_right).trans h₂ from rfl,
      ← rs_rs f D p h₂ (hle.trans inf_le_right)]
    exact Br_restrict f D I p _ hb₂

/-- The negative of a logarithmic form is logarithmic. -/
theorem neg_mem_relativeLogForms {W : X.Opens} {ω}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    -ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  refine ⟨W', hW', hxW', ?_⟩
  rw [show rs f D p hW' (-ω) = -rs f D p hW' ω from map_neg _ _]
  exact Br_neg f D I p W' hb

/-- The product of a function on `W` with a logarithmic form on `W` is logarithmic. -/
theorem smul_mem_relativeLogForms {W : X.Opens} (c : Γ(X, W)) {ω}
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W) :
    (show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W).hom c) • ω ∈
      MMP.Mori.Divisor.relativeLogForms n f D hD I p W := by
  refine (mem_relativeLogForms_iff' n f D hD I p _ _).2 fun x hx => ?_
  obtain ⟨W', hW', hxW', hb⟩ := (mem_relativeLogForms_iff' n f D hD I p _ _).1 hω x hx
  refine ⟨W', hW', hxW', ?_⟩
  have e : rs f D p hW' ((show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W).hom c) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf
      (LU D).toScheme.toRingedSpace).obj.obj (op _) from ((LU D).ι.app W').hom
        (X.presheaf.map (homOfLE hW').op c)) • rs f D p hW' ω := by
    refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
    exact congrArg (· • rs f D p hW' ω) (app_restrict hW' c)
  rw [e]
  exact Br_smul f D I p W' _ hb

end RLF

section Complex

variable (f : X ⟶ S) (U : X.Opens)

/-- The comparison `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)` followed by `j_*` of the structure map of `U`
is the structure map `f⁻¹𝒪_S ⟶ 𝒪_X` followed by restriction to `U`. -/
theorem phi_comp_str {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
        S.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).map (inverseImageStructureMap (U.ι ≫ f)) =
    inverseImageStructureMap f ≫
      (⟨U.ι.c⟩ : X.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj U.toScheme.sheaf) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  erw [Adjunction.homEquiv_naturality_right]
  have h1 : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
      S.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} (U.ι ≫ f).base).map
        (inverseImageStructureMap (U.ι ≫ f)) = ⟨(U.ι ≫ f).c⟩ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).homEquiv_unit
      _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h2 : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _)
      (inverseImageStructureMap f) = ⟨f.c⟩ := Equiv.apply_symm_apply _ _
  erw [h2]
  exact h1.trans rfl

/-- The comparison `f⁻¹𝒪_S ⟶ j_*((j ≫ f)⁻¹𝒪_S)` of the definition of the logarithmic complex. -/
noncomputable def phiS :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (U.ι ≫ f).base).unit.app
      S.sheaf)

/-- On a section `a` of `f⁻¹𝒪_S` over `W`, the structure map of `U` applied to `phiS f U a` is
the restriction to `U` of the image of `a` in `𝒪_X(W)`. -/
theorem phiS_apply {W : X.Opens}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op W)) :
    ((inverseImageStructureMap (U.ι ≫ f)).hom.app (op (U.ι ⁻¹ᵁ W))).hom
        (((phiS f U).hom.app (op W)).hom a) =
      (U.ι.app W).hom (((inverseImageStructureMap f).hom.app (op W)).hom a) :=
  congrArg (fun φ => (φ.hom.app (op W)).hom a) (phi_comp_str f U)

/-- The direct image `j_*` over the base rings, as in the definition of the logarithmic
complex. -/
noncomputable abbrev jStar : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf)) ⥤
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  let φ : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} U.ι.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (U.ι ≫ f).base).obj S.sheaf) := phiS f U
  SheafOfModules.pushforward.{u} (F := Opens.map U.ι.base)
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

/-- The term `j_*Ω^p_{U/S}`. -/
noncomputable abbrev KX (p : ℕ) : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (jStar f U).obj ((Scheme.Hom.deRhamComplex (U.ι ≫ f)).X p)

/-- A section `a` of `f⁻¹𝒪_S` acts on `j_*Ω^p_{U/S}` through its image in the functions on
`U`. -/
theorem KX_smul (p : ℕ) {W : X.Opens}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).obj.obj (op W))
    (ω : (KX f U p).val.obj (op W)) :
    a • ω = (show (Stacks.RingedSpace.structureRingSheaf U.toScheme.toRingedSpace).obj.obj
      (op (U.ι ⁻¹ᵁ W)) from (U.ι.app W).hom (((inverseImageStructureMap f).hom.app (op W)).hom a)) •
        (show ((Scheme.Hom.relativeDifferentialFormsAlgebra (U.ι ≫ f)).piece p).val.obj
          (op (U.ι ⁻¹ᵁ W)) from ω) := by
  rw [← phiS_apply f U a]
  rfl

end Complex

section LogSubmodule

variable (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)
  (hD : D.IsRelativeSNC n f) (I : X.IdealSheafData)

/-- The logarithmic forms `I · Ω^p_{X/S}(log D)` as a subsheaf of `f⁻¹𝒪_S`-modules of
`j_*Ω^p_{U/S}`. -/
noncomputable def logSubmodule (p : ℕ) : (KX f (LU D) p).Submodule where
  obj W :=
    { carrier := MMP.Mori.Divisor.relativeLogForms n f D hD I p W.unop
      add_mem' := add_mem_relativeLogForms n f D hD I p
      zero_mem' := zero_mem_relativeLogForms n f D hD I p W.unop
      smul_mem' := fun a ω hω => by
        have e := KX_smul f (LU D) p (W := W.unop) a ω
        exact (congrArg (· ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W.unop) e).mpr
          (smul_mem_relativeLogForms n f D hD I p _ hω) }
  map {W W'} g ω hω := by
    have e : (KX f (LU D) p).val.map g ω = rs f D p (leOfHom g.unop) ω :=
      PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω
    change (KX f (LU D) p).val.map g ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W'.unop
    rw [e]
    exact relativeLogForms_restrict n f D hD I p _ hω
  isSheaf W ω hω := by
    refine relativeLogForms_of_local n f D hD I p fun x hx => ?_
    obtain ⟨V, g, hg, hxV⟩ := hω x hx
    refine ⟨V, leOfHom g, hxV, ?_⟩
    have e : (KX f (LU D) p).val.map g.op ω = rs f D p (leOfHom g) ω :=
      PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω
    rw [← e]
    exact hg

/-- The de Rham differential between `d`-stable subsheaves of `j_*Ω^•_{U/S}`. -/
noncomputable def subCxD (N : ∀ p : ℕ, (KX f (LU D) p).Submodule)
    (hN : ∀ (p : ℕ) (W : X.Opensᵒᵖ) (ω : (KX f (LU D) p).val.obj W), ω ∈ (N p).obj W →
      ((jStar f (LU D)).map ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1))).val.app W ω ∈
        (N (p + 1)).obj W) (p : ℕ) :
    (N p).toSheafOfModules ⟶ (N (p + 1)).toSheafOfModules :=
  ⟨{ app := fun W => ModuleCat.ofHom (((((jStar f (LU D)).map
        ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1)))).val.app W).hom.restrict (hN p W))
     naturality := by
        intro W W' g
        ext ω
        exact Subtype.ext
          (PresheafOfModules.naturality_apply ((jStar f (LU D)).map
            ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1))).val g ω.1) }⟩

/-- The subcomplex of `j_*Ω^•_{U/S}` with terms a `d`-stable family of subsheaves `N`. -/
noncomputable def subCx (N : ∀ p : ℕ, (KX f (LU D) p).Submodule)
    (hN : ∀ (p : ℕ) (W : X.Opensᵒᵖ) (ω : (KX f (LU D) p).val.obj W), ω ∈ (N p).obj W →
      ((jStar f (LU D)).map ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1))).val.app W ω ∈
        (N (p + 1)).obj W) :
    CochainComplex (SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  CochainComplex.of (fun p => (N p).toSheafOfModules) (subCxD f D N hN)
    (by
      intro p
      ext W ω
      exact Subtype.ext (congrArg (fun g => g.val.app ((Opens.map (LU D).ι.base).op.obj W) ω.1)
        ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d_comp_d p (p + 1) (p + 2))))

/-- The differential of `subCx` in degree `p` is `subCxD`. -/
theorem subCx_d (N : ∀ p : ℕ, (KX f (LU D) p).Submodule) (hN) (p : ℕ) :
    (subCx f D N hN).d p (p + 1) = subCxD f D N hN p := by
  unfold subCx
  exact CochainComplex.of_d (fun p => (N p).toSheafOfModules) (subCxD f D N hN) p

/-- Equal families of subsheaves give equal subcomplexes. -/
theorem subCx_congr {N N' : ∀ p : ℕ, (KX f (LU D) p).Submodule} (h : N = N') (hN hN') :
    subCx f D N hN = subCx f D N' hN' := by
  subst h; rfl

/-- The differential of the subcomplex is the de Rham differential. -/
theorem subCx_d_val (N : ∀ p : ℕ, (KX f (LU D) p).Submodule) (hN) (p : ℕ)
    (W : X.Opensᵒᵖ) (x : ((subCx f D N hN).X p).val.obj W) :
    (((subCx f D N hN).d p (p + 1)).val.app W x).1 =
      ((jStar f (LU D)).map ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1))).val.app W
        x.1 := by
  rw [subCx_d]
  rfl

/-- With a `d`-stable family of logarithmic forms, the logarithmic de Rham complex is the
subcomplex with terms the logarithmic forms. -/
theorem relativeLogDeRhamComplex_eq_subCx
    (hd : ∀ (p : ℕ) (W : X.Opens) ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W →
      ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1)).val.app (op ((LU D).ι ⁻¹ᵁ W)) ω ∈
        MMP.Mori.Divisor.relativeLogForms n f D hD I ((p + 1 : ℕ) : ℤ) W) :
    MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD I =
      subCx f D (logSubmodule n f D hD I) (fun p W ω hω => hd p W.unop ω hω) := by
  have hT : (MMP.Mori.Divisor.relativeLogDeRhamTerms n f D hD I :
      ∀ p : ℕ, (KX f (LU D) p).Submodule) = logSubmodule n f D hD I := by
    apply le_antisymm
    · exact sInf_le ⟨fun q W ω hω => hω, fun q W ω hω => hd q W.unop ω hω⟩
    · refine le_sInf ?_
      rintro M ⟨hM1, -⟩ q
      apply SheafOfModules.Submodule.le_iff.mpr
      apply PresheafOfModules.Submodule.le_iff.mpr
      intro W ω hω
      exact hM1 q W.unop ω hω
  change subCx f D (MMP.Mori.Divisor.relativeLogDeRhamTerms n f D hD I)
      (MMP.Mori.Divisor.relativeLogDeRhamTerms_d_mem n f D hD I) = _
  exact subCx_congr f D hT _ _

/-- The direct image `j_*Ω^p_{U/S}` as an `𝒪_X`-module. -/
noncomputable abbrev jForms (p : ℤ) : X.Modules :=
  (Scheme.Modules.pushforward (LU D).ι).obj (Scheme.Hom.relativeDifferentialForms ((LU D).ι ≫ f) p)

/-- A function `c` on `W` acts on `j_*Ω^p_{U/S}` through its restriction to `U ∩ W`. -/
theorem jForms_smul (p : ℤ) {W : X.Opens} (c : X.ringCatSheaf.obj.obj (op W))
    (ω : (jForms f D p).val.obj (op W)) :
    c • ω = (show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
      (op ((LU D).ι ⁻¹ᵁ W)) from ((LU D).ι.app W).hom c) •
        (show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
          (op ((LU D).ι ⁻¹ᵁ W)) from ω) := rfl

/-- The logarithmic forms `I · Ω^p_{X/S}(log D)` as an `𝒪_X`-submodule of `j_*Ω^p_{U/S}`. -/
noncomputable def logModuleSubmodule (p : ℕ) : (jForms f D p).Submodule where
  obj W :=
    { carrier := MMP.Mori.Divisor.relativeLogForms n f D hD I p W.unop
      add_mem' := add_mem_relativeLogForms n f D hD I p
      zero_mem' := zero_mem_relativeLogForms n f D hD I p W.unop
      smul_mem' := fun c ω hω => by
        exact (congrArg (· ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W.unop)
          (jForms_smul f D p (W := W.unop) c ω)).mpr
          (smul_mem_relativeLogForms n f D hD I p _ hω) }
  map {W W'} g ω hω := by
    have e : (jForms f D p).val.map g ω = rs f D p (leOfHom g.unop) ω :=
      PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω
    change (jForms f D p).val.map g ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W'.unop
    rw [e]
    exact relativeLogForms_restrict n f D hD I p _ hω
  isSheaf W ω hω := by
    refine relativeLogForms_of_local n f D hD I p fun x hx => ?_
    obtain ⟨V, g, hg, hxV⟩ := hω x hx
    refine ⟨V, leOfHom g, hxV, ?_⟩
    have e : (jForms f D p).val.map g.op ω = rs f D p (leOfHom g) ω :=
      PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) ω
    rw [← e]
    exact hg

/-- The `𝒪_X`-module `I · Ω^p_{X/S}(log D)`. -/
noncomputable abbrev logModule (p : ℕ) : X.Modules :=
  (logModuleSubmodule n f D hD I p).toSheafOfModules

open Stacks.DeRhamDirectImage in
/-- The logarithmic forms read over `f⁻¹𝒪_S` are the `𝒪_X`-module `logModule` read over
`f⁻¹𝒪_S`. -/
noncomputable def logSubmoduleIso (p : ℕ) :
    (logSubmodule n f D hD I p).toSheafOfModules ≅
      (pushforward (toInverseImageBase f)).obj (logModule n f D hD I p) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) fun W a m =>
    Subtype.ext (KX_smul f (LU D) p (W := W.unop) a m.1)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) fun W a m =>
    Subtype.ext (KX_smul f (LU D) p (W := W.unop) a m.1).symm⟩

end LogSubmodule

section Chart

variable (n : ℕ) (f : X ⟶ S) [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor X)

/-- The data of a chart of a relative snc divisor at a point, as in
`MMP.Mori.Divisor.IsRelativeSNC`. -/
structure SNCChart (x : X) where
  /-- The affine open of the chart. -/
  W : X.affineOpens
  /-- The affine open of the base. -/
  V : S.affineOpens
  /-- `W` lies over `V`. -/
  e : (W : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)
  /-- The coordinates on `W`. -/
  t : Fin n → Γ(X, W)
  /-- The point `x` lies in `W`. -/
  hx : x ∈ (W : X.Opens)
  /-- The differentials of the coordinates form a basis of the relative Kähler differentials. -/
  hb : letI := (f.appLE V W e).hom.toAlgebra
    ∃ b : Module.Basis (Fin n) Γ(X, W) Ω[Γ(X, W)⁄Γ(S, V)],
      ∀ i, b i = KaehlerDifferential.D Γ(S, V) Γ(X, W) (t i)
  /-- The number of components of `D` through `x`. -/
  r : ℕ
  /-- There are at most `n` such components. -/
  hr : r ≤ n
  /-- The components of `D` through `x`. -/
  j : Fin r → MMP.Mori.PrimeDivisor X
  /-- The components are distinct. -/
  hj : Function.Injective j
  /-- Each `j i` is a component of `D` through `x` whose ideal on `W` is generated by the `i`-th
  coordinate. -/
  hjD : ∀ i, j i ∈ D.support ∧ x ∈ (j i).support ∧
    (j i).idealSheaf.ideal W = Ideal.span {t (Fin.castLE hr i)}
  /-- On `W`, the ideal of the support of `D` is generated by the product of the first `r`
  coordinates. -/
  hDW : D.suppIdeal.ideal W = Ideal.span {∏ i, t (Fin.castLE hr i)}

variable {n f D}

/-- A relative snc divisor has a chart at every point. -/
theorem nonempty_sncChart (hD : D.IsRelativeSNC n f) (x : X) : Nonempty (SNCChart n f D x) := by
  obtain ⟨W, V, e, t, hx, hb, r, hr, j, hj, hjD, hDW⟩ := hD.2 x
  exact ⟨⟨W, V, e, t, hx, hb, r, hr, j, hj, hjD, hDW⟩⟩

/-- Functions agreeing on the members of a cover agree. -/
theorem eq_of_cover {W : X.Opens} {ι : Type u} (V : ι → X.Opens) (hV : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) {a b : Γ(X, W)}
    (h : ∀ i, X.presheaf.map (homOfLE (hV i)).op a = X.presheaf.map (homOfLE (hV i)).op b) :
    a = b :=
  X.sheaf.eq_of_locally_eq' V W (fun i => homOfLE (hV i)) hcov a b h

/-- Compatible functions on the members of a cover glue. -/
theorem exists_glue_of_cover {W : X.Opens} {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ i, V i ≤ W) (hcov : W ≤ ⨆ i, V i) (sf : ∀ i, Γ(X, V i))
    (hcomp : ∀ i j, X.presheaf.map (homOfLE inf_le_left : V i ⊓ V j ⟶ V i).op (sf i) =
      X.presheaf.map (homOfLE inf_le_right : V i ⊓ V j ⟶ V j).op (sf j)) :
    ∃ a : Γ(X, W), ∀ i, X.presheaf.map (homOfLE (hV i)).op a = sf i := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hV i)) hcov sf hcomp
  exact ⟨a, ha⟩

/-- Forms on `U ∩ W` agreeing on the members of a cover of `W` agree. -/
theorem forms_eq_of_cover (f : X ⟶ S) (D : MMP.Mori.Divisor X) (p : ℤ) {W : X.Opens}
    {ι : Type u} (V : ι → X.Opens) (hV : ∀ i, V i ≤ W) (hcov : W ≤ ⨆ i, V i)
    {ω₁ ω₂ : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.obj
      (op ((LU D).ι ⁻¹ᵁ W))}
    (h : ∀ i, rs f D p (hV i) ω₁ = rs f D p (hV i) ω₂) : ω₁ = ω₂ := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} (LU D).toScheme :=
    ⟨((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).val.presheaf,
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece p).isSheaf⟩
  refine F.eq_of_locally_eq' (fun i => (LU D).ι ⁻¹ᵁ V i) ((LU D).ι ⁻¹ᵁ W)
    (fun i => (Opens.map (LU D).ι.base).map (homOfLE (hV i))) ?_ ω₁ ω₂ h
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- A section over `O` is a unit as soon as it is invertible at every point of `O`. -/
theorem isUnit_of_le_basicOpen {Y : Scheme.{u}} {O : Y.Opens} (a : Γ(Y, O))
    (h : O ≤ Y.basicOpen a) : IsUnit a :=
  RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace O a fun x hx =>
    (Y.mem_basicOpen a x hx).mp (h hx)

/-- A local equation of a component of `D` is invertible on the complement of `D`. -/
theorem isUnit_app_of_ideal_eq {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ D.support)
    {W₁ : X.affineOpens} {t : Γ(X, W₁)} (ht : E.idealSheaf.ideal W₁ = Ideal.span {t}) :
    IsUnit (((LU D).ι.app W₁).hom t) := by
  refine isUnit_of_le_basicOpen _ fun y hy => ?_
  rw [← Scheme.preimage_basicOpen]
  by_contra hyt
  have hyW : ((LU D).ι y) ∈ (W₁ : X.Opens) := hy
  have hmem : (LU D).ι y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support, SetLike.mem_coe,
      E.idealSheaf.mem_support_iff_of_mem hyW, ht, Scheme.mem_zeroLocus_iff]
    intro b hb hyb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    rw [Scheme.basicOpen_mul] at hyb
    exact hyt hyb.2
  exact (y.2 : (LU D).ι y ∉ D.supp) (MMP.Mori.DivisorWithCoeffs.support_subset_supp
    (Finsupp.mem_support_iff.mp hE) hmem)

/-- `b · d c₁ ∧ ⋯ ∧ d cₚ` is homogeneous of degree `p`. -/
theorem exists_incl_eq_mon (O : (LU D).toScheme.Opens) (b : Γ((LU D).toScheme, O))
    (l : List Γ((LU D).toScheme, O)) :
    ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (l.length : ℤ)).val.obj (op O),
      (TB ((LU D).ι ≫ f)).incl (l.length : ℤ) x = (TB ((LU D).ι ≫ f)).structureMap _ b *
        (l.map fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a)).prod := by
  set p := l.length
  let c : Fin (p + 1) → (LU D).toScheme.sheaf.obj.obj (op O) := Fin.cons b l.get
  let w := (TB ((LU D).ι ≫ f)).homogeneousProdLeft (op O) p fun i =>
    SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras ((LU D).ι ≫ f)) (op O) (c i.succ)
  refine ⟨c 0 • w, ?_⟩
  refine (incl_smul_eq f D _ (c 0) w).trans ?_
  refine congrArg ((TB ((LU D).ι ≫ f)).structureMap _ b * ·) ?_
  refine ((TB ((LU D).ι ≫ f)).incl_homogeneousProdLeft (op O) p _).trans ?_
  rw [← List.ofFn_get l, List.map_ofFn]
  rfl

/-- `exists_incl_eq_mon`, with the degree given as any `m` equal to the length of the list. -/
theorem exists_incl_eq_mon' (O : (LU D).toScheme.Opens) (b : Γ((LU D).toScheme, O))
    (l : List Γ((LU D).toScheme, O)) (m : ℕ) (hm : l.length = m) :
    ∃ x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (m : ℤ)).val.obj (op O),
      (TB ((LU D).ι ≫ f)).incl (m : ℤ) x = (TB ((LU D).ι ≫ f)).structureMap _ b *
        (l.map fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a)).prod := by
  subst hm
  exact exists_incl_eq_mon O b l

/-- The structure map `𝒪_U(O) → Ω^•_{U/S}(O)`. -/
noncomputable abbrev smU (O : (LU D).toScheme.Opens) :
    Γ((LU D).toScheme, O) →+* (TB ((LU D).ι ≫ f)).Total (op O) :=
  (TB ((LU D).ι ≫ f)).structureMap (op O)

/-- Restricting forms along two successive inclusions is restricting along the composite. -/
theorem totalRestrict_totalRestrict {O O' O'' : (LU D).toScheme.Opens} (φ : op O ⟶ op O')
    (ψ : op O' ⟶ op O'') (χ : op O ⟶ op O'') (z : (TB ((LU D).ι ≫ f)).Total (op O)) :
    (TB ((LU D).ι ≫ f)).totalRestrict ψ ((TB ((LU D).ι ≫ f)).totalRestrict φ z) =
      (TB ((LU D).ι ≫ f)).totalRestrict χ z := by
  rw [show χ = φ ≫ ψ from Subsingleton.elim _ _]
  exact (congrArg (fun F => F.hom z) ((TB ((LU D).ι ≫ f)).totalPresheaf.map_comp φ ψ)).symm

/-- The inclusion of the forms of degree `p` into the total algebra of forms is injective. -/
theorem incl_injective (p : ℤ) (O : (LU D).toScheme.Opens) :
    Function.Injective ((TB ((LU D).ι ≫ f)).incl (X := op O) p) :=
  DirectSum.of_injective (β := fun i => (((Scheme.Hom.relativeDifferentialFormsAlgebra
    ((LU D).ι ≫ f)).piece i).val.obj (op O))) p

/-- Permuting the factors of a product of pairwise anticommuting elements changes it at most
by a sign. -/
theorem prod_map_perm {T : Type*} [Ring T] {ι : Type*} (θ : ι → T)
    (hac : ∀ i j, θ i * θ j = -(θ j * θ i)) {l₁ l₂ : List ι} (h : l₁.Perm l₂) :
    (l₁.map θ).prod = (l₂.map θ).prod ∨ (l₁.map θ).prod = -(l₂.map θ).prod := by
  induction h with
  | nil => exact Or.inl rfl
  | cons x _ ih =>
    rcases ih with ih | ih
    · exact Or.inl (by simp [ih])
    · exact Or.inr (by simp [ih])
  | swap x y l =>
    right
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hac y x, neg_mul]
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁ <;> rcases ih₂ with h₂ | h₂
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr (h₁.trans h₂)
    · exact Or.inr (by rw [h₁, h₂])
    · exact Or.inl (by rw [h₁, h₂, neg_neg])

/-- `d a ∧ d a = 0`. -/
theorem incl_dOne_mul_self (O : (LU D).toScheme.Opens) (a : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a) * (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a) = 0 := by
  have h := (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
    (Scheme.Hom.relativeDifferentials ((LU D).ι ≫ f))).1 (op O)
      ((Scheme.Hom.universalRelativeDerivation ((LU D).ι ≫ f)).d (X := op O) a)
  refine ((TB ((LU D).ι ≫ f)).incl_mul_incl 1 1 _ _).trans ?_
  refine (congrArg ((TB ((LU D).ι ≫ f)).incl (1 + 1)) h).trans ?_
  exact (TB ((LU D).ι ≫ f)).incl_zero _

/-- `d (a + b) = d a + d b`. -/
theorem incl_dOne_add (O : (LU D).toScheme.Opens) (a b : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O (a + b)) =
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a) + (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O b) := by
  refine (congrArg ((TB ((LU D).ι ≫ f)).incl 1) ?_).trans ((TB ((LU D).ι ≫ f)).incl_add 1 _ _)
  unfold dOne
  exact (congrArg (fun ξ => (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials
    ((LU D).ι ≫ f))).val.app (op O) ξ) (map_add _ a b)).trans (map_add _ _ _)

/-- `d a ∧ d b = -(d b ∧ d a)`. -/
theorem incl_dOne_anticomm (O : (LU D).toScheme.Opens) (a b : Γ((LU D).toScheme, O)) :
    (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a) * (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O b) =
      -((TB ((LU D).ι ≫ f)).incl 1 (dOne f D O b) * (TB ((LU D).ι ≫ f)).incl 1 (dOne f D O a)) := by
  have h := incl_dOne_mul_self (f := f) (D := D) O (a + b)
  rw [incl_dOne_add, add_mul, mul_add, mul_add, incl_dOne_mul_self, incl_dOne_mul_self, zero_add,
    add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- For a ring map `sm` with central image, `∏ (sm (σ i) * δ i) = sm (∏ σ i) * ∏ δ i`. -/
theorem prod_map_mul_of_commute {R T ι : Type*} [CommRing R] [Ring T] (sm : R →+* T)
    (hc : ∀ r z, sm r * z = z * sm r) (σ : ι → R) (δ : ι → T) (L : List ι) :
    (L.map fun i => sm (σ i) * δ i).prod = sm ((L.map σ).prod) * (L.map δ).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, ih, map_mul]
    rw [mul_assoc, ← mul_assoc (δ i), ← hc, mul_assoc, mul_assoc]

/-- The logarithmic coordinate forms `θᵢ = sᵢ dtᵢ` (`i < r`) and `θᵢ = dtᵢ` (`i ≥ r`) of
coordinates `t` on an affine open `W`, with `sᵢ` an inverse of `tᵢ` on `U ∩ W`. -/
noncomputable def logθ (W : X.affineOpens) (t : Fin n → Γ(X, W)) (r : ℕ)
    (s : Fin r → Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (W : X.Opens))) (i : Fin n) :
    (TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W : X.Opens))) :=
  if h : (i : ℕ) < r then
    (TB ((LU D).ι ≫ f)).structureMap _ (s ⟨i, h⟩) *
      (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W).hom (t i)))
  else (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W).hom (t i)))

/-- The form `∑_K a_K θ_K` on an affine open `W' ⊆ W`. -/
noncomputable def logCombo (W : X.affineOpens) (t : Fin n → Γ(X, W)) (r : ℕ)
    (s : Fin r → Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (W : X.Opens))) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ W) (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    (TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))) :=
  ∑ K, (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom (a K)) *
    ((K.1.sort (· ≤ ·)).map fun i =>
      (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE hW')).op
        (logθ (f := f) (D := D) W t r s i)).prod

/-- The product `t₁ ⋯ t_r` restricted to `W'`. -/
noncomputable def logH (W : X.affineOpens) (t : Fin n → Γ(X, W)) {r : ℕ} (hr : r ≤ n)
    {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ W) : Γ(X, W') :=
  X.presheaf.map (homOfLE hW').op (∏ i, t (Fin.castLE hr i))

/-- **Logarithmic coordinate data**: an affine open `W` with coordinates `t`, of which the first
`r` are boundary coordinates with inverses `s` on `U ∩ W`. -/
structure LogData (n : ℕ) (f : X ⟶ S) (D : MMP.Mori.Divisor X) where
  /-- The affine open of the chart. -/
  W : X.affineOpens
  /-- The coordinates on `W`. -/
  t : Fin n → Γ(X, W)
  /-- The number of boundary coordinates. -/
  r : ℕ
  /-- There are at most `n` boundary coordinates. -/
  hr : r ≤ n
  /-- Inverses of the boundary coordinates on `U ∩ W`. -/
  s : Fin r → Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (W : X.Opens))

/-- The logarithmic coordinate forms `θ_K` are a basis of `Ω^p_{X/S}(log D)` over `W'`, and the
`t₁ ⋯ t_r θ_K` a basis of `Ω^p_{X/S}(log D)(-D)`. -/
def HasLogBasis (hD : D.IsRelativeSNC n f) (c : LogData n f D) (p : ℕ)
    {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) : Prop :=
  Function.Injective (logCombo (f := f) c.W c.t c.r c.s p hW') ∧
    (∀ ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ p W' ↔
      ∃ a, (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω = logCombo (f := f) c.W c.t c.r c.s p hW' a) ∧
    Function.Injective (fun a => logCombo (f := f) c.W c.t c.r c.s p hW'
      (logH c.W c.t c.hr hW' • a)) ∧
    (∀ ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal p W' ↔
      ∃ a, (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω =
        logCombo (f := f) c.W c.t c.r c.s p hW' (logH c.W c.t c.hr hW' • a))

variable (n f D) in
/-- **A logarithmic chart**: logarithmic coordinate data whose forms `θ_K` are a basis of the
logarithmic forms over every affine open `W' ⊆ W`. -/
structure LogChart (hD : D.IsRelativeSNC n f) extends LogData n f D where
  /-- The forms `θ_K` are a basis of the logarithmic forms over every affine open of `W`. -/
  basis : ∀ (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ W),
    HasLogBasis hD toLogData p hW'

namespace SNCChart

variable {x : X} (c : SNCChart n f D x)

/-- The inverses `1 / tᵢ` of the boundary coordinates on `U ∩ W`. -/
noncomputable def s (i : Fin c.r) : Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ (c.W : X.Opens)) :=
  ↑(isUnit_app_of_ideal_eq (c.hjD i).1 (c.hjD i).2.2).unit⁻¹

/-- `sᵢ · tᵢ = 1` on `U ∩ W`. -/
theorem hs (i : Fin c.r) : c.s i * ((LU D).ι.app c.W).hom (c.t (Fin.castLE c.hr i)) = 1 :=
  (isUnit_app_of_ideal_eq (c.hjD i).1 (c.hjD i).2.2).val_inv_mul

/-- Over every affine open `W' ⊆ W`, the forms `θ_K` are a basis of `I · Ω^p_{X/S}(log D)`
with coefficients in `I`, and the forms `t₁ ⋯ t_r θ_K` a basis of `Ω^p_{X/S}(log D)(-D)`. -/
theorem basis (hD : D.IsRelativeSNC n f) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) :
    Function.Injective (logCombo (f := f) c.W c.t c.r c.s p hW') ∧
      (∀ (I : X.IdealSheafData) ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD I p W' ↔
        ∃ a, (∀ K, a K ∈ I.ideal W') ∧
          (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω = logCombo (f := f) c.W c.t c.r c.s p hW' a) ∧
      Function.Injective (fun a => logCombo (f := f) c.W c.t c.r c.s p hW'
        (logH c.W c.t c.hr hW' • a)) ∧
      (∀ ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD D.suppIdeal p W' ↔
        ∃ a, (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω =
          logCombo (f := f) c.W c.t c.r c.s p hW' (logH c.W c.t c.hr hW' • a)) :=
  (MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).2 x c.W c.V c.e c.t c.hx
    c.hb c.r c.hr c.j c.hj c.hjD c.hDW c.s c.hs p W' hW'

/-- The logarithmic chart attached to a chart of a relative snc divisor. -/
noncomputable def toLogChart (hD : D.IsRelativeSNC n f) : LogChart n f D hD where
  W := c.W
  t := c.t
  r := c.r
  hr := c.hr
  s := c.s
  basis := fun p {W'} hW' => by
    obtain ⟨h1, h2, h3, h4⟩ := c.basis hD p hW'
    refine ⟨h1, fun ω => (h2 ⊤ ω).trans ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ =>
      ⟨a, fun K => ?_, ha⟩⟩, h3, h4⟩
    show a K ∈ (⊤ : X.IdealSheafData).ideal W'
    rw [Scheme.IdealSheafData.ideal_top]
    exact Submodule.mem_top

/-- The logarithmic chart of `c` lives on the affine open of `c`. -/
theorem toLogChart_W (hD : D.IsRelativeSNC n f) : (c.toLogChart hD).W = c.W := rfl

end SNCChart

namespace LogData

variable (c : LogData n f D)

/-- The logarithmic coordinate forms of the chart. -/
noncomputable abbrev θ (i : Fin n) :
    (TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (c.W : X.Opens))) :=
  logθ (f := f) c.W c.t c.r c.s i

/-- The form `∑_K a_K θ_K` on an affine open `W' ⊆ W`. -/
noncomputable abbrev combo (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    (TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))) :=
  logCombo (f := f) c.W c.t c.r c.s p hW' a

/-- The product `t₁ ⋯ t_r` restricted to `W'`. -/
noncomputable abbrev h {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) : Γ(X, W') :=
  logH c.W c.t c.hr hW'

/-- The coefficient of `dtᵢ` in `θᵢ`, restricted to `W'`. -/
noncomputable def σ {W' : X.Opens} (hW' : W' ≤ c.W) (i : Fin n) :
    Γ((LU D).toScheme, (LU D).ι ⁻¹ᵁ W') :=
  if h : (i : ℕ) < c.r then
    (LU D).toScheme.presheaf.map ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (c.s ⟨i, h⟩)
  else 1

/-- The restriction of `θᵢ` to `W'` is `σᵢ · d tᵢ`. -/
theorem totalRestrict_θ {W' : X.Opens} (hW' : W' ≤ c.W) (i : Fin n) :
    (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (c.θ i) =
      (TB ((LU D).ι ≫ f)).structureMap _ (c.σ hW' i) *
        (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ (((LU D).ι.app W').hom
          (X.presheaf.map (homOfLE hW').op (c.t i)))) := by
  unfold θ logθ σ
  split_ifs with hi
  · refine ((TB ((LU D).ι ≫ f)).totalRestrict_mul _ _ _).trans ?_
    refine congrArg₂ (· * ·) (totalRestrict_structureMap f D _ _) ?_
    exact (totalRestrict_incl_dOne f D _ _).trans
      (congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict hW' _))
  · refine (totalRestrict_incl_dOne f D _ _).trans ?_
    refine Eq.trans ?_ (congrArg (· * _) (map_one ((TB ((LU D).ι ≫ f)).structureMap
      (op ((LU D).ι ⁻¹ᵁ W'))))).symm
    refine Eq.trans ?_ (one_mul _).symm
    exact congrArg (fun a => (TB ((LU D).ι ≫ f)).incl 1 (dOne f D _ a)) (app_restrict hW' _)

/-- Every combination `∑_K a_K θ_K` is a form of degree `p`. -/
theorem exists_incl_eq_combo (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    ∃ ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece
        (p : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))),
      (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω = c.combo p hW' a := by
  classical
  have hK : ∀ K : {K : Finset (Fin n) // K.card = p},
      ∃ ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
        ((LU D).ι ≫ f)).piece (p : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ (W' : X.Opens))),
      (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω =
        (TB ((LU D).ι ≫ f)).structureMap _ (((LU D).ι.app W').hom (a K)) *
          ((K.1.sort (· ≤ ·)).map fun i =>
            (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE hW')).op
              (c.θ i)).prod := by
    intro K
    obtain ⟨ω, hω⟩ := exists_incl_eq_mon' (f := f) (D := D) _
      (((LU D).ι.app W').hom (a K) * ((K.1.sort (· ≤ ·)).map (c.σ hW')).prod)
      ((K.1.sort (· ≤ ·)).map fun i => ((LU D).ι.app W').hom
        (X.presheaf.map (homOfLE hW').op (c.t i))) p
      (by rw [List.length_map, Finset.length_sort, K.2])
    refine ⟨ω, hω.trans ?_⟩
    show smU (f := f) (D := D) _ (_ * _) * _ = smU (f := f) (D := D) _ _ * _
    rw [map_mul, mul_assoc]
    refine congrArg (_ * ·) ?_
    rw [List.map_congr_left (fun i _ => c.totalRestrict_θ hW' i)]
    exact ((prod_map_mul_of_commute (smU (f := f) (D := D) _)
      (fun r z => (TB ((LU D).ι ≫ f)).structureMap_commutes _ r z) _ _ _).trans
      (by rw [List.map_map]; rfl)).symm
  choose ω hω using hK
  refine ⟨∑ K, ω K, ?_⟩
  rw [show (TB ((LU D).ι ≫ f)).incl (p : ℤ) (∑ K, ω K) =
    ∑ K, (TB ((LU D).ι ≫ f)).incl (p : ℤ) (ω K) from map_sum (DirectSum.of _ (p : ℤ)) _ _]
  exact Finset.sum_congr rfl fun K _ => hω K

/-- The restriction of `∑_K a_K θ_K` to `W'' ≤ W'` is the combination of the restricted
coefficients. -/
theorem totalRestrict_combo (p : ℕ) {W' W'' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (h'' : (W'' : X.Opens) ≤ W') (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h'')).op
        (c.combo p hW' a) =
      c.combo p (h''.trans hW') (fun K => X.presheaf.map (homOfLE h'').op (a K)) := by
  unfold combo logCombo
  rw [show (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h'')).op
      (∑ K, _) = ∑ K, (TB ((LU D).ι ≫ f)).totalRestrict
        ((Opens.map (LU D).ι.base).map (homOfLE h'')).op _ from map_sum _ _ _]
  refine Finset.sum_congr rfl fun K _ => ?_
  refine ((TB ((LU D).ι ≫ f)).totalRestrict_mul _ _ _).trans ?_
  refine congrArg₂ (· * ·) ((totalRestrict_structureMap f D _ _).trans
    (congrArg _ (app_restrict h'' (a K)))) ?_
  rw [← (TB ((LU D).ι ≫ f)).totalRestrictRingHom_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact totalRestrict_totalRestrict (f := f) (D := D) _ _ _ _

/-- `∑_K a_K θ_K` is additive in the coefficients. -/
theorem combo_add (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (a b : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    c.combo p hW' (a + b) = c.combo p hW' a + c.combo p hW' b := by
  unfold combo logCombo
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  show smU (f := f) (D := D) _ _ * _ = smU (f := f) (D := D) _ _ * _ +
    smU (f := f) (D := D) _ _ * _
  rw [Pi.add_apply, map_add, map_add, add_mul]

/-- Scaling the coefficients of `∑_K a_K θ_K` by `r` multiplies the form by `r`. -/
theorem combo_smul (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) (r : Γ(X, W'))
    (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    c.combo p hW' (r • a) =
      smU (f := f) (D := D) _ (((LU D).ι.app W').hom r) * c.combo p hW' a := by
  unfold combo logCombo
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  show smU (f := f) (D := D) _ _ * _ = smU (f := f) (D := D) _ _ *
    (smU (f := f) (D := D) _ _ * _)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, mul_assoc]

/-- The twisting factor: `t₁ ⋯ t_r` for the twisted forms, `1` otherwise. -/
noncomputable def hε (ε : Bool) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) : Γ(X, W') :=
  bif ε then c.h hW' else 1

/-- The restriction of the twisting factor on `W'` is the twisting factor on `W''`. -/
theorem map_hε (ε : Bool) {W' W'' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (h'' : (W'' : X.Opens) ≤ W') :
    X.presheaf.map (homOfLE h'').op (c.hε ε hW') = c.hε ε (h''.trans hW') := by
  cases ε
  · exact map_one _
  · show X.presheaf.map (homOfLE h'').op (X.presheaf.map (homOfLE hW').op _) =
      X.presheaf.map (homOfLE (h''.trans hW')).op _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- `totalRestrict_combo` for coefficients multiplied by the twisting factor. -/
theorem totalRestrict_combo_hε (ε : Bool) (p : ℕ) {W' W'' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) (h'' : (W'' : X.Opens) ≤ W')
    (a : {K : Finset (Fin n) // K.card = p} → Γ(X, W')) :
    (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h'')).op
        (c.combo p hW' (c.hε ε hW' • a)) =
      c.combo p (h''.trans hW') (c.hε ε (h''.trans hW') •
        fun K => X.presheaf.map (homOfLE h'').op (a K)) := by
  refine (c.totalRestrict_combo p hW' h'' _).trans (congrArg _ (funext fun K => ?_))
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, c.map_hε]

/-- The basis property in terms of the twisting factor. -/
def BasisAt (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) : Prop :=
  Function.Injective (fun a => c.combo p hW' (c.hε ε hW' • a)) ∧
    ∀ ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD (bif ε then D.suppIdeal else ⊤) p W' ↔
      ∃ a, (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω = c.combo p hW' (c.hε ε hW' • a)

/-- `HasLogBasis` is `BasisAt` for the untwisted and for the twisted forms. -/
theorem hasLogBasis_iff (hD : D.IsRelativeSNC n f) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) :
    HasLogBasis hD c p hW' ↔ c.BasisAt hD false p hW' ∧ c.BasisAt hD true p hW' := by
  have e1 : ∀ a : {K : Finset (Fin n) // K.card = p} → Γ(X, W'), c.hε false hW' • a = a :=
    fun a => by rw [show c.hε false hW' = 1 from rfl, one_smul]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨fun a b hab => h1 (by simpa only [e1] using hab), fun ω => ?_⟩, ⟨h3, h4⟩⟩
    show ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD ⊤ p W' ↔ _
    simp only [e1]
    exact h2 ω
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    refine ⟨fun a b hab => h1 (by simpa only [e1] using hab), fun ω => ?_, h3, h4⟩
    have := h2 ω
    simp only [e1] at this
    exact this

/-- **The basis property is local.** -/
theorem basisAt_of_cover (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ)
    {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) {ι : Type u} (V : ι → X.affineOpens)
    (hV : ∀ i, (V i : X.Opens) ≤ W') (hcov : (W' : X.Opens) ≤ ⨆ i, (V i : X.Opens))
    (Hloc : ∀ i (V'' : X.affineOpens) (h'' : (V'' : X.Opens) ≤ V i),
      c.BasisAt hD ε p (h''.trans ((hV i).trans hW'))) :
    c.BasisAt hD ε p hW' := by
  classical
  have hincl : ∀ {O O' : X.Opens} (h'' : O' ≤ O) (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra
      ((LU D).ι ≫ f)).piece (p : ℤ)).val.obj (op ((LU D).ι ⁻¹ᵁ O))),
      (TB ((LU D).ι ≫ f)).incl (p : ℤ) (rs f D p h'' ω) =
        (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE h'')).op
          ((TB ((LU D).ι ≫ f)).incl (p : ℤ) ω) := fun h'' ω =>
    ((TB ((LU D).ι ≫ f)).totalRestrict_incl _ (p : ℤ) _).symm
  have hcov₂ : ∀ i j, ((V i : X.Opens) ⊓ (V j : X.Opens)) ≤
      ⨆ V'' : {V'' : X.affineOpens // (V'' : X.Opens) ≤ (V i : X.Opens) ⊓ (V j : X.Opens)},
        (V''.1 : X.Opens) := by
    intro i j x hx
    obtain ⟨V'', hx'', hle⟩ := exists_affineOpens_le (X := X) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V'', hle⟩, hx''⟩
  refine ⟨fun a b hab => ?_, fun ω => ⟨fun hω => ?_, fun ⟨a, ha⟩ => ?_⟩⟩
  · funext K
    refine eq_of_cover (fun i => (V i : X.Opens)) hV hcov fun i => ?_
    have hab' : c.combo p ((le_refl (V i : X.Opens)).trans ((hV i).trans hW'))
        (c.hε ε ((le_refl (V i : X.Opens)).trans ((hV i).trans hW')) •
          fun K => X.presheaf.map (homOfLE (hV i)).op (a K)) =
        c.combo p ((le_refl (V i : X.Opens)).trans ((hV i).trans hW'))
          (c.hε ε ((le_refl (V i : X.Opens)).trans ((hV i).trans hW')) •
            fun K => X.presheaf.map (homOfLE (hV i)).op (b K)) := by
      have := congrArg ((TB ((LU D).ι ≫ f)).totalRestrict
        ((Opens.map (LU D).ι.base).map (homOfLE (hV i))).op) hab
      simp only at this
      rw [c.totalRestrict_combo_hε, c.totalRestrict_combo_hε] at this
      exact this
    exact congrFun ((Hloc i (V i) le_rfl).1 hab') K
  · have hloc : ∀ i, ∃ a : {K : Finset (Fin n) // K.card = p} → Γ(X, V i),
        (TB ((LU D).ι ≫ f)).incl (p : ℤ) (rs f D p (hV i) ω) =
          c.combo p ((hV i).trans hW') (c.hε ε ((hV i).trans hW') • a) := fun i =>
      ((Hloc i (V i) le_rfl).2 _).1 (relativeLogForms_restrict n f D hD _ _ (hV i) hω)
    choose a ha using hloc
    have hcomp : ∀ K i j,
        X.presheaf.map (homOfLE inf_le_left : ((V i : X.Opens) ⊓ (V j : X.Opens)) ⟶ V i).op
          (a i K) =
        X.presheaf.map (homOfLE inf_le_right : ((V i : X.Opens) ⊓ (V j : X.Opens)) ⟶ V j).op
          (a j K) := by
      intro K i j
      refine eq_of_cover
        (fun V'' : {V'' : X.affineOpens // (V'' : X.Opens) ≤ (V i : X.Opens) ⊓ (V j : X.Opens)} =>
          (V''.1 : X.Opens)) (fun V'' => V''.2) (hcov₂ i j) fun V'' => ?_
      have hres : ∀ k (hk : (V''.1 : X.Opens) ≤ V k)
          (hk' : ((V i : X.Opens) ⊓ (V j : X.Opens)) ≤ V k),
          X.presheaf.map (homOfLE V''.2).op (X.presheaf.map (homOfLE hk').op (a k K)) =
            X.presheaf.map (homOfLE hk).op (a k K) := fun k hk hk' => by
        rw [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl
      rw [hres i (V''.2.trans inf_le_left), hres j (V''.2.trans inf_le_right)]
      have key : ∀ k (hk : (V''.1 : X.Opens) ≤ V k),
          c.combo p (hk.trans ((hV k).trans hW')) (c.hε ε (hk.trans ((hV k).trans hW')) •
            fun K => X.presheaf.map (homOfLE hk).op (a k K)) =
          (TB ((LU D).ι ≫ f)).incl (p : ℤ) (rs f D p (hk.trans (hV k)) ω) := by
        intro k hk
        rw [← c.totalRestrict_combo_hε ε p ((hV k).trans hW') hk, ← ha k, ← hincl, rs_rs]
      have := (key i (V''.2.trans inf_le_left)).trans (key j (V''.2.trans inf_le_right)).symm
      exact congrFun ((Hloc i V''.1 (V''.2.trans inf_le_left)).1 this) K
    have hglue : ∀ K, ∃ b : Γ(X, W'), ∀ i,
        X.presheaf.map (homOfLE (hV i)).op b = a i K := fun K =>
      exists_glue_of_cover (fun i => (V i : X.Opens)) hV hcov (fun i => a i K) (hcomp K)
    choose b hb using hglue
    refine ⟨b, ?_⟩
    obtain ⟨ω', hω'⟩ := c.exists_incl_eq_combo p hW' (c.hε ε hW' • b)
    have : ω = ω' := by
      refine forms_eq_of_cover f D p (fun i => (V i : X.Opens)) hV hcov fun i => ?_
      refine incl_injective (f := f) (D := D) (p : ℤ) _ ?_
      rw [ha i, hincl, hω', c.totalRestrict_combo_hε]
      congr 2
      funext K
      exact (hb K i).symm
    rw [this, hω']
  · refine relativeLogForms_of_local n f D hD _ _ fun x hx => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
    refine ⟨V i, hV i, hi, ((Hloc i (V i) le_rfl).2 _).2
      ⟨fun K => X.presheaf.map (homOfLE (hV i)).op (a K), ?_⟩⟩
    rw [hincl, ha, c.totalRestrict_combo_hε]

/-- The restricted logarithmic coordinate forms. -/
noncomputable abbrev θr {W' : X.Opens} (hW' : W' ≤ c.W) (i : Fin n) :
    (TB ((LU D).ι ≫ f)).Total (op ((LU D).ι ⁻¹ᵁ W')) :=
  (TB ((LU D).ι ≫ f)).totalRestrict ((Opens.map (LU D).ι.base).map (homOfLE hW')).op (c.θ i)

/-- If `x` and `y` are central and `A * B = -(B * A)`, then `x A · y B = -(y B · x A)`. -/
theorem central_mul_anticomm {T : Type*} [Ring T] {x y A B : T}
    (hx : ∀ z, x * z = z * x) (hy : ∀ z, y * z = z * y) (hAB : A * B = -(B * A)) :
    x * A * (y * B) = -(y * B * (x * A)) := by
  calc x * A * (y * B) = x * (A * y) * B := by simp only [mul_assoc]
    _ = x * (y * A) * B := by rw [hy A]
    _ = (x * y) * (A * B) := by simp only [mul_assoc]
    _ = (x * y) * (-(B * A)) := by rw [hAB]
    _ = -((y * x) * (B * A)) := by rw [hx y, mul_neg]
    _ = -(y * (x * B) * A) := by simp only [mul_assoc]
    _ = -(y * (B * x) * A) := by rw [hx B]
    _ = -(y * B * (x * A)) := by simp only [mul_assoc]

/-- The restricted coordinate forms anticommute. -/
theorem θr_anticomm {W' : X.Opens} (hW' : W' ≤ c.W) (i j : Fin n) :
    c.θr hW' i * c.θr hW' j = -(c.θr hW' j * c.θr hW' i) := by
  simp only [θr]
  rw [c.totalRestrict_θ, c.totalRestrict_θ]
  exact central_mul_anticomm (fun z => (TB ((LU D).ι ≫ f)).structureMap_commutes _ _ z)
    (fun z => (TB ((LU D).ι ≫ f)).structureMap_commutes _ _ z) (incl_dOne_anticomm _ _ _)

/-- Coordinate forms differing by units and a permutation give products differing by a unit. -/
theorem prod_θr_comparison (c' : LogData n f D) {V'' : X.Opens} (h1 : V'' ≤ c.W)
    (h2 : V'' ≤ c'.W) (σ : Equiv.Perm (Fin n)) (ν : Fin n → Γ(X, V''))
    (hθ : ∀ i, c'.θr h2 i =
      smU (f := f) (D := D) _ (((LU D).ι.app V'').hom (ν i)) * c.θr h1 (σ i))
    (K : Finset (Fin n)) :
    ∃ e : Γ(X, V''), (e = ((K.sort (· ≤ ·)).map ν).prod ∨ e = -((K.sort (· ≤ ·)).map ν).prod) ∧
      ((K.sort (· ≤ ·)).map (c'.θr h2)).prod =
        smU (f := f) (D := D) _ (((LU D).ι.app V'').hom e) *
          (((K.map σ.toEmbedding).sort (· ≤ ·)).map (c.θr h1)).prod := by
  classical
  rw [List.map_congr_left (fun i _ => hθ i),
    prod_map_mul_of_commute (smU (f := f) (D := D) _)
      (fun r z => (TB ((LU D).ι ≫ f)).structureMap_commutes _ r z)]
  have hperm : ((K.sort (· ≤ ·)).map σ).Perm ((K.map σ.toEmbedding).sort (· ≤ ·)) := by
    refine List.perm_of_nodup_nodup_toFinset_eq ((K.sort_nodup _).map σ.injective)
      (Finset.sort_nodup _ _) ?_
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_sort, Finset.mem_map,
      Equiv.coe_toEmbedding]
  have hmap : ((K.sort (· ≤ ·)).map fun i => c.θr h1 (σ i)) =
      (((K.sort (· ≤ ·)).map σ).map (c.θr h1)) := by rw [List.map_map]; rfl
  have hprodν : ((K.sort (· ≤ ·)).map fun i => ((LU D).ι.app V'').hom (ν i)).prod =
      ((LU D).ι.app V'').hom ((K.sort (· ≤ ·)).map ν).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rcases prod_map_perm (c.θr h1) (c.θr_anticomm h1) hperm with h | h
  · refine ⟨((K.sort (· ≤ ·)).map ν).prod, Or.inl rfl, ?_⟩
    rw [hmap, h, hprodν]
  · refine ⟨-((K.sort (· ≤ ·)).map ν).prod, Or.inr rfl, ?_⟩
    rw [hmap, h, hprodν, map_neg, map_neg, neg_mul, mul_neg]

/-- **The basis property is invariant under unit and permutation changes of the coordinate
forms.** -/
theorem basisAt_of_comparison (c' : LogData n f D) (hD : D.IsRelativeSNC n f) (ε : Bool)
    (p : ℕ) {V'' : X.affineOpens} (h1 : (V'' : X.Opens) ≤ c.W) (h2 : (V'' : X.Opens) ≤ c'.W)
    (σ : Equiv.Perm (Fin n)) (ν : Fin n → Γ(X, V'')) (hν : ∀ i, IsUnit (ν i))
    (hθ : ∀ i, c'.θr h2 i =
      smU (f := f) (D := D) _ (((LU D).ι.app V'').hom (ν i)) * c.θr h1 (σ i))
    (w : Γ(X, V'')) (hw : IsUnit w) (hh : c.hε ε h1 = w * c'.hε ε h2)
    (H : c'.BasisAt hD ε p h2) : c.BasisAt hD ε p h1 := by
  classical
  let τ : {K : Finset (Fin n) // K.card = p} ≃ {K : Finset (Fin n) // K.card = p} :=
    { toFun := fun K => ⟨K.1.map σ.toEmbedding, by rw [Finset.card_map, K.2]⟩
      invFun := fun L => ⟨L.1.map σ.symm.toEmbedding, by rw [Finset.card_map, L.2]⟩
      left_inv := fun K => Subtype.ext (by
        simp only [Finset.map_map]
        convert Finset.map_refl
        ext x; simp)
      right_inv := fun L => Subtype.ext (by
        simp only [Finset.map_map]
        convert Finset.map_refl
        ext x; simp) }
  have hcomp : ∀ K : {K : Finset (Fin n) // K.card = p}, ∃ e : Γ(X, V''), IsUnit e ∧
      ((K.1.sort (· ≤ ·)).map (c'.θr h2)).prod =
        smU (f := f) (D := D) _ (((LU D).ι.app V'').hom e) *
          (((τ K).1.sort (· ≤ ·)).map (c.θr h1)).prod := fun K => by
    obtain ⟨e, he, heq⟩ := c.prod_θr_comparison c' h1 h2 σ ν hθ K.1
    refine ⟨e, ?_, heq⟩
    have hu : IsUnit ((K.1.sort (· ≤ ·)).map ν).prod :=
      List.prod_isUnit fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hν i
    rcases he with rfl | rfl
    · exact hu
    · exact hu.neg
  choose e he heq using hcomp
  have key : ∀ b, c'.combo p h2 b =
      c.combo p h1 (fun L => e (τ.symm L) * b (τ.symm L)) := by
    intro b
    show ∑ K, smU (f := f) (D := D) _ (((LU D).ι.app V'').hom (b K)) *
        ((K.1.sort (· ≤ ·)).map (c'.θr h2)).prod =
      ∑ L, smU (f := f) (D := D) _ (((LU D).ι.app V'').hom (e (τ.symm L) * b (τ.symm L))) *
        ((L.1.sort (· ≤ ·)).map (c.θr h1)).prod
    conv_rhs => rw [← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Equiv.symm_apply_apply, heq K, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (b K)]
  let einv : {K : Finset (Fin n) // K.card = p} → Γ(X, V'') := fun K => ↑((he K).unit⁻¹)
  have heinv : ∀ K, einv K * e K = 1 := fun K => (he K).val_inv_mul
  let winv : Γ(X, V'') := ↑(hw.unit⁻¹)
  have hwinv : winv * w = 1 := hw.val_inv_mul
  let Φ : ({K : Finset (Fin n) // K.card = p} → Γ(X, V'')) →
      ({K : Finset (Fin n) // K.card = p} → Γ(X, V'')) := fun a K => einv K * w * a (τ K)
  have hΦ : ∀ a, c.combo p h1 (c.hε ε h1 • a) = c'.combo p h2 (c'.hε ε h2 • Φ a) := by
    intro a
    rw [key]
    congr 1
    funext L
    simp only [Pi.smul_apply, smul_eq_mul, Φ, Equiv.apply_symm_apply, hh]
    linear_combination (-(c'.hε ε h2 * w * a L)) * heinv (τ.symm L)
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    funext L
    have := congrFun h (τ.symm L)
    simp only [Φ, Equiv.apply_symm_apply] at this
    have h' := congrArg (fun z => winv * e (τ.symm L) * z) this
    linear_combination h' + (a₂ L - a₁ L) * (winv * w) * heinv (τ.symm L) +
      (a₂ L - a₁ L) * hwinv
  have hΦsurj : ∀ b, ∃ a, Φ a = b := by
    intro b
    refine ⟨fun L => winv * e (τ.symm L) * b (τ.symm L), funext fun K => ?_⟩
    simp only [Φ, Equiv.symm_apply_apply]
    linear_combination b K * (einv K * e K) * hwinv + b K * heinv K
  refine ⟨fun a₁ a₂ h => hΦinj (H.1 ((hΦ a₁).symm.trans (h.trans (hΦ a₂)))), fun ω => ?_⟩
  refine (H.2 ω).trans ⟨fun ⟨b, hb⟩ => ?_, fun ⟨a, ha⟩ => ⟨Φ a, ha.trans (hΦ a)⟩⟩
  obtain ⟨a, rfl⟩ := hΦsurj b
  exact ⟨a, hb.trans (hΦ a).symm⟩

/-- **Refining logarithmic coordinate data.** If `c'` lives on `W' ⊆ W`, its coordinates are those
of `c` restricted and permuted by `σ`, its boundary coordinates are boundary coordinates of `c`,
and the other boundary coordinates of `c` are units on `W'`, then a basis for `c'` on an affine
`V'' ⊆ W'` is a basis for `c`. -/
theorem basisAt_of_refinement (c' : LogData n f D) (hD : D.IsRelativeSNC n f)
    (hWW : (c'.W : X.Opens) ≤ c.W) (σ : Equiv.Perm (Fin n))
    (ht : ∀ i, c'.t i = X.presheaf.map (homOfLE hWW).op (c.t (σ i)))
    (hσS : ∀ m : Fin c'.r, ∃ k : Fin c.r, σ (Fin.castLE c'.hr m) = Fin.castLE c.hr k)
    (hunit : ∀ k : Fin c.r, (∀ m : Fin c'.r, σ (Fin.castLE c'.hr m) ≠ Fin.castLE c.hr k) →
      IsUnit (X.presheaf.map (homOfLE hWW).op (c.t (Fin.castLE c.hr k))))
    (hs : ∀ k, c.s k * ((LU D).ι.app c.W).hom (c.t (Fin.castLE c.hr k)) = 1)
    (hs' : ∀ m, c'.s m * ((LU D).ι.app c'.W).hom (c'.t (Fin.castLE c'.hr m)) = 1)
    (ε : Bool) (p : ℕ) {V'' : X.affineOpens} (h2 : (V'' : X.Opens) ≤ c'.W)
    (H : c'.BasisAt hD ε p h2) : c.BasisAt hD ε p (h2.trans hWW) := by
  classical
  set h1 : (V'' : X.Opens) ≤ c.W := h2.trans hWW
  let resW : Γ(X, c.W) →+* Γ(X, V'') := (X.presheaf.map (homOfLE h1).op).hom
  have hres : ∀ a : Γ(X, c.W), X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE hWW).op a)
      = resW a := fun a => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hsV : ∀ k,
      c.σ h1 (Fin.castLE c.hr k) * ((LU D).ι.app V'').hom (resW (c.t (Fin.castLE c.hr k))) = 1 := by
    intro k
    have hk : ((Fin.castLE c.hr k : Fin n) : ℕ) < c.r := by simp
    simp only [LogData.σ, dif_pos hk]
    have := congrArg ((LU D).toScheme.presheaf.map
      ((Opens.map (LU D).ι.base).map (homOfLE h1)).op) (hs k)
    rw [map_mul, map_one, app_restrict] at this
    convert this using 3
    all_goals exact congrArg _ (Fin.ext rfl)
  have hsV' : ∀ m, c'.σ h2 (Fin.castLE c'.hr m) *
      ((LU D).ι.app V'').hom (resW (c.t (σ (Fin.castLE c'.hr m)))) = 1 := by
    intro m
    have hm : ((Fin.castLE c'.hr m : Fin n) : ℕ) < c'.r := by simp
    simp only [LogData.σ, dif_pos hm]
    have := congrArg ((LU D).toScheme.presheaf.map
      ((Opens.map (LU D).ι.base).map (homOfLE h2)).op) (hs' m)
    rw [map_mul, map_one, app_restrict, ht, hres] at this
    convert this using 3
    all_goals exact congrArg _ (Fin.ext rfl)
  let ν : Fin n → Γ(X, V'') := fun i =>
    if (σ i : ℕ) < c.r ∧ ¬ ((i : ℕ) < c'.r) then resW (c.t (σ i)) else 1
  have hnot : ∀ i : Fin n, ¬ ((i : ℕ) < c'.r) → ∀ hk : (σ i : ℕ) < c.r,
      ∀ m : Fin c'.r, σ (Fin.castLE c'.hr m) ≠ Fin.castLE c.hr ⟨σ i, hk⟩ := by
    intro i hi hk m hm
    have : Fin.castLE c'.hr m = i := σ.injective (hm.trans (Fin.ext rfl))
    exact hi (this ▸ (by simp))
  have hν : ∀ i, IsUnit (ν i) := by
    intro i
    simp only [ν]
    split_ifs with h
    · have hu := hunit ⟨σ i, h.1⟩ (hnot i h.2 h.1)
      have : Fin.castLE c.hr ⟨σ i, h.1⟩ = σ i := Fin.ext rfl
      rw [this] at hu
      rw [← hres]
      exact hu.map _
    · exact isUnit_one
  have hcoef : ∀ i, c'.σ h2 i = ((LU D).ι.app V'').hom (ν i) * c.σ h1 (σ i) := by
    intro i
    by_cases hi : (i : ℕ) < c'.r
    · obtain ⟨k, hk⟩ := hσS ⟨i, hi⟩
      have hik : Fin.castLE c'.hr ⟨i, hi⟩ = i := Fin.ext rfl
      rw [hik] at hk
      have hνi : ν i = 1 := by simp only [ν]; rw [if_neg (fun h => h.2 hi)]
      rw [hνi, map_one, one_mul, hk]
      refine eq_of_mul_eq_one (x := ((LU D).ι.app V'').hom (resW (c.t (σ i)))) ?_ ?_
      · have := hsV' ⟨i, hi⟩
        rwa [hik] at this
      · rw [hk]
        exact hsV k
    · by_cases hk : (σ i : ℕ) < c.r
      · have hνi : ν i = resW (c.t (σ i)) := by simp only [ν]; rw [if_pos ⟨hk, hi⟩]
        have hc' : c'.σ h2 i = 1 := by simp only [LogData.σ, dif_neg hi]
        rw [hc', hνi]
        have := hsV ⟨σ i, hk⟩
        have e : Fin.castLE c.hr ⟨σ i, hk⟩ = σ i := Fin.ext rfl
        rw [e] at this
        rw [mul_comm]
        exact this.symm
      · have hνi : ν i = 1 := by simp only [ν]; rw [if_neg (fun h => hk h.1)]
        simp only [LogData.σ, dif_neg hi, dif_neg hk, hνi, map_one, mul_one]
  have hθ : ∀ i, c'.θr h2 i =
      smU (f := f) (D := D) _ (((LU D).ι.app V'').hom (ν i)) * c.θr h1 (σ i) := by
    intro i
    simp only [LogData.θr]
    rw [c'.totalRestrict_θ h2 i, c.totalRestrict_θ h1 (σ i)]
    have ht' : X.presheaf.map (homOfLE h2).op (c'.t i) = resW (c.t (σ i)) := by
      rw [ht i, hres]
    rw [ht', hcoef i]
    exact (congrArg (· * _) (map_mul (smU (f := f) (D := D) _) _ _)).trans (mul_assoc _ _ _)
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin c'.r → Fin c.r, ∀ m, σ (Fin.castLE c'.hr m) = Fin.castLE c.hr (κ m) :=
    ⟨fun m => (hσS m).choose, fun m => (hσS m).choose_spec⟩
  have hκinj : Function.Injective κ := fun m m' h => Fin.castLE_injective c'.hr
    (σ.injective ((hκ m).trans ((congrArg _ h).trans (hκ m').symm)))
  let P : Fin c.r → Prop := fun k => ∀ m : Fin c'.r, σ (Fin.castLE c'.hr m) ≠ Fin.castLE c.hr k
  have himg : Finset.univ.filter (fun k => ¬ P k) = Finset.univ.image κ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, P, not_forall,
      not_not]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Fin.castLE_injective c.hr ((hκ m).symm.trans hm)⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, hκ m⟩
  let w : Γ(X, V'') := ε.rec 1 (resW (∏ k ∈ Finset.univ.filter P, c.t (Fin.castLE c.hr k)))
  have hw : IsUnit w := by
    cases ε
    · exact isUnit_one
    · show IsUnit (resW (∏ k ∈ Finset.univ.filter P, c.t (Fin.castLE c.hr k)))
      rw [← hres]
      refine IsUnit.map _ ?_
      rw [map_prod]
      exact IsUnit.prod_iff.mpr fun k hk => hunit k (Finset.mem_filter.mp hk).2
  have hh : c.hε ε h1 = w * c'.hε ε h2 := by
    cases ε
    · exact (mul_one 1).symm
    · show resW (∏ i, c.t (Fin.castLE c.hr i)) = resW (∏ k ∈ Finset.univ.filter P,
        c.t (Fin.castLE c.hr k)) * X.presheaf.map (homOfLE h2).op (∏ m, c'.t (Fin.castLE c'.hr m))
      have : X.presheaf.map (homOfLE h2).op (∏ m, c'.t (Fin.castLE c'.hr m)) =
          resW (∏ m, c.t (σ (Fin.castLE c'.hr m))) := by
        rw [← hres, map_prod, map_prod, map_prod]
        exact Finset.prod_congr rfl fun m _ => by rw [ht]
      rw [this, ← map_mul, ← Finset.prod_filter_mul_prod_filter_not Finset.univ P, himg,
        Finset.prod_image fun m _ m' _ h => hκinj h]
      congr 2
      exact Finset.prod_congr rfl fun m _ => by rw [hκ]
  exact c.basisAt_of_comparison c' hD ε p h1 h2 σ ν hν hθ w hw hh H

end LogData

namespace LogChart

variable {hD : D.IsRelativeSNC n f} (c : LogChart n f D hD)

/-- On every affine open `W' ⊆ W`, the forms `h^ε θ_K` are a basis of the logarithmic forms,
twisted by `-D` if `ε`. -/
theorem basisε (ε : Bool) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) :
    Function.Injective (fun a => c.combo p hW' (c.hε ε hW' • a)) ∧
      ∀ ω, ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD (bif ε then D.suppIdeal else ⊤) p W' ↔
        ∃ a, (TB ((LU D).ι ≫ f)).incl (p : ℤ) ω = c.combo p hW' (c.hε ε hW' • a) := by
  have h := (c.toLogData.hasLogBasis_iff hD p hW').mp (c.basis p hW')
  cases ε
  exacts [h.1, h.2]

/-- The coefficient map `a ↦ ∑_K a_K (h^ε θ_K)` onto the sections of the logarithmic forms over a
chart affine `W' ⊆ W`. -/
noncomputable def coeff (ε : Bool) (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) :
    ({K : Finset (Fin n) // K.card = p} → Γ(X, W')) →ₗ[Γ(X, W')]
      Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) p, (W' : X.Opens)) where
  toFun a := ⟨(c.exists_incl_eq_combo p hW' (c.hε ε hW' • a)).choose,
    ((c.basisε ε p hW').2 _).2 ⟨a, (c.exists_incl_eq_combo p hW' _).choose_spec⟩⟩
  map_add' a b := by
    refine Subtype.ext (incl_injective (f := f) (D := D) (p : ℤ) _ ?_)
    refine (c.exists_incl_eq_combo p hW' _).choose_spec.trans ?_
    refine Eq.trans ?_ (map_add (DirectSum.of _ (p : ℤ)) _ _).symm
    rw [smul_add, c.combo_add]
    exact congrArg₂ (· + ·) (c.exists_incl_eq_combo p hW' _).choose_spec.symm
      (c.exists_incl_eq_combo p hW' _).choose_spec.symm
  map_smul' r a := by
    refine Subtype.ext (incl_injective (f := f) (D := D) (p : ℤ) _ ?_)
    refine (c.exists_incl_eq_combo p hW' _).choose_spec.trans ?_
    refine Eq.trans ?_ (incl_smul_eq f D _ _ _).symm
    rw [smul_comm, c.combo_smul]
    exact congrArg (_ * ·) (c.exists_incl_eq_combo p hW' _).choose_spec.symm

/-- The underlying form of a section of the logarithmic forms. -/
abbrev form {ε : Bool} {p : ℕ} {W' : X.Opens}
    (ω : Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) p, W')) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ f)).piece (p : ℤ)).val.obj
      (op ((LU D).ι ⁻¹ᵁ W')) :=
  (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) p).obj (op W')) from ω).1

/-- The form of `coeff ε p hW' a` is `∑_K a_K (h^ε θ_K)`. -/
theorem incl_coeff (ε : Bool) (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) (a) :
    (TB ((LU D).ι ≫ f)).incl (p : ℤ) (form (c.coeff ε p hW' a)) =
      c.combo p hW' (c.hε ε hW' • a) :=
  (c.exists_incl_eq_combo p hW' _).choose_spec

/-- The coefficient map is bijective. -/
theorem coeff_bijective (ε : Bool) (p : ℕ) {W' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W) :
    Function.Bijective (c.coeff ε p hW') := by
  refine ⟨fun a b hab => (c.basisε ε p hW').1 ?_, fun ω => ?_⟩
  · have := congrArg (fun z => (TB ((LU D).ι ≫ f)).incl (p : ℤ) (form z)) hab
    simp only at this
    rwa [c.incl_coeff, c.incl_coeff] at this
  · obtain ⟨a, ha⟩ := ((c.basisε ε p hW').2 (form ω)).1
      (show ↥((logModuleSubmodule n f D hD (bif ε then D.suppIdeal else ⊤) p).obj (op W'))
        from ω).2
    exact ⟨a, Subtype.ext (incl_injective (f := f) (D := D) (p : ℤ) _
      ((c.incl_coeff ε p hW' a).trans ha.symm))⟩

/-- The coefficient isomorphism over a chart affine. -/
noncomputable def coeffEquiv (ε : Bool) (p : ℕ) {W' : X.affineOpens}
    (hW' : (W' : X.Opens) ≤ c.W) :
    ({K : Finset (Fin n) // K.card = p} → Γ(X, W')) ≃ₗ[Γ(X, W')]
      Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) p, (W' : X.Opens)) :=
  LinearEquiv.ofBijective _ (c.coeff_bijective ε p hW')

/-- The coefficient maps commute with restriction to `W'' ≤ W'`. -/
theorem map_coeff (ε : Bool) (p : ℕ) {W' W'' : X.affineOpens} (hW' : (W' : X.Opens) ≤ c.W)
    (h'' : (W'' : X.Opens) ≤ W') (a) :
    (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p).presheaf.map (homOfLE h'').op
        (c.coeff ε p hW' a) =
      c.coeff ε p (h''.trans hW') (fun K => X.presheaf.map (homOfLE h'').op (a K)) := by
  refine Subtype.ext (incl_injective (f := f) (D := D) (p : ℤ) _ ?_)
  refine Eq.trans ?_ (c.incl_coeff ε p (h''.trans hW') _).symm
  refine ((TB ((LU D).ι ≫ f)).totalRestrict_incl _ (p : ℤ) _).symm.trans ?_
  refine (congrArg _ (c.incl_coeff ε p hW' a)).trans ?_
  refine (c.totalRestrict_combo p hW' h'' _).trans (congrArg _ (funext fun K => ?_))
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, c.map_hε]

end LogChart

end Chart

section QC

open Stacks.AlgebraicGeometry.AffinePushforward Stacks.AlgebraicGeometry.QuasicoherentBaseChange
  Stacks.AlgebraicGeometry.TorsionQuasicoherent

/-- **Quasi-coherence is detected by localization on the basic opens of a covering family of
affine opens.** -/
theorem isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover (N : X.Modules)
    (P : X.affineOpens → Prop) (hP : ∀ x : X, ∃ V, P V ∧ x ∈ (V : X.Opens))
    (h : ∀ V : X.affineOpens, P V → ∀ a : Γ(X, V),
      letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    N.IsQuasicoherent := by
  refine isQuasicoherent_of_presentations N (fun V : {V : X.affineOpens // P V} ↦ (V.1 : X.Opens))
    (IsOpenCover.mk ?_) fun V ↦ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := hP x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  obtain ⟨⟨U, hU'⟩, hPU⟩ := V
  have hU : IsAffineOpen U := hU'
  have h1 : (N.restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrict_fromSpec N hU (h ⟨U, hU'⟩ hPU)
  have h2 : ((N.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent := inferInstance
  have iso : (N.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ N.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app N).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app N
  have : (N.restrict U.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso h2
  exact (nonempty_presentation_of_isoSpec hU.isoSpec _).some

/-- A linear map `M → N` that, under identifications `M ≅ R^ι` and `N ≅ A^ι`, is the map induced
by `R → A` is a localization away from `a` when `A` is the localization of `R` away from `a`. -/
theorem isLocalizedModule_of_coeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (a : R)
    [IsLocalization.Away a A] {ι : Type*} [Finite ι] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N] (res : M →ₗ[R] N)
    (eM : (ι → R) ≃ₗ[R] M) (eN : (ι → A) ≃ₗ[A] N)
    (hcomm : ∀ c, res (eM c) = eN (fun i => algebraMap R A (c i))) :
    IsLocalizedModule.Away a res := by
  have h1 : IsLocalizedModule (Submonoid.powers a)
      (LinearMap.pi fun i : ι => (Algebra.linearMap R A) ∘ₗ LinearMap.proj i) := inferInstance
  have h2 := IsLocalizedModule.of_linearEquiv (Submonoid.powers a) _ (eN.restrictScalars R)
    (hf := h1)
  have h3 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers a) _ eM.symm (hf := h2)
  have e : ((eN.restrictScalars R : (ι → A) ≃ₗ[R] N) : (ι → A) →ₗ[R] N) ∘ₗ
      (LinearMap.pi fun i : ι => (Algebra.linearMap R A) ∘ₗ LinearMap.proj i) ∘ₗ
        (eM.symm : M →ₗ[R] (ι → R)) = res := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨c, rfl⟩ := eM.surjective m
    simp [hcomm]
    rfl
  rw [← e]
  exact h3

variable {n : ℕ} {f : X ⟶ S} [SmoothOfRelativeDimension n f] {D : MMP.Mori.Divisor X}

/-- On an affine open `U` of a logarithmic chart, restriction of the logarithmic forms from `U`
to a basic open `D(a)` is a localization away from `a`. -/
theorem LogChart.isLocalizedModule {hD : D.IsRelativeSNC n f} (c : LogChart n f D hD)
    (ε : Bool) (p : ℕ) {U : X.affineOpens} (hU : (U : X.Opens) ≤ c.W) (a : Γ(X, U)) :
    letI := moduleOfLE (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p) (X.basicOpen_le a)
    IsLocalizedModule.Away a
      (restrictₗ (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p) (X.basicOpen_le a)) := by
  letI := moduleOfLE (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p) (X.basicOpen_le a)
  letI := algebraOfLE X (X.basicOpen_le a)
  haveI := isScalarTowerOfLE (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p)
    (X.basicOpen_le a)
  haveI : IsLocalization.Away a Γ(X, X.basicOpen a) := U.2.isLocalization_basicOpen a
  have hV : ((X.affineBasicOpen a : X.affineOpens) : X.Opens) ≤ c.W :=
    (X.basicOpen_le a).trans hU
  let eM := c.coeffEquiv ε p hU
  let eN : ({K : Finset (Fin n) // K.card = p} → Γ(X, X.basicOpen a)) ≃ₗ[Γ(X, X.basicOpen a)]
      Γ(logModule n f D hD (bif ε then D.suppIdeal else ⊤) p, X.basicOpen a) :=
    c.coeffEquiv ε p (W' := X.affineBasicOpen a) hV
  have hcomm : ∀ b, restrictₗ (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p)
      (X.basicOpen_le a) (eM b) = eN (fun K => algebraMap Γ(X, U) Γ(X, X.basicOpen a) (b K)) :=
    fun b => c.map_coeff ε p hU (W'' := X.affineBasicOpen a) (X.basicOpen_le a) b
  exact isLocalizedModule_of_coeff a _ eM eN hcomm

section Coherent

open Stacks.AlgebraicGeometry.CoherentTFAE

/-- If the sections of `F` over an affine open `U` are a finite `Γ(X, U)`-module, so is the
module of `F` on `Spec Γ(X, U)`. -/
theorem finite_specModule_of_finite (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (h : Module.Finite Γ(X, U) Γ(F, U)) : Module.Finite Γ(X, U) (specModule F hU) := by
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  let e2 := (restrictSectionsEquiv F hU ⊤).trans
    (sectionsCongrSelf F hTop (fromSpec_image_le hU ⊤))
  have iso : specRestrict F hU ≅ F.restrict hU.fromSpec :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_inv_ι).app F
  have e1 := (moduleSpecΓFunctor.mapIso iso).toLinearEquiv
  have : Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec)) :=
    Module.Finite.equiv e2.symm
  exact Module.Finite.equiv e1.symm

/-- On a locally Noetherian scheme, a quasi-coherent module with finite sections over the members
of a covering family of affine opens is coherent. -/
theorem isCoherent_of_cover [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    (P : X.affineOpens → Prop) (hP : ∀ x : X, ∃ V, P V ∧ x ∈ (V : X.Opens))
    (hfin : ∀ V : X.affineOpens, P V → Module.Finite Γ(X, V) Γ(F, (V : X.Opens))) :
    F.IsCoherent := by
  have hcov : TopologicalSpace.IsOpenCover
      (fun V : {V : X.affineOpens // P V} => (V.1 : X.Opens)) := by
    refine TopologicalSpace.IsOpenCover.mk (top_le_iff.mp fun x _ => ?_)
    obtain ⟨V, hV, hx⟩ := hP x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩
  haveI : F.IsFiniteType := isFiniteType_of_cover_isFiniteTildeOn F _ hcov (fun V => V.1.2)
    fun V => isFiniteTildeOn_of_finite_specModule F _ _
      (finite_specModule_of_finite F V.1.2 (hfin _ V.2))
  exact Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType F

end Coherent

/-- The logarithmic forms `Ω^p_{X/S}(log D)`, twisted by `-D` if `ε`, are quasi-coherent. -/
theorem logModule_isQuasicoherent (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) :
    (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ_of_cover _
    (fun V => ∃ c : LogChart n f D hD, (V : X.Opens) ≤ c.W)
    (fun x => ⟨(nonempty_sncChart hD x).some.W, ⟨(nonempty_sncChart hD x).some.toLogChart hD,
      le_rfl⟩, (nonempty_sncChart hD x).some.hx⟩)
    (fun _ ⟨c, hV⟩ a => c.isLocalizedModule ε p hV a)

/-- Over a locally Noetherian scheme, the logarithmic forms `Ω^p_{X/S}(log D)`, twisted by `-D` if
`ε`, are coherent. -/
theorem logModule_isCoherent [IsLocallyNoetherian X] (hD : D.IsRelativeSNC n f) (ε : Bool)
    (p : ℕ) : (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p).IsCoherent :=
  haveI := logModule_isQuasicoherent hD ε p
  isCoherent_of_cover _ (fun V => ∃ c : LogChart n f D hD, (V : X.Opens) ≤ c.W)
    (fun x => ⟨(nonempty_sncChart hD x).some.W, ⟨(nonempty_sncChart hD x).some.toLogChart hD,
      le_rfl⟩, (nonempty_sncChart hD x).some.hx⟩)
    (fun _ ⟨c, hV⟩ => Module.Finite.equiv (c.coeffEquiv ε p hV))

/-- The de Rham differential maps logarithmic forms, twisted by `-D` if `ε`, to logarithmic
forms. -/
theorem deRham_mem_relativeLogForms (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) (W : X.Opens) (ω)
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n f D hD (bif ε then D.suppIdeal else ⊤) p W) :
    ((Scheme.Hom.deRhamComplex ((LU D).ι ≫ f)).d p (p + 1)).val.app (op ((LU D).ι ⁻¹ᵁ W)) ω ∈
      MMP.Mori.Divisor.relativeLogForms n f D hD (bif ε then D.suppIdeal else ⊤)
        ((p + 1 : ℕ) : ℤ) W := by
  cases ε
  · exact ((MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).1 p W ω).1 hω
  · exact ((MMP.Mori.Divisor.relativeLogForms_free_and_deRhamD_mem n f D hD).1 p W ω).2 hω

/-- The logarithmic de Rham complex `Ω^•_{X/S}(log D)` (twisted by `-D` if `ε`), with terms the
logarithmic forms. -/
noncomputable abbrev logCx (hD : D.IsRelativeSNC n f) (ε : Bool) :
    CochainComplex (SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  subCx f D (logSubmodule n f D hD (bif ε then D.suppIdeal else ⊤))
    (fun p W ω hω => deRham_mem_relativeLogForms hD ε p W.unop ω hω)

/-- The logarithmic de Rham complex is `logCx`. -/
theorem relativeLogDeRhamComplex_eq_logCx (hD : D.IsRelativeSNC n f) (ε : Bool) :
    MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤) =
      logCx hD ε :=
  relativeLogDeRhamComplex_eq_subCx n f D hD _ (deRham_mem_relativeLogForms hD ε)

open Stacks.DeRhamDirectImage in
/-- The term of degree `p` of the logarithmic de Rham complex is the `𝒪_X`-module `logModule`,
read over `f⁻¹𝒪_S`. -/
theorem exists_iso_relativeLogDeRhamComplex_X (hD : D.IsRelativeSNC n f) (ε : Bool) (p : ℕ) :
    Nonempty ((MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD
      (bif ε then D.suppIdeal else ⊤)).X p ≅
        (pushforward (toInverseImageBase f)).obj
          (logModule n f D hD (bif ε then D.suppIdeal else ⊤) p)) :=
  ⟨eqToIso (by rw [relativeLogDeRhamComplex_eq_logCx hD ε]; rfl) ≪≫
    logSubmoduleIso n f D hD _ p⟩

end QC

end G1

end LogForms

end MMP.Mori.Divisor.LogSpreadingProof

end
