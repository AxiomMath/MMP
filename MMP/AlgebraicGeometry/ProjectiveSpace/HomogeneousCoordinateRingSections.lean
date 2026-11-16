module

public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.SectionSelection
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreSectionsSurjective

/-!
# The homogeneous coordinate ring of an integral subscheme of projective space in high degree

Let `K` be a field, `S = K[T₀, …, Tₙ]` with its grading by total degree, `ℙⁿ_K = Proj S` and
`ι : Y ⟶ ℙⁿ_K` an integral closed subscheme. Write `I(Y) ⊆ S` for the homogeneous ideal of forms
vanishing on `Y` and `S(Y) = S ⧸ I(Y)` for the homogeneous coordinate ring. Then for all large `t`

`dim_K S(Y)_t = dim_K Γ(Y, 𝒪_Y(1)^{⊗ t})`,

where `𝒪_Y(1) = ι^* 𝒪(1)` (Hartshorne II Ex. 5.9, Serre).

The map is `a ↦ ι^*(a)`, a form of degree `t` read as a global section of `𝒪(t)` and restricted
to `Y`. Its kernel in degree `t` is `I(Y)_t` for every `t`: on an integral `Y` a section of an
invertible module is zero exactly when it vanishes at the generic point, and the section of a form
`a` vanishes at a point `y` of `ℙⁿ_K` exactly when `a ∈ y`. It is surjective for all large `t`,
since `Γ(ℙⁿ_K, 𝒪(t))` consists of the forms of degree `t` and restriction of sections of the
powers of the ample `𝒪(1)` to a closed subscheme is surjective in high degree.

## Main results

* `MMP.isAmple_twistingSheaf_one_polyGrading`, `MMP.isAmple_pullback_twistingSheaf_one`:
  ampleness of `𝒪(1)` and of its pull-backs, in the spelling of
  `AlgebraicGeometry.degreeWithRespectTo`.
* `MMP.pullbackGlobalSections_degreeSection_eq_zero_iff`: the kernel clause.
* `MMP.eventually_finrank_globalSections_tensorPower_eq_finrank_homogeneousQuotient`: the
  equality of dimensions for all large `t`.

## Implementation notes

`I(Y)` is `ProjectiveSpectrum.vanishingIdeal` of the support of `Y`, the ideal of forms lying in
every homogeneous prime of the support; since `Y` is integral this is the homogeneous ideal of
the variety `Y`. `S(Y)_t` is the image of the degree-`t` forms in `S ⧸ I(Y)`. The twisting sheaf
`𝒪(t)` and the tensor power `𝒪(1)^{⊗ t}` are identified by
`Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory Filter AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace MMP

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance] Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

/-- The polynomial ring is generated in degree one over its degree-zero part. -/
lemma adjoin_polyGrading_one_eq_top :
    Algebra.adjoin (polyGrading K n 0) ((polyGrading K n 1 : Set (MvPolynomial (Fin (n + 1)) K)))
      = ⊤ := by
  rw [← Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one (polyGrading K n)]
  exact Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule _ _

/-- **The section of `𝒪(t)` attached to a form of degree `t`, as a `K`-linear map** into the
global sections over the ground field. -/
def degreeSectionOverField (t : ℕ) :
    polyGrading K n t →ₗ[K]
      globalSectionsOverField K (projToSpecCoeff K n) (twistingSheaf (polyGrading K n) t) where
  toFun a := Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear K n t a
  map_add' := (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear K n t).map_add
  map_smul' c a := by
    rw [RingHom.id_apply, (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear K n t).map_smul]
    erw [ModuleCat.restrictScalars.smul_def]

@[simp]
theorem degreeSectionOverField_apply (t : ℕ) (a : polyGrading K n t) :
    degreeSectionOverField K n t a = degreeSection (polyGrading K n) t a :=
  rfl

/-- The pull-back of a twist of `𝒪_{ℙⁿ_K}` along any morphism into `ℙⁿ_K` is invertible. -/
theorem isInvertibleModule_pullback_twistingSheaf {Y : Scheme.{u}}
    (ι : Y ⟶ AlgebraicGeometry.Proj (polyGrading K n)) (t : ℤ) :
    Stacks.Ample.IsInvertibleModule Y
      ((Scheme.Modules.pullback ι).obj (twistingSheaf (polyGrading K n) t)) :=
  have := Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule K n t
  Stacks.InvertiblePullback.isInvertibleModule_pullback ι _

/-- The pull-back of a twist of `𝒪_{ℙⁿ_K}` is invertible, in the spelling of
`Stacks.SheafOfModules.Invertible.tensorPower`. -/
theorem stacksIsInvertible_pullback_twistingSheaf {Y : Scheme.{u}}
    (ι : Y ⟶ AlgebraicGeometry.Proj (polyGrading K n)) (t : ℤ) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback ι).obj (twistingSheaf (polyGrading K n) t)) :=
  @Stacks.RelativeVeryAmple.stacksIsInvertible Y _
    (isInvertibleModule_pullback_twistingSheaf K n ι t)

attribute [local instance] isInvertibleModule_pullback_twistingSheaf
  stacksIsInvertible_pullback_twistingSheaf

/-- `𝒪(1)` is ample on `ℙⁿ_K`, in the spelling of `AlgebraicGeometry.degreeWithRespectTo`. -/
theorem isAmple_twistingSheaf_one_polyGrading :
    Scheme.Modules.IsAmple (AlgebraicGeometry.Proj (polyGrading K n))
      (twistingSheaf (polyGrading K n) 1) :=
  Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
    (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one K n)

/-- The pull-back of `𝒪(1)` along an affine morphism into `ℙⁿ_K`, such as a closed immersion, is
ample. -/
theorem isAmple_pullback_twistingSheaf_one {Y : Scheme.{u}}
    (ι : Y ⟶ AlgebraicGeometry.Proj (polyGrading K n)) [IsAffineHom ι] :
    Scheme.Modules.IsAmple Y
      ((Scheme.Modules.pullback ι).obj (twistingSheaf (polyGrading K n) 1)) :=
  @Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple Y _
    (isInvertibleModule_pullback_twistingSheaf K n ι 1)
    (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom ι _
      (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one K n))

/-- **The kernel clause.** For an integral closed subscheme `Y` of `ℙⁿ_K`, the section of a form
`a` of degree `t` restricts to zero on `Y` exactly when `a` vanishes on the support of `Y`. -/
theorem pullbackGlobalSections_degreeSection_eq_zero_iff
    (V : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData) [IsIntegral V.subscheme] (t : ℕ)
    (a : polyGrading K n t) :
    pullbackGlobalSections V.subschemeι (twistingSheaf (polyGrading K n) t)
        (degreeSection (polyGrading K n) t a) = 0 ↔
      (a : MvPolynomial (Fin (n + 1)) K) ∈ ProjectiveSpectrum.vanishingIdeal
        (V.support : Set (AlgebraicGeometry.Proj (polyGrading K n))) := by
  have hNL := Stacks.AlgebraicGeometry.ProjTwistPowers.nonvanishingLocusDegreeSection
    (polyGrading K n) (adjoin_polyGrading_one_eq_top K n) t a
  have hrange := V.range_subschemeι
  refine Iff.trans ?_ (ProjectiveSpectrum.mem_vanishingIdeal _ _).symm
  constructor
  · intro h0 y hy
    rw [← hrange] at hy
    obtain ⟨z, rfl⟩ := hy
    by_contra hn
    have hmem : V.subschemeι.base z ∈ Stacks.Ample.nonvanishingLocus
        (X := AlgebraicGeometry.Proj (polyGrading K n)) (twistingSheaf (polyGrading K n) t)
        (degreeSection (polyGrading K n) t a) := by
      rw [hNL]
      exact (AlgebraicGeometry.Proj.mem_basicOpen _ _ _).2 hn
    have hz := (Set.ext_iff.1
      (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections V.subschemeι
        (twistingSheaf (polyGrading K n) t) (degreeSection (polyGrading K n) t a)) z).1 hmem
    rw [Stacks.Ample.mem_nonvanishingLocus_iff] at hz
    apply hz
    erw [h0, map_zero]
    exact Submodule.zero_mem _
  · intro ha
    have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading K n)) :=
      LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff K n)
    have : IsLocallyNoetherian V.subscheme := isLocallyNoetherian_of_isImmersion V.subschemeι
    refine (Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection
      _ _ _).trans ?_
    refine Stacks.EnriquesSeveriZariski.pullbackGlobalSection_eq_zero_of_mem_maximalSmul
      V.subschemeι _ rfl _ ?_
    have hx : V.subschemeι.base (genericPoint V.subscheme) ∉ Stacks.Ample.nonvanishingLocus
        (X := AlgebraicGeometry.Proj (polyGrading K n)) (twistingSheaf (polyGrading K n) t)
        (degreeSection (polyGrading K n) t a) := by
      rw [hNL]
      intro hb
      refine (AlgebraicGeometry.Proj.mem_basicOpen _ _ _).1 hb (ha _ ?_)
      rw [← hrange]
      exact ⟨_, rfl⟩
    exact not_not.1 hx

/-- `𝒪(1)^{⊗ t} ≅ 𝒪(t)` on `ℙⁿ_K`, in the tensor-power spelling of Tag 0BJ8. -/
def tensorPowerIsoTwistingSheaf (t : ℤ) :
    tensorPower (AlgebraicGeometry.Proj (polyGrading K n)).presheaf
        (AlgebraicGeometry.Proj (polyGrading K n)).ringCatSheaf.2
        (twistingSheaf (polyGrading K n) 1) t ≅ twistingSheaf (polyGrading K n) t :=
  Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso _ _ t ≪≫
    Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf _
      (adjoin_polyGrading_one_eq_top K n) t

/-- `ι^* 𝒪(t) ≅ (ι^* 𝒪(1))^{⊗ t}` along a morphism `ι` into `ℙⁿ_K`, for `t ≥ 0`. -/
def pullbackTwistingSheafIsoTensorPower {Y : Scheme.{u}}
    (ι : Y ⟶ AlgebraicGeometry.Proj (polyGrading K n)) (t : ℕ) :
    (Scheme.Modules.pullback ι).obj (twistingSheaf (polyGrading K n) t) ≅
      tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback ι).obj (twistingSheaf (polyGrading K n) 1)) t :=
  (Scheme.Modules.pullback ι).mapIso
      (Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf _
        (adjoin_polyGrading_one_eq_top K n) t).symm ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso ι _ t ≪≫
    (@Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Y _
      (isInvertibleModule_pullback_twistingSheaf K n ι 1) t).symm

/-- **The homogeneous coordinate ring of an integral closed subscheme of `ℙⁿ_K` computes the
sections of the powers of `𝒪_Y(1)` in high degree** (Hartshorne II Ex. 5.9). For an integral
closed subscheme `ι : Y ⟶ ℙⁿ_K` with homogeneous ideal `I(Y)`, for all large `t`
`dim_K Γ(Y, 𝒪_Y(1)^{⊗ t}) = dim_K (S ⧸ I(Y))_t`. -/
theorem eventually_finrank_globalSections_tensorPower_eq_finrank_homogeneousQuotient
    (V : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData) [IsIntegral V.subscheme] :
    ∀ᶠ t : ℕ in atTop,
      Module.finrank K (globalSectionsOverField K (V.subschemeι ≫ projToSpecCoeff K n)
        (tensorPower V.subscheme.presheaf V.subscheme.ringCatSheaf.2
          ((Scheme.Modules.pullback V.subschemeι).obj (twistingSheaf (polyGrading K n) 1))
          (t : ℤ))) =
      Module.finrank K ((polyGrading K n t).map
        (Ideal.Quotient.mkₐ K (ProjectiveSpectrum.vanishingIdeal
          (V.support : Set (AlgebraicGeometry.Proj (polyGrading K n)))).toIdeal).toLinearMap) := by
  set ι := V.subschemeι
  set f := projToSpecCoeff K n
  set I := ProjectiveSpectrum.vanishingIdeal
    (V.support : Set (AlgebraicGeometry.Proj (polyGrading K n)))
  obtain ⟨n₀, hn₀⟩ := exists_forall_surjective_pullbackGlobalSection_tensorPower f ι _
    (isAmple_twistingSheaf_one_polyGrading K n)
  refine eventually_atTop.2 ⟨n₀, fun t ht => ?_⟩
  let E := (Stacks.EnriquesSeveriZariski.globalSectionsFunctor K (ι ≫ f)).mapIso
    (pullbackTwistingSheafIsoTensorPower K n ι t)
  let β : polyGrading K n t →ₗ[K] _ := E.toLinearEquiv.toLinearMap ∘ₗ
    Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField K f ι
      (twistingSheaf (polyGrading K n) t) ∘ₗ degreeSectionOverField K n t
  let g : polyGrading K n t →ₗ[K] MvPolynomial (Fin (n + 1)) K ⧸ I.toIdeal :=
    (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap ∘ₗ (polyGrading K n t).subtype
  have hker : LinearMap.ker β = LinearMap.ker g := by
    ext a
    simp only [LinearMap.mem_ker, β, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact pullbackGlobalSections_degreeSection_eq_zero_iff K n V t a
  have hsurj : Function.Surjective β := by
    have hres : Function.Surjective
        (pullbackGlobalSections ι (twistingSheaf (polyGrading K n) t)) :=
      Stacks.AmpleFibreNeighbourhood.surjective_pullbackGlobalSections_congr ι
        (tensorPowerIsoTwistingSheaf K n t) fun y => (hn₀ t ht y).imp fun s hs =>
          (Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection
            _ _ s).trans hs
    exact E.toLinearEquiv.surjective.comp
      (hres.comp (Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection n t).2)
  have hrange : (polyGrading K n t).map (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap =
      LinearMap.range g := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h := LinearEquiv.finrank_eq (β.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange))
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
  rwa [hrange]

end MMP
