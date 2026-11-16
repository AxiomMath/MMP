module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ParameterPointFibre
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
public import MMP.AlgebraicTopology.CapProduct.Restriction
public import MMP.AlgebraicTopology.CapProduct.CupSupport
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas
public import MMP.AlgebraicTopology.OrientationClass.CapDeformation
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
public import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness

/-!
# Constancy of specialized classes along a locally trivial family

Let `g : P → T` be a continuous map to a Hausdorff manifold `T` with an oriented atlas, `μ` a
Borel–Moore class of `P`, and `W ⊆ T` a connected open subset over which `g` is a product:
`ψ : X × W ≃ₜ g⁻¹(W)` over `W`. For `s ∈ W` and the local orientation class `u_s` of `T` at `s`,
the specialization `g^*u_s ∩ μ ∈ H_*(g⁻¹ s)`, carried to `X` along `g⁻¹ s ≅ X × {s} ≅ X`, does not
depend on `s ∈ W` (Fulton, Lemma 19.2(c), over an open subset of the base).

## Main definitions

* `MMP.Fourfold.fibreHomeomorphOfProd`: the homeomorphism `g⁻¹(s) ≃ₜ X` given by a product
  structure `ψ : X × W ≃ₜ g⁻¹(W)` over `W ∋ s`.

## Main results

* `MMP.Fourfold.isLocalOrientationClass_map_inclHom`: the restriction of a local orientation
  class to an open subset is the local orientation class of the open subset.
* `pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass`:
  `g^*u_s ∩ μ`, carried to `X`, does not depend on `s ∈ W`.
* `MMP.Fourfold.pushforward_preimageRestrictHom_capProductSupportPullback`: the projection
  formula `ι_*((ι ≫ g)^*c ∩ x) = g^*c ∩ ι_*x` for the supported cap product and a proper `ι`.
* `MMP.Fourfold.isSmoothVariety_opens_of_le_smoothLocus`: an open inside the smooth locus
  of a curve over a perfect field is a smooth curve.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1–19.2.
-/

@[expose] public section

open CategoryTheory Set Topology MMP MMP.borelMooreHomology

namespace MMP.Fourfold

open Finsupp ThomClass SingularChain SingularCochain FundamentalClass

section localOrientation

variable {T : TopCat.{0}} [T2Space T] {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [ChartedSpace H T] {R : Type} [CommRing R]

/-- The complement of `⟨s, hs⟩` in an open `W` maps into the complement of `s` in `T`. -/
theorem compl_singleton_subset_preimage_inclHom (W : TopologicalSpace.Opens T) {s : T}
    (hs : s ∈ W) :
    ({⟨s, hs⟩}ᶜ : Set (TopCat.of W)) ⊆ (inclHom W).hom ⁻¹' ({s}ᶜ : Set T) :=
  fun _ hx hxs ↦ hx (Subtype.ext hxs)

/-- **Local orientation classes restrict to open subsets.** For an open subset `W` of a manifold
`T` and `s ∈ W`, the restriction to `(W, W - s)` of the local orientation class of `T` at `s` is
the local orientation class of `W` at `s`, for the induced atlas of `W`. -/
theorem isLocalOrientationClass_map_inclHom (W : TopologicalSpace.Opens T) {s : T} (hs : s ∈ W)
    {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {s} n}
    (hu : IsLocalOrientationClass R b s u) :
    IsLocalOrientationClass (T := TopCat.of W) R b ⟨s, hs⟩
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (inclHom W)
        (compl_singleton_subset_preimage_inclHom W hs) n).hom u) := by
  obtain ⟨α, hα, hc, hrep⟩ := hu
  refine ⟨cochainPullback R (inclHom W) n α,
    cochainPullback_mem_relCocycles (inclHom W) (compl_singleton_subset_preimage_inclHom W hs) hα,
    ⟨cochainPullback_mem_relCocycles (inclHom W)
      (compl_singleton_subset_preimage_inclHom W hs) hα, ?_⟩, ?_⟩
  · rintro e' ⟨_, ⟨x, rfl⟩, he'⟩ hs' v hv hvt
    rw [mem_singleton_iff] at he'
    subst he'
    set e := chartAt H (x : T)
    have hse : s ∈ e.source := by
      rwa [OpenPartialHomeomorph.subtypeRestr_source] at hs'
    have hes : (e.subtypeRestr ⟨x⟩) ⟨s, hs⟩ = e s := rfl
    have hvt' : range (affineSimplex v) ⊆ e.target := fun y hy ↦ by
      have h1 := (e.subtypeRestr ⟨x⟩).map_target (hvt hy)
      have h2 := (e.subtypeRestr ⟨x⟩).right_inv (hvt hy)
      rw [OpenPartialHomeomorph.subtypeRestr_source] at h1
      rw [← h2]
      exact e.map_source h1
    have key := hc.2 e (chart_mem_atlas H (x : T)) hse v (by rwa [← hes]) hvt'
    rw [linearCombination_single, one_smul] at key ⊢
    change α ((inclHom W).hom.comp (chartSimplexOf (e.subtypeRestr ⟨x⟩) v hvt)) = 1
    convert key using 2
    ext t
    simp only [ContinuousMap.comp_apply, chartSimplexOf_apply]
    exact (e.subtypeRestr_symm_eqOn ⟨x⟩ (hvt ⟨t, rfl⟩)).symm
  · rw [relativeSingularCohomologyEquiv_map, hrep, relCohomologyMap_mk]

end localOrientation

section setCongr

variable {R : Type} [CommRing R]

/-- **The cap product with supports does not depend on how the support is written**: for
`X₁ = X₂`, the classes `c ∩ a` over `X₁` and over `X₂` correspond under `X₁ ≃ X₂`. -/
theorem pushforward_setCongr_capProductSupport {Y : TopCat.{0}} {X₁ X₂ : Set Y} (h : X₁ = X₂)
    (hX₁ : IsClosed X₁) (hd₁ : HasProperNeighbourhoodDeformations X₁) (hX₂ : IsClosed X₂)
    (hd₂ : HasProperNeighbourhoodDeformations X₂) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X₁ j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) :
    (pushforward R (ModuleCat.of R R) (TopCat.ofHom (Homeomorph.setCongr h : C(X₁, X₂)))
        (Homeomorph.setCongr h).isProperMap (k - j)).hom
        (capProductSupport R Y hX₁ hd₁ j k c a) =
      capProductSupport R Y hX₂ hd₂ j k
        ((relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 Y)
          (fun x hx ↦ by rwa [h]) j).hom c) a := by
  subst h
  rw [relativeSingularCohomology.map_id]
  exact pushforward_id_apply' R _ _ (TopCat.ext fun _ ↦ rfl) _ _

/-- Pull-backs along equal maps agree. -/
theorem relativeSingularCohomology_map_congr {Y' Y : TopCat.{0}} {f f' : Y' ⟶ Y} (hff' : f = f')
    {A : Set Y} {A' : Set Y'} (h : A' ⊆ f ⁻¹' A) (h' : A' ⊆ f' ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map R (ModuleCat.of R R) f h j =
      relativeSingularCohomology.map R (ModuleCat.of R R) f' h' j := by
  subst hff'
  rfl

end setCongr

section family

variable {T : TopCat.{0}} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H] [ChartedSpace H T] {R : Type} [CommRing R]
  {P X : TopCat.{0}}

/-- The open subset `g⁻¹(W)` of `P`. -/
abbrev preimageOpens (g : P ⟶ T) (W : TopologicalSpace.Opens T) : TopologicalSpace.Opens P :=
  TopologicalSpace.Opens.comap g.hom W

variable {g : P ⟶ T} {W : TopologicalSpace.Opens T}

/-- A point of the fibre `g⁻¹(s)` over `s ∈ W` lies in `g⁻¹(W)`. -/
theorem mem_preimageOpens_of_mem_preimage_singleton {s : T} (hs : s ∈ W) {x : P}
    (hx : x ∈ g ⁻¹' {s}) : x ∈ preimageOpens g W := by
  change g x ∈ W
  rw [show g x = s from hx]
  exact hs

/-- **The fibre of a product family.** For a product structure `ψ : X × W ≃ₜ g⁻¹(W)` over `W`
and `s ∈ W`, the fibre `g⁻¹(s)` is homeomorphic to `X`. -/
def fibreHomeomorphOfProd (ψ : X × W ≃ₜ preimageOpens g W) (hψ : ∀ p, g (ψ p : P) = (p.2 : T))
    {s : T} (hs : s ∈ W) : (g ⁻¹' {s} : Set P) ≃ₜ X where
  toFun x := (ψ.symm ⟨x.1, mem_preimageOpens_of_mem_preimage_singleton hs x.2⟩).1
  invFun y := ⟨ψ (y, ⟨s, hs⟩), hψ (y, ⟨s, hs⟩)⟩
  left_inv x := by
    apply Subtype.ext
    have key : ∀ z : preimageOpens g W, g z.1 = s → (ψ ((ψ.symm z).1, ⟨s, hs⟩) : P) = z.1 :=
      fun z hz ↦ by
        have h3 := hψ (ψ.symm z)
        rw [ψ.apply_symm_apply] at h3
        have : ((ψ.symm z).1, (⟨s, hs⟩ : W)) = ψ.symm z :=
          Prod.ext rfl (Subtype.ext (hz.symm.trans h3))
        rw [this, ψ.apply_symm_apply]
    exact key _ x.2
  right_inv y := by
    change (ψ.symm (ψ (y, ⟨s, hs⟩))).1 = y
    rw [ψ.symm_apply_apply]
  continuous_toFun := continuous_fst.comp (ψ.symm.continuous.comp
    (continuous_subtype_val.subtype_mk _))
  continuous_invFun := ((continuous_subtype_val.comp (ψ.continuous.comp
    (continuous_id.prodMk continuous_const))).subtype_mk _)

/-- `g⁻¹(s) ≃ₜ X`, as a morphism of `TopCat`. -/
def fibreTransportHom (ψ : X × W ≃ₜ preimageOpens g W) (hψ : ∀ p, g (ψ p : P) = (p.2 : T))
    {s : T} (hs : s ∈ W) : TopCat.of (g ⁻¹' {s} : Set P) ⟶ X :=
  TopCat.ofHom (fibreHomeomorphOfProd ψ hψ hs : C(_, X))

/-- The map `g⁻¹(s) → X` induced by `ψ` is proper. -/
theorem isProperMap_fibreTransportHom (ψ : X × W ≃ₜ preimageOpens g W)
    (hψ : ∀ p, g (ψ p : P) = (p.2 : T)) {s : T} (hs : s ∈ W) :
    IsProperMap (fibreTransportHom ψ hψ hs) :=
  (fibreHomeomorphOfProd ψ hψ hs).isProperMap

section key

/-- `ψ : X × W → g⁻¹(W)`, as a morphism of `TopCat`. -/
def prodHom (ψ : X × W ≃ₜ preimageOpens g W) :
    TopCat.of (X × W) ⟶ TopCat.of (preimageOpens g W) :=
  TopCat.ofHom (ψ : C(X × W, preimageOpens g W))

/-- Composing `ψ` with `g⁻¹(W) → P → T` is the projection `X × W → W` followed by the inclusion
of `W`. -/
theorem prodHom_comp (ψ : X × W ≃ₜ preimageOpens g W) (hψ : ∀ p, g (ψ p : P) = (p.2 : T)) :
    prodHom ψ ≫ inclHom (preimageOpens g W) ≫ g = prodSnd X (TopCat.of W) ≫ inclHom W :=
  ConcreteCategory.hom_ext _ _ fun p ↦ hψ p

/-- The preimage of `s` under the projection `X × W → W` is the preimage under `ψ` of the fibre
`g⁻¹(s) ∩ g⁻¹(W)`. -/
theorem prodSnd_preimage_eq (ψ : X × W ≃ₜ preimageOpens g W) (hψ : ∀ p, g (ψ p : P) = (p.2 : T))
    {s : T} (hs : s ∈ W) :
    prodSnd X (TopCat.of W) ⁻¹' {⟨s, hs⟩} =
      prodHom ψ ⁻¹' ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s})) := by
  ext p
  change p.2 = ⟨s, hs⟩ ↔ g (ψ p : P) = s
  rw [hψ, Subtype.ext_iff]

/-- The fibre `g⁻¹(s)`, as a subset of `g⁻¹(W)`, is homeomorphic to `X` through `ψ`. -/
def interFibreTransportHomeomorph (ψ : X × W ≃ₜ preimageOpens g W)
    (hψ : ∀ p, g (ψ p : P) = (p.2 : T)) {s : T} (hs : s ∈ W) :
    ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s}) : Set (TopCat.of (preimageOpens g W))) ≃ₜ X where
  toFun x := (ψ.symm x.1).1
  invFun y := ⟨ψ (y, ⟨s, hs⟩), hψ (y, ⟨s, hs⟩)⟩
  left_inv x := by
    apply Subtype.ext
    have h3 := hψ (ψ.symm x.1)
    rw [ψ.apply_symm_apply] at h3
    have : ((ψ.symm x.1).1, (⟨s, hs⟩ : W)) = ψ.symm x.1 :=
      Prod.ext rfl (Subtype.ext ((show g (x.1 : P) = s from x.2).symm.trans h3))
    change ψ ((ψ.symm x.1).1, (⟨s, hs⟩ : W)) = x.1
    rw [this, ψ.apply_symm_apply]
  right_inv y := by
    change (ψ.symm (ψ (y, ⟨s, hs⟩))).1 = y
    rw [ψ.symm_apply_apply]
  continuous_toFun := continuous_fst.comp (ψ.symm.continuous.comp continuous_subtype_val)
  continuous_invFun := (ψ.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

/-- The map `g⁻¹(s) ∩ g⁻¹(W) → X` read through `ψ`, as a morphism of `TopCat`. -/
def interFibreTransportHom (ψ : X × W ≃ₜ preimageOpens g W)
    (hψ : ∀ p, g (ψ p : P) = (p.2 : T)) {s : T} (hs : s ∈ W) :
    TopCat.of ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s})) ⟶ X :=
  TopCat.ofHom (interFibreTransportHomeomorph ψ hψ hs : C(_, X))

/-- The map `g⁻¹(s) ∩ g⁻¹(W) → X` read through `ψ` is proper. -/
theorem isProperMap_interFibreTransportHom (ψ : X × W ≃ₜ preimageOpens g W)
    (hψ : ∀ p, g (ψ p : P) = (p.2 : T)) {s : T} (hs : s ∈ W) :
    IsProperMap (interFibreTransportHom ψ hψ hs) :=
  (interFibreTransportHomeomorph ψ hψ hs).isProperMap

/-- Three successive pull-backs are the pull-back along the composite. -/
theorem relativeSingularCohomology_map_map_map_apply {Y₀ Y₁ Y₂ Y₃ : TopCat.{0}}
    (f₁ : Y₁ ⟶ Y₀) (f₂ : Y₂ ⟶ Y₁) (f₃ : Y₃ ⟶ Y₂) {A₀ : Set Y₀} {A₁ : Set Y₁} {A₂ : Set Y₂}
    {A₃ : Set Y₃} (h₁ : A₁ ⊆ f₁ ⁻¹' A₀) (h₂ : A₂ ⊆ f₂ ⁻¹' A₁) (h₃ : A₃ ⊆ f₃ ⁻¹' A₂) (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y₀ A₀ j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) f₃ h₃ j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f₂ h₂ j).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) f₁ h₁ j).hom x)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (f₃ ≫ f₂ ≫ f₁)
        (fun _ hx ↦ h₁ (h₂ (h₃ hx))) j).hom x := by
  rw [relativeSingularCohomology.map_comp R _ f₃ (f₂ ≫ f₁) h₃ (fun _ hx ↦ h₁ (h₂ hx)),
    relativeSingularCohomology.map_comp R _ f₂ f₁ h₂ h₁]
  rfl

/-- Three successive pull-backs along maps with equal composites agree. -/
theorem relativeSingularCohomology_map_map_map_eq {Y₀ Y₁ Y₂ Y₃ Y₁' Y₂' : TopCat.{0}}
    (f₁ : Y₁ ⟶ Y₀) (f₂ : Y₂ ⟶ Y₁) (f₃ : Y₃ ⟶ Y₂) (f₁' : Y₁' ⟶ Y₀) (f₂' : Y₂' ⟶ Y₁')
    (f₃' : Y₃ ⟶ Y₂') (hcomp : f₃ ≫ f₂ ≫ f₁ = f₃' ≫ f₂' ≫ f₁') {A₀ : Set Y₀} {A₁ : Set Y₁}
    {A₂ : Set Y₂} {A₃ : Set Y₃} {A₁' : Set Y₁'} {A₂' : Set Y₂'} (h₁ : A₁ ⊆ f₁ ⁻¹' A₀)
    (h₂ : A₂ ⊆ f₂ ⁻¹' A₁) (h₃ : A₃ ⊆ f₃ ⁻¹' A₂) (h₁' : A₁' ⊆ f₁' ⁻¹' A₀)
    (h₂' : A₂' ⊆ f₂' ⁻¹' A₁') (h₃' : A₃ ⊆ f₃' ⁻¹' A₂') (j : ℤ)
    (x : relativeSingularCohomology R (ModuleCat.of R R) Y₀ A₀ j) :
    (relativeSingularCohomology.map R (ModuleCat.of R R) f₃ h₃ j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f₂ h₂ j).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) f₁ h₁ j).hom x)) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) f₃' h₃' j).hom
        ((relativeSingularCohomology.map R (ModuleCat.of R R) f₂' h₂' j).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) f₁' h₁' j).hom x)) := by
  rw [relativeSingularCohomology_map_map_map_apply, relativeSingularCohomology_map_map_map_apply]
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ x)
    (relativeSingularCohomology_map_congr (A := A₀) (A' := A₃) hcomp _ _ j)

variable [T2Space T] [T5Space P] [TopologicalSpace.MetrizableSpace X]

include H in
/-- The fibre `pr⁻¹ ⟨s, hs⟩` of `X × W → W` has proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_prodSnd_opens {s : T} (hs : s ∈ W) :
    HasProperNeighbourhoodDeformations (prodSnd X (TopCat.of W) ⁻¹' {⟨s, hs⟩}) :=
  hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton X (T := TopCat.of W) H ⟨s, hs⟩

/-- **The specialization over `s`, read on the product.** For a product structure
`ψ : X × W ≃ₜ g⁻¹(W)` over an open `W ∋ s`, the class `g^*u ∩ μ ∈ H_*(g⁻¹ s)`, carried to `X`,
is `pr^*(u|_W) ∩ ψ^{-1}_*(μ|_{g⁻¹ W})` carried to `X` along `X × {s} ≅ X`. -/
theorem pushforward_fibreTransportHom_capProductSupportPullback_eq_fibreProj
    (ψ : X × W ≃ₜ preimageOpens g W) (hψ : ∀ p, g (ψ p : P) = (p.2 : T))
    (hd : ∀ s : T, HasProperNeighbourhoodDeformations (g ⁻¹' {s})) {s : T} (hs : s ∈ W)
    (j m : ℤ) (u : cohomologyWithSupports R (ModuleCat.of R R) T {s} j)
    (μ : borelMooreHomology R (ModuleCat.of R R) P m) :
    (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs)
        (isProperMap_fibreTransportHom ψ hψ hs) (m - j)).hom
        (capProductSupportPullback R g isClosed_singleton (hd s) j m u μ) =
      (pushforward R (ModuleCat.of R R) (fibreProj (T := TopCat.of W) X ⟨s, hs⟩)
          (isProperMap_fibreProj X _) (m - j)).hom
        (capProductSupportPullback R (prodSnd X (TopCat.of W)) isClosed_singleton
          (hasProperNeighbourhoodDeformations_prodSnd_opens (H := H) hs) j m
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (inclHom W)
            (compl_singleton_subset_preimage_inclHom W hs) j).hom u)
          ((pushforward R (ModuleCat.of R R)
              (TopCat.ofHom (ψ.symm : C(preimageOpens g W, X × W))) ψ.symm.isProperMap m).hom
            ((restrict R (ModuleCat.of R R) (preimageOpens g W) m).hom μ))) := by
  have hY := prodSnd_preimage_eq ψ hψ hs
  have hd₃ := hasProperNeighbourhoodDeformations_prodSnd_opens (X := X) (H := H) hs
  have hXs : IsClosed (g ⁻¹' {s}) := isClosed_singleton.preimage g.hom.continuous
  have hX₂ : IsClosed ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s})) :=
    hXs.preimage (inclHom (preimageOpens g W)).hom.continuous
  have hY₂ : IsClosed (prodHom ψ ⁻¹' ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s}))) :=
    hX₂.preimage (prodHom ψ).hom.continuous
  have hdY₂ : HasProperNeighbourhoodDeformations
      (prodHom ψ ⁻¹' ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s}))) := hY ▸ hd₃
  have hdX₂ : HasProperNeighbourhoodDeformations
      ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s})) := by
    have h := HasProperNeighbourhoodDeformations.preimage_homeomorph hdY₂ ψ.symm
    convert h using 1
    ext x
    change _ ↔ g ((ψ (ψ.symm x) : preimageOpens g W) : P) ∈ ({s} : Set T)
    rw [ψ.apply_symm_apply]
    rfl
  have hres : IsProperMap (TopCat.ofHom (prodHom ψ |>.hom.restrictPreimage
      ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s})))) :=
    (show IsProperMap (prodHom ψ) from ψ.isProperMap).restrictPreimage _
  have hq' := isProperMap_interFibreTransportHom ψ hψ hs
  have hrq : IsProperMap (TopCat.ofHom (prodHom ψ |>.hom.restrictPreimage
      ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s}))) ≫ interFibreTransportHom ψ hψ hs) :=
    hq'.comp hres
  have hfib : fibreProj (T := TopCat.of W) X ⟨s, hs⟩ =
      TopCat.ofHom (Homeomorph.setCongr hY : C(_, _)) ≫
        (TopCat.ofHom (prodHom ψ |>.hom.restrictPreimage
          ((inclHom (preimageOpens g W)) ⁻¹' (g ⁻¹' {s}))) ≫ interFibreTransportHom ψ hψ hs) :=
    ConcreteCategory.hom_ext _ _ fun p ↦ by
      change p.1.1 = (ψ.symm (ψ p.1)).1
      rw [ψ.symm_apply_apply]
  have hc : (relativeSingularCohomology.map R (ModuleCat.of R R) (𝟙 (TopCat.of (X × W)))
        (fun x hx ↦ by
          change x ∈ (prodSnd X (TopCat.of W) ⁻¹' {⟨s, hs⟩})ᶜ
          rwa [hY]) j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodSnd X (TopCat.of W))
          {⟨s, hs⟩} j).hom
          ((relativeSingularCohomology.map R (ModuleCat.of R R) (inclHom W)
            (compl_singleton_subset_preimage_inclHom W hs) j).hom u)) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (prodHom ψ) _ j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom (preimageOpens g W))
          (g ⁻¹' {s}) j).hom
          ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g {s} j).hom u)) :=
    relativeSingularCohomology_map_map_map_eq _ _ _ _ _ _
      (by rw [Category.id_comp, prodHom_comp ψ hψ]) _ _ _ _ _ _ j u
  symm
  rw [capProductSupportPullback_apply,
    pushforward_apply_congr R hfib _ (hrq.comp (Homeomorph.setCongr hY).isProperMap),
    pushforward_comp_apply' R _ _ (Homeomorph.setCongr hY).isProperMap hrq,
    pushforward_setCongr_capProductSupport hY _ _ hY₂ hdY₂, hc,
    ← capProductSupportPullback_apply R (prodHom ψ) hX₂ hdY₂,
    pushforward_comp_apply' R _ _ hres hq',
    pushforward_restrictPreimage_capProductSupportPullback R (prodHom ψ) ψ.isProperMap hX₂ hdX₂
      hdY₂]
  have hμ : (pushforward R (ModuleCat.of R R) (prodHom ψ) ψ.isProperMap m).hom
      ((pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (ψ.symm : C(preimageOpens g W, X × W))) ψ.symm.isProperMap m).hom
        ((restrict R (ModuleCat.of R R) (preimageOpens g W) m).hom μ)) =
      (restrict R (ModuleCat.of R R) (preimageOpens g W) m).hom μ := by
    rw [← pushforward_comp_apply' R _ _ ψ.symm.isProperMap ψ.isProperMap]
    exact pushforward_id_apply' R _ _ (ConcreteCategory.hom_ext _ _ fun x ↦ ψ.apply_symm_apply x)
      _ _
  rw [hμ, ← capProductSupportPullback_apply R (inclHom (preimageOpens g W)) hXs hdX₂ j m,
    ← pushforward_opensInterMap_restrict_capProductSupport R P (preimageOpens g W) hXs (hd s)
      hdX₂ j m _ μ, capProductSupportPullback_apply]
  have hO : opensInter (preimageOpens g W) (g ⁻¹' {s}) = ⊤ :=
    eq_top_iff.2 fun x _ ↦ mem_preimageOpens_of_mem_preimage_singleton hs x.2
  have hp : IsProperMap (inclHom (opensInter (preimageOpens g W) (g ⁻¹' {s}))) :=
    (Topology.IsClosedEmbedding.subtypeVal (hO ▸ isClosed_univ)).isProperMap
  have hcomp : opensInterMap (preimageOpens g W) (g ⁻¹' {s}) ≫ interFibreTransportHom ψ hψ hs =
      inclHom (opensInter (preimageOpens g W) (g ⁻¹' {s})) ≫ fibreTransportHom ψ hψ hs :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have key2 : ∀ y : borelMooreHomology R (ModuleCat.of R R)
      (TopCat.of (opensInter (preimageOpens g W) (g ⁻¹' {s}))) (m - j),
      (pushforward R (ModuleCat.of R R) (interFibreTransportHom ψ hψ hs) hq' (m - j)).hom
        ((pushforward R (ModuleCat.of R R) (opensInterMap (preimageOpens g W) (g ⁻¹' {s}))
          (isProperMap_opensInterMap _ _) (m - j)).hom y) =
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs)
        (isProperMap_fibreTransportHom ψ hψ hs) (m - j)).hom
        ((pushforward R (ModuleCat.of R R) (inclHom (opensInter (preimageOpens g W) (g ⁻¹' {s})))
          hp (m - j)).hom y) := fun y ↦
    ((pushforward_comp_apply' R _ _ (isProperMap_opensInterMap _ _) hq' _ y).symm.trans
      (pushforward_apply_congr R hcomp _ ((isProperMap_fibreTransportHom ψ hψ hs).comp hp) _
        y)).trans
      (pushforward_comp_apply' R _ _ hp (isProperMap_fibreTransportHom ψ hψ hs) _ y)
  rw [key2, pushforward_inclHom_restrict_of_eq_top R hO hp]

/-- **Constancy of the specialization along a locally trivial family** (Fulton, Lemma 19.2(c),
over an open subset of the base). Let `g : P → T` be continuous, `T` a Hausdorff manifold with an
oriented atlas, `W ⊆ T` a connected open subset and `ψ : X × W ≃ₜ g⁻¹(W)` a product structure
over `W`. For `s, s' ∈ W` and the local orientation classes `u_s`, `u_{s'}` of `T`, the classes
`g^*u_s ∩ μ` and `g^*u_{s'} ∩ μ`, carried to `X` along `g⁻¹ s ≅ X` and `g⁻¹ s' ≅ X`, agree. -/
theorem pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass
    [ConnectedSpace W] (hT : IsOrientedAtlas H T) {n : ℕ} (hn : 0 < n)
    (b : Module.Basis (Fin n) ℝ H) (ψ : X × W ≃ₜ preimageOpens g W)
    (hψ : ∀ p, g (ψ p : P) = (p.2 : T))
    (hd : ∀ s : T, HasProperNeighbourhoodDeformations (g ⁻¹' {s})) (m : ℤ)
    (μ : borelMooreHomology R (ModuleCat.of R R) P m) {s s' : T} (hs : s ∈ W) (hs' : s' ∈ W)
    {u : cohomologyWithSupports R (ModuleCat.of R R) T {s} n}
    {u' : cohomologyWithSupports R (ModuleCat.of R R) T {s'} n}
    (hu : IsLocalOrientationClass R b s u) (hu' : IsLocalOrientationClass R b s' u') :
    (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs)
        (isProperMap_fibreTransportHom ψ hψ hs) (m - n)).hom
        (capProductSupportPullback R g isClosed_singleton (hd s) n m u μ) =
      (pushforward R (ModuleCat.of R R) (fibreTransportHom ψ hψ hs')
        (isProperMap_fibreTransportHom ψ hψ hs') (m - n)).hom
        (capProductSupportPullback R g isClosed_singleton (hd s') n m u' μ) := by
  rw [pushforward_fibreTransportHom_capProductSupportPullback_eq_fibreProj (H := H) ψ hψ hd hs,
    pushforward_fibreTransportHom_capProductSupportPullback_eq_fibreProj (H := H) ψ hψ hd hs']
  exact pushforward_fibreProj_capProductSupportPullback_eq_of_isLocalOrientationClass R
    (T := TopCat.of W) (isOrientedAtlas_opens hT W) hn b
    (fun t ↦ hasProperNeighbourhoodDeformations_prodSnd_preimage_singleton X H t) m _
    (isLocalOrientationClass_map_inclHom W hs hu) (isLocalOrientationClass_map_inclHom W hs' hu')

end key

end family

section preimageRestrict

variable {R : Type} [CommRing R] {V' P T' : TopCat.{0}}

/-- For `ι ≫ g = φ` and `Z ⊆ T'`, the map `φ⁻¹(Z) → g⁻¹(Z)` induced by `ι`. -/
def preimageRestrictHom (ι : V' ⟶ P) (g : P ⟶ T') {φ : V' ⟶ T'} (hφ : ι ≫ g = φ)
    (Z : Set T') : TopCat.of (φ ⁻¹' Z) ⟶ TopCat.of (g ⁻¹' Z) :=
  TopCat.ofHom ⟨fun x ↦ ⟨ι x.1, show (ι ≫ g) x.1 ∈ Z from hφ ▸ x.2⟩,
    (ι.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- For a proper `ι`, the induced map `φ⁻¹(Z) → g⁻¹(Z)` is proper. -/
theorem isProperMap_preimageRestrictHom {ι : V' ⟶ P} (hι : IsProperMap ι) (g : P ⟶ T')
    {φ : V' ⟶ T'} (hφ : ι ≫ g = φ) (Z : Set T') :
    IsProperMap (preimageRestrictHom ι g hφ Z) := by
  subst hφ
  have hset : (ι ≫ g) ⁻¹' Z = ι ⁻¹' (g ⁻¹' Z) := rfl
  have h := (hι.restrictPreimage (g ⁻¹' Z)).comp (Homeomorph.setCongr hset).isProperMap
  convert h using 1
  funext x
  apply Subtype.ext
  simp only [preimageRestrictHom, TopCat.hom_ofHom, ContinuousMap.coe_mk, Function.comp_apply,
    Set.restrictPreimage_coe]
  rfl

/-- **Projection formula for the supported cap product.** For a proper map `ι : V' → P`,
`g : P → T'` and a closed `Z ⊆ T'`, `ι_*((ι ≫ g)^*c ∩ x) = g^*c ∩ ι_*x` in `H_*(g⁻¹ Z)`. -/
theorem pushforward_preimageRestrictHom_capProductSupportPullback {ι : V' ⟶ P}
    (hι : IsProperMap ι) (g : P ⟶ T') {φ : V' ⟶ T'} (hφ : ι ≫ g = φ) {Z : Set T'}
    (hZ : IsClosed Z) (hd : HasProperNeighbourhoodDeformations (g ⁻¹' Z))
    (hd' : HasProperNeighbourhoodDeformations (φ ⁻¹' Z)) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) T' Z j)
    (x : borelMooreHomology R (ModuleCat.of R R) V' k) :
    (pushforward R (ModuleCat.of R R) (preimageRestrictHom ι g hφ Z)
        (isProperMap_preimageRestrictHom hι g hφ Z) (k - j)).hom
        (capProductSupportPullback R φ hZ hd' j k c x) =
      capProductSupportPullback R g hZ hd j k c
        ((pushforward R (ModuleCat.of R R) ι hι k).hom x) := by
  subst hφ
  rw [capProductSupportPullback_apply R (ι ≫ g), cohomologyWithSupports.pullback_comp]
  exact pushforward_restrictPreimage_capProductSupportPullback R ι hι
    (hZ.preimage g.hom.continuous) hd hd' j k
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) g Z j).hom c) x

end preimageRestrict

section ambientFibreCycle

open AlgebraicGeometry MMP.UnderlyingSpace

variable {R : Type} [CommRing R] {T : Scheme.{0}} [T.Over (Spec (.of ℂ))]
  [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [IsComplexScheme V]
  {G : Scheme.{0}} [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- For `ι ≫ g = f`, the maps induced on complex points satisfy `ι(ℂ) ≫ g(ℂ) = f(ℂ)`. -/
theorem fibreAmbientPointsHom_aux (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))] (g : G ⟶ T)
    [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))] (hf : ι ≫ g = f) :
    TopCat.ofHom (map (K := ℂ) ι) ≫ TopCat.ofHom (map (K := ℂ) g) =
      TopCat.ofHom (map (K := ℂ) f) := by
  subst hf
  rw [map_comp]
  rfl

/-- For `ι : V → G` and `g : G → T` with `ι ≫ g = f`, the map `V_t(ℂ) → g⁻¹(t) ⊆ G(ℂ)` from the
complex points of the scheme-theoretic fibre of `f` at a parameter point `t`. -/
noncomputable def fibreAmbientPointsHom (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))] (g : G ⟶ T)
    [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))] (hf : ι ≫ g = f)
    (t : ParameterPoint T) :
    TopCat.of (UnderlyingSpace ℂ (ParameterPoint.fibre f t)) ⟶
      TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {t.complexPoint}) :=
  ParameterPoint.fibreComplexPointsHom f t ≫
    preimageRestrictHom (TopCat.ofHom (map (K := ℂ) ι)) (TopCat.ofHom (map (K := ℂ) g))
      (fibreAmbientPointsHom_aux ι g hf) {t.complexPoint}

/-- For a proper `ι`, the map `fibreAmbientPointsHom ι g hf t` is proper. -/
theorem isProperMap_fibreAmbientPointsHom (ι : V ⟶ G) [ι.IsOver (Spec (.of ℂ))] [IsProper ι]
    (g : G ⟶ T) [g.IsOver (Spec (.of ℂ))] {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))]
    (hf : ι ≫ g = f) (t : ParameterPoint T) :
    IsProperMap (fibreAmbientPointsHom ι g hf t) :=
  (isProperMap_preimageRestrictHom (isProperMap_map (K := ℂ) ι) _
    (fibreAmbientPointsHom_aux ι g hf) _).comp
    (ParameterPoint.isProperMap_fibreComplexPointsHom f t)

end ambientFibreCycle

section smoothCurve

open AlgebraicGeometry

/-- **The smooth part of a curve is a smooth curve.** Let `C` be an integral separated
scheme of finite type and dimension one over a perfect field `K`, and `Γ` an open of `C` inside
the smooth locus of `C → Spec K` containing a point other than the generic point. Then `Γ`, over
`K` through `C`, is a smooth variety, smooth of relative dimension one. -/
theorem isSmoothVariety_opens_of_le_smoothLocus (K : Type) [Field K] [PerfectField K]
    {C : Scheme.{0}} [C.Over (Spec (.of K))] [IsIntegral C] [IsSeparated (C ↘ Spec (.of K))]
    [LocallyOfFiniteType (C ↘ Spec (.of K))] [QuasiCompact (C ↘ Spec (.of K))]
    (hC : topologicalKrullDim C = 1) (Γ : C.Opens) (hΓ : Γ ≤ (C ↘ Spec (.of K)).smoothLocus)
    {d : C} (hdΓ : d ∈ Γ) (hd : d ≠ genericPoint C) :
    letI : Γ.toScheme.Over (Spec (.of K)) := ⟨Γ.ι ≫ C ↘ Spec (.of K)⟩
    IsSmoothVariety K (Γ.toScheme ↘ Spec (.of K)) ∧
      SmoothOfRelativeDimension 1 (Γ.toScheme ↘ Spec (.of K)) := by
  letI : Γ.toScheme.Over (Spec (.of K)) := ⟨Γ.ι ≫ C ↘ Spec (.of K)⟩
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of K))
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (.of K))
  haveI : AlgebraicGeometry.IsNoetherian C := AlgebraicGeometry.IsNoetherian.mk
  haveI : Nonempty Γ.toScheme := ⟨⟨d, hdΓ⟩⟩
  haveI : IsIntegral Γ.toScheme := isIntegral_of_isOpenImmersion Γ.ι
  have hdimΓ : topologicalKrullDim Γ.toScheme = 1 := by
    have hstalk : ∀ x : Γ.toScheme,
        ringKrullDim (Γ.toScheme.presheaf.stalk x) = ringKrullDim (C.presheaf.stalk x.1) :=
      fun x ↦ ringKrullDim_eq_of_ringEquiv (Γ.stalkIso x).commRingCatIsoToRingEquiv
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    apply le_antisymm
    · refine iSup_le fun x ↦ ?_
      rw [hstalk x, ← hC, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y : C ↦ ringKrullDim (C.presheaf.stalk y)) x.1
    · refine le_iSup_of_le ⟨d, hdΓ⟩ ?_
      rw [hstalk ⟨d, hdΓ⟩]
      exact (Stacks.AlgebraicGeometry.AmpleDimensionOne.ringKrullDim_stalk_eq_one_of_ne_genericPoint
        C hC hd).ge
  haveI : AlgebraicGeometry.IsVariety K (Γ.toScheme ↘ Spec (.of K)) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstanceAs (IsSeparated (Γ.ι ≫ C ↘ Spec (.of K)))
      toLocallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType (Γ.ι ≫ C ↘ Spec (.of K)))
      toQuasiCompact := inferInstanceAs (QuasiCompact (Γ.ι ≫ C ↘ Spec (.of K))) }
  haveI : Smooth (Γ.toScheme ↘ Spec (.of K)) := by
    change Smooth (Γ.ι ≫ C ↘ Spec (.of K))
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.2 fun x _ ↦ hΓ x.2
  haveI : IsSmoothVariety K (Γ.toScheme ↘ Spec (.of K)) := { }
  refine ⟨inferInstance, ?_⟩
  -- `Γ` is its own fibre over the point of `Spec K`, of dimension one.
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq
    (Γ.toScheme ↘ Spec (.of K)) 1 fun x ↦ ?_
  have heq : ((Γ.toScheme ↘ Spec (.of K)) ⁻¹' {(Γ.toScheme ↘ Spec (.of K)) x}) =
      (Set.univ : Set Γ.toScheme) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let e : (Γ.toScheme ↘ Spec (.of K)).fiber ((Γ.toScheme ↘ Spec (.of K)) x) ≃ₜ Γ.toScheme :=
    ((Γ.toScheme ↘ Spec (.of K)).fiberHomeo _).trans ((Homeomorph.setCongr heq).trans
      (Homeomorph.Set.univ Γ.toScheme))
  rw [topologicalKrullDimAt_eq_of_homeomorph e,
    ← AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible K Γ.toScheme
      (Γ.toScheme ↘ Spec (.of K))]
  exact_mod_cast hdimΓ

end smoothCurve

/-- In a Noetherian space whose irreducible components are pairwise disjoint, every irreducible
component is open: its complement is the finite union of the other components. -/
theorem isOpen_of_mem_irreducibleComponents_of_disjoint {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] {A : Set α} (hA : A ∈ irreducibleComponents α)
    (hdisj : ∀ B ∈ irreducibleComponents α, ∀ C ∈ irreducibleComponents α, B ≠ C →
      Disjoint B C) : IsOpen A := by
  have heq : A = (⋃ B ∈ {B | B ∈ irreducibleComponents α ∧ B ≠ A}, B)ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, mem_setOf_eq, exists_prop, not_exists, not_and]
    refine ⟨fun hx B hB hxB ↦ Set.disjoint_left.1 (hdisj B hB.1 A hA hB.2) hxB hx,
      fun hx ↦ ?_⟩
    by_contra hxA
    exact hx (irreducibleComponent x) ⟨irreducibleComponent_mem_irreducibleComponents x,
      fun h ↦ hxA (h ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  rw [heq]
  refine (Set.Finite.isClosed_biUnion ?_ fun B hB ↦
    isClosed_of_mem_irreducibleComponents B hB.1).isOpen_compl
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun B hB ↦ hB.1

section clopenPiece

variable {R : Type} [CommRing R]

/-- A class pushed forward from a space mapping into an open `Ω`, restricted to `Ω` and pushed
back, is unchanged. -/
theorem pushforward_inclHom_restrict_pushforward_of_range_subset {A X : TopCat.{0}} [T2Space A]
    [T2Space X] (k : A ⟶ X) (hk : IsProperMap k) (Ω : TopologicalSpace.Opens X)
    (hΩ : Set.range k ⊆ Ω) (hp : IsProperMap (inclHom Ω)) (j : ℤ)
    (a : borelMooreHomology R (ModuleCat.of R R) A j) :
    (pushforward R (ModuleCat.of R R) (inclHom Ω) hp j).hom
        ((restrict R (ModuleCat.of R R) Ω j).hom
          ((pushforward R (ModuleCat.of R R) k hk j).hom a)) =
      (pushforward R (ModuleCat.of R R) k hk j).hom a := by
  have htop : TopologicalSpace.Opens.comap k.hom Ω = ⊤ :=
    eq_top_iff.2 fun x _ ↦ hΩ ⟨x, rfl⟩
  have hp' : IsProperMap (inclHom (TopologicalSpace.Opens.comap k.hom Ω)) :=
    (Topology.IsClosedEmbedding.subtypeVal (htop ▸ isClosed_univ)).isProperMap
  have hcomp : restrictPreimage k Ω ≫ inclHom Ω =
      inclHom (TopologicalSpace.Opens.comap k.hom Ω) ≫ k :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have h1 := restrict_pushforward_apply R (ModuleCat.of R R) k hk Ω j a
  change (pushforward R (ModuleCat.of R R) (inclHom Ω) hp j).hom
    ((restrict R (ModuleCat.of R R) Ω j).hom ((pushforward R (ModuleCat.of R R) k hk j).hom a)) = _
  have hq : IsProperMap (restrictPreimage k Ω ≫ inclHom Ω) := hcomp ▸ hk.comp hp'
  erw [h1]
  rw [pushforward_comp_apply R _ _ (isProperMap_restrictPreimage k Ω hk) hp hq,
    pushforward_apply_congr R hcomp hq (hk.comp hp'),
    ← pushforward_comp_apply R _ _ hp' hk (hk.comp hp'),
    pushforward_inclHom_restrict_of_eq_top R htop hp']

/-- A class pushed forward from a space mapping off an open `Ω` restricts to zero on `Ω`. -/
theorem restrict_pushforward_eq_zero_of_disjoint {A X : TopCat.{0}} [T2Space A] [T2Space X]
    (k : A ⟶ X) (hk : IsProperMap k) (Ω : TopologicalSpace.Opens X)
    (hΩ : Disjoint (Set.range k) Ω) (j : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) A j) :
    (restrict R (ModuleCat.of R R) Ω j).hom ((pushforward R (ModuleCat.of R R) k hk j).hom a) =
      0 := by
  haveI : IsEmpty (TopCat.of (TopologicalSpace.Opens.comap k.hom Ω)) :=
    ⟨fun x ↦ Set.disjoint_left.1 hΩ ⟨x.1, rfl⟩ x.2⟩
  have h1 := restrict_pushforward_apply R (ModuleCat.of R R) k hk Ω j a
  erw [h1]
  have h0 : (restrict R (ModuleCat.of R R) (TopologicalSpace.Opens.comap k.hom Ω) j).hom a = 0 :=
    ModuleCat.subsingleton_of_isZero (isZero_borelMooreHomology_of_isEmpty R _ _ j) |>.elim _ _
  rw [h0, map_zero]

/-- **Push-forward along a closed embedding with open image is injective.** -/
theorem pushforward_injective_of_isOpen_range {A X : TopCat.{0}} [T2Space A] [T2Space X]
    (k : A ⟶ X) (hk : Topology.IsClosedEmbedding k) (hopen : IsOpen (Set.range k)) (j : ℤ) :
    Function.Injective (pushforward R (ModuleCat.of R R) k hk.isProperMap j).hom := by
  intro a a' h
  set Ω : TopologicalSpace.Opens X := ⟨_, hopen⟩
  have htop : TopologicalSpace.Opens.comap k.hom Ω = ⊤ :=
    eq_top_iff.2 fun x _ ↦ ⟨x, rfl⟩
  have hp' : IsProperMap (inclHom (TopologicalSpace.Opens.comap k.hom Ω)) :=
    (Topology.IsClosedEmbedding.subtypeVal (htop ▸ isClosed_univ)).isProperMap
  have hemb : Topology.IsEmbedding (restrictPreimage k Ω) :=
    (hk.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict (Ω : Set X)
      (fun x ↦ x.2)
  have hsurj : Function.Surjective (restrictPreimage k Ω) := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨⟨x, ⟨x, rfl⟩⟩, rfl⟩
  set A' : TopCat.{0} := TopCat.of (TopologicalSpace.Opens.comap k.hom Ω)
  set B' : TopCat.{0} := TopCat.of Ω
  set e : A' ≃ₜ B' :=
    hemb.toHomeomorphOfSurjective hsurj
  have he : restrictPreimage k Ω = TopCat.ofHom (e : C(A', B')) :=
    ConcreteCategory.hom_ext _ _ fun _ ↦ rfl
  have key : ∀ b : borelMooreHomology R (ModuleCat.of R R) A j,
      (pushforward R (ModuleCat.of R R) (inclHom (TopologicalSpace.Opens.comap k.hom Ω)) hp' j).hom
        ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (e.symm : C(B', A'))) e.symm.isProperMap
          j).hom ((restrict R (ModuleCat.of R R) Ω j).hom
            ((pushforward R (ModuleCat.of R R) k hk.isProperMap j).hom b))) = b := fun b ↦ by
    have h1 := restrict_pushforward_apply R (ModuleCat.of R R) k hk.isProperMap Ω j b
    erw [h1]
    rw [pushforward_apply_congr R he _ e.isProperMap]
    have hid : TopCat.ofHom (e : C(A', B')) ≫ TopCat.ofHom (e.symm : C(B', A')) =
        𝟙 A' :=
      TopCat.ext fun x ↦ e.symm_apply_apply x
    rw [pushforward_comp_apply R (TopCat.ofHom (e : C(A', B'))) (TopCat.ofHom (e.symm : C(B', A')))
        e.isProperMap e.symm.isProperMap (by rw [hid]; exact isProperMap_id),
      pushforward_id_apply' R _ _ hid]
    exact pushforward_inclHom_restrict_of_eq_top R htop hp' j b
  rw [← key a, ← key a', h]

end clopenPiece

section fibrePiece

open AlgebraicGeometry MMP.UnderlyingSpace

variable {R : Type} [CommRing R] {T : Scheme.{0}} [T.Over (Spec (.of ℂ))]
  [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))] {V : Scheme.{0}} [V.Over (Spec (.of ℂ))]
  [IsComplexScheme V]
  {f : V ⟶ T} [f.IsOver (Spec (.of ℂ))] {X : TopCat.{0}}
  {W : TopologicalSpace.Opens (TopCat.of (UnderlyingSpace ℂ T))}

/-- The complex points of the fibre `V_t`, read in `X` through a product structure
`ψ : X × W ≃ₜ f⁻¹(W)`. -/
noncomputable def fibrePointsTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) :
    TopCat.of (UnderlyingSpace ℂ (ParameterPoint.fibre f t)) ⟶ X :=
  ParameterPoint.fibreComplexPointsHom f t ≫ fibreTransportHom ψ hψ ht

/-- The map `fibrePointsTransportHom ψ hψ t ht` is a closed embedding. -/
theorem isClosedEmbedding_fibrePointsTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) :
    Topology.IsClosedEmbedding (fibrePointsTransportHom ψ hψ t ht) :=
  (fibreHomeomorphOfProd ψ hψ ht).isClosedEmbedding.comp
    (Topology.IsClosedEmbedding.of_comp (f := ParameterPoint.fibreComplexPointsHom f t)
      Topology.IsEmbedding.subtypeVal
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (ParameterPoint.fibreι f t)))

/-- The map `fibrePointsTransportHom ψ hψ t ht` is surjective. -/
theorem surjective_fibrePointsTransportHom
    (ψ : X × W ≃ₜ preimageOpens (TopCat.ofHom (map (K := ℂ) f)) W)
    (hψ : ∀ p, map (K := ℂ) f (ψ p : UnderlyingSpace ℂ V) = (p.2 : UnderlyingSpace ℂ T))
    (t : ParameterPoint T) (ht : t.complexPoint ∈ W) :
    Function.Surjective (fibrePointsTransportHom ψ hψ t ht) := by
  refine (fibreHomeomorphOfProd ψ hψ ht).surjective.comp ?_
  rintro ⟨p, hp⟩
  have hp' : p ∈ pointsOver (K := ℂ) (Set.range (ParameterPoint.fibreι f t)) := by
    change map (K := ℂ) f p ∈ ({t.complexPoint} : Set _) at hp
    rw [← Set.mem_preimage, preimage_map_singleton, ParameterPoint.complexPoint_toHom_closedPoint]
      at hp
    rw [ParameterPoint.range_fibreι]
    exact hp
  rw [← range_map_of_isClosedImmersion] at hp'
  obtain ⟨q, rfl⟩ := hp'
  exact ⟨q, rfl⟩

end fibrePiece

end MMP.Fourfold
