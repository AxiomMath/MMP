module

public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicTopology.BorelMoore.ExteriorProductRestriction

/-!
# Generalities for the Thom class in a chart (Fulton, §19.1)

Bundle-agnostic lemmas used to compute Thom classes of vector bundles in charts:
functoriality of `relativeSingularCohomology.map` (`map_eq_map_of_hom_eq`, `map_hom_comp_apply`,
`map_map_of_comp_eq_id`), the degree of `z ↦ z ^ m` (`map_eq_smul_of_eq_pow`), and the
behaviour of local orientation classes under linear isomorphisms
(`IsLocalOrientationClass.map_linearEquiv`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Finsupp
open MMP.UnderlyingSpace

namespace MMP

open ThomClass SingularChain SingularCochain FundamentalClass

namespace relativeSingularCohomology

variable (R : Type) [CommRing R]

/-- `relativeSingularCohomology.map` depends only on the map. -/
lemma map_eq_map_of_hom_eq {Y' Y : TopCat.{0}} {f g : Y' ⟶ Y} (hfg : f = g) {A' : Set Y'}
    {A : Set Y} (hf : A' ⊆ f ⁻¹' A) (hg : A' ⊆ g ⁻¹' A) (j : ℤ) :
    map R (ModuleCat.of R R) f hf j = map R (ModuleCat.of R R) g hg j := by
  subst hfg
  rfl

/-- `relativeSingularCohomology.map` of a composite, applied to a class. -/
lemma map_hom_comp_apply {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y) {A'' : Set Y''}
    {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (hgf : A'' ⊆ (g ≫ f) ⁻¹' A)
    (j : ℤ) (u : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (map R (ModuleCat.of R R) (g ≫ f) hgf j).hom u =
      (map R (ModuleCat.of R R) g hg j).hom ((map R (ModuleCat.of R R) f hf j).hom u) := by
  rw [map_comp R (ModuleCat.of R R) g f hg hf j]
  rfl

/-- A map with a section on cohomology: if `g ≫ f = 𝟙`, then `g^* f^* = id`. -/
lemma map_map_of_comp_eq_id {Y' Y : TopCat.{0}} (g : Y ⟶ Y') (f : Y' ⟶ Y) (hgf : g ≫ f = 𝟙 Y)
    {A' : Set Y'} {A : Set Y} (hg : A ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (j : ℤ)
    (u : relativeSingularCohomology R (ModuleCat.of R R) Y A j) :
    (map R (ModuleCat.of R R) g hg j).hom ((map R (ModuleCat.of R R) f hf j).hom u) = u := by
  refine (map_hom_comp_apply R g f hg hf (fun (y : Y) (hy : y ∈ A) ↦ hf (hg hy)) j u).symm.trans ?_
  refine (congrArg (fun φ ↦ ModuleCat.Hom.hom φ u)
    (map_eq_map_of_hom_eq R hgf (fun (y : Y) (hy : y ∈ A) ↦ hf (hg hy))
      (fun (y : Y) (hy : y ∈ A) ↦ hy) j)).trans ?_
  exact congrArg (fun φ ↦ ModuleCat.Hom.hom φ u) (map_id R (ModuleCat.of R R) Y A j)

/-- **The degree of `z ↦ z ^ m`, pulled back**: if `h = g ^ m` for continuous maps
`g, h : Y → ℂ`, then `h^* u = m · g^* u` for every `u ∈ H²(ℂ, ℂ - 0)`, as classes in
`H²(Y, A)` for any `A ⊆ g⁻¹(ℂ - 0)` (`A ⊆ h⁻¹(ℂ - 0)` follows). -/
theorem map_eq_smul_of_eq_pow {Y : TopCat.{0}} (g h : Y ⟶ TopCat.of ℂ) (m : ℕ)
    (hgh : ∀ y, h y = g y ^ m) {A : Set Y} (hg : A ⊆ g ⁻¹' ({0}ᶜ : Set ℂ))
    (hh : A ⊆ h ⁻¹' ({0}ᶜ : Set ℂ))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) ({0} : Set ℂ) (2 : ℕ)) :
    (map R (ModuleCat.of R R) h hh (2 : ℕ)).hom u =
      (m : R) • (map R (ModuleCat.of R R) g hg (2 : ℕ)).hom u := by
  have e : h = g ≫ powMapHom m := by
    ext y
    exact hgh y
  have hgm : A ⊆ (g ≫ powMapHom m) ⁻¹' ({0}ᶜ : Set ℂ) :=
    fun (y : Y) (hy : y ∈ A) ↦ compl_zero_subset_preimage_powMapHom m (hg hy)
  refine (congrArg (fun φ ↦ ModuleCat.Hom.hom φ u)
    (map_eq_map_of_hom_eq R e hh hgm (2 : ℕ))).trans ?_
  refine (map_hom_comp_apply R g (powMapHom m) hg (compl_zero_subset_preimage_powMapHom m) hgm
    (2 : ℕ) u).trans ?_
  rw [map_powMapHom, map_smul]

end relativeSingularCohomology

/-! ### Local orientation classes of complex vector spaces -/

section localOrientation

variable {R : Type} [CommRing R] {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- A continuous linear equivalence `L : E ≃ H` maps the complement of `0` into the complement
of `0`. -/
lemma compl_zero_subset_preimage_ofHom_linearEquiv (L : E ≃L[ℝ] H) :
    ({0}ᶜ : Set (TopCat.of E)) ⊆
      (TopCat.ofHom (L : C(E, H)) : TopCat.of E ⟶ TopCat.of H) ⁻¹' ({0}ᶜ : Set (TopCat.of H)) :=
  fun _ hx h ↦ hx (L.map_eq_zero_iff.1 h)

/-- **Local orientation classes pull back along orientation-preserving linear isomorphisms**: if
`L : E ≅ H` carries the basis `b_E` to a basis of the orientation of `b_H`, then `L^*` carries the
local orientation class of `H` at `0` to that of `E`. -/
theorem IsLocalOrientationClass.map_linearEquiv {n : ℕ} {bE : Module.Basis (Fin n) ℝ E}
    {bH : Module.Basis (Fin n) ℝ H} (L : E ≃L[ℝ] H)
    (hL : 0 < bH.det ((L : E →ₗ[ℝ] H) ∘ bE))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of H) {0} n}
    (hu : IsLocalOrientationClass R bH (0 : TopCat.of H) u) :
    IsLocalOrientationClass R bE (0 : TopCat.of E)
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom (L : C(E, H)))
        (compl_zero_subset_preimage_ofHom_linearEquiv L) n).hom u) := by
  obtain ⟨α, hα, hc, hrep⟩ := hu
  set f : TopCat.of E ⟶ TopCat.of H := TopCat.ofHom (L : C(E, H))
  have hα' := cochainPullback_mem_relCocycles f (compl_zero_subset_preimage_ofHom_linearEquiv L) hα
  refine ⟨cochainPullback R f n α, hα', ⟨hα', fun e he hy v hv hvt ↦ ?_⟩, ?_⟩
  · rw [chartedSpaceSelf_atlas] at he
    subst he
    have hvt' : range (affineSimplex (fun k ↦ L (v k))) ⊆
        (chartAt H (0 : TopCat.of H)).target := by
      rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
      exact subset_univ _
    have hcomp : f.hom.comp (chartSimplexOf (OpenPartialHomeomorph.refl E) v hvt) =
        chartSimplexOf (chartAt H (0 : TopCat.of H)) (fun k ↦ L (v k)) hvt' := by
      ext1 t
      rw [chartSimplexOf_apply, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
        OpenPartialHomeomorph.refl_apply, id_eq]
      simp only [ContinuousMap.comp_apply, chartSimplexOf_apply, OpenPartialHomeomorph.refl_symm,
        OpenPartialHomeomorph.refl_apply, id_eq, affineSimplex_apply]
      change L (∑ k, (t : Fin (n + 1) → ℝ) k • v k) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ L.map_smul _ _
    have hv' := hv.map_linearMap (L : E →ₗ[ℝ] H) hL
    have key := hc.2 (chartAt H (0 : TopCat.of H)) (chart_mem_atlas _ _) (mem_chart_source _ _)
      (fun k ↦ L (v k)) (by simpa [chartAt_self_eq, Function.comp_def] using hv') hvt'
    rw [← hcomp] at key
    refine Eq.trans ?_ key
    simp only [SingularCochain.eval, linearCombination_single, one_smul]
    rfl
  · rw [relativeSingularCohomologyEquiv_map, hrep, relCohomologyMap_mk]

/-- The basis `e₁, i e₁` of `ℂ¹`, carried to `ℂ` by `w ↦ w 0`, is the basis `1, i`. -/
lemma complexOrientationBasis_one_map :
    (complexOrientationBasis 1).map
      ((LinearEquiv.funUnique (Fin 1) ℂ ℂ).restrictScalars ℝ) = Complex.basisOneI := by
  refine Module.Basis.eq_of_apply_eq fun b ↦ ?_
  have hb : b = finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), b)) := by
    fin_cases b <;> rfl
  rw [Module.Basis.map_apply]
  conv_lhs => rw [hb, complexOrientationBasis_apply]
  simp

end localOrientation

end MMP
