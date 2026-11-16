module

public import MMP.AlgebraicGeometry.CycleMap.TopClassComponentBasis
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.CycleClassPushforwardOrientation

/-!
# The cycle class of a subvariety read in a holomorphic chart (Fulton, §19.1)

Let `i : V → D` be a closed immersion of a complex variety `V` of dimension `k` into a complex
scheme `D`, `c = cl(V)` and `W ⊆ D(ℂ)` an open set contained in `i(V_reg(ℂ))`. Then `i`
identifies the open subset `i⁻¹(W)` of the complex manifold `V_reg(ℂ)` with `W`. If
`φ : W ≅ B` is a homeomorphism onto a connected oriented complex manifold `B` of dimension `k`
which is holomorphic in charts, with invertible complex derivative (that is, `φ ∘ i` is a
biholomorphism of `i⁻¹(W)` onto `B`), then `φ_* ((i_* c)|_W) = μ_B`: a biholomorphism preserves
the complex orientations, so it carries the fundamental class of `i⁻¹(W)` (the restriction of
`cl(V)`) to a fundamental class of `B`, which is unique as `B` is connected.

This is the cycle side of Fulton's proof of Lemma 19.1.3, read in a product chart.

## Main definitions

* `MMP.UnderlyingSpace.regularPreimageHomeomorph`: the homeomorphism
  `i⁻¹(W) ∩ V_reg(ℂ) ≃ₜ W` for an open `W ⊆ i(V_reg(ℂ))`.

## Main results

* `MMP.UnderlyingSpace.isOrientationPreserving_regularPreimageHomeomorph_trans`:
  the composite `i⁻¹(W) ≅ W ≅ B` is orientation preserving when `φ ∘ i` is holomorphic in charts
  with injective derivative.
* `MMP.IsVarietyFundamentalClass.pushforward_restrict_pushforward_eq_of_hasFDerivAt`:
  `φ_* ((i_* cl(V))|_W) = μ_B`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP.Intersection.Scheme (dimension)

namespace UnderlyingSpace

open MMP.UnderlyingSpace

variable {D V : Scheme.{0}} [D.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))]
  (i : V ⟶ D) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]

section Homeomorph

variable [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]

/-- For a closed immersion `i : V → D` over `ℂ` and an open `W ⊆ D(ℂ)` contained in
`i(V_reg(ℂ))`, the map `i` identifies the open subset `i⁻¹(W) ∩ V_reg(ℂ)` of `V_reg(ℂ)` with
`W`. -/
def _root_.MMP.UnderlyingSpace.regularPreimageHomeomorph (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V) :
    regularOpensInter (Opens.comap (map (K := ℂ) i) W) ≃ₜ W :=
  have hf : IsClosedEmbedding (map (K := ℂ) i) := isClosedEmbedding_map_of_isClosedImmersion i
  Equiv.toHomeomorphOfIsInducing (Equiv.ofBijective
    (fun x : regularOpensInter (Opens.comap (map (K := ℂ) i) W) ↦ (⟨mapFun i x.1.1, x.2⟩ : W))
    ⟨fun x y hxy ↦ Subtype.ext (Subtype.ext (hf.injective (congrArg Subtype.val hxy :))),
      fun p ↦ by
        obtain ⟨q, hq, hqp⟩ := hW p.2
        exact ⟨⟨⟨q, hq⟩, show mapFun i q ∈ W from hqp ▸ p.2⟩, Subtype.ext hqp⟩⟩)
    (by
      rw [← IsInducing.subtypeVal.of_comp_iff]
      exact hf.isInducing.comp (IsInducing.subtypeVal.comp IsInducing.subtypeVal))

/-- The point of `W` that `regularPreimageHomeomorph i W hW` assigns to `x` is `i(x)`. -/
@[simp]
lemma _root_.MMP.UnderlyingSpace.coe_regularPreimageHomeomorph_apply
    (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    (x : regularOpensInter (Opens.comap (map (K := ℂ) i) W)) :
    (regularPreimageHomeomorph i W hW x : UnderlyingSpace ℂ D) = mapFun i x.1.1 :=
  rfl

/-- `regularPreimageHomeomorph i W hW` sends `x` to `i(x)`, regarded as a point of `W`. -/
lemma _root_.MMP.UnderlyingSpace.regularPreimageHomeomorph_apply (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    (x : regularOpensInter (Opens.comap (map (K := ℂ) i) W)) :
    regularPreimageHomeomorph i W hW x = ⟨mapFun i x.1.1, x.2⟩ :=
  rfl

end Homeomorph

variable [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]

open Classical in
/-- **The identification `i⁻¹(W) ∩ V_reg(ℂ) ≅ W ≅ B` is orientation preserving** when `φ ∘ i`
is holomorphic in charts with injective derivative. Let `φ : W ≃ₜ B` be a homeomorphism onto a
manifold modelled on `ℂᵏ` such that, for every algebraic chart `e` of `V(ℂ)` with values in `ℂᵏ`
and every chart `e'` of `B`, the chart expression `e' ∘ φ ∘ i ∘ e⁻¹` (extended by `0` where
`i ∘ e⁻¹` leaves `W`) has an injective complex derivative at every regular point of `e`'s
source mapped by `i` into `W` and by `φ ∘ i` into the source of `e'`. Then the composite
homeomorphism is orientation preserving for the complex orientations. -/
theorem _root_.MMP.UnderlyingSpace.isOrientationPreserving_regularPreimageHomeomorph_trans {k : ℕ}
    (hk : (k : WithBot ℕ∞) = dimension V) (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    {B : Type} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℂ (Fin k)) B] (φ : W ≃ₜ B)
    (hφ : ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ V) (EuclideanSpace ℂ (Fin k)),
      IsAlgebraicChart e → ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ q ∈ e.source,
      q ∈ regularPart ℂ V → ∀ hq : mapFun i q ∈ W, φ ⟨mapFun i q, hq⟩ ∈ e'.source →
      ∃ L : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k), Function.Injective L ∧
        HasFDerivAt (fun y ↦ if h : mapFun i (e.symm y) ∈ W then e' (φ ⟨_, h⟩) else 0) L
          (e q)) :
    letI := regularChartedSpace (𝕜 := ℂ) hk
    IsOrientationPreserving (euclideanComplexOrientationBasis k)
      (euclideanComplexOrientationBasis k) ((regularPreimageHomeomorph i W hW).trans φ) := by
  let := regularChartedSpace (𝕜 := ℂ) hk
  rw [euclideanComplexOrientationBasis_eq_complexRealBasis]
  refine isOrientationPreserving_of_hasFDerivAt _ _ _ fun eN heN e' he' x hx hx' ↦ ?_
  obtain ⟨_, ⟨x₀, rfl⟩, heN⟩ := heN
  rw [mem_singleton_iff] at heN
  subst heN
  set a := (exists_isAlgebraicChart_of_dimension_eq hk x₀.1.1
    (mem_regularOpens.1 x₀.1.2)).choose
  have ha : IsAlgebraicChart a := (exists_isAlgebraicChart_of_dimension_eq hk x₀.1.1
    (mem_regularOpens.1 x₀.1.2)).choose_spec.2
  set eN := (chartAt (EuclideanSpace ℂ (Fin k)) x₀.1).subtypeRestr ⟨x₀⟩
  have hsrc : ∀ z, z ∈ eN.source ↔ z.1.1 ∈ a.source := fun z ↦ by
    rw [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    change z.1 ∈ (a.subtypeRestr ⟨x₀.1⟩).source ↔ _
    rw [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
  have hcoe : ∀ z, eN z = a z.1.1 := fun z ↦ rfl
  have hxa : x.1.1 ∈ a.source := (hsrc x).1 hx
  obtain ⟨L, hLi, hL⟩ := hφ a ha e' he' x.1.1 hxa x.1.2 x.2 hx'
  refine ⟨L.restrictScalars ℝ, ?_, ?_⟩
  swap
  · exact complexRealBasis_det_pos
      (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)))
      (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)))
      (L := (L : EuclideanSpace ℂ (Fin k) →ₗ[ℂ] EuclideanSpace ℂ (Fin k))) hLi
  have hL' := hL.restrictScalars ℝ
  rw [← hcoe x] at hL'
  refine hL'.congr_of_eventuallyEq ?_
  filter_upwards [eN.open_target.mem_nhds (eN.map_source hx)] with y hy
  have hz : (eN.symm y).1.1 = a.symm y := by
    have h1 := eN.right_inv hy
    rw [hcoe] at h1
    rw [← h1, a.left_inv ((hsrc _).1 (eN.map_target hy)), h1]
  have hW' : mapFun i (a.symm y) ∈ W := hz ▸ (eN.symm y).2
  rw [dite_eq_left hW', Homeomorph.trans_apply, regularPreimageHomeomorph_apply]
  exact congrArg (fun z ↦ e' (φ z)) (Subtype.ext (congrArg (mapFun i) hz))

end UnderlyingSpace

section CycleClass

open borelMooreHomology

variable (R : Type) [CommRing R] {D V : Scheme.{0}} [D.Over (Spec (.of ℂ))] [IsComplexScheme D]
  [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V] (i : V ⟶ D) [IsClosedImmersion i]
  [i.IsOver (Spec (.of ℂ))]

open Classical in
/-- **The cycle class of a subvariety read in a holomorphic chart** (Fulton, §19.1). Let
`i : V → D` be a closed immersion of a complex variety `V` of dimension `k`, `c = cl(V)`, and
`W ⊆ D(ℂ)` an open set contained in `i(V_reg(ℂ))`. Let `φ : W ≃ₜ B` be a homeomorphism onto a
connected Hausdorff manifold modelled on `ℂᵏ` with fundamental class `μ_B` for the complex
orientation, such that `φ ∘ i` is holomorphic with injective derivative in the algebraic charts
of `V` and the charts of `B`. Then `φ_* ((i_* c)|_W) = μ_B`. -/
theorem _root_.MMP.IsVarietyFundamentalClass.pushforward_restrict_pushforward_eq_of_hasFDerivAt
    {k : ℕ} {hk : (k : WithBot ℕ∞) = dimension V}
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ V)) (2 * k : ℕ)}
    (hc : IsVarietyFundamentalClass R hk c) (W : Opens (UnderlyingSpace ℂ D))
    (hW : (W : Set (UnderlyingSpace ℂ D)) ⊆ mapFun (K := ℂ) i '' regularPart ℂ V)
    {B : Type} [TopologicalSpace B] [T2Space B] [ConnectedSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB) (φ : W ≃ₜ B)
    (hφ : ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ V) (EuclideanSpace ℂ (Fin k)),
      IsAlgebraicChart e → ∀ e' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ q ∈ e.source,
      q ∈ regularPart ℂ V → ∀ hq : mapFun i q ∈ W, φ ⟨mapFun i q, hq⟩ ∈ e'.source →
      ∃ L : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k), Function.Injective L ∧
        HasFDerivAt (fun y ↦ if h : mapFun i (e.symm y) ∈ W then e' (φ ⟨_, h⟩) else 0) L
          (e q)) :
    pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(W, B))) φ.isProperMap (2 * k : ℕ)
      (restrict R (ModuleCat.of R R) (Y := TopCat.of (UnderlyingSpace ℂ D)) W (2 * k : ℕ)
        (pushforward R (ModuleCat.of R R) (TopCat.ofHom (map (K := ℂ) i))
          (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap (2 * k : ℕ) c)) = μB := by
  let := regularChartedSpace (𝕜 := ℂ) hk
  set Φ := (regularPreimageHomeomorph i W hW).trans φ
  have hμN := hc.isFundamentalClass_restrict (Opens.comap (map (K := ℂ) i) W)
  have h1 := hμN.pushforward_homeomorph R Φ
    (isOrientationPreserving_regularPreimageHomeomorph_trans i hk W hW φ hφ)
  have : SecondCountableTopology B := Φ.symm.isEmbedding.secondCountableTopology
  rw [← hμB.eq_of_connectedSpace' h1]
  set f : TopCat.of (UnderlyingSpace ℂ V) ⟶ TopCat.of (UnderlyingSpace ℂ D) :=
    TopCat.ofHom (map (K := ℂ) i)
  have hf : IsClosedEmbedding f := isClosedEmbedding_map_of_isClosedImmersion i
  have hreg : Opens.comap f.hom W ≤
      (regularOpens ℂ V : Opens (TopCat.of (UnderlyingSpace ℂ V))) := by
    intro q hq
    obtain ⟨q', hq', hqq'⟩ := hW hq
    rw [hf.injective hqq'] at hq'
    exact hq'
  have hp₁ := isProperMap_subOpensInv hreg
  have hp₂ := borelMooreHomology.isProperMap_restrictPreimage f W hf.isProperMap
  have hp₁₂ : IsProperMap (subOpensInv _ hreg ≫ borelMooreHomology.restrictPreimage f W) :=
    hp₂.comp hp₁
  have hp₃ : IsProperMap ((subOpensInv _ hreg ≫ borelMooreHomology.restrictPreimage f W) ≫
      TopCat.ofHom (φ : C(W, B))) :=
    φ.isProperMap.comp hp₁₂
  rw [restrict_pushforward_apply, restrict_eq_pushforward_subOpensInv hreg,
    pushforward_comp_apply R _ _ hp₁ hp₂ hp₁₂,
    pushforward_comp_apply R _ _ hp₁₂ φ.isProperMap hp₃]
  exact pushforward_apply_congr R (ConcreteCategory.hom_ext _ _ fun x ↦ rfl) _ _ _ _

end CycleClass

end MMP
