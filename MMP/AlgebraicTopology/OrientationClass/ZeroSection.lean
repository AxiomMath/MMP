module

public import MMP.AlgebraicTopology.OrientationClass.Submanifold
public import MMP.AlgebraicTopology.ThomClass.Natural
public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import MMP.AlgebraicTopology.OrientationClass.Independent
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Prod
/-!
# The orientation class of the zero section (Fulton, §19.1)

Let `E` be a complex vector bundle of rank `d` on a complex manifold `M`, and imbed `M` in the
total space `E` by the zero section. The identity of `E` is a tubular neighbourhood of
`0_E ⊆ E`, and the orientation class `u_{M,E} ∈ H^{2d}(E, E - 0_E)` relative to it is the Thom
class `u_E` (Fulton, §19.1; Bott–Tu, §6).

The zero section `0_E` is a subset of `E`, and the normal bundle of `0_E ⊆ E` is `E` itself,
carried to `0_E` by the homeomorphism `0_E ≅ M`, `v ↦ π v`: it is the pull-back
`π|_{0_E}^* E`. The identity tubular neighbourhood is the induced bundle map
`π|_{0_E}^* E → E`, which is a homeomorphism.

## Main definitions

* `MMP.zeroSectionProj`: the homeomorphism `0_E → M`, `v ↦ π v`, as a continuous
  map.
* `MMP.zeroSectionTubularNeighbourhood`: the identity tubular neighbourhood
  `π|_{0_E}^* E → E` of the zero section.

## Main results

* `MMP.isOrientationCompatible_zeroSectionTubularNeighbourhood`: it is compatible
  with the complex orientations, for the charts of the total space of a vector bundle on a
  charted space.
* `MMP.isOrientationClass_zeroSection_iff`: relative to the identity tubular
  neighbourhood, a class is the orientation class of the zero section exactly when it is the
  Thom class of `E`.
* `MMP.isOrientationClass_zeroSection_iff_of_isOrientationCompatible`:
  **`u_{M,E} = u_E`**, relative to every tubular neighbourhood compatible with the complex
  orientations.

## Implementation notes

`M` is any charted space modelled on a complex normed space `HB` and `E` any complex topological
vector bundle on `M`; the total space carries Mathlib's charts `FiberBundle.chartedSpace`
(modelled on `ModelProd HB F`, which is `HB × F`). Fulton's setting is `M` a complex manifold and
`E` holomorphic.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [R. Bott, L. Tu, *Differential forms in algebraic topology*][botttu1982], §6.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Topology

universe u

namespace MMP

variable {B : Type u} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The projection `0_E → M`, `v ↦ π v`, of the zero section of a vector bundle to the base (a
continuous map, inverse to the zero section on its range; see `zeroSection_zeroSectionProj`). -/
def zeroSectionProj : C(range (zeroSection F E), B) :=
  ⟨fun y ↦ y.1.proj, (FiberBundle.continuous_proj F E).comp continuous_subtype_val⟩

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The projection `0_E → M` sends a point of the zero section to its image under `π`. -/
@[simp]
lemma zeroSectionProj_apply (y : range (zeroSection F E)) : zeroSectionProj F E y = y.1.proj :=
  rfl

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The zero section is a left inverse of the projection `0_E → M`: `0_{π y} = y` for `y ∈ 0_E`. -/
lemma zeroSection_zeroSectionProj (y : range (zeroSection F E)) :
    zeroSection F E (zeroSectionProj F E y) = y.1 := by
  obtain ⟨_, b, rfl⟩ := y
  rfl

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The induced bundle map `π|_{0_E}^* E → E` is injective. -/
lemma injective_lift_zeroSectionProj :
    Function.Injective (Pullback.lift (E := E) (F := F) (zeroSectionProj F E)) := by
  rintro ⟨y, v⟩ ⟨y', v'⟩ h
  have h1 : zeroSectionProj F E y = zeroSectionProj F E y' := by
    change (Pullback.lift (E := E) (F := F) (zeroSectionProj F E) ⟨y, v⟩).proj =
      (Pullback.lift (E := E) (F := F) (zeroSectionProj F E) ⟨y', v'⟩).proj
    rw [h]
  obtain rfl : y = y' := Subtype.ext (by
    rw [← zeroSection_zeroSectionProj F E y, ← zeroSection_zeroSectionProj F E y', h1])
  change (⟨zeroSectionProj F E y, v⟩ : TotalSpace F E) = ⟨zeroSectionProj F E y, v'⟩ at h
  rw [(TotalSpace.mk_inj (F := F) (E := E)).1 h]

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E] in
/-- The induced bundle map `π|_{0_E}^* E → E` is surjective. -/
lemma surjective_lift_zeroSectionProj :
    Function.Surjective (Pullback.lift (E := E) (F := F) (zeroSectionProj F E)) := by
  rintro ⟨b, w⟩
  exact ⟨⟨⟨zeroSection F E b, b, rfl⟩, w⟩, rfl⟩

omit [FiniteDimensional ℂ F] in
/-- The induced bundle map `π|_{0_E}^* E → E` is an imbedding. -/
lemma isEmbedding_lift_zeroSectionProj :
    IsEmbedding (Pullback.lift (E := E) (F := F) (zeroSectionProj F E)) := by
  refine ⟨⟨?_⟩, injective_lift_zeroSectionProj F E⟩
  rw [Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  refine le_antisymm inf_le_right (le_inf ?_ le_rfl)
  let g : TotalSpace F E → range (zeroSection F E) :=
    fun p ↦ ⟨zeroSection F E p.proj, p.proj, rfl⟩
  have hg : Continuous g := ((Trivialization.continuous_zeroSection ℂ (F := F) (E := E)).comp
    (FiberBundle.continuous_proj F E)).subtype_mk _
  have hcomp : (TotalSpace.proj : TotalSpace F ((zeroSectionProj F E : _ → B) *ᵖ E) → _) =
      g ∘ Pullback.lift (zeroSectionProj F E) := by
    funext ⟨y, v⟩
    exact Subtype.ext (zeroSection_zeroSectionProj F E y).symm
  rw [hcomp, ← induced_compose]
  exact induced_mono (continuous_iff_le_induced.1 hg)

omit [FiniteDimensional ℂ F] in
/-- The induced bundle map `π|_{0_E}^* E ≅ E`, as a homeomorphism. -/
def zeroSectionLiftHomeomorph :
    TotalSpace F ((zeroSectionProj F E : _ → B) *ᵖ E) ≃ₜ TotalSpace F E :=
  (isEmbedding_lift_zeroSectionProj F E).toHomeomorphOfSurjective
    (surjective_lift_zeroSectionProj F E)

omit [FiniteDimensional ℂ F] in
/-- The homeomorphism `π|_{0_E}^* E ≅ E` is the induced bundle map of the pull-back. -/
@[simp]
lemma zeroSectionLiftHomeomorph_apply (v : TotalSpace F ((zeroSectionProj F E : _ → B) *ᵖ E)) :
    zeroSectionLiftHomeomorph F E v = Pullback.lift (zeroSectionProj F E) v :=
  rfl

omit [FiniteDimensional ℂ F] in
/-- The identity tubular neighbourhood `π|_{0_E}^* E → E` of the zero section `0_E ⊆ E`
(Fulton, §19.1: "the identity is a tubular neighbourhood"). -/
def zeroSectionTubularNeighbourhood :
    TubularNeighbourhood (P := TopCat.of (TotalSpace F E)) (M := range (zeroSection F E)) F
      ((zeroSectionProj F E : _ → B) *ᵖ E) where
  toFun := Pullback.lift (zeroSectionProj F E)
  isOpenEmbedding := (zeroSectionLiftHomeomorph F E).isOpenEmbedding
  map_zeroSection y := zeroSection_zeroSectionProj F E y

omit [FiniteDimensional ℂ F] in
/-- The identity tubular neighbourhood is the induced bundle map `π|_{0_E}^* E → E`. -/
@[simp]
lemma zeroSectionTubularNeighbourhood_apply
    (v : TotalSpace F ((zeroSectionProj F E : _ → B) *ᵖ E)) :
    zeroSectionTubularNeighbourhood F E v = Pullback.lift (zeroSectionProj F E) v :=
  rfl

section Thom

open ThomClass

variable (R : Type u) [CommRing R]

omit [FiniteDimensional ℂ F] in
/-- The tubular neighbourhood `π|_{0_E}^* E → E` is the induced bundle map of the pull-back. -/
lemma zeroSectionTubularNeighbourhood_toHom :
    (zeroSectionTubularNeighbourhood F E).toHom = pullbackBundleMap F E (zeroSectionProj F E) :=
  rfl

omit [FiniteDimensional ℂ F] in
/-- The map `H^j(E, E - 0_E) → H^j(N, N - 0_N)` of the identity tubular neighbourhood is the
pull-back along the bundle map `N = π|_{0_E}^* E → E`. -/
lemma thomPullback_zeroSectionTubularNeighbourhood (j : ℤ) :
    (zeroSectionTubularNeighbourhood F E).thomPullback R j =
      relativeSingularCohomology.map R (ModuleCat.of R R)
        (pullbackBundleMap F E (zeroSectionProj F E))
        (pullbackBundleMap_compl_zeroSection F E (zeroSectionProj F E)) j := by
  dsimp only [TubularNeighbourhood.thomPullback, cohomologyWithSupports.pullback,
    cohomologyWithSupports.forget]
  exact (relativeSingularCohomology.map_comp R (ModuleCat.of R R) (𝟙 _)
    (pullbackBundleMap F E (zeroSectionProj F E)) _ _ j).symm

omit [FiniteDimensional ℂ F] in
/-- The inverse `E → π|_{0_E}^* E` of the identity tubular neighbourhood. -/
def zeroSectionLiftInv :
    TopCat.of (TotalSpace F E) ⟶ TopCat.of (TotalSpace F ((zeroSectionProj F E : _ → B) *ᵖ E)) :=
  TopCat.ofHom ⟨(zeroSectionLiftHomeomorph F E).symm,
    (zeroSectionLiftHomeomorph F E).symm.continuous⟩

omit [FiniteDimensional ℂ F] in
/-- The inverse `E → π|_{0_E}^* E` of the identity tubular neighbourhood maps `E - 0_E` into the
complement of the zero section of `π|_{0_E}^* E`. -/
lemma zeroSectionLiftInv_compl_zeroSection :
    (range (zeroSection F E))ᶜ ⊆
      zeroSectionLiftInv F E ⁻¹' (range (zeroSection F ((zeroSectionProj F E : _ → B) *ᵖ E)))ᶜ := by
  intro x hx hy
  refine hx ?_
  have h := (zeroSectionTubularNeighbourhood F E).preimage_eq_range_zeroSection
  rw [← (zeroSectionLiftHomeomorph F E).apply_symm_apply x]
  exact (h.symm ▸ hy : (zeroSectionLiftHomeomorph F E).symm x ∈
    zeroSectionTubularNeighbourhood F E ⁻¹' range (zeroSection F E))

omit [FiniteDimensional ℂ F] in
/-- The map `E → π|_{0_E}^* E` followed by the bundle map `π|_{0_E}^* E → E` is the identity of
`E`. -/
lemma zeroSectionLiftInv_comp_pullbackBundleMap :
    zeroSectionLiftInv F E ≫ pullbackBundleMap F E (zeroSectionProj F E) = 𝟙 _ :=
  TopCat.ext fun x ↦ (zeroSectionLiftHomeomorph F E).apply_symm_apply x

omit [FiniteDimensional ℂ F] in
/-- The map `H^j(E, E - 0_E) → H^j(N, N - 0_N)` of the identity tubular neighbourhood is
injective. -/
lemma injective_thomPullback_zeroSectionTubularNeighbourhood (j : ℤ) :
    Function.Injective ((zeroSectionTubularNeighbourhood F E).thomPullback R j).hom := by
  rw [thomPullback_zeroSectionTubularNeighbourhood]
  refine Function.LeftInverse.injective (g := (relativeSingularCohomology.map R (ModuleCat.of R R)
    (zeroSectionLiftInv F E) (zeroSectionLiftInv_compl_zeroSection F E) j).hom) fun u ↦ ?_
  have h := relativeSingularCohomology.map_comp R (ModuleCat.of R R) (zeroSectionLiftInv F E)
    (pullbackBundleMap F E (zeroSectionProj F E)) (zeroSectionLiftInv_compl_zeroSection F E)
    (pullbackBundleMap_compl_zeroSection F E (zeroSectionProj F E)) j
  have h3 : relativeSingularCohomology.map R (ModuleCat.of R R)
      (zeroSectionLiftInv F E ≫ pullbackBundleMap F E (zeroSectionProj F E))
      (A' := (range (zeroSection F E))ᶜ) (A := (range (zeroSection F E))ᶜ)
      (fun _ hx ↦ pullbackBundleMap_compl_zeroSection F E (zeroSectionProj F E)
        (zeroSectionLiftInv_compl_zeroSection F E hx)) j = 𝟙 _ :=
    (relativeSingularCohomology.map_congr' R (zeroSectionLiftInv_comp_pullbackBundleMap F E) _
      (fun _ hx ↦ hx) j).trans
      (relativeSingularCohomology.map_id R (ModuleCat.of R R) (TopCat.of (TotalSpace F E)) _ j)
  exact congrArg (fun φ ↦ φ.hom u) (h.symm.trans h3)

/-- The pull-back of the Thom class `u_E` along the identity tubular neighbourhood is a Thom class
of `N = π|_{0_E}^* E` (naturality of Thom classes). -/
lemma isThomClass_thomPullback_zeroSectionTubularNeighbourhood :
    IsThomClass (R := R) F ((zeroSectionProj F E : _ → B) *ᵖ E)
      (((zeroSectionTubularNeighbourhood F E).thomPullback R
        (2 * Module.finrank ℂ F : ℕ)).hom (thomClass R F E)) := by
  rw [thomPullback_zeroSectionTubularNeighbourhood]
  exact (isThomClass_thomClass F E).pullback F E (zeroSectionProj F E)

end Thom

section Orientation

variable {HB : Type*} [NormedAddCommGroup HB] [NormedSpace ℂ HB] [ChartedSpace HB B]

variable (HB) in
/-- The charts of the total space of a vector bundle on a charted space modelled on `HB`, with
model `HB × F` (Mathlib's `FiberBundle.chartedSpace`, whose model `ModelProd HB F` is `HB × F`). -/
abbrev totalSpaceChartedSpace : ChartedSpace (HB × F) (TotalSpace F E) :=
  FiberBundle.chartedSpace (HB := HB) (E := E) (F := F)

omit [FiniteDimensional ℂ F] [NormedSpace ℂ HB] in
/-- In the chart of the total space at a point `0_b` of the zero section, the fibre `E_b` is
mapped by the linear isomorphism `E_b ≅ F` of the trivialization, shifted by the chart of the
base at `b`. -/
lemma chartAt_zeroSection_mk (b : B) (w : E b) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    chartAt (HB × F) (zeroSection F E b) ⟨b, w⟩ = (chartAt HB b b,
      (trivializationAt F E b).continuousLinearEquivAt ℂ b
        (mem_baseSet_trivializationAt F E b) w) := by
  change chartAt (ModelProd HB F) (zeroSection F E b) ⟨b, w⟩ = _
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply, zeroSection_proj, Trivialization.coe_coe]
  rw [(trivializationAt F E b).apply_eq_prod_continuousLinearEquivAt ℂ b
    (mem_baseSet_trivializationAt F E b) w]
  rfl

omit [FiniteDimensional ℂ F] [NormedSpace ℂ HB] in
/-- In the chart of the total space at `0_b`, a point `0_{b'}` of the zero section over the base
set of the trivialization at `b` goes to `(e_b b', 0)`. -/
lemma chartAt_zeroSection_zeroSection (b b' : B) (hb' : b' ∈ (trivializationAt F E b).baseSet) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    chartAt (HB × F) (zeroSection F E b) (zeroSection F E b') = (chartAt HB b b', 0) := by
  change chartAt (ModelProd HB F) (zeroSection F E b) ⟨b', 0⟩ = _
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply, zeroSection_proj, Trivialization.coe_coe]
  rw [(trivializationAt F E b).apply_eq_prod_continuousLinearEquivAt ℂ b' hb' 0, map_zero]
  rfl

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)] [_root_.VectorBundle ℂ F E]
  [NormedSpace ℂ HB] in
/-- A point `0_{b'}` of the zero section lies in the source of the chart of the total space at
`0_b` exactly when `b'` lies in the base set of the trivialization at `b` and in the source of the
chart of the base at `b`. -/
lemma zeroSection_mem_chartAt_source_iff (b b' : B) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    zeroSection F E b' ∈ (chartAt (HB × F) (zeroSection F E b)).source ↔
      b' ∈ (trivializationAt F E b).baseSet ∧ b' ∈ (chartAt HB b).source := by
  change zeroSection F E b' ∈ (chartAt (ModelProd HB F) (zeroSection F E b)).source ↔ _
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
    OpenPartialHomeomorph.refl_source, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true,
    Trivialization.mem_source, zeroSection_proj]
  refine and_congr_right fun h1 ↦ ?_
  rw [Trivialization.coe_coe, Trivialization.coe_fst _ ((Trivialization.mem_source _).2 h1),
    zeroSection_proj]

omit [FiniteDimensional ℂ F] in
/-- The tangent cone of the zero section `0_E ⊆ E` at `0_b`, in the chart at `0_b`, is
`HB × 0`. -/
lemma tangentConeAt_chartAt_zeroSection (b : B) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    tangentConeAt ℝ (chartAt (HB × F) (zeroSection F E b) ''
        (range (zeroSection F E) ∩ (chartAt (HB × F) (zeroSection F E b)).source))
      (chartAt (HB × F) (zeroSection F E b) (zeroSection F E b)) =
      (LinearMap.range (LinearMap.inl ℂ HB F) : Set (HB × F)) := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
  have hb := mem_baseSet_trivializationAt F E b
  rw [chartAt_zeroSection_zeroSection F E b b hb]
  have hset : ((LinearMap.range (LinearMap.inl ℂ HB F) : Submodule ℂ (HB × F)) : Set (HB × F)) =
      ((LinearMap.range (LinearMap.inl ℝ HB F) : Submodule ℝ (HB × F)) : Set (HB × F)) := by
    ext p
    simp
  rw [hset]
  apply subset_antisymm
  · refine tangentConeAt_subset_of_subset_submodule _ ?_ ?_ ⟨_, rfl⟩
    · rw [LinearMap.range_inl]
      exact isClosed_eq continuous_snd continuous_const
    · rintro _ ⟨_, ⟨⟨b', rfl⟩, hs⟩, rfl⟩
      rw [zeroSection_mem_chartAt_source_iff] at hs
      rw [chartAt_zeroSection_zeroSection F E b b' hs.1]
      exact ⟨_, rfl⟩
  · set S0 := chartAt HB b '' ((trivializationAt F E b).baseSet ∩ (chartAt HB b).source)
    have hS0 : S0 ∈ 𝓝 (chartAt HB b b) :=
      (chartAt HB b).image_mem_nhds (mem_chart_source HB b)
        (Filter.inter_mem ((trivializationAt F E b).open_baseSet.mem_nhds hb)
          ((chartAt HB b).open_source.mem_nhds (mem_chart_source HB b)))
    have hsub : S0 ×ˢ ({0} : Set F) ⊆ chartAt (HB × F) (zeroSection F E b) ''
        (range (zeroSection F E) ∩ (chartAt (HB × F) (zeroSection F E b)).source) := by
      rintro ⟨_, q⟩ ⟨⟨b', hb', rfl⟩, hq⟩
      rw [mem_singleton_iff] at hq
      subst hq
      exact ⟨zeroSection F E b', ⟨⟨b', rfl⟩, (zeroSection_mem_chartAt_source_iff F E b b').2 hb'⟩,
        chartAt_zeroSection_zeroSection F E b b' hb'.1⟩
    rintro _ ⟨p, rfl⟩
    refine tangentConeAt_mono hsub
      (subset_tangentConeAt_prod_left (subset_closure (mem_singleton (0 : F))) ?_)
    exact ⟨p, by rw [tangentConeAt_of_mem_nhds hS0]; trivial, rfl⟩

/-- The identity tubular neighbourhood of the zero section is compatible with the complex
orientations: along the fibre `E_b` its derivative in the chart at `0_b` is the complex linear
isomorphism `E_b ≅ F` of the trivialization, followed by the inclusion `F ⊆ HB × F`. -/
theorem isOrientationCompatible_zeroSectionTubularNeighbourhood :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    (zeroSectionTubularNeighbourhood F E).IsOrientationCompatible (E := HB × F) := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
  rintro ⟨_, b, rfl⟩
  set T := (trivializationAt F E b).continuousLinearEquivAt ℂ b
    (mem_baseSet_trivializationAt F E b)
  set e₀ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  set L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] HB × F :=
    ((ContinuousLinearMap.inr ℂ HB F).comp
      (e₀ : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] F)).restrictScalars ℝ
  have hL : ∀ v, L v = (0, e₀ v) := fun v ↦ rfl
  refine ⟨e₀.trans T.symm, L, ?_, ?_, LinearMap.range (LinearMap.inl ℂ HB F),
    tangentConeAt_chartAt_zeroSection F E b, ?_, ?_⟩
  · refine (L.hasFDerivAt.const_add (chartAt HB b b, (0 : F))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v ↦ ?_)
    change chartAt (HB × F) (zeroSection F E b) ⟨b, T.symm (e₀ v)⟩ = (chartAt HB b b, 0) + L v
    rw [hL, chartAt_zeroSection_mk, ContinuousLinearEquiv.apply_symm_apply]
    simp
  · intro v w h
    rw [hL, hL] at h
    exact e₀.injective (Prod.ext_iff.1 h).2
  · have h1 : LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] HB × F) =
        LinearMap.range (LinearMap.inr ℝ HB F) := by
      ext x
      simp only [LinearMap.mem_range]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨e₀ v, hv ▸ (hL v).symm⟩
      · rintro ⟨q, hq⟩
        exact ⟨e₀.symm q, (hL _).trans (by simp [← hq])⟩
    have h2 : (LinearMap.range (LinearMap.inl ℂ HB F)).restrictScalars ℝ =
        LinearMap.range (LinearMap.inl ℝ HB F) := by
      ext ⟨p, q⟩
      simp
    rw [h1, h2]
    exact LinearMap.isCompl_range_inl_inr.symm
  · intro c v
    rw [hL, hL]
    simp

open ThomClass in
/-- **The orientation class of the zero section is the Thom class** (Fulton, §19.1): for a complex
vector bundle `E` of rank `d` on a space `M` with charts modelled on a complex normed space `HB`,
imbedded in `E` by the zero section, the
orientation class `u_{M,E} ∈ H^{2d}(E, E - 0_E)` relative to the identity tubular neighbourhood
`π|_{0_E}^* E ≅ E` is the Thom class `u_E`: a class is the orientation class exactly when it is
`u_E`. The form for every compatible tubular neighbourhood is
`MMP.isOrientationClass_zeroSection_iff_of_isOrientationCompatible`. -/
theorem isOrientationClass_zeroSection_iff (R : Type u) [CommRing R]
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    IsOrientationClass (HB × F) R (zeroSectionTubularNeighbourhood F E) u ↔
      u = thomClass R F E := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
  constructor
  · rintro ⟨-, hu⟩
    refine injective_thomPullback_zeroSectionTubularNeighbourhood F E R _ ?_
    exact (existsUnique_isThomClass (R := R) F ((zeroSectionProj F E : _ → B) *ᵖ E)).unique hu
      (isThomClass_thomPullback_zeroSectionTubularNeighbourhood F E R)
  · rintro rfl
    exact ⟨isOrientationCompatible_zeroSectionTubularNeighbourhood F E,
      isThomClass_thomPullback_zeroSectionTubularNeighbourhood F E R⟩

open ThomClass in
/-- The Thom class `u_E` is the orientation class of the zero section of `E`, relative to the
identity tubular neighbourhood. -/
theorem isOrientationClass_zeroSection_thomClass (R : Type u) [CommRing R] :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    IsOrientationClass (HB × F) R (zeroSectionTubularNeighbourhood F E) (thomClass R F E) :=
  (isOrientationClass_zeroSection_iff F E R _).2 rfl

open ThomClass in
/-- **The orientation class of the zero section is the Thom class** (Fulton, §19.1;
Bott–Tu, §6): for a complex vector bundle `E` of rank `d` on a space `M` with charts modelled on a
finite-dimensional complex space `HB`, imbedded in `E` by the zero section, and for every tubular
neighbourhood `φ : N → E` of `0_E` compatible with the complex orientations, the orientation
class `u_{M,E} ∈ H^{2d}(E, E - 0_E)` relative to `φ` is the Thom class `u_E`: a class is the
orientation class exactly when it is `u_E`. (The orientation class does not depend on `φ`,
`MMP.isOrientationClass_iff_of_isOrientationCompatible`.) -/
theorem isOrientationClass_zeroSection_iff_of_isOrientationCompatible [FiniteDimensional ℂ HB]
    (R : Type u) [CommRing R] {N : range (zeroSection F E) → Type u} [∀ x, AddCommGroup (N x)]
    [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)] [TopologicalSpace (TotalSpace F N)]
    [FiberBundle F N] [_root_.VectorBundle ℂ F N]
    (φ : TubularNeighbourhood (P := TopCat.of (TotalSpace F E)) F N)
    (hφ : letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
      φ.IsOrientationCompatible (E := HB × F))
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
    IsOrientationClass (HB × F) R φ u ↔ u = thomClass R F E := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := E)
  exact (isOrientationClass_iff_of_isOrientationCompatible R φ
    (zeroSectionTubularNeighbourhood F E) hφ
    (isOrientationCompatible_zeroSectionTubularNeighbourhood F E) u).trans
    (isOrientationClass_zeroSection_iff F E R u)

end Orientation

end MMP
