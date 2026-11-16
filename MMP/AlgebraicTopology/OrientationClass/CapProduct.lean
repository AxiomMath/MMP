module

public import MMP.AlgebraicTopology.OrientationClass.Transversal
public import MMP.AlgebraicTopology.CapProduct.ExteriorProductChains
public import MMP.AlgebraicTopology.ComplexSubmanifold
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicTopology.FundamentalClass.Product
public import MMP.AlgebraicTopology.FundamentalClass.Locality
public import MMP.AlgebraicTopology.OrientationClass.CapPoint

/-!
# The orientation class of `X × {0}` in `X × F` (Fulton, §19.1)

Let `X` be a space with charts in a finite-dimensional complex normed space `HX`, and `F` a
finite-dimensional complex normed space of dimension `r`. In `X × F`, with the product charts
(model `HX × F`), the slice `X × {0} = pr⁻¹(0)` has the tubular neighbourhood
`φ : X × {0} × F → X × F`, `((x, 0), f) ↦ (x, f)` (the trivial bundle with fibre `F`), compatible
with the complex orientations. For the local orientation class `u₀ ∈ H^{2r}(F, F - 0)` of `F`
at `0` (for its complex orientation), the pull-back `pr^* u₀ ∈ H^{2r}(X × F, X × (F - 0))` along
the second projection is the orientation class of `X × {0}`: on the fibre simplex `ψ ∘ Δ` at
`(x, 0)` (a complex frame `ψ : ℂ^r ≅ F`, an oriented simplex `Δ` around `0`) it takes the value
`α(ψ ∘ Δ) = 1`, as `ψ` preserves complex orientations.

With the uniqueness of orientation classes (`MMP.IsOrientationClass.eq`) this identifies every
orientation class of `X × {0}` with `pr^* u₀`: the Thom class of the trivial bundle `D × ℂ^d` is
`pr^* u₀`.

## Main definitions

* `MMP.prodChartedSpaceModel`: the product charts of `X × F`, with model `HX × F`.
* `MMP.sliceTubularNeighbourhood`: the tubular neighbourhood `((x, 0), f) ↦ (x, f)` of `X × {0}`
  in `X × F`.

## Main results

* `MMP.isOrientationCompatible_sliceTubularNeighbourhood`: the tubular neighbourhood of
  `X × {0}` is compatible with the complex orientations.
* `MMP.isOrientationClass_pullback_prSnd`: `pr^* u₀` is the orientation class of `X × {0}`.
* `MMP.IsOrientationClass.eq_pullback_prSnd`: every orientation class of `X × {0}` is `pr^* u₀`.
* `MMP.IsFundamentalClass.pushforward_fst_exteriorProduct`: `μ_X × [pt] = μ_X` under
  `X × pt ≅ X`.
* `MMP.IsFundamentalClass.pushforward_capProductSupportPullback_prSnd`: the local model of
  `u_{M,P} ∩ μ_P = μ_M`: `pr^* u₀ ∩ (μ_X × μ_F) = μ_X` in `H_n(X × {0}) ≅ H_n X`.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Filter Topology Finsupp

universe u

namespace MMP

open MMP

open SingularChain SingularCochain ThomClass FundamentalClass BorelMooreCross BorelMooreCap

section Slice

variable {HX : Type*} [NormedAddCommGroup HX] [NormedSpace ℂ HX] (X : TopCat.{u})
  [ChartedSpace HX X] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

variable (HX) in
/-- The product charts of `X × F` (Mathlib's `prodChartedSpace`), with model `HX × F` (the model
`ModelProd HX F` of `prodChartedSpace` is `HX × F`). -/
abbrev prodChartedSpaceModel : ChartedSpace (HX × F) (TopCat.of (X × TopCat.of F)) :=
  prodChartedSpace HX X F F

/-- The slice `X × {0} = pr⁻¹(0)` of `X × F`. -/
abbrev zeroSlice : Set (TopCat.of (X × TopCat.of F)) := prSnd X (TopCat.of F) ⁻¹' {0}

/-- The map `((x, 0), f) ↦ (x, f)` from the trivial bundle with fibre `F` on `X × {0}`. -/
def sliceMap (v : TotalSpace F (Trivial (zeroSlice X F) F)) : TopCat.of (X × TopCat.of F) :=
  ((v.proj : X × F).1, v.2)

/-- Its inverse `(x, f) ↦ ((x, 0), f)`. -/
def sliceMapInv (p : TopCat.of (X × TopCat.of F)) : TotalSpace F (Trivial (zeroSlice X F) F) :=
  ⟨⟨(p.1, 0), mem_singleton _⟩, p.2⟩

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
/-- The map `((x, 0), f) ↦ (x, f)` is continuous. -/
lemma continuous_sliceMap : Continuous (sliceMap X F) := by
  have h := (Trivial.homeomorphProd (zeroSlice X F) F).continuous
  exact ((continuous_fst.comp continuous_subtype_val).comp h.fst).prodMk h.snd

omit [NormedSpace ℂ F] [FiniteDimensional ℂ F] in
/-- The map `(x, f) ↦ ((x, 0), f)` is continuous. -/
lemma continuous_sliceMapInv : Continuous (sliceMapInv X F) := by
  have h := (Trivial.homeomorphProd (zeroSlice X F) F).symm.continuous
  refine h.comp (Continuous.prodMk ?_ continuous_snd)
  exact (continuous_fst.prodMk continuous_const).subtype_mk _

/-- `((x, 0), f) ↦ (x, f)` as a homeomorphism. -/
def sliceHomeomorph : TotalSpace F (Trivial (zeroSlice X F) F) ≃ₜ TopCat.of (X × TopCat.of F) where
  toFun := sliceMap X F
  invFun := sliceMapInv X F
  left_inv v := by
    obtain ⟨⟨⟨x, f⟩, hx⟩, w⟩ := v
    obtain rfl := mem_singleton_iff.1 hx
    rfl
  right_inv p := rfl
  continuous_toFun := continuous_sliceMap X F
  continuous_invFun := continuous_sliceMapInv X F

/-- **The tubular neighbourhood of a slice**: `((x, 0), f) ↦ (x, f)`, from the trivial bundle with
fibre `F` on `X × {0}` to `X × F`. -/
def sliceTubularNeighbourhood :
    TubularNeighbourhood (P := TopCat.of (X × TopCat.of F)) (M := zeroSlice X F) F
      (Trivial (zeroSlice X F) F) where
  toFun := sliceMap X F
  isOpenEmbedding := (sliceHomeomorph X F).isOpenEmbedding
  map_zeroSection x := by
    obtain ⟨⟨y, f⟩, hx⟩ := x
    obtain rfl := mem_singleton_iff.1 hx
    rfl

/-- The tubular neighbourhood of `X × {0}` sends `((x, 0), f)` to `(x, f)`. -/
@[simp]
lemma sliceTubularNeighbourhood_apply (v : TotalSpace F (Trivial (zeroSlice X F) F)) :
    sliceTubularNeighbourhood X F v = ((v.proj : X × F).1, v.2) :=
  rfl

end Slice

section Compatible

variable {HX : Type*} [NormedAddCommGroup HX] [NormedSpace ℂ HX] [FiniteDimensional ℂ HX]
  (X : TopCat.{u}) [ChartedSpace HX X] (F : Type u) [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- The tangent cone of `U × {0}` at `(z, 0)`, `U` open, is `HX × 0`. -/
lemma tangentConeAt_image_prodMk_zero {U : Set HX} (hU : IsOpen U) {z : HX} (hz : z ∈ U) :
    tangentConeAt ℝ ((fun w : HX ↦ (w, (0 : F))) '' U) (z, 0) =
      (LinearMap.ker (LinearMap.snd ℂ HX F) : Set (HX × F)) := by
  have : FiniteDimensional ℝ (HX × F) := FiniteDimensional.complexToReal (HX × F)
  have hinv : comap (fun w : HX ↦ (w, (0 : F))) (𝓝 (z, 0)) ⊓ 𝓟 U ≤ 𝓝 z := by
    refine inf_le_left.trans ?_
    have h1 : 𝓝 ((z, 0) : HX × F) ≤ comap Prod.fst (𝓝 z) :=
      (continuous_fst.tendsto ((z, 0) : HX × F)).le_comap
    refine (comap_mono h1).trans ?_
    rw [comap_comap]
    exact le_of_eq comap_id
  rw [tangentConeAt_image_eq_range (hU.mem_nhds hz)
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (0 : F) z))
    (f := fun w : HX ↦ (w, (0 : F))) (fun a b hab ↦ by simpa using hab) hinv]
  ext ⟨a, b⟩
  simp only [mem_range, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    _root_.zero_apply, Prod.mk.injEq, SetLike.mem_coe, LinearMap.mem_ker,
    LinearMap.snd_apply]
  constructor
  · rintro ⟨y, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨a, rfl, rfl⟩

/-- For a surjective `g`, the range of `v ↦ (0, g v)` is the second factor of `A × B`. -/
lemma range_zero_prod_eq_range_inr {E A B : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [AddCommGroup A] [Module ℝ A] [TopologicalSpace A] [AddCommGroup B]
    [Module ℝ B] [TopologicalSpace B] {g : E →L[ℝ] B} (hg : Function.Surjective g) :
    LinearMap.range ((0 : E →L[ℝ] A).prod g : E →ₗ[ℝ] A × B) =
      LinearMap.range (LinearMap.inr ℝ A B) := by
  ext ⟨p, q⟩
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
    _root_.zero_apply, LinearMap.inr_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨v, rfl, rfl⟩
    exact ⟨g v, rfl, rfl⟩
  · rintro ⟨w, rfl, rfl⟩
    obtain ⟨v, rfl⟩ := hg w
    exact ⟨v, rfl, rfl⟩

/-- **The slice tubular neighbourhood is compatible with the complex orientations**: in the
product chart at `(x, 0)`, the fibre disc `v ↦ (e x, ψ v)` has the derivative `v ↦ (0, ψ v)`,
complex linear with image `0 × F`, complementary to the tangent space `HX × 0` of `X × {0}`. -/
theorem isOrientationCompatible_sliceTubularNeighbourhood :
    letI := prodChartedSpaceModel HX X F
    (sliceTubularNeighbourhood X F).IsOrientationCompatible (E := HX × F) := by
  let := prodChartedSpaceModel HX X F
  rintro ⟨⟨a, f⟩, hx⟩
  obtain rfl := mem_singleton_iff.1 hx
  set e := chartAt HX a
  let ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hchart : ∀ p : X × F, chartAt (HX × F) ((a, 0) : X × F) p = (e p.1, p.2) := fun p ↦ by
    change chartAt (ModelProd HX F) ((a, 0) : X × F) p = _
    rw [prodChartedSpace_chartAt]
    rfl
  have hsrc : ∀ p : X × F, p ∈ (chartAt (HX × F) ((a, 0) : X × F)).source ↔ p.1 ∈ e.source :=
    fun p ↦ by
      change p ∈ (chartAt (ModelProd HX F) ((a, 0) : X × F)).source ↔ _
      rw [prodChartedSpace_chartAt]
      simp [e, chartAt_self_eq]
  let ψR : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] F :=
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] F).restrictScalars ℝ
  refine ⟨ψ, (0 : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] HX).prod ψR, ?_, ?_,
    LinearMap.ker (LinearMap.snd ℂ HX F), ?_, ?_, ?_⟩
  · exact ((hasFDerivAt_const (e a) 0).prodMk ψR.hasFDerivAt).congr_of_eventuallyEq
      (.of_forall fun _ ↦ hchart _)
  · exact fun v w hvw ↦ ψ.injective (congrArg Prod.snd hvw)
  · have himg : chartAt (HX × F) ((a, 0) : X × F) ''
        (zeroSlice X F ∩ (chartAt (HX × F) ((a, 0) : X × F)).source) =
        (fun w : HX ↦ (w, (0 : F))) '' e.target := by
      ext q
      simp only [mem_image, mem_inter_iff, hsrc]
      constructor
      · rintro ⟨p, ⟨hp0, hp⟩, rfl⟩
        have hp0' : p.2 = 0 := mem_singleton_iff.1 hp0
        refine ⟨e p.1, e.map_source hp, ?_⟩
        rw [hchart, hp0']
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(e.symm w, 0), ⟨mem_singleton _, e.map_target hw⟩, ?_⟩
        rw [hchart]
        simp [e.right_inv hw]
    rw [himg, hchart]
    exact tangentConeAt_image_prodMk_zero F e.open_target (e.map_source (mem_chart_source HX a))
  · have h2 : (LinearMap.ker (LinearMap.snd ℂ HX F)).restrictScalars ℝ =
        LinearMap.range (LinearMap.inl ℝ HX F) := by
      rw [LinearMap.range_inl]
      rfl
    rw [range_zero_prod_eq_range_inr (A := HX) ψ.surjective, h2]
    exact LinearMap.isCompl_range_inl_inr.symm
  · exact fun c v ↦ by simp [ψR, map_smul]

end Compatible

section Thom

variable {HX : Type*} [NormedAddCommGroup HX] [NormedSpace ℂ HX] [FiniteDimensional ℂ HX]
  (X : TopCat.{u}) [ChartedSpace HX X] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] (R : Type u) [CommRing R]

omit [FiniteDimensional ℂ F] in
/-- The image `ψ ∘ Δ` of an affine simplex under a complex linear isomorphism `ψ : ℂ^r ≅ F` is
the chart simplex of `F` (charted by itself) with vertices `ψ (v k)`. -/
lemma comp_affineSimplex_eq_chartSimplexOf {r n : ℕ} (ψ : (Fin r → ℂ) ≃L[ℂ] F)
    (v : Fin (n + 1) → (Fin r → ℂ))
    (hvt : range (affineSimplex (fun k ↦ ψ (v k))) ⊆ (chartAt F (0 : TopCat.of F)).target) :
    ((ψ : C(Fin r → ℂ, F)).comp (affineSimplex v) : Simplex (TopCat.of F) n) =
      chartSimplexOf (chartAt F (0 : TopCat.of F)) (fun k ↦ ψ (v k)) hvt := by
  ext1 t
  rw [chartSimplexOf_apply, chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, id_eq]
  simp only [ContinuousMap.comp_apply, affineSimplex_apply]
  change ψ (∑ k, (t : Fin (n + 1) → ℝ) k • v k) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (ψ.toLinearMap.restrictScalars ℝ).map_smul _ _

/-- **`pr^* u₀` is the orientation class of `X × {0}`** (the Thom class of the trivial bundle
`X × F`): for the local orientation class `u₀ ∈ H^{2r}(F, F - 0)` of the complex orientation of
`F`, the pull-back along `pr : X × F → F` is the orientation class of `X × {0} = pr⁻¹(0)` relative
to the slice tubular neighbourhood. -/
theorem isOrientationClass_pullback_prSnd
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
      (2 * Module.finrank ℂ F : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀) :
    letI := prodChartedSpaceModel HX X F
    IsOrientationClass (HX × F) R (sliceTubularNeighbourhood X F)
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X (TopCat.of F)) {0}
        (2 * Module.finrank ℂ F : ℕ)).hom u₀) := by
  let := prodChartedSpaceModel HX X F
  refine ⟨isOrientationCompatible_sliceTubularNeighbourhood X F, ?_⟩
  obtain ⟨α, hα, hc, hrep⟩ := hu₀
  have hsub : ((prSnd X (TopCat.of F) ⁻¹' {0})ᶜ : Set (TopCat.of (X × TopCat.of F))) ⊆
      prSnd X (TopCat.of F) ⁻¹' ({0}ᶜ : Set (TopCat.of F)) := fun _ h ↦ h
  have hα' := cochainPullback_mem_relCocycles (prSnd X (TopCat.of F)) hsub hα
  have hrep' : relativeSingularCohomologyEquiv R ((prSnd X (TopCat.of F) ⁻¹' {0})ᶜ :
      Set (TopCat.of (X × TopCat.of F))) (2 * Module.finrank ℂ F)
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X (TopCat.of F)) {0}
        (2 * Module.finrank ℂ F : ℕ)).hom u₀) =
      Submodule.Quotient.mk ⟨cochainPullback R (prSnd X (TopCat.of F))
        (2 * Module.finrank ℂ F) α, hα'⟩ := by
    refine (relativeSingularCohomologyEquiv_map (R := R) (prSnd X (TopCat.of F)) hsub
      (2 * Module.finrank ℂ F) u₀).trans ?_
    rw [hrep, relCohomologyMap_mk]
  rw [isThomClass_thomPullback_iff R _ hα' hrep']
  intro x ψ v hv
  rw [eval_cochainPullback_single]
  let ψ' : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] F := ψ
  have hvt : range (affineSimplex (fun k ↦ ψ' (v k))) ⊆ (chartAt F (0 : TopCat.of F)).target := by
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact subset_univ _
  have hcomp : (prSnd X (TopCat.of F)).hom.comp
      ((sliceTubularNeighbourhood X F).toHom.hom.comp (fibreSimplex F x ψ v)) =
      chartSimplexOf (chartAt F (0 : TopCat.of F)) (fun k ↦ ψ' (v k)) hvt :=
    comp_affineSimplex_eq_chartSimplexOf ψ' v hvt
  rw [hcomp]
  have hv' := hv.map_linearMap ((ψ' : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℂ] F).restrictScalars ℝ)
    (complexOrientationBasisOf_det_pos (L := (ψ' : _ →ₗ[ℂ] F)) ψ'.injective)
  refine hc.2 (chartAt F (0 : TopCat.of F)) (chart_mem_atlas _ _) (mem_chart_source _ _) _ ?_ hvt
  simpa [chartAt_self_eq, Function.comp_def] using hv'

/-- **Every orientation class of `X × {0}` in `X × F` is `pr^* u₀`** (the Thom class of the
trivial bundle `X × F` is `pr^* u₀`): if `u` is the orientation class of `X × {0}` relative to
some tubular neighbourhood with fibre `F` compatible with the complex orientations (for the
product charts), then `u` is the pull-back of the local orientation class `u₀` of `F` at `0`. -/
theorem IsOrientationClass.eq_pullback_prSnd
    {N : zeroSlice X F → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)]
    [∀ x, TopologicalSpace (N x)] [TopologicalSpace (TotalSpace F N)] [FiberBundle F N]
    [_root_.VectorBundle ℂ F N] {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (X × TopCat.of F))
      (zeroSlice X F) (2 * Module.finrank ℂ F : ℕ)}
    (hu : letI := prodChartedSpaceModel HX X F; IsOrientationClass (HX × F) R φ u)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
      (2 * Module.finrank ℂ F : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀) :
    u = (cohomologyWithSupports.pullback R (ModuleCat.of R R) (prSnd X (TopCat.of F)) {0}
      (2 * Module.finrank ℂ F : ℕ)).hom u₀ := by
  let := prodChartedSpaceModel HX X F
  have hM : IsClosed (zeroSlice X F) :=
    isClosed_singleton.preimage (prSnd X (TopCat.of F)).hom.continuous
  exact hu.eq R hM (isOrientationClass_pullback_prSnd X R hu₀)

end Thom

section PointFactor

/-- A one-point space, charted by `ℝ^0`. -/
abbrev uniqueChartedSpace (Z : Type*) [TopologicalSpace Z] [Unique Z] :
    ChartedSpace (Fin 0 → ℝ) Z :=
  (Homeomorph.homeomorphOfUnique Z (Fin 0 → ℝ)).toOpenPartialHomeomorph.singletonChartedSpace
    (by simp)

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H]

/-- The linear isomorphism `H ≅ H × ℝ^0`, `h ↦ (h, 0)`, onto the model of a product with a
point. -/
def prodZeroLinearEquiv : H ≃ₗ[ℝ] ModelProd H (Fin 0 → ℝ) where
  toFun h := ((h, 0) : H × (Fin 0 → ℝ))
  invFun p := (p : H × (Fin 0 → ℝ)).1
  map_add' _ _ := Prod.ext rfl (Subsingleton.elim _ _)
  map_smul' _ _ := Prod.ext rfl (Subsingleton.elim _ _)
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)

/-- The image of a basis `b` of `H` under `H ≅ H × ℝ^0` is the product of `b` with the standard
basis of `ℝ^0`, reindexed by `Fin n ⊕ Fin 0 ≃ Fin (n + 0)`. -/
lemma map_prodZeroLinearEquiv_basis {n : ℕ} (b : Module.Basis (Fin n) ℝ H) :
    b.map prodZeroLinearEquiv =
      (b.prod (Pi.basisFun ℝ (Fin 0))).reindex finSumFinEquiv := by
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply,
    show i = Fin.castAdd 0 i from rfl, finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_apply]
  exact Prod.ext rfl (Subsingleton.elim _ _)

variable (R : Type u) [CommRing R] {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace H X] (Z : Type u) [TopologicalSpace Z] [Unique Z]

/-- In a one-point space, a class that is locally the class of its `0`-simplex is a fundamental
class. -/
theorem IsLocallyClassOf.isFundamentalClass_of_unique
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) (0 : ℕ)}
    {Δ₀ : Simplex (TopCat.of Z) 0} (hc : IsLocallyClassOf R c (default : Z) Δ₀) :
    letI := uniqueChartedSpace Z
    IsFundamentalClass R (Pi.basisFun ℝ (Fin 0)) c := by
  let := uniqueChartedSpace Z
  have hsimp : ∀ Δ : Simplex (TopCat.of Z) 0, Δ = Δ₀ := fun Δ ↦
    ContinuousMap.ext fun _ ↦ Subsingleton.elim _ _
  intro e he x v hv hvt
  refine IsLocallyClassOf.restrict _ ?_
  rw [Subsingleton.elim x.1 default, hsimp (inclChainSimplex _ _)]
  exact hc

/-- **`μ_X × [pt] = μ_X`**: the product of a fundamental class `μ_X ∈ H_n X` with the class of
the point (a class of `H_0` of a one-point space `Z`, locally the class of its `0`-simplex) is
carried to `μ_X` by the projection `X × Z ≅ X`. -/
theorem IsFundamentalClass.pushforward_fst_exteriorProduct {n : ℕ} {b : Module.Basis (Fin n) ℝ H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n} (hμ : IsFundamentalClass R b μ)
    {c : borelMooreHomology R (ModuleCat.of R R) (TopCat.of Z) (0 : ℕ)}
    {Δ₀ : Simplex (TopCat.of Z) 0} (hc : IsLocallyClassOf R c (default : Z) Δ₀) :
    IsFundamentalClass R b
      (borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (ContinuousMap.fst : C(X × Z, X))) isProperMap_fst_of_compactSpace n
        (congrDegree R _ (Nat.cast_add n 0).symm
          (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of Z) n (0 : ℕ)
            (μ ⊗ₜ c)))) := by
  letI := uniqueChartedSpace Z
  intro e' he' x v hv hvt
  set z₀ : Z := default
  set eZ := chartAt (Fin 0 → ℝ) z₀
  set L : H ≃ₗ[ℝ] ModelProd H (Fin 0 → ℝ) := prodZeroLinearEquiv
  have hxz : ((x : X), z₀) ∈ (e'.prod eZ).source := by
    rw [OpenPartialHomeomorph.prod_source]
    exact ⟨x.2, mem_chart_source _ _⟩
  have hA : ∀ t, affineSimplex (fun k ↦ L (v k)) t = L (affineSimplex v t) := fun t ↦ by
    simp only [affineSimplex_apply, map_sum, map_smul]
  have hV : IsOrientedSimplexAroundZero ((b.prod (Pi.basisFun ℝ (Fin 0))).reindex finSumFinEquiv)
      (fun k ↦ L (v k) - (show ModelProd H (Fin 0 → ℝ) from (e'.prod eZ) ((x : X), z₀))) := by
    have hfun : (fun k ↦ L (v k) - (show ModelProd H (Fin 0 → ℝ) from (e'.prod eZ) ((x : X), z₀))) =
        ⇑L ∘ (fun k ↦ v k - e' x) := by
      funext k
      change ((v k - e' x, _) : H × (Fin 0 → ℝ)) = (v k - e' x, 0)
      exact Prod.ext rfl (Subsingleton.elim _ _)
    rw [hfun, ← map_prodZeroLinearEquiv_basis]
    exact hv.map L
  have hVt : range (affineSimplex (fun k ↦ L (v k))) ⊆ (e'.prod eZ).target := by
    rintro _ ⟨t, rfl⟩
    rw [OpenPartialHomeomorph.prod_target, hA]
    refine ⟨hvt ⟨t, rfl⟩, ?_⟩
    rw [Subsingleton.elim (L (affineSimplex v t)).2 (eZ z₀)]
    exact eZ.map_source (mem_chart_source _ _)
  have h0 := hμ.exteriorProduct R (IsLocallyClassOf.isFundamentalClass_of_unique R Z hc)
    (e'.prod eZ) ⟨e', he', eZ, chart_mem_atlas _ _, rfl⟩ ⟨_, hxz⟩ _ hV hVt
  have h1 := IsLocallyClassOf.of_restrict _ h0
  have h2 := IsLocallyClassOf.pushforward (TopCat.ofHom (ContinuousMap.fst : C(X × Z, X)))
    isProperMap_fst_of_compactSpace
    (fun y hy ↦ Prod.ext hy (Subsingleton.elim _ _)) h1
  have hσ : (TopCat.ofHom (ContinuousMap.fst : C(X × Z, X))).hom.comp
      (inclChainSimplex (chartOpens (e'.prod eZ)) (chartSimplex (e'.prod eZ) _ hVt)) =
      inclChainSimplex (chartOpens e') (chartSimplex e' v hvt) := by
    ext1 t
    change ((e'.prod eZ).symm (affineSimplex (fun k ↦ L (v k)) t)).1 = e'.symm (affineSimplex v t)
    rw [hA]
    rfl
  rw [hσ] at h2
  exact IsLocallyClassOf.restrict (chartOpens e') h2

end PointFactor

section LocalModel

open borelMooreHomology

variable (R : Type u) [CommRing R]

/-- Two successive degree identifications `congrDegree` compose to one. -/
lemma congrDegree_congrDegree_apply (X : TopCat.{u}) {i i' i'' : ℤ} (h₁ : i = i') (h₂ : i' = i'')
    (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    congrDegree R X h₂ (congrDegree R X h₁ x) = congrDegree R X (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

/-- Proper pushforward commutes with the degree identification `congrDegree`. -/
lemma pushforward_congrDegree_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsProperMap f)
    {i i' : ℤ} (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) f hf i').hom (congrDegree R X h x) =
      congrDegree R Y h ((pushforward R (ModuleCat.of R R) f hf i).hom x) := by
  subst h
  rfl

/-- Proper pushforward commutes with degree identifications `congrDegree` on either side, for any
choice of the equalities of degrees. -/
lemma congrDegree_pushforward_congrDegree_of_eq {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : IsProperMap f) {k i i' : ℤ} (hx : k = i) (h' : i = i') (hy : k = i')
    (x : borelMooreHomology R (ModuleCat.of R R) X k) :
    congrDegree R Y h' ((pushforward R (ModuleCat.of R R) f hf i).hom (congrDegree R X hx x)) =
      (pushforward R (ModuleCat.of R R) f hf i').hom (congrDegree R X hy x) := by
  subst hx h'
  rfl

/-- The projection `pr⁻¹(S) → X`, `(x, s) ↦ x`. -/
def prPreFst (X : TopCat.{u}) {Y : TopCat.{u}} (S : Set Y) : TopCat.of (prPre X S) ⟶ X :=
  TopCat.ofHom ⟨fun p ↦ p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The projection `pr⁻¹(S) → X` is proper when `S` is compact. -/
lemma isProperMap_prPreFst (X : TopCat.{u}) {Y : TopCat.{u}} (S : Set Y) [CompactSpace S] :
    IsProperMap (prPreFst X S) :=
  (isProperMap_fst_of_compactSpace (X := X) (Y := S)).comp
    (prodPreimageHomeomorph X S).symm.isProperMap

/-- The identification `X × S ≅ pr⁻¹(S)` followed by the projection `pr⁻¹(S) → X` is the first
projection `X × S → X`. -/
lemma prodPreimage_comp_prPreFst (X : TopCat.{u}) {Y : TopCat.{u}} (S : Set Y) :
    prodPreimage X S ≫ prPreFst X S = TopCat.ofHom (ContinuousMap.fst : C(X × S, X)) :=
  rfl

variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H] {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The local model of `u_{M,P} ∩ μ_P = μ_M`**: in `X × F`, with `μ_X` a fundamental class
of `X`, `μ_F` the fundamental class of `F` for its complex orientation and `u₀ ∈ H^{2r}(F, F - 0)`
the local orientation class at `0`, the cap product `pr^* u₀ ∩ (μ_X × μ_F) ∈ H_n(X × {0})` is
carried to `μ_X` by the projection `X × {0} ≅ X`. (By the product formula for cap products,
`pr^* u₀ ∩ (μ_X × μ_F) = μ_X × (u₀ ∩ μ_F)`, and `u₀ ∩ μ_F = [0]`.) -/
theorem IsFundamentalClass.pushforward_capProductSupportPullback_prSnd {n : ℕ}
    {b : Module.Basis (Fin n) ℝ H}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n} (hμ : IsFundamentalClass R b μ)
    {μF : borelMooreHomology R (ModuleCat.of R R) (TopCat.of F) (2 * Module.finrank ℂ F : ℕ)}
    (hμF : IsFundamentalClass R (complexOrientationBasisOf F) μF)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
      (2 * Module.finrank ℂ F : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀)
    (h0d : HasProperNeighbourhoodDeformations ({0} : Set (TopCat.of F)))
    (hXd : HasProperNeighbourhoodDeformations
      (prSnd (TopCat.of X) (TopCat.of F) ⁻¹' ({0} : Set (TopCat.of F))))
    (hdeg : (n : ℤ) + (2 * Module.finrank ℂ F : ℕ) - (2 * Module.finrank ℂ F : ℕ) = (n : ℕ)) :
    IsFundamentalClass R b
      ((pushforward R (ModuleCat.of R R) (prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)))
        (isProperMap_prPreFst _ _) n).hom
        (congrDegree R _ hdeg
          (capProductSupportPullback R (prSnd (TopCat.of X) (TopCat.of F)) isClosed_singleton hXd
            (2 * Module.finrank ℂ F : ℕ) ((n : ℤ) + (2 * Module.finrank ℂ F : ℕ)) u₀
            (borelMooreHomology.exteriorProduct R (TopCat.of X) (TopCat.of F) n
              (2 * Module.finrank ℂ F : ℕ) (μ ⊗ₜ μF))))) := by
  have h0 : ((2 * Module.finrank ℂ F : ℕ) : ℤ) - ((2 * Module.finrank ℂ F : ℕ) : ℤ) =
      ((0 : ℕ) : ℤ) := by simp
  -- the point case `u₀ ∩ μ_F = [0]`
  obtain ⟨c, hcdef⟩ : ∃ c, c = congrDegree R _ h0 (capProductSupport R (TopCat.of F)
      isClosed_singleton h0d _ _ u₀ μF) := ⟨_, rfl⟩
  have hc : IsLocallyClassOf R c (default : ({0} : Set (TopCat.of F)))
      (ContinuousMap.const _ default) := by
    rw [hcdef]
    exact isLocallyClassOf_capProductSupport_of_isLocalOrientationClass (M := F)
      (complexOrientationBasisOf F) h0d hμF hu₀ h0 _ _
  have hfund := hμ.pushforward_fst_exteriorProduct R ({0} : Set (TopCat.of F)) hc
  have hcap : capProductSupport R (TopCat.of F) isClosed_singleton h0d _ _ u₀ μF =
      congrDegree R _ h0.symm c := by
    rw [hcdef, congrDegree_congrDegree_apply]
    rfl
  -- the product formula
  have hext := pushforward_prodPreimage_exteriorProduct_capProductSupport R (TopCat.of X)
    (TopCat.of F) isClosed_singleton h0d hXd n _ _ (by simp) u₀ μ μF
  rw [hcap, exteriorProduct_congrDegree_right] at hext
  have h' : (n : ℤ) + (((2 * Module.finrank ℂ F : ℕ) : ℤ) - ((2 * Module.finrank ℂ F : ℕ) : ℤ)) =
      n := by omega
  have key := congrArg (congrDegree R _ h') hext
  rw [congrDegree_congrDegree_apply] at key
  rw [← key, pushforward_congrDegree_apply, ← ModuleCat.comp_apply, ← pushforward_comp,
    pushforward_congr_hom R (prodPreimage_comp_prPreFst (TopCat.of X) ({0} : Set (TopCat.of F)))
      _ isProperMap_fst_of_compactSpace]
  convert hfund using 1
  exact congrDegree_pushforward_congrDegree_of_eq R _ _ _ _ _ _

end LocalModel

end MMP
