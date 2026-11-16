module

public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.AgreesSubmanifoldChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.StacksAgreesSubmanifoldStalk
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksLocal
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNonvanishing
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksPresentation

/-!
# The orientation class of a regular imbedding of non-singular varieties, for Stacks bundles

For an orientation datum `(ℰ, σ, V, Q)` of a regular closed immersion `i : X → Y` of complex
schemes (`MMP.Modules.RegularImbeddingOrientationDatum`) and charts on `Y(ℂ)`, the section `σ̄`
of `Q` is transversal to the zero section along `X(ℂ)` (`IsSectionTransversalAlong`) as soon as
the local coordinates `σ^♯bₐ` of `σ` in a chart `c = (V, b)` of `ℰ` are differentiable at the
points `x` of `X(ℂ)` with a complex linear derivative `Dσ` whose kernel is the tangent space
`T_x X` and whose image lies in the normal fibre `N_x`: in a trivialization of `Q`,
`σ̄(y) = τ_y(q_y(σ(y)))` with `y ↦ τ_y ∘ q_y` continuous and `σ(x) = 0`, so `σ̄` has derivative
`τ_x ∘ q_x ∘ Dσ` at `x`, and `q_x` is injective on `N_x`.

## Main results

* `MMP.Modules.eval_sectionCoord_eq_zero_of_mem_range`: the local coordinates of `σ` vanish on
  `Z(σ)`.
* `MMP.Modules.RegularImbeddingOrientationDatum.isSectionTransversalAlong_sectionBar`: `σ̄` is
  transversal to the zero section along `X(ℂ)` once the local coordinates of `σ` have a suitable
  complex derivative.
* `MMP.Modules.RegularImbeddingOrientationDatum.isSectionTransversalAlong_of_tangentCone`:
  transversality from non-singularity, when the tangent cones are complex subspaces of
  codimension `d`.
* `MMP.Modules.IsRegularImbeddingOrientationClass.eval_comp_affineSimplex_eq_one`: the disc
  criterion for `u_{X,Y}`, with no tubular neighbourhood.
* `MMP.Modules.IsRegularImbeddingOrientationClass.isOrientationClass`: **Fulton §19.2 (ii)**.

## Implementation notes

"`X` and `Y` non-singular" is `MMP.IsNonsingularPair i E`. The proof: the derivative of the local
coordinates of `σ` at `x ∈ X(ℂ)` kills `T_x X` (`σ` vanishes on `X`), lands in `N_x`
(differentiate the relations), and has rank `≥ d` (`le_finrank_span_chartDeriv`, the regularity
of `𝒪_{X,x} = 𝒪_{Y,x}/(σ)`), so its kernel is `T_x X`; then `σ̄` is transversal to the zero section
of `Q`, and `eval_comp_affineSimplex_eq_one_of_isSectionTransversalAlong` gives the disc
criterion. The local coordinates are taken on the affine open `V` of the chart itself, which
`σ⁻¹(π⁻¹V) = V` contains.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Filter Topology Asymptotics

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

section Coord

variable {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ}

/-- The open `V` of a chart `c = (V, b)` lies in `σ⁻¹(π⁻¹V)`. -/
lemma le_preimage_preimage_proj_of_comp_eq_id {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (c : Chart E r) : c.1.1 ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1) :=
  (preimage_preimage_proj_of_comp_eq_id hσ _).ge

/-- **The local coordinates of `σ` vanish on `Z(σ)`.** -/
theorem eval_sectionCoord_eq_zero_of_mem_range (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion i] {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) (c : Chart E r) {W : Y.Opens}
    (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ W)
    (hyX : y ∈ range (UnderlyingSpace.map (K := ℂ) i)) (a : Fin r) :
    eval y hy (sectionCoord σ c hW a) = 0 := by
  obtain ⟨x, rfl⟩ := hyX
  have hc := le_preimage_preimage_proj_of_comp_eq_id hσ c
  have hWc : W ≤ c.1.1 := hW.trans (preimage_preimage_proj_of_comp_eq_id hσ _).le
  rw [← map_sectionCoord σ c hc hWc a, eval_restrict]
  exact eval_mapFun_eq_zero_of_mem_ker i x (W := c.1) _
    (by rw [← hs, ideal_zeroLocus σ c c.1 hc]; exact Ideal.subset_span ⟨a, rfl⟩)

end Coord

section Differential

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) F}
  {E : Y.Modules} [E.IsQuasicoherent] {r : ℕ} {σ : Y ⟶ totalSpace E}

/-- The differential at `p` of the local coordinates on `W` of a section `σ` in the chart `c`. -/
def sectionCoordDeriv (e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) F)
    (σ : Y ⟶ totalSpace E) (c : Chart E r) {W : Y.Opens} (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1))
    (p : UnderlyingSpace ℂ Y) : F →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun a ↦ chartDeriv e W p (sectionCoord σ c hW a)

omit [FiniteDimensional ℂ F] in
/-- In an algebraic chart `e`, the local coordinates on `W` of a section `σ` in the chart `c`
have derivative `sectionCoordDeriv e σ c hW p` at `e p`. -/
lemma hasFDerivAt_sectionCoord (he : IsAlgebraicChart e) {p : UnderlyingSpace ℂ Y}
    (hp : p ∈ e.source) (c : Chart E r) {W : Y.Opens} (hW : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1))
    (hpW : ⊤ ≤ p.toHom ⁻¹ᵁ W) :
    HasFDerivAt (fun k a ↦ evalExt W (sectionCoord σ c hW a) (e.symm k))
      (sectionCoordDeriv e σ c hW p) (e p) :=
  hasFDerivAt_pi.2 fun a ↦
    (differentiableAt_evalExt he hp hpW (sectionCoord σ c hW a)).hasFDerivAt

/-- **The differential of `σ` along `Z(σ)` takes values in the normal fibre.** -/
lemma sectionCoordDeriv_mem_normalFibre (he : IsAlgebraicChart e) (hσ : σ ≫ proj E = 𝟙 Y)
    (c : Chart E r) {p : UnderlyingSpace ℂ Y} (hp : p ∈ e.source) (hpc : ⊤ ≤ p.toHom ⁻¹ᵁ c.1.1)
    (hs0 : ∀ a, eval p hpc
      (sectionCoord σ c (le_preimage_preimage_proj_of_comp_eq_id hσ c) a) = 0) (w : F) :
    sectionCoordDeriv e σ c (le_preimage_preimage_proj_of_comp_eq_id hσ c) p w ∈
      normalFibre σ c p := by
  rw [mem_normalFibre]
  intro W hW hpW g hg
  have hc := le_preimage_preimage_proj_of_comp_eq_id hσ c
  have hWc : W ≤ c.1.1 := hW.trans (preimage_preimage_proj_of_comp_eq_id hσ _).le
  have hsW : ∀ a, sectionCoord σ c hW a = Y.presheaf.map (homOfLE hWc).op (sectionCoord σ c hc a) :=
    fun a ↦ (map_sectionCoord σ c hc hWc a).symm
  have h0 := congrArg (fun t ↦ chartDeriv e W p t w) hg
  have hc0 := chartDeriv_constSection (e := e) hp hpW 0
  rw [constSection, map_zero, map_zero] at hc0
  simp only [hc0, zero_apply] at h0
  rw [chartDeriv_sum he hp hpW] at h0
  simp only [hsW, chartDeriv_mul he hp hpW, chartDeriv_restrict hWc hp hpW,
    evalExt_of_le _ hpW, eval_restrict, hs0, zero_smul, add_zero,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [sectionCoordDeriv, ContinuousLinearMap.pi_apply, smul_eq_mul, mul_comm]

omit [FiniteDimensional ℂ F] in
/-- **The differential of `σ` kills the tangent cone of `Z(σ)`.** -/
lemma sectionCoordDeriv_eq_zero_of_mem_tangentConeAt (he : IsAlgebraicChart e) {i : X ⟶ Y}
    [i.IsOver (Spec (.of ℂ))] [IsClosedImmersion i] (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) {p : UnderlyingSpace ℂ Y} (hp : p ∈ e.source)
    (hpX : p ∈ range (UnderlyingSpace.map (K := ℂ) i)) (c : Chart E r)
    (hpc : ⊤ ≤ p.toHom ⁻¹ᵁ c.1.1) {w : F}
    (hw : w ∈ tangentConeAt ℝ (e '' (range (UnderlyingSpace.map (K := ℂ) i) ∩ e.source)) (e p)) :
    sectionCoordDeriv e σ c (le_preimage_preimage_proj_of_comp_eq_id hσ c) p w = 0 := by
  have hc := le_preimage_preimage_proj_of_comp_eq_id hσ c
  have hD := ((hasFDerivAt_sectionCoord he hp c hc hpc).restrictScalars ℝ).hasFDerivWithinAt
    (s := e '' (range (UnderlyingSpace.map (K := ℂ) i) ∩ e.source))
  have h := hD.mapsTo_tangent_cone hw
  have hsub : (fun k a ↦ evalExt c.1.1 (sectionCoord σ c hc a) (e.symm k)) ''
      (e '' (range (UnderlyingSpace.map (K := ℂ) i) ∩ e.source)) ⊆
        ((⊥ : Submodule ℝ (Fin r → ℂ)) : Set (Fin r → ℂ)) := by
    rintro _ ⟨_, ⟨y, ⟨hyX, hys⟩, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    funext a
    change evalExt c.1.1 (sectionCoord σ c hc a) (e.symm (e y)) = 0
    rw [e.left_inv hys]
    by_cases hyj : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1
    · rw [evalExt_of_le _ hyj]
      exact eval_sectionCoord_eq_zero_of_mem_range i hσ hs c hc y hyj hyX a
    · simp [evalExt, hyj]
  have h0 := tangentConeAt_subset_of_subset_submodule _ (by simp) hsub (by
    rw [Submodule.mem_bot]
    funext a
    rw [e.left_inv hp, evalExt_of_le _ hpc]
    exact eval_sectionCoord_eq_zero_of_mem_range i hσ hs c hc p hpc hpX a) h
  simpa using h0

/-- **The kernel of the differential of `σ` has dimension at most `dim Y - d`** at a point of a
regular closed immersion `X ⊆ Y` of codimension `d` at which `X` and `Y` are regular, `Y` of
dimension `n`, in an algebraic chart modelled on `ℂⁿ`. -/
lemma finrank_ker_sectionCoordDeriv_add_le (he : IsAlgebraicChart e) {i : X ⟶ Y}
    [i.IsOver (Spec (.of ℂ))] [IsClosedImmersion i] {d n : ℕ}
    (hi : IsRegularClosedImmersionOfCodim i d) (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) {x : UnderlyingSpace ℂ X} (hp : mapFun i x ∈ e.source)
    (hn : Module.finrank ℂ F = n)
    [IsRegularLocalRing (Y.presheaf.stalk ((mapFun i x).toHom (IsLocalRing.closedPoint ℂ)))]
    (hdim : ringKrullDim (Y.presheaf.stalk ((mapFun i x).toHom (IsLocalRing.closedPoint ℂ))) = n)
    [IsRegularLocalRing (X.presheaf.stalk (x.toHom (IsLocalRing.closedPoint ℂ)))]
    (c : Chart E r) (hpc : ⊤ ≤ (mapFun i x).toHom ⁻¹ᵁ c.1.1) :
    Module.finrank ℂ (LinearMap.ker (sectionCoordDeriv e σ c
      (le_preimage_preimage_proj_of_comp_eq_id hσ c) (mapFun i x) : F →ₗ[ℂ] (Fin r → ℂ)))
      + d ≤ n := by
  have hc := le_preimage_preimage_proj_of_comp_eq_id hσ c
  have hpX : mapFun i x ∈ range (UnderlyingSpace.map (K := ℂ) i) := ⟨x, rfl⟩
  have hsW : ∀ a, evalExt c.1.1 (sectionCoord σ c hc a) (mapFun i x) = 0 := fun a ↦ by
    rw [evalExt_of_le _ hpc]
    exact eval_sectionCoord_eq_zero_of_mem_range i hσ hs c hc _ _ hpX a
  have hreg := isRegularLocalRing_quotient_span_germ_sectionCoord_mapFun (W := c.1) hc hs hpc
  have hdimq := ringKrullDim_quotient_span_germ_sectionCoord_mapFun (W := c.1) hc hi hs hpc
  rw [hdim] at hdimq
  have h := finrank_iInf_ker_chartDeriv_add_le hn he hp c.1.2 hpc hdim
    (fun a ↦ sectionCoord σ c hc a) hsW hreg (by exact_mod_cast hdimq)
  have hker : (⨅ a, LinearMap.ker (chartDeriv e c.1.1 (mapFun i x)
      (sectionCoord σ c hc a) : F →ₗ[ℂ] ℂ) : Submodule ℂ F) =
      LinearMap.ker (sectionCoordDeriv e σ c hc (mapFun i x) : F →ₗ[ℂ] (Fin r → ℂ)) := by
    rw [sectionCoordDeriv, ContinuousLinearMap.coe_pi, LinearMap.ker_pi]
  rwa [hker] at h

end Differential

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ} (D : RegularImbeddingOrientationDatum i d)

/-- `σ̄(y) = q_y(σ(y))` in the coordinates of a chart `c` of `ℰ`. -/
lemma sectionBar_eq_mk_chartL (c : Chart D.E D.rank) (y : D.nbhd)
    (hy : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1) :
    D.sectionBar y = ⟨y, D.chartL c y (fun a ↦ eval y.1 hy
      (sectionCoord D.σ c (le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c) a))⟩ := by
  rw [← quot_chartInv D c y hy, sectionBar]
  congr 1
  refine Subtype.ext ((mapFun_eq_chartInv_coord D.comp_proj c y.1 hy).trans ?_)
  congr 1
  funext a
  rw [eval_sectionCoord]

/-- `σ̄` vanishes on `X(ℂ)`. -/
lemma sectionBar_eq_zeroSection [IsClosedImmersion i] (y : D.nbhd)
    (hy : y.1 ∈ range (UnderlyingSpace.map (K := ℂ) i)) :
    D.sectionBar y = Bundle.zeroSection D.F D.Q y := by
  obtain ⟨c, hc⟩ := exists_mem_chartBase D.E D.rank y.1
  rw [sectionBar_eq_mk_chartL D c y hc]
  have h0 : (fun a ↦ eval y.1 hc (sectionCoord D.σ c
      (le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c) a)) = 0 := funext fun a ↦
    eval_sectionCoord_eq_zero_of_mem_range i D.comp_proj D.zeroLocus_eq c _ y.1 hc hy a
  rw [h0, map_zero]
  rfl

/-- The fibrewise linear map `τ_y ∘ q_y : ℂ^e → F` of a chart `c` and a trivialization `τ`. -/
def chartLTriv (c : Chart D.E D.rank)
    (τ : Trivialization D.F (TotalSpace.proj : TotalSpace D.F D.Q → D.nbhd)) [τ.IsLinear ℂ]
    (y : D.nbhd) : (Fin D.rank → ℂ) →L[ℂ] D.F :=
  LinearMap.toContinuousLinearMap (τ.linearMapAt ℂ y ∘ₗ D.chartL c y)

/-- In a linear trivialization `τ`, the fibre coordinate of `σ̄ y` is `τ_y ∘ q_y` applied to the
coordinates of `σ` at `y` in the chart `c`. -/
lemma trivialization_sectionBar_snd (c : Chart D.E D.rank)
    (τ : Trivialization D.F (TotalSpace.proj : TotalSpace D.F D.Q → D.nbhd)) [τ.IsLinear ℂ]
    (y : D.nbhd) (hy : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1) (hyτ : y ∈ τ.baseSet) :
    (τ (D.sectionBar y)).2 = D.chartLTriv c τ y (fun a ↦ eval y.1 hy
      (sectionCoord D.σ c (le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c) a)) := by
  rw [sectionBar_eq_mk_chartL D c y hy]
  simp only [chartLTriv, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, τ.coe_linearMapAt_of_mem hyτ]

/-- The fibrewise linear map `y ↦ τ_y ∘ q_y` is continuous along a continuous map `β` into
`D.nbhd` whose values lie in the base of `c` and in the base set of `τ`. -/
lemma continuousOn_chartLTriv (c : Chart D.E D.rank)
    (τ : Trivialization D.F (TotalSpace.proj : TotalSpace D.F D.Q → D.nbhd)) [τ.IsLinear ℂ]
    {Z : Type*} [TopologicalSpace Z] {β : Z → D.nbhd} {S : Set Z} (hβ : ContinuousOn β S)
    (hS : ∀ z ∈ S, ⊤ ≤ (β z).1.toHom ⁻¹ᵁ c.1.1 ∧ β z ∈ τ.baseSet) :
    ContinuousOn (fun z ↦ D.chartLTriv c τ (β z)) S := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  rw [continuousOn_iff_continuous_domRestrict]
  let q : S → TotalSpace D.F D.Q := fun z ↦ D.quot
    ⟨chartInv c (β z.1).1 (hS z.1 z.2).1 v,
      by rw [mapFun_proj_chartInv]; exact (β z.1).2⟩
  have hq : ∀ z : S, q z = ⟨β z.1, D.chartL c (β z.1) v⟩ :=
    fun z ↦ D.quot_chartInv c (β z.1) (hS z.1 z.2).1 v
  let ζ : S → {x : UnderlyingSpace ℂ Y // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin D.rank → ℂ) :=
    fun z ↦ (⟨(β z.1).1, (hS z.1 z.2).1⟩, v)
  have hζ : Continuous ζ := ((continuous_subtype_val.comp
    (continuousOn_iff_continuous_domRestrict.1 hβ)).subtype_mk _).prodMk continuous_const
  have hcp := (continuous_chartInv c).comp hζ
  have hqc : Continuous q := by
    have h1 : Continuous fun z : S ↦ (⟨chartInv c (ζ z).1.1 (ζ z).1.2 (ζ z).2,
        by rw [mapFun_proj_chartInv]; exact (β z.1).2⟩ :
          {p : UnderlyingSpace ℂ (totalSpace D.E) // mapFun (proj D.E) p ∈ D.nbhd}) :=
      hcp.subtype_mk _
    exact D.continuous_quot.comp h1
  have hc : Continuous fun z : S ↦ (τ (q z)).2 := by
    refine continuous_snd.comp (τ.continuousOn.comp_continuous hqc fun z ↦ ?_)
    rw [τ.mem_source, hq]
    exact (hS z.1 z.2).2
  refine hc.congr fun z ↦ ?_
  change _ = D.chartLTriv c τ (β z.1) v
  simp only [chartLTriv, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, hq, τ.coe_linearMapAt_of_mem (hS z.1 z.2).2]

section Transversal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [ChartedSpace E (UnderlyingSpace ℂ Y)]

/-- **`σ̄` is transversal to the zero section along `X(ℂ)`** as soon as, at every `x ∈ X(ℂ)`, the
local coordinates of `σ` in some chart `c` of `ℰ` are differentiable at `x` (in the chart of
`Y(ℂ)`) with a complex linear derivative `Dσ` whose kernel is the tangent cone of `X(ℂ)` at `x`
and whose image lies in the normal fibre `N_x`. -/
theorem isSectionTransversalAlong_sectionBar [IsClosedImmersion i]
    (hDs : ∀ x ∈ range (UnderlyingSpace.map (K := ℂ) i), ∃ (c : Chart D.E D.rank)
      (_ : ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1) (Ds : E →L[ℂ] (Fin D.rank → ℂ)),
      HasFDerivAt (fun k a ↦ evalExt c.1.1
          (sectionCoord D.σ c (le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c) a)
          ((_root_.chartAt E x).symm k)) (Ds.restrictScalars ℝ) (_root_.chartAt E x x) ∧
        (∀ w, Ds w = 0 ↔ w ∈ tangentConeAt ℝ (_root_.chartAt E x ''
          (range (UnderlyingSpace.map (K := ℂ) i) ∩ (_root_.chartAt E x).source))
          (_root_.chartAt E x x)) ∧
        ∀ w, Ds w ∈ normalFibre D.σ c x) :
    IsSectionTransversalAlong (P := TopCat.of (UnderlyingSpace ℂ Y)) E D.isOpen_nbhd
      D.sectionBar (range (UnderlyingSpace.map (K := ℂ) i)) := by
  intro x hx hxV
  let _ := openChartedSpace (P := TopCat.of (UnderlyingSpace ℂ Y)) E D.isOpen_nbhd
  obtain ⟨c, hj, Ds, hD, hker, hN⟩ := hDs x hx
  set b : D.nbhd := ⟨x, hxV⟩
  set τ := trivializationAt D.F D.Q b with hτ
  set e := _root_.chartAt E b
  let O : Set E := e.target ∩ e.symm ⁻¹' {y | ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1 ∧ y ∈ τ.baseSet}
  have hOo : IsOpen O := e.isOpen_inter_preimage_symm
    ((isOpen_chartBase c).preimage continuous_subtype_val |>.inter τ.open_baseSet)
  have hbO : e b ∈ O := ⟨e.map_source (mem_chart_source E b), by
    rw [mem_preimage, e.left_inv (mem_chart_source E b)]
    exact ⟨hj, mem_baseSet_trivializationAt D.F D.Q b⟩⟩
  have hex : e b = _root_.chartAt E x x := rfl
  let Mf : E → (Fin D.rank → ℂ) →L[ℂ] D.F := fun k ↦ D.chartLTriv c τ (e.symm k)
  have hMc : ContinuousAt Mf (_root_.chartAt E x x) := by
    rw [← hex]
    exact (D.continuousOn_chartLTriv c τ (e.continuousOn_symm.mono inter_subset_left)
      fun k hk ↦ hk.2).continuousAt (hOo.mem_nhds hbO)
  let Mf' : E → (Fin D.rank → ℂ) →L[ℝ] D.F := fun k ↦ (Mf k).restrictScalars ℝ
  have hMc' : ContinuousAt Mf' (_root_.chartAt E x x) :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Fin D.rank → ℂ) D.F ℝ ℝ).continuous.continuousAt.comp
      hMc
  have hw0 : (fun a ↦ evalExt c.1.1
      (sectionCoord D.σ c (le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c) a)
      ((_root_.chartAt E x).symm (_root_.chartAt E x x))) = 0 := by
    funext a
    rw [(_root_.chartAt E x).left_inv (mem_chart_source E x), evalExt_of_le _ hj]
    exact eval_sectionCoord_eq_zero_of_mem_range i D.comp_proj D.zeroLocus_eq c _ x hj hx a
  refine ⟨(Mf (_root_.chartAt E x x)).comp Ds, ?_, ?_⟩
  · refine (hasFDerivAt_apply_of_continuousAt_of_eq_zero hMc' hD hw0).congr_of_eventuallyEq ?_
    rw [← hex]
    filter_upwards [hOo.mem_nhds hbO] with k hk
    have hk1 : (e.symm k : UnderlyingSpace ℂ Y) = (_root_.chartAt E x).symm k :=
      (OpenPartialHomeomorph.subtypeRestr_symm_eqOn (_root_.chartAt E x) _ hk.1).symm
    change ((trivializationAt D.F D.Q b) (D.sectionBar (e.symm k))).2 = Mf k _
    rw [← hτ, D.trivialization_sectionBar_snd c τ _ hk.2.1 hk.2.2]
    exact congrArg (D.chartLTriv c τ (e.symm k))
      (funext fun a ↦ by rw [← hk1, evalExt_of_le _ hk.2.1])
  · have hMb : Mf (_root_.chartAt E x x) = D.chartLTriv c τ b := by
      change D.chartLTriv c τ (e.symm (_root_.chartAt E x x)) = _
      rw [← hex, e.left_inv (mem_chart_source E b)]
    intro w
    rw [← hker, ContinuousLinearMap.comp_apply, hMb]
    refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, map_zero]⟩
    change τ.linearMapAt ℂ b (D.chartL c b (Ds w)) = 0 at h0
    have h1 : D.chartL c b (Ds w) = 0 := injective_linearMapAt τ
      (mem_baseSet_trivializationAt D.F D.Q b) (by rw [h0, map_zero])
    exact (Submodule.disjoint_def.1 (D.isCompl_ker_chartL c b hj hx).disjoint) _ h1 (hN w)

end Transversal

end RegularImbeddingOrientationDatum

section Agrees

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ}

/-- For a regular closed immersion of non-singular schemes whose tangent cones are complex
subspaces of codimension `d`, the section `σ̄` of every orientation datum is transversal to the
zero section along `X(ℂ)`. -/
theorem RegularImbeddingOrientationDatum.isSectionTransversalAlong_of_tangentCone
    [ChartedSpace E (UnderlyingSpace ℂ Y)] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d)
    (hns : IsNonsingularPair i E) (D : RegularImbeddingOrientationDatum i d)
    (hW : ∀ x ∈ range (UnderlyingSpace.map (K := ℂ) i), ∃ W : Submodule ℂ E,
      tangentConeAt ℝ (_root_.chartAt E x '' (range (UnderlyingSpace.map (K := ℂ) i) ∩
        (_root_.chartAt E x).source)) (_root_.chartAt E x x) = W ∧
        Module.finrank ℂ W + d = Module.finrank ℂ E) :
    IsSectionTransversalAlong (P := TopCat.of (UnderlyingSpace ℂ Y)) E D.isOpen_nbhd
      D.sectionBar (range (UnderlyingSpace.map (K := ℂ) i)) := by
  refine D.isSectionTransversalAlong_sectionBar fun x hx ↦ ?_
  obtain ⟨c, hj⟩ := exists_mem_chartBase D.E D.rank x
  have he := hns.isAlgebraicChart (_root_.chartAt E x) (chart_mem_atlas E x)
  have hxs := mem_chart_source E x
  obtain ⟨W, hTW, hdimW⟩ := hW x hx
  obtain ⟨x', rfl⟩ := hx
  have hc := le_preimage_preimage_proj_of_comp_eq_id D.comp_proj c
  have hx0 : ∀ a, eval (mapFun i x') hj (sectionCoord D.σ c hc a) = 0 := fun a ↦
    eval_sectionCoord_eq_zero_of_mem_range i D.comp_proj D.zeroLocus_eq c hc _ hj ⟨x', rfl⟩ a
  refine ⟨c, hj, sectionCoordDeriv (_root_.chartAt E (mapFun i x')) D.σ c hc (mapFun i x'),
    (hasFDerivAt_sectionCoord he hxs c hc hj).restrictScalars ℝ, ?_,
    sectionCoordDeriv_mem_normalFibre he D.comp_proj c hxs hj hx0⟩
  have := (hns.regular_Y (mapFun i x')).1
  have := hns.regular_X x'
  have hdimK := finrank_ker_sectionCoordDeriv_add_le he hi D.comp_proj D.zeroLocus_eq hxs rfl
    (hns.regular_Y _).2 c hj
  set K := LinearMap.ker
    (sectionCoordDeriv (_root_.chartAt E (mapFun i x')) D.σ c hc (mapFun i x') :
      E →ₗ[ℂ] (Fin D.rank → ℂ)) with hK
  have hdimK' : Module.finrank ℂ K + d ≤ Module.finrank ℂ E := hdimK
  have hTW' : tangentConeAt ℝ (_root_.chartAt E (UnderlyingSpace.map (K := ℂ) i x') ''
      (range (UnderlyingSpace.map (K := ℂ) i) ∩
        (_root_.chartAt E (UnderlyingSpace.map (K := ℂ) i x')).source))
      (_root_.chartAt E (UnderlyingSpace.map (K := ℂ) i x')
        (UnderlyingSpace.map (K := ℂ) i x')) = W :=
    hTW
  have hWK : W ≤ K := fun w hw ↦ by
    rw [hK, LinearMap.mem_ker]
    exact sectionCoordDeriv_eq_zero_of_mem_tangentConeAt he D.comp_proj D.zeroLocus_eq hxs
      ⟨x', rfl⟩ c hj (hTW' ▸ hw)
  have hWK' : W = K := Submodule.eq_of_le_of_finrank_le hWK (by omega)
  intro w
  rw [hTW', SetLike.mem_coe, hWK', hK, LinearMap.mem_ker]
  rfl

open RegularImbeddingOrientationDatum SingularChain SingularCochain ThomClass in
/-- **Disc criterion for the orientation class of a regular imbedding of non-singular schemes.**
In the situation of `IsRegularImbeddingOrientationClass.isOrientationClass`, but with no tubular
neighbourhood (only the tangent cones of `X(ℂ)` are complex subspaces of codimension `d`), a
representing cocycle of the orientation class `u_{X,Y}` takes the value `1` on `B ∘ Δ` for every
oriented affine simplex `Δ` around `0` in `ℂ^d` and every transversal disc `B` of `X(ℂ)`. -/
theorem IsRegularImbeddingOrientationClass.eval_comp_affineSimplex_eq_one (R : Type) [CommRing R]
    [IsClosedImmersion i] [ChartedSpace E (UnderlyingSpace ℂ Y)]
    (hi : IsRegularClosedImmersionOfCodim i d) (hns : IsNonsingularPair i E)
    (hW : ∀ x ∈ range (UnderlyingSpace.map (K := ℂ) i), ∃ W : Submodule ℂ E,
      tangentConeAt ℝ (_root_.chartAt E x '' (range (UnderlyingSpace.map (K := ℂ) i) ∩
        (_root_.chartAt E x).source)) (_root_.chartAt E x x) = W ∧
        Module.finrank ℂ W + d = Module.finrank ℂ E)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R i d u)
    {α : Simplex (TopCat.of (UnderlyingSpace ℂ Y)) (2 * d) → R}
    (hα : α ∈ relCocycles R ((range (UnderlyingSpace.map (K := ℂ) i))ᶜ :
      Set (TopCat.of (UnderlyingSpace ℂ Y))) (2 * d))
    (hrep : relativeSingularCohomologyEquiv R ((range (UnderlyingSpace.map (K := ℂ) i))ᶜ :
      Set (TopCat.of (UnderlyingSpace ℂ Y))) (2 * d) u = Submodule.Quotient.mk ⟨α, hα⟩)
    {x : UnderlyingSpace ℂ Y} (hx : x ∈ range (UnderlyingSpace.map (K := ℂ) i))
    (B : C(Fin d → ℂ, TopCat.of (UnderlyingSpace ℂ Y))) (hB0 : B 0 = x)
    (hBM : ∀ v, B v ∈ range (UnderlyingSpace.map (K := ℂ) i) → v = 0)
    {L : (Fin d → ℂ) →L[ℝ] E} (hB : HasFDerivAt (fun v ↦ _root_.chartAt E x (B v)) L 0)
    (hinj : Function.Injective L) (W : Submodule ℂ E)
    (hTW : tangentConeAt ℝ (_root_.chartAt E x '' (range (UnderlyingSpace.map (K := ℂ) i) ∩
      (_root_.chartAt E x).source)) (_root_.chartAt E x x) = W)
    (hc : IsCompl (LinearMap.range (L : (Fin d → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hl : ∀ (c : ℂ) (v : Fin d → ℂ), L (c • v) - c • L v ∈ W)
    {v : Fin (2 * d + 1) → (Fin d → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis d) v) :
    SingularCochain.eval α (Finsupp.single (B.comp (affineSimplex v)) 1) = 1 := by
  obtain ⟨D, uQ, hQ, huD⟩ := hu
  exact eval_comp_affineSimplex_eq_one_of_isSectionTransversalAlong
    (P := TopCat.of (UnderlyingSpace ℂ Y)) (k := d) (u := u) (uQ := uQ) D.isOpen_nbhd R D.finrank_F
    D.sectionBar D.continuous_sectionBar D.proj_sectionBar D.range_subset_nbhd
    D.sectionBar_eq_zeroSection D.sectionBar_preimage_subset
    (D.isSectionTransversalAlong_of_tangentCone hi hns hW) hQ huD hα hrep hx B hB0 hBM hB hinj W
    hTW hc hl hv

open RegularImbeddingOrientationDatum in
/-- **Fulton, §19.2 (ii): for non-singular `X` and `Y` the two orientation classes agree.** Let
`i : X → Y` be a regular closed immersion of codimension `d` of complex schemes, `Y(ℂ)` with a
complex atlas of algebraic charts modelled on `E`, the local rings of `Y` regular of dimension
`dim E` and those of `X` regular (`IsNonsingularPair`). If `u ∈ H^{2d}(Y, Y - X)` is an
orientation class of `i` (`MMP.Modules.IsRegularImbeddingOrientationClass`) and `φ : N → Y(ℂ)` is
a tubular neighbourhood of `X(ℂ)` of rank `d` compatible with the complex orientations, then `u`
is the orientation class of the submanifold `X(ℂ) ⊆ Y(ℂ)` relative to `φ` (`IsOrientationClass`).
-/
theorem IsRegularImbeddingOrientationClass.isOrientationClass (R : Type) [CommRing R]
    [IsClosedImmersion i] [ChartedSpace E (UnderlyingSpace ℂ Y)]
    (hi : IsRegularClosedImmersionOfCodim i d) (hns : IsNonsingularPair i E)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {N : range (UnderlyingSpace.map (K := ℂ) i) → Type} [∀ x, AddCommGroup (N x)]
    [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)] [TopologicalSpace (TotalSpace F N)]
    [FiberBundle F N] [_root_.VectorBundle ℂ F N]
    (φ : TubularNeighbourhood (P := TopCat.of (UnderlyingSpace ℂ Y)) F N)
    (hφ : φ.IsOrientationCompatible (E := E)) (hF : Module.finrank ℂ F = d)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map i)) (2 * d : ℕ)}
    (hu : IsRegularImbeddingOrientationClass R i d u) :
    IsOrientationClass E R φ ((eqToHom (congrArg (fun n : ℕ ↦ cohomologyWithSupports R
      (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y)) (range (UnderlyingSpace.map i))
      ((2 * n : ℕ) : ℤ)) hF.symm)).hom u) := by
  subst hF
  obtain ⟨D, uQ, hQ, huD⟩ := hu
  simp only [eqToHom_refl, ModuleCat.id_apply]
  refine isOrientationClass_of_isSectionTransversalAlong D.isOpen_nbhd R φ hφ D.finrank_F
    D.sectionBar D.continuous_sectionBar D.proj_sectionBar D.range_subset_nbhd
    D.sectionBar_eq_zeroSection D.sectionBar_preimage_subset
    (D.isSectionTransversalAlong_of_tangentCone hi hns fun x hx ↦ ?_) hQ huD
  obtain ⟨ψ, L, -, hinj, W, hTW, hc, -⟩ := hφ ⟨x, hx⟩
  exact ⟨W, hTW, finrank_add_of_isCompl L hinj W hc⟩

end Agrees

end MMP.Modules
