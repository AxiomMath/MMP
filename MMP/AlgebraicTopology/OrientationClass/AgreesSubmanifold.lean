module

public import MMP.AlgebraicTopology.OrientationClass.Transversal
/-!
# The orientation class of a regular imbedding of non-singular varieties (Fulton, §19.2 (ii))

If `X ⊆ Y` is a regular imbedding of codimension `d` of non-singular complex varieties, the
orientation class `u_{X,Y}` of the regular imbedding (`IsRegularImbeddingOrientationClass`) is the
orientation class of the closed submanifold `X(ℂ) ⊆ Y(ℂ)` (`IsOrientationClass`).

This file holds the topological part of the proof: a **disc criterion through a section**. Let
`Q` be a complex vector bundle of rank `d` on an open neighbourhood `V` of `M` in a complex
manifold `P`, and `σ` a continuous section of `Q` vanishing exactly on `M`, which at each `x ∈ M`
is differentiable in the charts with a complex linear derivative `S` whose kernel is the tangent
space `T_x M`. If `u ∈ H^{2d}(P, P - M)` restricts on `V` to `σ^* u_Q`, then a representing
cocycle of `u` takes the value `1` on every transversal disc of `M`: for a disc `B` through
`x ∈ M` with derivative `L` complementary to `T_x M` and complex linear modulo `T_x M`, the disc
`σ ∘ B` of `Q` through `0_x` has derivative `(L, S ∘ L)`, and `S ∘ L` is a complex linear
isomorphism; so the disc criterion of the zero section (whose orientation class is `u_Q`)
applies.

## Main results

* `MMP.IsThomClass.eval_comp_affineSimplex_eq_one`: the disc criterion for the
  Thom class, as the orientation class of the zero section.
* `MMP.eval_comp_affineSimplex_eq_one_of_isSectionTransversalAlong`: the disc
  criterion through a transversal section.
* `MMP.isOrientationClass_of_isSectionTransversalAlong`: the pull-back of a Thom
  class by a transversal section is the orientation class.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Filter Topology Metric Finsupp Manifold

universe u

namespace MMP

open SingularChain SingularCochain ThomClass

section ZeroSection

variable {B : Type u} [TopologicalSpace B]
  {HB : Type*} [NormedAddCommGroup HB] [NormedSpace ℂ HB] [FiniteDimensional ℂ HB]
  [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {Q : B → Type u} [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)] [∀ x, TopologicalSpace (Q x)]
  [TopologicalSpace (TotalSpace F Q)] [FiberBundle F Q] [_root_.VectorBundle ℂ F Q]
  (R : Type u) [CommRing R]

/-- **Disc criterion for the Thom class.** A representing relative cocycle `α` of a Thom class
`u_Q` takes the value `1` on `A ∘ Δ`, for `Δ` an oriented affine simplex around `0` in `ℂ^d` and
`A : ℂ^d → Q` a continuous disc through `0_b` meeting the zero section only at `0`, differentiable
at `0` in the chart of the total space at `0_b` with a derivative whose fibre component is
injective and complex linear. -/
theorem IsThomClass.eval_comp_affineSimplex_eq_one
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F Q))
      (range (zeroSection F Q)) (2 * Module.finrank ℂ F : ℕ)}
    (huQ : IsThomClass (R := R) F Q uQ)
    {α : Simplex (TopCat.of (TotalSpace F Q)) (2 * Module.finrank ℂ F) → R}
    (hα : α ∈ relCocycles R ((range (zeroSection F Q))ᶜ : Set (TopCat.of (TotalSpace F Q)))
      (2 * Module.finrank ℂ F))
    (hrep : relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F Q)) _
      (2 * Module.finrank ℂ F) uQ = Submodule.Quotient.mk ⟨α, hα⟩)
    (b : B) (A : C(Fin (Module.finrank ℂ F) → ℂ, TotalSpace F Q)) (hA0 : A 0 = zeroSection F Q b)
    (hAM : ∀ v, A v ∈ range (zeroSection F Q) → v = 0)
    {L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] HB × F}
    (hA : letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := Q)
      HasFDerivAt (fun v ↦ chartAt (HB × F) (zeroSection F Q b) (A v)) L 0)
    (hinj : Function.Injective fun v ↦ (L v).2)
    (hl : ∀ (c : ℂ) v, (L (c • v)).2 = c • (L v).2)
    {v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v) :
    eval α (single (A.comp (affineSimplex v)) 1) = 1 := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := Q)
  have hu : IsOrientationClass (HB × F) R (zeroSectionTubularNeighbourhood F Q) uQ := by
    rw [eq_thomClass F Q huQ]
    exact isOrientationClass_zeroSection_thomClass F Q R
  let S : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] F :=
    (LinearMap.snd ℝ HB F).comp (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] HB × F)
  have hS : ∀ w, S w = (L w).2 := fun _ ↦ rfl
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℂ F) → ℂ) = Module.finrank ℝ F := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hSsurj : Function.Surjective S :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  have hLinj : Function.Injective L := fun w w' h ↦ hinj (congrArg Prod.snd h)
  refine hu.eval_comp_affineSimplex_eq_one R hα hrep ⟨b, rfl⟩ A hA0 hAM hA hLinj
    (LinearMap.range (LinearMap.inl ℂ HB F)) ?_ ?_ ?_ hv
  · exact tangentConeAt_chartAt_zeroSection F Q b
  · refine IsCompl.of_eq ?_ ?_
    · refine (Submodule.eq_bot_iff _).2 fun p hp ↦ ?_
      obtain ⟨⟨w, rfl⟩, ⟨h, hh⟩⟩ := Submodule.mem_inf.1 hp
      have h2 : (L w).2 = 0 := by simpa using (congrArg Prod.snd hh).symm
      have hw : w = 0 := hinj (by simpa using h2)
      simp [hw]
    · refine eq_top_iff.2 fun p _ ↦ ?_
      obtain ⟨w, hw⟩ := hSsurj p.2
      have hp : p = L w + (p.1 - (L w).1, 0) := by
        ext
        · simp
        · simp [← hS, hw]
      rw [hp]
      refine Submodule.add_mem_sup ⟨w, rfl⟩ ⟨p.1 - (L w).1, ?_⟩
      simp
  · intro c w
    refine ⟨(L (c • w) - c • L w).1, ?_⟩
    ext
    · simp
    · simp [hl c w]

end ZeroSection

section Retraction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial retraction of `V` onto the closed ball of radius `ρ` around `0`. -/
def radialRetraction (ρ : ℝ) (v : V) : V :=
  min 1 (ρ / ‖v‖) • v

/-- The radial retraction onto the closed ball of radius `ρ` fixes every `v` with `‖v‖ < ρ`. -/
lemma radialRetraction_of_norm_lt {ρ : ℝ} {v : V} (hv : ‖v‖ < ρ) : radialRetraction ρ v = v := by
  rcases eq_or_ne v 0 with rfl | h0
  · simp [radialRetraction]
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 h0
    have : 1 ≤ ρ / ‖v‖ := (le_div_iff₀ hpos).2 (by linarith)
    simp [radialRetraction, min_eq_left this]

/-- For `0 ≤ ρ`, the radial retraction takes values in the closed ball of radius `ρ`. -/
lemma norm_radialRetraction_le {ρ : ℝ} (hρ : 0 ≤ ρ) (v : V) : ‖radialRetraction ρ v‖ ≤ ρ := by
  rcases eq_or_ne v 0 with rfl | h0
  · simpa [radialRetraction] using hρ
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 h0
    rw [radialRetraction, norm_smul, Real.norm_of_nonneg (le_min zero_le_one (by positivity))]
    calc min 1 (ρ / ‖v‖) * ‖v‖ ≤ ρ / ‖v‖ * ‖v‖ := by gcongr; exact min_le_right _ _
      _ = ρ := div_mul_cancel₀ ρ hpos.ne'

/-- For `0 < ρ`, the radial retraction vanishes only at `0`. -/
lemma eq_zero_of_radialRetraction_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {v : V}
    (hv : radialRetraction ρ v = 0) : v = 0 := by
  by_contra h0
  rw [radialRetraction, smul_eq_zero] at hv
  exact (lt_min one_pos (div_pos hρ (norm_pos_iff.2 h0))).ne' (hv.resolve_right h0)

/-- For `0 < ρ`, the radial retraction is continuous. -/
lemma continuous_radialRetraction {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (radialRetraction (V := V) ρ) := by
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  rcases eq_or_ne v 0 with rfl | h0
  · have h : radialRetraction (V := V) ρ =ᶠ[𝓝 0] id := by
      filter_upwards [ball_mem_nhds (0 : V) hρ] with w hw
      exact radialRetraction_of_norm_lt (by simpa using hw)
    exact continuousAt_id.congr h.symm
  · exact (continuousAt_const.min (continuousAt_const.div continuousAt_id.norm
      (norm_ne_zero_iff.2 h0))).smul continuousAt_id

/-- A continuous disc `Bd` with `Bd 0` in an open set `U` agrees near `0` with a continuous disc
with values in `U`, which meets a set `Z` only at `0` whenever `Bd` does. -/
theorem exists_disc_mem_of_isOpen {X : Type*} [TopologicalSpace X] {k : ℕ}
    (Bd : C(Fin k → ℂ, X)) {U : Set X} (hU : IsOpen U) (h0 : Bd 0 ∈ U) :
    ∃ ρ > 0, ∃ Bt : C(Fin k → ℂ, X), (∀ w, Bt w ∈ U) ∧ (∀ w, ‖w‖ < ρ → Bt w = Bd w) ∧
      ∀ Z : Set X, (∀ v, Bd v ∈ Z → v = 0) → ∀ w, Bt w ∈ Z → w = 0 := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 (hU.preimage Bd.continuous) 0 h0
  have hρ : 0 < δ / 2 := by positivity
  have hBU : ∀ w, Bd (radialRetraction (δ / 2) w) ∈ U := fun w ↦
    hδU (mem_ball_zero_iff.2 ((norm_radialRetraction_le hρ.le w).trans_lt (by linarith)))
  exact ⟨δ / 2, hρ, ⟨fun w ↦ Bd (radialRetraction (δ / 2) w),
    Bd.continuous.comp (continuous_radialRetraction hρ)⟩, hBU,
    fun w hw ↦ congrArg Bd (radialRetraction_of_norm_lt hw),
    fun Z hZ w hw ↦ eq_zero_of_radialRetraction_eq_zero hρ (hZ (radialRetraction (δ / 2) w) hw)⟩

end Retraction

section ChartFormula

variable {B : Type u} [TopologicalSpace B]
  {HB : Type*} [NormedAddCommGroup HB] [NormedSpace ℂ HB] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Q : B → Type u} [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)] [∀ x, TopologicalSpace (Q x)]
  [TopologicalSpace (TotalSpace F Q)] [FiberBundle F Q]

/-- The chart of the total space at a point `0_b` of the zero section, at a point `q` over the
base set of the trivialization at `b`: the chart of the base at `b`, and the fibre coordinate of
the trivialization. -/
lemma chartAt_zeroSection_apply (b : B) (q : TotalSpace F Q)
    (hq : q.proj ∈ (trivializationAt F Q b).baseSet) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := Q)
    chartAt (HB × F) (zeroSection F Q b) q =
      (chartAt HB b q.proj, ((trivializationAt F Q b) q).2) := by
  change chartAt (ModelProd HB F) (zeroSection F Q b) q = _
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply, zeroSection_proj, Trivialization.coe_coe]
  change (chartAt HB b ((trivializationAt F Q b) q).1, ((trivializationAt F Q b) q).2) = _
  rw [Trivialization.coe_fst _ ((Trivialization.mem_source _).2 hq)]

/-- For a disc `Bt` of the base, in the trivialization and chart domains at `b` near `0`, with
derivative `L` in the chart at `b`, and a section `σ` whose fibre coordinate has derivative `S` at
`Bt 0`, the chart reading of `σ ∘ Bt` at `0_b` has derivative `(L, S ∘ L)` at `0`. -/
theorem hasFDerivAt_chartAt_zeroSection_comp {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (σ : B → TotalSpace F Q) (hσp : ∀ y, (σ y).proj = y) (b : B)
    {Bt : D → B} {L : D →L[ℝ] HB} (hB : HasFDerivAt (fun w ↦ chartAt HB b (Bt w)) L 0)
    {S : HB →L[ℝ] F}
    (hS : HasFDerivAt (fun k ↦ ((trivializationAt F Q b) (σ ((chartAt HB b).symm k))).2) S
      (chartAt HB b (Bt 0)))
    (hU : ∀ᶠ w in 𝓝 0, Bt w ∈ (trivializationAt F Q b).baseSet ∩ (chartAt HB b).source) :
    letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := Q)
    HasFDerivAt (fun w ↦ chartAt (HB × F) (zeroSection F Q b) (σ (Bt w)))
      (L.prod (S.comp L)) 0 := by
  refine (hB.prodMk (hS.comp 0 hB)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with w hw
  have hw₁ : (σ (Bt w)).proj ∈ (trivializationAt F Q b).baseSet := by rw [hσp]; exact hw.1
  rw [chartAt_zeroSection_apply b _ hw₁, hσp]
  exact Prod.ext rfl (congrArg (fun y ↦ ((trivializationAt F Q b) (σ y)).2)
    ((chartAt HB b).left_inv hw.2).symm)

end ChartFormula

section LinearAlgebra

/-- If `S : E →L[ℂ] F'` has kernel `W`, complementary to the range of an injective real linear map
`L`, and `L` is complex linear modulo `W`, then `S ∘ L` is injective and complex linear. -/
theorem injective_and_map_smul_comp_of_isCompl {E F' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F'] [NormedSpace ℂ F'] {k : ℕ}
    {L : (Fin k → ℂ) →L[ℝ] E} (hinj : Function.Injective L) {W : Submodule ℂ E}
    (hc : IsCompl (LinearMap.range (L : (Fin k → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hl : ∀ (c : ℂ) (v : Fin k → ℂ), L (c • v) - c • L v ∈ W) {S : E →L[ℂ] F'}
    (hSW : ∀ w, S w = 0 ↔ w ∈ W) :
    Function.Injective (fun v ↦ S (L v)) ∧ ∀ (c : ℂ) v, S (L (c • v)) = c • S (L v) := by
  have hSL : ∀ w, S (L w) = 0 → w = 0 := fun w hw ↦ by
    have hmem : L w ∈ (LinearMap.range (L : (Fin k → ℂ) →ₗ[ℝ] E) ⊓ W.restrictScalars ℝ) :=
      ⟨⟨w, rfl⟩, (hSW _).1 hw⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hinj (by rw [hmem, map_zero])
  refine ⟨fun w w' h ↦ sub_eq_zero.1 (hSL _ ?_), fun c w ↦ ?_⟩
  · simp only [map_sub]
    exact sub_eq_zero.2 h
  · have h0 : S (L (c • w) - c • L w) = 0 := (hSW _).2 (hl c w)
    rwa [map_sub, sub_eq_zero, S.map_smul] at h0

end LinearAlgebra

section SectionCriterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P} {V : Set P} (hV : IsOpen V)
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {Q : V → Type u} [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)] [∀ x, TopologicalSpace (Q x)]
  [TopologicalSpace (TotalSpace F' Q)] [FiberBundle F' Q] [_root_.VectorBundle ℂ F' Q]
  (R : Type u) [CommRing R]

variable (E) in
/-- The charts of an open subset `V` of a charted space. -/
abbrev openChartedSpace : ChartedSpace E V :=
  (⟨V, hV⟩ : TopologicalSpace.Opens P).instChartedSpace

variable (E) in
/-- A section `σ` of a vector bundle `Q` on an open `V ⊆ P` is *transversal to the zero section
along `M`* if at each `x ∈ M` its fibre coordinate in the trivialization at `x`, read in the chart
of `V` at `x`, is differentiable at `x` with a complex linear derivative `S` whose kernel is the
tangent cone of `M` at `x` (the tangent space `T_x M`, for a submanifold). -/
def IsSectionTransversalAlong (σ : V → TotalSpace F' Q) (Z : Set P) : Prop :=
  letI := openChartedSpace E hV
  ∀ (x : P) (_ : x ∈ Z) (hxV : x ∈ V), ∃ S : E →L[ℂ] F',
    HasFDerivAt (fun k ↦ ((trivializationAt F' Q ⟨x, hxV⟩)
        (σ ((chartAt E (⟨x, hxV⟩ : V)).symm k))).2)
      ((S : E →L[ℂ] F').restrictScalars ℝ) (chartAt E x x) ∧
    ∀ w, S w = 0 ↔ w ∈ tangentConeAt ℝ (chartAt E x '' (Z ∩ (chartAt E x).source)) (chartAt E x x)

/-- The inclusion of an open subset, as a morphism of `TopCat`. -/
abbrev subtypeValHom (V : Set P) : TopCat.of V ⟶ P :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction `H^j(P, P - Z) → H^j(V, V - Z)` to a subset `V ⊆ P`. -/
abbrev restrictSubset (V Z : Set P) (j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) P Z j ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of V) (Subtype.val ⁻¹' Z) j :=
  cohomologyWithSupports.pullback R (ModuleCat.of R R) (subtypeValHom V) Z j

omit [FiniteDimensional ℂ F'] [∀ x, Module ℂ (Q x)] [∀ x, TopologicalSpace (Q x)]
  [FiberBundle F' Q] [_root_.VectorBundle ℂ F' Q] in
/-- If `u ∈ H^{2k}(P, P - M)` restricts on `V` to `σ^* u_Q`, then representing cocycles of `u` and
of `u_Q` agree on a simplex `τ` of `V` whose faces avoid `M`, pushed to `P` and by `σ`. -/
theorem eval_single_eq_eval_single_comp_of_restrictSubset_eq
    (σ : V → TotalSpace F' Q) (hσc : Continuous σ)
    (hσ0 : σ ⁻¹' range (zeroSection F' Q) ⊆ Subtype.val ⁻¹' M)
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F' Q))
      (range (zeroSection F' Q)) (2 * Module.finrank ℂ F' : ℕ)}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F' : ℕ)}
    (hu : (restrictSubset R V M (2 * Module.finrank ℂ F' : ℕ)).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (TopCat.ofHom ⟨σ, hσc⟩)
          (range (zeroSection F' Q)) _ ≫
        cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of V) hσ0 _ ≫
        eqToHom rfl).hom uQ)
    {α : Simplex P (2 * Module.finrank ℂ F') → R}
    (hα : α ∈ relCocycles R (Mᶜ : Set P) (2 * Module.finrank ℂ F'))
    (hrep : relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F') u =
      Submodule.Quotient.mk ⟨α, hα⟩)
    {αQ : Simplex (TopCat.of (TotalSpace F' Q)) (2 * Module.finrank ℂ F') → R}
    (hαQ : αQ ∈ relCocycles R ((range (zeroSection F' Q))ᶜ : Set (TopCat.of (TotalSpace F' Q)))
      (2 * Module.finrank ℂ F'))
    (hrepQ : relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F' Q)) _
      (2 * Module.finrank ℂ F') uQ = Submodule.Quotient.mk ⟨αQ, hαQ⟩)
    (τ : Simplex (TopCat.of V) (2 * Module.finrank ℂ F'))
    (hτ : ∀ t : stdSimplex ℝ (Fin (2 * Module.finrank ℂ F' + 1)), (∃ i, t i = 0) →
      τ t ∈ ((Subtype.val ⁻¹' M)ᶜ : Set (TopCat.of V)))
    {τP : Simplex P (2 * Module.finrank ℂ F')} (hτP : (subtypeValHom V).hom.comp τ = τP) :
    eval α (single τP 1) = eval αQ (single ((⟨σ, hσc⟩ : C(V, TotalSpace F' Q)).comp τ) 1) := by
  subst hτP
  have hsubι : ((subtypeValHom V ⁻¹' M)ᶜ : Set (TopCat.of V)) ⊆
      subtypeValHom V ⁻¹' (Mᶜ : Set P) := fun _ h ↦ h
  have hsubσ : ((σ ⁻¹' range (zeroSection F' Q))ᶜ : Set (TopCat.of V)) ⊆
      (TopCat.ofHom (⟨σ, hσc⟩ : C(V, TotalSpace F' Q))) ⁻¹'
        ((range (zeroSection F' Q))ᶜ : Set (TopCat.of (TotalSpace F' Q))) := fun _ h ↦ h
  have hsub1 : ((Subtype.val ⁻¹' M)ᶜ : Set (TopCat.of V)) ⊆
      (𝟙 (TopCat.of V)) ⁻¹' ((σ ⁻¹' range (zeroSection F' Q))ᶜ) :=
    compl_subset_compl.mpr hσ0
  have hαι := cochainPullback_mem_relCocycles (subtypeValHom V) hsubι hα
  have hασ' := cochainPullback_mem_relCocycles
    (TopCat.ofHom (⟨σ, hσc⟩ : C(V, TotalSpace F' Q))) hsubσ hαQ
  have hασ := cochainPullback_mem_relCocycles (𝟙 (TopCat.of V)) hsub1 hασ'
  have hclass : (Submodule.Quotient.mk ⟨_, hαι⟩ :
      relCohomology R ((Subtype.val ⁻¹' M)ᶜ : Set (TopCat.of V)) (2 * Module.finrank ℂ F')) =
      Submodule.Quotient.mk ⟨_, hασ⟩ := by
    have e := congrArg (relativeSingularCohomologyEquiv R
      ((Subtype.val ⁻¹' M)ᶜ : Set (TopCat.of V)) (2 * Module.finrank ℂ F')) hu
    simp only [eqToHom_refl, Category.comp_id] at e
    have eL := relativeSingularCohomologyEquiv_map (R := R) (subtypeValHom V) hsubι
      (2 * Module.finrank ℂ F') u
    have eσ := relativeSingularCohomologyEquiv_map (R := R)
      (TopCat.ofHom (⟨σ, hσc⟩ : C(V, TotalSpace F' Q))) hsubσ (2 * Module.finrank ℂ F') uQ
    have e1 := relativeSingularCohomologyEquiv_map (R := R) (𝟙 (TopCat.of V)) hsub1
      (2 * Module.finrank ℂ F')
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R)
        (TopCat.ofHom (⟨σ, hσc⟩ : C(V, TotalSpace F' Q))) (range (zeroSection F' Q))
        (2 * Module.finrank ℂ F' : ℕ)).hom uQ)
    rw [hrep, relCohomologyMap_mk] at eL
    have e1' := e1.trans (congrArg (relCohomologyMap R (𝟙 (TopCat.of V)) hsub1 _) eσ)
    rw [hrepQ, relCohomologyMap_mk, relCohomologyMap_mk] at e1'
    exact eL.symm.trans (e.trans e1')
  have hrel := eval_single_eq_zero_of_mem_relCoboundaries (R := R) τ hτ
  have e1 : eval α (single ((subtypeValHom V).hom.comp τ) 1) =
      relEval (single τ 1) hrel (Submodule.Quotient.mk ⟨_, hαι⟩) := by
    rw [relEval_mk, eval_cochainPullback_single]
  rw [e1, hclass, relEval_mk, eval_cochainPullback_single, eval_cochainPullback_single]
  rfl

/-- **Disc criterion through a section.** Let `σ` be a section of a vector bundle `Q` of rank `k`
on an open `V ⊆ P` vanishing exactly on `M ⊆ V` and transversal to the zero section along `M`,
and `u ∈ H^{2k}(P, P - M)` a class whose restriction to `V` is `σ^* u_Q`, `u_Q` a Thom class of
`Q`. Then a representing cocycle of `u` takes the value `1` on `B ∘ Δ` for every oriented affine
simplex `Δ` around `0` in `ℂ^k` and every transversal disc `B` of `M`. -/
theorem eval_comp_affineSimplex_eq_one_of_isSectionTransversalAlong {k : ℕ}
    (hk : Module.finrank ℂ F' = k) (σ : V → TotalSpace F' Q) (hσc : Continuous σ)
    (hσp : ∀ y, (σ y).proj = y) (hMV : M ⊆ V) (hσM : ∀ y : V, y.1 ∈ M → σ y = zeroSection F' Q y)
    (hσ0 : σ ⁻¹' range (zeroSection F' Q) ⊆ Subtype.val ⁻¹' M)
    (hσd : IsSectionTransversalAlong E hV σ M)
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F' Q))
      (range (zeroSection F' Q)) (2 * Module.finrank ℂ F' : ℕ)}
    (huQ : IsThomClass (R := R) F' Q uQ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * k : ℕ)}
    (hu : (restrictSubset R V M (2 * k : ℕ)).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (TopCat.ofHom ⟨σ, hσc⟩)
          (range (zeroSection F' Q)) _ ≫
        cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of V) hσ0 _ ≫
        eqToHom (by rw [hk])).hom uQ)
    {α : Simplex P (2 * k) → R} (hα : α ∈ relCocycles R (Mᶜ : Set P) (2 * k))
    (hrep : relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * k) u =
      Submodule.Quotient.mk ⟨α, hα⟩)
    {x : P} (hx : x ∈ M) (Bd : C(Fin k → ℂ, P)) (hB0 : Bd 0 = x) (hBM : ∀ v, Bd v ∈ M → v = 0)
    {L : (Fin k → ℂ) →L[ℝ] E} (hB : HasFDerivAt (fun v ↦ chartAt E x (Bd v)) L 0)
    (hinj : Function.Injective L) (W : Submodule ℂ E)
    (hTW : tangentConeAt ℝ (chartAt E x '' (M ∩ (chartAt E x).source)) (chartAt E x x) = W)
    (hc : IsCompl (LinearMap.range (L : (Fin k → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hl : ∀ (c : ℂ) (v : Fin k → ℂ), L (c • v) - c • L v ∈ W)
    {v : Fin (2 * k + 1) → (Fin k → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis k) v) :
    eval α (single (Bd.comp (affineSimplex v)) 1) = 1 := by
  subst hk
  let _ := openChartedSpace E hV
  have hxV : x ∈ V := hMV hx
  set b : V := ⟨x, hxV⟩
  obtain ⟨⟨αQ, hαQ⟩, hrepQ⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F' Q))
      ((range (zeroSection F' Q))ᶜ) (2 * Module.finrank ℂ F') uQ)
  set U : Set V := (trivializationAt F' Q b).baseSet ∩ (chartAt E b).source
  have hUo : IsOpen (Subtype.val '' U : Set P) := hV.isOpenMap_subtype_val _
    ((trivializationAt F' Q b).open_baseSet.inter (chartAt E b).open_source)
  have hxU : Bd 0 ∈ (Subtype.val '' U : Set P) :=
    ⟨b, ⟨mem_baseSet_trivializationAt F' Q b, mem_chart_source E b⟩, hB0.symm⟩
  obtain ⟨ρ, hρ0, Bd', hBU, hBt, hBM'⟩ := exists_disc_mem_of_isOpen Bd hUo hxU
  let Bt : C(Fin (Module.finrank ℂ F') → ℂ, V) :=
    ⟨fun w ↦ ⟨Bd' w, (hBU w).elim fun y hy ↦ hy.2 ▸ y.2⟩, Bd'.continuous.subtype_mk _⟩
  have hBtU : ∀ w, Bt w ∈ U := fun w ↦ by
    obtain ⟨y, hy, hyw⟩ := hBU w
    rwa [show Bt w = y from Subtype.ext hyw.symm]
  have hBtM : ∀ w, (Bt w : P) ∈ M → w = 0 := hBM' M hBM
  have hBt0 : Bt 0 = b := Subtype.ext ((hBt 0 (by simpa using hρ0)).trans hB0)
  obtain ⟨S, hS, hSker⟩ := hσd x hx hxV
  have hB' : HasFDerivAt (fun w ↦ chartAt E b (Bt w)) L 0 := hB.congr_of_eventuallyEq <| by
    filter_upwards [ball_mem_nhds (0 : Fin (Module.finrank ℂ F') → ℂ) hρ0] with w hw
    exact congrArg (chartAt E x) (hBt w (by simpa using hw))
  have hS' : HasFDerivAt (fun k ↦ ((trivializationAt F' Q b) (σ ((chartAt E b).symm k))).2)
      (S.restrictScalars ℝ) (chartAt E b (Bt 0)) := by
    rwa [hBt0]
  have hSL := injective_and_map_smul_comp_of_isCompl hinj hc hl (S := S)
    fun w ↦ by rw [hSker, hTW]; rfl
  obtain ⟨c, hc0, hcρ⟩ := exists_range_affineSimplex_smul_subset_ball v hρ0
  have hvc := hv.smul hc0
  have hτB : (subtypeValHom V).hom.comp (Bt.comp (affineSimplex (c • v))) =
      Bd.comp (affineSimplex (c • v)) := by
    ext t
    exact hBt _ (mem_ball_zero_iff.1 (hcρ ⟨t, rfl⟩))
  rw [eval_comp_affineSimplex_smul Bd hBM R hα hv hc0]
  refine (eval_single_eq_eval_single_comp_of_restrictSubset_eq R σ hσc hσ0 hu hα hrep hαQ
    hrepQ.symm (Bt.comp (affineSimplex (c • v)))
    (fun t ht hM ↦ hvc.affineSimplex_ne_zero t ht (hBtM _ hM)) hτB).trans ?_
  let _ := totalSpaceChartedSpace (HB := E) (F := F') (E := Q)
  exact huQ.eval_comp_affineSimplex_eq_one R hαQ hrepQ.symm b
    ((⟨σ, hσc⟩ : C(V, TotalSpace F' Q)).comp Bt) ((congrArg σ hBt0).trans (hσM b hx))
    (fun w hw ↦ hBtM w (hσ0 hw))
    (hasFDerivAt_chartAt_zeroSection_comp σ hσp b hB' hS' (.of_forall hBtU)) hSL.1 hSL.2 hvc

end SectionCriterion

section Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P} {V : Set P} (hV : IsOpen V)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
  {Q : V → Type u} [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)] [∀ x, TopologicalSpace (Q x)]
  [TopologicalSpace (TotalSpace F' Q)] [FiberBundle F' Q] [_root_.VectorBundle ℂ F' Q]
  (R : Type u) [CommRing R]

/-- **The pull-back of a Thom class by a transversal section is the orientation class.** Let
`M ⊆ P` have a tubular neighbourhood `φ : N → P` of rank `d` compatible with the complex
orientations, and let `σ` be a section of a vector bundle `Q` of rank `d` on an open `V ⊇ M`,
vanishing exactly on `M` and transversal to the zero section along `M`
(`IsSectionTransversalAlong`). If `u ∈ H^{2d}(P, P - M)` restricts on `V` to `σ^* u_Q`, `u_Q` a
Thom class of `Q`, then `u` is the orientation class `u_{M,P}`. The section need only be
continuous, and differentiable at the points of `M`. -/
theorem isOrientationClass_of_isSectionTransversalAlong (φ : TubularNeighbourhood F N)
    (hφ : φ.IsOrientationCompatible (E := E)) (hk : Module.finrank ℂ F' = Module.finrank ℂ F)
    (σ : V → TotalSpace F' Q) (hσc : Continuous σ) (hσp : ∀ y, (σ y).proj = y) (hMV : M ⊆ V)
    (hσM : ∀ y : V, y.1 ∈ M → σ y = zeroSection F' Q y)
    (hσ0 : σ ⁻¹' range (zeroSection F' Q) ⊆ Subtype.val ⁻¹' M)
    (hσd : IsSectionTransversalAlong E hV σ M)
    {uQ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F' Q))
      (range (zeroSection F' Q)) (2 * Module.finrank ℂ F' : ℕ)}
    (huQ : IsThomClass (R := R) F' Q uQ)
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : (restrictSubset R V M (2 * Module.finrank ℂ F : ℕ)).hom u =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (TopCat.ofHom ⟨σ, hσc⟩)
          (range (zeroSection F' Q)) _ ≫
        cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of V) hσ0 _ ≫
        eqToHom (by rw [hk])).hom uQ) :
    IsOrientationClass E R φ u := by
  refine ⟨hφ, ?_⟩
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u)
  rw [isThomClass_thomPullback_iff R φ hα hrep.symm]
  intro x ψ v hv
  obtain ⟨L, hL, hinj, W, hTW, hc, hl⟩ := hφ.exists_hasFDerivAt_fibreDisc x ψ
  exact eval_comp_affineSimplex_eq_one_of_isSectionTransversalAlong hV R hk σ hσc hσp hMV hσM
    hσ0 hσd huQ hu hα hrep.symm x.2 (φ.fibreDisc x ψ) (φ.fibreDisc_zero x ψ)
    (φ.eq_zero_of_fibreDisc_mem x ψ) hL hinj W hTW hc hl hv

end Orientation

end MMP
