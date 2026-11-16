module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Unique.StacksCompare
public import MMP.Topology.VectorBundle.BundleMap
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksFrame
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksUnique

/-!
# Local comparison maps between two orientation data (Stacks bundles)

Let `D₁ = (ℰ₁, σ₁, V₁, Q₁)` and `D₂ = (ℰ₂, σ₂, V₂, Q₂)` be orientation data of a regular closed
imbedding `i : X → Y` of codimension `d` (`MMP.Modules.RegularImbeddingOrientationDatum`), and pull
`Q₁`, `Q₂` back to `V₁ ∩ V₂`. Near every point `x₀` of `X(ℂ)` there is a continuous fibrewise
linear map `φ : Q₁ → Q₂` carrying `σ̄₁` to `σ̄₂`: with one regular sequence `f` presenting both
sections, `σ_k = M_k f`, the maps `A_k(y) = q_k(y) ∘ M_k(y) : ℂᵈ → Q_k(y)` satisfy `σ̄_k = A_k f`,
`A₁(x₀)` is invertible, and `φ = A₂ A₁⁻¹`. At every point `x` of `X(ℂ)` near `x₀` the map `φ(x)`
is *compatible with presentations*: `φ(x) ∘ A₁' = A₂'` for every common presentation of `σ₁`,
`σ₂` at `x`, in any charts. This condition is affine, so it survives gluing, and it forces `φ(x)`
to be an isomorphism.

## Main definitions

* `MMP.Modules.RegularImbeddingOrientationDatum.chartL`: the quotient map `ℂᵉ → Q(y)` in a
  chart.
* `MMP.Modules.RegularImbeddingOrientationDatum.IsPresentationCompatible`.

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.exists_local_bundleMap`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Bundle Topology Filter

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d : ℕ}

section chart

variable (D : RegularImbeddingOrientationDatum i d)

/-- A point of `W(ℂ)`, `W ⊆ σ⁻¹(π⁻¹V)`, lies in the chart domain `V(ℂ)`. -/
lemma top_le_preimage_of_le {c : Chart D.E D.rank} {W : Y.Opens}
    (hW : W ≤ D.σ ⁻¹ᵁ (proj D.E ⁻¹ᵁ c.1.1)) {y : UnderlyingSpace ℂ Y}
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ W) : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1 :=
  hy.trans (Scheme.Hom.preimage_mono _
    (hW.trans (preimage_preimage_proj_of_comp_eq_id D.comp_proj _).le))

/-- The quotient map `𝐕(ℰ)(ℂ)_y = ℂᵉ → Q(y)` in the chart `c` (`0` if `y` is not in the
chart). -/
def chartL (c : Chart D.E D.rank) (y : D.nbhd) : (Fin D.rank → ℂ) →ₗ[ℂ] D.Q y :=
  open Classical in
  if h : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1 then (D.fibre c y.1 h y.2).choose else 0

/-- The quotient of the point of `𝐕(ℰ)(ℂ)_y` with chart coordinates `w` is `chartL c y w`. -/
lemma quot_chartInv (c : Chart D.E D.rank) (y : D.nbhd) (h : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1)
    (w : Fin D.rank → ℂ) :
    D.quot ⟨chartInv c y.1 h w, by rw [mapFun_proj_chartInv]; exact y.2⟩ =
      ⟨y, D.chartL c y w⟩ := by
  rw [chartL, dite_eq_left h]
  exact (D.fibre c y.1 h y.2).choose_spec.1 w

/-- For `y ∈ X(ℂ)`, the kernel of `chartL c y` is complementary to the normal fibre of `σ`
at `y`. -/
lemma isCompl_ker_chartL (c : Chart D.E D.rank) (y : D.nbhd) (h : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1)
    (hy : y.1 ∈ range (UnderlyingSpace.map i)) :
    IsCompl (LinearMap.ker (D.chartL c y)) (normalFibre D.σ c y.1) := by
  rw [chartL, dite_eq_left h]
  exact (D.fibre c y.1 h y.2).choose_spec.2.2 hy

/-- **`σ̄` in a presentation**: if `σ = M f` on `W ⊆ σ⁻¹(π⁻¹V)`, then `σ̄(y) = q(y)(M(y) f(y))`
for `y ∈ W(ℂ) ∩ V`. -/
lemma sectionBar_eq_chartL {c : Chart D.E D.rank} {W : Y.Opens}
    (hWc : W ≤ D.σ ⁻¹ᵁ (proj D.E ⁻¹ᵁ c.1.1)) {k : ℕ}
    {M : Fin D.rank → Fin k → Γ(Y, W)} {f : Fin k → Γ(Y, W)}
    (hM : ∀ a, sectionCoord D.σ c hWc a = ∑ b, M a b * f b)
    (y : D.nbhd) (hyW : ⊤ ≤ y.1.toHom ⁻¹ᵁ W) :
    D.sectionBar y = ⟨y, D.chartL c y (evalMatrix y.1 hyW M fun c ↦ eval y.1 hyW (f c))⟩ := by
  have hy : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1 := D.top_le_preimage_of_le hWc hyW
  rw [← quot_chartInv D c y hy, sectionBar]
  congr 1
  refine Subtype.ext ?_
  refine (mapFun_eq_chartInv_coord D.comp_proj c y.1 hy).trans ?_
  congr 1
  funext a
  have := congrArg (evalRingHom y.1 hyW) (hM a)
  simp only [map_sum, map_mul, evalRingHom_apply] at this
  rw [evalMatrix_apply, ← eval_sectionCoord D.σ c hWc y.1 hyW a]
  exact this.trans (Finset.sum_congr rfl fun c _ ↦ rfl)

/-- Equal points of `𝐕(ℰ)(ℂ)` in two charts have equal images under the chart quotient maps. -/
lemma chartL_eq_of_chartInv_eq {c c' : Chart D.E D.rank} (y : D.nbhd)
    (h : ⊤ ≤ y.1.toHom ⁻¹ᵁ c.1.1) (h' : ⊤ ≤ y.1.toHom ⁻¹ᵁ c'.1.1)
    {w w' : Fin D.rank → ℂ} (hw : chartInv c y.1 h w = chartInv c' y.1 h' w') :
    D.chartL c y w = D.chartL c' y w' := by
  have := congrArg D.quot (Subtype.ext hw :
    (⟨chartInv c y.1 h w, by rw [mapFun_proj_chartInv]; exact y.2⟩ :
      {p : UnderlyingSpace ℂ (totalSpace D.E) // mapFun (proj D.E) p ∈ D.nbhd}) =
      ⟨chartInv c' y.1 h' w', by rw [mapFun_proj_chartInv]; exact y.2⟩)
  rw [quot_chartInv, quot_chartInv] at this
  exact TotalSpace.mk_inj.1 this

/-- The family `y ↦ τ ∘ q(y) ∘ M(y) : ℂᵏ → F` of a chart `c`, a presentation matrix `M` on `W`
and a trivialization `τ` of `Q`. -/
def chartFamily (c : Chart D.E D.rank) {W : Y.Opens} {k : ℕ} (M : Fin D.rank → Fin k → Γ(Y, W))
    (τ : Trivialization D.F (TotalSpace.proj : TotalSpace D.F D.Q → D.nbhd)) [τ.IsLinear ℂ]
    (y : D.nbhd) : (Fin k → ℂ) →L[ℂ] D.F :=
  LinearMap.toContinuousLinearMap (τ.linearMapAt ℂ y ∘ₗ D.chartL c y ∘ₗ
    (evalMatrixExt W M y.1).toLinearMap)

/-- `chartFamily c M τ` composed with a continuous `β` is continuous on any set `S` mapped into
`W(ℂ)` and the base set of `τ`. -/
lemma continuousOn_chartFamily (c : Chart D.E D.rank) {W : Y.Opens}
    (hWc : W ≤ D.σ ⁻¹ᵁ (proj D.E ⁻¹ᵁ c.1.1)) {k : ℕ} (M : Fin D.rank → Fin k → Γ(Y, W))
    (τ : Trivialization D.F (TotalSpace.proj : TotalSpace D.F D.Q → D.nbhd)) [τ.IsLinear ℂ]
    {Z : Type*} [TopologicalSpace Z] {β : Z → D.nbhd} (hβ : Continuous β) {S : Set Z}
    (hS : ∀ z ∈ S, ⊤ ≤ (β z).1.toHom ⁻¹ᵁ W ∧ β z ∈ τ.baseSet) :
    ContinuousOn (fun z ↦ D.chartFamily c M τ (β z)) S := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have hj : ∀ z ∈ S, ⊤ ≤ (β z).1.toHom ⁻¹ᵁ c.1.1 := fun z hz ↦
    D.top_le_preimage_of_le hWc (hS z hz).1
  rw [continuousOn_iff_continuous_domRestrict]
  let q : S → TotalSpace D.F D.Q := fun z ↦ D.quot
    ⟨chartInv c (β z.1).1 (hj z.1 z.2) (evalMatrixExt W M (β z.1).1 v),
      by rw [mapFun_proj_chartInv]; exact (β z.1).2⟩
  have hq : ∀ z : S, q z = ⟨β z.1, D.chartL c (β z.1) (evalMatrixExt W M (β z.1).1 v)⟩ :=
    fun z ↦ D.quot_chartInv c (β z.1) (hj z.1 z.2) _
  have hval : Continuous fun z : S ↦ (β z.1).1 :=
    continuous_subtype_val.comp (hβ.comp continuous_subtype_val)
  have hM : Continuous fun z : S ↦ evalMatrixExt W M (β z.1).1 v :=
    ((continuousOn_evalMatrixExt W M).comp_continuous hval fun z ↦ (hS z.1 z.2).1).clm_apply
      continuous_const
  let ζ : S → {x : UnderlyingSpace ℂ Y // ⊤ ≤ x.toHom ⁻¹ᵁ c.1.1} × (Fin D.rank → ℂ) :=
    fun z ↦ (⟨(β z.1).1, hj z.1 z.2⟩, evalMatrixExt W M (β z.1).1 v)
  have hζ : Continuous ζ := (hval.subtype_mk _).prodMk hM
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
  change _ = D.chartFamily c M τ (β z.1) v
  simp only [chartFamily, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, hq, τ.coe_linearMapAt_of_mem (hS z.1 z.2).2, ContinuousLinearMap.coe_coe]

end chart

variable (D₁ D₂ : RegularImbeddingOrientationDatum i d)

/-- The inclusion `V₁ ∩ V₂ ⊆ V₁`. -/
def interIncl₁ : C(↥(D₁.nbhd ∩ D₂.nbhd), D₁.nbhd) :=
  ContinuousMap.inclusion inter_subset_left

/-- The inclusion `V₁ ∩ V₂ ⊆ V₂`. -/
def interIncl₂ : C(↥(D₁.nbhd ∩ D₂.nbhd), D₂.nbhd) :=
  ContinuousMap.inclusion inter_subset_right

/-- A linear map `ψ : Q₁(y) → Q₂(y)` at `y ∈ V₁ ∩ V₂` is *compatible with presentations* if
`ψ ∘ q₁(y) ∘ M₁(y) = q₂(y) ∘ M₂(y)` for every common local regular presentation `σ₁ = M₁ f`,
`σ₂ = M₂ f` at `y`, in any charts `c₁`, `c₂`. -/
def IsPresentationCompatible (b : ↥(D₁.nbhd ∩ D₂.nbhd))
    (ψ : D₁.Q (interIncl₁ D₁ D₂ b) →ₗ[ℂ] D₂.Q (interIncl₂ D₁ D₂ b)) : Prop :=
  ∀ (c₁ : Chart D₁.E D₁.rank) (c₂ : Chart D₂.E D₂.rank) (W : Y.Opens)
    (hW₁ : W ≤ D₁.σ ⁻¹ᵁ (proj D₁.E ⁻¹ᵁ c₁.1.1)) (hW₂ : W ≤ D₂.σ ⁻¹ᵁ (proj D₂.E ⁻¹ᵁ c₂.1.1))
    (hxW : ⊤ ≤ b.1.toHom ⁻¹ᵁ W)
    (M₁ : Fin D₁.rank → Fin d → Γ(Y, W)) (G₁ : Fin d → Fin D₁.rank → Γ(Y, W))
    (M₂ : Fin D₂.rank → Fin d → Γ(Y, W)) (G₂ : Fin d → Fin D₂.rank → Γ(Y, W))
    (f : Fin d → Γ(Y, W)),
    IsLocalRegularPresentation D₁.σ c₁ b.1 hW₁ hxW M₁ G₁ f →
    IsLocalRegularPresentation D₂.σ c₂ b.1 hW₂ hxW M₂ G₂ f →
    ∀ v : Fin d → ℂ,
      ψ (D₁.chartL c₁ (interIncl₁ D₁ D₂ b) (evalMatrix b.1 hxW M₁ v)) =
        D₂.chartL c₂ (interIncl₂ D₁ D₂ b) (evalMatrix b.1 hxW M₂ v)

omit [X.Over (Spec (.of ℂ))] in
/-- A point of a subtype whose value lies in the image of `O` under `Subtype.val` lies in `O`. -/
lemma mem_of_val_mem_image {S : Set (UnderlyingSpace ℂ Y)} {O : Set S} {b : S}
    (hb : b.1 ∈ Subtype.val '' O) : b ∈ O :=
  Subtype.val_injective.mem_set_image.1 hb

/-- **Local comparison maps.** Near every point `x₀` of `X(ℂ)` there is a fibrewise linear map
`φ : Q₁ → Q₂` over `V₁ ∩ V₂`, continuous on the total space, carrying `σ̄₁` to `σ̄₂`, and
compatible with presentations at the points of `X(ℂ)`. -/
theorem exists_local_bundleMap [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    (x : UnderlyingSpace ℂ X) :
    ∃ O : Set (UnderlyingSpace ℂ Y), IsOpen O ∧ mapFun i x ∈ O ∧
      ∃ φ : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), D₁.Q (interIncl₁ D₁ D₂ b) →ₗ[ℂ] D₂.Q (interIncl₂ D₁ D₂ b),
        (∀ p : TotalSpace D₁.F (⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q), p.proj.1 ∈ O →
          ContinuousAt (totalSpaceMap D₂.F (E₁ := ⇑(interIncl₁ D₁ D₂) *ᵖ D₁.Q)
            (E₂ := ⇑(interIncl₂ D₁ D₂) *ᵖ D₂.Q) φ) p) ∧
        (∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), b.1 ∈ O → ∀ v,
          D₁.sectionBar (interIncl₁ D₁ D₂ b) = ⟨interIncl₁ D₁ D₂ b, v⟩ →
            D₂.sectionBar (interIncl₂ D₁ D₂ b) = ⟨interIncl₂ D₁ D₂ b, φ b v⟩) ∧
        (∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), b.1 ∈ O → b.1 ∈ range (UnderlyingSpace.map i) →
          IsPresentationCompatible D₁ D₂ b (φ b)) := by
  classical
  set ι₁ := interIncl₁ D₁ D₂
  set ι₂ := interIncl₂ D₁ D₂
  set x₀ := mapFun i x
  let b₀ : ↥(D₁.nbhd ∩ D₂.nbhd) :=
    ⟨x₀, D₁.range_subset_nbhd ⟨x, rfl⟩, D₂.range_subset_nbhd ⟨x, rfl⟩⟩
  set c₁ := chartAt D₁.E D₁.rank x₀
  set c₂ := chartAt D₂.E D₂.rank x₀
  obtain ⟨W, hW₁, hW₂, hxW, M₁, G₁, M₂, G₂, f, hP⟩ := exists_isLocalRegularPresentation_pair i hi
    D₁.comp_proj D₁.zeroLocus_eq D₂.comp_proj D₂.zeroLocus_eq c₁ c₂ x
    (mem_chartBase_chartAt D₁.E D₁.rank x₀) (mem_chartBase_chartAt D₂.E D₂.rank x₀)
  let τ₁ := trivializationAt D₁.F D₁.Q (ι₁ b₀)
  let τ₂ := trivializationAt D₂.F D₂.Q (ι₂ b₀)
  let S : Set ↥(D₁.nbhd ∩ D₂.nbhd) :=
    {b | ⊤ ≤ b.1.toHom ⁻¹ᵁ W ∧ ι₁ b ∈ τ₁.baseSet ∧ ι₂ b ∈ τ₂.baseSet}
  have hSo : IsOpen S :=
    ((isOpen_setOf_le_preimage W).preimage continuous_subtype_val).inter
      ((τ₁.open_baseSet.preimage ι₁.continuous).inter (τ₂.open_baseSet.preimage ι₂.continuous))
  have hb₀S : b₀ ∈ S := ⟨hxW, FiberBundle.mem_baseSet_trivializationAt D₁.F D₁.Q (ι₁ b₀),
    FiberBundle.mem_baseSet_trivializationAt D₂.F D₂.Q (ι₂ b₀)⟩
  let A₁ : ↥(D₁.nbhd ∩ D₂.nbhd) → (Fin d → ℂ) →L[ℂ] D₁.F :=
    fun b ↦ D₁.chartFamily c₁ M₁ τ₁ (ι₁ b)
  let A₂ : ↥(D₁.nbhd ∩ D₂.nbhd) → (Fin d → ℂ) →L[ℂ] D₂.F :=
    fun b ↦ D₂.chartFamily c₂ M₂ τ₂ (ι₂ b)
  have hA₁ : ContinuousOn A₁ S :=
    D₁.continuousOn_chartFamily c₁ hW₁ M₁ τ₁ ι₁.continuous fun b hb ↦ ⟨hb.1, hb.2.1⟩
  have hA₂ : ContinuousOn A₂ S :=
    D₂.continuousOn_chartFamily c₂ hW₂ M₂ τ₂ ι₂.continuous fun b hb ↦ ⟨hb.1, hb.2.2⟩
  let β : D₁.F ≃L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (D₁.finrank_F.trans (Module.finrank_fin_fun ℂ).symm)
  let Â : ↥(D₁.nbhd ∩ D₂.nbhd) → (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    fun b ↦ (β : D₁.F →L[ℂ] (Fin d → ℂ)) ∘L A₁ b
  have hÂ : ContinuousOn Â S := continuousOn_const.clm_comp hA₁
  let O' : Set ↥(D₁.nbhd ∩ D₂.nbhd) := S ∩ Â ⁻¹' {u | IsUnit u}
  have hO' : IsOpen O' := hÂ.isOpen_inter_preimage hSo Units.isOpen
  have hinj₀ : Function.Injective (Â b₀) := by
    intro u u' huu'
    apply injective_comp_evalMatrix (hP x hxW).1 (D₁.chartL c₁ (ι₁ b₀))
      (D₁.isCompl_ker_chartL c₁ (ι₁ b₀) (mem_chartBase_chartAt D₁.E D₁.rank x₀) ⟨x, rfl⟩)
    apply injective_linearMapAt τ₁ (FiberBundle.mem_baseSet_trivializationAt D₁.F D₁.Q (ι₁ b₀))
    simp only [LinearMap.comp_apply, ← evalMatrixExt_apply M₁ hxW]
    exact β.injective huu'
  have hb₀O' : b₀ ∈ O' := ⟨hb₀S, isUnit_of_injective_clm hinj₀⟩
  let Φ : ↥(D₁.nbhd ∩ D₂.nbhd) → D₁.F →L[ℂ] D₂.F :=
    fun b ↦ A₂ b ∘L Ring.inverse (Â b) ∘L (β : D₁.F →L[ℂ] (Fin d → ℂ))
  let φ : ∀ b : ↥(D₁.nbhd ∩ D₂.nbhd), D₁.Q (ι₁ b) →ₗ[ℂ] D₂.Q (ι₂ b) := fun b ↦
    τ₂.symmₗ ℂ (ι₂ b) ∘ₗ (Φ b : D₁.F →ₗ[ℂ] D₂.F) ∘ₗ τ₁.linearMapAt ℂ (ι₁ b)
  have hkey : ∀ b (hb : b ∈ O') (u : Fin d → ℂ),
      φ b (D₁.chartL c₁ (ι₁ b) (evalMatrix b.1 hb.1.1 M₁ u)) =
        D₂.chartL c₂ (ι₂ b) (evalMatrix b.1 hb.1.1 M₂ u) := by
    rintro b ⟨⟨hbW, hb₁, hb₂⟩, hu⟩ u
    rw [← evalMatrixExt_apply M₁ hbW, ← evalMatrixExt_apply M₂ hbW]
    change τ₂.symmₗ ℂ (ι₂ b) (A₂ b (Ring.inverse (Â b) (Â b u))) = _
    rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu]
    exact τ₂.symmₗ_linearMapAt hb₂ _
  refine ⟨Subtype.val '' O', (D₁.isOpen_nbhd.inter D₂.isOpen_nbhd).isOpenMap_subtype_val _ hO',
    ⟨b₀, hb₀O', rfl⟩, φ, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨⟨hpW, hp₁, hp₂⟩, hpu⟩ := mem_of_val_mem_image hp
    have hpS : S ∈ 𝓝 p.proj := hSo.mem_nhds ⟨hpW, hp₁, hp₂⟩
    refine continuousAt_totalSpaceMap_of_trivialization (τ₁.pullback ι₁) (τ₂.pullback ι₂) Φ φ
      hp₁ hp₂ ?_ ?_
    · have hinv : ContinuousAt (fun b ↦ Ring.inverse (Â b)) p.proj := by
        obtain ⟨u, hu⟩ := hpu
        have := NormedRing.inverse_continuousAt u
        rw [hu] at this
        exact this.comp (f := Â) (hÂ.continuousAt hpS)
      exact (hA₂.continuousAt hpS).clm_comp (hinv.clm_comp continuousAt_const)
    · filter_upwards [hO'.mem_nhds ⟨⟨hpW, hp₁, hp₂⟩, hpu⟩] with b ⟨⟨_, hb₁, hb₂⟩, _⟩ v
      refine (pullback_linearMapAt ι₂ τ₂ hb₂ (φ b v)).trans ?_
      refine (τ₂.linearMapAt_symmₗ hb₂ _).trans ?_
      exact congrArg (Φ b) (pullback_linearMapAt ι₁ τ₁ hb₁ v).symm
  · intro b hb v hv
    have hb' : b ∈ O' := mem_of_val_mem_image hb
    rw [D₁.sectionBar_eq_chartL hW₁ (hP x hxW).1.eq_M (ι₁ b) hb'.1.1] at hv
    rw [D₂.sectionBar_eq_chartL hW₂ (hP x hxW).2.eq_M (ι₂ b) hb'.1.1, ← TotalSpace.mk_inj.1 hv]
    exact congrArg (TotalSpace.mk (ι₂ b)) (hkey b hb' _).symm
  · rintro ⟨y, hy⟩ hb ⟨x', rfl⟩ c₁' c₂' W' hW₁' hW₂' hxW' M₁' G₁' M₂' G₂' f' h₁' h₂' v
    have hb' := mem_of_val_mem_image hb
    obtain ⟨k₁, k₂⟩ := hP x' hb'.1.1
    obtain ⟨T, hT⟩ := IsLocalRegularPresentation.exists_chartInv_eq_pair D₁.comp_proj
      D₂.comp_proj k₁ k₂ h₁' h₂' (D₁.top_le_preimage_of_le hW₁ hb'.1.1)
      (D₂.top_le_preimage_of_le hW₂ hb'.1.1) (D₁.top_le_preimage_of_le hW₁' hxW')
      (D₂.top_le_preimage_of_le hW₂' hxW')
    exact (congrArg (φ _) (D₁.chartL_eq_of_chartInv_eq (ι₁ ⟨_, hy⟩) _ _ (hT v).1)).trans
      ((hkey _ hb' (T v)).trans (D₂.chartL_eq_of_chartInv_eq (ι₂ ⟨_, hy⟩) _ _ (hT v).2).symm)

end RegularImbeddingOrientationDatum

end MMP.Modules
