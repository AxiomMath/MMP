module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksPresentation
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksEmbedding
public import MMP.Analysis.InnerProductSpace.RangeProjection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNonvanishing

/-!
# Local frames of the normal bundle in a Hermitian embedding, for Stacks vector bundles

Let `ι : 𝐕(ℰ)(ℂ) → ℂᵐ` be a continuous map whose chart expressions `Φ_c(y) : ℂᵉ → ℂᵐ`,
`ι(φ_c⁻¹(y, w)) = Φ_c(y) w`, are linear (`MMP.Modules.exists_hermitianEmbedding`). For a local
regular presentation `σ|_W = M f` on `W ⊆ V`, `c = (V, b)`, the maps
`K(y) = Φ_c(y) ∘ M(y) : ℂᵈ → ℂᵐ` depend continuously on `y ∈ W(ℂ)`, and at the complex points
of `X` in `W` they are injective with range `Φ_c(y)(N_y)`, the image of the normal fibre; this
image does not depend on the chart.

## Main definitions

* `MMP.Modules.evalMatrixExt`: the matrix `M(y)` of values, `0` off `W(ℂ)`.
* `MMP.Modules.localFrame`: `K(y) = Φ_c(y) ∘ M(y)`.

## Main results

* `MMP.Modules.map_normalFibre_eq`: `Φ_c(y)(N_{c,y}) = Φ_{c'}(y)(N_{c',y})`.
* `MMP.Modules.range_localFrame`, `MMP.Modules.injective_localFrame`,
  `MMP.Modules.continuousOn_localFrame`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Bundle Set Topology

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)
open scoped Matrix

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] {e d m : ℕ}

/-- The matrix `M(y)` of values of `M` at `y`, as a continuous linear map (`0` off `W(ℂ)`). -/
def evalMatrixExt (W : Y.Opens) (M : Fin e → Fin d → Γ(Y, W)) (y : UnderlyingSpace ℂ Y) :
    (Fin d → ℂ) →L[ℂ] (Fin e → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of fun a b ↦ evalExt W (M a b) y))

/-- On `W(ℂ)`, `evalMatrixExt W M y` agrees with `evalMatrix y hy M`. -/
lemma evalMatrixExt_apply {W : Y.Opens} (M : Fin e → Fin d → Γ(Y, W)) {y : UnderlyingSpace ℂ Y}
    (hy : ⊤ ≤ y.toHom ⁻¹ᵁ W) (v : Fin d → ℂ) :
    evalMatrixExt W M y v = evalMatrix y hy M v := by
  simp only [evalMatrixExt, evalMatrix, LinearMap.coe_toContinuousLinearMap', evalExt_of_le _ hy]

/-- `y ↦ M(y)` is continuous on `W(ℂ)`. -/
lemma continuousOn_evalMatrixExt (W : Y.Opens) (M : Fin e → Fin d → Γ(Y, W)) :
    ContinuousOn (evalMatrixExt W M) {y | ⊤ ≤ y.toHom ⁻¹ᵁ W} := by
  refine continuousOn_clm_apply.2 fun v ↦ continuousOn_pi.2 fun a ↦ ?_
  refine ContinuousOn.congr (f := fun y ↦ ∑ b, evalExt W (M a b) y * v b) ?_ fun y _ ↦ ?_
  · exact continuousOn_finset_sum _ fun b _ ↦ (continuousOn_evalExt W _).mul continuousOn_const
  · simp only [evalMatrixExt, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]

variable {E : Y.Modules} [E.IsQuasicoherent]
  {ιE : UnderlyingSpace ℂ (totalSpace E) → EuclideanSpace ℂ (Fin m)}
  {Φ : Chart E e → UnderlyingSpace ℂ Y → (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin m)}

/-- `Φ_c(y) = Φ_{c'}(y) ∘ g(y)`, `g = transition c c'`. -/
lemma apply_eq_apply_transition
    (hΦ : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (w : Fin e → ℂ), ιE (chartInv c y hy w) = Φ c y w)
    (c c' : Chart E e) {y : UnderlyingSpace ℂ Y} (hy : y ∈ chartBase c) (hy' : y ∈ chartBase c')
    (w : Fin e → ℂ) : Φ c y w = Φ c' y (transition c c' y *ᵥ w) := by
  rw [← hΦ c y hy, ← hΦ c' y hy', chartInv_eq_chartInv c c' hy hy']

/-- On `chartBase c ∩ chartBase c'`, the range of `Φ_c(y)` is contained in that of `Φ_{c'}(y)`. -/
lemma range_le_range
    (hΦ : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (w : Fin e → ℂ), ιE (chartInv c y hy w) = Φ c y w)
    (c c' : Chart E e) {y : UnderlyingSpace ℂ Y} (hy : y ∈ chartBase c)
    (hy' : y ∈ chartBase c') :
    LinearMap.range (Φ c y).toLinearMap ≤ LinearMap.range (Φ c' y).toLinearMap := by
  rintro _ ⟨w, rfl⟩
  exact ⟨_, (apply_eq_apply_transition hΦ c c' hy hy' w).symm⟩

/-- The image `Φ_c(y)(N_{c,y})` of the normal fibre does not depend on the chart. -/
lemma map_normalFibre_eq
    (hΦ : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (w : Fin e → ℂ), ιE (chartInv c y hy w) = Φ c y w)
    (i : X ⟶ Y) [i.IsOver (Spec (.of ℂ))] [IsClosedImmersion i]
    (hi : IsRegularClosedImmersionOfCodim i d)
    {σ : Y ⟶ totalSpace E} (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker)
    (c c' : Chart E e) (x : UnderlyingSpace ℂ X)
    (hc : mapFun i x ∈ chartBase c) (hc' : mapFun i x ∈ chartBase c') :
    (normalFibre σ c (mapFun i x)).map (Φ c (mapFun i x)).toLinearMap =
      (normalFibre σ c' (mapFun i x)).map (Φ c' (mapFun i x)).toLinearMap := by
  rw [normalFibre_eq_map_transition i hi hσ hs c c' x hc hc', ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext fun w ↦ apply_eq_apply_transition hΦ c c' hc hc' w

variable (Φ) in
/-- The local frame `K(y) = Φ_c(y) ∘ M(y) : ℂᵈ → ℂᵐ` of a presentation `σ|_W = M f`. -/
def localFrame (c : Chart E e) {W : Y.Opens} (M : Fin e → Fin d → Γ(Y, W))
    (y : UnderlyingSpace ℂ Y) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  Φ c y ∘L evalMatrixExt W M y ∘L
    (EuclideanSpace.equiv (Fin d) ℂ : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ))

/-- `y ↦ K(y)` is continuous on `chartBase c ∩ W(ℂ)` when every `Φ_c` is continuous on
`chartBase c`. -/
lemma continuousOn_localFrame (hΦc : ∀ c : Chart E e, ContinuousOn (Φ c) (chartBase c))
    (c : Chart E e) {W : Y.Opens} (M : Fin e → Fin d → Γ(Y, W)) :
    ContinuousOn (localFrame Φ c M) (chartBase c ∩ {y | ⊤ ≤ y.toHom ⁻¹ᵁ W}) :=
  ((hΦc c).mono inter_subset_left).clm_comp
    (((continuousOn_evalMatrixExt W M).mono inter_subset_right).clm_comp continuousOn_const)

/-- If every `Φ_c(y)` is injective, then `K(y)` is injective at a point `y` of a local regular
presentation `σ|_W = M f`. -/
lemma injective_localFrame
    (hΦi : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y), y ∈ chartBase c →
      Function.Injective (Φ c y))
    {σ : Y ⟶ totalSpace E} {c : Chart E e} {y : UnderlyingSpace ℂ Y} (hyc : y ∈ chartBase c)
    {W : Y.Opens} {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} {hyW : ⊤ ≤ y.toHom ⁻¹ᵁ W}
    {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)} {f : Fin d → Γ(Y, W)}
    (h : IsLocalRegularPresentation σ c y hWc hyW M G f) :
    Function.Injective (localFrame Φ c M y) := by
  intro v v' hvv'
  simp only [localFrame, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe] at hvv'
  have h1 := hΦi c y hyc hvv'
  rw [evalMatrixExt_apply M hyW, evalMatrixExt_apply M hyW] at h1
  exact (EuclideanSpace.equiv (Fin d) ℂ).injective (injective_evalMatrix h h1)

/-- At a point `y` of a local regular presentation `σ|_W = M f`, the range of `K(y)` is the image
`Φ_c(y)(N_y)` of the normal fibre. -/
lemma range_localFrame {σ : Y ⟶ totalSpace E} {c : Chart E e} {y : UnderlyingSpace ℂ Y}
    {W : Y.Opens} {hWc : W ≤ σ ⁻¹ᵁ (proj E ⁻¹ᵁ c.1.1)} {hyW : ⊤ ≤ y.toHom ⁻¹ᵁ W}
    {M : Fin e → Fin d → Γ(Y, W)} {G : Fin d → Fin e → Γ(Y, W)} {f : Fin d → Γ(Y, W)}
    (h : IsLocalRegularPresentation σ c y hWc hyW M G f) :
    LinearMap.range (localFrame Φ c M y).toLinearMap =
      (normalFibre σ c y).map (Φ c y).toLinearMap := by
  rw [normalFibre_eq_range h]
  have h1 : (evalMatrixExt W M y).toLinearMap = evalMatrix y hyW M :=
    LinearMap.ext fun v ↦ evalMatrixExt_apply M hyW v
  have h2 : LinearMap.range ((evalMatrixExt W M y).toLinearMap ∘ₗ
      ((EuclideanSpace.equiv (Fin d) ℂ : EuclideanSpace ℂ (Fin d) →L[ℂ] (Fin d → ℂ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℂ] (Fin d → ℂ))) = LinearMap.range (evalMatrix y hyW M) := by
    rw [h1]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (EuclideanSpace.equiv (Fin d) ℂ).surjective)
  rw [← h2, ← LinearMap.range_comp]
  rfl

end MMP.Modules
