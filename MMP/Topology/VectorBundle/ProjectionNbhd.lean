module

public import MMP.Topology.VectorBundle.ProjectionImageBundle
public import MMP.Analysis.CStarAlgebra.SpectralProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Extending a family of projections from a subset to a neighbourhood

Let `A : B → (V →L[ℂ] V)` be a continuous family of self-adjoint operators on a
finite-dimensional complex inner product space, which on a subset `X ⊆ B` are projections of
rank `r`. Then on an open neighbourhood `U` of `X` the spectral projections of `A` form a
continuous family of projections of rank `r` (`MMP.ProjectionFamily`), equal to
`A` on `X`, with `range (P y) ⊆ range (A y)`.

## Main results

* `MMP.exists_projectionFamily_nhds`
-/

@[expose] public noncomputable section

open Set Topology Filter

namespace MMP

variable {B V F : Type*} [TopologicalSpace B] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Extending projections to a neighbourhood.** A continuous family `A` of self-adjoint
operators which on `X` are projections of rank `dim F` agrees on `X` with a continuous family of
projections of rank `dim F` on an open neighbourhood `U` of `X`, whose ranges lie in those of
`A`. -/
theorem exists_projectionFamily_nhds {A : B → V →L[ℂ] V} (hA : Continuous A)
    (hsa : ∀ b, IsSelfAdjoint (A b)) {X : Set B}
    (hX : ∀ x ∈ X, IsIdempotentElem (A x) ∧
      Module.finrank ℂ (LinearMap.range (A x).toLinearMap) = Module.finrank ℂ F) :
    ∃ (U : Set B) (_ : IsOpen U) (_ : X ⊆ U) (P : ProjectionFamily ℂ U V F),
      (∀ x : U, x.1 ∈ X → P x = A x) ∧
        ∀ y : U, LinearMap.range (P y).toLinearMap ≤ LinearMap.range (A y).toLinearMap := by
  set U₁ : Set B := {b | ‖A b * A b - A b‖ < 1 / 8}
  have hU₁ : IsOpen U₁ := isOpen_lt (by fun_prop) continuous_const
  set S : B → V →L[ℂ] V := fun b ↦ spectralProj (A b)
  have hnormal : ∀ b, IsStarNormal (A b) := fun b ↦ (hsa b).isStarNormal
  have hSidem : ∀ b ∈ U₁, IsIdempotentElem (S b) := fun b hb ↦
    isIdempotentElem_spectralProj (hnormal b) (le_of_lt hb)
  have hScont : ContinuousOn S U₁ :=
    continuousOn_spectralProj hA.continuousOn (fun b _ ↦ hnormal b) fun b hb ↦ le_of_lt hb
  set U : Set B := {b | b ∈ U₁ ∧
    Module.finrank ℂ (LinearMap.range (S b).toLinearMap) = Module.finrank ℂ F}
  have hXU₁ : ∀ x ∈ X, x ∈ U₁ := fun x hx ↦ by
    change ‖A x * A x - A x‖ < 1 / 8
    rw [(hX x hx).1.eq, sub_self, norm_zero]
    norm_num
  have hSX : ∀ x ∈ X, S x = A x := fun x hx ↦ spectralProj_eq_self (hnormal x) (hX x hx).1
  have hU : IsOpen U := by
    refine isOpen_iff_mem_nhds.2 fun b₀ hb₀ ↦ ?_
    have hT : ContinuousAt (ProjectionFamily.transport S b₀) b₀ := by
      have : ContinuousOn (ProjectionFamily.transport S b₀) U₁ := by
        unfold ProjectionFamily.transport
        exact (hScont.mul continuousOn_const).add
          ((continuousOn_const.sub hScont).mul continuousOn_const)
      exact this.continuousAt (hU₁.mem_nhds hb₀.1)
    have hunit : ∀ᶠ b in 𝓝 b₀, IsUnit (ProjectionFamily.transport S b₀ b) := by
      refine hT.preimage_mem_nhds (Units.isOpen.mem_nhds ?_)
      change IsUnit (ProjectionFamily.transport S b₀ b₀)
      rw [ProjectionFamily.transport_self (hSidem b₀ hb₀.1)]
      exact isUnit_one
    filter_upwards [hunit, hU₁.mem_nhds hb₀.1] with b hb hb₁
    exact ⟨hb₁, (ProjectionFamily.finrank_range_eq_of_isUnit_transport (hSidem b₀ hb₀.1)
      (hSidem b hb₁) hb).trans hb₀.2⟩
  refine ⟨U, hU, fun x hx ↦ ⟨hXU₁ x hx, by rw [hSX x hx]; exact (hX x hx).2⟩,
    { toFun := fun y ↦ S y
      continuous_toFun := hScont.comp_continuous continuous_subtype_val fun y ↦ y.2.1
      isIdempotentElem := fun y ↦ hSidem y y.2.1
      finrank_range := fun y ↦ y.2.2 }, fun x hx ↦ hSX x hx, fun y ↦ ?_⟩
  change LinearMap.range (S y).toLinearMap ≤ _
  rintro _ ⟨v, rfl⟩
  change spectralProj (A y) v ∈ _
  rw [spectralProj_eq_mul (hnormal y) (le_of_lt y.2.1)]
  exact LinearMap.mem_range_self _ _

end MMP
