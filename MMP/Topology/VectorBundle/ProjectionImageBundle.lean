module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The image bundle of a continuous family of projections

Let `P : B → (V →L[𝕜] V)` be a continuous family of idempotent operators on a finite-dimensional
normed space `V` whose ranges all have the dimension of a model space `F`. Then the ranges
`range (P b)` form a topological vector bundle on `B` with fibre `F`: near `b₀` the operator
`T_{b₀}(b) = P b ∘ P b₀ + (1 - P b) ∘ (1 - P b₀)` is invertible, maps `range (P b₀)` onto
`range (P b)` and depends continuously on `b`, so `T_{b₀}(b)⁻¹` trivializes the ranges over the
open set where `T_{b₀}(b)` is a unit.

The bundle is given by a `VectorBundleCore` with one chart for each point of `B`; its fibre at
`b` is `F`, identified with `range (P b)` by a fixed linear isomorphism. The fibrewise maps
`V → range (P b) ≅ F`, `v ↦ P b v`, assemble to a continuous map into the total space.

## Main definitions

* `MMP.ProjectionFamily.transport`: the operator `T_{b₀}(b)`.
* `MMP.ProjectionFamily.bundleCore`: the image bundle, as a `VectorBundleCore`.
* `MMP.ProjectionFamily.projL`: the map `V → F`, `v ↦ P b v` in the fibre at `b`.

## Main results

* `MMP.ProjectionFamily.continuous_mk_projL`: for continuous `β : Z → B` and
  `g : Z → V`, the map `z ↦ (β z, P (β z) (g z))` into the total space is continuous.
* `MMP.ProjectionFamily.projL_surjective`: each map `projL b : V → F` is surjective.
* `MMP.ProjectionFamily.projL_eq_zero_iff`: `projL b v = 0` if and only if `P b v = 0`.
-/

@[expose] public noncomputable section

open Bundle Set Topology Filter

namespace MMP

/-- A continuous family of idempotent operators on `V` whose ranges have the dimension of `F`. -/
structure ProjectionFamily (𝕜 B V F : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace B]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  /-- The operators `P b`. -/
  toFun : B → V →L[𝕜] V
  /-- The family `b ↦ P b` is continuous. -/
  continuous_toFun : Continuous toFun
  /-- Each `P b` is idempotent. -/
  isIdempotentElem (b : B) : IsIdempotentElem (toFun b)
  /-- Each range `range (P b)` has the dimension of `F`. -/
  finrank_range (b : B) :
    Module.finrank 𝕜 (LinearMap.range (toFun b).toLinearMap) = Module.finrank 𝕜 F

namespace ProjectionFamily

variable {𝕜 B V F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section transport

variable (P : B → V →L[𝕜] V)

/-- The operator `T_{b₀}(b) = P b ∘ P b₀ + (1 - P b) ∘ (1 - P b₀)`, which maps `range (P b₀)` to
`range (P b)` and, when `P b₀` is idempotent, is the identity for `b = b₀`. -/
def transport (b₀ b : B) : V →L[𝕜] V :=
  P b * P b₀ + (1 - P b) * (1 - P b₀)

variable {P} {b₀ b : B}

/-- If `P b₀` is idempotent, then `T_{b₀}(b) ∘ P b₀ = P b ∘ P b₀`. -/
lemma transport_mul (h₀ : IsIdempotentElem (P b₀)) (b : B) :
    transport P b₀ b * P b₀ = P b * P b₀ := by
  simp only [transport, add_mul, sub_mul, one_mul, mul_assoc, h₀.eq, mul_sub, mul_one, sub_self,
    add_zero]

/-- If `P b` is idempotent, then `P b ∘ T_{b₀}(b) = P b ∘ P b₀`. -/
lemma mul_transport (h : IsIdempotentElem (P b)) (b₀ : B) :
    P b * transport P b₀ b = P b * P b₀ := by
  simp only [transport, mul_add, mul_sub, mul_one, ← mul_assoc, h.eq, sub_self, zero_mul,
    add_zero]

/-- If `P b₀` and `P b` are idempotent, then `T_{b₀}(b) ∘ P b₀ = P b ∘ T_{b₀}(b)`. -/
lemma transport_mul_eq_mul_transport (h₀ : IsIdempotentElem (P b₀))
    (h : IsIdempotentElem (P b)) : transport P b₀ b * P b₀ = P b * transport P b₀ b := by
  rw [transport_mul h₀, mul_transport h]

/-- If `P b` is idempotent, then `T_b(b)` is the identity. -/
lemma transport_self (h : IsIdempotentElem (P b)) : transport P b b = 1 := by
  simp only [transport, h.eq, mul_sub, sub_mul, mul_one, one_mul]
  abel

/-- If `P b₀` and `P b` are idempotent and `T_{b₀}(b)` is invertible, then
`T_{b₀}(b)⁻¹ ∘ P b = P b₀ ∘ T_{b₀}(b)⁻¹`. -/
lemma inverse_transport_mul (h₀ : IsIdempotentElem (P b₀)) (h : IsIdempotentElem (P b))
    (hu : IsUnit (transport P b₀ b)) :
    Ring.inverse (transport P b₀ b) * P b = P b₀ * Ring.inverse (transport P b₀ b) := by
  have := transport_mul_eq_mul_transport h₀ h
  calc Ring.inverse (transport P b₀ b) * P b
      = Ring.inverse (transport P b₀ b) * P b * (transport P b₀ b *
          Ring.inverse (transport P b₀ b)) := by rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = Ring.inverse (transport P b₀ b) * (transport P b₀ b * P b₀) *
          Ring.inverse (transport P b₀ b) := by rw [this]; simp only [mul_assoc]
    _ = P b₀ * Ring.inverse (transport P b₀ b) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

/-- An invertible `T_{b₀}(b)` maps `range (P b₀)` onto `range (P b)`. -/
lemma map_range_transport (h₀ : IsIdempotentElem (P b₀)) (h : IsIdempotentElem (P b))
    (hu : IsUnit (transport P b₀ b)) :
    (LinearMap.range (P b₀).toLinearMap).map (transport P b₀ b).toLinearMap =
      LinearMap.range (P b).toLinearMap := by
  rw [← LinearMap.range_comp]
  have hc : (transport P b₀ b).toLinearMap ∘ₗ (P b₀).toLinearMap =
      (P b).toLinearMap ∘ₗ (transport P b₀ b).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (transport_mul_eq_mul_transport h₀ h)
  rw [hc, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (ContinuousLinearEquiv.unitsEquiv 𝕜 V hu.unit).surjective

/-- The ranges of `P b₀` and `P b` have the same dimension when `T_{b₀}(b)` is invertible. -/
lemma finrank_range_eq_of_isUnit_transport (h₀ : IsIdempotentElem (P b₀))
    (h : IsIdempotentElem (P b)) (hu : IsUnit (transport P b₀ b)) :
    Module.finrank 𝕜 (LinearMap.range (P b).toLinearMap) =
      Module.finrank 𝕜 (LinearMap.range (P b₀).toLinearMap) := by
  rw [← map_range_transport h₀ h hu]
  exact (Submodule.equivMapOfInjective _
    (ContinuousLinearEquiv.unitsEquiv 𝕜 V hu.unit).injective _).finrank_eq.symm

variable [TopologicalSpace B]

/-- For a continuous family `P`, the map `b ↦ T_{b₀}(b)` is continuous. -/
lemma continuous_transport (hP : Continuous P) (b₀ : B) : Continuous (transport P b₀) := by
  unfold transport
  fun_prop

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V]

/-- For a continuous family `P`, the set of `b` for which `T_{b₀}(b)` is a unit is open. -/
lemma isOpen_setOf_isUnit_transport (hP : Continuous P) (b₀ : B) :
    IsOpen {b | IsUnit (transport P b₀ b)} := by
  have := FiniteDimensional.complete 𝕜 V
  exact Units.isOpen.preimage (continuous_transport hP b₀)

/-- For a continuous family `P`, the map `b ↦ T_{b₀}(b)⁻¹` is continuous on the set where
`T_{b₀}(b)` is a unit. -/
lemma continuousOn_inverse_transport (hP : Continuous P) (b₀ : B) :
    ContinuousOn (fun b ↦ Ring.inverse (transport P b₀ b)) {b | IsUnit (transport P b₀ b)} := by
  have := FiniteDimensional.complete 𝕜 V
  intro b hb
  obtain ⟨u, hu⟩ := hb
  refine ContinuousAt.continuousWithinAt ?_
  exact (hu ▸ NormedRing.inverse_continuousAt u).comp (continuous_transport hP b₀).continuousAt

end transport

variable [TopologicalSpace B] (P : ProjectionFamily 𝕜 B V F)

/-- A projection family coerces to its family of operators `b ↦ P b`. -/
instance : CoeFun (ProjectionFamily 𝕜 B V F) fun _ ↦ B → V →L[𝕜] V :=
  ⟨ProjectionFamily.toFun⟩

/-- `P b` as a map onto its range. -/
def toRange (b : B) : V →L[𝕜] LinearMap.range (P b).toLinearMap :=
  (P b).codRestrict (LinearMap.range (P b).toLinearMap) fun v ↦ LinearMap.mem_range_self _ v

/-- The underlying vector of `toRange b v` is `P b v`. -/
@[simp]
lemma coe_toRange (b : B) (v : V) : (P.toRange b v : V) = P b v := rfl

/-- `toRange b` restricts to the identity on `range (P b)`. -/
@[simp]
lemma toRange_coe (b : B) (w : LinearMap.range (P b).toLinearMap) : P.toRange b w = w := by
  obtain ⟨_, v, rfl⟩ := w
  ext
  change P b (P b v) = P b v
  rw [← mul_apply_eq_comp, (P.isIdempotentElem b).eq]

/-- The base sets of the charts: `T_{b₀}(b)` is a unit. -/
def baseSet (b₀ : B) : Set B := {b | IsUnit (transport P b₀ b)}

/-- Membership in the base set of the chart at `b₀`: `T_{b₀}(b)` is a unit. -/
lemma mem_baseSet_iff {b₀ b : B} : b ∈ P.baseSet b₀ ↔ IsUnit (transport P b₀ b) := Iff.rfl

/-- Each point `b` lies in the base set of its own chart. -/
lemma mem_baseSet_self (b : B) : b ∈ P.baseSet b :=
  P.mem_baseSet_iff.2 <| by rw [transport_self (P.isIdempotentElem b)]; exact isUnit_one

/-- `T_{b₀}(b)` maps a vector of `range (P b₀)` into `range (P b)`: `P b` fixes its image. -/
lemma transport_apply_range {b₀ : B} (b : B) (u : LinearMap.range (P b₀).toLinearMap) :
    P b (transport P b₀ b u) = transport P b₀ b u := by
  have h := congrArg (fun A : V →L[𝕜] V ↦ A u)
    (transport_mul_eq_mul_transport (P.isIdempotentElem b₀) (P.isIdempotentElem b))
  simp only [mul_apply_eq_comp] at h
  rw [← h, ← P.coe_toRange b₀, P.toRange_coe]

/-- For `b` in the base set of the chart at `b₀`, `T_{b₀}(b)⁻¹` maps `range (P b)` into
`range (P b₀)`: `P b₀` fixes `T_{b₀}(b)⁻¹ (P b v)`. -/
lemma inverse_transport_apply {b₀ b : B} (hb : b ∈ P.baseSet b₀) (v : V) :
    P b₀ (Ring.inverse (transport P b₀ b) (P b v)) =
      Ring.inverse (transport P b₀ b) (P b v) := by
  have h := congrArg (fun A : V →L[𝕜] V ↦ A (P b v))
    (inverse_transport_mul (P.isIdempotentElem b₀) (P.isIdempotentElem b) hb)
  simp only [mul_apply_eq_comp] at h
  rw [← h, ← mul_apply_eq_comp (P b) (P b), (P.isIdempotentElem b).eq]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 F]

/-- The identification `range (P b) ≃ F`. -/
def frame (b : B) : LinearMap.range (P b).toLinearMap ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq _ _ (P.finrank_range b)).toContinuousLinearEquiv

/-- The map `V → F`, `v ↦ P b v` in the coordinates of `range (P b)`. -/
def projL (b : B) : V →L[𝕜] F :=
  (P.frame b : LinearMap.range (P b).toLinearMap →L[𝕜] F) ∘L P.toRange b

/-- The coordinate change from the chart at `i` to the chart at `j`, over `b`:
`F ≅ range (P i) → range (P j) ≅ F`, `u ↦ P j (T_j(b)⁻¹ (T_i(b) u))`. -/
def coordChange (i j b : B) : F →L[𝕜] F :=
  (P.frame j : LinearMap.range (P j).toLinearMap →L[𝕜] F) ∘L P.toRange j ∘L
    (Ring.inverse (transport P j b) * transport P i b) ∘L
      (LinearMap.range (P i).toLinearMap).subtypeL ∘L
      ((P.frame i).symm : F →L[𝕜] LinearMap.range (P i).toLinearMap)

/-- The explicit formula for `coordChange i j b v`. -/
lemma coordChange_apply (i j b : B) (v : F) :
    (P.coordChange i j b v : F) = P.frame j (P.toRange j (Ring.inverse (transport P j b)
      (transport P i b ((P.frame i).symm v)))) := rfl

/-- Over a point of the base set of the chart at `i`, the coordinate change from `i` to itself is
the identity. -/
lemma coordChange_self (i b : B) (hb : b ∈ P.baseSet i) (v : F) : P.coordChange i i b v = v := by
  rw [coordChange_apply, ← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hb,
    one_apply_eq_self, P.toRange_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- Over the intersection of the base sets of the charts at `i`, `j` and `k`, the coordinate change
from `j` to `k` composed with that from `i` to `j` is the one from `i` to `k`. -/
lemma coordChange_comp (i j k b : B) (hb : b ∈ P.baseSet i ∩ P.baseSet j ∩ P.baseSet k)
    (v : F) : P.coordChange j k b (P.coordChange i j b v) = P.coordChange i k b v := by
  obtain ⟨⟨hi, hj⟩, -⟩ := hb
  set u := (P.frame i).symm v
  have h1 : P b (transport P i b u) = transport P i b u := P.transport_apply_range b u
  have h2 : ((P.frame j).symm (P.coordChange i j b v) : V) =
      Ring.inverse (transport P j b) (transport P i b u) := by
    rw [coordChange_apply, ContinuousLinearEquiv.symm_apply_apply, coe_toRange, ← h1,
      P.inverse_transport_apply hj]
  rw [P.coordChange_apply j k b, h2, P.coordChange_apply i k b,
    ← mul_apply_eq_comp (transport P j b),
    Ring.mul_inverse_cancel _ hj, one_apply_eq_self]

/-- The coordinate change from the chart at `b` to the chart at `i`, applied to `projL b v`, is the
image of `P i (T_i(b)⁻¹ (P b v))` under `frame i`. -/
lemma coordChange_self_projL (i b : B) (v : V) :
    P.coordChange b i b (P.projL b v) = P.frame i (P.toRange i (Ring.inverse (transport P i b)
      (P b v))) := by
  rw [coordChange_apply, projL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, transport_self (P.isIdempotentElem b),
    one_apply_eq_self, coe_toRange]

/-- The map `projL b : V → F` is surjective. -/
lemma projL_surjective (b : B) : Function.Surjective (P.projL b) := by
  intro w
  obtain ⟨v, hv⟩ := ((P.frame b).symm w).2
  refine ⟨v, ?_⟩
  rw [projL, ContinuousLinearMap.comp_apply,
    show P.toRange b v = (P.frame b).symm w from Subtype.ext hv]
  exact (P.frame b).apply_symm_apply w

/-- `projL b v` vanishes if and only if `P b v` does. -/
@[simp]
lemma projL_eq_zero_iff (b : B) (v : V) : P.projL b v = 0 ↔ P b v = 0 := by
  rw [projL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    (P.frame b).map_eq_zero_iff, ← Submodule.coe_eq_zero, coe_toRange]

/-- The coordinate change from `i` to `j` depends continuously on `b` over the intersection of the
base sets of the two charts. -/
lemma continuousOn_coordChange (i j : B) :
    ContinuousOn (P.coordChange i j) (P.baseSet i ∩ P.baseSet j) := by
  have hT := (continuous_transport P.continuous_toFun i).continuousOn
    (s := P.baseSet i ∩ P.baseSet j)
  have hI := (continuousOn_inverse_transport P.continuous_toFun j).mono
    (inter_subset_right : P.baseSet i ∩ P.baseSet j ⊆ P.baseSet j)
  unfold coordChange
  refine continuousOn_const.clm_comp (continuousOn_const.clm_comp
    ((ContinuousOn.clm_comp hI hT).clm_comp continuousOn_const))

/-- **The image bundle** of the family of projections `P`: the vector bundle on `B` with fibre `F`
whose fibre at `b` is `range (P b) ≅ F`, the chart at `b₀` trivializing it through
`T_{b₀}(b)⁻¹` over the open set where `T_{b₀}(b)` is a unit. -/
def bundleCore : VectorBundleCore 𝕜 B F B where
  baseSet := P.baseSet
  isOpen_baseSet := isOpen_setOf_isUnit_transport P.continuous_toFun
  indexAt := id
  mem_baseSet_at := P.mem_baseSet_self
  coordChange := P.coordChange
  coordChange_self := P.coordChange_self
  continuousOn_coordChange := P.continuousOn_coordChange
  coordChange_comp := P.coordChange_comp

/-- The map `z ↦ (β z, P (β z) (g z))` into the image bundle is continuous. -/
theorem continuous_mk_projL {Z : Type*} [TopologicalSpace Z] {β : Z → B} (hβ : Continuous β)
    {g : Z → V} (hg : Continuous g) :
    Continuous fun z ↦ (⟨β z, P.projL (β z) (g z)⟩ : TotalSpace F P.bundleCore.Fiber) := by
  refine continuous_iff_continuousAt.2 fun z₀ ↦ ?_
  refine (FiberBundle.continuousAt_totalSpace F _).2 ⟨hβ.continuousAt, ?_⟩
  set i := β z₀
  have hcont : ContinuousAt (fun z ↦ P.frame i (P.toRange i (Ring.inverse (transport P i (β z))
      (P (β z) (g z))))) z₀ := by
    have hI : ContinuousAt (fun z ↦ Ring.inverse (transport P i (β z))) z₀ :=
      ((continuousOn_inverse_transport P.continuous_toFun i).continuousAt
        ((isOpen_setOf_isUnit_transport P.continuous_toFun i).mem_nhds
          (P.mem_baseSet_self i))).comp hβ.continuousAt
    have hPg : ContinuousAt (fun z ↦ P (β z) (g z)) z₀ :=
      ((P.continuous_toFun.comp hβ).clm_apply hg).continuousAt
    exact (P.frame i).continuous.continuousAt.comp ((P.toRange i).continuous.continuousAt.comp
      (hI.clm_apply hPg))
  refine hcont.congr (Eventually.of_forall fun z ↦ ?_)
  change _ = (P.bundleCore.localTriv (P.bundleCore.indexAt (β z₀)) _).2
  rw [VectorBundleCore.localTriv_apply]
  exact (P.coordChange_self_projL i (β z) (g z)).symm

end ProjectionFamily

end MMP
