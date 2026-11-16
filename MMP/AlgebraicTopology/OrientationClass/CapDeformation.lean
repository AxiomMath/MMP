module

public import MMP.AlgebraicTopology.CapProduct.SupportRetraction

/-!
# Proper neighbourhood deformations under homeomorphisms

If `X ⊆ Y` has arbitrarily small proper neighbourhood deformations (the precondition of the cap
product with supports), so has its preimage `φ⁻¹ X` under a homeomorphism `φ : Y' ≃ₜ Y`: transport
the closed neighbourhoods, retractions and deformations along `φ`.

## Main definitions

* `MMP.preimageHomeomorph`: `φ⁻¹ s ≃ₜ s`.

## Main results

* `MMP.HasProperNeighbourhoodDeformations.preimage_homeomorph`: if `X` has proper neighbourhood
  deformations, so has `φ ⁻¹' X` for a homeomorphism `φ`.
-/

@[expose] public noncomputable section

open Set Topology unitInterval

namespace MMP

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- The homeomorphism `φ⁻¹ s ≃ₜ s` induced by a homeomorphism `φ`. -/
def preimageHomeomorph (φ : Y' ≃ₜ Y) (s : Set Y) : (φ ⁻¹' s) ≃ₜ s where
  toFun y := ⟨φ y, y.2⟩
  invFun z := ⟨φ.symm z, show φ (φ.symm z) ∈ s by rw [φ.apply_symm_apply]; exact z.2⟩
  left_inv y := Subtype.ext (φ.symm_apply_apply y.1)
  right_inv z := Subtype.ext (φ.apply_symm_apply z.1)
  continuous_toFun := (φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- `preimageHomeomorph φ s` sends `y` to `φ y`. -/
@[simp]
lemma coe_preimageHomeomorph_apply (φ : Y' ≃ₜ Y) (s : Set Y) (y : φ ⁻¹' s) :
    (preimageHomeomorph φ s y : Y) = φ y :=
  rfl

/-- The inverse of `preimageHomeomorph φ s` sends `z` to `φ.symm z`. -/
@[simp]
lemma coe_preimageHomeomorph_symm_apply (φ : Y' ≃ₜ Y) (s : Set Y) (z : s) :
    ((preimageHomeomorph φ s).symm z : Y') = φ.symm z :=
  rfl

/-- **Proper neighbourhood deformations are invariant under homeomorphisms.** -/
theorem HasProperNeighbourhoodDeformations.preimage_homeomorph {X : Set Y}
    (h : HasProperNeighbourhoodDeformations X) (φ : Y' ≃ₜ Y) :
    HasProperNeighbourhoodDeformations (φ ⁻¹' X) := by
  intro M' hM'
  have hM : φ.symm ⁻¹' M' ∈ 𝓝ˢ X := by
    rw [mem_nhdsSet_iff_forall] at hM' ⊢
    intro x hx
    exact φ.symm.continuous.continuousAt.preimage_mem_nhds
      (hM' _ (show φ (φ.symm x) ∈ X by rw [φ.apply_symm_apply]; exact hx))
  obtain ⟨N, hN, hXN, hNM, r, hr, hrX, G, hG, hG0, hG1, hGX, hGM⟩ := h _ hM
  set ψN := preimageHomeomorph φ N
  set ψX := preimageHomeomorph φ X
  let r' : C(φ ⁻¹' N, φ ⁻¹' X) := (ψX.symm : C(X, φ ⁻¹' X)).comp (r.comp (ψN : C(_, N)))
  let G' : C((φ ⁻¹' N) × I, Y') := (φ.symm : C(Y, Y')).comp
    (G.comp ((ψN : C(_, N)).prodMap (ContinuousMap.id I)))
  refine ⟨φ ⁻¹' N, hN.preimage φ.continuous, ?_, fun y hy ↦ ?_, r',
    ψX.symm.isProperMap.comp (hr.comp ψN.isProperMap), fun y hy ↦ ?_, G',
    φ.symm.isProperMap.comp (hG.comp (ψN.isProperMap.prodMap isProperMap_id)), fun y ↦ ?_,
    fun y ↦ ?_, fun y t hy ↦ ?_, fun q ↦ ?_⟩
  · rw [← φ.preimage_interior]
    exact preimage_mono hXN
  · have := hGM (⟨φ y, hy⟩, 0)
    rw [hG0] at this
    change φ.symm (φ y) ∈ M' at this
    rwa [φ.symm_apply_apply] at this
  · change φ.symm (r ⟨φ y, y.2⟩ : Y) = y
    rw [hrX ⟨φ y, y.2⟩ hy, φ.symm_apply_apply]
  · change φ.symm (G (⟨φ y, y.2⟩, 0)) = y
    rw [hG0, φ.symm_apply_apply]
  · change φ.symm (G (⟨φ y, y.2⟩, 1)) = φ.symm (r ⟨φ y, y.2⟩)
    rw [hG1]
  · change φ.symm (G (⟨φ y, y.2⟩, t)) = y
    rw [hGX ⟨φ y, y.2⟩ t hy, φ.symm_apply_apply]
  · exact hGM _

end MMP
