module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.AmpleCriterion
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PullbackWedge

/-!
# The projection formula for an invertible module

For a morphism of schemes `f : X ⟶ Z`, an `𝒪_X`-module `𝓕` and an invertible `𝒪_Z`-module `𝓛`,
the canonical morphism `f_* 𝓕 ⊗ 𝓛 ⟶ f_*(𝓕 ⊗ f^* 𝓛)` is an isomorphism, and on sections it
sends `s ⊗ t` to `s ⊗ f^* t`.

## Implementation notes

* The canonical morphism is `Stacks.ProjectionFormula.projectionFormulaMap'` of the underlying
  morphism of ringed spaces `f.toLRSHom.toShHom`; invertibility of `𝓛` is
  `Stacks.Ample.IsInvertibleModule`.
* The tensor product of sheaves is the sheafified tensor product
  `Stacks.SheafOfModules.Tensor.sheafTensor`, and the elementary tensor of two sections over an
  open `V` is `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, the image of
  `s ⊗ t` in the sheafification. A section of `f_* 𝓕` over `V` is a section of `𝓕` over
  `f⁻¹ V`, and the pullback `f^* t` of a section `t` of `𝓛` over `V` is its image under the
  unit `𝓛 ⟶ f_* f^* 𝓛` of `f^* ⊣ f_*`, a section of `f^* 𝓛` over `f⁻¹ V`.
* The compatibility is stated over every open `V ⊆ Z`; `V = Z` is the compatibility with the
  maps on global sections.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules
open scoped TensorProduct

namespace MMP.Resolution.Bridges

open Stacks.ProjectionFormula (projectionFormulaMap')

/-- **Projection formula for an invertible module.** Let `f : X ⟶ Z` be a morphism of schemes,
`𝓕` an `𝒪_X`-module and `𝓛` an invertible `𝒪_Z`-module. Then
`f_*(𝓕 ⊗ f^* 𝓛) ≅ f_* 𝓕 ⊗ 𝓛`, compatibly with the maps on global sections.

The isomorphism is the canonical morphism `f_* 𝓕 ⊗ 𝓛 ⟶ f_*(𝓕 ⊗ f^* 𝓛)`; its compatibility with
sections is that it sends `s ⊗ t` to `s ⊗ f^* t` (the product `f^* t · s`) over every open
`V ⊆ Z`, in particular over `V = Z`. -/
@[mmp "lem_mmp_foundation_invertible_projection_formula"]
theorem isIso_projectionFormulaMap_and_tmul {X Z : Scheme.{u}} (f : X ⟶ Z) (F : X.Modules)
    (L : Z.Modules) [Stacks.Ample.IsInvertibleModule Z L] :
    IsIso (projectionFormulaMap' f.toLRSHom.toShHom F L) ∧
      ∀ (V : (TopologicalSpace.Opens Z)ᵒᵖ)
        (s : ((pushforwardFunctor f.toLRSHom.toShHom).obj F).val.obj V) (t : L.val.obj V),
        (projectionFormulaMap' f.toLRSHom.toShHom F L).val.app V
            ((tensorSheafUnit (Osharp := Z.sheaf) _ L).app V (s ⊗ₜ t)) =
          (tensorSheafUnit (Osharp := X.sheaf) F
              ((pullbackFunctor f.toLRSHom.toShHom).obj L)).app
            ((opensMap f.toLRSHom.toShHom).op.obj V)
            (s ⊗ₜ pullbackUnit f.toLRSHom.toShHom L V t) := by
  have := Stacks.ProjectionFormula.isInvertible_of_isInvertibleModule Z L
  exact ⟨Stacks.ProjectionFormula.isIso_projectionFormulaMap f.toLRSHom.toShHom F L,
    Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.projectionFormulaMap'_unit_tmul
      f.toLRSHom.toShHom F L⟩

end MMP.Resolution.Bridges

end
