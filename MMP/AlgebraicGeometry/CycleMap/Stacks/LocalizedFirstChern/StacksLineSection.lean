module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksSectionPoints
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.SectionIdeal

/-!
# A global section of a module as a section of the vector bundle of its dual

A global section `s ∈ Γ(X, ℒ)` of an `𝒪_X`-module `ℒ` gives, by evaluation, the module morphism
`ℒ^∨ ⟶ 𝒪_X`, `λ ↦ λ(s)` (Stacks' `Scheme.Modules.evalGlobalHom`), hence a section
`σ_s : X ⟶ 𝐕(ℒ^∨)` of the vector bundle of the dual (`MMP.Modules.globalSectionMap`), whose
`ℂ`-points over `x` are the elements of the fibre `ℒ(x)`. Its local coordinate in a chart
`(V, λ)` of `𝐕(ℒ^∨)` is `λ(s|_V)` (`MMP.Modules.sectionCoord_globalSectionMap`).

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Opposite

namespace MMP.Modules

variable {X : Scheme.{0}} (L : X.Modules) [(Scheme.Modules.dual L).IsQuasicoherent]

/-- Evaluation at a global section `s` of `ℒ`, `ℒ^∨ ⟶ 𝒪_X = 𝟙_* 𝒪_X`. -/
def globalSectionModuleHom (s : Γ(L, ⊤)) :
    Scheme.Modules.dual L ⟶ Scheme.Modules.structurePushforward (𝟙 X) :=
  Scheme.Modules.evalGlobalHom L s ≫ (Scheme.Modules.pushforwardId X).inv.app _

/-- **The section `σ_s : X ⟶ 𝐕(ℒ^∨)` of a global section `s` of `ℒ`**, over `X`. -/
def globalSectionOver (s : Γ(L, ⊤)) :
    Over.mk (𝟙 X) ⟶ Scheme.Modules.vectorBundleOver X (F := Scheme.Modules.dual L) :=
  (Scheme.Modules.vectorBundleHomEquiv (Scheme.Modules.dual L) (Over.mk (𝟙 X))).symm
    (globalSectionModuleHom L s)

/-- **The section `σ_s : X ⟶ 𝐕(ℒ^∨)` of a global section `s` of `ℒ`.** -/
def globalSectionMap (s : Γ(L, ⊤)) : X ⟶ totalSpace (Scheme.Modules.dual L) :=
  (globalSectionOver L s).left

/-- The section `σ_s` is a section of the projection `𝐕(ℒ^∨) ⟶ X`. -/
@[reassoc (attr := simp)]
lemma globalSectionMap_proj (s : Γ(L, ⊤)) :
    globalSectionMap L s ≫ proj (Scheme.Modules.dual L) = 𝟙 X :=
  Over.w (globalSectionOver L s)

/-- The preimage under `σ_s` of the preimage of an open `V ⊆ X` under the projection
`𝐕(ℒ^∨) ⟶ X` is `V`. -/
lemma preimage_proj_preimage_globalSectionMap (s : Γ(L, ⊤)) (V : X.Opens) :
    globalSectionMap L s ⁻¹ᵁ (proj (Scheme.Modules.dual L) ⁻¹ᵁ V) = V := by
  rw [← Scheme.Hom.comp_preimage, globalSectionMap_proj, Scheme.Hom.id_preimage]

/-- **The local coordinates of `σ_s`**: in a chart `(V, λ)` of `𝐕(ℒ^∨)`, the `i`-th local
coordinate of `σ_s` is `λᵢ(s|_V)`. -/
theorem sectionCoord_globalSectionMap (s : Γ(L, ⊤)) {r : ℕ}
    (c : Chart (Scheme.Modules.dual L) r) (i : Fin r) :
    sectionCoord (globalSectionMap L s) c
        (preimage_proj_preimage_globalSectionMap L s c.1.1).ge i =
      Scheme.Modules.evalGlobal L s (c.2 i) := by
  have h := appLE_totalSections_generator (Scheme.Modules.dual L) (globalSectionOver L s) c.1
    (c.2 i) (preimage_proj_preimage_globalSectionMap L s c.1.1).ge
  refine h.trans ((congrArg (fun φ : Scheme.Modules.dual L ⟶
      Scheme.Modules.structurePushforward (𝟙 X) ↦ (φ.val.app (op c.1.1)).hom (c.2 i))
    ((Scheme.Modules.vectorBundleHomEquiv (Scheme.Modules.dual L) (Over.mk (𝟙 X))).apply_symm_apply
      (globalSectionModuleHom L s))).trans rfl)

end MMP.Modules
