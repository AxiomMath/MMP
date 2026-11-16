module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Base change of a scheme over `Spec A` along a cocone of `A`-algebras

Let `f : Z ⟶ Spec A` be a morphism of schemes and let `c` be a cocone over a diagram `R` of
`A`-algebras, with point `B`. Base change along `Spec` of the cocone legs gives projections
`π_j : Z ×_A Spec B ⟶ Z ×_A Spec R_j`, and a morphism `g : j ⟶ k` of the diagram gives a
transition `t_g : Z ×_A Spec R_k ⟶ Z ×_A Spec R_j`. The projections are compatible with the
transitions: `π_k ≫ t_g = π_j`.

## Main results

* `MMP.pullbackMap_cocone_comp_transition`: `π_k ≫ t_g = π_j`.

## Implementation notes

The `A`-algebras are objects of `Under A`, and the projections and transitions are `pullback.map`
along `Spec.map` of the underlying ring maps, with the side conditions written as terms so that
every statement referring to these morphisms elaborates them to the same expression.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace MMP

/-- For a cocone `c` over a diagram `R` of `A`-algebras and `g : j ⟶ k`, the projection
`Z ×_A Spec c.pt ⟶ Z ×_A Spec R_k` followed by the transition
`Z ×_A Spec R_k ⟶ Z ×_A Spec R_j` is the projection `Z ×_A Spec c.pt ⟶ Z ×_A Spec R_j`. -/
@[reassoc]
theorem pullbackMap_cocone_comp_transition {A : CommRingCat.{u}} {Z : Scheme.{u}}
    (f : Z ⟶ Spec A) {J : Type u} [Category.{v} J] (R : J ⥤ Under A) (c : Cocone R)
    {j k : J} (g : j ⟶ k) :
    (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj k).hom) (𝟙 Z)
        (Spec.map (c.ι.app k).right) (𝟙 _)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id _).trans
          ((congrArg Spec.map (Under.w (c.ι.app k))).symm.trans (Spec.map_comp _ _)))) ≫
      (pullback.map f (Spec.map (R.obj k).hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
        (Spec.map (R.map g).right) (𝟙 _)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id _).trans
          ((congrArg Spec.map (Under.w (R.map g))).symm.trans (Spec.map_comp _ _)))) =
      (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
        (Spec.map (c.ι.app j).right) (𝟙 _)
        ((Category.comp_id f).trans (Category.id_comp f).symm)
        ((Category.comp_id _).trans
          ((congrArg Spec.map (Under.w (c.ι.app j))).symm.trans (Spec.map_comp _ _)))) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← Spec.map_comp,
      ← Under.comp_right, c.w g]

end MMP

end
