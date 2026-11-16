module
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree

/-!
# The projection formula for higher direct images along a vector bundle

Let `f : Y ⟶ X` be a morphism of schemes and `V` a vector bundle on `X`, that is, an
`𝒪_X`-module that is locally free of some finite rank `r`
(`MMP.Intersection.Scheme.Modules.IsLocallyFreeOfRank`). Then for every `i ≥ 0` and every
`𝒪_Y`-module `ℱ`, with no hypothesis on `f` or on `ℱ`,
`R^i f_*(ℱ ⊗ f^*V) ≅ R^i f_* ℱ ⊗ V`, naturally in `ℱ`. In degree zero this reads
`f_*(ℱ ⊗ f^*V) ≅ f_* ℱ ⊗ V`.

## Main results

* `MMP.Intersection.Scheme.Modules.nonempty_rightDerived_tensorRight_pullback_iso`: the
  natural isomorphism of functors
  `(- ⊗ f^*V) ⋙ R^i f_* ≅ R^i f_* ⋙ (- ⊗ V)` from `𝒪_Y`-modules to `𝒪_X`-modules.

## Implementation notes

Tensoring on the right by a module is `Stacks.ProjectionFormula.tensorRightInvertible`, the
right-tensoring endofunctor of the tensor-product bifunctor of `Z.Modules`; despite its name it
carries no invertibility hypothesis. `R^i f_*` is `Functor.rightDerived` of
`Scheme.Modules.pushforward f`, the higher direct image computed in sheaves of modules.
Naturality in `ℱ` is expressed by stating an isomorphism of functors.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004]
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Intersection.Scheme.Modules

/-- A module locally isomorphic to `𝒪^{⊕ r}` is finite locally free. -/
private lemma isFiniteLocallyFree_of_isLocallyFreeOfRank {X : Scheme.{u}} {V : X.Modules}
    {r : ℕ} (hV : IsLocallyFreeOfRank V r) : SheafOfModules.IsFiniteLocallyFree.{u, u, u} V :=
  (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators V).mp fun x =>
    let ⟨U, hx, e⟩ := hV x
    ⟨U, hx, ULift.{u} (Fin r), inferInstance, e⟩

/-- **The projection formula for higher direct images along a vector bundle**: for a morphism of
schemes `f : Y ⟶ X`, a locally free `𝒪_X`-module `V` of finite rank `r` and every `i`,
`R^i f_*(ℱ ⊗ f^*V) ≅ R^i f_* ℱ ⊗ V`, naturally in the `𝒪_Y`-module `ℱ`. -/
@[mmp "lem_mmp_foundation_laz_vector_bundle_projection_formula"]
public theorem nonempty_rightDerived_tensorRight_pullback_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (V : X.Modules) {r : ℕ} (hV : IsLocallyFreeOfRank V r) (i : ℕ) :
    Nonempty (Stacks.ProjectionFormula.tensorRightInvertible Y
          ((Scheme.Modules.pullback f).obj V) ⋙
        (Scheme.Modules.pushforward f).rightDerived i ≅
      (Scheme.Modules.pushforward f).rightDerived i ⋙
        Stacks.ProjectionFormula.tensorRightInvertible X V) :=
  have := isFiniteLocallyFree_of_isLocallyFreeOfRank hV
  let e := Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i
  ⟨Functor.isoWhiskerLeft _ e ≪≫
    Stacks.ProjectionFormula.higherDirectImageTensorRightFiniteLocallyFreeIso f V i ≪≫
    Functor.isoWhiskerRight e.symm _⟩

end MMP.Intersection.Scheme.Modules
