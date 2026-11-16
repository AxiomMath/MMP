module
public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyOnACofilteredLimit

/-!
# The action of an automorphism on pluricanonical sections

Let `X` be a smooth variety of dimension `d` over a field `k`, with structure morphism
`f : X ⟶ Spec k`, and let `σ : X ≅ X` be an automorphism over `k`. Functoriality of relative
differentials gives the canonical map `σ^*Ω^d_{X/k} ⟶ Ω^d_{X/k}` on top differential forms. It is
an isomorphism, because `σ` is étale. Together with the comparison
`σ^*(ω_X^{⊗n}) ≅ (σ^*ω_X)^{⊗n}`, its `n`-th tensor power gives `σ^*(ω_X^{⊗n}) ≅ ω_X^{⊗n}`, where
`ω_X = Ω^d_{X/k}`. The adjoint map `ω_X^{⊗n} ⟶ σ_*(ω_X^{⊗n})` on global sections is the `k`-linear
action `σ^* : H⁰(X, ω_X^{⊗n}) → H⁰(X, ω_X^{⊗n})`.

## Main definitions

* `MMP.pluricanonicalAction`: the action `σ^*` on `H⁰(X, ω_X^{⊗n})`.

## Implementation notes

The canonical sheaf is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f d`, the `d`-th
exterior power of the sheaf of relative differentials. Its tensor powers are
`SheafOfModules.tensorPower`, with `ω^{⊗0} = 𝒪_X` and `ω^{⊗1} = ω`. The global sections
`H⁰(X, -)` are a `k`-module, through the pushforward to `Spec k` followed by
`AlgebraicGeometry.moduleSpecΓFunctor`. For `n = 1` both the pullback comparison and the tensor
power of the differential map are the identity and the differential map itself, so the action is
pullback of top differential forms by definition.

## References

* [O. Fujino et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP

/-- **The action of an automorphism on pluricanonical sections.** Let `f : X ⟶ Spec k` be a
smooth variety of dimension `d` and `σ : X ≅ X` an automorphism over `k`. This is the `k`-linear
map `σ^* : H⁰(X, ω_X^{⊗n}) → H⁰(X, ω_X^{⊗n})`, where `ω_X = Ω^d_{X/k}`. It is induced on global
sections by `σ^*(ω_X^{⊗n}) ≅ (σ^*ω_X)^{⊗n} ≅ ω_X^{⊗n}`, the `n`-th tensor power of the canonical
isomorphism `σ^*Ω^d_{X/k} ≅ Ω^d_{X/k}` given by functoriality of relative differentials. -/
@[mmp "def_mmp_automorphism_pluricanonical_action"]
public def pluricanonicalAction {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsVariety k f] [Smooth f] (d : ℕ) (_hd : topologicalKrullDim X = d) (n : ℕ) (σ : X ≅ X)
    (hσ : σ.hom ≫ f = f) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.tensorPower (Opens.grothendieckTopology X)
          (Scheme.Hom.relativeDifferentialForms f (d : ℤ)) n)) →ₗ[k]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.tensorPower (Opens.grothendieckTopology X)
          (Scheme.Hom.relativeDifferentialForms f (d : ℤ)) n)) :=
  (moduleSpecΓFunctor.map
    ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction σ.hom).homEquiv _ _
          (Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorPowerIso σ.hom
              (Scheme.Hom.relativeDifferentialForms f (d : ℤ)) n ≪≫
            SheafOfModules.tensorPowerMapIso (Opens.grothendieckTopology X)
              (@asIso _ _ _ _ (Scheme.Hom.relativeDifferentialFormsMap σ.hom f f (𝟙 _)
                (hσ.trans (Category.comp_id f).symm) (d : ℤ))
                (Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale σ.hom f f (𝟙 _)
                  (hσ.trans (Category.comp_id f).symm) (d : ℤ))) n).hom) ≫
      (Scheme.Modules.pushforwardComp σ.hom f).hom.app _ ≫
      (Scheme.Modules.pushforwardCongr hσ).hom.app _)).hom

end MMP
