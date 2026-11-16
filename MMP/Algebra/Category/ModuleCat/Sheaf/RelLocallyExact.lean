module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Relative local exactness of a morphism of complexes of sheaves of modules

Let `φ : K' ⟶ K` be a morphism of `ℕ`-indexed cochain complexes of sheaves of modules on a
topological space. We say that `φ` is *relatively locally exact* if every section `x` of `K^p`
whose differential `d x` comes from `K'^{p+1}` is, near every point, of the form `d y + φ x'`
with `y` a section of `K^{p-1}` and `x'` a section of `K'^p`. In degree `0` the term `d y`
vanishes, since `K.d 0 0 = 0`, so the condition says that `x` comes from `K'^0` locally.

For a degreewise monomorphism `φ` this is the local exactness of the quotient complex `K / K'`,
so `φ` is a quasi-isomorphism (`MMP.LcBpf.quasiIso_of_relLocallyExact`).

## Main definitions

* `MMP.LcBpf.RelLocallyExact`: relative local exactness.

-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace MMP.LcBpf

/-- **Relative local exactness** of `φ : K' ⟶ K`: for every section `x` of `K^p` over `W` with
`d x = φ z` for a section `z` of `K'^{p+1}` over `W`, every point of `W` has an open
neighbourhood `V ⊆ W` on which `x = d y + φ x'`, with `y` a section of `K^{p-1}` and `x'` a
section of `K'^p` over `V`. (For `p = 0`, `K.d (0 - 1) 0 = K.d 0 0 = 0`.) -/
def RelLocallyExact {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
    {K' K : CochainComplex (SheafOfModules.{0} R) ℕ} (φ : K' ⟶ K) : Prop :=
  ∀ (p : ℕ) (W : Opens X) (x : (K.X p).val.obj (op W)),
    (∃ z : (K'.X (p + 1)).val.obj (op W),
      (φ.f (p + 1)).val.app (op W) z = (K.d p (p + 1)).val.app (op W) x) →
    ∀ pt ∈ W, ∃ (V : Opens X) (hV : V ≤ W), pt ∈ V ∧
      ∃ (y : (K.X (p - 1)).val.obj (op V)) (x' : (K'.X p).val.obj (op V)),
        (K.X p).val.map (homOfLE hV).op x =
          (K.d (p - 1) p).val.app (op V) y + (φ.f p).val.app (op V) x'

end MMP.LcBpf
