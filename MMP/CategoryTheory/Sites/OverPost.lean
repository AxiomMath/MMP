module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Slices of an equivalence of sites

Let `e : C ≌ D` be an equivalence whose functor is a dense subsite for topologies `J` on `C` and
`K` on `D` (for instance an equivalence of sites). For every `X : C` the induced equivalence of
slices `Over X ≌ Over (e.functor.obj X)`, whose functor is `Over.post e.functor`, is again a
dense subsite for the slice topologies `J.over X` and `K.over (e.functor.obj X)`.

This is what transports local properties of sheaves of modules (such as being of finite type,
which is phrased through restrictions `M.over X`) along an equivalence of sites.

## Main results

* `MMP.isDenseSubsite_overPost`: `Over.post e.functor` is a dense subsite.
-/

@[expose] public section

open CategoryTheory

namespace MMP

/-- The slices `Over X ≌ Over (e.functor.obj X)` of an equivalence of sites `e` form a dense
subsite for the slice topologies. -/
theorem isDenseSubsite_overPost {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.functor.IsDenseSubsite J K] (X : C) :
    (Over.post (X := X) e.functor).IsDenseSubsite (J.over X) (K.over (e.functor.obj X)) := by
  haveI : (Over.post (X := X) e.functor).IsEquivalence :=
    (Over.postEquiv X e).isEquivalence_functor
  exact
    { functorPushforward_mem_iff := fun {Y S} => by
        rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
          Sieve.overEquiv_functorPushforward_post]
        exact Functor.IsDenseSubsite.functorPushforward_mem_iff (G := e.functor) (J := J)
          (K := K) }

end MMP
