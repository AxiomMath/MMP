module

public import Mathlib.Topology.Sheaves.Over
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Preimage functors of homeomorphisms are cocontinuous

For a continuous map `f : X ⟶ Y` the preimage functor `Opens.map f : Opens Y ⥤ Opens X` is
continuous for the Grothendieck topologies of open covers. When `f` is a homeomorphism it is also
cocontinuous: an open `V ⊆ f⁻¹ U` is the preimage of its image `f(V) ⊆ U`, so a sieve on `f⁻¹ U`
covering it pulls back to a sieve on `U` covering it.

Hence both legs of the induced equivalence `Opens.mapMapIso` are
cocontinuous, and the equivalence is an equivalence of sites.

## Main results

* `MMP.isCocontinuous_opensMap_of_iso`: `Opens.map H.hom` is cocontinuous for `H : X ≅ Y`.
* `MMP.isCocontinuous_mapMapIso_functor`, `MMP.isCocontinuous_mapMapIso_inverse`: both legs of
  `Opens.mapMapIso H` are cocontinuous.
* `MMP.isDenseSubsite_mapMapIso_functor`: for an isomorphism `H : X ≅ Y` of topological spaces,
  the functor of `Opens.mapMapIso H` is a dense subsite.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace MMP

/-- The preimage functor of a homeomorphism is cocontinuous for the topologies of open covers. -/
theorem isCocontinuous_opensMap_of_iso {X Y : TopCat.{u}} (H : X ≅ Y) :
    (Opens.map H.hom).IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  ((Opens.mapMapIso H).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (coverPreserving_opens_map H.inv)

/-- The functor of the equivalence `Opens.mapMapIso H` of a homeomorphism is cocontinuous. -/
theorem isCocontinuous_mapMapIso_functor {X Y : TopCat.{u}} (H : X ≅ Y) :
    (Opens.mapMapIso H).functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  isCocontinuous_opensMap_of_iso H

/-- The inverse of the equivalence `Opens.mapMapIso H` of a homeomorphism is cocontinuous. -/
theorem isCocontinuous_mapMapIso_inverse {X Y : TopCat.{u}} (H : X ≅ Y) :
    (Opens.mapMapIso H).inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
  isCocontinuous_opensMap_of_iso H.symm

/-- For a homeomorphism `H`, the functor of the equivalence `Opens.mapMapIso H` is a dense
subsite for the topologies of open covers. -/
theorem isDenseSubsite_mapMapIso_functor {X Y : TopCat.{u}} (H : X ≅ Y) :
    (Opens.mapMapIso H).functor.IsDenseSubsite (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
  have := isCocontinuous_mapMapIso_functor H
  have := isCocontinuous_mapMapIso_inverse H
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ _

end MMP
