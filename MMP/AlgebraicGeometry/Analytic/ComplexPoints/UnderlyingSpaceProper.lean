module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyPullback
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Surjective and proper morphisms on underlying spaces

Let `K` be an algebraically closed field. A surjective morphism `f : X → Y` of schemes locally
of finite type over `K` is surjective on `K`-points: the fibre of `f` over a `K`-point of `Y` is
a non-empty scheme locally of finite type over `K`, so it has a closed point, which is a
`K`-point. Consequently, when `K` is a topological field, properness of the map of underlying
spaces `X(K) → Y(K)` can be checked after precomposing with the map induced by a surjective
morphism `X' → X`; this is the reduction used, with Chow's lemma, to show that a proper morphism
of complex schemes induces a proper map of underlying spaces (Fulton, §19.1).

## Main results

* `MMP.UnderlyingSpace.mapFun_surjective`: a surjective morphism of schemes
  locally of finite type over an algebraically closed field is surjective on `K`-points.
* `MMP.UnderlyingSpace.isProperMap_map_of_comp`: if `X' → X` is surjective and
  `X'(K) → Y(K)` is proper, so is `X(K) → Y(K)`.
* `MMP.UnderlyingSpace.isProperMap_map_of_isClosedImmersion_comp_snd`: a closed
  subscheme `X ⊆ A ×_S B`, with `S(K)` a point and `A(K)` compact, maps properly to `B(K)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Topology

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {X Y Z : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [Z.Over (Spec (.of K))]

/-- A surjective morphism `f : X → Y` over an algebraically closed field `K`, with `X` locally
of finite type over `K`, is surjective on `K`-points. -/
theorem mapFun_surjective (f : X ⟶ Y) [Surjective f] [f.IsOver (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    Function.Surjective (mapFun (K := K) f) := by
  intro p
  have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of K)) := by
    rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of K))
  obtain ⟨x', hx'⟩ := f.surjective (p.toHom (IsLocalRing.closedPoint K))
  obtain ⟨w, -, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := p.toHom) (g := f) _ x' hx'.symm
  let P : Scheme.{u} := pullback p.toHom f
  have : JacobsonSpace P :=
    LocallyOfFiniteType.jacobsonSpace (pullback.fst p.toHom f)
  obtain ⟨c, -, hc⟩ :=
    nonempty_inter_closedPoints (Z := Set.univ) ⟨w, trivial⟩ isClosed_univ.isLocallyClosed
  let q := (pointEquivClosedPoint (pullback.fst p.toHom f)).symm ⟨c, hc⟩
  refine ⟨⟨q.1 ≫ pullback.snd _ _, ?_⟩, UnderlyingSpace.ext ?_⟩
  · rw [Category.assoc, ← comp_over f (Spec (.of K)), ← Category.assoc (pullback.snd _ _),
      ← pullback.condition, Category.assoc, p.toHom_comp_over, Category.comp_id, q.2]
  · change (q.1 ≫ pullback.snd _ _) ≫ f = p.toHom
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, q.2, Category.id_comp]

variable [TopologicalSpace K]

/-- Properness of `X(K) → Y(K)` descends along a surjective morphism `p : Z → X`: if the map
`Z(K) → Y(K)` induced by `p ≫ f` is proper, so is the map induced by `f`. -/
theorem isProperMap_map_of_comp (p : Z ⟶ X) (f : X ⟶ Y) [Surjective p]
    [p.IsOver (Spec (.of K))] [f.IsOver (Spec (.of K))] [LocallyOfFiniteType (Z ↘ Spec (.of K))]
    (h : IsProperMap (map (K := K) (p ≫ f))) :
    IsProperMap (map (K := K) f) := by
  rw [map_comp] at h
  exact isProperMap_of_comp_of_surj (map p).continuous (map f).continuous h
    (mapFun_surjective p)

section Projection

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]
  [T1Space K]
variable {P A B S X : Scheme.{u}} [P.Over (Spec (.of K))] [A.Over (Spec (.of K))]
  [B.Over (Spec (.of K))] [S.Over (Spec (.of K))] [X.Over (Spec (.of K))]

/-- For a pullback `P = A ×_S B` over `K` with `S(K)` a single point and `A(K)` compact, the
projection `P(K) → B(K)` is proper: `P(K)` is homeomorphic to `A(K) × B(K)`. -/
theorem isProperMap_map_snd_of_isPullback {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S}
    {g : B ⟶ S} [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))]
    [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))] (H : IsPullback fst snd f g)
    [Subsingleton (UnderlyingSpace K S)] [CompactSpace (UnderlyingSpace K A)] :
    IsProperMap (map (K := K) snd) := by
  have hrange : Set.range (prodMap (K := K) fst snd) = Set.univ := by
    rw [range_prodMap_of_isPullback H]
    exact Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  have he : IsClosedEmbedding (prodMap (K := K) fst snd) :=
    ⟨isEmbedding_prodMap_of_isPullback H, hrange ▸ isClosed_univ⟩
  exact isProperMap_snd_of_compactSpace.comp he.isProperMap

/-- Let `P = A ×_S B` be a pullback over `K` with `S(K)` a single point and `A(K)` compact
(for instance `P = ℙⁿ × B` over `S = Spec K`, once `ℙⁿ(K)` is known to be compact). If
`f : X → B` factors as a closed immersion `X → P` followed by the projection, the map
`X(K) → B(K)` is proper. -/
theorem isProperMap_map_of_isClosedImmersion_comp_snd {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ S} {g : B ⟶ S} [fst.IsOver (Spec (.of K))] [snd.IsOver (Spec (.of K))]
    [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))] (H : IsPullback fst snd f g)
    [Subsingleton (UnderlyingSpace K S)] [CompactSpace (UnderlyingSpace K A)]
    (i : X ⟶ P) [IsClosedImmersion i] [i.IsOver (Spec (.of K))] :
    IsProperMap (map (K := K) (i ≫ snd)) := by
  rw [map_comp]
  exact (isProperMap_map_snd_of_isPullback H).comp
    (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap

end Projection

end UnderlyingSpace

end MMP
