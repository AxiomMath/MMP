module

public import MMP.AlgebraicTopology.BorelMoore.LongExactQuasiIso
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
/-!
# The Borel–Moore long exact sequence of a complex scheme (Fulton, §19.1)

Let `Y` be a complex scheme, `i : X → Y` a closed subscheme, and `U = Y - X` on underlying
spaces. Then there are homomorphisms `∂ : H_{j+1} U → H_j X` making
`⋯ → H_{j+1} U → H_j X → H_j Y → H_j U → H_{j-1} X → ⋯` exact.

The underlying space `Y(ℂ)` is locally contractible with a closed imbedding in some `ℝᴺ`, and
`X(ℂ)` is homeomorphic to the closed set `i(X(ℂ))`, again locally contractible
(`hasBasis_contractible_and_exists_isClosedEmbedding`, `UnderlyingSpace.hasOpenContractibleBasis`).
So `i(X(ℂ))` has arbitrarily small closed neighbourhoods with a proper deformation onto it, fixing
it (`exists_isClosed_isProperMap_retraction_homotopy`), and the restriction
`C^lf(Y) / C^lf(i(X)) → C^lf(U)` is a quasi-isomorphism
(`borelMooreHomology.isRelativeQuasiIso_of_isClosedEmbedding`). The long exact homology sequence
of `0 → C^lf(X) → C^lf(Y) → C^lf(Y) / C^lf(X) → 0` is the claim.

## Main results

* `MMP.IsComplexScheme.exists_borelMooreHomology_longExact`: the long exact sequence
  `⋯ → H_{k+1} U → H_k Z → H_k S → H_k U → H_{k-1} Z → ⋯` of Borel–Moore homology for a closed
  subscheme `Z` of a complex scheme `S` with complement `U`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, (3).
-/

@[expose] public noncomputable section

open CategoryTheory Topology AlgebraicGeometry Set

namespace MMP

open MMP

section exact

variable {A A' B C D : Type*} {p : A' → A} {q : A → A'}

/-- Exactness at `A`, transported along mutually inverse maps `p : A' → A`, `q : A → A'`. -/
lemma exact_comp_inverse [Zero B] {δ : D → A} {f : A → B} (h : Function.Exact δ f)
    (hpq : ∀ a, q (p a) = a) (hqp : ∀ a, p (q a) = a) :
    Function.Exact (q ∘ δ) (f ∘ p) := by
  intro y
  rw [Function.comp_apply, h (p y)]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [Function.comp_apply, hd, hpq]⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, (hqp _).symm⟩

/-- Exactness at `B`, after precomposing the incoming map with a surjection. -/
lemma exact_comp_surjective_left {f : A → B} {g : B → C} [Zero C]
    (h : Function.Exact f g) (hqp : ∀ a, p (q a) = a) :
    Function.Exact (f ∘ p) g := by
  intro y
  rw [h y]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨q a, by rw [Function.comp_apply, hqp]⟩
  · rintro ⟨a', rfl⟩
    exact ⟨p a', rfl⟩

end exact

namespace UnderlyingSpace

/-- The image of `Z(ℂ)` under a closed immersion `i : Z → S` over `ℂ` is closed in `S(ℂ)`. -/
lemma isClosed_range_map_of_isClosedImmersion {Z S : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [S.Over (Spec (.of ℂ))] (i : Z ⟶ S) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    IsClosed (range (map (K := ℂ) i)) :=
  (isClosedEmbedding_map_of_isClosedImmersion i).isClosed_range

end UnderlyingSpace

namespace IsComplexScheme

open UnderlyingSpace borelMooreHomology

/-- **The Borel–Moore long exact sequence of a complex scheme** (Fulton, §19.1, (3)). Let `S` be
a complex scheme, `i : Z → S` a closed subscheme over `ℂ`, and `U = S(ℂ) - i(Z(ℂ))`. There are
homomorphisms `∂ : H_{k+1} U → H_k Z` such that
`⋯ → H_{k+1} U → H_k Z → H_k S → H_k U → H_{k-1} Z → ⋯`, with `i_*` the proper push-forward and
`j^*` the restriction, is exact. -/
theorem exists_borelMooreHomology_longExact (R : Type) [CommRing R] (M : ModuleCat.{0} R)
    (S : Scheme.{0}) [S.Over (Spec (.of ℂ))] [IsComplexScheme S] {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (i : Z ⟶ S) [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] :
    ∃ δ : ∀ k : ℤ, MMP.borelMooreHomology R M
        (TopCat.of (complOpens (Y := TopCat.of (UnderlyingSpace ℂ S))
          (isClosed_range_map_of_isClosedImmersion i))) (k + 1) ⟶
        IsComplexScheme.borelMooreHomology R M Z k,
      (∀ k, Function.Exact (δ k).hom
        (pushforward R M (TopCat.ofHom (map (K := ℂ) i))
          (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap k).hom) ∧
      (∀ k, Function.Exact
        (pushforward R M (TopCat.ofHom (map (K := ℂ) i))
          (isClosedEmbedding_map_of_isClosedImmersion i).isProperMap k).hom
        (restrict R M (complOpens (Y := TopCat.of (UnderlyingSpace ℂ S))
          (isClosed_range_map_of_isClosedImmersion i)) k).hom) ∧
      (∀ k, Function.Exact
        (restrict R M (complOpens (Y := TopCat.of (UnderlyingSpace ℂ S))
          (isClosed_range_map_of_isClosedImmersion i)) (k + 1)).hom (δ k).hom) := by
  set Y : TopCat := TopCat.of (UnderlyingSpace ℂ S)
  set X : Set Y := range (map (K := ℂ) i)
  have hX : IsClosed X := isClosed_range_map_of_isClosedImmersion i
  have hi := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) i
  obtain ⟨hYc, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← comp_over i (Spec (.of ℂ))]
    infer_instance
  let e : UnderlyingSpace ℂ Z ≃ₜ X := hi.isEmbedding.toHomeomorph
  have hXc : HasOpenContractibleBasis X :=
    (UnderlyingSpace.hasOpenContractibleBasis Z).of_homeomorph e
  have hq := isRelativeQuasiIso_of_isClosedEmbedding R M (Y := Y) hF hX hXc hYc
  obtain ⟨δ, h1, h2, h3⟩ := exists_longExact_of_isRelativeQuasiIso R M hX hq
  let g : TopCat.of (UnderlyingSpace ℂ Z) ⟶ TopCat.of X := TopCat.ofHom ⟨e, e.continuous⟩
  let g' : TopCat.of X ⟶ TopCat.of (UnderlyingSpace ℂ Z) := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hg : IsProperMap g := e.isProperMap
  have hg' : IsProperMap g' := e.symm.isProperMap
  have hcomp : TopCat.ofHom (map (K := ℂ) i) = g ≫ subspaceInclusion Y X := rfl
  have hgg' : ∀ k (a : MMP.borelMooreHomology R M (TopCat.of X) k),
      (pushforward R M g hg k).hom ((pushforward R M g' hg' k).hom a) = a := by
    intro k a
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    have : g' ≫ g = 𝟙 _ := TopCat.ext fun x ↦ e.apply_symm_apply x
    simp only [this, pushforward_id]
    rfl
  have hg'g : ∀ k (a : MMP.borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ Z))
      k),
      (pushforward R M g' hg' k).hom ((pushforward R M g hg k).hom a) = a := by
    intro k a
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    have : g ≫ g' = 𝟙 _ := TopCat.ext fun x ↦ e.symm_apply_apply x
    simp only [this, pushforward_id]
    rfl
  have hpush : ∀ k, (pushforward R M (TopCat.ofHom (map (K := ℂ) i)) hi.isProperMap k).hom =
      (pushforward R M (subspaceInclusion Y X) (isProperMap_subspaceInclusion hX) k).hom ∘
        (pushforward R M g hg k).hom := by
    intro k
    rw [show pushforward R M (TopCat.ofHom (map (K := ℂ) i)) hi.isProperMap k =
      pushforward R M g hg k ≫ pushforward R M (subspaceInclusion Y X)
        (isProperMap_subspaceInclusion hX) k from
      pushforward_comp R M g (subspaceInclusion Y X) hg (isProperMap_subspaceInclusion hX) k]
    rfl
  refine ⟨fun k ↦ δ k ≫ pushforward R M g' hg' k, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [hpush]
    exact exact_comp_inverse (h1 k) (hg'g k) (hgg' k)
  · rw [hpush]
    exact exact_comp_surjective_left (h2 k) (hgg' k)
  · refine (h3 k).comp_injective (pushforward R M g' hg' k).hom (fun a b hab ↦ ?_)
      (map_zero (pushforward R M g' hg' k).hom)
    have := congrArg (pushforward R M g hg k).hom hab
    rwa [hgg', hgg'] at this

end IsComplexScheme

end MMP
