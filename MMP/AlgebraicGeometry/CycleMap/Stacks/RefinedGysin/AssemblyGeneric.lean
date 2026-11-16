module

public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.HomotopyGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ChainBaseChangeGeneric
public import MMP.AlgebraicTopology.RefinedGysin.Cone
public import MMP.AlgebraicTopology.RefinedGysin.CapSwap
public import MMP.AlgebraicTopology.CapProduct.SupportLemmas

/-!
# Topological lemmas for Fulton's Theorem 19.2

The bundle-free part of the statement and proof of Fulton's Theorem 19.2, shared by the cycle map
on Stacks' Chow groups (`MMP.Chow.ChowCycleMapRefinedGysinFormulaAt`) and its applications.

Let `X' = X ×_Y Y'` be a fibre square of complex schemes, with `g : Y' → Y`, `f' : X' → Y'` and
`f : X → Y` a closed immersion. The cap product `g^*(u) ∩ a` of a class `u ∈ H^*(Y, Y - X)` lands
in `H_*(g⁻¹(X(ℂ)))`, and is read in `H_* X'` along the proper map `X'(ℂ) → g⁻¹(X(ℂ))` induced by
`f'`.

## Main definitions

* `MMP.fibreSquarePointsHom`: `X'(ℂ) → g⁻¹(X(ℂ))`.

## Main results

* `MMP.hasProperNeighbourhoodDeformations_preimage_range_map`: `g⁻¹(X(ℂ))` has arbitrarily small
  proper neighbourhood deformations.
* `MMP.isProperMap_fibreSquarePointsHom`: `X'(ℂ) → g⁻¹(X(ℂ))` is proper when `f'` is a closed
  immersion.
* `MMP.cohomologyWithSupports.pullback_forget_apply`: pull-backs commute with forgetting supports.
* `MMP.borelMooreHomology.pushforward_capProductSupportPullback_of_comp_eq`: the projection
  formula through a composite.
* `MMP.borelMooreHomology.capProductSupportPullback_eq_pushforward_of_forget_eq`: cap products
  with supports along two maps.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set

namespace MMP

open UnderlyingSpace

section FibreSquare

variable {X Y X' Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [X'.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))]

/-- For a closed immersion `f : X → Y` and a morphism `g : Y' → Y` of schemes over `ℂ`, with `Y'`
a complex scheme, `g⁻¹(X(ℂ)) ⊆ Y'(ℂ)` has arbitrarily small proper neighbourhood deformations,
so that cap products with supports in it are defined. -/
theorem hasProperNeighbourhoodDeformations_preimage_range_map [IsComplexScheme Y'] (f : X ⟶ Y)
    [IsClosedImmersion f] [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y) [g.IsOver (Spec (.of ℂ))] :
    HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f)) := by
  have h : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)).hom ⁻¹'
      range (UnderlyingSpace.map (K := ℂ) f) =
      pointsOver (K := ℂ) (g.base ⁻¹' range f.base) := by
    rw [range_map_of_isClosedImmersion]
    rfl
  rw [h]
  exact hasProperNeighbourhoodDeformations_pointsOver Y'
    ⟨_, f.isClosedEmbedding.isClosed_range.preimage g.base.hom.continuous⟩

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [f'.IsOver (Spec (.of ℂ))] [g'.IsOver (Spec (.of ℂ))]

/-- For a fibre square `X' = X ×_Y Y'`, `f'` maps `X'(ℂ)` into `g⁻¹(X(ℂ))`. -/
lemma map_mem_preimage_range_of_isPullback (sq : IsPullback f' g' g f)
    (p : UnderlyingSpace ℂ X') :
    UnderlyingSpace.map (K := ℂ) f' p ∈
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f) :=
  range_map_eq_preimage_of_isPullback sq ▸ mem_range_self p

/-- The map `X'(ℂ) → g⁻¹(X(ℂ))` induced by `f'`, for a fibre square `X' = X ×_Y Y'`. -/
def fibreSquarePointsHom (sq : IsPullback f' g' g f) :
    TopCat.of (UnderlyingSpace ℂ X') ⟶
      TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)).hom ⁻¹'
        range (UnderlyingSpace.map (K := ℂ) f)) :=
  TopCat.ofHom ⟨fun p ↦ ⟨UnderlyingSpace.map (K := ℂ) f' p,
    map_mem_preimage_range_of_isPullback sq p⟩,
    (UnderlyingSpace.map (K := ℂ) f').continuous.subtype_mk _⟩

/-- The map `X'(ℂ) → g⁻¹(X(ℂ))` followed by the inclusion `g⁻¹(X(ℂ)) ⊆ Y'(ℂ)` is the map induced
by `f'`. -/
lemma fibreSquarePointsHom_comp_subsetInclusion (sq : IsPullback f' g' g f) :
    fibreSquarePointsHom sq ≫ borelMooreHomology.subsetInclusion _ =
      TopCat.ofHom (UnderlyingSpace.map (K := ℂ) f') :=
  rfl

/-- `X'(ℂ) → g⁻¹(X(ℂ))` is proper, `f'` being a closed immersion. -/
lemma isProperMap_fibreSquarePointsHom [IsClosedImmersion f'] (sq : IsPullback f' g' g f) :
    IsProperMap (fibreSquarePointsHom sq) :=
  (Topology.IsClosedEmbedding.of_comp (f := fibreSquarePointsHom sq)
    Topology.IsEmbedding.subtypeVal
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f')).isProperMap

end FibreSquare

/-- `2(m + d) - 2d = 2m` for natural numbers `m`, `d`, cast to `ℤ`. -/
lemma two_mul_add_sub_two_mul_eq (m d : ℕ) :
    ((2 * (m + d) : ℕ) : ℤ) - ((2 * d : ℕ) : ℤ) = ((2 * m : ℕ) : ℤ) := by
  push_cast; ring

/-- `(m + d) - d = m` for natural numbers `m`, `d`, cast to `ℤ`. -/
lemma natCast_add_sub_natCast (m d : ℕ) : ((m + d : ℕ) : ℤ) - (d : ℤ) = (m : ℤ) := by
  push_cast; ring

universe u

namespace cohomologyWithSupports

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

/-- Pull-backs commute with forgetting supports: `f^* (x|_B) = (f^* x)|_{f⁻¹ B}` for `A ⊆ B`. -/
lemma pullback_forget_apply {Y' Y : TopCat.{u}} (f : Y' ⟶ Y) {A B : Set Y} (hAB : A ⊆ B) (j : ℤ)
    (x : cohomologyWithSupports R M Y A j) :
    (pullback R M f B j).hom ((forget R M Y hAB j).hom x) =
      (forget R M Y' (preimage_mono hAB) j).hom ((pullback R M f A j).hom x) := by
  simp only [forget, pullback]
  erw [relativeSingularCohomology.map_hom_map_hom, relativeSingularCohomology.map_hom_map_hom]
  rfl

end cohomologyWithSupports

namespace borelMooreHomology

variable (R : Type u) [CommRing R]

/-- **Projection formula through a composite, for a map equal to the composite.** For a proper
`ι : C → N'`, maps `g : N' → N` and `F = g ∘ ι`, `Z ⊆ N` closed, `c ∈ H^j(N, N - Z)` and
`x ∈ H_k C`, `ρ_* (F^* c ∩ x) = g^* c ∩ ι_* x` in `H_{k-j}(g⁻¹ Z)`, for any (proper) map
`ρ : F⁻¹ Z → g⁻¹ Z` restricting `ι`. -/
theorem pushforward_capProductSupportPullback_of_comp_eq {C N' N : TopCat.{u}}
    (ι : C ⟶ N') (hι : IsProperMap ι) (g : N' ⟶ N) (F : C ⟶ N) (hF : ι ≫ g = F) {Z : Set N}
    (hZ : IsClosed Z) (hd : HasProperNeighbourhoodDeformations (g ⁻¹' Z))
    (hd' : HasProperNeighbourhoodDeformations (F ⁻¹' Z))
    (ρ : TopCat.of (F ⁻¹' Z) ⟶ TopCat.of (g ⁻¹' Z)) (hρ : ∀ x, (ρ x).1 = ι x.1)
    (hρp : IsProperMap ρ) (j k : ℤ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) N Z j)
    (x : borelMooreHomology R (ModuleCat.of R R) C k) :
    (pushforward R (ModuleCat.of R R) ρ hρp (k - j)).hom
        (capProductSupportPullback R F hZ hd' j k c x) =
      capProductSupportPullback R g hZ hd j k c
        ((pushforward R (ModuleCat.of R R) ι hι k).hom x) := by
  subst hF
  have e : ρ = TopCat.ofHom (ι.hom.restrictPreimage (g ⁻¹' Z)) := by
    ext p
    exact hρ p
  rw [pushforward_congr_eq R e hρp (hι.restrictPreimage (g ⁻¹' Z))]
  exact pushforward_restrictPreimage_capProductSupportPullback_comp R ι hι g hZ hd hd' j k c x

/-- Let `h : W → N`, `h' : W → N'`, `D ⊆ N`, `D' ⊆ N'` closed with `h⁻¹ D ⊆ h'⁻¹ D'`, and
classes `v`, `v'` with supports in `D`, `D'` and `(h^* v)|_{h'⁻¹ D'} = h'^* v'`. Then
`h'^* v' ∩ a = incl_*(h^* v ∩ a)`. -/
theorem capProductSupportPullback_eq_pushforward_of_forget_eq {W N N' : TopCat.{u}} (h : W ⟶ N)
    (h' : W ⟶ N') {D : Set N} {D' : Set N'} (hD : IsClosed D) (hD' : IsClosed D')
    (hd : HasProperNeighbourhoodDeformations (h ⁻¹' D))
    (hd' : HasProperNeighbourhoodDeformations (h' ⁻¹' D')) (hS : h ⁻¹' D ⊆ h' ⁻¹' D')
    {j : ℤ} {v : cohomologyWithSupports R (ModuleCat.of R R) N D j}
    {v' : cohomologyWithSupports R (ModuleCat.of R R) N' D' j}
    (hv : (cohomologyWithSupports.forget R (ModuleCat.of R R) W hS j).hom
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) h D j).hom v) =
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) h' D' j).hom v')
    (k : ℤ) (a : borelMooreHomology R (ModuleCat.of R R) W k) :
    capProductSupportPullback R h' hD' hd' j k v' a =
      (pushforward R (ModuleCat.of R R) (subsetInclusionOfSubset hS)
        (isProperMap_subsetInclusionOfSubset (hD.preimage h.hom.continuous) hS) (k - j)).hom
        (capProductSupportPullback R h hD hd j k v a) := by
  rw [capProductSupportPullback_apply, capProductSupportPullback_apply, ← hv,
    pushforward_subsetInclusionOfSubset_capProductSupport]

end borelMooreHomology

end MMP
