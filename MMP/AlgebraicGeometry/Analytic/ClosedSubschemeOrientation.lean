module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProperNeighbourhoodRetract
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.Quot.StacksExists
public import MMP.AlgebraicGeometry.RegularImmersion.OfSmooth

/-!
# Neighbourhood retractions and orientation classes of closed subschemes of complex schemes

Let `Y` be a complex scheme, `j : X → Y` a closed immersion over `ℂ`, and
`X^an = {y ∈ Y^an | y lies over a point of j(X)}` the image of the complex realization of `X` in
that of `Y`. Under the homeomorphism `Y^an ≃ₜ Y(ℂ)` with Fulton's underlying space, `X^an` is the
image of the closed embedding `X(ℂ) → Y(ℂ)`. Since `X(ℂ)` is locally contractible and `Y(ℂ)`
closed-embeds in some `ℝᴺ`, `X^an` is a retract of an open neighbourhood in `Y^an`. When `j` is a
regular closed immersion of codimension `d`
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim`), for instance a
smooth divisor (`d = 1`) in a smooth `Y` (EGA IV 17.12.1), its orientation class
`u ∈ H^{2d}(Y(ℂ), Y(ℂ) - X(ℂ))` gives a class in `H^{2d}(Y^an, Y^an - X^an)`.

## Main definitions

* `ComplexPoints.cohomologyWithSupportsOfUnderlyingSpace`: the transport
  `H^n(Y(ℂ), Y(ℂ) - X(ℂ)) → H^n(Y^an, Y^an - X^an)`.

## Main results

* `ComplexPoints.exists_isOpen_retraction_of_isClosedImmersion`: `X^an` is closed in `Y^an` and
  is a retract of an open neighbourhood.
* `ComplexPoints.exists_isRegularImbeddingOrientationClass_of_isRegularClosedImmersionOfCodim`:
  a regular closed immersion of codimension `d` has an orientation class in
  `H^{2d}(Y^an, Y^an - X^an)`.
* `ComplexPoints.exists_isRegularImbeddingOrientationClass_of_smoothOfRelativeDimension`: a
  smooth divisor in a smooth complex scheme is a regular closed immersion of codimension one,
  with an orientation class in `H²(Y^an, Y^an - X^an)`.

## Implementation notes

The retraction is obtained on `Y(ℂ)` from its closed embedding in some `ℝᴺ` and the local
contractibility of `X(ℂ)`, not from a manifold structure on `Y^an`; it needs no smoothness. The
orientation class is stated as the transport of a class satisfying
`MMP.Modules.IsRegularImbeddingOrientationClass` on `Y(ℂ)` (orientation data on the vector
bundle `𝐕(ℰ)` of a quasi-coherent `𝒪_Y`-module `ℰ`).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology Set MMP
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

namespace MMP.Analytic.ComplexPoints

variable {Y X : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))]
  (j : X ⟶ Y) [IsClosedImmersion j] [j.IsOver (Spec (.of ℂ))]

/-- The points of `Y^an` over the image of a closed immersion `j : X → Y` are the preimage, under
the identification `Y^an ≃ₜ Y(ℂ)`, of the image of `X(ℂ) → Y(ℂ)`. -/
lemma preimage_homeomorphUnderlyingSpace_range_map :
    homeomorphUnderlyingSpace ⁻¹' range (UnderlyingSpace.map (K := ℂ) j) =
      {y : ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ range j} := by
  ext y
  change homeomorphUnderlyingSpace y ∈ range (UnderlyingSpace.mapFun (K := ℂ) j) ↔ _
  rw [UnderlyingSpace.range_mapFun_of_isClosedImmersion]
  change y.hom (IsLocalRing.closedPoint ℂ) ∈ range j ↔ y.hom default ∈ range j
  have key : ∀ a b : Spec (.of ℂ), y.hom a ∈ range j ↔ y.hom b ∈ range j := fun a b ↦ by
    rw [Subsingleton.elim a b]
  exact key _ _

/-- **A closed subscheme of a complex scheme is a neighbourhood retract in the classical
topology** (Fulton, §19.1). For a closed immersion `j : X → Y` over `ℂ` into a complex scheme, the
set `X^an` of points of `Y^an` lying over `j(X)` is closed, and there are an open neighbourhood
`U` of `X^an` and a retraction `r : U → X^an`. -/
theorem exists_isOpen_retraction_of_isClosedImmersion [IsComplexScheme Y] :
    IsClosed {y : ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ range j} ∧
      ∃ U : Set (ComplexPoints (Y ↘ Spec (.of ℂ))), IsOpen U ∧
        {y : ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ range j} ⊆ U ∧
        ∃ r : C(U, {y : ComplexPoints (Y ↘ Spec (.of ℂ)) | y.toScheme ∈ range j}),
          ∀ y : U, (y : ComplexPoints (Y ↘ Spec (.of ℂ))).toScheme ∈ range j →
            (r y : ComplexPoints (Y ↘ Spec (.of ℂ))) = y := by
  rw [← preimage_homeomorphUnderlyingSpace_range_map j]
  set h := homeomorphUnderlyingSpace (X := Y)
  have hj := UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) j
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := by
    rw [← comp_over j (Spec (.of ℂ))]; infer_instance
  have hA : HasOpenContractibleBasis (range (UnderlyingSpace.map (K := ℂ) j)) :=
    (UnderlyingSpace.hasOpenContractibleBasis X).of_homeomorph hj.isEmbedding.toHomeomorph
  obtain ⟨N, -, hAN, r, -, hr⟩ :=
    UnderlyingSpace.exists_isClosed_isProperMap_retraction Y hj.isClosed_range hA
  refine ⟨hj.isClosed_range.preimage h.continuous, h ⁻¹' interior N,
    isOpen_interior.preimage h.continuous, fun y hy ↦ hAN hy, ?_⟩
  let r' : C(h ⁻¹' interior N, h ⁻¹' range (UnderlyingSpace.map (K := ℂ) j)) :=
    { toFun := fun y ↦ ⟨h.symm (r ⟨h y, interior_subset y.2⟩), by
        simp only [mem_preimage, Homeomorph.apply_symm_apply]; exact (r _).2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (h.symm.continuous.comp (continuous_subtype_val.comp
          (r.continuous.comp (Continuous.subtype_mk (h.continuous.comp
            continuous_subtype_val) _)))) _ }
  refine ⟨r', fun y hy ↦ ?_⟩
  have hy' : (y : ComplexPoints (Y ↘ Spec (.of ℂ))) ∈
      h ⁻¹' range (UnderlyingSpace.map (K := ℂ) j) := by
    rw [preimage_homeomorphUnderlyingSpace_range_map]; exact hy
  change h.symm (r ⟨h y, _⟩ : UnderlyingSpace ℂ Y) = y
  rw [hr ⟨h y, _⟩ hy', Homeomorph.symm_apply_apply]

variable (R : Type) [CommRing R]

/-- Transport of cohomology with supports in `X(ℂ) ⊆ Y(ℂ)` to cohomology with supports in
`X^an ⊆ Y^an`, along the homeomorphism `Y^an ≃ₜ Y(ℂ)`. -/
def cohomologyWithSupportsOfUnderlyingSpace (n : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
        (range (UnderlyingSpace.map (K := ℂ) j)) n ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (ComplexPoints (Y ↘ Spec (.of ℂ))))
        {y | y.toScheme ∈ range j} n :=
  cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom ⟨_, (homeomorphUnderlyingSpace (X := Y)).continuous⟩) _ n ≫
    cohomologyWithSupports.forget R (ModuleCat.of R R) _
      (preimage_homeomorphUnderlyingSpace_range_map j).le n

/-- **Orientation classes of regular imbeddings on the complex realization** (Fulton, §19.2). A
regular closed immersion `j : X → Y` of codimension `d` into a complex scheme has a class
`u ∈ H^{2d}(Y^an, Y^an - X^an; R)` which, under `Y^an ≃ₜ Y(ℂ)`, is an orientation class of `j`. -/
theorem exists_isRegularImbeddingOrientationClass_of_isRegularClosedImmersionOfCodim
    [IsComplexScheme Y] {d : ℕ} (hj : IsRegularClosedImmersionOfCodim j d) :
    ∃ u : cohomologyWithSupports R (ModuleCat.of R R)
        (TopCat.of (ComplexPoints (Y ↘ Spec (.of ℂ)))) {y | y.toScheme ∈ range j} (2 * d : ℕ),
      ∃ u₀, MMP.Modules.IsRegularImbeddingOrientationClass R j d u₀ ∧
        (cohomologyWithSupportsOfUnderlyingSpace j R (2 * d : ℕ)).hom u₀ = u := by
  obtain ⟨u₀, hu₀⟩ := MMP.Modules.exists_isRegularImbeddingOrientationClass R hj
  exact ⟨_, u₀, hu₀, rfl⟩

/-- **The orientation class of a smooth divisor** (Fulton, §19.2). Let `j : X → Y` be a closed
immersion over `ℂ` into a complex scheme, with `Y` smooth of relative dimension `n + 1` and `X`
smooth of relative dimension `n` over `ℂ`. Then `j` is a regular closed immersion of codimension
one, and there is a class `u ∈ H²(Y^an, Y^an - X^an; R)` which, under `Y^an ≃ₜ Y(ℂ)`, is an
orientation class of `j`. -/
theorem exists_isRegularImbeddingOrientationClass_of_smoothOfRelativeDimension
    [IsComplexScheme Y] {n : ℕ} [SmoothOfRelativeDimension (n + 1) (Y ↘ Spec (.of ℂ))]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] :
    IsRegularClosedImmersionOfCodim j 1 ∧
      ∃ u : cohomologyWithSupports R (ModuleCat.of R R)
          (TopCat.of (ComplexPoints (Y ↘ Spec (.of ℂ)))) {y | y.toScheme ∈ range j} (2 : ℕ),
        ∃ u₀, MMP.Modules.IsRegularImbeddingOrientationClass R j 1 u₀ ∧
          (cohomologyWithSupportsOfUnderlyingSpace j R (2 : ℕ)).hom u₀ = u := by
  have : SmoothOfRelativeDimension n (j ≫ Y ↘ Spec (.of ℂ)) := by
    rw [comp_over]; infer_instance
  have hreg : IsRegularClosedImmersionOfCodim j 1 :=
    isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension j (Y ↘ Spec (.of ℂ)) (n := n)
  exact ⟨hreg,
    exists_isRegularImbeddingOrientationClass_of_isRegularClosedImmersionOfCodim j R hreg⟩

end MMP.Analytic.ComplexPoints
