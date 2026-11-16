module

public import MMP.AlgebraicTopology.LocalizedFirstChern.BallChart

/-!
# The cap product with a local orientation class in a holomorphic vector chart (Fulton, §19.1)

Let `P` be a complex manifold of dimension `m + r` and `Θ : P ≅ B × ℂʳ` a homeomorphism onto the
product of a connected complex manifold `B` of dimension `m` and `ℂʳ`, holomorphic in charts with
injective derivative. Put `g = pr₂ ∘ Θ : P → ℂʳ` and `Y = g⁻¹(0)`, so that `y ↦ (Θ y).1` is a
homeomorphism `Y ≅ B`. For the local orientation class `u₀ ∈ H^{2r}(ℂʳ, ℂʳ - 0)` of `ℂʳ` at `0`
(complex orientation), the cap product `g^* u₀ ∩ μ_P ∈ H_{2m} Y` is carried to the fundamental
class `μ_B`.

The derivative of `Θ` in charts is an injective complex linear map, hence has positive real
determinant for the complex orientations; so `Θ` preserves the complex orientation of `ℂᵐ⁺ʳ` and
the product of the complex orientations of `ℂᵐ` and `ℂʳ`, and the computation in a product chart
(`IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback`) applies.

## Main results

* `MMP.complexOrientationBasis_eq_complexRealBasis`: the complex orientation basis
  of `ℂʳ` is the real basis attached to the standard complex basis.
* `MMP.det_prod_complexOrientationBasis_pos`: an injective complex linear map
  `ℂᵐ⁺ʳ → ℂᵐ × ℂʳ` has positive real determinant for the complex orientations.
* `MMP.isOrientationPreserving_of_injective_complex_fderiv_prod`: a homeomorphism
  `P ≅ B × ℂʳ`, holomorphic in charts with injective derivative, preserves complex orientations.
* `MMP.IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complexVector`:
  `g^* u₀ ∩ μ_P` is carried to `μ_B`.

## Implementation notes

The fundamental class of `P` lives in degree `2 * (m + r)`, while the product chart computation
is stated in degree `2 * m + 2 * r`; the two are matched by an intermediate statement for a
degree `N` with `N = n + k`, in which the orientation of the product is reindexed along
`Fin (n + k) ≃ Fin N`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open Set CategoryTheory Topology

namespace MMP

open MMP

open FundamentalClass borelMooreHomology BorelMooreCross BorelMooreCap ThomClass

/-! ### Complex orientations of `ℂᵐ × ℂʳ` -/

section ComplexBasis

/-- The complex orientation basis of `ℂʳ` is the real basis `complexRealBasis` attached to the
standard complex basis `Pi.basisFun ℂ (Fin r)`. -/
lemma complexOrientationBasis_eq_complexRealBasis (r : ℕ) :
    complexOrientationBasis r = complexRealBasis (Pi.basisFun ℂ (Fin r)) := by
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  simp [complexRealBasis]

/-- An injective complex linear map `ℂᵐ⁺ʳ → ℂᵐ × ℂʳ` has positive real determinant for the
complex orientation basis of `ℂᵐ⁺ʳ` and the product of the complex orientation bases of `ℂᵐ` and
`ℂʳ`. -/
theorem det_prod_complexOrientationBasis_pos {m r : ℕ}
    {N : EuclideanSpace ℂ (Fin (m + r)) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) × (Fin r → ℂ)}
    (hN : Function.Injective N) :
    0 < ((((euclideanComplexOrientationBasis m).prod (complexOrientationBasis r)).reindex
      finSumFinEquiv).reindex (finCongr (Nat.mul_add 2 m r).symm)).det
        ((N.restrictScalars ℝ) ∘ euclideanComplexOrientationBasis (m + r)) := by
  have h := complexRealBasis_det_pos (PiLp.basisFun 2 ℂ (Fin (m + r)))
    (((PiLp.basisFun 2 ℂ (Fin m)).prod (Pi.basisFun ℂ (Fin r))).reindex finSumFinEquiv) hN
  have hb := prod_complexRealBasis (PiLp.basisFun 2 ℂ (Fin m)) (Pi.basisFun ℂ (Fin r))
  rw [← complexOrientationBasis_eq_complexRealBasis,
    ← euclideanComplexOrientationBasis_eq_complexRealBasis] at hb
  have hb' : ((((euclideanComplexOrientationBasis m).prod (complexOrientationBasis r)).reindex
      finSumFinEquiv).reindex (finCongr (Nat.mul_add 2 m r).symm)) =
      complexRealBasis (((PiLp.basisFun 2 ℂ (Fin m)).prod (Pi.basisFun ℂ (Fin r))).reindex
        finSumFinEquiv) := by
    rw [hb]
    refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
    simp
  rw [hb', euclideanComplexOrientationBasis_eq_complexRealBasis]
  exact h

end ComplexBasis

/-! ### Holomorphic product charts preserve complex orientations -/

section Orientation

variable {P B : Type} [TopologicalSpace P] [TopologicalSpace B] {m r : ℕ}
  [ChartedSpace (EuclideanSpace ℂ (Fin (m + r))) P] [ChartedSpace (EuclideanSpace ℂ (Fin m)) B]

/-- **Holomorphic product charts preserve complex orientations.** If `Θ : P ≅ B × ℂʳ` is
holomorphic in charts with injective derivative, then `Θ` is orientation preserving from the
complex orientation of `ℂᵐ⁺ʳ` to the product of the complex orientations of `ℂᵐ` and `ℂʳ`. -/
theorem isOrientationPreserving_of_injective_complex_fderiv_prod (Θ : P ≃ₜ B × (Fin r → ℂ))
    (hΘ : ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (m + r))) P,
      ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin m)) B, ∀ x ∈ c.source, (Θ x).1 ∈ c'.source →
        ∃ L : EuclideanSpace ℂ (Fin (m + r)) →L[ℂ] EuclideanSpace ℂ (Fin m) × (Fin r → ℂ),
          Function.Injective L ∧
          HasFDerivAt (fun y ↦ (c' (Θ (c.symm y)).1, (Θ (c.symm y)).2)) L (c x)) :
    IsOrientationPreserving (H' := ModelProd (EuclideanSpace ℂ (Fin m)) (Fin r → ℂ))
      (euclideanComplexOrientationBasis (m + r))
      ((((euclideanComplexOrientationBasis m).prod (complexOrientationBasis r)).reindex
        finSumFinEquiv).reindex (finCongr (Nat.mul_add 2 m r).symm)) Θ := by
  apply isOrientationPreserving_of_hasFDerivAt
  intro c hc e' he' x hx hx'
  obtain ⟨c', hc', e₂, he₂, rfl⟩ := he'
  rw [chartedSpaceSelf_atlas] at he₂
  subst he₂
  have hx1 : (Θ x).1 ∈ c'.source := hx'.1
  obtain ⟨L, hLi, hL⟩ := hΘ c hc c' hc' x hx hx1
  have hL' : HasFDerivAt (fun y ↦ (c' (Θ (c.symm y)).1, (Θ (c.symm y)).2))
      (L.restrictScalars ℝ) (c x) := hL.restrictScalars ℝ
  have hdet := det_prod_complexOrientationBasis_pos
      (N := (L : EuclideanSpace ℂ (Fin (m + r)) →ₗ[ℂ] _)) hLi
  exact ⟨L.restrictScalars ℝ, hL', hdet⟩

end Orientation

/-! ### The cap product in a holomorphic vector chart -/

section ProductChart

variable (R : Type) [CommRing R]
  {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H]
  [ContinuousSMul ℝ H]
  {H' : Type*} [AddCommGroup H'] [Module ℝ H'] [TopologicalSpace H'] [ContinuousAdd H']
  [ContinuousSMul ℝ H'] [T2Space H']
  {P : Type} [TopologicalSpace P] [T2Space P] [ChartedSpace H P]
  {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace H' X]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- `IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback` for a
fundamental class of `P` in a degree `N` equal to `n + k`, the product orientation of `X × F`
being reindexed along `Fin (n + k) ≃ Fin N`. -/
theorem IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_of_eq_add
    [ConnectedSpace X] [SecondCountableTopology X] [TopologicalSpace.MetrizableSpace X]
    {n k N : ℕ} (hN : N = n + k) (hk : Even k) {b : Module.Basis (Fin N) ℝ H}
    {b' : Module.Basis (Fin n) ℝ H'} {bF : Module.Basis (Fin k) ℝ F}
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (N : ℕ)}
    (hμP : IsFundamentalClass R b μP)
    {μX : borelMooreHomology R (ModuleCat.of R R) (TopCat.of X) n}
    (hμX : IsFundamentalClass R b' μX)
    (Θ : P ≃ₜ X × F)
    (hΘ : IsOrientationPreserving (H' := ModelProd H' F) b
      (((b'.prod bF).reindex finSumFinEquiv).reindex (finCongr hN.symm)) Θ)
    (g : TopCat.of P ⟶ TopCat.of F) (hg : ∀ p, g p = (Θ p).2)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0} k}
    (hu₀ : IsLocalOrientationClass R bF (0 : TopCat.of F) u₀)
    (hdeg : ((N : ℕ) : ℤ) - (k : ℕ) = (n : ℕ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (zeroFibreHomeomorph Θ g hg : C(g ⁻¹' {0}, X)))
        (zeroFibreHomeomorph Θ g hg).isProperMap n).hom
      (congrDegree R _ hdeg
        (capProductSupportPullback R g isClosed_singleton
          (hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd Θ g hg) (k : ℕ) (N : ℕ)
          u₀ μP)) = μX := by
  subst hN
  rw [finCongr_refl, Module.Basis.reindex_refl] at hΘ
  exact hμP.pushforward_zeroFibreHomeomorph_capProductSupportPullback R hk hμX Θ hΘ g hg hu₀ _ hdeg

end ProductChart

section VectorChart

variable (R : Type) [CommRing R]

/-- **`g^* u₀ ∩ μ_P = μ_B` in a holomorphic vector chart.** Let `P` be a complex manifold of
dimension `m + r` with fundamental class `μ_P` (complex orientation), and `Θ : P ≅ B × ℂʳ` a
homeomorphism onto the product of a connected, second countable, metrizable complex manifold `B`
of dimension `m` (fundamental class `μ_B`) and `ℂʳ`, holomorphic in charts with injective
derivative. Let `g = pr₂ ∘ Θ : P → ℂʳ` and `u₀ ∈ H^{2r}(ℂʳ, ℂʳ - 0)` the local orientation class
of `ℂʳ` at `0` for its complex orientation. Then the homeomorphism `g⁻¹(0) ≅ B`,
`y ↦ (Θ y).1`, carries `g^* u₀ ∩ μ_P ∈ H_{2m}(g⁻¹ 0)` to `μ_B`. -/
theorem IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complexVector
    {P B : Type} [TopologicalSpace P] [TopologicalSpace B] {m r : ℕ}
    [T2Space P] [ChartedSpace (EuclideanSpace ℂ (Fin (m + r))) P]
    [T2Space B] [ConnectedSpace B] [SecondCountableTopology B] [TopologicalSpace.MetrizableSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin m)) B]
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (2 * (m + r) : ℕ)}
    (hμP : IsFundamentalClass R (euclideanComplexOrientationBasis (m + r)) μP)
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * m : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis m) μB)
    (Θ : P ≃ₜ B × (Fin r → ℂ))
    (hΘ : ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (m + r))) P,
      ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin m)) B, ∀ x ∈ c.source, (Θ x).1 ∈ c'.source →
        ∃ L : EuclideanSpace ℂ (Fin (m + r)) →L[ℂ] EuclideanSpace ℂ (Fin m) × (Fin r → ℂ),
          Function.Injective L ∧
          HasFDerivAt (fun y ↦ (c' (Θ (c.symm y)).1, (Θ (c.symm y)).2)) L (c x))
    (g : TopCat.of P ⟶ TopCat.of (Fin r → ℂ)) (hg : ∀ p, g p = (Θ p).2)
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (Fin r → ℂ)) {0} (2 * r : ℕ)}
    (hu₀ : IsLocalOrientationClass R (complexOrientationBasis r) (0 : TopCat.of (Fin r → ℂ)) u₀)
    (hdeg : ((2 * (m + r) : ℕ) : ℤ) - (2 * r : ℕ) = (2 * m : ℕ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (zeroFibreHomeomorph Θ g hg : C(g ⁻¹' {0}, B)))
        (zeroFibreHomeomorph Θ g hg).isProperMap (2 * m : ℕ)).hom
      (congrDegree R _ hdeg
        (capProductSupportPullback R g isClosed_singleton
          (hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd Θ g hg) (2 * r : ℕ)
          (2 * (m + r) : ℕ) u₀ μP)) = μB :=
  hμP.pushforward_zeroFibreHomeomorph_capProductSupportPullback_of_eq_add R (Nat.mul_add 2 m r)
    (even_two_mul r) hμB Θ (isOrientationPreserving_of_injective_complex_fderiv_prod Θ hΘ) g hg
    hu₀ hdeg

end VectorChart

end MMP
