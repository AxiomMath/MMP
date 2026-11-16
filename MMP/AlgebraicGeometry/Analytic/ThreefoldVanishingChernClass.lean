module

public import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary

/-!
# Divisors with vanishing first Chern class on a smooth projective threefold

Let `X` be a smooth projective complex threefold. Every prime divisor `P` of `X` is Cartier;
choose a Cartier divisor `π(P)` whose Weil divisor is `P`. For a `ℚ`-divisor `x = ∑_P x_P P`, the
rational first Chern class of `x` is `∑_P x_P c₁(𝒪_X(π(P))) ∈ H²(X^an; ℚ)`. Capping with the
fundamental class `[X]` sends `c₁(𝒪_X(π(P)))` to the class `[P] ∈ H_4(X, ℚ)`, so a `ℚ`-divisor
with vanishing rational first Chern class has vanishing class in `H_4(X, ℚ)`.

This is the last step of the equality case of the threefold index theorems, which conclude with
the vanishing of a rational combination of first Chern classes.

## Main results

* `MMP.Fourfold.divisorClass_eq_zero_of_sum_smul_mapCoeff_algebraicFirstChernClass_eq_zero`:
  `∑_P x_P c₁(𝒪_X(π(P))) = 0` in `H²(X^an; ℚ)` implies `[x] = 0` in `H_4(X, ℚ)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

public section

open AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Analytic MMP.Mori

/-- **A `ℚ`-divisor with vanishing rational first Chern class has vanishing homology class.**
Let `X` be a smooth projective complex threefold, `π(P)` a Cartier divisor with Weil divisor `P`
for every prime divisor `P`, and `x` a `ℚ`-divisor on `X`. If
`∑_P x_P c₁(𝒪_X(π(P))) = 0` in `H²(X^an; ℚ)`, then `[x] = 0` in `H_4(X, ℚ)`. -/
theorem divisorClass_eq_zero_of_sum_smul_mapCoeff_algebraicFirstChernClass_eq_zero
    {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsLocallyNoetherian X]
    [IsNormal X] (hX : Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ)))
    (hsm : Mori.IsSmoothScheme (X ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim X = 3)
    (π : Mori.PrimeDivisor X → X.CartierDivisor)
    (hπ : ∀ P, MMP.Intersection.IsWeilDivisorOfCartier (π P) (Finsupp.single P 1))
    (x : Mori.QDivisor X)
    (hx : Finsupp.linearCombination ℚ (fun Q => singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π Q)))) x = 0) :
    Chow.divisorClass X x = 0 := by
  have : IsIntegral X := ((Mori.isProjectiveVariety_iff _ _).1 hX).1.toIsIntegral
  have : CompactSpace X :=
    (quasiCompact_iff_compactSpace (X ↘ Spec (.of ℂ))).mp inferInstance
  have hdimX : topologicalKrullDim X = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  have hgen : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ))
      (_root_.genericPoint X) = ((2 + 1 : ℕ) : ℤ) :=
    MMP.Chow.relativeDimension_genericPoint_eq ℂ _ hdimX
  let Ψ := (BorelMooreCross.congrDegree ℚ (TopCat.of (UnderlyingSpace ℂ X))
      (by norm_num : ((2 * (2 + 1) : ℕ) : ℤ) - 2 = ((2 * 2 : ℕ) : ℤ))).toLinearMap ∘ₗ
    (borelMooreHomology.capProductPullback ℚ
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩ :
        TopCat.of (UnderlyingSpace ℂ X) ⟶ Analytification.space (X ↘ Spec (.of ℂ)))
      Set.univ 2 ((2 * (2 + 1) : ℕ) : ℤ)).flip
      (Chow.rationalCycleClass X (2 + 1)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          ((2 + 1 : ℕ) : ℤ) (_root_.genericPoint X) hgen))
  have hQ : ∀ Q : Mori.PrimeDivisor X, Chow.divisorClass X (Finsupp.single Q 1) =
      Ψ (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (MMP.CartierDivisor.sheaf (π Q)))) := by
    intro Q
    have hcQ := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
      (Finsupp.single Q 1 : Mori.Divisor X)
    have := hcQ.isInvertibleModule_divisorialSheaf
    have hsingle : Mori.Divisor.toQDivisor (Finsupp.single Q (1 : ℤ)) =
        ((1 : ℕ) : ℤ) • (Finsupp.single Q (1 : ℚ)) := by
      rw [Nat.cast_one, one_smul]
      ext E
      change ((Finsupp.single Q (1 : ℤ) E : ℤ) : ℚ) = _
      by_cases h : Q = E <;> simp [h, DivisorWithCoeffs.coeff_apply]
    have h := (smul_rationalCycleClass_eq_capProductPullback hX hsm hdimX
      (Finsupp.single Q 1) one_pos (Finsupp.single Q 1) hsingle (_root_.genericPoint X) hgen).1
    rw [Nat.cast_one, one_smul] at h
    obtain ⟨eQ⟩ := (hπ Q).nonempty_sheaf_iso_divisorialSheaf
    rw [algebraicFirstChernClass_eq_of_iso eQ]
    exact h
  have hx' : x = ∑ Q ∈ x.support, x Q • Finsupp.single Q (1 : ℚ) := by
    conv_lhs => rw [← Finsupp.sum_single x]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun Q _ => (Finsupp.smul_single_one _ _).symm
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hx
  rw [hx', map_sum]
  simp_rw [map_smul, hQ, ← map_smul, ← map_sum]
  rw [hx, map_zero]

end MMP.Fourfold
