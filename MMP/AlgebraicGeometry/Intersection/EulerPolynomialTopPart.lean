module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ComponentsVanishing

/-!
# The top part of the Euler polynomial is additive with generic lengths

Let `X` be a scheme proper over a field `k`, let `F` be a coherent `𝒪_X`-module with
`dim Supp F ≤ d` and let `L₁, …, L_r` be invertible `𝒪_X`-modules. The function
`n ↦ χ(X, F ⊗ L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` on `ℤ^r` is a rational polynomial `P` (Snapper). For
each integral closed subscheme `Z_j ⊆ Supp F` of dimension `d`, with generic point `η_j`, let
`Q_j` be the polynomial of `n ↦ χ(Z_j, (L₁|_{Z_j})^{n₁} ⊗ ⋯ ⊗ (L_r|_{Z_j})^{n_r})`. Then the
degree-`d` homogeneous component of `P` is
`∑_j length_{𝒪_{X,η_j}}(F_{η_j}) · (degree-d component of Q_j)`.

## Main results

* `MMP.Foundations.homogeneousComponent_eulerPolynomial_eq_sum_dimComponents`: the degree-`d`
  homogeneous component of the Euler polynomial of `F` is the length-weighted sum of those of
  the structure sheaves of the `d`-dimensional integral components of `Supp F`.

## Implementation notes

The components are indexed by `AlgebraicGeometry.DimIntegralSubscheme F d`, the integral closed
subschemes of `X` (with their reduced structure) contained in `Supp F` and of dimension exactly
`d`; since `dim Supp F ≤ d`, these are the irreducible components of `Supp F` of dimension `d`.
The length of `F` at the generic point is `Stacks.Chow.sheafMultiplicity`. The Euler
polynomials are not named: a rational polynomial in `r` variables is determined by its values
on `ℤ^r`, so the statement is made for any polynomials interpolating the Euler characteristic
functions.

When `dim Supp F = d` the statement is the degree-`d` part of [Stacks, Tag 0BEN]
(`AlgebraicGeometry.exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt`); when
`dim Supp F < d` both sides vanish, by [Stacks, Tag 0BEM] and because there are no components
of dimension `d`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.36
* [Stacks Project, Tag 0BEN](https://stacks.math.columbia.edu/tag/0BEN)
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Foundations

/-- **The top Euler-polynomial part is additive with generic lengths.** Let `X` be proper over
a field `k` via `f`, let `F` be coherent with `dim Supp F ≤ d` and let `L₁, …, L_r` be
invertible. If `P(n) = χ(X, F(n₁L₁ + ⋯ + n_rL_r))` for all `n ∈ ℤ^r` and, for each integral
closed subscheme `Z ⊆ Supp F` of dimension `d`, `Q_Z(n) = χ(Z, 𝒪_Z(n₁L₁|_Z + ⋯ + n_rL_r|_Z))`,
then the degree-`d` homogeneous component of `P` is the sum over these `Z` of
`length_{𝒪_{X,η_Z}} F_{η_Z}` times the degree-`d` homogeneous component of `Q_Z`. -/
@[mmp "lem_mmp_foundation_euler_top_part_fundamental_cycle"]
public theorem homogeneousComponent_eulerPolynomial_eq_sum_dimComponents
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.Modules) (hF : SheafOfModules.IsCoherent F) (d : ℕ)
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ (d : WithBot ℕ∞))
    {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
    (P : MvPolynomial (Fin r) ℚ)
    (hP : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
        (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ))
    (Q : DimIntegralSubscheme F d → MvPolynomial (Fin r) ℚ)
    (hQ : ∀ (Z : DimIntegralSubscheme F d) (n : Fin r → ℤ),
      MvPolynomial.eval (fun j => (n j : ℚ)) (Q Z) =
        (@eulerCharacteristic k _ Z.1.subscheme (Z.1.subschemeι ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.1.subscheme.ringCatSheaf)
            (fun j => (Scheme.Modules.pullback Z.1.subschemeι).obj (L j)) n)
          (isCoherent_twistedSheafUnitPullback k f Z.1.subschemeι L n) : ℚ)) :
    MvPolynomial.homogeneousComponent d P =
      ∑ᶠ Z : DimIntegralSubscheme F d,
        (Stacks.Chow.sheafMultiplicity F Z.genericPt : ℚ) •
          MvPolynomial.homogeneousComponent d (Q Z) := by
  rcases lt_or_eq_of_le hdim with hlt | heq
  · have := isEmpty_dimIntegralSubscheme_of_topologicalKrullDim_lt F hlt
    rw [finsum_of_isEmpty]
    obtain ⟨R, hdeg, hR⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k f L F hF
    rw [MvPolynomial.eq_of_eval_intCast_eq fun n => (hP n).trans (hR n).symm]
    rcases hdeg with h0 | hdeg
    · rw [h0, map_zero]
    refine MvPolynomial.homogeneousComponent_eq_zero _ _ ?_
    exact_mod_cast lt_of_le_of_lt hdeg hlt
  · have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
    have : F.IsCoherent := hF
    let e : DimIntegralSubscheme F d ≃ TopDimIntegralSubscheme F :=
      { toFun := fun W => ⟨W.1, W.2.1, W.2.2.1, by rw [heq]; exact W.2.2.2⟩
        invFun := fun W => ⟨W.1, W.2.1, W.2.2.1, by rw [← heq]; exact W.2.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have : Finite (TopDimIntegralSubscheme F) := finite_topDimIntegralSubscheme k f F
    have : Finite (DimIntegralSubscheme F d) := Finite.of_equiv _ e.symm
    have : Fintype (DimIntegralSubscheme F d) := Fintype.ofFinite _
    obtain ⟨R, hdeg, hR⟩ :=
      exists_eulerPolynomial_sub_topDimComponents_totalDegree_lt k f L F
    have hPR : P = R + ∑ Z : DimIntegralSubscheme F d,
        MvPolynomial.C (Stacks.Chow.sheafMultiplicity F Z.genericPt : ℚ) * Q Z := by
      refine MvPolynomial.eq_of_eval_intCast_eq fun n => ?_
      rw [map_add, hR n, hP n, map_sum, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
      have hsum : ∑ Z : DimIntegralSubscheme F d,
            (Stacks.Chow.sheafMultiplicity F (e Z).genericPt : ℚ) *
              (componentTwistEulerCharacteristic k f L (e Z) n : ℚ) =
          ∑ Z : DimIntegralSubscheme F d, MvPolynomial.eval (fun j => (n j : ℚ))
            (MvPolynomial.C (Stacks.Chow.sheafMultiplicity F Z.genericPt : ℚ) * Q Z) := by
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hQ Z n]
        rfl
      rw [hsum, sub_add_cancel]
    rw [hPR, map_add, map_sum, finsum_eq_sum_of_fintype]
    have hR0 : MvPolynomial.homogeneousComponent d R = 0 := by
      rcases hdeg with h0 | hdeg
      · rw [h0, map_zero]
      refine MvPolynomial.homogeneousComponent_eq_zero _ _ ?_
      rw [heq] at hdeg
      exact_mod_cast hdeg
    rw [hR0, zero_add]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul]

end MMP.Foundations
