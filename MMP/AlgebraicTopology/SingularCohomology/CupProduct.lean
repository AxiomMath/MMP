module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
/-!
# The cup product on cohomology with supports (Fulton, §19.1)

For closed subsets `X`, `W` of a space `Y` and a commutative ring `R`, the cup product is the
bilinear map
`∪ : H^i(Y, Y - X; R) × H^j(Y, Y - W; R) → H^{i+j}(Y, Y - (X ∩ W); R)`
of singular cohomology (Dold, VII.8). The complements `A = Y - X` and `B = Y - W` are open, so
the couple `{A, B}` is excisive: by the theorem of small chains the chain map `ρ` of
`MMP.SingularChain.smallChainMap` deforms every chain of `A ∪ B = Y - (X ∩ W)` into
the `{A, B}`-small chains, and `[φ] ∪ [ψ] = [ρ^* (φ ∪ ψ)]` for relative cocycles `φ`, `ψ`, where
`φ ∪ ψ` is the Alexander–Whitney cup product of cochains. The cup product vanishes when `i < 0`
or `j < 0`, where the groups are zero.

## Main definitions

* `MMP.cohomologyWithSupports.cup`: the cup product.

## Main results

* `MMP.cohomologyWithSupports.cup_natCast`: in degrees `p, q : ℕ` the cup
  product is the relative cup product `MMP.SingularCochain.relCup` of cocycles,
  through the identification
  `MMP.SingularCochain.relativeSingularCohomologyEquiv`.

## Implementation notes

Coefficients are in any commutative ring `R` (Fulton: `ℤ`, `ℚ`, `ℤ/p`). The cochain map `ρ` is
chain homotopic to the identity by construction (`ρ = 1 - ∂ D - D ∂`), so on the cohomology of
the small chains the product is the naive one.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VII.8.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1 and §3.2.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace MMP

namespace cohomologyWithSupports

open SingularCochain

variable (R : Type u) [CommRing R]

/-- Transport of relative singular cohomology along equalities of the subset and the degree. -/
def congrIndex (Y : TopCat.{u}) {S S' : Set Y} {k k' : ℤ} (hS : S = S') (hk : k = k') :
    relativeSingularCohomology R (ModuleCat.of R R) Y S k ≃ₗ[R]
      relativeSingularCohomology R (ModuleCat.of R R) Y S' k' := by
  subst hS hk
  exact LinearEquiv.refl R _

/-- The cup product in degrees `p, q : ℕ`. -/
def cupNat (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (p q : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X p →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y W q →ₗ[R]
        relativeSingularCohomology R (ModuleCat.of R R) Y (Xᶜ ∪ Wᶜ) (p + q : ℕ) :=
  ((relCup hX.isOpen_compl hW.isOpen_compl p q (p + q) rfl).compl₁₂
      (relativeSingularCohomologyEquiv R Xᶜ p).toLinearMap
      (relativeSingularCohomologyEquiv R Wᶜ q).toLinearMap).compr₂
    (relativeSingularCohomologyEquiv R (Xᶜ ∪ Wᶜ) (p + q)).symm.toLinearMap

/-- Fulton's cup product `H^i(Y, Y - X) ⊗ H^j(Y, Y - W) → H^{i+j}(Y, Y - (X ∩ W))` for closed
subsets `X`, `W` of `Y`, with coefficients in a commutative ring `R` (Dold, VII.8): on classes of
relative cocycles `φ`, `ψ` it is the class of `ρ^* (φ ∪ ψ)`, `ρ` the small-chains deformation for
the open couple `{Y - X, Y - W}`. It is zero in negative degrees. -/
def cup (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (i j : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y X i →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y W j →ₗ[R]
        cohomologyWithSupports R (ModuleCat.of R R) Y (X ∩ W) (i + j) :=
  if h : 0 ≤ i ∧ 0 ≤ j then
    ((cupNat R Y hX hW i.toNat j.toNat).compl₁₂
        (congrIndex R Y rfl (Int.toNat_of_nonneg h.1).symm).toLinearMap
        (congrIndex R Y rfl (Int.toNat_of_nonneg h.2).symm).toLinearMap).compr₂
      (congrIndex R Y (Set.compl_inter X W).symm
        (by rw [Nat.cast_add, Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg h.2])).toLinearMap
  else 0

/-- In degrees `p, q : ℕ` the cup product is the relative cup product of cocycles. -/
lemma cup_natCast (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) (p q : ℕ)
    (φ : cohomologyWithSupports R (ModuleCat.of R R) Y X p)
    (ψ : cohomologyWithSupports R (ModuleCat.of R R) Y W q) :
    cup R Y hX hW p q φ ψ =
      congrIndex R Y (Set.compl_inter X W).symm (Nat.cast_add p q)
        ((relativeSingularCohomologyEquiv R (Xᶜ ∪ Wᶜ) (p + q)).symm
          (relCup (R := R) hX.isOpen_compl hW.isOpen_compl p q (p + q) rfl
            (relativeSingularCohomologyEquiv R Xᶜ p φ)
            (relativeSingularCohomologyEquiv R Wᶜ q ψ))) := by
  have h : (0 : ℤ) ≤ p ∧ (0 : ℤ) ≤ q := ⟨by positivity, by positivity⟩
  simp only [cup, dif_pos h, Int.toNat_natCast]
  rfl

/-- The cup product vanishes in negative degrees. -/
lemma cup_of_neg (Y : TopCat.{u}) {X W : Set Y} (hX : IsClosed X) (hW : IsClosed W) {i j : ℤ}
    (h : i < 0 ∨ j < 0) : cup R Y hX hW i j = 0 := by
  rw [cup, dif_neg]
  omega

end cohomologyWithSupports

end MMP
