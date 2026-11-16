module

public import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Cochains
/-!
# The long exact sequence `H^p(Y, Y - X) → H^p Y → H^p(Y - X) → H^{p+1}(Y, Y - X)`

For a space `Y` and a subset `X ⊆ Y`, with `U = Y - X`, the long exact sequence of the pair
`(Y, U)` in singular cohomology with coefficients in the ring `R`,
```
⋯ → H^p(Y, Y - X) → H^p Y → H^p U → H^{p+1}(Y, Y - X) → H^{p+1} Y → ⋯
```
on Fulton's groups `MMP.cohomologyWithSupports` (§19.1): `H^p(Y, Y - X)` is
`cohomologyWithSupports R R Y X p`, `H^p Y` is `cohomologyWithSupports R R Y univ p` and `H^p U`
is `cohomologyWithSupports R R U univ p`. The first map is the forgetful map
`MMP.cohomologyWithSupports.toCohomology`, the second the restriction to `U`, and
the coboundary `δ` is transported from the cochain-level coboundary
`MMP.SingularCochain.relCohomologyDelta` along
`MMP.SingularCochain.relativeSingularCohomologyEquiv`; on cochains, `δ [ψ] = [δ χ]`
for any cochain `χ` on `Y` extending `ψ` (`delta_mk`). The exactness statements are in the form
`Function.Exact` used by Mathlib's five lemma (`Mathlib.Algebra.FiveLemma`).

## Main definitions

* `MMP.cohomologyWithSupports.restrictCompl`: `H^p Y → H^p(Y - X)`.
* `MMP.cohomologyWithSupports.delta`: `δ : H^p(Y - X) → H^{p+1}(Y, Y - X)`.

## Main results

* `MMP.cohomologyWithSupports.exact_toCohomology_restrictCompl`,
  `exact_restrictCompl_delta`, `exact_delta_toCohomology`: exactness.
* `MMP.cohomologyWithSupports.injective_toCohomology_zero`: in degree `0`.
* `MMP.cohomologyWithSupports.delta_mk`: `δ` on cochains.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u

namespace MMP

namespace cohomologyWithSupports

open SingularCochain SingularChain

variable (R : Type u) [CommRing R] (Y : TopCat.{u}) (X : Set Y)

/-- In the subspace `Y - X`, the complement of `univ` is contained in the preimage of the
complement of `univ` in `Y`. -/
lemma compl_univ_subset_preimage_compl_univ :
    (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ ⊆ subspaceInclusion Y Xᶜ ⁻¹' (Set.univ : Set Y)ᶜ :=
  fun x hx ↦ (hx (mem_univ x)).elim

/-- The preimage in `Y - X` of the complement of `univ` in `Y` is the complement of `univ`. -/
lemma preimage_compl_univ :
    subspaceInclusion Y Xᶜ ⁻¹' (Set.univ : Set Y)ᶜ = (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ := by
  ext; simp

/-- The complement of `univ` in `Y` is contained in `Y - X`. -/
lemma compl_univ_subset_compl : (Set.univ : Set Y)ᶜ ⊆ Xᶜ :=
  compl_subset_compl.mpr (subset_univ X)

/-- The restriction `H^p Y → H^p(Y - X)`. -/
def restrictCompl (p : ℤ) :
    cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ p ⟶
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ p :=
  relativeSingularCohomology.map R _ (subspaceInclusion Y Xᶜ)
    (compl_univ_subset_preimage_compl_univ Y X) p

/-- The coboundary `δ : H^p(Y - X) → H^{p+1}(Y, Y - X)` of the pair `(Y, Y - X)`. -/
def delta (p : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ p →ₗ[R]
      cohomologyWithSupports R (ModuleCat.of R R) Y X (p + 1 : ℕ) :=
  (relativeSingularCohomologyEquiv R Xᶜ (p + 1)).symm.toLinearMap ∘ₗ
    relCohomologyDelta R Xᶜ _ p ∘ₗ (relativeSingularCohomologyEquiv R _ p).toLinearMap

variable {R Y X}

/-- Under `relativeSingularCohomologyEquiv`, `delta` is the cochain-level coboundary
`relCohomologyDelta`. -/
lemma relativeSingularCohomologyEquiv_delta (p : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ p) :
    relativeSingularCohomologyEquiv R Xᶜ (p + 1) (delta R Y X p x) =
      relCohomologyDelta R Xᶜ _ p (relativeSingularCohomologyEquiv R _ p x) := by
  simp [delta]

/-- **`δ` on cochains.** If `x ∈ H^p(Y - X)` is the class of the cocycle `ψ` and `χ` is a cochain
on `Y` with `χ|_{Y - X} = ψ`, then `δ x` is the class of the relative cocycle `δ χ`. -/
theorem delta_mk (p : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ↥Xᶜ) Set.univ p)
    (ψ : relCocycles R (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ p)
    (hx : relativeSingularCohomologyEquiv R _ p x = Submodule.Quotient.mk ψ)
    (χ : Simplex Y p → R) (hχ : cochainPullback R (subspaceInclusion Y Xᶜ) p χ = ψ.1) :
    relativeSingularCohomologyEquiv R Xᶜ (p + 1) (delta R Y X p x) =
      Submodule.Quotient.mk ⟨coboundary R p χ, coboundary_mem_relCocycles_of_cochainPullback (by
        rw [hχ]
        exact ((mem_relCocycles_iff R _ p _).1 ψ.2).2)⟩ := by
  rw [relativeSingularCohomologyEquiv_delta, hx, relCohomologyDelta_mk ψ χ hχ]

/-- Under `relativeSingularCohomologyEquiv`, `toCohomology` is the cochain-level forgetful map
`relCohomologyForget`. -/
lemma relativeSingularCohomologyEquiv_toCohomology (p : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y X p) :
    relativeSingularCohomologyEquiv R (Set.univ : Set Y)ᶜ p ((toCohomology R _ Y X p).hom x) =
      relCohomologyForget R Xᶜ (compl_univ_subset_compl Y X) p
        (relativeSingularCohomologyEquiv R Xᶜ p x) :=
  relativeSingularCohomologyEquiv_map (𝟙 Y) _ p x

/-- Under `relativeSingularCohomologyEquiv`, `restrictCompl` is the cochain-level restriction
`relCohomologyRestrict`. -/
lemma relativeSingularCohomologyEquiv_restrictCompl (p : ℕ)
    (x : cohomologyWithSupports R (ModuleCat.of R R) Y Set.univ p) :
    relativeSingularCohomologyEquiv R _ p ((restrictCompl R Y X p).hom x) =
      relCohomologyRestrict R Xᶜ (preimage_compl_univ Y X) p
        (relativeSingularCohomologyEquiv R (Set.univ : Set Y)ᶜ p x) :=
  relativeSingularCohomologyEquiv_map (subspaceInclusion Y Xᶜ) _ p x

variable (R Y X)

/-- Exactness of `H^p(Y, Y - X) → H^p Y → H^p(Y - X)`. -/
theorem exact_toCohomology_restrictCompl (p : ℕ) :
    Function.Exact (toCohomology R (ModuleCat.of R R) Y X p).hom (restrictCompl R Y X p).hom := by
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := relativeSingularCohomologyEquiv R Xᶜ p)
    (e₂ := relativeSingularCohomologyEquiv R (Set.univ : Set Y)ᶜ p)
    (e₃ := relativeSingularCohomologyEquiv R (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ p)
    (g₁₂ := relCohomologyForget R Xᶜ (compl_univ_subset_compl Y X) p)
    (g₂₃ := relCohomologyRestrict R Xᶜ (preimage_compl_univ Y X) p) ?_ ?_).1
    (exact_relCohomologyForget_relCohomologyRestrict _ _ p)
  · ext x
    exact (relativeSingularCohomologyEquiv_toCohomology p x).symm
  · ext x
    exact (relativeSingularCohomologyEquiv_restrictCompl p x).symm

/-- Exactness of `H^p Y → H^p(Y - X) → H^{p+1}(Y, Y - X)`. -/
theorem exact_restrictCompl_delta (p : ℕ) :
    Function.Exact (restrictCompl R Y X p).hom (delta R Y X p) := by
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := relativeSingularCohomologyEquiv R (Set.univ : Set Y)ᶜ p)
    (e₂ := relativeSingularCohomologyEquiv R (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ p)
    (e₃ := relativeSingularCohomologyEquiv R Xᶜ (p + 1))
    (g₁₂ := relCohomologyRestrict R Xᶜ (preimage_compl_univ Y X) p)
    (g₂₃ := relCohomologyDelta R Xᶜ _ p) ?_ ?_).1
    (exact_relCohomologyRestrict_relCohomologyDelta _ (compl_univ_subset_compl Y X) p)
  · ext x
    exact (relativeSingularCohomologyEquiv_restrictCompl p x).symm
  · ext x
    exact (relativeSingularCohomologyEquiv_delta p x).symm

/-- Exactness of `H^p(Y - X) → H^{p+1}(Y, Y - X) → H^{p+1} Y`. -/
theorem exact_delta_toCohomology (p : ℕ) :
    Function.Exact (delta R Y X p) (toCohomology R (ModuleCat.of R R) Y X (p + 1 : ℕ)).hom := by
  refine (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := relativeSingularCohomologyEquiv R (Set.univ : Set (TopCat.of ↥Xᶜ))ᶜ p)
    (e₂ := relativeSingularCohomologyEquiv R Xᶜ (p + 1))
    (e₃ := relativeSingularCohomologyEquiv R (Set.univ : Set Y)ᶜ (p + 1))
    (g₁₂ := relCohomologyDelta R Xᶜ _ p)
    (g₂₃ := relCohomologyForget R Xᶜ (compl_univ_subset_compl Y X) (p + 1)) ?_ ?_).1
    (exact_relCohomologyDelta_relCohomologyForget (preimage_compl_univ Y X)
      (compl_univ_subset_compl Y X) p)
  · ext x
    exact (relativeSingularCohomologyEquiv_delta p x).symm
  · ext x
    exact (relativeSingularCohomologyEquiv_toCohomology (p + 1) x).symm

/-- In degree `0`, `H^0(Y, Y - X) → H^0 Y` is injective. -/
theorem injective_toCohomology_zero :
    Function.Injective (toCohomology R (ModuleCat.of R R) Y X (0 : ℕ)).hom := by
  intro x y hxy
  apply (relativeSingularCohomologyEquiv R Xᶜ 0).injective
  apply injective_relCohomologyForget_zero (compl_univ_subset_compl Y X)
  rw [← relativeSingularCohomologyEquiv_toCohomology,
    ← relativeSingularCohomologyEquiv_toCohomology, hxy]

end cohomologyWithSupports

end MMP
