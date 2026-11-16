module

public import MMP.AlgebraicTopology.ThomClass.Isomorphism.Basic
public import MMP.AlgebraicTopology.ThomClass.Natural

/-!
# Thom classes framed by `ℂⁿ`

For a complex topological vector bundle `E → B` with model fibre `F` and `n = dim F`, the
Thom-class condition with the fibres framed by `ℂⁿ`, its transport along `H^{2 dim F} = H^{2n}`
and Thom's theorem in that form.

## Main definitions

* `MMP.ThomClass.IsThomClassOfRank`: the Thom-class condition with the fibres framed by `ℂⁿ`.

## Main results

* `MMP.ThomClass.isThomClassOfRank_cast_iff`: for `dim F = n`, the condition in degree `2n` is
  the Thom-class condition transported along `H^{2 dim F} = H^{2n}`.
* `MMP.ThomClass.existsUnique_isThomClassOfRank`: there is exactly one class satisfying
  `IsThomClassOfRank F E n` when `dim F = n`.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], Thm. 10.4.
-/

@[expose] public noncomputable section

open Set Bundle Finsupp

universe u

namespace MMP

namespace SingularCochain

open SingularChain

variable {R : Type u} [CommRing R] {Y Z : TopCat.{u}} (g : Y ⟶ Z) {A : Set Y} {B : Set Z}

/-- Evaluating the pull-back `g^* u` on the relative cycle `single σ 1` is evaluating `u` on
`single (g ∘ σ) 1`. -/
lemma relEval_single_map (hA : A ⊆ g ⁻¹' B) {n : ℕ} (σ : Simplex Y n)
    (hσ : ∀ φ ∈ relCoboundaries R A n, eval φ (single σ 1) = 0)
    (hσ' : ∀ φ ∈ relCoboundaries R B n, eval φ (single (g.hom.comp σ) 1) = 0)
    (u : relativeSingularCohomology R (ModuleCat.of R R) Z B n) :
    relEval (single σ 1) hσ (relativeSingularCohomologyEquiv R A n
        ((relativeSingularCohomology.map R _ g hA n).hom u)) =
      relEval (single (g.hom.comp σ) 1) hσ' (relativeSingularCohomologyEquiv R B n u) := by
  rw [relativeSingularCohomologyEquiv_map]
  have hc' : ∀ φ ∈ relCoboundaries R B n,
      eval φ (Finsupp.mapDomain g.hom.comp (single σ (1 : R))) = 0 := by
    rw [Finsupp.mapDomain_single]
    exact hσ'
  exact (relEval_relCohomologyMap g hA _ _ hc' _).trans
    (LinearMap.congr_fun (relEval_congr Finsupp.mapDomain_single hc' hσ') _)

end SingularCochain

namespace ThomClass

open SingularChain SingularCochain

variable {R : Type u} [CommRing R] {B : Type u} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

/-- The Thom-class condition `⟨u, μ_{E_x}⟩ = 1` (`MMP.IsThomClass`), with the
fibres framed by `ℂⁿ` for an explicit `n`: at `n = dim F` it is definitionally
`MMP.IsThomClass` (`isThomClassOfRank_finrank_iff`); for any `n` with `dim F = n` it is
that condition transported along `H^{2 dim F} = H^{2n}` (`isThomClassOfRank_cast_iff`). -/
def IsThomClassOfRank (n : ℕ) (u : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (TotalSpace F E)) (range (zeroSection F E)) (2 * n : ℕ)) : Prop :=
  ∀ (x : B) (ψ : (Fin n → ℂ) ≃L[ℂ] E x) (v : Fin (2 * n + 1) → (Fin n → ℂ))
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis n) v),
    relEval (R := R) (single (fibreSimplex F x ψ v) 1)
      (eval_single_eq_zero_of_mem_relCoboundaries _
        (fibreSimplex_notMem_range_zeroSection F x ψ hv))
      (relativeSingularCohomologyEquiv R (Y := TopCat.of (TotalSpace F E)) _ _ u) = 1

omit [FiniteDimensional ℂ F] [_root_.VectorBundle ℂ F E] in
variable {F E} in
/-- At `n = dim F`, `IsThomClassOfRank` is the Thom-class condition `MMP.IsThomClass`. -/
lemma isThomClassOfRank_finrank_iff {u : cohomologyWithSupports R (ModuleCat.of R R)
    (TopCat.of (TotalSpace F E)) (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)} :
    IsThomClassOfRank F E (Module.finrank ℂ F) u ↔ IsThomClass F E u :=
  Iff.rfl

omit [TopologicalSpace B] [FiniteDimensional ℂ F] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [_root_.VectorBundle ℂ F E] in
variable (R) in
/-- `H^{2 dim F}(E, E - 0_E) = H^{2n}(E, E - 0_E)` when `dim F = n`. -/
lemma cohomology_rank_eq {n : ℕ} (hn : Module.finrank ℂ F = n) :
    (cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ) : Type u) =
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * n : ℕ) := by
  subst hn
  rfl

omit [FiniteDimensional ℂ F] [_root_.VectorBundle ℂ F E] in
variable {F E} in
/-- When `dim F = n`, a class `u` in degree `2 dim F` is a Thom class if and only if its transport
to degree `2n` along `cohomology_rank_eq` satisfies `IsThomClassOfRank F E n`. -/
lemma isThomClassOfRank_cast_iff {n : ℕ} (hn : Module.finrank ℂ F = n)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * Module.finrank ℂ F : ℕ)) :
    IsThomClassOfRank F E n (cast (cohomology_rank_eq R F E hn) u) ↔ IsThomClass F E u := by
  subst hn
  rfl

/-- **Thom's theorem** (Milnor–Stasheff, Thm. 10.4), with the fibres framed by `ℂⁿ`: when
`dim F = n`, there is exactly one class in `H^{2n}(E, E - 0_E)` satisfying
`IsThomClassOfRank F E n`. -/
theorem existsUnique_isThomClassOfRank {n : ℕ} (hn : Module.finrank ℂ F = n) :
    ∃! u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F E))
      (range (zeroSection F E)) (2 * n : ℕ), IsThomClassOfRank F E n u := by
  subst hn
  exact existsUnique_isThomClass F E

end ThomClass

end MMP
