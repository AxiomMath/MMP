module

public import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Euclidean
public import MMP.AlgebraicTopology.SingularCohomology.Contractible
public import MMP.AlgebraicTopology.PoincareDuality.Vanishing
public import MMP.AlgebraicTopology.PoincareDuality.TopDegree

/-!
# Poincaré duality for `ℝⁿ`

The convex case of Bredon's induction for Poincaré duality on open sets
(`PoincareDuality/AlexanderInduction.lean`). In the cocycle/cycle model of the cap
product (`capHomQ`), the property to be propagated over open sets is
`PoincareAlexander.DualityAt R Z n z`: for a locally finite `n`-cycle `z` of `Z`, the map
`[φ] ↦ [φ ∩ z]`, `H^p Z → H_q Z`, is bijective for `p + q = n`, and `H^p Z = 0`, `H_q Z = 0` for
`p, q > n`.

For `Z = ℝⁿ`: `H^p ℝⁿ = 0` for `p > 0` (`mk_eq_zero_of_homotopy_const`, the straight-line
contraction), `H_q ℝⁿ = 0` for `q ≠ n` (`borelMooreHomology.isZero_euclidean_of_lt`,
`borelMooreHomology.isZero_of_dim_lt`), and in bidegree `(0, n)` the duality reduces to
`r ↦ r [z]` being a bijection `R ≃ H_n ℝⁿ` (`bijective_capHomQ_zero_of_homotopy_const`), which
holds for every fundamental class by top-degree Poincaré duality.
## Main definitions

* `MMP.PoincareAlexander.DualityAt`: the property `Pᵤ` of the induction.
* `MMP.PoincareAlexander.euclideanContraction`: the straight-line contraction of `ℝⁿ`.

## Main results

* `MMP.PoincareAlexander.dualityAt_euclidean`: `DualityAt` for `ℝⁿ` and any cycle
  `z` with `r ↦ r [z]` bijective.
* `MMP.PoincareAlexander.dualityAt_euclidean_of_isFundamentalClass`: `DualityAt` for `ℝⁿ` at any
  cycle representing a fundamental class.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Function

universe u

namespace MMP

namespace PoincareAlexander

open SingularChain SingularCochain BorelMooreCross BorelMooreCap

/-- **The property `Pᵤ` of Bredon's induction for Poincaré duality**, at a locally finite
`n`-cycle `z` of `Z`: the cap product `[φ] ↦ [φ ∩ z]`, `H^p Z → H_q Z`, is bijective for
`p + q = n`, and `H^p Z = 0`, `H_q Z = 0` for `p, q > n`. -/
def DualityAt {R : Type u} [CommRing R] (Z : TopCat.{u}) (n : ℕ) (z : Cyc (R := R) Z n) : Prop :=
  (∀ p q (h : p + q = n),
    Bijective fun c ↦ capHomQ R (∅ : Set Z) p q n h c (Submodule.Quotient.mk z)) ∧
  (∀ p, n < p → Subsingleton (relCohomology R (∅ : Set Z) p)) ∧
  (∀ q, n < q → Subsingleton (HomQ (R := R) Z q))

variable {R : Type} [CommRing R]

/-- The straight-line contraction of `ℝⁿ` to `0`. -/
def euclideanContraction (n : ℕ) :
    TopCat.Homotopy (𝟙 (TopCat.of (Fin n → ℝ)))
      (TopCat.ofHom (ContinuousMap.const (TopCat.of (Fin n → ℝ)) 0)) where
  toFun p := (1 - (p.1 : ℝ)) • (p.2 : Fin n → ℝ)
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- `H^p ℝⁿ = 0` for `0 < p`. -/
lemma subsingleton_relCohomology_euclidean (n : ℕ) {p : ℕ} (hp : 0 < p) :
    Subsingleton (relCohomology R (∅ : Set (TopCat.of (Fin n → ℝ))) p) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [mk_eq_zero_of_homotopy_const (0 : TopCat.of (Fin n → ℝ)) (euclideanContraction n) hp φ,
    mk_eq_zero_of_homotopy_const (0 : TopCat.of (Fin n → ℝ)) (euclideanContraction n) hp ψ]

/-- `H_q ℝⁿ = 0` for `q ≠ n`, in the explicit model `HomQ`. -/
lemma subsingleton_homQ_euclidean {n q : ℕ} (hq : q ≠ n) :
    Subsingleton (HomQ (R := R) (TopCat.of (Fin n → ℝ)) q) := by
  have hz : IsZero (borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) q) := by
    rcases lt_or_gt_of_ne hq with h | h
    · exact borelMooreHomology.isZero_euclidean_of_lt R h
    · let : ChartedSpace (Fin n → ℝ) (Fin n → ℝ) := chartedSpaceSelf _
      exact borelMooreHomology.isZero_of_dim_lt R (Pi.basisFun ℝ (Fin n)) (by exact_mod_cast h)
  have := ModuleCat.subsingleton_of_isZero hz
  exact (homologyEquiv R (TopCat.of (Fin n → ℝ)) q).symm.injective.subsingleton

/-- **Poincaré duality for `ℝⁿ`** in the cocycle/cycle model: for a locally finite `n`-cycle `z`
of `ℝⁿ` such that `r ↦ r [z]` is a bijection `R ≃ H_n ℝⁿ` (e.g. a fundamental class), the
property `DualityAt` holds. -/
theorem dualityAt_euclidean {n : ℕ} (z : Cyc (R := R) (TopCat.of (Fin n → ℝ)) n)
    (hz : Bijective fun r : R ↦
      r • (Submodule.Quotient.mk z : HomQ (R := R) (TopCat.of (Fin n → ℝ)) n)) :
    DualityAt (TopCat.of (Fin n → ℝ)) n z := by
  refine ⟨fun p q h ↦ ?_, fun p hp ↦ subsingleton_relCohomology_euclidean n (by omega),
    fun q hq ↦ subsingleton_homQ_euclidean (by omega)⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain rfl : n = q := by omega
    exact bijective_capHomQ_zero_of_homotopy_const (0 : TopCat.of (Fin n → ℝ))
      (euclideanContraction n) n h z hz
  · have := subsingleton_relCohomology_euclidean (R := R) n hp
    have := subsingleton_homQ_euclidean (R := R) (n := n) (q := q) (by omega)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Poincaré duality for `ℝⁿ` at a fundamental class**: if the cycle `z` represents a
fundamental class `μ` of `ℝⁿ` (oriented by the standard basis, in its self-chart), then
`DualityAt` holds at `z`. -/
theorem dualityAt_euclidean_of_isFundamentalClass {n : ℕ}
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (Fin n → ℝ)) n}
    (hμ : letI : ChartedSpace (Fin n → ℝ) (Fin n → ℝ) := chartedSpaceSelf _
      IsFundamentalClass R (Pi.basisFun ℝ (Fin n)) μ)
    (z : Cyc (R := R) (TopCat.of (Fin n → ℝ)) n)
    (hzμ : homologyEquiv R (TopCat.of (Fin n → ℝ)) n μ = Submodule.Quotient.mk z) :
    DualityAt (TopCat.of (Fin n → ℝ)) n z := by
  let : ChartedSpace (Fin n → ℝ) (Fin n → ℝ) := chartedSpaceSelf _
  have hb := PoincareDuality.topHomologyFreeOnFundamentalClass_of_manifold (R := R)
    (Y := Fin n → ℝ) (Pi.basisFun ℝ (Fin n)) μ hμ
  refine dualityAt_euclidean z ?_
  have : (fun r : R ↦ r • (Submodule.Quotient.mk z : HomQ (R := R) (TopCat.of (Fin n → ℝ)) n)) =
      homologyEquiv R (TopCat.of (Fin n → ℝ)) n ∘ fun r : R ↦ r • μ := by
    funext r
    simp only [Function.comp_apply, map_smul, hzμ]
    rfl
  rw [this]
  exact (homologyEquiv R (TopCat.of (Fin n → ℝ)) n).bijective.comp hb

end PoincareAlexander

end MMP
