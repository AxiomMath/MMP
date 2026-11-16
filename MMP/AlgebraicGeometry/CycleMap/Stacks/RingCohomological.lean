module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.Ring
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PoincareDualityVariety
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.DivisorTransversal

/-!
# The cohomological cycle class map is multiplicative on Stacks' Chow groups

Let `X` be a non-singular complex variety of dimension `n` (`AlgebraicGeometry.IsSmoothVariety`
with `SmoothOfRelativeDimension n`), with fundamental class `μ_X = cl([X]_n)`. Poincaré duality
`c ↦ c ∩ μ_X`, `H^{2p} X ≅ H_{2n-2p} X` (`MMP.dualityEquiv`), turns the cycle class map
`cl_X : A_{n-p} X → H_{2n-2p} X` on Stacks' Chow groups into the cohomological cycle class
`cl : A^p X = A_{n-p} X → H^{2p} X` (`MMP.Chow.chowCohomologicalCycleClass`, zero for `p > n`),
dual to `cl_X`: `cl_X(α) = cl(α) ∩ μ_X`
(`MMP.Chow.chowCycleClass_chowGroupCongrDegree_eq_capProduct`). For the Stacks intersection
product, `cl(x · y) = cl(x) ∪ cl(y)` in `H^{2(p+q)} X`
(`MMP.Chow.chowCohomologicalCycleClass_selfIntersectionProduct`, Fulton, Corollary 19.2(b)), from
`cl_X(x · y) = d ∩ cl_X(x)` (`MMP.Chow.chowCycleClass_selfIntersectionProduct_eq_capProduct`) and
`d ∩ (c ∩ μ_X) = (c ∪ d) ∩ μ_X`.

## Main definitions

* `MMP.Chow.chowCohomologicalCycleClass`: `cl : A^p X → H^{2p} X`.

## Main results

* `MMP.Chow.isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass`: `cl([X]_n)` is the
  fundamental class of `X`.
* `MMP.Chow.chowCycleClass_chowGroupCongrDegree_eq_capProduct`: `cl_X(α) = cl(α) ∩ μ_X`.
* `MMP.Chow.chowCohomologicalCycleClass_selfIntersectionProduct`: `cl(x · y) = cl(x) ∪ cl(y)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Corollary 19.2(b).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow MMP.UnderlyingSpace

namespace MMP.Chow

variable (R : Type) [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [IsSmoothVariety ℂ (X ↘ Spec (.of ℂ))] {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]

variable (n) in
/-- **`cl([X]_n)` is the fundamental class of `X`**: the cycle class of the fundamental class of a
non-singular complex variety of dimension `n` restricts to the fundamental class of the complex
manifold `X(ℂ)`. -/
theorem isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass :
    IsVarietyFundamentalClass R (natCast_eq_dimension_of_isVariety (K := ℂ) X n)
      (chowCycleClass R n (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n)) := by
  obtain ⟨μ, hμ, -, -⟩ := existsUnique_isVarietyFundamentalClass R
    (natCast_eq_dimension_of_isVariety (K := ℂ) X n)
  rw [chowCycleClass_fundamentalChowClass,
    cycleClass_fundamentalCycle_of_isVarietyFundamentalClass R _ hμ]
  exact hμ

variable (X n) in
/-- **The cohomological cycle class** `cl : A^p X = A_{n-p} X → H^{2p} X` of a non-singular
complex variety of dimension `n` (Fulton, Corollary 19.2(b)), on Stacks' Chow groups: the class
dual to `cl_X(α)` under Poincaré duality `c ↦ c ∩ μ_X`, `μ_X = cl([X]_n)`. For `p > n` it is
zero (`A_{n-p} X = 0`). -/
def chowCohomologicalCycleClass (p : ℕ) :
    chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((n : ℤ) - p) →+
      cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) Set.univ
        (2 * p : ℕ) :=
  if hp : p ≤ n then
    (dualityEquiv (isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass R (X := X) n)
      p).symm |>.toLinearMap.toAddMonoidHom.comp
        ((BorelMooreCross.congrDegree R _ (by omega : ((2 * (n - p) : ℕ) : ℤ) =
            (2 * n : ℕ) - (2 * p : ℕ))).toLinearMap.toAddMonoidHom.comp
          ((chowCycleClass R (n - p)).comp
            (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (by omega : (n : ℤ) - p = ((n - p : ℕ) : ℤ))).toAddMonoidHom))
  else 0

/-- For `n < p` the cohomological cycle class is zero. -/
theorem chowCohomologicalCycleClass_eq_zero_of_lt {p : ℕ} (hp : n < p) :
    chowCohomologicalCycleClass R X n p = 0 := by
  rw [chowCohomologicalCycleClass, dif_neg (by omega)]

/-- For `p ≤ n` the cohomological cycle class is the Poincaré dual of the cycle class `cl_X` on
`A_{n-p} X`. -/
theorem chowCohomologicalCycleClass_apply_of_le {p : ℕ} (hp : p ≤ n)
    (α : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((n : ℤ) - p)) :
    chowCohomologicalCycleClass R X n p α =
      (dualityEquiv (isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass R (X := X) n)
        p).symm (BorelMooreCross.congrDegree R _
          (by omega : ((2 * (n - p) : ℕ) : ℤ) = (2 * n : ℕ) - (2 * p : ℕ))
          (chowCycleClass R (n - p) (chowGroupCongrDegree (fieldChowSituation ℂ)
            (X ↘ Spec (.of ℂ)) (by omega : (n : ℤ) - p = ((n - p : ℕ) : ℤ)) α))) := by
  rw [chowCohomologicalCycleClass, dif_pos hp]
  rfl

/-- **`cl_X(α) = cl(α) ∩ μ_X`** for `α ∈ A^p X = A_k X`, `k + p = n`: the cohomological cycle
class is dual to the cycle class `cl_X` (Fulton, Corollary 19.2(b)). -/
theorem chowCycleClass_chowGroupCongrDegree_eq_capProduct {p k : ℕ} (hk : k + p = n)
    (α : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((n : ℤ) - p)) :
    chowCycleClass R k
        (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (by omega : (n : ℤ) - p = k) α) =
      BorelMooreCross.congrDegree R _ (by omega)
        (borelMooreHomology.capProduct R _ Set.univ (2 * p : ℕ) (2 * n : ℕ)
          (chowCohomologicalCycleClass R X n p α)
          (chowCycleClass R n
            (fundamentalChowClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) n))) := by
  have hp : p ≤ n := by omega
  obtain rfl : k = n - p := by omega
  set D :=
    dualityEquiv (isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass R (X := X) n) p
  set z := BorelMooreCross.congrDegree R _ (by omega : ((2 * (n - p) : ℕ) : ℤ) =
    (2 * n : ℕ) - (2 * p : ℕ))
      (chowCycleClass R (n - p) (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        (by omega : (n : ℤ) - p = ((n - p : ℕ) : ℤ)) α)) with hz
  have hc : dualityCapMap n _ p (D.symm z) = z := D.apply_symm_apply z
  have hcl : chowCohomologicalCycleClass R X n p α = D.symm z :=
    chowCohomologicalCycleClass_apply_of_le R hp α
  rw [hcl]
  rw [dualityCapMap] at hc
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.flip_apply] at hc
  rw [borelMooreHomology.capProduct_congrIndex, borelMooreHomology.congrDegree_congrDegree,
    hz] at hc
  have h2 := congrArg (BorelMooreCross.congrDegree R (TopCat.of (UnderlyingSpace ℂ X))
    (by omega : ((2 * n : ℕ) : ℤ) - (2 * p : ℕ) = ((2 * (n - p) : ℕ) : ℤ))) hc
  rw [borelMooreHomology.congrDegree_congrDegree, borelMooreHomology.congrDegree_congrDegree,
    BorelMooreCross.congrDegree_self, LinearEquiv.refl_apply] at h2
  exact h2.symm

/-- Two transports along equalities of degrees compose. -/
@[simp]
theorem chowGroupCongrDegree_chowGroupCongrDegree {C : ChowSituation.{0}} {Z : Scheme.{0}}
    (s : Z ⟶ C.S) [LocallyOfFiniteType s] {i j k : ℤ} (h₁ : i = j) (h₂ : j = k)
    (a : chowGroup C s i) :
    chowGroupCongrDegree C s h₂ (chowGroupCongrDegree C s h₁ a) =
      chowGroupCongrDegree C s (h₁.trans h₂) a := by
  subst h₁ h₂
  rfl

/-- The Stacks intersection product commutes with transport of the degrees of its arguments. -/
theorem selfIntersectionProduct_chowGroupCongrDegree {a₀ b₀ a b c : ℤ} (h₁ : a₀ = a)
    (h₂ : b₀ = b) (h₃ : a + b - n = c)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) a₀)
    (y : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) b₀) :
    chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) h₃
        (selfIntersectionProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
          (X ↘ Spec (.of ℂ)) n
          (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
            (pullback.diagonal (X ↘ Spec (.of ℂ)))
            (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
            (isRegularClosedImmersionOfCodim_diagonal X n)) a b
          (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) h₁ x)
          (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) h₂ y)) =
      chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (by omega)
        (selfIntersectionProduct (fieldChowSituation ℂ)
          (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
          (X ↘ Spec (.of ℂ)) n
          (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
            (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
            (pullback.diagonal (X ↘ Spec (.of ℂ)))
            (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
            (isRegularClosedImmersionOfCodim_diagonal X n)) a₀ b₀ x y) := by
  subst h₁ h₂
  rfl

/-- **The cohomological cycle class is multiplicative** (Fulton, Corollary 19.2(b)): for a
non-singular complex variety `X` of dimension `n`, `x ∈ A^p X` and `y ∈ A^q X`,
`cl(x · y) = cl(x) ∪ cl(y)` in `H^{2(p+q)} X`, for the Stacks intersection product
`x · y = δ^!(x × y)` (`Stacks.Chow.selfIntersectionProduct`) formed with the class `c(δ, 𝒩)` of the
normal sheaf of the diagonal. -/
theorem chowCohomologicalCycleClass_selfIntersectionProduct (p q : ℕ)
    (x : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((n : ℤ) - p))
    (y : chowGroup (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((n : ℤ) - q)) :
    chowCohomologicalCycleClass R X n (p + q)
        (chowGroupCongrDegree (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          (by push_cast; ring : (n : ℤ) - p + ((n : ℤ) - q) - n = (n : ℤ) - ((p + q : ℕ) : ℤ))
          (selfIntersectionProduct (fieldChowSituation ℂ)
            (fun s _ ↦ fieldChowSituation_dimensionFunction ℂ s) (gysinSystemOfInvertible _)
            (X ↘ Spec (.of ℂ)) n
            (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
              (selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
              (pullback.diagonal (X ↘ Spec (.of ℂ)))
              (diagonal_comp_selfProductStructure (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)))
              (isRegularClosedImmersionOfCodim_diagonal X n)) ((n : ℤ) - p) ((n : ℤ) - q) x y)) =
      cupUniv R _ p q (chowCohomologicalCycleClass R X n p x)
        (chowCohomologicalCycleClass R X n q y) := by
  have hμ := isVarietyFundamentalClass_chowCycleClass_fundamentalChowClass R (X := X) n
  rcases le_or_gt (p + q) n with hpq | hpq
  · apply (borelMooreHomology.bijective_capProduct_univ_of_isVarietyFundamentalClass hμ
      ((2 * (p + q) : ℕ) : ℤ)).1
    apply (BorelMooreCross.congrDegree R _ (by omega : ((2 * n : ℕ) : ℤ) - ((2 * (p + q) : ℕ) : ℤ) =
      ((2 * (n - (p + q)) : ℕ) : ℤ))).injective
    change BorelMooreCross.congrDegree R _ _ (borelMooreHomology.capProduct R _ Set.univ
        ((2 * (p + q) : ℕ) : ℤ) (2 * n : ℕ) _ _) =
      BorelMooreCross.congrDegree R _ _ (borelMooreHomology.capProduct R _ Set.univ
        ((2 * (p + q) : ℕ) : ℤ) (2 * n : ℕ) _ _)
    rw [← chowCycleClass_chowGroupCongrDegree_eq_capProduct R (k := n - (p + q)) (by omega),
      chowGroupCongrDegree_chowGroupCongrDegree,
      ← selfIntersectionProduct_chowGroupCongrDegree
        (by omega : (n : ℤ) - p = ((n - p : ℕ) : ℤ)) (by omega : (n : ℤ) - q = ((n - q : ℕ) : ℤ))
        (by omega : ((n - p : ℕ) : ℤ) + ((n - q : ℕ) : ℤ) - n = ((n - (p + q) : ℕ) : ℤ)),
      chowCycleClass_selfIntersectionProduct_eq_capProduct R (k := n - p) (l := n - q) (q := q)
        (m := n - (p + q)) (by omega) (by omega) _ _ (chowCohomologicalCycleClass R X n q y)
        (chowCycleClass_chowGroupCongrDegree_eq_capProduct R (by omega) y),
      chowCycleClass_chowGroupCongrDegree_eq_capProduct R (k := n - p) (by omega) x,
      borelMooreHomology.capProduct_congrDegree,
      borelMooreHomology.capProduct_capProduct_eq_capProduct_cupUniv,
      borelMooreHomology.congrDegree_congrDegree, borelMooreHomology.congrDegree_congrDegree]
  · haveI : Subsingleton (borelMooreHomology R (ModuleCat.of R R)
        (TopCat.of (UnderlyingSpace ℂ X)) ((2 * n : ℕ) - (2 * (p + q) : ℕ))) :=
      ModuleCat.isZero_iff_subsingleton.1
        (isZero_borelMooreHomology_of_neg R _ _ (by omega))
    haveI := (bijective_dualityCapMap hμ (p + q)).1.subsingleton
    exact Subsingleton.elim _ _

end MMP.Chow
