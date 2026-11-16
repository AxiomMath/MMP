module

public import MMP.AlgebraicTopology.PoincareDuality.Alexander
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVarietyUnique
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicGeometry.Dimension.SmoothOfRelativeDimension
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularOpensSmooth

/-!
# Poincaré duality for a non-singular complex variety (Fulton, §19.1 and Corollary 19.2(b))

For a non-singular `n`-dimensional complex variety `X` with fundamental class `μ_X`, the map
`c ↦ c ∩ μ_X`, `H^j X → H_{2n-j} X`, is bijective for every `j`; this is Poincaré duality for the
complex manifold `X(ℂ) = X_reg(ℂ)`.

## Main results

* `MMP.borelMooreHomology.bijective_capProduct_univ_of_isVarietyFundamentalClass`: Poincaré
  duality `c ↦ c ∩ μ_X`, `H^j X → H_{2n-j} X`.
* `MMP.dualityCapMap`, `MMP.bijective_dualityCapMap`, `MMP.dualityEquiv`: the duality
  isomorphism `H^{2p} X ≃ H_{2n-2p} X`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and Corollary 19.2(b).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X]

namespace borelMooreHomology

open MMP.borelMooreHomology

variable (R : Type) [CommRing R]

/-- Pulling cohomology back along the inclusion of an open subset that is the whole space is
bijective. -/
theorem bijective_pullback_inclHom_of_eq_top {Y : TopCat.{0}} {O : Opens Y} (hO : O = ⊤)
    (j : ℤ) :
    Function.Bijective
      (cohomologyWithSupports.pullback R (ModuleCat.of R R) (inclHom O) univ j).hom := by
  subst hO
  let g : Y ⟶ TopCat.of (⊤ : Opens Y) := TopCat.ofHom ⟨fun y ↦ ⟨y, trivial⟩, by fun_prop⟩
  have e1 := cohomologyWithSupports.pullback_comp R (ModuleCat.of R R) g (inclHom ⊤) univ j
  have e2 := cohomologyWithSupports.pullback_comp R (ModuleCat.of R R) (inclHom ⊤) g univ j
  rw [show g ≫ inclHom ⊤ = 𝟙 Y from rfl, cohomologyWithSupports.pullback_id] at e1
  rw [show inclHom ⊤ ≫ g = 𝟙 _ from rfl, cohomologyWithSupports.pullback_id] at e2
  exact ⟨Function.LeftInverse.injective fun a ↦ (congrArg (fun F ↦ F.hom a) e1).symm,
    Function.RightInverse.surjective fun b ↦ (congrArg (fun F ↦ F.hom b) e2).symm⟩

/-- Restriction of Borel–Moore homology to an open subset that is the whole space is
injective. -/
theorem injective_restrict_of_eq_top {Y : TopCat.{0}} [T2Space Y] {O : Opens Y} (hO : O = ⊤)
    (i : ℤ) : Function.Injective (restrict R (ModuleCat.of R R) O i).hom := by
  have hp : IsProperMap (inclHom O) := by
    subst hO
    exact isProperMap_inclHom_top
  exact Function.LeftInverse.injective
    (g := (pushforward R (ModuleCat.of R R) (inclHom O) hp i).hom)
    (pushforward_inclHom_restrict_of_eq_top R hO hp i)

variable {R}

/-- **Poincaré duality for a non-singular complex variety** (Fulton, §19.1, (3) and
Corollary 19.2(b)). For a non-singular `n`-dimensional complex variety `X` with fundamental class
`μ_X`, `c ↦ c ∩ μ_X`, `H^j X → H_{2n-j} X`, is bijective for every `j`. -/
theorem bijective_capProduct_univ_of_isVarietyFundamentalClass {n : ℕ}
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)}
    (hμ : IsVarietyFundamentalClass R (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
      μ) (j : ℤ) :
    Function.Bijective fun c ↦
      capProduct R (TopCat.of (UnderlyingSpace ℂ X)) univ j (2 * n : ℕ) c μ := by
  letI := regularChartedSpace (𝕜 := ℂ)
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
  have hU := regularOpens_eq_top_of_smoothOfRelativeDimension (X := X) n
  have hD := bijective_capProduct_univ_of_isFundamentalClass
    (euclideanComplexOrientationBasis n) _ hμ j
  have hres := injective_restrict_of_eq_top R (Y := TopCat.of (UnderlyingSpace ℂ X)) hU
    ((2 * n : ℕ) - j)
  have hpull := bijective_pullback_inclHom_of_eq_top R
    (Y := TopCat.of (UnderlyingSpace ℂ X)) hU j
  have key := fun c ↦ restrict_capProduct_univ R
    (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) j (2 * n : ℕ) c μ
  refine ⟨fun c c' h ↦ ?_, fun a ↦ ?_⟩
  · apply hpull.1
    apply hD.1
    simp only at h ⊢
    rw [← key, ← key, h]
  · have hF : Function.Surjective fun c ↦ (restrict R (ModuleCat.of R R)
        (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) ((2 * n : ℕ) - j)).hom
          (capProduct R (TopCat.of (UnderlyingSpace ℂ X)) univ j (2 * n : ℕ) c μ) := by
      have h2 := hD.2.comp hpull.2
      convert h2 using 1
      funext c
      exact key c
    obtain ⟨b, hb⟩ : ∃ b, b = (restrict R (ModuleCat.of R R)
        (regularOpens ℂ X : Opens (TopCat.of (UnderlyingSpace ℂ X))) ((2 * n : ℕ) - j)).hom a :=
      ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hF b
    exact ⟨c, hres (hc.trans hb)⟩

end borelMooreHomology

section Duality

variable {R : Type} [CommRing R]

/-- The duality map `c ↦ c ∩ μ`, `H^{2p} X → H_{2n-2p} X`, with the degrees `2p` and
`2n - 2p` identified with the degrees of `borelMooreHomology.capProduct`. -/
def dualityCapMap (n : ℕ)
    (μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ))
    (p : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) Set.univ
        (2 * p : ℕ) →ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
        ((2 * n : ℕ) - (2 * p : ℕ)) :=
  (BorelMooreCross.congrDegree R _ (by omega)).toLinearMap ∘ₗ
    (borelMooreHomology.capProduct R (TopCat.of (UnderlyingSpace ℂ X)) Set.univ
      ((2 * n : ℕ) - ((2 * n : ℕ) - (2 * p : ℕ))) (2 * n : ℕ)).flip μ ∘ₗ
    (cohomologyWithSupports.congrIndex R _ rfl (by omega)).toLinearMap

/-- For a fundamental class `μ_X` of a non-singular `n`-dimensional complex variety, the duality
map `H^{2p} X → H_{2n-2p} X` is bijective. -/
theorem bijective_dualityCapMap {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)}
    (hμ : IsVarietyFundamentalClass R (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
      μ) (p : ℕ) : Function.Bijective (dualityCapMap n μ p) :=
  (LinearEquiv.bijective _).comp
    ((borelMooreHomology.bijective_capProduct_univ_of_isVarietyFundamentalClass hμ _).comp
      (LinearEquiv.bijective _))

/-- The duality isomorphism `H^{2p} X ≃ H_{2n-2p} X`, `c ↦ c ∩ μ_X`, of a non-singular complex
variety with fundamental class `μ_X`. -/
def dualityEquiv {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)}
    (hμ : IsVarietyFundamentalClass R (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
      μ) (p : ℕ) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) Set.univ
        (2 * p : ℕ) ≃ₗ[R]
      borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X))
        ((2 * n : ℕ) - (2 * p : ℕ)) :=
  LinearEquiv.ofBijective (dualityCapMap n μ p) (bijective_dualityCapMap hμ p)

/-- The duality isomorphism `dualityEquiv` sends `c` to `dualityCapMap n μ p c`. -/
@[simp]
lemma dualityEquiv_apply {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) (2 * n : ℕ)}
    (hμ : IsVarietyFundamentalClass R (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := X) n)
      μ) (p : ℕ) (c) : dualityEquiv hμ p c = dualityCapMap n μ p c :=
  rfl

end Duality

end MMP
