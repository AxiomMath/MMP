module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import MMP.AlgebraicTopology.LocalizedFirstChern.ProductCap
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Orientation
public import MMP.AlgebraicTopology.BorelMoore.Suspension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety

/-!
# The cap product with a local orientation class in a holomorphic ball chart (Fulton, §19.1)

Let `P` be a complex manifold of dimension `k + 1` and `Φ : P ≅ B_ε × B` a homeomorphism onto the
product of the disc `B_ε = ball(0, ε) ⊆ ℂ` and a connected complex manifold `B` of dimension `k`,
holomorphic in charts with injective derivative. Put `g = pr₁ ∘ Φ : P → ℂ` and `Y = g⁻¹(0)`, so
that `y ↦ (Φ y).2` is a homeomorphism `Y ≅ B`. For the local orientation class
`u₀ ∈ H²(ℂ, ℂ - 0)` of `ℂ` at `0` (orientation `1, i`), the cap product `g^* u₀ ∩ μ_P ∈ H_{2k} Y`
is carried to the fundamental class `μ_B`.

The proof composes `Φ` with the radial diffeomorphism `ρ : B_ε ≅ ℂ`,
`w ↦ (√(1 - ‖w/ε‖²))⁻¹ • (w/ε)`, to the product chart `Θ = (id × ρ) ∘ swap ∘ Φ : P ≅ B × ℂ`.
The derivative of `Θ` in charts is the product of the derivative of `ρ`, whose determinant is
positive, with a complex linear isomorphism; so `Θ` preserves the complex orientations and the
computation in a product chart
(`IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complex`) applies
to `g_Θ = pr₂ ∘ Θ = ρ ∘ g`. Finally `g = σ ∘ g_Θ` with `σ = ρ⁻¹ : ℂ → B_ε ⊆ ℂ`, and `σ^* u₀` is
again the local orientation class at `0`, since `σ` is differentiable at `0` with derivative
`ε • id`.

## Main definitions

* `MMP.ballZeroHomeomorph`: the radial homeomorphism `ball(0, ε) ≅ E`.
* `MMP.ballZeroFibreHomeomorph`: the homeomorphism `g⁻¹(0) ≅ B`.
* `MMP.ballChartProdHomeomorph`: the product chart `Θ : P ≅ B × ℂ`.

## Main results

* `MMP.det_fderiv_univUnitBall_pos`: `univUnitBall` has positive Jacobian.
* `MMP.IsLocalOrientationClass.map_of_hasFDerivAt`: local orientation classes pull
  back along maps differentiable at `0` with orientation-preserving derivative.
* `MMP.isOrientationPreserving_ballChartProdHomeomorph`.
* `MMP.hasProperNeighbourhoodDeformations_ballChart`.
* `MMP.IsFundamentalClass.pushforward_ballZeroFibreHomeomorph_capProductSupportPullback`:
  `g^* u₀ ∩ μ_P` is carried to `μ_B`.

## Implementation notes

The positivity of the Jacobian of `univUnitBall` is obtained from connectedness: the Jacobian is
continuous, nowhere zero (the map has a differentiable inverse on the unit ball) and equal to `1`
at the origin.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open Set CategoryTheory Topology Metric Filter

namespace MMP

open FundamentalClass borelMooreHomology BorelMooreCross ThomClass SingularChain SingularCochain
  Finsupp OpenPartialHomeomorph

/-! ### The radial homeomorphism `ball 0 ε ≅ E` -/

section BallHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ε : ℝ}

/-- For `0 < ε`, the point `ε • univUnitBall z` lies in the ball of radius `ε` about `0`. -/
lemma smul_univUnitBall_mem_ball (hε : 0 < ε) (z : E) : ε • univUnitBall z ∈ ball (0 : E) ε := by
  have h : univUnitBall z ∈ ball (0 : E) 1 := univUnitBall.map_source (mem_univ z)
  rw [mem_ball_zero_iff] at h ⊢
  rw [norm_smul, Real.norm_of_nonneg hε.le]
  nlinarith

/-- For `0 < ε` and `w` in the ball of radius `ε` about `0`, `ε⁻¹ • w` lies in the unit ball. -/
lemma inv_smul_mem_ball_one (hε : 0 < ε) (w : ball (0 : E) ε) :
    ε⁻¹ • (w : E) ∈ ball (0 : E) 1 := by
  have h := w.2
  rw [mem_ball_zero_iff] at h ⊢
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le), inv_mul_lt_one₀ hε]
  exact h

/-- The radial homeomorphism `ball 0 ε ≅ E`, `w ↦ (√(1 - ‖w / ε‖²))⁻¹ • (w / ε)`, with inverse
`z ↦ ε (√(1 + ‖z‖²))⁻¹ • z`. -/
def ballZeroHomeomorph (hε : 0 < ε) : ball (0 : E) ε ≃ₜ E where
  toFun w := univUnitBall.symm (ε⁻¹ • (w : E))
  invFun z := ⟨ε • univUnitBall z, smul_univUnitBall_mem_ball hε z⟩
  left_inv w := Subtype.ext <| by
    change ε • univUnitBall (univUnitBall.symm (ε⁻¹ • (w : E))) = w
    rw [univUnitBall.right_inv (inv_smul_mem_ball_one hε w), smul_inv_smul₀ hε.ne']
  right_inv z := by
    change univUnitBall.symm (ε⁻¹ • ε • univUnitBall z) = z
    rw [inv_smul_smul₀ hε.ne', univUnitBall.left_inv (mem_univ z)]
  continuous_toFun := univUnitBall.continuousOn_symm.comp_continuous
    (continuous_const.smul continuous_subtype_val) fun w ↦ inv_smul_mem_ball_one hε w
  continuous_invFun := (continuous_const.smul
    (continuousOn_univ.1 univUnitBall.continuousOn)).subtype_mk _

/-- `ballZeroHomeomorph hε w = univUnitBall.symm (ε⁻¹ • w)`. -/
@[simp]
lemma ballZeroHomeomorph_apply (hε : 0 < ε) (w : ball (0 : E) ε) :
    ballZeroHomeomorph hε w = univUnitBall.symm (ε⁻¹ • (w : E)) :=
  rfl

/-- The inverse of `ballZeroHomeomorph hε` sends `z` to `ε • univUnitBall z`. -/
@[simp]
lemma coe_ballZeroHomeomorph_symm_apply (hε : 0 < ε) (z : E) :
    ((ballZeroHomeomorph hε).symm z : E) = ε • univUnitBall z :=
  rfl

/-- The inverse of `ballZeroHomeomorph hε` sends `z` to `0` if and only if `z = 0`. -/
lemma coe_ballZeroHomeomorph_symm_eq_zero_iff (hε : 0 < ε) (z : E) :
    ((ballZeroHomeomorph hε).symm z : E) = 0 ↔ z = 0 := by
  rw [coe_ballZeroHomeomorph_symm_apply, smul_eq_zero, univUnitBall_apply, smul_eq_zero,
    inv_eq_zero, Real.sqrt_eq_zero', or_iff_right hε.ne', or_iff_right]
  intro h
  nlinarith [sq_nonneg ‖z‖]

end BallHomeomorph

/-! ### Derivatives of the radial homeomorphism -/

section BallDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ε : ℝ}

/-- The derivative of `univUnitBall` at `0` is the identity. -/
lemma hasFDerivAt_univUnitBall_zero :
    HasFDerivAt (univUnitBall : E → E) (ContinuousLinearMap.id ℝ E) 0 := by
  have hc : DifferentiableAt ℝ (fun x : E ↦ (√(1 + ‖x‖ ^ 2))⁻¹) 0 := by
    have h1 : DifferentiableAt ℝ (fun x : E ↦ 1 + ‖x‖ ^ 2) 0 :=
      (differentiableAt_const _).add (differentiableAt_id.norm_sq ℝ)
    exact (h1.sqrt (by simp)).inv (by simp)
  have h := hc.hasFDerivAt.smul (hasFDerivAt_id (0 : E))
  convert h using 1
  · funext x
    rw [univUnitBall_apply]
    rfl
  · ext v
    simp

/-- The real Jacobians of `univUnitBall.symm` at `univUnitBall x` and of `univUnitBall` at `x`
multiply to `1`. -/
lemma det_fderiv_univUnitBall_symm_mul (x : E) :
    LinearMap.det (fderiv ℝ univUnitBall.symm (univUnitBall x) : E →ₗ[ℝ] E) *
      LinearMap.det (fderiv ℝ univUnitBall x : E →ₗ[ℝ] E) = 1 := by
  have hd : DifferentiableAt ℝ (univUnitBall : E → E) x :=
    (contDiff_univUnitBall (n := 1)).differentiable one_ne_zero x
  have hy : univUnitBall x ∈ ball (0 : E) 1 := univUnitBall.map_source (mem_univ x)
  have hd' : DifferentiableAt ℝ univUnitBall.symm (univUnitBall x) :=
    ((contDiffOn_univUnitBall_symm (n := 1)).differentiableOn one_ne_zero _ hy).differentiableAt
      (isOpen_ball.mem_nhds hy)
  have hcomp : (fderiv ℝ univUnitBall.symm (univUnitBall x)).comp (fderiv ℝ univUnitBall x) =
      ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x hd' hd, ← fderiv_id (𝕜 := ℝ) (x := x)]
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.Eventually.of_forall fun z ↦ univUnitBall.left_inv (mem_univ z))
  rw [← LinearMap.det_comp]
  change LinearMap.det ((fderiv ℝ univUnitBall.symm (univUnitBall x)).comp
    (fderiv ℝ univUnitBall x) : E →ₗ[ℝ] E) = 1
  rw [hcomp]
  exact LinearMap.det_id

/-- The real Jacobian of `univUnitBall` is everywhere positive. -/
lemma det_fderiv_univUnitBall_pos (x : E) :
    0 < LinearMap.det (fderiv ℝ univUnitBall x : E →ₗ[ℝ] E) := by
  have hc : Continuous fun x : E ↦ LinearMap.det (fderiv ℝ univUnitBall x : E →ₗ[ℝ] E) :=
    ContinuousLinearMap.continuous_det.comp
      ((contDiff_univUnitBall (n := 1)).continuous_fderiv one_ne_zero)
  have h0 : LinearMap.det (fderiv ℝ univUnitBall (0 : E) : E →ₗ[ℝ] E) = 1 := by
    rw [hasFDerivAt_univUnitBall_zero.fderiv]
    exact LinearMap.det_id
  by_contra hneg
  push Not at hneg
  obtain ⟨y, hy⟩ := intermediate_value_univ x 0 hc ⟨hneg, by rw [h0]; norm_num⟩
  have hy' : LinearMap.det (fderiv ℝ univUnitBall y : E →ₗ[ℝ] E) = 0 := hy
  have := det_fderiv_univUnitBall_symm_mul y
  rw [hy', mul_zero] at this
  exact zero_ne_one this

/-- The inverse of `univUnitBall` is differentiable on the unit ball with positive Jacobian. -/
lemma differentiableAt_univUnitBall_symm_and_det_pos {y : E} (hy : y ∈ ball (0 : E) 1) :
    DifferentiableAt ℝ univUnitBall.symm y ∧
      0 < LinearMap.det (fderiv ℝ univUnitBall.symm y : E →ₗ[ℝ] E) := by
  refine ⟨((contDiffOn_univUnitBall_symm (n := 1)).differentiableOn one_ne_zero _ hy
    ).differentiableAt (isOpen_ball.mem_nhds hy), ?_⟩
  have hx : univUnitBall (univUnitBall.symm y) = y := univUnitBall.right_inv hy
  have h := det_fderiv_univUnitBall_symm_mul (univUnitBall.symm y)
  rw [hx] at h
  have hp := det_fderiv_univUnitBall_pos (univUnitBall.symm y)
  by_contra hneg
  push Not at hneg
  nlinarith

end BallDeriv

/-! ### Complex orientations of `ℂᵏ × ℂ` -/

section ComplexBasis

/-- The complex orientation basis of `ℂⁿ` is the real basis `e₁, i e₁, …, eₙ, i eₙ` obtained from
the standard complex basis. -/
lemma euclideanComplexOrientationBasis_eq_complexRealBasis (n : ℕ) :
    euclideanComplexOrientationBasis n = complexRealBasis (PiLp.basisFun 2 ℂ (Fin n)) := by
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  simp [complexRealBasis, euclideanComplexOrientationBasis]

/-- The real basis obtained from the complex basis `1` of `ℂ` is `1, i`. -/
lemma complexRealBasis_singleton :
    complexRealBasis (Module.Basis.singleton (Fin 1) ℂ) = Complex.basisOneI := by
  refine Module.Basis.eq_of_apply_eq fun b ↦ ?_
  have hb : b = finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), b)) := by
    fin_cases b <;> rfl
  conv_lhs => rw [hb, complexRealBasis_apply]
  simp

/-- An injective complex linear map `ℂᵏ⁺¹ → ℂᵏ × ℂ` has positive real determinant for the complex
orientation basis of `ℂᵏ⁺¹` and the product of the complex orientation bases of `ℂᵏ` and `ℂ`. -/
theorem det_prod_basisOneI_pos {k : ℕ}
    {N : EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin k) × ℂ}
    (hN : Function.Injective N) :
    0 < (((euclideanComplexOrientationBasis k).prod Complex.basisOneI).reindex
      finSumFinEquiv).det ((N.restrictScalars ℝ) ∘ euclideanComplexOrientationBasis (k + 1)) := by
  have h := complexRealBasis_det_pos (PiLp.basisFun 2 ℂ (Fin (k + 1)))
    (((PiLp.basisFun 2 ℂ (Fin k)).prod (Module.Basis.singleton (Fin 1) ℂ)).reindex
      finSumFinEquiv) hN
  have hb := prod_complexRealBasis (PiLp.basisFun 2 ℂ (Fin k))
    (Module.Basis.singleton (Fin 1) ℂ)
  rw [complexRealBasis_singleton, ← euclideanComplexOrientationBasis_eq_complexRealBasis] at hb
  rw [hb, Module.Basis.det_reindex, euclideanComplexOrientationBasis_eq_complexRealBasis]
  exact h

end ComplexBasis

/-! ### Local orientation classes under maps differentiable at `0` -/

section LocalOrientation

variable {R : Type} [CommRing R] {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Local orientation classes pull back along maps with orientation-preserving derivative.**
Let `f : E → H` be continuous with `f 0 = 0` and `f⁻¹(0) = 0`, differentiable at `0` with a
derivative of positive determinant for the bases `b_E`, `b_H`. Then `f^*` carries the local
orientation class of `H` at `0` to that of `E`. -/
theorem IsLocalOrientationClass.map_of_hasFDerivAt {n : ℕ} {bE : Module.Basis (Fin n) ℝ E}
    {bH : Module.Basis (Fin n) ℝ H} {f : E → H} (hfc : Continuous f) (hf0 : f 0 = 0)
    (hs : ({0}ᶜ : Set (TopCat.of E)) ⊆
      (TopCat.ofHom ⟨f, hfc⟩ : TopCat.of E ⟶ TopCat.of H) ⁻¹' ({0}ᶜ : Set (TopCat.of H)))
    {L : E →L[ℝ] H} (hL : HasFDerivAt f L 0) (hdet : 0 < bH.det ((L : E → H) ∘ bE))
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of H) {0} n}
    (hu : IsLocalOrientationClass R bH (0 : TopCat.of H) u) :
    IsLocalOrientationClass R bE (0 : TopCat.of E)
      ((relativeSingularCohomology.map R (ModuleCat.of R R) (TopCat.ofHom ⟨f, hfc⟩) hs n).hom
        u) := by
  obtain ⟨α, hα, hc, hrep⟩ := hu
  set fh : TopCat.of E ⟶ TopCat.of H := TopCat.ofHom ⟨f, hfc⟩
  have hα' := cochainPullback_mem_relCocycles fh hs hα
  refine ⟨cochainPullback R fh n α, hα', ?_, ?_⟩
  swap
  · rw [relativeSingularCohomologyEquiv_map, hrep, relCohomologyMap_mk]
  obtain ⟨δ, hδ, hloc⟩ := isLocallyHomologous_of_hasFDerivAt (X := TopCat.of H) bE bH
    isOpen_univ (g := id) continuousOn_id (injOn_id _) Filter.univ_mem hfc.continuousOn hf0
    (mem_univ _) hL hdet
  obtain ⟨w, hw, hwδ⟩ := exists_isOrientedSimplexAroundZero_subset bE (0 : E)
    (ball_mem_nhds 0 hδ)
  obtain ⟨-, hrel⟩ := hloc w hw hwδ
  have hvt : range (affineSimplex w) ⊆ (chartAt E (0 : TopCat.of E)).target := by
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact subset_univ _
  set w' : Fin (n + 1) → H := fun k ↦ 0 + L (w k - 0)
  have hvt' : range (affineSimplex w') ⊆ (chartAt H (0 : TopCat.of H)).target := by
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_target]
    exact subset_univ _
  have hw' : IsOrientedSimplexAroundZero bH fun k ↦ w' k - (chartAt H (0 : TopCat.of H)) 0 := by
    have := hw.map_linearMap (L : E →ₗ[ℝ] H) hdet
    convert this using 1
    funext k
    simp [w', chartAt_self_eq]
  refine isChartOrientedCocycle_of_eval (isOrientedAtlas_self E) bE hα'
    (chart_mem_atlas E (0 : TopCat.of E)) (mem_chart_source _ _) (v := w)
    (by simpa [chartAt_self_eq] using hw) hvt ?_
  have h1 := hrel (fh.hom.comp (chartSimplexOf (chartAt E (0 : TopCat.of E)) w hvt))
    (chartSimplexOf (chartAt H (0 : TopCat.of H)) w' hvt') (fun t ↦ rfl) (fun t ↦ rfl)
  have h2 := hc.2 (chartAt H (0 : TopCat.of H)) (chart_mem_atlas _ _) (mem_chart_source _ _) w'
    hw' hvt'
  refine Eq.trans ?_ ((eval_eq_of_isLocallyHomologous hα h1).trans h2)
  simp only [SingularCochain.eval, linearCombination_single, one_smul]
  rfl

end LocalOrientation

/-! ### Changing the support of the cap product along an equality of sets -/

section CongrSet

variable (R : Type) [CommRing R]

/-- The cap product `f^* c ∩ a` does not depend on how the support `Z` is written: for `Z = Z'`,
push-forwards of `f^* c ∩ a ∈ H(f⁻¹ Z)` and of `f^* c ∩ a ∈ H(f⁻¹ Z')` along maps agreeing on
`f⁻¹ Z = f⁻¹ Z'` coincide. -/
lemma pushforward_capProductSupportPullback_congr_set {Y' Y W : TopCat.{0}} (f : Y' ⟶ Y)
    {Z Z' : Set Y} (h : Z = Z') (hZ : IsClosed Z) (hZ' : IsClosed Z')
    (hd : HasProperNeighbourhoodDeformations (f ⁻¹' Z))
    (hd' : HasProperNeighbourhoodDeformations (f ⁻¹' Z')) (j k : ℤ) {m : ℤ} (hm : k - j = m)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y Z j)
    (a : borelMooreHomology R (ModuleCat.of R R) Y' k)
    (φ : TopCat.of (f ⁻¹' Z) ⟶ W) (φ' : TopCat.of (f ⁻¹' Z') ⟶ W) (hφ : IsProperMap φ)
    (hφ' : IsProperMap φ')
    (hφφ' : ∀ (x : Y') (hx : x ∈ f ⁻¹' Z) (hx' : x ∈ f ⁻¹' Z'), φ ⟨x, hx⟩ = φ' ⟨x, hx'⟩) :
    (pushforward R (ModuleCat.of R R) φ hφ m).hom
        (congrDegree R _ hm (capProductSupportPullback R f hZ hd j k c a)) =
      (pushforward R (ModuleCat.of R R) φ' hφ' m).hom
        (congrDegree R _ hm (capProductSupportPullback R f hZ' hd' j k
          ((cohomologyWithSupports.forget R (ModuleCat.of R R) Y h.subset j).hom c) a)) := by
  subst h
  rw [cohomologyWithSupports.forget_refl]
  have hφe : φ = φ' := by
    ext x
    exact hφφ' x.1 x.2 x.2
  subst hφe
  rfl

end CongrSet

/-! ### The zero fibre of `pr₁ ∘ Φ` -/

section BallChart

variable {P B : Type} [TopologicalSpace P] [TopologicalSpace B] {ε : ℝ}

/-- For `Φ : P ≃ₜ B_ε × B` and `g = pr₁ ∘ Φ`, the point `Φ⁻¹(0, b)` lies in `g⁻¹(0)`. -/
lemma symm_zero_mem_preimage_zero (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (hε : 0 < ε)
    (g : TopCat.of P ⟶ TopCat.of ℂ) (hg : ∀ p, g p = ((Φ p).1 : ℂ)) (b : B) :
    Φ.symm (⟨0, mem_ball_self hε⟩, b) ∈ (g ⁻¹' {0} : Set (TopCat.of P)) := by
  change g _ = 0
  rw [hg, Φ.apply_symm_apply]

/-- The zero fibre `g⁻¹(0)` of `g = pr₁ ∘ Φ` for `Φ : P ≃ₜ B_ε × B`, identified with `B` by
`y ↦ (Φ y).2`. -/
def ballZeroFibreHomeomorph (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (hε : 0 < ε)
    (g : TopCat.of P ⟶ TopCat.of ℂ) (hg : ∀ p, g p = ((Φ p).1 : ℂ)) :
    (g ⁻¹' {0} : Set (TopCat.of P)) ≃ₜ B where
  toFun y := (Φ y).2
  invFun b := ⟨Φ.symm (⟨0, mem_ball_self hε⟩, b), symm_zero_mem_preimage_zero Φ hε g hg b⟩
  left_inv y := Subtype.ext <| by
    have hy : ((Φ y).1 : ℂ) = 0 := (hg y).symm.trans y.2
    have h : ((⟨0, mem_ball_self hε⟩ : ball (0 : ℂ) ε), (Φ y).2) = Φ y :=
      Prod.ext (Subtype.ext hy.symm) rfl
    exact (congrArg Φ.symm h).trans (Φ.symm_apply_apply _)
  right_inv b := congrArg Prod.snd (Φ.apply_symm_apply _)
  continuous_toFun := continuous_snd.comp (Φ.continuous.comp continuous_subtype_val)
  continuous_invFun :=
    (Φ.symm.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _

/-- `ballZeroFibreHomeomorph Φ hε g hg y = (Φ y).2`. -/
@[simp]
lemma ballZeroFibreHomeomorph_apply (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (hε : 0 < ε)
    (g : TopCat.of P ⟶ TopCat.of ℂ) (hg : ∀ p, g p = ((Φ p).1 : ℂ))
    (y : (g ⁻¹' {0} : Set (TopCat.of P))) :
    ballZeroFibreHomeomorph Φ hε g hg y = (Φ y).2 :=
  rfl

/-- The product chart `Θ : P ≅ B × ℂ`, `p ↦ ((Φ p).2, ρ (Φ p).1)`, of a ball chart
`Φ : P ≅ B_ε × B`, for the radial homeomorphism `ρ : B_ε ≅ ℂ`. -/
def ballChartProdHomeomorph (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (hε : 0 < ε) : P ≃ₜ B × ℂ :=
  Φ.trans ((Homeomorph.prodComm _ _).trans ((Homeomorph.refl B).prodCongr (ballZeroHomeomorph hε)))

/-- `ballChartProdHomeomorph Φ hε p = ((Φ p).2, ballZeroHomeomorph hε (Φ p).1)`. -/
@[simp]
lemma ballChartProdHomeomorph_apply (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (hε : 0 < ε) (p : P) :
    ballChartProdHomeomorph Φ hε p = ((Φ p).2, ballZeroHomeomorph hε (Φ p).1) :=
  rfl

/-- The map `z ↦ ε (√(1 + ‖z‖²))⁻¹ • z`, the inverse of the radial homeomorphism `B_ε ≅ ℂ`
followed by the inclusion `B_ε ⊆ ℂ`. -/
def ballRetractionHom (ε : ℝ) : TopCat.of ℂ ⟶ TopCat.of ℂ :=
  TopCat.ofHom ⟨fun z ↦ ε • univUnitBall z,
    (continuousOn_univ.1 univUnitBall.continuousOn).const_smul ε⟩

/-- `ballRetractionHom ε z = ε • univUnitBall z`. -/
@[simp]
lemma ballRetractionHom_apply (z : ℂ) : ballRetractionHom ε z = ε • univUnitBall z :=
  rfl

/-- For `0 < ε`, the preimage of `0` under `ballRetractionHom ε` is `{0}`. -/
lemma preimage_ballRetractionHom_zero (hε : 0 < ε) :
    (ballRetractionHom ε ⁻¹' {0} : Set (TopCat.of ℂ)) = {0} := by
  ext z
  exact coe_ballZeroHomeomorph_symm_eq_zero_iff hε z

/-- For a ball chart `Φ : P ≅ B_ε × B` with `B` metrizable and `g = pr₁ ∘ Φ`, the zero fibre
`g⁻¹(0)` has arbitrarily small proper neighbourhood deformations in `P`. -/
theorem hasProperNeighbourhoodDeformations_ballChart [TopologicalSpace.MetrizableSpace B]
    (hε : 0 < ε) (Φ : P ≃ₜ ball (0 : ℂ) ε × B) (g : TopCat.of P ⟶ TopCat.of ℂ)
    (hg : ∀ p, g p = ((Φ p).1 : ℂ)) : HasProperNeighbourhoodDeformations (g ⁻¹' {0}) := by
  set Θ := ballChartProdHomeomorph Φ hε
  set gΘ : TopCat.of P ⟶ TopCat.of ℂ :=
    TopCat.ofHom ⟨fun p ↦ (Θ p).2, continuous_snd.comp Θ.continuous⟩
  have h := hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd Θ gΘ fun _ ↦ rfl
  have he : (gΘ ⁻¹' {0} : Set (TopCat.of P)) = g ⁻¹' {0} := by
    ext p
    change ballZeroHomeomorph hε (Φ p).1 = 0 ↔ g p = 0
    rw [hg, ← coe_ballZeroHomeomorph_symm_eq_zero_iff hε, Homeomorph.symm_apply_apply]
  rw [he] at h
  exact h

section Orientation

variable {k : ℕ} [ChartedSpace (EuclideanSpace ℂ (Fin (k + 1))) P]
  [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]

/-- **The product chart of a holomorphic ball chart preserves complex orientations.** If
`Φ : P ≅ B_ε × B` is holomorphic in charts with injective derivative, then
`Θ = (id × ρ) ∘ swap ∘ Φ : P ≅ B × ℂ` is orientation preserving from the complex orientation of
`ℂᵏ⁺¹` to the product of the complex orientations of `ℂᵏ` and `ℂ`. -/
theorem isOrientationPreserving_ballChartProdHomeomorph (hε : 0 < ε)
    (Φ : P ≃ₜ ball (0 : ℂ) ε × B)
    (hΦ : ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) P,
      ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
        ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
          Function.Injective L ∧
          HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x)) :
    IsOrientationPreserving (H' := ModelProd (EuclideanSpace ℂ (Fin k)) ℂ)
      (euclideanComplexOrientationBasis (k + 1))
      (((euclideanComplexOrientationBasis k).prod Complex.basisOneI).reindex finSumFinEquiv)
      (ballChartProdHomeomorph Φ hε) := by
  apply isOrientationPreserving_of_hasFDerivAt
  intro c hc e' he' x hx hx'
  obtain ⟨c', hc', e₂, he₂, rfl⟩ := he'
  rw [chartedSpaceSelf_atlas] at he₂
  subst he₂
  have hx2 : (Φ x).2 ∈ c'.source := hx'.1
  obtain ⟨L, hLi, hL⟩ := hΦ c hc c' hc' x hx hx2
  set a₀ : ℂ := ((Φ (c.symm (c x))).1 : ℂ)
  have ha₀ : ε⁻¹ • a₀ ∈ ball (0 : ℂ) 1 := inv_smul_mem_ball_one hε _
  obtain ⟨hd, hdet⟩ := differentiableAt_univUnitBall_symm_and_det_pos ha₀
  set Dρ : ℂ →L[ℝ] ℂ :=
    (fderiv ℝ univUnitBall.symm (ε⁻¹ • a₀)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)
  have hρ : HasFDerivAt (fun a : ℂ ↦ univUnitBall.symm (ε⁻¹ • a)) Dρ a₀ :=
    hd.hasFDerivAt.comp a₀ ((hasFDerivAt_id a₀).const_smul ε⁻¹)
  have hdetρ : 0 < LinearMap.det (Dρ : ℂ →ₗ[ℝ] ℂ) := by
    have h2 : ((ε⁻¹ • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
        ε⁻¹ • LinearMap.id := rfl
    rw [show (Dρ : ℂ →ₗ[ℝ] ℂ) = (fderiv ℝ univUnitBall.symm (ε⁻¹ • a₀) : ℂ →ₗ[ℝ] ℂ) ∘ₗ
      ((ε⁻¹ • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) from rfl,
      LinearMap.det_comp, h2, LinearMap.det_smul,
      LinearMap.det_id, mul_one]
    exact mul_pos hdet (pow_pos (inv_pos.2 hε) _)
  set G : ℂ × EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin k) × ℂ :=
    fun q ↦ (q.2, univUnitBall.symm (ε⁻¹ • q.1))
  set Gd : ℂ × EuclideanSpace ℂ (Fin k) →L[ℝ] EuclideanSpace ℂ (Fin k) × ℂ :=
    (ContinuousLinearMap.snd ℝ ℂ (EuclideanSpace ℂ (Fin k))).prod
      (Dρ.comp (ContinuousLinearMap.fst ℝ ℂ (EuclideanSpace ℂ (Fin k))))
  have hG : HasFDerivAt G Gd (a₀, c' (Φ (c.symm (c x))).2) :=
    hasFDerivAt_snd.prodMk
      (HasFDerivAt.comp (g := fun a : ℂ ↦ univUnitBall.symm (ε⁻¹ • a)) _ hρ hasFDerivAt_fst)
  have hcomp := hG.comp (c x) (hL.restrictScalars ℝ)
  refine ⟨Gd.comp (L.restrictScalars ℝ), hcomp, ?_⟩
  set N : EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin k) × ℂ :=
    (LinearEquiv.prodComm ℂ ℂ (EuclideanSpace ℂ (Fin k))).toLinearMap ∘ₗ
      (L : EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] ℂ × EuclideanSpace ℂ (Fin k))
  have hNi : Function.Injective N := fun a b h ↦
    hLi ((LinearEquiv.prodComm ℂ ℂ (EuclideanSpace ℂ (Fin k))).injective h)
  set M : (EuclideanSpace ℂ (Fin k) × ℂ) →ₗ[ℝ] (EuclideanSpace ℂ (Fin k) × ℂ) :=
    LinearMap.prodMap LinearMap.id (Dρ : ℂ →ₗ[ℝ] ℂ)
  have hfun : ⇑(Gd.comp (L.restrictScalars ℝ)) ∘ euclideanComplexOrientationBasis (k + 1) =
      ⇑M ∘ (⇑(N.restrictScalars ℝ) ∘ euclideanComplexOrientationBasis (k + 1)) := rfl
  rw [hfun, Module.Basis.det_comp]
  refine mul_pos ?_ (det_prod_basisOneI_pos hNi)
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  exact hdetρ

end Orientation

variable (R : Type) [CommRing R]

/-- **`g^* u₀ ∩ μ_P = μ_B` in a holomorphic ball chart.** For a ball chart `Φ : P ≃ₜ B_ε × B`,
holomorphic in charts with injective derivative, and `g = pr₁ ∘ Φ`, the push-forward of
`g^* u₀ ∩ μ_P` along `ballZeroFibreHomeomorph` is the fundamental class `μ_B`. -/
theorem IsFundamentalClass.pushforward_ballZeroFibreHomeomorph_capProductSupportPullback {k : ℕ}
    [T2Space P] [ChartedSpace (EuclideanSpace ℂ (Fin (k + 1))) P]
    [ConnectedSpace B] [SecondCountableTopology B] [TopologicalSpace.MetrizableSpace B]
    [ChartedSpace (EuclideanSpace ℂ (Fin k)) B]
    {μP : borelMooreHomology R (ModuleCat.of R R) (TopCat.of P) (2 * (k + 1) : ℕ)}
    (hμP : IsFundamentalClass R (euclideanComplexOrientationBasis (k + 1)) μP)
    {μB : borelMooreHomology R (ModuleCat.of R R) (TopCat.of B) (2 * k : ℕ)}
    (hμB : IsFundamentalClass R (euclideanComplexOrientationBasis k) μB)
    (hε : 0 < ε) (Φ : P ≃ₜ ball (0 : ℂ) ε × B)
    (hΦ : ∀ c ∈ atlas (EuclideanSpace ℂ (Fin (k + 1))) P,
      ∀ c' ∈ atlas (EuclideanSpace ℂ (Fin k)) B, ∀ x ∈ c.source, (Φ x).2 ∈ c'.source →
        ∃ L : EuclideanSpace ℂ (Fin (k + 1)) →L[ℂ] ℂ × EuclideanSpace ℂ (Fin k),
          Function.Injective L ∧
          HasFDerivAt (fun y ↦ (((Φ (c.symm y)).1 : ℂ), c' (Φ (c.symm y)).2)) L (c x))
    (g : TopCat.of P ⟶ TopCat.of ℂ) (hg : ∀ p, g p = ((Φ p).1 : ℂ))
    {u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of ℂ) {0} (2 : ℕ)}
    (hu₀ : IsLocalOrientationClass R Complex.basisOneI (0 : TopCat.of ℂ) u₀)
    (hYd : HasProperNeighbourhoodDeformations (g ⁻¹' {0}))
    (hdeg : ((2 * (k + 1) : ℕ) : ℤ) - (2 : ℕ) = (2 * k : ℕ)) :
    (pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (ballZeroFibreHomeomorph Φ hε g hg : C(g ⁻¹' {0}, B)))
        (ballZeroFibreHomeomorph Φ hε g hg).isProperMap (2 * k : ℕ)).hom
      (congrDegree R _ hdeg
        (capProductSupportPullback R g isClosed_singleton hYd (2 : ℕ) (2 * (k + 1) : ℕ) u₀ μP)) =
      μB := by
  set Θ := ballChartProdHomeomorph Φ hε
  obtain ⟨gΘ, hgΘ⟩ : ∃ gΘ : TopCat.of P ⟶ TopCat.of ℂ, ∀ p, gΘ p = (Θ p).2 :=
    ⟨TopCat.ofHom ⟨fun p ↦ (Θ p).2, continuous_snd.comp Θ.continuous⟩, fun _ ↦ rfl⟩
  have hgfac : g = gΘ ≫ ballRetractionHom ε := by
    ext p
    change g p = ballRetractionHom ε (gΘ p)
    rw [hg, hgΘ]
    exact (congrArg Subtype.val ((ballZeroHomeomorph hε).symm_apply_apply (Φ p).1)).symm
  subst hgfac
  have hσ0 := preimage_ballRetractionHom_zero hε
  have hcap : capProductSupportPullback R (gΘ ≫ ballRetractionHom ε) isClosed_singleton hYd
      (2 : ℕ) (2 * (k + 1) : ℕ) u₀ μP =
      capProductSupportPullback R gΘ
        (isClosed_singleton.preimage (ballRetractionHom ε).hom.continuous) hYd (2 : ℕ)
        (2 * (k + 1) : ℕ)
        ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (ballRetractionHom ε) {0}
          (2 : ℕ)).hom u₀) μP := by
    rw [capProductSupportPullback_apply, capProductSupportPullback_apply,
      cohomologyWithSupports.pullback_comp]
    rfl
  have hYd' := hasProperNeighbourhoodDeformations_preimage_zero_of_eq_snd Θ gΘ hgΘ
  have hφφ' : ∀ (x : TopCat.of P) (hx : x ∈ gΘ ⁻¹' (ballRetractionHom ε ⁻¹' {0}))
      (hx' : x ∈ gΘ ⁻¹' {0}),
      ballZeroFibreHomeomorph Φ hε (gΘ ≫ ballRetractionHom ε) hg ⟨x, hx⟩ =
        zeroFibreHomeomorph Θ gΘ hgΘ ⟨x, hx'⟩ :=
    fun x hx hx' ↦ rfl
  have hmain := pushforward_capProductSupportPullback_congr_set R gΘ hσ0
    (isClosed_singleton.preimage (ballRetractionHom ε).hom.continuous) isClosed_singleton hYd
    hYd' (2 : ℕ) (2 * (k + 1) : ℕ) hdeg
    ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (ballRetractionHom ε) {0}
      (2 : ℕ)).hom u₀) μP
    (TopCat.ofHom (X := (gΘ ⁻¹' (ballRetractionHom ε ⁻¹' {0}) : Set (TopCat.of P)))
      ((ballZeroFibreHomeomorph Φ hε (gΘ ≫ ballRetractionHom ε) hg :
        C(((gΘ ≫ ballRetractionHom ε) ⁻¹' {0} : Set (TopCat.of P)), B))))
    (TopCat.ofHom (zeroFibreHomeomorph Θ gΘ hgΘ : C(_, B)))
    (ballZeroFibreHomeomorph Φ hε (gΘ ≫ ballRetractionHom ε) hg).isProperMap
    (zeroFibreHomeomorph Θ gΘ hgΘ).isProperMap hφφ'
  rw [hcap]
  refine hmain.trans ?_
  have hs : ({0}ᶜ : Set (TopCat.of ℂ)) ⊆ (ballRetractionHom ε) ⁻¹' ({0}ᶜ : Set (TopCat.of ℂ)) :=
    fun z hz h ↦ hz ((coe_ballZeroHomeomorph_symm_eq_zero_iff hε z).1 h)
  have hdetσ : 0 < Complex.basisOneI.det
      (((ε • ContinuousLinearMap.id ℝ ℂ : ℂ →L[ℝ] ℂ) : ℂ → ℂ) ∘ Complex.basisOneI) := by
    change 0 < Complex.basisOneI.det (⇑(ε • LinearMap.id : ℂ →ₗ[ℝ] ℂ) ∘ Complex.basisOneI)
    rw [Module.Basis.det_comp, Module.Basis.det_self, LinearMap.det_smul, LinearMap.det_id]
    positivity
  have hu := IsLocalOrientationClass.map_of_hasFDerivAt (f := fun z : ℂ ↦ ε • univUnitBall z)
    (ballRetractionHom ε).hom.continuous (by simp [univUnitBall_apply_zero]) hs
    (hasFDerivAt_univUnitBall_zero.const_smul ε) hdetσ hu₀
  have key : (cohomologyWithSupports.forget R (ModuleCat.of R R) (TopCat.of ℂ) hσ0.subset
      (2 : ℕ)).hom ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (ballRetractionHom ε)
        {0} (2 : ℕ)).hom u₀) =
      (relativeSingularCohomology.map R (ModuleCat.of R R) (ballRetractionHom ε) hs
        (2 : ℕ)).hom u₀ := by
    have h := congrArg (fun φ ↦ ModuleCat.Hom.hom φ u₀)
      (relativeSingularCohomology.map_comp R (ModuleCat.of R R) (𝟙 (TopCat.of ℂ))
        (ballRetractionHom ε) (A'' := ({0}ᶜ : Set (TopCat.of ℂ)))
        (A' := (ballRetractionHom ε ⁻¹' ({0} : Set (TopCat.of ℂ)))ᶜ)
        (A := ({0}ᶜ : Set (TopCat.of ℂ))) (Set.compl_subset_compl.mpr hσ0.subset)
        (fun _ hx ↦ hx) (2 : ℕ))
    exact h.symm
  rw [key]
  exact IsFundamentalClass.pushforward_zeroFibreHomeomorph_capProductSupportPullback_complex R
    (n := 2 * k) hμP hμB Θ (isOrientationPreserving_ballChartProdHomeomorph hε Φ hΦ) gΘ hgΘ hu
    hYd' hdeg

end BallChart

end MMP
