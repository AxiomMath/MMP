module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BasicOpenPointsLevelSet

/-!
# Regular functions are analytic in level set charts

Let `X` be an affine scheme over `ℂ` (an `RCLike` field) with ring of global sections `A`, let
`g ∈ A`, and let `P` present `A_g` as `𝕜[x_i]_{i ∈ ι} / (f_j)_{j ∈ σ}` with polynomial map
`f = (f_j)` a submersion of class `C^n` along its zero set `L ⊆ 𝕜^ι`. The `𝕜`-points of `X` where
`g` does not vanish are homeomorphic to `L`, and `L` carries the charts of a `C^n` manifold.

Every element `s ∈ A_g` is the image of a polynomial `r` in the generators, so its value at the
point attached to `v ∈ L` is `r(v)`. Read in a chart of `L`, the function `s` is therefore `r`
composed with the inverse of the chart, which is `C^n`. For `n = ω` and `𝕜 = ℂ`: regular functions
are holomorphic in the charts of `X_reg(ℂ)`. This is the analytic input for the holomorphy of the
transition maps between charts coming from different presentations.

## Main results

* `MMP.UnderlyingSpace.awayEval_symm_nonvanishingLocusHomeomorphLevelSet_aeval`:
  the value of `r(x)` at the point attached to `v ∈ L` is `r(v)`.
* `MMP.UnderlyingSpace.contDiffOn_awayEval_comp_chart_symm`: every `s ∈ A_g` is
  `C^n` in every chart of `L`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial

universe u

namespace MMP

namespace UnderlyingSpace

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))] [IsAffine X]
  [Algebra 𝕜 Γ(X, ⊤)] {g : Γ(X, ⊤)} {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- The value of `r(x)` at the `𝕜`-point attached to a zero `v` of the relations is `r(v)`. -/
theorem awayEval_symm_nonvanishingLocusHomeomorphLevelSet_aeval
    (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 (Localization.Away g) ι σ)
    (v : SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P))
    (r : MvPolynomial ι 𝕜) :
    awayEval ((nonvanishingLocusHomeomorphLevelSet hK P).symm v) (aeval P.val r) =
      MvPolynomial.eval (v : ι → 𝕜) r := by
  have hv : (v : ι → 𝕜) ∈ zeroLocus P := by
    rw [zeroLocus_eq_levelSet]
    exact v.2
  have : (nonvanishingLocusHomeomorphLevelSet hK P).symm v =
      ⟨ofZero hK P ⟨v, hv⟩, ofZero_mem_nonvanishingLocus hK P _⟩ := rfl
  rw [this, awayEval_ofZero, presentationEval_aeval]

/-- **Regular functions are `C^n` in the charts of a level set.** If the relation map of `P` is a
`C^n` submersion along its zero set `L`, then for every `s ∈ A_g` the function
`k ↦ s(φ⁻¹(c⁻¹ k))` is `C^n` on the target of every chart `c` of `L`, where `φ` identifies the
`𝕜`-points where `g` does not vanish with `L`. -/
theorem contDiffOn_awayEval_comp_chart_symm (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 (Localization.Away g) ι σ) {n : WithTop ℕ∞}
    (hsub : SmoothLevelSet.IsSubmersionOn (𝕜 := 𝕜) n Set.univ
      (SubmersivePresentationLevelSet.relMap P))
    {z : ι → 𝕜} (hz : z ∈ SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P))
    (s : Localization.Away g) :
    ContDiffOn 𝕜 n (fun k ↦ awayEval ((nonvanishingLocusHomeomorphLevelSet hK P).symm
      ((SmoothLevelSet.chart hsub hz).symm k)) s) (SmoothLevelSet.chart hsub hz).target := by
  obtain ⟨r, rfl⟩ := P.aeval_val_surjective s
  simp_rw [awayEval_symm_nonvanishingLocusHomeomorphLevelSet_aeval]
  intro k hk
  refine ContDiffAt.contDiffWithinAt ?_
  have heq : (fun k ↦ MvPolynomial.eval (((SmoothLevelSet.chart hsub hz).symm k : _) : ι → 𝕜) r) =ᶠ[𝓝 k]
      fun k ↦ MvPolynomial.eval ((SmoothLevelSet.localDiffeo hsub hz).symm
        (0, (SmoothLevelSet.kerEquiv hsub hz).symm k)) r := by
    filter_upwards [(SmoothLevelSet.chart hsub hz).open_target.mem_nhds hk] with k' hk'
    rw [SmoothLevelSet.coe_chart_symm hsub hz hk']
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  refine (SubmersivePresentationLevelSet.contDiff_eval r).contDiffAt.comp _ ?_
  exact ContDiffAt.comp (g := (SmoothLevelSet.localDiffeo hsub hz).symm)
    (f := fun k ↦ ((0 : σ → 𝕜), (SmoothLevelSet.kerEquiv hsub hz).symm k)) k
    (SmoothLevelSet.contDiffAt_localDiffeo_symm hsub hz hk)
    (contDiff_const.prodMk (SmoothLevelSet.kerEquiv hsub hz).symm.contDiff).contDiffAt

end UnderlyingSpace

end MMP
