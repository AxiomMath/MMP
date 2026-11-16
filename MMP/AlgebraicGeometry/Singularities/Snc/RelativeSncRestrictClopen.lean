module

public import MMP.AlgebraicGeometry.Divisor.RestrictOpen
public import MMP.AlgebraicGeometry.Singularities.Snc.ReducedPreimageFiniteCover
public import MMP.AlgebraicGeometry.Singularities.Snc.WeakChartEtalePullback
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree

/-!
# Relative simple normal crossing divisors restrict to open and closed integral pieces

Let `π : V ⟶ Spec ℂ` be smooth of relative dimension `n` and `D` a relative simple normal crossing
divisor on `V`. For an open and closed subscheme `U ⊆ V` which is integral, the restriction of `D`
to `U` is a relative simple normal crossing divisor for `U ⟶ V ⟶ Spec ℂ`: the charts of `D` are
weak charts of `Supp D`, they pull back along the étale affine inclusion of `U`, and the reduced
divisor on `U` with these weak charts is relative snc
(`MMP.FourfoldProofs.FractionalLogComplexProof.exists_isRelativeSNC_reducedPreimage`).

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.isRelativeSNC_restrictDivisor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology MMP.Mori.Divisor.LogSpreadingProof

/-- If `D` is a relative simple normal crossing divisor for `π` and `U ⊆ V` is an open and closed
integral subscheme, then `restrictDivisor U D` is relative snc for `U.ι ≫ π`. -/
theorem isRelativeSNC_restrictDivisor (n : ℕ) {V : Scheme.{0}}
    (π : V ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π]
    (D : MMP.Mori.Divisor V) (hD : D.IsRelativeSNC n π) (U : V.Opens)
    (hU : IsClosed (U : Set V)) [IsIntegral U.toScheme] :
    MMP.Mori.Divisor.IsRelativeSNC n (U.ι ≫ π) (restrictDivisor U D) := by
  classical
  have : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]; exact hU)
  have : SmoothOfRelativeDimension n (𝟙 U.toScheme ≫ U.ι ≫ π) := by
    rw [Category.id_comp]; infer_instance
  have : Smooth (U.ι ≫ π) := SmoothOfRelativeDimension.smooth n (U.ι ≫ π)
  have hfin : topologicalKrullDim U.toScheme ≠ ⊤ := by
    rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (U.ι ≫ π) n]
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl]
    exact fun h => ENat.natCast_ne_top n (WithBot.coe_injective h)
  -- the support of the restriction is the preimage of the support
  have hZ : (U.ι.base ⁻¹' (D.supp : Set V)) = 𝟙 U.toScheme ⁻¹'
      (⋃ E ∈ (restrictDivisor U D).support, AlgebraicGeometry.PrimeDivisor.support E) := by
    rw [← coe_supp_eq_biUnion]
    ext x
    exact (mem_supp_restrictDivisor_iff U D x).symm
  have hchart : ∀ y : U.toScheme, ∃ c : WeakChart (𝟙 U.toScheme ≫ U.ι ≫ π) n
      (𝟙 U.toScheme ⁻¹' (⋃ E ∈ (restrictDivisor U D).support,
        AlgebraicGeometry.PrimeDivisor.support E)), y ∈ (c.W : Set U.toScheme) := by
    intro y
    obtain ⟨c₁, hc₁⟩ := exists_weakChart_of_isRelativeSNC π hD (U.ι y)
    obtain ⟨c₂, hc₂⟩ := exists_weakChart_comp_of_etale π U.ι
      (f' := 𝟙 U.toScheme ≫ U.ι ≫ π) (Category.id_comp _).symm c₁
    refine ⟨c₂.ofEq hZ, ?_⟩
    change y ∈ ((c₂.W : U.toScheme.Opens) : Set U.toScheme)
    rw [hc₂]
    exact hc₁
  obtain ⟨S', hS', hS'E⟩ := exists_isRelativeSNC_reducedPreimage (U.ι ≫ π) (𝟙 U.toScheme)
    rfl hfin (restrictDivisor U D).support hchart
  have hS'D : S' = restrictDivisor U D := by
    refine Finsupp.ext fun E' => ?_
    rw [hS'E E']
    by_cases h : E' ∈ (restrictDivisor U D).support
    · rw [ite_eq_left_iff.mpr (fun hn => absurd ⟨E', h, rfl⟩ hn), restrictDivisor_apply,
        hD.1 _ (by rwa [Finsupp.mem_support_iff, ← restrictDivisor_apply,
          ← Finsupp.mem_support_iff])]
    · rw [ite_eq_right_iff.mpr (fun hex => absurd (by
        obtain ⟨E, hE, he⟩ := hex
        exact (AlgebraicGeometry.PrimeDivisor.genericPoint_injective he) ▸ hE) h),
        ← Finsupp.notMem_support_iff.mp h]
  rw [← hS'D]
  simpa only [Category.id_comp] using hS'

end MMP.FourfoldProofs.FractionalLogComplexProof
