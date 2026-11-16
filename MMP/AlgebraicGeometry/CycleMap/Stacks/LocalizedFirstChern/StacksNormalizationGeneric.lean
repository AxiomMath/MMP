module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.StacksBundleCharts
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksBaseChangeChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.StacksNormalizationThom
public import MMP.AlgebraicTopology.ComplexVectorBundle.OfStacksBundle

/-!
# The bundle map of a base change is a fibrewise isomorphism

For a morphism `f : X' ⟶ X` of schemes over `ℂ` and `ℰ` quasi-coherent, finite locally free of
rank `r` on `X`, the bundle map `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` is a linear isomorphism on fibres, on complex
points and in charts.

## Main results

* `MMP.Modules.isFibrewiseIso_baseChangeMap`: `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` is a fibrewise isomorphism.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1, proof of Lemma 19.1.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set
open MMP.UnderlyingSpace

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

namespace MMP.Modules

open MMP AlgebraicGeometry.SheafOfModules

section Fibrewise

variable {X X' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [X'.Over (Spec (.of ℂ))] (f : X' ⟶ X)
  [f.IsOver (Spec (.of ℂ))] (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
  [IsFiniteLocallyFreeOfRank.{0, 0, 0} E r]

/-- **The bundle map `𝐕(f^*ℰ) ⟶ 𝐕(ℰ)` of a base change is a linear isomorphism on fibres**, on
complex points and in charts. -/
theorem isFibrewiseIso_baseChangeMap : IsFibrewiseIso r f (baseChangeMap f E) := by
  intro x'
  obtain ⟨c, hc⟩ := exists_mem_chartBase E r (mapFun f x')
  have hx : x'.toHom (IsLocalRing.closedPoint ℂ) ∈ f ⁻¹ᵁ c.1.1 := by
    have h := (top_le_preimage_iff (mapFun f x') c.1.1).1 hc
    rw [toHom_mapFun] at h
    exact h
  obtain ⟨c', hxc', hle⟩ :=
    exists_chart_mem_le (E := (Scheme.Modules.pullback f).obj E) (r := r) hx
  have hx' : x' ∈ chartBase c' := (top_le_preimage_iff x' c'.1.1).2 hxc'
  obtain ⟨A, hA⟩ := exists_gl_coord_baseChangeMap f E c c' hle x' hx'
  exact ⟨c', c, A, hx', hc, hA⟩

end Fibrewise

end MMP.Modules
