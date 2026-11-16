module

public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization

/-!
# Invertible sheaves on a projective cone that are locally `𝒪(1)`

Let `R` be a relative `Proj` situation over `X` (`Stacks.RelativeProj.Situation`) and
`g : Proj_X R ⟶ X` its relative `Proj`. If `𝒪(1)` is `g`-ample, then so is every invertible sheaf
`M` whose restriction to the chart `Proj Γ(W, R)` over each affine open `W` of `X` is isomorphic to
the twisting sheaf `𝒪(1)` of that projective spectrum: ampleness over `g⁻¹(W)` only depends on the
restriction to `g⁻¹(W)`, which is the image of the chart.

## Main results

* `MMP.Mori.isRelativelyAmple_of_restrict_projectiveConeChart_iso`: an invertible sheaf on the
  relative `Proj` that is chartwise isomorphic to `𝒪(1)` is relatively ample when `𝒪(1)` is.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace MMP.Mori

attribute [local instance] Stacks.InvertiblePullback.isInvertibleModule_pullback

/-- **Chartwise `𝒪(1)` is relatively ample.** On the relative `Proj` `g : Proj_X R ⟶ X` of a
relative `Proj` situation `R` over `X`, an invertible sheaf `M` whose restriction to the chart
`Proj Γ(W, R)` over every affine open `W` is isomorphic to the twisting sheaf `𝒪(1)` of that chart
is `g`-ample, provided `𝒪_{Proj R}(1)` is invertible and `g`-ample in the sense of Stacks
Tag 01VH. -/
theorem isRelativelyAmple_of_restrict_projectiveConeChart_iso (s : Stacks.RelativeProj.Situation.{u})
    (M : s.relativeProj.Modules) [Stacks.Ample.IsInvertibleModule s.relativeProj M]
    [Stacks.Ample.IsInvertibleModule s.relativeProj (s.twistSheaf 1)]
    (hR : Stacks.RelativeAmple.IsRelativelyAmple s.relativeProjToBase (s.twistSheaf 1))
    (e : ∀ W : s.base.affineOpens, Nonempty (M.restrict (s.relativeProjChart W) ≅
      ProjectiveSpectrum.Proj.twistingSheaf (s.sectionRingGrading W.1) 1)) :
    IsRelativelyAmple s.relativeProjToBase M := by
  intro y
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨W, hW, hyW, ?_⟩
  set c := s.relativeProjChart ⟨W, hW⟩
  have hr : Set.range (s.relativeProjToBase ⁻¹ᵁ W).ι.base = Set.range c.base := by
    rw [Scheme.Opens.range_ι, ← Stacks.RelativeProj.Situation.opensRange_relativeProjChart s ⟨W, hW⟩]
    rfl
  have h1 := hR.isAmple_preimage s.relativeProjToBase _ W hW
  have h2 := (Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_congr_range _ c hr _).mp h1
  obtain ⟨eW⟩ := e ⟨W, hW⟩
  have iso : (modulePullback c.toLRSHom.toShHom).obj (s.twistSheaf 1) ≅
      (modulePullback c.toLRSHom.toShHom).obj M :=
    (AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback c).app _ ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback c).symm.app _ ≪≫
      Stacks.RelativeProj.Situation.twistSheafChartIso s 1 ⟨W, hW⟩ ≪≫ eW.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback c).app _ ≪≫
      (AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback c).symm.app _
  have h3 := (Stacks.RelativeVeryAmple.isAmple_congr _ _ iso).mp h2
  exact (Stacks.RelativeAmpleRestrictBase.isAmple_pullbackModule_congr_range _ c hr _).mpr h3

end MMP.Mori
