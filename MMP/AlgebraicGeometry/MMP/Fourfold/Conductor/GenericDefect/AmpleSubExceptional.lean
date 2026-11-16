module
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.MinimalModel.PltReference
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition

/-!
# Ampleness of `N H - D` on a curve-and-point exceptional model

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ᵢ Fᵢ` and
`D = ∑ᵢ mᵢ Fᵢ`, `-D` relatively ample over `Y`. The projective variety `Y` carries an effective
ample Cartier divisor `H_Y`; its pull-back `H = r^* H_Y` is defined since `r` is dominant. Since
`-D` is `r`-ample and `H_Y` is ample, `A = N H - D` is ample on `Z` for all large `N`
([Stacks, Tag 0C4K]), hence ample on every closed subscheme of `Z`, in particular on every
component `Fᵢ` and on every double surface of `F`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.compactSpace`: the base `Y` is quasi-compact.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_isAmple_nsmul_sub`: an effective ample
  Cartier `H_Y` on `Y` with pull-back `H` such that `N H - D` is ample on `Z` and on every closed
  subscheme of `Z`, for all large `N`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Fourfold

open MMP.Mori

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- The base `Y` of a curve-and-point exceptional model is quasi-compact. -/
theorem IsCurvePointExceptionalModel.compactSpace (hr : IsCurvePointExceptionalModel sY r F D) :
    CompactSpace Y :=
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hr.isProjectiveVariety
  QuasiCompact.compactSpace_of_compactSpace sY

/-- **`A = N H - D` is ample for large `N`.** On a curve-and-point exceptional model there are an
effective ample Cartier divisor `H_Y` on `Y` and its pull-back `H = r^* H_Y` to `Z` such that for
all large `N` the divisor `N H - D` is Cartier and ample on `Z`, and its restriction to every
closed subscheme of `Z` (every component `Fᵢ`, every double surface) is ample. -/
theorem IsCurvePointExceptionalModel.exists_isAmple_nsmul_sub [CompactSpace Y]
    (hr : IsCurvePointExceptionalModel sY r F D) :
    ∃ (HY : Divisor Y) (hHY : HY.IsCartier)
      (hgen : ∀ W : irreducibleComponents Z, r (componentGenericPoint Z W) ∉ HY.supp)
      (H : Divisor Z), HY.IsEffective ∧ HY.IsAmple hHY ∧ HY.IsPullback r hgen H ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ hA : (N • H - D).IsCartier, (N • H - D).IsAmple hA ∧
        ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
          haveI := hA.isInvertibleModule_divisorialSheaf
          Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj (N • H - D).divisorialSheaf) := by
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hr.isProjectiveVariety
  have : IsIntegral Z := hr.isResolution.2.1.toIsIntegral
  have : IsDominant r := hr.isResolution.2.2.2.2.isDominant
  obtain ⟨HY, hHY, hHYe, hHYa⟩ := exists_isCartier_isEffective_isAmple sY
  have hgen := map_componentGenericPoint_notMem_supp_of_isDominant r HY
  obtain ⟨H, hH⟩ := hHY.exists_isPullback (f := r) hgen
  obtain ⟨hD, hDr⟩ := hr.isRelativelyAmple_neg
  have hHYr := MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf sY hHY hHYa
  obtain ⟨N₀, hN₀⟩ :=
    PltReference.exists_isRelativelyAmple_add_nsmul r sY hD hDr hHY hHYr hH
  refine ⟨HY, hHY, hgen, H, hHYe, hHYa, hH, N₀, fun N hN => ?_⟩
  have key : ∀ A : Divisor Z, -D + N • H = A → ∃ hA : A.IsCartier, A.IsAmple hA ∧
      ∀ {W : Scheme.{0}} (g : W ⟶ Z) [IsClosedImmersion g],
        haveI := hA.isInvertibleModule_divisorialSheaf
        Stacks.Ample.IsAmple W ((Scheme.Modules.pullback g).obj A.divisorialSheaf) := by
    rintro A rfl
    have hc := hD.add ((hH.isCartier hHY).nsmul N)
    have := hc.isInvertibleModule_divisorialSheaf
    have hamp : Stacks.Ample.IsAmple Z (-D + N • H).divisorialSheaf :=
      Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine (r ≫ sY) _
        (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple _ _
          inferInstance (hN₀ N hN))
    refine ⟨hc, hamp, fun {W} g _ => ?_⟩
    have h1 := Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding g _
      hamp (Or.inl ⟨inferInstance, inferInstance⟩)
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((Adjunction.leftAdjointUniq
        (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction g.toLRSHom.toShHom)
        (Scheme.Modules.pullbackPushforwardAdjunction g)).app (-D + N • H).divisorialSheaf)).1 h1
  exact key _ (by abel)

end MMP.Fourfold
