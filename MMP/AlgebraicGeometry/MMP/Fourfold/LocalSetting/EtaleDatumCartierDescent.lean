module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.MMP.BasepointFree.CurveFibreLineBundleDescent
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumRationalModel

/-!
# Cartier descent along a small model of a local étale datum

For a local étale datum `E` and a projective birational `g : Y' ⟶ E.scheme` whose fibres have
dimension at most one, a Cartier multiple `N = m D'` of a numerically `g`-trivial `ℚ`-divisor
`D'` has `𝒪_{Y'}(N) ≅ g^* M` for an invertible sheaf `M` on `E.scheme`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- A scheme containing a dense open isomorphic to a nonempty open of an irreducible scheme is
irreducible. -/
private theorem irreducibleSpace_of_iso_of_dense {X Y : Scheme.{0}} [IrreducibleSpace Y]
    (U : X.Opens) (V : Y.Opens) (hU : Dense (U : Set X)) (hV : (V : Set Y).Nonempty)
    (e : U.toScheme ≅ V.toScheme) : IrreducibleSpace X := by
  have hVirr : IsIrreducible (V : Set Y) :=
    ⟨hV, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset V.isOpen
      (Set.subset_univ _)⟩
  haveI : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hVirr
  have hrange : Set.range (e.inv ≫ U.ι) = (U : Set X) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e.inv v).2
    · intro hx
      obtain ⟨u, rfl⟩ : x ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
      refine ⟨e.hom u, ?_⟩
      change (e.hom ≫ e.inv ≫ U.ι) u = U.ι u
      rw [e.hom_inv_id_assoc]
  have hirr : IsIrreducible (U : Set X) := by
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (e.inv ≫ U.ι).continuous.continuousOn
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hU.closure_eq]
  exact hirr.closure

variable {Y Yt Y' : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
  {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}

/-- Let `(Y, Θ, T, π)` be a local setting and `E = (Y_e, q, η', L̃)` a local étale datum, and let
`g : Y' ⟶ Y_e` be projective birational with `Y'` normal and every fibre of dimension at most one.
If `D'` is a `ℚ`-Cartier `ℚ`-divisor on `Y'` that is numerically `g`-trivial, then for every
`m > 0` and every Cartier divisor `N` on `Y'` with `N = m D'`, there is an invertible sheaf `M`
on `Y_e` with `𝒪_{Y'}(N) ≅ g^* M`. -/
@[mmp "lem_mmp_lc_bpf_local_small_model_cartier_descent"]
public theorem LocalEtaleDatum.exists_isInvertibleModule_divisorialSheaf_iso_pullback
    (h : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L)
    [IsNormal Y'] [IsLocallyNoetherian Y'] [CompactSpace Y']
    (g : Y' ⟶ E.scheme) [QuasiCompact (g ≫ E.map ≫ sY)]
    (hg : IsProjectiveMorphism g) (hb : IsBirationalMorphism g)
    (hfib : ∀ y : E.scheme, topologicalKrullDim (g.fiber y) ≤ 1)
    (D' : QDivisor Y') (hD' : D'.IsQCartier)
    (hnum : IsNumericallyTrivialOver ℂ (g ≫ E.map ≫ sY) g (QDivisor.toRDivisor D'))
    (m : ℕ) (hm : 0 < m) (N : Divisor Y') (hN : N.IsCartier)
    (hND : Divisor.toQDivisor N = (m : ℚ) • D') :
    ∃ (M : E.scheme.Modules) (_ : Stacks.Ample.IsInvertibleModule E.scheme M),
      Nonempty (N.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj M) := by
  haveI hYe : IsQuasiProjectiveVariety ℂ (E.map ≫ sY) := E.isQuasiProjectiveVariety
  haveI : IsNormal E.scheme := E.isNormal
  haveI : IsIntegral E.scheme := hYe.toIsVariety.toIsIntegral
  haveI : Nonempty E.scheme := ⟨E.point⟩
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hg
  haveI : IrreducibleSpace Y' := by
    obtain ⟨e, -⟩ := hb
    exact irreducibleSpace_of_iso_of_dense e.source e.target e.dense_source
      e.dense_target.nonempty e.iso
  haveI : IsIntegral Y' := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ E.map ≫ sY) := {}
  haveI : IsQuasiProjectiveVariety ℂ (g ≫ E.map ≫ sY) :=
    (isQuasiProjectiveVariety_iff ℂ _).2 ⟨inferInstance,
      IsQuasiProjective.comp _ _ hg.isQuasiProjective hYe.isQuasiProjective⟩
  obtain ⟨hunit, hR1⟩ := E.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived_one h g hg hb
  haveI := hN.isInvertibleModule_divisorialSheaf
  obtain ⟨hinv, hiso⟩ := isInvertible_pushforward_and_isIso_counit_of_forall_degree_eq_zero
    g rfl hg hunit hR1 hfib N.divisorialSheaf
    (hnum.degree_eq_zero hm (by rw [hND, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]) hN)
  exact ⟨_, hinv, ⟨(asIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
    N.divisorialSheaf)).symm⟩⟩

end MMP.Fourfold
