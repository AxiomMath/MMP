module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo

/-!
# Singular curves of the product of a terminal threefold with a line

Let `Y` be a normal complex threefold such that `(Y, 0)` is terminal. Terminal varieties are
smooth in codimension two, so `Sing Y` is a finite set of closed points. The singular locus of
`Y × ℙ¹` is the preimage of `Sing Y` under the first projection, so for a closed subset `Q ⊆ Y`
the irreducible curves contained in `Sing (Y × ℙ¹) ∩ (Q × ℙ¹)` are exactly the curves
`T_y = {y} × ℙ¹` with `y ∈ Sing Y ∩ Q`, and these are pairwise distinct.

## Main results

* `MMP.Fourfold.IsTerminalVariety.singularLocus_product_projectiveLine_curves`: `Sing Y` is a
  finite set of closed points, and the irreducible curves in `Sing (Y × ℙ¹) ∩ (Q × ℙ¹)` are the
  pairwise distinct `MMP.Fourfold.pointSettingCurve sY y`, `y ∈ Sing Y ∩ Q`.

## Implementation notes

`Y × ℙ¹` is the fibre product of `sY` and the structure morphism of
`AlgebraicGeometry.projectiveLine ℂ`, a complex scheme through the first projection. An
irreducible curve is a closed irreducible subset of topological Krull dimension `1`, and
`{y} × ℙ¹` is the preimage of `y` under the first projection. Terminality of `(Y, 0)` is
`MMP.Fourfold.IsTerminalVariety`, which contains that `K_Y` is `ℚ`-Cartier.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 5.18
-/

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MMP.Mori

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- For a closed point `y` of a normal complex variety `Y`, the curve `{y} × ℙ¹ ⊆ Y × ℙ¹` is
closed, irreducible and of dimension one. -/
private theorem pointSettingCurve_spec {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (hY : IsNormalVariety ℂ sY) (y : Y) (hy : IsClosed ({y} : Set Y)) :
    IsClosed (pointSettingCurve sY y) ∧ IsIrreducible (pointSettingCurve sY y) ∧
      topologicalKrullDim (pointSettingCurve sY y) = 1 := by
  set sL := projectiveLine ℂ ↘ Spec (.of ℂ)
  set i := Y.fromSpecResidueField y
  have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hy
  have := hY.1
  have : IsNormal (Spec (Y.residueField y)) := isNormal_spec_of_isIntegrallyClosed _
  have hg : IsNormalVariety ℂ (i ≫ sY) :=
    ⟨(isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      inferInstance⟩
  have hb := (product_line_basic (i ≫ sY) sL hg (Or.inl ⟨Iso.refl _, by simp [sL]⟩)).1
  let ψ := pullbackRightPullbackFstIso sY sL i
  let φ := ψ.inv ≫ pullback.snd i (pullback.fst sY sL)
  have hφ : Set.range φ = pointSettingCurve sY y := by
    simp only [φ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ψ.inv.surjective.range_eq, Set.image_univ]
    rw [Scheme.Pullback.range_snd, Scheme.range_fromSpecResidueField]
    rfl
  refine ⟨hy.preimage (pullback.fst sY sL).base.hom.continuous, ?_, ?_⟩
  · have := hb.2.2.1.1.toIsIntegral
    rw [← hφ, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ φ.base.hom.continuous.continuousOn
  · let e := φ.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hφ)
    rw [← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph, hb.2.2.2.1]
    change topologicalKrullDim (PrimeSpectrum (Y.residueField y)) + 1 = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rfl

/-- An irreducible closed subset of dimension one contained in an irreducible closed subset of
dimension one is equal to it. -/
private theorem eq_of_subset_of_topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X]
    {Z T : Set X} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hTc : IsClosed T)
    (hTi : IsIrreducible T) (hZT : Z ⊆ T) (hZ : topologicalKrullDim Z = 1)
    (hT : topologicalKrullDim T = 1) : Z = T := by
  let Z' : IrreducibleCloseds X := ⟨Z, hZi, hZc⟩
  let T' : IrreducibleCloseds X := ⟨T, hTi, hTc⟩
  have h1 : Order.height Z' = 1 := by
    exact_mod_cast (topologicalKrullDim_coe_eq_height Z').symm.trans hZ
  have h2 : Order.height T' = 1 := by
    exact_mod_cast (topologicalKrullDim_coe_eq_height T').symm.trans hT
  by_contra hne
  have := Order.height_add_one_le (lt_of_le_of_ne (show Z' ≤ T' from hZT)
    fun h ↦ hne (congrArg SetLike.coe h))
  rw [h1, h2] at this
  exact absurd this (by decide)

/-- In a `T₀` space of dimension at most `n`, every point of a closed subset of codimension at
least `n` is closed. -/
private theorem isClosed_singleton_of_le_closedsCodimension {T : Type*} [TopologicalSpace T]
    [T0Space T] {n : ℕ} (hdim : topologicalKrullDim T ≤ n) {Z : Closeds T}
    (hcod : (n : ℕ∞) ≤ closedsCodimension Z) {y : T} (hy : y ∈ Z) : IsClosed ({y} : Set T) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_contra hne
  let W : IrreducibleCloseds T := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let V : IrreducibleCloseds T := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hVW : V < W := lt_of_le_of_ne
    (closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure)
    fun h ↦ hne (inseparable_iff_closure_eq.mpr (congrArg SetLike.coe h)).eq
  have hW : (n : ℕ∞) ≤ Order.coheight W := le_closedsCodimension_iff.mp hcod W
    (Z.isClosed.closure_subset_iff.mpr (by simpa using hy))
  have := (WithBot.coe_le_coe.mpr ((add_le_add_left hW 1).trans
    (Order.coheight_add_one_le hVW))).trans ((Order.coheight_le_krullDim V).trans hdim)
  norm_cast at this
  omega

/-- A closed subset of a noetherian quasi-sober space all of whose points are closed is finite. -/
private theorem finite_of_isClosed_of_forall_isClosed_singleton {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {Z : Set T} (hZ : IsClosed Z)
    (h : ∀ y ∈ Z, IsClosed ({y} : Set T)) : Z.Finite := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSf.sUnion fun t ht ↦ ?_
  have hg := (hSi t ht).isGenericPoint_genericPoint_closure
  rw [(hSc t ht).closure_eq] at hg
  rw [← hg.def, (h _ (Set.mem_sUnion_of_mem hg.mem ht)).closure_eq]
  exact Set.finite_singleton _

/-- Let `Y` be a normal complex threefold with `(Y, 0)` terminal and `Q ⊆ Y` closed. Then
`Sing Y` is a finite set of closed points, and the irreducible curves contained in
`Sing (Y × ℙ¹) ∩ (Q × ℙ¹)` are exactly the pairwise distinct curves `{y} × ℙ¹`
(`MMP.Fourfold.pointSettingCurve`), `y ∈ Sing Y ∩ Q`. -/
@[mmp "lem_mmp_indexb_product_singular_curves"]
public theorem IsTerminalVariety.singularLocus_product_projectiveLine_curves
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) (hdim : topologicalKrullDim Y = 3)
    (h : IsTerminalVariety sY) (Q : Closeds Y) :
    ((singularLocus sY : Set Y).Finite ∧ ∀ y ∈ (singularLocus sY : Set Y), IsClosed {y}) ∧
    {Z : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)) : Scheme.{0}) |
        IsClosed Z ∧ IsIrreducible Z ∧ topologicalKrullDim Z = 1 ∧
        Z ⊆ (singularLocus (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) : Set _) ∩
          (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base ⁻¹' (Q : Set Y)} =
      pointSettingCurve sY '' ((singularLocus sY : Set Y) ∩ Q) ∧
    Set.InjOn (pointSettingCurve sY) ((singularLocus sY : Set Y) ∩ Q) := by
  obtain ⟨n, K, hK, hKQ⟩ := h.1.1.isPair.2
  have hclosed : ∀ y ∈ (singularLocus sY : Set Y), IsClosed ({y} : Set Y) := fun y ↦
    isClosed_singleton_of_le_closedsCodimension (n := 3) hdim.le
      (IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
        h QDivisor.isQCartier_zero hK (by simpa using hKQ)).2
  have := hY.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  have hfin := finite_of_isClosed_of_forall_isClosed_singleton (singularLocus sY).isClosed hclosed
  set sL := projectiveLine ℂ ↘ Spec (.of ℂ)
  have hb := product_line_basic sY sL hY (Or.inl ⟨Iso.refl _, by simp [sL]⟩)
  refine ⟨⟨hfin, hclosed⟩, ?_, fun y _ y' _ hyy' ↦
    Set.singleton_injective (hb.1.2.1.surj.preimage_injective hyy')⟩
  ext Z
  simp only [Set.mem_setOf_eq, Set.mem_image]
  rw [hb.2.1, ← Set.preimage_inter]
  constructor
  · rintro ⟨hZc, hZi, hZd, hZsub⟩
    obtain ⟨T, hT, hZT⟩ := isIrreducible_iff_sUnion_isClosed.mp hZi
      ((hfin.inter_of_left (Q : Set Y)).toFinset.image (pointSettingCurve sY))
      (by
        simp only [Finset.mem_image, Set.Finite.mem_toFinset]
        rintro _ ⟨y, hy, rfl⟩
        exact (pointSettingCurve_spec hY y (hclosed y hy.1)).1)
      (fun z hz ↦ by simpa using hZsub hz)
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hT
    obtain ⟨y, hy, rfl⟩ := hT
    obtain ⟨hc, hi, hd⟩ := pointSettingCurve_spec hY y (hclosed y hy.1)
    exact ⟨y, hy, (eq_of_subset_of_topologicalKrullDim_eq_one hZc hZi hc hi hZT hZd hd).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, hi, hd⟩ := pointSettingCurve_spec hY y (hclosed y hy.1)
    exact ⟨hc, hi, hd, Set.preimage_mono (Set.singleton_subset_iff.mpr hy)⟩

end MMP.Fourfold
