module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumTerminal
import MMP.AlgebraicGeometry.Singularities.SmallModelCrepant
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus

/-!
# The small model of a local étale datum is terminal

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and
`(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum (`MMP.Fourfold.LocalEtaleDatum`). If
`g : Y' ⟶ Y_e` is a projective small birational morphism, then `Y'` is terminal.

Since `q` is étale, `K_{Y_e} = q^* K_Y` is `ℚ`-Cartier and `Y_e` is terminal; since `g` is small,
`K_{Y'} = g^* K_{Y_e}` (`MMP.Fourfold.IsSmallMorphism.exists_isCanonicalDivisor_eq_pullback`), so
log discrepancies over `Y'` and over `Y_e` agree. A valuation exceptional over `Y'` has centre of
codimension at least two on `Y_e`, as `g` contracts no divisor, so its log discrepancy exceeds one.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.isTerminalVariety_of_isSmallMorphism`: `Y'` is terminal.

## Implementation notes

`Y'` lies over `ℂ` through `g ≫ q ≫ s_Y`, and terminality is
`MMP.Fourfold.IsTerminalVariety`, which includes that `K_{Y'}` is `ℚ`-Cartier. The instance
hypotheses on `Y'` (integral, locally noetherian, normal) are needed to state terminality; they
follow from `MMP.Fourfold.IsSmallMorphism`. Projectivity of `g` is part of the statement but is
not used: the argument works for any small morphism to a terminal variety.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.30
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Fourfold.LocalEtaleDatum

open MMP.Mori

section Small

variable {k : Type u} [Field k] {X Y' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {sX : X ⟶ Spec (.of k)}

/-- A morphism is a local isomorphism at every point mapping into its biregular locus. -/
private theorem isIso_stalkMap_of_mem_biregularLocus (g : Y' ⟶ X) {x : Y'}
    (hx : g x ∈ biregularLocus g) : IsIso (g.stalkMap x) := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have : IsOpenImmersion ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) := by
    rw [← morphismRestrict_ι g (biregularLocus g)]
    infer_instance
  let x' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨x, hx⟩
  have h := IsOpenImmersion.instIsIsoCommRingCatStalkMap ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) x'
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap _) _
    (IsOpenImmersion.instIsIsoCommRingCatStalkMap (g ⁻¹ᵁ biregularLocus g).ι x') h

/-- **A small morphism is crepant for the empty boundary.** If `g : Y' ⟶ X` is small and `(X, 0)`
is a pair, the crepant boundary of `(X, 0)` on `Y'` is `0`. -/
private theorem isCrepantBoundary_zero [IsAlgClosed k] [CharZero k] {n : ℕ} {K : Divisor X}
    (hPw : IsPairWith sX n K 0) {g : Y' ⟶ X} (hg : IsSmallMorphism (g ≫ sX) sX g) :
    IsCrepantBoundary sX n K 0 g hg.isNormalVariety_source hg.isBirationalMorphism 0 := by
  intro F
  have hX := hg.isNormalVariety_target
  haveI : IsDominant g := hg.isBirationalMorphism.isDominant
  have hx : g F.genericPoint ∈ biregularLocus g := by
    by_contra hx
    simpa [F.coheight_genericPoint] using
      MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension F.genericPoint hx
  have hc : Order.coheight (g F.genericPoint) = 1 :=
    (MMP.Positivity.coheight_map_of_mem_biregularLocus g hx).trans F.coheight_genericPoint
  set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hgP : g F.genericPoint = P.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have := isIso_stalkMap_of_mem_biregularLocus g hx
  set D : DivisorOver k sX :=
    ⟨Y', g, hg.isNormalVariety_source, hg.isBirationalMorphism, F⟩
  have hv : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
    ext t
    change F.divisorialValuation (functionFieldMap g t) =
      P.divisorialValuation (functionFieldMap (𝟙 X) t)
    rw [functionFieldMap_id_apply]
    by_cases ht : t = 0
    · simp [ht]
    rw [F.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr ht),
      P.divisorialValuation_eq_exp_neg_ord ht,
      MMP.Positivity.ord_functionFieldMap_of_isIso g F P hgP]
  obtain ⟨c, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPw.isPair hPw.2.1 D
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPw.isPair hPw.2.1
    (DivisorOver.ofPrimeDivisor k hX P)
  have hcc := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw hv hcD hc'
  rw [hcc, IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc'] at hcD
  simpa using hcD

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {s : X ⟶ Spec (.of k)} (hs : IsSeparated s) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

omit [IsIntegral X] in
/-- A divisor `(W, f, E)` over a separated normal scheme `X` is exceptional if and only if
`f(η_E)` has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight [IsSeparated (X ↘ Limits.terminal Scheme)]
    (D : DivisorOver k sX) : D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hc : ((Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) : Closeds X) : Set X) =
      closure {D.f D.E.genericPoint} :=
    D.center_eq_closure_genericPoint
  rw [hc]
  exact ⟨fun h => h _ (subset_closure rfl),
    fun h x hx => h.trans (Order.coheight_anti (specializes_iff_mem_closure.mpr hx))⟩

/-- A small morphism does not lower coheight below two. -/
private theorem two_le_coheight_map_of_isSmallMorphism {g : Y' ⟶ X}
    (hg : IsSmallMorphism (g ≫ sX) sX g) {y : Y'} (hy : 2 ≤ Order.coheight y) :
    2 ≤ Order.coheight (g y) := by
  haveI := hg.isProper
  haveI := hg.isNormalVariety_target.1
  haveI := hg.isNormalVariety_source.1
  by_cases hx : g y ∈ biregularLocus g
  · rwa [MMP.Positivity.coheight_map_of_mem_biregularLocus g hx]
  · exact MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
      (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX g hg.isBirationalMorphism) _ hx

/-- **Log discrepancies over a small model.** Let `g : Y' ⟶ X` be a small morphism and `(X, 0)` a
pair. Then `(Y', 0)` is a pair, and every log discrepancy `a = a(D; Y', 0)` of a divisor `D` over
`Y'` is a log discrepancy `a(D'; X, 0)` of a divisor `D'` over `X` (namely `D` through `g`),
exceptional over `X` when `D` is exceptional over `Y'`. -/
private theorem isPair_and_exists_isLogDiscrepancy [IsAlgClosed k] [CharZero k]
    (hP : MMP.Mori.IsPair sX 0) {g : Y' ⟶ X} (hg : IsSmallMorphism (g ≫ sX) sX g) :
    MMP.Mori.IsPair (g ≫ sX) 0 ∧ ∀ (n : ℕ) (D : DivisorOver k (g ≫ sX)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (g ≫ sX) n (QDivisor.toRDivisor 0) D a →
      ∃ (n₀ : ℕ) (D' : DivisorOver k sX),
        MMP.Intersection.IsLogDiscrepancy sX n₀ (QDivisor.toRDivisor 0) D' a ∧
          (D.IsExceptional → D'.IsExceptional) := by
  have hX := hg.isNormalVariety_target
  have hY' := hg.isNormalVariety_source
  have hgb := hg.isBirationalMorphism
  haveI := hg.isProper
  haveI : IsDominant g := hgb.isDominant
  haveI : CompactSpace Y' := by
    have := hY'.1
    exact QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  obtain ⟨-, n₀, K, hK, hKq⟩ := id hP
  rw [add_zero] at hKq
  have hPw : IsPairWith sX n₀ K 0 := ⟨hX, hK, by rwa [add_zero]⟩
  obtain ⟨K', hK', -⟩ := hg.exists_isCanonicalDivisor_eq_pullback hK hKq
  obtain ⟨hPY, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP g hY' hgb hK hK'
    (Or.inl (isCrepantBoundary_zero hPw hg))
  refine ⟨hPY, fun n D a ha => ?_⟩
  obtain rfl : n = n₀ := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK'.topologicalKrullDim_eq
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsProper D.f := ha.2.1
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hK' D
  let D' : DivisorOver k sX :=
    { Y := D.Y
      f := D.f ≫ g
      isNormalVariety := by
        rw [Category.assoc]
        exact D.isNormalVariety
      isBirationalMorphism := IsPair.isBirationalMorphism_comp D.isBirationalMorphism hgb
      E := D.E }
  haveI : IsDominant (D.f ≫ g) := D'.isDominant
  have hv : D'.valuation = D.valuation.comap (functionFieldMap g) := by
    ext t
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
      D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  refine ⟨n, D', ?_, fun hD => ?_⟩
  · rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
    exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
      ((hiff D D' hv c).1 hc) inferInstance
  · have := isSeparated_toTerminal hX.1.toIsSeparated
    have := isSeparated_toTerminal hY'.1.toIsSeparated
    rw [isExceptional_iff_two_le_coheight] at hD ⊢
    exact two_le_coheight_map_of_isSmallMorphism hg hD

/-- **A small model of a terminal variety is terminal.** If `X` is terminal over an algebraically
closed field of characteristic zero and `g : Y' ⟶ X` is small, then `Y'` is terminal. -/
private theorem isTerminalVariety_comp_of_isSmallMorphism [IsAlgClosed k] [CharZero k]
    (hT : IsTerminalVariety sX) {g : Y' ⟶ X} (hg : IsSmallMorphism (g ≫ sX) sX g) :
    IsTerminalVariety (g ≫ sX) := by
  obtain ⟨⟨hPF, hklt⟩, hterm⟩ := hT
  obtain ⟨hPY, hD⟩ := isPair_and_exists_isLogDiscrepancy hPF.isPair hg
  refine ⟨⟨⟨hPF.isAlgClosed, hPF.charZero, hPY, fun _ => le_rfl⟩, fun n D a ha => ?_⟩,
    fun n D a hex ha => ?_⟩
  · obtain ⟨n₀, D', ha', -⟩ := hD n D a ha
    exact hklt n₀ D' a ha'
  · obtain ⟨n₀, D', ha', hex'⟩ := hD n D a ha
    exact hterm n₀ D' a (hex' hex) ha'

end Small

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- For a local étale datum `(Y_e, q, η', L̃)` of a local setting, the source `Y'` of a projective
small birational morphism `g : Y' ⟶ Y_e` is a terminal variety. -/
@[mmp "lem_oai4_c2_small_model_terminal"]
public theorem isTerminalVariety_of_isSmallMorphism
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] (g : Y' ⟶ E.scheme)
    (hg : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g) (hgp : IsProjectiveMorphism g) :
    IsTerminalVariety (g ≫ E.map ≫ sY) := by
  have hX := hg.isNormalVariety_target
  haveI : IsIntegral E.scheme := hX.1.toIsIntegral
  haveI : IsNormal E.scheme := hX.2
  haveI : LocallyOfFiniteType (E.map ≫ sY) := hX.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  exact isTerminalVariety_comp_of_isSmallMorphism
    (exists_isCanonicalDivisor_isPullback_and_isTerminalVariety hY E).2 hg

end MMP.Fourfold.LocalEtaleDatum

end
