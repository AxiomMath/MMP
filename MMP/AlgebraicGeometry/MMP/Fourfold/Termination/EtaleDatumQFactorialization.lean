module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.Extraction.QuasiProjective
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Small `ℚ`-factorialization of a local étale datum

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and
`(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum (`MMP.Fourfold.LocalEtaleDatum`). Then `Y_e`
admits a small `ℚ`-factorialization: a projective small birational morphism `g : Y' ⟶ Y_e` with
`Y'` a `ℚ`-factorial variety.

Since `q` is étale, `Y_e` is terminal, so `(Y_e, 0)` is a klt pair on a quasi-projective
variety; extracting the empty set of valuations gives the small `ℚ`-factorialization.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.exists_isSmallMorphism_isQFactorial`: the small
  `ℚ`-factorialization `g : Y' ⟶ Y_e`.

## Implementation notes

* `Y'` lies over `ℂ` through `g ≫ q ≫ s_Y`. A small birational morphism is
  `MMP.Fourfold.IsSmallMorphism` (proper, birational, normal varieties, exceptional locus of
  codimension at least two), and projectivity is `AlgebraicGeometry.IsProjectiveMorphism`.
* The instances on `Y'` (integral, locally Noetherian, normal), needed to speak of its Weil
  divisors in `MMP.Fourfold.IsQFactorial`, are part of the conclusion.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_oai4_c2_small_q_factorialization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)}

/-- Over a point of codimension one of `Z` lies at most one point of codimension one of `X`, for
a birational morphism `f : X ⟶ Z` of normal varieties. -/
private theorem eq_of_coheight_eq_one {f : X ⟶ Z} (hX : IsNormalVariety k (f ≫ sZ))
    (hZ : IsNormalVariety k sZ) (hf : IsBirationalMorphism f) {x₁ x₂ : X}
    (h₁ : Order.coheight x₁ = 1) (h₂ : Order.coheight x₂ = 1) (he : f x₁ = f x₂)
    (hy : Order.coheight (f x₂) = 1) : x₁ = x₂ := by
  haveI := hf.isDominant
  let P₁ : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₁ h₁
  let P₂ : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x₂ h₂
  let Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (f x₂) hy
  let D₁ : MMP.Mori.DivisorOver k sZ := ⟨X, f, hX, hf, P₁⟩
  let D₂ : MMP.Mori.DivisorOver k sZ := ⟨X, f, hX, hf, P₂⟩
  have hv₁ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hZ D₁ Q (by
    simp [D₁, P₁, Q, MMP.Mori.PrimeDivisor.genericPoint,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, he])
  have hv₂ := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hZ D₂ Q (by
    simp [D₂, P₂, Q, MMP.Mori.PrimeDivisor.genericPoint,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne])
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hf
  let F₁ := MMP.Mori.DivisorOver.ofPrimeDivisor k hX P₁
  let F₂ := MMP.Mori.DivisorOver.ofPrimeDivisor k hX P₂
  have hF : F₁.valuation = F₂.valuation := by
    ext g
    obtain ⟨g', rfl⟩ := hbij.2 g
    have := DFunLike.congr_fun (hv₁.trans hv₂.symm) g'
    change P₁.divisorialValuation (functionFieldMap (𝟙 X) (functionFieldMap f g')) =
      P₂.divisorialValuation (functionFieldMap (𝟙 X) (functionFieldMap f g'))
    rw [MMP.Mori.functionFieldMap_id_apply]
    exact this
  have h' : P₁.genericPoint = P₂.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hF
  simpa [F₁, F₂, P₁, P₂, MMP.Mori.PrimeDivisor.genericPoint,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] using h'

/-- A point of coheight at most one whose image under a dominant morphism is not the generic
point has coheight exactly one: a point of coheight zero is the generic point. -/
private theorem coheight_eq_one_of_map_ne_genericPoint (f : X ⟶ Z) [IsDominant f] {p : X}
    (hp : Order.coheight p ≤ 1) (hpg : f p ≠ genericPoint Z) : Order.coheight p = 1 := by
  refine le_antisymm hp (ENat.one_le_iff_ne_zero.mpr fun h0 => hpg ?_)
  rw [(Specializes.antisymm (Order.coheight_eq_zero.mp h0 (genericPoint_specializes p))
    (genericPoint_specializes p)).eq]
  exact MMP.Positivity.map_genericPoint_eq_of_isDominant f

/-- Codimension can only drop along a birational morphism of varieties. -/
private theorem coheight_le_coheight_map {f : X ⟶ Z} (hX : MMP.Mori.IsVariety k (f ≫ sZ))
    (hZ : MMP.Mori.IsVariety k sZ) (hf : IsBirationalMorphism f) (p : X) :
    Order.coheight p ≤ Order.coheight (f p) :=
  MMP.Flips.coheight_le_coheight_map sZ (f ≫ sZ) hZ hX f rfl
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (f ≫ sZ) hf).symm p

/-- A point `x` of codimension one of `X` whose prime divisor is not exceptional for a
birational morphism `f : X ⟶ Z` of normal varieties maps to a point of codimension one. -/
private theorem coheight_map_eq_one {f : X ⟶ Z} (hX : IsNormalVariety k (f ≫ sZ))
    (hZ : IsNormalVariety k sZ) (hf : IsBirationalMorphism f) {x : X}
    (hx : Order.coheight x = 1)
    (hex : ¬ RationalMap.IsExceptional (X := X) f.toRationalMap
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx)) :
    Order.coheight (f x) = 1 := by
  haveI := hf.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  refine le_antisymm (not_lt.mp fun hlt => hex ?_)
    (hx ▸ coheight_le_coheight_map hX.1 hZ.1 hf x)
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro y hy
  have hsub : f '' ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx).idealSheaf.support :
      Set X) ⊆ closure {f x} := by
    change f '' (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx).support ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, ← Set.image_singleton]
    exact image_closure_subset_closure_image f.continuous
  rw [TopologicalSpace.Closeds.coe_closure] at hy
  have hsp : f x ⤳ y := specializes_iff_mem_closure.mpr (closure_minimal hsub isClosed_closure hy)
  exact (Order.add_one_le_of_lt hlt).trans (by
    simpa [one_add_one_eq_two] using Order.coheight_anti (show y ≤ f x from hsp))

/-- A proper birational morphism of normal varieties with no exceptional prime divisor has
exceptional set of codimension at least two. -/
private theorem two_le_closedsCodimension_exceptionalSet {f : X ⟶ Z} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sZ)) (hZ : IsNormalVariety k sZ) (hf : IsBirationalMorphism f)
    (hex : ∀ P : MMP.Mori.PrimeDivisor X, ¬ RationalMap.IsExceptional (X := X) f.toRationalMap P) :
    2 ≤ closedsCodimension (exceptionalSet f) := by
  haveI := hf.isDominant
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf
  have hfin : ∀ y : Z, (f ⁻¹' {y}).Finite → y ∈ biregularLocus f := fun y hy =>
    le_biregularLocus
      ((MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1 inferInstance).2 hy
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hxE
  by_contra hx2
  have hgen : f x ≠ genericPoint Z := fun hg => mem_exceptionalSet.mp hxE
    (hfin _ (by rw [hg, preimage_genericPoint f hb]; exact Set.finite_singleton _))
  have hx1 : Order.coheight x = 1 := coheight_eq_one_of_map_ne_genericPoint f
    (Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using not_le.mp hx2)) hgen
  have hy1 := coheight_map_eq_one hX hZ hf hx1 (hex _)
  refine mem_exceptionalSet.mp hxE (hfin _ ((Set.finite_singleton x).subset fun p hp => ?_))
  have hp : f p = f x := hp
  have hp1 : Order.coheight p = 1 := coheight_eq_one_of_map_ne_genericPoint f
    (hy1 ▸ hp ▸ coheight_le_coheight_map hX.1 hZ.1 hf p) (hp ▸ hgen)
  exact eq_of_coheight_eq_one hX hZ hf hp1 hx1 hp hy1

private theorem solution :
    ∀ {Y Yt : Scheme.{0}} [inst : IsIntegral Y] [inst_1 : IsLocallyNoetherian Y]
      [inst_2 : IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y}
      {π : Yt ⟶ Y}, IsLocalSetting sY Θ T π → ∀ {b : ℕ}
      {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
      (E : LocalEtaleDatum sY T π L),
      ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : IsLocallyNoetherian Y') (_ : IsNormal Y')
        (g : Y' ⟶ E.scheme),
        IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g ∧ IsProjectiveMorphism g ∧
          IsQFactorial (g ≫ E.map ≫ sY) := by
  intro Y Yt _ _ _ sY Θ T π hY b L E
  haveI : IsNormal E.scheme := E.isNormal
  have hYe : AlgebraicGeometry.IsVariety ℂ (E.map ≫ sY) := E.isQuasiProjectiveVariety.toIsVariety
  haveI := hYe.toIsIntegral
  haveI := hYe.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  obtain ⟨hcan, hterm⟩ :=
    LocalEtaleDatum.exists_isCanonicalDivisor_isPullback_and_isTerminalVariety hY E
  obtain ⟨⟨hΘ, -⟩, -⟩ := hY.isKltTerminalPair
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := hΘ.isPair
  obtain ⟨-, -, Ke, hKe, -, -⟩ := hcan n₀ K₀ hK₀
  have hdim : topologicalKrullDim E.scheme = 4 := by
    rw [hKe.topologicalKrullDim_eq, ← hK₀.topologicalKrullDim_eq, hY.topologicalKrullDim_eq]
  obtain ⟨V, _, _, _, q, Ed, -, -, hV, hq, hproj, -, -, hexc, -⟩ :=
    exists_specifiedExtraction_of_isQuasiProjectiveVariety (E.map ≫ sY)
      E.isQuasiProjectiveVariety hdim 0 (fun _ => le_rfl) hterm.1 ∅ (by simp) hKe
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hproj
  have hYen : IsNormalVariety ℂ (E.map ≫ sY) := ⟨hYe, inferInstance⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, q,
    ⟨hV.1, hYen, rfl, inferInstance, hq, ?_⟩, hproj, hV⟩
  refine two_le_closedsCodimension_exceptionalSet hV.1 hYen hq fun P hP => ?_
  obtain ⟨⟨s, hs⟩, -⟩ := (hexc P).mp hP
  simp at hs

end Proof_lem_oai4_c2_small_q_factorialization

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.LocalEtaleDatum

open MMP.Mori

/-- For a local étale datum `(Y_e, q, η', L̃)` of a local setting `(Y, Θ, T, π)`, there is a
projective small birational morphism `g : Y' ⟶ Y_e` with `Y'` `ℚ`-factorial. -/
@[mmp "lem_oai4_c2_small_q_factorialization"]
public theorem exists_isSmallMorphism_isQFactorial
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) :
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (_ : IsLocallyNoetherian Y') (_ : IsNormal Y')
      (g : Y' ⟶ E.scheme),
      IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g ∧ IsProjectiveMorphism g ∧
        IsQFactorial (g ≫ E.map ≫ sY) :=
          by revert Y Yt sY Θ T π hY b L E; first | exact Proof_lem_oai4_c2_small_q_factorialization.solution | exact Proof_lem_oai4_c2_small_q_factorialization.solution _ | exact Proof_lem_oai4_c2_small_q_factorialization.solution _ _ | exact Proof_lem_oai4_c2_small_q_factorialization.solution _ _ _ | exact Proof_lem_oai4_c2_small_q_factorialization.solution _ _ _ _

end MMP.Fourfold.LocalEtaleDatum

