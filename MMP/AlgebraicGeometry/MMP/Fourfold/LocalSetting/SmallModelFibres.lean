module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoWeightedMonomialValuation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo

/-!
# Shrinking a small model around the curve

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and
`(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum (`MMP.Fourfold.LocalEtaleDatum`), with
`T' = closure {η'}`. Let `g : Y' ⟶ Y_e` be a projective small birational morphism. Then there is an
open neighbourhood `Y_e^1` of `η'` such that the singular locus of `Y_e^1` lies in `T'`, `g` is an
isomorphism over `Y_e^1 ∖ T'`, and every fibre of `g` over `Y_e^1` has dimension at most one.

Since `q` is étale, `Sing Y_e = q⁻¹(Sing Y)` has dimension at most one, so removing its
components other than `T'` gives the first property; the second follows from
`MMP.Fourfold.isBiregular_smoothLocus_of_isSmallMorphism`; and smallness bounds the dimension
of the generic fibre over `T'`, so upper semicontinuity of fibre dimension gives the third.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.exists_isBiregular_compl_curve_of_isSmallMorphism`: the
  neighbourhood `Y_e^1`.

## Implementation notes

`Sing(Y_e^1)` is `Y_e^1 ∩ Sing(Y_e)`, the smooth locus being local. The dimension of the fibre
`g⁻¹(y)` is the Krull dimension of its underlying topological space, the preimage of `{y}`.
The source assumes `Y'` is `ℚ`-factorial; the argument does not use it, and it is omitted.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.SmallModelFibres

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-- The singular locus of the fourfold of a local setting has codimension at least three: `Y` is
`ℚ`-factorial, so the terminal pair `(Y, Θ)` has `ℚ`-Cartier boundary and canonical divisor. -/
private theorem three_le_closedsCodimension_singularLocus
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) :
    3 ≤ closedsCodimension (singularLocus sY) := by
  have h := hY.isKltTerminalPair
  obtain ⟨-, n, K, hK, -⟩ := h.1.1.isPair
  exact (h.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sY hY.isQFactorial Θ) hK
    (isQCartier_of_isQFactorial sY hY.isQFactorial _)).2

/-- In a local setting, `dim 𝒪_{Y, η_T} = 3`: `Y` is a fourfold and `T` a curve. -/
private theorem ringKrullDim_stalk_localSettingGenericPoint
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) :
    ringKrullDim (Y.presheaf.stalk (localSettingGenericPoint T)) = 3 := by
  have hYv := hY.isProjectiveVariety
  have h1 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk ℂ Y sY (localSettingGenericPoint T)
  have h2 := topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible ℂ Y sY
    (localSettingGenericPoint T)
  have h3 := topologicalKrullDim_closure_singleton_eq_trdeg ℂ Y sY (localSettingGenericPoint T)
  rw [(isGenericPoint_localSettingGenericPoint T).def, hY.topologicalKrullDim_curve] at h3
  rw [← h2, hY.topologicalKrullDim_eq, ← h3] at h1
  generalize ringKrullDim (Y.presheaf.stalk (localSettingGenericPoint T)) = D at h1
  induction D using WithBot.recBotCoe with
  | bot => simp at h1
  | coe e =>
    have h1 : (4 : ℕ∞) = 1 + e := WithBot.coe_injective h1
    obtain rfl : e = 3 := by
      induction e using ENat.recTopCoe with
      | top => simp at h1
      | coe n =>
        norm_cast at h1 ⊢
        omega
    rfl

/-- A point of `Y_e` which is singular lies over a singular point of `Y`, `q` being étale. -/
private theorem map_mem_singularLocus
    {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) {z : E.scheme} (hz : z ∈ singularLocus (E.map ≫ sY)) :
    E.map z ∈ singularLocus sY := by
  rw [mem_singularLocus_iff] at hz ⊢
  intro h
  apply hz
  obtain ⟨U, hU, hsm⟩ := mem_smoothLocus_iff.mp h
  refine mem_smoothLocus_iff.mpr ⟨E.map ⁻¹ᵁ U, hU, ?_⟩
  rw [show (E.map ⁻¹ᵁ U).ι ≫ E.map ≫ sY = morphismRestrict E.map U ≫ U.ι ≫ sY by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]]
  infer_instance

/-- Every singular point of `Y_e` has coheight at least three, `q` being étale. -/
private theorem three_le_coheight_of_mem_singularLocus
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) [IsLocallyNoetherian E.scheme] {z : E.scheme}
    (hz : z ∈ singularLocus (E.map ≫ sY)) : 3 ≤ Order.coheight z := by
  have hcod := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (three_le_closedsCodimension_singularLocus hY) _ (map_mem_singularLocus E hz)
  have he : (Order.coheight z : WithBot ℕ∞) = Order.coheight (E.map z) := by
    rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight,
      ringKrullDim_stalk_eq_of_etale E.map z]
  exact hcod.trans (WithBot.coe_le_coe.mp he.ge)

/-- The point `η'` of `Y_e` has coheight three. -/
private theorem coheight_point_eq_three
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) [IsLocallyNoetherian E.scheme] :
    Order.coheight E.point = 3 := WithBot.coe_injective <| by
  rw [← ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_of_etale E.map E.point,
    E.map_point, ringKrullDim_stalk_localSettingGenericPoint hY]
  rfl

/-- The singular locus of `Y_e` near `η'` lies on `T'`. -/
private theorem exists_singularLocus_subset_curve
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) :
    ∃ U : E.scheme.Opens, E.point ∈ U ∧
      (U : Set E.scheme) ∩ singularLocus (E.map ≫ sY) ⊆ E.curve := by
  have hq := E.isQuasiProjectiveVariety
  have : LocallyOfFiniteType (E.map ≫ sY) := hq.toLocallyOfFiniteType
  have : QuasiCompact (E.map ≫ sY) := hq.toQuasiCompact
  have : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  have : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
  have : IsNoetherian E.scheme := {}
  obtain ⟨S, hirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible (singularLocus (E.map ≫ sY))
  classical
  let S' : Finset (TopologicalSpace.Closeds E.scheme) :=
    S.filter (fun k : TopologicalSpace.Closeds E.scheme => E.point ∉ k)
  let C : Set E.scheme := ⋃ (k : TopologicalSpace.Closeds E.scheme) (_ : k ∈ S'), (k : Set E.scheme)
  refine ⟨⟨Cᶜ, (S'.finite_toSet.isClosed_biUnion fun k _ => k.isClosed).isOpen_compl⟩, ?_, ?_⟩
  · change E.point ∉ C
    intro hpC
    obtain ⟨k, hk, hpk⟩ := Set.mem_iUnion₂.mp hpC
    exact (Finset.mem_filter.mp hk).2 hpk
  · rintro z ⟨hzU, hzS⟩
    have hzS' : z ∈ ((S.sup id : TopologicalSpace.Closeds E.scheme) : Set E.scheme) := by
      rwa [← hS]
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
      Set.mem_iUnion₂] at hzS'
    obtain ⟨k, hkS, hzk⟩ := hzS'
    by_cases hk : E.point ∈ (k : Set E.scheme)
    · obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hirr ⟨k, hkS⟩) k.isClosed
      have hζS : ζ ∈ singularLocus (E.map ≫ sY) := by
        change ζ ∈ ((singularLocus (E.map ≫ sY) : TopologicalSpace.Closeds E.scheme) : Set E.scheme)
        rw [hS, TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
        exact Set.mem_biUnion hkS hζ.mem
      have hζpt : ζ = E.point := by
        by_contra hne
        have hspec : ζ ⤳ E.point := hζ.specializes hk
        have hlt : E.point < ζ := lt_of_le_not_ge hspec fun h => hne (hspec.antisymm h).eq
        have h := (add_le_add (three_le_coheight_of_mem_singularLocus hY E hζS) le_rfl).trans
          (Order.coheight_add_one_le hlt)
        rw [coheight_point_eq_three hY E] at h
        exact absurd h (by decide)
      rw [hζpt] at hζ
      have : (k : Set E.scheme) = E.curve := by
        rw [E.coe_curve, ← hζ.def]
      exact this ▸ hzk
    · exact absurd (Set.mem_biUnion (x := k) (Finset.mem_filter.mpr ⟨hkS, hk⟩) hzk) hzU

/-- In `WithBot ℕ∞`, being less than two is being at most one. -/
private lemma lt_two_iff_le_one (d : WithBot ℕ∞) : d < 2 ↔ d ≤ 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact iff_of_true (WithBot.bot_lt_coe 2) bot_le
  | coe d =>
    exact WithBot.coe_lt_coe.trans <|
      (ENat.lt_add_one_iff ENat.one_ne_top).trans WithBot.coe_le_coe.symm

/-- The residue field of a fibre at the point through `x` has the same transcendence degree over
`κ(f x)` as `κ(x)`. -/
private lemma toENat_trdeg_residueField_asFiber_eq {X S : Scheme.{0}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg (S.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x))) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
        WithBot ℕ∞) := by
  let : Algebra (S.residueField (f x)) ((f.fiber (f x)).residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of (S.residueField (f x)))).inv ≫
      (f.fiberToSpecResidueField (f x)).appTop ≫
      (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f (f x)
  have h1 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk (S.residueField (f x))
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  have h2 := topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg f x
  exact add_right_cancel_of_ne_top_of_ne_bot
    (c := ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ringKrullDim_ne_top
    (ringKrullDim_eq_bot_iff_subsingleton.not.mpr (not_subsingleton _))
    (h1.symm.trans (h2.trans (add_comm _ _)))

/-- The fibre of `f` over `s` has dimension less than `n` exactly when every point `x` over `s`
has `trdeg_{κ(s)} κ(x) < n`. -/
private lemma topologicalKrullDim_fiber_lt_iff {X S : Scheme.{0}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (n : ℕ) :
    topologicalKrullDim (f.fiber s) < (n : WithBot ℕ∞) ↔
      ∀ x : X, f x = s →
        (Cardinal.toENat (@Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _
          (f.residueFieldMap x).hom.toAlgebra) : WithBot ℕ∞) < (n : WithBot ℕ∞) := by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · subst hx
    exact toENat_trdeg_lt_of_topologicalKrullDim_fiber_lt f x n h
  · have hu : topologicalKrullDim ↥(Set.univ : Set (f.fiber s)) = topologicalKrullDim (f.fiber s) :=
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    rw [← hu, topologicalKrullDim_lt_iff_forall_toENat_trdeg_lt (S.residueField s) (f.fiber s)
      (f.fiberToSpecResidueField s) isClosed_univ n]
    intro y _
    have hsy : f (f.fiberι s y) = s := by
      simpa [Scheme.Hom.comp_apply] using congrArg (fun q : f.fiber s ⟶ S ↦ q y) (f.fiber_fac s)
    have key := h _ hsy
    generalize hx : f.fiberι s y = x at hsy key
    subst hsy
    have hy : y = f.asFiber x :=
      (f.fiberι (f x)).isEmbedding.injective (by rw [hx, f.fiberι_asFiber])
    subst hy
    rwa [toENat_trdeg_residueField_asFiber_eq f x]

/-- A birational morphism induces an algebraic residue field extension at each generic point of
its source. -/
private lemma toENat_trdeg_residueField_genericPoint_eq_zero {X S : Scheme.{0}} {f : X ⟶ S}
    (hf : IsBirational f) {η : X} (hη : η ∈ genericPoints X) :
    Cardinal.toENat (@Algebra.trdeg (S.residueField (f η)) (X.residueField η) _ _
      (f.residueFieldMap η).hom.toAlgebra) = 0 := by
  let : Algebra (S.residueField (f η)) (X.residueField η) := (f.residueFieldMap η).hom.toAlgebra
  have : IsIso (f.stalkMap η) := hf.2 η hη
  have hsurj : Function.Surjective (f.residueFieldMap η) := by
    intro z
    obtain ⟨a, rfl⟩ := X.residue_surjective η z
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap η)).2 a
    exact ⟨S.residue (f η) b, by
      simpa using congrArg (fun φ => φ b) (Scheme.residue_residueFieldMap f η)⟩
  have : Algebra.IsIntegral (S.residueField (f η)) (X.residueField η) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hsurj
  rw [trdeg_eq_zero]
  simp

/-- Over `η'`, every point `x` of `Y'` has `trdeg_{κ(η')} κ(x) < 2`: otherwise the closure of `x`
would be a subset of the exceptional locus of codimension at most one. -/
private theorem toENat_trdeg_lt_two_of_map_eq_point
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} (g : Y' ⟶ E.scheme)
    (hg : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g) (x : Y') (hx : g x = E.point) :
    (Cardinal.toENat (@Algebra.trdeg (E.scheme.residueField (g x)) (Y'.residueField x) _ _
      (g.residueFieldMap x).hom.toAlgebra) : WithBot ℕ∞) < ((2 : ℕ) : WithBot ℕ∞) := by
  have hV' := hg.isNormalVariety_source.1
  have hV := hg.isNormalVariety_target.1
  have := hV'.toIsIntegral
  have := hV.toIsIntegral
  have := hg.isNormalVariety_target.2
  have := hg.isProper
  have : LocallyOfFiniteType (g ≫ E.map ≫ sY) := hV'.toLocallyOfFiniteType
  have : LocallyOfFiniteType (E.map ≫ sY) := hV.toLocallyOfFiniteType
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (E.map ≫ sY)
  have : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  let : Algebra (E.scheme.residueField (g x)) (Y'.residueField x) :=
    (g.residueFieldMap x).hom.toAlgebra
  by_contra! hlt
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg.isBirationalMorphism
  have hform := ringKrullDim_stalk_add_trdeg_le_of_forall_genericPoints g x 0
    (fun η hη _ => (toENat_trdeg_residueField_genericPoint_eq_zero hb hη).le)
  have hD : ringKrullDim (Y.presheaf.stalk (E.map (g x))) =
      ringKrullDim (Y.presheaf.stalk (localSettingGenericPoint T)) := by
    rw [hx, E.map_point]
  rw [ringKrullDim_stalk_eq_of_etale E.map (g x), hD, ringKrullDim_stalk_eq_coheight x,
    ringKrullDim_stalk_localSettingGenericPoint hY] at hform
  have hexc := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hV' hV g
    hg.comp_eq hb).2.1
  have hxexc : x ∈ (MMP.Mori.exceptionalSet g : Set Y') := by
    rw [hexc]
    change 0 < topologicalKrullDim ↥(g ⁻¹' {g x})
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo (g x)).isHomeomorph]
    by_contra! h0
    have := toENat_trdeg_lt_of_topologicalKrullDim_fiber_lt g x 1
      (h0.trans_lt (by exact_mod_cast zero_lt_one))
    exact absurd (hlt.trans_lt this) (by norm_num)
  have hcod := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension x hxexc
  have hform : Order.coheight x + Cardinal.toENat (Algebra.trdeg (E.scheme.residueField (g x))
      (Y'.residueField x)) ≤ 3 := WithBot.coe_le_coe.mp (by simpa using hform)
  exact absurd ((add_le_add hcod (WithBot.coe_le_coe.mp hlt)).trans hform) (by decide)

/-- The fibres of `g` near `η'` have dimension at most one. -/
private theorem exists_fibre_dim_le_one
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} (g : Y' ⟶ E.scheme)
    (hg : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g) :
    ∃ U : E.scheme.Opens, E.point ∈ U ∧ ∀ y ∈ U, topologicalKrullDim (g.base ⁻¹' {y}) ≤ 1 := by
  have hV' := hg.isNormalVariety_source.1
  have := hg.isProper
  have : LocallyOfFiniteType (g ≫ E.map ≫ sY) := hV'.toLocallyOfFiniteType
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (E.map ≫ sY)
  let B : Set Y' :=
    {x | topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) ≤ ((1 : ℕ) : WithBot ℕ∞)}ᶜ
  refine ⟨⟨(g '' B)ᶜ,
    (g.isClosedMap B (isOpen_setOf_fiberDimensionAt_le g 1).isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hxB, hx⟩
    apply hxB
    have hlt : topologicalKrullDim (g.fiber (g x)) < ((2 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_fiber_lt_iff g (g x) 2).2 fun x' hx' =>
        toENat_trdeg_lt_two_of_map_eq_point hY E g hg x' (hx'.trans hx)
    have hle := (lt_two_iff_le_one _).1 (by exact_mod_cast hlt)
    exact (_root_.topologicalKrullDimAt_le_topologicalKrullDim _).trans (by exact_mod_cast hle)
  · intro y hy
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo y).isHomeomorph]
    have hlt : topologicalKrullDim (g.fiber y) < ((2 : ℕ) : WithBot ℕ∞) := by
      refine (topologicalKrullDim_fiber_lt_iff g y 2).2 fun x hx => ?_
      have hloc : topologicalKrullDimAt (g.fiber (g x)) (g.asFiber x) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
        not_not.mp fun hxB => hy ⟨x, hxB, hx⟩
      rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg g x] at hloc
      have h0 : (0 : WithBot ℕ∞) ≤
          ringKrullDim ((g.fiber (g x)).presheaf.stalk (g.asFiber x)) := Order.krullDim_nonneg
      exact ((le_add_of_nonneg_left h0).trans hloc).trans_lt
        (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
    exact (lt_two_iff_le_one _).1 (by exact_mod_cast hlt)

end MMP.Fourfold.SmallModelFibres

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.LocalEtaleDatum

open MMP.Mori MMP.Fourfold MMP.Fourfold.SmallModelFibres

/-- For a local étale datum `(Y_e, q, η', L̃)` of a local setting and a projective small
birational morphism `g : Y' ⟶ Y_e`, there is an open neighbourhood `U` of `η'` whose singular
points lie on `T'`, over whose complement of `T'` the morphism `g` is an isomorphism, and over
which every fibre of `g` has dimension at most one. -/
@[mmp "lem_oai4_c2_small_model_fibres"]
theorem exists_isBiregular_compl_curve_of_isSmallMorphism
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ}
    {L : Fin b → (pointSettingFibre π (localSettingGenericPoint T)).Modules}
    (E : LocalEtaleDatum sY T π L) {Y' : Scheme.{0}} (g : Y' ⟶ E.scheme)
    (hg : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g) (hgp : IsProjectiveMorphism g) :
    ∃ U : E.scheme.Opens, E.point ∈ U ∧
      (U : Set E.scheme) ∩ singularLocus (E.map ≫ sY) ⊆ E.curve ∧
      IsBiregular g (U ⊓ ⟨(E.curve : Set E.scheme)ᶜ, E.curve.isClosed.isOpen_compl⟩) ∧
      ∀ y ∈ U, topologicalKrullDim (g.base ⁻¹' {y}) ≤ 1 := by
  obtain ⟨U₁, hU₁, hsing⟩ := exists_singularLocus_subset_curve hY E
  obtain ⟨U₂, hU₂, hfib⟩ := exists_fibre_dim_le_one hY E g hg
  have hsm := isBiregular_smoothLocus_of_isSmallMorphism _ _ g hg hgp
  refine ⟨U₁ ⊓ U₂, ⟨hU₁, hU₂⟩, fun y hy => hsing ⟨hy.1.1, hy.2⟩, ?_,
    fun y hy => hfib y hy.2⟩
  refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hsm))
  rintro y ⟨hy, hyT⟩
  by_contra h
  exact hyT (hsing ⟨hy.1, h⟩)

end MMP.Fourfold.LocalEtaleDatum
