module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Discrepancies increase exactly over the exceptional divisor of a divisorial contraction

Let `f : X ⟶ Y` be a birational contraction of normal varieties whose exceptional set `Ex(f)` is
a prime divisor `F₀`, `D_X` an `ℝ`-divisor on `X` with `K_X + D_X` `ℝ`-Cartier and
`-(K_X + D_X)` `f`-ample, and `D_Y = f_* D_X` with `K_Y + D_Y` `ℝ`-Cartier. For every divisor `B`
of `k(X)` with nonempty center on `Y`, `a(B, X, D_X) ≤ a(B, Y, D_Y)`
(`MMP.Flips.isDiscrepancy_le_of_isRelativelyNef` with `g = 𝟙`), and the inequality is strict if
and only if `Center_X(B) ⊆ F₀`. The Picard number `ρ(X/Y)` plays no role.

By `MMP.Flips.isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint`, equality holds if and only if
`K_X + D_X` is numerically trivial on the fibre over the generic point `b` of `Center_Y(B)`. If
`Center_X(B) ⊆ F₀`, every closed point of `closure {b}` has a positive-dimensional fibre, which
contains a curve on which `-(K_X + D_X)` is positive. Otherwise the fibre over `b` is the generic
point of `Center_X(B)` alone, and no curve contracted by `f` lies over the open set `Y ∖ f(F₀)`,
which contains `b`.

## Main results

* `MMP.Flips.IsBirationalContraction.isDiscrepancy_lt_iff_center_subset`.

## Implementation notes

`X` is a `k`-variety through `f ≫ s_Y`. The canonical divisors are compatible: `K_Y = div_Y(ω)`
and `K_X = div_X(f^*ω)` for one rational top form `ω` on `Y`. The divisor `B` is a valuation `v`
of `k(X)`; the same divisor of `k(Y)` is `v_Y = v ∘ f^*`. Its center on `X` is that of a proper
divisor over `X` realizing `v`, which is determined by `v`. As in `MMP.Flips.IsDiscrepancy`,
"`a` is the discrepancy" is a predicate on `a`. The source works over `ℂ`; the statement is made
over a perfect field.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.28.3.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

universe u

namespace MMP.Flips

open MMP.Mori

/-! ### Birational transforms of prime divisors -/

section InverseTransform

open TopologicalSpace Limits

variable {X Y : Scheme.{u}}

/-- A partial isomorphism representing `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A representative `g'` of the inverse of a birational morphism `f` is a section of `f` on its
domain. -/
private theorem apply_hom_eq_of_isInverse [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X]
    [IsReduced Y] [IsSeparated (X ↘ Limits.terminal Scheme)]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf)
      P = some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- A separated `k`-scheme is separated over the terminal scheme. -/
private theorem isSeparated_terminal_from {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] : IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- Let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If `f` sends
the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`, then the
strict transform of `P` under `f⁻¹` is `E`. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : MMP.Mori.RationalMap.DefinedAt (MMP.Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom (MMP.Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight,
      show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : MMP.Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

/-- The coefficient of `f⁻¹_* D` along a prime divisor `E` lying over no prime divisor of `X`
vanishes. -/
private theorem birationalInverseTransform_apply_eq_zero {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} {R : Type*} [AddCommMonoid R]
    (hX : MMP.Mori.IsVariety k sX) {f : Y ⟶ X} (hY : MMP.Mori.IsVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (D : DivisorWithCoeffs R X) {E : MMP.Mori.PrimeDivisor Y}
    (h : ∀ P : MMP.Mori.PrimeDivisor X, f E.genericPoint ≠ P.genericPoint) :
    birationalInverseTransform f hf D E = 0 := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := isSeparated_terminal_from sX
  have := isSeparated_terminal_from (f ≫ sX)
  exact mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP =>
    h P (genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP)) D

end InverseTransform

/-! ### Proper curves are not points -/

/-- A space of Krull dimension one has two distinct points. -/
private theorem not_subsingleton_of_topologicalKrullDim_eq_one {T : Type*} [TopologicalSpace T]
    (h : topologicalKrullDim T = 1) : ¬ Subsingleton T := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology T
  rw [h] at h0
  exact absurd h0 (by decide)

/-- A fibre of `f` containing a one-dimensional set `C₀` with `f '' C₀ = {y}` is not a point. -/
private theorem not_preimage_subset_singleton_of_image_eq_singleton {T S : Type*}
    [TopologicalSpace T] (f : T → S) {C₀ : Set T} (hC₀d : topologicalKrullDim C₀ = 1) {x x' : T}
    {y : S} (hx : x ∈ C₀) (hy : f '' C₀ = {y}) (hxx' : f x = f x') : ¬ f ⁻¹' {f x'} ⊆ {x} := by
  intro hs
  have hC₀ : ∀ c ∈ C₀, c = x := fun c hc => by
    have h1 : f c ∈ f '' C₀ := ⟨c, hc, rfl⟩
    have h2 : f x ∈ f '' C₀ := ⟨x, hx, rfl⟩
    rw [hy] at h1 h2
    exact hs (show f c = f x' from (h1.trans h2.symm).trans hxx')
  exact not_subsingleton_of_topologicalKrullDim_eq_one hC₀d
    ⟨fun a b => Subtype.ext ((hC₀ a a.2).trans (hC₀ b b.2).symm)⟩

/-- A proper curve has a point other than its generic point. -/
private theorem exists_mem_closure_ne_point {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    ∃ q ∈ closure ({C.point} : Set X), q ≠ C.point := by
  by_contra! h
  exact not_subsingleton_of_topologicalKrullDim_eq_one C.isProperCurve.dim_eq
    ⟨fun a b => (curveSubschemeAtι C.point).isEmbedding.injective <|
      (h _ (range_curveSubschemeAtι C.point ▸ ⟨a, rfl⟩)).trans
        (h _ (range_curveSubschemeAtι C.point ▸ ⟨b, rfl⟩)).symm⟩

/-! ### The identity of `Y` as the second model -/

/-- Discrepancies only depend on the structure morphism, not on how it is written. -/
private theorem isDiscrepancy_congr {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {s s' : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (h : s = s') {n : ℕ} {K : Divisor Y}
    {D : RDivisor Y} {v : Valuation Y.functionField ℤᵐ⁰} {a : ℝ} :
    MMP.Flips.IsDiscrepancy s n K D v a ↔ MMP.Flips.IsDiscrepancy s' n K D v a := by
  subst h; rfl

/-- The identity contracts no proper curve: a curve contracted by `𝟙` would be a point. -/
private theorem not_isContractedBy_id {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (C : ProperCurve sY) : ¬ C.IsContractedBy (𝟙 Y) := fun hC => by
  obtain ⟨q, hq, hne⟩ := exists_mem_closure_ne_point C
  exact hne (hC q hq)

/-- An `ℝ`-Cartier divisor is nef relative to the identity. -/
private theorem isRelativelyNef_id {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    {D : RDivisor Y} (hD : IsCartierCombination D) : IsRelativelyNef k sY (𝟙 Y) D := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  exact ⟨m, r, L, hL, hDL, fun C hC => (not_isContractedBy_id C hC).elim⟩

/-- An `ℝ`-Cartier divisor is numerically trivial over every point for the identity. -/
private theorem isNumericallyTrivialOverPoint_id {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    {D : RDivisor Y} (hD : IsCartierCombination D) (b : Y) :
    IsNumericallyTrivialOverPoint k sY (𝟙 Y) D b :=
  ⟨hD, ⊤, trivial, fun C hC => (not_isContractedBy_id C hC).elim⟩

/-- The birational transform under the inverse of the identity of a variety is the identity. -/
private theorem birationalInverseTransform_id {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    birationalInverseTransform (𝟙 Y) (isBirationalMorphism_of_isIso (𝟙 Y)) D = D := by
  have hY' : MMP.Mori.IsVariety k (𝟙 Y ≫ sY) := by rw [Category.id_comp]; exact hY.1
  exact Finsupp.ext fun E =>
    birationalInverseTransform_apply_of_genericPoint_eq hY (𝟙 Y) hY' _ D rfl

/-! ### The divisor `D_X` in the comparison setting -/

/-- `d + 2 ≤ e` fails when `d + 1 = e` is finite and nonempty. -/
private theorem not_add_two_le_of_add_one_eq {d e : WithBot ℕ∞} (h : d + 1 = e) (he : e ≠ ⊤)
    (he' : e ≠ ⊥) : ¬ d + 2 ≤ e := by
  induction d using WithBot.recBotCoe with
  | bot => exact fun _ => he' (by rw [← h]; rfl)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact fun _ => he (by rw [← h]; rfl)
    | coe d =>
      subst h
      have e1 : ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have e2 : ((d : ℕ∞) : WithBot ℕ∞) + 1 = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [e1, e2, WithBot.coe_le_coe, Nat.cast_le]
      omega

/-- The image of the generic point of a prime divisor exceptional over `Y` is not the generic
point of a prime divisor of `Y`. -/
private theorem map_genericPoint_ne_of_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y}
    {E : MMP.Mori.PrimeDivisor X} (hE : IsExceptionalPrimeDivisor sY f E)
    (Q : MMP.Mori.PrimeDivisor Y) : f E.genericPoint ≠ Q.genericPoint := by
  obtain ⟨_, _, _, hexc⟩ := hE
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  intro hQ
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint] at hexc
  change topologicalKrullDim (closure {f E.genericPoint} : Set Y) + 2 ≤ _ at hexc
  have h1 := topologicalKrullDim_closure_singleton_add_coheight sY (f E.genericPoint)
  rw [hQ, Q.coheight_genericPoint] at h1
  rw [hQ] at hexc
  refine not_add_two_le_of_add_one_eq (by exact_mod_cast h1)
    (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY) (fun h => ?_) hexc
  exact (Order.krullDim_eq_bot_iff.mp h).false
    (TopologicalSpace.IrreducibleCloseds.closureSingleton Q.genericPoint)

/-- The exceptional prime divisor `F₀` is exceptional over `Y`. -/
private theorem isExceptionalPrimeDivisor_of_support_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y}
    [IsProper f] (hX : IsNormalVariety k (f ≫ sY)) (hfb : IsBirationalMorphism f)
    {F₀ : MMP.Mori.PrimeDivisor X} (hF₀ : MMP.Flips.exceptionalSet f = (F₀.support : Set X)) :
    IsExceptionalPrimeDivisor sY f F₀ := by
  refine ⟨hX, hfb, inferInstance, ?_⟩
  refine (ProperDivisorOver.support_subset_exceptionalSet_iff hY _).mp ?_
  change (F₀.support : Set X) ⊆ MMP.Flips.exceptionalSet f
  exact hF₀.ge

/-- `D_X = f⁻¹_* f_* D_X + coeff_{F₀}(D_X) F₀` when `Ex(f) = F₀`. -/
private theorem birationalInverseTransform_add_single {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y}
    [IsProper f] (hX : IsNormalVariety k (f ≫ sY)) (hfb : IsBirationalMorphism f)
    {F₀ : MMP.Mori.PrimeDivisor X} (hF₀ : MMP.Flips.exceptionalSet f = (F₀.support : Set X))
    (D : RDivisor X) :
    birationalInverseTransform f hfb (MMP.Mori.RationalMap.transformDivisor f.toRationalMap D) +
      Finsupp.single F₀ (D F₀) = D := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant f := hfb.isDominant
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal_from sY
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.add_apply]
  by_cases hP : P = F₀
  · subst hP
    rw [birationalInverseTransform_apply_eq_zero hY.1 hX.1 hfb _
      (map_genericPoint_ne_of_isExceptionalPrimeDivisor hY
        (isExceptionalPrimeDivisor_of_support_eq hY hX hfb hF₀)), Finsupp.single_eq_same,
      zero_add]
  rw [Finsupp.single_eq_of_ne' (Ne.symm hP), add_zero]
  let DP : ProperDivisorOver k sY := ProperDivisorOver.mk ⟨X, f, hX, hfb, P⟩ inferInstance
  have hPne : ¬ DP.IsExceptional := by
    intro hexc
    have hsub := (ProperDivisorOver.support_subset_exceptionalSet_iff hY DP).mpr hexc
    change (P.support : Set X) ⊆ MMP.Flips.exceptionalSet f at hsub
    rw [hF₀] at hsub
    have : IsNormal X := hX.2
    have : LocallyOfFiniteType (f ≫ sY) := hX.1.toLocallyOfFiniteType
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
    refine hP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support F₀ P (hsub ?_)).symm
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨Q, -, hQ, -, -⟩ := DP.exists_primeDivisor_of_not_isExceptional hY hPne
  change f P.genericPoint = Q.genericPoint at hQ
  rw [birationalInverseTransform_apply_of_genericPoint_eq hY f hX.1 hfb _ hQ]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hQ)
    (fun P' hP' => ?_) D
  have hP'Q := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P' Q).mp hP'
  have := Q.isDiscreteValuationRing_localRing
  have hbij := hfb.functionFieldMap_bijective
  have : ValuationRing (Y.presheaf.stalk (f P.genericPoint)) := by rw [hQ]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (f P'.genericPoint)) := by rw [hP'Q]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij P.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij P'.genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap f hbij (hP'Q.trans hQ.symm)).symm

/-! ### Intersection numbers with proper curves -/

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  refine not_subsingleton_of_topologicalKrullDim_eq_one C.dim_eq ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
  obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rwa [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  have := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample Cartier divisor has positive intersection number with every proper curve
contracted by `f`. -/
private theorem pos_of_isCartierIntersectionNumber [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {L : Divisor X} (hLa : IsRelativelyAmpleCartier f L) {hL : L.IsCartier}
    {C : ProperCurve sX} (hC : C.IsContractedBy f) {d : ℤ}
    (h : IsCartierIntersectionNumber k sX C L hL d) : 0 < d := by
  rw [eq_degreeOn_of_isCartierIntersectionNumber k sX h]
  exact degreeOn_pos_of_isRelativelyAmpleCartier k sX f hLa hL C hC

/-- Every Cartier divisor has an intersection number with every proper curve. -/
private theorem exists_isCartierIntersectionNumber (k : Type u) [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (C : MMP.Mori.ProperCurve sY) (L : MMP.Mori.Divisor Y)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sY C L hL d := by
  let p := C.ι ≫ sY
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

end Curves

/-! ### Relative ampleness and curves -/

/-- An `f`-anti-ample divisor `A` has `-A` `f`-nef. -/
private theorem isRelativelyNef_neg_of_isRelativelyAntiAmple {k : Type u} [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X}
    (hA : IsRelativelyAntiAmple f A) : IsRelativelyNef k sX f (-A) := by
  obtain ⟨m, r, L, -, hr, hLa, hAL⟩ := hA
  refine ⟨m, r, L, fun j => (hLa j).1, hAL, fun C hC x hx' => ?_⟩
  obtain ⟨hL, d, -, hd, hx⟩ := hx'
  rw [hx]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le
    (by exact_mod_cast (pos_of_isCartierIntersectionNumber k sX f (hLa j) hC (hd j)).le)

/-- An `f`-anti-ample divisor has a nonzero intersection number with every proper curve
contracted by `f`. -/
private theorem exists_isRIntersectionNumber_ne_zero_of_isRelativelyAntiAmple {k : Type u}
    [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X}
    (hA : IsRelativelyAntiAmple f A) {C : ProperCurve sX} (hC : C.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (t : ℝ),
      IsRIntersectionNumber k sX A r L C t ∧ t ≠ 0 := by
  obtain ⟨m, r, L, hm, hr, hLa, hAL⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hLa j).1
  choose d hd using fun j => exists_isCartierIntersectionNumber k sX C (L j) (hLc j)
  have hApres : A = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [← neg_neg A, hAL]
    simp [neg_smul, Finset.sum_neg_distrib]
  refine ⟨m, -r, L, _, ⟨hLc, d, hApres, hd, rfl⟩, ?_⟩
  have hpos : 0 < ∑ j, r j * d j := Finset.sum_pos (fun j _ => mul_pos (hr j)
    (by exact_mod_cast pos_of_isCartierIntersectionNumber k sX f (hLa j) hC (hd j)))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_ne_zero] using hpos.ne'

/-! ### Centers -/

/-- A divisor `D` over `X` and a divisor `D'` over the separated `Y` with
`v(D) ∘ f^* = v(D')` have the same center point: `f (D.f η_E) = D'.f η_{E'}`. -/
private theorem map_genericPoint_eq_of_valuation_comap_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] (f : X ⟶ Y) [IsDominant f]
    (D : DivisorOver k sX) (D' : DivisorOver k sY)
    (hv : D.valuation.comap (functionFieldMap f) = D'.valuation) :
    f (D.f D.E.genericPoint) = D'.f D'.E.genericPoint := by
  refine MMP.Positivity.DivisorOver.eq_of_dominates sY D'.valuation (fun a => ?_) (fun a ha => ?_)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl) <;>
  rw [← hv, Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · exact MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _
      ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ a hu))

/-! ### Contracted curves in fibres -/

section ContractedCurves

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- In a Noetherian quasi-sober space, a closed connected set `F` that meets a closed set `S`
without lying in it contains a point outside `S` specializing to a point of `S`. -/
private theorem exists_specializes_of_isConnected {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] {F S : Set Y} (hF : IsClosed F)
    (hFc : IsConnected F) (hS : IsClosed S) (hmeet : (F ∩ S).Nonempty) (hsub : ¬ F ⊆ S) :
    ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
  set T := F \ S
  obtain ⟨s, hsT, hsS⟩ : (closure T ∩ S).Nonempty := by
    obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
    obtain ⟨w, -, hw⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
      isClosed_closure hS (fun a ha => (em (a ∈ S)).symm.imp
        (fun haS => subset_closure (show a ∈ T from ⟨ha, haS⟩)) id)
      ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
    exact ⟨w, hw⟩
  obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed (closure T))
  have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
    refine closure_minimal (fun y hy => ?_) ?_
    · obtain ⟨z, hz, hyz⟩ : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
      exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
    · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
  obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
  have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
  exact ⟨ζ, closure_minimal Set.sdiff_subset hF (hzT hζ.mem),
    fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS), s, hsS, hζ.specializes hsz⟩

/-- The fibre of a proper morphism `f` of `k`-schemes of finite type over a closed point is proper
over `k`. -/
private theorem isProper_fiberι_comp {k : Type u} [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : IsNormalVariety k sX) (x : X)
    (hx : IsClosed ({x} : Set X)) : IsProper (f.fiberι x ≫ f ≫ sX) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have : IsFinite (X.fromSpecResidueField x ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
  rw [Scheme.Hom.fiber_fac_assoc]
  infer_instance

/-- An injective morphism `ι : W ⟶ Y` to a separated `k`-scheme of finite type maps a proper curve
of `W` onto a proper curve of `Y`. -/
private theorem isProperCurve_of_injective {k : Type u} [Field k] {W Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    refine not_subsingleton_of_topologicalKrullDim_eq_one C.dim_eq
      ⟨fun a b => C.ι.isEmbedding.injective (hι ?_)⟩
    have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
    have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
    simpa using ha.trans hb.symm
  have hker := C.ker_comp ι
  constructor
  · have h1 := (MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ ι) hnc).topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy {k : Type u} [Field k] {X Y : Scheme}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ (Set.range C.ι ∩ S).Nonempty := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := exists_specializes_of_isConnected hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  let ι := f.fiberι x
  let sF := ι ≫ sY
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp sX f hX x hx
  have : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z; simp [← hp', hemb.injective.eq_iff]
    rw [this]; exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', -, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : ProperCurve sF := ⟨y', hy'⟩
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  let C : ProperCurve sY := ⟨ι y', isProperCurve_of_injective sY ι ι.isEmbedding.injective C'⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← hrange, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι y' ∈ closure {ι y'})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, p, ?_, hpS⟩
  rw [hrC, ← hp']
  exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

end ContractedCurves

/-! ### Fibres of a birational contraction away from its exceptional set -/

section Fibres

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- A point of the exceptional set `Ex(f)` (where `f` is not a local open immersion) lies in
`f⁻¹(Y ∖ V_f)`, the complement of the preimage of the biregular locus `V_f`. -/
private theorem mem_exceptionalSet_of_mem {f : X ⟶ Y} {x : X}
    (hx : x ∈ MMP.Flips.exceptionalSet f) : x ∈ (MMP.Mori.exceptionalSet f : Set X) := by
  by_contra h
  have : IsIso (f ∣_ MMP.Mori.biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine hx ⟨f ⁻¹ᵁ MMP.Mori.biregularLocus f,
    not_not.mp (mt MMP.Mori.mem_exceptionalSet.mpr h), ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- A proper curve none of whose points lies in `Ex(f)` is not contracted by `f`: `f` is
injective near each of its points. -/
private theorem not_isContractedBy_of_forall_notMem {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}
    (C : ProperCurve sX)
    (hC : ∀ q ∈ closure ({C.point} : Set X), q ∉ MMP.Flips.exceptionalSet f) :
    ¬ C.IsContractedBy f := by
  intro hCf
  obtain ⟨q, hq, hne⟩ := exists_mem_closure_ne_point C
  obtain ⟨V, hqV, hV⟩ := exists_isOpenImmersion_of_notMem_exceptionalSet (hC q hq)
  have hpV : C.point ∈ V := (specializes_iff_mem_closure.mpr hq).mem_open V.isOpen hqV
  exact hne (congrArg Subtype.val ((V.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨q, hqV⟩)
    (a₂ := ⟨C.point, hpV⟩) (by change f q = f C.point; exact hCf q hq)))

/-- For a birational contraction `f` and `x ∉ Ex(f)`, the fibre `f⁻¹(f x)` is `{x}`. -/
private theorem preimage_singleton_eq_of_notMem_exceptionalSet {sY : Y ⟶ Spec (.of k)}
    {f : X ⟶ Y} (hf : IsBirationalContraction k sY (f ≫ sY) f) {x : X}
    (hx : x ∉ MMP.Flips.exceptionalSet f) : f ⁻¹' {f x} = {x} := by
  have hXv := hf.isVariety_source
  have hYv := hf.isVariety_target
  obtain ⟨V, hxV, hV⟩ := exists_isOpenImmersion_of_notMem_exceptionalSet hx
  have hinj : ∀ y ∈ V, f y = f x → y = x := fun y hy h =>
    congrArg Subtype.val ((V.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨y, hy⟩) (a₂ := ⟨x, hxV⟩)
      (by change f y = f x; exact h))
  have hcoh : Order.coheight (f x) = Order.coheight x := coheight_map_of_notMem_exceptionalSet hx
  have hspec : ∀ y, x ⤳ y → f y = f x → y = x := fun y hxy hy => by
    by_contra hne
    have hlt : y < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxy) fun hge =>
      hne (hxy.antisymm (Scheme.le_iff_specializes.mp hge)).eq.symm
    letI : X.Over (Spec (.of k)) := ⟨f ≫ sY⟩
    have : LocallyOfFiniteType (X ↘ Spec (.of k)) := hXv.toLocallyOfFiniteType
    have h1 := Order.coheight_strictAnti hlt (coheight_lt_top_of_locallyOfFiniteType k x)
    have h2 := coheight_le_coheight_map sY (f ≫ sY) hYv hXv f rfl hf.dim_eq y
    rw [hy, hcoh] at h2
    exact (h1.trans_le h2).false
  have hconn := hf.toIsContraction.isConnected_preimage_singleton (f x)
  have hsplit := (isPreconnected_iff_subset_of_disjoint.mp hconn.isPreconnected) V
    (closure {x})ᶜ V.isOpen isClosed_closure.isOpen_compl (fun y hy => by
      by_cases hyc : y ∈ closure ({x} : Set X)
      · exact Or.inl (hspec y (specializes_iff_mem_closure.mpr hyc) hy ▸ hxV)
      · exact Or.inr hyc) (by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y ⟨hy, hyV, hyc⟩ => hyc ?_
      rw [hinj y hyV hy]
      exact subset_closure rfl)
  refine Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr rfl)
  rcases hsplit with h | h
  · exact hinj y (h hy) hy
  · exact absurd (subset_closure (Set.mem_singleton x)) (h (show x ∈ f ⁻¹' {f x} from rfl))

end Fibres

/-! ### Numerical triviality over the image of a point -/

/-- For a birational contraction `f` with `Ex(f) = F₀`, an `ℝ`-Cartier `A` is numerically
trivial on the fibre over `f(x)` when `x ∉ F₀`. -/
private theorem isNumericallyTrivialOverPoint_of_notMem {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    [IsProper f] [QuasiCompact (f ≫ sY)] (hf : IsBirationalContraction k sY (f ≫ sY) f)
    {F₀ : MMP.Mori.PrimeDivisor X} (hF₀ : MMP.Flips.exceptionalSet f = (F₀.support : Set X))
    {A : RDivisor X} (hAc : IsCartierCombination A) {x : X} (hxF : x ∉ F₀.support) :
    IsNumericallyTrivialOverPoint k (f ≫ sY) f A (f x) := by
  have hxE : x ∉ MMP.Flips.exceptionalSet f := hF₀ ▸ hxF
  refine ⟨hAc, ⟨(f '' F₀.support)ᶜ,
    (f.isClosedMap _ F₀.idealSheaf.support.isClosed).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨y, hyF, hy⟩
    have hyx : y ∈ f ⁻¹' {f x} := hy
    rw [preimage_singleton_eq_of_notMem_exceptionalSet hf hxE] at hyx
    exact hxF (hyx ▸ hyF)
  · intro C hCf hCU _ _ m r L t ht
    refine (not_isContractedBy_of_forall_notMem C (fun q hq hqE => hCU ?_) hCf).elim
    exact ⟨q, hF₀ ▸ hqE, hCf q hq⟩

/-- For a birational contraction `f` with `Ex(f) = F₀` and `-A` `f`-ample, `A` is numerically
trivial on the fibre over `f(x)` exactly when `x ∉ F₀`. -/
private theorem isNumericallyTrivialOverPoint_iff {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hY : IsNormalVariety k sY) {f : X ⟶ Y} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalContraction k sY (f ≫ sY) f)
    {F₀ : MMP.Mori.PrimeDivisor X} (hF₀ : MMP.Flips.exceptionalSet f = (F₀.support : Set X))
    {A : RDivisor X} (hAc : IsCartierCombination A) (hA : IsRelativelyAntiAmple f A) (x : X) :
    haveI : QuasiCompact (f ≫ sY) := hX.1.toQuasiCompact
    IsNumericallyTrivialOverPoint k (f ≫ sY) f A (f x) ↔ x ∉ F₀.support := by
  have hXv := hX.1
  have hYv := hY.1
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := hYv.toQuasiCompact
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have : LocallyOfFiniteType (f ≫ sY) := hXv.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (f ≫ sY)
  have : QuasiCompact (f ≫ sY) := hXv.toQuasiCompact
  have hfb : IsBirationalMorphism f := hf.surjective_and_isBirational.2
  have hF₀cl : IsClosed (F₀.support : Set X) := F₀.idealSheaf.support.isClosed
  refine ⟨?_, isNumericallyTrivialOverPoint_of_notMem hf hF₀ hAc⟩
  rintro ⟨-, U, hbU, hU⟩ hxF
  obtain ⟨z, ⟨hzU, hzb⟩, hzc⟩ := nonempty_inter_closedPoints
    (Z := (U : Set Y) ∩ closure {f x}) ⟨f x, hbU, subset_closure rfl⟩
    (U.isOpen.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have himg : closure {f x} ⊆ f '' closure {x} := closure_minimal
    (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩) (f.isClosedMap _ isClosed_closure)
  obtain ⟨x', hx', rfl⟩ := himg hzb
  have hx'F : x' ∈ F₀.support :=
    (hF₀cl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxF)) hx'
  have hzc' : IsClosed ({f x'} : Set Y) := hzc
  obtain ⟨x'', ⟨hx''z, hx''F⟩, hx''c⟩ := nonempty_inter_closedPoints
    (Z := f ⁻¹' {f x'} ∩ F₀.support) ⟨x', rfl, hx'F⟩
    ((hzc'.preimage f.continuous).inter hF₀cl).isLocallyClosed
  have hx''E : x'' ∈ (MMP.Mori.exceptionalSet f : Set X) :=
    mem_exceptionalSet_of_mem (hF₀ ▸ hx''F)
  obtain ⟨C₀, -, -, hC₀d, hx''C₀, y, hy⟩ :=
    MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet hXv hYv f rfl
      hfb hf.isIso_app hx''c hx''E
  have hsub := not_preimage_subset_singleton_of_image_eq_singleton f hC₀d hx''C₀ hy hx''z
  obtain ⟨C, hCf, p, hpC, hpS⟩ := exists_properCurve_isContractedBy sY (f ≫ sY) hY hX f rfl
    hfb (f x') hzc' hx''c ⟨x'', hx''z, rfl⟩ hsub
  rw [range_curveSubschemeAtι C.point, show p = x'' from hpS] at hpC
  have hfC : f C.point = f x' := (hCf x'' hpC).symm.trans hx''z
  obtain ⟨m, r, L, t, ht, ht0⟩ :=
    exists_isRIntersectionNumber_ne_zero_of_isRelativelyAntiAmple (f ≫ sY) hA hCf
  exact ht0 (hU C hCf (hfC ▸ hzU) (hfC ▸ hzb) (hfC ▸ hzc') m r L t ht)

/-- **Discrepancies increase exactly over the exceptional divisor** (FA 2.28.3.1). Let
`f : X ⟶ Y` be a birational contraction of normal varieties over a perfect field whose
exceptional set is a prime divisor `F₀`. Let `K_Y = div_Y(ω)` and `K_X = div_X(f^*ω)` for a
rational `n`-form `ω` on `Y`, `D_X` an `ℝ`-divisor on `X` with `K_X + D_X` `ℝ`-Cartier and
`-(K_X + D_X)` `f`-ample, and `D_Y = f_* D_X` with `K_Y + D_Y` `ℝ`-Cartier. Let `v` be a divisor
of `k(X)` whose transport `v_Y` to `k(Y)` has nonempty center on `Y`, and `B_v` a divisor over
`X` realizing `v`. Then `a(v, X, D_X) < a(v_Y, Y, D_Y)` if and only if
`Center_X(B_v) ⊆ F₀`. -/
@[mmp "lem_fa2_extremal_divisorial_contraction_discrepancy_increase"]
public theorem IsBirationalContraction.isDiscrepancy_lt_iff_center_subset {k : Type u} [Field k]
    [PerfectField k] {X Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [QuasiCompact sY]
    [LocallyOfFiniteType sY] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hY : IsNormalVariety k sY) {f : X ⟶ Y} [IsProper f]
    (hX : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalContraction k sY (f ≫ sY) f)
    {F₀ : Mori.PrimeDivisor X} (hF₀ : exceptionalSet f = (F₀.support : Set X))
    {n : ℕ} {ω : RationalPluriForms sY n 1} {K_X : Divisor X} {K_Y : Divisor Y}
    (hKY : divisorOfForm ω = K_Y)
    (hKX : haveI : Surjective f := hf.surjective_and_isBirational.1
      divisorOfForm (pullbackRationalPluriForms sY f ω) = K_X)
    {D_X : RDivisor X} {D_Y : RDivisor Y}
    (hKD : IsCartierCombination (logCanonicalDivisor K_X D_X))
    (hA : IsRelativelyAntiAmple f (logCanonicalDivisor K_X D_X))
    (hDY : Mori.RationalMap.transformDivisor f.toRationalMap D_X = D_Y)
    (hKDY : IsCartierCombination (logCanonicalDivisor K_Y D_Y))
    {vY : Valuation Y.functionField ℤᵐ⁰} (hvY : HasNonemptyCenter k sY vY)
    {v : Valuation X.functionField ℤᵐ⁰}
    (hv : haveI : Surjective f := hf.surjective_and_isBirational.1
      v.comap (functionFieldMap f) = vY)
    {Bv : ProperDivisorOver k (f ≫ sY)} (hBv : Bv.valuation = v)
    {a a' : ℝ} (ha : IsDiscrepancy (f ≫ sY) n K_X D_X v a)
    (ha' : IsDiscrepancy sY n K_Y D_Y vY a') :
    a < a' ↔ (Bv.center : Set X) ⊆ F₀.support := by
  have hfb : IsBirationalMorphism f := hf.surjective_and_isBirational.2
  have : IsDominant f := hfb.isDominant
  have hg : IsBirationalMorphism (𝟙 Y) := isBirationalMorphism_of_isIso (𝟙 Y)
  have hY' : IsNormalVariety k (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  have : QuasiCompact (f ≫ sY) := hX.1.toQuasiCompact
  have : IsSeparated sY := hY.1.toIsSeparated
  set E_X : RDivisor X := Finsupp.single F₀ (D_X F₀)
  have hDX : birationalInverseTransform f hfb D_Y + E_X = D_X := by
    rw [← hDY]; exact birationalInverseTransform_add_single hY hX hfb hF₀ D_X
  have hDY' : birationalInverseTransform (𝟙 Y) hg D_Y + 0 = D_Y :=
    (add_zero _).trans (birationalInverseTransform_id hY D_Y)
  have hEX : ∀ P : MMP.Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sY f P →
      E_X.coeff P = 0 := fun P hP => by
    refine DivisorWithCoeffs.coeff_single_of_ne (fun h => hP ?_) _
    exact h ▸ isExceptionalPrimeDivisor_of_support_eq hY hX hfb hF₀
  have hKY' : divisorOfForm (pullbackRationalPluriForms sY (𝟙 Y) ω) = K_Y := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hn, -⟩ := ha'
    rw [pullbackRationalPluriForms_id (toNat_trdeg_functionField_of_topologicalKrullDim_eq
      (sX := sY) hn)]
    exact hKY
  have hAX : IsRelativelyNef k (f ≫ sY) f
      (-logCanonicalDivisor K_X (birationalInverseTransform f hfb D_Y + E_X)) := by
    rw [hDX]; exact isRelativelyNef_neg_of_isRelativelyAntiAmple _ hA
  have hAY : IsRelativelyNef k (𝟙 Y ≫ sY) (𝟙 Y)
      (logCanonicalDivisor K_Y (birationalInverseTransform (𝟙 Y) hg D_Y + 0)) := by
    rw [hDY']; exact isRelativelyNef_id _ hKDY
  have hvY' : vY.comap (functionFieldMap (𝟙 Y)) = vY := by
    ext t; rw [Valuation.comap_apply, functionFieldMap_id_apply]
  have ha₁ : MMP.Flips.IsDiscrepancy (f ≫ sY) n K_X
      (birationalInverseTransform f hfb D_Y + E_X) v a := by rwa [hDX]
  have ha₁' : MMP.Flips.IsDiscrepancy (𝟙 Y ≫ sY) n K_Y
      (birationalInverseTransform (𝟙 Y) hg D_Y + 0) vY a' := by
    rwa [hDY', isDiscrepancy_congr (Category.id_comp sY)]
  have hle := (isDiscrepancy_le_of_isRelativelyNef hY hX hY' hfb hg hKX hKY' hEX
    (fun _ _ => rfl) hAX hAY hvY hv hvY').2.2 a a' ha₁ ha₁'
  obtain ⟨Bv', hBv'⟩ := hvY.2
  have hb : IsGenericPoint (Bv'.f Bv'.E.genericPoint) (Bv'.center : Set Y) := by
    rw [Bv'.center_eq_toDivisorOver_center, Bv'.toDivisorOver.center_eq_closure_genericPoint]
    rfl
  have heq := isDiscrepancy_eq_iff_isNumericallyTrivialOverPoint hY hX hY' hfb hg hKX hKY' hEX
    (fun _ _ => rfl) hAX hAY hvY hv hvY' hBv' hb ha₁ ha₁'
  have hfx : f (Bv.f Bv.E.genericPoint) = Bv'.f Bv'.E.genericPoint :=
    map_genericPoint_eq_of_valuation_comap_eq f Bv.toDivisorOver Bv'.toDivisorOver
      (by rw [show Bv.toDivisorOver.valuation = v from hBv, hv]; exact hBv'.symm)
  rw [lt_iff_le_and_ne, and_iff_right hle, Ne, heq, hDX, hDY',
    and_iff_left (isNumericallyTrivialOverPoint_id _ hKDY _), ← hfx,
    isNumericallyTrivialOverPoint_iff hY hX hf hF₀ hKD hA, not_not,
    Bv.center_eq_toDivisorOver_center, Bv.toDivisorOver.center_eq_closure_genericPoint,
    F₀.idealSheaf.support.isClosed.closure_subset_iff, Set.singleton_subset_iff]

end MMP.Flips
