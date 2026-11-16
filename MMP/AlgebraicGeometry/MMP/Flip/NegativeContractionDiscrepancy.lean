module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase

/-!
# Discrepancies under flips and negative contractions

Let `(X, Δ)` be a pair. For a `(K + Δ)`-flip `f⁺ : X⁺ ⟶ Y` of a `(K + Δ)`-flipping contraction
`f : X ⟶ Y`, discrepancies of divisors exceptional over `Y` do not decrease:
`a(E, X, Δ) ≤ a(E, X⁺, Δ⁺)`. For a proper birational morphism `f : X ⟶ Y` onto a normal variety
with `-(K_X + Δ)` `f`-nef and `K_Y + f_*Δ` `ℚ`-Cartier, `a(F, X, Δ) ≤ a(F, Y, f_*Δ)` for every
divisor `F` over `Y` exceptional over `Y`, and the inequality is strict when `-(K_X + Δ)` is
`f`-ample and the center of `F` on `Y` lies in `f(Ex f)`. All three are the comparison of
discrepancies `MMP.Mori.isDiscrepancy_le_of_isRelativelyNef` (resp. its strict form
`MMP.Mori.isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple`), applied with `X' = X⁺`, resp.
`X' = Y`, `f' = 𝟙 Y` and `Δ' = f_*Δ`.

## Main results

* `MMP.Mori.ProperCurve.not_isContractedBy_id`: the identity contracts no proper curve, so
  `MMP.Flips.isRelativelyNef_id`: every `ℝ`-Cartier divisor is nef over the identity.
* `MMP.Mori.isDiscrepancy_le_transformDivisor_of_isRelativelyNef`:
  `a(F, X, Δ) ≤ a(F, Y, f_*Δ)` for a negative contraction.
* `MMP.Mori.isDiscrepancy_lt_transformDivisor_of_hasRelativelyAmpleMultiple`:
  `a(F, X, Δ) < a(F, Y, f_*Δ)` when `-(K_X + Δ)` is `f`-ample and `center_Y F ⊆ f(Ex f)`.
* `MMP.Mori.IsFlip.isDiscrepancy_le`: `a(E, X, Δ) ≤ a(E, X⁺, Δ⁺)` for a flip.

## Implementation notes

A divisor over `Y` is given, as in `MMP.Mori.isDiscrepancy_le_of_isRelativelyNef`, by a divisor
`D` over the source and a divisor `D'` over the target inducing the same valuation of `k(Y)`;
being exceptional over `Y` is that `D.E` is exceptional for `D.f ≫ f`. The push-forward `f_*Δ` is
`MMP.Mori.RationalMap.transformDivisor`, and the boundary and canonical divisor of a flip are the
transforms `MMP.Mori.flipTransform f f⁺` fixed by `MMP.Mori.IsFlip`. Each result's auxiliary
lemmas live in a namespace `Proof_<tag>` named after its label, opened only for that
result; the strict negative-contraction result reuses the identity-morphism lemmas of the
non-strict one. The ground field is algebraically closed of characteristic zero, the standing
convention of Kollár–Mori.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proofs of
  Corollaries 3.42, 3.43 and 3.44
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry hiding PrimeDivisor

universe u

namespace MMP.Mori

/-- The identity morphism contracts no proper curve. -/
public theorem ProperCurve.not_isContractedBy_id {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (C : ProperCurve sY) : ¬ C.IsContractedBy (𝟙 Y) := by
  intro hC
  have : Subsingleton (curveSubschemeAt C.point) := ⟨fun a b =>
    (curveSubschemeAtι C.point).isEmbedding.injective <|
      (hC _ (range_curveSubschemeAtι C.point ▸ ⟨a, rfl⟩)).trans
        (hC _ (range_curveSubschemeAtι C.point ▸ ⟨b, rfl⟩)).symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (curveSubschemeAt C.point)
  rw [C.isProperCurve.dim_eq] at h0
  exact absurd h0 (by decide)

end MMP.Mori

namespace MMP.Flips

open MMP.Mori

/-- An `ℝ`-Cartier `ℝ`-divisor is nef relative to the identity. -/
public theorem isRelativelyNef_id {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    {D : RDivisor Y} (hD : IsCartierCombination D) : IsRelativelyNef k sY (𝟙 Y) D := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  exact ⟨m, r, L, hL, hDL, fun C hC => (C.not_isContractedBy_id hC).elim⟩

end MMP.Flips

namespace Proof_lem_km3c_negative_contraction_discrepancy_nondecreasing

open MMP.Mori

/-- The birational transform of divisors under the identity of a reduced separated scheme is the
identity. -/
private theorem transformDivisor_id {Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    RationalMap.transformDivisor (X := Y) (𝟙 Y : Y ⟶ Y).toRationalMap D = D := by
  have h (E : MMP.Mori.PrimeDivisor Y) :
      RationalMap.transformPrimeDivisor (X := Y) (𝟙 Y : Y ⟶ Y).toRationalMap E = some E :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 Y) E E).mpr rfl
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, hD, hD']
  | single E r => exact RationalMap.transformDivisor_single_of_eq_some (h E) r

/-- A `ℚ`-Cartier `ℚ`-divisor is nef relative to the identity. -/
private theorem isRelativelyNef_id {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY]
    {D : QDivisor Y} (hD : D.IsQCartier) : QDivisor.IsRelativelyNef sY (𝟙 Y) D :=
  ⟨hD, fun C hC => (C.not_isContractedBy_id hC).elim⟩

end Proof_lem_km3c_negative_contraction_discrepancy_nondecreasing

namespace MMP.Mori

open Proof_lem_km3c_negative_contraction_discrepancy_nondecreasing

/-- **Negative contractions do not decrease discrepancies** (Kollár–Mori, proof of 3.43). Let
`(X, Δ)` be a pair with canonical divisor `K_X` of dimension `n` and `f : X ⟶ Y` a proper
birational morphism onto a normal variety over an algebraically closed field of characteristic
zero, with `-(K_X + Δ)` `f`-nef, and let `K_Y` be a canonical divisor of `Y` of dimension `n` with
`K_Y + f_*Δ` `ℚ`-Cartier. Let `D` be a divisor over `X` and `D'` a divisor over `Y` inducing the
same valuation of `k(Y)`, exceptional over `Y`. If `a = a(D, X, Δ)` and `a' = a(D', Y, f_*Δ)`,
then `a ≤ a'`. -/
@[mmp "lem_km3c_negative_contraction_discrepancy_nondecreasing"]
public theorem isDiscrepancy_le_transformDivisor_of_isRelativelyNef {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sX] [QuasiCompact sY]
    {Δ : QDivisor X} (hpair : IsPair sX Δ) (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} [IsProper f] (hfs : f ≫ sY = sX) (hf : IsBirationalMorphism f)
    {KX : Divisor X} {KY : Divisor Y} (hK : KX.IsCanonicalDivisor sX n)
    (hKY : KY.IsCanonicalDivisor sY n)
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hQ : (Divisor.toQDivisor KY +
      RationalMap.transformDivisor (X := X) f.toRationalMap Δ).IsQCartier)
    (D : DivisorOver k sX) (D' : DivisorOver k sY)
    (hv : haveI : IsDominant f := hf.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation)
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a)
    (ha' : IsDiscrepancy sY n KY (RationalMap.transformDivisor (X := X) f.toRationalMap Δ) D' a') :
    a ≤ a' := by
  have := hY.1
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  refine isDiscrepancy_le_of_isRelativelyNef hpair.isNormalVariety hY hY hfs (Category.id_comp sY)
    hf (isBirationalMorphism_of_isIso (𝟙 Y)) hK hKY (transformDivisor_id _).symm hN
    (isRelativelyNef_id hQ) D D' ?_ hE ha ha'
  rw [hv]
  ext x
  rw [Valuation.comap_apply, functionFieldMap_id_apply]

end MMP.Mori

namespace Proof_lem_km3c_negative_contraction_discrepancy_strict

open MMP.Mori TopologicalSpace

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

/-- A prime divisor `E` of `W` whose generic point `g` maps into a closed subset `C` of
codimension at least two is exceptional for `g`. -/
private theorem isExceptional_of_map_genericPoint_mem {W Y : Scheme.{u}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] (g : W ⟶ Y) (E : MMP.Mori.PrimeDivisor W)
    {C : Closeds Y} (hC : 2 ≤ closedsCodimension C) (hE : g E.genericPoint ∈ C) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at hC ⊢
  refine fun z hz => hC z (closure_minimal ?_ C.isClosed hz)
  rintro _ ⟨e, he, rfl⟩
  have hηe : E.genericPoint ⤳ e := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  exact (hηe.map g.continuous).mem_closed C.isClosed hE

end Proof_lem_km3c_negative_contraction_discrepancy_strict

namespace MMP.Mori

open Proof_lem_km3c_negative_contraction_discrepancy_nondecreasing
open Proof_lem_km3c_negative_contraction_discrepancy_strict

/-- **Negative contractions strictly increase discrepancies** (Kollár–Mori, proof of 3.43–3.44).
In the setting of `MMP.Mori.isDiscrepancy_le_transformDivisor_of_isRelativelyNef`, assume
moreover that `-(K_X + Δ)` is `f`-ample. Let `D` be a divisor over `X` and `D'` a divisor over
`Y` inducing the same valuation of `k(Y)`, whose center on `Y` lies in `f(Ex f)`. If
`a = a(D, X, Δ)` and `a' = a(D', Y, f_*Δ)`, then `a < a'`. -/
@[mmp "lem_km3c_negative_contraction_discrepancy_strict"]
public theorem isDiscrepancy_lt_transformDivisor_of_hasRelativelyAmpleMultiple {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sX] [QuasiCompact sY]
    {Δ : QDivisor X} (hpair : IsPair sX Δ) (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} [IsProper f] (hfs : f ≫ sY = sX) (hf : IsBirationalMorphism f)
    {KX : Divisor X} {KY : Divisor Y} (hK : KX.IsCanonicalDivisor sX n)
    (hKY : KY.IsCanonicalDivisor sY n)
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor KX + Δ)))
    (hQ : (Divisor.toQDivisor KY +
      RationalMap.transformDivisor (X := X) f.toRationalMap Δ).IsQCartier)
    (hA : haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
      (-(Divisor.toQDivisor KX + Δ)).HasRelativelyAmpleMultiple f)
    (D : DivisorOver k sX) (D' : DivisorOver k sY)
    (hv : haveI : IsDominant f := hf.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation)
    (hc : (D'.center : Set Y) ⊆ f '' (exceptionalSet f : Set X))
    {a a' : ℚ} (ha : IsDiscrepancy sX n KX Δ D a)
    (ha' : IsDiscrepancy sY n KY (RationalMap.transformDivisor (X := X) f.toRationalMap Δ) D' a') :
    a < a' := by
  have := hY.1
  have : IsSeparated (Y ↘ Limits.terminal Scheme) := by
    rw [show (Y ↘ Limits.terminal Scheme) = sY ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsDominant f := hf.isDominant
  have := D.isLocallyNoetherian
  have := D.isNormal
  have hW : f (D.f D.E.genericPoint) ∈ (biregularLocus f).compl := by
    have hy : f (D.f D.E.genericPoint) ∈ (D'.center : Set Y) := by
      rw [map_genericPoint_eq_of_valuation_comap_eq f D D' hv,
        D'.center_eq_closure_genericPoint]
      exact subset_closure rfl
    obtain ⟨w, hw, hwy⟩ := hc hy
    exact hwy ▸ mem_exceptionalSet.mp hw
  refine isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple hpair.isNormalVariety hY hY hfs
    (Category.id_comp sY) hf (isBirationalMorphism_of_isIso (𝟙 Y)) hK hKY
    (transformDivisor_id _).symm hN (isRelativelyNef_id hQ) hA D D' ?_
    (isExceptional_of_map_genericPoint_mem _ D.E (two_le_closedsCodimension_compl_biregularLocus
      sY f (hY := hY.1) (hX := hfs ▸ hpair.isNormalVariety.1) hf) hW) hW ha ha'
  rw [hv]
  ext x
  rw [Valuation.comap_apply, functionFieldMap_id_apply]

end MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_km3c_flip_discrepancy_nondecreasing

open MMP.Mori

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {k : Type u} [Field k]
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {f : X ⟶ Y} {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hq fun C hC => ?_
  have := hL.isInvertibleModule_divisorialSheaf
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hq hm L hL hLD]
  exact div_nonneg (by exact_mod_cast
    (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      L.divisorialSheaf hamp C hC).le) m.cast_nonneg

/-- For a proper birational morphism `g : X' ⟶ Y` onto a normal variety with exceptional set of
codimension at least two, `g_* g⁻¹_* B = B` for every divisor `B` on `Y`. -/
private theorem transformDivisor_inverseTransformDivisor {k : Type u} [Field k]
    {X' Y : Scheme.{u}} [IsLocallyNoetherian X'] [IsNormal X'] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) {g : X' ⟶ Y}
    (hX' : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    (h2 : 2 ≤ closedsCodimension (exceptionalSet g)) {R : Type*} [AddCommMonoid R]
    (B : DivisorWithCoeffs R Y) :
    RationalMap.transformDivisor (X := X') g.toRationalMap (inverseTransformDivisor g B) = B := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsIntegral X' := hX'.1.toIsIntegral
  have : IsDominant g := hg.isDominant
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX' hg Q
  rw [htr]
  have hQV : g E.genericPoint ∈ biregularLocus g := by
    rw [hEQ]
    exact MMP.Positivity.mem_biregularLocus_of_coheight_le_one g hg.functionFieldMap_bijective h2
      Q.coheight_genericPoint.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hEQ hQV)
    (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hEQ)

end Proof_lem_km3c_flip_discrepancy_nondecreasing

namespace MMP.Mori

open Proof_lem_km3c_flip_discrepancy_nondecreasing

/-- **Flips do not decrease discrepancies** (Kollár–Mori, proof of 3.42). Let `(X, Δ)` be a pair
with canonical divisor `K` of dimension `n`, `f : X ⟶ Y` a `(K + Δ)`-flipping contraction and
`f⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip (`MMP.Mori.IsFlip`). Let `D` be a divisor over `X` and `D'` a
divisor over `X⁺` inducing the same valuation of `k(Y)`, exceptional over `Y`. If
`a = a(D, X, Δ)` and `a' = a(D', X⁺, Δ⁺)`, with `Δ⁺ = (f⁺)⁻¹_* f_* Δ` and
`K_{X⁺} = (f⁺)⁻¹_* f_* K`, then `a ≤ a'`. -/
@[mmp "lem_km3c_flip_discrepancy_nondecreasing"]
public theorem IsFlip.isDiscrepancy_le {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {n : ℕ} {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hpair : IsPair sX Δ) (hflip : IsFlip sX sY sX' K Δ f fp)
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hflip.isFlippingContraction.isNormalVariety_target.1.toIsIntegral
      haveI : IsDominant f := hflip.isFlippingContraction.isBirationalMorphism.isDominant
      haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    {a a' : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp Δ) D' a') :
    a ≤ a' := by
  have hc := hflip.isFlippingContraction
  have hY := hc.isNormalVariety_target
  have : IsProper f := hc.isProper
  have : IsProper fp := hflip.isProper
  have : QuasiCompact sX := hc.isNormalVariety_source.1.toQuasiCompact
  have : QuasiCompact sX' := hflip.isNormalVariety.1.toQuasiCompact
  exact isDiscrepancy_le_of_isRelativelyNef hc.isNormalVariety_source hflip.isNormalVariety hY
    hc.comp_eq hflip.comp_eq hc.isBirationalMorphism hflip.isBirationalMorphism ha.2.1 ha'.2.1
    (transformDivisor_inverseTransformDivisor hY (hflip.comp_eq ▸ hflip.isNormalVariety)
      hflip.isBirationalMorphism hflip.two_le_codimension _).symm
    (isRelativelyNef_of_hasRelativelyAmpleMultiple hc.hasRelativelyAmpleMultiple)
    (isRelativelyNef_of_hasRelativelyAmpleMultiple hflip.hasRelativelyAmpleMultiple)
    D D' hv hE ha ha'

end MMP.Mori

end
