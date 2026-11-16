module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
import StacksFrontier.RingTheory.Catenary.Localization
import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Klt pairs, contractions, discrepancies and general very ample members

This file collects several results from the foundations of the minimal model program.

* **Klt pairs.** For a pair `(X, B)` with a `ℚ`-boundary on a normal variety, being klt in the
  sense of positive log discrepancies (`MMP.Fourfold.IsKltPair`) is equivalent to being klt in
  the sense of Kollár–Mori (`MMP.Mori.IsKltPair`: `discrep(X, B) > -1` and `⌊B⌋ ≤ 0`). Log
  discrepancies are affine in the boundary, so rational convex combinations of klt boundaries
  are klt.
* **Contractions.** The contraction of an extremal face is unique up to unique isomorphism.
  For a proper birational morphism `f` with `f_* 𝒪_X = 𝒪_Y`, every closed point of the
  exceptional set lies on an irreducible curve contracted by `f`. The negativity lemma over a
  point: if `B` is effective, `ℚ`-Cartier and `-B` is `h`-nef for a proper birational `h`, every
  fibre of `h` lies in `Supp B` or misses it.
* **Discrepancies.** If `totaldiscrep(X, Δ) < -1` and `dim X ≥ 2`, repeatedly blowing up a
  codimension-two stratum gives exceptional divisors of arbitrarily negative discrepancy, so
  `discrep(X, Δ) = -∞`.
* **General members.** Bertini's irreducibility theorem for a free linear system whose morphism
  has image of dimension at least two, and its consequence: a very ample divisor on a projective
  variety of dimension at least two is linearly equivalent to an effective divisor with integral
  subscheme containing none of finitely many given closed irreducible proper subsets.

## Main results

* `MMP.Fourfold.isKltPair_iff_mori_isKltPair`: the two notions of klt pair agree.
* `MMP.Fourfold.isKltPair_of_mem_convexHull`: rational convex combinations of klt boundaries
  are klt.
* `MMP.Mori.existsUnique_iso_of_isContractionOfFace`: uniqueness of the contraction of an
  extremal face.
* `MMP.Mori.exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet`: closed points
  of the exceptional set lie on contracted curves.
* `MMP.Mori.QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg`: the
  negativity lemma over a point.
* `MMP.Mori.discrep_eq_bot_of_totalDiscrep_lt_neg_one`: a total discrepancy below `-1` forces
  `discrep = -∞` in dimension at least two.
* `MMP.Threefold.Bridges.exists_dense_open_geometricallyIrreducible_zeroScheme`: Bertini's
  irreducibility theorem for a free system.
* `MMP.Intersection.exists_linearlyEquivalent_isIntegral_subscheme_of_isVeryAmpleDivisor`: an
  integral very ample member avoiding finitely many closed subsets.

## Implementation notes

The klt dictionary is stated over a perfect field, the setting of the comparison
`MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy`; a pair in the sense of
`MMP.Fourfold.IsPair` lives over an algebraically closed field of characteristic zero anyway.
The convex hull statement allows an arbitrary set of boundaries, which is equivalent to finitely
many. The hypothesis `dim X ≥ 2` of `MMP.Mori.discrep_eq_bot_of_totalDiscrep_lt_neg_one` is
necessary: on `𝔸¹` with `Δ = 2 · {0}` there are no exceptional divisors. A linear system is
presented by a spanning family `s₀, …, s_N` of sections, and its dense opens live in the
coefficient space `𝔸ᴺ⁺¹_k` and in `ℙᴺ_k`. Clause (3) of Bertini's hypotheses
[Stacks, Tag 0G4F] is produced by generic freeness and going down on an affine chart.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.26, 2.22,
  2.31, 2.34, 2.61, 3.39
* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe v

namespace MMP.Proof_lem_fourfold_km_klt_dictionary

/-- **Nagata compactification**: a separated morphism of finite type `f : Y ⟶ Z` to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{v}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{v}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type v} [Field k]
    {Y P : Scheme.{v}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- If `t ≫ g` is birational and `t` is an open immersion of integral schemes, `g` is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{v}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, hW, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by rw [hc]; infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ?_ ?_ hUV ?_
  · obtain ⟨w, hw⟩ := hW
    exact ⟨t w, w, hw, rfl⟩
  · obtain ⟨w, hw⟩ := hW
    exact ⟨_, ⟨w, hw⟩, rfl⟩
  · rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
    obtain ⟨w, rfl⟩ := hz
    refine ⟨(t.isoImage W).hom w, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

/-- **Kollár–Mori 2.22 for the identity model.** Every divisor `(Y, f, E)` over a normal variety
`X` (with `f` not necessarily proper) has the valuation of a divisor over `X` whose morphism is
proper: compactify `f` by Nagata's theorem, `Y ⊆ P → X`, and replace `P` by the normalization of
`P` in `Y`, which is finite over `P`, normal, and contains `Y` as an open subscheme. -/
private theorem exists_isProper_valuation_eq {k : Type v} [Field k] {X : Scheme.{v}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    ∃ E : DivisorOver k sX, IsProper E.f ∧ E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ := exists_isOpenImmersion_isProper_comp_eq D.f
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p ≫ sX) j
  set t := j.toNormalization
  let g := j.fromNormalization ≫ p
  have htg : t ≫ g = D.f := by
    simp only [g, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hgv : IsNormalVariety k (g ≫ sX) :=
    ⟨(isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm⟩
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism)
  let D' : DivisorOver k sX :=
    ⟨_, g, hgv, hgb, OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨D', (inferInstance : IsProper g), (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

section

variable {k : Type v} [Field k] [PerfectField k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {B : QDivisor X}

/-- If `m(K + B)` is Cartier with `m > 0`, every divisor over `X` has a discrepancy in `m⁻¹ℤ`. -/
private theorem exists_isDiscrepancy_intCast_div (hP : IsPair sX B)
    (hK : K.IsCanonicalDivisor sX n) {m : ℕ} (hm : 0 < m)
    (hmC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) (D : DivisorOver k sX) :
    ∃ z : ℤ, IsDiscrepancy sX n K B D ((z : ℚ) / m) := by
  obtain ⟨-, U, hU, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn hP hK hmC (D.f D.E.genericPoint)
  refine ⟨D.ordPullback τ, hP.1, hK, m, hm, hmC, U, hU, τ, hτ, ?_⟩
  field_simp

/-- The lattice bound: a number `z / m ∈ m⁻¹ℤ` with `1 + z / m > 0` is at least `1/m - 1`. -/
private theorem one_div_sub_one_le_of_pos {m : ℕ} (hm : 0 < m) {z : ℤ}
    (h : 0 < 1 + (z : ℝ) / m) : 1 / (m : ℝ) - 1 ≤ z / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : (0 : ℝ) < m + z := by
    have := mul_pos hm0 h
    rwa [mul_add, mul_one, mul_div_cancel₀ _ hm0.ne'] at this
  have hz1 : (1 : ℝ) ≤ m + z := by exact_mod_cast (show (0 : ℤ) < m + z by exact_mod_cast hz)
  rw [div_sub_one hm0.ne', div_le_div_iff_of_pos_right hm0]
  linarith

/-- **Positive log discrepancies bound the discrepancy away from `-1`.** If every log
discrepancy of `(X, B)` is positive and `m(K + B)` is Cartier with `m > 0`, then
`discrep(X, B) ≥ 1/m - 1`: every discrepancy is that of a divisor with proper morphism, so it is
a log discrepancy minus one, and it lies in `m⁻¹ℤ`. -/
private theorem one_div_sub_one_le_discrep (hP : IsPair sX B) (hK : K.IsCanonicalDivisor sX n)
    {m : ℕ} (hm : 0 < m) (hmC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a → 0 < a) :
    ((1 / m - 1 : ℝ) : EReal) ≤ discrep sX n K B := by
  refine le_discrep_iff.mpr fun D a _ ha => ?_
  obtain ⟨E, hEp, hE⟩ := exists_isProper_valuation_eq hP.1 D
  obtain ⟨z, hz⟩ := exists_isDiscrepancy_intCast_div hP hK hm hmC E
  obtain rfl : a = (z : ℚ) / m :=
    MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hE.symm) ha hz
  have h0 := hpos n E _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hz hEp)
  push_cast at h0 ⊢
  exact EReal.coe_le_coe_iff.mpr (one_div_sub_one_le_of_pos hm h0)

/-- **Klt pairs have every discrepancy above `-1`.** If `discrep(X, B) > -1` and every
coefficient of `B` is `< 1`, then every divisor over `X`, exceptional or not, has discrepancy
`> -1`; a non-exceptional one has the valuation of a prime divisor `P` of `X`, with discrepancy
`-coeff_P(B)`. -/
private theorem neg_one_lt_of_isDiscrepancy (hP : IsPair sX B) (hK : K.IsCanonicalDivisor sX n)
    (hdisc : -1 < discrep sX n K B) (hcoeff : ∀ P, B.coeff P < 1) {D : DivisorOver k sX}
    {a : ℚ} (ha : IsDiscrepancy sX n K B D a) : -1 < a := by
  by_cases hE : D.IsExceptional
  · exact_mod_cast (EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hdisc (discrep_le hE ha)) :)
  obtain ⟨P, hPv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hP.1 _ hE
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor k hP.1 P)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hPv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hPv) ha hc,
    hc.eq_neg_coeff_of_ofPrimeDivisor hP.1]
  linarith [hcoeff P]

end

end MMP.Proof_lem_fourfold_km_klt_dictionary

end

section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

open MMP.Proof_lem_fourfold_km_klt_dictionary in
/-- **Klt via log discrepancies is klt in the sense of Kollár–Mori.** Let `X` be an integral
normal scheme over a perfect field `k`, `K` a canonical divisor of `X` of dimension `n`, and `B`
a `ℚ`-divisor such that `(X, B)` is a pair. Then `(X, B)` is klt in the sense of
`MMP.Fourfold.IsKltPair` (positive log
discrepancy at every divisorial valuation) if and only if it is klt in the sense of
`MMP.Mori.IsKltPair` with canonical divisor `K`. -/
@[mmp "lem_fourfold_km_klt_dictionary"]
public theorem isKltPair_iff_mori_isKltPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X}
    (hB : IsPair sX B) :
    IsKltPair sX B ↔ MMP.Mori.IsKltPair sX n K B := by
  have hP : MMP.Mori.IsPair sX B := hB.isPair
  have hX : IsNormalVariety k sX := hP.1
  have : CompactSpace X := by
    have := hX.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have hKB : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨-, n', K', hK', hQ⟩ := hP
    exact hQ.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK)
  refine ⟨fun ⟨_, hpos⟩ => ⟨⟨hX, hK, hKB⟩, ?_, roundDown_nonpos_iff.mpr fun P => ?_⟩,
    fun ⟨_, hdisc, hfl⟩ => ⟨hB, fun n' D b hb => ?_⟩⟩
  · obtain ⟨m, hm, hmC⟩ := hKB.exists_pos
    refine lt_of_lt_of_le ?_ (one_div_sub_one_le_discrep hP hK hm hmC hpos)
    rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_lt_coe_iff]
    linarith [show (0 : ℝ) < 1 / m by positivity]
  · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
      (DivisorOver.ofPrimeDivisor k hX P)
    have h0 := hpos n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstance : IsProper (𝟙 X)))
    rw [hc.eq_neg_coeff_of_ofPrimeDivisor hX] at h0
    push_cast at h0
    exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)
  · obtain rfl : n' = n := by
      exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hb).symm.trans
        hK.topologicalKrullDim_eq
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
    rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha b).mp hb).2]
    have := neg_one_lt_of_isDiscrepancy hP hK hdisc (roundDown_nonpos_iff.mp hfl) ha
    have : (-1 : ℝ) < a := by exact_mod_cast this
    linarith

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry

universe v

namespace MMP.Proof_lem_fourfold_rational_klt_convex

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori (Divisor QDivisor RDivisor DivisorOver DivisorWithCoeffs)

section Helpers

variable {k : Type v} [Field k] {X : Scheme.{v}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- For a pair `(X, Δ)`, a canonical divisor `K = div(ω)` and a divisor `(Y, f, E)` over `X`,
`m(K + Δ)` is a Cartier divisor `M` with a pull-back `M'` to `Y`, for some `m > 0`. -/
private lemma exists_cartier_presentation [PerfectField k] {Δ : QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (D : DivisorOver k sX) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ (m : ℕ) (M : Divisor X) (M' : Divisor D.Y), 0 < m ∧ M.IsCartier ∧
      (∀ Γ, (M.coeff Γ : ℝ) = m * (K.coeff Γ + Δ.coeff Γ)) ∧
      ∃ hC, M.IsPullback D.f hC M' := by
  obtain ⟨-, -, -, m, hm, ⟨M, hM, hMc⟩, -⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨M', hM'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hMc
  refine ⟨m, M, M', hm, hMc, fun Γ => ?_, _, hM'⟩
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, smul_add, natCast_zsmul, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, nsmul_eq_mul] at this
  exact_mod_cast (by linear_combination this : (M.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ))

/-- **The log discrepancy is affine in the boundary.** Fix a nonzero rational top form `ω`
with `K = div(ω)` and a divisor `E` over `X`. If `K + Bᵢ = (1 / mᵢ) Mᵢ` with `Mᵢ` Cartier, pulled
back to `M'ᵢ`, and `B = ∑ᵢ wᵢ Bᵢ` with `∑ᵢ wᵢ = 1`, then
`a(E, X, B) = ∑ᵢ wᵢ (1 + ord_E(f^*ω) - (1 / mᵢ) coeff_E(M'ᵢ))`, computed with the presentation
`K + B = ∑ᵢ (wᵢ / mᵢ) Mᵢ`. -/
private lemma isLogDiscrepancy_sum {n : ℕ} {D : DivisorOver k sX}
    (hX : MMP.Mori.IsNormalVariety k sX) (hf : IsProper D.f)
    {ω : MMP.Mori.RationalPluriForms sX n 1} (hω0 : ω ≠ 0) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hKω : ∀ Γ, K.coeff Γ = Γ.ordForm ω)
    {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∑ i, w i = 1) {Bi : ι → RDivisor X}
    {B : RDivisor X} (hB : ∀ Γ, B.coeff Γ = ∑ i, w i * (Bi i).coeff Γ)
    {m : ι → ℕ} (hm : ∀ i, 0 < m i) {M : ι → Divisor X}
    {M' : haveI := D.isLocallyNoetherian; haveI := D.isNormal; ι → Divisor D.Y}
    (hMc : ∀ i, (M i).IsCartier)
    (hM : ∀ i Γ, ((M i).coeff Γ : ℝ) = m i * (K.coeff Γ + (Bi i).coeff Γ))
    (hpb : haveI := D.isLocallyNoetherian; haveI := D.isNormal;
      ∀ i, ∃ hC, (M i).IsPullback D.f hC (M' i)) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    MMP.Intersection.IsLogDiscrepancy sX n B D
      (∑ i, w i * (1 + (D.ordPullback ω : ℝ) - (1 / (m i : ℝ)) * (M' i).coeff D.E)) := by
  have hm0 i : (m i : ℝ) ≠ 0 := by exact_mod_cast (hm i).ne'
  let e := Fintype.equivFin ι
  refine ⟨hX, hf, ω, hω0, ⟨K, hK, hKω⟩, Fintype.card ι, fun j => w (e.symm j) / m (e.symm j),
    fun j => M (e.symm j), fun j => M' (e.symm j), fun _ => hMc _, fun Γ => ?_, fun _ => hpb _, ?_⟩
  · dsimp only
    rw [Equiv.sum_comp e.symm (fun i => w i / m i * ((M i).coeff Γ : ℝ)), hB, ← hKω]
    have h i : w i / m i * ((M i).coeff Γ : ℝ) = w i * K.coeff Γ + w i * (Bi i).coeff Γ := by
      rw [hM]; field_simp [hm0 i]
    simp [h, Finset.sum_add_distrib, ← Finset.sum_mul, hw]
  · dsimp only
    rw [Equiv.sum_comp e.symm (fun i => w i / m i * ((M' i).coeff D.E : ℝ))]
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hw, mul_one, one_mul, ← mul_assoc, mul_one_div]

end Helpers

end MMP.Proof_lem_fourfold_rational_klt_convex

end

section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

open MMP.Proof_lem_fourfold_rational_klt_convex in
/-- **Rational convex combinations of klt boundaries are klt.** Let `S` be a set of
`ℚ`-divisors on a normal variety `X` with `(X, B')` klt for every `B' ∈ S`. If `B` is a
`ℚ`-divisor whose associated `ℝ`-divisor lies in the real convex hull of `S`, and `K_X + B` is
`ℚ`-Cartier, then `(X, B)` is klt. -/
@[mmp "lem_fourfold_rational_klt_convex"]
public theorem isKltPair_of_mem_convexHull {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {S : Set (QDivisor X)} (hS : ∀ B' ∈ S, IsKltPair sX B') {B : QDivisor X}
    (hB : QDivisor.toRDivisor B ∈ convexHull ℝ (QDivisor.toRDivisor '' S))
    (hQ : MMP.Mori.IsPair sX B) :
    IsKltPair sX B := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hB
  choose Bi hBiS hBiz using hz
  have hP i : MMP.Fourfold.IsPair sX (Bi i) := (hS _ (hBiS i)).1
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := 0) (g := w)
    (by simp [hw1])
  have := (hP i₀).isAlgClosed
  have := (hP i₀).charZero
  have hcoeff Γ : (QDivisor.toRDivisor B).coeff Γ =
      ∑ i, w i * (QDivisor.toRDivisor (Bi i)).coeff Γ := by
    rw [← hsum]
    simp only [MMP.Mori.DivisorWithCoeffs.coeff, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, ← hBiz]
  refine ⟨⟨inferInstance, inferInstance, hQ, fun P => ?_⟩, fun n D a ha => ?_⟩
  · have := (hcoeff P).symm ▸ Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw0 i) (by simpa using (hP i).nonneg P)
    simpa using this
  obtain ⟨hX, hf, ω, hω0, ⟨K, hK, hKω⟩, -⟩ := id ha
  choose m M M' hm hMc hM hpb using fun i => exists_cartier_presentation (hP i).isPair hK D
  have hai i : 0 < 1 + (D.ordPullback ω : ℝ) - (1 / (m i : ℝ)) * (M' i).coeff D.E := by
    simpa using (hS _ (hBiS i)).2 n D _ <| isLogDiscrepancy_sum (ι := Unit) hX hf hω0 hK hKω
      (w := 1) (by simp) (Bi := fun _ => QDivisor.toRDivisor (Bi i)) (by simp) (fun _ => hm i)
      (fun _ => hMc i) (fun _ Γ => by rw [QDivisor.coeff_toRDivisor, hM]) fun _ => hpb i
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha <| isLogDiscrepancy_sum hX hf hω0 hK hKω
    hw1 hcoeff hm hMc (fun i Γ => by rw [QDivisor.coeff_toRDivisor, hM]) hpb]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw0 i) (hai i).le)
    ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (hai i₀)⟩

end MMP.Fourfold

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori

section

universe u

namespace MMP.Proof_lem_km1b_contraction_unique

/-- A contraction of `F` factors uniquely every other contraction of `F`. -/
private theorem existsUnique_comp_eq {k : Type u} [Field k]
    {X Z Z' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sZ' : Z' ⟶ Spec (.of k)} {F : Set (NumericalCurveClasses sX)} {φ : X ⟶ Z} {φ' : X ⟶ Z'}
    (hφ : IsContractionOfFace k sX sZ F φ) (hφ' : IsContractionOfFace k sX sZ' F φ') :
    ∃! σ : Z ⟶ Z', φ ≫ σ = φ' := by
  have : IsProper sZ :=
    isProper_of_isProjectiveMorphism _ hφ.isProjectiveVariety_target.isProjective
  have hq : IsProjectiveMorphism φ := IsProjectiveMorphism.of_comp φ sZ
    (hφ.comp_eq ▸ hφ.isProjectiveVariety_source.isProjective)
  have : IsProper φ := isProper_of_isProjectiveMorphism _ hq
  have : IsIso φ.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ φ.c fun U => hφ.isIso_app U.unop
  have : Surjective φ := φ.surjective_of_isIso_app hφ.isIso_app
  exact existsUnique_comp_eq_of_isContractedBy hφ.isProjectiveVariety_source
    hφ.isProjectiveVariety_target hφ'.isProjectiveVariety_target hq hφ.comp_eq hφ'.comp_eq
    fun C hC => (hφ'.isContractedBy_iff C).mpr ((hφ.isContractedBy_iff C).mp hC)

/-- Factorizations `φ ≫ σ = φ'` and `φ' ≫ τ = φ` between contractions of `F` compose to the
identity of the target of `φ`. -/
private theorem comp_eq_id {k : Type u} [Field k]
    {X Z Z' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {F : Set (NumericalCurveClasses sX)} {φ : X ⟶ Z} {φ' : X ⟶ Z'}
    (hφ : IsContractionOfFace k sX sZ F φ) {σ : Z ⟶ Z'} {τ : Z' ⟶ Z}
    (hσ : φ ≫ σ = φ') (hτ : φ' ≫ τ = φ) : σ ≫ τ = 𝟙 Z :=
  (existsUnique_comp_eq hφ hφ).unique (by rw [← Category.assoc, hσ, hτ]) (Category.comp_id φ)

end MMP.Proof_lem_km1b_contraction_unique

end

end

section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

open MMP.Proof_lem_km1b_contraction_unique in
/-- **Uniqueness of the contraction of an extremal face.** If `φ : X ⟶ Z` and `φ' : X ⟶ Z'` are
contractions of the same extremal face `F` of `NE̅(X)`, then there is a unique isomorphism
`σ : Z ≅ Z'` with `φ ≫ σ.hom = φ'`. -/
@[mmp "lem_km1b_contraction_unique"]
public theorem existsUnique_iso_of_isContractionOfFace {k : Type u} [Field k]
    {X Z Z' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sZ' : Z' ⟶ Spec (.of k)} {F : Set (NumericalCurveClasses sX)} {φ : X ⟶ Z} {φ' : X ⟶ Z'}
    (hφ : IsContractionOfFace k sX sZ F φ) (hφ' : IsContractionOfFace k sX sZ' F φ') :
    ∃! σ : Z ≅ Z', φ ≫ σ.hom = φ' := by
  obtain ⟨σ, hσ, hσu⟩ := existsUnique_comp_eq hφ hφ'
  obtain ⟨τ, hτ, -⟩ := existsUnique_comp_eq hφ' hφ
  exact ⟨⟨σ, τ, comp_eq_id hφ hσ hτ, comp_eq_id hφ' hτ hσ⟩, hσ,
    fun e he => Iso.ext (hσu _ he)⟩

end MMP.Mori

end

section

namespace MMP.Proof_lem_km2a_contraction_exceptional_set_covered_by_curves

open AlgebraicGeometry CategoryTheory MMP.Mori TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

universe u

/-- The closure of a point of an irreducible closed subset `W` is contained in `W`. -/
private theorem closureSingleton_le {T : Type*} [TopologicalSpace T] {W : IrreducibleCloseds T}
    {p : T} (hp : p ∈ (W : Set T)) : closureSingleton p ≤ W := by
  rw [← SetLike.coe_subset_coe, coe_closureSingleton]
  exact W.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hp)

/-- Two distinct closed points of an irreducible closed subset `W` of a noetherian scheme locally
of finite type over a field lie on an irreducible closed subset of `W` of dimension one: a minimal
irreducible closed subset of `W` through both points has dimension at most one by
`Stacks.Algebraization.CurveThroughPoints.exists_specializes_specializes`, and at least one since
it strictly contains the closure of one of the points. -/
private theorem exists_dim_one_le_of_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] [NoetherianSpace Y] (W : IrreducibleCloseds Y)
    {p q : Y} (hpW : p ∈ (W : Set Y)) (hqW : q ∈ (W : Set Y)) (hp : IsClosed ({p} : Set Y))
    (hq : IsClosed ({q} : Set Y)) (hpq : p ≠ q) :
    ∃ C : IrreducibleCloseds Y, C ≤ W ∧ topologicalKrullDim (C : Set Y) = 1 ∧
      p ∈ (C : Set Y) ∧ q ∈ (C : Set Y) := by
  have hwf : WellFounded ((· < ·) : IrreducibleCloseds Y → IrreducibleCloseds Y → Prop) :=
    (InvImage.wf (fun C : IrreducibleCloseds Y => (⟨C, C.isClosed⟩ : Closeds Y))
      wellFounded_lt).mono fun _ _ h => h
  obtain ⟨C, ⟨hCW, hpC, hqC⟩, hmin⟩ := hwf.has_min
    {C | C ≤ W ∧ p ∈ (C : Set Y) ∧ q ∈ (C : Set Y)} ⟨W, le_rfl, hpW, hqW⟩
  refine ⟨C, hCW, ?_, hpC, hqC⟩
  have h2 : ¬ 2 ≤ topologicalKrullDim (C : Set Y) := fun h2 => by
    obtain ⟨t, htC, hne, htp, htq⟩ :=
      Stacks.Algebraization.CurveThroughPoints.exists_specializes_specializes g C h2 hpC hqC hp hq
    refine hmin (closureSingleton t) ⟨(closureSingleton_le htC).trans hCW, htp.mem_closure,
      htq.mem_closure⟩ ((closureSingleton_le htC).lt_of_ne fun h => hne ?_)
    rw [← coe_closureSingleton, h]
  have hpC' : closureSingleton p < C := (closureSingleton_le hpC).lt_of_ne fun h => by
    rw [← h, coe_closureSingleton, hp.closure_eq] at hqC
    exact hpq hqC.symm
  have h0 : Order.height C ≠ 0 := Order.height_ne_zero.mpr fun h => hpC'.not_ge (h hpC'.le)
  rw [Stacks.Algebraization.CurveThroughPoints.topologicalKrullDim_eq_height] at h2 ⊢
  have h2' : Order.height C < 2 := not_le.mp fun h => h2 (WithBot.coe_le_coe.mpr h)
  rw [le_antisymm (Order.le_of_lt_add_one h2') (Order.one_le_iff_ne_zero.mpr h0)]
  rfl

/-- A point `x` of a closed preconnected subset `F ≠ {x}` of a noetherian space lies on an
irreducible closed subset of `F` other than `{x}`: otherwise `{x}` and the union of the
irreducible components of `F` missing `x` would split `F` into two disjoint closed pieces. -/
private theorem exists_isIrreducible_ne_singleton {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {F : Set T} (hFc : IsClosed F) (hF : IsPreconnected F) {x : T}
    (hxF : x ∈ F) (hne : F ≠ {x}) :
    ∃ t ⊆ F, IsClosed t ∧ IsIrreducible t ∧ x ∈ t ∧ t ≠ {x} := by
  obtain ⟨S, hSfin, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
  by_contra! H
  obtain ⟨t₀, ht₀, hxt₀⟩ := hxF
  have hx : IsClosed ({x} : Set T) :=
    H t₀ (Set.subset_sUnion_of_mem ht₀) (hScl t₀ ht₀) (hSirr t₀ ht₀) hxt₀ ▸ hScl t₀ ht₀
  have hK : IsClosed (⋃₀ {t ∈ S | x ∉ t}) :=
    (hSfin.subset fun _ h => h.1).isClosed_sUnion fun t ht => hScl t ht.1
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hF _ _ hx hK
    (fun z ⟨t, ht, hzt⟩ => by
      by_cases hxt : x ∈ t
      · exact .inl (H t (Set.subset_sUnion_of_mem ht) (hScl t ht) (hSirr t ht) hxt ▸ hzt)
      · exact .inr ⟨t, ⟨ht, hxt⟩, hzt⟩)
    (Set.eq_empty_of_forall_notMem fun z ⟨_, hzx, t, ht, hzt⟩ =>
      ht.2 (Set.mem_singleton_iff.mp hzx ▸ hzt)) with h | h
  · exact hne (h.antisymm (Set.singleton_subset_iff.mpr ⟨t₀, ht₀, hxt₀⟩))
  · obtain ⟨t, ht, hxt⟩ := h ⟨t₀, ht₀, hxt₀⟩
    exact ht.2 hxt

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` is an isomorphism on sections over every open and finite over an open `V`, then every
point of `V` lies in the biregular locus of `f`. -/
private theorem mem_biregularLocus_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hO : ∀ U : Y.Opens, IsIso (f.app U)) {V : Y.Opens} (hV : IsFinite (f ∣_ V)) {y : Y}
    (hy : y ∈ V) : y ∈ biregularLocus f := by
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := V) hy
  have e := morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr (show U ≤ V from hUV)] at e
  have := hV
  have hfin : IsFinite (f ∣_ U) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite e).mp inferInstance
  have : IsAffine U := hU
  have hbir : IsBiregular f U := by
    change MorphismProperty.isomorphisms Scheme (f ∣_ U)
    rw [HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
    refine ⟨isAffine_of_isAffineHom (f ∣_ U), ?_⟩
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hO _)
      (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U ⊤)).op).isIso_hom
  exact le_biregularLocus hbir hyU

end MMP.Proof_lem_km2a_contraction_exceptional_set_covered_by_curves

end

section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

universe u

open MMP.Proof_lem_km2a_contraction_exceptional_set_covered_by_curves in
/-- If `f : X ⟶ Y` is a proper birational morphism of `k`-varieties with `f_* 𝒪_X = 𝒪_Y`, then
every closed point of the exceptional set `MMP.Mori.exceptionalSet f` lies on an irreducible closed
curve `C ⊆ X` with `f(C)` a point. -/
@[mmp "lem_km2a_contraction_exceptional_set_covered_by_curves"]
public theorem exists_isIrreducible_curve_image_eq_singleton_of_mem_exceptionalSet
    {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : IsVariety k sX) (hY : IsVariety k sY) (f : X ⟶ Y) (hf : f ≫ sY = sX)
    [IsProper f] (hbir : IsBirationalMorphism f) (hO : ∀ U : Y.Opens, IsIso (f.app U))
    {x : X} (hxc : IsClosed ({x} : Set X)) (hx : x ∈ exceptionalSet f) :
    ∃ C : Set X, IsClosed C ∧ IsIrreducible C ∧ topologicalKrullDim C = 1 ∧ x ∈ C ∧
      ∃ y : Y, f '' C = {y} := by
  have := hX
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have hyc : IsClosed {f x} := Set.image_singleton (f := f) ▸ f.isClosedMap _ hxc
  -- The fibre is not `{x}`, by Zariski's main theorem.
  have hne : f ⁻¹' {f x} ≠ {x} := fun h => by
    obtain ⟨V, hyV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f (f x)
      (h ▸ Set.finite_singleton x)
    exact mem_exceptionalSet.mp hx (mem_biregularLocus_of_isFinite f hO hV hyV)
  obtain ⟨t, htF, htc, hti, hxt, htx⟩ := exists_isIrreducible_ne_singleton
    (hyc.preimage f.continuous) (f.isConnected_preimage_singleton_of_isIso_app hO _).isPreconnected
    rfl hne
  -- A second closed point of `t`.
  obtain ⟨x', ⟨hx't, hx'x⟩, hx'c⟩ : (t \ {x} ∩ closedPoints X).Nonempty :=
    nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr fun h => htx <|
      (Set.sdiff_eq_empty.mp h).antisymm (Set.singleton_subset_iff.mpr hxt))
      (htc.isLocallyClosed.inter hxc.isOpen_compl.isLocallyClosed)
  obtain ⟨C, hCt, hCdim, hxC, -⟩ :=
    exists_dim_one_le_of_mem sX ⟨t, hti, htc⟩ hxt hx't hxc hx'c (Ne.symm hx'x)
  refine ⟨C, C.isClosed, C.isIrreducible, hCdim, hxC, f x, ?_⟩
  exact (Set.image_subset_iff.mpr fun z hz => htF (hCt hz)).antisymm
    (Set.singleton_subset_iff.mpr ⟨x, hxC, rfl⟩)

end MMP.Mori

end

section

open AlgebraicGeometry CategoryTheory MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proof_lem_km2a_negativity_lemma_fibers

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
private theorem isProper_fiberι_comp.{u} (k : Type u) [Field k] {X Y : Scheme.{u}}
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
private theorem isProperCurve_of_injective.{u} {k : Type u} [Field k] {W Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] (ι : W ⟶ Y)
    (hι : Function.Injective ι) (C : ProperCurve (ι ≫ sY)) : IsProperCurve sY (ι C.point) := by
  have hφsY : (C.ι ≫ ι) ≫ sY = C.ι ≫ ι ≫ sY := Category.assoc _ _ _
  have : AlgebraicGeometry.IsCurve k ((C.ι ≫ ι) ≫ sY) := hφsY ▸ C.isCurve
  have : IsProper ((C.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hι (by
      have ha : (C.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      simpa using ha.trans hb.symm))⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
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
private theorem exists_properCurve_isContractedBy.{u} (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
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
  have : IsProper sF := by simpa [sF, ι, hf] using isProper_fiberι_comp k sX f hX x hx
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
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
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
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [hrC]
    intro h
    exact hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

/-- An effective `ℚ`-Cartier `ℚ`-divisor `B` with `-B` `f`-nef contains no proper curve contracted
by `f` that meets `Supp B` without lying in it: `B` would be positive on it. -/
private theorem not_isContractedBy_of_isRelativelyNef_neg.{u} (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) {B : QDivisor Y} (hB : B.IsQCartier) (hBeff : B.IsEffective)
    (hnef : (-B).IsRelativelyNef sY f) (C : ProperCurve sY)
    (hC : ¬ Set.range C.ι ⊆ (B.supp : Set Y))
    (hmeet : (Set.range C.ι ∩ (B.supp : Set Y)).Nonempty) :
    ¬ C.IsContractedBy f := by
  intro hCf
  have hrC : Set.range C.ι = closure {C.point} := C.range_ι
  have hpt : C.point ∉ B.supp := fun h => hC (by
    rw [hrC]; exact (B.supp.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr h))
  obtain ⟨p, hpC, hpS⟩ := hmeet
  rw [hrC] at hpC
  obtain ⟨hnn, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sY B hB hBeff C hpt
  have hpos : 0 < B.intersectionNumber k sY C.ι C.dim_le hB :=
    lt_of_le_of_ne hnn fun h => hiff.mp h.symm p (specializes_iff_mem_closure.mpr hpC) hpS
  have hnB : (-B).IsQCartier := hnef.1
  have hneg := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sY hnef hnB C hCf
  have hBB := QDivisor.intersectionNumber_add' k sY C.ι C.dim_le B (-B) hB hnB
    (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
  rw [MMP.Fourfold.intersectionNumber_congr sY C.ι C.dim_le _ QDivisor.isQCartier_zero
    (add_neg_cancel B), MMP.Fourfold.intersectionNumber_zero] at hBB
  linarith

end MMP.Proof_lem_km2a_negativity_lemma_fibers

end

section

universe u

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Proof_lem_km2a_negativity_lemma_fibers in
/-- **Negativity lemma over a point.** If `h : Z ⟶ Y` is a proper birational morphism of normal
varieties over `k` and `B` is an effective `ℚ`-Cartier `ℚ`-divisor on `Z` with `-B` `h`-nef,
then for every `y : Y` the fibre `h⁻¹(y)` is either contained in `Supp B` or disjoint from it. -/
@[mmp "lem_km2a_negativity_lemma_fibers"]
public theorem QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
    (k : Type u) [Field k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z] [IsNormal Z]
    (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hB : B.IsQCartier) (hBeff : B.IsEffective)
    (hnef : (-B).IsRelativelyNef sZ h) (y : Y) :
    h.base ⁻¹' {y} ⊆ (B.supp : Set Z) ∨ Disjoint (h.base ⁻¹' {y}) (B.supp : Set Z) := by
  by_contra hc
  rw [not_or, Set.not_disjoint_iff] at hc
  obtain ⟨hsub, z1, hz1, hz1S⟩ := hc
  obtain ⟨z2, hz2, hz2S⟩ := Set.not_subset.mp hsub
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have hT : IsLocallyClosed (closure {z2} ∩ (B.supp : Set Z)ᶜ) :=
    isClosed_closure.isLocallyClosed.inter B.supp.isClosed.isOpen_compl.isLocallyClosed
  obtain ⟨q, ⟨hq2, hqS⟩, hqc⟩ :=
    nonempty_inter_closedPoints
      ⟨z2, (show z2 ∈ closure {z2} ∩ (B.supp : Set Z)ᶜ from ⟨subset_closure rfl, hz2S⟩)⟩ hT
  have hqc' : IsClosed ({h q} : Set Y) := by
    simpa using h.isClosedMap _ (mem_closedPoints_iff.mp hqc)
  have hyq : y ⤳ h q := by
    have h2 : z2 ⤳ q := specializes_iff_mem_closure.mpr hq2
    have h3 := h2.map h.continuous
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz2
    rwa [hz2] at h3
  have hhS : IsClosed (h '' (B.supp : Set Z)) := h.isClosedMap _ B.supp.isClosed
  obtain ⟨z3, hz3S, hz3⟩ := hyq.mem_closed hhS ⟨z1, hz1S, hz1⟩
  obtain ⟨C, hCf, hC, hCS⟩ := exists_properCurve_isContractedBy k sY sZ hY hZ h hh hhb (h q) hqc'
    B.supp.isClosed ⟨z3, hz3, hz3S⟩ fun hs => hqS (hs rfl)
  exact not_isContractedBy_of_isRelativelyNef_neg k sZ h hB hBeff hnef C hC hCS hCf

end MMP.Mori

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

universe v

namespace MMP.Proof_lem_km2b_discrep_minus_infinity_or_totaldiscrep_ge_minus_one

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]

/-! ### Birational morphisms -/

/-! ### Regular local rings -/

section RegularLocal

variable {R : Type*} [CommRing R]

/-- In a Noetherian domain, a nonzero principal prime ideal has height one. -/
private theorem height_span_singleton_eq_one [IsNoetherianRing R] [IsDomain R] {π : R}
    (hπ : Prime π) : (Ideal.span {π}).height = 1 := by
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self (I := Ideal.span {π})]; rfl)) ?_
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  intro h0
  rw [Ideal.height_eq_zero_iff] at h0
  have hbot : Ideal.span {π} ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le
  exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hbot))

/-- If `π` is a prime of a regular local ring `R` with `R / (π)` regular, then `π` is a member of
a regular system of parameters of `R`. -/
private theorem exists_isRegularSystemOfParameters_of_prime [IsRegularLocalRing R] {π : R}
    (hπ : Prime π) (hq : IsRegularLocalRing (R ⧸ Ideal.span {π})) :
    ∃ (m : ℕ) (z : Fin m → R) (i : Fin m), IsRegularSystemOfParameters z ∧
      Ideal.span {π} = Ideal.span {z i} := by
  have : IsNoetherianRing R := IsRegularLocalRing.toIsNoetherian
  have := IsRegularLocalRing.isDomain R
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hdim := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one
    (Ideal.span {π}) (height_span_singleton_eq_one hπ)
  have hrange : Ideal.span (Set.range ![π]) = Ideal.span {π} := by simp
  obtain ⟨m, t, ht⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    ![π]).1 ⟨by rwa [hrange], by rw [hrange]; exact_mod_cast hdim⟩
  exact ⟨1 + m, Fin.append ![π] t, Fin.castAdd m 0, ht, by simp⟩

/-- If `π, ρ` are non-associated primes of a regular local ring `R` with `R / (π)` and
`R / (π, ρ)` regular, then `π` and `ρ` are two members of a regular system of parameters
of `R`. -/
private theorem exists_isRegularSystemOfParameters_of_prime_pair [IsRegularLocalRing R]
    {π ρ : R} (hπ : Prime π) (hρ : Prime ρ) (hne : ¬ Associated π ρ)
    (hq : IsRegularLocalRing (R ⧸ Ideal.span {π}))
    (hq2 : IsRegularLocalRing (R ⧸ Ideal.span {π, ρ})) :
    ∃ (m : ℕ) (z : Fin m → R) (i j : Fin m), i ≠ j ∧ IsRegularSystemOfParameters z ∧
      Ideal.span {π} = Ideal.span {z i} ∧ Ideal.span {ρ} = Ideal.span {z j} := by
  have : IsNoetherianRing R := IsRegularLocalRing.toIsNoetherian
  have := IsRegularLocalRing.isDomain R
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hdim := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one
    (Ideal.span {π}) (height_span_singleton_eq_one hπ)
  set R' := R ⧸ Ideal.span {π}
  have : IsNoetherianRing R' := IsRegularLocalRing.toIsNoetherian
  have := IsRegularLocalRing.isDomain R'
  set ρ' : R' := Ideal.Quotient.mk _ ρ
  have hsup : Ideal.span {π} ⊔ Ideal.span {ρ} = Ideal.span {π, ρ} := by
    rw [Ideal.span_insert]
  have hmap : (Ideal.span {ρ}).map (Ideal.Quotient.mk (Ideal.span {π})) = Ideal.span {ρ'} := by
    rw [Ideal.map_span, Set.image_singleton]
  let e : R' ⧸ Ideal.span {ρ'} ≃+* R ⧸ Ideal.span {π, ρ} :=
    (Ideal.quotEquivOfEq hmap.symm).trans
      ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hsup))
  have hreg' : IsRegularLocalRing (R' ⧸ Ideal.span {ρ'}) := IsRegularLocalRing.of_ringEquiv e.symm
  have := IsRegularLocalRing.isDomain (R' ⧸ Ideal.span {ρ'})
  have hρ'0 : ρ' ≠ 0 := by
    intro h
    have : π ∣ ρ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    exact hne (hπ.irreducible.associated_of_dvd hρ.irreducible this)
  have hρ'p : Prime ρ' := by
    have : (Ideal.span {ρ'}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
    exact (Ideal.span_singleton_prime hρ'0).1 this
  have : (Ideal.span {ρ'}).IsPrime := (Ideal.span_singleton_prime hρ'0).2 hρ'p
  have hdim' := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one
    (Ideal.span {ρ'}) (height_span_singleton_eq_one hρ'p)
  rw [ringKrullDim_eq_of_ringEquiv e] at hdim'
  have hrange : Ideal.span (Set.range ![π, ρ]) = Ideal.span {π, ρ} := by
    congr 1
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  obtain ⟨m, t, ht⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    ![π, ρ]).1 ⟨by rwa [hrange], by
      rw [hrange, ← hdim, ← hdim', add_assoc]
      norm_num⟩
  exact ⟨2 + m, Fin.append ![π, ρ] t, Fin.castAdd m 0, Fin.castAdd m 1, by simp, ht, by simp,
    by simp⟩

end RegularLocal

/-! ### Local facts -/

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X Y : Scheme.{v}} {f : X ⟶ Y} {x y : X}
    (h : f x = f y) (hx : f x ∈ biregularLocus f) : x = y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let px : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let py : (f ⁻¹ᵁ V).toScheme := ⟨y, show f y ∈ V by rw [← h]; exact hx⟩
  have hpx : V.ι ((f ∣_ V) px) = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]; rfl
  have hpy : V.ι ((f ∣_ V) py) = f y := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]; rfl
  have h1 : (f ∣_ V) px = (f ∣_ V) py := V.ι.isOpenEmbedding.injective (by rw [hpx, hpy, h])
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective h1)

/-- A prime divisor whose ideal at `η_Z` is generated by a member of a regular system of
parameters has multiplicity `1` along `Z`. -/
private theorem multiplicityAlong_eq_one {X : Scheme.{v}} [IsLocallyNoetherian X]
    (Q : MMP.Mori.PrimeDivisor X) (Z : IrreducibleCloseds X) {m : ℕ}
    {z : Fin m → X.presheaf.stalk Z.isIrreducible.genericPoint}
    (hz : IsRegularSystemOfParameters z) (i : Fin m)
    (hQ : IdealSheafData.stalk Q.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z i}) :
    Q.multiplicityAlong Z = 1 := by
  have hmem : ∀ j, z j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) :=
    fun j => by
    rw [← hz.1]; exact Ideal.subset_span ⟨j, rfl⟩
  have hli := linearIndependent_toCotangent_of_isRegularSystemOfParameters hz hmem
  have hsq :
      z i ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ 2 := by
    intro h
    exact hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).2 h)
  have hQ' : Q.idealSheaf.stalkIdeal Z.isIrreducible.genericPoint = Ideal.span {z i} := by
    rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  rw [PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span Q Z hQ']
  refine le_antisymm (iSup₂_le fun s hs => ?_) (le_iSup₂_of_le 1 (by simpa using hmem i) le_rfl)
  by_contra hlt
  push Not at hlt
  have : 2 ≤ s := by exact_mod_cast (ENat.add_one_le_iff (by simp)).2 hlt
  exact hsq (Ideal.pow_le_pow_right this hs)

/-- A prime divisor not passing through `η_Z` has multiplicity `0` along `Z`. -/
private theorem multiplicityAlong_eq_zero {X : Scheme.{v}} (Q : MMP.Mori.PrimeDivisor X)
    (Z : IrreducibleCloseds X) (h : Z.isIrreducible.genericPoint ∉ Q.support) :
    Q.multiplicityAlong Z = 0 := by
  unfold MMP.Mori.PrimeDivisor.multiplicityAlong
  rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ h]
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · exact absurd (top_le_iff.1 (hs.trans (Ideal.pow_le_self hs0.ne')))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- The blow-up `blowUp I` is an open subscheme of the blow-up `Stacks.Blowup.blowUp J` of an
equal ideal, compatibly with the projections. -/
private theorem exists_openImmersion_stacksBlowUp {X : Scheme.{v}} {I J : X.IdealSheafData}
    (h : I = J) : ∃ j : blowUp I ⟶ Stacks.Blowup.blowUp J, IsOpenImmersion j ∧
      j ≫ Stacks.Blowup.blowUpToBase J = blowUpToBase I := by
  subst h
  refine ⟨(Stacks.Blowup.blowUpIso I).inv, inferInstance, ?_⟩
  rw [← Stacks.Blowup.blowUpIso_hom_comp, Iso.inv_hom_id_assoc]

/-! ### Two prime divisors with simple normal crossings at a point -/

/-- The prime divisors in the support of `E + S`, for distinct prime divisors `E`, `S`. -/
private theorem mem_support_single_add_single_iff {X : Scheme.{v}}
    {E S : MMP.Mori.PrimeDivisor X} (hES : E ≠ S) (P : MMP.Mori.PrimeDivisor X) :
    P ∈ (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor X).support ↔ P = E ∨ P = S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hPE : E = P
  · subst hPE; simp [hES, Ne.symm hES]
  · by_cases hPS : S = P
    · subst hPS; simp [hES, Ne.symm hES]
    · simp [hPE, hPS, Ne.symm hPE, Ne.symm hPS]

/-- **Two prime divisors on a smooth scheme cross normally at a point** `y` where the
scheme-theoretic intersections through `y` are regular: there is a regular system of parameters
of `𝒪_{V,y}` two members of which cut out `E` and `S` at `y`. -/
private theorem sncStalk_single_add_single {V : Scheme.{v}} (sV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType sV] (hsm : IsSmoothScheme sV) {E S : MMP.Mori.PrimeDivisor V}
    (hES : E ≠ S) (y : V)
    (hE : y ∈ E.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸ IdealSheafData.stalk E.idealSheaf y))
    (hS : y ∈ S.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸ IdealSheafData.stalk S.idealSheaf y))
    (hC : y ∈ E.support → y ∈ S.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸
        (IdealSheafData.stalk E.idealSheaf y ⊔ IdealSheafData.stalk S.idealSheaf y))) :
    ∃ (n : ℕ) (z : Fin n → V.presheaf.stalk y)
      (jj : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V).support ∧
          y ∈ E'.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ e, IdealSheafData.stalk e.1.idealSheaf y = Ideal.span {z (jj e)} := by
  classical
  have : Smooth sV := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsm
  have : IsRegularLocalRing (V.presheaf.stalk y) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sV).1 inferInstance y
  have := IsRegularLocalRing.isDomain (V.presheaf.stalk y)
  have hmem := mem_support_single_add_single_iff hES
  by_cases hyE : y ∈ E.support <;> by_cases hyS : y ∈ S.support
  · obtain ⟨π, hπ, hπE⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sV hsm E hyE
    obtain ⟨ρ, hρ, hρS⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sV hsm S hyS
    have hne : ¬ Associated π ρ := fun h => hES (MMP.Intersection.eq_of_stalk_idealSheaf_eq hyE
      hyS (by rw [hπE, hρS]; exact Ideal.span_singleton_eq_span_singleton.2 h))
    have hq := hE hyE
    rw [hπE] at hq
    have hq2 := hC hyE hyS
    rw [hπE, hρS, ← Ideal.span_insert] at hq2
    obtain ⟨m, z, i, j, hij, hz, hzi, hzj⟩ :=
      exists_isRegularSystemOfParameters_of_prime_pair hπ hρ hne hq hq2
    refine ⟨m, z, fun e => if e.1 = E then i else j, hz, fun e e' h => ?_, fun e => ?_⟩
    · dsimp only at h
      split_ifs at h with h1 h2 h2
      · exact Subtype.ext (h1.trans h2.symm)
      · exact absurd h hij
      · exact absurd h.symm hij
      · exact Subtype.ext ((((hmem e.1).1 e.2.1).resolve_left h1).trans
          (((hmem e'.1).1 e'.2.1).resolve_left h2).symm)
    · rcases (hmem e.1).1 e.2.1 with he | he
      · simp only [he, ite_true]; rw [hπE, hzi]
      · simp only [he, Ne.symm hES, ite_false]; rw [hρS, hzj]
  · obtain ⟨π, hπ, hπE⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sV hsm E hyE
    have hq := hE hyE
    rw [hπE] at hq
    obtain ⟨m, z, i, hz, hzi⟩ := exists_isRegularSystemOfParameters_of_prime hπ hq
    have hEe : ∀ e : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V).support ∧
          y ∈ E'.support}, e.1 = E := fun e =>
      ((hmem e.1).1 e.2.1).resolve_right fun h => hyS (h ▸ e.2.2)
    refine ⟨m, z, fun _ => i, hz, fun e e' _ => Subtype.ext ((hEe e).trans (hEe e').symm),
      fun e => ?_⟩
    rw [hEe e, hπE, hzi]
  · obtain ⟨ρ, hρ, hρS⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sV hsm S hyS
    have hq := hS hyS
    rw [hρS] at hq
    obtain ⟨m, z, i, hz, hzi⟩ := exists_isRegularSystemOfParameters_of_prime hρ hq
    have hSe : ∀ e : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V).support ∧
          y ∈ E'.support}, e.1 = S := fun e =>
      ((hmem e.1).1 e.2.1).resolve_left fun h => hyE (h ▸ e.2.2)
    refine ⟨m, z, fun _ => i, hz, fun e e' _ => Subtype.ext ((hSe e).trans (hSe e').symm),
      fun e => ?_⟩
    rw [hSe e, hρS, hzi]
  · obtain ⟨m, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (V.presheaf.stalk y)
    have hempty : ∀ e : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V).support ∧
          y ∈ E'.support}, False := fun e => by
      rcases (hmem e.1).1 e.2.1 with he | he
      · exact hyE (he ▸ e.2.2)
      · exact hyS (he ▸ e.2.2)
    exact ⟨m, z, fun e => (hempty e).elim, hz, fun e => (hempty e).elim,
      fun e => (hempty e).elim⟩

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_add {X : Scheme.{v}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I + J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hx,
    show (I + J).ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ from rfl, Ideal.map_sup]

/-- Over a perfect field, a point with regular local ring is a smooth point. -/
private theorem mem_smoothLocus_of_isRegularLocalRing' {Y : Scheme.{v}} (f : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (y : Y) (h : IsRegularLocalRing (Y.presheaf.stalk y)) :
    y ∈ f.smoothLocus := by
  haveI : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f)).mpr inferInstance
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hsm := (smoothAt_iff_isRegularLocalRing_stalk f y
    (Algebra.isSeparableExtension_of_perfectField _ _)).mpr h
  exact Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)

/-- A point of a closed subscheme is a regular point exactly when the quotient of the local ring
of the ambient scheme by the stalk of the ideal is regular. -/
private theorem mem_regularLocus_subscheme_iff {X : Scheme.{v}} (I : X.IdealSheafData)
    (z : I.subscheme) : z ∈ regularLocus I.subscheme ↔
      IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z) ⧸
        IdealSheafData.stalk I (I.subschemeι z)) :=
  ⟨fun h => by
    haveI : IsRegularLocalRing (I.subscheme.presheaf.stalk z) := h
    exact IsRegularLocalRing.of_ringEquiv
      (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I z).symm,
   fun h => by
    haveI := h
    exact IsRegularLocalRing.of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I z)⟩

/-- **A prime divisor crossing a given one normally.** Let `V` be a smooth variety of dimension
at least two, `E` a prime divisor of `V` and `C` a closed subset not containing the generic point
of `E`. There are an open `U ⊆ V` disjoint from `C` and prime divisors `A`, `S` of `U` with
`A = E ∩ U`, `A ≠ S`, `A ∩ S ≠ ∅` and `A + S` a simple normal crossing divisor. -/
private theorem exists_open_snc_pair {V : Scheme.{v}} (sV : V ⟶ Spec (.of k))
    (hV : IsNormalVariety k sV) (hsm : IsSmoothScheme sV) [IsIntegral V]
    (hdim : 2 ≤ topologicalKrullDim V) (E : MMP.Mori.PrimeDivisor V) (C : Set V)
    (hC : IsClosed C) (hηC : E.genericPoint ∉ C) :
    ∃ (U : V.Opens) (A S : MMP.Mori.PrimeDivisor U), Disjoint (U : Set V) C ∧
      U.ι A.genericPoint = E.genericPoint ∧ A ≠ S ∧
      ((A.support : Set U) ∩ S.support).Nonempty ∧
      (Finsupp.single A (1 : ℤ) + Finsupp.single S 1 : Divisor U).IsSNC (U.ι ≫ sV) := by
  classical
  haveI := hV.1
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : Smooth sV := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsm
  have hregV : ∀ y : V, IsRegularLocalRing (V.presheaf.stalk y) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sV).1 inferInstance
  -- the regular locus of `E`
  set IE := E.idealSheaf with hIE
  haveI : IsIntegral IE.subscheme := E.integral
  have hRE : IsOpen (regularLocus IE.subscheme) :=
    MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (IE.subschemeι ≫ sV)
  have hηRE : genericPoint IE.subscheme ∈ regularLocus IE.subscheme :=
    MMP.Flips.isRegularLocalRing_of_isField (Field.toIsField _)
  have hιη : IE.subschemeι (genericPoint IE.subscheme) = E.genericPoint := rfl
  set B₁ : Set V := C ∪ IE.subschemeι '' (regularLocus IE.subscheme)ᶜ with hB₁
  have hB₁c : IsClosed B₁ :=
    hC.union (IE.subschemeι.isClosedEmbedding.isClosedMap _ hRE.isClosed_compl)
  have hηB₁ : E.genericPoint ∉ B₁ := by
    rintro (h | ⟨z, hz, hzη⟩)
    · exact hηC h
    · exact hz (by rwa [show z = genericPoint IE.subscheme from
        IE.subschemeι.isClosedEmbedding.injective (hzη.trans hιη.symm)])
  have hηE : E.genericPoint ∈ E.support := MMP.Flips.primeDivisor_genericPoint_mem_support E
  -- a closed point `x` of `E ∖ B₁`
  haveI : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace sV
  obtain ⟨x, ⟨hxE, hxB₁⟩, hxcl⟩ := nonempty_inter_closedPoints (Z := (E.support : Set V) \ B₁)
    ⟨_, hηE, hηB₁⟩ ((IE.support.isClosed.isLocallyClosed).inter hB₁c.isOpen_compl.isLocallyClosed)
  have hxcl' : IsClosed ({x} : Set V) := hxcl
  have hdimx : 2 ≤ ringKrullDim (V.presheaf.stalk x) := by
    rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k V sV x hxcl',
      ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k V sV x]
    exact hdim
  -- local equations at `x`
  obtain ⟨π, hπ, hπE⟩ := MMP.Resolution.Aux.exists_prime_stalk_idealSheaf sV hsm E hxE
  obtain ⟨zx, hzx⟩ : x ∈ Set.range IE.subschemeι := by rwa [IE.range_subschemeι]
  have hzxR : zx ∈ regularLocus IE.subscheme := by
    by_contra h
    exact hxB₁ (Or.inr ⟨zx, h, hzx⟩)
  have hqE : IsRegularLocalRing (V.presheaf.stalk x ⧸ Ideal.span {π}) := by
    have := (mem_regularLocus_subscheme_iff IE zx).1 hzxR
    rw [hzx] at this
    rwa [hπE] at this
  haveI := hregV x
  obtain ⟨m, w, i₀, hw, hwi₀⟩ := exists_isRegularSystemOfParameters_of_prime hπ hqE
  have hm : 2 ≤ m := by
    have h := hw.2
    rw [h] at hdimx
    exact_mod_cast hdimx
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin m, i₁ ≠ i₀ := by
    by_cases h : (⟨0, by omega⟩ : Fin m) = i₀
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h] at h'; simp [Fin.ext_iff] at h'⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  -- the second prime divisor `S`, cut out by `w i₁` at `x`
  let q : PrimeSpectrum (V.presheaf.stalk x) :=
    ⟨Ideal.span {w i₁}, MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw i₁⟩
  have hIq := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk x q
  obtain ⟨S, -, hxS, hSx⟩ := MMP.Resolution.exists_primeDivisor_of_stalk_eq_span sV hsm
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {V.fromSpecStalk x q}))
    (c := Pi.single i₁ 1) hw (by
      rw [hIq]; show Ideal.span {w i₁} = _; congr 1; simp [Pi.single_apply, Finset.prod_ite_eq'])
    (m := i₁) (by simp)
  have hES : E ≠ S := by
    rintro rfl
    rw [hπE, hwi₀] at hSx
    exact hi₁ (MMP.Resolution.span_singleton_injective_of_isRegularSystemOfParameters hw hSx).symm
  -- the regular loci of `S` and of `E ∩ S`
  set IS := S.idealSheaf with hIS
  set IC := IE + IS with hIC
  have hRS : IsOpen (regularLocus IS.subscheme) :=
    MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (IS.subschemeι ≫ sV)
  have hRC : IsOpen (regularLocus IC.subscheme) :=
    MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (IC.subschemeι ≫ sV)
  set Bad : Set V := B₁ ∪ IS.subschemeι '' (regularLocus IS.subscheme)ᶜ ∪
    IC.subschemeι '' (regularLocus IC.subscheme)ᶜ with hBad
  have hBadc : IsClosed Bad :=
    (hB₁c.union (IS.subschemeι.isClosedEmbedding.isClosedMap _ hRS.isClosed_compl)).union
      (IC.subschemeι.isClosedEmbedding.isClosedMap _ hRC.isClosed_compl)
  have hregE : ∀ y ∉ Bad, y ∈ E.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸ IdealSheafData.stalk IE y) := by
    intro y hy hyE
    obtain ⟨z, rfl⟩ : y ∈ Set.range IE.subschemeι := by rwa [IE.range_subschemeι]
    refine (mem_regularLocus_subscheme_iff IE z).1 ?_
    by_contra h
    exact hy (Or.inl (Or.inl (Or.inr ⟨z, h, rfl⟩)))
  have hregS : ∀ y ∉ Bad, y ∈ S.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸ IdealSheafData.stalk IS y) := by
    intro y hy hyS
    obtain ⟨z, rfl⟩ : y ∈ Set.range IS.subschemeι := by rwa [IS.range_subschemeι]
    refine (mem_regularLocus_subscheme_iff IS z).1 ?_
    by_contra h
    exact hy (Or.inl (Or.inr ⟨z, h, rfl⟩))
  have hregC : ∀ y ∉ Bad, y ∈ E.support → y ∈ S.support →
      IsRegularLocalRing (V.presheaf.stalk y ⧸
        (IdealSheafData.stalk IE y ⊔ IdealSheafData.stalk IS y)) := by
    intro y hy hyE hyS
    have hyC : y ∈ (IC.support : Set V) := by
      rw [show IC = IE ⊔ IS from rfl, Scheme.IdealSheafData.support_sup]
      exact ⟨hyE, hyS⟩
    obtain ⟨z, rfl⟩ : y ∈ Set.range IC.subschemeι := by rwa [IC.range_subschemeι]
    rw [← stalk_add]
    refine (mem_regularLocus_subscheme_iff IC z).1 ?_
    by_contra h
    exact hy (Or.inr ⟨z, h, rfl⟩)
  have hxBad : x ∉ Bad := by
    rintro ((h | ⟨z, hz, hzx⟩) | ⟨z, hz, hzx⟩)
    · exact hxB₁ h
    · apply hz
      rw [mem_regularLocus_subscheme_iff, hzx, hSx]
      exact MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters
        hw i₁
    · apply hz
      rw [mem_regularLocus_subscheme_iff, hzx, stalk_add, hπE, hwi₀, hSx]
      have h2 : Ideal.span {w i₀} ⊔ Ideal.span {w i₁} =
          Ideal.span (w '' ↑({i₀, i₁} : Finset (Fin m))) := by
        rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
          Ideal.span_insert]
      rw [h2]
      exact (MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hw _).1
  -- the open `U` and the restrictions of `E` and `S`
  let U : V.Opens := ⟨Badᶜ, hBadc.isOpen_compl⟩
  have hxU : x ∈ U := hxBad
  obtain ⟨A, hA⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι E ⟨x, hxU⟩ hxE
  obtain ⟨S', hS'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    U.ι S ⟨x, hxU⟩ hxS
  have hAS : A ≠ S' := fun h => hES (by rw [← hA, ← hS', h])
  refine ⟨U, A, S', Set.disjoint_left.2 fun y hyU hyC => hyU (Or.inl (Or.inl (Or.inl hyC))), ?_,
    hAS, ⟨⟨x, hxU⟩, ?_, ?_⟩, ?_⟩
  · rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hA]
  · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι A _).1
      (by rwa [hA])
  · exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι S' _).1
      (by rwa [hS'])
  -- the snc condition, checked on `V`
  have hres : (Finsupp.single A (1 : ℤ) + Finsupp.single S' 1 : Divisor U) =
      (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V).restrictOpen U := by
    ext P
    change _ = (Finsupp.single E (1 : ℤ) + Finsupp.single S 1 : Divisor V)
      (OpenWeilRestriction.primeDivisorMap U.ι P)
    have hinj := OpenWeilRestriction.primeDivisorMap_injective U.ι
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.single_apply]
    rw [← hA, ← hS', hinj.eq_iff, hinj.eq_iff]
  rw [hres]
  refine ⟨fun P hP => ?_, fun v => ?_⟩
  · have h0 := Finsupp.mem_support_iff.1 hP
    rw [DivisorWithCoeffs.restrictOpen, Finsupp.comapDomain_apply] at h0
    have hP' : OpenWeilRestriction.primeDivisorMap U.ι P = E ∨
        OpenWeilRestriction.primeDivisorMap U.ι P = S :=
      (mem_support_single_add_single_iff hES _).1 (Finsupp.mem_support_iff.2 h0)
    have key : ∀ I : V.IdealSheafData, I.comap U.ι = P.idealSheaf →
        (∀ y ∉ Bad, y ∈ I.support → IsRegularLocalRing (V.presheaf.stalk y ⧸
          IdealSheafData.stalk I y)) →
        IsSmoothScheme (P.idealSheaf.subschemeι ≫ U.ι ≫ sV) := by
      intro I hI hreg
      haveI : LocallyOfFinitePresentation (I.subschemeι ≫ sV) :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := I.subschemeι ≫ sV)).mpr
          inferInstance
      refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sV I _ hI).2
        fun z hz => ?_
      obtain ⟨u, hu⟩ := hz
      refine mem_smoothLocus_of_isRegularLocalRing' (I.subschemeι ≫ sV) z ?_
      refine (mem_regularLocus_subscheme_iff I z).2 (hreg _ (hu ▸ u.2) ?_)
      rw [← SetLike.mem_coe, ← I.range_subschemeι]; exact ⟨z, rfl⟩
    rcases hP' with h | h
    · exact key IE (by rw [hIE, ← h]; exact
        MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι P) hregE
    · exact key IS (by rw [hIS, ← h]; exact
        MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι P) hregS
  · exact (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι _ v).2
      (sncStalk_single_add_single sV hsm hES (U.ι v) (hregE _ v.2) (hregS _ v.2) (hregC _ v.2))

/-! ### One blow-up of a stratum of an snc divisor -/

/-- The blow-up step, from the data provided by `MMP.Resolution.blowUp_snc_stratum` for a
component `Wc` of `a ∩ b`. -/
private theorem exists_blowUp_step_of_data {W : Scheme.{v}} (sW : W ⟶ Spec (.of k))
    (hW : IsNormalVariety k sW) (hsm : IsSmoothScheme sW) [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {n : ℕ} {KW : Divisor W} (hK : KW.IsCanonicalDivisor sW n)
    (T : Finset (MMP.Mori.PrimeDivisor W))
    (hT : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).IsSNC sW)
    (ΔW : QDivisor W) (hΔ : ∀ P, ΔW.coeff P ≠ 0 → P ∈ T)
    {a b : MMP.Mori.PrimeDivisor W} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
    (I : W.IdealSheafData) (Wc : Set W) (hWcne : Wc.Nonempty) (hWcirr : IsIrreducible Wc)
    (hWcab : Wc ⊆ (a.support : Set W) ∩ b.support)
    (hIvan : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Wc))
    (hsuppI : (I.support : Set W) = closure Wc)
    (hcodim : closedsCodimension (Closeds.closure Wc) = 2)
    (hZsm : IsSmoothScheme (I.subschemeι ≫ sW)) (hBsm : IsSmoothScheme (blowUpToBase I ≫ sW))
    (hiso : IsIso (blowUpToBase I ∣_ I.support.compl))
    (E : MMP.Mori.PrimeDivisor (blowUp I)) (S' : T → MMP.Mori.PrimeDivisor (blowUp I))
    (hEI : E.idealSheaf = I.comap (blowUpToBase I))
    (hS'tr : ∀ j : T, inverseTransformPrimeDivisor (blowUpToBase I) j.1 = some (S' j))
    (hS'inj : Function.Injective S') (hS'E : ∀ j, S' j ≠ E)
    (hsnc' : DivisorWithCoeffs.IsSNC (blowUpToBase I ≫ sW)
      (Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ) : Divisor (blowUp I)))
    (himga : blowUpToBase I '' ((S' ⟨a, ha⟩).support ∩ E.support) = Wc) :
    ∃ (W' : Scheme.{v}) (q : W' ⟶ W) (hW' : IsNormalVariety k (q ≫ sW))
      (hq : IsBirationalMorphism q),
      IsSmoothScheme (q ≫ sW) ∧ topologicalKrullDim W' = topologicalKrullDim W ∧
      ∃ (T' : Finset (MMP.Mori.PrimeDivisor W')) (Δ' : QDivisor W')
        (a' e : MMP.Mori.PrimeDivisor W'),
        (∑ P ∈ T', Finsupp.single P (1 : ℤ) : Divisor W').IsSNC (q ≫ sW) ∧
        (∀ P, Δ'.coeff P ≠ 0 → P ∈ T') ∧ a' ∈ T' ∧ e ∈ T' ∧ a' ≠ e ∧
        ((a'.support : Set W') ∩ e.support).Nonempty ∧
        IsCrepantBoundary sW n KW ΔW q hW' hq Δ' ∧
        Δ'.coeff a' = ΔW.coeff a ∧ Δ'.coeff e = ΔW.coeff a + ΔW.coeff b - 1 ∧
        q '' (e.support : Set W') ⊆ (a.support : Set W) ∩ b.support := by
  classical
  haveI := hW.1
  haveI : Smooth sW := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsm
  let S : T → MMP.Mori.PrimeDivisor W := Subtype.val
  let ja : T := ⟨a, ha⟩
  let p := blowUpToBase I
  have hIab : (I.support : Set W) ⊆ (a.support : Set W) ∩ b.support := by
    rw [hsuppI]
    exact closure_minimal hWcab (a.idealSheaf.support.isClosed.inter b.idealSheaf.support.isClosed)
  have hirr : IsIrreducible (I.support : Set W) := by rw [hsuppI]; exact hWcirr.closure
  set Z : IrreducibleCloseds W := ⟨I.support, hirr, I.support.isClosed⟩ with hZdef
  have hcodimZ : codimension Z = 2 := by
    rw [← closedsCodimension_coe Z]
    have : (⟨(Z : Set W), Z.isClosed⟩ : Closeds W) = Closeds.closure Wc := by
      ext1; exact hsuppI
    rw [this, hcodim]
  have hc1 : 1 ≤ codimension Z := by rw [hcodimZ]; norm_num
  haveI : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have hq : IsBirationalMorphism p :=
    MMP.Threefold.Resolution.isBirationalMorphism_blowUpToBase I hirr hc1
  have hI0 : I ≠ ⊥ := MMP.Threefold.Resolution.ne_bot_of_one_le_codimension I hirr hc1
  have hW' : IsNormalVariety k (p ≫ sW) :=
    ⟨(MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sW I hI0).1,
      (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBsm).2⟩
  have hdimB : topologicalKrullDim (blowUp I) = topologicalKrullDim W := by
    rw [hK.topologicalKrullDim_eq]
    exact MMP.Threefold.Resolution.topologicalKrullDim_blowUp sW I ⟨hsm, hZsm⟩ hirr hc1
      hK.topologicalKrullDim_eq
  -- the new snc divisor and the candidate crepant boundary
  let T' : Finset (MMP.Mori.PrimeDivisor (blowUp I)) := insert E (Finset.univ.image S')
  let Δ' : QDivisor (blowUp I) := Finsupp.single E (ΔW.coeff a + ΔW.coeff b - 1) +
    ∑ j, Finsupp.single (S' j) (ΔW.coeff (S j))
  have hEimg : E ∉ Finset.univ.image S' := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun j h => hS'E j h
  have hcoeff_S' : ∀ j, Δ'.coeff (S' j) = ΔW.coeff (S j) := fun j => by
    simp only [Δ', DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
    rw [if_neg (hS'E j).symm, zero_add, Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro i _ hij
      rw [if_neg (fun h => hij (hS'inj h))]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hcoeff_E : Δ'.coeff E = ΔW.coeff a + ΔW.coeff b - 1 := by
    simp only [Δ', DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, if_true, hS'E, if_false, Finset.sum_const_zero, add_zero]
  have hcoeff_other : ∀ F, F ≠ E → (∀ j, F ≠ S' j) → Δ'.coeff F = 0 := fun F hFE hFS => by
    simp only [Δ', DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
    rw [if_neg (Ne.symm hFE), Finset.sum_eq_zero fun j _ => if_neg (Ne.symm (hFS j)), add_zero]
  have hEsupp : (E.support : Set (blowUp I)) = p ⁻¹' I.support := by
    change ((E.idealSheaf).support : Set (blowUp I)) = _
    rw [hEI, Scheme.IdealSheafData.support_comap]
    rfl
  refine ⟨blowUp I, p, hW', hq, hBsm, hdimB, T', Δ', S' ja, E, ?_, ?_, ?_, ?_, hS'E ja, ?_, ?_,
    by rw [hcoeff_S'], hcoeff_E, ?_⟩
  · -- snc
    have : (∑ P ∈ T', Finsupp.single P (1 : ℤ) : Divisor (blowUp I)) =
        Finsupp.single E (1 : ℤ) + ∑ j, Finsupp.single (S' j) (1 : ℤ) := by
      rw [Finset.sum_insert hEimg, Finset.sum_image fun i _ j _ h => hS'inj h]
    rw [this]
    exact hsnc'
  · intro F hF
    by_contra hFT
    refine hF (hcoeff_other F (fun h => hFT (h ▸ Finset.mem_insert_self _ _)) fun j h => hFT ?_)
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ ja))
  · exact Finset.mem_insert_self _ _
  · -- `a' ∩ e ≠ ∅`
    obtain ⟨w₀, hw₀Wc⟩ := hWcne
    have hw : w₀ ∈ p '' ((S' ja).support ∩ E.support) := by rwa [himga]
    obtain ⟨y, hy, -⟩ := hw
    exact ⟨y, hy⟩
  · -- the crepant boundary
    have hPW : IsPairWith sW n KW ΔW :=
      ⟨hW, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩
    have hdisc_of_val : ∀ (D D' : DivisorOver k sW) (c : ℚ), D.valuation = D'.valuation →
        IsDiscrepancy sW n KW ΔW D' c → IsDiscrepancy sW n KW ΔW D c := by
      intro D D' c hv hc
      obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK D
      rwa [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hv hc₀ hc] at hc₀
    haveI : IsLocallyNoetherian (blowUp I) :=
      (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBsm).1
    haveI : IsNormal (blowUp I) :=
      (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBsm).2
    intro F
    rcases eq_or_ne F E with rfl | hFE
    · -- the exceptional divisor
      let Z' : IrreducibleCloseds W := ⟨closure Wc, hWcirr.closure, isClosed_closure⟩
      have hZ'Z : Z' = Z := IrreducibleCloseds.ext hsuppI.symm
      have hEmem : F.genericPoint ∈ F.support := MMP.Flips.primeDivisor_genericPoint_mem_support F
      have hpE1 : p '' (F.support : Set (blowUp I)) ⊆ closure Wc := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← hsuppI]
        exact (hEsupp ▸ hy : y ∈ p ⁻¹' I.support)
      have hgen : IsGenericPoint (p F.genericPoint) (closure Wc) := by
        refine subset_antisymm (closure_minimal (Set.singleton_subset_iff.2
          (hpE1 ⟨_, hEmem, rfl⟩)) isClosed_closure) (closure_minimal ?_ isClosed_closure)
        rw [← himga]
        rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
        have hy' : y ∈ closure {F.genericPoint} := by
          rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact map_mem_closure p.continuous hy' (Set.mapsTo_singleton.2 rfl)
      have hζgen : IsGenericPoint Z'.isIrreducible.genericPoint (closure Wc) := by
        have := Z'.isIrreducible.isGenericPoint_genericPoint_closure
        rwa [Z'.isClosed.closure_eq] at this
      have hpE : p F.genericPoint = Z'.isIrreducible.genericPoint := hgen.eq hζgen
      set ζ := Z'.isIrreducible.genericPoint with hζdef
      have hζab : ζ ∈ (a.support : Set W) ∩ b.support := hIab (hsuppI ▸ hζgen.mem)
      have hcohζ : Order.coheight ζ = 2 := by
        rw [← MMP.Flips.codimension_closureSingleton]
        have : IrreducibleCloseds.closureSingleton ζ = Z := by
          ext1
          rw [IrreducibleCloseds.coe_closureSingleton]
          exact hζgen.trans hsuppI.symm
        rw [this, hcodimZ]
      obtain ⟨m, z, jj, hz, hjj, hIz⟩ := hT.2 ζ
      have hm : m = 2 := by
        have h := hz.2
        rw [ringKrullDim_stalk_eq_coheight, hcohζ] at h
        exact_mod_cast h.symm
      have hmemT : ∀ Γ ∈ T, Γ ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).support := by
        intro Γ hΓ
        simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hΓ]
      have hmult : ∀ Γ ∈ ΔW.support, ((Γ.multiplicityAlong Z').toNat : ℚ) =
          (if Γ = a then 1 else 0) + (if Γ = b then 1 else 0) := by
        intro Γ hΓ
        have hΓT : Γ ∈ T := hΔ Γ (Finsupp.mem_support_iff.1 hΓ)
        by_cases hζΓ : ζ ∈ Γ.support
        · have h1 : Γ.multiplicityAlong Z' = 1 :=
            multiplicityAlong_eq_one Γ Z' hz (jj ⟨Γ, hmemT Γ hΓT, hζΓ⟩) (hIz ⟨Γ, hmemT Γ hΓT, hζΓ⟩)
          rw [h1]
          by_cases hΓa : Γ = a
          · subst hΓa; simp [hab]
          by_cases hΓb : Γ = b
          · subst hΓb; simp [hΓa]
          exfalso
          let A : {E : MMP.Mori.PrimeDivisor W //
            E ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).support ∧ ζ ∈ E.support} :=
            ⟨a, hmemT a ha, hζab.1⟩
          let B : {E : MMP.Mori.PrimeDivisor W //
            E ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).support ∧ ζ ∈ E.support} :=
            ⟨b, hmemT b hb, hζab.2⟩
          let C : {E : MMP.Mori.PrimeDivisor W //
            E ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).support ∧ ζ ∈ E.support} :=
            ⟨Γ, hmemT Γ hΓT, hζΓ⟩
          have hAB : jj A ≠ jj B := fun h => hab (congrArg Subtype.val (hjj h))
          have hAC : jj A ≠ jj C := fun h => hΓa (congrArg Subtype.val (hjj h)).symm
          have hBC : jj B ≠ jj C := fun h => hΓb (congrArg Subtype.val (hjj h)).symm
          have h1 := (jj A).isLt
          have h2 := (jj B).isLt
          have h3 := (jj C).isLt
          have hAB' := Fin.val_ne_of_ne hAB
          have hAC' := Fin.val_ne_of_ne hAC
          have hBC' := Fin.val_ne_of_ne hBC
          omega
        · rw [multiplicityAlong_eq_zero Γ Z' hζΓ]
          have hΓa : Γ ≠ a := fun h => hζΓ (h ▸ hζab.1)
          have hΓb : Γ ≠ b := fun h => hζΓ (h ▸ hζab.2)
          simp [hΓa, hΓb]
      have hsum : (ΔW.sum fun Γ c => c * ((Γ.multiplicityAlong Z').toNat : ℚ)) =
          ΔW.coeff a + ΔW.coeff b := by
        calc (ΔW.sum fun Γ c => c * ((Γ.multiplicityAlong Z').toNat : ℚ))
            = ΔW.sum (fun Γ c => (if Γ = a then c else 0) + (if Γ = b then c else 0)) :=
              Finsupp.sum_congr fun Γ hΓ => by rw [hmult Γ hΓ]; split_ifs <;> ring
          _ = ΔW.coeff a + ΔW.coeff b := by
              rw [Finsupp.sum_add, Finsupp.sum_ite_self_eq', Finsupp.sum_ite_self_eq']; rfl
      have hcZ' : ((2 : ℕ) : ℕ∞) = codimension Z' := by rw [hZ'Z, hcodimZ]; rfl
      obtain ⟨j, hjo, hj⟩ := exists_openImmersion_stacksBlowUp (X := W) (I := I)
        (J := Scheme.IdealSheafData.vanishingIdeal ⟨(Z' : Set W), Z'.isClosed⟩) hIvan
      obtain ⟨-, hdisc⟩ := MMP.Mori.isDiscrepancy_blowUp sW hW.1 hK ΔW Z' hcZ' le_rfl
        (⟨blowUp I, p, hW', hq, F⟩ : DivisorOver k sW) j hj hpE
      convert hdisc using 1
      rw [hcoeff_E, hsum]
      push_cast
      ring
    · -- a prime divisor other than the exceptional divisor
      have hηF : F.genericPoint ∉ E.support :=
        MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne hFE
      have hxI : p F.genericPoint ∉ (I.support : Set W) := fun h => hηF (hEsupp ▸ h)
      have hxV : p F.genericPoint ∈ biregularLocus p := le_biregularLocus hiso hxI
      have hcoh : Order.coheight (p F.genericPoint) = 1 :=
        (MMP.Positivity.coheight_map_of_mem_biregularLocus p hxV).trans F.coheight_genericPoint
      set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh with hGdef
      have hG : G.genericPoint = p F.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
      have hval := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hW
        (⟨blowUp I, p, hW', hq, F⟩ : DivisorOver k sW) G hG.symm
      obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK
        (DivisorOver.ofPrimeDivisor k hW G)
      have hcG := hc.eq_neg_coeff_of_ofPrimeDivisor hW
      have hdF := hdisc_of_val _ _ c hval hc
      suffices hFG : Δ'.coeff F = ΔW.coeff G by rwa [hFG, ← hcG]
      by_cases hFS : ∃ j, F = S' j
      · obtain ⟨j, rfl⟩ := hFS
        rw [hcoeff_S']
        have h1 :=
          (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          (hS'tr j)).1
        have : G = S j := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG.trans h1)
        rw [this]
      · push Not at hFS
        rw [hcoeff_other F hFE hFS]
        by_contra hne
        have hGT : G ∈ T := hΔ G (Ne.symm hne)
        obtain ⟨h1, h2⟩ :=
          MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
            (hS'tr ⟨G, hGT⟩)
        have h3 : p (S' ⟨G, hGT⟩).genericPoint = p F.genericPoint := h1.trans hG
        exact hFS ⟨G, hGT⟩ (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_map_eq_of_mem_biregularLocus h3 h2)).symm
  · -- `e` lies over `a ∩ b`
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ p ⁻¹' I.support := hEsupp ▸ hy
    exact hIab this

/-- **One blow-up.** Let `W` be a smooth variety of dimension `n` with canonical divisor `K_W`,
`∑_{P ∈ T} P` an snc divisor, `Δ_W` a `ℚ`-divisor supported on `T` and `a ≠ b` two meeting
components. Blowing up a component `Z` of `a ∩ b` gives a smooth variety `W'` with an snc divisor
`∑_{P ∈ T'} P` containing the support of the crepant boundary `Δ'` of `(W, Δ_W)`, the birational
transform `a'` of `a` and the exceptional divisor `e`, with `a' ∩ e ≠ ∅`, `coeff_{a'} Δ' =
coeff_a Δ_W` and `coeff_e Δ' = coeff_a Δ_W + coeff_b Δ_W - 1`; and `e` lies over `a ∩ b`. -/
private theorem exists_blowUp_step {W : Scheme.{v}} (sW : W ⟶ Spec (.of k))
    (hW : IsNormalVariety k sW) (hsm : IsSmoothScheme sW) [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {n : ℕ} {KW : Divisor W} (hK : KW.IsCanonicalDivisor sW n)
    (T : Finset (MMP.Mori.PrimeDivisor W))
    (hT : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).IsSNC sW)
    (ΔW : QDivisor W) (hΔ : ∀ P, ΔW.coeff P ≠ 0 → P ∈ T)
    {a b : MMP.Mori.PrimeDivisor W} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b)
    (hne : ((a.support : Set W) ∩ b.support).Nonempty) :
    ∃ (W' : Scheme.{v}) (q : W' ⟶ W) (hW' : IsNormalVariety k (q ≫ sW))
      (hq : IsBirationalMorphism q),
      IsSmoothScheme (q ≫ sW) ∧ topologicalKrullDim W' = topologicalKrullDim W ∧
      ∃ (T' : Finset (MMP.Mori.PrimeDivisor W')) (Δ' : QDivisor W')
        (a' e : MMP.Mori.PrimeDivisor W'),
        (∑ P ∈ T', Finsupp.single P (1 : ℤ) : Divisor W').IsSNC (q ≫ sW) ∧
        (∀ P, Δ'.coeff P ≠ 0 → P ∈ T') ∧ a' ∈ T' ∧ e ∈ T' ∧ a' ≠ e ∧
        ((a'.support : Set W') ∩ e.support).Nonempty ∧
        IsCrepantBoundary sW n KW ΔW q hW' hq Δ' ∧
        Δ'.coeff a' = ΔW.coeff a ∧ Δ'.coeff e = ΔW.coeff a + ΔW.coeff b - 1 ∧
        q '' (e.support : Set W') ⊆ (a.support : Set W) ∩ b.support := by
  classical
  let S : T → MMP.Mori.PrimeDivisor W := Subtype.val
  have hS : Function.Injective S := Subtype.val_injective
  have hSNC : (∑ j, Finsupp.single (S j) (1 : ℤ) : Divisor W).IsSNC sW := by
    rwa [Finset.sum_coe_sort T (fun P => Finsupp.single P (1 : ℤ))]
  let ja : T := ⟨a, ha⟩
  let jb : T := ⟨b, hb⟩
  let J : Finset T := {ja, jb}
  have hjab : ja ≠ jb := fun h => hab (congrArg Subtype.val h)
  have hJ : J.card = 2 := Finset.card_pair hjab
  have hinter : (⋂ j ∈ J, ((S j).support : Set W)) = (a.support : Set W) ∩ b.support := by
    simp [J, S, ja, jb]
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨Wc, hWc, hw₀Wc⟩ := MMP.Resolution.exists_mem_componentsOf
    (D := ⋂ j ∈ J, ((S j).support : Set W)) (hinter ▸ hw₀)
  obtain ⟨hZsm, hcodim, hBsm, hiso, E, S', hEI, -, hS'tr, hS'inj, hS'E, hsnc', himg, -⟩ :=
    MMP.Resolution.blowUp_snc_stratum sW hW.1 hsm S hS hSNC J hJ.ge ⟨Wc, hWc⟩
  refine exists_blowUp_step_of_data sW hW hsm hK T hT ΔW hΔ ha hb hab _ Wc ⟨w₀, hw₀Wc⟩ hWc.1.1
    (hinter ▸ hWc.1.2) rfl ?_ (by rw [hcodim, hJ]; rfl) hZsm hBsm hiso E S' hEI hS'tr hS'inj hS'E
    hsnc' (himg ja (by simp [J]))
  change ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure Wc)).support : Set W) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

/-! ### Open subschemes -/

/-- The smooth locus of a scheme over `k` is smooth over `k`. -/
private theorem isSmoothScheme_smoothLocus {Y : Scheme.{v}} (s : Y ⟶ Spec (.of k)) :
    IsSmoothScheme ((smoothLocus s).ι ≫ s) := by
  rw [IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  refine mem_smoothLocus_iff.2 ⟨(smoothLocus s).ι ⁻¹ᵁ W, hxW, ?_⟩
  have : Smooth (W.ι ≫ s) := hW
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{v}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion' {W Y : Scheme.{v}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

section Stage

variable {X : Scheme.{v}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The `j`-th stage of the construction: a smooth model `W` of `X` of dimension `n` with an snc
divisor `∑_{P ∈ T} P` containing the support of the crepant boundary `Δ_W` of `(X, Δ)`, and two
meeting components `a`, `b` with coefficients `1 + γ` and `j γ`, whose intersection lies over
points of codimension at least two of `X`. -/
private def Stage (sX : X ⟶ Spec (.of k)) (n : ℕ) (K : Divisor X) (Δ : QDivisor X) (γ : ℚ)
    (j : ℕ) : Prop :=
  ∃ (W : Scheme.{v}) (g : W ⟶ X) (hW : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g),
    IsSmoothScheme (g ≫ sX) ∧ topologicalKrullDim W = n ∧
    ∃ (T : Finset (MMP.Mori.PrimeDivisor W)) (ΔW : QDivisor W) (a b : MMP.Mori.PrimeDivisor W),
      (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor W).IsSNC (g ≫ sX) ∧
      (∀ P, ΔW.coeff P ≠ 0 → P ∈ T) ∧ a ∈ T ∧ b ∈ T ∧ a ≠ b ∧
      ((a.support : Set W) ∩ b.support).Nonempty ∧
      IsCrepantBoundary sX n K Δ g hW hg ΔW ∧
      ΔW.coeff a = 1 + γ ∧ ΔW.coeff b = j * γ ∧
      (∀ w ∈ (a.support : Set W) ∩ b.support, 2 ≤ Order.coheight (g w)) ∧
      (j ≠ 0 → 2 ≤ Order.coheight (g b.genericPoint))

/-- A divisor over a normal variety is exceptional exactly when its generic point maps to a point
of coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- At a stage `j ≥ 1`, the divisor `b` is exceptional over `X` with discrepancy `-j γ`, so
`discrep(X, Δ) ≤ -j γ`. -/
private theorem discrep_le_of_stage {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hX : IsNormalVariety k sX) {γ : ℚ} {j : ℕ} (hj : j ≠ 0)
    (h : Stage sX n K Δ γ j) : discrep sX n K Δ ≤ (((-(j * γ) : ℚ) : ℝ) : EReal) := by
  obtain ⟨W, g, hW, hg, -, -, T, ΔW, a, b, -, -, -, -, -, -, hcr, -, hb, -, hgb⟩ := h
  simpa [hb] using discrep_le ((isExceptional_iff_two_le_coheight hX
    (⟨W, g, hW, hg, b⟩ : DivisorOver k sX)).2 (hgb hj)) (hcr b)

/-- The inductive step: blowing up a component of `a ∩ b` passes from stage `j` to `j + 1`. -/
private theorem stage_succ {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) {γ : ℚ} {j : ℕ} (h : Stage sX n K Δ γ j) :
    Stage sX n K Δ γ (j + 1) := by
  obtain ⟨W, g, hW, hg, hsm, hdim, T, ΔW, a, b, hT, hΔ, ha, hb, hab, hne, hcr, hca, hcb, hco,
    -⟩ := h
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI := hW.1
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : IsDominant g := hg.isDominant
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  obtain ⟨KW, hKW⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX) hsm hdim
  obtain ⟨W', q, hW', hq, hsm', hdim', T', Δ', a', e, hT', hΔ', ha', he', hae, hne', hcr',
    hca', hce, himg⟩ := exists_blowUp_step (g ≫ sX) hW hsm hKW T hT ΔW hΔ ha hb hab hne
  haveI : IsIntegral W' := hW'.1.toIsIntegral
  haveI : IsDominant q := hq.isDominant
  have hW'' : IsNormalVariety k ((q ≫ g) ≫ sX) := by rwa [Category.assoc]
  have hg'' : IsBirationalMorphism (q ≫ g) :=
    MMP.Mori.IsPair.isBirationalMorphism_comp hq hg
  have hcrep := (MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP.isPair g hW hg hP.2.1 hKW
    (Or.inl hcr)).2
  refine ⟨W', q ≫ g, hW'', hg'', by rw [Category.assoc]; exact hsm', hdim'.trans hdim, T', Δ',
    a', e, by rw [Category.assoc]; exact hT', hΔ', ha', he', hae, hne', fun F => ?_,
    by rw [hca', hca], by rw [hce, hca, hcb]; push_cast; ring, ?_, fun _ => ?_⟩
  · refine (hcrep ⟨W', q, hW', hq, F⟩ ⟨W', q ≫ g, hW'', hg'', F⟩ ?_ _).1 (hcr' F)
    haveI : IsDominant (q ≫ g) := hg''.isDominant
    haveI : IsNormal W' := hW'.2
    haveI := hW'.1
    haveI : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (q ≫ g ≫ sX)
    ext t
    change F.divisorialValuation (functionFieldMap (q ≫ g) t) =
      F.divisorialValuation (functionFieldMap q (functionFieldMap g t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · rintro w ⟨-, hw⟩
    exact hco _ (himg ⟨w, hw, rfl⟩)
  · exact hco _ (himg ⟨e.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support e, rfl⟩)

/-- **The start of the construction.** Let `(Y, f, E)` be a divisor over `X` with
`a(E, X, Δ) = -1 - γ`, all of whose points other than the generic one lie over points of
codimension at least two of `X`. A smooth open `W` of `Y` meeting `E`, avoiding the other
components of the crepant boundary of `(X, Δ)` on `Y`, and carrying a prime divisor `S` crossing
`E ∩ W` normally, is a stage `0`. -/
private theorem stage_zero_of_divisorOver {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPairWith sX n K Δ) (hn : 2 ≤ n) (D : DivisorOver k sX) {γ : ℚ}
    (hD : IsDiscrepancy sX n K Δ D (-1 - γ))
    (hCH : ∀ y ∈ D.E.support, y ≠ D.E.genericPoint → 2 ≤ Order.coheight (D.f y)) :
    Stage sX n K Δ γ 0 := by
  classical
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isNormalVariety.1
  haveI : IsDominant D.f := D.isDominant
  haveI := hP.1.1
  obtain ⟨⟨ΔY, hcr, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hP.isPair hP.2.1
    D.f D.isNormalVariety D.isBirationalMorphism
  have hΔE : ΔY.coeff D.E = 1 + γ := by
    have h := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP rfl hD (hcr D.E)
    linarith
  -- the smooth locus `V` of `Y`
  set V := smoothLocus (D.f ≫ sX) with hVdef
  have hηV : D.E.genericPoint ∈ V :=
    MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus D.isNormalVariety D.E
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  have hVn : IsNormalVariety k (V.ι ≫ D.f ≫ sX) := isNormalVariety_ι D.isNormalVariety V
  have hVsm : IsSmoothScheme (V.ι ≫ D.f ≫ sX) := isSmoothScheme_smoothLocus _
  haveI : IsIntegral V := hVn.1.toIsIntegral
  haveI := hVn.1
  have hVb : IsBirationalMorphism (V.ι ≫ D.f) :=
    MMP.Mori.IsPair.isBirationalMorphism_comp (isBirationalMorphism_of_isOpenImmersion' V.ι)
      D.isBirationalMorphism
  have hdimV : topologicalKrullDim V = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX
      (V.ι ≫ D.f ≫ sX) hVb]
    exact hP.2.1.topologicalKrullDim_eq
  have hηE : D.E.genericPoint ∈ D.E.support := MMP.Flips.primeDivisor_genericPoint_mem_support D.E
  obtain ⟨EV, hEV⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι D.E ⟨_, hηV⟩ hηE
  have hEVη : V.ι EV.genericPoint = D.E.genericPoint := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, hEV]
  -- the other components of the crepant boundary
  set B : Set D.Y := ⋃ G ∈ ΔY.support.erase D.E, (G.support : Set D.Y) with hB
  have hBc : IsClosed B :=
    (Finset.finite_toSet _).isClosed_biUnion fun G _ => G.idealSheaf.support.isClosed
  have hηC : EV.genericPoint ∉ V.ι ⁻¹' B := by
    intro h
    rw [Set.mem_preimage, hEVη] at h
    obtain ⟨G, hG, hηG⟩ := Set.mem_iUnion₂.1 h
    exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne
      (Finset.ne_of_mem_erase hG).symm hηG
  obtain ⟨U, A, S, hUC, hAη, hAS, hne, hsnc⟩ := exists_open_snc_pair (V.ι ≫ D.f ≫ sX) hVn hVsm
    (by rw [hdimV]; exact_mod_cast hn) EV (V.ι ⁻¹' B) (hBc.preimage V.ι.continuous) hηC
  -- the model `W = U`
  obtain ⟨u₀, hu₀⟩ := hne
  haveI : Nonempty U := ⟨u₀⟩
  set j : U.toScheme ⟶ D.Y := U.ι ≫ V.ι with hjdef
  have hWU : IsNormalVariety k (U.ι ≫ V.ι ≫ D.f ≫ sX) := isNormalVariety_ι hVn U
  have hW : IsNormalVariety k ((j ≫ D.f) ≫ sX) := by
    simpa only [hjdef, Category.assoc] using hWU
  have hWj : IsNormalVariety k (j ≫ D.f ≫ sX) := by
    simpa only [hjdef, Category.assoc] using hWU
  haveI : IsIntegral U := hWU.1.toIsIntegral
  haveI := hWU.1
  haveI : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ V.ι ≫ D.f ≫ sX)
  haveI : IsNormal U := hWU.2
  have hj : IsBirationalMorphism j := isBirationalMorphism_of_isOpenImmersion' j
  have hg : IsBirationalMorphism (j ≫ D.f) :=
    MMP.Mori.IsPair.isBirationalMorphism_comp hj D.isBirationalMorphism
  have hjA : j A.genericPoint = D.E.genericPoint := by
    rw [hjdef, Scheme.Hom.comp_apply, hAη, hEVη]
  have hjinj : Function.Injective j := j.isOpenEmbedding.injective
  refine ⟨U, j ≫ D.f, hW, hg, ?_, ?_, {A, S}, Finsupp.single A (1 + γ), A, S, ?_, ?_, by simp,
    by simp, hAS, ⟨u₀, hu₀⟩, ?_, by simp [DivisorWithCoeffs.coeff_apply], ?_, ?_,
    fun h => absurd rfl h⟩
  · simpa only [hjdef, Category.assoc] using
      MMP.Threefold.Resolution.isSmoothScheme_ι (k := k) hVsm U
  · haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX ((j ≫ D.f) ≫ sX) hg]
    exact hP.2.1.topologicalKrullDim_eq
  · rw [Finset.sum_pair hAS]
    simpa only [hjdef, Category.assoc] using hsnc
  · intro P hP'
    by_contra hPT
    apply hP'
    have hPA : P ≠ A := fun h => hPT (h ▸ Finset.mem_insert_self _ _)
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hPA]
  · -- the crepant boundary
    intro F
    have hcohF : Order.coheight (j F.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion]; exact F.coheight_genericPoint
    set FY := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcohF with hFYdef
    have hFY : FY.genericPoint = j F.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcohF
    have hval1 := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq D.isNormalVariety
      (⟨U, j, hWj, hj, F⟩ : DivisorOver k (D.f ≫ sX)) FY hFY.symm
    have hval : (⟨U, j ≫ D.f, hW, hg, F⟩ : DivisorOver k sX).valuation =
        (⟨D.Y, D.f, D.isNormalVariety, D.isBirationalMorphism, FY⟩ :
          DivisorOver k sX).valuation := by
      haveI : IsDominant j := hj.isDominant
      haveI : IsDominant (j ≫ D.f) := hg.isDominant
      ext t
      have h1 := congrArg (fun v => v (functionFieldMap D.f t)) hval1
      change F.divisorialValuation (functionFieldMap j (functionFieldMap D.f t)) =
        MMP.Mori.PrimeDivisor.divisorialValuation FY
          (functionFieldMap (𝟙 D.Y) (functionFieldMap D.f t)) at h1
      rw [MMP.Mori.functionFieldMap_id_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at h1
      exact h1
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
      (⟨U, j ≫ D.f, hW, hg, F⟩ : DivisorOver k sX)
    have hcF := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hval hc (hcr FY)
    rw [hcF] at hc
    convert hc using 2
    by_cases hFA : F = A
    · subst hFA
      have : FY = D.E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hFY.trans hjA)
      rw [this, hΔE]
      simp [DivisorWithCoeffs.coeff_apply]
    · rw [show DivisorWithCoeffs.coeff (Finsupp.single A (1 + γ) : QDivisor U) F = 0 by
        simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hFA]]
      by_contra hne'
      have hFYE : FY ≠ D.E := fun h => hFA (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (hjinj ((hFY.symm.trans (congrArg _ h)).trans hjA.symm)))
      have hmem : FY ∈ ΔY.support.erase D.E :=
        Finset.mem_erase.2 ⟨hFYE, Finsupp.mem_support_iff.2 (Ne.symm hne')⟩
      have hjF : j F.genericPoint ∈ B :=
        Set.mem_iUnion₂.2 ⟨FY, hmem, hFY ▸ MMP.Flips.primeDivisor_genericPoint_mem_support FY⟩
      have hFU : U.ι F.genericPoint ∈ (U : Set V) := by
        have : U.ι F.genericPoint ∈ Set.range U.ι := ⟨_, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      exact Set.disjoint_left.1 hUC hFU hjF
  · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hAS]
  · rintro w ⟨hwA, hwS⟩
    have hjw : j w ∈ D.E.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwA ⊢
      have hsp : j A.genericPoint ⤳ j w :=
        (specializes_iff_mem_closure.2 hwA).map j.continuous
      rw [hjA] at hsp
      exact specializes_iff_mem_closure.1 hsp
    have hjw' : j w ≠ D.E.genericPoint := by
      intro h
      have hw : w = A.genericPoint := hjinj (h.trans hjA.symm)
      exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne hAS (hw ▸ hwS)
    have := hCH (j w) hjw hjw'
    rwa [Scheme.Hom.comp_apply]

/-- The start of the construction, from a divisor of total discrepancy `< -1`. -/
private theorem exists_stage_zero {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPairWith sX n K Δ) (hn : 2 ≤ n)
    (htot : totalDiscrep sX n K Δ < -1) : ∃ γ : ℚ, 0 < γ ∧ Stage sX n K Δ γ 0 := by
  obtain ⟨_, ⟨D, a, hD, ha, rfl⟩, hlt⟩ := sInf_lt_iff.1 htot
  have ha1 : a < -1 := by
    have : ((a : ℝ) : EReal) < ((-1 : ℝ) : EReal) := by simpa using hlt
    exact_mod_cast EReal.coe_lt_coe_iff.1 this
  refine ⟨-1 - a, by linarith,
    stage_zero_of_divisorOver hP hn D (by rwa [show -1 - (-1 - a) = a by ring]) ?_⟩
  rcases hD with hexc | ⟨hX, P, rfl⟩
  · have h2 := (isExceptional_iff_two_le_coheight hP.1 D).1 hexc
    intro y hy _
    have hsp : D.E.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact specializes_iff_mem_closure.2 hy
    exact h2.trans (Order.coheight_anti (Scheme.le_iff_specializes.2 (hsp.map D.f.continuous)))
  · show ∀ y : X, y ∈ P.support → y ≠ P.genericPoint → 2 ≤ Order.coheight ((𝟙 X : X ⟶ X) y)
    intro y hy hne
    have hsp : P.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact specializes_iff_mem_closure.2 hy
    have hlt : y < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hsp)
      fun h => hne ((Scheme.le_iff_specializes.1 h).antisymm hsp).eq
    have h1 := Order.coheight_strictAnti hlt
    rw [P.coheight_genericPoint] at h1
    have h2 : (2 : ℕ∞) ≤ Order.coheight y := by
      have := Order.add_one_le_of_lt (h1 (by simp))
      rwa [one_add_one_eq_two] at this
    simpa using h2

end Stage

end MMP.Proof_lem_km2b_discrep_minus_infinity_or_totaldiscrep_ge_minus_one

end

section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Mori

open MMP.Proof_lem_km2b_discrep_minus_infinity_or_totaldiscrep_ge_minus_one in
/-- **Kollár–Mori 2.31(1).** Let `(X, Δ)` be a pair over an algebraically closed field of
characteristic zero, with canonical divisor `K` of dimension `n ≥ 2`. If
`totaldiscrep(X, Δ) < -1`, then `discrep(X, Δ) = -∞`. -/
@[mmp "lem_km2b_discrep_minus_infinity_or_totaldiscrep_ge_minus_one"]
public theorem discrep_eq_bot_of_totalDiscrep_lt_neg_one {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hn : 2 ≤ n) (htot : totalDiscrep sX n K Δ < -1) :
    discrep sX n K Δ = ⊥ := by
  obtain ⟨γ, hγ, h0⟩ := exists_stage_zero hP hn htot
  have hst : ∀ j, Stage sX n K Δ γ j := fun j => by
    induction j with
    | zero => exact h0
    | succ j ih => exact stage_succ hP ih
  refine (EReal.eq_bot_iff_forall_lt _).2 fun r => ?_
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  obtain ⟨j, hj⟩ := exists_nat_gt (-r / (γ : ℝ))
  refine (discrep_le_of_stage hP.1 (Nat.succ_ne_zero j) (hst (j + 1))).trans_lt ?_
  rw [EReal.coe_lt_coe_iff]
  have h1 : -r < (j : ℝ) * γ := (div_lt_iff₀ hγ').1 hj
  push_cast
  nlinarith

end MMP.Mori

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Proof_lem_mmp_foundation_free_system_irreducible_bertini

open MMP.Threefold.Bridges
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections grading degreeOneElement)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-! ### Topology -/

/-- **Krull dimension is detected on an open cover.** If the opens `O j` cover `X` and `X` has a
chain of irreducible closed subsets of length `n`, so does one of the `O j`: restrict the chain
to an open containing a point of its smallest member. -/
private theorem exists_le_topologicalKrullDim_of_forall_mem {X : Type*} [TopologicalSpace X]
    {ι : Type*} (O : ι → Set X) (hO : ∀ j, IsOpen (O j)) (hcov : ∀ x, ∃ j, x ∈ O j) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ j, (n : WithBot ℕ∞) ≤ topologicalKrullDim (O j) := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  obtain ⟨y, hy⟩ := p.head.isIrreducible.nonempty
  obtain ⟨j, hj⟩ := hcov y
  have hmem : ∀ i, y ∈ (p i : Set X) := fun i =>
    (p.monotone (Fin.zero_le i)) hy
  have hemb : Topology.IsOpenEmbedding ((↑) : O j → X) := (hO j).isOpenEmbedding_subtypeVal
  let F : ∀ T : IrreducibleCloseds X, y ∈ (T : Set X) → IrreducibleCloseds (O j) :=
    fun T hT =>
      { carrier := ((↑) : O j → X) ⁻¹' (T : Set X)
        isIrreducible' := ⟨⟨⟨y, hj⟩, hT⟩, T.isIrreducible.2.preimage hemb⟩
        isClosed' := T.isClosed.preimage continuous_subtype_val }
  have hFlt : ∀ (T T' : IrreducibleCloseds X) (hT : y ∈ (T : Set X)) (hT' : y ∈ (T' : Set X)),
      T < T' → F T hT < F T' hT' := by
    intro T T' hT hT' hlt
    refine lt_of_le_of_ne (fun z hz => hlt.le hz) fun heq => hlt.ne ?_
    have hset : ((↑) : O j → X) ⁻¹' (T : Set X) = (↑) ⁻¹' (T' : Set X) :=
      congrArg (fun W : IrreducibleCloseds (O j) => (W : Set (O j))) heq
    refine le_antisymm hlt.le fun z hz => ?_
    have hsub : (T' : Set X) ⊆ closure ((T' : Set X) ∩ O j) := by
      intro z hz
      by_contra hzc
      obtain ⟨w, hwT, hwu, hwO⟩ := T'.isIrreducible.2 _ _ isClosed_closure.isOpen_compl (hO j)
        ⟨z, hz, hzc⟩ ⟨y, hT', hj⟩
      exact hwu (subset_closure ⟨hwT, hwO⟩)
    have hinter : (T' : Set X) ∩ O j ⊆ T := by
      rintro w ⟨hw, hwO⟩
      have : (⟨w, hwO⟩ : O j) ∈ ((↑) : O j → X) ⁻¹' (T' : Set X) := hw
      rw [← hset] at this
      exact this
    exact (closure_minimal hinter T.isClosed) (hsub hz)
  let q : LTSeries (IrreducibleCloseds (O j)) :=
    { length := p.length
      toFun := fun i => F (p i) (hmem i)
      step := fun i => hFlt _ _ (hmem _) (hmem _) (p.step i) }
  refine ⟨j, ?_⟩
  rw [← hp]
  exact Order.le_krullDim_iff.mpr ⟨q, rfl⟩

/-- An irreducible closed subset of a closed set `C` lies in an irreducible component of `C`. -/
private theorem exists_le_maximal_irreducibleCloseds {X : Type*} [TopologicalSpace X]
    {C : Set X} (hC : IsClosed C) (T : IrreducibleCloseds X) (hT : (T : Set X) ⊆ C) :
    ∃ Z : IrreducibleCloseds X, T ≤ Z ∧
      Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆ C) Z := by
  obtain ⟨Z, hTZ, hZ⟩ := zorn_le_nonempty₀ {W : IrreducibleCloseds X | T ≤ W ∧ (W : Set X) ⊆ C}
    (fun c hcs hc W hW => by
      have hpre : IsPreirreducible (⋃₀ ((fun W : IrreducibleCloseds X => (W : Set X)) '' c)) := by
        intro u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩
        obtain ⟨_, ⟨p, hpc, rfl⟩, hyp⟩ := Set.mem_sUnion.1 hy
        obtain ⟨_, ⟨q, hqc, rfl⟩, hxq⟩ := Set.mem_sUnion.1 hx
        rcases hc.total hpc hqc with hpq | hqp
        · obtain ⟨z, hzq, hzuv⟩ := q.isIrreducible.2 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
          exact ⟨z, Set.mem_sUnion_of_mem hzq ⟨q, hqc, rfl⟩, hzuv⟩
        · obtain ⟨z, hzp, hzuv⟩ := p.isIrreducible.2 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          exact ⟨z, Set.mem_sUnion_of_mem hzp ⟨p, hpc, rfl⟩, hzuv⟩
      have hne : (⋃₀ ((fun W : IrreducibleCloseds X => (W : Set X)) '' c)).Nonempty := by
        obtain ⟨y, hy⟩ := W.isIrreducible.nonempty
        exact ⟨y, Set.mem_sUnion_of_mem hy ⟨W, hW, rfl⟩⟩
      refine ⟨⟨closure (⋃₀ ((fun W : IrreducibleCloseds X => (W : Set X)) '' c)),
        (IsIrreducible.closure ⟨hne, hpre⟩), isClosed_closure⟩, ⟨?_, ?_⟩, ?_⟩
      · exact fun y hy => subset_closure (Set.mem_sUnion_of_mem ((hcs hW).1 hy) ⟨W, hW, rfl⟩)
      · refine closure_minimal ?_ hC
        rintro y ⟨_, ⟨p, hpc, rfl⟩, hyp⟩
        exact (hcs hpc).2 hyp
      · intro p hpc y hy
        exact subset_closure (Set.mem_sUnion_of_mem hy ⟨p, hpc, rfl⟩))
    T ⟨le_rfl, hT⟩
  refine ⟨Z, hTZ, hZ.prop.2, fun W hW hZW => hZ.2 ⟨hTZ.trans hZW, hW⟩ hZW⟩

/-- **Clause (3) of [Stacks, Tag 0G4F] from a chart.** Let `f : Spec R → X` be an open embedding
with `R` a Noetherian domain, and let the closed sets `H v` of `X` be cut out on the chart by
functions `τ v`. If `m` is a prime with `τ v₁ ∉ m`, `τ v₂, τ v₃ ∈ m`, `τ v₂ ≠ 0`, and `τ v₃` lies
in no minimal prime of `(τ v₂)` below `m`, then an irreducible component of `H v₂ ∩ H v₃`
through the point `m` has codimension two and is not contained in `H v₁`. -/
private theorem exists_maximal_codimension_eq_two {X : Type*} [TopologicalSpace X]
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f : PrimeSpectrum R → X} (hf : Topology.IsOpenEmbedding f)
    {V : Type*} (H : V → Set X) (hH : ∀ v, IsClosed (H v)) (τ : V → R)
    (hτ : ∀ p v, f p ∈ H v ↔ τ v ∈ p.asIdeal)
    (m : PrimeSpectrum R) (v₁ v₂ v₃ : V) (h₁ : τ v₁ ∉ m.asIdeal) (h₂ : τ v₂ ∈ m.asIdeal)
    (h₃ : τ v₃ ∈ m.asIdeal) (h₂0 : τ v₂ ≠ 0)
    (hgood : ∀ q ∈ (Ideal.span {τ v₂}).minimalPrimes, q ≤ m.asIdeal → τ v₃ ∉ q) :
    ∃ Z : IrreducibleCloseds X,
      Maximal (fun W : IrreducibleCloseds X => (W : Set X) ⊆ H v₂ ∩ H v₃) Z ∧
        ¬ (Z : Set X) ⊆ H v₁ ∧ codimension Z = 2 := by
  classical
  set C := H v₂ ∩ H v₃
  have hC : IsClosed C := (hH v₂).inter (hH v₃)
  have hxC : f m ∈ C := ⟨(hτ m v₂).2 h₂, (hτ m v₃).2 h₃⟩
  let T : IrreducibleCloseds X :=
    ⟨closure {f m}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨Z, hTZ, hmax⟩ := exists_le_maximal_irreducibleCloseds hC T
    (closure_minimal (Set.singleton_subset_iff.mpr hxC) hC)
  have hxZ : f m ∈ (Z : Set X) := hTZ (subset_closure rfl)
  refine ⟨Z, hmax, fun h => h₁ ((hτ m v₁).1 (h hxZ)), ?_⟩
  set I := Ideal.span {τ v₂, τ v₃}
  have hne : (f ⁻¹' (Z : Set X)).Nonempty := ⟨m, hxZ⟩
  have hmemI : ∀ p : PrimeSpectrum R, f p ∈ C → I ≤ p.asIdeal := fun p hp => by
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact (hτ p v₂).1 hp.1
    · exact (hτ p v₃).1 hp.2
  have himgC : f '' PrimeSpectrum.zeroLocus (I : Set R) ⊆ C := by
    rintro _ ⟨p, hp, rfl⟩
    have hIp : I ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hp
    exact ⟨(hτ p v₂).2 (hIp (Ideal.subset_span (by simp))),
      (hτ p v₃).2 (hIp (Ideal.subset_span (by simp)))⟩
  have hfZ : f ⁻¹' (Z : Set X) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := fun p hp =>
    (PrimeSpectrum.mem_zeroLocus _ _).2 (hmemI p (hmax.prop hp))
  have hp := PrimeSpectrum.vanishingIdeal_preimage_mem_minimalPrimes hf Z hne hC hmax himgC hfZ
  have hh := PrimeSpectrum.height_vanishingIdeal_preimage hf Z hne
  set p := PrimeSpectrum.vanishingIdeal (f ⁻¹' (Z : Set X))
  have hpp : p.IsPrime := hp.1.1
  rw [← hh]
  refine le_antisymm ?_ ?_
  · refine (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes I p hp).trans ?_
    have h : I.spanRank ≤ 2 := (Submodule.spanRank_span_le_card _).trans <| by
      simpa [one_add_one_eq_two] using Cardinal.mk_insert_le (a := τ v₂) (s := {τ v₃})
    simpa using Cardinal.toENat.monotone' h
  · have hpm : p ≤ m.asIdeal := fun r hr => (PrimeSpectrum.mem_vanishingIdeal _ _).1 hr m hxZ
    have h2p : Ideal.span {τ v₂} ≤ p :=
      (Ideal.span_mono (by simp)).trans hp.1.2
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le h2p
    have : q.IsPrime := hq.1.1
    have hq3 : τ v₃ ∉ q := hgood q hq (hqp.trans hpm)
    have hp3 : τ v₃ ∈ p := hp.1.2 (Ideal.subset_span (by simp))
    have hqlt : q < p := lt_of_le_of_ne hqp fun h => hq3 (h ▸ hp3)
    have hbot : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.mpr fun h => h₂0 <| by
      simpa [h] using hq.1.2 (Ideal.mem_span_singleton_self (τ v₂))
    have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rw [Ideal.height_bot, zero_add] at e1
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ q.height + 1 := by gcongr
      _ ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hqlt

/-! ### Commutative algebra -/

section Algebra

variable {k : Type*} [Field k]
  {R : Type*} [CommRing R] [Algebra k R]

/-- Over an algebraically closed field, every element of a finitely generated algebra is
congruent to a scalar modulo a maximal ideal. -/
private theorem exists_sub_algebraMap_mem [IsAlgClosed k] [Algebra.FiniteType k R]
    (m : Ideal R) [m.IsMaximal] (r : R) :
    ∃ c : k, r - algebraMap k R c ∈ m := by
  let _ := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)).2
    (Ideal.Quotient.mk m r)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap, sub_self]

/-- **Going down after a flat localization.** If `R_a` is flat over `A_a` and `q` is a prime of
`R` not containing `a`, the height of `q` bounds the height of its contraction to `A`. -/
private theorem height_comap_le_of_flat {A : Type*} [CommRing A] [Algebra A R]
    [IsNoetherianRing A] [IsNoetherianRing R] (a : A)
    (hflat : Module.Flat (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid R (Submonoid.powers a))))
    (q : Ideal R) [q.IsPrime] (haq : algebraMap A R a ∉ q) :
    (q.comap (algebraMap A R)).height ≤ q.height := by
  set Aa := Localization.Away a
  set Ra := Localization (Algebra.algebraMapSubmonoid R (Submonoid.powers a))
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid R (Submonoid.powers a) : Set R) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hmem
    exact haq ((‹q.IsPrime›).mem_of_pow_mem n (by simpa using hmem))
  set Q := q.map (algebraMap R Ra)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Ra q ‹_› hdisj
  set P := Q.comap (algebraMap Aa Ra)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver P := ⟨rfl⟩
  have : IsNoetherianRing Aa := IsLocalization.isNoetherianRing (Submonoid.powers a) Aa ‹_›
  have : IsNoetherianRing Ra :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid R (Submonoid.powers a)) Ra ‹_›
  have hQq : Q.under R = q := IsLocalization.under_map_of_isPrime_disjoint _ Ra ‹_› hdisj
  have hPq : P.under A = q.comap (algebraMap A R) := by
    rw [← hQq]
    change Ideal.comap (algebraMap A Aa) (Ideal.comap (algebraMap Aa Ra) Q) =
      Ideal.comap (algebraMap A R) (Ideal.comap (algebraMap R Ra) Q)
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have h1 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q
  rw [← hPq, IsLocalization.height_under (Submonoid.powers a) P, ← hQq,
    IsLocalization.height_under (Algebra.algebraMapSubmonoid R (Submonoid.powers a)) Q, h1]
  exact le_self_add

/-- **Generic flatness** for a finitely generated algebra over a Noetherian domain: after
inverting a nonzero element of the base, the algebra becomes flat. -/
private theorem exists_ne_zero_flat_localization {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Algebra A R] [Algebra.FiniteType A R] :
    ∃ a : A, a ≠ 0 ∧ Module.Flat (Localization.Away a)
      (Localization (Algebra.algebraMapSubmonoid R (Submonoid.powers a))) := by
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨f, hf, hfree⟩ := Module.FinitePresentation.exists_ne_zero_free_localizedModule_away
    (R := A) (S := R) (M := R)
  refine ⟨f, hf, ?_⟩
  set Ra := Localization (Algebra.algebraMapSubmonoid R (Submonoid.powers f))
  have : IsLocalizedModule (Submonoid.powers f) (IsScalarTower.toAlgHom A R Ra).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have := hfree (Localization.Away f) Ra (IsScalarTower.toAlgHom A R Ra).toLinearMap
  infer_instance

/-- In a Jacobson domain a nonzero element lies outside some maximal ideal. -/
private theorem exists_isMaximal_notMem [IsDomain R] [IsJacobsonRing R] {r : R} (hr : r ≠ 0) :
    ∃ m : Ideal R, m.IsMaximal ∧ r ∉ m := by
  have hj : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (Ideal.isPrime_bot.isRadical)
  have hr' : r ∉ (⊥ : Ideal R).jacobson := by rwa [hj]
  rw [Ideal.jacobson, Submodule.mem_sInf] at hr'
  push Not at hr'
  obtain ⟨m, ⟨-, hm⟩, hrm⟩ := hr'
  exact ⟨m, hm, hrm⟩

/-- **The algebraic core of the choice of the three sections.** Let `R` be a finitely generated
domain over an algebraically closed field `k`, `A ⊆ R` a finitely generated subalgebra of
dimension at least two and `τ : V → R` a `k`-linear map such that, for primes `q ⊆ m` with `m`
maximal, `q` and `m` contract to the same prime of `A` as soon as every `τ v` in `m` lies in
`q`. Then there are a maximal ideal `m` and vectors `v₂, v₃` with `τ v₂, τ v₃ ∈ m`, `τ v₂ ≠ 0`,
and `τ v₃` outside every minimal prime of `(τ v₂)` contained in `m`. -/
private theorem exists_isMaximal_forall_notMem_minimalPrimes [IsAlgClosed k] [IsDomain R]
    [Algebra.FiniteType k R] (A : Subalgebra k R) [Algebra.FiniteType k A]
    (hA : 2 ≤ ringKrullDim A) {V : Type*} [AddCommGroup V] [Module k V] (τ : V →ₗ[k] R)
    (hpt : ∀ m q : Ideal R, m.IsMaximal → q.IsPrime → q ≤ m →
      (∀ v, τ v ∈ m → τ v ∈ q) → q.comap (algebraMap A R) = m.comap (algebraMap A R)) :
    ∃ (m : Ideal R) (v₂ v₃ : V), m.IsMaximal ∧ τ v₂ ∈ m ∧ τ v₃ ∈ m ∧ τ v₂ ≠ 0 ∧
      ∀ q ∈ (Ideal.span {τ v₂}).minimalPrimes, q ≤ m → τ v₃ ∉ q := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Algebra.FiniteType A R := Algebra.FiniteType.of_restrictScalars_finiteType k A R
  obtain ⟨a, ha0, hflat⟩ := exists_ne_zero_flat_localization (A := A) (R := R)
  have ha0' : algebraMap A R a ≠ 0 := fun h => ha0 (Subtype.ext h)
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨m, hm, ham⟩ := exists_isMaximal_notMem ha0'
  set n := m.comap (algebraMap A R) with hn_def
  have hnmax : n.IsMaximal := by
    let _ := Ideal.Quotient.field m
    have hsurj : Function.Surjective ((Ideal.Quotient.mkₐ k m).comp A.val) := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem (k := k) m r
      refine ⟨algebraMap k A c, ?_⟩
      rw [AlgHom.comp_apply, AlgHom.commutes, Ideal.Quotient.mkₐ_eq_mk]
      refine Ideal.Quotient.eq.mpr ?_
      rw [← neg_sub]
      exact m.neg_mem hc
    have hker : RingHom.ker ((Ideal.Quotient.mkₐ k m).comp A.val) = n := by
      ext x; simp [n, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj
  have hn2 : (2 : ℕ∞) ≤ n.height := by
    have := (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
      k A).1 n
    rw [this] at hA
    exact WithBot.coe_le_coe.mp hA
  have key : ∀ q : Ideal R, q.IsPrime → q ≤ m → (∀ v, τ v ∈ m → τ v ∈ q) →
      (2 : ℕ∞) ≤ q.height := fun q hq hqm h => by
    have := height_comap_le_of_flat a hflat q (fun h' => ham (hqm h'))
    rw [hpt m q hm hq hqm h] at this
    exact hn2.trans this
  obtain ⟨v₂, hv₂m, hv₂0⟩ : ∃ v, τ v ∈ m ∧ τ v ≠ 0 := by
    by_contra h
    push Not at h
    have := key ⊥ Ideal.isPrime_bot bot_le (fun v hv => by rw [h v hv]; exact zero_mem _)
    rw [Ideal.height_bot] at this
    exact absurd this (by norm_num)
  set M : Submodule k V := (m.restrictScalars k).comap τ
  set S := {q : Ideal R | q ∈ (Ideal.span {τ v₂}).minimalPrimes ∧ q ≤ m}
  have hS : S.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R _).subset fun q hq => hq.1
  have : Finite S := hS.to_subtype
  let W : S → Submodule k M := fun q => ((q.1.restrictScalars k).comap τ).comap M.subtype
  have hW : ∀ q, W q ≠ ⊤ := by
    rintro ⟨q, hq, hqm⟩ htop
    have hqp : q.IsPrime := hq.1.1
    have h2 := key q hqp hqm fun v hv => by
      have : (⟨v, hv⟩ : M) ∈ W ⟨q, hq, hqm⟩ := htop ▸ Submodule.mem_top
      exact this
    have h1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
    exact absurd (h2.trans h1) (by norm_num)
  obtain ⟨v₃, hv₃⟩ := Submodule.exists_forall_notMem_of_forall_ne_top W hW
  exact ⟨m, v₂, v₃, hm, hv₂m, v₃.2, hv₂0, fun q hq hqm h => hv₃ ⟨q, hq, hqm⟩ h⟩

end Algebra

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-! ### The chart of the morphism of the system -/

section Charts

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A vector of `V` is homogeneous of degree one in `Sym_k V`. -/
private theorem ι_mem_grading_one (v : V) : SymmetricAlgebra.ι k V v ∈ grading k V 1 :=
  (degreeOneElement k V v).2

/-- An inducing map whose range lies in the range of an embedding does not raise dimension. -/
private theorem topologicalKrullDim_le_of_isInducing_of_range_subset {Y Z W : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W] {g : Y → W}
    (hg : Topology.IsInducing g) {e : Z → W} (he : Topology.IsEmbedding e)
    (hr : Set.range g ⊆ Set.range e) :
    topologicalKrullDim Y ≤ topologicalKrullDim Z := by
  have hg' : Topology.IsInducing (Set.codRestrict g (Set.range e) fun y => hr ⟨y, rfl⟩) :=
    hg.codRestrict _
  exact (he.toHomeomorph.symm.isInducing.comp hg').topologicalKrullDim_le

section PointValue

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The preimage of the standard open `D₊(v)` under the morphism of a generating system is the
nonvanishing open of the section of `v`. -/
private theorem preimage_basicOpen_morphismOfGeneratingSections'
    (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v : V) :
    morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v) =
      nonvanishingOpen X L (ψ v) := by
  refine ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V v)).trans ?_
  change nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L 1)
      ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1) = _
  rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]

end PointValue

/-- **A section vanishes on its zero scheme**: a point at which a global section of an invertible
module fails to generate lies on the support of its zero scheme. -/
private theorem mem_supportSet_zeroScheme_of_notMem_nonvanishingOpen (s : Γ(L, ⊤)) {y : X}
    (hy : y ∉ nonvanishingOpen X L s) : y ∈ (zeroScheme X L s).supportSet := by
  by_contra hsupp
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, y ∈ V z := Opens.mem_iSup.mp (hV ▸ Opens.mem_top y)
  obtain ⟨t⟩ := htriv z
  obtain ⟨W, hW, hyW, hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hz
  let t' := t.comp (homOfLE hWV)
  let e : Γ(L, W) ≃ₗ[Γ(X, W)] Γ(X, W) := t'.θ W (𝟙 W)
  set a : Γ(X, W) := e (L.presheaf.map (homOfLE le_top).op s) with ha
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨W, hW⟩) hyW,
    zeroScheme_ideal_of_trivialization X L s ⟨W, hW⟩ e a rfl,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton, Set.mem_compl_iff, not_not] at hsupp
  exact hy ((Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t' s hyW).mpr
    ((X.mem_basicOpen a y hyW).mp hsupp))

section Chart

variable (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (v₀ : V)
  {U : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ nonvanishingOpen X L (ψ v₀))

/-- The ring `Sym_k(V)_{(v₀)}` of the standard chart `D₊(v₀)` of `ℙ(V)`. -/
private abbrev ChartRing := HomogeneousLocalization.Away (grading k V) (SymmetricAlgebra.ι k V v₀)

/-- The open immersion `Spec Sym_k(V)_{(v₀)} ⟶ ℙ(V)` onto `D₊(v₀)`. -/
private noncomputable abbrev chartι :
    Spec (.of (ChartRing (k := k) v₀)) ⟶ projectiveSpaceOfModule k V :=
  Proj.awayι (grading k V) (SymmetricAlgebra.ι k V v₀) (ι_mem_grading_one (k := k) v₀) one_pos

private theorem isOpenImmersion_chartι : IsOpenImmersion (chartι (k := k) v₀) := by
  change IsOpenImmersion (Proj.awayι (grading k V) (SymmetricAlgebra.ι k V v₀)
    (ι_mem_grading_one (k := k) v₀) one_pos)
  unfold Proj.awayι
  infer_instance

private theorem range_chartι :
    Set.range (chartι (k := k) v₀) =
      (Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v₀) : Set _) := by
  have := isOpenImmersion_chartι (k := k) v₀
  have h := Proj.opensRange_awayι (grading k V) (SymmetricAlgebra.ι k V v₀)
    (ι_mem_grading_one (k := k) v₀) one_pos
  rw [← Scheme.Hom.coe_opensRange]
  exact congrArg (fun W : (projectiveSpaceOfModule k V).Opens =>
    (W : Set (projectiveSpaceOfModule k V))) h

include hUW in
private theorem range_fromSpec_comp_subset :
    Set.range (hU.fromSpec ≫ morphismOfGeneratingSections k V L ψ hψ) ⊆
      Set.range (chartι (k := k) v₀) := by
  rintro _ ⟨p, rfl⟩
  rw [range_chartι]
  have := hUW (hU.range_fromSpec ▸ ⟨p, rfl⟩ : hU.fromSpec p ∈ (U : Set X))
  rwa [← preimage_basicOpen_morphismOfGeneratingSections' ψ hψ v₀] at this

/-- **The chart ring map** `Sym_k(V)_{(v₀)} → Γ(X, U)` of the morphism of the system, on an
affine open `U` on which the section of `v₀` does not vanish. -/
private noncomputable def chartHom : CommRingCat.of (ChartRing (k := k) v₀) ⟶ Γ(X, U) :=
  haveI := isOpenImmersion_chartι (k := k) v₀
  Spec.preimage (IsOpenImmersion.lift (chartι (k := k) v₀)
    (hU.fromSpec ≫ morphismOfGeneratingSections k V L ψ hψ)
    (range_fromSpec_comp_subset ψ hψ v₀ hU hUW))

private theorem spec_map_chartHom :
    Spec.map (chartHom ψ hψ v₀ hU hUW) ≫ chartι (k := k) v₀ =
      hU.fromSpec ≫ morphismOfGeneratingSections k V L ψ hψ := by
  have := isOpenImmersion_chartι (k := k) v₀
  rw [chartHom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem chartι_comap_chartHom (p : PrimeSpectrum Γ(X, U)) :
    chartι (k := k) v₀ (PrimeSpectrum.comap (chartHom ψ hψ v₀ hU hUW).hom p) =
      morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec p) := by
  calc chartι (k := k) v₀ (PrimeSpectrum.comap (chartHom ψ hψ v₀ hU hUW).hom p)
      = (Spec.map (chartHom ψ hψ v₀ hU hUW) ≫ chartι (k := k) v₀) p := rfl
    _ = (hU.fromSpec ≫ morphismOfGeneratingSections k V L ψ hψ) p := by
        rw [spec_map_chartHom]
    _ = morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec p) := rfl

/-- The degree-one fraction `v / v₀` of the chart ring. -/
private noncomputable def chartFraction : V →ₗ[k] ChartRing (k := k) v₀ where
  toFun v := HomogeneousLocalization.Away.mk (grading k V) (ι_mem_grading_one (k := k) v₀) 1
    (SymmetricAlgebra.ι k V v) (by simp only [one_smul]; exact ι_mem_grading_one (k := k) v)
  map_add' v w := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_add]
    erw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.Away.val_mk, map_add, Localization.add_mk_self]
  map_smul' c v := by
    apply HomogeneousLocalization.val_injective
    simp only [RingHom.id_apply]
    erw [HomogeneousLocalization.val_smul, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.Away.val_mk, map_smul, Localization.smul_mk]

private theorem chartFraction_self : chartFraction (k := k) v₀ v₀ = 1 := by
  apply HomogeneousLocalization.val_injective
  erw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  · convert Localization.mk_self
      (⟨_, 1, rfl⟩ : Submonoid.powers (SymmetricAlgebra.ι k V v₀)) using 2
    simp
  · exact ι_mem_grading_one v₀

private theorem isLocalizationElem_eq_chartFraction (v : V) :
    HomogeneousLocalization.Away.isLocalizationElem (ι_mem_grading_one (k := k) v₀)
      (ι_mem_grading_one (k := k) v) = chartFraction (k := k) v₀ v := by
  apply HomogeneousLocalization.val_injective
  erw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  · simp only [pow_one]
  · exact ι_mem_grading_one v₀

/-- **The divisor of a member on the chart.** A point of `U` lies in the nonvanishing open of
`ψ v` exactly when the chart ring map does not send `v / v₀` into its prime. -/
private theorem fromSpec_mem_nonvanishingOpen_iff (p : PrimeSpectrum Γ(X, U)) (v : V) :
    hU.fromSpec p ∈ nonvanishingOpen X L (ψ v) ↔
      (chartHom ψ hψ v₀ hU hUW).hom (chartFraction (k := k) v₀ v) ∉ p.asIdeal := by
  rw [← preimage_basicOpen_morphismOfGeneratingSections' ψ hψ v]
  change morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec p) ∈
      Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v) ↔ _
  rw [← chartι_comap_chartHom ψ hψ v₀ hU hUW p]
  have h := Proj.awayι_preimage_basicOpen (grading k V) (ι_mem_grading_one (k := k) v₀) one_pos
    (ι_mem_grading_one (k := k) v) one_pos
  have h' : chartι (k := k) v₀ (PrimeSpectrum.comap (chartHom ψ hψ v₀ hU hUW).hom p) ∈
        Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v) ↔
      PrimeSpectrum.comap (chartHom ψ hψ v₀ hU hUW).hom p ∈ PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem (ι_mem_grading_one (k := k) v₀)
          (ι_mem_grading_one (k := k) v)) :=
    Iff.of_eq (congrArg (fun W : (Spec (.of (ChartRing (k := k) v₀))).Opens =>
      PrimeSpectrum.comap (chartHom ψ hψ v₀ hU hUW).hom p ∈ W) h)
  rw [h', isLocalizationElem_eq_chartFraction]
  exact Iff.rfl

/-- The `k`-algebra structure of `Γ(X, U)` induced by the structure morphism of `X`. -/
private noncomputable def chartScalars : CommRingCat.of k ⟶ Γ(X, U) :=
  Spec.preimage (hU.fromSpec ≫ X ↘ Spec (.of k))

private theorem spec_map_chartScalars :
    Spec.map (chartScalars hU) = hU.fromSpec ≫ X ↘ Spec (.of k) :=
  Spec.map_preimage _

private theorem algebraMap_chartRing_eq :
    CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (grading k V)
          (Submonoid.powers (SymmetricAlgebra.ι k V v₀))) =
      CommRingCat.ofHom (algebraMap k (ChartRing (k := k) v₀)) := by
  ext c
  rfl

open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare in
/-- **The chart ring map is `k`-linear**: the morphism of the system is a morphism over `k`. -/
private theorem chartHom_algebraMap (c : k) :
    (chartHom ψ hψ v₀ hU hUW).hom (algebraMap k (ChartRing (k := k) v₀) c) =
      (chartScalars hU).hom c := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing (k := k) v₀))) =
      chartι (k := k) v₀ ≫ projectiveSpaceOfModuleToSpec k V := by
    have h := Proj.awayι_toSpecZero (grading k V) (SymmetricAlgebra.ι k V v₀)
      (ι_mem_grading_one (k := k) v₀) one_pos
    rw [← algebraMap_chartRing_eq, Spec.map_comp]
    change _ = chartι (k := k) v₀ ≫ (Proj.toSpecZero (grading k V) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V))))
    rw [← Category.assoc]
    exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V))))
      h.symm
  have key : CommRingCat.ofHom (algebraMap k (ChartRing (k := k) v₀)) ≫
      chartHom ψ hψ v₀ hU hUW = chartScalars hU := by
    apply Spec.map_injective
    rw [Spec.map_comp, spec_map_chartScalars, h1, ← Category.assoc, spec_map_chartHom,
      Category.assoc,
      morphismOfGeneratingSections_comp_projectiveSpaceOfModuleToSpec]
  exact congrArg (fun f => f.hom c) key

private theorem finiteType_chartScalars [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    letI := (chartScalars (k := k) hU).hom.toAlgebra
    Algebra.FiniteType k Γ(X, U) := by
  have : LocallyOfFiniteType (Spec.map (chartScalars (k := k) hU)) := by
    rw [spec_map_chartScalars]; infer_instance
  exact HasRingHomProperty.Spec_iff.mp this

/-- The chart ring map as a `k`-algebra map. -/
private noncomputable def chartAlgHom :
    letI := (chartScalars (k := k) hU).hom.toAlgebra
    ChartRing (k := k) v₀ →ₐ[k] Γ(X, U) :=
  letI := (chartScalars (k := k) hU).hom.toAlgebra
  { (chartHom ψ hψ v₀ hU hUW).hom with
    commutes' := chartHom_algebraMap ψ hψ v₀ hU hUW }

/-- A degree-one form lies in the homogeneous prime of the image of a point of `U` exactly when
the chart ring map sends its fraction into the prime of the point. -/
private theorem mem_pointSubmodule_iff_chart (p : PrimeSpectrum Γ(X, U)) (v : V) :
    v ∈ ProjectiveSpaceOfModule.pointSubmodule k V
        (morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec p)) ↔
      (chartHom ψ hψ v₀ hU hUW).hom (chartFraction (k := k) v₀ v) ∈ p.asIdeal := by
  rw [ProjectiveSpaceOfModule.mem_pointSubmodule_iff, ← not_iff_not,
    ← fromSpec_mem_nonvanishingOpen_iff ψ hψ v₀ hU hUW p v,
    ← preimage_basicOpen_morphismOfGeneratingSections' ψ hψ v]
  exact Iff.rfl

/-- **Primes of `U` with the same linear forms through them meet the chart ring in the same
prime.** If `q ⊆ m` with `m` maximal and every fraction `v / v₀` vanishing at `m` vanishes at
`q`, then `q` and `m` have the same image in `D₊(v₀)`: the image of `m` is the `k`-point cut out
by the functional `v ↦ (v / v₀)(m)`, and a point of `ℙ(V)` on the hyperplane of a functional is
the point of that functional. -/
private theorem comap_chartHom_eq_of_forall [IsAlgClosed k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (m q : Ideal Γ(X, U)) [hm : m.IsMaximal]
    [hq : q.IsPrime]
    (h : ∀ v, (chartHom ψ hψ v₀ hU hUW).hom (chartFraction (k := k) v₀ v) ∈ m →
      (chartHom ψ hψ v₀ hU hUW).hom (chartFraction (k := k) v₀ v) ∈ q) :
    q.comap (chartHom ψ hψ v₀ hU hUW).hom = m.comap (chartHom ψ hψ v₀ hU hUW).hom := by
  let _ := (chartScalars (k := k) hU).hom.toAlgebra
  have := finiteType_chartScalars (k := k) hU
  let _ := Ideal.Quotient.field m
  have : Module.Finite k (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  have : Algebra.IsIntegral k (Γ(X, U) ⧸ m) := Algebra.IsIntegral.of_finite k _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, U) ⧸ m)
  let e : k ≃ₐ[k] Γ(X, U) ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k _) hb
  let τ : V →ₗ[k] Γ(X, U) := (chartAlgHom ψ hψ v₀ hU hUW).toLinearMap ∘ₗ chartFraction v₀
  have hτ : ∀ v, τ v = (chartHom ψ hψ v₀ hU hUW).hom (chartFraction (k := k) v₀ v) :=
    fun v => rfl
  let l : Module.Dual k V := e.symm.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ k m).toLinearMap ∘ₗ τ
  have hker : ∀ v, l v = 0 ↔ τ v ∈ m := fun v => by
    simp only [l, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hl : l ≠ 0 := by
    intro h0
    have := (hker v₀).1 (by rw [h0]; rfl)
    rw [hτ, chartFraction_self, map_one] at this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)
  have hmem : ∀ (P : PrimeSpectrum Γ(X, U)), (∀ v, τ v ∈ m → τ v ∈ P.asIdeal) →
      morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec P) =
        ProjectiveSpaceOfModule.linearFunctionalPoint k V l hl := by
    intro P hP
    have h1 := (ProjectiveSpaceOfModule.mem_linearSubspace_iff k V (LinearMap.ker l)
      (morphismOfGeneratingSections k V L ψ hψ (hU.fromSpec P))).2 fun v hv =>
        (mem_pointSubmodule_iff_chart ψ hψ v₀ hU hUW P v).2 (hP v ((hker v).1 hv))
    rwa [ProjectiveSpaceOfModule.linearSubspace_ker k V l hl, Set.mem_singleton_iff] at h1
  have hzm := hmem ⟨m, hm.isPrime⟩ fun v hv => hv
  have hzq := hmem ⟨q, hq⟩ fun v hv => h v hv
  have heq := hzq.trans hzm.symm
  rw [← chartι_comap_chartHom ψ hψ v₀ hU hUW, ← chartι_comap_chartHom ψ hψ v₀ hU hUW] at heq
  have := isOpenImmersion_chartι (k := k) v₀
  have := (chartι (k := k) v₀).isOpenEmbedding.injective heq
  exact congrArg PrimeSpectrum.asIdeal this

private theorem finiteType_chartRing [Module.Free k V] [Module.Finite k V] :
    Algebra.FiniteType k (ChartRing (k := k) v₀) := by
  have : Algebra.FiniteType k (SymmetricAlgebra k V) :=
    (inferInstance : Algebra.FiniteType k
      (MvPolynomial (Module.Free.ChooseBasisIndex k V) k)).equiv
      (SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis k V)).symm
  have : Algebra.FiniteType (grading k V 0) (SymmetricAlgebra k V) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : Algebra.FiniteType (grading k V 0) (ChartRing (k := k) v₀) :=
    HomogeneousLocalization.Away.finiteType _ 1 (ι_mem_grading_one (k := k) v₀)
  have h0 : (algebraMap k (grading k V 0)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have h1 : (algebraMap (grading k V 0) (ChartRing (k := k) v₀)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have heq : algebraMap k (ChartRing (k := k) v₀) =
      (algebraMap (grading k V 0) (ChartRing (k := k) v₀)).comp (algebraMap k (grading k V 0)) := by
    ext c
    rfl
  have := h1.comp h0
  rw [← heq] at this
  exact RingHom.finiteType_algebraMap.mp this

/-- **The image of `X_{v₀}` in `D₊(v₀)` has dimension at most that of the image of the chart
ring map**: it lies in the closure of the image of the dense open `U`, which is the spectrum of
`Sym_k(V)_{(v₀)} / ker`. -/
private theorem topologicalKrullDim_le_ringKrullDim_quotient [IrreducibleSpace X]
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim {z : Set.range (morphismOfGeneratingSections k V L ψ hψ) |
        z.1 ∈ (Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v₀) : Set _)} ≤
      ringKrullDim (ChartRing (k := k) v₀ ⧸ RingHom.ker (chartHom ψ hψ v₀ hU hUW).hom) := by
  have := isOpenImmersion_chartι (k := k) v₀
  set φ := morphismOfGeneratingSections k V L ψ hψ
  set γ := (chartHom ψ hψ v₀ hU hUW).hom
  set I := RingHom.ker γ
  let e : PrimeSpectrum (ChartRing (k := k) v₀ ⧸ I) → projectiveSpaceOfModule k V :=
    chartι (k := k) v₀ ∘ PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have he : Topology.IsEmbedding e :=
    (chartι (k := k) v₀).isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).isEmbedding
  have hG : Topology.IsInducing (fun z : {z : Set.range φ |
      z.1 ∈ (Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V v₀) : Set _)} => z.1.1) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine topologicalKrullDim_le_of_isInducing_of_range_subset hG he ?_
  rintro _ ⟨⟨⟨_, ⟨x, rfl⟩⟩, hz⟩, rfl⟩
  have hz' : φ x ∈ Set.range (chartι (k := k) v₀) := by rwa [range_chartι]
  obtain ⟨y, hy⟩ := hz'
  have hxcl : x ∈ closure (U : Set X) := by
    rw [(U.isOpen.dense hUne).closure_eq]; trivial
  have h1 : φ x ∈ closure (φ '' (U : Set X)) :=
    image_closure_subset_closure_image φ.continuous ⟨x, hxcl, rfl⟩
  have h2 : y ∈ closure ((chartι (k := k) v₀) ⁻¹' (φ '' (U : Set X))) := by
    rw [← (chartι (k := k) v₀).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (chartι (k := k) v₀).continuous]
    change chartι (k := k) v₀ y ∈ closure (φ '' (U : Set X))
    rwa [hy]
  have h3 : (chartι (k := k) v₀) ⁻¹' (φ '' (U : Set X)) ⊆ Set.range (PrimeSpectrum.comap γ) := by
    rintro w ⟨u, hu, hwu⟩
    rw [← hU.range_fromSpec] at hu
    obtain ⟨p, rfl⟩ := hu
    refine ⟨p, (chartι (k := k) v₀).isOpenEmbedding.injective ?_⟩
    rw [chartι_comap_chartHom ψ hψ v₀ hU hUW p]
    exact hwu
  have h4 : y ∈ PrimeSpectrum.zeroLocus (I : Set _) := by
    rw [← PrimeSpectrum.closure_range_comap]
    exact closure_mono h3 h2
  rw [← Ideal.mk_ker (I := I), ← range_comap_of_surjective _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective] at h4
  obtain ⟨y', rfl⟩ := h4
  exact ⟨y', hy⟩

end Chart

/-- **The sections of a basis already generate.** Every point lies in the nonvanishing open of
the section of some basis vector: the vectors whose sections vanish at a point form a subspace,
the degree-one part of the homogeneous prime of its image. -/
private theorem exists_mem_nonvanishingOpen_basis {ι : Type*} (b : Module.Basis ι k V)
    (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (x : X) :
    ∃ j, x ∈ nonvanishingOpen X L (ψ (b j)) := by
  by_contra h
  push Not at h
  set K := ProjectiveSpaceOfModule.pointSubmodule k V
    (morphismOfGeneratingSections k V L ψ hψ x)
  have hmem : ∀ v, v ∈ K ↔ x ∉ nonvanishingOpen X L (ψ v) := fun v => by
    rw [ProjectiveSpaceOfModule.mem_pointSubmodule_iff, ← not_iff_not, not_not,
      ← preimage_basicOpen_morphismOfGeneratingSections' ψ hψ v]
    exact Iff.rfl
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hmem _).2 (h j)
  have hx : x ∈ ⨆ v : V, nonvanishingOpen X L (ψ v) := by rw [hψ]; trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact (hmem c).1 (hK ▸ Submodule.mem_top) hc

end Charts

/-- The hypotheses of [Stacks, Tag 0G4F] for the system `s`. -/
private theorem nonempty_hypotheses [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs).base)) :
    Nonempty (systemFamily (k := k) s).Hypotheses := by
  classical
  set V := Fin (N + 1) → k
  set ψ : V →ₗ[k] Γ(L, ⊤) := systemSection s
  set D := systemFamily (k := k) s with hD
  set φ := morphismOfGeneratingSections k V L ψ hs
  have : IrreducibleSpace X := inferInstance
  -- a standard chart `D₊(T_{j₀})` meeting the image in dimension at least two
  let O : Fin (N + 1) → Set (Set.range φ) := fun j =>
    {z | z.1 ∈ (Proj.basicOpen (grading k V) (SymmetricAlgebra.ι k V (Pi.single j 1)) : Set _)}
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (Proj.basicOpen (grading k V) _).isOpen.preimage continuous_subtype_val
  have hcov : ∀ z, ∃ j, z ∈ O j := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    obtain ⟨j, hj⟩ := exists_mem_nonvanishingOpen_basis (Pi.basisFun k (Fin (N + 1))) ψ hs x
    refine ⟨j, ?_⟩
    rw [Pi.basisFun_apply, ← preimage_basicOpen_morphismOfGeneratingSections' ψ hs] at hj
    exact hj
  obtain ⟨j₀, hj₀⟩ := exists_le_topologicalKrullDim_of_forall_mem O hO hcov 2
    (by exact_mod_cast hdim)
  set v₀ : V := Pi.single j₀ 1
  obtain ⟨⟨⟨_, ⟨x₀, rfl⟩⟩, hx₀⟩⟩ : Nonempty (O j₀) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : IsEmpty (IrreducibleCloseds (O j₀)) :=
      ⟨fun T => hne.elim T.isIrreducible.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hj₀
    exact absurd hj₀ (by decide)
  have hx₀W : x₀ ∈ nonvanishingOpen X L (ψ v₀) := by
    rwa [← preimage_basicOpen_morphismOfGeneratingSections' ψ hs]
  obtain ⟨U, hU', hx₀U, hUW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx₀W
  have hU : IsAffineOpen U := hU'
  have : Nonempty U := ⟨⟨x₀, hx₀U⟩⟩
  -- the ring of the chart, its subalgebra of ratios, and the linear forms
  let _ := (chartScalars (k := k) hU).hom.toAlgebra
  have := finiteType_chartScalars (k := k) hU
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k _
  set γₐ := chartAlgHom ψ hs v₀ hU hUW
  set A := γₐ.range
  have := finiteType_chartRing (k := k) v₀
  have : Algebra.FiniteType k A := Algebra.FiniteType.of_surjective γₐ.rangeRestrict
    γₐ.rangeRestrict_surjective
  have hker : RingHom.ker γₐ.rangeRestrict = RingHom.ker (chartHom ψ hs v₀ hU hUW).hom := by
    ext b
    simp only [RingHom.mem_ker]
    rw [← Subtype.coe_inj]
    rfl
  have hA : 2 ≤ ringKrullDim A := by
    refine hj₀.trans ((topologicalKrullDim_le_ringKrullDim_quotient ψ hs v₀ hU hUW
      ⟨x₀, hx₀U⟩).trans (le_of_eq (ringKrullDim_eq_of_ringEquiv ?_)))
    exact (Ideal.quotEquivOfEq hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective γₐ.rangeRestrict_surjective).toRingEquiv
  let τ : V →ₗ[k] Γ(X, U) := γₐ.toLinearMap ∘ₗ chartFraction (k := k) v₀
  have hτ : ∀ v, τ v = (chartHom ψ hs v₀ hU hUW).hom (chartFraction (k := k) v₀ v) :=
    fun v => rfl
  have hpt : ∀ m q : Ideal Γ(X, U), m.IsMaximal → q.IsPrime → q ≤ m →
      (∀ v, τ v ∈ m → τ v ∈ q) → q.comap (algebraMap A Γ(X, U)) =
        m.comap (algebraMap A Γ(X, U)) := by
    intro m q hm hq _ h
    have heq := comap_chartHom_eq_of_forall ψ hs v₀ hU hUW m q h
    ext ⟨a, b, rfl⟩
    exact Ideal.ext_iff.mp heq b
  obtain ⟨m, v₂, v₃, hm, h2m, h3m, h20, hgood⟩ :=
    exists_isMaximal_forall_notMem_minimalPrimes A hA τ hpt
  -- the divisors of the system on the chart
  have hdiv : ∀ (p : PrimeSpectrum Γ(X, U)) (v : V),
      hU.fromSpec p ∈ D.divisorSet v ↔ τ v ∈ p.asIdeal := fun p v => by
    have h := fromSpec_mem_nonvanishingOpen_iff ψ hs v₀ hU hUW p v
    rw [← hτ] at h
    exact ⟨fun hd => Classical.byContradiction fun hn =>
        D.notMem_divisorSet_of_mem_nonvanishingOpen v (h.2 hn) hd,
      fun hv => mem_supportSet_zeroScheme_of_notMem_nonvanishingOpen _ fun hn => h.1 hn hv⟩
  have h1m : τ v₀ ∉ m := by
    rw [hτ, chartFraction_self, map_one]
    exact (Ideal.ne_top_iff_one m).1 hm.ne_top
  obtain ⟨Z, hZmax, hZ1, hZcodim⟩ := exists_maximal_codimension_eq_two
    hU.fromSpec.isOpenEmbedding D.divisorSet D.isClosed_divisorSet τ hdiv ⟨m, hm.isPrime⟩
    v₀ v₂ v₃ h1m h2m h3m h20 hgood
  -- the common zero locus is empty
  have hid : D.GeneratesBy (id : D.V → D.V) := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    have hx : x ∈ (⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c)) := by
      rw [hs]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hempty : D.commonZeroSet = ∅ :=
    D.commonZeroSet_eq_empty_of_generates ((D.generates_iff_generatesBy_id).mpr hid)
  exact ⟨{ locallyOfFiniteType := inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
           quasiCompact := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
           geometricallyIrreducible :=
             geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X _
           v₁ := v₀
           v₂ := v₂
           v₃ := v₃
           Z := Z
           Z_component := hZmax
           Z_not_subset := hZ1
           Z_codimension := hZcodim
           commonZeroSet_codimension := fun Y hY => by
             rw [hempty] at hY
             obtain ⟨y, hy⟩ := Y.isIrreducible.nonempty
             exact absurd (hY hy) (Set.notMem_empty y) }⟩

/-- The general member of the system is irreducible, in polynomial form. -/
private theorem exists_polynomial_irreducibleSpace_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs).base)) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        IrreducibleSpace (zeroScheme X L (systemSection s c)).subscheme := by
  classical
  obtain ⟨hyp⟩ := nonempty_hypotheses s hs hdim
  set D := systemFamily (k := k) s with hD
  obtain ⟨U, hUne, hU⟩ := hyp.forGeneral_geometricallyIrreducible
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_parameterPoint_mem (D := D) U hUne
  let σ : D.basisIndex ≃ Fin (N + 1) :=
    Equiv.ulift.trans (finCongr (Module.finrank_fin_fun k))
  refine ⟨MvPolynomial.rename σ P, fun h => hP0 (MvPolynomial.rename_injective _ σ.injective
    (h.trans (map_zero _).symm)), fun c hc => ?_⟩
  have e1 : MvPolynomial.eval c (MvPolynomial.rename σ P) = MvPolynomial.eval (c ∘ σ) P :=
    MvPolynomial.eval_rename _ _ _
  have hPc : MvPolynomial.eval (c ∘ σ) P ≠ 0 := fun h0 => hc (e1.trans h0)
  have hmem := hP (c ∘ σ) hPc
  let a : Fin (Module.finrank D.k D.V) → D.k := fun i => (c ∘ σ) (ULift.up i)
  have hgi := hU D.k a hmem a rfl
  have hirr := D.isIrreducible_divisorSet_of_geometricallyIrreducible a hgi
  have hsum : (∑ i, a i • D.basis i) = (c : D.V) := sum_smul_reindex_basisFun c
  rw [hsum] at hirr
  -- the subscheme is homeomorphic onto its support
  set Z := zeroScheme X L (systemSection s c)
  have hrange : Set.range Z.subschemeι.base = Z.supportSet :=
    Scheme.IdealSheafData.range_subschemeι Z
  have hemb : Topology.IsEmbedding Z.subschemeι.base :=
    Z.subschemeι.isClosedEmbedding.isEmbedding
  have hirr' : IsIrreducible (Set.range Z.subschemeι.base) := hrange ▸ hirr
  have := Subtype.irreducibleSpace hirr'
  exact (hemb.toHomeomorph).irreducibleSpace_iff.mpr inferInstance

/-- The general member of the system is geometrically irreducible, geometrically reduced and
integral, in polynomial form. -/
private theorem exists_polynomial_isIntegral_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs).base)) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        GeometricallyIrreducible
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          GeometricallyReduced
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          IsIntegral (zeroScheme X L (systemSection s c)).subscheme := by
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_irreducibleSpace_zeroScheme s hs hdim
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isReduced_zeroScheme s hs
  refine ⟨P * Q, mul_ne_zero hP0 hQ0, fun c hc => ?_⟩
  rw [map_mul] at hc
  have := hP c (left_ne_zero_of_mul hc)
  have := hQ c (right_ne_zero_of_mul hc)
  exact ⟨geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _,
    geometricallyReduced_of_isReduced _, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end MMP.Proof_lem_mmp_foundation_free_system_irreducible_bertini

end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

open MMP.Proof_lem_mmp_foundation_free_system_irreducible_bertini in
/-- **Bertini's irreducibility theorem for a free system.** Let `k` be algebraically closed of
characteristic zero, `X` a variety over `k`, `L` an invertible sheaf on `X` and `s₀, …, s_N`
global sections of `L` generating it, such that the image of the morphism
`φ : X ⟶ ℙ(V^*)` of the system has dimension at least two. There are a dense open of the
coefficient space `𝔸ᴺ⁺¹_k` and a dense open of `ℙᴺ_k` such that for every coefficient vector `c`
in the first, and every `c ≠ 0` with `[c]` in the second, the zero scheme of `∑ᵢ cᵢ sᵢ` is
geometrically irreducible and geometrically reduced over `k`, and integral. -/
@[mmp "lem_mmp_foundation_free_system_irreducible_bertini"]
public theorem exists_dense_open_geometricallyIrreducible_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    (hdim : 2 ≤ topologicalKrullDim
      (Set.range (morphismOfGeneratingSections k (Fin (N + 1) → k) L (systemSection s) hs).base)) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        GeometricallyIrreducible
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          GeometricallyReduced
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          IsIntegral (zeroScheme X L (systemSection s c)).subscheme) ∧
    (∃ U : (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        GeometricallyIrreducible
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          GeometricallyReduced
            ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) ∧
          IsIntegral (zeroScheme X L (systemSection s c)).subscheme) := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_isIntegral_zeroScheme s hs hdim
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0, fun c hc => hQ c ?_⟩, ?_⟩
  · intro h0
    change Q ∉ RingHom.ker (MvPolynomial.eval c) at hc
    exact hc ((RingHom.mem_ker).mpr h0)
  obtain ⟨d, hd⟩ : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
    by_contra h
    push Not at h
    apply hQ0
    rw [← MvPolynomial.sum_homogeneousComponent Q]
    exact Finset.sum_eq_zero fun i _ => h i
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  have hhc : MvPolynomial.eval c (MvPolynomial.homogeneousComponent d Q) ≠ 0 := by
    intro h0
    change MvPolynomial.homogeneousComponent d Q ∉
      (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
    exact hmem <| Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d Q⟩ ((RingHom.mem_ker).mpr h0)
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c hhc
  have h := hQ (t • c) htQ
  rwa [zeroScheme_systemSection_smul s c ht] at h

end MMP.Threefold.Bridges

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace MMP.Proof_lem_mmp_foundation_km_very_ample_integral_member

open MMP.Intersection MMP.Threefold.Bridges
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule baseRingHom
  morphismOfGeneratingSections)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-! ### The morphism of the very ample system is an immersion -/

/-- A morphism `i : X ⟶ ℙʳ_S` over `S` with `M ≅ i^*𝒪(1)` is the morphism of a generating family
of sections of `M` (the uniqueness half of [Stacks, Tag 01NE]). -/
private theorem exists_generatesStalks_eq_toProjectiveSpaceOver {X S : Scheme.{u}} (f : X ⟶ S)
    {r : ℕ} (M : X.Modules) [IsInvertibleModule X M] (i : X ⟶ projectiveSpaceOver r S)
    (hi : i ≫ (projectiveSpaceOver r S ↘ S) = f)
    (e : M ≅ (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r S)) :
    ∃ (t : Fin (r + 1) → Γ(M, ⊤)) (ht : GeneratesStalks t),
      toProjectiveSpaceOver t ht f = i := by
  have hlift : liftOver f (i ≫ projectiveSpaceOver.toIntegralAtUniverse r S) = i :=
    liftOver_eq f i hi
  let g : X ⟶ projectiveSpaceAtUniverse.{u} r := i ≫ projectiveSpaceOver.toIntegralAtUniverse r S
  let β : (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} r) ≅ M :=
    (liftOverTwistIso f g).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hlift
        (projectiveSpaceTwistingSheaf r S) ≪≫ e.symm
  have ht : GeneratesStalks (fun j => Scheme.Modules.Hom.app β.hom ⊤
      (Stacks.TwistPullbackPinned.pullbackCoordSection g j)) :=
    Stacks.ProductFamilyTwist.generatesStalks_congr β
      (Stacks.ProjectiveSpaceModuli.taut_generates g)
  refine ⟨_, ht, ?_⟩
  have hgt : g = toProjectiveSpaceAtUniverse _ ht :=
    Stacks.ProjectiveSpaceModuli.eq_of_pin _ ht g _
      (fun j => Stacks.ProjectiveSpaceModuli.pin_of_iso _ _ β (fun _ => rfl) g
        (Stacks.ProjectiveSpaceModuli.taut_pin g) j)
      (fun j => ι_toProjectiveSpaceAtUniverse _ ht j)
  rw [toProjectiveSpaceOver, ← hgt]
  exact hlift

/-- The morphism of a generating family depends only on the family. -/
private theorem toProjectiveSpaceOver_congr' {X S : Scheme.{u}} {M : X.Modules}
    [IsInvertibleModule X M] {r : ℕ} (f : X ⟶ S) {t t' : Fin (r + 1) → Γ(M, ⊤)}
    (h : t = t') (ht : GeneratesStalks t) (ht' : GeneratesStalks t') :
    toProjectiveSpaceOver t ht f = toProjectiveSpaceOver t' ht' f := by
  subst h; rfl

open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare in
/-- A very ample divisor carries finitely many generating sections whose morphism to projective
space is an immersion. -/
private theorem exists_family_isImmersion (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (A : X.CartierDivisor) (hA : IsVeryAmpleDivisor k A) :
    ∃ (N : ℕ) (s : Fin (N + 1) → Γ(MMP.CartierDivisor.sheaf A, ⊤))
      (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X (MMP.CartierDivisor.sheaf A) (systemSection s
          c) = ⊤),
      IsImmersion (morphismOfGeneratingSections k (Fin (N + 1) → k) (MMP.CartierDivisor.sheaf A)
        (systemSection s) hs) := by
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ :=
    MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple k (MMP.CartierDivisor.sheaf A)
        (MMP.CartierDivisor.sheaf A)
      hA (Iso.refl _)
  obtain ⟨t, ht, hti⟩ := exists_generatesStalks_eq_toProjectiveSpaceOver _ _ i hover e
  have hsingle : ∀ j, systemSection (k := k) t (Pi.single j 1) = t j := fun j => by
    simp [systemSection, Fintype.linearCombination_apply_single]
  have hs : ⨆ c : Fin (n + 1) → k, nonvanishingOpen X (MMP.CartierDivisor.sheaf A) (systemSection t
      c) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_nvCover_of_generatesStalks t ht x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single j 1, by rwa [hsingle]⟩
  refine ⟨n, t, hs, ?_⟩
  let b := Pi.basisFun k (Fin (n + 1))
  have h := morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso b
    (systemSection t) hs
  have hb : Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.basisSections b
      (systemSection t) = t := funext fun j => by
    rw [← hsingle j]
    simp [Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare.basisSections, b]
  rw [toProjectiveSpaceOver_congr' _ hb _ ht, hti] at h
  let E := (Over.forget _).mapIso (AlgebraicGeometry.basisProjectiveSpaceOfModuleIso b)
  have : morphismOfGeneratingSections k (Fin (n + 1) → k) (MMP.CartierDivisor.sheaf A)
      (systemSection t) hs =
      i ≫ E.inv := (Iso.eq_comp_inv E).mpr h
  rw [this]
  have hE : IsImmersion E.inv := inferInstance
  exact @IsImmersion.comp _ _ _ i E.inv hi hE

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

/-! ### Local frames and the zero scheme -/

section

variable {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- Every point has an affine neighbourhood `U` on which `L` is trivialized by a generator `e`,
with `σ|_U = r • e` and `σ` nonvanishing exactly where `r` is a unit. -/
private theorem exists_affine_frame (σ : Γ(L, ⊤)) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ (U : X.Opens)) (e : Γ(L, U)) (r : Γ(X, U)),
      IsTrivializingGenerator L U e ∧ L.presheaf.map (homOfLE le_top).op σ = r • e ∧
      ∀ (y : X) (hy : y ∈ (U : X.Opens)),
        y ∈ Stacks.Ample.nonvanishingLocus L σ ↔ IsUnit (X.presheaf.germ U y hy r) := by
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 L
  obtain ⟨z, hz⟩ : ∃ z : X, x ∈ V z := TopologicalSpace.Opens.mem_iSup.mp (hV ▸ trivial)
  obtain ⟨t⟩ := htriv z
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hz
  refine ⟨⟨U, hU⟩, hxU, L.presheaf.map (homOfLE hUV).op (Stacks.NonvanishingOpen.basis t),
    X.presheaf.map (homOfLE hUV).op (Stacks.NonvanishingOpen.trivTop t σ),
    (isTrivializingGenerator_basis t).res hUV, ?_, fun y hy => ?_⟩
  · have h := Stacks.NonvanishingOpen.eq_triv_smul_basis t (L.presheaf.map (homOfLE le_top).op σ)
    have h2 := congrArg (L.presheaf.map (homOfLE hUV).op) h
    rwa [modules_map_map, Scheme.Modules.map_smul] at h2
  · rw [Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit t σ (hUV hy),
      X.presheaf.germ_res_apply]

/-- On an affine open trivializing `L` by `e`, the ideal of the zero scheme of `σ = r • e` is
`(r)`. -/
private theorem zeroScheme_ideal_eq_span (σ : Γ(L, ⊤)) (U : X.affineOpens) (e : Γ(L, U))
    (r : Γ(X, U)) (he : IsTrivializingGenerator L U e)
    (hσ : L.presheaf.map (homOfLE le_top).op σ = r • e) :
    (zeroScheme X L σ).ideal U = Ideal.span {r} := by
  rw [zeroScheme_ideal]
  change Ideal.span {a | ∃ φ : Γ(L, U) →ₗ[Γ(X, U)] Γ(X, U),
    a = φ (L.presheaf.map (homOfLE le_top).op σ)} = _
  rw [hσ]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro a ⟨φ, rfl⟩
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)
  · have hb : Function.Bijective (LinearMap.toSpanSingleton Γ(X, U) Γ(L, U) e) := by
      have := he U le_rfl
      simp only [modules_map_id] at this
      exact this
    rw [Set.singleton_subset_iff]
    refine Ideal.subset_span ⟨(LinearEquiv.ofBijective _ hb).symm.toLinearMap, ?_⟩
    change r = (LinearEquiv.ofBijective _ hb).symm (LinearMap.toSpanSingleton Γ(X, U) Γ(L, U) e r)
    exact ((LinearEquiv.ofBijective _ hb).symm_apply_apply r).symm

/-- A point where `σ` does not vanish lies outside the zero scheme of `σ`. -/
private theorem notMem_support_zeroScheme (σ : Γ(L, ⊤)) {x : X}
    (hx : x ∈ Stacks.Ample.nonvanishingLocus L σ) : x ∉ (zeroScheme X L σ).support := by
  obtain ⟨U, hxU, e, r, he, hσ, hnv⟩ := exists_affine_frame σ x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, zeroScheme_ideal_eq_span σ U e r he hσ,
    Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  intro h
  exact h r rfl ((Scheme.mem_basicOpen _ _ _ hxU).mpr ((hnv x hxU).mp hx))

/-- On an integral scheme, the local coordinate of a section not vanishing at some point is a
unit of the sheaf of rational functions. -/
private theorem isUnit_toTotalQuotient_of_frame [IsIntegral X] {σ : Γ(L, ⊤)}
    (hσ : (Stacks.Ample.nonvanishingLocus L σ).Nonempty) {U : X.Opens} {x : X} (hxU : x ∈ U)
    {r : Γ(X, U)} (hnv : ∀ (y : X) (hy : y ∈ U),
      y ∈ Stacks.Ample.nonvanishingLocus L σ ↔ IsUnit (X.presheaf.germ U y hy r)) :
    IsUnit (toTotalQuotient U r) := by
  obtain ⟨y, hyσ, hyU⟩ := nonempty_preirreducible_inter
    (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus X L σ) U.isOpen hσ ⟨x, hxU⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    simpa using (hnv y hyU).mp hyσ
  refine isUnit_toTotalQuotientSheaf_app X.sheaf U r fun z hz =>
    show X.presheaf.germ U z hz r ∈ nonZeroDivisors (X.presheaf.stalk z) from
      mem_nonZeroDivisors_of_ne_zero fun h =>
        hr0 (germ_injective_of_isIntegral X z hz (by rw [h, map_zero]))

end

/-- On an integral scheme, a section `σ` of `𝒪_X(A)` not vanishing at some point is a unit of
`Γ(X, 𝓜_X)`, and `A + div σ` is an effective divisor linearly equivalent to `A` whose closed
subscheme is the zero scheme of `σ`. -/
private theorem exists_isEffective_isSubschemeOfEffective_zeroScheme {X : Scheme.{u}}
    [IsIntegral X] (A : X.CartierDivisor) (σ : Γ(MMP.CartierDivisor.sheaf A, ⊤))
    (hσ : (Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf A) σ).Nonempty) :
    ∃ A' : X.CartierDivisor, IsEffective A' ∧ LinearlyEquivalent A' A ∧
      IsSubschemeOfEffective A' (zeroScheme X (MMP.CartierDivisor.sheaf A) σ) := by
  choose U hxU e r he hσU hnv using fun x => exists_affine_frame σ x
  have hr : ∀ x, IsUnit (toTotalQuotient (U x : X.Opens) (r x)) := fun x =>
    isUnit_toTotalQuotient_of_frame hσ (hxU x) (hnv x)
  choose he' hloc using fun x =>
    MMP.CartierDivisor.isLocalEquationOn_inv_of_isTrivializingGenerator (he x)
  have hval : ∀ x, X.totalQuotientSheaf.obj.map
      (homOfLE le_top : (U x : X.Opens) ⟶ ⊤).op (MMP.CartierDivisorSheaf.sectionVal σ) =
        toTotalQuotient _ (r x) * MMP.CartierDivisorSheaf.sectionVal (e x) := fun x => by
    erw [← MMP.CartierDivisorSheaf.sectionVal_map, hσU x, MMP.CartierDivisor.sectionVal_smul]
  have hu : IsUnit (MMP.CartierDivisorSheaf.sectionVal σ) := isUnit_of_locally _ fun x _ =>
    ⟨U x, homOfLE le_top, hxU x, by rw [hval x]; exact (hr x).mul (he' x)⟩
  have hloc' : ∀ x, IsLocalEquationOn (A + principalDivisor hu.unit) (U x) (hr x).unit := by
    intro x
    have h := (hloc x).mul (isLocalEquationOn_principalDivisor_res hu.unit (U x))
    convert h using 1
    ext
    rw [Units.val_mul, Units.coe_map]
    change toTotalQuotient _ (r x) = _ * X.totalQuotientSheaf.obj.map _
        (MMP.CartierDivisorSheaf.sectionVal σ)
    rw [hval x, mul_left_comm, IsUnit.val_inv_mul, mul_one]
  refine ⟨A + principalDivisor hu.unit, fun x => ⟨U x, hxU x, r x, hr x, hloc' x⟩, ?_,
    fun x => ⟨U x, hxU x, r x, hr x, hloc' x, zeroScheme_ideal_eq_span σ (U x) (e x) (r x) (he x)
      (hσU x)⟩⟩
  change A + principalDivisor hu.unit - A ∈ principalSubgroup X
  rw [add_sub_cancel_left]
  exact principalDivisor_mem _

/-! ### Choosing the member -/

/-- A dense open of the coefficient space `𝔸ᴺ⁺¹_k` over an infinite field contains a `k`-point
`c` at which a given nonzero polynomial does not vanish. -/
private theorem exists_coefficientPoint_mem_and_eval_ne_zero {k : Type u} [Field k] [Infinite k]
    {N : ℕ} (U : (coefficientSpace k N).Opens) (hU : Dense (U : Set (coefficientSpace k N)))
    {g : MvPolynomial (Fin (N + 1)) k} (hg : g ≠ 0) :
    ∃ c : Fin (N + 1) → k, coefficientPoint c ∈ U ∧ MvPolynomial.eval c g ≠ 0 := by
  haveI : Nonempty (coefficientSpace k N) := ⟨coefficientPoint 0⟩
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.2
  have hf : f ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (Submodule.zero_mem _)
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (f * g) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hf hg (MvPolynomial.funext fun c => by simpa using h c)
  rw [map_mul] at hc
  refine ⟨c, hfU ?_, right_ne_zero_of_mul hc⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => left_ne_zero_of_mul hc h

section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable (k) in
/-- The global sections of `L` vanishing at `x`, as a `k`-subspace. -/
private def vanishingSubspace (L : X.Modules) (x : X) : Submodule k Γ(L, ⊤) where
  carrier := {t | (L.presheaf.Γgerm x).hom t ∈ Stacks.ModuleStalk.maximalSmul L x}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_mem _
  smul_mem' c t ht := by
    change (L.presheaf.Γgerm x).hom (baseRingHom k X c • t) ∈ Stacks.ModuleStalk.maximalSmul L x
    rw [Stacks.ModuleStalk.Γgerm_smul]
    exact Submodule.smul_mem _ _ ht

/-- For a generating system and a point `x` there is a nonzero polynomial (a linear form) whose
nonvanishing at `c` forces `∑ cᵢ sᵢ` not to vanish at `x`. -/
private theorem exists_polynomial_mem_nonvanishingLocus {N : ℕ} {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) (x : X) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 →
        x ∈ Stacks.Ample.nonvanishingLocus L (systemSection s c) := by
  set K := (vanishingSubspace k L x).comap (systemSection s)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin (N + 1) → k, c₀ ∉ K :=
    TopologicalSpace.Opens.mem_iSup.mp (hs.symm ▸ trivial :
      x ∈ ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c))
  obtain ⟨ψ, hψc, hψK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := K) hc₀ inferInstance
  set ℓ : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (ψ (Pi.single j 1)) * MvPolynomial.X j
  have hev : ∀ c, MvPolynomial.eval c ℓ = ψ c := by
    intro c
    conv_rhs => rw [pi_eq_sum_univ c]
    simp only [ℓ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨ℓ, fun h => hψc (by rw [← hev, h, map_zero]), fun c hc hcK => hc ?_⟩
  rw [hev, ← Submodule.mem_bot k, ← hψK]
  exact ⟨c, hcK, rfl⟩

end

end MMP.Proof_lem_mmp_foundation_km_very_ample_integral_member

end

section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Intersection

open MMP.Threefold.Bridges MMP.Proof_lem_mmp_foundation_km_very_ample_integral_member in
/-- **An integral very ample member avoiding finitely many closed subsets.** Let `k` be an
algebraically closed field of characteristic zero, `X` a projective variety over `k` of dimension
at least two, `A` a very ample Cartier divisor on `X` and `(Wᵢ)` a finite family of closed
irreducible proper subsets of `X`. Then there is an effective Cartier divisor `A'` linearly
equivalent to `A` whose closed subscheme `Z` is integral and contains none of the `Wᵢ`. -/
@[mmp "lem_mmp_foundation_km_very_ample_integral_member"]
public theorem exists_linearlyEquivalent_isIntegral_subscheme_of_isVeryAmpleDivisor
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProjectiveVariety k (X ↘ Spec (.of k))] (hdim : 2 ≤ topologicalKrullDim X)
    (A : X.CartierDivisor) (hA : IsVeryAmpleDivisor k A)
    {ι : Type*} [Finite ι] (W : ι → Set X) (hWc : ∀ i, IsClosed (W i))
    (hWi : ∀ i, IsIrreducible (W i)) (hWne : ∀ i, W i ≠ Set.univ) :
    ∃ (A' : X.CartierDivisor) (Z : X.IdealSheafData), IsEffective A' ∧ LinearlyEquivalent A' A ∧
      IsSubschemeOfEffective A' Z ∧ IsIntegral Z.subscheme ∧
      ∀ i, ¬ W i ⊆ (Z.support : Set X) := by
  classical
  haveI : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨N, s, hs, himm⟩ := exists_family_isImmersion k A hA
  obtain ⟨⟨U, hUd, hU⟩, -⟩ := exists_dense_open_geometricallyIrreducible_zeroScheme s hs
    (hdim.trans_eq (Scheme.Hom.isEmbedding _).toHomeomorph.isHomeomorph.topologicalKrullDim_eq)
  choose w hw using fun i => (hWi i).nonempty
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  choose ℓ hℓ0 hℓ using fun x => exists_polynomial_mem_nonvanishingLocus s hs x
  haveI := Fintype.ofFinite ι
  have hg : ℓ x₀ * ∏ i, ℓ (w i) ≠ 0 :=
    mul_ne_zero (hℓ0 x₀) (Finset.prod_ne_zero_iff.mpr fun i _ => hℓ0 (w i))
  obtain ⟨c, hcU, hc⟩ := exists_coefficientPoint_mem_and_eval_ne_zero U hUd hg
  rw [map_mul, map_prod] at hc
  have hc₀ := hℓ x₀ c (left_ne_zero_of_mul hc)
  have hci : ∀ i, w i ∈ Stacks.Ample.nonvanishingLocus (MMP.CartierDivisor.sheaf A) (systemSection s
      c) :=
    fun i => hℓ (w i) c (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc) i
      (Finset.mem_univ _))
  obtain ⟨A', hA'e, hA'l, hA'Z⟩ :=
    exists_isEffective_isSubschemeOfEffective_zeroScheme A (systemSection s c) ⟨x₀, hc₀⟩
  exact ⟨A', zeroScheme X (MMP.CartierDivisor.sheaf A) (systemSection s c), hA'e, hA'l, hA'Z, (hU c
      hcU).2.2,
    fun i hsub => notMem_support_zeroScheme _ (hci i) (hsub (hw i))⟩

end MMP.Intersection

end
