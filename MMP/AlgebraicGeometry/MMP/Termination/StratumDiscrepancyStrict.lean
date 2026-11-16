module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumDiscrepancyMonotone
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalFlips
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.MMP.Abundance.SubkltSurfacePluriformFinite
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry

/-!
# Strict increase of stratum discrepancies under a flip

For a flip `X → Y ← X⁺` of projective dlt pairs and corresponding stratum adjunction pairs
`(S, B_S)` and `(S⁺, B_{S⁺})`, a prime divisor `P` of `S⁺` contracted by `S⁺ → Y` has strictly
larger discrepancy over `S⁺` than over `S`.

## Main results

* `MMP.Mori.IsFlip.isDiscrepancy_lt_of_isStratumAdjunctionPair`
-/

namespace MMP.Fold06.LemMmpStratumDiscrepancyStrictTarget

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology MMP.Mori

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

open MMP.Fourfold

/-! ### The reduced closure of a point -/

/-- The closure of a point `s` of `W` with its reduced induced structure. -/
private noncomputable abbrev pointClosure {W : Scheme.{0}} (s : W) : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {s})).subscheme

/-- The inclusion of the reduced closure of a point. -/
private noncomputable abbrev pointClosureι {W : Scheme.{0}} (s : W) : pointClosure s ⟶ W :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {s})).subschemeι

private theorem range_pointClosureι {W : Scheme.{0}} (s : W) :
    Set.range (pointClosureι s) = closure {s} := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure]

/-- A closed immersion from an integral scheme maps the generic point to the generic point of its
image. -/
private theorem isGenericPoint_map_genericPoint {Z W : Scheme.{0}} [IsIntegral Z] (i : Z ⟶ W)
    [IsClosedImmersion i] : IsGenericPoint (i (genericPoint Z)) (Set.range i) := by
  have := (genericPoint_spec Z).image i.base.hom.continuous
  rwa [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at this

private theorem pointClosureι_genericPoint {W : Scheme.{0}} (s : W) :
    haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
    pointClosureι s (genericPoint (pointClosure s)) = s := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  have h1 := isGenericPoint_map_genericPoint (pointClosureι s)
  rw [range_pointClosureι] at h1
  exact h1.eq isGenericPoint_closure

/-- `p s` is the generic point of the stratum for a strict transform `closure {s}` of `S`. -/
private theorem apply_eq_of_comp_eq {W X S : Scheme.{0}} [IsIntegral S] (s : W) (p : W ⟶ X)
    (ι : S ⟶ X) (pS : pointClosure s ⟶ S) (hpS : IsBirationalMorphism pS)
    (hsq : pS ≫ ι = pointClosureι s ≫ p) : p s = ι (genericPoint S) := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  haveI : IsDominant pS := hpS.isDominant
  have h := congrArg (fun g => g.base (genericPoint (pointClosure s))) hsq
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  change ι (pS (genericPoint (pointClosure s))) = p (pointClosureι s
    (genericPoint (pointClosure s))) at h
  rw [pointClosureι_genericPoint, MMP.Positivity.map_genericPoint_eq_of_isDominant] at h
  exact h.symm

private theorem vanishingIdeal_le_of_mem_closure {W : Scheme.{0}} {s w : W}
    (h : w ∈ closure ({s} : Set W)) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {s}) ≤
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w}) :=
  Scheme.IdealSheafData.vanishingIdeal_antimono (by
    change closure {w} ⊆ closure {s}
    exact closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure)

/-- The inclusion of the closure of a point `ι_s t` of `closure {s}`. -/
private noncomputable abbrev pointClosureIncl {W : Scheme.{0}} (s : W) (t : pointClosure s) :
    pointClosure (pointClosureι s t) ⟶ pointClosure s :=
  Scheme.IdealSheafData.inclusion (vanishingIdeal_le_of_mem_closure
    (by rw [← range_pointClosureι]; exact ⟨t, rfl⟩))

private theorem pointClosureIncl_ι {W : Scheme.{0}} (s : W) (t : pointClosure s) :
    pointClosureIncl s t ≫ pointClosureι s = pointClosureι (pointClosureι s t) :=
  Scheme.IdealSheafData.inclusion_subschemeι _

private theorem range_pointClosureIncl {W : Scheme.{0}} (s : W) (t : pointClosure s) :
    Set.range (pointClosureIncl s t) = closure {t} := by
  have hinj := (pointClosureι s).isClosedEmbedding.injective
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have h1 : pointClosureι s (pointClosureIncl s t y) ∈ closure {pointClosureι s t} := by
      rw [← Scheme.Hom.comp_apply, pointClosureIncl_ι, ← range_pointClosureι]
      exact ⟨y, rfl⟩
    rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    rwa [hinj hzx] at hz
  · intro hx
    have h1 : pointClosureι s x ∈ closure {pointClosureι s t} := by
      rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq]
      exact ⟨x, hx, rfl⟩
    rw [← range_pointClosureι] at h1
    obtain ⟨y, hy⟩ := h1
    refine ⟨y, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, pointClosureIncl_ι, hy]

private theorem isClosedImmersion_pointClosureIncl {W : Scheme.{0}} (s : W)
    (t : pointClosure s) : IsClosedImmersion (pointClosureIncl s t) := by
  haveI : IsClosedImmersion (pointClosureIncl s t ≫ pointClosureι s) := by
    rw [pointClosureIncl_ι]; infer_instance
  exact IsClosedImmersion.of_comp _ (pointClosureι s)

private theorem exists_strictTransformPoint {Z S : Scheme.{0}} [IsIntegral Z] [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] (q : Z ⟶ S) [IsProper q]
    (hq : IsBirationalMorphism q) (P : MMP.Mori.PrimeDivisor S) :
    ∃ t : Z, q t = P.genericPoint ∧ IsIso (q.stalkMap t) ∧ Order.coheight t = 1 := by
  have hb : P.genericPoint ∈ biregularLocus q :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq
      P.coheight_genericPoint.le
  set V := biregularLocus q
  haveI : IsIso (q ∣_ V) := isBiregular_biregularLocus q
  let v : V.toScheme := ⟨P.genericPoint, hb⟩
  have e : inv (q ∣_ V) ≫ (q ⁻¹ᵁ V).ι ≫ q = V.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hqt : q ((q ⁻¹ᵁ V).ι ((inv (q ∣_ V)) v)) = P.genericPoint := by
    have := congrArg (fun φ : V.toScheme ⟶ S => φ v) e
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  refine ⟨_, hqt, MMP.isIso_stalkMap_of_mem_biregularLocus q (by rw [hqt]; exact hb), ?_⟩
  have := MMP.Positivity.coheight_map_of_mem_biregularLocus q
    (x := (q ⁻¹ᵁ V).ι ((inv (q ∣_ V)) v)) (by rw [hqt]; exact hb)
  rw [← this, hqt, P.coheight_genericPoint]

private theorem pointClosureIncl_genericPoint {W : Scheme.{0}} (s : W) (t : pointClosure s) :
    haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (pointClosureι s t)
    pointClosureIncl s t (genericPoint (pointClosure (pointClosureι s t))) = t := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (pointClosureι s t)
  apply (pointClosureι s).isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, pointClosureIncl_ι, pointClosureι_genericPoint]

/-- **The strict transform of a prime divisor.** For a proper morphism `p_S` from the closure of
`s` to a normal integral `S`, a local isomorphism at `t` over the generic point of a prime divisor
`T ⊆ S`, the closure of `t` maps onto `T` by a proper birational morphism. -/
private theorem exists_strictTransform {W S T : Scheme.{0}} (s : W)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral T]
    (pS : pointClosure s ⟶ S) [IsProper pS]
    (j : T ⟶ S) [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor S)
    (hP : Set.range j.base = (P.support : Set S))
    (t : pointClosure s) (ht : pS t = P.genericPoint) (hiso : IsIso (pS.stalkMap t)) :
    ∃ pT : pointClosure (pointClosureι s t) ⟶ T,
      pT ≫ j = pointClosureIncl s t ≫ pS ∧ IsProper pT ∧ IsBirationalMorphism pT := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (pointClosureι s t)
  haveI := isClosedImmersion_pointClosureIncl s t
  set jW := pointClosureIncl s t with hjW
  have H : j.ker ≤ (jW ≫ pS).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range j,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range (jW ≫ pS)]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change closure (Set.range (jW ≫ pS)) ⊆ closure (Set.range j)
    apply closure_mono
    rintro _ ⟨x, rfl⟩
    have hx : jW x ∈ closure {t} := by rw [← range_pointClosureIncl]; exact ⟨x, rfl⟩
    have h2 := (specializes_iff_mem_closure.mpr hx).map pS.base.hom.continuous
    rw [ht] at h2
    rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp h2
  set pT := IsClosedImmersion.lift j (jW ≫ pS) H
  have hsq : pT ≫ j = jW ≫ pS := IsClosedImmersion.lift_fac j (jW ≫ pS) H
  haveI : IsProper (pT ≫ j) := by rw [hsq]; infer_instance
  haveI : IsProper pT := IsProper.of_comp pT j
  refine ⟨pT, hsq, inferInstance, ?_⟩
  set g := genericPoint (pointClosure (pointClosureι s t))
  have hjg : jW g = t := pointClosureIncl_genericPoint s t
  have hjT : j (genericPoint T) = P.genericPoint := by
    have h1 := isGenericPoint_map_genericPoint j
    rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact h1.eq isGenericPoint_closure
  have hpTg : pT g = genericPoint T := by
    apply j.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hjg, ht, hjT]
  have hiso' : IsIso (pS.stalkMap (jW g)) := by
    have key : ∀ x, x = t → IsIso (pS.stalkMap x) := by rintro x rfl; exact hiso
    exact key _ hjg
  have hsurj : Function.Surjective (pT.stalkMap g) := by
    have e1 := Scheme.Hom.stalkMap_congr_hom (pT ≫ j) (jW ≫ pS) hsq g
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at e1
    have hs : Function.Surjective (j.stalkMap (pT g) ≫ pT.stalkMap g) := by
      rw [e1]
      have h1 := jW.stalkMap_surjective g
      have h2 := (ConcreteCategory.bijective_of_isIso (pS.stalkMap (jW g))).2
      have h3 := (ConcreteCategory.bijective_of_isIso (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ => φ.base g) hsq))).hom).2
      exact h1.comp (h2.comp h3)
    exact Function.Surjective.of_comp hs
  have hinj : Function.Injective (pT.stalkMap g) := by
    have hF : IsField (T.presheaf.stalk (pT g)) := by
      rw [hpTg]
      exact Field.toIsField _
    letI := hF.toField
    exact (pT.stalkMap g).hom.injective
  haveI : IsIso (pT.stalkMap g) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  haveI : LocallyOfFiniteType pT :=
    LocallyOfFiniteType.of_comp (inferInstance : LocallyOfFiniteType (pT ≫ j))
  have hfin : (irreducibleComponents T).Finite := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, hgU, hU⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap pT g hfin inferInstance
  exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' pT U ⟨g, hgU⟩

/-! ### Counting the components of an snc divisor through a point -/

open Classical in
private theorem coeff_sum_single {W : Scheme.{0}} (E : Finset (MMP.Mori.PrimeDivisor W))
    (G : MMP.Mori.PrimeDivisor W) :
    (∑ G' ∈ E, Finsupp.single G' (1 : ℤ)) G = if G ∈ E then 1 else 0 := by
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

open Classical in
/-- In an snc divisor, at most `coheight x` components pass through a point `x`. -/
private theorem card_filter_mem_le_coheight {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    [IsLocallyNoetherian W] {E : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (x : W) :
    (((E.filter fun G => x ∈ G.support).card : ℕ) : ℕ∞) ≤ Order.coheight x := by
  obtain ⟨n, z, jE, hz, hinj, -⟩ := hE.2 x
  have hn : (n : WithBot ℕ∞) = Order.coheight x := by
    rw [← hz.2, ringKrullDim_stalk_eq_coheight]
  have hmem : ∀ G ∈ E.filter (fun G => x ∈ G.support),
      G ∈ (∑ G' ∈ E, Finsupp.single G' (1 : ℤ)).support ∧ x ∈ G.support := by
    intro G hG
    rw [Finset.mem_filter] at hG
    refine ⟨?_, hG.2⟩
    rw [Finsupp.mem_support_iff, coeff_sum_single, if_pos hG.1]
    exact one_ne_zero
  let ι : (E.filter fun G => x ∈ G.support) → Fin n := fun G => jE ⟨G.1, hmem G.1 G.2⟩
  have hι : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.mk.inj (hinj hab))
  have h1 := Fintype.card_le_of_injective ι hι
  rw [Fintype.card_coe, Fintype.card_fin] at h1
  have h2 : ((n : ℕ) : ℕ∞) = Order.coheight x := by exact_mod_cast hn
  rw [← h2]
  exact_mod_cast h1

private theorem isClosed_support {W : Scheme.{0}} (G : MMP.Mori.PrimeDivisor W) :
    IsClosed (G.support : Set W) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure

private theorem isSNC_sum_single_of_subset {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    {E T : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (hTE : T ⊆ E) :
    DivisorWithCoeffs.IsSNC sW (∑ G ∈ T, Finsupp.single G (1 : ℤ)) := by
  classical
  refine hE.of_support_subset fun G hG => ?_
  rw [Finsupp.mem_support_iff, coeff_sum_single] at hG ⊢
  split_ifs at hG with h
  · rw [if_pos (hTE h)]; exact one_ne_zero
  · exact absurd rfl hG

/-- At a point `y`, the reduced ideal of `closure {y}` is the maximal ideal. -/
private theorem stalk_vanishingIdeal_closure_self {W : Scheme.{0}} (y : W) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})) y =
      IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  have hg := pointClosureι_genericPoint y
  have hk := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {y})) (genericPoint (pointClosure y))
  have hmax := IsLocalRing.ker_eq_maximalIdeal ((pointClosureι y).stalkMap
    (genericPoint (pointClosure y))).hom ((pointClosureι y).stalkMap_surjective _)
  rw [hmax] at hk
  change IsLocalRing.maximalIdeal (W.presheaf.stalk (pointClosureι y _)) = _ at hk
  rw [hg] at hk
  exact hk.symm

open Classical in
/-- **Transversality.** The restriction to the stratum `closure {s}` of an snc component `G₀`
through the codimension-one point `t` of the stratum has multiplicity one along `closure {t}`. -/
private theorem coeff_isPullback_single_eq_one
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW] [QuasiCompact sW]
    (hsm : IsSmoothScheme sW)
    {E T : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (hTE : T ⊆ E)
    {s : W} (hTs : ∀ G ∈ T, s ∈ G.support) (hsc : Order.coheight s = T.card)
    {G0 : MMP.Mori.PrimeDivisor W} (hG0 : G0 ∈ E)
    [IsLocallyNoetherian (pointClosure s)] [IsNormal (pointClosure s)]
    (t : pointClosure s) (hcoh : Order.coheight t = 1) (hwG : pointClosureι s t ∈ G0.support)
    (hwc : Order.coheight (pointClosureι s t) = (insert G0 T).card)
    {hgen : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor W)}
    {C : Divisor (pointClosure s)}
    (hC : Divisor.IsPullback (pointClosureι s) (Finsupp.single G0 (1 : ℤ) : Divisor W) hgen C) :
    C.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh) = 1 := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  set P : MMP.Mori.PrimeDivisor (pointClosure s) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh with hPdef
  have hPg : P.genericPoint = t := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t hcoh
  obtain ⟨n, hn, hCn⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder G0
    (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm G0) hC P
  rw [hCn]
  set w := pointClosureι s t with hw
  have hws : w ∈ closure ({s} : Set W) := by rw [← range_pointClosureι]; exact ⟨t, rfl⟩
  have hwT : ∀ G ∈ insert G0 T, w ∈ G.support := by
    intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact hwG
    · exact closure_minimal (Set.singleton_subset_iff.mpr (hTs G hG)) (isClosed_support G) hws
  have hsnc' := isSNC_sum_single_of_subset hE (Finset.insert_subset hG0 hTE)
  have hsncT := isSNC_sum_single_of_subset hE hTE
  obtain ⟨-, -, hstw⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW hsnc' hwT hwc
  obtain ⟨-, -, hsts⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW hsncT hTs hsc
  have e1 := hstw w (subset_closure rfl)
  rw [stalk_vanishingIdeal_closure_self, Finset.iSup_insert] at e1
  rw [← hsts w hws] at e1
  have hk := Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {s})) t
  have hmap : Ideal.map ((pointClosureι s).stalkMap t).hom
      (IdealSheafData.stalk G0.idealSheaf w) = IsLocalRing.maximalIdeal _ := by
    have h1 := IsLocalRing.map_maximalIdeal_of_surjective ((pointClosureι s).stalkMap t).hom
      ((pointClosureι s).stalkMap_surjective t)
    change Ideal.map _ (IsLocalRing.maximalIdeal (W.presheaf.stalk w)) = _ at h1
    rw [e1, Ideal.map_sup, ← hk, (Ideal.map_eq_bot_iff_le_ker _).mpr le_rfl, sup_bot_eq] at h1
    exact h1
  have hcomap : IdealSheafData.stalk (G0.idealSheaf.comap (pointClosureι s)) t =
      IsLocalRing.maximalIdeal _ := by
    rw [IdealSheafData.stalk_comap]; exact hmap
  have hdvr : IsDiscreteValuationRing ((pointClosure s).presheaf.stalk t) := by
    have := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing P
    change IsDiscreteValuationRing ((pointClosure s).presheaf.stalk P.genericPoint) at this
    rw [hPg] at this
    exact this
  have hn' : MMP.Resolution.idealOrder
      (IdealSheafData.stalk (G0.idealSheaf.comap (pointClosureι s)) t) = n := by
    rw [← hPg]; exact hn
  rw [hcomap, MMP.Threefold.Resolution.idealOrder_maximalIdeal] at hn'
  exact_mod_cast (show (n : ℕ∞) = 1 from hn'.symm)

/-! ### Dimension of the closure of a point -/

private theorem topologicalKrullDim_image_of_isEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hf : IsEmbedding f) (C : Set A) :
    topologicalKrullDim (f '' C) = topologicalKrullDim C := by
  have he : IsEmbedding (f ∘ ((↑) : C → A)) := hf.comp IsEmbedding.subtypeVal
  have h1 := IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph
  have h2 : Set.range (f ∘ ((↑) : C → A)) = f '' C := by rw [Set.range_comp, Subtype.range_coe]
  rw [h1, h2]

/-- Dimension bookkeeping: from `a + x = N`, `b + z = N` and `a + y = b` in `WithBot ℕ∞`,
`x = z + y`. -/
private theorem coheight_arith {a b : WithBot ℕ∞} {x y z : ℕ∞} {N : ℕ}
    (h1 : a + (x : WithBot ℕ∞) = N) (h2 : b + (z : WithBot ℕ∞) = N)
    (h3 : a + (y : WithBot ℕ∞) = b) : x = z + y := by
  lift a to ℕ∞ using (by rintro rfl; simp at h1)
  lift b to ℕ∞ using (by rintro rfl; simp at h2)
  norm_cast at h1 h2 h3
  lift a to ℕ using (by rintro rfl; simp at h1)
  lift x to ℕ using (by rintro rfl; simp at h1)
  lift b to ℕ using (by rintro rfl; simp at h2)
  lift z to ℕ using (by rintro rfl; simp at h2)
  lift y to ℕ using (by rintro rfl; simp at h3)
  norm_cast at h1 h2 h3 ⊢
  omega

/-- Cancellation of a finite coheight: `a + c = N = b + c` forces `a = b`. -/
private theorem eq_of_add_coheight_eq {a b : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h1 : a + (c : WithBot ℕ∞) = N) (h2 : b + (c : WithBot ℕ∞) = N) : a = b := by
  lift a to ℕ∞ using (by rintro rfl; simp at h1)
  lift b to ℕ∞ using (by rintro rfl; simp at h2)
  norm_cast at h1 h2 ⊢
  lift a to ℕ using (by rintro rfl; simp at h1)
  lift b to ℕ using (by rintro rfl; simp at h2)
  lift c to ℕ using (by rintro rfl; simp at h1)
  norm_cast at h1 h2 ⊢
  omega

/-- Coheights add along the closure of a point of a variety. -/
private theorem coheight_pointClosureι {W : Scheme.{0}} [IsIntegral W] (sW : W ⟶ Spec (.of k))
    [LocallyOfFiniteType sW] (s : W) (t : pointClosure s) :
    Order.coheight (pointClosureι s t) = Order.coheight s + Order.coheight t := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW (pointClosureι s t)
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sW s
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (pointClosureι s ≫ sW) t
  have hemb := (pointClosureι s).isClosedEmbedding.isEmbedding
  have e1 : topologicalKrullDim (pointClosure s) = topologicalKrullDim (closure {s} : Set W) := by
    rw [← range_pointClosureι, ← Set.image_univ, topologicalKrullDim_image_of_isEmbedding hemb]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm
  have e2 : topologicalKrullDim (closure {t} : Set (pointClosure s)) =
      topologicalKrullDim (closure {pointClosureι s t} : Set W) := by
    rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq,
      topologicalKrullDim_image_of_isEmbedding hemb]
  rw [e2, e1] at h3
  have hW := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sW
  rw [hW] at h1 h2
  exact coheight_arith h1 h2 h3

/-- A pull-back has coefficient zero along a prime divisor whose generic point maps off the
support. -/
private theorem coeff_isPullback_eq_zero_of_notMem {V Y : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [IsLocallyNoetherian Y] [IsNormal Y] {f : V ⟶ Y} {B : Divisor Y}
    {hB : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ B.supp}
    {B' : Divisor V} (h : B.IsPullback f hB B') (E : MMP.Mori.PrimeDivisor V)
    (hE : f E.genericPoint ∉ B.supp) : B'.coeff E = 0 := by
  set U : Y.Opens := ⟨(B.supp : Set Y)ᶜ, B.supp.isClosed.isOpen_compl⟩
  have hU : B.IsLocalEquation U 1 := by
    rintro G ⟨x, hxG, hxU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hxU (DivisorWithCoeffs.support_subset_supp hne hxG)
  have hEU : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hE
  rw [h U 1 hU E hEU]
  have hZp := E.map_componentGenericPoint_mem f hEU
  rw [pullbackComponent_eq hB hU hZp (mem_pointComponent _) 1 (by
    simp only [Units.val_one, map_one]; rfl), map_one]
  exact E.ordUnit_one

/-- A point of codimension one on a prime divisor is its generic point. -/
private theorem eq_genericPoint_of_mem_support {W : Scheme.{0}} {G : MMP.Mori.PrimeDivisor W}
    {s : W} (hs : s ∈ G.support) (hc : Order.coheight s = 1) : s = G.genericPoint := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hs
  have hsG : G.genericPoint ⤳ s := specializes_iff_mem_closure.mpr hs
  by_cases h2 : s ⤳ G.genericPoint
  · exact (hsG.antisymm h2).eq.symm
  · have hlt : s < G.genericPoint := lt_of_le_not_ge hsG h2
    have h3 := Order.coheight_add_one_le hlt
    rw [hc, MMP.Mori.PrimeDivisor.coheight_genericPoint] at h3
    exact absurd h3 (by decide)

open Classical in
/-- The components other than `closure {t}` of the restriction of `G₀` to the stratum miss
`closure {t}`. -/
private theorem coeff_isPullback_single_eq_zero
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW] [QuasiCompact sW]
    {E T : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (hTE : T ⊆ E)
    {s : W} (hTs : ∀ G ∈ T, s ∈ G.support)
    {G0 : MMP.Mori.PrimeDivisor W} (hG0 : G0 ∈ E)
    [IsLocallyNoetherian (pointClosure s)] [IsNormal (pointClosure s)]
    (t : pointClosure s) (hcoh : Order.coheight t = 1) (hwG : pointClosureι s t ∈ G0.support)
    (hwc : Order.coheight (pointClosureι s t) = (insert G0 T).card)
    {hgen : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor W)}
    {C : Divisor (pointClosure s)}
    (hC : Divisor.IsPullback (pointClosureι s) (Finsupp.single G0 (1 : ℤ) : Divisor W) hgen C)
    (Q : MMP.Mori.PrimeDivisor (pointClosure s))
    (hQ : Q ≠ AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh)
    (hQt : (Q.support ∩ closure {t}).Nonempty) : C.coeff Q = 0 := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  refine coeff_isPullback_eq_zero_of_notMem hC Q fun hy => hQ ?_
  replace hy : pointClosureι s Q.genericPoint ∈ G0.support :=
    DivisorWithCoeffs.supp_single_le _ _ hy
  set w := pointClosureι s t
  obtain ⟨x, hxQ, hxt⟩ := hQt
  have hws : w ∈ closure ({s} : Set W) := by rw [← range_pointClosureι]; exact ⟨t, rfl⟩
  have hwT : ∀ G ∈ insert G0 T, w ∈ G.support := by
    intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact hwG
    · exact closure_minimal (Set.singleton_subset_iff.mpr (hTs G hG)) (isClosed_support G) hws
  obtain ⟨-, -, hstw⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW
    (isSNC_sum_single_of_subset hE (Finset.insert_subset hG0 hTE)) hwT hwc
  have hx' : pointClosureι s x ∈ closure {w} := by
    rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq]
    exact ⟨x, hxt, rfl⟩
  have hQx : Q.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ hxQ
  have hsp := hQx.map (pointClosureι s).base.hom.continuous
  have hyw : pointClosureι s Q.genericPoint ∈ closure ({w} : Set W) := by
    have := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})) hsp).mpr (by
        rw [hstw _ hx']
        refine iSup₂_le fun G hG => ?_
        refine (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes G.idealSheaf hsp).mp ?_
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hy
        · have hys : pointClosureι s Q.genericPoint ∈ closure ({s} : Set W) := by
            rw [← range_pointClosureι]; exact ⟨_, rfl⟩
          exact closure_minimal (Set.singleton_subset_iff.mpr (hTs G hG)) (isClosed_support G) hys)
    change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})).support :
      Set W) at this
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at this
    exact this
  rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq] at hyw
  obtain ⟨q, hq, hqy⟩ := hyw
  have hqQ : q = Q.genericPoint := (pointClosureι s).isClosedEmbedding.injective hqy
  rw [hqQ] at hq
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  refine eq_genericPoint_of_mem_support ?_ Q.coheight_genericPoint
  rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]

/-! ### Coefficients of pull-backs along local isomorphisms -/

/-- Along a prime divisor at whose generic point the morphism is a local isomorphism, the
pull-back of a `ℚ`-Cartier divisor has the coefficient of the image prime divisor. -/
private theorem coeff_qDivisor_isPullback_of_isIso {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y}
    (E : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = P.genericPoint) [IsIso (f.stalkMap E.genericPoint)]
    {L : QDivisor Y} (hL : L.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : QDivisor X} (h : L.IsPullback f hB L') : L'.coeff E = L.coeff P := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hL.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have h1 := MMP.Positivity.coeff_eq_of_isPullback E P heq hDc hp
  have e1 := congrArg (fun G : QDivisor X => G.coeff E) hD'
  have e2 := congrArg (fun G : QDivisor Y => G.coeff P) hD
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul] at e1 e2
  rw [h1] at e1
  have hm' : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact mul_left_cancel₀ hm' (e1.symm.trans e2)

/-! ### Independence of the canonical divisor -/

/-- A discrepancy for one canonical divisor is a discrepancy for every canonical divisor. -/
private theorem isDiscrepancy_of_isCanonicalDivisor {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K K' : Divisor X} {Δ : QDivisor X} {D : DivisorOver k sX} {a : ℚ}
    (h : IsDiscrepancy sX n K Δ D a) (hK' : K'.IsCanonicalDivisor sX n) :
    IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, hK, m, hm, hC, rest⟩ := h
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK
  refine ⟨hX, hK', m, hm, ?_, rest⟩
  obtain ⟨D₀, hD₀, hD₀c⟩ := hC
  refine ⟨D₀ + (m : ℤ) • principalDivisor φ, ?_,
    hD₀c.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩
  have hK'eq : K' = K + principalDivisor φ := by rw [← hφ]; abel
  rw [map_add, hD₀, map_zsmul, hK'eq, map_add, smul_add, smul_add, smul_add]
  abel

/-- A crepant boundary for one canonical divisor is a crepant boundary for every one. -/
private theorem isCrepantBoundary_of_isCanonicalDivisor {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} {n : ℕ}
    {K K' : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)}
    {hf : IsBirationalMorphism f} {ΔY : QDivisor Y}
    (h : IsCrepantBoundary sX n K Δ f hY hf ΔY) (hK' : K'.IsCanonicalDivisor sX n) :
    IsCrepantBoundary sX n K' Δ f hY hf ΔY :=
  fun F => isDiscrepancy_of_isCanonicalDivisor (h F) hK'

/-! ### One adjunction step on the resolution: the new component -/

open Classical in
/-- The coefficient of `B_W - ∑_{G ∈ T} c_G G` at a prime divisor. -/
private theorem coeff_sub_sum_smul_single {W : Scheme.{0}} (BW : QDivisor W)
    (T : Finset (MMP.Mori.PrimeDivisor W)) (G : MMP.Mori.PrimeDivisor W) :
    (BW - ∑ G' ∈ T, BW.coeff G' • (Finsupp.single G' 1 : QDivisor W)).coeff G =
      if G ∈ T then 0 else BW.coeff G := by
  change (BW - ∑ G' ∈ T, BW.coeff G' • (Finsupp.single G' 1 : QDivisor W)) G = _
  rw [Finsupp.sub_apply, Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', DivisorWithCoeffs.coeff_apply]
  split_ifs <;> simp

open Classical in
/-- If only one component `G₀` of `A` passes through the image of the generic point of `Q`, and
`G₀` restricts with multiplicity one along `Q`, the pull-back of `A` has the coefficient of `G₀`
along `Q`. -/
private theorem coeff_isPullback_eq_coeff_single {V Y : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {f : V ⟶ Y} (Q : MMP.Mori.PrimeDivisor V) (G0 : MMP.Mori.PrimeDivisor Y)
    (hG0c : Divisor.IsCartier (Finsupp.single G0 (1 : ℤ) : Divisor Y))
    {hg0 : ∀ Z : irreducibleComponents V,
      f (componentGenericPoint V Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor Y)}
    {C : Divisor V} (hC : Divisor.IsPullback f (Finsupp.single G0 (1 : ℤ) : Divisor Y) hg0 C)
    (hCQ : C.coeff Q = 1) {A : QDivisor Y} (hA : A.IsQCartier)
    (hAG : ∀ G : MMP.Mori.PrimeDivisor Y, f Q.genericPoint ∈ G.support → G ≠ G0 → A.coeff G = 0)
    {hgA : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ A.supp}
    {A' : QDivisor V} (hA' : A.IsPullback f hgA A') : A'.coeff Q = A.coeff G0 := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hA.exists_pos
  obtain ⟨D', hD', hpD⟩ := hA' m hm D hD hDc
  have hDG : ∀ G, D.coeff G = m * A.coeff G := by
    intro G
    have := congrArg (fun B : QDivisor Y => B.coeff G) hD
    simpa [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor] using this
  set c : ℤ := D.coeff G0
  set D1 : Divisor Y := D - c • (Finsupp.single G0 (1 : ℤ) : Divisor Y)
  have hD1c : D1.IsCartier := hDc.sub (hG0c.zsmul c)
  have hD1Q : f Q.genericPoint ∉ D1.supp := by
    intro hmem
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    apply hG
    change D G - (c • (Finsupp.single G0 (1 : ℤ) : Divisor Y)) G = 0
    by_cases hGG : G = G0
    · subst hGG; simp [c, DivisorWithCoeffs.coeff_apply]
    · have h1 : (D G : ℚ) = 0 := by
        have := hDG G
        rw [DivisorWithCoeffs.coeff_apply] at this
        rw [this, hAG G hxG hGG, mul_zero]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, Ne.symm hGG, if_false, smul_zero,
        sub_zero]
      exact_mod_cast h1
  have hsuppD : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ D.supp := by
    intro Z hZ
    apply hgA Z
    rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ
  have hsupp1 : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ D1.supp := by
    intro Z hZ
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    have hG' : D G ≠ 0 ∨ (c • (Finsupp.single G0 (1 : ℤ) : Divisor Y)) G ≠ 0 := by
      by_contra h
      push Not at h
      exact hG (by change D G - _ = 0; rw [h.1, h.2, sub_zero])
    rcases hG' with h | h
    · exact hsuppD Z (DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, h, hxG⟩)
    · have hGG : G = G0 := by
        by_contra hne
        simp [Finsupp.single_apply, Ne.symm hne] at h
      subst hGG
      exact hg0 Z (DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_apply])
        hxG)
  obtain ⟨D1', hD1'⟩ := hD1c.exists_isPullback hsupp1
  have hD1'Q : D1'.coeff Q = 0 := coeff_isPullback_eq_zero_of_notMem hD1' Q hD1Q
  have hsuppc : ∀ Z : irreducibleComponents V,
      f (componentGenericPoint V Z) ∉
        DivisorWithCoeffs.supp (c • (Finsupp.single G0 (1 : ℤ) : Divisor Y)) := by
    intro Z hZ
    rw [Finsupp.smul_single] at hZ
    exact hg0 Z (DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_apply])
      (DivisorWithCoeffs.supp_single_le _ _ hZ))
  have hpc := hC.zsmul hG0c c hsuppc
  have hsum := hD1'.add hD1c (hG0c.zsmul c) (by
    intro Z hZ
    apply hsuppD Z
    have : D1 + c • (Finsupp.single G0 (1 : ℤ) : Divisor Y) = D := by
      simp only [D1, sub_add_cancel]
    rwa [this] at hZ) hpc
  have heq : D' = D1' + c • C := hpD.eq hDc (hsum.of_eq (by simp [D1]))
  have hcoef : (D'.coeff Q : ℚ) = m * A.coeff G0 := by
    rw [heq, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, hD1'Q, hCQ, zero_add,
      smul_eq_mul, mul_one]
    exact_mod_cast hDG G0
  have hD'Q := congrArg (fun B : QDivisor V => B.coeff Q) hD'
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, zsmul_eq_mul] at hD'Q
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hm'
  rw [← hcoef]
  exact_mod_cast hD'Q.symm

/-! ### One adjunction step on the resolution -/

/-- Generic points of the components of an integral scheme map under a dominant morphism off the
support of any divisor. -/
private theorem map_componentGenericPoint_notMem_supp {V Y : Scheme.{0}} [IsIntegral V]
    [IsIntegral Y] (f : V ⟶ Y) [IsDominant f] {R : Type*} [Zero R] (L : DivisorWithCoeffs R Y)
    (Z : irreducibleComponents V) : f (componentGenericPoint V Z) ∉ L.supp := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint,
    MMP.Positivity.map_genericPoint_eq_of_isDominant]
  exact MMP.Fourfold.genericPoint_notMem_supp L

/-- Every rational `1`-fold form is a top form. -/
private theorem exists_toPluriForms_eq {S : Scheme.{0}} [IsIntegral S]
    {sS : S ⟶ Spec (.of k)} {d : ℕ} (σ : RationalPluriForms sS d 1) :
    ∃ ω : RationalTopForms sS d, ω.toPluriForms sS = σ := by
  letI := functionFieldAlgebra sS
  set e := (PiTensorProduct.subsingletonEquiv (0 : Fin 1) :
    PiTensorProduct S.functionField (fun _ : Fin 1 => ⋀[S.functionField]^d Ω[S.functionField⁄k])
      ≃ₗ[S.functionField] ⋀[S.functionField]^d Ω[S.functionField⁄k])
  refine ⟨e σ, ?_⟩
  change PiTensorProduct.tprod S.functionField (fun _ : Fin 1 => e σ) = σ
  exact e.injective (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)

private theorem ne_zero_of_toPluriForms_eq {S : Scheme.{0}} [IsIntegral S]
    {sS : S ⟶ Spec (.of k)} {d : ℕ} {σ : RationalPluriForms sS d 1}
    {ω : RationalTopForms sS d} (hω : ω.toPluriForms sS = σ) (hσ : σ ≠ 0) : ω ≠ 0 := by
  rintro rfl
  apply hσ
  rw [← hω]
  exact (PiTensorProduct.tprod _).map_coord_zero (0 : Fin 1) rfl

/-- The divisor of a rational form does not depend on how the structure morphism is written. -/
private theorem divisorOfForm_cast {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {s₁ s₂ : Z ⟶ Spec (.of k)} (h : s₁ = s₂)
    [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂] {d : ℕ} {m : ℤ}
    (hT : RationalPluriForms s₁ d m = RationalPluriForms s₂ d m) (τ : RationalPluriForms s₁ d m) :
    divisorOfForm (cast hT τ) = divisorOfForm τ := by
  subst h
  rfl

/-- A pull-back along a morphism equal to `g` is a pull-back along `g`. -/
private theorem qDivisor_isPullback_congr {V Y : Scheme.{0}} [IsLocallyNoetherian V] [IsNormal V]
    [IsLocallyNoetherian Y] [IsNormal Y] {f g : V ⟶ Y} (hfg : f = g) {L : QDivisor Y}
    {hf : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ L.supp}
    {hg : ∀ Z : irreducibleComponents V, g (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback f hf L') : L.IsPullback g hg L' := by
  subst hfg
  exact h

/-- A pull-back of a divisor equal to `L₂` is a pull-back of `L₂`. -/
private theorem qDivisor_isPullback_of_eq {V Y : Scheme.{0}} [IsLocallyNoetherian V]
    [IsNormal V] [IsLocallyNoetherian Y] [IsNormal Y] {f : V ⟶ Y} {L₁ L₂ : QDivisor Y}
    (hL : L₁ = L₂) {h₁ : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ L₁.supp}
    {h₂ : ∀ Z : irreducibleComponents V, f (componentGenericPoint V Z) ∉ L₂.supp}
    {L' : QDivisor V} (h : L₁.IsPullback f h₁ L') : L₂.IsPullback f h₂ L' := by
  subst hL
  exact h

open Classical in
/-- **Restriction to the next stratum.** With `A = B_W - ∑_{G ∈ T} c_G G` restricting to `Θ` on
`closure {s}`, `G₀` the component through `w = ι_s t` of coefficient `c_{G₀} = 1`, and
`R = (Θ - closure {t})|_{closure {t}}`, the divisor `B_W - ∑_{G ∈ T ∪ {G₀}} c_G G` restricts to
`R` on `closure {w}`. -/
private theorem isPullback_next_of_isPullback
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW] [QuasiCompact sW] (hsm : IsSmoothScheme sW)
    {E T : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (hTE : T ⊆ E)
    {s : W} (hTs : ∀ G ∈ T, s ∈ G.support) (hsc : Order.coheight s = T.card)
    {BW : QDivisor W} {G0 : MMP.Mori.PrimeDivisor W} (hG0 : G0 ∈ E) (hG0T : G0 ∉ T)
    (hc0 : BW.coeff G0 = 1) (hsG0 : s ∉ G0.support)
    [IsLocallyNoetherian (pointClosure s)] [IsNormal (pointClosure s)]
    (t : pointClosure s) (hcoh : Order.coheight t = 1) (hwG : pointClosureι s t ∈ G0.support)
    (hwc : Order.coheight (pointClosureι s t) = (insert G0 T).card)
    [IsLocallyNoetherian (pointClosure (pointClosureι s t))]
    [IsNormal (pointClosure (pointClosureι s t))]
    {hgen : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).supp}
    {Θ : QDivisor (pointClosure s)}
    (hΘ : (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).IsPullback
      (pointClosureι s) hgen Θ)
    {hR : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureIncl s t (componentGenericPoint _ Z) ∉
        (Θ - Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh :
          MMP.Mori.PrimeDivisor (pointClosure s)) 1).supp}
    {R : QDivisor (pointClosure (pointClosureι s t))}
    (hR' : (Θ - Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh :
      MMP.Mori.PrimeDivisor (pointClosure s)) 1).IsPullback (pointClosureIncl s t) hR R)
    (hgen' : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureι (pointClosureι s t) (componentGenericPoint _ Z) ∉
        (BW - ∑ G ∈ insert G0 T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).supp) :
    (BW - ∑ G ∈ insert G0 T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).IsPullback
      (pointClosureι (pointClosureι s t)) hgen' R := by
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (pointClosureι s t)
  haveI : CompactSpace (pointClosure s) := (pointClosureι s).isClosedEmbedding.compactSpace
  haveI : CompactSpace (pointClosure (pointClosureι s t)) :=
    (pointClosureι (pointClosureι s t)).isClosedEmbedding.compactSpace
  haveI := isClosedImmersion_pointClosureIncl s t
  set Pt : MMP.Mori.PrimeDivisor (pointClosure s) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh with hPtdef
  have hPtg : Pt.genericPoint = t :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t hcoh
  set A := BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) with hAdef
  set A' := BW - ∑ G ∈ insert G0 T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) with hA'def
  have hsplit : A = A' + Divisor.toQDivisor (Finsupp.single G0 (1 : ℤ)) := by
    ext G
    change A.coeff G = (A' + Divisor.toQDivisor (Finsupp.single G0 (1 : ℤ))).coeff G
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_sub_sum_smul_single,
      coeff_sub_sum_smul_single]
    by_cases hG : G = G0
    · subst hG
      simp [hG0T, hc0, DivisorWithCoeffs.coeff_apply]
    · have h1 : DivisorWithCoeffs.coeff (Finsupp.single G0 (1 : ℤ) : Divisor W) G = 0 := by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg (fun h => hG h.symm)]
      rw [h1]
      simp [Finset.mem_insert, hG]
  have hA'q : A'.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm A'
  have hG0cart : Divisor.IsCartier (Finsupp.single G0 (1 : ℤ) : Divisor W) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hgs : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) = s := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint]
  have hg0 : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor W) := by
    intro Z hZ
    rw [hgs] at hZ
    exact hsG0 (DivisorWithCoeffs.supp_single_le _ _ hZ)
  obtain ⟨C, hC⟩ := hG0cart.exists_isPullback hg0
  have hCPt : C.coeff Pt = 1 := coeff_isPullback_single_eq_one hsm hE hTE hTs hsc hG0 t hcoh hwG
    hwc hC
  have hCQ : ∀ Q : MMP.Mori.PrimeDivisor (pointClosure s), Q ≠ Pt →
      (Q.support ∩ closure {t}).Nonempty → C.coeff Q = 0 :=
    fun Q hQ hQt => coeff_isPullback_single_eq_zero hE hTE hTs hG0 t hcoh hwG hwc hC Q hQ hQt
  have hg0Q : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        (Divisor.toQDivisor (Finsupp.single G0 (1 : ℤ) : Divisor W)).supp := by
    intro Z hZ
    rw [Divisor.supp_toQDivisor] at hZ
    exact hg0 Z hZ
  have hCq := QDivisor.isPullback_toQDivisor hG0cart hg0Q hC
  -- the restriction of `A'` to `closure {s}`
  have hgA' : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉ A'.supp := by
    intro Z hZ
    obtain ⟨G, hG, hsG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    rw [hgs] at hsG
    have hA'G : A'.coeff G =
        A.coeff G - DivisorWithCoeffs.coeff (Finsupp.single G0 (1 : ℤ) : Divisor W) G := by
      rw [hsplit, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]; ring
    have hAG : A.coeff G = 0 := by
      by_contra hne
      exact hgen (MMP.Mori.pointComponent (genericPoint _)) (by
        rw [hgs]; exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, hne, hsG⟩)
    have hsG' : DivisorWithCoeffs.coeff (Finsupp.single G0 (1 : ℤ) : Divisor W) G = 0 := by
      by_contra hne
      exact hg0 (MMP.Mori.pointComponent (genericPoint _)) (by
        rw [hgs]; exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, hne, hsG⟩)
    apply hG
    rw [hA'G, hAG, hsG']
    simp
  obtain ⟨ΘA', hΘA', -⟩ := hA'q.existsUnique_isPullback hgA'
  have hsum := MMP.Mori.QDivisor.IsPullback.add hA'q (QDivisor.isQCartier_toQDivisor hG0cart)
    hΘA' hCq (by rw [← hsplit]; exact hgen)
  have hΘeq : Θ = ΘA' + Divisor.toQDivisor C :=
    ((MMP.Fourfold.isQCartier_of_isSmoothScheme hsm A).existsUnique_isPullback hgen).unique hΘ
      (qDivisor_isPullback_of_eq hsplit.symm hsum)
  -- the correction term vanishes on `closure {t}`
  set C'' : QDivisor (pointClosure s) := Divisor.toQDivisor C - Finsupp.single Pt 1 with hC''
  have hsmZ : IsSmoothScheme ((pointClosureι s) ≫ sW) := by
    obtain ⟨-, h, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW
      (isSNC_sum_single_of_subset hE hTE) hTs hsc
    exact h
  have hC''q : C''.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsmZ C''
  have hC''coef : ∀ Q : MMP.Mori.PrimeDivisor (pointClosure s),
      (Q.support ∩ closure {t}).Nonempty → C''.coeff Q = 0 := by
    intro Q hQt
    rw [hC'', DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor]
    by_cases hQ : Q = Pt
    · subst hQ
      rw [hCPt, DivisorWithCoeffs.coeff_single_self]; norm_num
    · rw [hCQ Q hQ hQt, DivisorWithCoeffs.coeff_single_of_ne (fun h => hQ h.symm)]; norm_num
  have hgC'' : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureIncl s t (componentGenericPoint _ Z) ∉ C''.supp := by
    intro Z hZ
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    refine hQ (hC''coef Q ⟨_, hxQ, ?_⟩)
    rw [← range_pointClosureIncl]; exact ⟨_, rfl⟩
  obtain ⟨R'', hR'', -⟩ := hC''q.existsUnique_isPullback hgC''
  have hR''0 : R'' = 0 := by
    ext Q'
    change R''.coeff Q' = 0
    refine MMP.Mori.QDivisor.IsPullback.coeff_eq_zero_of_notMem hC''q hR'' Q' fun hmem => ?_
    obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    refine hQ (hC''coef Q ⟨_, hxQ, ?_⟩)
    rw [← range_pointClosureIncl]; exact ⟨_, rfl⟩
  -- the restriction of `ΘA'` to `closure {t}`
  have hgt : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureIncl s t (componentGenericPoint _ Z) = Pt.genericPoint := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureIncl_genericPoint, hPtg]
  have hΘPt : (Θ - Finsupp.single Pt 1).coeff Pt = 0 := by
    by_contra hne
    exact hR (MMP.Mori.pointComponent (genericPoint _)) (by
      rw [hgt]
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨Pt, hne, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩)
  have hΘA'Pt : ΘA'.coeff Pt = 0 := by
    have h1 : Θ.coeff Pt = ΘA'.coeff Pt + (C.coeff Pt : ℚ) := by
      rw [hΘeq, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have h2 : (Θ - Finsupp.single Pt 1).coeff Pt = Θ.coeff Pt - 1 := by
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self]
    rw [hCPt] at h1
    rw [h2] at hΘPt
    push_cast at h1
    linarith
  have hgΘA' : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureIncl s t (componentGenericPoint _ Z) ∉ ΘA'.supp := fun Z => by
    rw [hgt]
    exact MMP.CyclicChartDifferent.genericPoint_notMem_supp_of_coeff_eq_zero hΘA'Pt
  have hΘA'q := MMP.Fourfold.isQCartier_of_isSmoothScheme hsmZ ΘA'
  obtain ⟨RA', hRA', -⟩ := hΘA'q.existsUnique_isPullback hgΘA'
  have heq2 : ΘA' + C'' = Θ - Finsupp.single Pt 1 := by rw [hΘeq, hC'']; abel
  have hsum2 := MMP.Mori.QDivisor.IsPullback.add hΘA'q hC''q hRA' hR'' (by
    intro Z; rw [heq2]; exact hR Z)
  have hReq : R = RA' := by
    have h1 := ((MMP.Fourfold.isQCartier_of_isSmoothScheme hsmZ
      (Θ - Finsupp.single Pt 1)).existsUnique_isPullback hR).unique hR'
      (qDivisor_isPullback_of_eq heq2 hsum2)
    rw [h1, hR''0, add_zero]
  have hcomp := MMP.Mori.QDivisor.IsPullback.comp hΘA' hRA' (fun Z => by
    rw [pointClosureIncl_ι]; exact hgen' Z)
  rw [hReq]
  exact qDivisor_isPullback_congr (pointClosureIncl_ι s t) hcomp

/-- An integral scheme of dimension `0`, locally of finite type over `k`, has no prime divisor. -/
private theorem isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero {Z : Scheme.{0}}
    [IsIntegral Z] (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ]
    (h : topologicalKrullDim Z = 0) : IsEmpty (MMP.Mori.PrimeDivisor Z) := by
  refine ⟨fun F => ?_⟩
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ F.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, h] at h1
  induction htd : topologicalKrullDim (closure {F.genericPoint} : Set Z) with
  | bot => rw [htd] at h1; simp at h1
  | coe a =>
    rw [htd] at h1
    have : a + 1 = 0 := by exact_mod_cast h1
    exact absurd this (by simp)

/-- On a birational model `p_S : Z → S` of a pair `(S, B_S)` with crepant boundary `Θ`, the
coefficient of `Θ` along a prime divisor `P'` of `Z` at whose generic point `p_S` is a local
isomorphism onto the generic point of a prime divisor `P` of `S` is the coefficient of `B_S`
along `P`. -/
private theorem coeff_eq_coeff_of_isCrepantBoundary
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {sS : S ⟶ Spec (.of k)} [LocallyOfFiniteType sS] {BS : QDivisor S}
    (hSp : MMP.Mori.IsPair sS BS)
    {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    (pS : Z ⟶ S) [IsProper pS] [LocallyOfFiniteType (pS ≫ sS)]
    (hZv : IsNormalVariety k (pS ≫ sS)) (hpS : IsBirationalMorphism pS) {Θ : QDivisor Z}
    (hcr : ∀ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor sS d →
      IsCrepantBoundary sS d K BS pS hZv hpS Θ)
    (Pt : MMP.Mori.PrimeDivisor Z) (P : MMP.Mori.PrimeDivisor S)
    [IsIso (pS.stalkMap Pt.genericPoint)] (hPtP : pS Pt.genericPoint = P.genericPoint) :
    Θ.coeff Pt = BS.coeff P := by
  haveI : IsDominant pS := hpS.isDominant
  obtain ⟨hSv, dS, K0, hK0, hK0q⟩ := id hSp
  have hdS : topologicalKrullDim S = dS := hK0.topologicalKrullDim_eq
  have hbS := hpS.functionFieldMap_bijective
  have hdtr := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdS
  obtain ⟨ω0, hω0⟩ : ∃ ω0 : RationalTopForms sS dS, ω0 ≠ 0 := by
    letI := functionFieldAlgebra sS
    letI := functionFieldAlgebra (pS ≫ sS)
    letI := functionFieldMapAlgebra pS
    haveI := isScalarTower_functionFieldMap sS pS
    obtain ⟨ω, hω⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective sS pS hbS hdtr
    exact ⟨ω, hω.ne_zero⟩
  have hKω0 := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hSv hdS hω0
  have hpbω0 := (MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add sS hSp hdS
    ω0 hω0 pS hZv hpS Θ).mp (hcr dS _ hKω0) (map_componentGenericPoint_notMem_supp pS _)
  have hLq : (Divisor.toQDivisor (topFormDivisor sS ω0) + BS).IsQCartier :=
    hK0q.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sS hSv hK0 hKω0)
  have hc1 := coeff_qDivisor_isPullback_of_isIso Pt P hPtP hLq hpbω0
  have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso pS hbS hdtr Pt P hPtP
    (ω0.toPluriForms sS)
  simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, topFormDivisor,
    coeff_divisorOfForm] at hc1
  rw [hord] at hc1
  linarith

/-- **Adjunction of crepant boundaries along a strict transform.** Let `(S, B_S)` be a pair of
dimension `e + 1 ≥ 2` with crepant boundary `Θ` on a smooth birational model `p_S : Z → S`, and
let `j : V → S` be an adjunction step along the prime divisor `P`. If `j_Y : Y → Z` is a smooth
prime divisor `P'` of `Z` at whose generic point `p_S` is a local isomorphism onto the generic
point of `P`, and `p_V : Y → V` is birational with `p_V ≫ j = j_Y ≫ p_S`, then `(V, B_V)` is a
pair, `Θ` has coefficient `1` along `P'`, and `(Θ - P')|_Y` is a crepant boundary of `(V, B_V)`
on `Y`. -/
private theorem isCrepantBoundary_sub_single_of_isAdjunctionStep
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {sS : S ⟶ Spec (.of k)} [LocallyOfFiniteType sS] {BS : QDivisor S}
    (hSp : MMP.Mori.IsPair sS BS)
    {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    (pS : Z ⟶ S) [IsProper pS] [LocallyOfFiniteType (pS ≫ sS)]
    (hZv : IsNormalVariety k (pS ≫ sS)) (hpS : IsBirationalMorphism pS)
    (hZsm : IsSmoothScheme (pS ≫ sS)) {Θ : QDivisor Z}
    (hcr : ∀ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor sS d →
      IsCrepantBoundary sS d K BS pS hZv hpS Θ)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (j : V ⟶ S) [LocallyOfFiniteType (j ≫ sS)] {BV : QDivisor V}
    (hj : IsAdjunctionStep sS BS j BV) (P : MMP.Mori.PrimeDivisor S)
    (hPr : Set.range j = (P.support : Set S)) {e : ℕ} (hdS : topologicalKrullDim S = e + 1)
    (hdV : topologicalKrullDim V = e) (he0 : 0 < e)
    (Pt : MMP.Mori.PrimeDivisor Z) [IsIso (pS.stalkMap Pt.genericPoint)]
    (hPtP : pS Pt.genericPoint = P.genericPoint)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (jW : Y ⟶ Z) [IsClosedImmersion jW] (hjWP : jW (genericPoint Y) = Pt.genericPoint)
    (hPtr : Set.range jW = (Pt.support : Set Z)) (hYsm : IsSmoothScheme (jW ≫ pS ≫ sS))
    (pV : Y ⟶ V) [IsProper pV] (hsqV : pV ≫ j = jW ≫ pS)
    [LocallyOfFiniteType (pV ≫ j ≫ sS)]
    (hYv : IsNormalVariety k (pV ≫ j ≫ sS)) (hpV : IsBirationalMorphism pV) :
    MMP.Mori.IsPair (j ≫ sS) BV ∧ Θ.coeff Pt = 1 ∧
      ∃ (hg : ∀ Z' : irreducibleComponents Y,
          jW (componentGenericPoint _ Z') ∉ (Θ - Finsupp.single Pt 1).supp)
        (R : QDivisor Y), (Θ - Finsupp.single Pt 1).IsPullback jW hg R ∧
        ∀ (d : ℕ) (K : Divisor V), K.IsCanonicalDivisor (j ≫ sS) d →
          IsCrepantBoundary (j ≫ sS) d K BV pV hYv hpV R := by
  haveI : IsDominant pS := hpS.isDominant
  haveI : IsDominant pV := hpV.isDominant
  have hVv := hj.1
  obtain ⟨-, -, -, -, hjci, -⟩ := id hj
  haveI := hjci
  obtain ⟨hSv, dS, K0, hK0, hK0q⟩ := id hSp
  have hbS := hpS.functionFieldMap_bijective
  obtain ⟨Q0⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdV (by omega)
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sS hSv hdS j hVv P hPr Q0
  obtain ⟨ωσ, hωσ⟩ := exists_toPluriForms_eq σ
  have hωσ0 : ωσ ≠ 0 := ne_zero_of_toPluriForms_eq hωσ hσ0
  have hKσ := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hSv hdS hωσ0
  have hDσq : (Divisor.toQDivisor (divisorOfForm σ) + BS).IsQCartier := by
    have := hK0q.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sS hSv hK0 hKσ)
    rwa [topFormDivisor, hωσ] at this
  obtain ⟨hgenV, hL1⟩ :=
    hj.isPullback_divisorOfForm_add_of_isPoincareResidue hdS P hPr σ hσ0 hσP ρσ hρσ hDσq
  have hcrσ : ∀ hB, (Divisor.toQDivisor (divisorOfForm σ) + BS).IsPullback pS hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sS pS σ)) + Θ) := by
    rw [← hωσ]
    exact (MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add sS hSp hdS
      ωσ hωσ0 pS hZv hpS Θ).mp (hcr (e + 1) _ hKσ)
  set σW := pullbackRationalPluriForms sS pS σ with hσWdef
  have hdtr' := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hdS
  have hσWP : Pt.ordForm σW = -1 := by
    rw [hσWdef, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso pS hbS hdtr' Pt P
      hPtP σ]
    exact hσP
  have hσW0 : σW ≠ 0 := fun h => by
    rw [h, MMP.Mori.PrimeDivisor.ordForm_zero] at hσWP
    exact absurd hσWP (by decide)
  have hdZ : topologicalKrullDim Z = e + 1 := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (pS ≫ sS),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective sS pS hbS, hdtr']
    norm_cast
  haveI : LocallyOfFinitePresentation (pS ≫ sS) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := pS ≫ sS)).mpr inferInstance
  haveI : Smooth (pS ≫ sS) := (isSmoothScheme_iff _).mp hZsm
  haveI : LocallyOfFinitePresentation (jW ≫ pS ≫ sS) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := jW ≫ pS ≫ sS)).mpr inferInstance
  haveI : Smooth (jW ≫ pS ≫ sS) := (isSmoothScheme_iff _).mp hYsm
  obtain ⟨η, hηiff, hη0, -, -⟩ := MMP.Mori.existsUnique_isPoincareResidue_of_ordForm_eq_neg_one
    (pS ≫ sS) hdZ jW Pt hjWP σW hσW0 hσWP
  have hη := (hηiff η).mpr rfl
  obtain ⟨-, -, hadj⟩ := MMP.Fourfold.isPullback_divisorOfForm_add_of_isPoincareResidue
    (pS ≫ sS) hZv.1 hdZ jW Pt hPtr σW hσW0 hσWP η hη
  set Dd : QDivisor Z := Divisor.toQDivisor (divisorOfForm σW) + Θ with hDd
  have hDdq : Dd.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hZsm Dd
  have hjV : j (genericPoint V) = P.genericPoint := by
    have h1 := isGenericPoint_map_genericPoint j
    rw [hPr, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact h1.eq isGenericPoint_closure
  have hPσ : (Divisor.toQDivisor (divisorOfForm σ) + BS).coeff P = 0 := by
    by_contra hne
    apply hgenV (MMP.Mori.pointComponent (genericPoint V))
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjV]
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  have hPgen : P.genericPoint ∉ (Divisor.toQDivisor (divisorOfForm σ) + BS).supp :=
    MMP.CyclicChartDifferent.genericPoint_notMem_supp_of_coeff_eq_zero hPσ
  have hDdPt : Dd.coeff Pt = 0 := by
    rw [coeff_qDivisor_isPullback_of_isIso Pt P hPtP hDσq
      (hcrσ (map_componentGenericPoint_notMem_supp pS _)), hPσ]
  have hDdgen : ∀ Z' : irreducibleComponents Y, jW (componentGenericPoint _ Z') ∉ Dd.supp := by
    intro Z'
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjWP]
    exact MMP.CyclicChartDifferent.genericPoint_notMem_supp_of_coeff_eq_zero hDdPt
  obtain ⟨R, ⟨hgR, hR⟩, hDdR⟩ := hadj Dd Θ hDdq hDdgen rfl
  -- functoriality of the restrictions
  have hgcomp : ∀ Z' : irreducibleComponents Y,
      (jW ≫ pS) (componentGenericPoint _ Z') ∉
        (Divisor.toQDivisor (divisorOfForm σ) + BS).supp := by
    intro Z'
    rw [Scheme.Hom.comp_apply, MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjWP, hPtP]
    exact hPgen
  have hc1 := MMP.Mori.QDivisor.IsPullback.comp
    (hcrσ (map_componentGenericPoint_notMem_supp pS _)) hDdR hgcomp
  have hL1q := hL1.isQCartier hDσq
  obtain ⟨R1, hR1, -⟩ := hL1q.existsUnique_isPullback (map_componentGenericPoint_notMem_supp pV _)
  have hgcomp' : ∀ Z' : irreducibleComponents Y,
      (pV ≫ j) (componentGenericPoint _ Z') ∉
        (Divisor.toQDivisor (divisorOfForm σ) + BS).supp := by
    intro Z'
    rw [hsqV]
    exact hgcomp Z'
  have hc2 := MMP.Mori.QDivisor.IsPullback.comp hL1 hR1 hgcomp'
  have hc2' := qDivisor_isPullback_congr (hg := hgcomp) hsqV hc2
  have hR1eq : R1 = Divisor.toQDivisor (divisorOfForm η) + R :=
    (hDσq.existsUnique_isPullback hgcomp).unique hc2' hc1
  -- the residue of the pull-back is the pull-back of the residue
  haveI : IsIso (pS.stalkMap (jW (genericPoint Y))) :=
    hjWP ▸ (inferInstance : IsIso (pS.stalkMap Pt.genericPoint))
  have hRC := MMP.Fourfold.IsPoincareResidue.pullback (sY := sS) hdS P hjV hρσ pS jW pV hsqV
  have hηeq := (hηiff _).mp hRC
  have hdivη : divisorOfForm η = divisorOfForm (pullbackRationalPluriForms (j ≫ sS) pV ρσ) := by
    rw [← hηeq]
    exact divisorOfForm_cast (by rw [← Category.assoc, hsqV, Category.assoc]) _ _
  have hfin : ∀ hB, (Divisor.toQDivisor (divisorOfForm ρσ) + BV).IsPullback pV hB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms (j ≫ sS) pV ρσ)) + R) := by
    intro hB
    rw [← hdivη, ← hR1eq]
    exact hR1
  -- the coefficient along `P'`
  have hc0 : Θ.coeff Pt = 1 := by
    have h1 : (Θ - Finsupp.single Pt 1).coeff Pt = 0 := by
      by_contra hne
      apply hgR (MMP.Mori.pointComponent (genericPoint _))
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hjWP]
      exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨Pt, hne, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self] at h1
    linarith
  -- the crepant boundary of `(V, B_V)`
  obtain ⟨ωρ, hωρ⟩ := exists_toPluriForms_eq ρσ
  have hωρ0 : ωρ ≠ 0 := ne_zero_of_toPluriForms_eq hωρ hρσ0
  have hKρ := MMP.Spreading.CanonExist.isCanonicalDivisor_topFormDivisor hVv hdV hωρ0
  have hVp : MMP.Mori.IsPair (j ≫ sS) BV := by
    refine ⟨hVv, e, topFormDivisor (j ≫ sS) ωρ, hKρ, ?_⟩
    rw [topFormDivisor, hωρ]
    exact hL1q
  refine ⟨hVp, hc0, hgR, R, hR, fun d K hK => ?_⟩
  have hde : d = e := by
    have := hK.topologicalKrullDim_eq
    rw [hdV] at this
    exact_mod_cast this.symm
  subst hde
  have hcbρ : IsCrepantBoundary (j ≫ sS) d (topFormDivisor (j ≫ sS) ωρ) BV pV hYv hpV R := by
    refine (MMP.Mori.isCrepantBoundary_iff_isPullback_topFormDivisor_add (j ≫ sS) hVp hdV
      ωρ hωρ0 pV hYv hpV R).mpr ?_
    intro hB
    have := hfin
    rw [← hωρ] at this
    exact this hB
  exact isCrepantBoundary_of_isCanonicalDivisor hcbρ hK

open Classical in
/-- **One adjunction step on the resolution.** If the adjunction pair `(S, B_S)` has crepant
boundary `(B_W - ∑_{G ∈ T} c_G G)|_{S_W}` on the closure `S_W` of a point `s` of the snc model
`W`, then for an adjunction step `V ⊂ S` the strict transform `V_W ⊂ S_W` is the closure of a
point `w`, lying on one more snc component `G₀` with `c_{G₀} ≥ 1`, and `(V, B_V)` has crepant
boundary `(B_W - ∑_{G ∈ T ∪ {G₀}} c_G G)|_{V_W}`. -/
private theorem crepantStratum_step
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) (hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {ι : S ⟶ X} {BS : QDivisor S}
    (s : W) (pS : pointClosure s ⟶ S) (T : Finset (MMP.Mori.PrimeDivisor W))
    [IsLocallyNoetherian (pointClosure s)] [IsNormal (pointClosure s)]
    (hZv : IsNormalVariety k (pS ≫ ι ≫ sX)) (hpS : IsBirationalMorphism pS)
    (hsq : pS ≫ ι = pointClosureι s ≫ p) [IsProper pS] (hZsm : IsSmoothScheme (pS ≫ ι ≫ sX))
    (hTE : T ⊆ E) (hsc : Order.coheight s = T.card)
    (hTs : ∀ G ∈ T, s ∈ G.support ∧ 1 ≤ BW.coeff G) (hSp : MMP.Mori.IsPair (ι ≫ sX) BS)
    {hgen : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).supp}
    {Θ : QDivisor (pointClosure s)}
    (hΘ : (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).IsPullback
      (pointClosureι s) hgen Θ)
    (hcr : ∀ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d →
      IsCrepantBoundary (ι ≫ sX) d K BS pS hZv hpS Θ)
    {V : Scheme.{0}} (j : V ⟶ S) {BV : QDivisor V} (hj : IsAdjunctionStep (ι ≫ sX) BS j BV) :
    haveI : IsIntegral V := hj.1.1.toIsIntegral
    haveI : IsNormal V := hj.1.2
    haveI : IsLocallyNoetherian V :=
      haveI := hj.1.1.toLocallyOfFiniteType
      LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    ∃ (s' : W) (pV : pointClosure s' ⟶ V) (T' : Finset (MMP.Mori.PrimeDivisor W))
      (_ : IsLocallyNoetherian (pointClosure s')) (_ : IsNormal (pointClosure s'))
      (hZv' : IsNormalVariety k (pV ≫ (j ≫ ι) ≫ sX)) (hpV : IsBirationalMorphism pV),
      pV ≫ j ≫ ι = pointClosureι s' ≫ p ∧ IsProper pV ∧
      IsSmoothScheme (pV ≫ (j ≫ ι) ≫ sX) ∧
      T' ⊆ E ∧ T'.card = T.card + 1 ∧ Order.coheight s' = T'.card ∧
      (∀ G ∈ T', s' ∈ G.support ∧ 1 ≤ BW.coeff G) ∧ MMP.Mori.IsPair ((j ≫ ι) ≫ sX) BV ∧
      ∃ (hgen' : ∀ Z : irreducibleComponents (pointClosure s'),
          pointClosureι s' (componentGenericPoint _ Z) ∉
            (BW - ∑ G ∈ T', BW.coeff G • (Finsupp.single G 1 : QDivisor W)).supp)
        (Θ' : QDivisor (pointClosure s')),
        (BW - ∑ G ∈ T', BW.coeff G • (Finsupp.single G 1 : QDivisor W)).IsPullback
          (pointClosureι s') hgen' Θ' ∧
        ∀ (d : ℕ) (K : Divisor V), K.IsCanonicalDivisor ((j ≫ ι) ≫ sX) d →
          IsCrepantBoundary ((j ≫ ι) ≫ sX) d K BV pV hZv' hpV Θ' := by
  -- the next stratum `V`
  obtain ⟨hVv, P, hP1, hPr, hjci, -⟩ := id hj
  haveI := hjci
  haveI : IsIntegral V := hVv.1.toIsIntegral
  haveI : IsNormal V := hVv.2
  haveI : LocallyOfFiniteType (j ≫ ι ≫ sX) := hVv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
  haveI : CompactSpace V := j.isClosedEmbedding.compactSpace
  haveI : LocallyOfFiniteType (ι ≫ sX) := hSp.1.1.toLocallyOfFiniteType
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  haveI : CompactSpace (pointClosure s) := (pointClosureι s).isClosedEmbedding.compactSpace
  haveI : IsDominant pS := hpS.isDominant
  haveI : LocallyOfFiniteType (pS ≫ ι ≫ sX) := hZv.1.toLocallyOfFiniteType
  haveI := hWv.1
  -- the strict transform of `V`
  obtain ⟨t, ht, hiso, hcoh⟩ := exists_strictTransformPoint pS hpS P
  obtain ⟨pV, hsqV, hpVp, hpVb⟩ := exists_strictTransform s pS j P hPr t ht hiso
  haveI := hpVp
  haveI : IsDominant pV := hpVb.isDominant
  haveI := isClosedImmersion_pointClosureIncl s t
  set Pt : MMP.Mori.PrimeDivisor (pointClosure s) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne t hcoh with hPtdef
  have hPtg : Pt.genericPoint = t :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne t hcoh
  have hwc0 : Order.coheight (pointClosureι s t) = T.card + 1 := by
    rw [coheight_pointClosureι (p ≫ sX) s t, hcoh, hsc]
  haveI hisoPt : IsIso (pS.stalkMap Pt.genericPoint) := hPtg ▸ hiso
  have hPtP : pS Pt.genericPoint = P.genericPoint := by rw [hPtg, ht]
  -- the coefficient of `Θ` along the strict transform
  have hΘPt : Θ.coeff Pt = BS.coeff P :=
    coeff_eq_coeff_of_isCrepantBoundary hSp pS hZv hpS hcr Pt P hPtP
  -- the new component `G₀`
  set A := BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) with hAdef
  have hAq : A.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm A
  have hAcoef : ∀ G, A.coeff G = if G ∈ T then 0 else BW.coeff G :=
    coeff_sub_sum_smul_single BW T
  have hwA : (pointClosureι s t) ∈ A.supp := by
    by_contra hwA
    have h0 := MMP.Mori.QDivisor.IsPullback.coeff_eq_zero_of_notMem hAq hΘ Pt
      (by rw [hPtg]; exact hwA)
    rw [hΘPt] at h0
    linarith
  obtain ⟨G0, hG0c, hwG0⟩ := DivisorWithCoeffs.mem_supp_iff.mp hwA
  have hG0T : G0 ∉ T := fun h => hG0c (by rw [hAcoef, if_pos h])
  have hAG0 : A.coeff G0 = BW.coeff G0 := by rw [hAcoef, if_neg hG0T]
  have hG0E : G0 ∈ E := hBWE G0 (by rw [← hAG0]; exact hG0c)
  have hws : (pointClosureι s t) ∈ closure ({s} : Set W) := by
    rw [← range_pointClosureι]; exact ⟨t, rfl⟩
  have hwT : ∀ G ∈ T, (pointClosureι s t) ∈ G.support := fun G hG =>
    closure_minimal (Set.singleton_subset_iff.mpr (hTs G hG).1) (isClosed_support G) hws
  have hinsc : (insert G0 T).card = T.card + 1 := Finset.card_insert_of_notMem hG0T
  have hwc : Order.coheight (pointClosureι s t) = (insert G0 T).card := by
    rw [hwc0, hinsc]; norm_cast
  have hins : insert G0 T ⊆ E.filter (fun G => (pointClosureι s t) ∈ G.support) := by
    intro G hG
    rw [Finset.mem_filter]
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact ⟨hG0E, hwG0⟩
    · exact ⟨hTE hG, hwT G hG⟩
  have hfilt : E.filter (fun G => (pointClosureι s t) ∈ G.support) = insert G0 T := by
    symm
    apply Finset.eq_of_subset_of_card_le hins
    have hcard := card_filter_mem_le_coheight hE (pointClosureι s t)
    rw [hwc] at hcard
    exact_mod_cast hcard
  have hwonly : ∀ G ∈ E, (pointClosureι s t) ∈ G.support → G ∈ insert G0 T := fun G hG hwG => by
    rw [← hfilt]; exact Finset.mem_filter.mpr ⟨hG, hwG⟩
  have hsG0 : s ∉ G0.support := by
    intro hsG
    have hc := card_filter_mem_le_coheight hE s
    have hsub : insert G0 T ⊆ E.filter (fun G => s ∈ G.support) := by
      intro G hG
      rw [Finset.mem_filter]
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact ⟨hG0E, hsG⟩
      · exact ⟨hTE hG, (hTs G hG).1⟩
    have h1 := Finset.card_le_card hsub
    rw [hinsc] at h1
    rw [hsc] at hc
    have h2 : ((T.card + 1 : ℕ) : ℕ∞) ≤ T.card := le_trans (by exact_mod_cast h1) hc
    norm_cast at h2
    omega
  -- the coefficient of `G₀`
  have hG0cart : Divisor.IsCartier (Finsupp.single G0 (1 : ℤ) : Divisor W) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hWsm _
  have hg0 : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor W) := by
    intro Z hZ
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint] at hZ
    exact hsG0 (DivisorWithCoeffs.supp_single_le _ _ hZ)
  obtain ⟨C, hC⟩ := hG0cart.exists_isPullback hg0
  have hCPt : C.coeff Pt = 1 := coeff_isPullback_single_eq_one hWsm hE hTE
    (fun G hG => (hTs G hG).1) hsc hG0E t hcoh hwG0 hwc hC
  have hΘG0 : Θ.coeff Pt = BW.coeff G0 := by
    rw [← hAG0]
    refine coeff_isPullback_eq_coeff_single Pt G0 hG0cart hC hCPt hAq ?_ hΘ
    intro G hG hne
    rw [hPtg] at hG
    by_cases hGT : G ∈ T
    · rw [hAcoef, if_pos hGT]
    · rw [hAcoef, if_neg hGT]
      by_contra hBG
      exact hne ((Finset.mem_insert.mp (hwonly G (hBWE G hBG) hG)).resolve_right hGT)
  have hG0ge : 1 ≤ BW.coeff G0 := by rw [← hΘG0, hΘPt]; exact hP1
  -- the strict transform is smooth
  obtain ⟨-, hZwsm, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX)
    (isSNC_sum_single_of_subset hE (Finset.insert_subset hG0E hTE))
    (fun G hG => by
      rcases Finset.mem_insert.mp hG with rfl | hG
      · exact hwG0
      · exact hwT G hG) hwc
  have hsqW : pV ≫ j ≫ ι = pointClosureι (pointClosureι s t) ≫ p := by
    rw [← Category.assoc, hsqV, Category.assoc, hsq, ← Category.assoc, pointClosureIncl_ι]
  have hsW : pV ≫ (j ≫ ι) ≫ sX = pointClosureι (pointClosureι s t) ≫ p ≫ sX := by
    rw [← Category.assoc pV, hsqW, Category.assoc]
  have hZwsm' : IsSmoothScheme (pV ≫ (j ≫ ι) ≫ sX) := by rw [hsW]; exact hZwsm
  obtain ⟨hZwln, hZwn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hZwsm'
  haveI := hZwln
  haveI := hZwn
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure (pointClosureι s t)
  haveI : CompactSpace (pointClosure (pointClosureι s t)) :=
    (pointClosureι (pointClosureι s t)).isClosedEmbedding.compactSpace
  have hZv' : IsNormalVariety k (pV ≫ (j ≫ ι) ≫ sX) := by
    refine ⟨?_, hZwn⟩
    rw [hsW]
    exact ⟨⟩
  haveI : LocallyOfFiniteType (pV ≫ (j ≫ ι) ≫ sX) := hZv'.1.toLocallyOfFiniteType
  -- the new boundary
  set A' := BW - ∑ G ∈ insert G0 T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) with hA'def
  have hA'q : A'.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm A'
  have hgen' : ∀ Z : irreducibleComponents (pointClosure (pointClosureι s t)),
      pointClosureι (pointClosureι s t) (componentGenericPoint _ Z) ∉ A'.supp := by
    intro Z hZ
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint] at hZ
    obtain ⟨G, hG, hwG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    apply hG
    rw [hA'def, coeff_sub_sum_smul_single]
    by_cases hGT : G ∈ insert G0 T
    · rw [if_pos hGT]
    · rw [if_neg hGT]
      by_contra hBG
      exact hGT (hwonly G (hBWE G hBG) hwG)
  obtain ⟨Θ', hΘ', -⟩ := hA'q.existsUnique_isPullback hgen'
  -- dimensions
  obtain ⟨e, he⟩ : ∃ e : ℕ,
      (letI := functionFieldAlgebra (j ≫ ι ≫ sX); (Algebra.trdeg k V.functionField).toNat) = e :=
    ⟨_, rfl⟩
  have hdV : topologicalKrullDim V = e := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (j ≫ ι ≫ sX), he]
  have hdS' : topologicalKrullDim S = e + 1 := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX), ← hj.trdeg_add_one, he]
    norm_cast
  have hbV := hpVb.functionFieldMap_bijective
  have hdZw : topologicalKrullDim (pointClosure (pointClosureι s t)) = e := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (pV ≫ j ≫ ι ≫ sX),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective (j ≫ ι ≫ sX) pV hbV, he]
  refine ⟨(pointClosureι s t), pV, insert G0 T, hZwln, hZwn, hZv', hpVb, hsqW, hpVp, hZwsm', ?_,
    hinsc, hwc, ?_, ?_⟩
  · exact Finset.insert_subset hG0E hTE
  · intro G hG
    rcases Finset.mem_insert.mp hG with rfl | hG
    · exact ⟨hwG0, hG0ge⟩
    · exact ⟨hwT G hG, (hTs G hG).2⟩
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · -- `V` is a point: there are no prime divisors
    subst he0
    have hVempty : IsEmpty (MMP.Mori.PrimeDivisor V) :=
      isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero (j ≫ ι ≫ sX) (by rw [hdV]; rfl)
    have hZwempty : IsEmpty (MMP.Mori.PrimeDivisor (pointClosure (pointClosureι s t))) :=
      isEmpty_primeDivisor_of_topologicalKrullDim_eq_zero (pV ≫ (j ≫ ι) ≫ sX)
        (by rw [hdZw]; rfl)
    refine ⟨?_, hgen', Θ', hΘ', fun d K hK F => (hZwempty.false F).elim⟩
    obtain ⟨KV, hKV⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ ι ≫ sX) hVv hdV
    refine ⟨hVv, 0, KV, hKV, ?_⟩
    have h0 : Divisor.toQDivisor KV + BV = 0 := by
      ext F
      exact (hVempty.false F).elim
    rw [h0]
    exact ⟨1, one_ne_zero, 0, by simp, Divisor.isCartier_zero⟩
  -- `dim V ≥ 1`: adjunction of the crepant boundary along the strict transform
  have hjWP : pointClosureIncl s t (genericPoint (pointClosure (pointClosureι s t))) =
      Pt.genericPoint := by
    rw [pointClosureIncl_genericPoint, hPtg]
  have hPtr : Set.range (pointClosureIncl s t) = (Pt.support : Set (pointClosure s)) := by
    rw [range_pointClosureIncl, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure {x}) hPtg.symm
  have hYsm : IsSmoothScheme (pointClosureIncl s t ≫ pS ≫ ι ≫ sX) := by
    have hjWs : pointClosureIncl s t ≫ pS ≫ ι ≫ sX =
        pointClosureι (pointClosureι s t) ≫ p ≫ sX := by
      rw [← Category.assoc pS, hsq, ← Category.assoc, ← Category.assoc, pointClosureIncl_ι]
      exact Category.assoc _ _ _
    rw [hjWs]
    exact hZwsm
  obtain ⟨hVp, hc1, hgR, R, hR, hcrR⟩ :=
    isCrepantBoundary_sub_single_of_isAdjunctionStep hSp pS hZv hpS hZsm hcr j hj P hPr hdS'
      hdV he0 Pt hPtP (pointClosureIncl s t) hjWP hPtr hYsm pV hsqV hZv' hpVb
  have hc0 : BW.coeff G0 = 1 := by rw [← hΘG0]; exact hc1
  have hRA' := isPullback_next_of_isPullback hWsm hE hTE (fun G hG => (hTs G hG).1) hsc hG0E
    hG0T hc0 hsG0 t hcoh hwG0 hwc hΘ hR hgen'
  have hΘ'R : Θ' = R := (hA'q.existsUnique_isPullback hgen').unique hΘ' hRA'
  subst hΘ'R
  exact ⟨hVp, hgen', Θ', hΘ', hcrR⟩

/-! ### The crepant boundaries along a flag -/

/-- A birational model of a variety of dimension `n` has dimension `n`. -/
private theorem topologicalKrullDim_eq_of_isBirationalMorphism {X W : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] (hp : IsBirationalMorphism p) {n : ℕ}
    (hdX : topologicalKrullDim X = n) : topologicalKrullDim W = n := by
  haveI : IsDominant p := hp.isDominant
  rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (p ≫ sX),
    ← MMP.Mori.trdeg_functionField_eq_of_bijective sX p hp.functionFieldMap_bijective,
    MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX]

/-- The target of a birational morphism from a variety of dimension `n` has dimension `n`. -/
private theorem topologicalKrullDim_target_eq_of_isBirationalMorphism {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)] (hf : IsBirationalMorphism f) {n : ℕ}
    (hdX : topologicalKrullDim X = n) : topologicalKrullDim Y = n := by
  haveI : IsDominant f := hf.isDominant
  rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg sY,
    MMP.Mori.trdeg_functionField_eq_of_bijective sY f hf.functionFieldMap_bijective,
    MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := f ≫ sY) hdX]

/-- **Crepant boundaries are transported along isomorphisms.** If `B_W` is the crepant boundary
of `(X, B)` on `p : W ⟶ X` and `e : Z ⟶ W` is an isomorphism, then `e^* B_W` is the crepant
boundary of `(X, B)` on `e ≫ p`. -/
private theorem isCrepantBoundary_comp_of_isIso {X W Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hXp : MMP.Mori.IsPair sX B) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (p : W ⟶ X)
    (hWv : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {BW : QDivisor W}
    (hcr : IsCrepantBoundary sX n K B p hWv hp BW) (hBWq : BW.IsQCartier)
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (e : Z ⟶ W) [IsIso e]
    (hZv : IsNormalVariety k ((e ≫ p) ≫ sX)) (hpe : IsBirationalMorphism (e ≫ p))
    {hg : ∀ Z' : irreducibleComponents Z, e (componentGenericPoint Z Z') ∉ BW.supp}
    {Θ : QDivisor Z} (hΘ : BW.IsPullback e hg Θ) :
    IsCrepantBoundary sX n K B (e ≫ p) hZv hpe Θ := by
  intro F
  haveI : LocallyOfFiniteType sX := hXp.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.1.toLocallyOfFiniteType
  haveI : IsDominant p := hp.isDominant
  have hdX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdW : topologicalKrullDim W = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sX) p hp hdX
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWv hdW
  obtain ⟨hPW, hiff⟩ :=
    MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hXp p hWv hp hK hKW (Or.inl hcr)
  have hcohG : Order.coheight (e F.genericPoint) = 1 := by
    rw [AlgebraicGeometry.coheight_eq_of_isOpenImmersion,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set G : MMP.Mori.PrimeDivisor W :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e F.genericPoint) hcohG with hGdef
  have hGg : G.genericPoint = e F.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcohG
  obtain ⟨a0, ha0⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW hKW
    (DivisorOver.ofPrimeDivisor k hWv G)
  have ha0eq := ha0.eq_neg_coeff_of_ofPrimeDivisor hWv
  have hΘF : Θ.coeff F = BW.coeff G := coeff_qDivisor_isPullback_of_isIso F G hGg.symm hBWq hΘ
  have hval : (⟨Z, e ≫ p, hZv, hpe, F⟩ : DivisorOver k sX).valuation =
      (DivisorOver.ofPrimeDivisor k hWv G).valuation.comap (functionFieldMap p) := by
    have h1 : (DivisorOver.ofPrimeDivisor k hWv G).valuation.comap (functionFieldMap p) =
        (⟨W, p, hWv, hp, G⟩ : DivisorOver k sX).valuation := by
      ext g
      change G.divisorialValuation (functionFieldMap (𝟙 W) (functionFieldMap p g)) =
        G.divisorialValuation (functionFieldMap p g)
      rw [functionFieldMap_id_apply]
    rw [h1]
    refine MMP.Positivity.DivisorOver.valuation_eq_of_iso _ _ ⊤ ⊤ trivial trivial
      (Z.topIso ≪≫ asIso e ≪≫ W.topIso.symm) ?_ ?_
    · simp [Scheme.topIso_hom]
    · apply Subtype.ext
      have h3 : ∀ y : W, (⊤ : W.Opens).ι (W.topIso.inv y) = y := fun y => by
        rw [← Scheme.Hom.comp_apply, ← Scheme.topIso_hom, Iso.inv_hom_id]
        rfl
      rw [hGg]
      exact h3 _
  refine (hiff (DivisorOver.ofPrimeDivisor k hWv G) ⟨Z, e ≫ p, hZv, hpe, F⟩ hval _).mp ?_
  rw [hΘF, ← ha0eq]
  exact ha0

/-- The closure of the generic point is the whole scheme, so its inclusion is an isomorphism. -/
private theorem isIso_pointClosureι_genericPoint (W : Scheme.{0}) [IsIntegral W] :
    IsIso (pointClosureι (genericPoint W)) := by
  rw [Scheme.isIso_subschemeι_iff_eq_bot]
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  ext x
  simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    Closeds.coe_top, Set.mem_univ, iff_true]
  exact specializes_iff_mem_closure.mp (genericPoint_specializes x)

open Classical in
/-- **The crepant boundary along a flag.** Let `p : W ⟶ X` be a proper birational morphism from a
smooth variety, `E` a finite set of prime divisors of `W` with snc sum carrying the crepant
boundary `B_W` of the pair `(X, B)`. For every flag of iterated adjunction data of `(X, B)` of
length `k` ending at `(S, B_S)`, the strict transform of `S` is the closure `S_W` of a point `s`
of `W`, smooth and proper birational over `S`, lying on `k = codim s` components `G ∈ E` with
`c_G ≥ 1`, and the crepant boundary of `(S, B_S)` on `S_W` is
`(B_W - ∑_{G ∈ T} c_G G)|_{S_W}`. -/
private theorem exists_crepantStratum
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)] [IsProper p]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (hp : IsBirationalMorphism p) (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) (hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E) {B : QDivisor X}
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isIntegral_stratum
    haveI : IsNormal S := F.isNormal_stratum
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    ∃ (s : W) (pS : pointClosure s ⟶ S) (T : Finset (MMP.Mori.PrimeDivisor W))
      (_ : IsLocallyNoetherian (pointClosure s)) (_ : IsNormal (pointClosure s))
      (hZv : IsNormalVariety k (pS ≫ ι ≫ sX)) (hpS : IsBirationalMorphism pS),
      pS ≫ ι = pointClosureι s ≫ p ∧ IsProper pS ∧ IsSmoothScheme (pS ≫ ι ≫ sX) ∧
      T ⊆ E ∧ T.card = F.length ∧ Order.coheight s = T.card ∧
      (∀ G ∈ T, s ∈ G.support ∧ 1 ≤ BW.coeff G) ∧ MMP.Mori.IsPair (ι ≫ sX) BS ∧
      ∃ (hgen : ∀ Z : irreducibleComponents (pointClosure s),
          pointClosureι s (componentGenericPoint _ Z) ∉
            (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).supp)
        (Θ : QDivisor (pointClosure s)),
        (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W)).IsPullback
          (pointClosureι s) hgen Θ ∧
        ∀ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX) d →
          IsCrepantBoundary (ι ≫ sX) d K BS pS hZv hpS Θ := by
  induction F with
  | refl h =>
    haveI := hWv.1
    set η := genericPoint W with hη
    haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure η
    haveI : IsIso (pointClosureι η) := isIso_pointClosureι_genericPoint W
    haveI : CompactSpace (pointClosure η) := (pointClosureι η).isClosedEmbedding.compactSpace
    have hcη : Order.coheight η = ((∅ : Finset (MMP.Mori.PrimeDivisor W)).card : ℕ∞) := by
      rw [Finset.card_empty, Nat.cast_zero, Order.coheight_eq_zero]
      exact fun z _ => genericPoint_specializes z
    obtain ⟨-, hZsm, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX)
      (isSNC_sum_single_of_subset hE (Finset.empty_subset E)) (fun G hG => by simp at hG) hcη
    obtain ⟨hZln, hZn⟩ :=
      MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hZsm
    haveI := hZln
    haveI := hZn
    have hZv : IsNormalVariety k ((pointClosureι η ≫ p) ≫ 𝟙 X ≫ sX) := by
      refine ⟨?_, hZn⟩
      rw [Category.id_comp, Category.assoc]
      exact ⟨⟩
    have hpS : IsBirationalMorphism (pointClosureι η ≫ p) :=
      MMP.Mori.isBirationalMorphism_comp (isBirationalMorphism_of_isIso _) hp
    set A := BW - ∑ G ∈ (∅ : Finset (MMP.Mori.PrimeDivisor W)),
      BW.coeff G • (Finsupp.single G 1 : QDivisor W) with hAdef
    have hAq : A.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm A
    have hgen : ∀ Z : irreducibleComponents (pointClosure η),
        pointClosureι η (componentGenericPoint _ Z) ∉ A.supp := by
      intro Z
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint]
      exact MMP.Fourfold.genericPoint_notMem_supp A
    obtain ⟨Θ, hΘ, -⟩ := hAq.existsUnique_isPullback hgen
    have hAeq : A = BW := by rw [hAdef, Finset.sum_empty, sub_zero]
    refine ⟨η, pointClosureι η ≫ p, ∅, hZln, hZn, hZv, hpS, Category.comp_id _, inferInstance,
      by rw [Category.id_comp, Category.assoc]; exact hZsm, Finset.empty_subset E, rfl, hcη,
      fun G hG => by simp at hG, by rw [Category.id_comp]; exact h, hgen, Θ, hΘ, ?_⟩
    intro d K hK
    have hK' : K.IsCanonicalDivisor sX d := hK
    have hBWq : BW.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm BW
    have key : ∀ (A' : QDivisor W) (hA' : A' = BW)
        (hg : ∀ Z : irreducibleComponents (pointClosure η),
          pointClosureι η (componentGenericPoint _ Z) ∉ A'.supp),
        A'.IsPullback (pointClosureι η) hg Θ →
        IsCrepantBoundary sX d K B (pointClosureι η ≫ p) hZv hpS Θ := by
      rintro A' rfl hg hΘ'
      exact isCrepantBoundary_comp_of_isIso h hK' p hWv hp (hcrW d K hK') hBWq
        (pointClosureι η) hZv hpS hΘ'
    exact key A hAeq hgen hΘ
  | @step S₀ T₀ ι₀ BS₀ F j BT hj ih =>
    haveI : IsIntegral _ := F.isIntegral_stratum
    haveI : IsNormal _ := F.isNormal_stratum
    haveI : IsLocallyNoetherian _ := F.isLocallyNoetherian_stratum
    haveI := F.isClosedImmersion
    obtain ⟨s, pS, T, hZln, hZn, hZv, hpS, hsq, hpSp, hZsm, hTE, hTc, hsc, hTs, hSp, hgen, Θ,
      hΘ, hcr⟩ := ih
    haveI := hZln
    haveI := hZn
    haveI := hpSp
    haveI : CompactSpace S₀ := ι₀.isClosedEmbedding.compactSpace
    obtain ⟨s', pV, T', hZln', hZn', hZv', hpV, hsqV, hpVp, hZsm', hTE', hTc', hsc', hTs', hVp,
      hgen', Θ', hΘ', hcr'⟩ :=
      crepantStratum_step p hWv hWsm E hE BW hBWE s pS T hZv hpS hsq hZsm hTE hsc hTs hSp hΘ hcr
        j hj
    refine ⟨s', pV, T', hZln', hZn', hZv', hpV, hsqV, hpVp, hZsm', hTE', ?_, hsc', hTs', hVp,
      hgen', Θ', hΘ', hcr'⟩
    rw [hTc', hTc]
    rfl

/-! ### The final stratum of a flag on a dlt pair lies in the snc locus -/

open Classical in
/-- **A stratum of coefficient-one components is a zero place.** Let `p : W ⟶ X` be a proper
birational morphism from a smooth variety, `B_W` the crepant boundary of the pair `(X, B)`, with
coefficients at most one and supported on an snc divisor `∑_{G ∈ E} G`. If `s ∈ W` has
codimension `c ≥ 1` and lies on `c` components `G ∈ E` of coefficient one, then some divisor over
`X` with centre `closure {p s}` has discrepancy `-1`: the component itself if `c = 1`, the
exceptional divisor of the blow-up of `closure {s}` if `c ≥ 2`. -/
private theorem exists_isDiscrepancy_neg_one_center_eq
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)] [IsProper p]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (hp : IsBirationalMorphism p) (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) (hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E) {B : QDivisor X}
    (hXp : MMP.Mori.IsPair sX B) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hcrW : IsCrepantBoundary sX n K B p hWv hp BW) (hle : ∀ G, BW.coeff G ≤ 1)
    (s : W) (T : Finset (MMP.Mori.PrimeDivisor W)) (hTE : T ⊆ E) (hT0 : T.Nonempty)
    (hsc : Order.coheight s = T.card) (hTs : ∀ G ∈ T, s ∈ G.support ∧ 1 ≤ BW.coeff G) :
    ∃ D : DivisorOver k sX, IsProper D.f ∧ IsDiscrepancy sX n K B D (-1) ∧
      (D.center : Set X) = closure {p s} := by
  haveI := hWv.1
  have hT1 : ∀ G ∈ T, BW.coeff G = 1 := fun G hG => le_antisymm (hle G) (hTs G hG).2
  have hyT : ∀ G ∈ T, s ∈ G.support := fun G hG => (hTs G hG).1
  -- the components of `E` through `s` are those of `T`
  have hfilt : ∀ G ∈ E, s ∈ G.support → G ∈ T := by
    have hsub : T ⊆ E.filter (fun G => s ∈ G.support) := fun G hG =>
      Finset.mem_filter.mpr ⟨hTE hG, hyT G hG⟩
    have hcard := card_filter_mem_le_coheight hE s
    rw [hsc] at hcard
    have heq := Finset.eq_of_subset_of_card_le hsub (by exact_mod_cast hcard)
    intro G hG hsG
    rw [heq]
    exact Finset.mem_filter.mpr ⟨hG, hsG⟩
  have hΔ : ∀ Γ : MMP.Mori.PrimeDivisor W, closure ({s} : Set W) ⊆ Γ.support →
      BW.coeff Γ = if Γ ∈ T then 1 else 0 := by
    intro Γ hΓ
    split_ifs with hΓT
    · exact hT1 Γ hΓT
    · by_contra hne
      exact hΓT (hfilt Γ (hBWE Γ hne) (hΓ (subset_closure rfl)))
  have hdW : topologicalKrullDim W = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sX) p hp hK.topologicalKrullDim_eq
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWv hdW
  obtain ⟨hPW, hiff⟩ :=
    MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hXp p hWv hp hK hKW (Or.inl hcrW)
  rcases Nat.lt_or_ge T.card 2 with hc | hc2
  · -- one component: `s` is its generic point
    obtain ⟨G, hG⟩ : ∃ G, T = {G} := Finset.card_eq_one.mp (by
      have := hT0.card_pos
      omega)
    have hGT : G ∈ T := by rw [hG]; exact Finset.mem_singleton_self G
    have hsG : s = G.genericPoint := eq_genericPoint_of_mem_support (hyT G hGT) (by
      rw [hsc, hG, Finset.card_singleton, Nat.cast_one])
    refine ⟨⟨W, p, hWv, hp, G⟩, inferInstance, ?_, ?_⟩
    · have := hcrW G
      rwa [hT1 G hGT] at this
    · rw [DivisorOver.center_eq_closure_genericPoint, hsG]
  · -- at least two components: blow up `closure {s}`
    obtain ⟨-, hZsm, hZst⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX)
      (isSNC_sum_single_of_subset hE hTE) hyT hsc
    set Z := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({s} : Set W)) with hZdef
    have hZsupp : (Z.support : Set W) = closure {s} := by
      rw [hZdef, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    have hZst' : ∀ x ∈ Z.support, IdealSheafData.stalk Z x =
        ⨆ G ∈ T, IdealSheafData.stalk G.idealSheaf x := fun x hx => by
      rw [← SetLike.mem_coe, hZsupp] at hx
      exact hZst x hx
    have hZT : ∀ G ∈ T, (Z.support : Set W) ⊆ G.support := fun G hG => by
      rw [hZsupp]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hyT G hG)) (isClosed_support G)
    have hirr : IsIrreducible (Z.support : Set W) := hZsupp ▸ isIrreducible_singleton.closure
    have hcodim : codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
        IrreducibleCloseds W) = T.card := by
      have heq : (⟨Z.support, hirr, Z.support.isClosed⟩ : IrreducibleCloseds W) =
          IrreducibleCloseds.closureSingleton s := by
        ext1; exact hZsupp
      rw [heq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton, hsc]
    have hc1' : 1 ≤ codimension (⟨Z.support, hirr, Z.support.isClosed⟩ :
        IrreducibleCloseds W) := by
      rw [hcodim]; exact_mod_cast (by omega : 1 ≤ T.card)
    have hsb : MMP.Resolution.IsSmoothBlowup (p ≫ sX) Z := ⟨hWsm, hZsm⟩
    obtain ⟨hvar, hsmB, hprojB, hbir, -, -, -⟩ :=
     MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
        (p ≫ sX) hWv.1 hdW Z hsb hirr hcodim.symm hc2
    set π := blowUpToBase Z with hπ
    haveI := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension Z hirr hc1'
    haveI : Smooth (π ≫ p ≫ sX) := hsmB
    haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp Z) :=
      MMP.Resolution.isLocallyNoetherian_of_smooth (π ≫ p ≫ sX)
    haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
    haveI : IsNormal (AlgebraicGeometry.blowUp Z) :=
      AlgebraicGeometry.isNormal_of_smooth (π ≫ p ≫ sX)
    have hNπ : IsNormalVariety k (π ≫ p ≫ sX) := ⟨hvar, inferInstance⟩
    haveI : IsProper π := by
      haveI := hprojB
      infer_instance
    set Eb := MMP.Fourfold.SNCWeight.StratumBlowup.excE (p ≫ sX) hsb hirr hc1' with hEb
    have hEgen : π Eb.genericPoint = s := by
      have h1 := MMP.Fourfold.SNCWeight.BlowupCrepancy.closure_map_genericPoint_excE (p ≫ sX)
        hsb hirr hc1'
      rw [hZsupp] at h1
      exact (inseparable_iff_closure_eq.2 h1).eq
    have hDU := MMP.Fourfold.isDiscrepancy_excE_neg_one (p ≫ sX) hKW hPW hsb hirr
      hcodim.symm (by omega) (isSNC_sum_single_of_subset hE hTE) hZT hZst'
      (fun Γ hΓ => hΔ Γ (hZsupp ▸ hΓ)) hNπ hc1' hbir
    have hNπ' : IsNormalVariety k ((π ≫ p) ≫ sX) := hNπ
    have hbir' : IsBirationalMorphism (π ≫ p) := MMP.Mori.isBirationalMorphism_comp hbir hp
    haveI : IsDominant π := hbir.isDominant
    haveI : IsDominant p := hp.isDominant
    haveI : IsDominant (π ≫ p) := hbir'.isDominant
    have hval : (⟨_, π ≫ p, hNπ', hbir', Eb⟩ : DivisorOver k sX).valuation =
        (⟨_, π, hNπ, hbir, Eb⟩ : DivisorOver k (p ≫ sX)).valuation.comap
          (functionFieldMap p) := by
      ext g
      change Eb.divisorialValuation (functionFieldMap (π ≫ p) g) =
        Eb.divisorialValuation (functionFieldMap π (functionFieldMap p g))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    refine ⟨⟨_, π ≫ p, hNπ', hbir', Eb⟩, inferInstance,
      (hiff _ ⟨_, π ≫ p, hNπ', hbir', Eb⟩ hval (-1)).mp hDU, ?_⟩
    rw [DivisorOver.center_eq_closure_genericPoint]
    change closure {p (π Eb.genericPoint)} = _
    rw [hEgen]

/-- On a log canonical pair, the crepant boundary on a proper birational model has coefficients
at most one. -/
private theorem coeff_le_one_of_isLogCanonicalPair {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) {n : ℕ} {K : Divisor X}
    (p : W ⟶ X) [IsProper p] (hWv : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p)
    {BW : QDivisor W} (hcrW : IsCrepantBoundary sX n K B p hWv hp BW)
    (G : MMP.Mori.PrimeDivisor W) :
    BW.coeff G ≤ 1 := by
  have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hcrW G)
    (show IsProper (⟨W, p, hWv, hp, G⟩ : DivisorOver k sX).f from inferInstance)
  have h2 := hlc.2.2 n _ _ h1
  have h3 : (0 : ℝ) ≤ 1 + ((-BW.coeff G : ℚ) : ℝ) := h2
  have h4 : ((BW.coeff G : ℚ) : ℝ) ≤ 1 := by push_cast at h3; linarith
  exact_mod_cast h4

/-- **The final stratum of a flag on a dlt pair meets the snc locus.** For a dlt pair `(X, B)`
with non-snc locus `Z` and a flag of positive length ending at `S`, computed on a log
resolution, the generic point of `S` lies outside `Z`. -/
private theorem map_notMem_of_isDltPair
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)] [IsProper p]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (hp : IsBirationalMorphism p) (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) (hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E) {B : QDivisor X}
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    (Zd : Closeds X) (hZd : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Zd →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a)
    (s : W) (T : Finset (MMP.Mori.PrimeDivisor W)) (hTE : T ⊆ E) (hT0 : T.Nonempty)
    (hsc : Order.coheight s = T.card) (hTs : ∀ G ∈ T, s ∈ G.support ∧ 1 ≤ BW.coeff G) :
    p s ∉ (Zd : Set X) := by
  intro hsZ
  have hXp := hlc.1
  obtain ⟨-, n, K, hK, -⟩ := id hXp
  have hle := coeff_le_one_of_isLogCanonicalPair hlc p hWv hp (hcrW n K hK)
  obtain ⟨D, hDp, hD, hDc⟩ := exists_isDiscrepancy_neg_one_center_eq p hWv hWsm hp E hE BW hBWE
    hXp hK (hcrW n K hK) hle s T hTE hT0 hsc hTs
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hD hDp
  have hsub : (D.center : Set X) ⊆ Zd := by
    rw [hDc]
    exact closure_minimal (Set.singleton_subset_iff.mpr hsZ) Zd.isClosed
  have hpos := hZd n D hsub _ hlog
  norm_num at hpos

/-- A morphism which is an isomorphism over an open `U` reflects specializations over `U`. -/
private theorem specializes_of_isIso_restrict {W X : Scheme.{0}} (p : W ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] {x y : W} (hx : p x ∈ U) (hy : p y ∈ U) (h : p x ⤳ p y) : x ⤳ y := by
  let x' : (p ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  let y' : (p ⁻¹ᵁ U).toScheme := ⟨y, hy⟩
  have h1 : (p ∣_ U) x' ⤳ (p ∣_ U) y' := by
    apply (U.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    change ((p ∣_ U) x').1 ⤳ ((p ∣_ U) y').1
    rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
    exact h
  have h2 := h1.map (inv (p ∣_ U)).base.hom.continuous
  have e : ∀ z : (p ⁻¹ᵁ U).toScheme, (inv (p ∣_ U)) ((p ∣_ U) z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  change (inv (p ∣_ U)) ((p ∣_ U) x') ⤳ (inv (p ∣_ U)) ((p ∣_ U) y') at h2
  rw [e, e] at h2
  exact h2.map (p ⁻¹ᵁ U).ι.base.hom.continuous

/-- A morphism which is an isomorphism over an open `U` is surjective over `U`. -/
private theorem exists_apply_eq_of_isIso_restrict {W X : Scheme.{0}} (p : W ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] {x : X} (hx : x ∈ U) : ∃ w : W, p w ∈ U ∧ p w = x := by
  let w' : (p ⁻¹ᵁ U).toScheme := (inv (p ∣_ U)) ⟨x, hx⟩
  have e : (p ∣_ U) w' = ⟨x, hx⟩ := by
    change ((inv (p ∣_ U)) ≫ (p ∣_ U)) _ = _
    rw [IsIso.inv_hom_id]
    rfl
  have h1 : p w'.1 = x := by
    rw [← morphismRestrict_base_coe, e]
  exact ⟨w'.1, h1 ▸ hx, h1⟩

/-- Let `p : W ⟶ X` be an isomorphism over an open `U ∋ p s`, where `s ∈ W` is a point of
codimension `|T|` on the components `T` of an snc divisor. A generalization `x₀` of `p s` lying on
the image of every component of `T` is `p s` itself. -/
private theorem eq_apply_of_specializes_of_isIso_restrict
    {X W : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)]
    [QuasiCompact (p ≫ sX)] {E : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (U : X.Opens) [IsIso (p ∣_ U)] {s : W} {T : Finset (MMP.Mori.PrimeDivisor W)}
    (hTE : T ⊆ E) (hsc : Order.coheight s = T.card) (hyT : ∀ G ∈ T, s ∈ G.support)
    (hsU : p s ∈ U) {x₀ : X} (hx₀s : x₀ ⤳ p s)
    (hx₀G : ∀ G ∈ T, x₀ ∈ closure {p G.genericPoint}) : x₀ = p s := by
  have hgenU : ∀ G ∈ T, p G.genericPoint ∈ U := fun G hG =>
    ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ (hyT G hG)).map
      p.base.hom.continuous).mem_open U.isOpen hsU
  have hx₀U : x₀ ∈ U := hx₀s.mem_open U.isOpen hsU
  obtain ⟨w₀, hw₀U, hw₀⟩ := exists_apply_eq_of_isIso_restrict p U hx₀U
  have hw₀s : w₀ ⤳ s := specializes_of_isIso_restrict p U hw₀U hsU (hw₀ ▸ hx₀s)
  have hw₀G : ∀ G ∈ T, w₀ ∈ G.support := by
    intro G hG
    have h1 : p G.genericPoint ⤳ p w₀ := by
      rw [hw₀]
      exact specializes_iff_mem_closure.mpr (hx₀G G hG)
    have h2 := specializes_of_isIso_restrict p U (hgenU G hG) hw₀U h1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp h2
  obtain ⟨hcomp, -, -⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX)
    (isSNC_sum_single_of_subset hE hTE) hyT hsc
  have hle : closure ({w₀} : Set W) ⊆ closure {s} := hcomp.2
    ⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.mpr
      (Set.mem_iInter₂.mpr hw₀G)) (isClosed_biInter fun G _ => isClosed_support G)⟩
    (closure_mono (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hw₀s)) |>.trans
      (by rw [closure_closure]))
  have hsw : s ⤳ w₀ := specializes_iff_mem_closure.mpr (hle (subset_closure rfl))
  have hws : w₀ = s := (hw₀s.antisymm hsw).eq
  rw [← hw₀, hws]

open Classical in
/-- **The final stratum of a flag on a dlt pair is a dlt stratum.** Let `p : W ⟶ X` be a proper
birational morphism from a smooth variety which is an isomorphism over an open `U ⊆ X`, with the
crepant boundary `B_W` of the dlt pair `(X, B)` supported on an snc divisor. If `s ∈ W` has
codimension `c ≥ 1`, lies on `c` components `G` of coefficient at least one, and `p s ∈ U`, then
`closure {p s}` is a component of the intersection of the images of these components, a dlt
stratum of `(X, B)`. -/
private theorem isDltStratum_closure_of_isIso_restrict
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]
    (p : W ⟶ X) [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)] [IsProper p]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWsm : IsSmoothScheme (p ≫ sX))
    (hp : IsBirationalMorphism p) (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B)
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    (U : X.Opens) [IsIso (p ∣_ U)]
    (s : W) (T : Finset (MMP.Mori.PrimeDivisor W)) (hTE : T ⊆ E) (hT0 : T.Nonempty)
    (hsc : Order.coheight s = T.card) (hTs : ∀ G ∈ T, s ∈ G.support ∧ 1 ≤ BW.coeff G)
    (hsU : p s ∈ U) :
    MMP.Fourfold.IsDltStratum sX B (closure {p s}) := by
  have hlc := hB.1
  have hXp := hlc.1
  have hU : U ≤ MMP.Mori.biregularLocus p :=
    MMP.Mori.le_biregularLocus (f := p) (V := U) (inferInstance : IsIso (p ∣_ U))
  have hyT : ∀ G ∈ T, s ∈ G.support := fun G hG => (hTs G hG).1
  have hspG : ∀ G ∈ T, G.genericPoint ⤳ s := fun G hG =>
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ (hyT G hG)
  have hgenU : ∀ G ∈ T, p G.genericPoint ∈ U := fun G hG =>
    ((hspG G hG).map p.base.hom.continuous).mem_open U.isOpen hsU
  have hcohP : ∀ G ∈ T, Order.coheight (p G.genericPoint) = 1 := fun G hG => by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p (hU (hgenU G hG)),
      MMP.Mori.PrimeDivisor.coheight_genericPoint]
  let φ : T → MMP.Mori.PrimeDivisor X := fun G =>
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hcohP G.1 G.2)
  have hφg : ∀ G : T, (φ G).genericPoint = p G.1.genericPoint := fun G =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hφsupp : ∀ G : T, ((φ G).support : Set X) = closure {p G.1.genericPoint} := fun G => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure ({x} : Set X)) (hφg G)
  set J := T.attach.image φ with hJ
  have hcoeffJ : ∀ P ∈ J, 1 ≤ B.coeff P := by
    intro P hP
    obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hP
    haveI : IsIso (p.stalkMap G.1.genericPoint) :=
      MMP.isIso_stalkMap_of_mem_biregularLocus p (hU (hgenU G.1 G.2))
    have h := coeff_eq_coeff_of_isCrepantBoundary hXp p hWv hp hcrW G.1 (φ G) (hφg G).symm
    rw [← h]
    exact (hTs G.1 G.2).2
  have hinter : ∀ x : X, x ∈ (⋂ P ∈ J, (P.support : Set X)) ↔
      ∀ G : T, x ∈ closure {p G.1.genericPoint} := by
    intro x
    simp only [Set.mem_iInter, hJ, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · intro h G
      rw [← hφsupp]
      exact h _ ⟨G, rfl⟩
    · rintro h P ⟨G, rfl⟩
      rw [hφsupp]
      exact h G
  have hclosed : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
    isClosed_biInter fun P _ => isClosed_support P
  have hsJ : p s ∈ ⋂ P ∈ J, (P.support : Set X) := (hinter _).mpr fun G =>
    specializes_iff_mem_closure.mp ((hspG G.1 G.2).map p.base.hom.continuous)
  obtain ⟨G₀, hG₀⟩ := hT0
  refine ⟨hB, J, ⟨φ ⟨G₀, hG₀⟩, Finset.mem_image.mpr ⟨⟨G₀, hG₀⟩, Finset.mem_attach _ _, rfl⟩⟩,
    hcoeffJ, ⟨p s, hsJ⟩, ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hsJ) hclosed⟩, ?_⟩
  rintro T₀ ⟨hT₀irr, hT₀J⟩ hsub
  obtain ⟨x₀, hx₀⟩ := QuasiSober.sober hT₀irr.closure isClosed_closure
  have hx₀s : x₀ ⤳ p s := specializes_iff_mem_closure.mpr (by
    rw [hx₀.def]; exact subset_closure (hsub (subset_closure rfl)))
  have hx₀J : x₀ ∈ ⋂ P ∈ J, (P.support : Set X) :=
    closure_minimal hT₀J hclosed (by rw [← hx₀.def]; exact subset_closure rfl)
  intro x hx
  rw [← eq_apply_of_specializes_of_isIso_restrict p hE U hTE hsc hyT hsU hx₀s
    fun G hG => (hinter x₀).mp hx₀J ⟨G, hG⟩, hx₀.def]
  exact subset_closure hx

/-! ### The crepant boundary on a log resolution -/

open Classical in
/-- **The crepant boundary on a log resolution.** For a log resolution `p : W ⟶ X` of a pair
`(X, B)`, with reduced snc divisor `G` supported on `p⁻¹_* B` and the exceptional divisors, the
crepant boundary `B_W` with `K_W + B_W = p^*(K_X + B)` exists for every canonical divisor `K_X`,
is independent of it, and is supported on the components of `G`. -/
private theorem exists_crepantBoundary_of_isLogResolution
    {X W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hXp : MMP.Mori.IsPair sX B)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) [IsProper p] (hWv : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p)
    (hres : MMP.Flips.IsLogResolution sX (MMP.Mori.QDivisor.toRDivisor B) p) :
    ∃ E : Finset (MMP.Mori.PrimeDivisor W),
      DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)) ∧
      ∃ BW : QDivisor W, (∀ G, BW.coeff G ≠ 0 → G ∈ E) ∧
        ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
          IsCrepantBoundary sX d K B p hWv hp BW := by
  obtain ⟨-, hvar, hsm, -, hf, G, hG01, hGiff, hGsnc⟩ := hres
  have hX := hXp.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨-, n, K₀, hK₀, -⟩ := id hXp
  have hn : topologicalKrullDim X = n := hK₀.topologicalKrullDim_eq
  -- the snc divisor `G` is the reduced sum of its components
  have hGsum : (∑ P ∈ G.support, Finsupp.single P (1 : ℤ)) = G := by
    ext P
    change (∑ P ∈ G.support, Finsupp.single P (1 : ℤ)) P = G P
    rw [coeff_sum_single]
    split_ifs with hP
    · rcases hG01 P with h | h
      · exact absurd h (Finsupp.mem_support_iff.mp hP)
      · exact h.symm
    · exact (Finsupp.notMem_support_iff.mp hP).symm
  refine ⟨G.support, by rw [hGsum]; exact MMP.Flips.IsSNCDivisor.isSNC hvar hsm hGsnc, ?_⟩
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hXp hK₀ p hWv hp
  have hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW := by
    intro d K hK
    have hd : d = n := by
      have := hK.topologicalKrullDim_eq
      rw [hn] at this
      exact_mod_cast this.symm
    subst hd
    exact isCrepantBoundary_of_isCanonicalDivisor hBW hK
  refine ⟨BW, fun P hP => ?_, hcrW⟩
  rw [Finsupp.mem_support_iff]
  have h1 : G.coeff P = 1 := by
    by_cases hexc : P.genericPoint ∈ (MMP.Mori.exceptionalSet p : Set W)
    · exact (hGiff P).mpr
        (Or.inr ((MMP.Flips.isExceptionalPrimeDivisor_iff hX hn hWv hp P).mpr hexc))
    · refine (hGiff P).mpr (Or.inl
        ((MMP.Flips.coeff_birationalInverseTransform_ne_zero_iff hX _ hWv hp P hexc).mpr ?_))
      have hb : p P.genericPoint ∈ MMP.Mori.biregularLocus p := not_not.mp hexc
      have hco : Order.coheight (p P.genericPoint) = 1 := by
        rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p hb,
          MMP.Mori.PrimeDivisor.coheight_genericPoint]
      set Q : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
      have hQ : Q.genericPoint = p P.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
      haveI : IsIso (p.stalkMap P.genericPoint) := MMP.isIso_stalkMap_of_mem_biregularLocus p hb
      have hc := coeff_eq_coeff_of_isCrepantBoundary hXp p hWv hp hcrW P Q hQ.symm
      refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, ?_, ?_⟩
      · rw [MMP.Mori.QDivisor.coeff_toRDivisor, ← hc]
        exact_mod_cast hP
      · rw [← hQ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
  rw [show G P = G.coeff P from rfl, h1]
  exact one_ne_zero

/-! ### Comparing the crepant boundaries of a flip on a common model -/

/-- **The crepant boundaries of a flip on a common model.** Let `f⁺ : X⁺ ⟶ Y` be a flip of
`f : X ⟶ Y`, and `p : W ⟶ X`, `q : W ⟶ X⁺` proper birational morphisms with `p ≫ f = q ≫ f⁺`.
The crepant boundaries `B_W` of `(X, B)` and `B⁺_W` of `(X⁺, B⁺)` on `W` satisfy
`B⁺_W ≤ B_W`, with equality along every prime divisor of `W` that is not exceptional over `Y`:
discrepancies do not decrease under a flip, and they are equal at divisors of `Y`. -/
private theorem coeff_le_coeff_of_isFlip {X X' Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hflip : IsFlip sX sY sX' K B f fp) (hXp : MMP.Mori.IsPair sX B)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (p : W ⟶ X) (q : W ⟶ X')
    [IsProper p] [IsProper q] (hWv : IsNormalVariety k (p ≫ sX))
    (hWv' : IsNormalVariety k (q ≫ sX')) (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp) {BW B'W : QDivisor W}
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    (hcrW' : ∀ (d : ℕ) (K' : Divisor X'), K'.IsCanonicalDivisor sX' d →
      IsCrepantBoundary sX' d K' (flipTransform f fp B) q hWv' hq B'W)
    (G : MMP.Mori.PrimeDivisor W) :
    B'W.coeff G ≤ BW.coeff G ∧
      (Order.coheight ((p ≫ f) G.genericPoint) ≤ 1 → B'W.coeff G = BW.coeff G) := by
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := hflip.isNormalVariety
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  have hf := hFC.isBirationalMorphism
  have hfp := hflip.isBirationalMorphism
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNormal Y := hYv.2
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  have hXv' : IsNormalVariety k (f ≫ sY) := by rw [hfs]; exact hXv
  obtain ⟨N, hK⟩ := hFC.isCanonicalDivisor
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hX'p : MMP.Mori.IsPair sX' (flipTransform f fp B) :=
    ⟨hX'v, N, _, hK', hflip.isQCartier⟩
  have hdX : topologicalKrullDim X = N := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = N := hK'.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hfs]; infer_instance
  have hdY : topologicalKrullDim Y = N :=
    topologicalKrullDim_target_eq_of_isBirationalMorphism (sY := sY) f hf hdX
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.1.toLocallyOfFiniteType
  have hdW : topologicalKrullDim W = N :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sX) p hp hdX
  obtain ⟨V, hfV, hfpV, hXV, -, hVc⟩ := hflip.exists_opens_isIso
  haveI := hfV
  haveI := hfpV
  have hVf : V ≤ MMP.Mori.biregularLocus f := MMP.Mori.le_biregularLocus (f := f) (V := V) hfV
  have hVfp : V ≤ MMP.Mori.biregularLocus fp :=
    MMP.Mori.le_biregularLocus (f := fp) (V := V) hfpV
  have hpf : IsBirationalMorphism (p ≫ f) := MMP.Mori.isBirationalMorphism_comp hp hf
  haveI : IsDominant (p ≫ f) := hpf.isDominant
  have hqfp : IsBirationalMorphism (q ≫ fp) := MMP.Mori.isBirationalMorphism_comp hq hfp
  haveI : IsDominant (q ≫ fp) := hqfp.isDominant
  have hWY : IsNormalVariety k ((p ≫ f) ≫ sY) := by rw [Category.assoc, hfs]; exact hWv
  -- equality away from the divisors exceptional over `Y`
  have heq : Order.coheight ((p ≫ f) G.genericPoint) ≤ 1 → B'W.coeff G = BW.coeff G := by
    intro hc
    have hyq : (p ≫ f) G.genericPoint = fp (q G.genericPoint) := by
      rw [hpq, Scheme.Hom.comp_apply]
    have hyV : (p ≫ f) G.genericPoint ∈ V := by
      by_contra hyV
      rcases hVc _ hyV with ⟨e, he, hey⟩ | ⟨e, he, hey⟩
      · have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hFC.two_le_codimension he
        have h3 := MMP.Flips.coheight_le_coheight_map sY sX hYv.1 hXv.1 f hfs
          (hdX.trans hdY.symm) e
        rw [hey] at h3
        exact absurd (h2.trans (h3.trans hc)) (by decide)
      · have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet
          hflip.two_le_codimension he
        have h3 := MMP.Flips.coheight_le_coheight_map sY sX' hYv.1 hX'v.1 fp hfs'
          (hdX'.trans hdY.symm) e
        rw [hey] at h3
        exact absurd (h2.trans (h3.trans hc)) (by decide)
    have hcp : Order.coheight (p G.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX (p ≫ sX) hXv.1 hWv.1 p rfl
        (hdW.trans hdX.symm) G.genericPoint
      rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
      have h2 : Order.coheight (f (p G.genericPoint)) = Order.coheight (p G.genericPoint) :=
        MMP.Positivity.coheight_map_of_mem_biregularLocus f (hVf hyV)
      rw [Scheme.Hom.comp_apply] at hc
      exact le_antisymm (h2 ▸ hc) h1
    have hcq : Order.coheight (q G.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX' (q ≫ sX') hX'v.1 hWv'.1 q rfl
        (hdW.trans hdX'.symm) G.genericPoint
      rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
      have h2 : Order.coheight (fp (q G.genericPoint)) = Order.coheight (q G.genericPoint) :=
        MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hVfp (hyq ▸ hyV))
      rw [hyq] at hc
      exact le_antisymm (h2 ▸ hc) h1
    set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcp
    set P' : MMP.Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcq
    have hPg : P.genericPoint = p G.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcp
    have hP'g : P'.genericPoint = q G.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcq
    haveI : IsIso (p.stalkMap G.genericPoint) := MMP.isIso_stalkMap_of_mem_biregularLocus p
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hp hcp.le)
    haveI : IsIso (q.stalkMap G.genericPoint) := MMP.isIso_stalkMap_of_mem_biregularLocus q
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal q hq hcq.le)
    have h1 := coeff_eq_coeff_of_isCrepantBoundary hXp p hWv hp hcrW G P hPg.symm
    have h2 := coeff_eq_coeff_of_isCrepantBoundary hX'p q hWv' hq hcrW' G P' hP'g.symm
    have h3 : (flipTransform f fp B) P' = B P := MMP.Mori.flipTransform_apply hYv hXv' hf V hXV
      (by rw [hPg, hP'g, ← hyq, Scheme.Hom.comp_apply]) B
    rw [h1, h2]
    exact h3
  refine ⟨?_, heq⟩
  by_cases hc : Order.coheight ((p ≫ f) G.genericPoint) ≤ 1
  · exact (heq hc).le
  · have hE : RationalMap.IsExceptional (X := W) (p ≫ f).toRationalMap G :=
      (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hYv
        (⟨W, p ≫ f, hWY, hpf, G⟩ : DivisorOver k sY)).mpr
        (Order.add_one_le_of_lt (not_le.mp hc))
    have hv : (⟨W, p, hWv, hp, G⟩ : DivisorOver k sX).valuation.comap (functionFieldMap f) =
        (⟨W, q, hWv', hq, G⟩ : DivisorOver k sX').valuation.comap (functionFieldMap fp) := by
      ext g
      change G.divisorialValuation (functionFieldMap p (functionFieldMap f g)) =
        G.divisorialValuation (functionFieldMap q (functionFieldMap fp g))
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hpq]
    have hle := IsFlip.isDiscrepancy_le hXp hflip ⟨W, p, hWv, hp, G⟩ ⟨W, q, hWv', hq, G⟩ hv hE
      (hcrW N K hK G) (hcrW' N _ hK' G)
    linarith

/-- **Flips strictly increase the discrepancy of a divisor centred over the flipped locus**
(Kollár–Mori 3.38(5)), the strict form of `MMP.Mori.IsFlip.isDiscrepancy_le`. -/
private theorem IsFlip.isDiscrepancy_lt_of_notMem_biregularLocus {n : ℕ} {X X' Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hflip : IsFlip sX sY sX' K Δ f fp)
    (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : haveI : IsIntegral Y := hflip.isFlippingContraction.isNormalVariety_target.1.toIsIntegral
      haveI : IsDominant f := hflip.isFlippingContraction.isBirationalMorphism.isDominant
      haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp))
    (hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E)
    (hW : fp (D'.f D'.E.genericPoint) ∉ biregularLocus fp)
    {a a' : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp Δ) D' a') :
    a < a' := by
  have hc := hflip.isFlippingContraction
  have hY := hc.isNormalVariety_target
  have : IsProper f := hc.isProper
  have : IsProper fp := hflip.isProper
  have : QuasiCompact sX := hc.isNormalVariety_source.1.toQuasiCompact
  have : QuasiCompact sX' := hflip.isNormalVariety.1.toQuasiCompact
  exact MMP.Mori.isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target hc.isNormalVariety_source
    hflip.isNormalVariety hY hc.comp_eq hflip.comp_eq hc.isBirationalMorphism
    hflip.isBirationalMorphism ha.2.1 ha'.2.1
    (MMP.Mori.transformDivisor_inverseTransformDivisor hY
      (hflip.comp_eq ▸ hflip.isNormalVariety) hflip.isBirationalMorphism
      hflip.two_le_codimension _).symm
    (MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple hc.hasRelativelyAmpleMultiple)
    (MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple hflip.hasRelativelyAmpleMultiple)
    D D' hv hE hflip.hasRelativelyAmpleMultiple hW ha ha'

/-- On a smooth variety, every point other than the generic point is the centre of a divisor
over it: the prime divisor itself in codimension one, the exceptional divisor of the blow-up of
the closure of the point otherwise. -/
private theorem exists_divisorOver_center_eq {W : Scheme.{0}} [IsIntegral W]
    {sW : W ⟶ Spec (.of k)} (hWv : IsNormalVariety k sW) (hWsm : IsSmoothScheme sW) (w : W)
    (hw : w ≠ genericPoint W) : ∃ F : DivisorOver k sW, F.f F.E.genericPoint = w := by
  haveI : LocallyOfFiniteType sW := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsNormal W := hWv.2
  have h1 : 1 ≤ Order.coheight w := by
    refine Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h0 => hw ?_)
    exact ((genericPoint_specializes w).antisymm
      (Order.coheight_eq_zero.mp h0 (genericPoint_specializes w))).eq.symm
  rcases h1.eq_or_lt with h1 | h2
  · refine ⟨DivisorOver.ofPrimeDivisor k hWv
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w h1.symm), ?_⟩
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne w h1.symm
  · set V : IrreducibleCloseds W := IrreducibleCloseds.closureSingleton w with hV
    have hgen : V.isIrreducible.genericPoint = w := by
      have h' : IsGenericPoint w (closure (V : Set W)) := by
        change closure {w} = closure (closure {w})
        rw [closure_closure]
      exact V.isIrreducible.isGenericPoint_genericPoint_closure.eq h'
    have hcod : 2 ≤ codimension V := by
      rw [MMP.Flips.codimension_eq_coheight_genericPoint, hgen]
      exact Order.add_one_le_of_lt h2
    have hreg : IsRegularLocalRing (W.presheaf.stalk w) :=
      (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sW).mp hWsm.smooth w
    obtain ⟨F, -, -, -, hF, -⟩ := MMP.Mori.TerminalCodimTwo.exists_divisorOver_smoothBlowup hWv V
      hcod w hgen.symm hreg
    exact ⟨F, hF⟩

/-! ### Monotonicity along the common stratum -/

/-- A divisor `E` with `0 ≤ E ≤ D` has support inside the support of `D`. -/
private theorem mem_supp_of_le {W : Scheme.{0}} {E D : Divisor W} (h0 : ∀ G, 0 ≤ E.coeff G)
    (hle : ∀ G, E.coeff G ≤ D.coeff G) {x : W} (hx : x ∈ E.supp) : x ∈ D.supp := by
  obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
  exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, by have := h0 G; have := hle G; omega, hxG⟩

/-- On a smooth variety, the pull-back of an effective divisor `D` along a morphism mapping the
generic point off its support has positive coefficient along a prime divisor `Q` whose generic
point maps into the support of `D`: writing `D = a + (D - a)` for a component `a` of `D` through
the image of `η_Q`, the pull-back of `a` has positive order along `Q`, and that of the effective
`D - a` is effective. -/
private theorem coeff_pos_of_divisor_isPullback {Z W : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW]
    (hWsm : IsSmoothScheme sW) (j : Z ⟶ W) (Q : MMP.Mori.PrimeDivisor Z) (D : Divisor W)
    (hD : ∀ G, 0 ≤ D.coeff G) (hQ : j Q.genericPoint ∈ D.supp)
    {hg : ∀ Z' : irreducibleComponents Z, j (componentGenericPoint Z Z') ∉ D.supp}
    {D' : Divisor Z} (hp : D.IsPullback j hg D') : 0 < D'.coeff Q := by
  classical
  obtain ⟨a, ha, hQa⟩ := DivisorWithCoeffs.mem_supp_iff.mp hQ
  set A : Divisor W := Finsupp.single a 1
  have hA0 : ∀ G, 0 ≤ A.coeff G := fun G => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> omega
  have hAD : ∀ G, A.coeff G ≤ D.coeff G := fun G => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; have := hD a; omega
    · exact hD G
  have hR0 : ∀ G, 0 ≤ (D - A).coeff G := fun G => by
    rw [DivisorWithCoeffs.coeff_sub]; have := hAD G; omega
  have hRD : ∀ G, (D - A).coeff G ≤ D.coeff G := fun G => by
    rw [DivisorWithCoeffs.coeff_sub]; have := hA0 G; omega
  have hca := MMP.Fourfold.isCartier_of_isSmoothScheme hWsm A
  have hcR := MMP.Fourfold.isCartier_of_isSmoothScheme hWsm (D - A)
  obtain ⟨Pa, hPa⟩ := hca.exists_isPullback fun Z' h => hg Z' (mem_supp_of_le hA0 hAD h)
  obtain ⟨Pf, hPf⟩ := hcR.exists_isPullback fun Z' h => hg Z' (mem_supp_of_le hR0 hRD h)
  have hPa1 : 1 ≤ Pa.coeff Q := by
    obtain ⟨m, hm, hmc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder a
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hWsm a)
      hPa Q
    rw [hmc]
    have hle : IdealSheafData.stalk (a.idealSheaf.comap j) Q.genericPoint ≤
        IsLocalRing.maximalIdeal _ := by
      rw [IdealSheafData.stalk_comap, Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ IsLocalRing.maximalIdeal _ :=
        (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support a.idealSheaf _).mpr hQa hx
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        (IsLocalRing.mem_maximalIdeal _).1 hx' (isUnit_of_map_unit _ _ hu)
    have h1 : (1 : ℕ∞) ≤ MMP.Resolution.idealOrder
        (IdealSheafData.stalk (a.idealSheaf.comap j) Q.genericPoint) :=
      le_iSup₂_of_le 1 (by rw [pow_one]; exact hle) le_rfl
    rw [hm] at h1
    exact_mod_cast h1
  have hPf0 : 0 ≤ Pf.coeff Q :=
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hcR (V := ⊤) (fun G _ => hR0 G) hPf
      Q ⟨Q.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact ⟨subset_closure rfl, trivial⟩⟩
  have heq : D' = Pa + Pf := hp.eq (MMP.Fourfold.isCartier_of_isSmoothScheme hWsm D)
    (Divisor.IsPullback.of_eq (add_sub_cancel A D)
      (Divisor.IsPullback.add hca hcR (by rw [add_sub_cancel]; exact hg) hPa hPf))
  rw [heq, DivisorWithCoeffs.coeff_add]
  omega

/-- On a smooth variety, the pull-back of an effective `ℚ`-divisor `A` along a morphism mapping
the generic point off its support has positive coefficient along a prime divisor whose generic
point maps into the support of `A`. -/
private theorem coeff_pos_of_isPullback {Z W : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW]
    (hWsm : IsSmoothScheme sW) (j : Z ⟶ W) {A : QDivisor W} (hA : ∀ G, 0 ≤ A.coeff G)
    {hg : ∀ Z' : irreducibleComponents Z, j (componentGenericPoint Z Z') ∉ A.supp}
    {R : QDivisor Z} (hR : A.IsPullback j hg R) (Q : MMP.Mori.PrimeDivisor Z)
    (hQ : j Q.genericPoint ∈ A.supp) : 0 < R.coeff Q := by
  obtain ⟨m, hm, D, hD, hDc⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm A).exists_pos
  obtain ⟨D', hD', hp⟩ := hR m hm D hD hDc
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have hDcoeff : ∀ G, (D.coeff G : ℚ) = m * A.coeff G := fun G => by
    have e := congrArg (fun B : QDivisor W => B.coeff G) hD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at e
    rw [e]; push_cast; ring
  have hD0 : ∀ G, 0 ≤ D.coeff G := fun G => by
    have : (0 : ℚ) ≤ D.coeff G := by rw [hDcoeff]; exact mul_nonneg hm0.le (hA G)
    exact_mod_cast this
  have hDQ : j Q.genericPoint ∈ D.supp := by
    obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hQ
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, fun h0 => hP ?_, hxP⟩
    have := hDcoeff P
    rw [h0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hm0.ne'
  have h1 := coeff_pos_of_divisor_isPullback hWsm j Q D hD0 hDQ hp
  have e := congrArg (fun B : QDivisor Z => B.coeff Q) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at e
  have h2 : (0 : ℚ) < D'.coeff Q := by exact_mod_cast h1
  rw [e] at h2
  push_cast at h2
  exact pos_of_mul_pos_right h2 hm0.le

/-- Discrepancies only depend on the structure morphism up to equality. -/
private theorem exists_isDiscrepancy_of_eq {Z : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] {s₁ s₂ : Z ⟶ Spec (.of k)} (h : s₁ = s₂) {n : ℕ}
    {K : Divisor Z} {Δ : QDivisor Z} {D : DivisorOver k s₁} {a : ℚ}
    (ha : IsDiscrepancy s₁ n K Δ D a) :
    ∃ D₂ : DivisorOver k s₂, D₂.valuation = D.valuation ∧ IsDiscrepancy s₂ n K Δ D₂ a := by
  subst h
  exact ⟨D, rfl, ha⟩

/-- **The flipped locus lies on the support of `B_W - B⁺_W`.** In the setting of
`coeff_le_coeff_of_isFlip`, with `W` smooth, a point `w` of `W` mapping outside the biregular
locus of `f⁺` lies on a prime divisor `G` whose coefficient in `B⁺_W` is strictly smaller than in
`B_W`. Indeed a divisor over `W` centred at `w` has strictly larger discrepancy over `X⁺` than
over `X`, while the two discrepancies differ by the order of `B_W - B⁺_W` along it. -/
private theorem exists_coeff_lt_of_isFlip {X X' Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hflip : IsFlip sX sY sX' K B f fp) (hXp : MMP.Mori.IsPair sX B)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (p : W ⟶ X) (q : W ⟶ X')
    [IsProper p] [IsProper q] (hWv : IsNormalVariety k (p ≫ sX))
    (hWv' : IsNormalVariety k (q ≫ sX')) (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp) (hWsm : IsSmoothScheme (p ≫ sX))
    {BW B'W : QDivisor W}
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    (hcrW' : ∀ (d : ℕ) (K' : Divisor X'), K'.IsCanonicalDivisor sX' d →
      IsCrepantBoundary sX' d K' (flipTransform f fp B) q hWv' hq B'W)
    (w : W) (hw : fp (q w) ∉ MMP.Mori.biregularLocus fp) :
    ∃ G : MMP.Mori.PrimeDivisor W, B'W.coeff G < BW.coeff G ∧ w ∈ G.support := by
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := hflip.isNormalVariety
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  have hf := hFC.isBirationalMorphism
  have hfp := hflip.isBirationalMorphism
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  obtain ⟨N, hK⟩ := hFC.isCanonicalDivisor
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hX'p : MMP.Mori.IsPair sX' (flipTransform f fp B) :=
    ⟨hX'v, N, _, hK', hflip.isQCartier⟩
  have hdX : topologicalKrullDim X = N := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = N := hK'.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hfs]; infer_instance
  have hdY : topologicalKrullDim Y = N :=
    topologicalKrullDim_target_eq_of_isBirationalMorphism (sY := sY) f hf hdX
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.1.toLocallyOfFiniteType
  have hdW : topologicalKrullDim W = N :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sX) p hp hdX
  have hqp : q ≫ sX' = p ≫ sX := by
    rw [← hfs', ← hfs, ← Category.assoc, ← hpq, Category.assoc]
  have hcmp := fun G => coeff_le_coeff_of_isFlip hflip hXp p q hWv hWv' hp hq hpq hcrW hcrW' G
  haveI : IsNormal Y := hYv.2
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  by_contra hcon
  push Not at hcon
  -- `w` is not the generic point, which maps into the biregular locus
  have hwgen : w ≠ genericPoint W := by
    rintro rfl
    apply hw
    obtain ⟨V, -, hfpV, hXV, -, -⟩ := hflip.exists_opens_isIso
    haveI := hfpV
    have hVf : V ≤ MMP.Mori.biregularLocus fp := MMP.Mori.le_biregularLocus (f := fp) (V := V)
      (inferInstance : IsIso (fp ∣_ V))
    have h0 : Order.coheight (genericPoint X) ≤ 1 := by
      rw [Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z]
      exact zero_le_one
    have h1 := hVf (hXV _ h0)
    rwa [MMP.Positivity.map_genericPoint_eq_of_isDominant f,
      ← MMP.Positivity.map_genericPoint_eq_of_isDominant fp,
      ← MMP.Positivity.map_genericPoint_eq_of_isDominant q] at h1
  obtain ⟨F, hF⟩ := exists_divisorOver_center_eq hWv hWsm w hwgen
  haveI := F.isIntegral
  haveI := F.isLocallyNoetherian
  haveI := F.isNormal
  haveI : QuasiCompact (F.f ≫ p ≫ sX) := F.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace F.Y := QuasiCompact.compactSpace_of_compactSpace (F.f ≫ p ≫ sX)
  -- `F` as a divisor over `X⁺`, through `q ≫ s_{X⁺} = p ≫ s_X`
  let F' : DivisorOver k (q ≫ sX') :=
    { F with isNormalVariety := by rw [hqp]; exact F.isNormalVariety }
  let FX := compDivisorOver p hWv hp F
  let FX' := compDivisorOver q hWv' hq F'
  have hFX := valuation_compDivisorOver p hWv hp F
  have hFX' := valuation_compDivisorOver q hWv' hq F'
  -- the centre of `F` on `Y` is outside the biregular locus of `f⁺`, hence of codimension `≥ 2`
  have hcen : (F.f ≫ q ≫ fp) F.E.genericPoint = fp (q w) := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hF]
  have h2 : 2 ≤ Order.coheight (fp (q w)) := by
    have he : q w ∈ (exceptionalSet fp : Set X') := MMP.Mori.mem_exceptionalSet.mpr hw
    exact (MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hflip.two_le_codimension he).trans
      (MMP.Flips.coheight_le_coheight_map sY sX' hYv.1 hX'v.1 fp hfs' (hdX'.trans hdY.symm) _)
  have hpf : IsBirationalMorphism ((F.f ≫ p) ≫ f) :=
    MMP.Mori.isBirationalMorphism_comp
      (MMP.Mori.isBirationalMorphism_comp F.isBirationalMorphism hp) hf
  have hFY : IsNormalVariety k (((F.f ≫ p) ≫ f) ≫ sY) := by
    simp only [Category.assoc]
    rw [hfs]
    exact F.isNormalVariety
  have hE : RationalMap.IsExceptional (X := FX.Y) (FX.f ≫ f).toRationalMap FX.E :=
    (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hYv
      (⟨F.Y, (F.f ≫ p) ≫ f, hFY, hpf, F.E⟩ : DivisorOver k sY)).mpr (by
        change 2 ≤ Order.coheight (((F.f ≫ p) ≫ f) F.E.genericPoint)
        rw [show (F.f ≫ p) ≫ f = F.f ≫ q ≫ fp by rw [Category.assoc, hpq], hcen]
        exact h2)
  have hv :
      FX.valuation.comap (functionFieldMap f) = FX'.valuation.comap (functionFieldMap fp) := by
    have hcomp : (functionFieldMap p).comp (functionFieldMap f) =
        (functionFieldMap q).comp (functionFieldMap fp) := by
      ext g
      simp only [RingHom.comp_apply]
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hpq]
    rw [hFX, hFX', ← Valuation.comap_comp, ← Valuation.comap_comp, hcomp]
    rfl
  have hW : fp (FX'.f FX'.E.genericPoint) ∉ MMP.Mori.biregularLocus fp := by
    change fp ((F.f ≫ q) F.E.genericPoint) ∉ _
    rw [Scheme.Hom.comp_apply, hF]
    exact hw
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hXp hK FX
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hX'p hK' FX'
  have hlt := IsFlip.isDiscrepancy_lt_of_notMem_biregularLocus hflip FX FX' hv hE hW ha ha'
  -- the discrepancies over `W`
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ sX) hWv hdW
  obtain ⟨KW', hKW'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (q ≫ sX') hWv'
    (hdW.trans (by rfl))
  obtain ⟨-, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hXp p hWv hp hK hKW
    (Or.inl (hcrW N K hK))
  obtain ⟨-, hiff'⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hX'p q hWv' hq hK' hKW'
    (Or.inl (hcrW' N _ hK'))
  have haW := (hiff F FX hFX a).mpr ha
  have haW' := (hiff' F' FX' hFX' a').mpr ha'
  obtain ⟨F₂, hF₂v, haW₂⟩ := exists_isDiscrepancy_of_eq hqp haW'
  have haW₃ := isDiscrepancy_of_isCanonicalDivisor haW₂ hKW
  -- the boundary `B_W = B⁺_W + (B_W - B⁺_W)`, with `w` off the support of the difference
  set Δd : QDivisor W := BW - B'W with hΔd
  have hpair' : IsPairWith (p ≫ sX) N KW B'W :=
    ⟨hWv, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm _⟩
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair'.isPair hKW F
  have hba : b = a' := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair' hF₂v.symm hb haW₃
  have hΔdq : Δd.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm Δd
  obtain ⟨-, hB, hshift⟩ := MMP.Mori.IsPairWith.isDiscrepancy_add_smul_iff hpair' hΔdq F
  obtain ⟨L, hL, -⟩ := hΔdq.existsUnique_isPullback hB
  have hL0 : L.coeff F.E = 0 := by
    refine MMP.Mori.QDivisor.IsPullback.coeff_eq_zero_of_notMem hΔdq hL F.E ?_
    rw [hF]
    intro hmem
    obtain ⟨G, hG, hwG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hlt' : B'W.coeff G < BW.coeff G := by
      rw [hΔd, DivisorWithCoeffs.coeff_sub] at hG
      exact lt_of_le_of_ne (hcmp G).1 fun h => hG (by rw [h, sub_self])
    exact hcon G hlt' hwG
  have hb' := ((hshift L hL).1 b).mpr hb
  rw [hL0, sub_zero, show B'W + Δd = BW by rw [hΔd]; abel] at hb'
  have hab : a = b := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hWv, hKW, MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm _⟩
    rfl
    haW hb'
  linarith

/-- **Strict monotonicity on a common crepant model.** Let `(S, B_S)` and `(S', B_{S'})` be pairs
with crepant boundaries `Θ` and `Θ'` on a common smooth birational model `Z` (with the same
structure morphism), with `Θ = Θ' + R`. If `D` over `S` and `D'` over `S'` both induce the
valuation `ord_Q` of a prime divisor `Q` of `Z`, then
`a(D', S', B_{S'}) - a(D, S, B_S) = coeff_Q R`; in particular `a(D, S, B_S) < a(D', S', B_{S'})`
when `R` has positive coefficient along `Q`. -/
private theorem isDiscrepancy_lt_of_crepant {Z S S' : Scheme.{0}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S'] [CompactSpace S']
    {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)} {BS : QDivisor S} {BS' : QDivisor S'}
    (hSp : MMP.Mori.IsPair sS BS) (hSp' : MMP.Mori.IsPair sS' BS')
    (pS : Z ⟶ S) (pS' : Z ⟶ S') [IsProper pS] [IsProper pS'] [IsDominant pS] [IsDominant pS']
    (hZv : IsNormalVariety k (pS ≫ sS)) (hZv' : IsNormalVariety k (pS' ≫ sS'))
    (hpS : IsBirationalMorphism pS) (hpS' : IsBirationalMorphism pS')
    (hZsm : IsSmoothScheme (pS ≫ sS)) (hstr : pS' ≫ sS' = pS ≫ sS) {Θ Θ' : QDivisor Z}
    (hcr : ∀ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor sS d →
      IsCrepantBoundary sS d K BS pS hZv hpS Θ)
    (hcr' : ∀ (d : ℕ) (K : Divisor S'), K.IsCanonicalDivisor sS' d →
      IsCrepantBoundary sS' d K BS' pS' hZv' hpS' Θ')
    {R : QDivisor Z} (hΘ : Θ = Θ' + R) (Q : MMP.Mori.PrimeDivisor Z) (hRQ : 0 < R.coeff Q)
    (D : DivisorOver k sS) (D' : DivisorOver k sS')
    (hD : D.valuation = (DivisorOver.ofPrimeDivisor k hZv Q).valuation.comap (functionFieldMap pS))
    (hD' : D'.valuation =
      (DivisorOver.ofPrimeDivisor k hZv' Q).valuation.comap (functionFieldMap pS'))
    {n n' : ℕ} {KS : Divisor S} {KS' : Divisor S'} {a a' : ℚ}
    (ha : IsDiscrepancy sS n KS BS D a) (ha' : IsDiscrepancy sS' n' KS' BS' D' a') :
    a < a' := by
  haveI : LocallyOfFiniteType sS := hSp.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sS' := hSp'.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (pS ≫ sS) := hZv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (pS' ≫ sS') := hZv'.1.toLocallyOfFiniteType
  have hKS : KS.IsCanonicalDivisor sS n := ha.2.1
  have hKS' : KS'.IsCanonicalDivisor sS' n' := ha'.2.1
  have hdZ : topologicalKrullDim Z = n :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sS) pS hpS hKS.topologicalKrullDim_eq
  have hdZ' : topologicalKrullDim Z = n' :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sS') pS' hpS'
      hKS'.topologicalKrullDim_eq
  obtain rfl : n = n' := by
    have := hdZ.symm.trans hdZ'
    exact_mod_cast this
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (pS ≫ sS) hZv hdZ
  obtain ⟨KZ', hKZ'⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (pS' ≫ sS') hZv' hdZ'
  let DZ := DivisorOver.ofPrimeDivisor k hZv Q
  let DZ' := DivisorOver.ofPrimeDivisor k hZv' Q
  have hvv : DZ.valuation = DZ'.valuation := by
    ext g
    change Q.divisorialValuation (functionFieldMap (𝟙 Z) g) =
      Q.divisorialValuation (functionFieldMap (𝟙 Z) g)
    rfl
  -- discrepancies on `Z`
  obtain ⟨-, hiff⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hSp pS hZv hpS hKS hKZ
    (Or.inl (hcr n KS hKS))
  obtain ⟨-, hiff'⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hSp' pS' hZv' hpS' hKS'
    hKZ' (Or.inl (hcr' n KS' hKS'))
  have haZ := (hiff DZ D hD a).mpr ha
  have haZ' := (hiff' DZ' D' hD' a').mpr ha'
  obtain ⟨DZ'', hDZ''v, haZ''⟩ := exists_isDiscrepancy_of_eq hstr haZ'
  have haZ''' := isDiscrepancy_of_isCanonicalDivisor haZ'' hKZ
  -- the discrepancy of `Q` for `(Z, Θ')` is `a'`
  have hRq : R.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hZsm R
  have hpair' : IsPairWith (pS ≫ sS) n KZ Θ' :=
    ⟨hZv, hKZ, MMP.Fourfold.isQCartier_of_isSmoothScheme hZsm _⟩
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair'.isPair hKZ DZ
  have hba : b = a' := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair'
    (hvv.trans hDZ''v.symm) hb haZ'''
  -- adding `R` lowers it by `coeff_Q R`
  haveI : IsLocallyNoetherian DZ.Y := DZ.isLocallyNoetherian
  haveI : IsNormal DZ.Y := DZ.isNormal
  haveI : IsIntegral DZ.Y := DZ.isIntegral
  haveI : CompactSpace DZ.Y := ‹CompactSpace Z›
  obtain ⟨-, hB, hshift⟩ := MMP.Mori.IsPairWith.isDiscrepancy_add_smul_iff hpair' hRq DZ
  obtain ⟨L, hL, -⟩ := hRq.existsUnique_isPullback hB
  have hiso : IsIso (DZ.f.stalkMap Q.genericPoint) := by
    change IsIso ((𝟙 Z : Z ⟶ Z).stalkMap Q.genericPoint)
    rw [Scheme.Hom.stalkMap_id]
    exact IsIso.id _
  have hLQ : L.coeff Q = R.coeff Q :=
    @coeff_qDivisor_isPullback_of_isIso DZ.Y Z _ _ _ _ DZ.f Q Q rfl hiso R hRq _ L hL
  have hb' := ((hshift L hL).1 b).mpr hb
  rw [← hΘ] at hb'
  have hab : a = b - L.coeff DZ.E := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
    ⟨hZv, hKZ, MMP.Fourfold.isQCartier_of_isSmoothScheme hZsm _⟩ rfl haZ hb'
  change a = b - L.coeff Q at hab
  rw [hab, hLQ, hba]
  linarith

/-! ### Final strata of flags on a dlt pair -/

/-- **The final stratum of a flag on a dlt pair.** Let `(X, B)` be a projective dlt pair, smooth
with snc boundary off the closed set `Z` of the definition. For a flag of positive length
ending at `S`, the generic point of `S` lies outside `Z`, and `closure {η_S}` is a dlt stratum.
This is read off on a log resolution which is an isomorphism over `X ∖ Z`. -/
private theorem notMem_and_isDltStratum_of_stratumAdjunctionData
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hXproj : IsProjectiveMorphism sX)
    (hB : MMP.Intersection.IsDltPair sX B) (Zd : Closeds X)
    (hZsm : IsSmoothScheme (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX))
    (hZsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Zd.compl : X.Opens)) B))
    (hZpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Zd →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
    (hF : 0 < F.length) :
    haveI : IsIntegral S := F.isIntegral_stratum
    ι (genericPoint S) ∉ (Zd : Set X) ∧
      MMP.Fourfold.IsDltStratum sX B (closure {ι (genericPoint S)}) := by
  haveI : IsIntegral S := F.isIntegral_stratum
  haveI : IsNormal S := F.isNormal_stratum
  haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
  have hlc := hB.1
  have hXp := hlc.1
  have hX := hXp.1
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : IsNoetherian X := {}
  set U : X.Opens := Zd.compl with hUdef
  have hΔ : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor B) := fun E =>
    ⟨by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hlc.2.1 E,
      by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hB.2.1 E⟩
  have hUΔ : MMP.Mori.IsSNCSubset (U.ι ≫ sX) (B.supp.preimage U.ι.continuous) := by
    apply MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hZsm
    have h := MMP.Intersection.isSNCClosedSubset_preimage_of_isSNC sX U B hZsnc
    convert h using 2
    rw [Closeds.coe_preimage, DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  have hmap : ∀ h : U ≤ (Scheme.PartialIso.refl X).source, X.homOfLE h ≫
      (Scheme.PartialIso.refl X).iso.hom ≫ (Scheme.PartialIso.refl X).target.ι = U.ι := by
    intro h
    simp only [Scheme.PartialIso.refl_iso, Iso.refl_hom, Category.id_comp,
      Scheme.PartialIso.refl_target]
    exact Scheme.homOfLE_ι X _
  have hU : U ≤ (Scheme.PartialIso.refl X).source := le_top
  have hU' : U ≤ (Scheme.PartialIso.refl X).target := le_top
  obtain ⟨W, p, -, hres, -, -, -, -, hiso, -⟩ :=
    MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso sX sX hX hX hXproj hXproj B B
      hΔ hΔ (Scheme.PartialIso.refl X)
      (by
        simp only [Scheme.PartialIso.IsOver, Scheme.PartialIso.refl_iso, Iso.refl_hom,
          Category.id_comp]
        rfl)
      U U hU hU' rfl hZsm hUΔ hUΔ
      (by
        convert hUΔ using 1
        ext1
        simp only [Closeds.coe_sup, Closeds.coe_preimage]
        rw [hmap, Set.union_self])
  have hvar : MMP.Mori.IsVariety k (p ≫ sX) := hres.2.1
  have hsm : IsSmoothScheme (p ≫ sX) := hres.2.2.1
  haveI : IsProper p := hres.2.2.2.1
  have hp : IsBirationalMorphism p := hres.2.2.2.2.1
  haveI : IsIntegral W := hvar.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hvar.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hvar.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  obtain ⟨hWln, hWn⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hsm
  haveI := hWln
  haveI := hWn
  have hWv : IsNormalVariety k (p ≫ sX) := ⟨hvar, inferInstance⟩
  obtain ⟨E, hE, BW, hBWE, hcrW⟩ := exists_crepantBoundary_of_isLogResolution hXp p hWv hp hres
  obtain ⟨s, pS, T, hZln, hZn, hZv, hpS, hsq, -, -, hTE, hTc, hsc, hTs, -, -⟩ :=
    exists_crepantStratum p hWv hsm hp E hE BW hBWE hcrW F
  have hT0 : T.Nonempty := Finset.card_pos.mp (by rw [hTc]; exact hF)
  have hps := apply_eq_of_comp_eq s p ι pS hpS hsq
  haveI : IsIso (p ∣_ U) := hiso
  have hnot := map_notMem_of_isDltPair p hWv hsm hp E hE BW hBWE hlc hcrW Zd hZpos s T hTE hT0
    hsc hTs
  have hstr := isDltStratum_closure_of_isIso_restrict p hWv hsm hp E hE BW hB hcrW U s T hTE hT0
    hsc hTs hnot
  rw [hps] at hnot hstr
  exact ⟨hnot, hstr⟩

/-- **The final stratum of a flag on a dlt pair lies off the exceptional set** of a contraction
`f` whose exceptional set has codimension at least two and contains no dlt stratum. -/
private theorem genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hXproj : IsProjectiveMorphism sX)
    (hB : MMP.Intersection.IsDltPair sX B) (Zd : Closeds X)
    (hZsm : IsSmoothScheme (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX))
    (hZsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Zd.compl : X.Opens)) B))
    (hZpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Zd →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor B) D a →
        0 < a)
    {f : X ⟶ Y} (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (hstrata : ∀ T : Set X, MMP.Fourfold.IsDltStratum sX B T →
      ¬ T ⊆ (exceptionalSet f : Set X))
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isIntegral_stratum
    ι (genericPoint S) ∉ (exceptionalSet f : Set X) := by
  haveI : IsIntegral S := F.isIntegral_stratum
  intro hmem
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · cases F with
    | refl h =>
      have h2x := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 hmem
      have hmax : IsMax ((𝟙 X : X ⟶ X) (genericPoint X)) := fun z _ => genericPoint_specializes z
      rw [Order.coheight_eq_zero.mpr hmax] at h2x
      exact absurd h2x (by decide)
    | step => simp [StratumAdjunctionData.length] at h0
  · obtain ⟨-, hstr⟩ := notMem_and_isDltStratum_of_stratumAdjunctionData hXproj hB Zd hZsm hZsnc
      hZpos F hpos
    exact hstrata _ hstr (closure_minimal (Set.singleton_subset_iff.mpr hmem)
      (exceptionalSet f).isClosed)

/-! ### A common log resolution of a flip -/

/-- Smoothness over `k` passes to smaller opens. -/
private theorem isSmoothScheme_of_le {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {U V : X.Opens}
    (h : U ≤ V) (hV : IsSmoothScheme (V.ι ≫ sX)) : IsSmoothScheme (U.ι ≫ sX) := by
  haveI : LocallyOfFinitePresentation (V.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := V.ι ≫ sX)).mpr inferInstance
  haveI : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  rw [isSmoothScheme_iff] at hV ⊢
  haveI := hV
  rw [← Scheme.homOfLE_ι X h, Category.assoc]
  infer_instance

/-- Simple normal crossings of a boundary on an open pass to its smaller opens. -/
private theorem isSNCSubset_of_le {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {B : QDivisor X} {U V : X.Opens}
    (h : U ≤ V) (hV : IsSmoothScheme (V.ι ≫ sX))
    (hB : DivisorWithCoeffs.IsSNC (V.ι ≫ sX) (MMP.Mori.inverseTransformDivisor V.ι B)) :
    MMP.Mori.IsSNCSubset (U.ι ≫ sX) (B.supp.preimage U.ι.continuous) := by
  haveI : IsNoetherian X := {}
  haveI : ∀ E : MMP.Mori.PrimeDivisor X,
      LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ sX) := fun E =>
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := E.idealSheaf.subschemeι ≫ sX)).mpr inferInstance
  have hU := isSmoothScheme_of_le h hV
  rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen] at hB
  have hBU : (B.restrictOpen U).IsSNC (U.ι ≫ sX) :=
    MMP.Mori.DivisorWithCoeffs.IsSNC.comapDomain_of_range_subset sX U.ι V.ι
      (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact h) B hB
  apply MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hU
  have h' := MMP.Intersection.isSNCClosedSubset_preimage_of_isSNC_restrictOpen sX U B hBU
  convert h' using 2
  rw [Closeds.coe_preimage, DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
  rfl

/-- A morphism which is an isomorphism over an open `U` is injective over `U`. -/
private theorem eq_of_apply_eq_of_isIso_restrict {W X : Scheme.{0}} (p : W ⟶ X) (U : X.Opens)
    [IsIso (p ∣_ U)] {a b : W} (ha : p a ∈ U) (h : p a = p b) : a = b := by
  have hb : p b ∈ U := h ▸ ha
  have h1 : p a ⤳ p b := by rw [h]
  have h2 : p b ⤳ p a := by rw [h]
  exact ((specializes_of_isIso_restrict p U ha hb h1).antisymm
    (specializes_of_isIso_restrict p U hb ha h2)).eq

/-- **A common log resolution of a flip.** Let `f⁺ : X⁺ ⟶ Y` be a flip of `f : X ⟶ Y` between
projective dlt pairs, both isomorphisms over `V ⊆ Y`, and `V₀ ⊆ V` an open avoiding the images
of the non-snc loci. There are log resolutions `p : W ⟶ X` of `(X, B)` and `q : W ⟶ X⁺` of
`(X⁺, B⁺)` with `p ≫ f = q ≫ f⁺`, isomorphisms over `f⁻¹ V₀` and `f⁺⁻¹ V₀`. -/
private theorem exists_commonLogResolution
    {X X' Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hXproj : IsProjectiveMorphism sX) (hX'proj : IsProjectiveMorphism sX')
    (hB : MMP.Intersection.IsDltPair sX B)
    (hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B))
    (hflip : IsFlip sX sY sX' K B f fp) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V)
    (Zd : Closeds X) (hZsm : IsSmoothScheme (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX))
    (hZsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Zd.compl : X.Opens) ≫ sX)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Zd.compl : X.Opens)) B))
    (Zd' : Closeds X') (hZsm' : IsSmoothScheme (Scheme.Opens.ι (Zd'.compl : X'.Opens) ≫ sX'))
    (hZsnc' : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Zd'.compl : X'.Opens) ≫ sX')
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Zd'.compl : X'.Opens))
        (flipTransform f fp B)))
    (V₀ : Y.Opens) (hV₀ : V₀ ≤ V) (hV₀Z : ∀ z ∈ (Zd : Set X), f z ∉ V₀)
    (hV₀Z' : ∀ z ∈ (Zd' : Set X'), fp z ∉ V₀) :
    ∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ X'),
      MMP.Flips.IsLogResolution sX (MMP.Mori.QDivisor.toRDivisor B) p ∧
      MMP.Flips.IsLogResolution sX' (MMP.Mori.QDivisor.toRDivisor (flipTransform f fp B)) q ∧
      p ≫ f = q ≫ fp ∧ IsIso (p ∣_ f ⁻¹ᵁ V₀) ∧ IsIso (q ∣_ fp ⁻¹ᵁ V₀) := by
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := hflip.isNormalVariety
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  have hf := hFC.isBirationalMorphism
  haveI : IsProper f := hFC.isProper
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : IsNormal Y := hYv.2
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hYv.1.toIsSeparated
  have hXv' : IsNormalVariety k (f ≫ sY) := by rw [hfs]; exact hXv
  have hcoh0 : ∀ {T : Scheme.{0}} [IsIntegral T], Order.coheight (genericPoint T) ≤ 1 :=
    fun {T} _ => by
      rw [Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z]
      exact zero_le_one
  have hVf : V ≤ MMP.Mori.biregularLocus f := MMP.Mori.le_biregularLocus (f := f) (V := V)
    (inferInstance : IsIso (f ∣_ V))
  have hVfp : V ≤ MMP.Mori.biregularLocus fp := MMP.Mori.le_biregularLocus (f := fp) (V := V)
    (inferInstance : IsIso (fp ∣_ V))
  -- the partial isomorphism `X ⤏ X⁺` over `V`
  let φ : X.PartialIso X' :=
    { source := f ⁻¹ᵁ V
      dense_source := (f ⁻¹ᵁ V).isOpen.dense ⟨genericPoint X, hXV _ hcoh0⟩
      target := fp ⁻¹ᵁ V
      dense_target := (fp ⁻¹ᵁ V).isOpen.dense ⟨genericPoint X', hX'V _ hcoh0⟩
      iso := asIso (f ∣_ V) ≪≫ (asIso (fp ∣_ V)).symm }
  have hkey : φ.iso.hom ≫ φ.target.ι ≫ fp = φ.source.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V)) ≫ (fp ⁻¹ᵁ V).ι ≫ fp = (f ⁻¹ᵁ V).ι ≫ f
    rw [← morphismRestrict_ι fp V, Category.assoc, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  have hφ : φ.IsOver sX sX' := by
    simpa only [Category.assoc, hfs, hfs'] using congrArg (fun g => g ≫ sY) hkey
  have hUle : f ⁻¹ᵁ V₀ ≤ φ.source := fun x hx => hV₀ hx
  have hU'le : fp ⁻¹ᵁ V₀ ≤ φ.target := fun x hx => hV₀ hx
  have hkey' : ∀ a : φ.source.toScheme, fp (φ.target.ι (φ.iso.hom a)) = f (φ.source.ι a) :=
    fun a => by
      have := congrArg (fun g => g.base a) hkey
      simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using this
  have hUU' : φ.source.ι ⁻¹ᵁ (f ⁻¹ᵁ V₀) = φ.iso.hom ⁻¹ᵁ (φ.target.ι ⁻¹ᵁ (fp ⁻¹ᵁ V₀)) := by
    ext a
    change f (φ.source.ι a) ∈ V₀ ↔ fp (φ.target.ι (φ.iso.hom a)) ∈ V₀
    rw [hkey']
  have hUZ : f ⁻¹ᵁ V₀ ≤ (Zd.compl : X.Opens) := fun x hx hxZ => hV₀Z x hxZ hx
  have hU'Z : fp ⁻¹ᵁ V₀ ≤ (Zd'.compl : X'.Opens) := fun x hx hxZ => hV₀Z' x hxZ hx
  have hΔ : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor B) := fun E =>
    ⟨by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hB.1.2.1 E,
      by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hB.2.1 E⟩
  have hΔ' : MMP.Flips.IsBoundary (MMP.Mori.QDivisor.toRDivisor (flipTransform f fp B)) :=
    fun E => ⟨by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hB'.1.2.1 E,
      by rw [MMP.Mori.QDivisor.coeff_toRDivisor]; exact_mod_cast hB'.2.1 E⟩
  have hUΔ := isSNCSubset_of_le hUZ hZsm hZsnc
  have hUΔ' := isSNCSubset_of_le hU'Z hZsm' hZsnc'
  -- the supports of `B` and `B⁺` correspond over `V`
  have hsupp : ∀ u : (f ⁻¹ᵁ V₀).toScheme,
      (X.homOfLE hUle ≫ φ.iso.hom ≫ φ.target.ι) u ∈
          ((flipTransform f fp B).supp : Set X') ↔
        (f ⁻¹ᵁ V₀).ι u ∈ (B.supp : Set X) := by
    intro u
    set x := (f ⁻¹ᵁ V₀).ι u with hx
    set x' := (X.homOfLE hUle ≫ φ.iso.hom ≫ φ.target.ι) u with hx'
    have hfx : fp x' = f x := by
      have e1 : x' = φ.target.ι (φ.iso.hom (X.homOfLE hUle u)) := by rw [hx']; rfl
      have e2 : φ.source.ι (X.homOfLE hUle u) = x := by
        rw [hx, ← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rw [e1, hkey', e2]
    have hxV : f x ∈ V := hV₀ u.2
    have hx'V : fp x' ∈ V := hfx ▸ hxV
    constructor
    · intro hmem
      obtain ⟨P', hP', hx'P'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      have hsp' : P'.genericPoint ⤳ x' :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ hx'P'
      have hP'V : fp P'.genericPoint ∈ V := (hsp'.map fp.base.hom.continuous).mem_open
        V.isOpen hx'V
      obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq f fp V P' hP'V
      have hc : (flipTransform f fp B) P' = B P :=
        MMP.Mori.flipTransform_apply hYv hXv' hf V hXV hP B
      refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, ?_⟩
      · rw [DivisorWithCoeffs.coeff_apply, ← hc]
        exact hP'
      · have h1 : f P.genericPoint ⤳ f x := by
          rw [hP, ← hfx]
          exact hsp'.map fp.base.hom.continuous
        have h2 := specializes_of_isIso_restrict f V (hP ▸ hP'V) hxV h1
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp h2
    · intro hmem
      obtain ⟨P, hP, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
      have hsp : P.genericPoint ⤳ x :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ hxP
      have hPV : f P.genericPoint ∈ V := (hsp.map f.base.hom.continuous).mem_open V.isOpen hxV
      obtain ⟨P', hP'⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq fp f V P hPV
      have hc : (flipTransform f fp B) P' = B P :=
        MMP.Mori.flipTransform_apply hYv hXv' hf V hXV hP'.symm B
      refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P', ?_, ?_⟩
      · rw [DivisorWithCoeffs.coeff_apply, hc]
        exact hP
      · have h1 : fp P'.genericPoint ⤳ fp x' := by
          rw [hP', hfx]
          exact hsp.map f.base.hom.continuous
        have h2 := specializes_of_isIso_restrict fp V (hP' ▸ hPV) hx'V h1
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact specializes_iff_mem_closure.mp h2
  have hUΔΔ' : MMP.Mori.IsSNCSubset ((f ⁻¹ᵁ V₀).ι ≫ sX)
      (B.supp.preimage (f ⁻¹ᵁ V₀).ι.continuous ⊔ (flipTransform f fp B).supp.preimage
        (X.homOfLE hUle ≫ φ.iso.hom ≫ φ.target.ι).continuous) := by
    convert hUΔ using 1
    ext1
    simp only [Closeds.coe_sup, Closeds.coe_preimage]
    ext u
    simp only [Set.mem_union, Set.mem_preimage]
    rw [hsupp u, or_self]
  obtain ⟨W, p, q, hres, -, hres', -, hcompat, hiso, hiso'⟩ :=
    MMP.Flips.exists_isLogResolution_isIso_restrict_of_partialIso sX sX' hXv hX'v hXproj
      hX'proj B (flipTransform f fp B) hΔ hΔ' φ hφ (f ⁻¹ᵁ V₀) (fp ⁻¹ᵁ V₀) hUle hU'le hUU'
      (isSmoothScheme_of_le hUZ hZsm) hUΔ hUΔ' hUΔΔ'
  refine ⟨W, p, q, hres, hres', ?_, hiso, hiso'⟩
  -- `p ≫ f = q ≫ f⁺` holds on the dense open `p⁻¹(f⁻¹ V)`, hence everywhere
  have hWvar : MMP.Mori.IsVariety k (p ≫ sX) := hres.2.1
  haveI : IsIntegral W := hWvar.toIsIntegral
  have hp : IsBirationalMorphism p := hres.2.2.2.2.1
  haveI : IsDominant p := hp.isDominant
  have hpη : p (genericPoint W) ∈ φ.source := by
    change f (p (genericPoint W)) ∈ V
    rw [MMP.Positivity.map_genericPoint_eq_of_isDominant]
    exact hXV _ hcoh0
  haveI : IsDominant (p ⁻¹ᵁ φ.source).ι :=
    ⟨(p ⁻¹ᵁ φ.source).ι.isOpenEmbedding.isOpen_range.dense
      ⟨genericPoint W, ⟨⟨genericPoint W, hpη⟩, rfl⟩⟩⟩
  have h1 : (p ⁻¹ᵁ φ.source).ι ≫ q ≫ fp = (p ⁻¹ᵁ φ.source).ι ≫ p ≫ f := by
    rw [← Category.assoc, hcompat, Category.assoc, Category.assoc, hkey, ← Category.assoc,
      morphismRestrict_ι, Category.assoc]
  have h2 : (p ≫ f) ≫ sY = (q ≫ fp) ≫ sY := by
    rw [Category.assoc, Category.assoc, hfs, hfs']
    refine ext_of_isDominant (p ⁻¹ᵁ φ.source).ι ?_
    have := congrArg (fun g => g ≫ sY) h1
    simp only [Category.assoc] at this
    rw [hfs, hfs'] at this
    exact this.symm
  exact (ext_of_isDominant_of_isSeparated sY h2 (p ⁻¹ᵁ φ.source).ι h1.symm)

/-! ### Assembly over a common log resolution -/

/-- The extension of function fields of `p_S : Z ⟶ S`, after the stalk map of `h : S ⟶ Y` at the
generic point of `S`, is the stalk map of `p_S ≫ h` at the generic point of `Z`. -/
private theorem functionFieldMap_stalkMap_apply {Z S Y : Scheme.{0}} [IsIntegral Z] [IsIntegral S]
    (pS : Z ⟶ S) [IsDominant pS] (h : S ⟶ Y)
    (e : h (genericPoint S) = (pS ≫ h) (genericPoint Z))
    (r : Y.presheaf.stalk (h (genericPoint S))) :
    functionFieldMap pS ((h.stalkMap (genericPoint S)).hom r) =
      ((pS ≫ h).stalkMap (genericPoint Z)).hom ((Y.presheaf.stalkCongr (.of_eq e)).hom.hom r) := by
  have hpt : genericPoint S = pS (genericPoint Z) :=
    (MMP.Positivity.map_genericPoint_eq_of_isDominant pS).symm
  have key := Scheme.Hom.stalkMap_congr h h rfl (genericPoint S) (pS (genericPoint Z)) hpt
  have key' := congrArg (fun φ => φ.hom r) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key'
  rw [Scheme.Hom.stalkMap_comp]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  change (pS.stalkMap (genericPoint Z)).hom ((S.presheaf.stalkCongr _).hom.hom
    ((h.stalkMap (genericPoint S)).hom r)) = _
  rw [key']
  rfl

/-- Two valuations of `K` agreeing along a surjective ring map onto `K` are equal. -/
private theorem valuation_eq_of_comap_eq_of_surjective {R K : Type*} [CommRing R] [Field K]
    {v w : Valuation K (WithZero (Multiplicative ℤ))} (χ : R →+* K)
    (hχ : Function.Surjective χ) (h : v.comap χ = w.comap χ) : v = w := by
  ext g
  obtain ⟨r, rfl⟩ := hχ g
  exact congrArg (fun u => u r) h

/-- Composites of the canonical isomorphisms between stalks at equal points. -/
private theorem stalkCongr_hom_stalkCongr_hom_apply {Y : Scheme.{0}} {a b c : Y}
    (h₁ : Inseparable a b) (h₂ : Inseparable b c) (h₃ : Inseparable a c)
    (r : Y.presheaf.stalk a) :
    (Y.presheaf.stalkCongr h₂).hom.hom ((Y.presheaf.stalkCongr h₁).hom.hom r) =
      (Y.presheaf.stalkCongr h₃).hom.hom r := by
  obtain rfl := h₁.eq
  obtain rfl := h₂.eq
  simp [TopCat.Presheaf.stalkCongr_hom]

open Classical in
/-- **The comparison on a common log resolution.** Let `p : W ⟶ X`, `q : W ⟶ X⁺` be log
resolutions of the two sides of a flip with `p ≫ f = q ≫ f⁺`, carrying crepant boundaries on
snc divisors. If the strict transforms of corresponding strata `S`, `S⁺` are the closure of the
same point `s` of `W`, and the components of `W` through `s` are not exceptional over `Y`, then
the discrepancy of a prime divisor `P` of `S⁺` lying over the flipped locus strictly increases from
`(S, B_S)` to `(S⁺, B_{S⁺})`: the strict transform of `P` on the common stratum lies on the
support of `B_W - B⁺_W`, whose restriction measures the difference. -/
private theorem isDiscrepancy_lt_of_commonLogResolution {X X' Y W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hflip : IsFlip sX sY sX' K B f fp) (hXp : MMP.Mori.IsPair sX B)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (p : W ⟶ X) (q : W ⟶ X') [LocallyOfFiniteType (p ≫ sX)] [QuasiCompact (p ≫ sX)]
    [LocallyOfFiniteType (q ≫ sX')] [QuasiCompact (q ≫ sX')] [IsProper p] [IsProper q]
    (hWv : IsNormalVariety k (p ≫ sX)) (hWv' : IsNormalVariety k (q ≫ sX'))
    (hWsm : IsSmoothScheme (p ≫ sX)) (hWsm' : IsSmoothScheme (q ≫ sX'))
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (E : Finset (MMP.Mori.PrimeDivisor W))
    (hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    (BW : QDivisor W) (hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E)
    (hcrW : ∀ (d : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K B p hWv hp BW)
    (E' : Finset (MMP.Mori.PrimeDivisor W))
    (hE' : DivisorWithCoeffs.IsSNC (q ≫ sX') (∑ G ∈ E', Finsupp.single G (1 : ℤ)))
    (B'W : QDivisor W) (hB'WE : ∀ G, B'W.coeff G ≠ 0 → G ∈ E')
    (hcrW' : ∀ (d : ℕ) (K' : Divisor X'), K'.IsCanonicalDivisor sX' d →
      IsCrepantBoundary sX' d K' (flipTransform f fp B) q hWv' hq B'W)
    {S S' : Scheme.{0}} {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (F : StratumAdjunctionData sX B ι BS)
    (F' : StratumAdjunctionData sX' (flipTransform f fp B) ι' BS')
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    (hbir : f (ι (genericPoint S)) ∈ MMP.Mori.biregularLocus f)
    (hcorr : (ι ≫ f).base (genericPoint S) = (ι' ≫ fp).base (genericPoint S'))
    (hss : ∀ s s' : W, p s = ι (genericPoint S) → q s' = ι' (genericPoint S') →
      Order.coheight s = F.length → Order.coheight s' = F'.length →
      s = s' ∧ ∀ G : MMP.Mori.PrimeDivisor W, s ∈ G.support →
        Order.coheight ((p ≫ f) G.genericPoint) ≤ 1)
    (hS'v : IsNormalVariety k (ι' ≫ sX')) (P : MMP.Mori.PrimeDivisor S')
    (hPf : fp (ι' P.genericPoint) ∉ MMP.Mori.biregularLocus fp)
    (D : DivisorOver k (ι ≫ sX))
    (hv : D.valuation.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
      (DivisorOver.ofPrimeDivisor k hS'v P).valuation.comap
        ((Y.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ (ι' ≫ fp).stalkMap (genericPoint S')).hom)
    {n n' : ℕ} {KS : Divisor S} {KS' : Divisor S'} {a a' : ℚ}
    (ha : IsDiscrepancy (ι ≫ sX) n KS BS D a)
    (ha' : IsDiscrepancy (ι' ≫ sX') n' KS' BS' (DivisorOver.ofPrimeDivisor k hS'v P) a') :
    a < a' := by
  have hFC := hflip.isFlippingContraction
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  haveI : IsIntegral Y := hFC.isNormalVariety_target.1.toIsIntegral
  haveI := F.isClosedImmersion
  haveI := F'.isClosedImmersion
  haveI : CompactSpace S := ι.isClosedEmbedding.compactSpace
  haveI : CompactSpace S' := ι'.isClosedEmbedding.compactSpace
  -- the crepant strata on both sides
  obtain ⟨s, pS, T, hZln, hZn, hZv, hpS, hsq, hpSp, hZsm, hTE, hTc, hsc, hTs, hSp, hgen, Θ,
    hΘ, hcr⟩ := exists_crepantStratum p hWv hWsm hp E hE BW hBWE hcrW F
  obtain ⟨s', pS', T', hZln', hZn', hZv', hpS', hsq', hpSp', hZsm', hTE', hTc', hsc', hTs', hSp',
    hgen', Θ', hΘ', hcr'⟩ := exists_crepantStratum q hWv' hWsm' hq E' hE' B'W hB'WE hcrW' F'
  have hps := apply_eq_of_comp_eq s p ι pS hpS hsq
  have hqs := apply_eq_of_comp_eq s' q ι' pS' hpS' hsq'
  obtain ⟨rfl, hagree0⟩ := hss s s' hps hqs (by rw [hsc, hTc]) (by rw [hsc', hTc'])
  haveI := hZln
  haveI := hZn
  haveI := hpSp
  haveI := hpSp'
  haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
  haveI : CompactSpace (pointClosure s) := (pointClosureι s).isClosedEmbedding.compactSpace
  haveI : IsDominant pS := hpS.isDominant
  haveI : IsDominant pS' := hpS'.isDominant
  have hcmp := fun G => coeff_le_coeff_of_isFlip hflip hXp p q hWv hWv' hp hq hpq hcrW hcrW' G
  have hagree : ∀ G, s ∈ G.support → B'W.coeff G = BW.coeff G := fun G hG =>
    (hcmp G).2 (hagree0 G hG)
  -- the two sets of components through `s` agree
  have hT : T = T' := by
    have hfilt : ∀ G ∈ E', s ∈ G.support → G ∈ T' := by
      have hsub : T' ⊆ E'.filter (fun G => s ∈ G.support) := fun G hG =>
        Finset.mem_filter.mpr ⟨hTE' hG, (hTs' G hG).1⟩
      have hcard := card_filter_mem_le_coheight hE' s
      rw [hsc'] at hcard
      have heq := Finset.eq_of_subset_of_card_le hsub (by exact_mod_cast hcard)
      intro G hG hsG
      rw [heq]
      exact Finset.mem_filter.mpr ⟨hG, hsG⟩
    have hTT' : T ⊆ T' := fun G hG => by
      have h1 := (hTs G hG).2
      have h2 := hagree G (hTs G hG).1
      exact hfilt G (hB'WE G (by rw [h2]; linarith)) (hTs G hG).1
    refine Finset.eq_of_subset_of_card_le hTT' ?_
    have := hsc.symm.trans hsc'
    exact le_of_eq (by exact_mod_cast this.symm)
  subst hT
  -- `Θ = Θ' + R` with `R` the restriction of `B_W - B⁺_W ≥ 0`
  set Δd : QDivisor W := BW - B'W with hΔd
  have hsum : ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) =
      ∑ G ∈ T, B'W.coeff G • (Finsupp.single G 1 : QDivisor W) :=
    Finset.sum_congr rfl fun G hG => by rw [hagree G (hTs G hG).1]
  have hA : BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W) =
      (B'W - ∑ G ∈ T, B'W.coeff G • (Finsupp.single G 1 : QDivisor W)) + Δd := by
    rw [hsum, hΔd]
    abel
  have hgR : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉ Δd.supp := by
    intro Z hZ
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint] at hZ
    obtain ⟨P, hP, hsP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    apply hP
    rw [hΔd, DivisorWithCoeffs.coeff_sub, hagree P hsP, sub_self]
  have hΔdq : Δd.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm Δd
  have hA'q := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm
    (B'W - ∑ G ∈ T, B'W.coeff G • (Finsupp.single G 1 : QDivisor W))
  have hAq := MMP.Fourfold.isQCartier_of_isSmoothScheme hWsm
    (BW - ∑ G ∈ T, BW.coeff G • (Finsupp.single G 1 : QDivisor W))
  obtain ⟨R, hR, -⟩ := hΔdq.existsUnique_isPullback hgR
  have hsum2 := MMP.Mori.QDivisor.IsPullback.add hA'q hΔdq hΘ' hR (by
    intro Z; rw [← hA]; exact hgen Z)
  have hΘeq : Θ = Θ' + R :=
    (hAq.existsUnique_isPullback hgen).unique hΘ (qDivisor_isPullback_of_eq hA.symm hsum2)
  -- the structure morphisms of the common stratum agree
  have hqp : q ≫ sX' = p ≫ sX := by rw [← hfs', ← hfs, ← Category.assoc, ← hpq, Category.assoc]
  have hstr : pS' ≫ ι' ≫ sX' = pS ≫ ι ≫ sX := by
    rw [← Category.assoc, hsq', ← Category.assoc, hsq, Category.assoc, Category.assoc, hqp]
  -- the stalk map `𝒪_{Y,y} → k(S)` is onto
  set ψ := ((ι ≫ f).stalkMap (genericPoint S)).hom with hψ
  set ψ' := ((Y.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
    (ι' ≫ fp).stalkMap (genericPoint S')).hom with hψ'
  have hψsurj : Function.Surjective ψ := by
    haveI : IsIso (f.stalkMap (ι (genericPoint S))) :=
      MMP.isIso_stalkMap_of_mem_biregularLocus f hbir
    have h2 : Function.Surjective
        (f.stalkMap (ι (genericPoint S)) ≫ ι.stalkMap (genericPoint S)).hom := by
      rw [CommRingCat.hom_comp]
      exact (ι.stalkMap_surjective (genericPoint S)).comp
        (ConcreteCategory.bijective_of_isIso (f.stalkMap (ι (genericPoint S)))).2
    rw [hψ, Scheme.Hom.stalkMap_comp]
    exact h2
  have hg : pS ≫ ι ≫ f = pS' ≫ ι' ≫ fp := by
    rw [← Category.assoc, hsq, Category.assoc, hpq, ← Category.assoc, ← hsq', Category.assoc]
  have hχ : (functionFieldMap pS).comp ψ = (functionFieldMap pS').comp ψ' := by
    ext r
    have e1 : (ι ≫ f) (genericPoint S) = (pS ≫ ι ≫ f) (genericPoint (pointClosure s)) := by
      rw [Scheme.Hom.comp_apply pS, MMP.Positivity.map_genericPoint_eq_of_isDominant pS]
    have e2 : (ι' ≫ fp) (genericPoint S') =
        (pS' ≫ ι' ≫ fp) (genericPoint (pointClosure s)) := by
      rw [Scheme.Hom.comp_apply pS', MMP.Positivity.map_genericPoint_eq_of_isDominant pS']
    have hI : Inseparable ((ι ≫ f) (genericPoint S))
        ((pS' ≫ ι' ≫ fp) (genericPoint (pointClosure s))) :=
      Inseparable.of_eq (e1.trans (congrArg (fun g => g.base (genericPoint _)) hg))
    rw [RingHom.comp_apply, RingHom.comp_apply, hψ, hψ', CommRingCat.hom_comp,
      RingHom.comp_apply, functionFieldMap_stalkMap_apply pS (ι ≫ f) e1,
      functionFieldMap_stalkMap_apply pS' (ι' ≫ fp) e2,
      Scheme.Hom.stalkMap_congr_hom _ _ hg, CommRingCat.hom_comp, RingHom.comp_apply,
      stalkCongr_hom_stalkCongr_hom_apply _ _ hI, stalkCongr_hom_stalkCongr_hom_apply _ _ hI]
  -- the strict transform `Q` of `P` on the common stratum
  have hPb : P.genericPoint ∈ MMP.Mori.biregularLocus pS' :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal pS' hpS'
      (MMP.Mori.PrimeDivisor.coheight_genericPoint P).le
  haveI : IsIso (pS' ∣_ MMP.Mori.biregularLocus pS') := MMP.Mori.isBiregular_biregularLocus pS'
  obtain ⟨z, -, hz⟩ := exists_apply_eq_of_isIso_restrict pS' _ hPb
  have hzc : Order.coheight z = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus pS' (hz ▸ hPb), hz,
      MMP.Mori.PrimeDivisor.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor (pointClosure s) :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hzc with hQdef
  have hQg : Q.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hzc
  -- both divisors induce `ord_Q` on the common stratum
  have hD' : (DivisorOver.ofPrimeDivisor k hS'v P).valuation =
      (DivisorOver.ofPrimeDivisor k hZv' Q).valuation.comap (functionFieldMap pS') := by
    rw [← valuation_compDivisorOver pS' hZv' hpS' (DivisorOver.ofPrimeDivisor k hZv' Q)]
    refine (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hS'v _ P ?_).symm
    change (𝟙 _ ≫ pS') Q.genericPoint = P.genericPoint
    rw [Category.id_comp, hQg, hz]
  have hvv : (DivisorOver.ofPrimeDivisor k hZv Q).valuation =
      (DivisorOver.ofPrimeDivisor k hZv' Q).valuation := by
    ext g
    change Q.divisorialValuation (functionFieldMap (𝟙 _) g) =
      Q.divisorialValuation (functionFieldMap (𝟙 _) g)
    rfl
  have hD : D.valuation =
      (DivisorOver.ofPrimeDivisor k hZv Q).valuation.comap (functionFieldMap pS) := by
    apply valuation_eq_of_comap_eq_of_surjective ψ hψsurj
    rw [hv, hD', ← Valuation.comap_comp, ← Valuation.comap_comp, ← hχ, hvv]
  -- `Q` lies over the flipped locus, so `R` has positive coefficient along it
  have hw : fp (q (pointClosureι s z)) ∉ MMP.Mori.biregularLocus fp := by
    have e : q (pointClosureι s z) = ι' P.genericPoint := by
      rw [← Scheme.Hom.comp_apply, ← hsq', Scheme.Hom.comp_apply, hz]
    rw [e]
    exact hPf
  obtain ⟨G, hGlt, hwG⟩ :=
    exists_coeff_lt_of_isFlip hflip hXp p q hWv hWv' hp hq hpq hWsm hcrW hcrW' _ hw
  have hQsupp : pointClosureι s Q.genericPoint ∈ Δd.supp := by
    rw [hQg]
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, ?_, hwG⟩
    rw [hΔd, DivisorWithCoeffs.coeff_sub]
    exact sub_ne_zero.mpr hGlt.ne'
  have hRQ : 0 < R.coeff Q := coeff_pos_of_isPullback hWsm (pointClosureι s)
    (fun G => by rw [hΔd, DivisorWithCoeffs.coeff_sub]; linarith [(hcmp G).1]) hR Q hQsupp
  exact isDiscrepancy_lt_of_crepant hSp hSp' pS pS' hZv hZv' hpS hpS' hZsm hstr hcr hcr' hΘeq Q
    hRQ D _ hD hD' ha ha'

/-- A point of a variety lying over the generic point of a variety of the same dimension is
the generic point: coheights do not decrease along morphisms of varieties of equal dimension. -/
private theorem coheight_eq_zero_of_apply_eq_genericPoint {W X Y : Scheme.{0}} [IsIntegral Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (hY : MMP.Mori.IsVariety k sY) {q : W ⟶ X} (hW : MMP.Mori.IsVariety k (q ≫ sX))
    (f : X ⟶ Y) (hfs : f ≫ sY = sX)
    (hXY : topologicalKrullDim X = topologicalKrullDim Y)
    (hWX : topologicalKrullDim W = topologicalKrullDim X) (s : W)
    (h : f (q s) = genericPoint Y) : Order.coheight s = 0 := by
  refine nonpos_iff_eq_zero.mp
    ((MMP.Flips.coheight_le_coheight_map sX (q ≫ sX) hX hW q rfl hWX s).trans
      ((MMP.Flips.coheight_le_coheight_map sY sX hY hX f hfs hXY _).trans ?_))
  rw [h, Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z]

/-- **Strict discrepancy increase along a contracted divisor of the flipped stratum**, over an
algebraically closed field `k` of characteristic zero: for corresponding adjunction pairs
`(S, B_S)`, `(S⁺, B_{S⁺})` of a flip of projective dlt pairs which is an isomorphism at the generic
point of every boundary stratum, and a prime divisor `P` of `S⁺` contracted by `S⁺ → Y`,
`a(D, S, B_S) < a(P, S⁺, B_{S⁺})` for any divisor `D` over `S` with the same valuation on
`𝒪_{Y,y}` as `P`. -/
private theorem isDiscrepancy_lt_of_isStratumAdjunctionPair {X X' Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hX' : MMP.Mori.IsProjectiveVariety k sX')
    (hB : MMP.Intersection.IsDltPair sX B)
    (hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B))
    (hflip : IsFlip sX sY sX' K B f fp)
    (hstrata : ∀ T : Set X, MMP.Fourfold.IsDltStratum sX B T →
      ¬ T ⊆ (exceptionalSet f : Set X))
    (hstrata' : ∀ T : Set X', MMP.Fourfold.IsDltStratum sX' (flipTransform f fp B) T →
      ¬ T ⊆ (exceptionalSet fp : Set X'))
    {S S' : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (hS : MMP.Fourfold.IsStratumAdjunctionPair sX B ι BS)
    (hS' : MMP.Fourfold.IsStratumAdjunctionPair sX' (flipTransform f fp B) ι' BS')
    (hcorr : (ι ≫ f).base (genericPoint S) = (ι' ≫ fp).base (genericPoint S'))
    (P : MMP.Mori.PrimeDivisor S')
    (hP : topologicalKrullDim (closure {(ι' ≫ fp).base P.genericPoint} : Set Y) <
      topologicalKrullDim (closure {P.genericPoint} : Set S'))
    (D : DivisorOver k (ι ≫ sX))
    (hv : D.valuation.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
      (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P).valuation.comap
        ((Y.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ (ι' ≫ fp).stalkMap (genericPoint S')).hom)
    {n n' : ℕ} {KS : Divisor S} {KS' : Divisor S'} {a a' : ℚ}
    (ha : IsDiscrepancy (ι ≫ sX) n KS BS D a)
    (ha' : IsDiscrepancy (ι' ≫ sX') n' KS' BS'
      (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P) a') :
    a < a' := by
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hYv := hFC.isNormalVariety_target
  have hX'v := hflip.isNormalVariety
  have hfs := hFC.comp_eq
  have hfs' := hflip.comp_eq
  have hf := hFC.isBirationalMorphism
  have hfp := hflip.isBirationalMorphism
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  have hXproj : IsProjectiveMorphism sX := ((MMP.Mori.isProjectiveVariety_iff k sX).mp hX).2
  have hX'proj : IsProjectiveMorphism sX' := ((MMP.Mori.isProjectiveVariety_iff k sX').mp hX').2
  have hXp : MMP.Mori.IsPair sX B := hB.1.1
  have hX'p : MMP.Mori.IsPair sX' (flipTransform f fp B) := hB'.1.1
  obtain ⟨-, -, Zd, hZsm, hZsnc, hZpos⟩ := id hB
  obtain ⟨-, -, Zd', hZsm', hZsnc', hZpos'⟩ := id hB'
  set F := hS.some with hF
  set F' := hS'.some with hF'
  -- dimensions
  obtain ⟨N, hK⟩ := hFC.isCanonicalDivisor
  have hdX : topologicalKrullDim X = N := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = N :=
    (hflip.isCanonicalDivisor_flipTransform hK).topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hfs]; infer_instance
  have hdY : topologicalKrullDim Y = N :=
    topologicalKrullDim_target_eq_of_isBirationalMorphism (sY := sY) f hf hdX
  -- the generic points of the strata lie off the exceptional sets
  have hxf := genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData hXproj hB Zd hZsm
    hZsnc hZpos hFC.two_le_codimension hstrata F
  have hx'f := genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData hX'proj hB' Zd' hZsm'
    hZsnc' hZpos' hflip.two_le_codimension hstrata' F'
  have hbir : f (ι (genericPoint S)) ∈ MMP.Mori.biregularLocus f := not_not.mp hxf
  have hbir' : fp (ι' (genericPoint S')) ∈ MMP.Mori.biregularLocus fp := not_not.mp hx'f
  have hcorr' : f (ι (genericPoint S)) = fp (ι' (genericPoint S')) := hcorr
  -- the open over which both contractions are isomorphisms, away from the non-snc loci
  obtain ⟨V, hfV, hfpV, hXV, hX'V, hVc⟩ := hflip.exists_opens_isIso
  haveI := hfV
  haveI := hfpV
  have hVf : V ≤ MMP.Mori.biregularLocus f := MMP.Mori.le_biregularLocus (f := f) (V := V)
    (inferInstance : IsIso (f ∣_ V))
  have hcl : IsClosed (f '' (Zd : Set X)) := f.isClosedMap _ Zd.isClosed
  have hcl' : IsClosed (fp '' (Zd' : Set X')) := fp.isClosedMap _ Zd'.isClosed
  let V₀ : Y.Opens := V ⊓ ⟨(f '' (Zd : Set X))ᶜ, hcl.isOpen_compl⟩ ⊓
    ⟨(fp '' (Zd' : Set X'))ᶜ, hcl'.isOpen_compl⟩
  have hV₀ : V₀ ≤ V := inf_le_left.trans inf_le_left
  have hV₀Z : ∀ z ∈ (Zd : Set X), f z ∉ V₀ := fun z hz h => h.1.2 ⟨z, hz, rfl⟩
  have hV₀Z' : ∀ z ∈ (Zd' : Set X'), fp z ∉ V₀ := fun z hz h => h.2 ⟨z, hz, rfl⟩
  obtain ⟨W, p, q, hres, hres', hpq, hiso, hiso'⟩ := exists_commonLogResolution hXproj hX'proj
    hB hB' hflip V hXV hX'V Zd hZsm hZsnc Zd' hZsm' hZsnc' V₀ hV₀ hV₀Z hV₀Z'
  -- the log resolutions
  have hvar : MMP.Mori.IsVariety k (p ≫ sX) := hres.2.1
  have hsm : IsSmoothScheme (p ≫ sX) := hres.2.2.1
  haveI : IsProper p := hres.2.2.2.1
  have hp : IsBirationalMorphism p := hres.2.2.2.2.1
  have hvar' : MMP.Mori.IsVariety k (q ≫ sX') := hres'.2.1
  have hsm' : IsSmoothScheme (q ≫ sX') := hres'.2.2.1
  haveI : IsProper q := hres'.2.2.2.1
  have hq : IsBirationalMorphism q := hres'.2.2.2.2.1
  haveI : IsIntegral W := hvar.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hvar.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ sX) := hvar.toQuasiCompact
  haveI : LocallyOfFiniteType (q ≫ sX') := hvar'.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ sX') := hvar'.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  obtain ⟨hWln, hWn⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
  haveI := hWln
  haveI := hWn
  haveI : IsDominant p := hp.isDominant
  have hWv : IsNormalVariety k (p ≫ sX) := ⟨hvar, inferInstance⟩
  have hWv' : IsNormalVariety k (q ≫ sX') := ⟨hvar', inferInstance⟩
  have hdW : topologicalKrullDim W = N :=
    topologicalKrullDim_eq_of_isBirationalMorphism (sX := sX) p hp hdX
  obtain ⟨E, hE, BW, hBWE, hcrW⟩ := exists_crepantBoundary_of_isLogResolution hXp p hWv hp hres
  obtain ⟨E', hE', B'W, hB'WE, hcrW'⟩ :=
    exists_crepantBoundary_of_isLogResolution hX'p q hWv' hq hres'
  -- the contracted prime divisor `P` lies over the flipped locus
  have hPf : fp (ι' P.genericPoint) ∉ MMP.Mori.biregularLocus fp := by
    haveI := F'.isClosedImmersion
    intro hb
    have hc := MMP.Positivity.coheight_map_of_mem_biregularLocus fp hb
    have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (fp (ι' P.genericPoint))
    have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX'
      (ι' P.genericPoint)
    rw [hc, hdY] at h1
    rw [hdX'] at h2
    have h3 := eq_of_add_coheight_eq h1 h2
    have e : topologicalKrullDim (closure {ι' P.genericPoint} : Set X') =
        topologicalKrullDim (closure {P.genericPoint} : Set S') := by
      rw [← Set.image_singleton, ι'.isClosedEmbedding.closure_image_eq,
        topologicalKrullDim_image_of_isEmbedding ι'.isClosedEmbedding.isEmbedding]
    rw [show (ι' ≫ fp).base P.genericPoint = fp (ι' P.genericPoint) from rfl, h3, e] at hP
    exact lt_irrefl _ hP
  refine isDiscrepancy_lt_of_commonLogResolution hflip hXp p q hWv hWv' hsm hsm' hp hq hpq E hE
    BW hBWE hcrW E' hE' B'W hB'WE hcrW' F F' hbir hcorr ?_ F'.isNormalVariety P hPf D hv ha ha'
  -- the strict transforms of the two strata are the closure of the same point
  intro s s' hps hqs hcs hcs'
  haveI : IsDominant q := hq.isDominant
  have hgen0 : ∀ w : W, Order.coheight w = 0 → w = genericPoint W := fun w hw =>
    ((genericPoint_specializes w).antisymm
      (Order.coheight_eq_zero.mp hw (genericPoint_specializes w))).eq.symm
  have hdom : ∀ {T : Scheme.{0}} [IsIntegral T] (g : W ⟶ T) [IsDominant g],
      g (genericPoint W) = genericPoint T := fun g =>
    MMP.Positivity.map_genericPoint_eq_of_isDominant g
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · -- `S = X`, hence `S⁺ = X⁺`
    have hs := hgen0 s (by rw [hcs, h0]; rfl)
    have hs' := hgen0 s' (coheight_eq_zero_of_apply_eq_genericPoint hX'v.1 hYv.1 hvar' fp hfs'
      (hdX'.trans hdY.symm) (hdW.trans hdX'.symm) s'
      (by rw [hqs, ← hcorr', ← hps, hs, hdom p, MMP.Positivity.map_genericPoint_eq_of_isDominant]))
    refine ⟨hs.trans hs'.symm, fun G hG => ?_⟩
    have h1 : Order.coheight G.genericPoint ≤ Order.coheight s :=
      Order.coheight_anti (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support _ hG)
    rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, hcs, h0] at h1
    exact absurd h1 (by decide)
  have hpos' : 0 < F'.length := by
    by_contra h0'
    have hs' := hgen0 s' (by rw [hcs', Nat.eq_zero_of_not_pos h0']; rfl)
    have h := coheight_eq_zero_of_apply_eq_genericPoint hXv.1 hYv.1 hvar f hfs
      (hdX.trans hdY.symm) (hdW.trans hdX.symm) s
      (by rw [hps, hcorr', ← hqs, hs', hdom q, MMP.Positivity.map_genericPoint_eq_of_isDominant])
    rw [hcs] at h
    norm_cast at h
    omega
  · -- both flags have positive length
    have hxZ := (notMem_and_isDltStratum_of_stratumAdjunctionData hXproj hB Zd hZsm hZsnc hZpos
      F hpos).1
    have hx'Z := (notMem_and_isDltStratum_of_stratumAdjunctionData hX'proj hB' Zd' hZsm' hZsnc'
      hZpos' F' hpos').1
    have hyV : f (ι (genericPoint S)) ∈ V := by
      by_contra hyV
      rcases hVc _ hyV with ⟨e, he, hey⟩ | ⟨e, he, hey⟩
      · exact (MMP.Mori.mem_exceptionalSet.mp he) (hey ▸ hbir)
      · exact (MMP.Mori.mem_exceptionalSet.mp he) (by rw [hey, hcorr']; exact hbir')
    have hyV₀ : f (ι (genericPoint S)) ∈ V₀ := by
      refine ⟨⟨hyV, ?_⟩, ?_⟩
      · rintro ⟨z, hz, hzx⟩
        have := eq_of_apply_eq_of_isIso_restrict f V (hzx ▸ hyV) hzx
        exact hxZ (this ▸ hz)
      · rintro ⟨z, hz, hzx⟩
        have hzV : fp z ∈ V := by rw [hzx]; exact hyV
        have := eq_of_apply_eq_of_isIso_restrict fp V hzV (hzx.trans hcorr')
        exact hx'Z (this ▸ hz)
    have hsU : p s ∈ f ⁻¹ᵁ V₀ := by
      change f (p s) ∈ V₀
      rw [hps]
      exact hyV₀
    have hfqs : fp (q s) = f (p s) := by
      rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply]
    have hqsx : q s = ι' (genericPoint S') :=
      eq_of_apply_eq_of_isIso_restrict fp V (by rw [hfqs]; exact hV₀ hsU)
        (by rw [hfqs, hps, hcorr'])
    have hqsU : q s ∈ fp ⁻¹ᵁ V₀ := by
      change fp (q s) ∈ V₀
      rw [hfqs]
      exact hsU
    refine ⟨eq_of_apply_eq_of_isIso_restrict q (fp ⁻¹ᵁ V₀) hqsU (hqsx.trans hqs.symm),
      fun G hG => ?_⟩
    have hsp : G.genericPoint ⤳ s := specializes_iff_mem_closure.mpr (by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hG)
    have hpG : p G.genericPoint ∈ f ⁻¹ᵁ V₀ :=
      (hsp.map p.base.hom.continuous).mem_open (f ⁻¹ᵁ V₀).isOpen hsU
    have h1 : Order.coheight (p G.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p
        (MMP.Mori.le_biregularLocus (f := p) (V := f ⁻¹ᵁ V₀) hiso hpG),
        MMP.Mori.PrimeDivisor.coheight_genericPoint]
    have h2 : Order.coheight (f (p G.genericPoint)) = Order.coheight (p G.genericPoint) :=
      MMP.Positivity.coheight_map_of_mem_biregularLocus f (hVf (hV₀ hpG))
    rw [Scheme.Hom.comp_apply, h2, h1]

end MMP.Fold06.LemMmpStratumDiscrepancyStrictTarget

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **Strict discrepancy increase along a contracted divisor of the flipped stratum.** In the
setting of `MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair`, let `P` be a prime
divisor of the stratum `S⁺` whose generic point maps to a point of `Y` with closure of smaller
dimension than `P`. If a divisor `D` over `S` has the same valuation on `𝒪_{Y,y}` as `P`, then
`a(D, S, B_S) < a(P, S⁺, B_{S⁺})`. -/
@[mmp "lem_mmp_stratum_discrepancy_strict_target"]
public theorem IsFlip.isDiscrepancy_lt_of_isStratumAdjunctionPair {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X X' Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsProjectiveVariety k sX) (hX' : IsProjectiveVariety k sX')
    (hB : MMP.Intersection.IsDltPair sX B)
    (hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B))
    (hflip : IsFlip sX sY sX' K B f fp)
    (hstrata : ∀ T : Set X, MMP.Fourfold.IsDltStratum sX B T →
      ¬ T ⊆ (exceptionalSet f : Set X))
    (hstrata' : ∀ T : Set X', MMP.Fourfold.IsDltStratum sX' (flipTransform f fp B) T →
      ¬ T ⊆ (exceptionalSet fp : Set X'))
    {S S' : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (hS : MMP.Fourfold.IsStratumAdjunctionPair sX B ι BS)
    (hS' : MMP.Fourfold.IsStratumAdjunctionPair sX' (flipTransform f fp B) ι' BS')
    (hcorr : (ι ≫ f).base (genericPoint S) = (ι' ≫ fp).base (genericPoint S'))
    (P : PrimeDivisor S')
    (hP : topologicalKrullDim (closure {(ι' ≫ fp).base P.genericPoint} : Set Y) <
      topologicalKrullDim (closure {P.genericPoint} : Set S'))
    (D : DivisorOver k (ι ≫ sX))
    (hv : D.valuation.comap ((ι ≫ f).stalkMap (genericPoint S)).hom =
      (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P).valuation.comap
        ((Y.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ (ι' ≫ fp).stalkMap (genericPoint S')).hom)
    {n n' : ℕ} {KS : Divisor S} {KS' : Divisor S'} {a a' : ℚ}
    (ha : IsDiscrepancy (ι ≫ sX) n KS BS D a)
    (ha' : IsDiscrepancy (ι' ≫ sX') n' KS' BS'
      (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P) a') :
    a < a' :=
  MMP.Fold06.LemMmpStratumDiscrepancyStrictTarget.isDiscrepancy_lt_of_isStratumAdjunctionPair hX
    hX' hB hB' hflip hstrata hstrata' hS hS' hcorr P hP D hv ha ha'

end MMP.Mori
