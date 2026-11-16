module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalFlips
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry

/-!
# Boundary strata are eventually preserved by a sequence of flips

For a sequence of `(K + B)`-flips starting from a projective dlt pair `(X₀, B₀)`, from some index
on no boundary stratum lies in a flipping or flipped locus, and every stratum of `(Xᵢ, Bᵢ)` has a
birational transform that is a stratum of `(Xᵢ₊₁, Bᵢ₊₁)`. The proof counts strata, whose number
can only decrease across a flip.
-/

section

open CategoryTheory TopologicalSpace MMP MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor IsProjectiveVariety

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fold06.LemMmpStrataEventuallyBirational

section CrepantStrata

open MMP.Fourfold Topology

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

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

/-- A point of the closure of `s` lies on every prime divisor through `s`. -/
private theorem pointClosureι_mem_support {W : Scheme.{0}} {s : W} {G : MMP.Mori.PrimeDivisor W}
    (hs : s ∈ G.support) (t : pointClosure s) : pointClosureι s t ∈ G.support :=
  closure_minimal (Set.singleton_subset_iff.mpr hs)
    (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
    (by rw [← range_pointClosureι]; exact ⟨t, rfl⟩)

private theorem isClosedImmersion_pointClosureIncl {W : Scheme.{0}} (s : W)
    (t : pointClosure s) : IsClosedImmersion (pointClosureIncl s t) := by
  haveI : IsClosedImmersion (pointClosureIncl s t ≫ pointClosureι s) := by
    rw [pointClosureIncl_ι]
    infer_instance
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

/-- A point lying on `t` components of an snc divisor has codimension at least `t`. -/
private theorem card_le_coheight_of_isSNC {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    {E : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ)))
    {T : Finset (MMP.Mori.PrimeDivisor W)} (hTE : T ⊆ E) {w : W}
    (hw : ∀ G ∈ T, w ∈ G.support) : (T.card : ℕ∞) ≤ Order.coheight w := by
  obtain ⟨N, z, j, hz, hj, -⟩ := MMP.Mori.exists_at_of_isSNC hE w
  have hN : (N : ℕ∞) = Order.coheight w := by
    have h1 := hz.2
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h1
    exact_mod_cast h1.symm
  rw [← hN]
  let φ : T → {G : MMP.Mori.PrimeDivisor W // G ∈ E ∧ w ∈ G.support} :=
    fun G => ⟨G.1, hTE G.2, hw G.1 G.2⟩
  have hφ : Function.Injective (j ∘ φ) :=
    hj.comp fun G G' h => Subtype.ext (congrArg Subtype.val h :)
  have := Fintype.card_le_of_injective _ hφ
  simp only [Fintype.card_coe, Fintype.card_fin] at this
  exact_mod_cast this

private theorem isSNC_sum_single_of_subset {W : Scheme.{0}} {sW : W ⟶ Spec (.of k)}
    {E T : Finset (MMP.Mori.PrimeDivisor W)}
    (hE : DivisorWithCoeffs.IsSNC sW (∑ G ∈ E, Finsupp.single G (1 : ℤ))) (hTE : T ⊆ E) :
    DivisorWithCoeffs.IsSNC sW (∑ G ∈ T, Finsupp.single G (1 : ℤ)) := by
  classical
  refine hE.of_support_subset fun G hG => ?_
  rw [Finsupp.mem_support_iff, coeff_sum_single] at hG ⊢
  split_ifs at hG with h
  · rw [if_pos (hTE h)]
    exact one_ne_zero
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
  have hwT : ∀ G ∈ insert G0 T, w ∈ G.support :=
    (Finset.forall_mem_insert _ _ _).mpr ⟨hwG, fun G hG => pointClosureι_mem_support (hTs G hG) t⟩
  have hsnc' := isSNC_sum_single_of_subset hE (Finset.insert_subset hG0 hTE)
  have hsncT := isSNC_sum_single_of_subset hE hTE
  obtain ⟨-, -, hstw⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW hsnc' hwT hwc
  obtain ⟨-, -, hsts⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW hsncT hTs hsc
  have e1 := hstw w (subset_closure rfl)
  rw [stalk_vanishingIdeal_closure_self, Finset.iSup_insert] at e1
  rw [← hsts w (by rw [← range_pointClosureι]; exact ⟨t, rfl⟩)] at e1
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

private theorem eq_add_of_add_eq_of_add_eq {a b : WithBot ℕ∞} {x y z : ℕ∞} {N : ℕ}
    (h1 : a + (x : WithBot ℕ∞) = N) (h2 : b + (z : WithBot ℕ∞) = N)
    (h3 : a + (y : WithBot ℕ∞) = b) : x = z + y := by
  induction a with
  | bot => simp at h1
  | coe a =>
    induction b with
    | bot => simp at h2
    | coe b =>
      have h1' : a + x = N := by exact_mod_cast h1
      have h2' : b + z = N := by exact_mod_cast h2
      have h3' : a + y = b := by exact_mod_cast h3
      induction a with
      | top => simp at h1'
      | coe a =>
        induction x with
        | top => simp at h1'
        | coe x =>
          induction b with
          | top => simp at h2'
          | coe b =>
            induction z with
            | top => simp at h2'
            | coe z =>
              induction y with
              | top => simp at h3'
              | coe y =>
                have e1 : a + x = N := by exact_mod_cast h1'
                have e2 : b + z = N := by exact_mod_cast h2'
                have e3 : a + y = b := by exact_mod_cast h3'
                have : x = z + y := by omega
                exact_mod_cast this

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
  exact eq_add_of_add_eq_of_add_eq h1 h2 h3

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
  have hy : pointClosureι s Q.genericPoint ∈ G0.support := by
    obtain ⟨G, hG, hyG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    have : G = G0 := by
      by_contra hne
      apply hG
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg (fun h => hne h.symm)]
    exact this ▸ hyG
  set w := pointClosureι s t
  obtain ⟨x, hxQ, hxt⟩ := hQt
  have hwT : ∀ G ∈ insert G0 T, w ∈ G.support :=
    (Finset.forall_mem_insert _ _ _).mpr ⟨hwG, fun G hG => pointClosureι_mem_support (hTs G hG) t⟩
  obtain ⟨-, -, hstw⟩ := MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC sW
    (isSNC_sum_single_of_subset hE (Finset.insert_subset hG0 hTE)) hwT hwc
  have hx' : pointClosureι s x ∈ closure {w} := by
    rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq]
    exact ⟨x, hxt, rfl⟩
  have hQx : Q.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxQ
  have hsp := hQx.map (pointClosureι s).base.hom.continuous
  have hyw : pointClosureι s Q.genericPoint ∈ closure ({w} : Set W) := by
    have := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})) hsp).mpr (by
        rw [hstw _ hx']
        refine iSup₂_le fun G hG => ?_
        refine (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes G.idealSheaf hsp).mp ?_
        rcases Finset.mem_insert.mp hG with rfl | hG
        · exact hy
        · exact pointClosureι_mem_support (hTs G hG) Q.genericPoint)
    change _ ∈
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {w})).support : Set W) at this
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at this
  rw [← Set.image_singleton, (pointClosureι s).isClosedEmbedding.closure_image_eq] at hyw
  obtain ⟨q, hq, hqy⟩ := hyw
  have hqQ : q = Q.genericPoint := (pointClosureι s).isClosedEmbedding.injective hqy
  rw [hqQ] at hq
  have htQ : t ⤳ Q.genericPoint := specializes_iff_mem_closure.mpr hq
  have heq : Q.genericPoint = t := by
    by_cases h2 : Q.genericPoint ⤳ t
    · exact (h2.antisymm htQ).eq
    · have hlt : Q.genericPoint < t := lt_of_le_not_ge htQ h2
      have h3 := Order.coheight_add_one_le hlt
      rw [hcoh, MMP.Mori.PrimeDivisor.coheight_genericPoint] at h3
      exact absurd h3 (by decide)
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact heq

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
      exact hg0 Z (DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, by
        rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same]; exact one_ne_zero, hxG⟩)
  obtain ⟨D1', hD1'⟩ := hD1c.exists_isPullback hsupp1
  have hD1'Q : D1'.coeff Q = 0 := coeff_isPullback_eq_zero_of_notMem hD1' Q hD1Q
  have hsuppc : ∀ Z : irreducibleComponents V,
      f (componentGenericPoint V Z) ∉
        DivisorWithCoeffs.supp (c • (Finsupp.single G0 (1 : ℤ) : Divisor Y)) := by
    intro Z hZ
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    have hGG : G = G0 := by
      by_contra hne
      apply hG
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (fun h => hne h.symm), smul_zero]
    subst hGG
    exact hg0 Z (DivisorWithCoeffs.mem_supp_iff.mpr ⟨G, by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same]; exact one_ne_zero, hxG⟩)
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

/-- Every nonzero rational `1`-fold form is a nonzero top form. -/
private theorem exists_toPluriForms_eq {S : Scheme.{0}} [IsIntegral S]
    {sS : S ⟶ Spec (.of k)} {d : ℕ} {σ : RationalPluriForms sS d 1} (hσ : σ ≠ 0) :
    ∃ ω : RationalTopForms sS d, ω.toPluriForms sS = σ ∧ ω ≠ 0 := by
  letI := functionFieldAlgebra sS
  set e := (PiTensorProduct.subsingletonEquiv (0 : Fin 1) :
    PiTensorProduct S.functionField (fun _ : Fin 1 => ⋀[S.functionField]^d Ω[S.functionField⁄k])
      ≃ₗ[S.functionField] ⋀[S.functionField]^d Ω[S.functionField⁄k])
  obtain ⟨ω, hω⟩ : ∃ ω : RationalTopForms sS d, ω.toPluriForms sS = σ := ⟨e σ, by
    change PiTensorProduct.tprod S.functionField (fun _ : Fin 1 => e σ) = σ
    exact e.injective (PiTensorProduct.subsingletonEquiv_apply_tprod _ _)⟩
  refine ⟨ω, hω, fun h => hσ ?_⟩
  rw [← hω, h]
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
    obtain ⟨G, hG, hsG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    have : G = G0 := by
      by_contra hne; apply hG
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg (fun h => hne h.symm)]
    exact hsG0 (this ▸ hsG)
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
    ω0 hω0 pS hZv hpS Θ).mp (hcr dS _ hKω0)
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' pS _)
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
  obtain ⟨ωσ, hωσ, hωσ0⟩ := exists_toPluriForms_eq hσ0
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
      (hcrσ (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' pS _)),
      hPσ]
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
    (hcrσ (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' pS _))
    hDdR hgcomp
  have hL1q := hL1.isQCartier hDσq
  obtain ⟨R1, hR1, -⟩ :=
    hL1q.existsUnique_isPullback
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' pV _)
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
  haveI : IsIso (pS.stalkMap (jW (genericPoint Y))) := by
    have key : ∀ x, x = Pt.genericPoint → IsIso (pS.stalkMap x) := by
      rintro x rfl; infer_instance
    exact key _ hjWP
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
  obtain ⟨ωρ, hωρ, hωρ0⟩ := exists_toPluriForms_eq hρσ0
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
  haveI hisoPt : IsIso (pS.stalkMap Pt.genericPoint) := by
    have key : ∀ x, x = t → IsIso (pS.stalkMap x) := by rintro x rfl; exact hiso
    exact key _ hPtg
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
  have hwT : ∀ G ∈ T, (pointClosureι s t) ∈ G.support := fun G hG =>
    pointClosureι_mem_support (hTs G hG).1 t
  have hinsc : (insert G0 T).card = T.card + 1 := Finset.card_insert_of_notMem hG0T
  have hwc : Order.coheight (pointClosureι s t) = (insert G0 T).card := by
    rw [hwc0, hinsc]
    norm_cast
  have hwonly : ∀ G ∈ E, (pointClosureι s t) ∈ G.support → G ∈ insert G0 T := by
    intro G hG hwG
    by_contra hGT
    have hc := card_le_coheight_of_isSNC hE
      (Finset.insert_subset hG (Finset.insert_subset hG0E hTE))
      ((Finset.forall_mem_insert _ _ _).mpr ⟨hwG, (Finset.forall_mem_insert _ _ _).mpr ⟨hwG0, hwT⟩⟩)
    rw [Finset.card_insert_of_notMem hGT, hwc] at hc
    norm_cast at hc
    omega
  have hsG0 : s ∉ G0.support := by
    intro hsG
    have hc := card_le_coheight_of_isSNC hE (Finset.insert_subset hG0E hTE)
      ((Finset.forall_mem_insert _ _ _).mpr ⟨hsG, fun G hG => (hTs G hG).1⟩)
    rw [hinsc, hsc] at hc
    norm_cast at hc
    omega
  -- the coefficient of `G₀`
  have hG0cart : Divisor.IsCartier (Finsupp.single G0 (1 : ℤ) : Divisor W) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hWsm _
  have hg0 : ∀ Z : irreducibleComponents (pointClosure s),
      pointClosureι s (componentGenericPoint _ Z) ∉
        DivisorWithCoeffs.supp (Finsupp.single G0 (1 : ℤ) : Divisor W) := by
    intro Z hZ
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, pointClosureι_genericPoint] at hZ
    obtain ⟨G, hG, hsG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hZ
    have : G = G0 := by
      by_contra hne; apply hG
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg (fun h => hne h.symm)]
    exact hsG0 (this ▸ hsG)
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
    ((Finset.forall_mem_insert _ _ _).mpr ⟨hwG0, hwT⟩) hwc
  have hsqW : pV ≫ j ≫ ι = pointClosureι (pointClosureι s t) ≫ p := by
    rw [← Category.assoc, hsqV, Category.assoc, hsq, ← Category.assoc, pointClosureIncl_ι]
  have hsW : pV ≫ (j ≫ ι) ≫ sX = pointClosureι (pointClosureι s t) ≫ p ≫ sX := by
    rw [← Category.assoc pV, hsqW, Category.assoc]
  have hZwsm' : IsSmoothScheme (pV ≫ (j ≫ ι) ≫ sX) := by rwa [hsW]
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
    refine hG ?_
    rw [hA'def, coeff_sub_sum_smul_single, ite_eq_left_iff]
    intro hGT
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
  refine ⟨pointClosureι s t, pV, insert G0 T, hZwln, hZwn, hZv', hpVb, hsqW, hpVp, hZwsm', ?_,
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
  have hdW : topologicalKrullDim W = n := by
    rw [MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (p ≫ sX),
      ← MMP.Mori.trdeg_functionField_eq_of_bijective sX p hp.functionFieldMap_bijective,
      MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX]
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
      simp only [Scheme.topIso_hom, hGg]
      rfl
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

/-! ### The final stratum of a flag of a dlt pair -/

/-- A specialization between points of equal finite codimension is an equality. -/
private theorem eq_of_specializes_of_coheight_le {W : Scheme.{0}} {w s : W} (h : w ⤳ s)
    (hc : Order.coheight s ≤ Order.coheight w) (htop : Order.coheight s ≠ ⊤) : w = s := by
  by_contra hne
  have hlt : s < w := lt_of_le_not_ge h fun h' => hne (h.antisymm h').eq
  exact absurd hc (not_le.mpr (Order.coheight_strictAnti hlt
    ((Order.coheight_anti hlt.le).trans_lt htop.lt_top)))

open Classical in
/-- **A flag of a dlt pair ends at the centre of a divisor of discrepancy at most `-1`.** For a
flag of iterated adjunction data of a dlt pair `(X, B)` ending at `(S, B_S)` of positive length,
there is a divisor `D` over `X`, with proper model, whose centre has generic point `ι(η_S)` and
whose discrepancy `a(D, X, B)` is at most `-1` for every canonical divisor of `X`. -/
private theorem exists_divisorOver_of_stratumAdjunctionData {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    {B : QDivisor X} (hXv : IsNormalVariety k sX) (hB : MMP.Intersection.IsDltPair sX B)
    {S : Scheme.{0}} [IsIntegral S] {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (hne : ι (genericPoint S) ≠ genericPoint X) :
    ∃ D : DivisorOver k sX, IsProper D.f ∧ D.f D.E.genericPoint = ι (genericPoint S) ∧
      ∃ a : ℚ, a ≤ -1 ∧ ∀ (d : ℕ) (K' : Divisor X), K'.IsCanonicalDivisor sX d →
        IsDiscrepancy sX d K' B D a := by
  obtain ⟨⟨hpair, -, hlc⟩, hB1, Z, hZsm, hZsnc, hZpos⟩ := hB
  obtain ⟨-, n, K, hK, hQ⟩ := hpair
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  -- a log resolution which is an isomorphism over the snc locus `X ∖ Z`
  obtain ⟨W, p, hres, -, hsnc, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (k := k) sX hXv
      B.support
  have hZV : (Z.compl : X.Opens) ≤ biregularLocus p :=
    le_biregularLocus (hiso _ hZsm (MMP.Intersection.isSNCClosedSubset_preimage_of_isSNC sX _ B
      hZsnc))
  have hWvar := hres.isVariety_source
  have : IsIntegral W := hWvar.toIsIntegral
  have : LocallyOfFiniteType (p ≫ sX) := hWvar.toLocallyOfFiniteType
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have hWsm := hres.isSmoothScheme
  have : Smooth (p ≫ sX) := (MMP.Mori.isSmoothScheme_iff (p ≫ sX)).mp hWsm
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal W := AlgebraicGeometry.isNormal_of_smooth (p ≫ sX)
  have hWv : IsNormalVariety k (p ≫ sX) := ⟨hWvar, inferInstance⟩
  have hp := hres.isBirationalMorphism
  have : IsDominant p := hp.isDominant
  have : IsProper p := hres.isProjective.isProper
  -- the snc divisor of the prime divisors in `Ex(p) ∪ p⁻¹(Supp B)`
  have hfin := MMP.Intersection.finite_setOf_support_subset hsnc
  set E := hfin.toFinset with hEdef
  have hreg : ∀ y : W, ∃ (m : ℕ) (z : Fin m → W.presheaf.stalk y),
      IsRegularSystemOfParameters z := by
    intro y
    have := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk (p ≫ sX)).mp
      inferInstance y
    exact exists_isRegularSystemOfParameters _
  have hE : DivisorWithCoeffs.IsSNC (p ≫ sX) (∑ G ∈ E, Finsupp.single G (1 : ℤ)) :=
    MMP.Intersection.isSNC_reducedDivisorOf_of_mem_componentsOf hreg hsnc E
      fun P hP => MMP.Intersection.support_mem_componentsOf hsnc P (hfin.mem_toFinset.mp hP)
  -- the crepant boundary of `(X, B)` on `W`
  have hP : MMP.Mori.IsPair sX B := ⟨hXv, n, K, hK, hQ⟩
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := hP.existsUnique_isCrepantBoundary hK p hWv hp
  have hcrW : ∀ (d : ℕ) (K' : Divisor X), K'.IsCanonicalDivisor sX d →
      IsCrepantBoundary sX d K' B p hWv hp BW := by
    intro d K' hK'
    have hd : d = n := by
      have h1 := hK'.topologicalKrullDim_eq
      rw [hK.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    subst hd
    exact isCrepantBoundary_of_isCanonicalDivisor hBW hK'
  -- a prime divisor of `W` over the biregular locus is the strict transform of one of `X`
  have hnonexc : ∀ G : MMP.Mori.PrimeDivisor W, p G.genericPoint ∈ biregularLocus p →
      ∃ C : MMP.Mori.PrimeDivisor X, C.genericPoint = p G.genericPoint ∧
        B.coeff C = BW.coeff G := by
    intro G hGV
    set D : DivisorOver k sX := ⟨W, p, hWv, hp, G⟩ with hD
    have hnex : ¬ D.IsExceptional := by
      rw [DivisorOver.isExceptional_iff_two_le_coheight hXv]
      change ¬ 2 ≤ Order.coheight (p G.genericPoint)
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p hGV,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
      decide
    obtain ⟨C, hCv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXv D hnex
    have hcen := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXv hCv
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
      (DivisorOver.ofPrimeDivisor k hXv C)
    have h1 := ha.eq_neg_coeff_of_ofPrimeDivisor hXv
    have h2 := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hCv hcen
      (hBW G) ha
    refine ⟨C, ?_, ?_⟩
    · rw [hcen]; rfl
    · linarith
  have hBclosed : IsClosed (B.support.sup fun E => (E.idealSheaf.support : Set X)) := by
    rw [Finset.sup_set_eq_biUnion]
    exact isClosed_biUnion_finset fun E _ => E.idealSheaf.support.isClosed
  have hBWE : ∀ G, BW.coeff G ≠ 0 → G ∈ E := by
    intro G hG
    rw [hEdef, Set.Finite.mem_toFinset]
    show (G.support : Set W) ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    by_cases hGx : p G.genericPoint ∈ biregularLocus p
    · obtain ⟨C, hCg, hCc⟩ := hnonexc G hGx
      have hCB : C ∈ B.support := Finsupp.mem_support_iff.mpr (by
        rw [← DivisorWithCoeffs.coeff_apply, hCc]; exact hG)
      refine Set.subset_union_of_subset_right ?_ _
      refine closure_minimal (Set.singleton_subset_iff.mpr ?_) (hBclosed.preimage p.continuous)
      show p G.genericPoint ∈ B.support.sup fun E => (E.idealSheaf.support : Set X)
      refine (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X =>
        (E.idealSheaf.support : Set X)) hCB) ?_
      rw [← hCg]
      show C.genericPoint ∈ (C.support : Set X)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    · refine Set.subset_union_of_subset_left ?_ _
      exact closure_minimal (Set.singleton_subset_iff.mpr hGx) (MMP.Mori.exceptionalSet p).isClosed
  obtain ⟨s, pS, T, _, _, hZv, hpS, hcomm, -, -, hTE, hTcard, hcoh, hTs, -, -⟩ :=
    exists_crepantStratum p hWv hWsm hp E hE BW hBWE hcrW F
  -- `s` lies over the generic point of `S`
  have hps : p s = ι (genericPoint S) := by
    haveI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure s
    have : IsDominant pS := hpS.isDominant
    have h1 := congrArg (fun φ : pointClosure s ⟶ X => φ (genericPoint (pointClosure s))) hcomm
    simp only [Scheme.Hom.comp_apply] at h1
    rw [pointClosureι_genericPoint, MMP.Positivity.map_genericPoint_eq_of_isDominant pS] at h1
    exact h1.symm
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · exfalso
    apply hne
    rw [hT0, Finset.card_empty, Nat.cast_zero, Order.coheight_eq_zero] at hcoh
    have hs : genericPoint W = s :=
      ((genericPoint_specializes s).antisymm (hcoh (genericPoint_specializes s))).eq
    rw [← hps, ← hs, MMP.Positivity.map_genericPoint_eq_of_isDominant p]
  have hsG : ∀ G ∈ T, s ∈ G.support := fun G hG => (hTs G hG).1
  obtain ⟨G₀, hG₀⟩ := hTne
  by_cases h1 : T.card = 1
  · have h2 : G₀.genericPoint ⤳ s := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hsG G₀ hG₀
    have hsη : G₀.genericPoint = s := eq_of_specializes_of_coheight_le h2
      (by rw [hcoh, h1, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]; rfl)
      (by rw [hcoh]; exact ENat.coe_ne_top _)
    refine ⟨⟨W, p, hWv, hp, G₀⟩, inferInstanceAs (IsProper p), ?_, -BW.coeff G₀,
      by linarith [(hTs G₀ hG₀).2], fun d K' hK' => hcrW d K' hK' G₀⟩
    show p G₀.genericPoint = _
    rw [hsη, hps]
  have hc2 : 2 ≤ T.card := by
    have := Finset.card_pos.mpr ⟨G₀, hG₀⟩
    omega
  have hTsnc := isSNC_sum_single_of_subset hE hTE
  obtain ⟨-, hZsm', hIst⟩ :=
    MMP.Fourfold.closure_singleton_mem_componentsOf_of_isSNC (p ≫ sX) hTsnc hsG hcoh
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {s}) with hI
  have hIsupp : (I.support : Set W) = closure {s} := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hirr : IsIrreducible (I.support : Set W) := hIsupp ▸ isIrreducible_singleton.closure
  have hcodim : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds W) =
      T.card := by
    have : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds W) =
        IrreducibleCloseds.closureSingleton s := IrreducibleCloseds.ext hIsupp
    rw [this, MMP.Flips.codimension_closureSingleton, hcoh]
  have hc1' : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds W) := by
    rw [hcodim]; exact_mod_cast (by omega : 1 ≤ T.card)
  have hsb : MMP.Resolution.IsSmoothBlowup (p ≫ sX) I := ⟨hWsm, hZsm'⟩
  have hdimW : topologicalKrullDim W = n := by
    rw [← hK.topologicalKrullDim_eq, ← toENat_trdeg_functionField (sX := p ≫ sX),
      ← toENat_trdeg_functionField (sX := sX),
      trdeg_functionField_eq_of_bijective _ p hp.functionFieldMap_bijective]
  obtain ⟨hvar, hsmB, hproj, hbir, -, -, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (p ≫ sX) hWvar hdimW I hsb hirr hcodim.symm hc2
  set π := blowUpToBase I with hπ
  haveI := MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1'
  haveI := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1'
  haveI : Smooth (π ≫ p ≫ sX) := hsmB
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (π ≫ p ≫ sX)
  haveI : IsNormal (AlgebraicGeometry.blowUp I) :=
    AlgebraicGeometry.isNormal_of_smooth (π ≫ p ≫ sX)
  haveI : IsProper π := hproj.isProper
  have hNπ : IsNormalVariety k (π ≫ p ≫ sX) := ⟨hvar, inferInstance⟩
  have hN : IsNormalVariety k ((π ≫ p) ≫ sX) := by rw [Category.assoc]; exact hNπ
  have hb : IsBirationalMorphism (π ≫ p) := isBirationalMorphism_comp hbir hp
  set Ex := MMP.Fourfold.SNCWeight.StratumBlowup.excE (p ≫ sX) hsb hirr hc1' with hEx
  obtain ⟨KW, hKW⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sX) hWsm hdimW
  obtain ⟨hPW, hiff⟩ := hP.isDiscrepancy_iff_of_crepant p hWv hp hK hKW (Or.inl hBW)
  have hexc : IsDiscrepancy (p ≫ sX) n KW BW
      ⟨AlgebraicGeometry.blowUp I, π, hNπ, hbir, Ex⟩ (-1) := by
    refine MMP.Fourfold.isDiscrepancy_excE_neg_one (p ≫ sX) hKW hPW hsb hirr hcodim.symm
      (by omega) hTsnc (fun G hG => ?_) (fun x hx => hIst x (by rw [← hIsupp]; exact hx))
      (fun Γ hΓ => ?_) hNπ hc1' hbir
    · rw [hIsupp]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hsG G hG))
        (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support G)
    · have hsΓ : s ∈ Γ.support := hΓ (by rw [hIsupp]; exact subset_closure rfl)
      split_ifs with hΓT
      · have h1 := (hTs Γ hΓT).2
        have h2 := hlc n ⟨W, p, hWv, hp, Γ⟩ _
          (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBW Γ)
            (inferInstanceAs (IsProper p)))
        have h3 : (BW.coeff Γ : ℝ) ≤ 1 := by push_cast at h2; linarith
        have h4 : BW.coeff Γ ≤ 1 := by exact_mod_cast h3
        linarith
      · by_contra hne
        have hΓE := hBWE Γ hne
        have := card_le_coheight_of_isSNC hE (Finset.insert_subset hΓE hTE)
          ((Finset.forall_mem_insert _ _ _).mpr ⟨hsΓ, hsG⟩)
        rw [Finset.card_insert_of_notMem hΓT, hcoh] at this
        exact absurd this (by norm_cast; omega)
  set E' : DivisorOver k sX := ⟨AlgebraicGeometry.blowUp I, π ≫ p, hN, hb, Ex⟩
  have hπη : π Ex.genericPoint = s := by
    have hcl := MMP.Fourfold.SNCWeight.BlowupCrepancy.closure_map_genericPoint_excE
      (p ≫ sX) hsb hirr hc1'
    rw [hIsupp] at hcl
    exact (inseparable_iff_closure_eq.mpr hcl).eq
  refine ⟨E', inferInstanceAs (IsProper (π ≫ p)), ?_, -1, le_rfl, fun d K' hK' => ?_⟩
  · show (π ≫ p) Ex.genericPoint = _
    rw [Scheme.Hom.comp_apply, hπη, hps]
  · have hd : d = n := by
      have h1 := hK'.topologicalKrullDim_eq
      rw [hK.topologicalKrullDim_eq] at h1
      exact_mod_cast h1.symm
    subst hd
    obtain ⟨-, hiff'⟩ := hP.isDiscrepancy_iff_of_crepant p hWv hp hK' hKW (Or.inl (hcrW _ K' hK'))
    refine (hiff' ⟨AlgebraicGeometry.blowUp I, π, hNπ, hbir, Ex⟩ E' ?_ (-1)).mp hexc
    ext t
    change Ex.divisorialValuation (functionFieldMap (π ≫ p) t) =
      Ex.divisorialValuation (functionFieldMap π (functionFieldMap p t))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

end CrepantStrata

/-! ### Strata of a dlt pair are centres of divisors of discrepancy at most `-1` -/

section Strata

open MMP.Fourfold

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- **A boundary stratum of a dlt pair is the centre of a divisor of discrepancy at most `-1`.**
For a boundary stratum `T` of a dlt pair `(X, B)` there is a divisor `D` over `X`, with proper
model, whose centre has as generic point the generic point `x` of `T`, and with `a(D, X, B) ≤ -1`
for every canonical divisor of `X`. -/
private theorem IsDltStratum.exists_divisorOver_isDiscrepancy_le_neg_one {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hXv : IsNormalVariety k sX) {T : Set X}
    (hT : IsDltStratum sX B T) :
    ∃ x : X, IsGenericPoint x T ∧ ∃ D : DivisorOver k sX, IsProper D.f ∧
      D.f D.E.genericPoint = x ∧ ∃ a : ℚ, a ≤ -1 ∧ ∀ (d : ℕ) (K' : Divisor X),
        K'.IsCanonicalDivisor sX d → IsDiscrepancy sX d K' B D a := by
  have hdlt := hT.1
  obtain ⟨⟨⟨S, ι, BS, hr, hS⟩, -⟩, -⟩ := hT.exists_isStratumAdjunctionPair_and_isDltPair
  have F := hS.some
  haveI : IsIntegral S := F.isIntegral_stratum
  haveI := F.isClosedImmersion
  have hTc : IsClosed T := hr ▸ ι.isClosedEmbedding.isClosed_range
  have hx : IsGenericPoint (ι (genericPoint S)) T := by
    refine Set.Subset.antisymm
      (closure_minimal (Set.singleton_subset_iff.mpr (hr ▸ ⟨_, rfl⟩)) hTc) ?_
    rw [← hr]
    rintro _ ⟨s, rfl⟩
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes s).map ι.continuous)
  obtain ⟨-, J, ⟨P, hP⟩, -, -, hmax⟩ := hT
  have hxP : ι (genericPoint S) ∈ (P.support : Set X) := by
    have h1 := hmax.1.2 hx.mem
    simp only [Set.mem_iInter] at h1
    exact h1 P hP
  have hne : ι (genericPoint S) ≠ genericPoint X := fun h =>
    MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P (h ▸ hxP)
  obtain ⟨D, hDp, hDx, a, ha, hdisc⟩ := exists_divisorOver_of_stratumAdjunctionData hXv hdlt F hne
  exact ⟨_, hx, D, hDp, hDx, a, ha, hdisc⟩

end Strata

/-! ### One flip -/

section Flip

open MMP.Fourfold

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- A flip `MMP.Fourfold.IsFlipOf` of `K + B`, with `K` canonical, is a flip `MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFlipOf {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    IsFlip sX sZ sX' K B f fp := by
  have hc := hflip.isContraction
  have hs := hflip.isSmallMorphism
  have hs' := hflip.isSmallMorphism_flip
  have he : flipTransform f fp (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B := by
    rw [map_add, MMP.Mori.flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := hc.isNormalVariety_source
          isNormalVariety_target := hc.isNormalVariety_target
          comp_eq := hc.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := hflip.isQCartier
          isProper := hs.isProper
          isBirationalMorphism := hs.isBirationalMorphism
          two_le_codimension := hs.two_le_codimension
          hasRelativelyAmpleMultiple := hflip.hasRelativelyAmpleMultiple }
      isNormalVariety := hs'.isNormalVariety_source
      comp_eq := hs'.comp_eq
      isProper := hs'.isProper
      isBirationalMorphism := hs'.isBirationalMorphism
      isQCartier := he ▸ hflip.isQCartier_flip
      hasRelativelyAmpleMultiple := he ▸ hflip.hasRelativelyAmpleMultiple_flip
      two_le_codimension := hs'.two_le_codimension }

/-- **One flip of a dlt pair.** Let `f⁺ : X⁺ ⟶ Z` be a `(K + B)`-flip of `f : X ⟶ Z` with `(X, B)`
dlt. Then `(X⁺, B⁺)`, `B⁺ = (f⁺)⁻¹_* f_* B`, is dlt, and every boundary stratum `T⁺` of `(X⁺, B⁺)`
has its generic point over the locus of `Z` over which both `f` and `f⁺` are isomorphisms. -/
private theorem isDltPair_and_map_mem_biregularLocus {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hB : MMP.Intersection.IsDltPair sX B) :
    MMP.Intersection.IsDltPair sX' (flipTransform f fp B) ∧
      ∀ T' : Set X', IsDltStratum sX' (flipTransform f fp B) T' →
        ∃ x' : X', IsGenericPoint x' T' ∧ fp x' ∈ biregularLocus f ∧
          fp x' ∈ biregularLocus fp := by
  have hMF := isFlip_of_isFlipOf hK hflip
  have hFC := hMF.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hX'v := hMF.isNormalVariety
  have hYv := hFC.isNormalVariety_target
  have hK' := hMF.isCanonicalDivisor_flipTransform (k := k) hK
  have hBm : MMP.Mori.IsDltPair sX n K B :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hB
  have hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B) :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX' hK' _).mpr (hMF.isDltPair hBm)
  refine ⟨hB', fun T' hT' => ?_⟩
  obtain ⟨x', hx', D', -, hD'x, a', ha'1, ha'⟩ :=
    IsDltStratum.exists_divisorOver_isDiscrepancy_le_neg_one hX'v hT'
  refine ⟨x', hx', ?_⟩
  have : IsProper f := hFC.isProper
  have : IsProper fp := hMF.isProper
  have : IsIntegral Z := hYv.1.toIsIntegral
  have : IsSeparated sZ := hYv.1.toIsSeparated
  have : IsDominant f := hFC.isBirationalMorphism.isDominant
  have : IsDominant fp := hMF.isBirationalMorphism.isDominant
  have : QuasiCompact sX := hXv.1.toQuasiCompact
  have : QuasiCompact sX' := hX'v.1.toQuasiCompact
  obtain ⟨V, hVf, hVfp, -, hX'V, -⟩ := hMF.exists_opens_isIso
  by_contra hcon
  have hcoh : 2 ≤ Order.coheight x' := by
    by_contra h2
    have h1 : Order.coheight x' ≤ 1 := by
      contrapose! h2
      exact Order.add_one_le_of_lt h2
    have hV := hX'V x' h1
    exact hcon ⟨le_biregularLocus hVf hV, le_biregularLocus hVfp hV⟩
  have hD'ex : D'.IsExceptional := by
    rw [DivisorOver.isExceptional_iff_two_le_coheight hX'v, hD'x]
    exact hcoh
  obtain ⟨D, hv⟩ := hMF.exists_divisorOver_valuation_comap_eq D'
  obtain ⟨hex1, hex2⟩ := hMF.isExceptional_iff_and_isExceptional_comp D D' hv
  have hDex := hex1.mp hD'ex
  have hE := hex2 hDex
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.1 hK D
  have hlc : (-1 : ℚ) ≤ a := by
    have := hBm.isLcPair.2.trans (discrep_le hDex ha)
    rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp] at this
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  have hy : f (D.f D.E.genericPoint) = fp (D'.f D'.E.genericPoint) :=
    MMP.Mori.map_genericPoint_eq_of_valuation_comap_eq sZ f fp D D' hv
  have ha'' := ha' n _ hK'
  have hN := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := sX)
    hFC.hasRelativelyAmpleMultiple
  have hN' := isRelativelyNef_of_hasRelativelyAmpleMultiple (sX := sX')
    hMF.hasRelativelyAmpleMultiple
  have hΔY := (transformDivisor_inverseTransformDivisor hYv
    (by rw [hMF.comp_eq]; exact hMF.isNormalVariety) hMF.isBirationalMorphism
    hMF.two_le_codimension
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap B)).symm
  have hlt : a < a' := by
    by_cases hW : fp (D'.f D'.E.genericPoint) ∈ biregularLocus fp
    · have hW' : f (D.f D.E.genericPoint) ∉ biregularLocus f := by
        rw [hy, hD'x]
        exact fun h => hcon ⟨h, hD'x ▸ hW⟩
      exact isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple hXv hX'v hYv hFC.comp_eq
        hMF.comp_eq hFC.isBirationalMorphism hMF.isBirationalMorphism hK hK' hΔY hN hN'
        hFC.hasRelativelyAmpleMultiple D D' hv hE hW' ha ha''
    · exact isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target hXv hX'v hYv hFC.comp_eq
        hMF.comp_eq hFC.isBirationalMorphism hMF.isBirationalMorphism hK hK' hΔY hN hN'
        D D' hv hE hMF.hasRelativelyAmpleMultiple hW ha ha''
  linarith

/-- Over the biregular locus of `g` every point has a preimage. -/
private theorem exists_eq_of_mem_biregularLocus {X Y : Scheme.{0}} (g : X ⟶ Y) {y : Y}
    (hy : y ∈ biregularLocus g) : ∃ x : X, g x = y := by
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  obtain ⟨z, hz⟩ := (g ∣_ biregularLocus g).surjective ⟨y, hy⟩
  refine ⟨(g ⁻¹ᵁ biregularLocus g).ι z, ?_⟩
  have := congrArg (fun u => (biregularLocus g).ι u) hz
  simp only at this
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply] at this
  exact this

/-- The closure of the image of the closure of a point is the closure of the image point. -/
private theorem closure_image_closure_singleton {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {g : A → B} (hg : Continuous g) (a : A) :
    closure (g '' closure {a}) = closure {g a} := by
  rw [closure_image_closure hg, Set.image_singleton]

/-- Two irreducible closed subsets whose generic points lie over the biregular locus of `g` and
which have the same closure of image under `g` are equal. -/
private theorem eq_of_closure_image_eq {X Y : Scheme.{0}} (g : X ⟶ Y) {T₁ T₂ : Set X}
    {x₁ x₂ : X} (h₁ : IsGenericPoint x₁ T₁) (h₂ : IsGenericPoint x₂ T₂)
    (hV₁ : g x₁ ∈ biregularLocus g) (hV₂ : g x₂ ∈ biregularLocus g)
    (h : closure (g.base '' T₁) = closure (g.base '' T₂)) : T₁ = T₂ := by
  rw [← h₁.def, ← h₂.def, closure_image_closure_singleton g.continuous,
    closure_image_closure_singleton g.continuous] at h
  have he : g x₁ = g x₂ := (inseparable_iff_closure_eq.mpr h).eq
  have h12 : x₁ ⤳ x₂ :=
    MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hV₁ hV₂ (he ▸ specializes_rfl)
  have h21 : x₂ ⤳ x₁ :=
    MMP.Threefold.Resolution.specializes_of_mem_biregularLocus g hV₂ hV₁ (he ▸ specializes_rfl)
  rw [← h₁.def, ← h₂.def, (h12.antisymm h21).eq]

/-- **Strata over the common isomorphism locus correspond.** Let `f⁺ : X⁺ ⟶ Z` be a
`(K + B)`-flip of `f : X ⟶ Z` with `(X, B)` dlt, and `T⁺` a boundary stratum of `(X⁺, B⁺)` with
generic point `x⁺` over the locus where `f` and `f⁺` are isomorphisms. Then the closure `S` of
the point of `X` over `f⁺(x⁺)` is a boundary stratum of `(X, B)` not contained in `Ex(f)`, with
`closure (f(S)) = closure (f⁺(T⁺))`. -/
private theorem exists_isDltStratum_of_mem_biregularLocus {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hB : MMP.Intersection.IsDltPair sX B) {T' : Set X'}
    (hT' : IsDltStratum sX' (flipTransform f fp B) T') {x' : X'} (hx' : IsGenericPoint x' T')
    (hf : fp x' ∈ biregularLocus f) (hfp : fp x' ∈ biregularLocus fp) :
    ∃ S : Set X, IsDltStratum sX B S ∧ ¬ S ⊆ (exceptionalSet f : Set X) ∧
      closure (f.base '' S) = closure (fp.base '' T') := by
  classical
  have hMF := isFlip_of_isFlipOf hK hflip
  have hFC := hMF.isFlippingContraction
  have hYv := hFC.isNormalVariety_target
  have : IsProper f := hFC.isProper
  obtain ⟨V, hVf, hVfp, hXV, hX'V, -⟩ := hMF.exists_opens_isIso
  obtain ⟨x, hxy⟩ := exists_eq_of_mem_biregularLocus f hf
  have hxf : f x ∈ biregularLocus f := hxy ▸ hf
  have hxfp : f x ∈ biregularLocus fp := hxy ▸ hfp
  obtain ⟨-, J', hJ'ne, hJ'1, -, hmax'⟩ := hT'
  -- the prime divisors of `X` corresponding to those of `X⁺`
  have hPc : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp P'.genericPoint := by
    intro P'
    have hV : fp P'.genericPoint ∈ V :=
      hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
    obtain ⟨u, hu⟩ := exists_eq_of_mem_biregularLocus f (le_biregularLocus hVf hV)
    have hcu : Order.coheight u = 1 := by
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f
        (hu ▸ le_biregularLocus hVf hV), hu,
        MMP.Positivity.coheight_map_of_mem_biregularLocus fp (le_biregularLocus hVfp hV)]
      exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P'
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne u hcu, ?_⟩
    show f (AlgebraicGeometry.PrimeDivisor.genericPoint _) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hu]
  choose φ hφ using hPc
  have hφV : ∀ P' : MMP.Mori.PrimeDivisor X',
      fp P'.genericPoint ∈ biregularLocus f ∧ fp P'.genericPoint ∈ biregularLocus fp := by
    intro P'
    have hV := hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
    exact ⟨le_biregularLocus hVf hV, le_biregularLocus hVfp hV⟩
  have hmem : ∀ {W : Scheme.{0}} (P : MMP.Mori.PrimeDivisor W) (w : W),
      w ∈ (P.support : Set W) ↔ P.genericPoint ⤳ w := fun P w => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]
  set J : Finset (MMP.Mori.PrimeDivisor X) := J'.image φ with hJ
  have hJ1 : ∀ P ∈ J, 1 ≤ B.coeff P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
    have hc := MMP.Mori.flipTransform_apply hYv
      (by rw [hFC.comp_eq]; exact hFC.isNormalVariety_source) hFC.isBirationalMorphism V hXV
      (hφ P') B
    have h1 := hJ'1 P' hP'
    rw [DivisorWithCoeffs.coeff_apply] at h1 ⊢
    rwa [hc] at h1
  have hCcl : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
    isClosed_biInter fun P _ => P.idealSheaf.support.isClosed
  have hC'cl : IsClosed (⋂ P ∈ J', (P.support : Set X')) :=
    isClosed_biInter fun P _ => P.idealSheaf.support.isClosed
  have hx'J : ∀ P' ∈ J', x' ∈ (P'.support : Set X') := by
    have h1 := hmax'.1.2 hx'.mem
    simp only [Set.mem_iInter] at h1
    exact h1
  have hxJ : x ∈ ⋂ P ∈ J, (P.support : Set X) := by
    simp only [Set.mem_iInter]
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
    rw [hmem]
    have h1 := ((hmem P' x').mp (hx'J P' hP')).map fp.continuous
    rw [← hφ P', ← hxy] at h1
    exact MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f
      (by rw [hφ P']; exact (hφV P').1) hxf h1
  refine ⟨closure {x}, ⟨hB, J, hJ'ne.image φ, hJ1, ⟨x, hxJ⟩,
    ⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.mpr hxJ) hCcl⟩,
    fun R hR hSR => ?_⟩, fun h => (mem_exceptionalSet.mp (h (subset_closure rfl))) hxf, ?_⟩
  · obtain ⟨hRirr, hRsub⟩ := hR
    have hr := hRirr.isGenericPoint_genericPoint_closure
    set r := hRirr.genericPoint
    have hrR : r ∈ closure R := by rw [← hr.def]; exact subset_closure rfl
    have hrJ : r ∈ ⋂ P ∈ J, (P.support : Set X) := closure_minimal hRsub hCcl hrR
    simp only [Set.mem_iInter] at hrJ
    have hrx : r ⤳ x := by
      rw [specializes_iff_mem_closure, hr.def]
      exact subset_closure (hSR (subset_closure rfl))
    have hfr : f r ⤳ f x := hrx.map f.continuous
    have hrVf : f r ∈ biregularLocus f := hfr.mem_open (biregularLocus f).isOpen hxf
    have hrVfp : f r ∈ biregularLocus fp := hfr.mem_open (biregularLocus fp).isOpen hxfp
    obtain ⟨r', hr'⟩ := exists_eq_of_mem_biregularLocus fp hrVfp
    have hr'x' : r' ⤳ x' :=
      MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fp (hr' ▸ hrVfp) hfp
        (by rw [hr', ← hxy]; exact hfr)
    have hr'J : ∀ P' ∈ J', r' ∈ (P'.support : Set X') := by
      intro P' hP'
      have h1 := ((hmem (φ P') r).mp (hrJ (φ P') (Finset.mem_image_of_mem φ hP'))).map
        f.continuous
      rw [hφ P', ← hr'] at h1
      exact (hmem P' r').mpr
        (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus fp (hφV P').2 (hr' ▸ hrVfp) h1)
    have hcl' : closure {r'} ⊆ T' := hmax'.2 ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr (by simp only [Set.mem_iInter]; exact hr'J))
        hC'cl⟩ (by rw [← hx'.def]; exact specializes_iff_closure_subset.mp hr'x')
    have hx'r' : x' ⤳ r' := by
      rw [specializes_iff_mem_closure, hx'.def]
      exact hcl' (subset_closure rfl)
    have hr'e : r' = x' := (hr'x'.antisymm hx'r').eq
    have hfxr : f x ⤳ f r := by rw [← hr', hr'e, ← hxy]
    have hxr : x ⤳ r := MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hxf hrVf hfxr
    have hre : r = x := (hrx.antisymm hxr).eq
    intro z hz
    have hz' : z ∈ closure R := subset_closure hz
    rwa [← hr.def, hre] at hz'
  · rw [closure_image_closure_singleton f.continuous, ← hx'.def,
      closure_image_closure_singleton fp.continuous, hxy]

end Flip

/-! ### Counting strata -/

section Count

open MMP.Fourfold

variable {k : Type} [Field k]

/-- On a Noetherian integral normal scheme, a `ℚ`-divisor has finitely many boundary strata. -/
private theorem finite_setOf_isDltStratum {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of k))
    (B : QDivisor X) : {T : Set X | IsDltStratum sX B T}.Finite := by
  classical
  haveI : IsNoetherian X := {}
  have key : ∀ J : Finset (MMP.Mori.PrimeDivisor X), {T : Set X | Maximal
      (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ P ∈ J, (P.support : Set X)) T}.Finite := by
    intro J
    have hC : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
      isClosed_biInter fun P _ => P.idealSheaf.support.isClosed
    obtain ⟨S, hS, hCS⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨_, hC⟩
    refine ((S.image fun Z : Closeds X => (Z : Set X)).finite_toSet).subset ?_
    intro T hT
    obtain ⟨⟨hTirr, hTsub⟩, hTmax⟩ := hT
    have hcov : T ⊆ ⋃₀ ↑(S.image fun Z : Closeds X => (Z : Set X)) := by
      intro t ht
      have h1 : t ∈ ((S.sup id : Closeds X) : Set X) := by
        rw [← hCS]; exact hTsub ht
      rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at h1
      simp only [Set.mem_iUnion, Function.comp_apply, id] at h1
      obtain ⟨Z, hZ, htZ⟩ := h1
      exact ⟨Z, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hZ), htZ⟩
    obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hTirr) _ (by
      intro z hz
      obtain ⟨Z, -, rfl⟩ := Finset.mem_image.mp hz
      exact Z.isClosed) hcov
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hz
    have hZC : (Z : Set X) ⊆ ⋂ P ∈ J, (P.support : Set X) := by
      have : (Z : Set X) ⊆ ((S.sup id : Closeds X) : Set X) := by
        rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
        exact Set.subset_biUnion_of_mem (u := fun Z : Closeds X => (SetLike.coe ∘ id) Z) hZ
      rw [← hCS] at this
      exact this
    have hTZ : T = Z := Set.Subset.antisymm hTz (hTmax ⟨hS ⟨Z, hZ⟩, hZC⟩ hTz)
    rw [hTZ]
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hZ)
  refine ((B.support.powerset.finite_toSet).biUnion fun J _ => key J).subset ?_
  rintro T ⟨-, J, -, hJ1, -, hmax⟩
  refine Set.mem_biUnion (x := J) ?_ hmax
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro P hP
  rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
  exact ne_of_gt (lt_of_lt_of_le one_pos (hJ1 P hP))

end Count

/-! ### Strata across one flip -/

section OneFlip

open MMP.Fourfold

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- **Counting strata across one flip.** Let `f⁺ : X⁺ ⟶ Z` be a `(K + B)`-flip of `f : X ⟶ Z`
with `(X, B)` dlt. The strata of `(X⁺, B⁺)` inject into the strata of `(X, B)` not contained in
`Ex(f)`, compatibly with their images in `Z`. Hence there are at most as many strata on `X⁺` as on
`X`, and if there are as many, no stratum of either pair lies in the exceptional locus and every
stratum of `(X, B)` has a birational transform on `X⁺`. -/
private theorem ncard_isDltStratum_flipTransform_le {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hB : MMP.Intersection.IsDltPair sX B) :
    {T' | IsDltStratum sX' (flipTransform f fp B) T'}.ncard ≤ {T | IsDltStratum sX B T}.ncard ∧
      ({T' | IsDltStratum sX' (flipTransform f fp B) T'}.ncard =
          {T | IsDltStratum sX B T}.ncard →
        (∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X)) ∧
        (∀ T' : Set X', IsDltStratum sX' (flipTransform f fp B) T' →
          ¬ T' ⊆ (exceptionalSet fp : Set X')) ∧
        (∀ T : Set X, IsDltStratum sX B T →
          ∃ T' : Set X', IsDltStratum sX' (flipTransform f fp B) T' ∧
            closure (f.base '' T) = closure (fp.base '' T'))) := by
  classical
  set St := {T : Set X | IsDltStratum sX B T}
  set St' := {T' : Set X' | IsDltStratum sX' (flipTransform f fp B) T'}
  set Bad := {T : Set X | IsDltStratum sX B T ∧ T ⊆ (exceptionalSet f : Set X)}
  have hfin : St.Finite := finite_setOf_isDltStratum sX B
  have h1 := (isDltPair_and_map_mem_biregularLocus hK hflip hB).2
  have h2 : ∀ T' ∈ St', ∃ S ∈ St, S ∉ Bad ∧
      closure (f.base '' S) = closure (fp.base '' T') := fun T' hT' => by
    obtain ⟨x', hx', hxf, hxfp⟩ := h1 T' hT'
    obtain ⟨S, hS, hSex, hScl⟩ :=
      exists_isDltStratum_of_mem_biregularLocus hK hflip hB hT' hx' hxf hxfp
    exact ⟨S, hS, fun h => hSex h.2, hScl⟩
  choose! g hgS hgB hgcl using h2
  have hinj : Set.InjOn g St' := by
    intro T₁ h₁ T₂ h₂ he
    obtain ⟨x₁, hx₁, -, hV₁⟩ := h1 T₁ h₁
    obtain ⟨x₂, hx₂, -, hV₂⟩ := h1 T₂ h₂
    exact eq_of_closure_image_eq fp hx₁ hx₂ hV₁ hV₂ ((hgcl T₁ h₁).symm.trans (he ▸ hgcl T₂ h₂))
  have hsub : Bad ⊆ St := fun T hT => hT.1
  have hle : St'.ncard ≤ (St \ Bad).ncard :=
    Set.ncard_le_ncard_of_injOn g (fun T hT => ⟨hgS T hT, hgB T hT⟩) hinj hfin.diff
  have hsum : (St \ Bad).ncard + Bad.ncard = St.ncard :=
    Set.ncard_diff_add_ncard_of_subset hsub hfin
  refine ⟨by omega, fun heq => ⟨fun T hT hTex => ?_, fun T' hT' hT'ex => ?_, fun S hS => ?_⟩⟩
  · have hBad : Bad = ∅ := (Set.ncard_eq_zero (hfin.subset hsub)).mp (by omega)
    exact hBad.subset ⟨hT, hTex⟩
  · obtain ⟨x', hx', -, hV⟩ := h1 T' hT'
    exact (mem_exceptionalSet.mp (hT'ex hx'.mem)) hV
  · have himg : g '' St' = St := by
      refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hgS) ?_ hfin
      rw [hinj.ncard_image]
      omega
    obtain ⟨T', hT', rfl⟩ : S ∈ g '' St' := himg ▸ hS
    exact ⟨T', hT', hgcl T' hT'⟩

end OneFlip

end MMP.Fold06.LemMmpStrataEventuallyBirational

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Only finitely many boundary strata are lost in a sequence of flips.** Let `L ∈ ℕ ∪ {∞}` and,
for `i + 1 < L`, let `fp i : X (i + 1) ⟶ Z i` be a `(K_i + B_i)`-flip (`MMP.Fourfold.IsFlipOf`) of
`f i : X i ⟶ Z i`, with `K i` a canonical divisor of `X i` and
`B (i + 1) = (fp i)⁻¹_* (f i)_* (B i)`. If `X 0` is projective and `(X 0, B 0)` is dlt, then there
is `N` such that for every `i ≥ N` with `i + 1 < L`: no boundary stratum of `(X i, B i)` is
contained in `Ex(f i)`, no boundary stratum of `(X (i + 1), B (i + 1))` is contained in
`Ex(fp i)`, and every boundary stratum `T` of `(X i, B i)` has as birational transform a boundary
stratum `T'` of `(X (i + 1), B (i + 1))`, with `closure (f i '' T) = closure (fp i '' T')`. -/
@[mmp "lem_mmp_strata_eventually_birational"]
public theorem exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    [∀ i, CompactSpace (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
    {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
    {n : ℕ} {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)} {L : ℕ∞}
    (hX : Mori.IsProjectiveVariety k (sX 0))
    (hB0 : MMP.Intersection.IsDltPair (sX 0) (B 0))
    (hK : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < L → (K i).IsCanonicalDivisor (sX i) n)
    (hflip : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < L →
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hB : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < L → B (i + 1) = flipTransform (f i) (fp i) (B i)) :
    ∃ N : ℕ, ∀ i ≥ N, ((i + 1 : ℕ) : ℕ∞) < L →
      (∀ T : Set (X i), IsDltStratum (sX i) (B i) T →
        ¬ T ⊆ (exceptionalSet (f i) : Set (X i))) ∧
      (∀ T' : Set (X (i + 1)), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
        ¬ T' ⊆ (exceptionalSet (fp i) : Set (X (i + 1)))) ∧
      (∀ T : Set (X i), IsDltStratum (sX i) (B i) T →
        ∃ T' : Set (X (i + 1)), IsDltStratum (sX (i + 1)) (B (i + 1)) T' ∧
          closure ((f i).base '' T) = closure ((fp i).base '' T')) := by
  classical
  have hle : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < L → ((i : ℕ) : ℕ∞) < L := fun i hi =>
    lt_of_le_of_lt (by exact_mod_cast Nat.le_succ i) hi
  have hdlt : ∀ i : ℕ, (i = 0 ∨ ((i : ℕ) : ℕ∞) < L) →
      MMP.Intersection.IsDltPair (sX i) (B i) := by
    intro i
    induction i with
    | zero => exact fun _ => hB0
    | succ i ih =>
      intro hi
      have hi' : ((i + 1 : ℕ) : ℕ∞) < L := hi.resolve_left (Nat.succ_ne_zero i)
      rw [hB i hi']
      exact (MMP.Fold06.LemMmpStrataEventuallyBirational.isDltPair_and_map_mem_biregularLocus
        (hK i hi') (hflip i hi') (ih (Or.inr (hle i hi')))).1
  have key := fun i (hi : ((i + 1 : ℕ) : ℕ∞) < L) =>
    hB i hi ▸ MMP.Fold06.LemMmpStrataEventuallyBirational.ncard_isDltStratum_flipTransform_le
      (hK i hi) (hflip i hi) (hdlt i (Or.inr (hle i hi)))
  by_cases hL : L = ⊤
  · subst hL
    set c : ℕ → ℕ := fun i => {T | IsDltStratum (sX i) (B i) T}.ncard
    have hanti : Antitone c :=
      antitone_nat_of_succ_le fun i => (key i (WithTop.coe_lt_top _)).1
    refine ⟨Function.argmin c, fun i hi _ => (key i (WithTop.coe_lt_top _)).2 ?_⟩
    change c (i + 1) = c i
    rw [le_antisymm (hanti hi) (Function.argmin_le c i),
      le_antisymm (hanti (hi.trans (Nat.le_succ i))) (Function.argmin_le c (i + 1))]
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hL
    refine ⟨m, fun i hi hi' => absurd hi' ?_⟩
    have : ¬ (i + 1 < m) := by omega
    exact_mod_cast this

end MMP.Fourfold
