module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Basic
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Resolution.Blowup
import MMP.AlgebraicGeometry.MMP.Threefold.Basic
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Resolution.Principalization
import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisor
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisorSupport
import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective

/-!
# Smooth blow-ups extracting valuations, and projective birational maps onto smooth varieties

Two results on blow-ups over a smooth variety `V` over a field `k` of characteristic zero.

* Let `D ⊆ V` be a divisor with simple normal crossings and `v = ord_E` a divisorial valuation of
  `k(V)` with a centre on `V`. On an open neighbourhood `U` of (the generic point of) the centre
  there is a smooth blow-up sequence `U_r → ⋯ → U_0 = U` whose centres have simple normal
  crossings with the successive total transforms of `D ∩ U`, with a prime divisor `E'` on `U_r`
  such that `ord_{E'} = v`. One represents `v` on a projective birational model of an affine
  neighbourhood of the centre, dominated by the blow-up of a coherent ideal `I`; the canonical
  principalization of `I` with initial boundary `D` factors through the model, and the strict
  transform of the representing prime divisor represents `v`.
* Let `V = Y` be quasi-projective and `r : Z ⟶ Y` a projective birational morphism with `Z`
  integral. Then `Z ≅ Bl_I Y` over `Y` for an ideal sheaf `I` trivial in codimension one; `r`
  carries an effective Cartier divisor `A` supported exactly on the exceptional set with `-A`
  relatively ample; and a blow-up sequence of `Y` with smooth centres dominates `r`. Writing
  `Z ⊆ ℙⁿ_Y`, the homogeneous coordinates of its generic point are rescaled locally (the local
  rings of `Y` are factorial) to families without common divisor, which generate `I`; over an
  affine open the closures of the generic point in `Proj` agree, so `Z ≅ Bl_I Y`. The
  exceptional divisor of the blow-up is `A`, and a principalization of `I` dominates `r`.

## Main results

* `MMP.Resolution.exists_closedBlowupSequence_valuation_eq`: the extraction of a divisorial
  valuation by smooth blow-ups with snc centres.
* `MMP.Resolution.exists_iso_blowUp_of_isSmoothScheme`: a projective birational morphism onto a
  smooth quasi-projective variety is an ideal blow-up, with exceptional Cartier divisor and a
  dominating smooth blow-up sequence.

## Implementation notes

* Blow-up sequences are `MMP.Resolution.ClosedBlowupSequence`s, smooth
  (`MMP.Resolution.ClosedBlowupSequence.IsSmooth`) with centres having simple normal crossings
  with the total transforms of the boundary
  (`MMP.Resolution.ClosedBlowupSequence.CentersHaveSNCWith`). The divisor extracted over `V` is
  `(U_r, Π ≫ U.ι, E')` as a `MMP.Mori.DivisorOver`, and the representation of `v` is equality of
  valuations of `k(V)`.
* The blow-up is StacksDraft's `AlgebraicGeometry.blowUp I` with `AlgebraicGeometry.blowUpToBase`;
  an ideal sheaf is a `Scheme.IdealSheafData`. "Unit ideal in codimension one" says that every
  point of the cosupport `I.support` has local ring of dimension at least two. Cartier divisors
  are `Scheme.CartierDivisor`s; "exceptional" is the equality of the support of `A`
  with `MMP.Mori.exceptionalSet r`. The dominating sequence has birational composite, which
  excludes degenerate sequences (such as one blowing up the zero ideal, with empty target).
* The source works over `ℂ`; the statements are made over any field of characteristic zero,
  where canonical principalization is available.

## References

* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], 3.24–3.29, §3.3
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 1.6.2
* [R. Hartshorne, *Algebraic geometry*, II.7.17]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Proof_lem_mmp_snc_valuation_extraction

open MMP.Mori MMP.Flips MMP.Resolution TopologicalSpace

/-! ### Valuations along proper birational morphisms -/

/-- An irreducible space has finitely many irreducible components. -/
private theorem finite_irreducibleComponents (T : Type*) [TopologicalSpace T]
    [IrreducibleSpace T] : Finite (irreducibleComponents T) := by
  rw [irreducibleComponents_eq_singleton]; infer_instance

/-- Pulling back rational functions along a composite of dominant morphisms of integral schemes
is the composite of the pull-backs. -/
private theorem functionFieldMap_comp_apply' {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b]
    (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap (a ≫ b) t := by
  have := Scheme.Hom.stalkMapOfEq_comp a b (genericPoint A) (genericPoint B) (genericPoint C)
    (map_genericPoint_of_isDominant a) (map_genericPoint_of_isDominant b)
    (map_genericPoint_of_isDominant (a ≫ b))
  exact (congrArg (fun φ => φ.hom t) this).symm

/-- If `G ≫ f` is dominant and `f` is birational between integral schemes, then `G` is
dominant. -/
private theorem isDominant_of_isDominant_comp_of_isBirational {T Y X : Scheme.{u}} [IsIntegral T]
    [IsIntegral Y] [IsIntegral X] (G : T ⟶ Y) (f : Y ⟶ X) [IsSeparated f] [LocallyOfFiniteType f]
    [IsDominant (G ≫ f)] (hf : IsBirational f) : IsDominant G := by
  haveI := IsDominant.of_comp G f
  have := finite_irreducibleComponents Y
  have := finite_irreducibleComponents X
  obtain ⟨W, hWd, hWiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational f hf
    (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have hgW : genericPoint X ∈ (W : Set X) :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).2 (by simpa using hWd.nonempty)
  have h1 : f (G (genericPoint T)) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply]; exact map_genericPoint_of_isDominant (G ≫ f)
  have h2 : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hG : G (genericPoint T) = genericPoint Y := by
    have hinj := (f ∣_ W).isOpenEmbedding.injective
    have ha : G (genericPoint T) ∈ f ⁻¹ᵁ W := by simpa [h1] using hgW
    have hb : genericPoint Y ∈ f ⁻¹ᵁ W := by simpa [h2] using hgW
    exact congrArg Subtype.val (@hinj ⟨_, ha⟩ ⟨_, hb⟩ (Subtype.ext
      ((morphismRestrict_base_coe f W _).trans
        (h1.trans (h2.symm.trans (morphismRestrict_base_coe f W ⟨_, hb⟩).symm)))))
  refine ⟨dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)⟩
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint T, hG⟩)

/-- Let `f : Y ⟶ X` be a proper birational morphism and `φ : T ⟶ X` a proper birational
morphism factoring as `φ = G ≫ f`, with `T` and `Y` normal integral locally Noetherian. For every
prime divisor `E` of `Y` there is a prime divisor `E'` of `T` with `ord_{E'} = ord_E` as
valuations of `k(X)`. -/
private theorem exists_primeDivisor_valuationOver_eq {T Y X : Scheme.{u}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X]
    (G : T ⟶ Y) (f : Y ⟶ X) [IsProper f] [IsDominant f] (hf : IsBirational f)
    {φ : T ⟶ X} [IsProper φ] [IsDominant φ] (hφb : IsBirationalMorphism φ) (hφ : G ≫ f = φ)
    (E : MMP.Mori.PrimeDivisor Y) :
    ∃ E' : MMP.Mori.PrimeDivisor T, E'.valuationOver φ = E.valuationOver f := by
  subst hφ
  haveI : IsProper G := IsProper.of_comp G f
  haveI : IsDominant G := isDominant_of_isDominant_comp_of_isBirational G f hf
  have hG : Function.Bijective (functionFieldMap G) := by
    refine ⟨(functionFieldMap G).injective, fun t => ?_⟩
    obtain ⟨s, rfl⟩ := hφb.functionFieldMap_bijective.2 t
    exact ⟨functionFieldMap f s, functionFieldMap_comp_apply' G f s⟩
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing G hG E.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (G.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      E.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E' : MMP.Mori.PrimeDivisor T := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E'.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  have heq : G E'.genericPoint = E.genericPoint := hE ▸ hx
  haveI : IsIso (G.stalkMap E'.genericPoint) := hE ▸ hiso
  have key : E'.valuationOver G = E.divisorialValuation := by
    refine Valuation.ext fun t => ?_
    rw [MMP.Mori.PrimeDivisor.valuationOver_apply]
    by_cases ht : t = 0
    · rw [ht, map_zero, map_zero, map_zero]
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
      MMP.Positivity.ord_functionFieldMap_of_isIso G E' E heq t]
  refine ⟨E', Valuation.ext fun t => ?_⟩
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
    ← functionFieldMap_comp_apply' G f t, ← MMP.Mori.PrimeDivisor.valuationOver_apply, key]

/-! ### A dominating blow-up -/

/-- A proper birational morphism `f : Y ⟶ V` onto a Noetherian integral scheme is dominated by
the blow-up of `V` along an ideal sheaf which does not vanish at the generic point of `V`
([Stacks, Tag 081T]). -/
private theorem exists_blowUp_dominating {Y V : Scheme.{u}} [IsIntegral Y] [IsIntegral V]
    [IsNoetherian V] (f : Y ⟶ V) [IsProper f] (hf : IsBirational f) :
    ∃ (M : V.IdealSheafData) (g : blowUp M ⟶ Y),
      genericPoint V ∉ (M.support : Set V) ∧ g ≫ f = blowUpToBase M := by
  have := finite_irreducibleComponents Y
  have := finite_irreducibleComponents V
  obtain ⟨W, hWd, hWiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational f hf
    (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have hWc : IsCompact (W : Set V) := NoetherianSpace.isCompact _
  obtain ⟨S', b, hb, g, hg⟩ := exists_isAdmissibleBlowup_dominating_of_isCompact f W hWc
    (strictTransformOpenImmersion_of_isIso_morphismRestrict f W hWc)
  obtain ⟨M, -, hMdisj, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff W b).1 hb
  refine ⟨M, e.inv ≫ g, fun hM => ?_, ?_⟩
  · have hgW : genericPoint V ∈ (W : Set V) :=
      ((genericPoint_spec V).mem_open_set_iff W.isOpen).2 (by simpa using hWd.nonempty)
    exact Set.disjoint_left.mp hMdisj hgW hM
  · rw [Category.assoc, hg, ← he, Iso.inv_hom_id_assoc]

/-! ### The boundary as an ordered divisor -/

/-- The support of the inverse image of an ordered divisor is the inverse image of its
support. -/
private theorem support_comap_orderedDivisor {X Y : Scheme.{u}} (E : OrderedDivisor X)
    (h : Y ⟶ X) : (E.comap h).support = h ⁻¹' E.support := by
  simp [OrderedDivisor.support, OrderedDivisor.comap, Scheme.IdealSheafData.support_comap,
    Set.preimage_iUnion]

/-- A divisor with simple normal crossings on a smooth Noetherian scheme over a perfect field is
the support of an ordered snc divisor, its irreducible components in some order. -/
private theorem exists_orderedDivisor_support_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsNoetherian X]
    (hX : IsSmoothScheme sX) {D : Set X} (hD : IsSNCClosedSubset sX D) :
    ∃ E : OrderedDivisor X, E.support = D ∧ E.IsOrderedSNC sX := by
  obtain ⟨hDc, hD0 | ⟨-, hfin, hfam⟩⟩ := hD
  · refine ⟨OrderedDivisor.empty X, ?_, ?_⟩
    · simp [OrderedDivisor.support, OrderedDivisor.empty, hD0]
    · haveI : LocallyOfFinitePresentation sX :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
      haveI : Smooth sX := (isSmoothScheme_iff _).1 hX
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
      haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
        (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp
          inferInstance x
      obtain ⟨n, z, hz⟩ := exists_isRegularSystemOfParameters (X.presheaf.stalk x)
      exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩
  · haveI : Finite (componentsOf D) := hfin.to_subtype
    let e := (Finite.equivFin (componentsOf D)).symm
    refine ⟨⟨_, fun i => componentsFamily D (e i)⟩, ?_, ?_⟩
    · change ⋃ i, ((componentsFamily D (e i)).support : Set X) = D
      rw [e.surjective.iUnion_comp (fun V => ((componentsFamily D V).support : Set X))]
      exact iUnion_support_componentsFamily hDc
    · exact isOrderedSNC_of_exists_rep hfam _ fun y => ⟨e, e.injective, fun i hi => ⟨hi, rfl⟩⟩

/-! ### Smooth blow-up sequences over a variety -/

/-- The identity is birational. -/
private theorem isBirational_id {X : Scheme.{u}} : IsBirational (𝟙 X) := by
  refine ⟨Set.bijOn_id _, fun x _ => ?_⟩
  rw [Scheme.Hom.stalkMap_id]
  exact IsIso.id _

/-- The end of a smooth blow-up sequence over a smooth variety `Y → X`, whose centres lie over a
closed subset `S ⊆ X` missing the generic point, is a smooth variety, proper and birational
over `X`. -/
private theorem toBase_props {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) (S : Set X) (hS : genericPoint X ∉ S) :
    ∀ {Y : Scheme.{u}} (B : ClosedBlowupSequence Y) (f : Y ⟶ X),
      AlgebraicGeometry.IsVariety k (f ≫ sX) → IsBirational f → IsSmoothScheme (f ≫ sX) →
      IsProper f → B.IsSmooth (f ≫ sX) → B.CentersLieOver f S →
      AlgebraicGeometry.IsVariety k (B.toBase ≫ f ≫ sX) ∧ IsBirational (B.toBase ≫ f) ∧
        IsSmoothScheme (B.toBase ≫ f ≫ sX) ∧ IsProper (B.toBase ≫ f)
  | _, .nil _, f, hv, hb, hs, hp, _, _ => by
    simpa [ClosedBlowupSequence.toBase] using ⟨hv, hb, hs, hp⟩
  | Y, .cons Z B, f, hv, hb, hs, hp, ⟨_, hZsm, hBsm⟩, ⟨hZS, hBS⟩ => by
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      have : IsIntegral Y := hv.toIsIntegral
      obtain ⟨y, -, hy⟩ := hb.1.surjOn (show genericPoint X ∈ genericPoints X by
        rw [genericPoints_eq_singleton]; rfl)
      exact hS (hZS ⟨y, by simp [Scheme.IdealSheafData.support_bot], hy⟩)
    haveI := hv
    obtain ⟨hv', hproj, hb'⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
        (f ≫ sX) Z hZ
    haveI : IsProper (blowUpToBase Z) := hproj.isProper
    haveI := hp
    rw [show (ClosedBlowupSequence.cons Z B).toBase ≫ f ≫ sX =
        B.toBase ≫ blowUpToBase Z ≫ f ≫ sX from Category.assoc _ _ _,
      show (ClosedBlowupSequence.cons Z B).toBase ≫ f =
        B.toBase ≫ blowUpToBase Z ≫ f from Category.assoc _ _ _]
    exact toBase_props sX S hS B (blowUpToBase Z ≫ f) (by rwa [Category.assoc])
      (hb'.comp hb) (by
        rw [Category.assoc]
        haveI := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (f ≫ sX) Z
          ⟨hs, hZsm⟩).1
        exact MMP.Resolution.isSmoothScheme_of_smooth _)
      inferInstance (by rwa [Category.assoc]) hBS

end Proof_lem_mmp_snc_valuation_extraction

namespace MMP.Resolution

open MMP.Mori MMP.Flips TopologicalSpace
open Proof_lem_mmp_snc_valuation_extraction

/-- **Extraction of a divisorial valuation by smooth blow-ups with snc centres.** Let `V` be a
smooth variety over a field `k` of characteristic zero, `D ⊆ V` a divisor with simple normal
crossings and `F = (Y, f, E)` a divisor over `V` (with `f` proper). Then there are an open
`U ⊆ V` meeting the centre of `F` and a smooth blow-up sequence `B` of `U` whose centres have
simple normal crossings with the successive total transforms of `U ∩ D`, such that the last
scheme of `B` is a normal variety, birational over `V`, carrying a prime divisor `E'` with
`ord_{E'} = ord_E` as valuations of `k(V)`. -/
@[mmp "lem_mmp_snc_valuation_extraction"]
public theorem exists_closedBlowupSequence_valuation_eq {k : Type u} [Field k] [CharZero k]
    {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sV]
    (hV : IsSmoothScheme sV) {D : Set V} (hD : IsSNCClosedSubset sV D)
    (F : ProperDivisorOver k sV) :
    ∃ (U : V.Opens) (B : ClosedBlowupSequence U),
      ((F.center : Set V) ∩ U).Nonempty ∧ B.IsSmooth (U.ι ≫ sV) ∧
        B.CentersHaveSNCWith (U.ι ≫ sV) (U.ι ⁻¹' D) ∧
        ∃ (hN : IsNormalVariety k ((B.toBase ≫ U.ι) ≫ sV))
          (hb : IsBirationalMorphism (B.toBase ≫ U.ι)) (E : Mori.PrimeDivisor B.target),
          (⟨B.target, B.toBase ≫ U.ι, hN, hb, E⟩ : DivisorOver k sV).valuation =
            F.valuation := by
  haveI : IsIntegral V := AlgebraicGeometry.IsVariety.toIsIntegral (f := sV)
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsNoetherian V := {}
  haveI : IsNormal V :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hV).2
  haveI := F.isIntegral
  haveI := F.isNormal
  haveI := F.isLocallyNoetherian
  haveI := F.isDominant
  haveI := F.isProper
  have hFb : IsBirational F.f := Bridges.isBirational_of_isBirationalMorphism F.isBirationalMorphism
  -- a blow-up of `V` dominating the model `Y`
  obtain ⟨M, g, hMgen, hg⟩ := exists_blowUp_dominating F.f hFb
  -- the boundary as an ordered snc divisor
  obtain ⟨E0, hE0supp, hE0⟩ := exists_orderedDivisor_support_eq sV hV hD
  -- the open set `U = V`
  let U : V.Opens := ⊤
  haveI : IsIso U.ι := by
    show IsIso (⊤ : V.Opens).ι
    rw [← Scheme.topIso_hom]; infer_instance
  haveI : Nonempty U := ⟨⟨genericPoint V, trivial⟩⟩
  haveI : IsDominant U.ι := Opens.isDominant_ι (by simp [U])
  let t0 : FieldBlowupTriple.{u} := ⟨⟨V, M, E0⟩, k, sV⟩
  have ht0 : t0 ∈ sncTriples := by
    refine ⟨inferInstance, hV, inferInstance, inferInstance, fun η hη => ?_, hE0.1, hE0.2⟩
    have hgen : IsGenericPoint η (⊤ : Set V) :=
      hη.eq_of_le (IrreducibleSpace.isIrreducible_univ V) (Set.subset_univ _)
    change IdealSheafData.stalk M η ≠ ⊥
    rw [hgen.eq (genericPoint_spec V),
      (Stacks.Divisors.stalk_eq_top_iff_notMem_support M _).2 hMgen]
    exact top_ne_bot
  have ht1 : t0.pullback U.ι ∈ sncTriples := pullback_mem_sncTriples ht0 U.ι
  have ht : t0.pullback U.ι ∈ triples :=
    mem_triples_iff.2 ⟨ht1, (.of_preirreducibleSpace _ : TopologicalSpace.Equidimensional U)⟩
  obtain ⟨-, hprop1, hprop2, hprop3, -⟩ :=
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, u, u}
  let B : ClosedBlowupSequence U := canonicalPrincipalization _ (triples_subset_sncTriples ht)
  -- the centres miss the generic point of `U`
  have hS : genericPoint U ∉ ((M.comap U.ι).support : Set U) ∪ (E0.comap U.ι).doubleLocus := by
    rintro (h | ⟨i, j, -, hi, -⟩)
    · rw [Scheme.IdealSheafData.support_comap] at h
      change U.ι (genericPoint U) ∈ (M.support : Set V) at h
      rw [map_genericPoint_of_isDominant U.ι] at h
      exact hMgen h
    · have hη : closure {genericPoint U} ∈ irreducibleComponents U := by
        rw [(genericPoint_spec U).def, irreducibleComponents_eq_singleton]; rfl
      exact ht1.2.2.2.2.2.2.notMem_support_of_mem_irreducibleComponents hη i hi
  obtain ⟨hv, hb, hs, hp⟩ := toBase_props (U.ι ≫ sV) _ hS B (𝟙 U.toScheme)
    (by rw [Category.id_comp]; exact ⟨⟩) isBirational_id (by rw [Category.id_comp]; exact ht1.2.1)
    inferInstance (by rw [Category.id_comp]; exact (hprop1 _ ht).1) (hprop3 _ ht)
  simp only [Category.comp_id, Category.id_comp] at hv hb hs hp
  rw [← Category.assoc] at hv hs
  haveI := hv
  haveI : IsIntegral B.target := hv.toIsIntegral
  haveI := hp
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hs
  have hbB : IsBirationalMorphism (B.toBase ≫ U.ι) := isBirationalMorphism_comp_of_isBirational
    U.ι B.toBase (Bridges.isBirational_of_isBirationalMorphism (isBirationalMorphism_of_isIso _)) hb
  haveI := hbB.isDominant
  -- the total transform of `M` is invertible
  have hcart : Stacks.Blowup.IsCartierOver M (Over.mk (B.toBase ≫ U.ι)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (M.comap (B.toBase ≫ U.ι))
    rw [Scheme.IdealSheafData.comap_comp]
    exact (exists_divisorWithCoeffs_of_isMonomialIdeal ((B.toBase ≫ U.ι) ≫ sV) hs _
      (hprop2 _ ht)).choose_spec.2.1
  -- hence `B.target → U` factors through `blowUp M → Y`
  obtain ⟨E', hE'⟩ := exists_primeDivisor_valuationOver_eq (blowUpLift M _ hcart ≫ g) F.f hFb hbB
    (by simp only [Category.assoc, hg, blowUpLift_comp]) F.E
  refine ⟨U, B, ?_, (hprop1 _ ht).1, ?_, ⟨hv, inferInstance⟩, hbB, E', hE'⟩
  · refine ⟨F.f F.E.genericPoint, ⟨F.E.genericPoint, ?_, rfl⟩, trivial⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure F.E]
    exact subset_closure rfl
  · have := (hprop1 _ ht).2
    rwa [show (t0.pullback U.ι).E.support = U.ι ⁻¹' D from
      (support_comap_orderedDivisor E0 U.ι).trans (by rw [hE0supp])] at this

end MMP.Resolution

section ConductorBlowup

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_mmp_conductor_smooth_target_blowup

open MMP.Resolution Limits Stacks.AlgebraicGeometry.ProjPolyChart Stacks.ProjectiveSpaceChartRatio

/-- A blow-up sequence truncated at its length is itself. -/
private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

/-! ### Ideals without a common divisor -/

section DivisorFree

variable {R : Type*} [CommRing R]

/-- An ideal `J` of `R` has *no common divisor* if it is nonzero and `s ∣ x * j` for every
`j ∈ J` forces `s ∣ x`. -/
private def IsDivisorFree (J : Ideal R) : Prop :=
  J ≠ ⊥ ∧ ∀ x s : R, (∀ j ∈ J, s ∣ x * j) → s ∣ x

/-- A principal ideal without common divisor is the unit ideal. -/
private theorem IsDivisorFree.eq_top_of_isPrincipal {J : Ideal R} (hJ : IsDivisorFree J)
    (hp : J.IsPrincipal) : J = ⊤ := by
  obtain ⟨g, rfl⟩ := hp
  have : g ∣ 1 := hJ.2 1 g fun j hj => by
    rw [one_mul]; exact Ideal.mem_span_singleton.1 (by simpa using hj)
  exact Ideal.span_singleton_eq_top.2 (isUnit_of_dvd_one this)

/-- In a factorial local ring, a proper ideal without common divisor forces dimension at least
two. -/
private theorem IsDivisorFree.two_le_ringKrullDim [IsLocalRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {J : Ideal R} (hJ : IsDivisorFree J) (hJm : J ≠ ⊤) :
    2 ≤ ringKrullDim R := by
  obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ.1
  have hau : ¬ IsUnit a := fun hu => hJm (Ideal.eq_top_of_isUnit_mem _ haJ hu)
  obtain ⟨p, hp, -⟩ := WfDvdMonoid.exists_irreducible_factor hau ha0
  have hpp : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.1 hp
  -- some element `b` of `J` is not divisible by the prime `p`
  have hnot : ¬ ∀ j ∈ J, p ∣ 1 * j := fun h => hpp.not_unit (isUnit_of_dvd_one (hJ.2 1 p h))
  push Not at hnot
  obtain ⟨b, hbJ, hpb⟩ := hnot
  rw [one_mul] at hpb
  have hspan : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).2 hpp
  have h1 : (⊥ : Ideal R) < Ideal.span {p} := bot_lt_iff_ne_bot.2 (by simpa using hpp.ne_zero)
  have h2 : Ideal.span {p} < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hspan.ne_top) fun h => hpb ?_
    rw [← Ideal.mem_span_singleton, h]; exact IsLocalRing.le_maximalIdeal hJm hbJ
  let P0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let P1 : PrimeSpectrum R := ⟨_, hspan⟩
  let P2 : PrimeSpectrum R := ⟨_, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R := by
    refine Order.le_krullDim_iff.2 ⟨RelSeries.fromListIsChain [P0, P1, P2] (by simp) ?_, rfl⟩
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨h1, h2⟩
  exact_mod_cast this

end DivisorFree

/-! ### Colon ideals -/

section Colon

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {ι : Type*} (f : ι → K)

private def colonSet : Set K := {c | ∀ k, c * f k ∈ (algebraMap R K).range}

private def colonSubmodule : Submodule R K :=
  Submodule.span R {x | ∃ c ∈ colonSet R f, ∃ k, x = c * f k}

private def colonIdeal : Ideal R := (colonSubmodule R f).comap (Algebra.linearMap R K)

variable {R f}

private theorem mem_colonIdeal {a : R} :
    a ∈ colonIdeal R f ↔ algebraMap R K a ∈ colonSubmodule R f := Iff.rfl

private theorem colonSubmodule_le_range :
    colonSubmodule R f ≤ LinearMap.range (Algebra.linearMap R K) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨c, hc, k, rfl⟩
  obtain ⟨a, ha⟩ := hc k
  exact ⟨a, ha⟩

private theorem exists_colonIdeal_eq_span [IsDomain R] [UniqueFactorizationMonoid R]
    [IsFractionRing R K] [Fintype ι] (hf : ∃ k, f k ≠ 0) :
    ∃ (d : K) (b : ι → R), d ≠ 0 ∧ (∀ k, algebraMap R K (b k) = d * f k) ∧
      (∀ x s : R, (∀ k, s ∣ x * b k) → s ∣ x) ∧ colonIdeal R f = Ideal.span (Set.range b) := by
  classical
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid R
  obtain ⟨k₀, hk₀⟩ := hf
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.univ.image f)
  choose p hp using fun k => hq (f k) (Finset.mem_image_of_mem f (Finset.mem_univ k))
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hq0 : algebraMap R K q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  have hp' : ∀ k, algebraMap R K (p k) = algebraMap R K q * f k := fun k => by
    rw [hp k, Algebra.smul_def]
  obtain ⟨b, hb, hgcd⟩ := Finset.extract_gcd p (Finset.univ_nonempty_iff.2 ⟨k₀⟩)
  set G := Finset.univ.gcd p
  have hG0 : G ≠ 0 := by
    intro h
    rw [Finset.gcd_eq_zero_iff] at h
    have := hp' k₀
    rw [h k₀ (Finset.mem_univ _), map_zero] at this
    exact mul_ne_zero hq0 hk₀ this.symm
  have hGK : algebraMap R K G ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ hinj]
  set d : K := algebraMap R K q / algebraMap R K G
  have hd0 : d ≠ 0 := div_ne_zero hq0 hGK
  have hbd : ∀ k, algebraMap R K (b k) = d * f k := fun k => by
    have h := hp' k
    rw [hb k (Finset.mem_univ _), map_mul] at h
    rwa [show d * f k = (algebraMap R K q * f k) / algebraMap R K G by simp only [d]; ring,
      eq_div_iff hGK, mul_comm]
  have hfree : ∀ x s : R, (∀ k, s ∣ x * b k) → s ∣ x := by
    intro x s h
    have h1 : s ∣ Finset.univ.gcd (fun k => x * b k) := Finset.dvd_gcd fun k _ => h k
    rw [Finset.gcd_mul_left, hgcd, mul_one] at h1
    exact (dvd_normalize_iff).1 h1
  refine ⟨d, b, hd0, hbd, hfree, le_antisymm ?_ ?_⟩
  · -- every multiplier is `d` times an element of `R`
    have hmult : ∀ c ∈ colonSet R f, ∃ w : R, c = d * algebraMap R K w := by
      intro c hc
      obtain ⟨a₁, s₁, hs₁, hu⟩ := IsFractionRing.div_surjective (A := R) (c / d)
      have hs₁K : algebraMap R K s₁ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs₁
      have hc' : c = d * (algebraMap R K a₁ / algebraMap R K s₁) := by rw [hu]; field_simp
      have hdvd : ∀ k, s₁ ∣ a₁ * b k := by
        intro k
        obtain ⟨t, ht⟩ := hc k
        refine ⟨t, hinj ?_⟩
        rw [map_mul, map_mul, ht, hbd, hc']
        field_simp
      obtain ⟨w, hw⟩ := hfree a₁ s₁ hdvd
      refine ⟨w, ?_⟩
      rw [hc', hw, map_mul]
      field_simp
    have hle : colonSubmodule R f ≤
        Submodule.map (Algebra.linearMap R K) (Ideal.span (Set.range b) : Submodule R R) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hc, k, rfl⟩
      obtain ⟨w, rfl⟩ := hmult c hc
      refine ⟨w * b k, Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩), ?_⟩
      simp only [Algebra.linearMap_apply, map_mul, hbd]; ring
    intro a ha
    obtain ⟨a', ha', h⟩ := hle ha
    rwa [hinj h] at ha'
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_colonIdeal, hbd]
    exact Submodule.subset_span ⟨d, fun k' => ⟨b k', hbd k'⟩, k, rfl⟩

private theorem map_colonIdeal [Finite ι] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization M S] [Algebra S K] [IsScalarTower R S K]
    (hS : Function.Injective (algebraMap S K)) :
    (colonIdeal R f).map (algebraMap R S) = colonIdeal S f := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap S K (algebraMap R S a) ∈ colonSubmodule S f
    rw [← IsScalarTower.algebraMap_apply]
    have hle : (colonSubmodule R f).restrictScalars R ≤ (colonSubmodule S f).restrictScalars R := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hc, k, rfl⟩
      refine Submodule.subset_span ⟨c, fun k' => ?_, k, rfl⟩
      obtain ⟨b, hb⟩ := hc k'
      exact ⟨algebraMap R S b, by rw [← hb, ← IsScalarTower.algebraMap_apply]⟩
    exact hle ha
  · intro a ha
    have key : ∀ v ∈ colonSubmodule S f, ∃ m ∈ M, (m : R) • v ∈ colonSubmodule R f := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, k, rfl⟩ := hx
        have : ∀ k', ∃ m ∈ M, ((m : R) • c) * f k' ∈ (algebraMap R K).range := by
          intro k'
          obtain ⟨s, hs⟩ := hc k'
          obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.surj M s
          refine ⟨m, m.2, x, ?_⟩
          rw [smul_mul_assoc, ← hs, Algebra.smul_def, IsScalarTower.algebraMap_apply R S K,
            IsScalarTower.algebraMap_apply R S K, ← map_mul, mul_comm, ← hxm]
        choose m hm hm' using this
        cases nonempty_fintype ι
        refine ⟨∏ k', m k', prod_mem fun k' _ => hm k', Submodule.subset_span
          ⟨(∏ k', m k' : R) • c, fun k' => ?_, k, by rw [smul_mul_assoc]⟩⟩
        obtain ⟨y, hy⟩ := hm' k'
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k'), mul_smul, smul_mul_assoc, ← hy]
        exact ⟨_ * y, by rw [map_mul, Algebra.smul_def]⟩
      | zero => exact ⟨1, one_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨m', hm', hmy⟩ := hy
        refine ⟨m * m', mul_mem hm hm', ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmx
        · rw [mul_smul]; exact Submodule.smul_mem _ _ hmy
      | smul s x _ hx =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨⟨y, m'⟩, hym⟩ := IsLocalization.surj M s
        refine ⟨m' * m, mul_mem m'.2 hm, ?_⟩
        have : ((m' * m : R)) • (s • x) = y • ((m : R) • x) := by
          rw [← algebraMap_smul (A := S) (R := R), smul_smul, ← algebraMap_smul (A := S) (R := R) y,
            ← algebraMap_smul (A := S) (R := R) (m : R), smul_smul]
          congr 1
          simp only at hym
          rw [map_mul]
          linear_combination (algebraMap R S m) * hym
        rw [this]
        exact Submodule.smul_mem _ _ hmx
    obtain ⟨m, hm, hmv⟩ := key _ ha
    obtain ⟨x, hx⟩ := colonSubmodule_le_range hmv
    have hx' : algebraMap R S x = algebraMap R S m * a := by
      apply hS
      rw [← IsScalarTower.algebraMap_apply, map_mul, ← IsScalarTower.algebraMap_apply]
      simpa [Algebra.smul_def] using hx
    have hxI : x ∈ colonIdeal R f := by
      rw [mem_colonIdeal]
      have : algebraMap R K x = (m : R) • algebraMap S K a := by simpa using hx
      rw [this]; exact hmv
    have hu : IsUnit (algebraMap R S m) := IsLocalization.map_units S ⟨m, hm⟩
    have : a = hu.unit⁻¹ * algebraMap R S x := by
      rw [hx', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hxI)

end Colon

/-! ### The colon ideal sheaf -/

section Sheaf

variable {Y : Scheme.{u}} [IsIntegral Y] {ι : Type} [Finite ι] (f : ι → Y.functionField)

open Classical in
/-- The colon ideal sheaf. -/
private noncomputable def colonIdealSheaf : Y.IdealSheafData where
  ideal U := if h : Nonempty U.1 then (haveI := h; colonIdeal Γ(Y, U.1) f) else ⊤
  map_ideal_basicOpen U g := by
    by_cases hU : Nonempty U.1
    · by_cases hg : Nonempty (Y.basicOpen g)
      · have hg' : Nonempty (Y.affineBasicOpen g).1 := hg
        rw [dif_pos hU, dif_pos hg']
        have hloc := U.2.isLocalization_basicOpen g
        refine @map_colonIdeal Γ(Y, U.1) Y.functionField _ _ _ ι f _ (Submonoid.powers g)
          Γ(Y, Y.basicOpen g) _ _ hloc _ ?_ (Y.germToFunctionField_injective _)
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le g)) _ _ a).symm
      · have hbot : Y.basicOpen g = ⊥ := by
          ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hg ⟨⟨x, hx⟩⟩
        haveI : Subsingleton Γ(Y, Y.basicOpen g) := hbot ▸ inferInstance
        exact Subsingleton.elim _ _
    · have : ¬ Nonempty (Y.affineBasicOpen g).1 := fun ⟨x⟩ => hU ⟨⟨x.1, Y.basicOpen_le g x.2⟩⟩
      rw [dif_neg hU, dif_neg this]
      exact Ideal.map_top _

private theorem colonIdealSheaf_ideal (U : Y.affineOpens) [h : Nonempty U.1] :
    (colonIdealSheaf f).ideal U = colonIdeal Γ(Y, U.1) f := by
  classical
  exact dif_pos h

private theorem stalk_colonIdealSheaf (y : Y) :
    IdealSheafData.stalk (colonIdealSheaf f) y = colonIdeal (Y.presheaf.stalk y) f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU, colonIdealSheaf_ideal]
  have hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  letI := Y.presheaf.algebra_section_stalk ⟨y, hyU⟩
  exact @map_colonIdeal Γ(Y, U) Y.functionField _ _ _ ι f _
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (Y.presheaf.stalk y) _ _ hloc _
    (functionField_isScalarTower Y U ⟨y, hyU⟩) (IsFractionRing.injective _ _)

end Sheaf

/-! ### The standard charts of `ℙⁿ_ℤ` -/

attribute [local instance] MvPolynomial.gradedAlgebra

section Charts

variable {n : ℕ}

/-- The integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`. -/
private noncomputable abbrev projZ (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n)

/-- The standard chart `D₊(T_j)`. -/
private noncomputable abbrev chartOpen (n : ℕ) (j : Fin (n + 1)) : (projZ.{u} n).Opens :=
  Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j)

/-- The ratio `T_k / T_j` as a germ at a point of the chart `D₊(T_j)`. -/
private noncomputable def ratio {x : projZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (projZ.{u} n).presheaf.stalk x :=
  (projZ.{u} n).presheaf.germ _ x hx
    (Proj.awayToSection _ _ (coordFracAt (ULift.{u} ℤ) n j k))

private theorem val_stalkIso'_ratio {x : projZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x (ratio hx k)).val =
      Localization.mk (MvPolynomial.X k)
        ⟨MvPolynomial.X j, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hx)⟩ := by
  rw [ratio]
  erw [Proj.stalkIso'_germ, ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [coordFracAt, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  simp

private theorem ratio_mul {x : projZ.{u} n} {j m : Fin (n + 1)} (hj : x ∈ chartOpen n j)
    (hm : x ∈ chartOpen n m) (k : Fin (n + 1)) :
    ratio hm k = ratio hj k * ratio hm j := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [map_mul, HomogeneousLocalization.val_mul, val_stalkIso'_ratio, val_stalkIso'_ratio,
    val_stalkIso'_ratio]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]; ring⟩

private theorem ratio_self {x : projZ.{u} n} {j : Fin (n + 1)} (hj : x ∈ chartOpen n j) :
    ratio hj j = 1 := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [(Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x).map_one, HomogeneousLocalization.val_one,
    val_stalkIso'_ratio]
  exact Localization.mk_self ⟨_, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hj)⟩

private theorem germ_mem_closure_ratio {x : projZ.{u} n} {j : Fin (n + 1)} (hx : x ∈ chartOpen n j)
    (b : Γ(projZ.{u} n, chartOpen n j)) :
    (projZ.{u} n).presheaf.germ _ x hx b ∈ Subring.closure (Set.range (ratio hx)) := by
  obtain ⟨s, rfl⟩ : ∃ s, Proj.awayToSection _ _ s = b :=
    ⟨(Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv b, by
      rw [← CommRingCat.comp_apply]
      exact congrArg (fun φ => φ b)
        (congrArg CommRingCat.Hom.hom
          (Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv_hom_id)⟩
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) n j s
  set ψ : HomogeneousLocalization.Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j) →+*
      (projZ.{u} n).presheaf.stalk x :=
    ((projZ.{u} n).presheaf.germ _ x hx).hom.comp (Proj.awayToSection _ _).hom
  change ψ (chartHom _ n j p) ∈ _
  have : ψ.comp (chartHom (ULift.{u} ℤ) n j) =
      MvPolynomial.eval₂Hom (ψ.comp (coeffToAway _ n j)) (fun k => ψ (chartCoord _ n j k)) := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  rw [← RingHom.comp_apply, this]
  have hc : ∀ c : ULift.{u} ℤ, (ψ.comp (coeffToAway _ n j)) c ∈
      Subring.closure (Set.range (ratio hx)) := fun c => by
    rw [show c = ((c.down : ℤ) : ULift.{u} ℤ) from by ext; simp, map_intCast]
    exact intCast_mem _ _
  exact MvPolynomial.eval₂_mem (fun c _ => hc _) (fun k => Subring.subset_closure ⟨k.1, rfl⟩)

end Charts

/-! ### The coordinate ratios on a closed subscheme of `ℙⁿ_Y` -/

section Ratios

variable {Y Z : Scheme.{u}} {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y)

/-- The projection of `Z ⊆ ℙⁿ_Y` to the integral model `ℙⁿ_ℤ`. -/
private noncomputable abbrev toProjZ : Z ⟶ projZ.{u} n :=
  i ≫ (pullback.snd (terminal.from Y) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
    projectiveSpaceOver n Y ⟶ projZ.{u} n)

/-- The germ at `z` of the pulled-back ratio `T_k / T_j`, for `z` on the chart `T_j ≠ 0`. -/
private noncomputable def gRatio (z : Z) {j : Fin (n + 1)} (hz : toProjZ i z ∈ chartOpen n j)
    (k : Fin (n + 1)) : Z.presheaf.stalk z :=
  (toProjZ i).stalkMap z (ratio hz k)

private theorem gRatio_mul (z : Z) {j m : Fin (n + 1)} (hj : toProjZ i z ∈ chartOpen n j)
    (hm : toProjZ i z ∈ chartOpen n m) (k : Fin (n + 1)) :
    gRatio i z hm k = gRatio i z hj k * gRatio i z hm j := by
  rw [gRatio, gRatio, gRatio, ratio_mul hj hm k, map_mul]

private theorem gRatio_self (z : Z) {j : Fin (n + 1)} (hj : toProjZ i z ∈ chartOpen n j) :
    gRatio i z hj j = 1 := by
  rw [gRatio, ratio_self, map_one]

private theorem algebraMap_gRatio [IsIntegral Z] (z : Z) {j : Fin (n + 1)}
    (hz : toProjZ i z ∈ chartOpen n j) (hη : toProjZ i (genericPoint Z) ∈ chartOpen n j)
    (k : Fin (n + 1)) :
    algebraMap (Z.presheaf.stalk z) Z.functionField (gRatio i z hz k) =
      gRatio i (genericPoint Z) hη k := by
  have h : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  change (Z.presheaf.stalkSpecializes h).hom ((toProjZ i).stalkMap z (ratio hz k)) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, gRatio, ratio, ratio]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply (projZ.{u} n).presheaf hz _ _

end Ratios

/-! ### The ideal sheaf -/

section Core

/-- If `ρ(b_k) = g_k ρ(b_j)` for all `k`, the image of the ideal generated by the `b_k` is
generated by `ρ(b_j)`. -/
private theorem map_span_range_eq_span_singleton {A B : Type*} [CommRing A] [CommRing B]
    {ι : Type*} (ρ : A →+* B) (b : ι → A) (g : ι → B) (j : ι)
    (h : ∀ k, ρ (b k) = g k * ρ (b j)) :
    (Ideal.span (Set.range b)).map ρ = Ideal.span {ρ (b j)} := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Function.comp_apply, h k]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨j, rfl⟩

/-- If `ρ(b_k) = g_k ρ(b_j)` with `ρ(b_j) ≠ 0`, `ρ` local into a domain, and the `b_k` generate a
principal ideal, then every `g_k` lies in the image of `ρ`. -/
private theorem mem_range_of_span_singleton_eq {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    {ι : Type*} (ρ : A →+* B) [IsLocalHom ρ] (b : ι → A) (g : ι → B) (j : ι) (t : A)
    (ht : Ideal.span {t} = Ideal.span (Set.range b)) (h : ∀ k, ρ (b k) = g k * ρ (b j))
    (hne : ρ (b j) ≠ 0) (k : ι) : g k ∈ Set.range ρ := by
  have hspan := map_span_range_eq_span_singleton ρ b g j h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1
    (show b j ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨j, rfl⟩)
  have htm : ρ t ∈ Ideal.span {ρ (b j)} :=
    hspan ▸ Ideal.mem_map_of_mem ρ (ht ▸ Ideal.mem_span_singleton_self t)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 htm
  have hav : ρ a * v = 1 :=
    mul_right_cancel₀ hne (by rw [mul_assoc, hv, one_mul, ← map_mul, ha])
  have hau : IsUnit a := (isUnit_map_iff ρ a).1 (isUnit_iff_exists_inv.2 ⟨v, hav⟩)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (show b k ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨c * ↑hau.unit⁻¹, mul_right_cancel₀ hne ?_⟩
  have hinv : ρ ↑hau.unit⁻¹ * ρ a = 1 := by
    rw [← map_mul, hau.val_inv_mul, map_one]
  rw [← h k, ← hc, ← ha, map_mul, map_mul, map_mul]
  linear_combination (ρ c * ρ t) * hinv

/-- The stalk of an effective Cartier divisor is principal. -/
private theorem exists_stalk_eq_span_singleton {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ t, IdealSheafData.stalk J x = Ideal.span {t} := by
  obtain ⟨U, hU, hxU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hf, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- **The stalks of `ℙⁿ_Y` on a standard chart.** At a point `x` of `ℙⁿ_Y = Y ×_ℤ ℙⁿ_ℤ` on the
chart `T_j ≠ 0`, a subring of the stalk which contains the functions from `Y`, the ratios
`T_k / T_j` and the inverses of its units is the whole stalk. -/
private theorem eq_top_of_subring_stalk_pullback {Y : Scheme.{u}} {n : ℕ} (f : Y ⟶ ⊤_ Scheme)
    (g : projZ.{u} n ⟶ ⊤_ Scheme) (x : ↥(pullback f g)) {j : Fin (n + 1)}
    (hx : pullback.snd f g x ∈ chartOpen n j) (T : Subring ((pullback f g).presheaf.stalk x))
    (h1 : ∀ a, (pullback.fst f g).stalkMap x a ∈ T)
    (h2 : ∀ k, (pullback.snd f g).stalkMap x (ratio hx k) ∈ T)
    (h3 : ∀ v : ((pullback f g).presheaf.stalk x)ˣ, v.1 ∈ T → (v⁻¹).1 ∈ T) :
    T = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pullback.fst f g x)) isOpen_univ
  have hV : IsAffineOpen (chartOpen n j) :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos
  have hW := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf f g hU hV
  have hxW : x ∈ pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j := ⟨hyU, hx⟩
  have hgerm : ∀ s, ((pullback f g).presheaf.germ _ x hxW).hom s ∈ T := by
    have htop := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf f g hU hV rfl
      inf_le_left inf_le_right (T.comap ((pullback f g).presheaf.germ _ x hxW).hom)
      (fun a => ?_) (fun b => ?_)
    · intro s
      have : s ∈ T.comap ((pullback f g).presheaf.germ _ x hxW).hom := htop ▸ Subring.mem_top s
      exact this
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.fst f g) U x hyU a
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      exact h1 _
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.snd f g) (chartOpen n j) x hx b
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      have hle : Subring.closure (Set.range (ratio hx)) ≤
          T.comap ((pullback.snd f g).stalkMap x).hom :=
        Subring.closure_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k)
      exact hle (germ_mem_closure_ratio hx b)
  letI := (pullback f g).presheaf.algebra_section_stalk (U := pullback.fst f g ⁻¹ᵁ U ⊓
    pullback.snd f g ⁻¹ᵁ chartOpen n j) ⟨x, hxW⟩
  haveI := hW.isLocalization_stalk ⟨x, hxW⟩
  refine top_unique fun s _ => ?_
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl s
  dsimp only
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  have hu := IsLocalization.map_units ((pullback f g).presheaf.stalk x) t
  have hinv : IsLocalization.mk' ((pullback f g).presheaf.stalk x)
      (1 : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j)) t =
      (hu.unit⁻¹).1 := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [IsUnit.unit_spec, mul_comm, IsLocalization.mk'_spec, map_one]
  rw [hinv]
  exact T.mul_mem (hgerm a) (h3 _ (hgerm t))

/-- Let `φ : Z ⟶ X` be a separated dominant morphism of
integral schemes all of whose maps on local rings are surjective. Then `φ` is injective. -/
private theorem injective_of_surjective_stalkMap {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (φ : Z ⟶ X) [IsSeparated φ] [IsDominant φ]
    (hsurj : ∀ z, Function.Surjective (φ.stalkMap z)) : Function.Injective φ := by
  intro z z' hzz
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring
    (LocalSubring.range (algebraMap (Z.presheaf.stalk z) Z.functionField))
  -- domination of the local rings of `X`, read in the function field of `Z`
  let HX : X → Prop := fun w => ∀ c : X.presheaf.stalk w,
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V
  let HX' : X → Prop := fun w => ∀ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w),
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V.nonunits
  let D : Z → Prop := fun p => (∀ a : Z.presheaf.stalk p, algebraMap _ Z.functionField a ∈ V) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk p), algebraMap _ Z.functionField a ∈ V.nonunits
  have hDX : ∀ p, D p → HX (φ p) ∧ HX' (φ p) := by
    intro p hp
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]; exact hp.1 _
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine hp.2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 hc (isUnit_of_map_unit _ _ hu)
  have hXD : ∀ p, HX (φ p) → HX' (φ p) → D p := by
    intro p h1 h2
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]; exact h1 c
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine h2 c ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (hu.map _)
  have hDz : D z := by
    refine ⟨fun a => hV.1 ⟨a, rfl⟩, fun a ha => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨hV.1 ⟨a, rfl⟩, (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_⟩
    haveI := hV.2
    have hu' := isUnit_of_map_unit (Subring.inclusion hV.1) ⟨_, ⟨a, rfl⟩⟩ hu
    obtain ⟨⟨b, ⟨a', rfl⟩⟩, hb⟩ := isUnit_iff_exists_inv.1 hu'
    have hb' : algebraMap _ Z.functionField (a * a') = 1 := by
      rw [map_mul]; exact congrArg Subtype.val hb
    rw [← map_one (algebraMap (Z.presheaf.stalk z) Z.functionField)] at hb'
    exact (IsLocalRing.mem_maximalIdeal _).1 ha
      (isUnit_iff_exists_inv.2 ⟨a', IsFractionRing.injective _ _ hb'⟩)
  have hDz' : D z' := by
    obtain ⟨h1, h2⟩ := hDX z hDz
    exact hXD z' (hzz ▸ h1) (hzz ▸ h2)
  -- the lift `Spec V ⟶ Z` through a dominated point
  let ψ : ∀ p, D p → Z.presheaf.stalk p →+* V := fun p hp =>
    (algebraMap _ Z.functionField).codRestrict V hp.1
  have hψloc : ∀ p (hp : D p), IsLocalHom (ψ p hp) := by
    intro p hp
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    obtain ⟨_, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1
      (hp.2 a ((IsLocalRing.mem_maximalIdeal _).2 hna))
    exact (IsLocalRing.mem_maximalIdeal _).1 hm ha
  let l : ∀ p, D p → (Spec (.of V) ⟶ Z) := fun p hp =>
    Spec.map (CommRingCat.ofHom (ψ p hp)) ≫ Z.fromSpecStalk p
  have hl : ∀ p (hp : D p),
      Spec.map (CommRingCat.ofHom (algebraMap V Z.functionField)) ≫ l p hp =
        Z.fromSpecStalk (genericPoint Z) := by
    intro p hp
    have hy : genericPoint Z ⤳ p := (genericPoint_spec Z).specializes trivial
    have hc : CommRingCat.ofHom (ψ p hp) ≫ CommRingCat.ofHom (algebraMap V Z.functionField) =
        Z.presheaf.stalkSpecializes hy := by
      ext a; rfl
    simp only [l]
    rw [← Spec.map_comp_assoc, hc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hlp : ∀ p (hp : D p), l p hp (IsLocalRing.closedPoint V) = p := by
    intro p hp
    haveI : IsLocalHom (CommRingCat.ofHom (ψ p hp)).hom := hψloc p hp
    change Z.fromSpecStalk p (Spec.map (CommRingCat.ofHom (ψ p hp))
      (IsLocalRing.closedPoint V)) = p
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  -- the composite `Spec V ⟶ X` only depends on the image point
  let χ : ∀ w, HX w → X.presheaf.stalk w →+* V := fun w hw =>
    ((functionFieldMap φ).comp (algebraMap _ X.functionField)).codRestrict V hw
  have hlφ : ∀ p (hp : D p), l p hp ≫ φ =
      Spec.map (CommRingCat.ofHom (χ (φ p) (hDX p hp).1)) ≫ X.fromSpecStalk (φ p) := by
    intro p hp
    simp only [l]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext c
    change algebraMap _ Z.functionField ((φ.stalkMap p).hom c) =
      functionFieldMap φ (algebraMap _ X.functionField c)
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hχ : ∀ w w' (_ : w = w') (hw : HX w) (hw' : HX w'),
      Spec.map (CommRingCat.ofHom (χ w hw)) ≫ X.fromSpecStalk w =
        Spec.map (CommRingCat.ofHom (χ w' hw')) ≫ X.fromSpecStalk w' := by
    rintro w _ rfl hw hw'; rfl
  let S : ValuativeCommSq φ :=
    { R := V
      K := Z.functionField
      i₁ := Z.fromSpecStalk (genericPoint Z)
      i₂ := l z hDz ≫ φ
      commSq := ⟨by rw [← hl z hDz, Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion φ S
  let L : S.commSq.LiftStruct := ⟨l z hDz, hl z hDz, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨l z' hDz', hl z' hDz',
    by show l z' hDz' ≫ φ = l z hDz ≫ φ; rw [hlφ z' hDz', hlφ z hDz]; exact hχ _ _ hzz.symm _ _⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  rw [← hlp z hDz, ← hlp z' hDz']
  exact congrArg (fun m : Spec (.of V) ⟶ Z => m (IsLocalRing.closedPoint V)) hLL

/-- **The comparison morphism is an isomorphism.** Let `Z ⊆ ℙⁿ_Y` be closed and integral over an
integral `Y`, `I` an ideal sheaf on `Y` vanishing nowhere near the generic point, and
`φ : Z ⟶ Bl_I Y` a morphism over `Y`. Suppose that at every `z`, on a chart `T_j ≠ 0`, the stalk of
`I` at the image of `z` is generated by elements `b_k` with `r^♯ b_k = (T_k / T_j) · r^♯ b_j` and
`r^♯ b_j ≠ 0`. Then `φ` is an isomorphism. -/
private theorem isIso_of_comp_blowUpToBase {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r) [IsDominant r]
    (I : Y.IdealSheafData) (hgenY : genericPoint Y ∉ I.support)
    (φ : Z ⟶ blowUp I) (hφ : φ ≫ blowUpToBase I = r)
    (hloc : ∀ z : Z, ∃ (j : Fin (n + 1)) (hz : toProjZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0) :
    IsIso φ := by
  subst hφ
  have hI : I ≠ ⊥ := by
    rintro rfl
    exact hgenY (by simp only [Scheme.IdealSheafData.support_bot]; trivial)
  haveI : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  -- the generic point goes to the generic point
  have hgen : φ (genericPoint Z) = genericPoint (blowUp I) := by
    have h1 : blowUpToBase I (φ (genericPoint Z)) = genericPoint Y :=
      map_genericPoint_of_isDominant (φ ≫ blowUpToBase I)
    have hV : φ (genericPoint Z) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
      change blowUpToBase I (φ _) ∈ I.support.compl
      rw [h1]
      exact hgenY
    have hV' : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl :=
      ((genericPoint_spec _).mem_open_set_iff (blowUpToBase I ⁻¹ᵁ _).isOpen).2 ⟨_, trivial, hV⟩
    have h2 : blowUpToBase I (genericPoint (blowUp I)) = genericPoint Y := by
      have hs : genericPoint (blowUp I) ⤳ φ (genericPoint Z) :=
        (genericPoint_spec _).specializes trivial
      have := hs.map (blowUpToBase I).base.hom.continuous
      rw [h1] at this
      exact (this.antisymm ((genericPoint_spec Y).specializes trivial)).eq
    have := (blowUpToBase I ∣_ I.support.compl).homeomorph.injective
      (a₁ := ⟨_, hV⟩) (a₂ := ⟨_, hV'⟩) (Subtype.ext
        (((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV⟩).trans h1).trans
          ((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV'⟩).trans h2).symm))
    exact congrArg Subtype.val this
  haveI : IsDominant φ := ⟨by
    refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
    rw [← (genericPoint_spec (blowUp I)).def]
    exact closure_mono (by rintro _ rfl; exact ⟨_, hgen⟩)⟩
  -- the stalk maps are injective
  have hinj : ∀ z, Function.Injective (φ.stalkMap z) := fun z => by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h := MMP.Mori.functionFieldMap_algebraMap_stalk φ z a
    rw [ha, map_zero] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1
      ((map_eq_zero_iff _ (functionFieldMap φ).injective).1 h)
  -- the stalk maps are surjective
  have hsurj : ∀ z, Function.Surjective (φ.stalkMap z) := by
    intro z
    obtain ⟨j, hz, b, hspan, hrel, hne⟩ := hloc z
    have hcomp : ∀ a, (φ ≫ blowUpToBase I).stalkMap z a =
        φ.stalkMap z ((blowUpToBase I).stalkMap (φ z) a) := fun a => by
      rw [Scheme.Hom.stalkMap_comp]; rfl
    -- the inverse image of `I` is principal at `φ z`
    obtain ⟨t, ht⟩ := exists_stalk_eq_span_singleton (I.comap (blowUpToBase I))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) (φ z)
    have ht' : Ideal.span {t} =
        Ideal.span (Set.range fun k => (blowUpToBase I).stalkMap (φ z) (b k)) := by
      rw [← ht, idealStalk_comap_eq_map]
      exact ((congrArg (Ideal.map ((blowUpToBase I).stalkMap (φ z)).hom) hspan).trans
        (Ideal.map_span _ _)).trans (congrArg Ideal.span (Set.range_comp _ _).symm)
    -- the coordinate ratios come from the blow-up
    have hg : ∀ k, gRatio i z hz k ∈ Set.range (φ.stalkMap z) :=
      mem_range_of_span_singleton_eq (φ.stalkMap z).hom
        (fun k => (blowUpToBase I).stalkMap (φ z) (b k)) (gRatio i z hz) j t ht'
        (fun k => by rw [← hcomp, ← hcomp]; exact hrel k) (by rw [← hcomp]; exact hne)
    -- the functions from `Y` come from the blow-up
    have hY : ∀ a, ∃ c, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a = φ.stalkMap z c := by
      intro a
      rw [Scheme.Hom.stalkMap_congr_hom _ _ hir z, CommRingCat.comp_apply, hcomp]
      exact ⟨_, rfl⟩
    have e1 : ∀ a, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a =
        i.stalkMap z ((pullback.fst (terminal.from Y)
          (terminal.from (projectiveSpaceAtUniverse.{u} n))).stalkMap (i z) a) := by
      intro a; rw [Scheme.Hom.stalkMap_comp]; rfl
    have e2 : ∀ k, gRatio i z hz k = i.stalkMap z ((pullback.snd (terminal.from Y)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
          projectiveSpaceOver n Y ⟶ projZ.{u} n).stalkMap (i z) (ratio hz k)) := by
      intro k; rw [gRatio]; erw [Scheme.Hom.stalkMap_comp]; rfl
    -- the image of `φ` pulled back to the stalk of `ℙⁿ_Y` is everything
    have hT := eq_top_of_subring_stalk_pullback (terminal.from Y) (terminal.from (projZ.{u} n))
      (i z) hz (((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom) (fun a => ?_) (fun k => ?_)
      (fun v hv => ?_)
    · intro a
      obtain ⟨c, rfl⟩ := i.stalkMap_surjective z a
      have : c ∈ ((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom := hT ▸ Subring.mem_top c
      exact this
    · obtain ⟨c, hc⟩ := hY a
      exact ⟨c, hc.symm.trans (e1 a)⟩
    · obtain ⟨c, hc⟩ := hg k
      exact ⟨c, hc.trans (e2 k)⟩
    · obtain ⟨c, hc⟩ := hv
      have hcu : IsUnit c := isUnit_of_map_unit (φ.stalkMap z).hom c (hc ▸ v.isUnit.map _)
      refine ⟨↑hcu.unit⁻¹, ?_⟩
      have h1 : (i.stalkMap z) v.1 * (i.stalkMap z) (v⁻¹).1 = 1 :=
        (map_mul (i.stalkMap z).hom v.1 (v⁻¹).1).symm.trans
          ((congrArg (i.stalkMap z).hom v.mul_inv).trans (map_one _))
      have h2 : (φ.stalkMap z) c * (φ.stalkMap z) ↑hcu.unit⁻¹ = 1 :=
        (map_mul (φ.stalkMap z).hom c _).symm.trans
          ((congrArg (φ.stalkMap z).hom hcu.mul_val_inv).trans (map_one _))
      change (φ.stalkMap z) ↑hcu.unit⁻¹ = (i.stalkMap z) (v⁻¹).1
      change (φ.stalkMap z) c = (i.stalkMap z) v.1 at hc
      linear_combination (-(φ.stalkMap z) ↑hcu.unit⁻¹) * h1 -
        ((φ.stalkMap z) ↑hcu.unit⁻¹ * (i.stalkMap z) (v⁻¹).1) * hc +
        (i.stalkMap z) (v⁻¹).1 * h2
  -- `φ` is closed and separated
  haveI : IsProper (φ ≫ blowUpToBase I) := by
    rw [← hir]
    haveI := isProper_projectiveSpaceOver n Y
    infer_instance
  haveI : IsSeparated φ := IsSeparated.of_comp φ (blowUpToBase I)
  haveI : UniversallyClosed φ := UniversallyClosed.of_comp_of_isSeparated φ (blowUpToBase I)
  -- `φ` is injective
  have hφinj : Function.Injective φ := injective_of_surjective_stalkMap φ hsurj
  have hclosed : IsClosedMap φ := φ.isClosedMap
  have hφsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← hclosed.isClosed_range.closure_eq]
    exact (IsDominant.denseRange (f := φ)).closure_range
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨TopCat.isIso_of_bijective_of_isClosedMap _ ⟨hφinj, hφsurj⟩ hclosed, fun z => ?_⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj z, hsurj z⟩

/-- **The core.** A closed integral subscheme `Z` of `ℙⁿ_Y`, birational over an integral
locally noetherian `Y` with factorial local rings, is the blow-up of an ideal sheaf whose stalks
have no common divisor. -/
private theorem exists_iso_blowUp_of_isClosedImmersion {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y]
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y))
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r) (hrb : MMP.Mori.IsBirationalMorphism r) :
    ∃ (I : Y.IdealSheafData) (e : Z ≅ blowUp I),
      (∀ y, IsDivisorFree (IdealSheafData.stalk I y)) ∧ e.hom ≫ blowUpToBase I = r := by
  classical
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hrb
  -- the chart of the generic point and the coordinate ratios there
  have hcover : ∀ x : projZ.{u} n, ∃ j, x ∈ chartOpen n j := fun x => by
    have hx : x ∈ (⊤ : (projZ.{u} n).Opens) := trivial
    rw [← iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hgen : ∀ (z : Z) {j : Fin (n + 1)}, toProjZ i z ∈ chartOpen n j →
      toProjZ i (genericPoint Z) ∈ chartOpen n j := fun z j hz =>
    ((genericPoint_spec Z).mem_open_set_iff (toProjZ i ⁻¹ᵁ chartOpen n j).isOpen).2 ⟨z, trivial, hz⟩
  obtain ⟨j₀, hj₀⟩ := hcover (toProjZ i (genericPoint Z))
  set c : Fin (n + 1) → Z.functionField := fun k => gRatio i (genericPoint Z) hj₀ k
  have hc₀ : c j₀ = 1 := gRatio_self i _ hj₀
  have hcrel : ∀ (z : Z) {j : Fin (n + 1)} (hz : toProjZ i z ∈ chartOpen n j) (k : Fin (n + 1)),
      c k = algebraMap _ Z.functionField (gRatio i z hz k) * c j := by
    intro z j hz k
    rw [algebraMap_gRatio i z hz (hgen z hz)]
    exact gRatio_mul i _ (hgen z hz) hj₀ k
  have hcj : ∀ (z : Z) {j : Fin (n + 1)} (_ : toProjZ i z ∈ chartOpen n j), c j ≠ 0 := by
    intro z j hz h
    have := hcrel z hz j₀
    rw [h, mul_zero, hc₀] at this
    exact one_ne_zero this
  -- the coordinate ratios as rational functions on `Y`
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hrb
  set f : Fin (n + 1) → Y.functionField := fun k => Function.surjInv hbij.2 (c k)
  have hf : ∀ k, functionFieldMap r (f k) = c k := fun k => Function.surjInv_eq hbij.2 _
  have hf₀ : ∃ k, f k ≠ 0 := ⟨j₀, fun h => by
    have := hf j₀
    rw [h, map_zero, hc₀] at this
    exact zero_ne_one this⟩
  set I := colonIdealSheaf f
  -- the stalks of `I`
  have hstalk : ∀ y : Y, ∃ (d : Y.functionField) (b : Fin (n + 1) → Y.presheaf.stalk y),
      d ≠ 0 ∧ (∀ k, algebraMap _ Y.functionField (b k) = d * f k) ∧
      IsDivisorFree (IdealSheafData.stalk I y) ∧
      IdealSheafData.stalk I y = Ideal.span (Set.range b) := by
    intro y
    haveI := hUFD y
    obtain ⟨d, b, hd, hbd, hfree, hspan⟩ :=
      exists_colonIdeal_eq_span (R := Y.presheaf.stalk y) (K := Y.functionField) hf₀
    rw [stalk_colonIdealSheaf]
    refine ⟨d, b, hd, hbd, ⟨?_, fun x s h => hfree x s fun k =>
      h _ (hspan ▸ Ideal.subset_span ⟨k, rfl⟩)⟩, hspan⟩
    obtain ⟨k, hk⟩ := hf₀
    rw [hspan, Ne, Ideal.span_eq_bot, not_forall]
    refine ⟨b k, ?_⟩
    simp only [Set.mem_range, exists_apply_eq_apply, true_implies]
    intro h0
    have := hbd k
    rw [h0, map_zero] at this
    exact mul_ne_zero hd hk this.symm
  -- the local data on `Z`
  have hloc : ∀ z : Z, ∃ (j : Fin (n + 1)) (hz : toProjZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0 := by
    intro z
    obtain ⟨j, hz⟩ := hcover (toProjZ i z)
    obtain ⟨d, b, hd, hbd, -, hspan⟩ := hstalk (r z)
    have himg : ∀ k, algebraMap _ Z.functionField (r.stalkMap z (b k)) =
        functionFieldMap r d * c k := fun k => by
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, hbd, map_mul, hf]
    have hinj : Function.Injective (algebraMap (Z.presheaf.stalk z) Z.functionField) :=
      IsFractionRing.injective _ _
    refine ⟨j, hz, b, hspan, fun k => hinj ?_, fun h0 => ?_⟩
    · rw [map_mul, himg, himg, hcrel z hz k]
      ring
    · have := himg j
      rw [h0, map_zero] at this
      exact mul_ne_zero ((map_ne_zero _).2 hd) (hcj z hz) this.symm
  -- the inverse image of `I` is an effective Cartier divisor
  have hcart : Stacks.Blowup.IsCartierOver I (Over.mk r) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (I.comap r)
    have : LocallyOfFiniteType r := by
      rw [← hir]
      haveI := isProper_projectiveSpaceOver n Y
      infer_instance
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian r
    refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun z _ => ?_
    obtain ⟨j, hz, b, hspan, hrel, hne⟩ := hloc z
    refine ⟨_, IsRegular.of_ne_zero hne, ?_⟩
    rw [idealStalk_comap_eq_map, hspan]
    exact map_span_range_eq_span_singleton _ b _ j hrel
  -- the comparison morphism
  have hgenY : genericPoint Y ∉ I.support := by
    obtain ⟨-, -, -, -, hfree, -⟩ := hstalk (genericPoint Y)
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support]
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfree.1
    exact Ideal.eq_top_of_isUnit_mem _ ha (isUnit_iff_ne_zero.2 ha0)
  haveI := isIso_of_comp_blowUpToBase r i hir I hgenY (blowUpLift I r hcart)
    (blowUpLift_comp _ _ _) hloc
  refine ⟨I, asIso (blowUpLift I r hcart), fun y => ?_, blowUpLift_comp _ _ _⟩
  obtain ⟨-, -, -, -, hfree, -⟩ := hstalk y
  exact hfree

end Core

/-! ### The exceptional divisor -/

/-- **Relative ampleness across an isomorphism of the source.** If `L` is `f`-ample and
`M ≅ e^* L` for an isomorphism `e`, then `M` is `(e ≫ f)`-ample. -/
private theorem isRelativelyAmple_comp_of_iso {X X' S : Scheme.{u}} (e : X ≅ X') (f : X' ⟶ S)
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M]
    (ε : M ≅ Stacks.AmpleLocallyClosed.pullbackModule e.hom L)
    (h : MMP.Mori.IsRelativelyAmple f L) : MMP.Mori.IsRelativelyAmple (e.hom ≫ f) M := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  have hamp' := Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion
    (e.hom ∣_ (f ⁻¹ᵁ V)) _ hamp
  have hcomm : (e.hom ∣_ (f ⁻¹ᵁ V)) ≫ (f ⁻¹ᵁ V).ι = (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ e.hom :=
    morphismRestrict_ι e.hom (f ⁻¹ᵁ V)
  let i1 := ((RingedSpaceModuleAdjunction.modulePullbackComp
      (e.hom ∣_ (f ⁻¹ᵁ V)).toLRSHom.toShHom (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).app L).symm
  let i2 := eqToIso (congrArg (fun φ : (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ X' =>
      (RingedSpaceModuleAdjunction.modulePullback φ.toLRSHom.toShHom).obj L) hcomm)
  let i3 := (RingedSpaceModuleAdjunction.modulePullbackComp
      (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι.toLRSHom.toShHom e.hom.toLRSHom.toShHom).app L
  let i4 := (RingedSpaceModuleAdjunction.modulePullback
      (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι.toLRSHom.toShHom).mapIso ε.symm
  let iso : Stacks.AmpleLocallyClosed.pullbackModule (e.hom ∣_ (f ⁻¹ᵁ V))
      ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L) ≅
      (RingedSpaceModuleAdjunction.modulePullback
        (e.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι.toLRSHom.toShHom).obj M := i1 ≪≫ i2 ≪≫ i3 ≪≫ i4
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ iso).1 hamp'

/-- A point of `Y` lies in the biregular locus of `e.hom ≫ blowUpToBase I` iff it is off the
cosupport of `I`, when the stalks of `I` have no common divisor. -/
private theorem mem_biregularLocus_iff_notMem_support {Y Z : Scheme.{u}} (I : Y.IdealSheafData)
    (e : Z ≅ blowUp I) (hI : ∀ y, IsDivisorFree (IdealSheafData.stalk I y))
    (hJc : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (e.hom ≫ blowUpToBase I)))
    (y : Y) : y ∈ MMP.Mori.biregularLocus (e.hom ≫ blowUpToBase I) ↔ y ∉ I.support := by
  set r := e.hom ≫ blowUpToBase I
  refine ⟨fun hy hyI => ?_, fun hy => ?_⟩
  · set W := MMP.Mori.biregularLocus r
    haveI : IsIso (r ∣_ W) := MMP.Mori.isBiregular_biregularLocus r
    obtain ⟨x₀, hzy⟩ := (r ∣_ W).surjective ⟨y, hy⟩
    have hzy' : r ((r ⁻¹ᵁ W).ι x₀) = y :=
      (morphismRestrict_base_coe r W x₀).symm.trans (congrArg Subtype.val hzy)
    set z := (r ⁻¹ᵁ W).ι x₀
    -- the map on local rings of `r` at `z` is an isomorphism
    haveI : IsOpenImmersion ((r ⁻¹ᵁ W).ι ≫ r) := by
      rw [← morphismRestrict_ι]; infer_instance
    haveI h1 : IsIso (((r ⁻¹ᵁ W).ι ≫ r).stalkMap x₀) := inferInstance
    rw [Scheme.Hom.stalkMap_comp] at h1
    haveI : IsIso (r.stalkMap z) := @IsIso.of_isIso_comp_right _ _ _ _ _ (r.stalkMap z)
      ((r ⁻¹ᵁ W).ι.stalkMap x₀) inferInstance h1
    have hbij := ConcreteCategory.bijective_of_isIso (r.stalkMap z)
    -- so the stalk of `I` at `r z` is principal, hence trivial
    obtain ⟨t, ht⟩ := exists_stalk_eq_span_singleton _ hJc z
    rw [idealStalk_comap_eq_map] at ht
    obtain ⟨s, rfl⟩ := hbij.2 t
    have hprin : (IdealSheafData.stalk I (r z)).IsPrincipal := by
      refine ⟨s, ?_⟩
      have hs : Ideal.span {(r.stalkMap z).hom s} =
          Ideal.map (r.stalkMap z).hom (Ideal.span {s}) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [← Ideal.comap_map_of_bijective (r.stalkMap z).hom hbij
        (I := IdealSheafData.stalk I (r z)), ht, hs,
        Ideal.comap_map_of_bijective (r.stalkMap z).hom hbij]
    have htop := (hI (r z)).eq_top_of_isPrincipal hprin
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support I (r z)).1 htop (hzy' ▸ hyI)
  · refine MMP.Mori.le_biregularLocus (V := I.support.compl) ?_ hy
    change IsIso ((e.hom ≫ blowUpToBase I) ∣_ I.support.compl)
    rw [morphismRestrict_comp]
    haveI h2 : IsIso (blowUpToBase I ∣_ I.support.compl) := isIso_blowUp_restrict_compl_support I
    have h3 : IsIso (e.hom ∣_ (blowUpToBase I ⁻¹ᵁ I.support.compl)) := inferInstance
    exact IsIso.comp_isIso' h3 h2

/-- **The exceptional divisor.** If `r` factors as an isomorphism onto `Bl_I Y` followed by the
blow-up, with `I` without common divisor in its stalks, the inverse image of `I` is an effective
Cartier divisor `A` on `Z`, supported on the exceptional set of `r`, with `-A` relatively ample. -/
private theorem exists_isEffective_cartierSupport_eq_exceptionalSet {Y Z : Scheme.{u}}
    [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) (I : Y.IdealSheafData) (e : Z ≅ blowUp I)
    (hI : ∀ y, IsDivisorFree (IdealSheafData.stalk I y)) (he : e.hom ≫ blowUpToBase I = r) :
    ∃ A : Z.CartierDivisor, MMP.Intersection.IsEffective A ∧
      (MMP.Intersection.cartierSupport A) = (MMP.Mori.exceptionalSet r : Set Z)
          ∧ IsRelativelyAmpleCartier r (-A) := by
  subst he
  have hJ' : I.comap (e.hom ≫ blowUpToBase I) = (exceptionalIdeal I).comap e.hom :=
    Scheme.IdealSheafData.comap_comp I e.hom (blowUpToBase I)
  have hJc : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (e.hom ≫ blowUpToBase I)) :=
    hJ' ▸ Stacks.Divisors.isPullbackDefined_of_flat e.hom _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  obtain ⟨A, hA, hAJ⟩ := (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq
    (I.comap (e.hom ≫ blowUpToBase I))).1 hJc
  refine ⟨A, hA, ?_, ?_⟩
  · rw [← MMP.CartierDivisor.coe_support_subscheme hA, hAJ, Scheme.IdealSheafData.support_comap]
    ext z
    change (e.hom ≫ blowUpToBase I) z ∈ I.support ↔ z ∈ MMP.Mori.exceptionalSet _
    rw [MMP.Mori.mem_exceptionalSet, mem_biregularLocus_iff_notMem_support I e hI hJc, not_not]
  · haveI : Stacks.Ample.IsInvertibleModule (blowUp I) (exceptionalIdealModule I) :=
      Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
        (twistOneIsoExceptionalIdealModule I)
    have hamp : MMP.Mori.IsRelativelyAmple (blowUpToBase I) (exceptionalIdealModule I) :=
      MMP.Mori.IsRelativelyAmple.of_stacks _ _
        ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
          (twistOneIsoExceptionalIdealModule I)).1
          (isRelativelyAmple_blowUpTwist I
            (Scheme.IdealSheafData.isFiniteType_of_isLocallyNoetherian I)))
    -- the ideal sheaf of `A` is the pullback of the exceptional ideal sheaf
    set E := exceptionalIdeal I
    let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace
    let aS : (E.comap e.hom).subscheme ≅ E.subscheme :=
      E.comapIso e.hom ≪≫ asIso (Limits.pullback.snd e.hom E.subschemeι)
    have hcommS : (E.comap e.hom).subschemeι ≫ e.hom = aS.hom ≫ E.subschemeι := by
      simp only [aS, Iso.trans_hom, asIso_hom, Category.assoc, ← Limits.pullback.condition]
      rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    have hcomm : (E.comap e.hom).subschemeι.toLRSHom.toShHom ≫ (F.mapIso e).hom =
        (F.mapIso aS).hom ≫ E.subschemeι.toLRSHom.toShHom := by
      have := congrArg F.map hcommS
      rw [F.map_comp, F.map_comp] at this
      exact this
    let ε : MMP.CartierDivisor.sheaf (-A)
        ≅ Stacks.AmpleLocallyClosed.pullbackModule e.hom (exceptionalIdealModule I) :=
      (MMP.CartierDivisor.idealSheafIsoSheafNeg A hA).symm ≪≫
        eqToIso (congrArg (fun K : Z.IdealSheafData =>
          Stacks.ClosedImmersion.idealSheaf K.subschemeι.toLRSHom.toShHom) (hAJ.trans hJ')) ≪≫
        Stacks.ClosedImmersion.idealSheafIsoOfSquare (F.mapIso aS) (F.mapIso e) _ _ hcomm
    exact isRelativelyAmple_comp_of_iso e (blowUpToBase I) (exceptionalIdealModule I) _ ε hamp

/-! ### Domination by smooth blow-ups -/

/-- A blow-up sequence of `Y` with smooth centres and birational composite factors through
`r : Z ≅ Bl_I Y ⟶ Y`. -/
private theorem exists_closedBlowupSequence_isSmooth_comp_eq_toBase {k : Type u} [Field k]
    [CharZero k] {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (hY : IsQuasiProjectiveVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY) (r : Z ⟶ Y)
    (I : Y.IdealSheafData) (e : Z ≅ blowUp I)
    (hI : ∀ y, IsDivisorFree (IdealSheafData.stalk I y)) (he : e.hom ≫ blowUpToBase I = r) :
    ∃ (B : ClosedBlowupSequence Y) (g : B.target ⟶ Z), B.IsSmooth sY ∧
      MMP.Mori.IsBirationalMorphism B.toBase ∧ g ≫ r = B.toBase := by
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  have hIbot : I ≠ ⊥ := by
    rintro rfl
    exact (hI (genericPoint Y)).1 (by simp [IdealSheafData.stalk])
  obtain ⟨ht, hvar⟩ := isVariety_and_isProjective_toBase_truncate_canonicalPrincipalization sY
    hY.toIsVariety hYs I hIbot
  obtain ⟨h1, h2, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  set B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
  have hB := hvar B.length
  rw [truncate_length] at hB
  obtain ⟨hBv, -, hBb, hBs⟩ := hB
  haveI : LocallyOfFiniteType (B.toBase ≫ sY) := hBv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian (B.toBase ≫ sY)
  haveI : Smooth (B.toBase ≫ sY) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hBs
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap B.toBase) := by
    refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun x _ => ?_
    obtain ⟨n, z, c, hz, hspan⟩ := h2 _ ht x
    haveI := isRegularLocalRing_stalk_of_smooth_over_field (B.toBase ≫ sY) x
    haveI : IsDomain (B.target.presheaf.stalk x) := IsRegularLocalRing.isDomain _
    refine ⟨∏ i, z i ^ c i, IsRegular.of_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ =>
      pow_ne_zero _ (ne_zero_of_isRegularSystemOfParameters hz i)), hspan⟩
  refine ⟨B, blowUpLift I B.toBase hcart ≫ e.inv, (h1 _ ht).1, hBb, ?_⟩
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, blowUpLift_comp]

end Proof_lem_mmp_conductor_smooth_target_blowup

namespace MMP.Resolution

open Proof_lem_mmp_conductor_smooth_target_blowup

/-- **A projective birational morphism onto a smooth variety is an ideal blow-up.** Let `Y` be a
smooth quasi-projective variety over a field `k` of characteristic zero and `r : Z ⟶ Y` a
projective birational morphism with `Z` integral. Then
1. there is an ideal sheaf `I` on `Y` whose cosupport has codimension at least two, and an
   isomorphism `Z ≅ blowUp I` over `Y`;
2. there is an effective Cartier divisor `A` on `Z` with support `MMP.Mori.exceptionalSet r` and
   `-A` relatively ample over `Y`;
3. there is a blow-up sequence of `Y` with smooth centres whose composite is birational and
   factors through `r`. -/
@[mmp "lem_mmp_conductor_smooth_target_blowup"]
public theorem exists_iso_blowUp_of_isSmoothScheme {k : Type u} [Field k] [CharZero k]
    {Y Z : Scheme.{u}} [IsIntegral Z] (sY : Y ⟶ Spec (.of k))
    (hY : IsQuasiProjectiveVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY) (r : Z ⟶ Y)
    (hr : IsProjectiveMorphism r) (hrb : MMP.Mori.IsBirationalMorphism r) :
    (∃ (I : Y.IdealSheafData) (e : Z ≅ blowUp I),
      (∀ y ∈ I.support, 2 ≤ ringKrullDim (Y.presheaf.stalk y)) ∧
        e.hom ≫ blowUpToBase I = r) ∧
    (∃ A : Z.CartierDivisor, MMP.Intersection.IsEffective A ∧
      MMP.Intersection.cartierSupport A = (MMP.Mori.exceptionalSet r : Set Z) ∧
      IsRelativelyAmpleCartier r (-A)) ∧
    ∃ (B : ClosedBlowupSequence Y) (g : B.target ⟶ Z), B.IsSmooth sY ∧
      MMP.Mori.IsBirationalMorphism B.toBase ∧ g ≫ r = B.toBase := by
  haveI : IsIntegral Y := hY.toIsVariety.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sY hYs
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    fun y => isRegularLocalRing_stalk_of_smooth_over_field sY y
  have hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    fun y => IsRegularLocalRing.uniqueFactorizationMonoid _
  obtain ⟨n, i, hi, hir⟩ := hr
  obtain ⟨I, e, hI, he⟩ := exists_iso_blowUp_of_isClosedImmersion hUFD r i hir hrb
  refine ⟨⟨I, e, fun y hy => ?_, he⟩,
    exists_isEffective_cartierSupport_eq_exceptionalSet r I e hI he,
    exists_closedBlowupSequence_isSmooth_comp_eq_toBase sY hY hYs r I e hI he⟩
  haveI := hreg y
  haveI : IsDomain (Y.presheaf.stalk y) := IsRegularLocalRing.isDomain _
  exact (hI y).two_le_ringKrullDim fun h =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support I y).1 h hy

end MMP.Resolution

end ConductorBlowup

end
