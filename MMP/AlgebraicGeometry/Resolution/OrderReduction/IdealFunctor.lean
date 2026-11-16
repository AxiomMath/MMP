module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Resolution.BirationalTransformIdeal
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientIdeal
import MMP.AlgebraicGeometry.Resolution.OrderReduction.BdFunctorSmoothPullback
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaximalContactStep
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Resolution.MaximalContact.OnePlusBInvariance
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.TuningOfIdeals
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealOrder
import MMP.AlgebraicGeometry.Resolution.LinearBlowupCharts
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DBalancedLogDerivative
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction

/-!
# The order reduction functor `𝓑𝓞_{n,m}` for ideals

Let `𝓜` be a marked order-reduction family on dimensions `0, …, n - 1` and `m ≥ 1`. For a triple
`(X, I, E)` with `dim X = n` and `maxord I ≤ m`, the functor `𝓑𝓞_{n,m}` is obtained by gluing
the local sequences `𝓑_{n,m}` on surjective open cover maps `g : X^* → X` along which
`(X^*, g^*I, g⁻¹E)` is a local triple. This file proves that the gluing exists and that
`𝓑𝓞_{n,m}` has the properties of Kollár's Thm. 3.103:

* its pull-back along every such cover is the local sequence (Step 3 of the proof);
* it is a smooth blow-up sequence of order `m` without empty blow-ups, and it reduces the maximal
  order below `m` (part (1));
* it commutes with smooth morphisms and with change of fields (part (2));
* along a smooth hypersurface carrying the ideal, it is the push-forward of `𝓜_{n-1,1}` on the
  hypersurface (part (3)), as is `𝓑𝓞^Y_1` (Thm. 3.104 Step 2.4).

Each property is checked on a cover by local triples and descends along it.

## Main results

* `MMP.Resolution.boFunctor_pullback`
* `MMP.Resolution.boFunctor_isOrderMTripleSeq`
* `MMP.Resolution.boMaximalContact_eq_pushforward_of_eq_map`
* `MMP.Resolution.boFunctor_eq_pushforward_of_eq_map`
* `MMP.Resolution.commutesWithSmoothOn_boFunctor`
* `MMP.Resolution.commutesWithFieldChangeOn_boFunctor`
* `MMP.Resolution.maxOrder_endOf_boFunctor_lt`

## Implementation notes

Open cover maps include the map from the empty scheme, along which a triple pulls back to one of
dimension `⊥`; it lies in neither `idealTriplesOfDim {n} m` nor `mcLocalTriples n m`. The
globalization of blow-up sequences is therefore applied to both classes enlarged by the triples
on empty schemes, with the empty sequence as the value there.

Kollár states `maxord I = 1` in Thm. 3.103 (3); this fails for `J_Y = 𝒪_Y`, where `I = 𝒪_X` has
maximal order `0`. In general `maxord I ≤ 1`, the identity holds in both cases, and the
hypersurface is assumed nonempty instead.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.103, Thm. 3.104]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Open cover maps -/

/-- Open cover maps, as a morphism property. -/
private abbrev openCoverMaps : MorphismProperty Scheme.{u} := fun _ _ g => IsOpenCoverMap g

set_option backward.isDefEq.respectTransparency false in
/-- An open cover map is étale. -/
private theorem etale_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) : Etale g := by
  obtain ⟨n, U, -, hU, hi⟩ := hg
  exact IsZariskiLocalAtSource.of_iSup_eq_top U hU fun a => inferInstance

/-- An open cover map is smooth. -/
private theorem smooth_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) : Smooth g :=
  have := etale_of_isOpenCoverMap hg
  inferInstance

/-- The base change of an open cover map is an open cover map. -/
private theorem isOpenCoverMap_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsOpenCoverMap g) :
    IsOpenCoverMap g' := by
  obtain ⟨n, U, hd, hU, hi⟩ := hg
  refine ⟨n, fun a => f' ⁻¹ᵁ U a, fun a b hab => ?_, ?_, fun a => ?_⟩
  · show Disjoint _ _
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.1 (hd hab),
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  · have hpb := (isPullback_morphismRestrict f' (U a)).flip.paste_horiz sq.flip
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip (hi a)

/-- An open cover map, with the pieces indexed by a finite type. -/
private theorem isOpenCoverMap_of_fintype {X' X : Scheme.{u}} {g : X' ⟶ X} {ι : Type*} [Fintype ι]
    (U : ι → X'.Opens) (hd : Pairwise (fun a b => Disjoint (U a) (U b))) (hU : (⨆ a, U a) = ⊤)
    (hi : ∀ a, IsOpenImmersion ((U a).ι ≫ g)) : IsOpenCoverMap g := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun a => U (e.symm a), fun a b hab => hd (e.symm.injective.ne hab),
    ?_, fun a => hi _⟩
  rw [← hU]
  exact e.symm.iSup_comp (g := U)

private theorem isOpenCoverMap_comp {X'' X' X : Scheme.{u}} {f : X'' ⟶ X'} {g : X' ⟶ X}
    (hf : IsOpenCoverMap f) (hg : IsOpenCoverMap g) : IsOpenCoverMap (f ≫ g) := by
  obtain ⟨s, V, hVd, hV, hVi⟩ := hf
  obtain ⟨r, U, hUd, hU, hUi⟩ := hg
  let W : Fin r × Fin s → X''.Opens := fun p => V p.2 ⊓ f ⁻¹ᵁ U p.1
  refine ⟨r * s, fun i => W (finProdFinEquiv.symm i), fun i j hij => ?_, ?_, fun i => ?_⟩
  · have hne : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j :=
      fun e => hij (finProdFinEquiv.symm.injective e)
    dsimp only
    generalize finProdFinEquiv.symm i = p at hne ⊢
    generalize finProdFinEquiv.symm j = q at hne ⊢
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    by_cases hb : b = d
    · subst hb
      have hac : a ≠ c := fun e => hne (by rw [e])
      have := hUd hac
      refine Disjoint.mono inf_le_right inf_le_right ?_
      rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.1 this, Scheme.Hom.preimage_bot]
    · exact Disjoint.mono inf_le_left inf_le_left (hVd hb)
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⨆ b, V b) := hV ▸ trivial
    have hfx : f x ∈ (⨆ a, U a) := hU ▸ trivial
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hfx
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨finProdFinEquiv (a, b), by
        show x ∈ W (finProdFinEquiv.symm (finProdFinEquiv (a, b)))
        rw [Equiv.symm_apply_apply]; exact ⟨hb, ha⟩⟩
  · dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, b⟩ := p
    have e : (W (a, b)).ι = X''.homOfLE inf_le_left ≫ (V b).ι := (Scheme.homOfLE_ι _ _).symm
    have h1 : IsOpenImmersion ((W (a, b)).ι ≫ f) := by
      rw [e, Category.assoc]; infer_instance
    have hr : Set.range ((W (a, b)).ι ≫ f) ⊆ Set.range (U a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      have hy : (W (a, b)).ι y ∈ W (a, b) := by
        have : (W (a, b)).ι y ∈ Set.range (W (a, b)).ι := ⟨y, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      exact hy.2
    let l := IsOpenImmersion.lift (U a).ι ((W (a, b)).ι ≫ f) hr
    have hl : l ≫ (U a).ι = (W (a, b)).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion l := by
      have : IsOpenImmersion (l ≫ (U a).ι) := hl ▸ h1
      exact IsOpenImmersion.of_comp l (U a).ι
    rw [← Category.assoc, ← hl, Category.assoc]
    infer_instance

private theorem isOpenCoverMap_sigmaDesc {X : Scheme.{u}} (n : ℕ) (U : Fin n → Scheme.{u})
    (g : ∀ i, U i ⟶ X) (hg : ∀ i, IsOpenCoverMap (g i)) : IsOpenCoverMap (Sigma.desc g) := by
  choose t P hPd hP hPi using hg
  let Q : (Σ i : Fin n, Fin (t i)) → (∐ U).Opens := fun p => Sigma.ι U p.1 ''ᵁ P p.1 p.2
  have hQ : ∀ p : Σ i : Fin n, Fin (t i), ∀ x, x ∈ Q p ↔ ∃ y ∈ P p.1 p.2, Sigma.ι U p.1 y = x :=
    fun p x => Iff.rfl
  refine isOpenCoverMap_of_fintype Q (fun p q hpq => ?_) ?_ (fun p => ?_)
  · show Disjoint (Q p) (Q q)
    by_cases h : p.1 = q.1
    · obtain ⟨i, a⟩ := p
      obtain ⟨j, b⟩ := q
      dsimp only at h
      subst h
      have hab : a ≠ b := fun e => hpq (by rw [e])
      rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨y, hy, rfl⟩ := (hQ _ _).1 hx1
      obtain ⟨z, hz, hzy⟩ := (hQ _ _).1 hx2
      obtain rfl := (Sigma.ι U i).isOpenEmbedding.injective hzy
      exact (disjoint_iff.1 (hPd i hab)).le ⟨hy, hz⟩
    · exact Disjoint.mono (Scheme.Hom.image_le_opensRange _ _) (Scheme.Hom.image_le_opensRange _ _)
        (disjoint_opensRange_sigmaι U _ _ h)
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ i, ((sigmaOpenCover U).f i).opensRange := by
      rw [Scheme.OpenCover.iSup_opensRange]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, rfl⟩ := hi
    have hy : y ∈ ⨆ a, P i a := by rw [hP i]; trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, a⟩, (hQ _ _).2 ⟨y, ha, rfl⟩⟩
  · obtain ⟨i, a⟩ := p
    show IsOpenImmersion ((Sigma.ι U i ''ᵁ P i a).ι ≫ Sigma.desc g)
    rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc, Sigma.ι_desc]
    have := hPi i a
    infer_instance

/-- An open immersion is an open cover map, with the single piece `⊤`. -/
private theorem isOpenCoverMap_of_isOpenImmersion {X' X : Scheme.{u}} (g : X' ⟶ X)
    [IsOpenImmersion g] : IsOpenCoverMap g :=
  isOpenCoverMap_of_fintype (ι := Unit) (fun _ => ⊤) (fun a b hab => (hab rfl).elim)
    (iSup_const) (fun _ => inferInstance)

/-- The order of an ideal sheaf is preserved by pull-back along an open immersion. -/
private theorem multAt_comap_of_isOpenImmersion {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] (J : Y.IdealSheafData) (y : Y') :
    multAt (J.comap f) y = multAt J (f y) := by
  rw [multAt, multAt, IdealSheafData.stalk_comap]
  exact MMP.Threefold.Resolution.idealOrder_map_ringEquiv
    (RingEquiv.ofBijective (f.stalkMap y).hom (ConcreteCategory.bijective_of_isIso _)) _

/-- The order of an ideal sheaf is preserved by pull-back along an open cover map. -/
private theorem multAt_comap_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (I : X.IdealSheafData) (y : X') :
    multAt (I.comap g) y = multAt I (g y) := by
  obtain ⟨n, U, -, hU, hi⟩ := hg
  have hy : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have h1 := multAt_comap_of_isOpenImmersion (U a).ι (I.comap g) ⟨y, ha⟩
  have h2 := multAt_comap_of_isOpenImmersion ((U a).ι ≫ g) I ⟨y, ha⟩
  rw [Scheme.IdealSheafData.comap_comp] at h2
  exact h1.symm.trans h2

/-- `ord_x I ≤ maxord I`. -/
private theorem multAt_le_maxOrder {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    multAt I x ≤ maxOrder I :=
  le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) x (Set.mem_univ x)

/-- Pull-back along an open cover map does not raise the maximal order. -/
private theorem maxOrder_comap_le_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (I : X.IdealSheafData) :
    maxOrder (I.comap g) ≤ maxOrder I :=
  iSup₂_le fun y _ => (multAt_comap_of_isOpenCoverMap hg I y).trans_le (multAt_le_maxOrder I _)

/-- Pulling back along a surjection that preserves the order pointwise preserves the maximal
order. -/
private theorem maxOrder_comap_of_surjective {X Y : Scheme} (f : Y ⟶ X) (I : X.IdealSheafData)
    (hf : Function.Surjective f) (h : ∀ y, multAt (I.comap f) y = multAt I (f y)) :
    maxOrder (I.comap f) = maxOrder I := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_pos, h]
  exact hf.iSup_comp (multAt I)

/-- Pull-back along a surjective open cover map preserves the maximal order. -/
private theorem maxOrder_comap_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (I : X.IdealSheafData) :
    maxOrder (I.comap g) = maxOrder I :=
  maxOrder_comap_of_surjective g I hs.surj (multAt_comap_of_isOpenCoverMap hg I)

/-! ### Dimension -/

/-- The local dimension is preserved by an open cover map. -/
private theorem topologicalKrullDimAt_of_isOpenCoverMap {X' X : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (y : X') :
    topologicalKrullDimAt X' y = topologicalKrullDimAt X (g y) := by
  obtain ⟨r, U, -, hU, hi⟩ := hg
  have hy : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ((U a).ι.isOpenEmbedding.topologicalKrullDimAt_eq ⟨y, ha⟩).trans
    (((U a).ι ≫ g).isOpenEmbedding.topologicalKrullDimAt_eq ⟨y, ha⟩).symm

/-- On an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of any irreducible component. -/
private theorem topologicalKrullDimAt_eq_topologicalKrullDim_of_mem (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) {C : Set X} (hC : C ∈ irreducibleComponents X)
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- The dimension of an irreducible component is the local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    ∃ η ∈ Z, topologicalKrullDimAt X η = topologicalKrullDim Z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  refine ⟨η, hη.mem, ?_⟩
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s η]
  refine le_antisymm (iSup₂_le fun Z' hZ' => ?_)
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents X ∧ η ∈ Z'}) =>
      topologicalKrullDim Z') Z ⟨hZ, hη.mem⟩)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {η} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- A smooth scheme locally of finite type over its field, as for every triple, is smooth over
it as a morphism. -/
private theorem smooth_of_mem_triples {t : FieldBlowupTriple.{u}} (ht : t ∈ triples) :
    Smooth t.sX :=
  haveI := (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr ht.2.2.1
  (MMP.Mori.isSmoothScheme_iff _).1 ht.2.1

/-- Triples are stable under pull-back by open cover maps. -/
private theorem pullback_mem_triples_of_isOpenCoverMap (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {Y : Scheme.{u}} (h : Y ⟶ t.X) (hh : IsOpenCoverMap h) :
    t.pullback h ∈ triples := by
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  haveI : QuasiCompact t.sX := ht.2.2.2.1
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  haveI : CompactSpace t.X := (quasiCompact_iff_compactSpace t.sX).1 ‹_›
  haveI : IsNoetherian t.X := {}
  haveI : CompactSpace Y := by
    obtain ⟨r, U, -, hU, hi⟩ := hh
    refine ⟨?_⟩
    have : (Set.univ : Set Y) = ⋃ a, ((U a : Set Y)) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hU]; rfl
    rw [this]
    refine isCompact_iUnion fun a => ?_
    have hc : IsCompact (Set.range ((U a).ι ≫ h)) :=
      NoetherianSpace.isCompact _
    have hemb := ((U a).ι ≫ h).isOpenEmbedding
    have : IsCompact (Set.univ : Set (U a)) := by
      rwa [hemb.isInducing.isCompact_iff, Set.image_univ]
    simpa using this.image (U a).ι.continuous
  haveI : QuasiCompact (h ≫ t.sX) := quasiCompact_of_compactSpace _
  refine mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) h, ?_⟩
  intro W hW W' hW'
  obtain ⟨η, -, hη⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k (h ≫ t.sX) hW
  obtain ⟨η', -, hη'⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k (h ≫ t.sX) hW'
  have hC := irreducibleComponent_mem_irreducibleComponents (h η)
  refine hη.symm.trans (Eq.trans ?_ hη')
  rw [topologicalKrullDimAt_of_isOpenCoverMap hh,
    topologicalKrullDimAt_of_isOpenCoverMap hh,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_mem t.k t.sX ht.2.2.2.2.1 hC,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_mem t.k t.sX ht.2.2.2.2.1 hC]

/-- On a triple of dimension `n`, the local dimension at every point is `n`. -/
private theorem topologicalKrullDimAt_eq_of_hasDimensionIn {n : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hd : HasDimensionIn t.X {n}) (x : t.X) :
    topologicalKrullDimAt t.X x = ((n : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨n', rfl, hn'⟩ := hd
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  have hC := irreducibleComponent_mem_irreducibleComponents x
  rw [topologicalKrullDimAt_eq_topologicalKrullDim_of_mem t.k t.sX ht.2.2.2.2.1 hC, ← hn',
    topologicalKrullDim_eq_iSup_irreducibleComponents t.X]
  refine le_antisymm (le_iSup₂ (f := fun W (_ : W ∈ irreducibleComponents t.X) =>
    topologicalKrullDim W) _ hC) (iSup₂_le fun W hW => (ht.2.2.2.2.1 W hW _ hC).le)

/-- A nonempty scheme locally of finite type over a field whose local dimension is `n` at every
point has dimension `n`. -/
private theorem hasDimensionIn_of_forall_topologicalKrullDimAt {n : ℕ} (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [Nonempty X]
    (hX : ∀ x : X, topologicalKrullDimAt X x = ((n : ℕ∞) : WithBot ℕ∞)) :
    HasDimensionIn X {n} := by
  refine ⟨n, Set.mem_singleton n, ?_⟩
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine le_antisymm ?_
    ((hX x₀).symm.le.trans (_root_.topologicalKrullDimAt_le_topologicalKrullDim x₀))
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup₂_le fun W hW => ?_
  obtain ⟨x, hxW⟩ := hW.1.nonempty
  rw [← hX x, topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  exact le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
    topologicalKrullDim D) W ⟨hW, hxW⟩

/-- A nonempty scheme with an open cover map to an equidimensional scheme of dimension `n`, of
finite type over a field, has dimension `n`. -/
private theorem hasDimensionIn_of_isOpenCoverMap {n : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hd : HasDimensionIn t.X {n}) {Y : Scheme.{u}} [Nonempty Y]
    (h : Y ⟶ t.X) (hh : IsOpenCoverMap h) : HasDimensionIn Y {n} := by
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  exact hasDimensionIn_of_forall_topologicalKrullDimAt t.k (h ≫ t.sX) fun y =>
    (topologicalKrullDimAt_of_isOpenCoverMap hh y).trans
      (topologicalKrullDimAt_eq_of_hasDimensionIn t ht hd _)

private theorem nonempty_of_hasDimensionIn {X : Scheme.{u}} {n : ℕ} (h : HasDimensionIn X {n}) :
    Nonempty X := by
  obtain ⟨d, -, hd⟩ := h
  by_contra hX
  rw [not_nonempty_iff] at hX
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty X).mpr hX] at hd
  exact WithBot.bot_ne_coe hd

/-- The dimension of a scheme of dimension `n ≥ 1` is at least one. -/
private theorem one_le_topologicalKrullDim {X : Scheme.{u}} {n : ℕ} (hn : 1 ≤ n)
    (hd : HasDimensionIn X {n}) : 1 ≤ topologicalKrullDim X := by
  obtain ⟨n', rfl, hn'⟩ := hd
  rw [hn']
  exact_mod_cast hn

/-- On an equidimensional space of dimension `≥ 1` every irreducible component has positive
dimension. -/
private theorem pos_topologicalKrullDim_of_mem_irreducibleComponents {T : Type*}
    [TopologicalSpace T] (he : TopologicalSpace.Equidimensional T)
    (hd : 1 ≤ topologicalKrullDim T) :
    ∀ Z ∈ irreducibleComponents T, 0 < topologicalKrullDim Z := by
  intro Z hZ
  by_contra hle
  rw [not_lt] at hle
  have : topologicalKrullDim T ≤ 0 := by
    rw [topologicalKrullDim_eq_iSup_irreducibleComponents T]
    exact iSup₂_le fun W hW => (he W hW Z hZ) ▸ hle
  exact absurd (hd.trans this) (by decide)

/-- Every irreducible component of an equidimensional scheme of dimension `n ≥ 1` has positive
dimension. -/
private theorem pos_dim_of_mem_irreducibleComponents {n : ℕ} (hn : 1 ≤ n)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hd : HasDimensionIn t.X {n}) :
    ∀ Z ∈ irreducibleComponents t.X, 0 < topologicalKrullDim Z :=
  pos_topologicalKrullDim_of_mem_irreducibleComponents ht.2.2.2.2.1
    (one_le_topologicalKrullDim hn hd)

/-! ### Derivative ideals under smooth pull-back -/

/-- Higher derivative ideals commute with smooth pull-back. -/
private theorem higherDerivativeIdeal_comap_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] (f : Y ⟶ X) [Smooth f]
    (hf : f ≫ sX = sY) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal sY (I.comap f) r = (higherDerivativeIdeal sX I r).comap f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih,
      derivativeIdeal_comap_of_smooth sX sY f hf hdim]

/-- The maximal contact ideal commutes with smooth pull-back preserving the maximal order. -/
private theorem maximalContactIdeal_comap_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] (f : Y ⟶ X) [Smooth f]
    (hf : f ≫ sX = sY) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (hI : maxOrder (I.comap f) = maxOrder I) :
    maximalContactIdeal sY (I.comap f) = (maximalContactIdeal sX I).comap f := by
  rw [maximalContactIdeal, maximalContactIdeal, hI,
    higherDerivativeIdeal_comap_of_smooth sX sY f hf hdim]

/-! ### Pull-backs of triples and of blow-up sequences -/

/-- Pulling back a triple along `a` then `b` is pulling it back along `b ≫ a`. -/
private theorem fieldBlowupTriple_pullback_pullback (t : FieldBlowupTriple.{u})
    {Y W : Scheme.{u}} (a : Y ⟶ t.X) (b : W ⟶ Y) :
    (t.pullback a).pullback b = t.pullback (b ≫ a) := by
  have h1 : (t.I.comap a).comap b = t.I.comap (b ≫ a) :=
    (Scheme.IdealSheafData.comap_comp _ _ _).symm
  have h2 : (fun i => ((t.E.E i).comap a).comap b) = fun i => (t.E.E i).comap (b ≫ a) :=
    funext fun i => (Scheme.IdealSheafData.comap_comp _ _ _).symm
  unfold FieldBlowupTriple.pullback OrderedDivisor.comap
  dsimp only
  rw [h1, h2, Category.assoc]

private theorem fieldBlowupTriple_pullback_id (t : FieldBlowupTriple.{u}) :
    t.pullback (𝟙 t.X) = t := by
  obtain ⟨⟨X, I, ⟨s, E⟩⟩, k, sX⟩ := t
  have h1 : I.comap (𝟙 X) = I := Scheme.IdealSheafData.comap_id I
  have h2 : (fun i => (E i).comap (𝟙 X)) = E := funext fun i => Scheme.IdealSheafData.comap_id _
  change FieldBlowupTriple.mk ⟨X, I.comap (𝟙 X), ⟨s, fun i => (E i).comap (𝟙 X)⟩⟩ k (𝟙 X ≫ sX) = _
  rw [h1, h2, Category.id_comp]

/-- `k^*(h^*𝐁) = (h ∘ k)^*𝐁`. -/
private theorem pullback_pullback {X Y W : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) (k : W ⟶ Y) : (B.pullback h).pullback k = B.pullback (k ≫ h) :=
  eq_of_heq (B.pullback_pullback_heq h k (k ≫ h) rfl (by simp))

/-- A blow-up sequence without empty blow-ups is its own pull-back along the identity. -/
private theorem pullback_id_of_hasNoEmptyBlowups {X : Scheme.{u}} {S : ClosedBlowupSequence X}
    (hS : S.HasNoEmptyBlowups) : S.pullback (𝟙 X) = S :=
  calc S.pullback (𝟙 X) = (S.pullback (𝟙 X)).reduction :=
        (ClosedBlowupSequence.reduction_eq_self
          (ClosedBlowupSequence.hasNoEmptyBlowups_pullback S hS (𝟙 X))).symm
    _ = S.reduction := ClosedBlowupSequence.reduction_pullback S (𝟙 X)
    _ = S := ClosedBlowupSequence.reduction_eq_self hS

/-- If a centre is empty, so is its pull-back: hence `HasNoEmptyBlowups` descends along any
morphism. -/
private theorem hasNoEmptyBlowups_of_pullback {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X), (B.pullback g).HasNoEmptyBlowups → B.HasNoEmptyBlowups := by
  induction B with
  | nil X => intros; trivial
  | cons Z B ih =>
    intro Y g h
    refine ⟨fun hZ => h.1 ?_, ih _ h.2⟩
    subst hZ
    exact Scheme.IdealSheafData.comap_top g

/-! ### Local triples under open cover maps -/

/-- The codimension of an irreducible closed subset of the source of an open immersion is that of
its closure in the target. -/
private theorem codimension_map_of_isOpenImmersion {X₀ X : Scheme.{u}} (j : X₀ ⟶ X)
    [IsOpenImmersion j] (W : IrreducibleCloseds X₀) :
    codimension (IrreducibleCloseds.map j j.continuous W) = codimension W := by
  have hf := j.isOpenEmbedding
  rw [codimension_eq_coheight, codimension_eq_coheight]
  refine (Order.coheight_eq_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing) ?_ _).symm
  intro a b hab
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding j hf
  have hb : (j ⁻¹' (b : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨x, hab.le (subset_closure ⟨x, hx, rfl⟩)⟩
  refine ⟨e.symm ⟨b, hb⟩, ?_, ?_⟩
  · rw [← e.lt_iff_lt, OrderIso.apply_symm_apply]
    exact hab
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)

/-- An irreducible subset of the source of an open cover map lies in one of its pieces. -/
private theorem exists_subset_of_isIrreducible {X : Scheme.{u}} {r : ℕ} {U : Fin r → X.Opens}
    (hd : Pairwise (fun a b => Disjoint (U a) (U b))) (hU : (⨆ a, U a) = ⊤) {T : Set X}
    (hT : IsIrreducible T) {y : X} (hy : y ∈ T) (a : Fin r) (ha : y ∈ U a) :
    T ⊆ U a := by
  intro z hz
  have hz' : z ∈ ⨆ b, U b := hU ▸ trivial
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hz'
  by_cases hab : a = b
  · exact hab ▸ hb
  obtain ⟨w, -, hwa, hwb⟩ := hT.isPreirreducible _ _ (U a).2 (U b).2 ⟨y, hy, ha⟩ ⟨z, hz, hb⟩
  exact absurd (show w ∈ U a ⊓ U b from ⟨hwa, hwb⟩)
    (by rw [disjoint_iff.1 (hd hab)]; exact fun h => h)

/-- The preimage of a smooth hypersurface under an open cover map is a smooth hypersurface. -/
private theorem isSmoothHypersurface_comap_of_isOpenCoverMap (t : FieldBlowupTriple.{u})
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) (hh : IsOpenCoverMap h) :
    IsSmoothHypersurface (h ≫ t.sX) (H.comap h) := by
  obtain ⟨hHs, hHc⟩ := hH
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  refine ⟨?_, ?_⟩
  · haveI := MMP.Mori.IsSmoothScheme.smooth hHs
    have he : (H.comap h).subschemeι ≫ h ≫ t.sX =
        (H.comapIso h).hom ≫ Limits.pullback.snd h H.subschemeι ≫ H.subschemeι ≫ t.sX := by
      rw [← H.comapIso_hom_fst h, Category.assoc, Limits.pullback.condition_assoc]
    rw [he]
    exact MMP.Mori.isSmoothScheme_of_smooth inferInstance
  · intro W₀ hW₀
    obtain ⟨r, U, hUd, hU, hi⟩ := hh
    -- `W₀` lies in a single piece `U a`.
    obtain ⟨y, hy⟩ := W₀.isIrreducible.nonempty
    have hy' : y ∈ ⨆ a, U a := hU ▸ trivial
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
    have hsub : (W₀ : Set Y) ⊆ U a :=
      exists_subset_of_isIrreducible hUd hU W₀.isIrreducible hy a ha
    let j := (U a).ι
    let ψ := (U a).ι ≫ h
    haveI : IsOpenImmersion ψ := hi a
    let ej := IrreducibleCloseds.orderIsoOfIsOpenEmbedding j j.isOpenEmbedding
    let eψ := IrreducibleCloseds.orderIsoOfIsOpenEmbedding ψ ψ.isOpenEmbedding
    have hne : (j ⁻¹' (W₀ : Set Y)).Nonempty := ⟨⟨y, ha⟩, hy⟩
    let V₀ := ej.symm ⟨W₀, hne⟩
    have hV₀ : IrreducibleCloseds.map j j.continuous V₀ = W₀ :=
      congrArg Subtype.val (ej.apply_symm_apply ⟨W₀, hne⟩)
    have hV₀set : (V₀ : Set (U a)) = j ⁻¹' W₀ := rfl
    let W := IrreducibleCloseds.map ψ ψ.continuous V₀
    have hWH : (W : Set t.X) ⊆ H.support := by
      refine closure_minimal ?_ H.support.2
      rintro _ ⟨v, hv, rfl⟩
      exact (mem_support_comap_iff h H (j v)).1 (hW₀.prop hv)
    have hWmax : Maximal (fun W' : IrreducibleCloseds t.X ↦ (W' : Set t.X) ⊆ H.support) W := by
      refine ⟨hWH, fun W' hW' hWW' => ?_⟩
      have hne' : (ψ ⁻¹' (W' : Set t.X)).Nonempty :=
        ⟨⟨y, ha⟩, hWW' (subset_closure ⟨⟨y, ha⟩, hy, rfl⟩)⟩
      let V' := eψ.symm ⟨W', hne'⟩
      have hV' : IrreducibleCloseds.map ψ ψ.continuous V' = W' :=
        congrArg Subtype.val (eψ.apply_symm_apply ⟨W', hne'⟩)
      have hV'set : (V' : Set (U a)) = ψ ⁻¹' W' := rfl
      have hle : V₀ ≤ V' := fun v hv => by
        show ψ v ∈ (W' : Set t.X)
        exact hWW' (subset_closure ⟨v, hv, rfl⟩)
      have h1 : W₀ ≤ IrreducibleCloseds.map j j.continuous V' :=
        hV₀ ▸ IrreducibleCloseds.map_mono j.continuous hle
      have h2 : ((IrreducibleCloseds.map j j.continuous V' : IrreducibleCloseds Y) : Set Y) ⊆
          (H.comap h).support := by
        refine closure_minimal ?_ (H.comap h).support.2
        rintro _ ⟨v, hv, rfl⟩
        rw [hV'set] at hv
        exact (mem_support_comap_iff h H (j v)).2 (hW' hv)
      have h3 := hW₀.2 h2 h1
      have h4 : V' ≤ V₀ := fun v hv => by
        show j v ∈ (W₀ : Set Y)
        exact h3 (subset_closure ⟨v, hv, rfl⟩)
      rw [← hV']
      exact IrreducibleCloseds.map_mono ψ.continuous h4
    have := hHc W hWmax
    rwa [codimension_map_of_isOpenImmersion ψ V₀, ← codimension_map_of_isOpenImmersion j V₀,
      hV₀] at this

/-- Step (ii'): local triples are stable under pull-back by open cover maps with nonempty
source. -/
private theorem pullback_mem_mcLocalTriples {n m : ℕ} (hn : 1 ≤ n) (t : FieldBlowupTriple.{u})
    (ht : t ∈ mcLocalTriples n m) {Y : Scheme.{u}} [Nonempty Y] (h : Y ⟶ t.X)
    (hh : IsOpenCoverMap h) :
    t.pullback h ∈ mcLocalTriples n m := by
  obtain ⟨htr, hd, hle, hmc⟩ := ht
  have hle' : maxOrder (t.I.comap h) ≤ maxOrder t.I := maxOrder_comap_le_of_isOpenCoverMap hh t.I
  refine ⟨pullback_mem_triples_of_isOpenCoverMap t htr h hh,
    hasDimensionIn_of_isOpenCoverMap (Y := Y) t htr hd h hh, hle'.trans hle, ?_⟩
  rcases (hle'.trans hle).lt_or_eq with hlt | heq
  · exact Or.inl hlt
  refine Or.inr ⟨heq, ?_⟩
  have hmI : maxOrder t.I = m := le_antisymm hle (heq ▸ hle')
  obtain ⟨H, hHs, hHle⟩ := hmc.resolve_left hmI.not_lt |>.2
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  haveI : Smooth t.sX := smooth_of_mem_triples htr
  refine ⟨H.comap h, isSmoothHypersurface_comap_of_isOpenCoverMap t hHs h hh, ?_⟩
  change H.comap h ≤ maximalContactIdeal (h ≫ t.sX) (t.I.comap h)
  rw [maximalContactIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl
    (pos_dim_of_mem_irreducibleComponents hn t htr hd) t.I (heq.trans hmI.symm)]
  exact Scheme.IdealSheafData.comap_mono h hHle

/-! ### Gluing along finite disjoint open covers -/

/-- A property local at the source holds for `f` if it holds on the nonempty members of a
family of open immersions covering the source. -/
private theorem of_forall_exists_isOpenImmersion (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type*} {V : ι → Scheme.{u}}
    (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)] (hpt : ∀ x : X, ∃ i, ∃ v : V i, j i v = x)
    (h : ∀ i, Nonempty (V i) → P (j i ≫ f)) : P f := by
  choose i v hv using hpt
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x => (j (i x)).opensRange)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, ⟨v x, hv x⟩⟩) fun x => ?_
  have e : (j (i x)).opensRange.ι = (j (i x)).isoOpensRange.inv ≫ j (i x) := by
    rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e, Category.assoc]
  exact MorphismProperty.RespectsIso.precomp P _ _ (h _ ⟨v x⟩)

/-- Nonvanishing of `I` at the generic points of the irreducible components holds as soon as
it holds on the members of an open cover. -/
private theorem isNonzeroAtGenericPoints_of_forall_exists_isOpenImmersion {X : Scheme.{u}}
    (I : X.IdealSheafData) {ι : Type*} {V : ι → Scheme.{u}} (j : ∀ i, V i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hpt : ∀ x : X, ∃ i, ∃ v : V i, j i v = x)
    (hV : ∀ i, Nonempty (V i) → IsNonzeroAtGenericPoints (I.comap (j i))) :
    IsNonzeroAtGenericPoints I := by
  intro η hη h0
  obtain ⟨i, v, rfl⟩ := hpt η
  have hemb := (j i).isOpenEmbedding
  have hv : closure ({v} : Set (V i)) ∈ irreducibleComponents (V i) := by
    rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hη hemb ⟨_, subset_closure rfl, v, rfl⟩
  refine hV i ⟨v⟩ v hv ?_
  rw [IdealSheafData.stalk_comap, h0, Ideal.map_bot]

/-- The ordered snc condition on `E` glues along a finite open cover. -/
private theorem isOrderedSNC_of_disjoint_cover (t : FieldBlowupTriple.{u}) [CharZero t.k]
    [LocallyOfFiniteType t.sX] (N : ℕ)
    (V : Fin N → Scheme.{u}) (j : ∀ i, V i ⟶ t.X) (hj : ∀ i, IsOpenImmersion (j i))
    (hcov : (⋃ i, Set.range (j i)) = Set.univ)
    (hV : ∀ i, t.pullback (j i) ∈ triples ∨ IsEmpty (V i)) :
    t.E.IsOrderedSNC t.sX := by
  have hpt := Set.iUnion_eq_univ_iff.1 hcov
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have hcoord : ∀ x : t.X, ∃ (n : ℕ) (z : Fin n → t.X.presheaf.stalk x)
      (c : {i // x ∈ (t.E.E i).support} → Fin n), MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (t.E.E i.1) x = Ideal.span {z (c i)}) ∧
          Function.Injective c := by
    intro x
    obtain ⟨i, v, rfl⟩ := hpt x
    haveI := hj i
    have htr : t.pullback (j i) ∈ triples := (hV i).resolve_right (@not_isEmpty_of_nonempty _ ⟨v⟩)
    obtain ⟨n, z, c, hz, hc, hinj⟩ : ∃ (n : ℕ) (z : Fin n → (V i).presheaf.stalk v)
        (c : {k // v ∈ ((t.E.E k).comap (j i)).support} → Fin n),
        MMP.Mori.IsRegularSystemOfParameters z ∧
          (∀ k, IdealSheafData.stalk ((t.E.E k.1).comap (j i)) v = Ideal.span {z (c k)}) ∧
            Function.Injective c := htr.2.2.2.2.2.2.2.2 v
    let e : t.X.presheaf.stalk (j i v) ≃+* (V i).presheaf.stalk v :=
      RingEquiv.ofBijective ((j i).stalkMap v).hom (ConcreteCategory.bijective_of_isIso _)
    have hmem : ∀ k : {k // j i v ∈ (t.E.E k).support},
        v ∈ ((t.E.E k.1).comap (j i)).support :=
      fun k => (mem_support_comap_iff _ _ _).2 k.2
    refine ⟨n, fun a => e.symm (z a), fun k => c ⟨k.1, hmem k⟩,
      isRegularSystemOfParameters_map_ringEquiv e.symm hz, fun k => ?_, fun a b hab => ?_⟩
    · have h1 : IdealSheafData.stalk ((t.E.E k.1).comap (j i)) v =
          Ideal.span {z (c ⟨k.1, hmem k⟩)} := hc ⟨k.1, hmem k⟩
      have h2 : IdealSheafData.stalk ((t.E.E k.1).comap (j i)) v =
          Ideal.map (e : _ →+* _) (IdealSheafData.stalk (t.E.E k.1) (j i v)) :=
        IdealSheafData.stalk_comap _ _ _
      have h3 := congrArg (Ideal.map (e.symm.toRingHom)) (h2.symm.trans h1)
      rw [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv, Ideal.map_span, Set.image_singleton] at h3
      exact h3
    · exact Subtype.ext (congrArg Subtype.val (hinj hab) :)
  have hpar : ∀ i, ∀ y ∈ (t.E.E i).support, ∃ (n : ℕ) (w : Fin n → t.X.presheaf.stalk y)
      (a : Fin n), MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (t.E.E i) y = Ideal.span {w a} := by
    intro i y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hcoord y
    exact ⟨n, z, c ⟨i, hy⟩, hz, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter t.sX _ (hpar i)⟩, hcoord⟩

set_option backward.isDefEq.respectTransparency false in
/-- The conditions of a triple glue along a finite disjoint open cover by triples of one
dimension `n`. -/
private theorem mem_triples_of_disjoint_cover {n : ℕ} (t : FieldBlowupTriple.{u}) [Nonempty t.X]
    (N : ℕ) (V : Fin N → Scheme.{u}) (j : ∀ i, V i ⟶ t.X) (hj : ∀ i, IsOpenImmersion (j i))
    (hd : Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))))
    (hcov : (⋃ i, Set.range (j i)) = Set.univ)
    (hV : ∀ i, (t.pullback (j i) ∈ triples ∧ HasDimensionIn (V i) {n}) ∨ IsEmpty (V i)) :
    t ∈ triples := by
  have hpt := Set.iUnion_eq_univ_iff.1 hcov
  have hV'' : ∀ i, Nonempty (V i) → t.pullback (j i) ∈ triples ∧ HasDimensionIn (V i) {n} :=
    fun i hi => (hV i).resolve_right (not_isEmpty_of_nonempty _)
  have hV' : ∀ i, Nonempty (V i) → t.pullback (j i) ∈ triples := fun i hi => (hV'' i hi).1
  haveI := hj
  obtain ⟨x₀⟩ := ‹Nonempty t.X›
  obtain ⟨i₀, v₀, -⟩ := hpt x₀
  have hLFT : LocallyOfFiniteType t.sX :=
    of_forall_exists_isOpenImmersion @LocallyOfFiniteType t.sX j hpt fun i hi => (hV' i hi).2.2.1
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hLFT
  have hsm : Smooth t.sX := of_forall_exists_isOpenImmersion @Smooth t.sX j hpt fun i hi =>
    smooth_of_mem_triples (hV' i hi)
  have hcpt : ∀ i, CompactSpace (V i) := fun i => by
    rcases isEmpty_or_nonempty (V i) with h | h
    · infer_instance
    · exact (quasiCompact_iff_compactSpace (j i ≫ t.sX)).1 (hV' i h).2.2.2.1
  haveI : CompactSpace t.X := ⟨by
    rw [← hcov]
    exact isCompact_iUnion fun i => isCompact_range (j i).continuous⟩
  have hdimZ : ∀ Z ∈ irreducibleComponents t.X,
      topologicalKrullDim Z = ((n : ℕ∞) : WithBot ℕ∞) := fun Z hZ => by
    obtain ⟨η, -, hη⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k t.sX hZ
    obtain ⟨i, v, rfl⟩ := hpt η
    rw [← hη, (j i).isOpenEmbedding.topologicalKrullDimAt_eq v]
    exact topologicalKrullDimAt_eq_of_hasDimensionIn (t.pullback (j i)) (hV'' i ⟨v⟩).1
      (hV'' i ⟨v⟩).2 v
  have he : Equidimensional t.X := fun Z hZ Z' hZ' => by rw [hdimZ Z hZ, hdimZ Z' hZ']
  have hnz := isNonzeroAtGenericPoints_of_forall_exists_isOpenImmersion t.I j hpt fun i hi =>
    (hV' i hi).2.2.2.2.2.1
  haveI : CharZero t.k := (hV' i₀ ⟨v₀⟩).1
  have hsnc := isOrderedSNC_of_disjoint_cover t N V j hj hcov fun i => (hV i).imp (·.1) id
  exact ⟨(hV' i₀ ⟨v₀⟩).1, (MMP.Mori.isSmoothScheme_iff _).2 hsm, hLFT,
    quasiCompact_of_compactSpace _, he, hnz, hsnc⟩

/-- Restriction to an open subscheme commutes with finite intersections of ideal sheaves. -/
private theorem comap_iInf_of_isOpenImmersion' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {ι : Type*} [Finite ι] (I : ι → Y.IdealSheafData) :
    (⨅ i, I i).comap j = ⨅ i, (I i).comap j := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_iInf,
    Scheme.IdealSheafData.ideal_iInf]
  simp only [iInf_apply, Ideal.comap_iInf, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- Restriction to an open subscheme commutes with intersections of two ideal sheaves. -/
private theorem comap_inf_of_isOpenImmersion' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (I J : Y.IdealSheafData) : (I ⊓ J).comap j = I.comap j ⊓ J.comap j := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_inf,
    Scheme.IdealSheafData.ideal_inf]
  simp only [Pi.inf_apply, Ideal.comap_inf, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

/-- An ideal sheaf is determined by its restrictions to a jointly surjective family of open
immersions. -/
private theorem ideal_ext_of_comap' {Y : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ y, ∃ i, y ∈ Set.range (j i))
    {I J : Y.IdealSheafData} (h : ∀ i, I.comap (j i) = J.comap (j i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun W : Σ i, (U i).affineOpens => ⟨j W.1 ''ᵁ W.2.1, W.2.2.image_of_isOpenImmersion _⟩)
    ?_ fun W => ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, x, rfl⟩ := hcov y
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      (U i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨V, hV⟩⟩, ⟨x, hxV, rfl⟩⟩
  · have e := congrArg (fun K : (U W.1).IdealSheafData => K.ideal W.2) (h W.1)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((j W.1).appIso W.2.1).inv).2 e

/-- An inclusion of ideal sheaves may be checked on a jointly surjective family of open
immersions. -/
private theorem le_of_forall_comap_le {Y : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (j : ∀ i, U i ⟶ Y) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ y, ∃ i, y ∈ Set.range (j i))
    {I J : Y.IdealSheafData} (h : ∀ i, I.comap (j i) ≤ J.comap (j i)) : I ≤ J := by
  have : I ⊓ J = I := ideal_ext_of_comap' j hcov fun i => by
    rw [comap_inf_of_isOpenImmersion', inf_eq_left.2 (h i)]
  exact inf_eq_left.1 this

/-- A closed subscheme with no points is a smooth hypersurface. -/
private theorem isSmoothHypersurface_of_isEmpty {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (H : X.IdealSheafData) (hH : IsEmpty H.subscheme) :
    IsSmoothHypersurface sX H := by
  refine ⟨?_, fun W hW => ?_⟩
  · unfold MMP.Mori.IsSmoothScheme
    exact eq_top_iff.2 fun x _ => isEmptyElim x
  · obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    have hxs : x ∈ (H.support : Set X) := hW.1 hx
    rw [← H.range_subschemeι] at hxs
    obtain ⟨z, -⟩ := hxs
    exact isEmptyElim z

set_option backward.isDefEq.respectTransparency false in
/-- Smoothness of a closed subscheme may be checked on a jointly surjective family of open
immersions. -/
private theorem isSmoothScheme_subscheme_of_comap {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {N : ℕ} {V : Fin N → Scheme.{u}} (j : ∀ i, V i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hpt : ∀ x : X, ∃ i, ∃ v : V i, j i v = x)
    (H : X.IdealSheafData)
    (hH : ∀ i, MMP.Mori.IsSmoothScheme ((H.comap (j i)).subschemeι ≫ j i ≫ sX)) :
    MMP.Mori.IsSmoothScheme (H.subschemeι ≫ sX) := by
  let j' : ∀ i, (H.comap (j i)).subscheme ⟶ H.subscheme := fun i =>
    (H.comapIso (j i)).hom ≫ Limits.pullback.snd (j i) H.subschemeι
  haveI : ∀ i, IsOpenImmersion (j' i) := fun i => by dsimp only [j']; infer_instance
  have he : ∀ i, j' i ≫ H.subschemeι ≫ sX = (H.comap (j i)).subschemeι ≫ j i ≫ sX := fun i => by
    simp only [j', Category.assoc, ← Limits.pullback.condition_assoc,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  refine MMP.Mori.isSmoothScheme_of_smooth
    (of_forall_exists_isOpenImmersion @Smooth _ j' (fun z => ?_) fun i _ => ?_)
  · obtain ⟨i, v, hv⟩ := hpt (H.subschemeι z)
    obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback v z hv
    refine ⟨i, (H.comapIso (j i)).inv p, ?_⟩
    show ((H.comapIso (j i)).hom ≫ Limits.pullback.snd (j i) H.subschemeι)
      ((H.comapIso (j i)).inv p) = z
    rw [Scheme.Hom.comp_apply, Scheme.inv_hom_apply, hp2]
  · rw [he i]
    exact MMP.Mori.IsSmoothScheme.smooth (hH i)

/-- Being of pure codimension one may be checked on a jointly surjective family of open
immersions. -/
private theorem isPureCodimOne_support_of_comap {X : Scheme.{u}} {N : ℕ} {V : Fin N → Scheme.{u}}
    (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)] (hpt : ∀ x : X, ∃ i, ∃ v : V i, j i v = x)
    (H : X.IdealSheafData) (hH : ∀ i, MMP.Mori.IsPureCodimOne (H.comap (j i)).support) :
    MMP.Mori.IsPureCodimOne H.support := by
  intro W hW
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  obtain ⟨i, v, rfl⟩ := hpt x
  let ψ := j i
  let eψ := IrreducibleCloseds.orderIsoOfIsOpenEmbedding ψ ψ.isOpenEmbedding
  have hne : (ψ ⁻¹' (W : Set X)).Nonempty := ⟨v, hx⟩
  let V₀ := eψ.symm ⟨W, hne⟩
  have hV₀ : IrreducibleCloseds.map ψ ψ.continuous V₀ = W :=
    congrArg Subtype.val (eψ.apply_symm_apply ⟨W, hne⟩)
  have hmax : Maximal (fun W' : IrreducibleCloseds (V i) ↦
      (W' : Set (V i)) ⊆ (H.comap ψ).support) V₀ := by
    refine ⟨fun y hy => (mem_support_comap_iff ψ H y).2 (hW.1 hy), fun V' hV' hle => ?_⟩
    have h2 : ((IrreducibleCloseds.map ψ ψ.continuous V' : IrreducibleCloseds X) : Set X) ⊆
        H.support := by
      refine closure_minimal ?_ H.support.2
      rintro _ ⟨y, hy, rfl⟩
      exact (mem_support_comap_iff ψ H y).1 (hV' hy)
    have h1 : W ≤ IrreducibleCloseds.map ψ ψ.continuous V' :=
      hV₀ ▸ IrreducibleCloseds.map_mono ψ.continuous hle
    have h3 := hW.2 h2 h1
    intro y hy
    show ψ y ∈ (W : Set X)
    exact h3 (subset_closure ⟨y, hy, rfl⟩)
  rw [← hV₀, codimension_map_of_isOpenImmersion ψ V₀]
  exact hH i V₀ hmax

/-- MC-hypersurfaces glue along a finite disjoint open cover: on the pieces of maximal order `m`
take their MC-hypersurfaces, and on the others, where `MC(I)` is the unit ideal, the empty
hypersurface. -/
private theorem exists_isMCHypersurface_of_disjoint_cover {n m : ℕ} (hn : 1 ≤ n)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hdim : HasDimensionIn t.X {n})
    (hmax : maxOrder t.I = m) (N : ℕ) (V : Fin N → Scheme.{u}) (j : ∀ i, V i ⟶ t.X)
    (hj : ∀ i, IsOpenImmersion (j i))
    (hd : Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))))
    (hcov : (⋃ i, Set.range (j i)) = Set.univ)
    (hV : ∀ i, t.pullback (j i) ∈ mcLocalTriples n m ∨ IsEmpty (V i)) :
    ∃ H, IsMCHypersurface t.sX t.I H := by
  haveI : CharZero t.k := ht.1
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  haveI : Smooth t.sX := smooth_of_mem_triples ht
  haveI := hj
  have hpos := pos_dim_of_mem_irreducibleComponents hn t ht hdim
  have hpt := Set.iUnion_eq_univ_iff.1 hcov
  have hmc : maximalContactIdeal t.sX t.I = higherDerivativeIdeal t.sX t.I (m - 1) := by
    rw [maximalContactIdeal, hmax, ENat.toNat_coe]
  have hloc : ∀ i, ∃ Hi : (V i).IdealSheafData, IsSmoothHypersurface (j i ≫ t.sX) Hi ∧
      Hi ≤ (maximalContactIdeal t.sX t.I).comap (j i) := by
    intro i
    haveI : Smooth (j i) := inferInstance
    rcases hV i with hl | he
    · obtain ⟨pitr, pidim, -, hlt | ⟨heq, Hi, hHi⟩⟩ := hl
      · refine ⟨⊤, isSmoothHypersurface_of_isEmpty _ _ inferInstance, ?_⟩
        haveI : LocallyOfFiniteType (j i ≫ t.sX) := pitr.2.2.1
        haveI : QuasiCompact (j i ≫ t.sX) := pitr.2.2.2.1
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact absurd hlt (by simp)
        have hm' : maxOrder (t.I.comap (j i)) ≤ ((m - 1 : ℕ) : ℕ∞) := by
          have e : ((m : ℕ) : ℕ∞) = ((m - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; omega
          rw [e] at hlt
          exact (ENat.lt_add_one_iff (ENat.coe_ne_top _)).1 hlt
        have hdim' : ∃ n' : ℕ, 0 < n' ∧
            ∀ Z ∈ irreducibleComponents (V i), topologicalKrullDim Z = n' :=
          ⟨n, hn, fun Z hZ => by
            obtain ⟨η, -, hη⟩ := topologicalKrullDim_eq_topologicalKrullDimAt t.k (j i ≫ t.sX) hZ
            rw [← hη]
            exact topologicalKrullDimAt_eq_of_hasDimensionIn (t.pullback (j i)) pitr pidim η⟩
        rw [hmc, ← higherDerivativeIdeal_comap_of_smooth t.sX (j i ≫ t.sX) (j i) rfl hpos]
        exact (higherDerivativeIdeal_eq_top_of_maxOrder_le (I := t.I.comap (j i))
          (j i ≫ t.sX) hdim' pitr.2.2.2.2.2.1 hm').ge
      · refine ⟨Hi, hHi.1, ?_⟩
        rw [← maximalContactIdeal_comap_of_smooth t.sX (j i ≫ t.sX) (j i) rfl hpos t.I
          (heq.trans hmax.symm)]
        exact hHi.2
    · exact ⟨(maximalContactIdeal t.sX t.I).comap (j i),
        isSmoothHypersurface_of_isEmpty _ _
          ⟨fun z => isEmptyElim (Scheme.IdealSheafData.subschemeι _ z)⟩,
        le_rfl⟩
  have hcl : ∀ i, IsClosed (Set.range (j i)) := fun i => by
    refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun x hx => ?_)
    obtain ⟨l, v, rfl⟩ := hpt x
    have hli : l ≠ i := by rintro rfl; exact hx ⟨v, rfl⟩
    exact ⟨Set.range (j l), fun y hy hy' => Set.disjoint_left.1 (hd hli) hy hy',
      (j l).isOpenEmbedding.isOpen_range, ⟨v, rfl⟩⟩
  haveI : ∀ i, QuasiCompact (j i) := fun i =>
    have := IsClosedImmersion.of_isPreimmersion (j i) (hcl i); inferInstance
  choose Hs hHs using hloc
  let H : t.X.IdealSheafData := ⨅ i, (Hs i).map (j i)
  have hcomap : ∀ l, H.comap (j l) = Hs l := by
    intro l
    rw [comap_iInf_of_isOpenImmersion']
    refine le_antisymm
      ((iInf_le _ l).trans (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion (j l) (Hs l)).le)
      (le_iInf fun i => ?_)
    by_cases hil : i = l
    · subst hil; rw [ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion]
    · have htop : ((Hs i).map (j i)).comap (j l) = ⊤ := by
        rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap,
          Scheme.IdealSheafData.support_map]
        refine eq_bot_iff.2 fun y hy => ?_
        have h1 : (j l) y ∈ Set.range (j i) :=
          closure_minimal (Set.image_subset_range _ _) (hcl i) hy
        exact (Set.disjoint_left.1 (hd hil) h1 ⟨y, rfl⟩).elim
      rw [htop]
      exact le_top
  have hHc : ∀ l, IsSmoothHypersurface (j l ≫ t.sX) (H.comap (j l)) := fun l =>
    (hcomap l).symm ▸ (hHs l).1
  refine ⟨H, ⟨isSmoothScheme_subscheme_of_comap t.sX j hpt H fun l => (hHc l).1,
    isPureCodimOne_support_of_comap j hpt H fun l => (hHc l).2⟩, ?_⟩
  exact le_of_forall_comap_le j (fun y => by obtain ⟨i, v, h⟩ := hpt y; exact ⟨i, v, h⟩)
    fun l => by rw [hcomap l]; exact (hHs l).2

/-- Step (ii): a nonempty finite disjoint union of local or empty triples is a local triple. -/
private theorem mem_mcLocalTriples_of_disjoint_cover {n m : ℕ} (hn : 1 ≤ n)
    (t : FieldBlowupTriple.{u}) [Nonempty t.X] (N : ℕ) (V : Fin N → Scheme.{u})
    (j : ∀ i, V i ⟶ t.X) (hj : ∀ i, IsOpenImmersion (j i))
    (hd : Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))))
    (hcov : (⋃ i, Set.range (j i)) = Set.univ)
    (hV : ∀ i, t.pullback (j i) ∈ mcLocalTriples n m ∨ IsEmpty (V i)) :
    t ∈ mcLocalTriples n m := by
  have hpt := Set.iUnion_eq_univ_iff.1 hcov
  have hV' : ∀ i, Nonempty (V i) → t.pullback (j i) ∈ mcLocalTriples n m := fun i hi =>
    (hV i).resolve_right (not_isEmpty_of_nonempty _)
  have htr := mem_triples_of_disjoint_cover t N V j hj hd hcov fun i =>
    (hV i).imp (fun h => ⟨h.1, h.2.1⟩) id
  haveI : LocallyOfFiniteType t.sX := htr.2.2.1
  have hdim : HasDimensionIn t.X {n} :=
    hasDimensionIn_of_forall_topologicalKrullDimAt t.k t.sX fun x => by
      obtain ⟨i, v, rfl⟩ := hpt x
      haveI := hj i
      have hl := hV' i ⟨v⟩
      rw [(j i).isOpenEmbedding.topologicalKrullDimAt_eq v]
      exact topologicalKrullDimAt_eq_of_hasDimensionIn (t.pullback (j i)) hl.1 hl.2.1 v
  have hle : maxOrder t.I ≤ m := iSup₂_le fun x _ => by
    obtain ⟨i, v, rfl⟩ := hpt x
    haveI := hj i
    have hl := hV' i ⟨v⟩
    rw [← multAt_comap_of_isOpenImmersion]
    exact (multAt_le_maxOrder _ v).trans hl.2.2.1
  refine ⟨htr, hdim, hle, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, exists_isMCHypersurface_of_disjoint_cover hn t htr hdim heq N V j hj hd
      hcov hV⟩

/-! ### Local triples cover every triple -/

/-- On an affine open `U`, the zero scheme of `f ∈ J(U)` is contained in `J|_U`. -/
private theorem ker_spec_quotient_le_comap {X : Scheme.{u}} (U : X.affineOpens)
    (J : X.IdealSheafData) (f : Γ(X, U.1)) (hf : f ∈ J.ideal U) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫ U.2.isoSpec.inv).ker ≤
      J.comap U.1.ι := by
  haveI : IsAffine U.1.toScheme := U.2
  rw [Scheme.ker_of_isAffine]
  refine Scheme.IdealSheafData.le_of_isAffine ?_
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have e := Scheme.IdealSheafData.map_ideal' J
    (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩) (V := U)
    (homOfLE (le_of_eq U.1.ι_image_top)).op
  rw [← e]
  intro a ha
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, homOfLE_refl, op_id, Functor.map_id,
    CommRingCat.hom_id, Ideal.map_id, Ideal.comap_id] at ha ⊢
  rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id] at ha
  change a ∈ Ideal.map _ (J.ideal U)
  rw [RingHom.mem_ker, Scheme.Hom.comp_appTop] at ha
  have key := IsAffineOpen.isoSpec_inv_appTop (X := X) (U := U.1) U.2
  have hz : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))).appTop
      ((Scheme.ΓSpecIso Γ(X, U.1)).inv (U.1.topIso.hom a)) = 0 := by
    rw [key, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp,
      RingHom.comp_apply] at ha
    exact ha
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  have h2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv (U.1.topIso.hom a))) hnat
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [show (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (Ideal.span {f}))))).hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom (U.1.topIso.hom.hom a)) = 0
    from hz, map_zero] at h2
  have h3 : Ideal.Quotient.mk (Ideal.span {f}) (U.1.topIso.hom a) = 0 := by
    convert h2.symm using 2
    exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(X, U.1)) _).symm
  have hmem : U.1.topIso.hom a ∈ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.1 h3
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  have ha' : a = U.1.topIso.inv (U.1.topIso.hom a) := (Iso.hom_inv_id_apply _ _).symm
  rw [ha', ← hr, map_mul]
  have hinv :
      U.1.topIso.inv.hom = (X.presheaf.map (homOfLE (le_of_eq U.1.ι_image_top)).op).hom := by
    rw [Scheme.Opens.topIso_inv]; congr 3
  have hfm : U.1.topIso.inv.hom f ∈
      Ideal.map (X.presheaf.map (homOfLE (le_of_eq U.1.ι_image_top)).op).hom (J.ideal U) := by
    rw [hinv]; exact Ideal.mem_map_of_mem _ hf
  exact Ideal.mul_mem_left _ _ hfm

/-- On an affine open `U`, the ideal of the zero scheme of `f ∈ Γ(U)` is generated by `f`. -/
private theorem ideal_ker_spec_quotient_top {X : Scheme.{u}} (U : X.affineOpens) (f : Γ(X, U.1)) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {U.1.topIso.inv f} := by
  haveI : IsAffine U.1.toScheme := U.2
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, Scheme.Hom.comp_appTop,
    IsAffineOpen.isoSpec_inv_appTop U.2]
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  have hnat' : (Scheme.ΓSpecIso _).inv ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))).appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})) ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, hnat]
  rw [Category.assoc]; erw [hnat']
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have h1 : U.1.topIso.hom.hom a = e a := rfl
  have h2 : f = e (U.1.topIso.inv.hom f) := (CommRingCat.hom_inv_apply U.1.topIso f).symm
  rw [h1]
  conv_lhs => rw [h2]
  rw [map_dvd_iff]

/-- On an affine open `U` of a scheme smooth over a field, the zero locus of a nonzerodivisor
`f ∈ Γ(U)` is of pure codimension one in `U`. -/
private theorem isPureCodimOne_support_ker_of_mem_nonZeroDivisors {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (U : X.affineOpens) (f : Γ(X, U.1))
    (hnzd : f ∈ nonZeroDivisors Γ(X, U.1)) :
    MMP.Mori.IsPureCodimOne (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker.support := by
  set D := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv).ker
  have : LocallyOfFiniteType (U.1.ι ≫ sX) := inferInstance
  have : IsLocallyNoetherian U.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian (U.1.ι ≫ sX)
  intro W hW
  set e := irreducibleSetEquivPoints (α := U.1.toScheme)
  have hWη : (W : Set U.1.toScheme) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set U.1.toScheme) := by rw [hWη]; exact subset_closure rfl
  have hηD : e W ∈ D.support := hW.1 hηW
  obtain ⟨z, hz⟩ : ∃ z, D.subschemeι z = e W := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι] at hηD; exact hηD
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1, ← hz]
  have hmax : IsMax z := by
    intro b hb
    rw [Scheme.le_iff_specializes] at hb ⊢
    have hcl := D.subschemeι.isClosedEmbedding
    have hb' : D.subschemeι b ⤳ e W := hz ▸ hb.map D.subschemeι.continuous
    have hbD : D.subschemeι b ∈ D.support := by
      rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨b, rfl⟩
    have hle : W ≤ e.symm (D.subschemeι b) := by
      rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes]
      exact hb'
    have hsub : ((e.symm (D.subschemeι b) : TopologicalSpace.IrreducibleCloseds U.1.toScheme) :
        Set U.1.toScheme) ⊆ D.support := by
      change closure {D.subschemeι b} ⊆ _
      exact closure_minimal (Set.singleton_subset_iff.mpr hbD) D.support.isClosed
    have hge := hW.2 hsub hle
    rw [← e.le_iff_le, e.apply_symm_apply, Scheme.le_iff_specializes, ← hz] at hge
    exact hcl.isInducing.specializes_iff.mp hge
  have hz0 : ringKrullDim (D.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]; rfl
  have hzD : D.subschemeι z ∈ D.support := hz ▸ hηD
  set η := D.subschemeι z
  let V : U.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hηV : η ∈ (V : U.1.toScheme.Opens) := trivial
  set g := U.1.topIso.inv.hom f
  have hJ : D.ideal V = Ideal.span {g} := ideal_ker_spec_quotient_top U f
  have hg : g ∈ nonZeroDivisors Γ(U.1.toScheme, V.1) := by
    refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
    have hφ : U.1.topIso.hom.hom g = f := CommRingCat.hom_inv_apply U.1.topIso f
    have h0 : U.1.topIso.hom.hom x * f = 0 := by rw [← hφ, ← map_mul, hx, map_zero]
    exact (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).1
      ((mem_nonZeroDivisors_iff_right.1 hnzd _ h0).trans (map_zero _).symm)
  have hst : IdealSheafData.stalk D η =
      Ideal.span {(U.1.toScheme.presheaf.germ V.1 η hηV).hom g} := by
    rw [IdealSheafData.stalk_eq_map_germ D η V hηV, hJ, Ideal.map_span, Set.image_singleton]
  let _ : Algebra Γ(U.1.toScheme, V.1) (U.1.toScheme.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk U.1.toScheme.presheaf ⟨η, hηV⟩
  have : IsLocalization.AtPrime (U.1.toScheme.presheaf.stalk η)
      (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal := V.2.isLocalization_stalk ⟨η, hηV⟩
  have : Module.Flat Γ(U.1.toScheme, V.1) (U.1.toScheme.presheaf.stalk η) :=
    IsLocalization.flat _ (V.2.primeIdealOf ⟨η, hηV⟩).asIdeal.primeCompl
  have hgreg : IsSMulRegular (U.1.toScheme.presheaf.stalk η)
      ((U.1.toScheme.presheaf.germ V.1 η hηV).hom g) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := Γ(U.1.toScheme, V.1))
      (M := U.1.toScheme.presheaf.stalk η) hg
  have hgm : (U.1.toScheme.presheaf.germ V.1 η hηV).hom g ∈
      IsLocalRing.maximalIdeal (U.1.toScheme.presheaf.stalk η) := by
    have hmem := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := D) (U := V) hηV).mp hzD
    rw [Scheme.mem_zeroLocus_iff] at hmem
    have hnot := hmem g (by rw [SetLike.mem_coe, hJ]; exact Ideal.mem_span_singleton_self g)
    rw [Scheme.mem_basicOpen _ _ _ hηV] at hnot
    exact hnot
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hgreg hgm
  rw [← hst, ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv D z),
    hz0, zero_add, ringKrullDim_stalk_eq_coheight] at hdim
  exact_mod_cast hdim.symm

/-- On an affine open `U` of a scheme smooth over `k`, the zero scheme of a nonzerodivisor
`f ∈ J(U)` whose zero scheme `Spec(Γ(U)/(f))` is smooth over `k` is a smooth hypersurface of `U`
contained in `J|_U`. -/
private theorem exists_isSmoothHypersurface_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (U : X.affineOpens) (J : X.IdealSheafData)
    (f : Γ(X, U.1)) (hf : f ∈ J.ideal U) (hnzd : f ∈ nonZeroDivisors Γ(X, U.1))
    (hs : Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
      U.2.isoSpec.inv ≫ U.1.ι ≫ sX)) :
    ∃ H : U.1.toScheme.IdealSheafData, IsSmoothHypersurface (U.1.ι ≫ sX) H ∧
      H ≤ J.comap U.1.ι := by
  set i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫ U.2.isoSpec.inv
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion i := by dsimp [i]; infer_instance
  refine ⟨i.ker, ⟨?_, isPureCodimOne_support_ker_of_mem_nonZeroDivisors sX U f hnzd⟩, ?_⟩
  · have he : i.ker.subschemeι ≫ U.1.ι ≫ sX = inv i.toImage ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))) ≫
          U.2.isoSpec.inv ≫ U.1.ι ≫ sX := by
      have hι : i.imageι = inv i.toImage ≫ i :=
        (IsIso.eq_inv_comp _).2 (Scheme.Hom.toImage_imageι i)
      change i.imageι ≫ _ = _
      rw [hι]
      simp only [Category.assoc, i]
    rw [he]
    have hinv : Smooth (inv i.toImage) := inferInstance
    exact MMP.Mori.isSmoothScheme_of_smooth (MorphismProperty.comp_mem @Smooth _ _ hinv hs)
  · exact ker_spec_quotient_le_comap U J f hf

/-- Step (i): local triples cover every global triple. -/
private theorem exists_isOpenCoverMap_mem_mcLocalTriples {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {n} m) (x : t.X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ t.X), IsOpenCoverMap g ∧ x ∈ Set.range g ∧
      t.pullback g ∈ mcLocalTriples n m := by
  obtain ⟨htr, hd, hle⟩ := ht
  haveI : CharZero t.k := htr.1
  haveI : LocallyOfFiniteType t.sX := htr.2.2.1
  haveI : QuasiCompact t.sX := htr.2.2.2.1
  haveI : Smooth t.sX := smooth_of_mem_triples htr
  have hpos := pos_dim_of_mem_irreducibleComponents hn t htr hd
  haveI : Nonempty t.X := ⟨x⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact ⟨t.X, 𝟙 _, isOpenCoverMap_of_isOpenImmersion _, ⟨x, rfl⟩,
      pullback_mem_mcLocalTriples hn t ⟨htr, hd, hle, Or.inl hlt⟩ (𝟙 _)
        (isOpenCoverMap_of_isOpenImmersion _)⟩
  obtain ⟨U, hxU, -, f, -, hf, hnzd, hsm⟩ :=
    exists_smul_generator_mem_maximalContactIdeal_smooth t.sX htr.2.2.2.2.1 hpos
      htr.2.2.2.2.2.1 hm heq (SheafOfModules.unit _) x
  have hU : IsOpenCoverMap U.1.ι := isOpenCoverMap_of_isOpenImmersion _
  haveI : Nonempty U.1.toScheme := ⟨⟨x, hxU⟩⟩
  refine ⟨U.1, U.1.ι, hU, ⟨⟨x, hxU⟩, rfl⟩, ?_⟩
  have hle' := maxOrder_comap_le_of_isOpenCoverMap hU t.I
  refine ⟨pullback_mem_triples_of_isOpenCoverMap t htr _ hU,
    hasDimensionIn_of_isOpenCoverMap (Y := U.1.toScheme) t htr hd _ hU, hle'.trans hle, ?_⟩
  rcases (hle'.trans hle).lt_or_eq with hlt | heq'
  · exact Or.inl hlt
  refine Or.inr ⟨heq', ?_⟩
  obtain ⟨H, hH, hHle⟩ := exists_isSmoothHypersurface_of_section t.sX U _ f hf hnzd hsm
  refine ⟨H, hH, ?_⟩
  change H ≤ maximalContactIdeal (U.1.ι ≫ t.sX) (t.I.comap U.1.ι)
  rw [maximalContactIdeal_comap_of_smooth t.sX _ U.1.ι rfl hpos t.I (heq'.trans heq.symm)]
  exact hHle

/-- A triple whose every point has an open cover map neighbourhood pulling it back into `LT`, on a
quasi-compact scheme, admits a single surjective open cover map from a finite disjoint union along
which it pulls back into `LT`, provided `LT` is closed under finite disjoint unions. -/
private theorem exists_surjective_isOpenCoverMap_pullback_mem (LT : Set FieldBlowupTriple.{u})
    (hunion : ∀ (t : FieldBlowupTriple.{u}) (n : ℕ) (V : Fin n → Scheme.{u})
      (j : ∀ i, V i ⟶ t.X), (∀ i, IsOpenImmersion (j i)) →
      Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))) →
      (⋃ i, Set.range (j i)) = Set.univ → (∀ i, t.pullback (j i) ∈ LT) → t ∈ LT)
    (t : FieldBlowupTriple.{u}) [CompactSpace t.X]
    (hloc : ∀ x : t.X, ∃ (U : Scheme.{u}) (g : U ⟶ t.X),
      IsOpenCoverMap g ∧ x ∈ Set.range g ∧ t.pullback g ∈ LT) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ t.X), IsOpenCoverMap g ∧ Surjective g ∧ t.pullback g ∈ LT := by
  choose U g hMg hx hLT using hloc
  have hopen : ∀ x, IsOpen (Set.range (g x)) := fun x => by
    have : Smooth (g x) := smooth_of_isOpenCoverMap (hMg x)
    have : UniversallyOpen (g x) := UniversallyOpen.of_flat (g x)
    exact (g x).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (g x)) hopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  let e := s.equivFin.symm
  let V : Fin s.card → Scheme.{u} := fun i => U (e i).1
  let G : ∀ i, V i ⟶ t.X := fun i => g (e i).1
  refine ⟨∐ V, Sigma.desc G, isOpenCoverMap_sigmaDesc _ V G (fun i => hMg _), ⟨fun x => ?_⟩, ?_⟩
  · obtain ⟨i, hi, y, rfl⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    let j := s.equivFin ⟨i, hi⟩
    have hmem : ∀ i', i' = i → g i y ∈ Set.range (g i') := by
      rintro _ rfl
      exact ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hmem (e j).1 (by simp [e, j])
    refine ⟨Sigma.ι V j y', ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    exact hy'
  · refine hunion _ _ V (Sigma.ι V)
      (fun i => Scheme.IsLocallyDirected.instIsOpenImmersionι (Discrete.functor V) ⟨i⟩)
      (fun a b hab => ?_) ?_ (fun i => ?_)
    · have := disjoint_opensRange_sigmaι V a b hab
      refine Set.disjoint_left.2 fun x h₁ h₂ => ?_
      have hx : x ∈ (Sigma.ι V a).opensRange ⊓ (Sigma.ι V b).opensRange := ⟨h₁, h₂⟩
      rw [this.eq_bot] at hx
      exact hx
    · refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
      obtain ⟨⟨i⟩, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Discrete.functor V) x
      exact ⟨i, y, hy⟩
    · rw [fieldBlowupTriple_pullback_pullback, Sigma.ι_desc]
      exact hLT _

/-- Every triple of dimension `n` with `maxord I ≤ m` becomes local on a surjective open cover map
(Kollár 3.103 proof, Step 3 (i)–(ii)): local triples cover it, and finitely many of them suffice
by quasi-compactness; their disjoint union is local. -/
private theorem exists_surjective_isOpenCoverMap_mem_mcLocalTriples {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {n} m) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ t.X), IsOpenCoverMap g ∧ Surjective g ∧
      t.pullback g ∈ mcLocalTriples n m := by
  haveI : QuasiCompact t.sX := ht.1.2.2.2.1
  haveI : CompactSpace t.X := ⟨by
    simpa using QuasiCompact.isCompact_preimage (f := t.sX) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Nonempty t.X := nonempty_of_hasDimensionIn ht.2.1
  let LT : Set FieldBlowupTriple.{u} := {s | s ∈ mcLocalTriples n m ∨ IsEmpty s.X}
  obtain ⟨X', g, hg, hs, hl⟩ := exists_surjective_isOpenCoverMap_pullback_mem LT
    (fun s N V j hj hd hcov hV => by
      rcases isEmpty_or_nonempty s.X with hX | hX
      · exact Or.inr hX
      · exact Or.inl (mem_mcLocalTriples_of_disjoint_cover hn s N V j hj hd hcov hV))
    t (fun x => by
      obtain ⟨U, g, hg, hx, hl⟩ := exists_isOpenCoverMap_mem_mcLocalTriples hn hm t ht x
      exact ⟨U, g, hg, hx, Or.inl hl⟩)
  haveI : Nonempty X' := ⟨(hs.surj (Classical.arbitrary t.X)).choose⟩
  exact ⟨X', g, hg, hs, hl.resolve_right (not_isEmpty_of_nonempty (α := X'))⟩

/-! ### The well-tuned ideal -/

/-- The order of the zero ideal is `⊤`. -/
private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊥ : Ideal R) = ⊤ := by
  refine eq_top_iff.2 (ENat.forall_natCast_le_iff_le.1 fun j _ => ?_)
  exact le_iSup₂ (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ IsLocalRing.maximalIdeal R ^ j) =>
    (j : ℕ∞)) j bot_le

/-- An ideal sheaf of finite maximal order is nonzero at every point. -/
private theorem isNonzeroAtGenericPoints_of_maxOrder_ne_top {X : Scheme.{u}}
    {J : X.IdealSheafData} (hJ : maxOrder J ≠ ⊤) : IsNonzeroAtGenericPoints J := by
  intro η _ h0
  refine hJ (eq_top_iff.2 ?_)
  have : multAt J η = ⊤ := by rw [multAt, h0, idealOrder_bot]
  exact this ▸ multAt_le_maxOrder J η

/-- The triple `(X, W(I), E)` with the well-tuned ideal. -/
private noncomputable abbrev wellTunedTriple (t : FieldBlowupTriple.{u}) : FieldBlowupTriple.{u} :=
  ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩

/-- For a triple of dimension `n ≥ 1` with `maxord I = m ≥ 1`: `maxord W(I) = m!`, `(X, W(I), E)`
is a triple, and `MC(W(I)) = MC(I)` (Kollár Thm. 3.103 proof, Step 3). -/
private theorem wellTunedTriple_spec {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hd : HasDimensionIn t.X {n})
    (hmax : maxOrder t.I = m) :
    maxOrder (wellTunedIdeal t.sX t.I) = (m.factorial : ℕ) ∧ wellTunedTriple t ∈ triples ∧
      maximalContactIdeal t.sX (wellTunedIdeal t.sX t.I) = maximalContactIdeal t.sX t.I := by
  haveI : CharZero t.k := ht.1
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  haveI : QuasiCompact t.sX := ht.2.2.2.1
  haveI : Smooth t.sX := smooth_of_mem_triples ht
  have hdim := one_le_topologicalKrullDim hn hd
  have hm' : 1 ≤ (maxOrder t.I).toNat := by rw [hmax]; simpa using hm
  have hW : maxOrder (wellTunedIdeal t.sX t.I) = (m.factorial : ℕ) := by
    rw [Kollar.maxOrder_wellTunedIdeal t.sX ht.2.2.2.2.1 hdim t.I hm', hmax]; simp
  refine ⟨hW, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
    isNonzeroAtGenericPoints_of_maxOrder_ne_top (by rw [hW]; exact ENat.coe_ne_top _),
    ht.2.2.2.2.2.2⟩, ?_⟩
  rw [wellTunedIdeal, Kollar.maximalContactIdeal_maximalCoefficientIdeal t.sX ht.2.2.2.2.1 hdim
    t.I hm' (Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)),
    Kollar.maximalCoefficientIdeal_one_eq_maximalContactIdeal t.sX
      (pos_dim_of_mem_irreducibleComponents hn t ht hd) t.I hm']

/-- An MC-hypersurface for `I` is one for `W(I)`. -/
private theorem isMCHypersurface_wellTuned {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hd : HasDimensionIn t.X {n})
    (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData} (hH : IsMCHypersurface t.sX t.I H) :
    IsMCHypersurface t.sX (wellTunedIdeal t.sX t.I) H :=
  ⟨hH.1, by rw [(wellTunedTriple_spec hn hm t ht hd hmax).2.2]; exact hH.2⟩

/-- The chosen hypersurface of a local triple of maximal order `m` is an MC-hypersurface. -/
private theorem isMCHypersurface_mcHypersurfaceChoice {n m : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ mcLocalTriples n m) (hmax : maxOrder t.I = m) :
    IsMCHypersurface t.sX t.I (mcHypersurfaceChoice t) := by
  have hex : ∃ H, IsMCHypersurface t.sX t.I H :=
    (ht.2.2.2.resolve_left (by rw [hmax]; exact lt_irrefl _)).2
  rw [mcHypersurfaceChoice, dif_pos hex]
  exact hex.choose_spec

/-- The chosen MC-hypersurface of a local triple of maximal order `m` is one for `W(I)`. -/
private theorem isMCHypersurface_wellTunedIdeal {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) (hmax : maxOrder t.I = m) :
    IsMCHypersurface t.sX (wellTunedIdeal t.sX t.I) (mcHypersurfaceChoice t) :=
  isMCHypersurface_wellTuned hn hm t ht.1 ht.2.1 hmax
    (isMCHypersurface_mcHypersurfaceChoice t ht hmax)

/-- The pull-back of an MC-hypersurface along an open cover map preserving the maximal order is
an MC-hypersurface. -/
private theorem isMCHypersurface_comap_of_isOpenCoverMap {n : ℕ} (hn : 1 ≤ n)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hd : HasDimensionIn t.X {n})
    {H : t.X.IdealSheafData} (hH : IsMCHypersurface t.sX t.I H) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    (hh : IsOpenCoverMap h) (hmax : maxOrder (t.I.comap h) = maxOrder t.I) :
    IsMCHypersurface (h ≫ t.sX) (t.I.comap h) (H.comap h) := by
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  haveI : Smooth t.sX := smooth_of_mem_triples ht
  refine ⟨isSmoothHypersurface_comap_of_isOpenCoverMap t hH.1 h hh, ?_⟩
  rw [maximalContactIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl
    (pos_dim_of_mem_irreducibleComponents hn t ht hd) t.I hmax]
  exact Scheme.IdealSheafData.comap_mono h hH.2

/-- `boMaximalContact` only sees the ideal through its value. -/
private theorem boMaximalContact_congr {M : MarkedFamily.{u}} {m : ℕ} {X : Scheme.{u}}
    {J₁ J₂ : X.IdealSheafData} (E : OrderedDivisor X) (k : Type u) [Field k]
    (sX : X ⟶ Spec (.of k)) (hJ : J₁ = J₂) (H : X.IdealSheafData) :
    boMaximalContact M m ⟨⟨X, J₁, E⟩, k, sX⟩ H = boMaximalContact M m ⟨⟨X, J₂, E⟩, k, sX⟩ H := by
  subst hJ; rfl

private theorem boLocal_congr (M : MarkedFamily.{u}) (m : ℕ) {s s' : FieldBlowupTriple.{u}}
    (e : s = s') : boLocal M m s ≍ boLocal M m s' := by
  subst e; rfl

/-- `𝓑_{n,m}` commutes with surjective open cover maps between local triples. -/
private theorem boLocal_pullback_of_isOpenCoverMap {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    (hh : IsOpenCoverMap h) (hs : Surjective h) (hY : t.pullback h ∈ mcLocalTriples n m) :
    boLocal M m (t.pullback h) = (boLocal M m t).pullback h := by
  have hmaxY : maxOrder (t.I.comap h) = maxOrder t.I := maxOrder_comap_of_isOpenCoverMap hh hs t.I
  rcases ht.2.2.1.lt_or_eq with hlt | heq
  · have hlt' : maxOrder (t.pullback h).I < m := by
      change maxOrder (t.I.comap h) < m
      rwa [hmaxY]
    rw [boLocal, boLocal, if_pos hlt, if_pos hlt']
    rfl
  have heq' : maxOrder (t.pullback h).I = m := hmaxY.trans heq
  have hnlt : ¬ maxOrder t.I < m := heq.not_lt
  have hnlt' : ¬ maxOrder (t.pullback h).I < m := heq'.not_lt
  rw [boLocal, boLocal, if_neg hnlt, if_neg hnlt']
  haveI : Smooth h := smooth_of_isOpenCoverMap hh
  have htr := ht.1
  have hd := ht.2.1
  have htrY := hY.1
  have hdY := hY.2.1
  haveI : LocallyOfFiniteType t.sX := htr.2.2.1
  haveI : Smooth t.sX := smooth_of_mem_triples htr
  haveI : LocallyOfFiniteType (h ≫ t.sX) := htrY.2.2.1
  haveI : CharZero t.k := htr.1
  -- `W(g^*I) = g^*W(I)`.
  have hWY : wellTunedIdeal (h ≫ t.sX) (t.I.comap h) = (wellTunedIdeal t.sX t.I).comap h := by
    unfold wellTunedIdeal
    rw [hmaxY]
    exact Kollar.maximalCoefficientIdeal_comap_of_smooth t.sX (h ≫ t.sX) htr.2.1 htrY.2.1
      htr.2.2.2.2.1 htrY.2.2.2.2.1 (one_le_topologicalKrullDim hn hd) h rfl t.I
      (by rw [heq]; simpa using hm) hmaxY _
  obtain ⟨hWm, hWtr, -⟩ := wellTunedTriple_spec hn hm t htr hd heq
  obtain ⟨hWmY, hWtrY, -⟩ := wellTunedTriple_spec hn hm (t.pullback h) htrY hdY heq'
  have hn' : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞) := by
    obtain ⟨d, hd1, hd2⟩ := hd
    rw [Set.mem_singleton_iff] at hd1
    rw [hd2, hd1]
  have hn'' : topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞) := by
    obtain ⟨d, hd1, hd2⟩ := hdY
    rw [Set.mem_singleton_iff] at hd1
    rw [show topologicalKrullDim Y = _ from hd2, hd1]
  -- The two MC-hypersurfaces `H(X^*, g^*I)` and `g⁻¹H(X, I)` for `W(g^*I)`.
  have hH := isMCHypersurface_mcHypersurfaceChoice t ht heq
  have hH' := isMCHypersurface_mcHypersurfaceChoice (t.pullback h) hY heq'
  have hHc := isMCHypersurface_comap_of_isOpenCoverMap hn t htr hd hH h hh hmaxY
  have e1 := boMaximalContact_eq_of_isMCHypersurface (N := n) M hn hM
    (wellTunedTriple (t.pullback h)) hWtrY hn'' hn le_rfl (Nat.factorial_pos m) hWmY
    (isMCHypersurface_wellTuned hn hm (t.pullback h) htrY hdY heq' hH')
    (isMCHypersurface_wellTuned hn hm (t.pullback h) htrY hdY heq' hHc)
  refine e1.trans ?_
  have e2 := boMaximalContact_pullback (N := n) M hn hM (wellTunedTriple t) hWtr hn' hn
    le_rfl (Nat.factorial_pos m) hWm (isMCHypersurface_wellTuned hn hm t htr hd heq hH)
    h inferInstance (Or.inr hs) (by
      have e : wellTunedTriple (t.pullback h) = (wellTunedTriple t).pullback h := by
        show (⟨⟨Y, wellTunedIdeal (h ≫ t.sX) (t.I.comap h), t.E.comap h⟩, t.k, h ≫ t.sX⟩ :
            FieldBlowupTriple.{u}) = ⟨⟨Y, (wellTunedIdeal t.sX t.I).comap h, t.E.comap h⟩, t.k,
            h ≫ t.sX⟩
        rw [hWY]
      exact e ▸ hWtrY) hn'' hn le_rfl
    (by change maxOrder ((wellTunedIdeal t.sX t.I).comap h) = _
        rw [maxOrder_comap_of_isOpenCoverMap hh hs, hWm])
  refine (boMaximalContact_congr _ _ _ hWY _).trans (e2.trans ?_)
  exact ClosedBlowupSequence.reduction_eq_self
    (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _) h)

/-! ### Gluing the local sequences -/

/-- **Kollár, Thm. 3.103 proof, Step 3.** Let `𝓜` be a marked order-reduction family on
dimensions `0, …, n - 1` (`IsMarkedOrderReductionFamily`), `n, m ≥ 1`, and `(X, I, E)` a triple
with `dim X = n` and `maxord I ≤ m`. For every surjective open cover map `g : X^* → X`
(`IsOpenCoverMap`) with `(X^*, g^*I, g⁻¹E) ∈ 𝓛𝓣_{n,m}` (`mcLocalTriples`),
`g^* 𝓑𝓞_{n,m}(X, I, E) = 𝓑_{n,m}(X^*, g^*I, g⁻¹E)` (`boFunctor`, `boLocal`). -/
@[mmp "lem_kr3e_bo_extends_local"]
public theorem boFunctor_pullback {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {n} m)
    {X' : Scheme.{u}} (g : X' ⟶ t.X) (hg : IsOpenCoverMap g) (hsurj : Surjective g)
    (hloc : t.pullback g ∈ mcLocalTriples n m) :
    (boFunctor M n m t).pullback g = boLocal M m (t.pullback g) := by
  classical
  haveI : (openCoverMaps.{u}).IsStableUnderBaseChange :=
    ⟨fun sq hg => isOpenCoverMap_of_isPullback sq hg⟩
  haveI : (openCoverMaps.{u}).IsStableUnderComposition :=
    ⟨fun _ _ hf hg => isOpenCoverMap_comp hf hg⟩
  -- Empty triples are added to both classes: the pull-back along the empty open cover map has
  -- dimension `⊥`, so it lies in neither `idealTriplesOfDim {n} m` nor `mcLocalTriples n m`.
  let GT : Set FieldBlowupTriple.{u} := {s | s ∈ idealTriplesOfDim {n} m ∨ IsEmpty s.X}
  let LT : Set FieldBlowupTriple.{u} := {s | s ∈ mcLocalTriples n m ∨ IsEmpty s.X}
  let 𝓑 : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple LT := fun s _ =>
    if IsEmpty s.X then .nil s.X else boLocal M m s
  have hex := Kollar.exists_pullback_eq_of_commutes_with_surjections openCoverMaps
    (fun _ _ _ hg => smooth_of_isOpenCoverMap hg) (fun _ hg => hg)
    (fun n U g hg => isOpenCoverMap_sigmaDesc n U g hg) GT LT
    (fun s hs => hs.imp (fun hs => ⟨hs.1, hs.2.1, hs.2.2.1⟩) id)
    (fun s hs => by
      rcases hs with hs | hs
      · exact ⟨hs.1.2.2.1, hs.1.2.2.2.1⟩
      · exact ⟨inferInstance, inferInstance⟩)
    (fun s hs x => by
      rcases hs with hs | hs
      · obtain ⟨U, g, hg, hx, hl⟩ := exists_isOpenCoverMap_mem_mcLocalTriples hn hm s hs x
        exact ⟨U, g, hg, hx, Or.inl hl⟩
      · exact isEmptyElim x)
    (fun s N V j hj hd hcov hV => by
      rcases isEmpty_or_nonempty s.X with hX | hX
      · exact Or.inr hX
      · exact Or.inl (mem_mcLocalTriples_of_disjoint_cover hn s N V j hj hd hcov hV))
    (fun s hs Y h hh => by
      rcases isEmpty_or_nonempty Y with hY | hY
      · exact Or.inr hY
      · rcases hs with hs | hs
        · exact Or.inl (pullback_mem_mcLocalTriples hn s hs h hh)
        · exact Or.inr (Function.isEmpty h))
    𝓑
    (fun s hs Y h hh hhs hY => by
      rcases isEmpty_or_nonempty s.X with hX | hX
      · haveI := Function.isEmpty h
        simp only [𝓑, FieldBlowupTriple.pullback]
        rw [if_pos hX, if_pos ‹IsEmpty Y›]
        rfl
      · have hs' : s ∈ mcLocalTriples n m := hs.resolve_right (not_isEmpty_of_nonempty _)
        haveI : Nonempty Y := ⟨(hhs.surj hX.some).choose⟩
        have hY' : s.pullback h ∈ mcLocalTriples n m :=
          hY.resolve_right (not_isEmpty_of_nonempty (α := Y))
        simp only [𝓑]
        rw [if_neg (not_isEmpty_of_nonempty (α := s.X))]
        exact (if_neg (not_isEmpty_of_nonempty (α := Y))).trans
          (boLocal_pullback_of_isOpenCoverMap M hn hM hm s hs' h hh hhs hY'))
    t (Or.inl ht)
  have hex' : ∃ B : ClosedBlowupSequence t.X, ∀ (X' : Scheme.{u}) (g : X' ⟶ t.X),
      IsOpenCoverMap g → Surjective g → t.pullback g ∈ mcLocalTriples n m →
        B.pullback g = boLocal M m (t.pullback g) := by
    obtain ⟨B, hB⟩ := hex
    refine ⟨B, fun X' g hg hs hl => (hB X' g hg hs (Or.inl hl)).trans ?_⟩
    haveI : Nonempty X' := nonempty_of_hasDimensionIn hl.2.1
    simp only [𝓑]
    exact if_neg (not_isEmpty_of_nonempty (α := X'))
  unfold boFunctor
  rw [dif_pos hex']
  exact hex'.choose_spec X' g hg hsurj hloc

/-! ### `𝓑𝓞_{n,m}` is of order `m` -/

/-- A smooth blow-up sequence of order `m` starting with a triple is a smooth blow-up sequence. -/
private theorem isSmooth_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m → B.IsSmooth s
  | _, .nil _, _, _, _, _ => trivial
  | _, .cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.2.1, isSmooth_of_isOrderMTripleSeq m B _ _ _ h.2.2.2.2.2⟩

/-- `𝓑𝓞^H_{m!}(X, W(I), E)` is of order `m` for `(X, I, E)`: it is of order `m!` for
`(X, W(I), E)` (`boMaximalContact_isOrderMTripleSeq`), and tuning
(`isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd`) together with
`isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq` on both sides transfers the order. -/
private theorem boLocal_isOrderMTripleSeq_of_maxOrder_eq {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) (hmax : maxOrder t.I = m) :
    (boLocal M m t).IsOrderMTripleSeq t.sX t.I t.E m := by
  have hlt : ¬ maxOrder t.I < m := by simp [hmax]
  simp only [boLocal, hlt, ↓reduceIte]
  set tW : FieldBlowupTriple.{u} := ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩
  obtain ⟨hWmax, hWt, -⟩ := wellTunedTriple_spec hn hm t ht.1 ht.2.1 hmax
  replace hWt : IsTriple t.sX (wellTunedIdeal t.sX t.I) t.E := hWt
  obtain ⟨d, hd, hdim⟩ := ht.2.1
  rw [Set.mem_singleton_iff] at hd
  subst hd
  have hB := boMaximalContact_isOrderMTripleSeq (N := d) (n := d) (m := m.factorial) M hn hM tW
    hWt hdim hn le_rfl (Nat.factorial_pos m) hWmax
    (mcHypersurfaceChoice t) (isMCHypersurface_wellTunedIdeal hn hm t ht hmax)
  set B := boMaximalContact M m.factorial tW (mcHypersurfaceChoice t)
  have hsm : B.IsSmooth t.sX := isSmooth_of_isOrderMTripleSeq _ B _ _ _ hB
  have hIt : IsTriple t.sX t.I t.E := ht.1
  have hmn : (maxOrder t.I).toNat = m := by simp [hmax]
  have h1 := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX
    (wellTunedIdeal t.sX t.I) t.E hWt m.factorial hWmax B).1.2 hB
  have h2 := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd
    t.sX t.I t.E hIt (pos_dim_of_mem_irreducibleComponents hn t ht.1 ht.2.1)
    (by omega) m.factorial (Nat.factorial_pos m) (hmn ▸ Nat.dvd_factorial (by omega) le_rfl)
    B hsm).2 (by simpa [wellTunedIdeal, hmn] using h1)
  rw [hmn] at h2
  exact (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E hIt m
    hmax B).1.1 h2

/-- In the maximal-order case `𝓑_{n,m}` is `𝓑𝓞^H_{m!}(X, W(I), E)`, a reduction, so it has no
empty blow-ups. -/
private theorem boLocal_hasNoEmptyBlowups_of_maxOrder_eq {m : ℕ} (M : MarkedFamily.{u})
    (t : FieldBlowupTriple.{u}) (hmax : maxOrder t.I = m) :
    (boLocal M m t).HasNoEmptyBlowups := by
  have hlt : ¬ maxOrder t.I < m := by simp [hmax]
  simp only [boLocal, hlt, ↓reduceIte, boMaximalContact]
  exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _

/-- `𝓑_{n,m}` is a smooth blow-up sequence of order `m` without empty blow-ups. -/
private theorem boLocal_isOrderMTripleSeq {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) :
    (boLocal M m t).IsOrderMTripleSeq t.sX t.I t.E m ∧ (boLocal M m t).HasNoEmptyBlowups := by
  by_cases hlt : maxOrder t.I < m
  · simp only [boLocal, hlt, ↓reduceIte]
    exact ⟨ht.1, trivial⟩
  · have hmax := le_antisymm ht.2.2.1 (not_lt.1 hlt)
    exact ⟨boLocal_isOrderMTripleSeq_of_maxOrder_eq M hn hM hm t ht hmax,
      boLocal_hasNoEmptyBlowups_of_maxOrder_eq M t hmax⟩

/-- The canonical lift of a surjective open cover map along a blow-up is a surjective open cover
map (blow-ups commute with flat base change). -/
private theorem isOpenCoverMap_canonicalLift {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (Z : X.IdealSheafData) :
    IsOpenCoverMap (canonicalLift g Z) ∧ Surjective (canonicalLift g Z) := by
  haveI : Smooth g := smooth_of_isOpenCoverMap hg
  exact ⟨isOpenCoverMap_of_isPullback (Kollar.isPullback_canonicalLift_of_flat g Z) hg,
    Kollar.surjective_canonicalLift g Z⟩

/-- The pieces `U_a.ι ≫ g` of a surjective open cover map are open immersions covering the
target. -/
private theorem exists_pieces_of_isOpenCoverMap {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) :
    ∃ (r : ℕ) (U : Fin r → X'.Opens), (∀ a, IsOpenImmersion ((U a).ι ≫ g)) ∧
      (∀ y : X', ∃ a, y ∈ U a) ∧ ∀ x : X, ∃ a, ∃ v : (U a : Scheme.{u}), ((U a).ι ≫ g) v = x := by
  obtain ⟨r, U, -, hU, hi⟩ := hg
  have hmem : ∀ y : X', ∃ a, y ∈ U a := fun y => by
    have hy : y ∈ ⨆ a, U a := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨r, U, hi, hmem, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hs.surj x
  obtain ⟨a, ha⟩ := hmem y
  exact ⟨a, ⟨y, ha⟩, rfl⟩

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- An irreducible closed set meeting the image of an open embedding is the closure of its
trace on the image. -/
private theorem closure_image_preimage_of_isIrreducible (hf : Topology.IsOpenEmbedding f)
    {C : Set α} (hC : IsIrreducible C) (hCc : IsClosed C) (hne : (f ⁻¹' C).Nonempty) :
    closure (f '' (f ⁻¹' C)) = C := by
  rw [Set.image_preimage_eq_inter_range]
  refine le_antisymm (hCc.closure_subset_iff.2 Set.inter_subset_left) ?_
  obtain ⟨b, hb⟩ := hne
  exact subset_closure_inter_of_isPreirreducible_of_isOpen hC.isPreirreducible hf.isOpen_range
    ⟨f b, hb, b, rfl⟩

/-- The trace of an irreducible component of a closed `D` on an open subspace it meets is an
irreducible component of the trace of `D`. -/
private theorem preimage_mem_componentsOf_of_nonempty (hf : Topology.IsOpenEmbedding f)
    {D C : Set α} (hD : IsClosed D) (hC : C ∈ componentsOf D) (hne : (f ⁻¹' C).Nonempty) :
    f ⁻¹' C ∈ componentsOf (f ⁻¹' D) := by
  have hCc := Aux.isClosed_of_mem_componentsOf hD hC
  refine ⟨⟨⟨hne, hC.1.1.isPreirreducible.preimage hf⟩, Set.preimage_mono hC.1.2⟩, ?_⟩
  rintro S ⟨hS, hSD⟩ hle
  have h1 : IsIrreducible (closure (f '' S)) := (hS.image f hf.continuous.continuousOn).closure
  have h2 : closure (f '' S) ⊆ D :=
    closure_minimal ((Set.image_mono hSD).trans (Set.image_preimage_subset f D)) hD
  have h3 : C ⊆ closure (f '' S) := by
    rw [← closure_image_preimage_of_isIrreducible hf hC.1.1 hCc hne]
    exact closure_mono (Set.image_mono hle)
  have := hC.2 ⟨h1, h2⟩ h3
  intro b hb
  exact this (subset_closure ⟨b, hb, rfl⟩)

/-- The closure of the image of an irreducible component of the trace of a closed `D` on an
open subspace is an irreducible component of `D`, whose trace it is. -/
private theorem closure_image_mem_componentsOf (hf : Topology.IsOpenEmbedding f) {D : Set α}
    (hD : IsClosed D) {T : Set β} (hT : T ∈ componentsOf (f ⁻¹' D)) :
    closure (f '' T) ∈ componentsOf D ∧ f ⁻¹' closure (f '' T) = T := by
  have hTc := Aux.isClosed_of_mem_componentsOf (hD.preimage hf.continuous) hT
  have hpre : f ⁻¹' closure (f '' T) = T := by
    rw [hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous,
      Set.preimage_image_eq _ hf.injective, hTc.closure_eq]
  refine ⟨⟨⟨(hT.1.1.image f hf.continuous.continuousOn).closure,
    closure_minimal ((Set.image_mono hT.1.2).trans (Set.image_preimage_subset f D)) hD⟩, ?_⟩,
    hpre⟩
  rintro S ⟨hS, hSD⟩ hle
  have hSne : (f ⁻¹' S).Nonempty := by
    obtain ⟨b, hb⟩ := hT.1.1.nonempty
    exact ⟨b, hle (subset_closure ⟨b, hb, rfl⟩)⟩
  have h1 : f ⁻¹' S ⊆ T := hT.2 ⟨⟨hSne, hS.isPreirreducible.preimage hf⟩, Set.preimage_mono hSD⟩
    (by rw [← hpre]; exact Set.preimage_mono hle)
  obtain ⟨b, hb⟩ := hSne
  refine (subset_closure_inter_of_isPreirreducible_of_isOpen hS.isPreirreducible hf.isOpen_range
    ⟨f b, hb, b, rfl⟩).trans (closure_mono ?_)
  rintro _ ⟨hx, c, rfl⟩
  exact ⟨c, h1 hx, rfl⟩

/-- A closed irreducible `C` meeting the image of an open embedding is an irreducible component
of a closed `D` exactly when its trace is one of the trace of `D`. -/
private theorem mem_componentsOf_iff_preimage_of_nonempty (hf : Topology.IsOpenEmbedding f)
    {D C : Set α} (hD : IsClosed D) (hC : IsIrreducible C) (hCc : IsClosed C)
    (hne : (f ⁻¹' C).Nonempty) :
    C ∈ componentsOf D ↔ f ⁻¹' C ∈ componentsOf (f ⁻¹' D) :=
  ⟨fun h => preimage_mem_componentsOf_of_nonempty hf hD h hne, fun h => by
    have := (closure_image_mem_componentsOf hf hD h).1
    rwa [closure_image_preimage_of_isIrreducible hf hC hCc hne] at this⟩

end Topology

/-- The support of `g⁻¹I` is the inverse image of the support of `I`. -/
private theorem coe_support_comap_eq {X Y : Scheme.{u}} (g : Y ⟶ X) (I : X.IdealSheafData) :
    ((I.comap g).support : Set Y) = g ⁻¹' (I.support : Set X) :=
  Set.ext (mem_support_comap_iff g I)

/-- An irreducible component `T` of the inverse image of a closed `D` under an open cover map
`g` maps to the irreducible component `closure (g T)` of `D`, of the same codimension; and `T` is
an irreducible component of the inverse image of another closed `D'` exactly when
`closure (g T)` is one of `D'`. -/
private theorem closure_image_mem_componentsOf_of_isOpenCoverMap {X X' : Scheme.{u}}
    {g : X' ⟶ X} (hg : IsOpenCoverMap g) {D : Set X} (hD : IsClosed D) {T : Set X'}
    (hT : T ∈ componentsOf (g ⁻¹' D)) :
    ∃ hC : closure (g '' T) ∈ componentsOf D,
      codimension (irreducibleClosure hT.1.1) = codimension (irreducibleClosure hC.1.1) ∧
      ∀ D' : Set X, IsClosed D' →
        (T ∈ componentsOf (g ⁻¹' D') ↔ closure (g '' T) ∈ componentsOf D') := by
  obtain ⟨r, U, hd, hU, hi⟩ := hg
  obtain ⟨y, hy⟩ := hT.1.1.nonempty
  have hy' : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
  have hTc : IsClosed T := Aux.isClosed_of_mem_componentsOf (hD.preimage g.continuous) hT
  have hsub : T ⊆ U a := exists_subset_of_isIrreducible hd hU hT.1.1 hy a ha
  haveI := hi a
  have hTimg : (U a).ι '' ((U a).ι ⁻¹' T) = T :=
    Set.image_preimage_eq_of_subset (by rw [Scheme.Opens.range_ι]; exact hsub)
  have hne : ((U a).ι ⁻¹' T).Nonempty := ⟨⟨y, ha⟩, hy⟩
  have hgT : g '' T = ((U a).ι ≫ g) '' ((U a).ι ⁻¹' T) := by
    conv_lhs => rw [← hTimg]
    rw [Set.image_image]
    rfl
  have hpre : ∀ D' : Set X, ((U a).ι ≫ g) ⁻¹' D' = (U a).ι ⁻¹' (g ⁻¹' D') := fun _ => rfl
  have hiff : ∀ D' : Set X, IsClosed D' → (T ∈ componentsOf (g ⁻¹' D') ↔
      (U a).ι ⁻¹' T ∈ componentsOf (((U a).ι ≫ g) ⁻¹' D')) := fun D' hD' => by
    rw [hpre]
    exact mem_componentsOf_iff_preimage_of_nonempty (U a).ι.isOpenEmbedding
      (hD'.preimage g.continuous) hT.1.1 hTc hne
  have hS : (U a).ι ⁻¹' T ∈ componentsOf (((U a).ι ≫ g) ⁻¹' D) := (hiff D hD).1 hT
  obtain ⟨hC, hCpre⟩ := closure_image_mem_componentsOf ((U a).ι ≫ g).isOpenEmbedding hD hS
  let V₀ : IrreducibleCloseds (U a) := ⟨(U a).ι ⁻¹' T, hS.1.1, hTc.preimage (U a).ι.continuous⟩
  have h1 : irreducibleClosure hT.1.1 =
      IrreducibleCloseds.map (U a).ι (U a).ι.continuous V₀ := by
    ext1
    show closure T = closure ((U a).ι '' ((U a).ι ⁻¹' T))
    rw [hTimg]
  rw [hgT]
  refine ⟨hC, ?_, fun D' hD' => ?_⟩
  · have h2 : irreducibleClosure hC.1.1 =
        IrreducibleCloseds.map ((U a).ι ≫ g) ((U a).ι ≫ g).continuous V₀ := by
      ext1
      exact closure_closure
    rw [h1, h2, codimension_map_of_isOpenImmersion, codimension_map_of_isOpenImmersion]
  · rw [hiff D' hD', mem_componentsOf_iff_preimage_of_nonempty ((U a).ι ≫ g).isOpenEmbedding hD'
      hC.1.1 isClosed_closure (by rw [hCpre]; exact hne), hCpre]

/-- Every irreducible component `C` of a closed `D` through `g y`, for an open cover map `g`,
is `closure (g T)` for an irreducible component `T` of `g⁻¹D` through `y`. -/
private theorem exists_mem_componentsOf_preimage_of_isOpenCoverMap {X X' : Scheme.{u}}
    {g : X' ⟶ X} (hg : IsOpenCoverMap g) {D : Set X} (hD : IsClosed D) {C : Set X}
    (hC : C ∈ componentsOf D) (y : X') (hy : g y ∈ C) :
    ∃ T ∈ componentsOf (g ⁻¹' D), y ∈ T ∧ closure (g '' T) = C := by
  obtain ⟨r, U, -, hU, hi⟩ := hg
  have hy' : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
  haveI := hi a
  have hCc := Aux.isClosed_of_mem_componentsOf hD hC
  have hne : (((U a).ι ≫ g) ⁻¹' C).Nonempty := ⟨⟨y, ha⟩, hy⟩
  have hS := preimage_mem_componentsOf_of_nonempty ((U a).ι ≫ g).isOpenEmbedding hD hC hne
  have hS' : ((U a).ι ≫ g) ⁻¹' C ∈ componentsOf ((U a).ι ⁻¹' (g ⁻¹' D)) := hS
  obtain ⟨hT, -⟩ := closure_image_mem_componentsOf (U a).ι.isOpenEmbedding
    (hD.preimage g.continuous) hS'
  refine ⟨_, hT, subset_closure ⟨⟨y, ha⟩, hy, rfl⟩, ?_⟩
  rw [closure_image_closure g.continuous, Set.image_image]
  exact closure_image_preimage_of_isIrreducible ((U a).ι ≫ g).isOpenEmbedding hC.1.1 hCc hne

/-- The components of codimension `≥ 2` pull back along an open cover map. -/
private theorem preimage_componentsOfCodimAtLeastTwo_of_isOpenCoverMap {X X' : Scheme.{u}}
    {g : X' ⟶ X} (hg : IsOpenCoverMap g) {D : Set X} (hD : IsClosed D) :
    g ⁻¹' componentsOfCodimAtLeastTwo D = componentsOfCodimAtLeastTwo (g ⁻¹' D) := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨C, hC, hcod, hy⟩
    obtain ⟨T, hT, hyT, hTC⟩ := exists_mem_componentsOf_preimage_of_isOpenCoverMap hg hD hC y hy
    obtain ⟨hC', hcod', -⟩ := closure_image_mem_componentsOf_of_isOpenCoverMap hg hD hT
    refine ⟨T, hT, ?_, hyT⟩
    subst hTC
    rwa [hcod']
  · rintro ⟨T, hT, hcod, hy⟩
    obtain ⟨hC, hcod', -⟩ := closure_image_mem_componentsOf_of_isOpenCoverMap hg hD hT
    exact ⟨_, hC, hcod' ▸ hcod, subset_closure ⟨y, hy, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The triple conditions descend along a
surjective open cover map: smoothness, finite type and the snc condition are local
(`of_forall_exists_isOpenImmersion`, `isOrderedSNC_of_disjoint_cover` on the pieces
`U_a.ι ≫ g`), quasi-compactness passes to the image, and the local dimensions agree
(`topologicalKrullDimAt_of_isOpenCoverMap`). -/
private theorem isTriple_of_comap_of_isOpenCoverMap {k : Type u} [Field k] {X X' : Scheme.{u}}
    {g : X' ⟶ X} (hg : IsOpenCoverMap g) (hs : Surjective g) (s : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (E : OrderedDivisor X)
    (h : IsTriple (g ≫ s) (I.comap g) (E.comap g)) : IsTriple s I E := by
  obtain ⟨r, U, hi, -, hpt⟩ := exists_pieces_of_isOpenCoverMap hg hs
  let t : FieldBlowupTriple.{u} := { X := X, I := I, E := E, k := k, sX := s }
  have ht' : t.pullback g ∈ triples := h
  have hV : ∀ a, t.pullback ((U a).ι ≫ g) ∈ triples := fun a => by
    rw [← fieldBlowupTriple_pullback_pullback]
    exact pullback_mem_triples_of_isOpenCoverMap (t.pullback g) ht' (U a).ι
      (isOpenCoverMap_of_isOpenImmersion (U a).ι)
  haveI := hi
  have hLFT : LocallyOfFiniteType s :=
    of_forall_exists_isOpenImmersion @LocallyOfFiniteType s (fun a => (U a).ι ≫ g)
      hpt fun a _ => (hV a).2.2.1
  haveI := hLFT
  haveI : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr hLFT
  have hsm : Smooth s := of_forall_exists_isOpenImmersion @Smooth s (fun a => (U a).ι ≫ g)
    hpt fun a _ => by
      haveI : LocallyOfFinitePresentation (((U a).ι ≫ g) ≫ s) :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType
          (f := ((U a).ι ≫ g) ≫ s)).mpr (hV a).2.2.1
      exact (MMP.Mori.isSmoothScheme_iff _).1 (hV a).2.1
  haveI : LocallyOfFiniteType (g ≫ s) := h.2.2.1
  haveI : CompactSpace X' := (quasiCompact_iff_compactSpace (g ≫ s)).1 h.2.2.2.1
  haveI : CompactSpace X := ⟨by
    rw [← Set.range_eq_univ.2 hs.surj]
    exact isCompact_range g.continuous⟩
  have he : Equidimensional X := by
    have key : ∀ Z ∈ irreducibleComponents X, ∃ y : X',
        topologicalKrullDim Z = topologicalKrullDim (irreducibleComponent y) := by
      intro Z hZ
      obtain ⟨η, -, hη⟩ := topologicalKrullDim_eq_topologicalKrullDimAt k s hZ
      obtain ⟨y, rfl⟩ := hs.surj η
      refine ⟨y, ?_⟩
      rw [← hη, ← topologicalKrullDimAt_of_isOpenCoverMap hg y,
        topologicalKrullDimAt_eq_topologicalKrullDim_of_mem k (g ≫ s) h.2.2.2.2.1
          (irreducibleComponent_mem_irreducibleComponents y) y]
    intro Z hZ Z' hZ'
    obtain ⟨y, hy⟩ := key Z hZ
    obtain ⟨y', hy'⟩ := key Z' hZ'
    rw [hy, hy']
    exact h.2.2.2.2.1 _ (irreducibleComponent_mem_irreducibleComponents y) _
      (irreducibleComponent_mem_irreducibleComponents y')
  have hnz := isNonzeroAtGenericPoints_of_forall_exists_isOpenImmersion t.I
    (fun a => (U a).ι ≫ g) hpt fun a _ => (hV a).2.2.2.2.2.1
  haveI : CharZero k := h.1
  have hsnc := isOrderedSNC_of_disjoint_cover t r (fun a => (U a : Scheme.{u}))
    (fun a => (U a).ι ≫ g) hi (by
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨a, v, hv⟩ := hpt x
      exact ⟨a, v, hv⟩) fun a => Or.inl (hV a)
  exact ⟨h.1, (MMP.Mori.isSmoothScheme_iff _).2 hsm, hLFT,
    quasiCompact_of_compactSpace _, he, hnz, hsnc⟩

/-- Smoothness of a closed subscheme descends
along a surjective open cover map (`isSmoothScheme_subscheme_of_comap` on the pieces). -/
private theorem isSmoothScheme_subscheme_of_isOpenCoverMap {k : Type u} [Field k]
    {X X' : Scheme.{u}} {g : X' ⟶ X} (hg : IsOpenCoverMap g) (hs : Surjective g)
    (s : X ⟶ Spec (.of k)) (Z : X.IdealSheafData)
    (h : MMP.Mori.IsSmoothScheme ((Z.comap g).subschemeι ≫ g ≫ s)) :
    MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) := by
  obtain ⟨r, U, hi, -, hpt⟩ := exists_pieces_of_isOpenCoverMap hg hs
  haveI := hi
  refine isSmoothScheme_subscheme_of_comap s (fun a => (U a).ι ≫ g) hpt Z fun a => ?_
  haveI := MMP.Mori.IsSmoothScheme.smooth h
  set H := Z.comap g
  have he : (H.comap (U a).ι).subschemeι ≫ (U a).ι ≫ g ≫ s =
      (H.comapIso (U a).ι).hom ≫ Limits.pullback.snd (U a).ι H.subschemeι ≫
        H.subschemeι ≫ g ≫ s := by
    rw [← H.comapIso_hom_fst (U a).ι, Category.assoc, Limits.pullback.condition_assoc]
  rw [Scheme.IdealSheafData.comap_comp, Category.assoc]
  rw [he]
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- Positive codimension of the components of the centre descends along a surjective open cover
map: an irreducible component of `supp Z` meets
the image of some piece `U_a.ι ≫ g`; its inverse image is (the trace of) an irreducible component
of `supp g⁻¹Z`, of the same codimension. -/
private theorem hasComponentsOfPositiveCodim_of_isOpenCoverMap {X X' : Scheme.{u}}
    {g : X' ⟶ X} (hg : IsOpenCoverMap g) (hs : Surjective g) (Z : X.IdealSheafData)
    (h : HasComponentsOfPositiveCodim ((Z.comap g).support : Set X')) :
    HasComponentsOfPositiveCodim (Z.support : Set X) := by
  intro W hW
  obtain ⟨x, hx⟩ := hW.1.1.nonempty
  obtain ⟨y, rfl⟩ := hs.surj x
  obtain ⟨T, hT, -, hTC⟩ :=
    exists_mem_componentsOf_preimage_of_isOpenCoverMap hg Z.support.2 hW y hx
  have hT' : T ∈ componentsOf ((Z.comap g).support : Set X') := by
    rwa [coe_support_comap_eq]
  obtain ⟨hC, hcod, -⟩ := closure_image_mem_componentsOf_of_isOpenCoverMap hg Z.support.2 hT
  subst hTC
  rw [← hcod]
  exact h T hT'

/-- An open cover map induces isomorphisms on stalks. -/
private theorem isIso_stalkMap_of_isOpenCoverMap {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (y : X') : IsIso (g.stalkMap y) := by
  obtain ⟨r, U, -, hU, hi⟩ := hg
  have hy : y ∈ ⨆ a, U a := hU ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  haveI := hi a
  obtain ⟨v, rfl⟩ : y ∈ Set.range (U a).ι := by rw [Scheme.Opens.range_ι]; exact ha
  have h1 : IsIso (((U a).ι ≫ g).stalkMap v) :=
    inferInstanceAs <| IsIso (((U a).ι ≫ g).toLRSHom.stalkMap v)
  have h2 : IsIso ((U a).ι.stalkMap v) :=
    inferInstanceAs <| IsIso ((U a).ι.toLRSHom.stalkMap v)
  rw [Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap ((U a).ι v)) ((U a).ι.stalkMap v) h2 h1

/-- snc with the boundary is a condition at the points of the centre, and `g` is a local
isomorphism: it descends along a surjective open cover map. -/
private theorem hasSNCWith_of_isOpenCoverMap {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (h : HasSNCWith (E.comap g).E (Z.comap g)) : HasSNCWith E.E Z := by
  intro x hx
  obtain ⟨u, rfl⟩ := hs.surj x
  obtain ⟨n, z, c, J, hz, hE, hinj, hZ⟩ := h u ((mem_support_comap_iff g Z u).2 hx)
  haveI : IsIso (g.stalkMap u) := isIso_stalkMap_of_isOpenCoverMap hg u
  let e' := (asIso (g.stalkMap u)).commRingCatIsoToRingEquiv
  have hmem : ∀ i, u ∈ ((E.comap g).E i).support ↔ g u ∈ (E.E i).support := fun i =>
    mem_support_comap_iff g (E.E i) u
  have hback : ∀ (K : X.IdealSheafData) (A : Ideal (X'.presheaf.stalk u)),
      IdealSheafData.stalk (K.comap g) u = A →
        IdealSheafData.stalk K (g u) = A.map (e'.symm : _ →+* _) := by
    intro K A hA
    rw [IdealSheafData.stalk_comap] at hA
    rw [← hA]
    exact (Ideal.map_of_equiv (f := e')).symm
  refine ⟨n, fun i => e'.symm (z i), fun i => c ⟨i.1, (hmem i.1).2 i.2⟩, J,
    isRegularSystemOfParameters_map_ringEquiv e'.symm hz, ?_, ?_, ?_⟩
  · intro i
    rw [hback _ _ (hE ⟨i.1, (hmem i.1).2 i.2⟩), Ideal.map_span, Set.image_singleton]
    rfl
  · intro i i' hii
    exact Subtype.ext (congrArg (fun t => t.1) (hinj hii))
  · rw [hback _ _ hZ, Ideal.map_span, ← Set.image_comp]
    rfl

/-- `ord_Z I = m` descends along a surjective open cover map: the generic point of each
irreducible component of `supp Z` lifts to the generic point of an irreducible component of
`supp g⁻¹Z`,
and `ord` is preserved (`multAt_comap_of_isOpenCoverMap`). -/
private theorem orderAlongEq_of_isOpenCoverMap {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (I Z : X.IdealSheafData) (m : ℕ)
    (h : OrderAlongEq (I.comap g) ((Z.comap g).support : Set X') m) :
    OrderAlongEq I (Z.support : Set X) m := by
  intro W hW
  obtain ⟨x, hx⟩ := hW.1.1.nonempty
  obtain ⟨y, rfl⟩ := hs.surj x
  obtain ⟨T, hT, -, hTC⟩ :=
    exists_mem_componentsOf_preimage_of_isOpenCoverMap hg Z.support.2 hW y hx
  have hT' : T ∈ componentsOf ((Z.comap g).support : Set X') := by
    rwa [coe_support_comap_eq]
  have h1 := h T hT'
  unfold orderAlong at h1 ⊢
  rw [multAt_comap_of_isOpenCoverMap hg] at h1
  have hWc : closure W = W := (Aux.isClosed_of_mem_componentsOf Z.support.2 hW).closure_eq
  have hgen : g hT'.1.1.genericPoint = hW.1.1.genericPoint := by
    have h2 := hT'.1.1.isGenericPoint_genericPoint_closure.image g.continuous
    rw [closure_image_closure g.continuous, hTC] at h2
    have h3 := hW.1.1.isGenericPoint_genericPoint_closure
    rw [hWc] at h3
    exact h2.eq h3
  rw [← hgen]
  exact h1

/-- Along a smooth centre of constant order `m`, the divisor of the controlled transform is
`I_F^m`. -/
private theorem controlledTransformDivisorIdeal_eq_pow' {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  have hfun : (fun W : componentsOf (Z.support : Set X) => (orderAlong I W.2.1.1).toNat) =
      fun _ => m := funext fun W => by rw [hord W.1 W.2]; rfl
  rw [controlledTransformDivisorIdeal_eq_exceptionalDivisorIdeal, hfun]
  refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
  obtain ⟨n, hn, -, hW⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ (fun _ => m) y
  rw [hn, IdealSheafData.stalk_pow]
  by_cases hx : blowUpToBase Z y ∈ (Z.support : Set X)
  · obtain ⟨W, rfl⟩ := hW hx
    rfl
  · have htop : IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y = ⊤ := by
      rwa [IdealSheafData.stalk_eq_top_iff_notMem_support, Scheme.IdealSheafData.support_comap]
    rw [htop, Ideal.top_pow, Ideal.top_pow]

/-- Along a smooth centre along which `ord_Z I = m`, the controlled transform of `I` is the
ideal of the birational transform of the marked ideal `(I, m)`. -/
private theorem controlledTransform_eq_birationalTransform_I {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (I : X.IdealSheafData) (m : ℕ)
    (hord : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransform Z I = (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I := by
  show idealColon _ _ = idealColon _ _
  rw [controlledTransformDivisorIdeal_eq_pow' sX hX Z hZ I m hord]

/-- The controlled transform commutes with the canonical lift of any morphism `g` along which
the smoothness and the order of the centre are preserved: both sides are birational transforms
of the marked ideal `(I, m)` (Kollár 3.62). -/
private theorem controlledTransform_comap_canonicalLift {k : Type u} [Field k]
    {X X' : Scheme.{u}} {g : X' ⟶ X} (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s)
    [LocallyOfFiniteType s] [QuasiCompact s] (hX' : MMP.Mori.IsSmoothScheme (g ≫ s))
    [LocallyOfFiniteType (g ≫ s)] [QuasiCompact (g ≫ s)] (I Z : X.IdealSheafData) (m : ℕ)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s))
    (hZ' : MMP.Mori.IsSmoothScheme ((Z.comap g).subschemeι ≫ g ≫ s))
    (hord : OrderAlongEq I (Z.support : Set X) m)
    (hord' : OrderAlongEq (I.comap g) ((Z.comap g).support : Set X') m) :
    MMP.Resolution.controlledTransform (Z.comap g) (I.comap g) =
      (MMP.Resolution.controlledTransform Z I).comap (canonicalLift g Z) := by
  rw [controlledTransform_eq_birationalTransform_I (g ≫ s) hX' (Z.comap g) hZ' (I.comap g) m
    hord', controlledTransform_eq_birationalTransform_I s hX Z hZ I m hord]
  have ha : I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ m :=
    comap_le_comap_pow_of_stalk_le _ _ _ _
      (stalk_le_pow_of_orderAlongGE s hX Z hZ I m fun W hW => (hord W hW).ge)
  exact congrArg MarkedIdeal.I
    (Kollar.birationalTransform_comap_eq_comap_canonicalLift g Z ⟨I, m⟩ ha)

/-- The total transform commutes with the canonical lift of an open cover map: the components
of the centre, their codimensions and the components of `Supp E` correspond along `g`. -/
private theorem totalTransform_comap_canonicalLift {X X' : Scheme.{u}} {g : X' ⟶ X}
    (hg : IsOpenCoverMap g) (hs : Surjective g) (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    (E.comap g).totalTransform (Z.comap g) = (E.totalTransform Z).comap (canonicalLift g Z) := by
  set cl := canonicalLift g Z
  obtain ⟨hcl, -⟩ := isOpenCoverMap_canonicalLift hg hs Z
  haveI : Smooth cl := smooth_of_isOpenCoverMap hcl
  have hred := IsReducedFlatBaseChange.of_smooth cl
  haveI := hred.universallyOpen
  have hfun : ∀ S : Set X, cl ⁻¹' (blowUpToBase Z ⁻¹' S) =
      blowUpToBase (Z.comap g) ⁻¹' (g ⁻¹' S) := by
    intro S
    rw [← Set.preimage_comp, ← Set.preimage_comp, ← TopCat.coe_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, canonicalLift_comp_blowUpToBase]
  have hvan : ∀ S : Set (blowUp Z),
      (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure S)).comap cl =
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (cl ⁻¹' S)) := by
    intro S
    refine hred.comap_vanishingIdeal _ _ ?_
    exact (cl.isOpenMap.preimage_closure_eq_closure_preimage cl.continuous S).symm
  have hsc := coe_support_comap_eq g Z
  have hsE : ∀ i, (((E.E i).comap g).support : Set X') = g ⁻¹' ((E.E i).support : Set X) :=
    fun i => coe_support_comap_eq g (E.E i)
  have hEs : OrderedDivisor.support (⟨E.s, fun i => (E.E i).comap g⟩ : OrderedDivisor X') =
      g ⁻¹' E.support := by
    simp only [OrderedDivisor.support, Set.preimage_iUnion]
    exact Set.iUnion_congr hsE
  have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.2
  have hWc : IsClosed (Z.support : Set X) := Z.support.2
  have key : ∀ i : Fin (E.s + 1), totalTransformSet (E.comap g) (Z.comap g) i =
      cl ⁻¹' totalTransformSet E Z i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [OrderedDivisor.comap, totalTransformSet, Fin.snoc_last, Set.preimage_iUnion,
        hfun]
      rw [hEs, hsc]
      ext y
      simp only [Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨T, hT, hTE, hy⟩
        obtain ⟨hC, -, hiff⟩ := closure_image_mem_componentsOf_of_isOpenCoverMap hg hWc hT
        exact ⟨_, hC, fun hCE => hTE ((hiff _ hEc).2 hCE), subset_closure ⟨_, hy, rfl⟩⟩
      · rintro ⟨C, hC, hCE, hy⟩
        obtain ⟨T, hT, hyT, hTC⟩ :=
          exists_mem_componentsOf_preimage_of_isOpenCoverMap hg hWc hC _ hy
        obtain ⟨-, -, hiff⟩ := closure_image_mem_componentsOf_of_isOpenCoverMap hg hWc hT
        exact ⟨T, hT, fun hTE => hCE (hTC ▸ (hiff _ hEc).1 hTE), hyT⟩
    · simp only [totalTransformSet, Fin.snoc_castSucc, OrderedDivisor.comap]
      rw [hfun, hsc, hsE, ← preimage_componentsOfCodimAtLeastTwo_of_isOpenCoverMap hg hWc]
      simp only [Set.preimage_diff]
  have key2 : ∀ i : Fin (E.s + 1), ((E.comap g).totalTransform (Z.comap g)).E i =
      ((E.totalTransform Z).E i).comap cl := by
    intro i
    have h1 := totalTransform_E_eq (E.comap g) (Z.comap g) i
    have h2 := totalTransform_E_eq E Z i
    rw [key i] at h1
    rw [h1, h2, hvan]
  exact congrArg (OrderedDivisor.mk (E.s + 1)) (funext key2)

/-- **Descent of smooth blow-up sequences of order `m`** along a surjective open cover map: each
condition is local on `X_i` and is reflected by the surjective open cover maps `g_i`, and the
controlled and total transforms commute with them. -/
private theorem isOrderMTripleSeq_of_pullback {k : Type u} [Field k] (m : ℕ) :
    ∀ {X X' : Scheme.{u}} (B : ClosedBlowupSequence X) (g : X' ⟶ X), IsOpenCoverMap g →
      Surjective g → ∀ (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X),
      (B.pullback g).IsOrderMTripleSeq (g ≫ s) (I.comap g) (E.comap g) m →
      B.IsOrderMTripleSeq s I E m
  | _, _, .nil _, g, hg, hs, s, I, E, h => isTriple_of_comap_of_isOpenCoverMap hg hs s I E h
  | _, _, .cons Z B, g, hg, hs, s, I, E, h => by
    obtain ⟨hT, hZs, hZc, hZe, hZo, hB⟩ := h
    have hT' := isTriple_of_comap_of_isOpenCoverMap hg hs s I E hT
    have hZs' := isSmoothScheme_subscheme_of_isOpenCoverMap hg hs s Z hZs
    have hZc' := hasComponentsOfPositiveCodim_of_isOpenCoverMap hg hs Z hZc
    have hZo' := orderAlongEq_of_isOpenCoverMap hg hs I Z m hZo
    refine ⟨hT', hZs', hZc', hasSNCWith_of_isOpenCoverMap hg hs E Z hZe, hZo', ?_⟩
    obtain ⟨hg', hs'⟩ := isOpenCoverMap_canonicalLift hg hs Z
    refine isOrderMTripleSeq_of_pullback m B (canonicalLift g Z) hg' hs' _ _ _ ?_
    haveI : LocallyOfFiniteType s := hT'.2.2.1
    haveI : QuasiCompact s := hT'.2.2.2.1
    haveI : LocallyOfFiniteType (g ≫ s) := hT.2.2.1
    haveI : QuasiCompact (g ≫ s) := hT.2.2.2.1
    rw [controlledTransform_comap_canonicalLift s hT'.2.1 hT.2.1 I Z m hZs' hZs hZo' hZo,
      totalTransform_comap_canonicalLift hg hs E Z] at hB
    rwa [← Category.assoc, ← canonicalLift_comp_blowUpToBase, Category.assoc] at hB

/-- **Kollár, Thm. 3.103 (opening clause).** Let `𝓜` be a marked order-reduction family on
dimensions `0, …, n - 1` (`IsMarkedOrderReductionFamily`), `n, m ≥ 1`, and `(X, I, E)` a triple
with `dim X = n` and `maxord I ≤ m` (`idealTriplesOfDim`). Then `boFunctor M n m (X, I, E)` is a
smooth blow-up sequence of order `m` starting with `(X, I, E)`
(`ClosedBlowupSequence.IsOrderMTripleSeq`) without empty blow-ups
(`ClosedBlowupSequence.HasNoEmptyBlowups`). -/
@[mmp "lem_kr3e_bo_is_sequence_of_order_m"]
public theorem boFunctor_isOrderMTripleSeq {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {n} m) :
    (boFunctor M n m t).IsOrderMTripleSeq t.sX t.I t.E m ∧
      (boFunctor M n m t).HasNoEmptyBlowups := by
  unfold boFunctor
  split_ifs with h
  · -- The chosen sequence pulls back to `𝓑_{n,m}` along every local cover; descend along one.
    obtain ⟨X', g, hg, hsurj, hloc⟩ :=
      exists_surjective_isOpenCoverMap_mem_mcLocalTriples hn hm t ht
    have hpb := h.choose_spec X' g hg hsurj hloc
    obtain ⟨h1, h2⟩ := boLocal_isOrderMTripleSeq M hn hM hm _ hloc
    rw [← hpb] at h1 h2
    exact ⟨isOrderMTripleSeq_of_pullback m _ g hg hsurj _ _ _ h1,
      hasNoEmptyBlowups_of_pullback _ g h2⟩
  · exact ⟨ht.1, trivial⟩

/-! ### `𝓑𝓞^Y_1` along a smooth hypersurface -/

/-- Along an isomorphism `h`, the extension by closure of the pull-back `h^*𝐁` is `𝐁`. -/
private theorem extendByClosure_pullback_of_isIso : ∀ {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (h : Y ⟶ X) [IsIso h], (B.pullback h).extendByClosure h = B
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons Z B, h, _ => by
    have hc : ((Z.comap h).map h).comap h = Z.comap h :=
      ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion h _
    have hZ : (Z.comap h).map h = Z := by
      have := congrArg (fun W => W.comap (inv h)) hc
      simpa only [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
        Scheme.IdealSheafData.comap_id] using this
    simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.extendByClosure, dif_pos hc]
    rw [ClosedBlowupSequence.cons_eq_cons_iff]
    refine ⟨hZ, ?_⟩
    have key : ∀ (Z' : _) (e : Z' = Z) (p : blowUp (Z.comap h) = blowUp (Z'.comap h)),
        (B.pullback (canonicalLift h Z)).extendByClosure (eqToHom p ≫ canonicalLift h Z') ≍
          (B.pullback (canonicalLift h Z)).extendByClosure (canonicalLift h Z) := by
      rintro Z' rfl p
      rw [eqToHom_refl, Category.id_comp]
    haveI := MMP.Resolution.Kollar.isIso_canonicalLift h Z
    exact (key _ hZ _).trans (heq_of_eq (extendByClosure_pullback_of_isIso B _))

/-- Triples of dimension in `S` and maximal order `≤ m` are stable under pull-back along an
isomorphism. -/
private theorem pullback_mem_idealTriplesOfDim_of_isIso {S : Set ℕ} {m : ℕ}
    {t : FieldBlowupTriple.{u}} (ht : t ∈ idealTriplesOfDim S m) {Y : Scheme.{u}}
    (h : Y ⟶ t.X) [IsIso h] : t.pullback h ∈ idealTriplesOfDim S m := by
  haveI : QuasiCompact t.sX := ht.1.2.2.2.1
  let e : Y ≃ₜ t.X := Scheme.Hom.homeomorph h
  have hdim : topologicalKrullDim Y = topologicalKrullDim t.X :=
    IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph
  refine ⟨mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht.1) h,
    Equidimensional.of_homeomorph e ht.1.2.2.2.2.1⟩, ?_,
    (maxOrder_comap_le_of_isOpenCoverMap (isOpenCoverMap_of_isOpenImmersion h) t.I).trans ht.2.2⟩
  obtain ⟨d, hd, e⟩ := ht.2.1
  exact ⟨d, hd, hdim.trans e⟩

/-- A closed subscheme `H` containing the zero locus of an ideal `I` of maximal order `1`, i.e.
with `H ≤ I`, is nonempty. -/
private theorem support_nonempty_of_le_of_maxOrder_eq_one {X : Scheme.{u}}
    {I H : X.IdealSheafData} (hmax : maxOrder I = 1) (hHI : H ≤ I) :
    (H.support : Set X).Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x, multAt I x ≠ 0 := by
    by_contra! h
    have h0 : maxOrder I = 0 := by simp [maxOrder, maxOrderAlong, h]
    exact zero_ne_one (h0.symm.trans hmax)
  refine ⟨x, Scheme.IdealSheafData.support_antitone hHI ?_⟩
  by_contra h
  rw [multAt, (IdealSheafData.stalk_eq_top_iff_not_mem_support I x).2 h,
    MMP.Threefold.Resolution.idealOrder_top] at hx
  exact hx rfl

section Hypersurface

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [LocallyOfFiniteType sX]

/-- At a point of a smooth hypersurface `H` of a smooth scheme, the stalk of `H` is generated by
one member of a regular system of parameters: `𝒪_{X,x} / H_x` is regular and `H_x` is a prime of
height one. -/
private theorem exists_stalk_eq_span_parameter_of_isSmoothHypersurface
    (hX : MMP.Mori.IsSmoothScheme sX) {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) :
    ∀ x ∈ H.support, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (j : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ IdealSheafData.stalk H x = Ideal.span {z j} := by
  intro x hx
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance x
  have hq := MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk sX H hH.1 hx
  haveI : (IdealSheafData.stalk H x).IsPrime := by
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
  have hdim := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one _
    (MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne H hH.2 (x := x))
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) = m := by
    have hlt := ringKrullDim_lt_top (R := X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    have h0 := ringKrullDim_nonneg_of_nontrivial
      (R := X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)
    generalize ringKrullDim (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) = e at hlt h0 ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe m => exact ⟨m, rfl⟩
  obtain ⟨xs, ys, hs, -, hI⟩ := MMP.Flips.ResolutionInputs.exists_flag_isRegularSystemOfParameters
    le_rfl hq hdim hq (r := 1) (m := m) le_rfl (by rw [← hdim, hm]; push_cast; ring) hm
  exact ⟨1 + m, Fin.append xs ys, Fin.castAdd m 0, hs, by rw [hI, Fin.append_left]; rfl⟩

/-- A smooth hypersurface `H` of a smooth scheme is an ordered snc divisor `(H)`. -/
private theorem isOrderedSNC_singleton_of_isSmoothHypersurface (hX : MMP.Mori.IsSmoothScheme sX)
    {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) :
    (⟨1, fun _ => H⟩ : OrderedDivisor X).IsOrderedSNC sX := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  have hD := exists_stalk_eq_span_parameter_of_isSmoothHypersurface hX hH
  have hred : IsReduced H.subscheme := Aux.isReduced_subscheme_of_isSmoothScheme sX H hH.1
  refine ⟨fun _ => ⟨hred, isEffectiveCartierDivisor_of_stalk_eq_span_parameter H hD⟩,
    fun _ => ⟨hred, hH.2, hH.1⟩, fun x => ?_⟩
  by_cases hx : x ∈ H.support
  · obtain ⟨m, w, j, hw, hst⟩ := hD x hx
    exact ⟨m, w, fun _ => j, hw, fun _ => hst, fun a b _ => Subsingleton.elim a b⟩
  · haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp
        inferInstance x
    obtain ⟨m, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
    exact ⟨m, z, fun i => absurd i.2 hx, hz, fun i => absurd i.2 hx, fun a => absurd a.2 hx⟩

end Hypersurface

/-- `𝓑𝓓` returns a sequence without empty blow-ups. -/
private theorem reduction_bdFunctor (M : MarkedFamily.{u}) (d m j : ℕ) (t : FieldBlowupTriple.{u}) :
    (bdFunctor M d m j t).reduction = bdFunctor M d m j t := by
  unfold bdFunctor
  split_ifs
  · exact ClosedBlowupSequence.reduction_reduction _
  · rfl

/-- An ordered divisor with no entries is the empty one. -/
private theorem eq_empty_of_s_eq_zero {Y : Scheme.{u}} (D : OrderedDivisor Y) (h : D.s = 0) :
    D = OrderedDivisor.empty Y := by
  obtain ⟨s, E⟩ := D
  dsimp only at h
  subst h
  unfold OrderedDivisor.empty
  congr
  funext i
  exact i.elim0

open Classical in
/-- The last step of `boMaximalContact` when the separation sequence is empty: on `V = X`, a
triple that is the pull-back of `t₁` along `V ↪ X`, extension by closure of `𝓑𝓓` gives back
`𝓑𝓓(t₁)`. -/
private theorem extendByClosure_bdFunctor_eq {N d : ℕ} (M : MarkedFamily.{u}) (hN : 1 ≤ N)
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (t₁ : FieldBlowupTriple.{u})
    (ht₁ : t₁ ∈ idealTriplesOfDim (Set.Icc 1 N) 1) (hj : 0 < t₁.E.s) (hne : Nonempty t₁.X)
    (V : t₁.X.Opens) (I' : (V : Scheme.{u}).IdealSheafData) (E' : OrderedDivisor V)
    (s' : (V : Scheme.{u}) ⟶ Spec (.of t₁.k)) (hV : V = ⊤) (hd : d = dimNat t₁.X)
    (hI' : I' = t₁.I.comap V.ι) (hE' : E' = t₁.E.comap V.ι) (hs' : s' = V.ι ≫ t₁.sX) :
    (if (V : Set t₁.X).Nonempty ∧ IsTriple s' I' E' then
        bdFunctor M d 1 0 ⟨⟨V, I', E'⟩, t₁.k, s'⟩ else .nil _).extendByClosure V.ι =
      bdFunctor M d 1 0 t₁ := by
  subst hV hd hI' hE' hs'
  haveI : IsIso (⊤ : t₁.X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  haveI : LocallyOfFiniteType t₁.sX := ht₁.1.2.2.1
  haveI : QuasiCompact t₁.sX := ht₁.1.2.2.2.1
  have hmem := pullback_mem_idealTriplesOfDim_of_isIso ht₁ (⊤ : t₁.X.Opens).ι
  rw [if_pos ⟨⟨hne.some, trivial⟩, hmem.1⟩]
  have hc := (commutesWithSmoothOn_bdFunctor M hN hM le_rfl (j := 0)).1 t₁ ⟨ht₁, hj⟩ _
    (⊤ : t₁.X.Opens).ι inferInstance inferInstance inferInstance inferInstance ⟨hmem, hj⟩
  have hdV : dimNat (⊤ : t₁.X.Opens) = dimNat t₁.X := by
    unfold dimNat
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.Hom.homeomorph (⊤ : t₁.X.Opens).ι).isHomeomorph]
  change bdFunctor M (dimNat (⊤ : t₁.X.Opens)) 1 0 _ = _ at hc
  rw [hdV] at hc
  change (bdFunctor M (dimNat t₁.X) 1 0 (t₁.pullback (⊤ : t₁.X.Opens).ι)).extendByClosure _ = _
  rw [hc]
  exact extendByClosure_pullback_of_isIso (bdFunctor M (dimNat t₁.X) 1 0 t₁) (⊤ : t₁.X.Opens).ι

/-- **Kollár, Thm. 3.104 Step 2.4 (closed embeddings).** Let `M` be a marked order-reduction
family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`) and `(X, I, ∅)` a triple of
dimension `n` with `1 ≤ n ≤ N`. Let `H` be a smooth hypersurface (`IsSmoothHypersurface`) with
inclusion `τ : H ↪ X`, and `J` an ideal sheaf on `H`, nonzero at the generic point of every
irreducible component of `H` (`IsNonzeroAtGenericPoints`), with `I = J.map τ`, i.e.
`𝒪_X/I = τ_*(𝒪_H/J)`, and `maxord I = 1`. Then `boMaximalContact M 1 (X, I, ∅) H` is the
push-forward along `τ` of `M (n - 1) 1 (H, J, 1, ∅)`. -/
@[mmp "lem_kr3e_bo_maximal_contact_closed_embedding"]
public theorem boMaximalContact_eq_pushforward_of_eq_map {N n : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hE : t.E.s = 0)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    (J : H.subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map H.subschemeι) (hmax : maxOrder t.I = 1) :
    let tY : MarkedTriple.{u} :=
      ⟨⟨⟨H.subscheme, J, OrderedDivisor.empty H.subscheme⟩, t.k, H.subschemeι ≫ t.sX⟩, 1⟩
    boMaximalContact M 1 t H = (M (n - 1) 1 tY).pushforward H.subschemeι := by
  intro tY
  obtain ⟨⟨X, I, ⟨s, E⟩⟩, k, sX⟩ := t
  dsimp only at hE
  subst hE
  have hdimX : dimNat X = n := by simp [dimNat, hdim]
  -- `(X, I, (H))` is a triple
  have htr : (⟨⟨X, I, ⟨1, fun _ => H⟩⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈ triples := by
    haveI : CharZero k := ht.1
    haveI : LocallyOfFiniteType sX := ht.2.2.1
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1,
      isOrderedSNC_singleton_of_isSmoothHypersurface ht.2.1 hH⟩
  have ht₁ : (⟨⟨X, I, ⟨1, fun _ => H⟩⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈
      idealTriplesOfDim (Set.Icc 1 N) 1 :=
    ⟨htr, ⟨n, ⟨hn, hnN⟩, hdim⟩, hmax.le⟩
  have hS := support_nonempty_of_le_of_maxOrder_eq_one hmax
    ((Scheme.IdealSheafData.ker_subschemeι H).symm.le.trans (hI ▸ Scheme.Hom.le_ker_comp _ _))
  have hne : Nonempty X := ⟨hS.some⟩
  have hbd : bdFunctor M n 1 0 (⟨⟨X, I, ⟨1, fun _ => H⟩⟩, k, sX⟩ : FieldBlowupTriple.{u}) =
      (M (n - 1) 1 ⟨⟨⟨H.subscheme, J,
        ((⟨1, fun _ => H⟩ : OrderedDivisor X).deleteIndex 0).comap H.subschemeι⟩, k,
          H.subschemeι ≫ sX⟩, 1⟩).pushforward H.subschemeι :=
    bdFunctor_eq_pushforward_of_eq_map M hN hM _ htr hdim hn hnN Nat.one_pos hS J hJ hI
  rw [eq_empty_of_s_eq_zero
    (((⟨1, fun _ => H⟩ : OrderedDivisor X).deleteIndex 0).comap H.subschemeι) rfl] at hbd
  unfold boMaximalContact divisorSeparationSequence
  dsimp only
  refine Eq.trans (congrArg (fun B => ((ClosedBlowupSequence.nil X).append B).reduction)
    (extendByClosure_bdFunctor_eq M hN hM _ ht₁ Nat.one_pos hne _ _ _ _ ?hV rfl ?hI' ?hE' ?hs')) ?_
  case hV =>
    ext x
    simp only [Nat.not_lt_zero, if_false, iSup_bot]
    exact iff_of_true (by simp) trivial
  case hI' => rfl
  case hE' =>
    show (⟨1, Fin.cons ((H.subschemeι.ker).comap _) _⟩ : OrderedDivisor _) =
      ⟨1, fun _ => H.comap _⟩
    refine congrArg (OrderedDivisor.mk 1) (funext fun i => ?_)
    fin_cases i
    exact congrArg (fun W => Scheme.IdealSheafData.comap W _)
      (Scheme.IdealSheafData.ker_subschemeι H)
  case hs' =>
    show _ ≫ (𝟙 X ≫ sX) = _
    rw [Category.id_comp]
    rfl
  show (bdFunctor M (dimNat X) 1 0 _).reduction = _
  rw [reduction_bdFunctor, hdimX, hbd]

/-! ### `𝓑𝓞_{n,1}` along a smooth hypersurface -/

/-- No irreducible component of `X` lies in a closed subset of pure codimension one. -/
private theorem not_subset_of_isPureCodimOne {X : Type*} [TopologicalSpace X]
    {S : Closeds X} (hS : MMP.Mori.IsPureCodimOne S) :
    ∀ Z ∈ irreducibleComponents X, ¬ Z ⊆ (S : Set X) := by
  intro Z hZ hsub
  let W : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hmax : IsMax W := fun W' hW' => hZ.2 W'.isIrreducible hW'
  have h1 := hS W ⟨hsub, fun W' _ hW' => hmax hW'⟩
  rw [codimension_eq_coheight, Order.coheight_eq_zero.2 hmax] at h1
  exact zero_ne_one h1

/-- The push-forward of the empty sequence is empty. -/
private theorem pushforward_nil {S X : Scheme.{u}} (j : S ⟶ X) :
    (ClosedBlowupSequence.nil S).pushforward j = .nil X := by
  have hex : ∃ B', ClosedBlowupSequence.IsPushforward j (.nil S) B' := ⟨.nil X, trivial⟩
  rw [ClosedBlowupSequence.pushforward, dif_pos hex]
  generalize hB : hex.choose = B
  have := hB ▸ hex.choose_spec
  cases B with
  | nil => rfl
  | cons Z B => exact this.elim

/-- A smooth centre along which `I` has order `≥ m`, in a smooth scheme, lies in
`cosupp(I, m)`. -/
private theorem support_subset_cosupport {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (a : MarkedIdeal X)
    (hord : OrderAlongGE a.I (Z.support : Set X) a.m) :
    (Z.support : Set X) ⊆ a.cosupport := by
  intro u hu
  change (a.m : ℕ∞) ≤ idealOrder _
  rw [natCast_le_idealOrder_iff']
  refine (stalk_le_pow_of_orderAlongGE s hX Z hZ a.I a.m hord u).trans ?_
  refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun h => ?_) a.m
  exact ((IdealSheafData.stalk_eq_top_iff_notMem_support Z u).1 h) hu

/-- A smooth blow-up sequence of order `≥ m` without empty blow-ups starting with a marked
triple of empty cosupport is empty. -/
private theorem eq_nil_of_cosupport_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s a E) (hne : B.HasNoEmptyBlowups)
    (ha : a.cosupport = ∅) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    obtain ⟨hT, hZ, -, -, hord, -⟩ := hB
    have hsub := support_subset_cosupport s hT.2.1 Z hZ a hord
    rw [ha, Set.subset_empty_iff] at hsub
    refine (hne.1 ?_).elim
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    exact SetLike.coe_injective hsub

section Dimension

open MMP.Mori

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- If the stalks of `D` are generated by members of regular systems of parameters, the local
ring of `D` at a point has dimension one less than that of `Y`. -/
private theorem exists_ringKrullDim_stalk_subscheme (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (s : D.subscheme) : ∃ m : ℕ, ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) = m ∧
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((m - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hz : D.subschemeι s ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨s, rfl⟩
  obtain ⟨m, w, j, hw, hy⟩ := hD _ hz
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  refine ⟨m, hw.2, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv D s), hy]
  exact ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j

/-- On an equidimensional scheme of dimension `d` locally of finite type over a field, a
nonempty quasi-compact closed subscheme whose stalk ideals are generated by members of regular
systems of parameters is equidimensional of dimension `d - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_subscheme {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (he : Equidimensional Y) {d : ℕ}
    (hd : topologicalKrullDim Y = ((d : ℕ∞) : WithBot ℕ∞)) (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    [CompactSpace D.subscheme] [Nonempty D.subscheme] :
    Equidimensional D.subscheme ∧
      topologicalKrullDim D.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ s,
      ringKrullDim (D.subscheme.presheaf.stalk s) ≤ (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s
    obtain ⟨m, hm, hs⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have h1 : ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y => ringKrullDim (Y.presheaf.stalk y)) _
    rw [hm, hd] at h1
    have h2 : m ≤ d := by exact_mod_cast h1
    rw [hs]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast Nat.sub_le_sub_right h2 1)
  have hcl : ∀ s : D.subscheme, IsClosed ({s} : Set D.subscheme) →
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s hs
    obtain ⟨m, hm, hs'⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have hy : IsClosed ({D.subschemeι s} : Set Y) := by
      simpa using D.subschemeι.isClosedEmbedding.isClosedMap _ hs
    have h1 := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sY _ hy
    rw [topologicalKrullDimAt_eq_of_equidimensional k Y sY he
      (d := d) (by rw [hd]; rfl), hm] at h1
    have h2 : m = d := by exact_mod_cast h1.symm
    rw [hs', h2]
  have hat : ∀ s : D.subscheme,
      topologicalKrullDimAt D.subscheme s = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    intro s
    rw [topologicalKrullDimAt_eq_iInf_closedSpecializations (D.subschemeι ≫ sY) s]
    obtain ⟨s', hs'mem, hs'cl⟩ :=
      (isClosed_closure (s := ({s} : Set D.subscheme))).exists_closed_singleton
        ⟨s, subset_closure rfl⟩
    refine le_antisymm (iInf_le_of_le ⟨s', specializes_iff_mem_closure.2 hs'mem, hs'cl⟩
      (hcl s' hs'cl).le) (le_iInf fun x => (hcl x.1 x.2.2).ge)
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq k _ (D.subschemeι ≫ sY) hat, ?_⟩
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨s0, -, hs0⟩ :=
    isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := D.subscheme))
  exact le_antisymm (iSup_le hle) (le_iSup_of_le s0 (hcl s0 hs0).ge)

end Dimension

/-- The empty ordered divisor on a smooth scheme is an ordered snc divisor. -/
private theorem isOrderedSNC_empty {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : MMP.Mori.IsSmoothScheme sX) :
    (OrderedDivisor.empty X).IsOrderedSNC sX := by
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩

/-- If `maxord I = 1`, then `W(I) = MC(I) = D^0(I) = I`. -/
private theorem wellTunedIdeal_eq_self {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hcomp : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hmax : maxOrder I = 1) :
    maximalContactIdeal sX I = I ∧ wellTunedIdeal sX I = I := by
  have hMC : maximalContactIdeal sX I = I := by
    rw [maximalContactIdeal, hmax]; exact higherDerivativeIdeal_zero sX I
  refine ⟨hMC, ?_⟩
  have e : (((maxOrder I).toNat.factorial : ℕ) : ℤ) = 1 := by rw [hmax]; rfl
  rw [wellTunedIdeal, e, Kollar.maximalCoefficientIdeal_one_eq_maximalContactIdeal sX hcomp I
    (by rw [hmax]; rfl), hMC]

/-- A point lies in the support of `I` exactly when `I` has order `≥ 1` there. -/
private theorem one_le_multAt_iff_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    ((1 : ℕ) : ℕ∞) ≤ multAt I x ↔ x ∈ I.support := by
  change _ ≤ idealOrder _ ↔ _
  rw [natCast_le_idealOrder_iff', pow_one, ← not_iff_not,
    ← IdealSheafData.stalk_eq_top_iff_notMem_support]
  exact ⟨fun h => by_contra fun h' => h (IsLocalRing.le_maximalIdeal h'),
    fun h h' => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ h'))⟩

/-- An ideal sheaf of maximal order `0` is the unit ideal. -/
private theorem eq_top_of_maxOrder_eq_zero {X : Scheme.{u}} {I : X.IdealSheafData}
    (h0 : maxOrder I = 0) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine eq_bot_iff.2 fun x hx => ?_
  have hle := multAt_le_maxOrder I x
  rw [h0] at hle
  exact absurd (((one_le_multAt_iff_mem_support I x).2 hx).trans hle) (by simp)

/-- A marked order reduction family sends a marked triple with unit ideal to the empty
sequence: the cosupport is empty, so no centre can be blown up. -/
private theorem markedFamily_eq_nil_of_I_eq_top {a b μ : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily a b M) (hμ : 1 ≤ μ) {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriplesOfDim (Set.Icc a b) μ) (htop : t.I = ⊤) :
    M (dimNat t.X) μ t = .nil _ := by
  obtain ⟨F, hF, -⟩ := hM μ hμ
  rw [← hF t ht]
  refine eq_nil_of_cosupport_eq_empty _ _ _ _ (F.isOrderGeMarkedTripleSeq t ht)
    (F.hasNoEmptyBlowups t ht) (Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_)
  have hy' : (t.m : ℕ∞) ≤ multAt t.I y := hy
  rw [ht.2.1] at hy'
  have := (one_le_multAt_iff_mem_support t.I y).1 ((Nat.cast_le.2 hμ).trans hy')
  simp [htop, ← SetLike.mem_coe] at this

/-- A nonempty smooth hypersurface of a triple of dimension `n` is equidimensional of dimension
`n - 1`. -/
private theorem equidimensional_and_topologicalKrullDim_of_isSmoothHypersurface {n : ℕ}
    {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H) [Nonempty H.subscheme] :
    Equidimensional H.subscheme ∧
      topologicalKrullDim H.subscheme = (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, -, -⟩ := ht
  haveI := hchar; haveI := hlft; haveI := hqc
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  haveI : CompactSpace t.X := QuasiCompact.compactSpace_of_compactSpace t.sX
  haveI : CompactSpace H.subscheme := QuasiCompact.compactSpace_of_compactSpace H.subschemeι
  exact equidimensional_and_topologicalKrullDim_subscheme t.sX hequi hdim H
    (exists_stalk_eq_span_parameter_of_isSmoothHypersurface hsm hH)

/-- An ideal containing the ideal of a smooth hypersurface `H` of a triple has maximal order
`≤ 1`: no irreducible component of `X` lies in `H`. -/
private theorem maxOrder_le_one_of_isSmoothHypersurface {t : FieldBlowupTriple.{u}}
    (ht : t ∈ triples) {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {J : H.subscheme.IdealSheafData} (hI : t.I = J.map H.subschemeι) : maxOrder t.I ≤ 1 := by
  obtain ⟨hchar, hsm, hlft, -, -, -, -⟩ := ht
  haveI := hchar; haveI := hlft
  haveI : PerfectField t.k := PerfectField.ofCharZero
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr inferInstance
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : LocallyOfFinitePresentation (H.subschemeι ≫ t.sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := H.subschemeι ≫ t.sX)).mpr
      inferInstance
  haveI : Smooth (H.subschemeι ≫ t.sX) := (MMP.Mori.isSmoothScheme_iff _).1 hH.1
  haveI : ∀ x : t.X, IsRegularLocalRing (t.X.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk t.sX).mp
      inferInstance
  haveI : ∀ y : H.subscheme, IsRegularLocalRing (H.subscheme.presheaf.stalk y) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
      (H.subschemeι ≫ t.sX)).mp inferInstance
  exact Kollar.maxOrder_le_one_of_eq_ker H J t.I (not_subset_of_isPureCodimOne hH.2) hI

/-- On a local triple, `𝓑𝓞` is the local sequence `𝓑`. -/
private theorem boFunctor_eq_boLocal {d m : ℕ} (M : MarkedFamily.{u}) (hd : 1 ≤ d)
    (hM : IsMarkedOrderReductionFamily 0 (d - 1) M) (hm : 1 ≤ m) (t : FieldBlowupTriple.{u})
    (ht : t ∈ mcLocalTriples d m) : boFunctor M d m t = boLocal M m t := by
  have hT : t ∈ idealTriplesOfDim {d} m := ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have e := boFunctor_pullback M hd hM hm t hT (𝟙 _) (isOpenCoverMap_of_isOpenImmersion _)
    inferInstance
    (by rw [fieldBlowupTriple_pullback_id]; exact ht)
  rw [pullback_id_of_hasNoEmptyBlowups (boFunctor_isOrderMTripleSeq M hd hM hm t hT).2] at e
  exact e.trans (eq_of_heq (boLocal_congr M m (fieldBlowupTriple_pullback_id _)))

/-- **Kollár, Thm. 3.103 (3).** Let `n ≥ 1`, `M` a marked order-reduction family on dimensions
`0, …, n - 1` (`IsMarkedOrderReductionFamily`), and `(X, I, ∅)` a triple of dimension `n`. Let `H`
be a nonempty smooth hypersurface (`IsSmoothHypersurface`) with inclusion `τ : H ↪ X`, and `J` an
ideal sheaf on `H`, nonzero at the generic point of every irreducible component of `H`
(`IsNonzeroAtGenericPoints`), with `I = J.map τ`, i.e. `𝒪_X/I = τ_*(𝒪_H/J)`. Then
`boFunctor M n 1 (X, I, ∅)` is the push-forward along `τ` of `M (n - 1) 1 (H, J, 1, ∅)`. -/
@[mmp "thm_kr3e_order_reduction_ideals_closed_embedding"]
public theorem boFunctor_eq_pushforward_of_eq_map {n : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hE : t.E.s = 0)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H) (hY : Nonempty H.subscheme)
    (J : H.subscheme.IdealSheafData) (hJ : IsNonzeroAtGenericPoints J)
    (hI : t.I = J.map H.subschemeι) :
    let tY : MarkedTriple.{u} :=
      ⟨⟨⟨H.subscheme, J, OrderedDivisor.empty H.subscheme⟩, t.k, H.subschemeι ≫ t.sX⟩, 1⟩
    boFunctor M n 1 t = (M (n - 1) 1 tY).pushforward H.subschemeι := by
  intro tY
  obtain ⟨hchar, hsm, hlft, hqc, -, -, -⟩ := id ht
  haveI := hchar; haveI := hlft; haveI := hqc
  haveI : PerfectField t.k := PerfectField.ofCharZero
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr inferInstance
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hle1 := maxOrder_le_one_of_isSmoothHypersurface ht hH hI
  have hdX : HasDimensionIn t.X {n} := ⟨n, rfl, hdim⟩
  have htI : t ∈ idealTriplesOfDim {n} 1 := ⟨ht, hdX, by exact_mod_cast hle1⟩
  rcases le_iff_lt_or_eq.1 hle1 with h0 | h1
  · have hlt : maxOrder t.I < (1 : ℕ) := by exact_mod_cast h0
    rw [boFunctor_eq_boLocal M hn hM le_rfl t ⟨ht, hdX, by exact_mod_cast hle1, Or.inl hlt⟩,
      boLocal, if_pos hlt]
    have hJtop : J = ⊤ := by
      refine top_le_iff.1 ?_
      have := Scheme.IdealSheafData.comap_map_le (I := J) (f := H.subschemeι)
      rwa [← hI, eq_top_of_maxOrder_eq_zero (ENat.lt_one_iff_eq_zero.1 h0),
        Scheme.IdealSheafData.comap_top] at this
    obtain ⟨hequiY, hdimY⟩ :=
      equidimensional_and_topologicalKrullDim_of_isSmoothHypersurface ht hdim hH
    have htY : tY ∈ markedTriplesOfDim (Set.Icc 0 (n - 1)) 1 :=
      ⟨⟨hchar, hH.1, inferInstance, inferInstance, hequiY, hJ, isOrderedSNC_empty _ hH.1⟩, rfl,
        ⟨n - 1, ⟨Nat.zero_le _, le_rfl⟩, hdimY⟩⟩
    have hdn : dimNat tY.X = n - 1 := by
      change ((topologicalKrullDim H.subscheme).unbotD 0).toNat = n - 1
      rw [hdimY]; rfl
    rw [← hdn, markedFamily_eq_nil_of_I_eq_top hM le_rfl htY hJtop, pushforward_nil]
  · obtain ⟨hMC, hW⟩ :=
      wellTunedIdeal_eq_self t.sX (pos_dim_of_mem_irreducibleComponents hn t ht hdX) h1
    have hHI : H ≤ t.I := hI ▸
      (Scheme.IdealSheafData.ker_subschemeι H).symm.le.trans (Scheme.Hom.le_ker_comp _ _)
    have hmc : IsMCHypersurface t.sX t.I H := ⟨hH, hMC.symm ▸ hHI⟩
    have hchoice : IsMCHypersurface t.sX t.I (mcHypersurfaceChoice t) := by
      have hex : ∃ H, IsMCHypersurface t.sX t.I H := ⟨H, hmc⟩
      rw [mcHypersurfaceChoice, dif_pos hex]; exact hex.choose_spec
    rw [boFunctor_eq_boLocal M hn hM le_rfl t
        ⟨ht, hdX, by exact_mod_cast hle1, Or.inr ⟨by exact_mod_cast h1, H, hmc⟩⟩, boLocal,
      if_neg (by rw [h1]; exact lt_irrefl _), Nat.factorial_one,
      boMaximalContact_congr t.E t.k t.sX hW]
    exact (boMaximalContact_eq_of_isMCHypersurface M hn hM t ht hdim hn le_rfl le_rfl
      (by exact_mod_cast h1) hchoice hmc).trans
      (boMaximalContact_eq_pushforward_of_eq_map M hn hM t ht hE hdim hn le_rfl hH J hJ hI h1)

/-! ### `𝓑𝓞` commutes with smooth morphisms -/

/-- In characteristic zero `ord_y h^*I = ord_{h(y)} I` for smooth `h`: the order is detected by
the higher derivative ideals, which commute with the smooth pull-back `h^*`. -/
private theorem multAt_comap_of_smooth (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hd : 1 ≤ topologicalKrullDim t.X) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] (y : Y) :
    multAt (t.I.comap h) y = multAt t.I (h y) := by
  obtain ⟨hchar, hsm, hlft, -, he, -⟩ := ht
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hD := higherDerivativeIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl
    (pos_topologicalKrullDim_of_mem_irreducibleComponents he hd) t.I
  have key (n : ℕ) : (n : ℕ∞) ≤ multAt (t.I.comap h) y ↔ (n : ℕ∞) ≤ multAt t.I (h y) := by
    cases n with
    | zero => simp
    | succ n =>
      rw [succ_le_multAt_iff_forall_mem_support (h ≫ t.sX),
        succ_le_multAt_iff_forall_mem_support t.sX]
      exact forall₂_congr fun j _ => hD j ▸ mem_support_comap_iff h _ y
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n => (key n).1)
    (ENat.forall_natCast_le_iff_le.mp fun n => (key n).2)

/-- The pulled-back ideal has no larger maximal order. -/
private theorem maxOrder_comap_le_of_smooth (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hd : 1 ≤ topologicalKrullDim t.X) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] :
    maxOrder (t.I.comap h) ≤ maxOrder t.I := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_pos]
  exact iSup_le fun y => (multAt_comap_of_smooth t ht hd h y).symm ▸ le_iSup (multAt t.I) (h y)

/-- On an empty scheme every blow-up is empty, so pull-back with empty blow-ups deleted to an
empty scheme gives the empty sequence. -/
private theorem pullbackReduced_eq_nil_of_isEmpty {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} [IsEmpty Y] (h : Y ⟶ X), B.pullbackReduced h = .nil Y := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro Y _ h
    have hZ : Z.comap h = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      exact eq_bot_iff.2 fun y _ => isEmptyElim y
    simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
    exact ih _

/-- A marked order-reduction family on dimensions `a, …, b` is one on dimensions `a, …, b'` for
`b' ≤ b`: restrict each functor to the smaller class. -/
private theorem isMarkedOrderReductionFamily_mono {a b b' : ℕ} {M : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily a b M) (hb : b' ≤ b) :
    IsMarkedOrderReductionFamily a b' M := by
  intro μ hμ
  obtain ⟨F, hF, h1, h2a, h2b⟩ := hM μ hμ
  have sub : ∀ {t : MarkedTriple.{u}}, t ∈ markedTriplesOfDim (Set.Icc a b') μ →
      t ∈ markedTriplesOfDim (Set.Icc a b) μ := fun {t} ht => by
    obtain ⟨d, hd, e⟩ := ht.2.2
    exact ⟨ht.1, ht.2.1, d, ⟨hd.1, hd.2.trans hb⟩, e⟩
  refine ⟨⟨fun t ht => F.toFun t (sub ht), fun t ht => F.isOrderGeMarkedTripleSeq t (sub ht),
    fun t ht => F.hasNoEmptyBlowups t (sub ht)⟩, fun t ht => hF t (sub ht),
    fun t ht => h1 t (sub ht), ⟨fun t ht Y h hs hsu hl hq hY => h2a.1 t (sub ht) Y h hs hsu hl hq
      (sub hY), fun t ht Y h hs hl hq hY => h2a.2 t (sub ht) Y h hs hl hq (sub hY)⟩,
    fun t ht L _ σ hL => h2b t (sub ht) L σ (sub hL)⟩

/-- A member of the class has a dimension `d ∈ [1, n]`, namely `dimNat X`. -/
private theorem mem_idealTriplesOfDim_dimNat {n m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim (Set.Icc 1 n) m) :
    t ∈ idealTriplesOfDim {dimNat t.X} m ∧ 1 ≤ dimNat t.X ∧ dimNat t.X ≤ n := by
  obtain ⟨d, hd, hX⟩ := ht.2.1
  have e : dimNat t.X = d := by simp [dimNat, hX]
  rw [e]
  exact ⟨⟨ht.1, ⟨d, rfl, hX⟩, ht.2.2⟩, hd.1, hd.2⟩

/-- The class of triples of dimension `d` with `maxord I ≤ m` is stable under pull-back along
open cover maps from nonempty schemes. -/
private theorem pullback_mem_idealTriplesOfDim {d m : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim {d} m) {X' : Scheme.{u}} [Nonempty X'] (g : X' ⟶ t.X)
    (hg : IsOpenCoverMap g) : t.pullback g ∈ idealTriplesOfDim {d} m :=
  ⟨pullback_mem_triples_of_isOpenCoverMap t ht.1 g hg,
    hasDimensionIn_of_isOpenCoverMap (Y := X') t ht.1 ht.2.1 g hg,
    (maxOrder_comap_le_of_isOpenCoverMap hg t.I).trans ht.2.2⟩

/-- **Step 1.** `𝓑𝓞` commutes with surjective open cover maps `g : X'' → X`: on a further
surjective open cover `X''' → X''` by a local triple both pull-backs are `𝓑(X''')`. -/
private theorem boFunctor_pullback_of_isOpenCoverMap {d m : ℕ} (M : MarkedFamily.{u})
    (hd : 1 ≤ d) (hM : IsMarkedOrderReductionFamily 0 (d - 1) M)
    (hm : 1 ≤ m) (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {d} m) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) (hg : IsOpenCoverMap g) (hs : Surjective g) :
    boFunctor M d m (t.pullback g) = (boFunctor M d m t).pullback g := by
  have := nonempty_of_hasDimensionIn ht.2.1
  have : Nonempty X' := ⟨(hs.surj (Classical.arbitrary t.X)).choose⟩
  have ht' := pullback_mem_idealTriplesOfDim ht g hg
  obtain ⟨X'', g'', hg'', hs'', hloc⟩ :=
    exists_surjective_isOpenCoverMap_mem_mcLocalTriples hd hm _ ht'
  have : Smooth g'' := smooth_of_isOpenCoverMap hg''
  have := hs''
  have := hs
  apply Kollar.eq_of_pullback_eq_of_flat_of_surjective g''
  rw [boFunctor_pullback M hd hM hm _ ht' g'' hg'' hs'' hloc]
  refine Eq.trans ?_ (pullback_pullback _ g g'').symm
  have hloc' : t.pullback (g'' ≫ g) ∈ mcLocalTriples d m :=
    fieldBlowupTriple_pullback_pullback t g g'' ▸ hloc
  refine Eq.trans ?_ (boFunctor_pullback M hd hM hm t ht (g'' ≫ g) (isOpenCoverMap_comp hg'' hg)
    ⟨fun x => by
      obtain ⟨y, rfl⟩ := hs.surj x
      obtain ⟨z, rfl⟩ := hs''.surj y
      exact ⟨z, rfl⟩⟩ hloc').symm
  exact eq_of_heq (boLocal_congr M m (fieldBlowupTriple_pullback_pullback t g g''))

/-- Along a flat surjection, pull-back commutes with deleting empty blow-ups. -/
private theorem reduction_pullback_of_flat {X W : Scheme.{u}} (B : ClosedBlowupSequence X)
    (k : W ⟶ X) [Flat k] [Surjective k] : (B.pullback k).reduction = B.reduction.pullback k :=
  (ClosedBlowupSequence.reduction_pullback_reduction B k).symm.trans
    (ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (ClosedBlowupSequence.hasNoEmptyBlowups_reduction B) k))

/-- A blow-up sequence `C` on `Y` is `(h^*𝐁)^red` as soon as its pull-back along a flat
surjection `k : W → Y` is `(k'^*g^*𝐁)^red` for some `k'` with `h ∘ k = g ∘ k'`. -/
private theorem eq_pullback_reduction_of_pullback_eq {X Y X' W : Scheme.{u}}
    (B : ClosedBlowupSequence X) {h : Y ⟶ X} {g : X' ⟶ X} {k : W ⟶ Y} {k' : W ⟶ X'}
    [Flat k] [Surjective k] (w : k ≫ h = k' ≫ g) {C : ClosedBlowupSequence Y}
    (hC : C.pullback k = ((B.pullback g).pullback k').reduction) :
    C = (B.pullback h).reduction := by
  apply Kollar.eq_of_pullback_eq_of_flat_of_surjective k
  rw [← reduction_pullback_of_flat, pullback_pullback, hC, pullback_pullback, w]

/-- The triples of the class, together with the triples on the empty scheme (the pull-backs
along empty open cover maps). -/
private def extClass (n m : ℕ) : Set FieldBlowupTriple.{u} :=
  {s | s ∈ idealTriplesOfDim (Set.Icc 1 n) m ∨ IsEmpty s.X}

open Classical in
/-- `𝓑𝓞`, extended by the empty sequence on empty schemes. -/
private noncomputable def extFunctor (M : MarkedFamily.{u}) (m : ℕ) (s : FieldBlowupTriple.{u}) :
    ClosedBlowupSequence s.X :=
  if IsEmpty s.X then .nil s.X else boFunctor M (dimNat s.X) m s

private theorem not_isEmpty_of_mem_idealTriplesOfDim {n m : ℕ} {s : FieldBlowupTriple.{u}}
    (hs : s ∈ idealTriplesOfDim (Set.Icc 1 n) m) : ¬ IsEmpty s.X := fun _ => by
  obtain ⟨x⟩ := nonempty_of_hasDimensionIn (mem_idealTriplesOfDim_dimNat hs).1.2.1
  exact isEmptyElim x

private theorem extFunctor_of_mem (M : MarkedFamily.{u}) {n m : ℕ} {s : FieldBlowupTriple.{u}}
    (hs : s ∈ idealTriplesOfDim (Set.Icc 1 n) m) :
    extFunctor M m s = boFunctor M (dimNat s.X) m s := by
  unfold extFunctor; rw [if_neg (not_isEmpty_of_mem_idealTriplesOfDim hs)]

private theorem mem_of_mem_extClass {n m : ℕ} {s : FieldBlowupTriple.{u}} (hs : s ∈ extClass n m)
    (hne : Nonempty s.X) : s ∈ idealTriplesOfDim (Set.Icc 1 n) m :=
  hs.resolve_right fun _ => isEmptyElim hne.some

/-- The pull-back of a member of the class along an open cover map from a nonempty scheme is a
member of the same dimension. -/
private theorem pullback_mem_of_isOpenCoverMap {n m : ℕ} {s : FieldBlowupTriple.{u}}
    (hs : s ∈ idealTriplesOfDim (Set.Icc 1 n) m) {X' : Scheme.{u}} [Nonempty X'] (g : X' ⟶ s.X)
    (hg : IsOpenCoverMap g) :
    s.pullback g ∈ idealTriplesOfDim (Set.Icc 1 n) m ∧ dimNat X' = dimNat s.X := by
  obtain ⟨hs', h1, h2⟩ := mem_idealTriplesOfDim_dimNat hs
  have := pullback_mem_idealTriplesOfDim hs' g hg
  obtain ⟨d, hd, e⟩ := this.2.1
  rw [Set.mem_singleton_iff] at hd
  subst hd
  refine ⟨⟨this.1, ⟨_, ⟨h1, h2⟩, e⟩, this.2.2⟩, ?_⟩
  have e' : topologicalKrullDim X' = ((dimNat s.X : ℕ∞) : WithBot ℕ∞) := e
  show ((topologicalKrullDim X').unbotD 0).toNat = dimNat s.X
  rw [e']
  simp

private theorem extClass_pullback {n m : ℕ} (s : FieldBlowupTriple.{u}) (hs : s ∈ extClass n m)
    (X' : Scheme.{u}) (g : X' ⟶ s.X) (hg : IsOpenCoverMap g) : s.pullback g ∈ extClass n m := by
  by_cases hX' : IsEmpty X'
  · exact Or.inr hX'
  rw [not_isEmpty_iff] at hX'
  exact Or.inl (pullback_mem_of_isOpenCoverMap (mem_of_mem_extClass hs ⟨g hX'.some⟩) g hg).1

private theorem extFunctor_pullback_of_surjective {n m : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (s : FieldBlowupTriple.{u}) (hs : s ∈ extClass n m) (X' : Scheme.{u}) (g : X' ⟶ s.X)
    (hg : IsOpenCoverMap g) (hgs : Surjective g) :
    extFunctor M m (s.pullback g) = (extFunctor M m s).pullback g := by
  by_cases hX : IsEmpty s.X
  · have := hX
    have : IsEmpty (s.pullback g).X := Function.isEmpty g
    unfold extFunctor
    rw [if_pos hX, if_pos this]
    rfl
  rw [not_isEmpty_iff] at hX
  have hs' := mem_of_mem_extClass hs hX
  have : Nonempty X' := ⟨(hgs.surj hX.some).choose⟩
  obtain ⟨hp, hdim⟩ := pullback_mem_of_isOpenCoverMap hs' g hg
  obtain ⟨hs'', h1, h2⟩ := mem_idealTriplesOfDim_dimNat hs'
  rw [extFunctor_of_mem M hs', extFunctor_of_mem M hp]
  change boFunctor M (dimNat X') m _ = _
  rw [hdim]
  exact boFunctor_pullback_of_isOpenCoverMap M h1
    (isMarkedOrderReductionFamily_mono hM (by omega)) hm s hs'' g hg hgs

/-- Pure codimension one of a smooth hypersurface is preserved by preimage under a smooth
morphism: the local equation, one member of a regular system of parameters, pulls back to one. -/
private theorem isPureCodimOne_comap_of_smooth (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] :
    MMP.Mori.IsPureCodimOne (H.comap h).support := by
  have : CharZero t.k := ht.1
  have : LocallyOfFiniteType t.sX := ht.2.2.1
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (h ≫ t.sX)
  refine isPureCodimOne_support_of_stalk_eq_span_parameter _ fun y hy => ?_
  have hx := (mem_support_comap_iff h H y).1 hy
  obtain ⟨n, z, j, hz, hzj⟩ :=
    exists_stalk_eq_span_parameter_of_isSmoothHypersurface ht.2.1 hH (h y) hx
  obtain ⟨m, w, c', hw, hc', -⟩ := exists_coordinates_comap_of_flat h y (Flat.stalkMap h y)
    (MMP.Resolution.isRegularLocalRing_closedFibre_of_smooth h y) (fun _ : Unit => H)
    (c := fun _ => j) hz
    (fun _ => hzj) (fun a b _ => Subsingleton.elim a b)
  exact ⟨m, w, c' ⟨(), hy⟩, hw, hc' ⟨(), hy⟩⟩

/-- The preimage of a smooth hypersurface under a smooth morphism is a smooth hypersurface. -/
private theorem isSmoothHypersurface_comap_of_smooth (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] :
    IsSmoothHypersurface (h ≫ t.sX) (H.comap h) := by
  obtain ⟨hHs, hHc⟩ := hH
  refine ⟨?_, isPureCodimOne_comap_of_smooth t ht ⟨hHs, hHc⟩ h⟩
  have := MMP.Mori.IsSmoothScheme.smooth hHs
  have he : (H.comap h).subschemeι ≫ h ≫ t.sX =
      (H.comapIso h).hom ≫ Limits.pullback.snd h H.subschemeι ≫ H.subschemeι ≫ t.sX := by
    rw [← H.comapIso_hom_fst h, Category.assoc, Limits.pullback.condition_assoc]
  rw [he]
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- Smooth pull-back does not raise the maximal order, so `maxord h^*I = m` and `maxord I ≤ m`
force `maxord I = m`. -/
private theorem maxOrder_eq_of_maxOrder_comap_eq {d m : ℕ} (hd : 1 ≤ d)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) (hdim : HasDimensionIn t.X {d})
    (hle : maxOrder t.I ≤ m) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (heq : maxOrder (t.I.comap h) = m) : maxOrder t.I = m :=
  le_antisymm hle (heq ▸ maxOrder_comap_le_of_smooth t ht (one_le_topologicalKrullDim hd hdim) h)

/-- Local triples are stable under smooth pull-back within the class: if `maxord h^*I = m`, the
pull-back of the MC-hypersurface of `X^*` is an MC-hypersurface for `h^*I`, since
`MC(h^*I) = h^*MC(I)`. -/
private theorem pullback_mem_mcLocalTriples_of_smooth {d d' m : ℕ} (hd : 1 ≤ d)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples d m) {Y : Scheme.{u}} (h : Y ⟶ t.X)
    [Smooth h] (hY : t.pullback h ∈ idealTriplesOfDim {d'} m) :
    t.pullback h ∈ mcLocalTriples d' m := by
  refine ⟨hY.1, hY.2.1, hY.2.2, ?_⟩
  rcases lt_or_eq_of_le hY.2.2 with hlt | heq
  · exact Or.inl hlt
  refine Or.inr ⟨heq, ?_⟩
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr ht.1.2.2.1
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 ht.1.2.1
  have hmax : maxOrder t.I = m := maxOrder_eq_of_maxOrder_comap_eq hd t ht.1 ht.2.1 ht.2.2.1 h heq
  have hI : maxOrder (t.I.comap h) = maxOrder t.I := heq.trans hmax.symm
  obtain ⟨H, hH⟩ := (ht.2.2.2.resolve_left (by rw [hmax]; exact lt_irrefl _)).2
  refine ⟨H.comap h, isSmoothHypersurface_comap_of_smooth t ht.1 hH.1 h, ?_⟩
  change H.comap h ≤ maximalContactIdeal (h ≫ t.sX) (t.I.comap h)
  rw [maximalContactIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl
    (pos_dim_of_mem_irreducibleComponents hd t ht.1 ht.2.1) t.I hI]
  exact Scheme.IdealSheafData.comap_mono h hH.2

/-- The cosupport of the birational transform of `(I, m)` along the first blow-up of a sequence
of order `≥ m` lies over `cosupp(I, m)`. -/
private theorem cosupport_birationalTransform_subset_of_isOrderGe {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (B : ClosedBlowupSequence (blowUp Z))
    (hB : (ClosedBlowupSequence.cons Z B).IsOrderGeMarkedTripleSeq s a E) :
    (a.birationalTransform Z).cosupport ⊆ blowUpToBase Z ⁻¹' a.cosupport := by
  have e : B.truncate 0 = .nil _ := by cases B <;> rfl
  have := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E _ hB 1
  change ((ClosedBlowupSequence.cons Z (B.truncate 0)).markedTransform a).cosupport ⊆
    (ClosedBlowupSequence.cons Z (B.truncate 0)).toBase ⁻¹' a.cosupport at this
  rw [e] at this
  intro y hy
  have hy' : y ∈ (𝟙 (blowUp Z) ≫ blowUpToBase Z) ⁻¹' a.cosupport := this hy
  rwa [Category.id_comp] at hy'

/-- A smooth blow-up sequence of order `≥ m` for `(X, I, m, E)` has all its centres over
`cosupp(I, m)`, so its pull-back along a morphism missing `cosupp(I, m)` is empty after
deleting empty blow-ups. -/
private theorem pullbackReduced_eq_nil_of_isOrderGe {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      ∀ {Y : Scheme.{u}} (h : Y ⟶ X), (∀ y, h y ∉ a.cosupport) → B.pullbackReduced h = .nil Y
  | _, .nil _, _, _, _, _, _, _, _ => rfl
  | X, .cons Z B, s, a, E, hB, Y, h, hh => by
    have hsupp : (Z.support : Set X) ⊆ a.cosupport := by
      obtain ⟨hT, hZ, -, -, ha, -⟩ := hB
      exact support_subset_cosupport s (by simpa using hT.2.1) Z (by simpa using hZ) a
        (by simpa [Scheme.IdealSheafData.comap_id] using ha)
    have hZc : Z.comap h = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun y hy => ?_
      exact hh y (hsupp ((mem_support_comap_iff h Z y).1 hy))
    simp only [ClosedBlowupSequence.pullbackReduced, hZc, dite_true]
    refine pullbackReduced_eq_nil_of_isOrderGe B _ _ _ hB.2.2.2.2.2 _ fun y hy => hh y ?_
    have := cosupport_birationalTransform_subset_of_isOrderGe s a E Z B hB hy
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, blowUpLift_comp] at this

/-- If `maxord I = m` but `maxord h^*I < m`, the pull-back of `𝓑(X^*)` along the smooth `h` has
only empty blow-ups: the centres of `𝓑(X^*)` lie over `cosupp(I, m)`, which `h(Y)` misses
because `ord_y h^*I = ord_{h(y)} I`. -/
private theorem pullback_boLocal_reduction_eq_nil {n d m : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples d m) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hmax : maxOrder t.I = m) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hY : maxOrder (t.I.comap h) < m) :
    ((boLocal M m t).pullback h).reduction = .nil Y := by
  have hT : t ∈ idealTriplesOfDim {d} m := ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hM' := isMarkedOrderReductionFamily_mono hM (Nat.sub_le_sub_right hdn 1)
  have hOrd := (boFunctor_isOrderMTripleSeq M hd hM' hm t hT).1
  rw [boFunctor_eq_boLocal M hd hM' hm t ht] at hOrd
  have hGe := ((ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I
    t.E ht.1 m hmax _).1).2 hOrd
  rw [ClosedBlowupSequence.reduction_pullback]
  refine pullbackReduced_eq_nil_of_isOrderGe _ _ _ _ hGe h fun y hy => ?_
  have hy' : (m : ℕ∞) ≤ multAt (t.I.comap h) y := by
    rw [multAt_comap_of_smooth t ht.1 (one_le_topologicalKrullDim hd ht.2.1) h y]; exact hy
  refine absurd (hy'.trans ?_) (not_le.2 hY)
  change multAt (t.I.comap h) y ≤ maxOrderAlong (t.I.comap h) Set.univ
  exact le_iSup₂_of_le (f := fun z (_ : z ∈ Set.univ) => multAt (t.I.comap h) z) y
    (Set.mem_univ y) le_rfl

/-- **Local case.** `𝓑(Y^*) = (h^{*\,*}𝓑(X^*))^red` for a smooth `h^* : Y^* → X^*` between
local triples of dimensions in `[1, n]`. -/
private theorem boLocal_pullback_of_smooth {n d d' m : ℕ} (M : MarkedFamily.{u}) (hn : 1 ≤ n)
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ i ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {i} μ) (fun t _ => M i μ t)) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples d m) (hd : 1 ≤ d) (hdn : d ≤ n)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] (hY : t.pullback h ∈ mcLocalTriples d' m)
    (hd' : 1 ≤ d') (hd'n : d' ≤ n) :
    boLocal M m (t.pullback h) = ((boLocal M m t).pullback h).reduction := by
  by_cases hYm : maxOrder (t.pullback h).I < m
  · have hL : boLocal M m (t.pullback h) = .nil Y := by unfold boLocal; rw [if_pos hYm]; rfl
    rw [hL]
    by_cases hXm : maxOrder t.I < m
    · have hR : boLocal M m t = .nil t.X := by unfold boLocal; rw [if_pos hXm]
      rw [hR]; rfl
    · exact (pullback_boLocal_reduction_eq_nil M hM hm t ht hd hdn
        (le_antisymm ht.2.2.1 (not_lt.1 hXm)) h hYm).symm
  have heq : maxOrder (t.pullback h).I = m := le_antisymm hY.2.2.1 (not_lt.1 hYm)
  have : CharZero t.k := ht.1.1
  have : LocallyOfFiniteType t.sX := ht.1.2.2.1
  have : LocallyOfFiniteType (h ≫ t.sX) := hY.1.2.2.1
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr ht.1.2.2.1
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 ht.1.2.1
  have hmax : maxOrder t.I = m := maxOrder_eq_of_maxOrder_comap_eq hd t ht.1 ht.2.1 ht.2.2.1 h heq
  have hI : maxOrder (t.I.comap h) = maxOrder t.I := heq.trans hmax.symm
  have hXm : ¬ maxOrder t.I < m := by rw [hmax]; exact lt_irrefl _
  have hL : boLocal M m (t.pullback h) = boMaximalContact M m.factorial
      (wellTunedTriple (t.pullback h)) (mcHypersurfaceChoice (t.pullback h)) := by
    unfold boLocal; rw [if_neg hYm]
  have hR : boLocal M m t = boMaximalContact M m.factorial (wellTunedTriple t)
      (mcHypersurfaceChoice t) := by
    unfold boLocal; rw [if_neg hXm]
  rw [hL, hR]
  have hm' : 1 ≤ (maxOrder t.I).toNat := by rw [hmax]; simpa using hm
  have hW : wellTunedIdeal (h ≫ t.sX) (t.I.comap h) = (wellTunedIdeal t.sX t.I).comap h := by
    unfold wellTunedIdeal
    rw [hI]
    exact Kollar.maximalCoefficientIdeal_comap_of_smooth t.sX (h ≫ t.sX) ht.1.2.1 hY.1.2.1
      ht.1.2.2.2.2.1 hY.1.2.2.2.2.1 (one_le_topologicalKrullDim hd ht.2.1) h rfl t.I hm' hI _
  have hWt : wellTunedTriple (t.pullback h) = (wellTunedTriple t).pullback h := by
    change (⟨⟨Y, wellTunedIdeal (h ≫ t.sX) (t.I.comap h), t.E.comap h⟩, t.k, h ≫ t.sX⟩ :
      FieldBlowupTriple.{u}) = ⟨⟨Y, (wellTunedIdeal t.sX t.I).comap h, t.E.comap h⟩, t.k,
        h ≫ t.sX⟩
    rw [hW]
  obtain ⟨hWmax, hWtr, -⟩ := wellTunedTriple_spec hd hm t ht.1 ht.2.1 hmax
  obtain ⟨hWmaxY, hWtrY, -⟩ := wellTunedTriple_spec hd' hm (t.pullback h) hY.1 hY.2.1 heq
  have hH := isMCHypersurface_mcHypersurfaceChoice t ht hmax
  have hHY := isMCHypersurface_mcHypersurfaceChoice _ hY heq
  have hHc : IsMCHypersurface (h ≫ t.sX) (t.I.comap h) ((mcHypersurfaceChoice t).comap h) := by
    refine ⟨isSmoothHypersurface_comap_of_smooth t ht.1 hH.1 h, ?_⟩
    rw [maximalContactIdeal_comap_of_smooth t.sX (h ≫ t.sX) h rfl
      (pos_dim_of_mem_irreducibleComponents hd t ht.1 ht.2.1) t.I hI]
    exact Scheme.IdealSheafData.comap_mono h hH.2
  have hW1 := isMCHypersurface_wellTuned hd' hm (t.pullback h) hY.1 hY.2.1 heq hHY
  have hW2 := isMCHypersurface_wellTuned hd' hm (t.pullback h) hY.1 hY.2.1 heq hHc
  obtain ⟨_, rfl, hdX⟩ := ht.2.1
  obtain ⟨_, rfl, hdY⟩ := hY.2.1
  have hfac : 1 ≤ m.factorial := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [boMaximalContact_eq_of_isMCHypersurface M hn hM (wellTunedTriple (t.pullback h)) hWtrY
    hdY hd' hd'n hfac hWmaxY hW1 hW2]
  have hP := boMaximalContact_pullback M hn hM (wellTunedTriple t) hWtr hdX hd hdn hfac hWmax
    (isMCHypersurface_wellTuned hd hm t ht.1 ht.2.1 hmax hH) h inferInstance (Or.inl hMe)
    (hWt ▸ hWtrY) hdY hd' hd'n (by change maxOrder ((wellTunedIdeal t.sX t.I).comap h) = _
                                   rw [← hW]; exact hWmaxY)
  exact (boMaximalContact_congr _ _ _ hW _).trans hP

private theorem extFunctor_local {n m : ℕ} (M : MarkedFamily.{u}) (hn : 1 ≤ n)
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ i ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {i} μ) (fun t _ => M i μ t)) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim (Set.Icc 1 n) m)
    {X' : Scheme.{u}} (g : X' ⟶ t.X) (hg : IsOpenCoverMap g) (hgs : Surjective g)
    (hloc : t.pullback g ∈ mcLocalTriples (dimNat t.X) m)
    {Ys : Scheme.{u}} (k : Ys ⟶ (t.pullback g).X) (hk : Smooth k)
    (hY' : (t.pullback g).pullback k ∈ extClass n m) :
    extFunctor M m ((t.pullback g).pullback k) =
      ((extFunctor M m (t.pullback g)).pullback k).reduction := by
  have := hk
  by_cases hYe : IsEmpty Ys
  · have : IsEmpty ((t.pullback g).pullback k).X := hYe
    have hL : extFunctor M m ((t.pullback g).pullback k) = .nil _ := by
      unfold extFunctor; exact if_pos hYe
    exact hL.trans (Eq.trans (ClosedBlowupSequence.reduction_pullback _ _)
      (pullbackReduced_eq_nil_of_isEmpty _ _)).symm
  rw [not_isEmpty_iff] at hYe
  have : Nonempty X' := ⟨k hYe.some⟩
  obtain ⟨ht', h1, h2⟩ := mem_idealTriplesOfDim_dimNat ht
  obtain ⟨hX', hdX'⟩ := pullback_mem_of_isOpenCoverMap ht g hg
  have hY'' := mem_of_mem_extClass hY' hYe
  obtain ⟨hY3, h1', h2'⟩ := mem_idealTriplesOfDim_dimNat hY''
  have hM' := isMarkedOrderReductionFamily_mono hM (Nat.sub_le_sub_right h2 1)
  have hM'' := isMarkedOrderReductionFamily_mono hM (Nat.sub_le_sub_right h2' 1)
  rw [extFunctor_of_mem M hX', extFunctor_of_mem M hY'']
  have hb : boFunctor M (dimNat (t.pullback g).X) m (t.pullback g) =
      boLocal M m (t.pullback g) := by
    change boFunctor M (dimNat X') m _ = _
    rw [hdX', boFunctor_pullback_of_isOpenCoverMap M h1 hM' hm t ht' g hg hgs]
    exact boFunctor_pullback M h1 hM' hm t ht' g hg hgs hloc
  have hYloc := pullback_mem_mcLocalTriples_of_smooth h1 _ hloc k hY3
  rw [hb, boFunctor_eq_boLocal M h1' hM'' hm _ hYloc]
  exact boLocal_pullback_of_smooth M hn hM hMe hm _ hloc h1 h2 k hYloc h1' h2'

/-- **Globalization.** `𝓑𝓞(Y) = (h^*𝓑𝓞(X))^red` for smooth `h : Y → X` within the class: pass to
a surjective open cover of `X` by a local triple, apply the local case there, and descend along
the base change of the cover to `Y`. -/
private theorem boFunctor_pullback_of_smooth {n m : ℕ} (M : MarkedFamily.{u}) (hn : 1 ≤ n)
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ i ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {i} μ) (fun t _ => M i μ t)) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u})
    (ht : t ∈ idealTriplesOfDim (Set.Icc 1 n) m) {Y : Scheme.{u}} (h : Y ⟶ t.X) (hs : Smooth h)
    (hY : t.pullback h ∈ idealTriplesOfDim (Set.Icc 1 n) m) :
    boFunctor M (dimNat Y) m (t.pullback h) =
      ((boFunctor M (dimNat t.X) m t).pullback h).reduction := by
  obtain ⟨ht', h1, h2⟩ := mem_idealTriplesOfDim_dimNat ht
  obtain ⟨X', g, hg, hgs, hloc⟩ := exists_surjective_isOpenCoverMap_mem_mcLocalTriples h1 hm t ht'
  have : Smooth (Limits.pullback.fst h g) :=
    smooth_of_isOpenCoverMap
      (isOpenCoverMap_of_isPullback (IsPullback.of_hasPullback h g).flip hg)
  have := hgs
  have hfs : Surjective (Limits.pullback.fst h g) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback h g).flip hgs
  have hYs := extClass_pullback _ (Or.inl hY) _ _
    (isOpenCoverMap_of_isPullback (IsPullback.of_hasPullback h g).flip hg)
  have e : (t.pullback h).pullback (Limits.pullback.fst h g) =
      (t.pullback g).pullback (Limits.pullback.snd h g) := by
    rw [fieldBlowupTriple_pullback_pullback, fieldBlowupTriple_pullback_pullback,
      Limits.pullback.condition]
  have key : extFunctor M m (t.pullback h) = ((extFunctor M m t).pullback h).reduction := by
    refine eq_pullback_reduction_of_pullback_eq (k := Limits.pullback.fst h g)
      (k' := Limits.pullback.snd h g) _ Limits.pullback.condition ?_
    have hsnd : Smooth (Limits.pullback.snd h g) :=
      MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback h g) hs
    have hext : ∀ {s s' : FieldBlowupTriple.{u}}, s = s' →
        extFunctor M m s ≍ extFunctor M m s' := fun e => by subst e; rfl
    refine (extFunctor_pullback_of_surjective M hM hm _ (Or.inl hY) _ _
      (isOpenCoverMap_of_isPullback (IsPullback.of_hasPullback h g).flip hg) hfs).symm.trans ?_
    have e2 : extFunctor M m ((t.pullback h).pullback (Limits.pullback.fst h g)) =
        extFunctor M m ((t.pullback g).pullback (Limits.pullback.snd h g)) := eq_of_heq (hext e)
    refine e2.trans ?_
    refine (extFunctor_local M hn hM hMe hm t ht g hg hgs hloc _ hsnd (e ▸ hYs)).trans ?_
    exact congrArg
      (fun C : ClosedBlowupSequence X' => (C.pullback (Limits.pullback.snd h g)).reduction)
      (extFunctor_pullback_of_surjective M hM hm _ (Or.inl ht) _ _ hg hgs)
  rwa [extFunctor_of_mem M ht, extFunctor_of_mem M hY] at key

/-- **Kollár, Thm. 3.103 (2), smooth morphisms.** Let `n ≥ 1`, let `𝓜` be a marked
order-reduction family on dimensions `0, …, n - 1` (`IsMarkedOrderReductionFamily`) whose
members ignore empty entries (`IgnoresEmptyEntriesMarked`), and `m ≥ 1`. On the class of
triples `(X, I, E)` with `1 ≤ dim X ≤ n` and `maxord I ≤ m` (`idealTriplesOfDim`), the functor
`(X, I, E) ↦ boFunctor M (dim X) m (X, I, E)` commutes with smooth morphisms
(`CommutesWithSmoothOn`). -/
@[mmp "thm_kr3e_order_reduction_ideals_commutes_smooth"]
public theorem commutesWithSmoothOn_boFunctor {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hMe : ∀ d ∈ Set.Icc 0 (n - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t))
    (hm : 1 ≤ m) :
    CommutesWithSmoothOn (idealTriplesOfDim (Set.Icc 1 n) m)
      (fun t _ => boFunctor M (dimNat t.X) m t) := by
  refine ⟨fun t ht Y h hs hsu _ _ hY => ?_,
    fun t ht Y h hs _ _ hY => boFunctor_pullback_of_smooth M hn hM hMe hm t ht h hs hY⟩
  have := hsu
  obtain ⟨ht', h1, h2⟩ := mem_idealTriplesOfDim_dimNat ht
  exact (boFunctor_pullback_of_smooth M hn hM hMe hm t ht h hs hY).trans
    (ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (boFunctor_isOrderMTripleSeq M h1
        (isMarkedOrderReductionFamily_mono hM (Nat.sub_le_sub_right h2 1)) hm t ht').2 h))

/-! ### `𝓑𝓞` commutes with change of fields -/

/-- Change of fields preserves the dimension of a scheme locally of finite type over a field
([Stacks, Tag 02FY]). -/
private theorem topologicalKrullDim_fieldChangeScheme (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {L : Type u} [Field L] (σ : t.k →+* L) :
    topologicalKrullDim (t.fieldChangeScheme σ) = topologicalKrullDim t.X := by
  obtain ⟨-, -, hlft, -, -, -, -⟩ := ht
  letI := σ.toAlgebra
  exact topologicalKrullDim_baseChange t.k L (t.fieldChangeProj σ) (t.fieldChange σ).sX t.sX
    (IsPullback.of_hasPullback _ _)

/-- Change of fields preserves equidimensionality: the local dimension at a point of `X_L` is
the local dimension of `X` at its image ([Stacks, Tag 02FY]). -/
private theorem equidimensional_fieldChangeScheme (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {d : ℕ} (hdim : topologicalKrullDim t.X = ((d : ℕ∞) : WithBot ℕ∞))
    {L : Type u} [Field L] (σ : t.k →+* L) : Equidimensional (t.fieldChangeScheme σ) := by
  obtain ⟨-, -, hlft, -, heq, -, -⟩ := ht
  letI := σ.toAlgebra
  set q : t.fieldChangeScheme σ ⟶ Spec (.of L) :=
    Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom (algebraMap t.k L)))
  have hP : IsPullback (t.fieldChangeProj σ) q t.sX
      (Spec.map (CommRingCat.ofHom (algebraMap t.k L))) := IsPullback.of_hasPullback _ _
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback hP hlft
  refine equidimensional_of_topologicalKrullDimAt_eq L _ q (d := d) fun x => ?_
  rw [← topologicalKrullDimAt_eq_of_isPullback_of_subsingleton hP x]
  exact topologicalKrullDimAt_eq_of_equidimensional t.k t.X t.sX heq hdim _

/-- The higher derivative ideals commute with the pull-back along `X_L ⟶ X`. -/
private theorem higherDerivativeIdeal_comap_pullback_fst {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) r =
      (higherDerivativeIdeal sX I r).comap
        (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  letI := σ.toAlgebra
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih]
    exact (derivativeIdeal_comap_pullback_fst (L := L) sX).2 _

/-- A morphism of smooth schemes over fields of characteristic zero that commutes with all
higher derivative ideals of `I` preserves the order of `I` pointwise. -/
private theorem multAt_comap_eq_of_higherDerivativeIdeal {k K : Type u} [Field k] [CharZero k]
    [Field K] [CharZero K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of K))
    [Smooth sX] [Smooth sY] (f : Y ⟶ X) (I : X.IdealSheafData)
    (hD : ∀ j, higherDerivativeIdeal sY (I.comap f) j = (higherDerivativeIdeal sX I j).comap f)
    (y : Y) : multAt (I.comap f) y = multAt I (f y) := by
  have key (n : ℕ) : (n : ℕ∞) ≤ multAt (I.comap f) y ↔ (n : ℕ∞) ≤ multAt I (f y) := by
    cases n with
    | zero => simp
    | succ n =>
      rw [succ_le_multAt_iff_forall_mem_support sY, succ_le_multAt_iff_forall_mem_support sX]
      exact forall₂_congr fun j _ => hD j ▸ mem_support_comap_iff f _ y
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n => (key n).1)
    (ENat.forall_natCast_le_iff_le.mp fun n => (key n).2)

/-- The structure morphism of a field change of a triple is smooth. -/
private theorem smooth_fieldChange_sX (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) : Smooth t.sX ∧ Smooth (t.fieldChange σ).sX := by
  obtain ⟨-, hsm, hlft, -, -, -, -⟩ := ht
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hlft
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  exact ⟨this, (inferInstance : MorphismProperty.IsStableUnderBaseChange @Smooth).of_isPullback
    (IsPullback.of_hasPullback _ _) this⟩

/-- Change of fields preserves the maximal order. -/
private theorem maxOrder_fieldChange (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    maxOrder (t.fieldChange σ).I = maxOrder t.I := by
  obtain ⟨h1, h2⟩ := smooth_fieldChange_sX t ht σ
  have := ht.1
  haveI : CharZero (t.fieldChange σ).k := charZero_of_injective_ringHom σ.injective
  exact maxOrder_comap_of_surjective _ t.I (t.fieldChangeProj σ).surjective
    (multAt_comap_eq_of_higherDerivativeIdeal t.sX (t.fieldChange σ).sX _ t.I
      (higherDerivativeIdeal_comap_pullback_fst σ t.sX t.I))

/-- Change of fields preserves triples. -/
private theorem mem_triples_fieldChange (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {d : ℕ} (hdim : topologicalKrullDim t.X = ((d : ℕ∞) : WithBot ℕ∞))
    {L : Type u} [Field L] (σ : t.k →+* L) : t.fieldChange σ ∈ triples :=
  mem_triples_iff.2 ⟨fieldChange_mem_sncTriples (mem_triples_iff.1 ht).1 σ,
    equidimensional_fieldChangeScheme t ht hdim σ⟩

/-- Change of fields preserves smooth hypersurfaces. -/
private theorem isSmoothHypersurface_comap_fieldChangeProj (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {H : t.X.IdealSheafData} (hH : IsSmoothHypersurface t.sX H)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    IsSmoothHypersurface (t.fieldChange σ).sX (H.comap (t.fieldChangeProj σ)) := by
  have hsX : Smooth t.sX := (smooth_fieldChange_sX t ht σ).1
  obtain ⟨hchar, hsm, hlft, hqc, -, -, -⟩ := ht
  have hcharL : CharZero L := (RingHom.charZero_iff σ.injective).mp hchar
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  obtain ⟨hlftL, -⟩ := t.fieldChange_finiteType σ
  have : PerfectField t.k := PerfectField.ofCharZero
  have : PerfectField (t.fieldChange σ).k := (PerfectField.ofCharZero : PerfectField L)
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra t.k L := σ.toAlgebra
    exact (inferInstance : Module.Flat t.k L)
  set p := t.fieldChangeProj σ
  have : Flat p :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange @Flat).of_isPullback
      (IsPullback.of_hasPullback _ _).flip ‹_›
  have : IsLocallyNoetherian (t.fieldChange σ).X :=
    LocallyOfFiniteType.isLocallyNoetherian (t.fieldChange σ).sX
  -- `H` is cut out at each of its points by one regular parameter
  have hD : ∀ x ∈ H.support, ∃ (m : ℕ) (w : Fin m → t.X.presheaf.stalk x) (j : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧ IdealSheafData.stalk H x = Ideal.span {w j} := by
    intro x hx
    have hISreg := MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk t.sX H hH.1 hx
    have : IsRegularLocalRing (t.X.presheaf.stalk x) :=
      (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk t.sX).mp hsX x
    have : (IdealSheafData.stalk H x).IsPrime := by
      have : IsDomain (t.X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) :=
        IsRegularLocalRing.isDomain _
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hht := MMP.Flips.ResolutionInputs.height_stalk_eq_one_of_isPureCodimOne H hH.2 (x := x)
    have hdim := MMP.Flips.ResolutionInputs.ringKrullDim_quotient_add_one_of_height_eq_one _ hht
    set m := (IsLocalRing.maximalIdeal
      (t.X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)).spanFinrank
    have hJdim : ringKrullDim (t.X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) = m :=
      (IsRegularLocalRing.spanFinrank_maximalIdeal).symm
    have hR : ringKrullDim (t.X.presheaf.stalk x) = ((1 + m : ℕ) : WithBot ℕ∞) := by
      rw [← hdim, hJdim, add_comm]; push_cast; rfl
    obtain ⟨x0, y0, hw, -, hI⟩ :=
      MMP.Flips.ResolutionInputs.exists_flag_isRegularSystemOfParameters le_rfl hISreg hdim
        hISreg le_rfl hR hJdim
    exact ⟨1 + m, Fin.append x0 y0, Fin.castAdd m 0, hw, by rw [hI, Fin.append_left]; rfl⟩
  have hD' : ∀ y ∈ (H.comap p).support, ∃ (m : ℕ) (w : Fin m → _)
      (j : Fin m), MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (H.comap p) y = Ideal.span {w j} := by
    intro y hy
    have hpy : p y ∈ H.support := (mem_support_comap_iff p H y).1 hy
    obtain ⟨n, z, j, hz, hzj⟩ := hD (p y) hpy
    obtain ⟨m, w, c', hw, hc', -⟩ := exists_coordinates_comap_of_flat p y (Flat.stalkMap p y)
      (isRegularLocalRing_closedFibre_of_isRegular_fiber p y
        (isRegular_fiber_pullback_fst t.sX σ (p y))) (fun _ : Unit => H) (c := fun _ => j) hz
      (fun _ => hzj) (fun a b _ => Subsingleton.elim a b)
    exact ⟨m, w, c' ⟨(), hy⟩, hw, hc' ⟨(), hy⟩⟩
  exact ⟨isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ hD',
    isPureCodimOne_support_of_stalk_eq_span_parameter _ hD'⟩

/-- Change of fields preserves MC-hypersurfaces. -/
private theorem isMCHypersurface_comap_fieldChangeProj (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H) {L : Type u} [Field L] (σ : t.k →+* L) :
    IsMCHypersurface (t.fieldChange σ).sX (t.fieldChange σ).I
      (H.comap (t.fieldChangeProj σ)) := by
  refine ⟨isSmoothHypersurface_comap_fieldChangeProj t ht hH.1 σ, ?_⟩
  have := (smooth_fieldChange_sX t ht σ).1
  have hD := higherDerivativeIdeal_comap_pullback_fst σ t.sX t.I
  unfold maximalContactIdeal
  rw [maxOrder_fieldChange t ht σ]
  change _ ≤ higherDerivativeIdeal (Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom σ)))
    (t.I.comap (Limits.pullback.fst t.sX (Spec.map (CommRingCat.ofHom σ)))) _
  rw [hD]
  exact Scheme.IdealSheafData.comap_mono _ hH.2

/-- Change of fields preserves local triples. -/
private theorem mem_mcLocalTriples_fieldChange {n m : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ mcLocalTriples n m) {L : Type u} [Field L] (σ : t.k →+* L) :
    t.fieldChange σ ∈ mcLocalTriples n m := by
  obtain ⟨htr, ⟨d, hd, hdim⟩, hle, hor⟩ := ht
  have hord := maxOrder_fieldChange t htr σ
  refine ⟨mem_triples_fieldChange t htr hdim σ,
    ⟨d, hd, (topologicalKrullDim_fieldChangeScheme t htr σ).trans hdim⟩, hord ▸ hle, ?_⟩
  rcases hor with h | ⟨h1, H, hH⟩
  · exact Or.inl (hord ▸ h)
  · exact Or.inr ⟨hord.trans h1, _, isMCHypersurface_comap_fieldChangeProj t htr hH σ⟩

/-- The base change `g_L : X^*_L → X_L` of `g : X^* → X` along `σ`. -/
private noncomputable def fieldChangeMap (t : FieldBlowupTriple.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) {L : Type u} [Field L] (σ : t.k →+* L) :
    Limits.pullback (g ≫ t.sX) (Spec.map (CommRingCat.ofHom σ)) ⟶ t.fieldChangeScheme σ :=
  Limits.pullback.map ((t.pullback g).sX) (Spec.map (CommRingCat.ofHom σ))
    t.sX (Spec.map (CommRingCat.ofHom σ)) g (𝟙 _) (𝟙 _) (Category.comp_id _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem fieldChangeMap_fst (t : FieldBlowupTriple.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) {L : Type u} [Field L] (σ : t.k →+* L) :
    fieldChangeMap t g σ ≫ t.fieldChangeProj σ = (t.pullback g).fieldChangeProj σ ≫ g :=
  Limits.pullback.lift_fst _ _ _

private theorem fieldChangeMap_snd (t : FieldBlowupTriple.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) {L : Type u} [Field L] (σ : t.k →+* L) :
    fieldChangeMap t g σ ≫ (t.fieldChange σ).sX = ((t.pullback g).fieldChange σ).sX :=
  (Limits.pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The base change of a surjective open cover map is one. -/
private theorem isOpenCoverMap_fieldChangeMap (t : FieldBlowupTriple.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) (hg : IsOpenCoverMap g) (hs : Surjective g) {L : Type u} [Field L]
    (σ : t.k →+* L) :
    IsOpenCoverMap (fieldChangeMap t g σ) ∧ Surjective (fieldChangeMap t g σ) := by
  set q : Limits.pullback (g ≫ t.sX) (Spec.map (CommRingCat.ofHom σ)) ⟶ X' :=
    Limits.pullback.fst _ _ with hq
  have hR : IsPullback (Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom σ)))
      (t.fieldChangeProj σ) (Spec.map (CommRingCat.ofHom σ)) t.sX :=
    (IsPullback.of_hasPullback _ _).flip
  have hO : IsPullback (fieldChangeMap t g σ ≫
      Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom σ)))
      q (Spec.map (CommRingCat.ofHom σ)) (g ≫ t.sX) := by
    convert (IsPullback.of_hasPullback (g ≫ t.sX) (Spec.map (CommRingCat.ofHom σ))).flip using 1
    exact fieldChangeMap_snd t g σ
  have hP : IsPullback (fieldChangeMap t g σ) q (t.fieldChangeProj σ) g :=
    IsPullback.of_right hO (fieldChangeMap_fst t g σ) hR
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip hs⟩
  obtain ⟨r, U, hdisj, hU, hi⟩ := hg
  refine ⟨r, fun a => q ⁻¹ᵁ U a, fun a b hab => ?_, ?_, fun a => ?_⟩
  · change Disjoint (q ⁻¹ᵁ U a) (q ⁻¹ᵁ U b)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hdisj hab),
      Scheme.Hom.preimage_bot]
  · rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  · exact MorphismProperty.of_isPullback
      ((isPullback_morphismRestrict q (U a)).paste_vert hP.flip) (hi a)

/-- Pulling `(X_L, I_L, E_L)` back along `g_L` gives the field change of `(X^*, g^*I, g⁻¹E)`. -/
private theorem pullback_fieldChangeMap (t : FieldBlowupTriple.{u}) {X' : Scheme.{u}}
    (g : X' ⟶ t.X) {L : Type u} [Field L] (σ : t.k →+* L) :
    (t.fieldChange σ).pullback (fieldChangeMap t g σ) = (t.pullback g).fieldChange σ := by
  have hc : fieldChangeMap t g σ ≫ t.fieldChangeProj σ =
      (t.pullback g).fieldChangeProj σ ≫ g := fieldChangeMap_fst t g σ
  have hcomap : ∀ J : t.X.IdealSheafData, (J.comap (t.fieldChangeProj σ)).comap
      (fieldChangeMap t g σ) = (J.comap g).comap ((t.pullback g).fieldChangeProj σ) :=
    fun J => (Scheme.IdealSheafData.comap_comp _ _ _).symm.trans
      ((congrArg J.comap hc).trans (Scheme.IdealSheafData.comap_comp _ _ _))
  have h₂ : (fun i => ((t.E.E i).comap (t.fieldChangeProj σ)).comap (fieldChangeMap t g σ)) =
      fun i => ((t.E.E i).comap g).comap ((t.pullback g).fieldChangeProj σ) :=
    funext fun i => hcomap _
  have h₃ := fieldChangeMap_snd t g σ
  have h₁ := hcomap t.I
  unfold FieldBlowupTriple.pullback FieldBlowupTriple.fieldChange OrderedDivisor.comap at *
  simp only at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]

/-- On a local triple of maximal order `m ≥ 1`, the well-tuned ideal commutes with change of
fields: `W(I_L) = p^* W(I)` (`Kollar.maximalCoefficientIdeal_comap_fieldChange` with `s = m!`). -/
private theorem wellTunedIdeal_fieldChange {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) (hmax : maxOrder t.I = m)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    wellTunedIdeal (t.fieldChange σ).sX (t.fieldChange σ).I =
      (wellTunedIdeal t.sX t.I).comap (t.fieldChangeProj σ) := by
  obtain ⟨-, hsm, hlft, -, heq, -, -⟩ := ht.1
  obtain ⟨d, hd, hdim⟩ := ht.2.1
  rw [Set.mem_singleton_iff] at hd
  subst hd
  have : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hlft
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have := ht.1.1
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by rw [hdim]; exact_mod_cast hn
  unfold wellTunedIdeal
  rw [maxOrder_fieldChange t ht.1 σ]
  exact Kollar.maximalCoefficientIdeal_comap_fieldChange σ t.sX heq hdim1 t.I
    (by simp [hmax]; omega) _

/-- `𝓑_{n,m}` commutes with change of fields on local triples. -/
private theorem boLocal_fieldChange {n m : ℕ} (M : MarkedFamily.{u}) (hn : 1 ≤ n)
    (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m) {d : ℕ} (hd1 : 1 ≤ d)
    (hdn : d ≤ n) (s : FieldBlowupTriple.{u}) (hs : s ∈ mcLocalTriples d m)
    {L : Type u} [Field L] (σ : s.k →+* L) :
    boLocal M m (s.fieldChange σ) = (boLocal M m s).pullback (s.fieldChangeProj σ) := by
  have hsL := mem_mcLocalTriples_fieldChange s hs σ
  have hord := maxOrder_fieldChange s hs.1 σ
  by_cases hlt : maxOrder s.I < m
  · have hlt' : maxOrder (s.fieldChange σ).I < m := hord ▸ hlt
    simp only [boLocal, hlt, hlt', ↓reduceIte]
    rfl
  have hmax : maxOrder s.I = m := le_antisymm hs.2.2.1 (not_lt.mp hlt)
  have hmax' : maxOrder (s.fieldChange σ).I = m := hord.trans hmax
  have hlt' : ¬ maxOrder (s.fieldChange σ).I < m := by rw [hmax']; exact lt_irrefl _
  simp only [boLocal, hlt, hlt', ↓reduceIte]
  obtain ⟨d', hd', hdim⟩ := hs.2.1
  rw [Set.mem_singleton_iff] at hd'
  subst hd'
  obtain ⟨hWmax, hWt, -⟩ := wellTunedTriple_spec hd1 hm s hs.1 hs.2.1 hmax
  have hHW := isMCHypersurface_wellTunedIdeal hd1 hm s hs hmax
  have hW := wellTunedIdeal_fieldChange hd1 hm s hs hmax σ
  set W : FieldBlowupTriple.{u} := ⟨⟨s.X, wellTunedIdeal s.sX s.I, s.E⟩, s.k, s.sX⟩
  refine (boMaximalContact_congr _ _ _ hW _).trans ?_
  change boMaximalContact M m.factorial (W.fieldChange σ) _ = _
  have hmf : 1 ≤ m.factorial := m.factorial_pos
  obtain ⟨hWLmax, hWLt, -⟩ := wellTunedTriple_spec hd1 hm (s.fieldChange σ) hsL.1 hsL.2.1 hmax'
  have hWLt' : W.fieldChange σ ∈ triples := by
    dsimp only [wellTunedTriple] at hWLt
    change IsTriple _ _ _ at hWLt ⊢
    rwa [hW] at hWLt
  have hWLmax' : maxOrder (W.fieldChange σ).I = (m.factorial : ℕ) := by rwa [hW] at hWLmax
  have hdimL : topologicalKrullDim (W.fieldChange σ).X = ((d' : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_fieldChangeScheme s hs.1 σ).trans hdim
  have hH1 : IsMCHypersurface (W.fieldChange σ).sX (W.fieldChange σ).I
      (mcHypersurfaceChoice (s.fieldChange σ)) := by
    have := isMCHypersurface_wellTunedIdeal hd1 hm (s.fieldChange σ) hsL hmax'
    rwa [hW] at this
  have hH2 : IsMCHypersurface (W.fieldChange σ).sX (W.fieldChange σ).I
      ((mcHypersurfaceChoice s).comap (s.fieldChangeProj σ)) :=
    isMCHypersurface_comap_fieldChangeProj W hWt hHW σ
  rw [boMaximalContact_eq_of_isMCHypersurface M hn hM (W.fieldChange σ) hWLt' hdimL hd1 hdn
    hmf hWLmax' hH1 hH2]
  exact boMaximalContact_fieldChange M hn hM W hWt hdim hd1 hdn hmf hWmax hHW σ

/-- **Kollár, Thm. 3.103 (2), change of fields.** Let `n ≥ 1`, let `𝓜` be a marked
order-reduction family on dimensions `0, …, n - 1` (`IsMarkedOrderReductionFamily`) and
`m ≥ 1`. On the class of triples `(X, I, E)` with `1 ≤ dim X ≤ n` and `maxord I ≤ m`
(`idealTriplesOfDim`), the functor `(X, I, E) ↦ boFunctor M (dim X) m (X, I, E)` commutes with
change of fields (`CommutesWithFieldChangeOn`). -/
@[mmp "thm_kr3e_order_reduction_ideals_commutes_field_change"]
public theorem commutesWithFieldChangeOn_boFunctor {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m) :
    CommutesWithFieldChangeOn (idealTriplesOfDim (Set.Icc 1 n) m)
      (fun t _ => boFunctor M (dimNat t.X) m t) := by
  intro t ht L _ σ hL
  obtain ⟨htr, ⟨d, hd, hdim⟩, hmax⟩ := ht
  have hdimL : topologicalKrullDim (t.fieldChange σ).X = ((d : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_fieldChangeScheme t htr σ).trans hdim
  have hdn : dimNat t.X = d := by simp [dimNat, hdim]
  have hdnL : dimNat (t.fieldChange σ).X = d := by simp [dimNat, hdimL]
  simp only [hdn, hdnL]
  have ht' : t ∈ idealTriplesOfDim {d} m := ⟨htr, ⟨d, rfl, hdim⟩, hmax⟩
  have htL' : t.fieldChange σ ∈ idealTriplesOfDim {d} m := ⟨hL.1, ⟨d, rfl, hdimL⟩, hL.2.2⟩
  have hMd : IsMarkedOrderReductionFamily 0 (d - 1) M :=
    isMarkedOrderReductionFamily_mono hM (Nat.sub_le_sub_right hd.2 1)
  obtain ⟨X', g, hg, hsurj, hloc⟩ :=
    exists_surjective_isOpenCoverMap_mem_mcLocalTriples hd.1 hm t ht'
  obtain ⟨hgL, hsurjL⟩ := isOpenCoverMap_fieldChangeMap t g hg hsurj σ
  have hlocL : (t.fieldChange σ).pullback (fieldChangeMap t g σ) ∈ mcLocalTriples d m := by
    rw [pullback_fieldChangeMap]
    exact mem_mcLocalTriples_fieldChange _ hloc σ
  have := smooth_of_isOpenCoverMap hgL
  apply Kollar.eq_of_pullback_eq_of_flat_of_surjective (fieldChangeMap t g σ)
  refine (boFunctor_pullback M hd.1 hMd hm _ htL' _ hgL hsurjL hlocL).trans ?_
  refine Eq.trans (b := boLocal M m ((t.pullback g).fieldChange σ))
    (eq_of_heq (boLocal_congr M m (pullback_fieldChangeMap t g σ))) ?_
  refine (boLocal_fieldChange M hn hM hm hd.1 hd.2 _ hloc σ).trans ?_
  rw [← boFunctor_pullback M hd.1 hMd hm t ht' g hg hsurj hloc]
  exact (pullback_pullback _ _ _).trans
    ((congrArg _ (fieldChangeMap_fst t g σ).symm).trans (pullback_pullback _ _ _).symm)

/-! ### `𝓑𝓞` reduces the maximal order -/

/-- The last morphism of the pull-back of a blow-up sequence along a surjective open cover map
is again a surjective open cover map (blow-ups commute with flat base change). -/
private theorem isOpenCoverMap_pullbackHom {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {X' : Scheme.{u}} (g : X' ⟶ X), IsOpenCoverMap g → Surjective g →
      IsOpenCoverMap (B.pullbackHom g) ∧ Surjective (B.pullbackHom g) := by
  induction B with
  | nil X => exact fun g hg hs => ⟨hg, hs⟩
  | cons Z B ih =>
    intro X' g hg hs
    have : Etale g := etale_of_isOpenCoverMap hg
    exact ih (canonicalLift g Z)
      (isOpenCoverMap_of_isPullback (Kollar.isPullback_canonicalLift_of_flat g Z) hg)
      (Kollar.surjective_canonicalLift g Z)

/-- A smooth blow-up sequence of order `m` starting with a triple is one starting with `(X, I)`. -/
private theorem isOrderMPlainSeq_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m →
        B.IsOrderMPlainSeq s I m
  | _, .nil _, _, _, _, h => ⟨h.2.1, h.2.2.2.2.2.1⟩
  | _, .cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.1.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      isOrderMPlainSeq_of_isOrderMTripleSeq m B _ _ _ h.2.2.2.2.2⟩

private theorem truncate_length {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.truncate B.length = B := by
  induction B with
  | nil _ => rfl
  | cons Z B ih =>
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [ih]

/-- **Descent of `maxord I_r < m`.** Let `B` be a smooth blow-up sequence of order `m` starting
with a triple `(X, I, E)` with `maxord I ≤ m`, and `g` a surjective open cover map. If the last
marked ideal of `g^*B` starting with `(g^*I, m)` has maximal order `< m`, so has the last
controlled transform `I_r` of `I` along `B`: that marked ideal is `(g_r^*I_r, m)`
(`isOrderGePlainSeq_pullback_of_etale`), and `g_r` is a surjective open cover map. -/
private theorem maxOrder_controlledTransform_lt_of_pullback (t : FieldBlowupTriple.{u}) {m : ℕ}
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) (B : ClosedBlowupSequence t.X)
    (hB : B.IsOrderMTripleSeq t.sX t.I t.E m) {X' : Scheme.{u}} (g : X' ⟶ t.X)
    (hg : IsOpenCoverMap g) (hsurj : Surjective g)
    (h : maxOrder ((B.pullback g).markedTransform ⟨t.I.comap g, m⟩).I < m) :
    maxOrder (B.controlledTransform t.I) < m := by
  have hP := isOrderMPlainSeq_of_isOrderMTripleSeq m B _ _ _ hB
  have hT : IsTriple t.sX t.I t.E := by
    cases B with
    | nil _ => exact hB
    | cons _ _ => exact hB.1
  obtain ⟨h0, hsm, hlft, hqc, heq, hI, -⟩ := hT
  have := h0; have := hlft; have := hqc
  have := etale_of_isOpenCoverMap hg
  have he := (ClosedBlowupSequence.isOrderGePlainSeq_pullback_of_etale t.sX hsm heq t.I hI m hm
    hmax B hP g).2 B.length
  rw [truncate_length] at he
  rw [he] at h
  obtain ⟨hgr, hsr⟩ := isOpenCoverMap_pullbackHom B g hg hsurj
  exact (maxOrder_comap_of_isOpenCoverMap hgr hsr _).ge.trans_lt h

/-- An empty cosupport `cosupp(I, m) = ∅` means `maxord I < m`. -/
private theorem maxOrder_lt_of_cosupport_eq_empty {X : Scheme.{u}} (I : X.IdealSheafData)
    {m : ℕ} (hm : 1 ≤ m) (h : (⟨I, m⟩ : MarkedIdeal X).cosupport = ∅) :
    maxOrder I < m := by
  have hx : ∀ x, multAt I x ≤ ((m - 1 : ℕ) : ℕ∞) := by
    intro x
    have hlt : multAt I x < m := by
      by_contra hc
      have : x ∈ (⟨I, m⟩ : MarkedIdeal X).cosupport := not_lt.1 hc
      simp [h] at this
    induction h' : multAt I x using ENat.recTopCoe with
    | top => rw [h'] at hlt; simp at hlt
    | coe a =>
      rw [h'] at hlt
      have : a < m := by exact_mod_cast hlt
      exact_mod_cast (by omega : a ≤ m - 1)
  have : maxOrder I ≤ ((m - 1 : ℕ) : ℕ∞) := iSup₂_le fun x _ => hx x
  exact this.trans_lt (by exact_mod_cast (by omega : m - 1 < m))

/-- `I^{(m-1)!} ≤ W(I)` for `m = maxord I ≥ 1`: the exponent vector `c = ((m-1)!, 0, …, 0)` has
weight `m · (m-1)! = m!`. -/
private theorem pow_le_wellTunedIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) :
    I ^ ((maxOrder I).toNat - 1).factorial ≤ wellTunedIdeal sX I := by
  set m := (maxOrder I).toNat
  let c : Fin (m + 1) → ℕ := Pi.single 0 (m - 1).factorial
  have hw : ((m.factorial : ℕ) : ℤ) ≤ (coefficientWeight m c : ℤ) := by
    have : coefficientWeight m c = m * (m - 1).factorial := by
      unfold coefficientWeight
      rw [Fintype.sum_eq_single 0 (fun j hj => by simp [c, Pi.single_apply, hj])]
      simp [c]
    rw [this]
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [hm', Nat.add_sub_cancel, Nat.factorial_succ]
  have hprod : ∏ j : Fin (m + 1), higherDerivativeIdeal sX I (j : ℕ) ^ c j =
      I ^ (m - 1).factorial := by
    rw [Fintype.prod_eq_single 0 (fun j hj => by simp [c, Pi.single_apply, hj])]
    simp [c, higherDerivativeIdeal_zero]
  unfold wellTunedIdeal maximalCoefficientIdeal
  rw [← hprod]
  exact le_iSup₂_of_le (f := fun (c : Fin (m + 1) → ℕ) (_ : ((m.factorial : ℕ) : ℤ) ≤
    (coefficientWeight m c : ℤ)) =>
      ∏ j : Fin (m + 1), higherDerivativeIdeal sX I (j : ℕ) ^ c j) c hw le_rfl

/-- In the maximal-order case the last controlled transform of `𝓑_{n,m}` has `maxord < m`:
`maxord W_r < m!`, and tuning identifies `cosupp(I_r, m)` with `cosupp(W_r, m!)`. -/
private theorem maxOrder_controlledTransform_boLocal_lt_of_maxOrder_eq {n m : ℕ}
    (M : MarkedFamily.{u}) (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M)
    (hm : 1 ≤ m) (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m)
    (hmax : maxOrder t.I = m) :
    maxOrder ((boLocal M m t).controlledTransform t.I) < m := by
  have hBI := boLocal_isOrderMTripleSeq_of_maxOrder_eq M hn hM hm t ht hmax
  have hlt : ¬ maxOrder t.I < m := by simp [hmax]
  simp only [boLocal, hlt, ↓reduceIte] at hBI ⊢
  set tW : FieldBlowupTriple.{u} := ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩
  obtain ⟨hWmax, hWt, -⟩ := wellTunedTriple_spec hn hm t ht.1 ht.2.1 hmax
  replace hWt : IsTriple t.sX (wellTunedIdeal t.sX t.I) t.E := hWt
  have hH := isMCHypersurface_wellTunedIdeal hn hm t ht hmax
  obtain ⟨h0, hsm, hlft, hqc, heq, -, -⟩ := ht.1
  obtain ⟨d, hd, hdim⟩ := ht.2.1
  rw [Set.mem_singleton_iff] at hd
  subst hd
  have hm! : 1 ≤ m.factorial := Nat.factorial_pos m
  have hB := boMaximalContact_isOrderMTripleSeq (N := d) (n := d) (m := m.factorial) M hn hM tW
    hWt hdim hn le_rfl hm! hWmax (mcHypersurfaceChoice t) hH
  set B := boMaximalContact M m.factorial tW (mcHypersurfaceChoice t)
  have hWr : maxOrder (B.controlledTransform (wellTunedIdeal t.sX t.I)) < m.factorial :=
    maxOrder_endOf_boMaximalContact_lt (N := d) (n := d) M hn hM tW hWt hdim hn le_rfl hm!
      hWmax (mcHypersurfaceChoice t) hH
  have hsmB : B.IsSmooth t.sX := isSmooth_of_isOrderMTripleSeq _ B _ _ _ hB
  have hmn : (maxOrder t.I).toNat = m := by simp [hmax]
  have hfac : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
  have hIr := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E
    ht.1 m hmax B)
  have hWtr := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX
    (wellTunedIdeal t.sX t.I) t.E hWt m.factorial hWmax B).2 hB
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by
    rw [hdim]; exact_mod_cast hn
  have := h0
  have : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hpow : t.I ^ (m - 1).factorial ≤ wellTunedIdeal t.sX t.I := by
    have := pow_le_wellTunedIdeal t.sX t.I (by omega)
    rwa [hmn] at this
  have hJ : wellTunedIdeal t.sX t.I ≤
      maximalCoefficientIdeal t.sX t.I (((maxOrder t.I).toNat * (m - 1).factorial : ℕ) : ℤ) :=
    le_of_eq (by rw [hmn, hfac, wellTunedIdeal, hmn])
  have hGe : B.IsOrderGeMarkedTripleSeq t.sX ⟨t.I, (maxOrder t.I).toNat⟩ t.E := by
    rw [hmn]; exact hIr.1.2 hBI
  have htune :=
    ClosedBlowupSequence.cosupport_markedTransform_eq_of_pow_le_of_le_maximalCoefficientIdeal
      t.sX heq hdim1 t.I (by omega) (m - 1).factorial (Nat.factorial_pos _)
      (wellTunedIdeal t.sX t.I) hpow hJ t.E B hsmB hGe
  rw [hmn, hfac] at htune
  have hempty : (B.markedTransform ⟨wellTunedIdeal t.sX t.I, m.factorial⟩).cosupport = ∅ := by
    ext x
    simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_le, ClosedBlowupSequence.markedTransform_m, hWtr]
    exact (multAt_le_maxOrder _ x).trans_lt hWr
  rw [hempty] at htune
  have hI : (B.markedTransform ⟨t.I, m⟩) = ⟨B.controlledTransform t.I, m⟩ := by
    rw [← hIr.2 hBI]
    conv_lhs => rw [show B.markedTransform ⟨t.I, m⟩ =
      ⟨(B.markedTransform ⟨t.I, m⟩).I, (B.markedTransform ⟨t.I, m⟩).m⟩ from rfl]
    rw [ClosedBlowupSequence.markedTransform_m]
  rw [hI] at htune
  rw [if_neg hlt]
  exact maxOrder_lt_of_cosupport_eq_empty _ hm htune

/-- On a local triple the last marked ideal of `𝓑_{n,m}` starting with `(I, m)` is the last
controlled transform of `I`. -/
private theorem markedTransform_boLocal_I {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) :
    ((boLocal M m t).markedTransform ⟨t.I, m⟩).I = (boLocal M m t).controlledTransform t.I := by
  by_cases hlt : maxOrder t.I < m
  · rw [boLocal, if_pos hlt]
    rfl
  · have hmax := le_antisymm ht.2.2.1 (not_lt.1 hlt)
    exact (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E
      ht.1 m hmax _).2 (boLocal_isOrderMTripleSeq_of_maxOrder_eq M hn hM hm t ht hmax)

/-- The last controlled transform of `𝓑_{n,m}` on a local triple has `maxord < m`. -/
private theorem maxOrder_controlledTransform_boLocal_lt {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ mcLocalTriples n m) :
    maxOrder ((boLocal M m t).controlledTransform t.I) < m := by
  by_cases hlt : maxOrder t.I < m
  · rw [boLocal, if_pos hlt]
    exact hlt
  · exact maxOrder_controlledTransform_boLocal_lt_of_maxOrder_eq M hn hM hm t ht
      (le_antisymm ht.2.2.1 (not_lt.1 hlt))

/-- **Kollár, Thm. 3.103 (1).** Let `𝓜` be a marked order-reduction family on dimensions
`0, …, n - 1` (`IsMarkedOrderReductionFamily`), `n, m ≥ 1`, and `(X, I, E)` a triple with
`dim X = n` and `maxord I ≤ m` (`idealTriplesOfDim`). Then the end `(X_r, I_r, E_r)` of
`boFunctor M n m (X, I, E)` (`FieldBlowupTriple.endOf`) satisfies `maxOrder I_r < m`. -/
@[mmp "thm_kr3e_order_reduction_ideals_reduces_order"]
public theorem maxOrder_endOf_boFunctor_lt {n m : ℕ} (M : MarkedFamily.{u})
    (hn : 1 ≤ n) (hM : IsMarkedOrderReductionFamily 0 (n - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ idealTriplesOfDim {n} m) :
    maxOrder (t.endOf (boFunctor M n m t)).I < m := by
  obtain ⟨X', g, hg, hsurj, hloc⟩ := exists_surjective_isOpenCoverMap_mem_mcLocalTriples hn hm t ht
  have hpb := boFunctor_pullback M hn hM hm t ht g hg hsurj hloc
  have h := maxOrder_controlledTransform_boLocal_lt M hn hM hm _ hloc
  rw [← markedTransform_boLocal_I M hn hM hm _ hloc, ← hpb] at h
  exact maxOrder_controlledTransform_lt_of_pullback t hm ht.2.2 _
    (boFunctor_isOrderMTripleSeq M hn hM hm t ht).1 g hg hsurj h

end MMP.Resolution
