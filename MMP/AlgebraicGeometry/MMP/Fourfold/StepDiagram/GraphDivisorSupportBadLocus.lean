module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorEffective
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.RingTheory.RegularLocalRing.CompletionStrictHenselization
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The support of the graph divisor of a threefold step diagram

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a threefold step diagram, `(G, u, v)` its normalized graph,
`g = f⁻ ∘ u = f⁺ ∘ v : G ⟶ Z`, and `H = u^* D⁻ - v^* D⁺` its graph divisor. Let `Σ ⊆ Z` be the
bad locus of the base, the complement of the largest open over which `f⁻` and `f⁺` are both
isomorphisms. Then `Supp H = g⁻¹(Σ)`.

Over `Z ∖ Σ` the map `v` is finite, proper and birational onto the normal `X⁺`, hence an
isomorphism, and `v_* H = 0` kills every coefficient of `H` there. Conversely the fibre of `g`
through a closed point of `g⁻¹(Σ)` is connected with at least two points, so it contains a proper
curve `C` through that point contracted by `g`; as `-H` is `g`-ample and `H ≥ 0`, `C` lies in
`Supp H`.

## Main results

* `MMP.Fourfold.IsThreefoldGraphDivisor.coe_supp_eq_preimage_badLocusBase`: `Supp H = g⁻¹(Σ)`.

## Implementation notes

The equality is one of subsets of `G`, with `g⁻¹(Σ)` the set-theoretic preimage of
`MMP.Fourfold.badLocusBase fm fp`. The auxiliary lemmas live in the namespace
`Proof_lem_mmp_indexc_graph_support`, opened only for the main result.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_mmp_indexc_graph_support

open Limits TopologicalSpace MMP.Mori MMP.Fourfold

/-- Over an open `W` on which `f₁` is an isomorphism, two points of `X₁ ×_S X₂` lying over
`f₁⁻¹ W` with the same image in `X₂` are equal: there the fibre product is an open subscheme of
`X₂`. -/
private theorem eq_of_snd_eq_of_isIso_morphismRestrict {X₁ X₂ S : Scheme.{0}} (f₁ : X₁ ⟶ S)
    (f₂ : X₂ ⟶ S) (W : S.Opens) [IsIso (f₁ ∣_ W)] {p q : ↑(pullback f₁ f₂)}
    (hp : pullback.fst f₁ f₂ p ∈ f₁ ⁻¹ᵁ W) (hq : pullback.fst f₁ f₂ q ∈ f₁ ⁻¹ᵁ W)
    (h : pullback.snd f₁ f₂ p = pullback.snd f₁ f₂ q) : p = q := by
  set j := (f₁ ⁻¹ᵁ W).ι ≫ f₁
  haveI : IsOpenImmersion j := by
    rw [show j = (f₁ ∣_ W) ≫ W.ι from (morphismRestrict_ι f₁ W).symm]
    infer_instance
  let m := pullback.map j f₂ f₁ f₂ (f₁ ⁻¹ᵁ W).ι (𝟙 _) (𝟙 _) (by simp [j]) (by simp)
  have hrange : ∀ r : ↑(pullback f₁ f₂), pullback.fst f₁ f₂ r ∈ f₁ ⁻¹ᵁ W → r ∈ Set.range m := by
    intro r hr
    rw [Scheme.Pullback.range_map]
    exact ⟨by rwa [Scheme.Opens.range_ι], ⟨pullback.snd f₁ f₂ r, rfl⟩⟩
  have hsnd : ∀ r', pullback.snd f₁ f₂ (m r') = pullback.snd j f₂ r' := fun r' => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Category.comp_id]
  obtain ⟨p', rfl⟩ := hrange p hp
  obtain ⟨q', rfl⟩ := hrange q hq
  rw [hsnd, hsnd] at h
  rw [(pullback.snd j f₂).isOpenEmbedding.injective h]

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_mem_biregularLocus {X Y : Scheme.{0}} (f : X ⟶ Y) {a b : X}
    (ha : f a ∈ biregularLocus f) (hab : f a = f b) : a = b := by
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let a' : (f ⁻¹ᵁ V).toScheme := ⟨a, ha⟩
  let b' : (f ⁻¹ᵁ V).toScheme := ⟨b, show f b ∈ V from hab ▸ ha⟩
  have hι : ∀ z : (f ⁻¹ᵁ V).toScheme, V.ι ((f ∣_ V) z) = f ((f ⁻¹ᵁ V).ι z) := fun z => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : (f ∣_ V) a' = (f ∣_ V) b' := V.ι.isOpenEmbedding.injective (by rwa [hι, hι])
  exact congrArg (f ⁻¹ᵁ V).ι ((f ∣_ V).isOpenEmbedding.injective h1)

/-- In a Noetherian quasi-sober space, a closed point `y` of a closed connected set `F` with
another point has a proper generization inside `F`. -/
private theorem exists_specializes_ne_of_isPreconnected {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {F : Set X} (hF : IsClosed F) (hFc : IsPreconnected F)
    {y : X} (hy : y ∈ F) (hyc : IsClosed ({y} : Set X)) {y' : X} (hy' : y' ∈ F) (hne : y' ≠ y) :
    ∃ η ∈ F, η ⤳ y ∧ η ≠ y := by
  by_contra! hcon
  obtain ⟨S, hSfin, hScl, hSirr, hFeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  set T := ⋃₀ {t ∈ S | y ∉ t}
  have hTcl : IsClosed T :=
    (hSfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hScl t ht.1
  have hyT : y ∉ T := fun ⟨_, ⟨_, hyt⟩, hy⟩ => hyt hy
  have hcover : F ⊆ {y} ∪ T := by
    intro p hp
    rw [hFeq] at hp
    obtain ⟨t, htS, hpt⟩ := hp
    by_cases hyt : y ∈ t
    · obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hSirr t htS) (hScl t htS)
      have hζy : ζ = y :=
        hcon ζ (hFeq ▸ Set.subset_sUnion_of_mem htS hζ.mem) (hζ.specializes hyt)
      rw [← hζ.def, hζy, hyc.closure_eq] at hpt
      exact Or.inl hpt
    · exact Or.inr ⟨t, ⟨htS, hyt⟩, hpt⟩
  have hdisj : F ∩ ({y} ∩ T) = ∅ := by
    rw [Set.singleton_inter_eq_empty.mpr hyT, Set.inter_empty]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hFc _ _ hyc hTcl hcover hdisj with h | h
  · exact hne (h hy')
  · exact hyT (h hy)

/-- If `u ≫ f₁ = v ≫ f₂` with `G ⟶ X₁ ×_S X₂` finite and `f₁` an isomorphism over `W`, then
the fibres of `v` through points of `(u ≫ f₁)⁻¹ W` are finite. -/
private theorem finite_preimage_singleton_of_isIso_morphismRestrict {X₁ X₂ S G : Scheme.{0}}
    {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {u : G ⟶ X₁} {v : G ⟶ X₂} (huv : u ≫ f₁ = v ≫ f₂)
    [IsFinite (pullback.lift u v huv)] (W : S.Opens) [IsIso (f₁ ∣_ W)] {x : G}
    (hx : f₁ (u x) ∈ W) : (v ⁻¹' {v x}).Finite := by
  set l := pullback.lift u v huv
  have hcomp : ∀ b : G, f₁ (u b) = f₂ (v b) := fun b => by
    rw [← Scheme.Hom.comp_apply, huv, Scheme.Hom.comp_apply]
  have hfst : ∀ b : G, f₁ (u b) ∈ W → pullback.fst f₁ f₂ (l b) ∈ f₁ ⁻¹ᵁ W := fun b hb => by
    rwa [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have hsnd : ∀ b : G, pullback.snd f₁ f₂ (l b) = v b := fun b => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  refine (l.finite_preimage_singleton (l x)).subset fun a (ha : v a = v x) => ?_
  exact eq_of_snd_eq_of_isIso_morphismRestrict f₁ f₂ W
    (hfst a (by rwa [hcomp, ha, ← hcomp])) (hfst x hx) (by rw [hsnd, hsnd, ha])

/-- If `g = w ≫ f'` with `w` surjective and the fibre of `f'` over `g y` positive-dimensional, the
fibre of `g` through `y` has a second point. -/
private theorem exists_ne_of_topologicalKrullDim_fibre_pos {G X' Z : Scheme.{0}} {w : G ⟶ X'}
    {f' : X' ⟶ Z} {g : G ⟶ Z} (hw : Function.Surjective w) (hg : w ≫ f' = g) {y : G}
    (hpos : 0 < topologicalKrullDim (f' ⁻¹' {g y})) : ∃ y' ∈ g ⁻¹' {g y}, y' ≠ y := by
  subst hg
  have hnt : Nontrivial (f' ⁻¹' {(w ≫ f') y}) := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    haveI : DiscreteTopology (f' ⁻¹' {(w ≫ f') y}) := Subsingleton.discreteTopology
    exact (topologicalKrullDim_zero_of_discreteTopology _).not_gt hpos
  obtain ⟨⟨b, hb⟩, hne⟩ := exists_ne (α := f' ⁻¹' {(w ≫ f') y}) ⟨w y, by simp⟩
  obtain ⟨b', rfl⟩ := hw b
  exact ⟨b', hb, fun h => hne (Subtype.ext (congrArg w h))⟩

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

/-- `Supp H ⊆ g⁻¹(Σ)`: over `Z ∖ Σ` the map `v` is an isomorphism, so a prime of `G` whose image
meets `Z ∖ Σ` is the strict transform of a prime of `X⁺`, and `v_* H = 0` kills its coefficient. -/
private theorem supp_subset_preimage_badLocusBase
    (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) :
    (H.supp : Set G) ⊆ (u ≫ fm) ⁻¹' (badLocusBase fm fp : Set Z) := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  haveI := hD.isNormalVariety_plus.1
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsFinite (pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsProper v := pullback.lift_snd u v hG.comp_eq ▸ inferInstance
  haveI : IsSeparated (Xp ↘ terminal Scheme) := by
    rw [show (Xp ↘ terminal Scheme) = sXp ≫ (Spec (.of ℂ) ↘ terminal Scheme) from
      terminal.hom_ext _ _]
    infer_instance
  intro x hx
  rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff] at hx
  obtain ⟨E, hE, hxE⟩ := hx
  rw [Set.mem_preimage, coe_badLocusBase, Set.mem_compl_iff]
  intro hxU
  set U := commonBiregularLocus fm fp
  haveI : IsIso (fm ∣_ U) := isBiregular_commonBiregularLocus_left fm fp
  have hηx : E.genericPoint ⤳ x := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hyV : v E.genericPoint ∈ biregularLocus v := by
    obtain ⟨hO, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso v
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
        hG.isBirationalMorphism_plus)).1 inferInstance
    exact le_biregularLocus (V := ⟨_, hO⟩) hiso
      (finite_preimage_singleton_of_isIso_morphismRestrict hG.comp_eq U
        ((hηx.map (u ≫ fm).continuous).mem_open U.isOpen hxU))
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (v E.genericPoint)
    ((MMP.Positivity.coheight_map_of_mem_biregularLocus v hyV).trans E.coheight_genericPoint)
  have hvE : v E.genericPoint = P.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have h0 := congrArg (fun D : QDivisor Xp => D P) h.transformDivisor_eq_zero.1
  simp only [Finsupp.zero_apply] at h0
  rw [RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff v E P).mpr hvE)] at h0
  · exact hE (by rwa [DivisorWithCoeffs.coeff_apply])
  · intro E' hE'
    have hvE' := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff v E' P).mp hE'
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_mem_biregularLocus v (hvE'.trans hvE.symm ▸ hyV) (hvE'.trans hvE.symm))

/-- Every proper curve of `G` contracted by `g` lies in `Supp H`: off `Supp H` one has `H · C ≥ 0`
as `H ≥ 0`, whereas `H · C < 0` as `-H` is `g`-ample. -/
private theorem point_mem_supp_of_isContractedBy
    (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) {sG : G ⟶ Spec (.of ℂ)}
    [QuasiCompact sG] [CompactSpace G] (C : ProperCurve sG) (hC : C.IsContractedBy (u ≫ fm)) :
    C.point ∈ H.supp := by
  by_contra hCS
  obtain ⟨m, hm, L, hLc, hL, hamp⟩ := h.hasRelativelyAmpleMultiple_neg
  have hHq : H.IsQCartier :=
    ⟨-(m : ℤ), by simpa using hm.ne', L, by rw [hL, smul_neg, neg_smul], hLc⟩
  have hHnq : (-H).IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hL, hLc⟩
  have hnn := (intersectionNumber_nonneg_and_eq_zero_iff (k := ℂ) sG H hHq h.nonneg C hCS).1
  have hpos : 0 < (-H).intersectionNumber ℂ sG C.ι C.dim_le hHnq := by
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sG C.ι C.dim_le (-H) hHnq hm L hLc hL]
    haveI := hLc.isInvertibleModule_divisorialSheaf
    have := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      (u ≫ fm) _ hamp C hC
    exact div_pos (Int.cast_pos.mpr this) (Nat.cast_pos.mpr hm)
  have hq1 : ((-1 : ℚ) • H).IsQCartier := by rwa [neg_one_smul]
  have hneg := intersectionNumber_smul sG C.ι C.dim_le H hHq (-1) hq1
  rw [← intersectionNumber_congr sG C.ι C.dim_le hHnq hq1 (neg_one_smul ℚ H).symm] at hneg
  linarith

/-- `g⁻¹(Σ) ⊆ Supp H`: through a closed point `y ∈ g⁻¹(Σ)` the fibre of `g` is connected with a
second point, so it carries a proper curve through `y`, which lies in `Supp H` by
`point_mem_supp_of_isContractedBy`; closed points are dense in `g⁻¹(Σ)`. -/
private theorem preimage_badLocusBase_subset_supp
    (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) :
    (u ≫ fm) ⁻¹' (badLocusBase fm fp : Set Z) ⊆ (H.supp : Set G) := by
  have hD := h.isThreefoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI := hZ.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hD.isNormalVariety_plus.1
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_plus
  haveI : IsProper sXp :=
    isProper_of_isProjectiveMorphism _ hD.isProjectiveVariety_plus.isProjective
  haveI : IsFinite (pullback.lift u v hG.comp_eq) := hG.isFinite
  haveI : IsProper v := pullback.lift_snd u v hG.comp_eq ▸ inferInstance
  haveI : IsProper u := pullback.lift_fst u v hG.comp_eq ▸ inferInstance
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  set sG := v ≫ sXp
  set g := u ≫ fm
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace sG
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  haveI : IsNoetherian G := {}
  rw [← closure_inter_closedPoints ((badLocusBase fm fp).isClosed.preimage g.continuous)]
  refine closure_minimal ?_ H.supp.isClosed
  rintro y ⟨hyB, hyc⟩
  rw [mem_closedPoints_iff] at hyc
  have hz : IsClosed ({g y} : Set Z) := by simpa [Set.image_singleton] using g.isClosedMap _ hyc
  set F := g ⁻¹' {g y}
  have hFcl : IsClosed F := hz.preimage g.continuous
  obtain ⟨y', hy'F, hne⟩ : ∃ y' ∈ F, y' ≠ y := by
    rcases hD.pos_dim_fibre_of_mem_badLocusBase hz hyB with hp | hp
    · exact exists_ne_of_topologicalKrullDim_fibre_pos u.surjective rfl hp
    · exact exists_ne_of_topologicalKrullDim_fibre_pos v.surjective hG.comp_eq.symm hp
  have hb : IsBirationalMorphism g :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm u
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hD.isBirationalMorphism_minus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
  have hconn : _root_.IsConnected F :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sG sZ ⟨⟩ hZ g
      hb).2 (g y)
  obtain ⟨η, hηF, hηy, hηne⟩ :=
    exists_specializes_ne_of_isPreconnected hFcl hconn.isPreconnected rfl hyc hy'F hne
  obtain ⟨c, hηc, hcy, -, hcurve⟩ := exists_isProperCurve_of_specializes sG hηy hyc hyc rfl hηne
  have hcF : c ∈ F := hηc.mem_closed hFcl hηF
  exact hcy.mem_closed H.supp.isClosed (point_mem_supp_of_isContractedBy h ⟨c, hcurve⟩
    fun x hx => ((specializes_iff_mem_closure.mpr hx).mem_closed hFcl hcF).trans hcF.symm)

end Proof_lem_mmp_indexc_graph_support

namespace MMP.Fourfold

open Proof_lem_mmp_indexc_graph_support

open MMP.Mori

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- **Support of the graph divisor.** For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with
normalized graph `(G, u, v)` and graph divisor `H`, the support of `H` is the preimage
`g⁻¹(Σ)` of the bad locus `Σ = MMP.Fourfold.badLocusBase fm fp` under `g = u ≫ fm`. -/
@[mmp "lem_mmp_indexc_graph_support"]
theorem IsThreefoldGraphDivisor.coe_supp_eq_preimage_badLocusBase
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H) :
    (H.supp : Set G) = (u ≫ fm) ⁻¹' (badLocusBase fm fp : Set Z) :=
  (supp_subset_preimage_badLocusBase h).antisymm (preimage_badLocusBase_subset_supp h)

end MMP.Fourfold

end
