module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.SurfaceMldFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.LowDiscrepancySetStabilizes
import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Bad surfaces of small mld along a stabilized small klt tail

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfold step
diagrams, with bad loci `W_i⁻ ⊆ X_i` and `W_i⁺ ⊆ X_{i+1}`. On each side, only finitely many
indices `i` carry an irreducible surface `V ⊆ W_i^±` whose generic minimal log discrepancy
`mld_{η_V}(X_i^±, B_i^±)` is at most one. Consequently there is an index `i₁` beyond which every
irreducible surface in a bad locus has generic mld greater than one.

At such an index the generic mld is attained by a divisor centred at `V`: the log discrepancies
of `(X_i, B_i)` are positive and lie in `(1/m) ℤ` for a Cartier index `m` of `K_i + B_i`. The
attaining place is exceptional with log discrepancy at most one, so it is the transport `s_i` of
a stable place `s ∈ I_∞`, and its log discrepancy lies in the fixed finite set `F` of
`exists_finset_minimalLogDiscrepancy`. For a stable place `s`, the log discrepancies
`b_k = a_k(s_k)` are nondecreasing in `k`, and `b_k < b_{k+1}` whenever the centre of `s_k` lies in
`W_k⁻` or the centre of `s_{k+1}` lies in `W_k⁺`. So a pair `(s, x) ∈ I_∞ × F` is selected at no
more than one bad index, and there are only finitely many such pairs.

The comparison `b_{k+1} - b_k = ξ(H) ≥ 0` is computed on the normalized graph `(G, u, v)` of the
`k`-th step diagram with graph divisor `H`. The graph is the normalization of the reduced closure
of the point of `X_k ×_{Z_k} X_{k+1}` over the two generic points. `H ≥ 0` comes from the
negativity lemma, because `-H` is `v`-nef and `v_* H = 0`. The comparison itself is proved on a
realization of `ξ` over `G`. Its strictness comes from `g⁻¹(Σ_k) ⊆ Supp H` for `g = f_k ∘ u`.
For a closed point `z ∈ Σ_k`, the negativity lemma makes the fibre `g⁻¹(z)` either contained in
`Supp H` or disjoint from it. In the second case the fibre contains no proper curve, because `H`
would have degree zero on it while `-H` is `g`-ample. The fibres of `f_k` and `f_k⁺` over `z`
would then be finite, which is impossible over `Σ_k`. Finally, the pull-back of the effective
`ℚ`-Cartier `H` has positive coefficient along every divisor whose centre lies in `Supp H`.

## Main results

* `IsStabilizedSmallKltTail.finite_setOf_exists_surface_subset_badLocus`:
  on each side, the indices carrying a bad surface of generic mld at most one form a finite set.
* `IsStabilizedSmallKltTail.exists_forall_ge_one_lt_minimalLogDiscrepancy`:
  eventually every bad surface has generic mld greater than one.

## Implementation notes

The two sides `σ = -` and `σ = +` are stated together, as a conjunction. On the negative side the
pair is `(X_i, B_i)` and the bad locus `W_i⁻`; on the positive side the pair is
`(X_{i+1}, B_{i+1})` and the bad locus `W_i⁺`. An irreducible surface is an irreducible closed
subset of dimension two, and its generic mld is `MMP.Fourfold.minimalLogDiscrepancy` at its
generic point.

The supporting results (the negativity lemma over an arbitrary field, the graph divisor of a step
diagram and the discrepancy comparison across it) are private to this file and live in
`MMP.Fourfold.BadSurfaces`.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39
-/

@[expose] public section

namespace MMP.Fourfold.BadSurfaces

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-! ### Residue fields and stalks at generic points -/

section Residue

/-- The residue map of a point whose local ring is a field is bijective. -/
private theorem residue_bijective_of_isField {X : Scheme.{0}} (x : X)
    (hx : IsField (X.presheaf.stalk x)) : Function.Bijective (X.residue x) := by
  letI := hx.toField
  exact ⟨(X.residue x).hom.injective, IsLocalRing.residue_surjective⟩

/-- The local ring of an integral scheme at its generic point is a field. -/
private theorem isField_stalk_of_eq_genericPoint {X : Scheme.{0}} [IsIntegral X] {x : X}
    (hx : x = genericPoint X) : IsField (X.presheaf.stalk x) := by
  subst hx
  exact Field.toIsField X.functionField

/-- A morphism of integral schemes sending generic point to generic point and inducing an
isomorphism of residue fields there is an isomorphism on local rings there. -/
private theorem isIso_stalkMap_of_isIso_residueFieldMap {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    [IsIso (f.residueFieldMap (genericPoint X))] : IsIso (f.stalkMap (genericPoint X)) := by
  have h1 := residue_bijective_of_isField (genericPoint X) (isField_stalk_of_eq_genericPoint rfl)
  have h2 := residue_bijective_of_isField (f (genericPoint X))
    (isField_stalk_of_eq_genericPoint hf)
  have h3 : Function.Bijective (f.residueFieldMap (genericPoint X)) :=
    ConcreteCategory.bijective_of_isIso _
  have hc := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (Scheme.residue_residueFieldMap f (genericPoint X))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hc
  have hb : Function.Bijective ((X.residue (genericPoint X)) ∘
      (f.stalkMap (genericPoint X))) := by
    rw [← hc]; exact h3.comp h2
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b hab => hb.1 (by simp [hab]), fun c => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (X.residue _ c)
  exact ⟨a, h1.1 ha⟩

/-- A morphism of integral schemes sending generic point to generic point and inducing an
isomorphism of residue fields there is birational. -/
private theorem isBirational_of_isIso_residueFieldMap_genericPoint {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : f (genericPoint X) = genericPoint Y)
    [IsIso (f.residueFieldMap (genericPoint X))] : IsBirational f := by
  haveI := isIso_stalkMap_of_isIso_residueFieldMap f hf
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ?_ fun x hx => ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
    exact hf
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    infer_instance

/-- A birational morphism of integral schemes induces an isomorphism of residue fields at the
generic point. -/
private theorem isIso_residueFieldMap_genericPoint {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {f : X ⟶ Y} (hf : IsBirational f) :
    IsIso (f.residueFieldMap (genericPoint X)) := by
  haveI := hf.isIso_stalkMap (genericPoint X) (by rw [genericPoints_eq_singleton]; rfl)
  exact isIso_residueFieldMap_of_isIso_stalkMap _ _

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- If the residue field map of `g` at `T.y` is an isomorphism, then so is the canonical map
`κ(T.x) ⟶ κ(T.x) ⊗_{κ(T.s)} κ(T.y)`, being a pushout of an isomorphism. -/
private theorem isIso_tensorInl {X Z S : Scheme.{0}} {f : X ⟶ S} {g : Z ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (hres : IsIso (g.residueFieldMap T.y)) :
    IsIso T.tensorInl := by
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  change IsIso (pushout.inl ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  infer_instance

/-- At a point `w` of `X ×_S Z` over `x` and `z`, if the residue field map of `g : Z ⟶ S` at `z`
is an isomorphism then so is that of the first projection at `w`
([Stacks, Tag 01JT]). -/
private theorem isIso_residueFieldMap_fst {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    (z : Z) [hres : IsIso (g.residueFieldMap z)] (w : ↥(pullback f g))
    (hw₂ : pullback.snd f g w = z) : IsIso ((pullback.fst f g).residueFieldMap w) := by
  subst hw₂
  have hinl := isIso_tensorInl (Scheme.Pullback.Triplet.ofPoint w) hres
  obtain ⟨ι, -, hι⟩ := hinl.out
  have hfac : (Scheme.Pullback.Triplet.ofPoint w).tensorInl ≫ Scheme.Pullback.ofPointTensor w =
      (pullback.fst f g).residueFieldMap w :=
    pushout.inl_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint w)
  have htri : Spec.map ((Scheme.Pullback.Triplet.ofPoint w).tensorInl ≫
      Scheme.Pullback.ofPointTensor w) ≫
      Spec.map ι ≫ (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo =
      (pullback f g).fromSpecResidueField w := by
    rw [Spec.map_comp, Category.assoc,
      ← Category.assoc (Spec.map (Scheme.Pullback.Triplet.ofPoint w).tensorInl), ← Spec.map_comp,
      hι, Spec.map_id, Category.id_comp, Scheme.Pullback.ofPointTensor_SpecTensorTo]
  have key : ∀ {K : Type} [Field K] (ψ : CommRingCat.of K ⟶ (pullback f g).residueField w)
      (a : Spec (CommRingCat.of K) ⟶ pullback f g),
      Spec.map ψ ≫ a = (pullback f g).fromSpecResidueField w → IsIso ψ := by
    intro K _ ψ a h
    obtain ⟨⟨y, k⟩, rfl⟩ := (Scheme.SpecToEquivOfField K (pullback f g)).symm.surjective a
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h
    have hy : y = w := by
      have h₁ : (pullback f g).fromSpecResidueField y (Spec.map k (Spec.map ψ default)) =
          (pullback f g).fromSpecResidueField w default :=
        congrArg (fun m : Spec ((pullback f g).residueField w) ⟶ pullback f g ↦ m default) h
      simpa using h₁
    subst y
    have : Mono ψ := ConcreteCategory.mono_of_injective ψ ψ.hom.injective
    have : IsSplitEpi ψ := ⟨⟨k, by
      simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
        ← cancel_mono ((pullback f g).fromSpecResidueField w), Category.assoc,
        Category.id_comp] using h⟩⟩
    exact isIso_of_mono_of_isSplitEpi ψ
  exact key _ _ (.trans (congrArg
    (fun u ↦ Spec.map u ≫ Spec.map ι ≫ (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo)
    hfac.symm) htri)

/-- Residue field maps that are isomorphisms compose. -/
private theorem isIso_residueFieldMap_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [IsIso (f.residueFieldMap x)] [IsIso (g.residueFieldMap (f x))] :
    IsIso ((f ≫ g).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›

/-- At a point `w` of `X ×_S Z` over `x` and `z`, if the residue field map of `f : X ⟶ S` at `x`
is an isomorphism then so is that of the second projection at `w`. -/
private theorem isIso_residueFieldMap_snd {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    (x : X) [IsIso (f.residueFieldMap x)] (w : ↥(pullback f g))
    (hw₁ : pullback.fst f g w = x) : IsIso ((pullback.snd f g).residueFieldMap w) := by
  haveI := isIso_residueFieldMap_fst g f x ((pullbackSymmetry f g).hom w)
    (by rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_snd, hw₁])
  rw [← pullbackSymmetry_hom_comp_fst]
  exact isIso_residueFieldMap_comp _ _ w

/-- A morphism surjective on stalks induces isomorphisms of residue fields. -/
private theorem isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, fun c => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have hc := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _))
    (Scheme.residue_residueFieldMap f x)
  exact congrFun hc b

end Residue

/-! ### The normalized graph and the graph divisor -/

section Graph

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- **A step diagram has a graph divisor**: the normalization `G` of the closure `Γ ⊆ X⁻ ×_Z X⁺`
of the point over the two generic points, with its two projections `u`, `v`, is a normalized
graph, and the pull-backs of the `ℚ`-Cartier divisors `D^±` to `G` exist. -/
private theorem exists_isGraphDivisor {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) :
    ∃ (G : Scheme.{0}) (_ : IsLocallyNoetherian G) (_ : IsNormal G) (u : G ⟶ Xm) (v : G ⟶ Xp)
      (H : QDivisor G), IsGraphDivisor sXm sZ sXp K B fm fp u v H := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sXm := h.isNormalVariety_minus.1.toLocallyOfFiniteType
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  have hbm' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbm
  have hbp' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbp
  have hηm : fm (genericPoint Xm) = genericPoint Z := map_genericPoint_of_isDominant fm
  have hηp : fp (genericPoint Xp) = genericPoint Z := map_genericPoint_of_isDominant fp
  -- the generic point `t` of the graph
  obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := fm) (g := fp)
    (genericPoint Xm) (genericPoint Xp) (hηm.trans hηp.symm)
  set Γ := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({t} : Set ↥(pullback fm fp))))
  haveI : IsIntegral Γ.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  set ι := Γ.subschemeι
  have hιγ : ι (genericPoint Γ.subscheme) = t := by
    have h1 := (genericPoint_spec Γ.subscheme).image ι.continuous
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
    have h2 : IsGenericPoint t (closure (closure ({t} : Set ↥(pullback fm fp)))) := by
      rw [closure_closure]; exact isGenericPoint_closure
    exact h1.eq h2
  set γ := genericPoint Γ.subscheme
  have hΓfin : ∀ U : Γ.subscheme.Opens, IsCompact (U : Set Γ.subscheme) →
      (irreducibleComponents (U : Set Γ.subscheme)).Finite :=
    fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U
  set G := Γ.subscheme.normalizationScheme hΓfin
  set ν := Γ.subscheme.normalization hΓfin
  haveI : IsFinite ν := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field ℂ (ι ≫ pullback.fst fm fp ≫ sXm)) hΓfin
  haveI : IsIntegral G := Scheme.isIntegral_normalizationScheme _ _
  haveI : IsNormal G := Scheme.isNormal_normalizationScheme _ _
  have hν : IsBirational ν := Scheme.isBirational_normalization _ _
  -- residue fields at the generic point of the graph
  haveI := isIso_residueFieldMap_genericPoint hbm'
  haveI := isIso_residueFieldMap_genericPoint hbp'
  haveI := isIso_residueFieldMap_of_surjectiveOnStalks ι γ
  have hgen1 : (ι ≫ pullback.fst fm fp) γ = genericPoint Xm := by
    rw [Scheme.Hom.comp_apply, hιγ, ht₁]
  have hgen2 : (ι ≫ pullback.snd fm fp) γ = genericPoint Xp := by
    rw [Scheme.Hom.comp_apply, hιγ, ht₂]
  haveI := isIso_residueFieldMap_fst fm fp _ (ι γ) (by rw [hιγ, ht₂])
  haveI := isIso_residueFieldMap_snd fm fp _ (ι γ) (by rw [hιγ, ht₁])
  haveI := isIso_residueFieldMap_comp ι (pullback.fst fm fp) γ
  haveI := isIso_residueFieldMap_comp ι (pullback.snd fm fp) γ
  have hb1 := isBirational_of_isIso_residueFieldMap_genericPoint _ hgen1
  have hb2 := isBirational_of_isIso_residueFieldMap_genericPoint _ hgen2
  set u : G ⟶ Xm := ν ≫ ι ≫ pullback.fst fm fp with hudef
  set v : G ⟶ Xp := ν ≫ ι ≫ pullback.snd fm fp with hvdef
  haveI : IsProper u := by rw [hudef]; infer_instance
  haveI : IsProper v := by rw [hvdef]; infer_instance
  haveI : LocallyOfFiniteType (u ≫ sXm) := by rw [hudef]; infer_instance
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (u ≫ sXm)
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace u
  have hbu : IsBirationalMorphism u := isBirationalMorphism_of_isBirational u (hν.comp hb1)
  have hbv : IsBirationalMorphism v := isBirationalMorphism_of_isBirational v (hν.comp hb2)
  have hcomp : u ≫ fm = v ≫ fp := by
    simp only [hudef, hvdef, Category.assoc, pullback.condition]
  have hlift : pullback.lift u v hcomp = ν ≫ ι := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  have hG : IsNormalizedGraph fm fp u v :=
    { isIntegral := inferInstance, isNormal := inferInstance, comp_eq := hcomp,
      isFinite := by rw [hlift]; infer_instance, isBirationalMorphism_minus := hbu,
      isBirationalMorphism_plus := hbv }
  haveI := hbu.isDominant
  haveI := hbv.isDominant
  have hm := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' u
    (Divisor.toQDivisor K + B)
  have hp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' v
    (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B)
  exact ⟨G, inferInstance, inferInstance, u, v, _, h, hG, _, _, hm, hp,
    QDivisor.isPullback_pullback h.isQCartier_minus hm,
    QDivisor.isPullback_pullback h.isQCartier_plus hp, rfl⟩

end Graph

/-! ### Function fields -/

/-- Pulling back rational functions along a composite of dominant morphisms of integral schemes
is the composite of the pull-backs. -/
private theorem functionFieldMap_comp_apply {X Y W : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral W] (f : X ⟶ Y) (g : Y ⟶ W) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)]
    (a : W.functionField) :
    functionFieldMap (f ≫ g) a = functionFieldMap f (functionFieldMap g a) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (f ≫ g)) =
      CommRingCat.ofHom ((functionFieldMap f).comp (functionFieldMap g)) from
    congrArg (fun φ : W.functionField ⟶ X.functionField ↦ φ.hom a) h
  apply Spec.map_injective
  apply (cancel_mono (W.fromSpecStalk (genericPoint W))).mp
  rw [functionFieldMap_fromSpecStalk (f ≫ g)]
  have hof : CommRingCat.ofHom ((functionFieldMap f).comp (functionFieldMap g)) =
      CommRingCat.ofHom (functionFieldMap g) ≫ CommRingCat.ofHom (functionFieldMap f) := rfl
  rw [hof, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk g,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap f))),
    functionFieldMap_fromSpecStalk f]
  exact (Category.assoc _ _ _).symm

section

/-!
### Exceptional coefficients in a relative numerical equivalence are nonnegative

Let `f : Y ⟶ X` be a proper birational morphism of normal varieties over a field `k`, `L` an
`ℝ`-Cartier divisor on `X`, `M` an `f`-nef `ℝ`-Cartier divisor on `Y` and `B` an `ℝ`-Cartier
divisor on `Y` whose coefficients along the prime divisors not exceptional over `X` are
nonnegative. If `f^*L ≡_f M + B`, then `B` is effective.

Since `f^*L · C = 0` for every curve `C` contracted by `f`, the divisor `-B` is `f`-nef. By the
Chow lemma there is a projective birational morphism `h : Y' ⟶ Y` from a normal variety with
`f' = h ≫ f` projective. The pull-back `B' = h^*B` has `-B'` `f'`-nef, by the projection formula
`h^*N · C' = N · h_*C'`, and `f'_*B'` is effective, since the coefficient of `B'` along the strict
transform of a prime divisor `P` of `Y` is that of `P` in `B`. The negativity lemma, in the form of
Kollár's argument over an affine open of `X` (an effective Cartier divisor `W` with `-W` relatively
ample and the largest `t` with `B'|_V + tW` effective), gives `B' ≥ 0`, hence `B ≥ 0`.

References:

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19, 2.19.1
* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 2.9
-/

open MMP.Flips

universe u

namespace NegativityCoefficients

section Helpers

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
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
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

/-- An effective `ℝ`-divisor `D = ∑ s_j M_j + t N`, presented by Cartier divisors, has `D · C ≥ 0`
on every proper curve `C` not contained in `Supp D`. -/
private theorem sum_degreeOn_add_nonneg (hX : IsNormalVariety k sX) (C : ProperCurve sX) {n : ℕ}
    (s : Fin n → ℝ) (M : Fin n → Divisor X) (hM : ∀ j, (M j).IsCartier) (t : ℝ) (N : Divisor X)
    (hN : N.IsCartier)
    (hD : (∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N).IsEffective)
    (hC : C.point ∉ (∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N).supp) :
    0 ≤ ∑ j, s j * ((M j).degreeOn k sX C.ι C.dim_le (hM j) : ℝ) +
      t * (N.degreeOn k sX C.ι C.dim_le hN : ℝ) := by
  let s' : Fin (n + 1) → ℝ := Fin.snoc s t
  let M' : Fin (n + 1) → Divisor X := Fin.snoc M N
  have hM' : ∀ j, (M' j).IsCartier :=
    Fin.lastCases (by simpa [M'] using hN) fun j => by simpa [M'] using hM j
  have hDM : ∑ j, s j • Divisor.toRDivisor (M j) + t • Divisor.toRDivisor N =
      ∑ j, s' j • Divisor.toRDivisor (M' j) := by
    simp [Fin.sum_univ_castSucc, s', M']
  rw [hDM] at hD hC
  have h := IsRIntersectionNumber.nonneg_of_isEffective k sX hX _ ⟨_, s', M', hM', rfl⟩ hD C hC s'
    M' (isRIntersectionNumber_sum_degreeOn k sX C s' M' hM')
  simpa [Fin.sum_univ_castSucc, s', M'] using h

end Intersection

/-- The fibre of `f` over a closed point is connected and proper, so if it meets a closed set `S`
without lying in it, it contains a proper curve contracted by `f` that meets `S` without lying
in it. -/
private theorem exists_properCurve_isContractedBy (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (x : X) (hx : IsClosed ({x} : Set X)) {S : Set Y} (hS : IsClosed S)
    (hmeet : (f.base ⁻¹' {x} ∩ S).Nonempty) (hsub : ¬ f.base ⁻¹' {x} ⊆ S) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ ¬ Set.range C.ι ⊆ S ∧
      (Set.range C.ι ∩ S).Nonempty := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    sY sX hY.1 hX f hfb).2 x
  have hFcl : IsClosed (f.base ⁻¹' {x}) := hx.preimage f.continuous
  have key : ∀ {F S : Set Y}, IsClosed F → _root_.IsConnected F → IsClosed S →
      (F ∩ S).Nonempty → ¬ F ⊆ S → ∃ η ∈ F, η ∉ S ∧ ∃ s ∈ S, η ⤳ s := by
    intro F S hF hFc hS hmeet hsub
    set T := F \ S
    have hTF : closure T ⊆ F := closure_minimal Set.diff_subset hF
    by_cases hdis : (closure T ∩ S).Nonempty
    · obtain ⟨s, hsT, hsS⟩ := hdis
      obtain ⟨Z, hZfin, hZcl, hZirr, hZeq⟩ :=
        TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
          (isClosed_closure : IsClosed (closure T))
      have hsub' : closure T ⊆ ⋃₀ {t ∈ Z | (t ∩ T).Nonempty} := by
        refine closure_minimal (fun y hy => ?_) ?_
        · have : y ∈ ⋃₀ Z := hZeq ▸ subset_closure hy
          obtain ⟨z, hz, hyz⟩ := this
          exact ⟨z, ⟨hz, y, hyz, hy⟩, hyz⟩
        · exact (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
      obtain ⟨z, ⟨hzZ, t, htz, htT⟩, hsz⟩ := hsub' hsT
      obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hZirr z hzZ) (hZcl z hzZ)
      have hzT : z ⊆ closure T := hZeq ▸ Set.subset_sUnion_of_mem hzZ
      exact ⟨ζ, hTF (hzT hζ.mem), fun hζS => htT.2 ((hζ.specializes htz).mem_closed hS hζS),
        s, hsS, hζ.specializes hsz⟩
    · obtain ⟨y, hyF, hyS⟩ := Set.not_subset.mp hsub
      obtain ⟨w, -, hwT, hwS⟩ := isPreconnected_closed_iff.mp hFc.isPreconnected _ _
        isClosed_closure hS (fun a ha => by
          by_cases haS : a ∈ S
          · exact Or.inr haS
          · exact Or.inl (subset_closure (show a ∈ T from ⟨ha, haS⟩)))
        ⟨y, hyF, subset_closure (show y ∈ T from ⟨hyF, hyS⟩)⟩ hmeet
      exact (hdis ⟨w, hwT, hwS⟩).elim
  obtain ⟨η, hηF, hηS, s, hsS, hηs⟩ := key hFcl hconn hS hmeet hsub
  obtain ⟨p, hps, hpc⟩ := nonempty_inter_closedPoints
    ⟨s, (show s ∈ closure {s} from subset_closure rfl)⟩ isClosed_closure.isLocallyClosed
  have hηp : η ⤳ p := hηs.trans (specializes_iff_mem_closure.mpr hps)
  have hpS : p ∈ S := (specializes_iff_mem_closure.mpr hps).mem_closed hS hsS
  have hpF : p ∈ f.base ⁻¹' {x} := hηp.mem_closed hFcl hηF
  -- the scheme-theoretic fibre, proper over `k`
  let ι := f.fiberι x
  let sF := ι ≫ sY
  haveI : IsProper sF := by
    have h : sF = f.fiberToSpecResidueField x ≫ (X.fromSpecResidueField x ≫ sX) := by
      simp only [sF, ι, ← hf, Scheme.Hom.fiber_fac_assoc]
    rw [h]
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
    haveI : LocallyOfFiniteType (X.fromSpecResidueField x) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp hx
    haveI : IsFinite (X.fromSpecResidueField x ≫ sX) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    haveI : IsProper (f.fiberToSpecResidueField x) :=
      inferInstanceAs (IsProper (Limits.pullback.snd f (X.fromSpecResidueField x)))
    haveI : IsProper (X.fromSpecResidueField x ≫ sX) := inferInstance
    infer_instance
  haveI : IsLocallyNoetherian (f.fiber x) := LocallyOfFiniteType.isLocallyNoetherian sF
  have hrι : Set.range ι = f.base ⁻¹' {x} := f.range_fiberι x
  obtain ⟨η', hη'⟩ : η ∈ Set.range ι := hrι ▸ hηF
  obtain ⟨p', hp'⟩ : p ∈ Set.range ι := hrι ▸ hpF
  have hemb : Topology.IsEmbedding ι := ι.isEmbedding
  have hη'p' : η' ⤳ p' := by
    rwa [← hemb.isInducing.specializes_iff, hη', hp']
  have hp'c : IsClosed ({p'} : Set (f.fiber x)) := by
    rw [show ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} by ext; simp [← hp', hemb.injective.eq_iff]]
    exact (mem_closedPoints_iff.mp hpc).preimage ι.continuous
  obtain ⟨y', -, hy'p', hy'S, hy'⟩ := MMP.Fourfold.exists_isProperCurve_of_specializes sF hη'p'
    hp'c (hS.preimage ι.continuous) (by simpa [hp'] using hpS)
    (by simpa [hη'] using hηS)
  let C' : MMP.Mori.ProperCurve sF := ⟨y', hy'⟩
  -- its image in `Y` is a proper curve of `Y`
  have hφsY : (C'.ι ≫ ι) ≫ sY = C'.ι ≫ sF := Category.assoc _ _ _
  haveI : AlgebraicGeometry.IsCurve k ((C'.ι ≫ ι) ≫ sY) := hφsY ▸ C'.isCurve
  haveI : IsProper ((C'.ι ≫ ι) ≫ sY) := by rw [hφsY]; infer_instance
  have hrange : Set.range (C'.ι ≫ ι) = closure {ι y'} := C'.range_comp ι rfl
  have hinj : Function.Injective (C'.ι ≫ ι) := fun a b h =>
    C'.ι.isEmbedding.injective (hemb.injective (by simpa using h))
  have hnc : ¬ ∃ z, Set.range (C'.ι ≫ ι) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C'.scheme := ⟨fun a b => hinj (by
      have ha : (C'.ι ≫ ι) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C'.ι ≫ ι) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C'.scheme
    rw [C'.dim_eq] at h0
    exact absurd h0 (by decide)
  have hcurve := MMP.Mori.isCurve_imageι_comp sY (C'.ι ≫ ι) hnc
  have hker := C'.ker_comp ι
  have hdim : topologicalKrullDim (curveSubschemeAt (ι y')) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim (C'.ι ≫ ι).ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (ι y') ≫ sY) := by
    have h1 : IsProper ((C'.ι ≫ ι).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C'.ι ≫ ι).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  let C : MMP.Mori.ProperCurve sY := ⟨ι y', ⟨hdim, hprop⟩⟩
  have hrC : Set.range C.ι = closure {ι y'} := C.range_ι
  have hclF : closure {ι y'} ⊆ f.base ⁻¹' {x} := by
    rw [← hrange, ← hrι]
    rintro _ ⟨w, rfl⟩
    exact ⟨C'.ι w, by simp⟩
  have hCf : C.IsContractedBy f := fun _ hz => (hclF hz).trans (hclF (subset_closure rfl)).symm
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [hrC]
    intro h
    exact hy'S (h (subset_closure rfl))
  · refine ⟨p, ?_, hpS⟩
    rw [hrC, ← hp']
    exact specializes_iff_mem_closure.mp (hy'p'.map ι.continuous)

/-- **A contracted curve through a point with positive-dimensional fibre.** If `f : Y ⟶ X` is a
proper birational morphism of normal varieties and `z` a closed point of `Y` mapped outside the
biregular locus of `f`, then some proper curve contracted by `f` passes through `z`. -/
private theorem exists_properCurve_specializes (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsNormal X] (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    (z : Y) (hz : IsClosed ({z} : Set Y)) (hzf : f z ∉ biregularLocus f) :
    ∃ C : MMP.Mori.ProperCurve sY, C.IsContractedBy f ∧ C.point ⤳ z := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have hx : IsClosed ({f z} : Set X) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hz
  have hsub : ¬ f.base ⁻¹' {f z} ⊆ {z} := by
    intro h
    obtain ⟨-, hEx, -⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k
      hY.1 hX.1 f hf (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    have hzE : z ∈ (MMP.Mori.exceptionalSet f : Set Y) := hzf
    rw [hEx] at hzE
    have hss : (f.base ⁻¹' {f z}).Subsingleton := Set.subsingleton_singleton.anti h
    haveI : Subsingleton (f.base ⁻¹' {f z}) := hss.coe_sort
    exact absurd (topologicalKrullDim_zero_of_discreteTopology _) (not_le.mpr hzE)
  obtain ⟨C, hCf, -, w, hw, hwz⟩ := exists_properCurve_isContractedBy k sX sY hX hY f hf hfb
    (f z) hx hz ⟨z, rfl, rfl⟩ hsub
  refine ⟨C, hCf, ?_⟩
  rw [Set.mem_singleton_iff.mp hwz, C.range_ι] at hw
  exact specializes_iff_mem_closure.mpr hw

/-- **Negative coefficients lie over the exceptional locus.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties and `B` an `ℝ`-divisor on `Y` with `f_* B` effective.
If `B` has a negative coefficient along the prime divisor `P`, then `f` maps the generic point of
`P` outside the biregular locus of `f`: over the biregular locus `f(P)` would be a prime divisor
of `X` whose coefficient in `f_* B` is that of `P` in `B`. -/
private theorem map_genericPoint_notMem_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX) {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) [IsProper f] (hfb : IsBirationalMorphism f)
    {B : RDivisor Y}
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective)
    {P : MMP.Mori.PrimeDivisor Y} (hP : B.coeff P < 0) :
    f P.genericPoint ∉ biregularLocus f := by
  intro hmem
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hmem]
    exact P.coheight_genericPoint
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = f P.genericPoint :=
    PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E, hE, -, hcoeff⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX hY hfb Q
  have hEQ : f E.genericPoint = f P.genericPoint := hE.trans hQ
  have hEP : E = P := by
    have h1 : f E.genericPoint ∈ biregularLocus f := by rwa [hEQ]
    refine PrimeDivisor.genericPoint_injective ?_
    exact (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f h1 hmem
      (by rw [hEQ])).antisymm
      (MMP.Threefold.Resolution.specializes_of_mem_biregularLocus f hmem h1 (by rw [hEQ])) |>.eq
  have h := hpush Q
  rw [DivisorWithCoeffs.coeff_apply, hcoeff B, hEP] at h
  exact absurd h (not_le.mpr hP)

/-- **Degrees can be computed on an open subscheme.** Let `V ⊆ Y` be an integral open subscheme,
`L` a Cartier divisor on `Y` and `C` a proper curve of `Y` lying in `V`, which is the proper curve
`C_V` of `V`. Then the degree of the restriction `L|_V` (the pull-back along `V ⟶ Y`) along `C_V`
is the degree of `L` along `C`. -/
private theorem degreeOn_pullback_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (V : Y.Opens) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)) (hC : V.ι CV.point = C.point)
    (hCV : closure ({C.point} : Set Y) ⊆ V) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    (L.pullback hL hB).degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le (hL.isCartier_pullback V.ι hB) =
      L.degreeOn k sY C.ι C.dim_le hL := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  have := hL.isInvertibleModule_divisorialSheaf
  have hLV := hL.isCartier_pullback V.ι hB
  have := hLV.isInvertibleModule_divisorialSheaf
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι CV.point hC (by
    rw [Scheme.Opens.range_ι]; exact hCV)
  have : IsProper ((CV.ι ≫ V.ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sY C.ι (CV.ι ≫ V.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) L.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp k sY V.ι CV.ι CV.dim_le L.divisorialSheaf
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL V.ι hB
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (V.ι ≫ sY) CV.ι CV.dim_le e₂
  exact (h1.trans (h2.trans h3.symm)).symm

/-- The coefficient of the restriction `L|_V` of a Cartier divisor along a prime divisor `E` of
the open subscheme `V` is the coefficient of `L` along the closure of `E`. -/
private theorem coeff_pullback_ι {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (V : Y.Opens) [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (E : MMP.Mori.PrimeDivisor V) :
    (L.pullback hL hB).coeff E = L.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) :=
  MMP.Positivity.coeff_eq_of_isPullback E _
    (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm hL
    (Divisor.isPullback_pullback hL hB)

/-- **An effective Cartier divisor negative on the contracted curves over an affine open.** Let
`f : Y ⟶ X` be a projective birational morphism of normal varieties and `U ⊆ X` an affine open
with `V = f⁻¹(U)` nonempty. There is an effective Cartier divisor `W` on `V` with `W · C < 0` for
every proper curve `C ⊆ V` contracted by `f`: as `U` is quasi-projective, Kollár 2.9 gives `W`
with `-W` relatively ample over `U`. -/
private theorem exists_isCartier_degreeOn_neg (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian X]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    (hfp : IsProjective f) (hfb : IsBirationalMorphism f) (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty (f ⁻¹ᵁ U)] [IsLocallyNoetherian (f ⁻¹ᵁ U)]
    [IsNormal (f ⁻¹ᵁ U)] [CompactSpace (f ⁻¹ᵁ U)] [QuasiCompact ((f ⁻¹ᵁ U).ι ≫ sY)] :
    ∃ W : Divisor (f ⁻¹ᵁ U), 0 ≤ W ∧ ∃ hW : W.IsCartier,
      ∀ C : ProperCurve ((f ⁻¹ᵁ U).ι ≫ sY), C.IsContractedBy (f ∣_ U) →
        W.degreeOn k ((f ⁻¹ᵁ U).ι ≫ sY) C.ι C.dim_le hW < 0 := by
  set V := f ⁻¹ᵁ U
  set f' : V.toScheme ⟶ U.toScheme := f ∣_ U
  haveI : IsProper f := IsProjective.isProper hfp
  have hι : ∀ y, U.ι (f' y) = f (V.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain ⟨y₀⟩ := ‹Nonempty V›
  haveI : Nonempty U := ⟨f' y₀⟩
  haveI := hX.1
  haveI := hY.1
  have hYV := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sY V
  have hXU := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sX U
  haveI : IsAffine U := hU
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hXU.toLocallyOfFiniteType
  have hXqp : Stacks.HProjective.IsHQuasiProjective (U.ι ≫ sX) := by
    open Stacks.HQuasiProjectiveDimensionOne in exact isHQuasiProjective_of_isAffine_toSpec _
  have hproj : IsProjectiveMorphism f' := isProjectiveMorphism_of_isProjective_of_isAffine f'
    (IsProjective.of_isPullback (isPullback_morphismRestrict f U) hfp)
  -- `f'` is finite over a neighbourhood of the generic point
  have hgf : ∃ W : U.toScheme.Opens, ((W : Set U) ∩ Set.range f'.base).Nonempty ∧
      IsFinite (f' ∣_ W) := by
    have : IsIntegral V.toScheme := hYV.toIsIntegral
    have : IsIntegral U.toScheme := hXU.toIsIntegral
    have : IsIntegral X := hX.1.toIsIntegral
    have : IsIntegral Y := hY.1.toIsIntegral
    have hpre := preimage_genericPoint f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    have hηU : U.ι (genericPoint U) = genericPoint X :=
      Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion U.ι
    have hηV : V.ι (genericPoint V) = genericPoint Y :=
      Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion V.ι
    have hfη : f (genericPoint Y) = genericPoint X := by
      have : genericPoint Y ∈ f.base ⁻¹' {genericPoint X} := by rw [hpre]; rfl
      exact this
    have hmem : ∀ y : V.toScheme, f' y = genericPoint U → V.ι y = genericPoint Y := by
      intro y hy
      have h : V.ι y ∈ f.base ⁻¹' {genericPoint X} := by
        change f (V.ι y) = genericPoint X
        rw [← hι, hy, hηU]
      rw [hpre] at h
      exact h
    have hfin : (f'.base ⁻¹' {genericPoint U}).Finite := by
      refine Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ => V.ι.isOpenEmbedding.injective ?_
      exact (hmem y₁ hy₁).trans (hmem y₂ hy₂).symm
    obtain ⟨W, hW, hfinW⟩ : ∃ W : U.toScheme.Opens, genericPoint U ∈ W ∧ IsFinite (f' ∣_ W) := by
      open MMP.Threefold.Mori MMP.Threefold.Resolution in
      exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton f' _ hfin
    refine ⟨W, ⟨genericPoint U, hW, genericPoint V, ?_⟩, hfinW⟩
    apply U.ι.isOpenEmbedding.injective
    rw [hι, hηV, hfη, hηU]
  obtain ⟨W, hW0, hWc, hamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism
      hYV hXU hXqp hproj hgf
  refine ⟨W, hW0, hWc, fun C hC => ?_⟩
  have := hWc.neg.isInvertibleModule_divisorialSheaf
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hYV f'
    (-W).divisorialSheaf hamp C hC
  have hneg := Divisor.degreeOn_neg' k (V.ι ≫ sY) C.ι C.dim_le W hWc
  change 0 < (-W).degreeOn k (V.ι ≫ sY) C.ι C.dim_le hWc.neg at hpos
  rw [hneg] at hpos
  change W.degreeOn k (V.ι ≫ sY) C.ι C.dim_le hWc < 0
  omega

/-- The generic point of a prime divisor `E` lies outside the support of every divisor in which
`E` has coefficient zero. -/
private theorem genericPoint_notMem_supp_of_coeff_eq_zero {R : Type*} [Zero R] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {D : DivisorWithCoeffs R Y}
    {E : MMP.Mori.PrimeDivisor Y} (hDE : D.coeff E = 0) : E.genericPoint ∉ D.supp := by
  intro h
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hmem] at hE'
  exact hE' hDE

/-- **The largest `t`.** Let `W` be an effective divisor which is positive along every prime
divisor where the `ℝ`-divisor `B` is negative, and suppose `B` is negative somewhere. For the
largest `t > 0` with `B + t W` effective, some prime divisor along which `B` is negative is not a
component of `B + t W`. -/
private theorem exists_isEffective_add_smul_coeff_eq_zero {Y : Scheme.{u}} (B : RDivisor Y)
    {W : Divisor Y} (hW0 : 0 ≤ W) (hW : ∀ E, B.coeff E < 0 → 0 < W.coeff E)
    {E₀ : MMP.Mori.PrimeDivisor Y} (hE₀ : B.coeff E₀ < 0) :
    ∃ t : ℝ, 0 < t ∧ (B + t • Divisor.toRDivisor W).IsEffective ∧
      ∃ E, B.coeff E < 0 ∧ (B + t • Divisor.toRDivisor W).coeff E = 0 := by
  classical
  have hS : ∀ E, E ∈ B.support.filter (B.coeff · < 0) ↔ B.coeff E < 0 := fun E => by
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  obtain ⟨E₁, hE₁, hmax⟩ := (B.support.filter (B.coeff · < 0)).exists_max_image
    (fun E => -B.coeff E / (W.coeff E : ℝ)) ⟨E₀, (hS E₀).2 hE₀⟩
  rw [hS] at hE₁
  have hW₁ : (0 : ℝ) < W.coeff E₁ := by exact_mod_cast hW E₁ hE₁
  have ht : 0 < -B.coeff E₁ / W.coeff E₁ := div_pos (neg_pos.mpr hE₁) hW₁
  have hcoeff : ∀ (t : ℝ) E,
      (B + t • Divisor.toRDivisor W).coeff E = B.coeff E + t * W.coeff E := fun t E => by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
  refine ⟨_, ht, fun E => ?_, E₁, hE₁, ?_⟩
  · rw [hcoeff]
    by_cases h : B.coeff E < 0
    · have hWE : (0 : ℝ) < W.coeff E := by exact_mod_cast hW E h
      linarith [(div_le_iff₀ hWE).mp (hmax E ((hS E).2 h))]
    · have : (0 : ℝ) ≤ W.coeff E := by exact_mod_cast hW0 E
      nlinarith [not_lt.mp h]
  · rw [hcoeff]
    field_simp
    ring

/-- **A contracted curve meets every neighbourhood of a negative component.** Let `f : Y ⟶ X` be
a proper birational morphism of normal varieties and `B` an `ℝ`-divisor on `Y` with `f_* B`
effective. If `B` has a negative coefficient along `P`, then every open set `O` meeting `P`
contains a closed point lying on a proper curve contracted by `f`. -/
private theorem exists_properCurve_specializes_of_coeff_neg (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    [IsProper f] (hfb : IsBirationalMorphism f) {B : RDivisor Y}
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective)
    {P : MMP.Mori.PrimeDivisor Y} (hP : B.coeff P < 0) {O : Set Y} (hO : IsOpen O)
    (hPO : P.genericPoint ∈ O) :
    ∃ C : ProperCurve sY, C.IsContractedBy f ∧ ∃ z ∈ O, C.point ⤳ z := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hA := map_genericPoint_notMem_biregularLocus hX (hf ▸ hY) hfb hpush hP
  obtain ⟨z, ⟨hzP, hzO⟩, hzc⟩ := nonempty_inter_closedPoints
    (show (closure {P.genericPoint} ∩ O).Nonempty from ⟨_, subset_closure rfl, hPO⟩)
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hzf : f z ∉ biregularLocus f := fun h => hA
    (((specializes_iff_mem_closure.mpr hzP).map f.continuous).mem_open (biregularLocus f).isOpen h)
  obtain ⟨C, hCf, hCz⟩ :=
    exists_properCurve_specializes k sX sY hX hY f hf hfb z (mem_closedPoints_iff.mp hzc) hzf
  exact ⟨C, hCf, z, hzO, hCz⟩

end Helpers

section Reduction

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor_of_coheight_eq_one {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := by
  rintro ⟨hY, hg, hp, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

/-- The pull-back `f^*L` of a Cartier divisor has degree zero on every curve contracted by `f`. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sY] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) (hf : f ≫ sX = sY)
    {L₀ : Divisor X} (hL₀ : L₀.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L₀.supp}
    {L₁ : Divisor Y} (hp : L₀.IsPullback f hB L₁) (hc : L₁.IsCartier) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) : L₁.degreeOn k sY C.ι C.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hL₀ hp
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f hf hL₀ hB C hC

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- **`B · C ≤ 0` on contracted curves.** If `f^*L ≡_f M + B` with `M` `f`-nef, then
`B · C = f^*L · C - M · C = -M · C ≤ 0` on every proper curve `C` contracted by `f`, computed from
any presentation `B = ∑ s_j N_j` by Cartier divisors. -/
private theorem sum_degreeOn_nonpos_of_isNumericallyEquivalentOver {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [QuasiCompact sY] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y]
    {f : Y ⟶ X} (hf : f ≫ sX = sY) {L : RDivisor X} {L' : RDivisor Y}
    (hL' : IsRCartierPullback f L L') {M : RDivisor Y} (hMnef : IsRelativelyNef k sY f M)
    {B : RDivisor Y} (hnum : IsNumericallyEquivalentOver k sY f L' (M + B)) {m : ℕ}
    (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hB : B = ∑ j, s j • Divisor.toRDivisor (N j)) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) :
    ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0 := by
  obtain ⟨mL, rL, L₀, L₁, hL₀, -, hpb, rfl⟩ := hL'
  have hL₁c : ∀ j, (L₁ j).IsCartier := fun j => by
    obtain ⟨hBj, hj⟩ := hpb j
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) hj]
    exact (hL₀ j).isCartier_pullback f hBj
  have hLx : IsRIntersectionNumber k sY (∑ j, rL j • Divisor.toRDivisor (L₁ j)) rL L₁ C 0 := by
    convert isRIntersectionNumber_sum_degreeOn k sY C rL L₁ hL₁c using 1
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [degreeOn_eq_zero_of_isPullback f hf (hL₀ j) (hpb j).2 (hL₁c j) C hC, Int.cast_zero,
      mul_zero]
  obtain ⟨mM, rM, LM, hLM, rfl, hMall⟩ := hMnef
  have hMx := isRIntersectionNumber_sum_degreeOn k sY C rM LM hLM
  have hBx := isRIntersectionNumber_sum_degreeOn k sY C s N hN
  rw [← hB] at hBx
  have hMB := (IsRIntersectionNumber.eq_and_linear k sY C).2 _ B rM LM s N _ _ 1 1 hMx hBx
  rw [one_smul, one_smul] at hMB
  linarith [hnum.2.2 C hC _ rL L₁ 0 _ _ _ _ hLx hMB, hMall C hC _ hMx]

/-- **Pulling back a divisor nonpositive on contracted curves.** Let `h : Y' ⟶ Y` be proper and
`B = ∑ s_j N_j` a combination of Cartier divisors with `B · C ≤ 0` on every curve contracted by
`f : Y ⟶ X`. Then `-h^*B = -∑ s_j h^*N_j` is `(h ≫ f)`-nef: by the projection formula a curve
`C'` contracted by `h ≫ f` has `h^*B · C' = [k(C') : k(h C')] (B · h C')` if `h(C')` is a curve,
which is then contracted by `f`, and `h^*B · C' = 0` if `h(C')` is a point. -/
private theorem isRelativelyNef_neg_sum_pullback {k : Type u} [Field k] {X Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [IsProper h] [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ X) {m : ℕ} (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hNB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp)
    (hBC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0) :
    IsRelativelyNef k (h ≫ sY) (h ≫ f)
      (-∑ j, s j • Divisor.toRDivisor ((N j).pullback (hN j) (hNB j))) := by
  have hN'c : ∀ j, ((N j).pullback (hN j) (hNB j)).IsCartier := fun j =>
    (hN j).isCartier_pullback h (hNB j)
  refine ⟨m, fun j => -s j, _, hN'c, by simp [← Finset.sum_neg_distrib], fun C' hC' x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (h ≫ sY) C' (fun j => -s j) _ hN'c
  rw [(IsRIntersectionNumber.eq_and_linear k (h ≫ sY) C').1 _ _ _ _ _ _ _ hx
    (by simpa [← Finset.sum_neg_distrib] using hx0)]
  by_cases hc : IsProperCurve sY (h C'.point)
  · -- `h(C')` is a curve `C`, contracted by `f`
    let C : ProperCurve sY := ⟨_, hc⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      have hsub : closure ({h C'.point} : Set Y) ⊆ h '' closure ({C'.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    simp only [degreeOn_pullback_eq_mul h (hN _) (hNB _) C' C rfl, Int.cast_mul, Int.cast_natCast,
      neg_mul, Finset.sum_neg_distrib, mul_left_comm (s _), ← Finset.mul_sum, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hBC C hCf)
  · -- `h(C')` is a point
    simp [degreeOn_pullback_eq_zero h (hN _) (hNB _) C' hc]

/-- **The push-forward of a pull-back.** Let `h : Y' ⟶ Y` and `f : Y ⟶ X` be birational
morphisms of normal varieties with `f` and `h ≫ f` proper, and `B'` the pull-back of `B` along
`h`. If `B` is nonnegative along every prime divisor of `Y` not exceptional over `X`, then
`(h ≫ f)_* B'` is effective. For a prime divisor `Q` of `X` with strict transform `E` on `Y'`,
the stalks of `X` at `η_Q` and of `Y` at `h(η_E)` are isomorphic, so `h(η_E)` is the generic point
of a prime divisor `P` of `Y` mapping onto `Q`, and `B'(E) = B(P) ≥ 0`. -/
private theorem isEffective_transformDivisor_comp_of_isRCartierPullback {k : Type u} [Field k]
    {X Y Y' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y']
    (hX : IsNormalVariety k sX) (h : Y' ⟶ Y) (f : Y ⟶ X)
    (hY' : IsNormalVariety k ((h ≫ f) ≫ sX)) [IsProper (h ≫ f)] (hfb : IsBirationalMorphism f)
    (hhb : IsBirationalMorphism h) (hf'b : IsBirationalMorphism (h ≫ f)) {B : RDivisor Y}
    {B' : RDivisor Y'} (hB' : IsRCartierPullback h B B')
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sX f P → 0 ≤ B.coeff P) :
    (MMP.Mori.RationalMap.transformDivisor (h ≫ f).toRationalMap B').IsEffective := by
  have := hfb.isDominant
  have := hhb.isDominant
  intro Q
  obtain ⟨E, hE, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hY' hf'b Q
  rw [DivisorWithCoeffs.coeff_apply, htr]
  have hfy : f (h E.genericPoint) = Q.genericPoint := by rw [← Scheme.Hom.comp_apply]; exact hE
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (X.presheaf.stalk (f (h E.genericPoint))) := by rw [hfy]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hfb.functionFieldMap_bijective
    (h E.genericPoint)
  have hco : Order.coheight (h E.genericPoint) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap (h E.genericPoint))).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hfy,
      Q.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  set P : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hP : P.genericPoint = h E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have := P.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Y.presheaf.stalk (h E.genericPoint)) := by rw [← hP]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing h hhb.functionFieldMap_bijective
    E.genericPoint
  rw [← DivisorWithCoeffs.coeff_apply, MMP.Fourfold.coeff_eq_of_isRCartierPullback E P hP.symm hB']
  refine hBG P (not_isExceptionalPrimeDivisor_of_coheight_eq_one hX f P ?_)
  rw [hP, hfy]
  exact Q.coheight_genericPoint

end Reduction

section Negativity

/-- **Negativity lemma** over an arbitrary field. Let `f : Y ⟶ X` be a projective birational
morphism of normal varieties over `k` and `B` an `ℝ`-Cartier divisor on `Y` with `-B` `f`-nef and
`f_*B` effective. Then `B` is effective. -/
private theorem isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) (hfp : IsProjective f)
    (hfb : IsBirationalMorphism f)
    {B : RDivisor Y} (hB : IsCartierCombination B) (hnef : IsRelativelyNef k sY f (-B))
    (hpush : (MMP.Mori.RationalMap.transformDivisor f.toRationalMap B).IsEffective) :
    B.IsEffective := by
  classical
  haveI : IsProper f := IsProjective.isProper hfp
  haveI := hY.1
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨m, r, L, hL, hpres, hall⟩ := hnef
  -- `-B` is `f`-nef: `∑ r_j (L_j · C) ≥ 0` on every contracted curve
  have hN : ∀ C : ProperCurve sY, C.IsContractedBy f →
      0 ≤ ∑ j, r j * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) := fun C hC =>
    hall C hC _ (by rw [hpres]; exact isRIntersectionNumber_sum_degreeOn k sY C r L hL)
  have hBpres : B = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [← neg_neg B, hpres]; simp [neg_smul, Finset.sum_neg_distrib]
  intro P₀
  by_contra! hP₀
  -- localize over an affine open `U` meeting `f(P₀)`
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show f P₀.genericPoint ∈ (⊤ : X.Opens) from trivial)
  set V := f ⁻¹ᵁ U
  set f' : V.toScheme ⟶ U.toScheme := f ∣_ U
  have hι : ∀ y, U.ι (f' y) = f (V.ι y) := fun y => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  haveI : Nonempty V := ⟨⟨P₀.genericPoint, hxU⟩⟩
  haveI : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨_, hxU⟩)
  have hYV := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sY V
  haveI : IsIntegral V := hYV.toIsIntegral
  haveI : IsNormal V := isNormal_of_isOpenImmersion V.ι
  haveI : IsAffine U := hU
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace f'
  haveI : QuasiCompact (V.ι ≫ sY) := quasiCompact_of_compactSpace _
  have hYVn : IsNormalVariety k (V.ι ≫ sY) := ⟨hYV, inferInstance⟩
  obtain ⟨W, hW0, hWc, hWneg⟩ := exists_isCartier_degreeOn_neg k sX sY hX hY f hf hfp hfb U hU
  -- the restriction `B|_V = ∑ (-r_j) L_j|_V`
  have hBj : ∀ j, ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ (L j).supp :=
    fun j => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' V.ι (L j)
  let L' : Fin m → Divisor V := fun j => (L j).pullback (hL j) (hBj j)
  have hL' : ∀ j, (L' j).IsCartier := fun j => (hL j).isCartier_pullback V.ι (hBj j)
  set BV : RDivisor V := ∑ j, (-r j) • Divisor.toRDivisor (L' j) with hBVdef
  have hBV : ∀ E, BV.coeff E = B.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) := by
    intro E
    rw [hBVdef, hBpres]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := coeff_pullback_ι V (hL j) (hBj j) E
    simp only [DivisorWithCoeffs.coeff_apply] at this
    change -r j * ((L' j E : ℤ) : ℝ) = -r j * ((L j _ : ℤ) : ℝ)
    rw [this]
  -- a contracted curve through a closed point of a negative component, off a closed set
  have hcurve : ∀ (E : MMP.Mori.PrimeDivisor V) (T : TopologicalSpace.Closeds V),
      BV.coeff E < 0 → E.genericPoint ∉ T →
      ∃ (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)), C.IsContractedBy f ∧
        CV.IsContractedBy f' ∧ V.ι CV.point = C.point ∧ closure ({C.point} : Set Y) ⊆ V ∧
        CV.point ∉ T := by
    intro E T hE hET
    obtain ⟨C, hCf, _, ⟨z', hz'T, rfl⟩, hCz⟩ :=
      exists_properCurve_specializes_of_coeff_neg k sX sY hX hY f hf hfb hpush
        (P := OpenWeilRestriction.primeDivisorMap V.ι E) (by rwa [← hBV])
        (V.ι.isOpenEmbedding.isOpenMap _ T.isClosed.isOpen_compl)
        ⟨E.genericPoint, hET, (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm⟩
    -- the curve lies in `V`
    have hfz : f C.point = f (V.ι z') := (hCf _ (specializes_iff_mem_closure.mp hCz)).symm
    have hsub : closure ({C.point} : Set Y) ⊆ V := fun w hw => by
      show f w ∈ U
      rw [hCf w hw, hfz, ← hι]
      exact (f' z').2
    obtain ⟨CV, hCV⟩ := MMP.Threefold.Resolution.exists_properCurve_of_closure_subset k V C hsub
    refine ⟨C, CV, hCf, fun y hy => ?_, hCV, hsub, fun hCT => ?_⟩
    · apply U.ι.isOpenEmbedding.injective
      rw [hι, hι, hCV]
      refine hCf _ (map_mem_closure V.ι.continuous hy fun w hw => ?_)
      rw [Set.mem_singleton_iff.1 hw, hCV]
      rfl
    · have hsp : CV.point ⤳ z' := by
        rwa [← V.ι.isOpenEmbedding.isInducing.specializes_iff, hCV]
      exact hz'T (hsp.mem_closed T.isClosed hCT)
  -- every prime divisor with negative coefficient in `B|_V` is a component of `W`
  have hWpos : ∀ E, BV.coeff E < 0 → 0 < W.coeff E := by
    intro E hE
    by_contra! hW
    obtain ⟨C, CV, -, hCVf, -, -, hCVT⟩ := hcurve E _ hE
      (genericPoint_notMem_supp_of_coeff_eq_zero (le_antisymm hW (hW0 E)))
    exact (hWneg CV hCVf).not_ge (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (V.ι ≫ sY)
      CV.ι CV.dim_le W hWc hW0 ⟨_, by rwa [CV.ι_genericPoint]⟩).1
  -- for the largest `t` with `D = B|_V + t W` effective, `D · C ≥ 0` for a contracted curve `C`
  obtain ⟨E₀, hE₀⟩ := MMP.Threefold.Resolution.exists_primeDivisorMap_eq V P₀ hxU
  obtain ⟨t, ht, hDeff, E₁, hE₁, hD₁⟩ :=
    exists_isEffective_add_smul_coeff_eq_zero BV hW0 hWpos (E₀ := E₀) (by rwa [hBV, hE₀])
  obtain ⟨C, CV, hCf, hCVf, hCV, hsub, hCVT⟩ :=
    hcurve E₁ _ hE₁ (genericPoint_notMem_supp_of_coeff_eq_zero hD₁)
  have h := sum_degreeOn_add_nonneg k (V.ι ≫ sY) hYVn CV (fun j => -r j) L' hL' t W hWc hDeff hCVT
  have hdeg : ∀ j, ((L' j).degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le (hL' j) : ℝ) =
      (L j).degreeOn k sY C.ι C.dim_le (hL j) := fun j => by
    exact_mod_cast degreeOn_pullback_ι V (hL j) (hBj j) C CV hCV hsub
  simp only [hdeg, neg_mul, Finset.sum_neg_distrib] at h
  -- but `D · C = B · C + t (W · C) < 0`
  have hWC : (W.degreeOn k (V.ι ≫ sY) CV.ι CV.dim_le hWc : ℝ) < 0 := by
    exact_mod_cast hWneg CV hCVf
  nlinarith [hN C hCf]

end Negativity

/-- **Exceptional coefficients are nonnegative.** If `f^*L ≡_f M + B` with `M` `f`-nef and `B`
nonnegative along every prime divisor not exceptional over `X`, then `B` is effective. -/
private theorem isEffective_of_isNumericallyEquivalentOver (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) [IsProper f] (hfb : IsBirationalMorphism f)
    {L : RDivisor X} (hL : IsCartierCombination L) {L' : RDivisor Y}
    (hL' : IsRCartierPullback f L L')
    {M : RDivisor Y} (hM : IsCartierCombination M) (hMnef : IsRelativelyNef k sY f M)
    {B : RDivisor Y} (hB : IsCartierCombination B)
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sX f P → 0 ≤ B.coeff P)
    (hnum : IsNumericallyEquivalentOver k sY f L' (M + B)) :
    B.IsEffective := by
  have := hY.1
  have := hX.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral X := hX.1.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨m, s, N, hN, hBeq⟩ := hB
  have hBeq' : B = ∑ j, s j • Divisor.toRDivisor (N j) := by
    simpa only [toRDivisor_eq_mapCoeffs] using hBeq
  -- the Chow lemma: `h : Y' ⟶ Y` projective birational, `Y'` normal, `h ≫ f` projective
  obtain ⟨Y', h, hY'v, hY'n, hhp, hhb, hfp'⟩ :=
    MMP.Resolution.Bridges.exists_isProjective_isBirational_isNormal_chowModification k hY.1 hX.1
      f hf ‹_› (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
  have : IsProper h := IsProjective.isProper hhp
  have : IsIntegral Y' := hY'v.toIsIntegral
  have : QuasiCompact (h ≫ sY) := hY'v.toQuasiCompact
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (h ≫ sY)
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (h ≫ sY)
  have hY' : IsNormalVariety k (h ≫ sY) := ⟨hY'v, hY'n⟩
  have hhB : IsBirationalMorphism h := isBirationalMorphism_of_isBirational h hhb
  have hf'b : IsBirationalMorphism (h ≫ f) := isBirationalMorphism_of_isBirational (h ≫ f)
    (hhb.comp (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb))
  have hf' : (h ≫ f) ≫ sX = h ≫ sY := by rw [Category.assoc, hf]
  have : IsDominant h := hhB.isDominant
  -- the pull-back `B' = h^*B = ∑ s_j h^*N_j`, with `-B'` `(h ≫ f)`-nef and `(h ≫ f)_* B' ≥ 0`
  have hNB j : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant h (N j)
  have hB' : IsRCartierPullback h B _ := ⟨m, s, N, _, hN, hBeq',
    fun j => ⟨hNB j, Divisor.isPullback_pullback (hN j) (hNB j)⟩, rfl⟩
  have hB'eff := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor k sX (h ≫ sY)
    hX hY' (h ≫ f) hf' hfp' hf'b
    ⟨m, s, _, fun j => (hN j).isCartier_pullback h (hNB j), by simp only [toRDivisor_eq_mapCoeffs]⟩
    (isRelativelyNef_neg_sum_pullback h f s N hN hNB
      (sum_degreeOn_nonpos_of_isNumericallyEquivalentOver hf hL' hMnef hnum s N hN hBeq'))
    (isEffective_transformDivisor_comp_of_isRCartierPullback hX h f (hf' ▸ hY') hfb hhB hf'b hB'
      hBG)
  intro P
  obtain ⟨E, hE, _, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hY' hhB P
  rw [← MMP.Fourfold.coeff_eq_of_isRCartierPullback E P hE hB']
  exact hB'eff E

end NegativityCoefficients

end

section

/-!
### The negativity lemma

Let `h : Z ⟶ Y` be a proper birational morphism of normal varieties over a field `k` and `B` a
`ℚ`-Cartier `ℚ`-divisor on `Z` with `-B` `h`-nef. Then `B` is effective if and only if `h_* B`
is effective.

If `B` is effective so is `h_* B`, since the birational transform keeps or drops coefficients.
Conversely, regard `B` as an `ℝ`-divisor. A presentation `m (-B) = L` with `L` Cartier makes
`-B` an `ℝ`-Cartier divisor that is `h`-nef in the sense of real intersection numbers: the
intersection number of `L` with a proper curve `C` is the degree of `𝒪_Z(L)` along `C`, whichever
normalization of `C` computes it. If `P` is a prime divisor of `Z` not exceptional over `Y`, then
`y = h(η_P)` has coheight at most one, so `𝒪_{Y,y}` is a valuation ring and `h` induces an
isomorphism `𝒪_{Y,y} ≅ 𝒪_{Z,η_P}`; hence `y` is the generic point of a prime divisor `Q` of `Y`,
and the coefficient of `Q` in `h_* B` is that of `P` in `B`, which is therefore nonnegative. The
negativity lemma in the form `NegativityCoefficients.isEffective_of_isNumericallyEquivalentOver`
(with `L = 0` and `M = -B`) then shows that `B` is effective.

The source argues by induction on the dimension, cutting by general hyperplane sections down to
the surface case. Here the negativity lemma for `ℝ`-divisors and proper birational morphisms over
an arbitrary field, `NegativityCoefficients.isEffective_of_isNumericallyEquivalentOver`, is applied
directly.

References:

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.39(1)
-/

open MMP.Flips

universe u

namespace Negativity

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact NegativityCoefficients.degreeOn_normalization C hν hdim _

/-- **`ℚ`-nefness is `ℝ`-nefness.** A `ℚ`-Cartier `ℚ`-divisor which is nef over `Y` is, as an
`ℝ`-divisor, `ℝ`-Cartier and nef over `Y`. -/
private theorem QDivisor.IsRelativelyNef.isRelativelyNef_toRDivisor [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} {f : X ⟶ Y} {D : QDivisor X}
    (h : QDivisor.IsRelativelyNef sX f D) :
    MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D) := by
  obtain ⟨hD, hh⟩ := h
  set N := D.cartierIndex hD
  have hNpos : (0 : ℚ) < N := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set L : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : L.IsCartier := (D.cartierIndexSMul hD).2
  have hLD : ∀ P, (L.coeff P : ℚ) = N * D.coeff P := fun P => by
    have := congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul D hD)
    simpa [zsmul_eq_mul] using this
  refine ⟨1, fun _ => ((1 / N : ℚ) : ℝ), fun _ => L, fun _ => hLc, ?_, fun C hC x hx => ?_⟩
  · ext P
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, smul_eq_mul, ← Rat.cast_intCast, hLD P]
    push_cast
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hNpos.ne']
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    have key := hh C hC
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    rw [Fin.sum_univ_one, eq_degreeOn_of_isCartierIntersectionNumber (hd 0)]
    exact (by exact_mod_cast key :
      (0 : ℝ) ≤ ((1 / N : ℚ) : ℝ) * (L.degreeOn k sX C.ι C.dim_le hLc : ℝ))

end Intersection

/-- An `ℝ`-divisor that is nef over `Y` is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyNef {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    {D : RDivisor X} (h : MMP.Flips.IsRelativelyNef k sX f D) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD, -⟩ := h
  exact ⟨m, r, L, hL, hD⟩

/-- The negative of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_neg {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : RDivisor X} (h : IsCartierCombination D) : IsCartierCombination (-D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact ⟨m, -r, L, hL, by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- The zero divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_zero {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] :
    IsCartierCombination (0 : RDivisor X) :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

/-- A prime divisor `P` of `Z` whose image `h(η_P)` has coheight at least two in `Y` is
exceptional over `Y`. -/
private theorem isExceptionalPrimeDivisor_of_two_le_coheight {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) (h : Z ⟶ Y)
    (hZ : IsNormalVariety k (h ≫ sY)) [IsProper h] (hhb : IsBirationalMorphism h)
    (P : MMP.Mori.PrimeDivisor Z) (h2 : 2 ≤ Order.coheight (h P.genericPoint)) :
    IsExceptionalPrimeDivisor sY h P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨n, hYdim⟩ := NegativityCoefficients.exists_topologicalKrullDim_eq_natCast sY
  refine ⟨hZ, hhb, inferInstance, ?_⟩
  unfold ProperDivisorOver.IsExceptional
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hYdim]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (h P.genericPoint)
  rw [hYdim] at hd
  exact (NegativityCoefficients.withBot_add_two_le_iff hd).mpr h2

/-- Over a prime divisor `P` of `Z` not exceptional over `Y`, the coefficient of `P` in `B` is the
coefficient of `h(P)` in `h_* B`. -/
private theorem coeff_nonneg_of_not_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) (h : Z ⟶ Y)
    (hZ : IsNormalVariety k (h ≫ sY)) [IsProper h] (hhb : IsBirationalMorphism h) {B : QDivisor Z}
    (heff : (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective)
    (P : MMP.Mori.PrimeDivisor Z) (hP : ¬ IsExceptionalPrimeDivisor sY h P) :
    0 ≤ B.coeff P := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsDominant h := hhb.isDominant
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have : IsNormal Z := hZ.2
  have hbij := hhb.functionFieldMap_bijective
  have hle : Order.coheight (h P.genericPoint) ≤ 1 := by
    by_contra hlt
    exact hP (isExceptionalPrimeDivisor_of_two_le_coheight hY h hZ hhb P
      (Order.add_one_le_of_lt (not_le.mp hlt)))
  haveI : ValuationRing (Y.presheaf.stalk (h P.genericPoint)) := by
    rcases lt_or_eq_of_le hle with h0 | h1
    · have hmax : IsMax (h P.genericPoint) :=
        Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
      have hgy : h P.genericPoint = genericPoint Y :=
        Specializes.antisymm (hmax (genericPoint_specializes _))
          (genericPoint_specializes _) |>.eq
      rw [hgy]
      change ValuationRing Y.functionField
      infer_instance
    · set Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
      have hQ : Q.genericPoint = h P.genericPoint :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
      have := Q.isDiscreteValuationRing_localRing
      rw [← hQ]
      infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing h hbij P.genericPoint
  have hco : Order.coheight (h P.genericPoint) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv
      (asIso (h.stalkMap P.genericPoint)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1
  set Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = h P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E, hE, hiso, hcoeff⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hZ hhb Q
  have hEP : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap h hbij (x₁ := P.genericPoint) (x₂ := E.genericPoint)
      (hE.trans hQ)).symm
  have := heff Q
  rwa [DivisorWithCoeffs.coeff_apply, hcoeff B, hEP] at this

/-- The birational transform of an effective divisor is effective: it keeps or drops each
coefficient. -/
private theorem isEffective_transformDivisor {X Y : Scheme.{u}} {f : RationalMap X Y}
    {D : QDivisor X} (hD : D.IsEffective) :
    (RationalMap.transformDivisor (X := X) f D).IsEffective := by
  classical
  rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  refine Finset.sum_induction _ DivisorWithCoeffs.IsEffective
    (fun _ _ => DivisorWithCoeffs.IsEffective.add) DivisorWithCoeffs.isEffective_zero fun P _ => ?_
  rw [RationalMap.transformDivisor_single]
  rcases f.transformPrimeDivisor P with _ | E
  · exact DivisorWithCoeffs.isEffective_zero
  · intro E'
    simp only [Option.elim_some]
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_rfl

/-- **The negativity lemma for `ℝ`-divisors.** Let `h : Z ⟶ Y` be a proper birational morphism of
normal varieties and `B` an `ℝ`-divisor on `Z` with `-B` nef over `Y`. If the coefficient of `B`
along every prime divisor not exceptional over `Y` is nonnegative, then `B` is effective. -/
private theorem isEffective_of_isRelativelyNef_neg (k : Type u) [Field k] {Y Z : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ] [IsLocallyNoetherian Z]
    [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ) (h : Z ⟶ Y)
    (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h) {B : RDivisor Z}
    (hnef : MMP.Flips.IsRelativelyNef k sZ h (-B))
    (hBG : ∀ P : MMP.Mori.PrimeDivisor Z, ¬ IsExceptionalPrimeDivisor sY h P → 0 ≤ B.coeff P) :
    B.IsEffective := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  have hMc := isCartierCombination_of_isRelativelyNef hnef
  refine NegativityCoefficients.isEffective_of_isNumericallyEquivalentOver k sY sZ hY hZ h hh hhb
    (L := 0) (L' := 0) isCartierCombination_zero
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    hMc hnef (by simpa using isCartierCombination_neg hMc) hBG ?_
  rw [neg_add_cancel]
  exact ⟨isCartierCombination_zero, isCartierCombination_zero, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂
    h₁ h₂ => (IsRIntersectionNumber.eq_and_linear k sZ C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩

/-- **The negativity lemma.** For a proper birational morphism `h` of normal varieties and a
`ℚ`-Cartier divisor `B` with `-B` `h`-nef, `B` is effective if and only if `h_* B` is. -/
private theorem isEffective_iff_isEffective_transformDivisor (k : Type u) [Field k]
    {Y Z : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [QuasiCompact sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (hY : IsNormalVariety k sY) (hZ : IsNormalVariety k sZ)
    (h : Z ⟶ Y) (hh : h ≫ sY = sZ) [IsProper h] (hhb : IsBirationalMorphism h)
    {B : QDivisor Z} (hB : B.IsQCartier) (hnef : (-B).IsRelativelyNef sZ h) :
    B.IsEffective ↔
      (RationalMap.transformDivisor (X := Z) h.toRationalMap B).IsEffective := by
  refine ⟨isEffective_transformDivisor, fun heff E => ?_⟩
  have := isEffective_of_isRelativelyNef_neg k sY sZ hY hZ h hh hhb (B := B.toRDivisor)
    (by simpa using QDivisor.IsRelativelyNef.isRelativelyNef_toRDivisor (k := k) hnef)
    (fun P hP => by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast coeff_nonneg_of_not_isExceptionalPrimeDivisor hY h (hh ▸ hZ) hhb heff P hP) E
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

end Negativity

end

/-! ### Normalized graphs and relatively ample multiples -/

section Shared

/-- The first projection `u : G ⟶ X⁻` of a normalized graph of proper morphisms is proper. -/
private theorem isProper_minus_of_isNormalizedGraph {Xm Xp Z G : Scheme.{0}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} [IsProper fp] (hG : IsNormalizedGraph fm fp u v) :
    IsProper u := by
  haveI := hG.isFinite
  rw [← Limits.pullback.lift_fst u v hG.comp_eq]
  infer_instance

/-- The second projection `v : G ⟶ X⁺` of a normalized graph of proper morphisms is proper. -/
private theorem isProper_plus_of_isNormalizedGraph {Xm Xp Z G : Scheme.{0}} {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp} [IsProper fm] (hG : IsNormalizedGraph fm fp u v) :
    IsProper v := by
  haveI := hG.isFinite
  rw [← Limits.pullback.lift_snd u v hG.comp_eq]
  infer_instance

/-- The `ℚ`-Cartier property passes from `D` to `-D`. -/
private theorem isQCartier_neg {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : (-D).IsQCartier := by
  obtain ⟨n, hn, E, hE, hEc⟩ := h
  exact ⟨-n, neg_ne_zero.mpr hn, E, by rw [hE, smul_neg, neg_smul, neg_neg], hEc⟩

/-- A `ℚ`-divisor with a relatively ample multiple is `ℚ`-Cartier. -/
private theorem isQCartier_of_hasRelativelyAmpleMultiple {X W : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ W} {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple g) : D.IsQCartier := by
  obtain ⟨m, hm, L, hLc, hL, -⟩ := hD
  exact ⟨m, by exact_mod_cast hm.ne', L, hL, hLc⟩

/-- A `ℚ`-divisor with a `g`-ample multiple is positive on every proper curve contracted by `g`. -/
private theorem intersectionNumber_pos_of_hasRelativelyAmpleMultiple {X W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {g : X ⟶ W} {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple g) (hDq : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy g) : 0 < D.intersectionNumber ℂ sX C.ι C.dim_le hDq := by
  obtain ⟨m, hm, L, hLc, hL, hamp⟩ := hD
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le D hDq hm L hLc hL]
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
    g _ hamp C hC
  exact div_pos (Int.cast_pos.mpr this) (Nat.cast_pos.mpr hm)

/-- A `ℚ`-divisor with a `g`-ample multiple is `v`-nef for every `v` whose contracted curves are
contracted by `g`. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple {X Y W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {g : X ⟶ W} {v : X ⟶ Y} {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple g)
    (hvg : ∀ C : ProperCurve sX, C.IsContractedBy v → C.IsContractedBy g) :
    D.IsRelativelyNef sX v :=
  QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX
    (isQCartier_of_hasRelativelyAmpleMultiple hD) fun C hC =>
      (intersectionNumber_pos_of_hasRelativelyAmpleMultiple sX hD
        (isQCartier_of_hasRelativelyAmpleMultiple hD) C (hvg C hC)).le

end Shared

section

/-!
### The graph divisor of a step diagram is effective

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a step diagram with normalized graph `(G, u, v)` and graph
divisor `H`. The morphism `v : G ⟶ X⁺` is proper and birational between normal varieties. Every
curve contracted by `v` is contracted by `g = f⁺ ∘ v = f⁻ ∘ u`, and `-H` is `g`-ample, so `-H` is
`v`-nef; moreover `v_* H = 0`. The negativity lemma gives `H ≥ 0`.
-/

namespace GraphDivisorEffective

/-- **The graph divisor is effective.** -/
private theorem nonneg_of_isGraphDivisor {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm]
    [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsLocallyNoetherian G] [IsNormal G]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) : 0 ≤ H := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  haveI := hG.isIntegral
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_plus_of_isNormalizedGraph hG
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace v
  haveI := hD.isNormalVariety_plus.1
  have hnef : (-H).IsRelativelyNef (v ≫ sXp) v :=
    isRelativelyNef_of_hasRelativelyAmpleMultiple _ h.hasRelativelyAmpleMultiple_neg
      fun C hC x hx => by
        rw [hG.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  exact DivisorWithCoeffs.isEffective_iff_nonneg.mp <|
    (Negativity.isEffective_iff_isEffective_transformDivisor ℂ sXp (v ≫ sXp)
      hD.isNormalVariety_plus ⟨⟨⟩, inferInstance⟩ v rfl hG.isBirationalMorphism_plus
      (by simpa using isQCartier_neg hnef.1) hnef).2
      (by rw [h.transformDivisor_eq_zero]; exact DivisorWithCoeffs.isEffective_zero)

end GraphDivisorEffective

end

section

/-!
### Discrepancy comparison for step diagrams

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a step diagram of fourfolds with normalized graph `(G, u, v)` and
graph divisor `H = u^* D⁻ - v^* D⁺`, where `D^± = K_{X^±} + B^±`. For a valuation `ξ` of `k(G)`
whose restriction to `k(X⁻)` is a normalized divisorial valuation,
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H) ≥ 0`.

The proof realizes `ξ = ord_E` on a normal variety `W` with a proper birational `w : W ⟶ G`; this
uses the valuative criterion for the proper morphism `u` to find a point of `G` dominated by the
valuation ring of `ξ`. The canonical divisor `K⁻` is `div(f⁻^* τ)` for a rational top form `τ` on
`Z`, and then `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻ = div(f⁺^* τ)`: a prime divisor of `X⁺` and its centre on `X⁻`
lie over the same prime divisor of `Z`, where `f^±` are local isomorphisms. So `(uw)^* (f⁻)^* τ`
and `(vw)^* (f⁺)^* τ` are the same form on `W`, and the two log discrepancies, computed with it,
differ by the coefficient along `E` of `(uw)^* D⁻ - (vw)^* D⁺ = w^* H`. Finally `w^* H ≥ 0`
because `H ≥ 0` is `ℚ`-Cartier.

References:

* [OpenAI, *Projective lc fourfolds*][OAI4], the graph divisor of a step diagram
-/

open Opposite
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

universe u

namespace GraphComparison

section CanonicalDivisorExistence

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- In an irreducible space every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (Z : irreducibleComponents T) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem specializes_componentGenericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (specializes_componentGenericPoint Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_genericPoint_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (specializes_componentGenericPoint Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (specializes_componentGenericPoint E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (specializes_componentGenericPoint E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (specializes_componentGenericPoint E.component)).hom
            s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_genericPoint_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_genericPoint_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (specializes_componentGenericPoint _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨x, hx, hxe⟩ => by
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx⟩
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · exact fun h E' hE' => (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · exact Subtype.ext (restrictRF_injective U V (congrArg Subtype.val h))
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := Opens.isDominant_ι (T.isOpen.dense ⟨_, (Classical.arbitrary T).2⟩)
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : IsIntegral T := inferInstance
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

end CanonicalDivisorExistence

section Helpers

variable {X Y : Scheme.{u}}

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If the exceptional set of `f` has codimension at least two, it misses the generic point of
every prime divisor. -/
private theorem genericPoint_notMem_exceptionalSet {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (exceptionalSet f : Set X) := fun h => by
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f :=
  not_not.mp (genericPoint_notMem_exceptionalSet h2 P)

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal_support (D : MMP.Mori.PrimeDivisor X) :
    D.idealSheaf = Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support := by
  have := D.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

private theorem mem_support_iff (D : MMP.Mori.PrimeDivisor X) (x : X) :
    x ∈ D.support ↔ D.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, specializes_iff_mem_closure]

/-- If `f(P) = Q` as sets then `f(η_P) = η_Q`. -/
private theorem map_genericPoint_eq_of_image_eq {f : X ⟶ Y} (P : MMP.Mori.PrimeDivisor X)
    (Q : MMP.Mori.PrimeDivisor Y) (h : f '' P.support = Q.support) :
    f P.genericPoint = Q.genericPoint := by
  have h1 : f P.genericPoint ∈ Q.support :=
    h ▸ ⟨_, (mem_support_iff P _).mpr specializes_rfl, rfl⟩
  obtain ⟨y, hy, hfy⟩ : Q.genericPoint ∈ f '' P.support :=
    h ▸ (mem_support_iff Q _).mpr specializes_rfl
  have h3 : f P.genericPoint ⤳ Q.genericPoint :=
    hfy ▸ ((mem_support_iff P y).mp hy).map f.continuous
  exact (h3.antisymm ((mem_support_iff Q _).mp h1)).eq

/-- Over the biregular locus, the inverse transform of `Q` is the prime divisor through the
point over `η_Q`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of {f : X ⟶ Y}
    (P : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (hPQ : f P.genericPoint = Q.genericPoint) (hV : Q.genericPoint ∈ biregularLocus f) :
    inverseTransformPrimeDivisor f Q = some P := by
  have hset : (inverseTransform f Q.idealSheaf.support : Set X) = P.support := by
    rw [inverseTransform, Closeds.coe_closure]
    refine le_antisymm (closure_minimal ?_ ?_) ?_
    · rintro y ⟨hyQ, hyV⟩
      have h1 : f P.genericPoint ⤳ f y := hPQ ▸ (mem_support_iff Q _).mp hyQ
      exact (mem_support_iff P y).mpr (specializes_of_map_specializes (hPQ ▸ hV) hyV h1)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr (subset_closure ?_)) isClosed_closure
      refine ⟨?_, ?_⟩
      · change f P.genericPoint ∈ Q.support
        rw [hPQ]; exact (mem_support_iff Q _).mpr specializes_rfl
      · change f P.genericPoint ∈ biregularLocus f
        rwa [hPQ]
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨Q.genericPoint,
    (mem_support_iff Q _).mpr specializes_rfl, hV⟩, ?_⟩
  rw [inverseTransformIdeal, idealSheaf_eq_vanishingIdeal_support P]
  congr 1
  ext1
  exact hset.symm

/-- For a surjective `f`, `P` is the inverse transform of at most one prime divisor `Q`. -/
private theorem eq_of_inverseTransformPrimeDivisor_eq_some {f : X ⟶ Y}
    (hs : Function.Surjective f) {P : MMP.Mori.PrimeDivisor X} {Q Q' : MMP.Mori.PrimeDivisor Y}
    (hPQ : f P.genericPoint = Q.genericPoint) (h : inverseTransformPrimeDivisor f Q' = some P) :
    Q' = Q := by
  obtain ⟨⟨z, hzQ, hzV⟩, hI⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp h
  have hset : P.support = closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) := by
    have := congrArg (fun I ↦ (I.support : Set X)) hI
    simp only [inverseTransformIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    rw [AlgebraicGeometry.PrimeDivisor.support, this, inverseTransform, Closeds.coe_closure]
  have hQ'cl : IsClosed (Q'.support : Set Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  -- `η_Q ∈ Q'`
  have h1 : Q.genericPoint ∈ Q'.support := by
    have hP : P.genericPoint ∈ closure (f ⁻¹' ((Q'.support : Set Y) ∩ biregularLocus f)) :=
      hset ▸ (mem_support_iff P _).mpr specializes_rfl
    have := image_closure_subset_closure_image f.continuous ⟨_, hP, rfl⟩
    rw [hPQ] at this
    refine closure_minimal ?_ hQ'cl this
    rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
    exact hy
  -- `η_{Q'} ∈ Q`
  have h2 : Q'.genericPoint ∈ Q.support := by
    have hgV : Q'.genericPoint ∈ biregularLocus f :=
      ((mem_support_iff Q' z).mp hzQ).mem_open (biregularLocus f).isOpen hzV
    obtain ⟨y, hy⟩ := hs Q'.genericPoint
    have hyP : y ∈ P.support := by
      rw [hset]
      refine subset_closure ⟨?_, ?_⟩
      · change f y ∈ Q'.support
        rw [hy]; exact (mem_support_iff Q' _).mpr specializes_rfl
      · change f y ∈ biregularLocus f
        rw [hy]; exact hgV
    rw [← hy, mem_support_iff, ← hPQ]
    exact ((mem_support_iff P y).mp hyP).map f.continuous
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (((mem_support_iff Q' _).mp h1).antisymm ((mem_support_iff Q _).mp h2)).eq

end Helpers

/-- A normal complex variety is separated. -/
private theorem isSeparated_toTerminal_of_isNormalVariety {X : Scheme.{0}}
    {s : X ⟶ Spec (.of ℂ)} (h : IsNormalVariety ℂ s) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  have := h.1
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-! ### Birational morphisms over the generic point of a prime divisor -/

section Birational

variable {X Y : Scheme.{u}}

/-- A separated birational morphism is injective over a point whose local ring is a valuation
ring. -/
private theorem eq_of_map_eq_of_valuationRing [IsIntegral X] [IsIntegral Y] {f : X ⟶ Y}
    [IsSeparated f] [IsDominant f] (hμ : Function.Bijective (functionFieldMap f)) {y : Y}
    [ValuationRing (Y.presheaf.stalk y)] {x₁ x₂ : X} (h₁ : f x₁ = y) (h₂ : f x₂ = y) :
    x₁ = x₂ := by
  subst h₁
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₁
  haveI : ValuationRing (Y.presheaf.stalk (f x₂)) := by rw [h₂]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hμ x₂
  exact MMP.Positivity.eq_of_isIso_stalkMap f hμ h₂

end Birational

/-! ### Strict transforms across a step -/

section FlipTransform

variable {Xm Xp Z : Scheme.{u}} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The coefficient of `P` in the strict transform `(f⁺)⁻¹_* f⁻_* D` is that of `P⁻` in `D`,
when `P⁻` is the only prime divisor with transform `Q` under `f⁻` and `Q` the only prime divisor
with inverse transform `P` under `f⁺`. -/
private theorem flipTransform_apply
    {Pm : MMP.Mori.PrimeDivisor Xm} {Q : MMP.Mori.PrimeDivisor Z} {P : MMP.Mori.PrimeDivisor Xp}
    (h1 : RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap Pm = some Q)
    (h1' : ∀ E', RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap E' = some Q →
      E' = Pm)
    (h2 : inverseTransformPrimeDivisor fp Q = some P)
    (h2' : ∀ Q', inverseTransformPrimeDivisor fp Q' = some P → Q' = Q)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    flipTransform fm fp D P = D Pm := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [inverseTransformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h2 h2',
    RationalMap.transformDivisor, MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 h1']

/-- Let `f⁻ : X⁻ → Z ← X⁺ : f⁺` be birational, `f⁻` separated, `f⁺` surjective, and let `Q` be a
prime divisor of `Z` whose local ring is a valuation ring, with `f⁻(η_P) = η_Q = f⁺(η_{P⁺})` and
`f⁺` biregular over `η_Q`. Then the strict transform `(f⁺)⁻¹_* f⁻_* D` has the coefficient of
`D` at `P` at `P⁺`. -/
private theorem flipTransform_apply_of_map_genericPoint [IsIntegral Xm] [IsIntegral Z]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] [IsSeparated fm] [IsDominant fm]
    (hbm : Function.Bijective (functionFieldMap fm))
    (hs : Function.Surjective fp) {P : MMP.Mori.PrimeDivisor Xm} {Pp : MMP.Mori.PrimeDivisor Xp}
    {Q : MMP.Mori.PrimeDivisor Z} [ValuationRing (Z.presheaf.stalk Q.genericPoint)]
    (hPQ : fm P.genericPoint = Q.genericPoint) (hPpQ : fp Pp.genericPoint = Q.genericPoint)
    (hV : Q.genericPoint ∈ biregularLocus fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) : flipTransform fm fp D Pp = D P :=
  flipTransform_apply
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hPQ)
    (fun E' hE' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_valuationRing hbm
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm E' Q).mp hE') hPQ)
    (inverseTransformPrimeDivisor_eq_some_of Pp Q hPpQ hV)
    (fun _ hQ' => eq_of_inverseTransformPrimeDivisor_eq_some hs hPpQ hQ') D

end FlipTransform

section ValuationLift

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]
    exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

end ValuationLift

private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  (eq_univ_of_irreducibleComponents W).symm ▸ Set.mem_univ t

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ
/-- If `m • (div ω + Δ)` is the integral divisor `D`, then `ord_Γ ω + coeff_Γ Δ = m⁻¹ coeff_Γ D`:
the coefficients of the `ℝ`-divisor `K + Δ` read off from a Cartier multiple. -/
private theorem ordForm_add_coeff_eq {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] {d : ℕ}
    (ω : RationalPluriForms sZ d 1) (Δ : QDivisor Z)
    {m₀ : ℕ} (hm₀ : 0 < m₀) {D : Divisor Z}
    (hD : Divisor.toQDivisor D = (m₀ : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + Δ))
    (Γ : MMP.Mori.PrimeDivisor Z) :
    (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor Δ).coeff Γ =
      ∑ _i : Fin 1, (m₀ : ℝ)⁻¹ * (D.coeff Γ : ℝ) := by
  have hc := congrArg (fun G : QDivisor Z => G.coeff Γ) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast, coeff_divisorOfForm] at hc
  have hR : (D.coeff Γ : ℝ) = m₀ * (Γ.ordForm ω + (Δ.coeff Γ : ℝ)) := by exact_mod_cast hc
  have hm₀R : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  simp only [Finset.univ_unique, Finset.sum_singleton, QDivisor.coeff_toRDivisor, hR]
  field_simp

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-! ### Rational top forms -/

section Forms

/-- Forms pulled back along equal morphisms have the same order along a prime divisor. -/
private theorem ordForm_pullbackRationalPluriForms_congr {W Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} {g g' : W ⟶ Z}
    [IsDominant g] [IsDominant g'] (hg : g = g') (E : MMP.Mori.PrimeDivisor W) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sZ d m) :
    E.ordForm (pullbackRationalPluriForms sZ g τ) =
      E.ordForm (pullbackRationalPluriForms sZ g' τ) := by
  subst hg
  rfl

/-- **Rational top forms descend along a birational morphism.** If `f : X ⟶ Z` induces an
isomorphism of function fields, every rational top form on `X` is the pull-back `f^* τ` of a
rational top form `τ` on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    (ω : RationalPluriForms (f ≫ sZ) n 1) :
    ∃ τ : RationalPluriForms sZ n 1, pullbackRationalPluriForms sZ f τ = ω := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd
  obtain ⟨g, hg⟩ := hbij.2
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 _ = ω
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = ω
  rw [hg]
  exact basis_unit_repr_smul _ ω

end Forms

/-! ### Strict transforms across a step -/

section StepDiagram

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- **A step extracts no divisor.** In a step diagram, a prime divisor `P` of `X⁺` and a prime
divisor `P⁻` of `X⁻` lie over the same prime divisor `Q` of `Z`, and every strict transform
`(f⁺)⁻¹_* f⁻_* D` has at `P` the coefficient of `D` at `P⁻`. -/
private theorem exists_flipTransform_apply_eq (hD : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (P : MMP.Mori.PrimeDivisor Xp) :
    ∃ (Pm : MMP.Mori.PrimeDivisor Xm) (Q : MMP.Mori.PrimeDivisor Z),
      fm Pm.genericPoint = Q.genericPoint ∧ fp P.genericPoint = Q.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm),
        flipTransform fm fp D P = D Pm := by
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  have hbm := hD.isBirationalMorphism_minus
  haveI := hbm.isDominant
  haveI := hD.isBirationalMorphism_plus.isDominant
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ := exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hbm
    hD.isSmallMorphism_plus P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  have := Q.isDiscreteValuationRing_localRing
  exact ⟨Pm, Q, hPmQ', hPQ', fun D => flipTransform_apply_of_map_genericPoint
    hbm.functionFieldMap_bijective fp.surjective hPmQ' hPQ'
    (hPQ' ▸ map_genericPoint_mem_biregularLocus hD.isSmallMorphism_plus.two_le_codimension P) D⟩

/-- **The canonical divisor of `X⁺`.** In a step diagram over `Z` with `K = div(f⁻^* τ)` for a
rational top form `τ` on `Z`, the strict transform `K⁺ = (f⁺)⁻¹_* f⁻_* K` is `div(f⁺^* τ)`. -/
private theorem divisorOfForm_eq_flipTransform [IsIntegral Z]
    (hD : IsFourfoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) {n : ℕ}
    (hd : letI := functionFieldAlgebra sZ; (Algebra.trdeg ℂ Z.functionField).toNat = n)
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType (fp ≫ sZ)] [IsDominant fm] [IsDominant fp]
    (τ : RationalPluriForms sZ n 1)
    (hK : ∀ Γ, Γ.ordForm (pullbackRationalPluriForms sZ fm τ) = K.coeff Γ) :
    divisorOfForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K := by
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  refine Finsupp.ext fun P => ?_
  obtain ⟨Pm, Q, hPm, hP, hfl⟩ := exists_flipTransform_apply_eq hD P
  have := Q.isDiscreteValuationRing_localRing
  have : ValuationRing (Z.presheaf.stalk (fp P.genericPoint)) := by rw [hP]; infer_instance
  have : ValuationRing (Z.presheaf.stalk (fm Pm.genericPoint)) := by rw [hPm]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hbp.functionFieldMap_bijective
    P.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing fm hbm.functionFieldMap_bijective
    Pm.genericPoint
  change P.ordForm (pullbackRationalPluriForms sZ fp τ) = flipTransform fm fp K P
  rw [hfl K, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp
      hbp.functionFieldMap_bijective hd P Q hP τ,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fm
      hbm.functionFieldMap_bijective hd Pm Q hPm τ, hK Pm]
  rfl

end StepDiagram

/-! ### Log discrepancies from Cartier multiples -/

section LogDiscrepancy

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The log discrepancy of a valuation is unique. -/
private theorem isValuationLogDiscrepancy_eq {B : QDivisor X}
    {ξ : Valuation X.functionField ℤᵐ⁰} {a a' : ℝ} (h : IsValuationLogDiscrepancy sX B ξ a)
    (h' : IsValuationLogDiscrepancy sX B ξ a') : a = a' := by
  obtain ⟨n, D, -, hv, h⟩ := h
  obtain ⟨n', D', -, hv', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hv.trans hv'.symm)

/-- **The log discrepancy from a Cartier multiple.** Let `div(ω)` be a canonical divisor of a
normal variety `X` with `m (div(ω) + B) = C` a Cartier divisor, and `(Y, f, E)` a divisor over `X`
with `f` proper and `f^* C = L`. Then `a(E, X, B) = 1 + ord_E(f^* ω) - m⁻¹ coeff_E L`. -/
private theorem isLogDiscrepancy_of_isPullback [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n) {B : QDivisor X} {m : ℕ} (hm : 0 < m)
    {C : Divisor X}
    (hC : Divisor.toQDivisor C = (m : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + B))
    (hCc : C.IsCartier) {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X)
    [IsProper f] (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : MMP.Mori.PrimeDivisor Y)
    {hB : ∀ T : irreducibleComponents Y, f (componentGenericPoint Y T) ∉ C.supp}
    {L : Divisor Y} (hL : C.IsPullback f hB L) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) ⟨Y, f, hY, hf, E⟩
      (1 + ((⟨Y, f, hY, hf, E⟩ : DivisorOver ℂ sX).ordPullback ω : ℝ) -
        (m : ℝ)⁻¹ * (L.coeff E : ℝ)) :=
  ⟨hX, ‹IsProper f›, ω, hω, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, 1, fun _ => (m : ℝ)⁻¹,
    fun _ => C, fun _ => L, fun _ => hCc, fun Γ => ordForm_add_coeff_eq ω B hm hC Γ,
    fun _ => ⟨_, hL⟩, by simp⟩

end LogDiscrepancy

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose local
equations are regular (algebraic Hartogs), so their pull-backs have nonnegative order. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    exact_mod_cast h2 ▸ mul_nonneg hmq.le (hA P)
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 : (D' E : ℚ) = A.cartierIndex hAq * B E :=
    (by simpa using congrArg (· E) hD' :
      Divisor.toQDivisor D' E = A.cartierIndex hAq * B E)
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  exact nonneg_of_mul_nonneg_right (h1 ▸ h0') hmq

/-! ### The comparison -/

section Comparison

/-- `m₁ Λ⁻ - m₀ Λ⁺` is the integral divisor `m₀ m₁ (H⁻ - H⁺)` when `Λ⁻ = m₀ H⁻`, `Λ⁺ = m₁ H⁺`. -/
private theorem toQDivisor_zsmul_add_neg_zsmul {Y : Scheme.{0}} {Lu Lv : Divisor Y}
    {Hm Hp : QDivisor Y} {m₀ m₁ : ℕ} (hLu : Divisor.toQDivisor Lu = (m₀ : ℤ) • Hm)
    (hLv : Divisor.toQDivisor Lv = (m₁ : ℤ) • Hp) :
    Divisor.toQDivisor ((m₁ : ℤ) • Lu + (-(m₀ : ℤ)) • Lv) = ((m₀ * m₁ : ℕ) : ℤ) • (Hm - Hp) := by
  rw [map_add, map_zsmul, map_zsmul, hLu, hLv, smul_smul, smul_smul, smul_sub]
  push_cast
  rw [neg_mul, neg_smul, mul_comm (m₁ : ℤ) m₀, ← sub_eq_add_neg]

/-- A divisor `(W, w, E)` over `G`, seen over `X` through a birational `g : G ⟶ X`, has
valuation `ord_E` read on `k(X)` through `g`. -/
private theorem valuation_mk_comp {X G : Scheme.{0}} [IsIntegral X] [IsIntegral G]
    {s : X ⟶ Spec (.of ℂ)} {t : G ⟶ Spec (.of ℂ)} (g : G ⟶ X) [IsDominant g]
    (D : DivisorOver ℂ t)
    (hW : IsNormalVariety ℂ ((D.f ≫ g) ≫ s)) (hb : IsBirationalMorphism (D.f ≫ g)) :
    (⟨D.Y, D.f ≫ g, hW, hb, D.E⟩ : DivisorOver ℂ s).valuation =
      D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

/-- The graph divisor is `ℚ`-Cartier: `m₀ m₁ H = m₁ u^*(m₀ D⁻) - m₀ v^*(m₁ D⁺)`. -/
private theorem isQCartier_of_isGraphDivisor (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) :
    H.IsQCartier := by
  have hD := h.isFourfoldStepDiagram
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₁, hm₁, DXp, hDXp, hDXpc⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Lu, hLu, hLupb⟩ := hHm m₀ hm₀ DX hDX hDXc
  obtain ⟨Lv, hLv, hLvpb⟩ := hHp m₁ hm₁ DXp hDXp hDXpc
  exact ⟨((m₀ * m₁ : ℕ) : ℤ), by exact_mod_cast (Nat.mul_pos hm₀ hm₁).ne', _,
    toQDivisor_zsmul_add_neg_zsmul hLu hLv,
    ((hLupb.isCartier hDXc).zsmul _).add ((hLvpb.isCartier hDXpc).zsmul _)⟩

/-- **The comparison of log discrepancies on a model over the graph.** For a proper divisor
`(W, w, E)` over `G` and the pull-back `H' = w^*H`, the valuation `ord_E` has log discrepancies
`a⁻` over `(X⁻, B⁻)` and `a⁺` over `(X⁺, B⁺)`, and `a⁺ - a⁻ = coeff_E H'`: both are computed
with the one form `(uw)^* (f⁻)^* τ = (vw)^* (f⁺)^* τ`, so they differ by the coefficient along
`E` of `(uw)^* D⁻ - (vw)^* D⁺ = w^* H`. -/
private theorem exists_isValuationLogDiscrepancy_sub_eq
    (h : IsGraphDivisor (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp u v H)
    (D : DivisorOver ℂ (u ≫ fm ≫ sZ)) (hDp : IsProper D.f)
    (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
    (H' : QDivisor D.Y)
    (hH' : haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      H.IsPullback D.f hH H') :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ am ap : ℝ,
      IsValuationLogDiscrepancy (fm ≫ sZ) B (D.valuation.comap (functionFieldMap u)) am ∧
      IsValuationLogDiscrepancy (fp ≫ sZ) (flipTransform fm fp B)
        (D.valuation.comap (functionFieldMap v)) ap ∧
      ap - am = (H'.coeff D.E : ℝ) := by

  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, hHeq⟩ := h.exists_pullback
  -- the varieties and morphisms of the step
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  have hXm := hD.isNormalVariety_minus
  have hXp := hD.isNormalVariety_plus
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  haveI := isProper_plus_of_isNormalizedGraph hG
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isBirationalMorphism_plus
  have hbu := hG.isBirationalMorphism_minus
  have hbv := hG.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI := hbu.isDominant
  haveI := hbv.isDominant
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace u
  -- the canonical divisors `K = div(f⁻^* τ)` and `K⁺ = div(f⁺^* τ)`
  obtain ⟨n, hK⟩ := hD.isCanonicalDivisor
  have hnm : topologicalKrullDim Xm = n := hK.topologicalKrullDim_eq
  have hnZ : topologicalKrullDim Z = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fm ≫ sZ) hbm).trans hnm
  have hnp : topologicalKrullDim Xp = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (fp ≫ sZ) hbp).symm.trans
      hnZ
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXm hK
  obtain ⟨τ, rfl⟩ := exists_pullbackRationalPluriForms_eq fm hbm.functionFieldMap_bijective hd ω
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    apply hω0
    letI := functionFieldAlgebra sZ
    letI := functionFieldAlgebra (fm ≫ sZ)
    letI := functionFieldMapAlgebra fm
    haveI := isScalarTower_functionFieldMap sZ fm
    change pullbackForms (K := Z.functionField) (K' := Xm.functionField) 1 0 = 0
    rw [pullbackForms]
    split_ifs
    · rw [pullbackFormsAlong]
      simp
    · rfl
  have hωp0 : pullbackRationalPluriForms sZ fp τ ≠ 0 :=
    pullbackRationalPluriForms_ne_zero fp hbp.functionFieldMap_bijective hd hτ0
  have hdivm : divisorOfForm (pullbackRationalPluriForms sZ fm τ) = K :=
    Finsupp.ext hω
  have hdivp := divisorOfForm_eq_flipTransform hD hd τ hω
  have hKm : (divisorOfForm (pullbackRationalPluriForms sZ fm τ)).IsCanonicalDivisor
      (fm ≫ sZ) n := hdivm ▸ hK
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor (fp ≫ sZ) hXp hnp
  have hKp : (divisorOfForm (pullbackRationalPluriForms sZ fp τ)).IsCanonicalDivisor
      (fp ≫ sZ) n := hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXp hK₀ hωp0)
  -- Cartier multiples of `D^±` and their pull-backs to `G`
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hD.isQCartier_minus.exists_pos
  obtain ⟨m₁, hm₁, DXp, hDXp, hDXpc⟩ := hD.isQCartier_plus.exists_pos
  obtain ⟨Lu, hLu, hLupb⟩ := hHm m₀ hm₀ DX hDX hDXc
  obtain ⟨Lv, hLv, hLvpb⟩ := hHp m₁ hm₁ DXp hDXp hDXpc
  have hLuc := hLupb.isCartier hDXc
  have hLvc := hLvpb.isCartier hDXpc
  rw [← hdivm] at hDX
  rw [← hdivp] at hDXp
  have hN : 0 < m₀ * m₁ := Nat.mul_pos hm₀ hm₁
  have hCH := toQDivisor_zsmul_add_neg_zsmul hLu hLv
  rw [← hHeq] at hCH
  have hCHc := (hLuc.zsmul (m₁ : ℤ)).add (hLvc.zsmul (-(m₀ : ℤ)))
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsProper D.f := hDp
  haveI : CompactSpace D.Y :=
    (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  -- `W = D.Y` as a divisor over `X⁻` and over `X⁺`
  have hWm : IsNormalVariety ℂ ((D.f ≫ u) ≫ fm ≫ sZ) := by
    rw [Category.assoc]
    exact D.isNormalVariety
  have hWp : IsNormalVariety ℂ ((D.f ≫ v) ≫ fp ≫ sZ) := by
    rw [Category.assoc, ← Category.assoc v, ← hG.comp_eq, Category.assoc]
    exact D.isNormalVariety
  have hbwu : IsBirationalMorphism (D.f ≫ u) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational u D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbu)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  have hbwv : IsBirationalMorphism (D.f ≫ v) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational v D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbv)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  haveI := hbwu.isDominant
  haveI := hbwv.isDominant
  -- the pull-backs of the Cartier multiples to `W`
  obtain ⟨Lw, hLw⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hLuc
  obtain ⟨Lvw, hLvw⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hLvc
  have h₁ := isPullback_comp hLupb hLw
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ u) DX)
  have h₂ := isPullback_comp hLvpb hLvw
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ v) DXp)
  -- the pull-back of `(m₀ m₁) H`
  obtain ⟨D'', hD'', hD''pb⟩ := hH' _ hN _ hCH hCHc
  have hCHpb : ((m₁ : ℤ) • Lu + (-(m₀ : ℤ)) • Lv : Divisor G).IsPullback D.f
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _)
      ((m₁ : ℤ) • Lw + (-(m₀ : ℤ)) • Lvw) :=
    Divisor.IsPullback.add (hLuc.zsmul _) (hLvc.zsmul _) _
      (hLw.zsmul hLuc _ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _))
      (hLvw.zsmul hLvc _ (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f _))
  have hD''eq : D'' = (m₁ : ℤ) • Lw + (-(m₀ : ℤ)) • Lvw := hD''pb.eq hCHc hCHpb
  have hcoef : ((m₀ : ℚ) * m₁) * H'.coeff D.E = m₁ * Lw.coeff D.E - m₀ * Lvw.coeff D.E := by
    have := congrArg (fun F : QDivisor D.Y => F.coeff D.E) hD''
    simp only [hD''eq, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul] at this
    push_cast at this
    linarith
  -- the two log discrepancies
  have ham := isLogDiscrepancy_of_isPullback hXm hω0 hKm hm₀ hDX hDXc (D.f ≫ u) hWm hbwu D.E h₁
  have hap := isLogDiscrepancy_of_isPullback hXp hωp0 hKp hm₁ hDXp hDXpc (D.f ≫ v) hWp hbwv
    D.E h₂
  refine ⟨_, _, ⟨n, _, inferInstance, ?_, ham⟩, ⟨n, _, inferInstance, ?_, hap⟩, ?_⟩
  · exact valuation_mk_comp u D hWm hbwu
  · exact valuation_mk_comp v D hWp hbwv
  · have hord : D.E.ordForm (pullbackRationalPluriForms (fm ≫ sZ) (D.f ≫ u)
          (pullbackRationalPluriForms sZ fm τ)) =
        D.E.ordForm (pullbackRationalPluriForms (fp ≫ sZ) (D.f ≫ v)
          (pullbackRationalPluriForms sZ fp τ)) := by
      rw [pullbackRationalPluriForms_comp fm (D.f ≫ u) hbm.functionFieldMap_bijective
          hbwu.functionFieldMap_bijective hd,
        pullbackRationalPluriForms_comp fp (D.f ≫ v) hbp.functionFieldMap_bijective
          hbwv.functionFieldMap_bijective hd]
      exact ordForm_pullbackRationalPluriForms_congr
        (by rw [Category.assoc, Category.assoc, hG.comp_eq]) D.E τ
    change 1 + (D.E.ordForm (pullbackRationalPluriForms (fp ≫ sZ) (D.f ≫ v)
          (pullbackRationalPluriForms sZ fp τ)) : ℝ) - (m₁ : ℝ)⁻¹ * (Lvw.coeff D.E : ℝ) -
        (1 + (D.E.ordForm (pullbackRationalPluriForms (fm ≫ sZ) (D.f ≫ u)
          (pullbackRationalPluriForms sZ fm τ)) : ℝ) - (m₀ : ℝ)⁻¹ * (Lw.coeff D.E : ℝ)) = _
    rw [hord]
    have hcoefR : ((m₀ : ℝ) * m₁) * (H'.coeff D.E : ℝ) =
        m₁ * (Lw.coeff D.E : ℝ) - m₀ * (Lvw.coeff D.E : ℝ) := by exact_mod_cast hcoef
    have hm₀R : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
    have hm₁R : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁.ne'
    field_simp
    linear_combination -hcoefR

end Comparison

/-- **Discrepancy comparison on the normalized graph.** For a valuation `ξ` of `k(G)` restricting
to a normalized divisorial valuation of `k(X⁻)`, `ξ(H) = c ≥ 0` is computed on any proper
realization of `ξ` over `G`, both log discrepancies exist, and
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = c`. -/
private theorem exists_isValuationLogDiscrepancy_sub_eq_coeff {Xm Xp Z G : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp]
    [IsNormal Xp] [IsLocallyNoetherian G] [IsNormal G] [IsIntegral G]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
    {H : QDivisor G} (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H)
    (ξ : Valuation G.functionField (WithZero (Multiplicative ℤ)))
    (hξ : haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sXm (ξ.comap (functionFieldMap u))) :
    haveI := h.isNormalizedGraph.isBirationalMorphism_minus.isDominant
    haveI := h.isNormalizedGraph.isBirationalMorphism_plus.isDominant
    ∃ c : ℚ, 0 ≤ c ∧
      (∃ (D : DivisorOver ℂ (u ≫ sXm)), IsProper D.f ∧ D.valuation = ξ ∧
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∃ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' ∧ H'.coeff D.E = c) ∧
      (∀ D : DivisorOver ℂ (u ≫ sXm), IsProper D.f → D.valuation = ξ →
        haveI := D.isLocallyNoetherian
        haveI := D.isNormal
        ∀ (hH : ∀ T : irreducibleComponents D.Y, D.f (componentGenericPoint D.Y T) ∉ H.supp)
          (H' : QDivisor D.Y), H.IsPullback D.f hH H' → H'.coeff D.E = c) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) a) ∧
      (∃ a : ℝ, IsValuationLogDiscrepancy sXp (flipTransform fm fp B)
        (ξ.comap (functionFieldMap v)) a) ∧
      ∀ am ap : ℝ, IsValuationLogDiscrepancy sXm B (ξ.comap (functionFieldMap u)) am →
        IsValuationLogDiscrepancy sXp (flipTransform fm fp B) (ξ.comap (functionFieldMap v)) ap →
          ap - am = c := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  have hHq := isQCartier_of_isGraphDivisor h
  have hH0 : 0 ≤ H := GraphDivisorEffective.nonneg_of_isGraphDivisor h
  have e₁ := hD.comp_eq_minus
  have e₂ := hD.comp_eq_plus
  subst e₁ e₂
  have hXm := hD.isNormalVariety_minus
  haveI := hXm.1
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  have hbu := hG.isBirationalMorphism_minus
  haveI := hbu.isDominant
  have hGu : IsNormalVariety ℂ (u ≫ fm ≫ sZ) :=
    ⟨(isVariety_iff ℂ (u ≫ fm ≫ sZ)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  -- a realization of `ξ` over `G`
  obtain ⟨D₁, -, hv₁⟩ := hξ
  obtain ⟨D₀, hD₀p, rfl⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq hGu (𝟙 Xm) u
    (isBirationalMorphism_of_isIso _) hbu inferInstance (Category.id_comp _) rfl D₁ ξ (by
      rw [hv₁]
      ext t
      simp [MMP.Mori.functionFieldMap_id_apply])
  haveI := D₀.isIntegral
  haveI := D₀.isNormal
  haveI := D₀.isLocallyNoetherian
  haveI := D₀.isDominant
  haveI : CompactSpace D₀.Y :=
    (D₀.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hH₀ : ∀ T : irreducibleComponents D₀.Y, D₀.f (componentGenericPoint D₀.Y T) ∉ H.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D₀.f H
  have hH₀pb := QDivisor.isPullback_pullback hHq hH₀
  obtain ⟨am₀, ap₀, ham₀, hap₀, hdiff₀⟩ :=
    exists_isValuationLogDiscrepancy_sub_eq h D₀ hD₀p hH₀ _ hH₀pb
  refine ⟨(H.pullback hHq hH₀).coeff D₀.E, nonneg_of_isPullback hH0 hHq hH₀pb D₀.E,
    ⟨D₀, hD₀p, rfl, hH₀, _, hH₀pb, rfl⟩, ?_, ⟨am₀, ham₀⟩, ⟨ap₀, hap₀⟩, ?_⟩
  · intro D hDp hDv hH' H' hpb
    obtain ⟨am, ap, ham, hap, hdiff⟩ := exists_isValuationLogDiscrepancy_sub_eq h D hDp hH' H' hpb
    rw [hDv] at ham hap
    rw [isValuationLogDiscrepancy_eq ham ham₀, isValuationLogDiscrepancy_eq hap hap₀,
      hdiff₀] at hdiff
    exact_mod_cast hdiff.symm
  · intro am ap ham hap
    rw [isValuationLogDiscrepancy_eq ham ham₀, isValuationLogDiscrepancy_eq hap hap₀, hdiff₀]

end GraphComparison

end

/-! ### The support of the graph divisor -/

section Support

/-- A closed subset of a quasi-sober space all of whose points are closed has dimension at most
zero. -/
private theorem topologicalKrullDim_nonpos_of_forall_isClosed {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {T : Set X} (hT : IsClosed T) (h : ∀ x ∈ T, IsClosed ({x} : Set X)) :
    topologicalKrullDim T ≤ 0 := by
  haveI : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  haveI : T1Space T := ⟨fun x => by
    have := (h x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ T)))
    convert this using 1
    ext y; simp [Subtype.ext_iff]⟩
  have hsing : ∀ s : IrreducibleCloseds T, ∃ x, (s : Set T) = {x} := fun s => by
    obtain ⟨x, hx⟩ := QuasiSober.sober s.isIrreducible s.isClosed
    exact ⟨x, by rw [← hx.def, closure_singleton]⟩
  unfold topologicalKrullDim
  rw [Order.krullDim_nonpos_iff_forall_isMax]
  intro s t hst
  obtain ⟨x, hx⟩ := hsing s
  obtain ⟨y, hy⟩ := hsing t
  have hxs : x ∈ (s : Set T) := by rw [hx]; rfl
  have hxy : x ∈ (t : Set T) := hst hxs
  rw [hy] at hxy
  change (t : Set T) ⊆ s
  rw [hx, hy, Set.singleton_subset_iff, ← hxy]; rfl

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

/-- **Support of the graph divisor.** Every point of the normalized graph lying over the bad
locus `Σ` of the base lies in `Supp H`. For a closed point `z ∈ Σ`, the negativity lemma makes
`g⁻¹(z)` either contained in `Supp H` or disjoint from it; in the second case `g⁻¹(z)` contains no
proper curve (on such a curve `H` would have degree zero while `-H` is `g`-ample), so the fibres of
`f⁻` and `f⁺` over `z` would be finite, which is impossible over `Σ`. Closed points are dense in
the closed set `g⁻¹(Σ)`. -/
private theorem mem_supp_of_map_mem_badLocusBase
    (h : IsGraphDivisor sXm sZ sXp K B fm fp u v H) (hH0 : 0 ≤ H) (hHq : H.IsQCartier)
    (y : G) (hy : fm (u y) ∈ badLocusBase fm fp) : y ∈ H.supp := by
  have hD := h.isFourfoldStepDiagram
  have hG := h.isNormalizedGraph
  have e₁ := hD.comp_eq_minus
  have e₂ := hD.comp_eq_plus
  subst e₁ e₂
  haveI := hG.isIntegral
  have hZ := hD.isNormalVariety_target
  haveI := hD.isProjectiveVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper fp := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  haveI := isProper_plus_of_isNormalizedGraph hG
  have hbm := hD.isBirationalMorphism_minus
  have hbu := hG.isBirationalMorphism_minus
  have hbv := hG.isBirationalMorphism_plus
  haveI := hbu.isDominant
  haveI := hbv.isDominant
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace u
  have hGv : IsNormalVariety ℂ (u ≫ fm ≫ sZ) :=
    ⟨(isVariety_iff ℂ (u ≫ fm ≫ sZ)).mpr
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  haveI := hGv.1
  haveI : QuasiCompact (u ≫ fm ≫ sZ) := hGv.1.toQuasiCompact
  haveI : LocallyOfFiniteType (u ≫ fm ≫ sZ) := hGv.1.toLocallyOfFiniteType
  haveI : IsProper (u ≫ fm ≫ sZ) := inferInstance
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace (u ≫ fm ≫ sZ)
  have hgb : IsBirationalMorphism (u ≫ fm) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm u
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbm)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbu)
  have hamp := h.hasRelativelyAmpleMultiple_neg
  have hnHq := isQCartier_neg hHq
  have hnef : (-H).IsRelativelyNef (u ≫ fm ≫ sZ) (u ≫ fm) :=
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg _ hnHq fun C hC =>
      (intersectionNumber_pos_of_hasRelativelyAmpleMultiple _ hamp hnHq C hC).le
  have hu : Function.Surjective u := (inferInstance : Surjective u).surj
  have hv : Function.Surjective v := (inferInstance : Surjective v).surj
  -- the closed points of `g⁻¹(Σ)` lie in `Supp H`
  have key : ∀ y' : G, IsClosed ({y'} : Set G) → (u ≫ fm) y' ∈ badLocusBase fm fp →
      y' ∈ H.supp := by
    intro y' hy'c hy'B
    set z := (u ≫ fm) y' with hz
    have hzc : IsClosed ({z} : Set Z) := by
      have := (u ≫ fm).isClosedMap _ hy'c
      rwa [Set.image_singleton] at this
    have hFcl : IsClosed ((u ≫ fm).base ⁻¹' {z}) := hzc.preimage (u ≫ fm).continuous
    rcases MMP.Mori.QDivisor.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg
      ℂ sZ (u ≫ fm ≫ sZ) hZ hGv (u ≫ fm) (Category.assoc _ _ _) hgb hHq
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hH0) hnef z with hs | hd
    · exact hs rfl
    exfalso
    -- every point of the fibre `g⁻¹(z)` is closed: otherwise it contains a contracted curve
    -- disjoint from `Supp H`, on which `-H` is positive and `H` is zero
    have hcl : ∀ w ∈ (u ≫ fm).base ⁻¹' {z}, IsClosed ({w} : Set G) := by
      intro w hw
      by_contra hwc
      obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
        (⟨w, subset_closure rfl⟩ : (closure ({w} : Set G)).Nonempty)
        isClosed_closure.isLocallyClosed
      have hwp : w ⤳ p := specializes_iff_mem_closure.mpr hp
      have hpw : w ∉ ({p} : Set G) := fun e => hwc (by
        rw [Set.mem_singleton_iff.mp e]; exact mem_closedPoints_iff.mp hpc)
      obtain ⟨y'', hwy, -, -, hC⟩ := exists_isProperCurve_of_specializes (u ≫ fm ≫ sZ) hwp
        (mem_closedPoints_iff.mp hpc) (mem_closedPoints_iff.mp hpc) rfl hpw
      let C : ProperCurve (u ≫ fm ≫ sZ) := ⟨y'', hC⟩
      have hCF : closure {y''} ⊆ (u ≫ fm).base ⁻¹' {z} :=
        closure_minimal (Set.singleton_subset_iff.mpr (hwy.mem_closed hFcl hw)) hFcl
      have hCg : C.IsContractedBy (u ≫ fm) := fun _ hx =>
        (hCF hx).trans (hCF (subset_closure rfl)).symm
      have hy''S : y'' ∉ H.supp := fun hm =>
        Set.disjoint_left.mp hd (hCF (subset_closure rfl)) hm
      obtain ⟨-, hiff⟩ := intersectionNumber_nonneg_and_eq_zero_iff (u ≫ fm ≫ sZ) H hHq hH0 C
        hy''S
      have h0 := hiff.mpr fun x hx hxS =>
        Set.disjoint_left.mp hd (hCF (specializes_iff_mem_closure.mp hx)) hxS
      have hpos := intersectionNumber_pos_of_hasRelativelyAmpleMultiple _ hamp hnHq C hCg
      have hBB := QDivisor.intersectionNumber_add' ℂ (u ≫ fm ≫ sZ) C.ι C.dim_le H (-H) hHq hnHq
        (by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero)
      rw [MMP.Fourfold.intersectionNumber_congr (u ≫ fm ≫ sZ) C.ι C.dim_le _
        QDivisor.isQCartier_zero (add_neg_cancel H), MMP.Fourfold.intersectionNumber_zero] at hBB
      linarith
    -- so the fibres of `f⁻` and `f⁺` over `z` consist of closed points
    have hm : ∀ x ∈ fm.base ⁻¹' {z}, IsClosed ({x} : Set Xm) := by
      intro x hx
      obtain ⟨w, rfl⟩ := hu x
      simpa using u.isClosedMap _ (hcl w (by simpa using hx))
    have hp : ∀ x ∈ fp.base ⁻¹' {z}, IsClosed ({x} : Set Xp) := by
      intro x hx
      obtain ⟨w, rfl⟩ := hv x
      have hw : w ∈ (u ≫ fm).base ⁻¹' {z} := by
        rw [hG.comp_eq]; simpa using hx
      simpa using v.isClosedMap _ (hcl w hw)
    rcases hD.pos_dim_fibre_of_mem_badLocusBase hzc hy'B with h1 | h1
    · exact (not_lt.mpr (topologicalKrullDim_nonpos_of_forall_isClosed
        (hzc.preimage fm.continuous) hm)) h1
    · exact (not_lt.mpr (topologicalKrullDim_nonpos_of_forall_isClosed
        (hzc.preimage fp.continuous) hp)) h1
  have hT : IsClosed ((u ≫ fm).base ⁻¹' (badLocusBase fm fp : Set Z)) :=
    (badLocusBase fm fp).isClosed.preimage (u ≫ fm).continuous
  have hsub : (u ≫ fm).base ⁻¹' (badLocusBase fm fp : Set Z) ⊆ H.supp := by
    rw [← JacobsonSpace.closure_inter_closedPoints hT]
    refine closure_minimal ?_ H.supp.isClosed
    rintro y' ⟨hy'T, hy'c⟩
    exact key y' (mem_closedPoints_iff.mp hy'c) hy'T
  exact hsub (by simpa using hy)

/-- **The pull-back of an effective `ℚ`-Cartier divisor is positive over its support.** If
`f(η_E) ∈ Supp A`, then `E` occurs in `f^*(mA)` (`Supp f^*(mA) = f⁻¹ Supp(mA)`), so the
coefficient of `E` in the effective `f^*A` is positive. -/
private theorem coeff_pos_of_isPullback_of_mem_supp {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) (hB0 : 0 ≤ B) (E : MMP.Mori.PrimeDivisor Y)
    (hE : f E.genericPoint ∈ A.supp) : 0 < B.coeff E := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀e : DivisorWithCoeffs.IsEffective D₀ := by
    intro P
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    have : (0:ℚ) ≤ (D₀ P : ℚ) := h2 ▸ mul_nonneg hmq.le (hA P)
    exact_mod_cast this
  have hsupp : D₀.supp = A.supp :=
    QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD₀
  have hmem : E.genericPoint ∈ (D'.supp : Set Y) := by
    rw [MMP.Flips.supp_eq_preimage_supp_of_isPullback hD₀c hD₀e hp, Set.mem_preimage, hsupp]
    exact hE
  obtain ⟨P, hP0, hEP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hEP
  have h1 : (D' P : ℚ) = A.cartierIndex hAq * B P :=
    (by simpa using congrArg (· P) hD' :
      Divisor.toQDivisor D' P = A.cartierIndex hAq * B P)
  have hne : B.coeff P ≠ 0 := by
    intro h0
    apply hP0
    have : (D' P : ℚ) = 0 := by rw [h1]; simp [DivisorWithCoeffs.coeff] at h0 ⊢; simp [h0]
    exact_mod_cast this
  exact lt_of_le_of_ne (hB0 P) (Ne.symm hne)

end Support

/-! ### The strict comparison along a step -/

section Step

open MMP.Fourfold.StepSequence

/-- A valuation is determined by its restriction along a bijective map of function fields. -/
private theorem valuation_eq_of_comap_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {f : X ⟶ Y} [IsDominant f] (hf : Function.Bijective (functionFieldMap f))
    {v w : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : v.comap (functionFieldMap f) = w.comap (functionFieldMap f)) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hf.2 t
  exact DFunLike.congr_fun h s

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem eq_of_corresponds (S : StepSequence) :
    ∀ (i : ℕ) {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
      {η η' : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))},
      S.Corresponds i ξ η → S.Corresponds i ξ η' → η = η'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨ζ, hζ, hη⟩, ⟨ζ', hζ', hη'⟩ => by
    obtain rfl := eq_of_corresponds S i hζ hζ'
    exact valuation_eq_of_comap_eq
      (S.isFourfoldStepDiagram i).isBirationalMorphism_plus.functionFieldMap_bijective
      (hη.trans hη'.symm)

/-- **Strict discrepancy comparison along a step** (the graph comparison and its strictness).
Let `η` be a normalized divisorial valuation of `k(X_i)` and `η'` the corresponding valuation of
`k(X_{i+1})`, with log discrepancies `a = a_i(η)` and `a' = a_{i+1}(η')`. Then `a ≤ a'`, and
`a < a'` as soon as the centre of `η` on `X_i` lies in `W_i⁻` or the centre of `η'` on `X_{i+1}`
lies in `W_i⁺`. -/
private theorem le_and_lt_of_isTransportedValuation (S : StepSequence) (i : ℕ)
    {η : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))}
    {η' : Valuation (S.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (htr : S.IsTransportedValuation i η η')
    (hη : MMP.Intersection.IsNormalizedDivisorialValuation ℂ (S.sX i) η)
    {a a' : ℝ} (ha : S.IsLogDiscrepancyAt i η a) (ha' : S.IsLogDiscrepancyAt (i + 1) η' a') :
    a ≤ a' ∧
      ((∃ D : DivisorOver ℂ (S.sX i), D.valuation = η ∧
          D.f D.E.genericPoint ∈ S.badLocusMinusAt i) ∨
        (∃ D : DivisorOver ℂ (S.sX (i + 1)), D.valuation = η' ∧
          D.f D.E.genericPoint ∈ S.badLocusPlusAt i) → a < a') := by
  have hD := S.isFourfoldStepDiagram i
  obtain ⟨G, _, _, u, v, H, hH⟩ := exists_isGraphDivisor hD
  have hG := hH.isNormalizedGraph
  haveI := hG.isIntegral
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  let e := RingEquiv.ofBijective (functionFieldMap v)
    hG.isBirationalMorphism_plus.functionFieldMap_bijective
  let ξ := η'.comap e.symm.toRingHom
  have hξv : ξ.comap (functionFieldMap v) = η' := by
    ext t
    simp only [ξ, Valuation.comap_apply]
    congr 1
    exact e.symm_apply_apply t
  have htr' : S.IsTransportedValuation i (ξ.comap (functionFieldMap u)) η' := by
    ext t
    rw [← hξv]
    simp only [Valuation.comap_apply]
    rw [← functionFieldMap_comp_apply, ← functionFieldMap_comp_apply]
    simp only [hG.comp_eq]
  have hξu : ξ.comap (functionFieldMap u) = η :=
    valuation_eq_of_comap_eq hD.isBirationalMorphism_minus.functionFieldMap_bijective
      (htr'.symm.trans htr)
  have hap : IsValuationLogDiscrepancy (S.sX (i + 1)) (flipTransform (S.f i) (S.fp i) (S.B i))
      (ξ.comap (functionFieldMap v)) a' := by
    rw [hξv, ← S.B_eq i]; exact ha'
  have hξ : MMP.Intersection.IsNormalizedDivisorialValuation ℂ (S.sX i)
      (ξ.comap (functionFieldMap u)) := hξu ▸ hη
  obtain ⟨c, hc, ⟨D₀, hD₀p, hD₀v, hH₀, H', hpb, hc'⟩, -, -, -, hdiff⟩ :=
    GraphComparison.exists_isValuationLogDiscrepancy_sub_eq_coeff hH ξ hξ
  have ham : IsValuationLogDiscrepancy (S.sX i) (S.B i) (ξ.comap (functionFieldMap u)) a :=
    hξu ▸ ha
  have h1 := hdiff a a' ham hap
  have hc0 : (0 : ℝ) ≤ c := by exact_mod_cast hc
  refine ⟨by linarith, fun hbad => ?_⟩
  haveI := D₀.isIntegral
  haveI := D₀.isLocallyNoetherian
  haveI := D₀.isNormal
  haveI := D₀.isDominant
  haveI : IsProper D₀.f := hD₀p
  haveI : IsProper (S.f i) := isProper_of_isProjectiveMorphism _ hD.isProjectiveMorphism_minus
  haveI : IsProper (S.fp i) := hD.isProper_plus
  haveI := isProper_minus_of_isNormalizedGraph hG
  haveI := isProper_plus_of_isNormalizedGraph hG
  have hH0 : 0 ≤ H := GraphDivisorEffective.nonneg_of_isGraphDivisor hH
  have hHq := GraphComparison.isQCartier_of_isGraphDivisor hH
  -- the centre of `ξ` on `G` lies over `Σ_i`
  have hy : S.f i (u (D₀.f D₀.E.genericPoint)) ∈ badLocusBase (S.f i) (S.fp i) := by
    rcases hbad with ⟨D, hDv, hDW⟩ | ⟨D, hDv, hDW⟩
    · have hW : IsNormalVariety ℂ ((D₀.f ≫ u) ≫ S.sX i) := by
        rw [Category.assoc]; exact D₀.isNormalVariety
      have hb : IsBirationalMorphism (D₀.f ≫ u) :=
        MMP.Mori.isBirationalMorphism_comp_of_isBirational u D₀.f
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
            hG.isBirationalMorphism_minus)
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D₀.isBirationalMorphism)
      have hv1 := GraphComparison.valuation_mk_comp u D₀ hW hb
      rw [hD₀v, hξu, ← hDv] at hv1
      have hc1 := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq
        hD.isNormalVariety_minus hv1
      have : (D₀.f ≫ u) D₀.E.genericPoint = D.f D.E.genericPoint := hc1
      rw [Scheme.Hom.comp_apply] at this
      rw [this]
      exact hDW
    · have hW : IsNormalVariety ℂ ((D₀.f ≫ v) ≫ S.sX (i + 1)) := by
        have h1 : v ≫ S.sX (i + 1) = u ≫ S.sX i := by
          rw [← hD.comp_eq_plus, ← hD.comp_eq_minus, ← Category.assoc, ← Category.assoc,
            hG.comp_eq]
        rw [Category.assoc, h1]; exact D₀.isNormalVariety
      have hb : IsBirationalMorphism (D₀.f ≫ v) :=
        MMP.Mori.isBirationalMorphism_comp_of_isBirational v D₀.f
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
            hG.isBirationalMorphism_plus)
          (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D₀.isBirationalMorphism)
      have hv1 := GraphComparison.valuation_mk_comp v D₀ hW hb
      rw [hD₀v, hξv, ← hDv] at hv1
      have hc1 := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq
        hD.isNormalVariety_plus hv1
      have : (D₀.f ≫ v) D₀.E.genericPoint = D.f D.E.genericPoint := hc1
      rw [Scheme.Hom.comp_apply] at this
      have hcomm : S.f i (u (D₀.f D₀.E.genericPoint)) =
          S.fp i (v (D₀.f D₀.E.genericPoint)) := by
        show (u ≫ S.f i) (D₀.f D₀.E.genericPoint) = (v ≫ S.fp i) (D₀.f D₀.E.genericPoint)
        rw [hG.comp_eq]
      rw [hcomm, this]
      exact hDW
  have hmem := mem_supp_of_map_mem_badLocusBase hH hH0 hHq _ hy
  have hpos := coeff_pos_of_isPullback_of_mem_supp hH0 hHq hpb
    (GraphComparison.nonneg_of_isPullback hH0 hHq hpb) D₀.E hmem
  rw [hc'] at hpos
  have : (0 : ℝ) < c := by exact_mod_cast hpos
  linarith

/-- **The discrepancies of a stable place along the tail.** For `s ∈ I_∞`, the log discrepancies
`b_k = a_k(s_k)` of its transports `s_k` form a nondecreasing sequence, strictly increasing at
every step `k` at which the centre of `s_k` on `X_k` lies in `W_k⁻` or the centre of `s_{k+1}` on
`X_{k+1}` lies in `W_k⁺`. -/
private theorem exists_monotone_logDiscrepancy (S : StepSequence)
    {s : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    (hs : s ∈ S.stableLowDiscrepancySet) :
    ∃ (η : ∀ k, Valuation (S.X k).functionField (WithZero (Multiplicative ℤ))) (b : ℕ → ℝ),
      (∀ k, S.Corresponds k s (η k)) ∧ (∀ k, S.IsLogDiscrepancyAt k (η k) (b k)) ∧
        Monotone b ∧
        ∀ k, ((∃ D : DivisorOver ℂ (S.sX k), D.valuation = η k ∧
            D.f D.E.genericPoint ∈ S.badLocusMinusAt k) ∨
          (∃ D : DivisorOver ℂ (S.sX (k + 1)), D.valuation = η (k + 1) ∧
            D.f D.E.genericPoint ∈ S.badLocusPlusAt k)) → b k < b (k + 1) := by
  choose η hηI hηc using hs
  have hex : ∀ k, ∃ b : ℝ, S.IsLogDiscrepancyAt k (η k) b := fun k => by
    obtain ⟨-, b, hb, -⟩ := hηI k
    exact ⟨b, hb⟩
  choose b hb using hex
  have hstep : ∀ k, b k ≤ b (k + 1) ∧
      (((∃ D : DivisorOver ℂ (S.sX k), D.valuation = η k ∧
            D.f D.E.genericPoint ∈ S.badLocusMinusAt k) ∨
          (∃ D : DivisorOver ℂ (S.sX (k + 1)), D.valuation = η (k + 1) ∧
            D.f D.E.genericPoint ∈ S.badLocusPlusAt k)) → b k < b (k + 1)) := fun k => by
    obtain ⟨ζ, hζ, htr⟩ := hηc (k + 1)
    obtain rfl := eq_of_corresponds S k hζ (hηc k)
    obtain ⟨⟨D, hDp, hDv, -⟩, -⟩ := hηI k
    exact le_and_lt_of_isTransportedValuation S k htr ⟨D, hDp, hDv⟩ (hb k) (hb (k + 1))
  exact ⟨η, b, hηc, hb, monotone_nat_of_le_succ fun k => (hstep k).1, fun k => (hstep k).2⟩

end Step

/-! ### Attained generic mlds -/

section Attained

open MMP.Fourfold.StepSequence

private theorem isCanonicalDivisor_K (S : StepSequence) (i : ℕ) :
    (S.K i).IsCanonicalDivisor (S.sX i) 4 := by
  obtain ⟨m, hm⟩ := (S.isFourfoldStepDiagram i).isCanonicalDivisor
  have h := hm.topologicalKrullDim_eq
  rw [(S.isFourfoldStepDiagram i).dim_minus] at h
  obtain rfl : m = 4 := by exact_mod_cast h.symm
  exact hm

private theorem eq_four_of_isLogDiscrepancy (S : StepSequence) (i : ℕ) {n : ℕ}
    {B : RDivisor (S.X i)} {D : DivisorOver ℂ (S.sX i)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (S.sX i) n B D a) : n = 4 := by
  have e := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  rw [(S.isFourfoldStepDiagram i).dim_minus] at e
  exact_mod_cast e.symm

/-- The log discrepancies of `(X_i, B_i)` lie in `(1/m) ℤ` for a Cartier index `m` of
`K_i + B_i`. -/
private theorem exists_mul_eq_int_of_isLogDiscrepancy (S : StepSequence) (i : ℕ)
    (hklt : IsKltPair (S.sX i) (S.B i)) :
    ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (D : DivisorOver ℂ (S.sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (S.sX i) n (QDivisor.toRDivisor (S.B i)) D a →
        ∃ z : ℤ, (m : ℝ) * a = z := by
  obtain ⟨m, hm, hC⟩ := (S.isFourfoldStepDiagram i).isQCartier_minus.exists_pos
  refine ⟨m, hm, fun n D a ha => ?_⟩
  obtain rfl := eq_four_of_isLogDiscrepancy S i ha
  obtain ⟨-, U, hU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hklt.1.isPair
    (isCanonicalDivisor_K S i) hC (D.f D.E.genericPoint)
  have hd : IsDiscrepancy (S.sX i) 4 (S.K i) (S.B i) D ((D.ordPullback τ : ℚ) / m) :=
    ⟨hklt.1.isPair.1, isCanonicalDivisor_K S i, m, hm, hC, U, hU, τ, hτ, by
      field_simp⟩
  have e := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hd ha
  subst e
  refine ⟨m + D.ordPullback τ, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- A nonempty set of positive reals in `(1/m) ℤ` has a least element. -/
private theorem exists_isLeast_of_mul_eq_int {A : Set ℝ} {m : ℕ} (hm : 0 < m)
    (hA : ∀ a ∈ A, ∃ z : ℤ, (m : ℝ) * a = z) (hpos : ∀ a ∈ A, 0 < a) (hne : A.Nonempty) :
    ∃ a, IsLeast A a := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hex : ∃ k : ℕ, ∃ a ∈ A, (m : ℝ) * a = k := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨z, hz⟩ := hA a ha
    have hz0 : 0 ≤ z := by
      have : (0 : ℝ) < z := hz ▸ mul_pos hmR (hpos a ha)
      exact_mod_cast this.le
    exact ⟨z.toNat, a, ha, by rw [hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm⟩
  obtain ⟨a₀, ha₀, hk⟩ := Nat.find_spec hex
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  obtain ⟨z, hz⟩ := hA b hb
  have hz0 : 0 ≤ z := by
    have : (0 : ℝ) < z := hz ▸ mul_pos hmR (hpos b hb)
    exact_mod_cast this.le
  have hle := Nat.find_min' hex ⟨b, hb, by
    rw [hz]; exact_mod_cast (Int.toNat_of_nonneg hz0).symm⟩
  have : (m : ℝ) * a₀ ≤ m * b := by
    rw [hk, hz]
    have : ((Nat.find hex : ℕ) : ℤ) ≤ z := by omega
    exact_mod_cast this
  exact le_of_mul_le_mul_left this hmR

/-- **The generic mld is attained.** If `mld_x(X_i, B_i) ≤ 1` for a klt `(X_i, B_i)`, some
divisor over `X_i` with centre `{x}⁻` has log discrepancy `mld_x(X_i, B_i)`: the log
discrepancies are positive and lie in `(1/m) ℤ`. -/
private theorem exists_isLogDiscrepancy_eq_minimalLogDiscrepancy (S : StepSequence) (i : ℕ)
    (hklt : IsKltPair (S.sX i) (S.B i)) (x : S.X i)
    (hx : minimalLogDiscrepancy (S.sX i) (S.B i) x ≤ 1) :
    ∃ (n : ℕ) (D : DivisorOver ℂ (S.sX i)) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy (S.sX i) n (QDivisor.toRDivisor (S.B i)) D a ∧
        (D.center : Set (S.X i)) = closure {x} ∧
        minimalLogDiscrepancy (S.sX i) (S.B i) x = (a : EReal) := by
  obtain ⟨m, hm, hmA⟩ := exists_mul_eq_int_of_isLogDiscrepancy S i hklt
  set A : Set ℝ := {a | ∃ (n : ℕ) (D : DivisorOver ℂ (S.sX i)),
    MMP.Intersection.IsLogDiscrepancy (S.sX i) n (QDivisor.toRDivisor (S.B i)) D a ∧
      (D.center : Set (S.X i)) = closure {x}}
  have hmld : minimalLogDiscrepancy (S.sX i) (S.B i) x = sInf ((↑) '' A : Set EReal) := by
    unfold minimalLogDiscrepancy
    congr 1
    ext t
    exact ⟨fun ⟨n, D, a, ha, hc, h⟩ => ⟨a, ⟨n, D, ha, hc⟩, h.symm⟩,
      fun ⟨a, ⟨n, D, ha, hc⟩, h⟩ => ⟨n, D, a, ha, hc, h.symm⟩⟩
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hmld, h, Set.image_empty, sInf_empty] at hx
    exact absurd hx (by decide)
  obtain ⟨a, haA, hal⟩ := exists_isLeast_of_mul_eq_int hm
    (fun a h => by obtain ⟨n, D, ha, -⟩ := h; exact hmA n D a ha)
    (fun a h => by obtain ⟨n, D, ha, -⟩ := h; exact hklt.2 n D a ha) hne
  obtain ⟨n, D, ha, hc⟩ := haA
  refine ⟨n, D, a, ha, hc, ?_⟩
  rw [hmld]
  refine le_antisymm (sInf_le ⟨a, ⟨n, D, ha, hc⟩, rfl⟩) (le_sInf ?_)
  rintro _ ⟨b, hb, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (hal hb)

/-- On a variety of dimension four, an irreducible closed surface has codimension two. -/
private theorem codimension_eq_two {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hX : topologicalKrullDim X = 4)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 2) :
    codimension V = 2 := by
  have hEq : (irreducibleSetEquivPoints (α := X)).symm V.isIrreducible.genericPoint = V :=
    IrreducibleCloseds.ext (V.isIrreducible.isGenericPoint_genericPoint_closure.trans
      V.isClosed.closure_eq)
  rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.isGenericPoint_genericPoint_closure.trans V.isClosed.closure_eq, hV,
    hX] at h
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe c =>
    have h' : (((2 + c : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast
      exact h
    have : 2 + c = 4 := by exact_mod_cast WithBot.coe_injective h'
    obtain rfl : c = 2 := by omega
    rfl

/-- **A bad surface of small mld carries a stable place.** If `V ⊆ X_i` is an irreducible surface
with `mld_{η_V}(X_i, B_i) ≤ 1`, there are a stable place `s ∈ I_∞` and `x ∈ F` such that the
transport `s_i` of `s` to `k(X_i)` is realized by a divisor over `X_i` with centre `V` and has log
discrepancy `x`. -/
private theorem exists_stable_of_minimalLogDiscrepancy_le_one {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) {F : Finset ℚ}
    (hF : ∀ (i : ℕ) (V : IrreducibleCloseds (S.X i)), topologicalKrullDim (V : Set (S.X i)) = 2 →
        minimalLogDiscrepancy (S.sX i) (S.B i) V.isIrreducible.genericPoint ≤ 1 →
          ∃ x ∈ F, minimalLogDiscrepancy (S.sX i) (S.B i) V.isIrreducible.genericPoint =
            ((x : ℝ) : EReal))
    (i : ℕ) (V : IrreducibleCloseds (S.X i)) (hV : topologicalKrullDim (V : Set (S.X i)) = 2)
    (hmld : minimalLogDiscrepancy (S.sX i) (S.B i) V.isIrreducible.genericPoint ≤ 1) :
    ∃ s ∈ S.stableLowDiscrepancySet, ∃ x ∈ F, ∃ η, S.Corresponds i s η ∧
      (∃ D : DivisorOver ℂ (S.sX i), D.valuation = η ∧ D.f D.E.genericPoint ∈ V) ∧
      S.IsLogDiscrepancyAt i η x := by
  have hD := S.isFourfoldStepDiagram i
  haveI : LocallyOfFiniteType (S.sX i) := hD.isNormalVariety_minus.1.toLocallyOfFiniteType
  obtain ⟨n, D, a, ha, hc, heq⟩ := exists_isLogDiscrepancy_eq_minimalLogDiscrepancy S i
    (hS.isKlt i) _ hmld
  have hVη : closure {V.isIrreducible.genericPoint} = (V : Set (S.X i)) :=
    V.isIrreducible.isGenericPoint_genericPoint_closure.trans V.isClosed.closure_eq
  have hcV : D.center = V := SetLike.coe_injective (hc.trans hVη)
  obtain ⟨x, hxF, hx⟩ := hF i V hV hmld
  have hax : a = x := by
    rw [heq] at hx
    exact_mod_cast hx
  have hlow : D.valuation ∈ S.lowDiscrepancySetAt i := by
    refine ⟨⟨D, ha.2.1, rfl, ?_⟩, a, ⟨n, D, ha.2.1, rfl, ha⟩, ?_⟩
    · rw [hcV, codimension_eq_two (S.sX i) hD.dim_minus V hV]
    · rw [heq] at hmld
      exact_mod_cast hmld
  rw [hS.lowDiscrepancySetAt_eq i] at hlow
  obtain ⟨s, hs, hcor⟩ := hlow
  refine ⟨s, hs, x, hxF, D.valuation, hcor, ⟨D, rfl, ?_⟩, ⟨n, D, ha.2.1, rfl, hax ▸ ha⟩⟩
  rw [← hcV, ← SetLike.mem_coe, MMP.Mori.DivisorOver.center_eq_closure_genericPoint]
  exact subset_closure rfl

end Attained

/-- **A monotone sequence takes a value at most once across a strict step.** If `b` is monotone,
`b i < b (i + 1)` for every `i ∈ P`, and `b (i + c) = x` for every `i ∈ P` with `c ≤ 1`, then `P`
has at most one element: for `i < j` in `P`, `b (i + c) < b (j + c)`. -/
private theorem subsingleton_of_monotone_of_lt_succ {b : ℕ → ℝ} (hb : Monotone b) {P : Set ℕ}
    {c : ℕ} (hc : c ≤ 1) {x : ℝ} (hlt : ∀ i ∈ P, b i < b (i + 1)) (hx : ∀ i ∈ P, b (i + c) = x) :
    P.Subsingleton := by
  have key : ∀ i ∈ P, ∀ j ∈ P, ¬ i < j := fun i hi j hj hij => by
    have h := hb (Nat.succ_le_of_lt hij)
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · simp only [add_zero] at hx
      linarith [hlt i hi, hx i hi, hx j hj]
    · linarith [hlt j hj, hx i hi, hx j hj]
  exact fun i hi j hj => le_antisymm (not_lt.1 (key j hj i hi)) (not_lt.1 (key i hi j hj))

open MMP.Fourfold.StepSequence in
/-- **Bad surfaces of small mld on one side.** Fix an offset `c ≤ 1` and sets `W i ⊆ X_{i+c}`
such that, along every stable place, the log discrepancy strictly increases at step `i` whenever
the centre on `X_{i+c}` of its transport lies in `W i`. Then only finitely many indices `i` carry
an irreducible surface `V ⊆ W i` with `mld_{η_V}(X_{i+c}, B_{i+c}) ≤ 1`: such an index is selected
by a pair `(s, x) ∈ I_∞ × F`, and each pair selects at most one index. -/
private theorem finite_setOf_exists_surface_subset {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) {c : ℕ} (hc : c ≤ 1) (W : ∀ i, Set (S.X (i + c)))
    (hW : ∀ (η : ∀ k, Valuation (S.X k).functionField (WithZero (Multiplicative ℤ)))
      (b : ℕ → ℝ),
      (∀ k, ((∃ D : DivisorOver ℂ (S.sX k), D.valuation = η k ∧
            D.f D.E.genericPoint ∈ S.badLocusMinusAt k) ∨
          (∃ D : DivisorOver ℂ (S.sX (k + 1)), D.valuation = η (k + 1) ∧
            D.f D.E.genericPoint ∈ S.badLocusPlusAt k)) → b k < b (k + 1)) →
      ∀ i (D : DivisorOver ℂ (S.sX (i + c))), D.valuation = η (i + c) →
        D.f D.E.genericPoint ∈ W i → b i < b (i + 1)) :
    {i : ℕ | ∃ V : IrreducibleCloseds (S.X (i + c)),
        topologicalKrullDim (V : Set (S.X (i + c))) = 2 ∧ (V : Set (S.X (i + c))) ⊆ W i ∧
          minimalLogDiscrepancy (S.sX (i + c)) (S.B (i + c))
            V.isIrreducible.genericPoint ≤ 1}.Finite := by
  obtain ⟨F, -, hF⟩ := hS.exists_finset_minimalLogDiscrepancy
  have hI := (finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq S
    hS.isSmallFrom_zero hS.isKlt).1
  let P : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ)) → ℚ → Set ℕ :=
    fun s x => {i | ∃ η, S.Corresponds (i + c) s η ∧
      (∃ D : DivisorOver ℂ (S.sX (i + c)), D.valuation = η ∧ D.f D.E.genericPoint ∈ W i) ∧
        S.IsLogDiscrepancyAt (i + c) η x}
  have hsub : ∀ s ∈ S.stableLowDiscrepancySet, ∀ x : ℚ, (P s x).Subsingleton := by
    intro s hs x
    obtain ⟨η, b, hηc, hb, hmono, hlt⟩ := exists_monotone_logDiscrepancy S hs
    refine subsingleton_of_monotone_of_lt_succ hmono hc (x := x)
      (fun i ⟨η', hη'c, ⟨D, hDv, hDW⟩, _⟩ => ?_) (fun i ⟨η', hη'c, _, hx⟩ => ?_)
    · obtain rfl := eq_of_corresponds S (i + c) hη'c (hηc (i + c))
      exact hW η b hlt i D hDv hDW
    · obtain rfl := eq_of_corresponds S (i + c) hη'c (hηc (i + c))
      exact GraphComparison.isValuationLogDiscrepancy_eq (hb (i + c)) hx
  refine (hI.biUnion fun s hs => F.finite_toSet.biUnion fun x _ =>
    (hsub s hs x).finite).subset ?_
  rintro i ⟨V, hV, hVW, hmld⟩
  obtain ⟨s, hs, x, hxF, η, hcor, ⟨D, hDv, hDV⟩, hx⟩ :=
    exists_stable_of_minimalLogDiscrepancy_le_one hS hF (i + c) V hV hmld
  simp only [Set.mem_iUnion]
  exact ⟨s, hs, x, hxF, η, hcor, ⟨D, hDv, hVW hDV⟩, hx⟩

end MMP.Fourfold.BadSurfaces

namespace MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Bad surfaces of small mld occur finitely often on each side.** For a stabilized small klt
tail `S`, the set of indices `i` such that some irreducible closed surface `V ⊆ W_i⁻ ⊆ X_i` has
`mld_{η_V}(X_i, B_i) ≤ 1` is finite, and so is the set of indices `i` such that some irreducible
closed surface `V ⊆ W_i⁺ ⊆ X_{i+1}` has `mld_{η_V}(X_{i+1}, B_{i+1}) ≤ 1`. -/
@[mmp "lem_mmp_fourfold_bad_surfaces_finite_by_denominators"]
public theorem finite_setOf_exists_surface_subset_badLocus {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) :
    {i : ℕ | ∃ V : IrreducibleCloseds (S.X i),
        topologicalKrullDim (V : Set (S.X i)) = 2 ∧
          (V : Set (S.X i)) ⊆ S.badLocusMinusAt i ∧
          minimalLogDiscrepancy (S.sX i) (S.B i) V.isIrreducible.genericPoint ≤ 1}.Finite ∧
      {i : ℕ | ∃ V : IrreducibleCloseds (S.X (i + 1)),
        topologicalKrullDim (V : Set (S.X (i + 1))) = 2 ∧
          (V : Set (S.X (i + 1))) ⊆ S.badLocusPlusAt i ∧
          minimalLogDiscrepancy (S.sX (i + 1)) (S.B (i + 1))
            V.isIrreducible.genericPoint ≤ 1}.Finite :=
  ⟨BadSurfaces.finite_setOf_exists_surface_subset hS (c := 0) zero_le_one (S.badLocusMinusAt ·)
      fun _ _ h i D hDv hDW => h i (.inl ⟨D, hDv, hDW⟩),
    BadSurfaces.finite_setOf_exists_surface_subset hS (c := 1) le_rfl (S.badLocusPlusAt ·)
      fun _ _ h i D hDv hDW => h i (.inr ⟨D, hDv, hDW⟩)⟩

/-- **Bad surfaces eventually have generic mld above one.** For a stabilized small klt tail `S`
there is `i₁` such that for all `i ≥ i₁`, every irreducible closed surface `V ⊆ W_i⁻ ⊆ X_i` has
`1 < mld_{η_V}(X_i, B_i)`, and every irreducible closed surface `V ⊆ W_i⁺ ⊆ X_{i+1}` has
`1 < mld_{η_V}(X_{i+1}, B_{i+1})`. -/
@[mmp "prop_oai4_codim_two_b"]
public theorem exists_forall_ge_one_lt_minimalLogDiscrepancy {S : StepSequence}
    (hS : S.IsStabilizedSmallKltTail) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁,
      (∀ V : IrreducibleCloseds (S.X i),
        topologicalKrullDim (V : Set (S.X i)) = 2 →
          (V : Set (S.X i)) ⊆ S.badLocusMinusAt i →
          1 < minimalLogDiscrepancy (S.sX i) (S.B i) V.isIrreducible.genericPoint) ∧
      (∀ V : IrreducibleCloseds (S.X (i + 1)),
        topologicalKrullDim (V : Set (S.X (i + 1))) = 2 →
          (V : Set (S.X (i + 1))) ⊆ S.badLocusPlusAt i →
          1 < minimalLogDiscrepancy (S.sX (i + 1)) (S.B (i + 1))
            V.isIrreducible.genericPoint) := by
  obtain ⟨hm, hp⟩ := hS.finite_setOf_exists_surface_subset_badLocus
  obtain ⟨i₁, h⟩ := Filter.eventually_atTop.mp <| Nat.cofinite_eq_atTop ▸
    hm.eventually_cofinite_notMem.and hp.eventually_cofinite_notMem
  exact ⟨i₁, fun i hi => by simpa [not_and, not_le] using h i hi⟩

end MMP.Fourfold.StepSequence.IsStabilizedSmallKltTail

end
