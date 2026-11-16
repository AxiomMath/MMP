module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepSequence
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram.GraphDivisorBranchCounts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeAdditivity
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Bad loci and discrepancies of fourfold step diagrams

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a step diagram of complex fourfolds, with bad locus `Σ ⊆ Z`
(the complement of the largest open set over which both `f⁻` and `f⁺` are isomorphisms) and bad
loci `W^± = (f^±)⁻¹(Σ)`. Let `(G, u, v)` be the normalized graph of `X⁻ ⇢ X⁺`, `g = u ≫ f⁻` and
`H = u^*(K⁻ + B⁻) - v^*(K⁺ + B⁺)` the graph divisor. This file proves:

* **Strictness of the comparison.** For a normalized divisorial valuation `ξ` of the common
  function field, `a(ξ; X⁻, B⁻) < a(ξ; X⁺, B⁺)` holds exactly when `c_{X⁻}(ξ) ⊆ W⁻`, exactly
  when `c_{X⁺}(ξ) ⊆ W⁺`. Realize `ξ = ord_E` on a model `w : W ⟶ G`. Local equations of `M D^±`
  near the centres and a common top form on `Z` give a rational function `φ` on `G`, a local
  equation of `M H` near `y = w(η_E)`, with `M (a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻)) = v_E(w^*φ)`. The
  negativity lemma makes `H` effective (`-H` is `g`-ample and `H` vanishes over `Z ∖ Σ`) and
  puts `g⁻¹(Σ)` inside `Supp H` (a contracted curve through a closed point of `cl{y}` missing
  `Supp H` would have `-H · C > 0` and `H · C ≥ 0`). So `v_E(w^*φ) > 0` exactly when `g(y) ∈ Σ`.
* **Lost divisors improve strictly.** A prime divisor `E` of `X⁻` contracted by `X⁻ ⇢ X⁺` lies
  in `W⁻`, so its log discrepancy strictly increases.
* **The graph dimension bound.** If `Σ ≠ ∅` then `dim W⁻ + dim W⁺ ≥ 3`: some prime divisor of
  the fourfold `G` lies over `Σ` (otherwise `H = 0`, so `𝒪_G` is `g`-ample and `g`, hence `f^±`,
  is finite over `Σ`), and the finiteness of `(u, v) : G ⟶ X⁻ ×_Z X⁺` bounds the transcendence
  degree of its residue field by those of its images.
* **Bad loci of small steps.** `dim W⁺ ≤ 2`, and `dim W⁻ ≤ 2` when `f⁻` is small: a point of
  codimension at most one on the small side lies off the exceptional set, and a proper
  birational morphism onto the normal `Z` is an isomorphism over every point of codimension at
  most one, so the point is off the bad locus. Then `dim Σ ≤ 1` when `f⁻` is small: a chain of
  two strict specializations in `Σ` lifts, along the side `f^σ` with a positive-dimensional fibre
  over its generic end, to a chain of three in `W^σ`.

## Main results

* `MMP.Fourfold.IsFourfoldStepDiagram.tfae_lt_and_centre_subset_badLocus`
* `MMP.Fourfold.IsFourfoldStepDiagram.lt_of_isExceptionalValuation_divisorialValuation`
* `MMP.Fourfold.IsFourfoldStepDiagram.three_le_topologicalKrullDim_badLocusMinus_add`
* `MMP.Fourfold.IsFourfoldStepDiagram.topologicalKrullDim_badLocusPlus_le_two`
* `MMP.Fourfold.IsFourfoldStepDiagram.topologicalKrullDim_badLocusMinus_le_two`
* `MMP.Fourfold.IsFourfoldStepDiagram.topologicalKrullDim_badLocusBase_le_one`
* `MMP.Fourfold.topologicalKrullDim_badLocusBase_le_one_of_isSmallMorphism`: the same bound
  for any two small morphisms from fourfolds, without boundaries

## Implementation notes

* The common function field is realised by a valuation `ξ` of `k(X⁻)` together with the
  valuation `ξ⁺` of `k(X⁺)` with the same restriction to `k(Z)` (through `functionFieldMap f⁻`
  and `functionFieldMap f⁺`). Log discrepancies and centres are the values satisfying
  `MMP.Fourfold.IsValuationLogDiscrepancy` and `MMP.Intersection.IsCentre`; each is determined
  by the valuation. The boundary of `X⁺` is `MMP.Mori.flipTransform f⁻ f⁺ B⁻`.
* The normalized graph is the normalization of the reduced closure of the point of
  `X⁻ ×_Z X⁺` over the two generic points; both projections are birational because the residue
  field of that point is `κ(X⁻) = κ(X⁺)`.
* Dimensions are Krull dimensions of the underlying closed subspaces (`topologicalKrullDim`,
  valued in `WithBot ℕ∞`); an empty bad locus has dimension `⊥`.
* The bounds `dim W^± ≤ 2` are proved on `X^±` and `Z` directly, without the graph divisor: the
  fact the graph computation detects, that `W^±` contains no prime divisor, follows from
  smallness and biregularity in codimension one over the normal `Z`.

## References

* [OpenAI, *Projective lc fourfolds*][OAI4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.38, 3.39
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Topology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

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
    rw [← hc]
    exact h3.comp h2
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

/-- A proper birational morphism of normal locally noetherian integral schemes is a birational
morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsNormal X] [IsNormal Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f) : IsBirationalMorphism f := by
  simpa using MMP.Mori.isBirationalMorphism_comp_of_isBirational f (𝟙 Y) hf
    (isBirational_of_bijOn_of_isIso_stalkMap _ (Set.bijOn_id _) fun _ _ => inferInstance)

/-- If the residue field map of `g` at `T.y` is an isomorphism, then so is the canonical map
`κ(T.x) ⟶ κ(T.x) ⊗_{κ(T.s)} κ(T.y)`, being a pushout of an isomorphism. -/
private theorem isIso_tensorInl {X Z S : Scheme.{0}} {f : X ⟶ S} {g : Z ⟶ S}
    (T : Scheme.Pullback.Triplet f g) (hres : IsIso (g.residueFieldMap T.y)) :
    IsIso T.tensorInl := by
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  change IsIso (pushout.inl ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  infer_instance

/-- If the residue field map of `g : Z ⟶ S` at `z` is an isomorphism, a point of `X ×_S Z` is
determined by its two projections when the second one is `z` ([Stacks, Tag 01JT]). -/
private theorem eq_of_fst_eq_of_snd_eq {X Z S : Scheme.{0}} (f : X ⟶ S) (g : Z ⟶ S)
    {w w' : ↥(pullback f g)} (hres : IsIso (g.residueFieldMap (pullback.snd f g w)))
    (h₁ : pullback.fst f g w' = pullback.fst f g w)
    (h₂ : pullback.snd f g w' = pullback.snd f g w) : w' = w := by
  have : Subsingleton ↥(Spec (Scheme.Pullback.carrierEquiv w).fst.tensor) := by
    have hinl := isIso_tensorInl (Scheme.Pullback.carrierEquiv w).fst hres
    exact (PrimeSpectrum.comap_injective_of_surjective
      (Scheme.Pullback.carrierEquiv w).fst.tensorInl.hom
      (ConcreteCategory.bijective_of_isIso _).2).subsingleton
  refine Scheme.Pullback.carrierEquiv.injective
    (Scheme.Pullback.carrierEquiv_eq_iff.mpr ?_)
  exact ⟨Scheme.Pullback.Triplet.ext h₁ h₂, Subsingleton.elim _ _⟩

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

/-! ### The normalized graph -/

/-- The data of a normalized graph of a step diagram, together with the finiteness facts used
below. -/
private structure GraphData {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (_h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) where
  G : Scheme.{0}
  u : G ⟶ Xm
  v : G ⟶ Xp
  isNormalizedGraph : IsNormalizedGraph fm fp u v
  isNormal : IsNormal G
  isLocallyNoetherian : IsLocallyNoetherian G
  compactSpace : CompactSpace G
  locallyOfFiniteType : LocallyOfFiniteType (u ≫ sXm)
  isProper_u : IsProper u
  isProper_v : IsProper v

/-- The source of a normalized graph is integral. -/
private theorem GraphData.isIntegral {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    {h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp} (D : GraphData h) : IsIntegral D.G :=
  D.isNormalizedGraph.isIntegral

attribute [local instance] GraphData.isIntegral GraphData.isNormal GraphData.isLocallyNoetherian
  GraphData.compactSpace GraphData.locallyOfFiniteType GraphData.isProper_u GraphData.isProper_v

/-- **The normalized graph exists**: the normalization `G` of the closure `Γ ⊆ X⁻ ×_Z X⁺` of the
point over the two generic points, with its two projections. -/
private theorem exists_graphData {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) : Nonempty (GraphData h) := by
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
      rw [closure_closure]
      exact isGenericPoint_closure
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
  exact ⟨⟨G, u, v, hG, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩⟩

/-! ### Fibres and biregular loci -/

/-- A proper birational morphism of complex varieties onto a normal variety is an isomorphism
over a neighbourhood of every point with finite fibre. -/
private theorem mem_biregularLocus_of_finite {U R : Scheme.{0}} {sU : U ⟶ Spec (.of ℂ)}
    {sR : R ⟶ Spec (.of ℂ)} (hU : AlgebraicGeometry.IsVariety ℂ sU)
    (hR : AlgebraicGeometry.IsVariety ℂ sR) [IsNormal R] (f : U ⟶ R) (hf : f ≫ sR = sU)
    [IsProper f] (hb : IsBirational f) {z : R} (hz : (f ⁻¹' {z}).Finite) :
    z ∈ biregularLocus f := by
  obtain ⟨⟨hO, hiso⟩, -, -⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hU hR f hf hb
  exact le_biregularLocus (V := ⟨_, hO⟩) hiso hz

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The structure map `g = u ≫ f⁻` of the normalized graph has finite fibres over the open where
both `f^±` are isomorphisms: there a fibre of `X⁻ ×_Z X⁺` is one point, and `(u, v)` is finite. -/
private theorem finite_preimage_of_mem_commonBiregularLocus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {z : Z}
    (hz : z ∈ commonBiregularLocus fm fp) : ((D.u ≫ fm) ⁻¹' {z}).Finite := by
  have hG := D.isNormalizedGraph
  haveI := hG.isFinite
  haveI : IsIso (fm ∣_ biregularLocus fm) := isBiregular_biregularLocus fm
  haveI : IsIso (fp ∣_ biregularLocus fp) := isBiregular_biregularLocus fp
  have sm := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict fm _ hz.1
  have sp := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict fp _ hz.2
  rcases ((D.u ≫ fm) ⁻¹' {z}).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]
    exact Set.finite_empty
  set L := pullback.lift D.u D.v hG.comp_eq
  refine (L.finite_preimage_singleton (L x₀)).subset fun x hx => ?_
  have hx' : fm (D.u x) = z := hx
  have hx₀' : fm (D.u x₀) = z := hx₀
  have hvx : fp (D.v x) = z := by
    rwa [← Scheme.Hom.comp_apply, ← hG.comp_eq]
  have hvx₀ : fp (D.v x₀) = z := by
    rwa [← Scheme.Hom.comp_apply, ← hG.comp_eq]
  have hres : IsIso (fp.residueFieldMap (pullback.snd fm fp (L x₀))) := by
    have hsnd : pullback.snd fm fp (L x₀) = D.v x₀ := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    have hmem : fp (pullback.snd fm fp (L x₀)) ∈ biregularLocus fp := by
      rw [hsnd, hvx₀]
      exact hz.2
    haveI := MMP.isIso_stalkMap_of_mem_biregularLocus fp hmem
    exact isIso_residueFieldMap_of_isIso_stalkMap _ _
  refine eq_of_fst_eq_of_snd_eq fm fp hres ?_ ?_
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact sm hx' hx₀'
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact sp hvx hvx₀

/-- The source of the normalized graph is a complex variety through `u ≫ s⁻`. -/
private theorem isVariety_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : AlgebraicGeometry.IsVariety ℂ (D.u ≫ sXm) := by
  have := h.isNormalVariety_minus.1
  exact (isVariety_iff ℂ (D.u ≫ sXm)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The structure map `g = u ≫ f⁻` of the normalized graph is birational. -/
private theorem isBirational_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsBirational (D.u ≫ fm) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  exact IsBirational.comp
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      D.isNormalizedGraph.isBirationalMorphism_minus)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)

/-- The source of the normalized graph is a normal complex variety through `u ≫ s⁻`. -/
private theorem isNormalVariety_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsNormalVariety ℂ (D.u ≫ sXm) :=
  ⟨isVariety_graph h D, inferInstance⟩

/-- The structure map `g = u ≫ f⁻` of the normalized graph is a birational morphism. -/
private theorem isBirationalMorphism_graph (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsBirationalMorphism (D.u ≫ fm) := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  exact MMP.Mori.isBirationalMorphism_comp_of_isBirational fm D.u
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
      D.isNormalizedGraph.isBirationalMorphism_minus)

/-- The source of the normalized graph is a normal complex variety through `v ≫ s⁺`. -/
private theorem isNormalVariety_graph_plus (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : IsNormalVariety ℂ (D.v ≫ sXp) := by
  have := h.isNormalVariety_plus.1
  exact ⟨(isVariety_iff ℂ (D.v ≫ sXp)).mpr
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- **The graph divisor vanishes over `U = Z ∖ Σ`.** If the generic point of a prime divisor `E`
of `G` lies over the open where both `f^±` are isomorphisms, then `g` is an isomorphism there,
so `v(η_E)` is the generic point of a prime divisor `P` of `X⁺` over which `E` is the only prime
divisor; the coefficient of `E` in `H` is that of `P` in `v_* H = 0`. -/
private theorem coeff_eq_zero_of_mem_commonBiregularLocus
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {H : QDivisor D.G}
    (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) (E : MMP.Mori.PrimeDivisor D.G)
    (hE : (D.u ≫ fm) E.genericPoint ∈ commonBiregularLocus fm fp) : H E = 0 := by
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hgz : (D.u ≫ fm) E.genericPoint ∈ biregularLocus (D.u ≫ fm) :=
    mem_biregularLocus_of_finite (isVariety_graph h D) hZ.1 (D.u ≫ fm)
      (by rw [Category.assoc, h.comp_eq_minus]) (isBirational_graph h D)
      (finite_preimage_of_mem_commonBiregularLocus h D hE)
  have hvx : fp (D.v E.genericPoint) ∈ biregularLocus fp := by
    rw [← Scheme.Hom.comp_apply, ← hG.comp_eq]
    exact hE.2
  have hco : Order.coheight (D.v E.genericPoint) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hvx, ← Scheme.Hom.comp_apply,
      ← hG.comp_eq, MMP.Positivity.coheight_map_of_mem_biregularLocus _ hgz,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hP : P.genericPoint = D.v E.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  obtain ⟨E', hE'P, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply
    h.isNormalVariety_plus (isNormalVariety_graph_plus h D) hG.isBirationalMorphism_plus P
  have hEE' : E' = E := by
    haveI : IsIso ((D.u ≫ fm) ∣_ biregularLocus (D.u ≫ fm)) :=
      isBiregular_biregularLocus (D.u ≫ fm)
    refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict _ _ hgz ?_ rfl)
    change (D.u ≫ fm) E'.genericPoint = (D.u ≫ fm) E.genericPoint
    rw [hG.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hE'P]
    exact congrArg fp hP
  have h0 := hH.transformDivisor_eq_zero
  have := htr H
  rw [h0, hEE'] at this
  exact this.symm

/-- A step diagram with a normalized graph has a graph divisor: the pull-backs of the
`ℚ`-Cartier divisors `D^±` exist, the generic point of `G` mapping to the generic points of
`X^±`. -/
private theorem exists_isGraphDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) : ∃ H : QDivisor D.G, IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H := by
  haveI := D.isNormalizedGraph.isBirationalMorphism_minus.isDominant
  haveI := D.isNormalizedGraph.isBirationalMorphism_plus.isDominant
  have hm := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D.u
    (Divisor.toQDivisor K + B)
  have hp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' D.v
    (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B)
  exact ⟨_, h, D.isNormalizedGraph, _, _, hm, hp,
    QDivisor.isPullback_pullback h.isQCartier_minus hm,
    QDivisor.isPullback_pullback h.isQCartier_plus hp, rfl⟩

/-! ### A model over the graph realizing the valuation -/

/-- The birational map `(f')⁻¹ ∘ f : X ⤏ X'` of two birational morphisms to a separated
scheme is a birational map over `Y`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} [IsReduced X]
    [IsReduced X'] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom f' = f.toRationalMap := by
  obtain ⟨em, hem⟩ := hf
  obtain ⟨ep, hep⟩ := hf'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Y) hem
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep f' (𝟙 Y) hep
  set e := em.trans ep.symm with he
  have H : e.IsOver (f ≫ 𝟙 Y) (f' ≫ 𝟙 Y) := h1.trans h2.symm
  have H' : e.iso.hom ≫ e.target.ι ≫ f' = e.source.ι ≫ f := by
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using H
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H']
  simp

/-- **A model over the graph.** For a divisor `D₀` over `X⁻` there are a normal variety `W` with a
proper birational morphism `w : W ⟶ G` and a prime divisor `E` of `W` such that the divisor
`(W, w ≫ u, E)` over `X⁻` has the valuation of `D₀`. -/
private theorem exists_model (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h)
    (D₀ : DivisorOver ℂ sXm) :
    ∃ (W : Scheme.{0}) (w : W ⟶ D.G) (hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm))
      (hb : IsBirationalMorphism (w ≫ D.u)), IsProper w ∧ IsBirationalMorphism w ∧
      ∃ E : MMP.Mori.PrimeDivisor W,
        (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ sXm).valuation = D₀.valuation := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hG := D.isNormalizedGraph
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper (D.u ≫ fm) := inferInstance
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq h.isBirationalMorphism_minus
    (isBirationalMorphism_graph h D)
  obtain ⟨W, g₁, w, hW₁, hg₁, hg₁p, hwp, hw, -, hcomm, E, hE⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq
      h.isNormalVariety_minus (isNormalVariety_graph h D) fm (D.u ≫ fm) φ hφ hφS D₀
  have e : (w ≫ D.u) ≫ sXm = g₁ ≫ sXm := calc
    (w ≫ D.u) ≫ sXm = (w ≫ D.u) ≫ fm ≫ sZ := by rw [h.comp_eq_minus]
    _ = g₁ ≫ fm ≫ sZ := by rw [← Category.assoc g₁, hcomm]; simp only [Category.assoc]
    _ = g₁ ≫ sXm := by rw [h.comp_eq_minus]
  have hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm) := by rwa [e]
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((w ≫ D.u) ≫ sXm)
  haveI : IsDominant w := hw.isDominant
  have hb : IsBirationalMorphism (w ≫ D.u) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational D.u w
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_minus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hw)
  refine ⟨W, w, hW, hb, hwp, hw, E, ?_⟩
  rw [← hE]
  haveI := hg₁.isDominant
  haveI := hb.isDominant
  haveI := h.isBirationalMorphism_minus.isDominant
  ext x
  obtain ⟨t, rfl⟩ := h.isBirationalMorphism_minus.functionFieldMap_bijective.2 x
  change E.divisorialValuation (functionFieldMap (w ≫ D.u) (functionFieldMap fm t)) =
    E.divisorialValuation (functionFieldMap g₁ (functionFieldMap fm t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [Category.assoc, hcomm]

/-! ### Log discrepancies through local equations -/

/-- **Log discrepancies through a local equation.** Let `ω` be a nonzero rational top form on
the normal variety `X` of dimension `n`, `B` a `ℚ`-divisor and `φ` a rational function with
`v_Γ(φ) = M (ord_Γ ω + coeff_Γ B)` along every prime divisor `Γ` through the image `x` of the
generic point of `E`, for a divisor `(Y, f, E)` over `X` of valuation `ξ` (so `φ` is a local
equation of `M (div ω + B)` near `x`). Then `M (a(ξ; X, B) - 1) = M ord_E(f^*ω) - v_E(f^*φ)`. -/
private theorem mul_sub_one_eq_of_isValuationLogDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) {Δ : QDivisor X}
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (ha : IsValuationLogDiscrepancy sX Δ ξ a) (D' : DivisorOver ℂ sX) (hD' : D'.valuation = ξ)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) {M : ℕ} (hM : 0 < M)
    {φ : X.functionField} (hφ : φ ≠ 0)
    (hφΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, D'.f D'.E.genericPoint ∈ Γ.support →
      (X.ord φ Γ.genericPoint : ℝ) = M * ((Γ.ordForm ω : ℝ) + (Δ.coeff Γ : ℝ))) :
    haveI := D'.isIntegral
    haveI := D'.isLocallyNoetherian
    haveI := D'.isDominant
    (M : ℝ) * (a - 1) =
      M * D'.ordPullback ω - D'.Y.ord (functionFieldMap D'.f φ) D'.E.genericPoint := by
  classical
  obtain ⟨n', D, -, hDv, hl⟩ := ha
  have hn' : n' = n := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hl
    rw [hn] at this
    exact_mod_cast this.symm
  subst hn'
  have hv : D.valuation = D'.valuation := hDv.trans hD'.symm
  have hx : D.f D.E.genericPoint = D'.f D'.E.genericPoint :=
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hv
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have := D'.isDominant
  have e1 : D'.ordPullback ω = D.ordPullback ω :=
    (MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv ω).symm
  have e2 : D'.Y.ord (functionFieldMap D'.f φ) D'.E.genericPoint =
      D.Y.ord (functionFieldMap D.f φ) D.E.genericPoint :=
    MMP.Threefold.Bridges.ord_functionFieldMap_eq_of_valuationOver_eq D.E D'.E hv hφ
  rw [e1, e2]
  rw [← hx] at hφΓ
  obtain ⟨-, -, ω', hω'0, -, m', r, C, C', hCc, hsum, hpb, rfl⟩ := hl
  let := MMP.Mori.functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set x := D.f D.E.genericPoint with hxdef
  choose V hV ψ hψ using fun i => hCc i x
  let Z0 := MMP.Mori.pointComponent x
  let g : Fin m' → X.functionField := fun i =>
    MMP.Threefold.Mori.Helpers.evalFF Z0 ((ψ i : MMP.Mori.RationalFunctions X))
  have hg : ∀ i, g i ≠ 0 := fun i => ((ψ i).isUnit.map _).ne_zero
  set cω' := (MMP.Mori.ZTensorPower.basis β 1).repr ω' () with hcω'
  set cω := (MMP.Mori.ZTensorPower.basis β 1).repr ω () with hcω
  have hcω'0 : cω' ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω'0
  have hcω0 : cω ≠ 0 := MMP.Mori.repr_ne_zero_of_ne_zero β hω
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  let G : Option (Option (Option (Fin m'))) → X.functionField := fun j =>
    Option.elim j cω' fun j => Option.elim j cω fun j => Option.elim j φ g
  let wt : Option (Option (Option (Fin m'))) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-1) fun j => Option.elim j (1 / (M : ℝ)) fun i => -r i
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | _ | i)
    exacts [hcω'0, hcω0, hφ, hg i]
  have hgΓ : ∀ (Γ : MMP.Mori.PrimeDivisor X) (i : Fin m'), x ∈ Γ.support →
      X.ord (g i) Γ.genericPoint = (C i).coeff Γ := by
    intro Γ i hΓ
    have hZ : Γ.component = Z0 := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hψ i Γ ⟨x, hΓ, hV i⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG wt
    fun Γ hΓ => by
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd β
    have f1 : (Γ.ordForm ω' : ℝ) = X.ord cω' Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω' hω'0)
    have f2 : (Γ.ordForm ω : ℝ) = X.ord cω Γ.genericPoint + NΓ := by
      exact_mod_cast (by simpa using hNΓ 1 ω hω)
    have f3 := hφΓ Γ hΓ
    have f4 := hsum Γ
    rw [QDivisor.coeff_toRDivisor] at f4
    simp only [Fintype.sum_option, G, wt, Option.elim]
    simp_rw [hgΓ Γ _ hΓ]
    have f5 : ∑ i, ((C i).coeff Γ : ℝ) * -r i = -∑ i, r i * ((C i).coeff Γ : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [f5, f3]
    field_simp
    linear_combination -f1 + f2 + f4
  have hcoeff : ∀ i, ((C' i).coeff D.E : ℝ) =
      D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint := by
    intro i
    obtain ⟨hC, hCp⟩ := hpb i
    exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hCp (hψ i) D.E (hV i) Z0
  have h1 : (D.ordPullback ω' : ℝ) =
      D.Y.ord (functionFieldMap D.f cω') D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω' hω'0)
  have h2 : (D.ordPullback ω : ℝ) =
      D.Y.ord (functionFieldMap D.f cω) D.E.genericPoint + N := by
    exact_mod_cast (by simpa using hN 1 ω hω)
  simp only [Fintype.sum_option, G, wt, Option.elim] at key
  simp_rw [hcoeff]
  have f5 : ∑ i, (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) * -r i =
      -∑ i, r i * (D.Y.ord (functionFieldMap D.f (g i)) D.E.genericPoint : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [f5] at key
  field_simp at key
  linear_combination (M : ℝ) * h1 - (M : ℝ) * h2 + key

/-! ### Pull-backs of forms -/

section Forms

variable {k : Type} [Field k] [PerfectField k]

/-- Along a morphism `f` inducing an isomorphism of function fields, every rational pluri-form
is a pull-back: `τ = f^*σ`, with `σ ≠ 0` when `τ ≠ 0`. -/
private theorem exists_pullbackRationalPluriForms_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms (f ≫ sY) d m) :
    ∃ σ : RationalPluriForms sY d m, pullbackRationalPluriForms sY f σ = τ ∧
      (τ ≠ 0 → σ ≠ 0) := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  set bY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m with hbY
  set bX := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m with hbX
  obtain ⟨c, hc⟩ := hf.2 (bX.repr τ ())
  have hpull : pullbackRationalPluriForms sY f (c • bY ()) = τ := by
    change pullbackForms m (c • bY ()) = τ
    rw [pullbackForms_eq hω m]
    apply bX.ext_elem
    intro i
    obtain rfl : i = () := rfl
    rw [repr_pullbackFormsAlong hω m]
    simp only [bY, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact hc
  refine ⟨c • bY (), hpull, fun hτ hσ => hτ ?_⟩
  rw [← hpull, hσ]
  change pullbackForms m 0 = 0
  rw [pullbackForms_eq hω m]
  simp [pullbackFormsAlong]

/-- Along a morphism inducing an isomorphism of function fields, the pull-back of a nonzero
rational pluri-form is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d) {m : ℤ}
    {σ : RationalPluriForms sY d m} (hσ : σ ≠ 0) : pullbackRationalPluriForms sY f σ ≠ 0 := by
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY f hf hd
  rw [show pullbackRationalPluriForms sY f σ = pullbackFormsAlong hω m σ from
    pullbackForms_eq hω m σ]
  intro h0
  have h1 := repr_pullbackFormsAlong hω m σ
  rw [h0] at h1
  have h2 : algebraMap Y.functionField X.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr σ ()) = 0 := by
    rw [← h1]
    exact (DFunLike.congr_fun (LinearEquiv.map_zero _) ()).trans Finsupp.zero_apply
  exact repr_ne_zero_of_ne_zero _ hσ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h2)

/-- **Orders of pulled-back forms along a composite.** For `g : W ⟶ X` and a birational
`f : X ⟶ Y`, the order along `(W, g, F)` over `X` of `f^*σ` is the order along
`(W, g ≫ f, F)` over `Y` of `σ`. -/
private theorem ordPullback_pullbackRationalPluriForms {X Y W : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsDominant f]
    [LocallyOfFiniteType (f ≫ sY)] (hf : IsBirationalMorphism f) {d : ℕ}
    (hd : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = d)
    {g : W ⟶ X} (hW : IsNormalVariety k (g ≫ f ≫ sY)) (hg : IsBirationalMorphism g)
    (hgf : IsBirationalMorphism (g ≫ f)) (F : MMP.Mori.PrimeDivisor W) {m : ℤ}
    (σ : RationalPluriForms sY d m) :
    (⟨W, g, hW, hg, F⟩ : DivisorOver k (f ≫ sY)).ordPullback
        (pullbackRationalPluriForms sY f σ) =
      (⟨W, g ≫ f, hW, hgf, F⟩ : DivisorOver k sY).ordPullback σ := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant g := hg.isDominant
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ f ≫ sY)
  change F.ordForm (pullbackRationalPluriForms (f ≫ sY) g (pullbackRationalPluriForms sY f σ)) =
    F.ordForm (pullbackRationalPluriForms sY (g ≫ f) σ)
  rw [MMP.Flips.pullbackRationalPluriForms_comp f g hf.functionFieldMap_bijective
    hg.functionFieldMap_bijective hd σ]
  rfl

/-- The order of the pull-back of a form along equal morphisms is the same. -/
private theorem ordForm_pullbackRationalPluriForms_congr {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sX : X ⟶ Spec (.of k)} {f₁ f₂ : Y ⟶ X}
    [IsDominant f₁] [IsDominant f₂] (hf : f₁ = f₂) (E : MMP.Mori.PrimeDivisor Y) {d : ℕ}
    {m : ℤ} (σ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms sX f₁ σ) =
      E.ordForm (pullbackRationalPluriForms sX f₂ σ) := by
  subst hf
  rfl

end Forms

/-- The order along `Γ` of the rational function of a local equation of a divisor `L` on an open
`U` is the coefficient of `Γ` in `L`, for every prime divisor `Γ` through a point `x ∈ U`. -/
private theorem ord_evalFF_eq_coeff {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {L : Divisor X} {U : X.Opens} {ψ : (MMP.Mori.RationalFunctions X)ˣ}
    (hψ : L.IsLocalEquation U ψ) {x : X} (hx : x ∈ U) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    X.ord (MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent x)
      (ψ : MMP.Mori.RationalFunctions X)) Γ.genericPoint = L Γ := by
  have hZ : Γ.component = MMP.Mori.pointComponent x := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  change _ = L.coeff Γ
  rw [hψ Γ ⟨x, hΓ, hx⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]

/-- **The common differential.** Let `σ` be a rational top form on `Z` whose pull-back to `X⁻`
cuts out the canonical divisor `K⁻`. Then its pull-back to `X⁺` cuts out
`K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`: at a prime divisor `P` of `X⁺`, take the prime divisor `E` of the
normalized graph over `P` and the prime divisor `P⁻ = u(E)` of `X⁻`; all the maps are local
isomorphisms at these generic points. -/
private theorem ordForm_pullbackRationalPluriForms_eq_flipTransform
    [IsIntegral Z] [IsDominant fm] [IsDominant fp]
    (h : IsFourfoldStepDiagram (fm ≫ sZ) sZ (fp ≫ sZ) K B fm fp) (D : GraphData h) {n : ℕ}
    (hnZ : topologicalKrullDim Z = n) (σ : RationalPluriForms sZ n 1)
    (hσ : ∀ Γ : MMP.Mori.PrimeDivisor Xm,
      Γ.ordForm (pullbackRationalPluriForms sZ fm σ) = K Γ)
    (P : MMP.Mori.PrimeDivisor Xp) :
    P.ordForm (pullbackRationalPluriForms sZ fp σ) = flipTransform fm fp K P := by
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  have hdZ := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  have hdm := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := fm ≫ sZ)
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hbm).symm.trans hnZ)
  have hdp := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := fp ≫ sZ)
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fp ≫ sZ)
      hbp).symm.trans hnZ)
  obtain ⟨E, hvE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hXp (isNormalVariety_graph_plus h D) hG.isBirationalMorphism_plus P
  obtain ⟨Pm, huE, hfl⟩ := exists_eq_genericPoint_flipTransform_apply hbm
    h.isSmallMorphism_plus P (D.u E.genericPoint)
    (by rw [← Scheme.Hom.comp_apply, hG.comp_eq, Scheme.Hom.comp_apply, hvE])
  haveI := isIso_stalkMap_of_map_eq_genericPoint hG.isBirationalMorphism_minus huE
  haveI := hiso
  rw [hfl K, ← hσ Pm,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso D.v
      hG.isBirationalMorphism_plus.functionFieldMap_bijective hdp E P hvE,
    ← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso D.u
      hG.isBirationalMorphism_minus.functionFieldMap_bijective hdm E Pm huE,
    MMP.Flips.pullbackRationalPluriForms_comp fp D.v hbp.functionFieldMap_bijective
      hG.isBirationalMorphism_plus.functionFieldMap_bijective hdZ σ,
    MMP.Flips.pullbackRationalPluriForms_comp fm D.u hbm.functionFieldMap_bijective
      hG.isBirationalMorphism_minus.functionFieldMap_bijective hdZ σ]
  exact ordForm_pullbackRationalPluriForms_congr hG.comp_eq.symm E σ

/-- The order of a quotient of nonzero rational functions is the difference of the orders. -/
private theorem ord_mul_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (x : X) :
    X.ord (a * b⁻¹) x = X.ord a x - X.ord b x := by
  have hinv : X.ord b⁻¹ x = -X.ord b x := by
    have := MMP.Mori.ord_zpow x hb (-1)
    rwa [zpow_neg, zpow_one, neg_one_mul] at this
  rw [Scheme.ord_mul ha (inv_ne_zero hb), hinv]
  ring

/-! ### The discrepancy comparison through the graph divisor -/

/-- **The comparison of discrepancies is the graph divisor** (the formula
`a(ξ; X⁺, B⁺) - a(ξ; X⁻, B⁻) = ξ(H)`). For a model `w : W ⟶ G` and a prime divisor `E` of `W`,
there are `M > 0` and a local equation `φ` of `M H` near `w(η_E)` with
`M (a(E; X⁺, B⁺) - a(E; X⁻, B⁻)) = v_E(w^*φ)`. -/
private theorem exists_ord_eq_mul_sub (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {w : W ⟶ D.G}
    [IsDominant w] [IsProper w] (hW : IsNormalVariety ℂ ((w ≫ D.u) ≫ sXm))
    (hW' : IsNormalVariety ℂ ((w ≫ D.v) ≫ sXp)) (hb : IsBirationalMorphism (w ≫ D.u))
    (hb' : IsBirationalMorphism (w ≫ D.v)) (E : MMP.Mori.PrimeDivisor W)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ sXm).valuation = ξ)
    (hξp : (⟨W, w ≫ D.v, hW', hb', E⟩ : DivisorOver ℂ sXp).valuation = ξp)
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap) :
    ∃ (M : ℕ) (φ : D.G.functionField), 0 < M ∧ φ ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor D.G, w E.genericPoint ∈ Γ.support →
        (D.G.ord φ Γ.genericPoint : ℚ) = M * H Γ) ∧
      (M : ℝ) * (ap - am) = W.ord (functionFieldMap w φ) E.genericPoint := by
  classical
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hbm := h.isBirationalMorphism_minus
  have hbp := h.isBirationalMorphism_plus
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI := hb.isDominant
  haveI := hb'.isDominant
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  obtain ⟨n, hK⟩ := h.isCanonicalDivisor
  have hnm : topologicalKrullDim Xm = n := hK.topologicalKrullDim_eq
  obtain rfl := h.comp_eq_minus
  obtain rfl := h.comp_eq_plus
  haveI : LocallyOfFiniteType (fm ≫ sZ) := hXm.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hXp.1.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ sZ := hZ.1
  haveI : MMP.Mori.IsVariety ℂ (fm ≫ sZ) := hXm.1
  haveI : MMP.Mori.IsVariety ℂ (fp ≫ sZ) := hXp.1
  have hnZ : topologicalKrullDim Z = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fm ≫ sZ)
      hbm).trans hnm
  have hnp : topologicalKrullDim Xp = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (k := ℂ) sZ (fp ≫ sZ)
      hbp).symm.trans hnZ
  have hdZ := MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hnZ
  -- the common differential
  obtain ⟨ω₀, hω₀, hω₀K⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXm hK
  obtain ⟨σ, rfl, hσ⟩ :=
    exists_pullbackRationalPluriForms_eq fm hbm.functionFieldMap_bijective hdZ ω₀
  have hσ0 := hσ hω₀
  have hωp0 := pullbackRationalPluriForms_ne_zero fp hbp.functionFieldMap_bijective hdZ hσ0
  have hωpK := ordForm_pullbackRationalPluriForms_eq_flipTransform h D hnZ σ hω₀K
  -- Cartier multiples of `D^±`
  obtain ⟨m₁, hm₁, L₁₀, hL₁₀, hL₁₀c⟩ := h.isQCartier_minus.exists_pos
  obtain ⟨m₂, hm₂, L₂₀, hL₂₀, hL₂₀c⟩ := h.isQCartier_plus.exists_pos
  set M := m₁ * m₂ with hMdef
  have hM : 0 < M := Nat.mul_pos hm₁ hm₂
  set L₁ : Divisor Xm := (m₂ : ℤ) • L₁₀ with hL₁def
  set L₂ : Divisor Xp := (m₁ : ℤ) • L₂₀ with hL₂def
  have hL₁ : Divisor.toQDivisor L₁ = (M : ℤ) • (Divisor.toQDivisor K + B) := by
    rw [hL₁def, map_zsmul, hL₁₀, smul_smul, hMdef]
    push_cast
    rw [mul_comm]
  have hL₂ : Divisor.toQDivisor L₂ = (M : ℤ) •
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) := by
    rw [hL₂def, map_zsmul, hL₂₀, smul_smul, hMdef]
    push_cast
    rfl
  have hL₁c : L₁.IsCartier := hL₁₀c.zsmul _
  have hL₂c : L₂.IsCartier := hL₂₀c.zsmul _
  have cL₁ : ∀ Γ, (L₁ Γ : ℚ) = M * ((K Γ : ℚ) + B Γ) := fun Γ => by
    have := congrArg (fun G : QDivisor Xm => G Γ) hL₁
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at this
    exact this
  have cL₂ : ∀ Γ, (L₂ Γ : ℚ) =
      M * ((flipTransform fm fp K Γ : ℚ) + flipTransform fm fp B Γ) := fun Γ => by
    have := congrArg (fun G : QDivisor Xp => G Γ) hL₂
    simp only [Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast] at this
    exact this
  -- local equations near the centres
  set xm := (w ≫ D.u) E.genericPoint with hxm
  set xp := (w ≫ D.v) E.genericPoint with hxp
  obtain ⟨U₁, hxU₁, ψ₁, hψ₁⟩ := hL₁c xm
  obtain ⟨U₂, hxU₂, ψ₂, hψ₂⟩ := hL₂c xp
  set φ₁ := MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent xm)
    (ψ₁ : MMP.Mori.RationalFunctions Xm) with hφ₁def
  set φ₂ := MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent xp)
    (ψ₂ : MMP.Mori.RationalFunctions Xp) with hφ₂def
  have hφ₁ : φ₁ ≠ 0 := (ψ₁.isUnit.map _).ne_zero
  have hφ₂ : φ₂ ≠ 0 := (ψ₂.isUnit.map _).ne_zero
  -- the two log discrepancies
  have em := mul_sub_one_eq_of_isValuationLogDiscrepancy hXm hnm ham _ hξ hω₀ hM hφ₁
    fun Γ hΓ => by
      rw [ord_evalFF_eq_coeff hψ₁ hxU₁ Γ hΓ, hω₀K Γ]
      exact_mod_cast cL₁ Γ
  have ep := mul_sub_one_eq_of_isValuationLogDiscrepancy hXp hnp hap _ hξp hωp0 hM hφ₂
    fun Γ hΓ => by
      rw [ord_evalFF_eq_coeff hψ₂ hxU₂ Γ hΓ, hωpK Γ]
      exact_mod_cast cL₂ Γ
  -- the common form along `E`
  have hgf : IsBirationalMorphism ((w ≫ D.u) ≫ fm) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fm (w ≫ D.u)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbm)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  have hgf' : IsBirationalMorphism ((w ≫ D.v) ≫ fp) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational fp (w ≫ D.v)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbp)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb')
  have e1 := ordPullback_pullbackRationalPluriForms fm hbm hdZ hW hb hgf E σ
  have e2 := ordPullback_pullbackRationalPluriForms fp hbp hdZ hW' hb' hgf' E σ
  haveI := hgf.isDominant
  haveI := hgf'.isDominant
  have hv : (⟨W, (w ≫ D.v) ≫ fp, hW', hgf', E⟩ : DivisorOver ℂ sZ).valuation =
      (⟨W, (w ≫ D.u) ≫ fm, hW, hgf, E⟩ : DivisorOver ℂ sZ).valuation := by
    change E.valuationOver ((w ≫ D.v) ≫ fp) = E.valuationOver ((w ≫ D.u) ≫ fm)
    simp only [Category.assoc, hG.comp_eq]
  have e3 := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hZ hnZ hv σ
  -- the rational function on `G`
  set φ := functionFieldMap D.u φ₁ * (functionFieldMap D.v φ₂)⁻¹ with hφdef
  have hu₁ : functionFieldMap D.u φ₁ ≠ 0 := (map_ne_zero _).mpr hφ₁
  have hv₂ : functionFieldMap D.v φ₂ ≠ 0 := (map_ne_zero _).mpr hφ₂
  refine ⟨M, φ, hM, mul_ne_zero hu₁ (inv_ne_zero hv₂), fun Γ hΓ => ?_, ?_⟩
  · obtain ⟨Hm, Hp, hm, hp, hHm, hHp, hHeq⟩ := hH.exists_pullback
    obtain ⟨L₁', hL₁', hpb₁⟩ := hHm M hM L₁ hL₁ hL₁c
    obtain ⟨L₂', hL₂', hpb₂⟩ := hHp M hM L₂ hL₂ hL₂c
    have hsp : Γ.genericPoint ⤳ w E.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓ
    have hU₁ : D.u Γ.genericPoint ∈ U₁ := (hsp.map D.u.continuous).mem_open U₁.2 hxU₁
    have hU₂ : D.v Γ.genericPoint ∈ U₂ := (hsp.map D.v.continuous).mem_open U₂.2 hxU₂
    have c1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpb₁ hψ₁ Γ hU₁
      (MMP.Mori.pointComponent xm)
    have c2 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpb₂ hψ₂ Γ hU₂
      (MMP.Mori.pointComponent xp)
    have d1 := congrArg (fun G : QDivisor D.G => G Γ) hL₁'
    have d2 := congrArg (fun G : QDivisor D.G => G Γ) hL₂'
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at d1 d2
    change (L₁' Γ : ℚ) = M * Hm Γ at d1
    change (L₂' Γ : ℚ) = M * Hp Γ at d2
    rw [ord_mul_inv hu₁ hv₂, hHeq, Finsupp.sub_apply]
    change (L₁'.coeff Γ : ℚ) = _ at d1
    rw [c1] at d1
    change (L₂'.coeff Γ : ℚ) = _ at d2
    rw [c2] at d2
    push_cast
    rw [d1, d2]
    ring
  · rw [map_mul, map_inv₀, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      ord_mul_inv ((map_ne_zero _).mpr hφ₁) ((map_ne_zero _).mpr hφ₂)]
    have e4 : (⟨W, w ≫ D.u, hW, hb, E⟩ : DivisorOver ℂ (fm ≫ sZ)).ordPullback
        (pullbackRationalPluriForms sZ fm σ) =
        (⟨W, w ≫ D.v, hW', hb', E⟩ : DivisorOver ℂ (fp ≫ sZ)).ordPullback
          (pullbackRationalPluriForms sZ fp σ) := by
      rw [e1, e2, e3]
    change (M : ℝ) * (am - 1) = M * _ - _ at em
    change (M : ℝ) * (ap - 1) = M * _ - _ at ep
    rw [e4] at em
    push_cast
    linear_combination ep - em

/-! ### Proper curves and intersection numbers -/

section Curves

open MMP.Flips

universe u

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
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
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

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem IsCartierIntersectionNumber.eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

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
    have : ({p'} : Set (f.fiber x)) = ι ⁻¹' {p} := by
      ext z
      simp [← hp', hemb.injective.eq_iff]
    rw [this]
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
  have hCf : C.IsContractedBy f := fun z hz => by
    have h1 := hclF hz
    have h2 := hclF (subset_closure rfl : ι y' ∈ closure {ι y'})
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  refine ⟨C, hCf, ?_, ?_⟩
  · rw [hrC]
    exact fun h => hy'S (h (subset_closure rfl))
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

end Curves

/-! ### Effectivity and support of the graph divisor -/

/-- **`-H` is positive on contracted curves.** The graph divisor is `H = -(1/m) L` for a Cartier
divisor `L = -mH`, `m > 0`, ample relative to `g = u ≫ f⁻`; so `L` has positive degree on every
proper curve contracted by `g`. -/
private theorem exists_eq_smul_degreeOn_pos (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) :
    ∃ (m : ℕ) (L : Divisor D.G) (hL : L.IsCartier), 0 < m ∧
      QDivisor.toRDivisor H = (-1 / (m : ℝ)) • Divisor.toRDivisor L ∧
      ∀ C : MMP.Mori.ProperCurve (D.u ≫ sXm), C.IsContractedBy (D.u ≫ fm) →
        0 < L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL := by
  obtain ⟨m, hm, L, hL, hLq, hamp⟩ := hH.hasRelativelyAmpleMultiple_neg
  refine ⟨m, L, hL, hm, ?_, fun C hC => ?_⟩
  · ext P
    have h1 := congrArg (fun G : QDivisor D.G => G P) hLq
    simp only [Finsupp.smul_apply, Finsupp.neg_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((L P : ℤ) : ℚ) = _ at h1
    change ((H P : ℚ) : ℝ) = (-1 / (m : ℝ)) * ((L P : ℤ) : ℝ)
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have h2 : ((L P : ℤ) : ℝ) = m * (-((H P : ℚ) : ℝ)) := by exact_mod_cast h1
    rw [h2]
    field_simp
  · haveI := hL.isInvertibleModule_divisorialSheaf
    exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
      (D.u ≫ fm) L.divisorialSheaf hamp C hC

/-- The graph divisor, as an `ℝ`-divisor, is a combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_of_eq_smul {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {H : QDivisor X} {L : Divisor X} (hL : L.IsCartier)
    {c : ℝ} (hHL : QDivisor.toRDivisor H = c • Divisor.toRDivisor L) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor H) :=
  ⟨1, ![c], ![L], fun j => by rwa [Fin.fin_one_eq_zero j], by
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]; exact hHL⟩

/-- **`-H` is `g`-nef.** -/
private theorem isRelativelyNef_neg_toRDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H) :
    MMP.Flips.IsRelativelyNef ℂ (D.u ≫ sXm) (D.u ≫ fm) (-QDivisor.toRDivisor H) := by
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  obtain ⟨m, L, hL, hm, hHL, hpos⟩ := exists_eq_smul_degreeOn_pos h D hH
  refine ⟨1, ![1 / (m : ℝ)], ![L], fun j => by rwa [Fin.fin_one_eq_zero j], ?_,
    fun C hC x hx => ?_⟩
  · rw [hHL, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, ← neg_smul]
    congr 1
    ring
  · obtain ⟨hL', d, -, hd, hxd⟩ := hx
    have h0 := IsCartierIntersectionNumber.eq_degreeOn ℂ (D.u ≫ sXm) (hd 0)
    have hp := hpos C hC
    rw [hxd]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [h0]
    have : (0 : ℝ) < (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) := by exact_mod_cast hp
    exact mul_nonneg (by positivity) this.le

/-- **The graph divisor is effective**, by the negativity lemma: `-H` is `g`-nef, and `H`
vanishes along every prime divisor of `G` that is not exceptional over `Z`, since such a divisor
lies over a point of codimension one of `Z`, where both `f^±` are isomorphisms. -/
private theorem coeff_nonneg_of_isGraphDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    (Γ : MMP.Mori.PrimeDivisor D.G) : 0 ≤ H Γ := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hGv := isNormalVariety_graph h D
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  have hbg := isBirationalMorphism_graph h D
  have hf : (D.u ≫ fm) ≫ sZ = D.u ≫ sXm := by rw [Category.assoc, h.comp_eq_minus]
  obtain ⟨m, L, hL, hm, hHL, -⟩ := exists_eq_smul_degreeOn_pos h D hH
  have hB := isCartierCombination_toRDivisor_of_eq_smul hL hHL
  have hnef := isRelativelyNef_neg_toRDivisor h D hH
  have hM : MMP.Flips.IsCartierCombination (-QDivisor.toRDivisor H) := by
    obtain ⟨n, r, Ls, hLs, hpres⟩ := hB
    exact ⟨n, -r, Ls, hLs, by rw [hpres]; simp [Finset.sum_neg_distrib, neg_smul]⟩
  have h0Z : MMP.Flips.IsCartierCombination (0 : RDivisor Z) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have h0G : MMP.Flips.IsCartierCombination (0 : RDivisor D.G) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  have hpb0 : MMP.Flips.IsRCartierPullback (D.u ≫ fm) (0 : RDivisor Z) 0 :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hnum : MMP.Flips.IsNumericallyEquivalentOver ℂ (D.u ≫ sXm) (D.u ≫ fm) 0
      (-QDivisor.toRDivisor H + QDivisor.toRDivisor H) := by
    rw [neg_add_cancel]
    exact ⟨h0G, h0G, fun C _ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ =>
      (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ (D.u ≫ sXm) C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sZ
  have heff := MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback ℂ sZ (D.u ≫ sXm)
    hZ hGv (D.u ≫ fm) hf hbg h0Z hpb0 hM hnef hB (fun P hP => by
      have hco : Order.coheight ((D.u ≫ fm) P.genericPoint) ≤ 1 := by
        by_contra hc
        rw [not_le] at hc
        apply hP
        refine ⟨by rwa [hf], hbg, inferInstance, ?_⟩
        unfold MMP.Flips.ProperDivisorOver.IsExceptional
        rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
          DivisorOver.center_eq_closure_genericPoint, hn]
        have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ
          ((D.u ≫ fm) P.genericPoint)
        rw [hn] at hd
        exact (withBot_add_two_le_iff hd).mpr (Order.add_one_le_of_lt hc)
      have hx : ringKrullDim (Z.presheaf.stalk ((D.u ≫ fm) P.genericPoint)) ≤ 1 := by
        rw [ringKrullDim_stalk_eq_coheight]
        exact_mod_cast hco
      have hzm := MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZ fm
        (by rw [h.comp_eq_minus]; exact h.isNormalVariety_minus.1) h.isBirationalMorphism_minus hx
      have hzp := MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hZ fp
        (by rw [h.comp_eq_plus]; exact h.isNormalVariety_plus.1) h.isBirationalMorphism_plus hx
      rw [QDivisor.coeff_toRDivisor]
      have := coeff_eq_zero_of_mem_commonBiregularLocus h D hH P ⟨hzm, hzp⟩
      change (0 : ℝ) ≤ ((H P : ℚ) : ℝ)
      rw [this]
      simp) hnum
  have := heff Γ
  rw [QDivisor.coeff_toRDivisor] at this
  exact_mod_cast this

/-- A point of the bad locus of the base lies outside the biregular locus of the structure map
`g = u ≫ f⁻` of the normalized graph: over the biregular locus the fibres of `g`, hence those of
`f^±`, are single points. -/
private theorem notMem_biregularLocus_of_mem_badLocusBase
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h) {z : Z}
    (hz : z ∈ badLocusBase fm fp) : z ∉ biregularLocus (D.u ≫ fm) := by
  intro hzg
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  have hG := D.isNormalizedGraph
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  haveI : IsIso ((D.u ≫ fm) ∣_ biregularLocus (D.u ≫ fm)) :=
    isBiregular_biregularLocus (D.u ≫ fm)
  have hs := MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict
    (D.u ≫ fm) _ hzg
  refine hz ⟨?_, ?_⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_minus.1 hZ.1 fm h.comp_eq_minus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)
      ((hs.finite.image D.u).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.u.surjective a
    exact ⟨x, ha, rfl⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_plus.1 hZ.1 fp h.comp_eq_plus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_plus)
      ((hs.finite.image D.v).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.v.surjective a
    refine ⟨x, ?_, rfl⟩
    change (D.u ≫ fm) x = z
    rwa [hG.comp_eq]

/-- **The support of the graph divisor contains `g⁻¹(Σ)`.** By the negativity lemma over a point,
the fibre of `g` over `g(y)` lies in `Supp H` or misses it. In the second case `H = 0` near a
closed point `y₀ ∈ cl{y}`, which lies over `Σ`, so off the biregular locus of `g`; a proper curve
contracted by `g` through `y₀` then misses `Supp H`, so `H · C ≥ 0`, while `-H` is `g`-ample. -/
private theorem exists_mem_support_coeff_ne_zero (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {y : D.G} (hy : (D.u ≫ fm) y ∈ badLocusBase fm fp) :
    ∃ Γ : MMP.Mori.PrimeDivisor D.G, y ∈ Γ.support ∧ H Γ ≠ 0 := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  have hGv := isNormalVariety_graph h D
  haveI : QuasiCompact (D.u ≫ sXm) := (isVariety_graph h D).toQuasiCompact
  haveI : LocallyOfFiniteType (D.u ≫ sXm) := (isVariety_graph h D).toLocallyOfFiniteType
  haveI : JacobsonSpace D.G := LocallyOfFiniteType.jacobsonSpace (D.u ≫ sXm)
  have hbg := isBirationalMorphism_graph h D
  have hf : (D.u ≫ fm) ≫ sZ = D.u ≫ sXm := by rw [Category.assoc, h.comp_eq_minus]
  obtain ⟨m, L, hL, hm, hHL, hpos⟩ := exists_eq_smul_degreeOn_pos h D hH
  have hB := isCartierCombination_toRDivisor_of_eq_smul hL hHL
  have hnef := isRelativelyNef_neg_toRDivisor h D hH
  have hBeff : (QDivisor.toRDivisor H).IsEffective := fun P => by
    rw [QDivisor.coeff_toRDivisor]
    exact_mod_cast coeff_nonneg_of_isGraphDivisor h D hH P
  set S := (QDivisor.toRDivisor H).supp with hS
  rcases MMP.Flips.preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg ℂ sZ
    (D.u ≫ sXm) hZ hGv (D.u ≫ fm) hf hbg hB hBeff hnef ((D.u ≫ fm) y) with hsub | hdis
  · obtain ⟨Γ, hΓ, hyΓ⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp (hsub rfl)
    refine ⟨Γ, hyΓ, fun h0 => hΓ ?_⟩
    rw [QDivisor.coeff_toRDivisor]
    change ((H Γ : ℚ) : ℝ) = 0
    rw [h0]
    simp
  · exfalso
    set g := D.u ≫ fm with hg
    have hSc : IsClosed (g '' (S : Set D.G)) := g.isClosedMap _ S.isClosed
    have hyV : y ∈ g ⁻¹' (g '' (S : Set D.G))ᶜ := by
      rintro ⟨s, hs, hgs⟩
      exact Set.disjoint_left.mp hdis (show s ∈ g.base ⁻¹' {g y} from hgs) hs
    have hT : IsLocallyClosed (closure {y} ∩ g ⁻¹' (g '' (S : Set D.G))ᶜ) :=
      isClosed_closure.isLocallyClosed.inter
        (hSc.isOpen_compl.preimage g.continuous).isLocallyClosed
    have hne : (closure {y} ∩ g ⁻¹' (g '' (S : Set D.G))ᶜ).Nonempty :=
      ⟨y, subset_closure rfl, hyV⟩
    obtain ⟨y₀, ⟨hy₀y, hy₀V⟩, hy₀c⟩ := nonempty_inter_closedPoints hne hT
    have hz₀ : g y₀ ∈ badLocusBase fm fp :=
      ((specializes_iff_mem_closure.mpr hy₀y).map g.continuous).mem_closed
        (badLocusBase fm fp).isClosed hy
    obtain ⟨C, hCf, hCy₀⟩ := exists_properCurve_specializes ℂ sZ (D.u ≫ sXm) hZ hGv g hf hbg
      y₀ (mem_closedPoints_iff.mp hy₀c) (notMem_biregularLocus_of_mem_badLocusBase h D hz₀)
    have hgC : g C.point = g y₀ := (hCf y₀ (specializes_iff_mem_closure.mp hCy₀)).symm
    have hCS : C.point ∉ S := fun hCS => hy₀V ⟨C.point, hCS, hgC⟩
    have hx := isRIntersectionNumber_sum_degreeOn ℂ (D.u ≫ sXm) C ![-1 / (m : ℝ)] ![L]
      (fun j => by rwa [Fin.fin_one_eq_zero j])
    rw [show ∑ j, ![-1 / (m : ℝ)] j • Divisor.toRDivisor (![L] j) = QDivisor.toRDivisor H by
      rw [hHL, Fin.sum_univ_one]; rfl] at hx
    have hnn := MMP.Flips.IsRIntersectionNumber.nonneg_of_isEffective ℂ (D.u ≫ sXm) hGv _ hB
      hBeff C hCS _ _ hx
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hnn
    have hp : (0 : ℝ) < (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) := by
      exact_mod_cast hpos C hCf
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have : -1 / (m : ℝ) * (L.degreeOn ℂ (D.u ≫ sXm) C.ι C.dim_le hL : ℝ) < 0 :=
      mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) hm') hp
    linarith

/-! ### Orders of pull-backs at the centre -/

/-- A rational function with order zero along every prime divisor through `f(η_E)` has
order zero along `E` after pull-back. -/
private theorem ord_functionFieldMap_eq_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y) {φ : X.functionField} (hφ : φ ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support →
      X.ord φ Γ.genericPoint = 0) :
    Y.ord (functionFieldMap f φ) E.genericPoint = 0 := by
  have := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := f) E (fun _ : Unit => φ)
    (fun _ => hφ) (fun _ => 1) fun Γ hΓ => by simp [h Γ hΓ]
  simpa using this

/-- A rational function with nonnegative order along every prime divisor through `f(η_E)`, and
positive order along one of them, has positive order along `E` after pull-back. -/
private theorem ord_functionFieldMap_pos {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y) {φ : X.functionField} (hφ : φ ≠ 0)
    (h : ∀ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support →
      0 ≤ X.ord φ Γ.genericPoint)
    (h' : ∃ Γ : MMP.Mori.PrimeDivisor X, f E.genericPoint ∈ Γ.support ∧
      0 < X.ord φ Γ.genericPoint) :
    0 < Y.ord (functionFieldMap f φ) E.genericPoint := by
  obtain ⟨Γ₀, hΓ₀, hpos⟩ := h'
  obtain ⟨r, hr⟩ :=
    MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg _ hφ h
  have hrm : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (f E.genericPoint)) := by
    by_contra hru
    have hu : IsUnit r := by
      by_contra hu'
      exact hru ((IsLocalRing.mem_maximalIdeal _).mpr hu')
    have hsp : Γ₀.genericPoint ⤳ f E.genericPoint := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hΓ₀
    have hr' : algebraMap Γ₀.localRing X.functionField
        ((X.presheaf.stalkSpecializes hsp).hom r) = φ := by
      rw [MMP.Mori.algebraMap_stalkSpecializes, hr]
    have hlt := (Γ₀.divisorialValuation_algebraMap_lt_one_iff
      ((X.presheaf.stalkSpecializes hsp).hom r)).mp (by
        rw [hr', Γ₀.divisorialValuation_eq_exp_neg_ord hφ, ← WithZero.exp_zero,
          WithZero.exp_lt_exp]
        omega)
    exact (IsLocalRing.mem_maximalIdeal _).mp hlt (hu.map _)
  have hs : (f.stalkMap E.genericPoint).hom r ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) := by
    rw [IsLocalRing.mem_maximalIdeal] at hrm ⊢
    exact (map_mem_nonunits_iff _ _).mpr hrm
  have hfφ : functionFieldMap f φ =
      algebraMap E.localRing Y.functionField ((f.stalkMap E.genericPoint).hom r) := by
    rw [← hr, MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hlt := (E.divisorialValuation_algebraMap_lt_one_iff _).mpr hs
  rw [← hfφ, E.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hφ), ← WithZero.exp_zero,
    WithZero.exp_lt_exp] at hlt
  omega

/-- **The graph divisor detects the bad locus at the centre.** Let `w : W ⟶ G` be a model,
`E` a prime divisor of `W`, and `φ` a rational function on `G` with `v_Γ(φ) = M coeff_Γ(H)`,
`M > 0`, along every prime divisor `Γ` through `y = w(η_E)`. Then `v_E(w^*φ) > 0` exactly when
`g(y) ∈ Σ`: over `Z ∖ Σ` the divisor `H` vanishes near `y`, while over `Σ` it is effective and
nonzero along some prime divisor through `y`. -/
private theorem ord_functionFieldMap_pos_iff (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) {H : QDivisor D.G} (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v H)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (w : W ⟶ D.G)
    [IsDominant w] (E : MMP.Mori.PrimeDivisor W) {M : ℕ} (hM : 0 < M) {φ : D.G.functionField}
    (hφ : φ ≠ 0) (hφΓ : ∀ Γ : MMP.Mori.PrimeDivisor D.G, w E.genericPoint ∈ Γ.support →
      (D.G.ord φ Γ.genericPoint : ℚ) = M * H Γ) :
    0 < W.ord (functionFieldMap w φ) E.genericPoint ↔
      (D.u ≫ fm) (w E.genericPoint) ∈ badLocusBase fm fp := by
  refine ⟨fun hpos => ?_, fun hmem => ?_⟩
  · by_contra hnm
    have hU : (D.u ≫ fm) (w E.genericPoint) ∈ commonBiregularLocus fm fp := by
      by_contra hU
      exact hnm (by rwa [← SetLike.mem_coe, coe_badLocusBase])
    have h0 := ord_functionFieldMap_eq_zero w E hφ fun Γ hΓ => by
      have hsp : Γ.genericPoint ⤳ w E.genericPoint := by
        rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      have := hφΓ Γ hΓ
      rw [coeff_eq_zero_of_mem_commonBiregularLocus h D hH Γ
        ((hsp.map (D.u ≫ fm).continuous).mem_open (commonBiregularLocus fm fp).2 hU),
        mul_zero] at this
      exact_mod_cast this
    exact hpos.ne' h0
  · obtain ⟨Γ₀, hΓ₀, hΓ₀H⟩ := exists_mem_support_coeff_ne_zero h D hH hmem
    refine ord_functionFieldMap_pos w E hφ (fun Γ hΓ => ?_) ⟨Γ₀, hΓ₀, ?_⟩
    · have : (0 : ℚ) ≤ D.G.ord φ Γ.genericPoint := by
        rw [hφΓ Γ hΓ]
        have := coeff_nonneg_of_isGraphDivisor h D hH Γ
        positivity
      exact_mod_cast this
    · have : (0 : ℚ) < D.G.ord φ Γ₀.genericPoint := by
        rw [hφΓ Γ₀ hΓ₀]
        exact mul_pos (by exact_mod_cast hM)
          ((coeff_nonneg_of_isGraphDivisor h D hH Γ₀).lt_of_ne hΓ₀H.symm)
      exact_mod_cast this

/-! ### Centres -/

/-- The centre of a normalized divisorial valuation `ξ = ord_E`, for a divisor `(W, g, E)`
over `X`, is the closure of `g(η_E)`. -/
private theorem coe_eq_closure_of_isCentre {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    {ξ : Valuation X.functionField (WithZero (Multiplicative ℤ))} {C : IrreducibleCloseds X}
    (hC : MMP.Intersection.IsCentre ℂ sX ξ C) (D : DivisorOver ℂ sX) (hD : D.valuation = ξ) :
    (C : Set X) = closure {D.f D.E.genericPoint} := by
  obtain ⟨D₀, -, hv₀, rfl⟩ := hC
  rw [D₀.center_eq_closure_genericPoint,
    MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX (hv₀.symm.trans hD.symm)]

/-- The closure of a point lies in the preimage `f⁻¹(S)` of the closed set `S` exactly when the
image of the point lies in `S`. -/
private theorem closure_subset_preimage_iff {X Y : Scheme.{0}} (f : X ⟶ Y) (S : Closeds Y)
    (x : X) : closure {x} ⊆ f ⁻¹' (S : Set Y) ↔ f x ∈ S :=
  ⟨fun hs => hs (subset_closure rfl),
    fun hx => closure_minimal (Set.singleton_subset_iff.mpr hx) (S.isClosed.preimage f.continuous)⟩

/-- `ξ⁺`, the valuation of `k(X⁺)` corresponding to `ξ = ord_E`, is `ord_E` for `(W, g', E)`. -/
private theorem valuation_eq_of_comap_eq {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} [IsIntegral Z]
    [IsDominant fm] [IsDominant fp] (hfp : IsBirationalMorphism fp) {W : Scheme.{0}}
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {g : W ⟶ Xm} {g' : W ⟶ Xp}
    (hW : IsNormalVariety ℂ (g ≫ sXm)) (hW' : IsNormalVariety ℂ (g' ≫ sXp))
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hcomm : g ≫ fm = g' ≫ fp)
    (E : MMP.Mori.PrimeDivisor W) {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : ξp.comap (functionFieldMap fp) =
      (⟨W, g, hW, hg, E⟩ : DivisorOver ℂ sXm).valuation.comap (functionFieldMap fm)) :
    (⟨W, g', hW', hg', E⟩ : DivisorOver ℂ sXp).valuation = ξp := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ sXm)
  haveI : IsDominant g := hg.isDominant
  haveI : IsDominant g' := hg'.isDominant
  have hinj : Function.Injective
      (Valuation.comap (Γ₀ := WithZero (Multiplicative ℤ)) (functionFieldMap fp)) := by
    intro v w hvw
    ext x
    obtain ⟨y, rfl⟩ := hfp.functionFieldMap_bijective.2 x
    exact congrArg (fun v => v y) hvw
  apply hinj
  rw [hξ]
  ext x
  simp only [Valuation.comap_apply]
  change E.divisorialValuation (functionFieldMap g' (functionFieldMap fp x)) =
    E.divisorialValuation (functionFieldMap g (functionFieldMap fm x))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  simp only [hcomm]

/-! ### The comparison theorem -/

/-- **Strictness of the comparison.** In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of fourfolds,
let `ξ` be a normalized divisorial valuation of `k(X⁻)` and `ξ⁺` the corresponding valuation of
`k(X⁺)` (the one with the same restriction to `k(Z)`). Write `a⁻ = a(ξ; X⁻, B⁻)` and
`a⁺ = a(ξ⁺; X⁺, B⁺)`, and let `C⁻ = c_{X⁻}(ξ)` and `C⁺ = c_{X⁺}(ξ⁺)` be the centres. Then the
following are equivalent: `a⁻ < a⁺`; `C⁻ ⊆ W⁻`; `C⁺ ⊆ W⁺`. -/
@[mmp "lem_oai4_graph_b"]
public theorem IsFourfoldStepDiagram.tfae_lt_and_centre_subset_badLocus
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    {ξ : Valuation Xm.functionField (WithZero (Multiplicative ℤ))}
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      ξp.comap (functionFieldMap fp) = ξ.comap (functionFieldMap fm))
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B ξ am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap)
    {Cm : IrreducibleCloseds Xm} {Cp : IrreducibleCloseds Xp}
    (hCm : MMP.Intersection.IsCentre ℂ sXm ξ Cm) (hCp : MMP.Intersection.IsCentre ℂ sXp ξp Cp) :
    List.TFAE [am < ap, (Cm : Set Xm) ⊆ badLocusMinus fm fp,
      (Cp : Set Xp) ⊆ badLocusPlus fm fp] := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isBirationalMorphism_plus.isDominant
  obtain ⟨D⟩ := exists_graphData h
  obtain ⟨H, hH⟩ := exists_isGraphDivisor h D
  have hG := D.isNormalizedGraph
  have hCm' := hCm
  obtain ⟨D₀, -, rfl, -⟩ := hCm'
  obtain ⟨W, w, hW, hb, hwp, hw, E, hE⟩ := exists_model h D D₀
  haveI := hwp
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : IsLocallyNoetherian W :=
    haveI := hW.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((w ≫ D.u) ≫ sXm)
  haveI : IsDominant w := hw.isDominant
  have hcomm : (w ≫ D.u) ≫ fm = (w ≫ D.v) ≫ fp := by
    rw [Category.assoc, Category.assoc, hG.comp_eq]
  have hW' : IsNormalVariety ℂ ((w ≫ D.v) ≫ sXp) := by
    have e : (w ≫ D.v) ≫ sXp = (w ≫ D.u) ≫ sXm := calc
      (w ≫ D.v) ≫ sXp = (w ≫ D.v) ≫ fp ≫ sZ := by rw [h.comp_eq_plus]
      _ = (w ≫ D.u) ≫ fm ≫ sZ := by rw [← Category.assoc, ← hcomm, Category.assoc]
      _ = (w ≫ D.u) ≫ sXm := by rw [h.comp_eq_minus]
    rwa [e]
  have hb' : IsBirationalMorphism (w ≫ D.v) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational D.v w
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hG.isBirationalMorphism_plus)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hw)
  set Dm : DivisorOver ℂ sXm := ⟨W, w ≫ D.u, hW, hb, E⟩ with hDm
  set Dp : DivisorOver ℂ sXp := ⟨W, w ≫ D.v, hW', hb', E⟩ with hDp
  have hDpv : Dp.valuation = ξp :=
    valuation_eq_of_comap_eq h.isBirationalMorphism_plus hW hW' hb hb' hcomm E
      (by rwa [hE])
  -- the centres
  set z := (D.u ≫ fm) (w E.genericPoint) with hz
  have hCmc : (Cm : Set Xm) = closure {(w ≫ D.u) E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_minus hCm Dm hE
  have hCpc : (Cp : Set Xp) = closure {(w ≫ D.v) E.genericPoint} :=
    coe_eq_closure_of_isCentre h.isNormalVariety_plus hCp Dp hDpv
  have h2 : (Cm : Set Xm) ⊆ badLocusMinus fm fp ↔ z ∈ badLocusBase fm fp := by
    rw [hCmc, coe_badLocusMinus, closure_subset_preimage_iff fm]
    rfl
  have h3 : (Cp : Set Xp) ⊆ badLocusPlus fm fp ↔ z ∈ badLocusBase fm fp := by
    rw [hCpc, coe_badLocusPlus, closure_subset_preimage_iff fp, ← Scheme.Hom.comp_apply,
      ← hcomm, hz]
    rfl
  -- the discrepancies
  obtain ⟨M, φ, hM, hφ, hφΓ, hkey⟩ :=
    exists_ord_eq_mul_sub h D hH hW hW' hb hb' E hE hDpv ham hap
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : am < ap ↔ z ∈ badLocusBase fm fp := by
    rw [← sub_pos, ← mul_pos_iff_of_pos_left hM', hkey, Int.cast_pos]
    exact ord_functionFieldMap_pos_iff h D hH w E hM hφ hφΓ
  tfae_have 1 ↔ 2 := h1.trans h2.symm
  tfae_have 2 ↔ 3 := h2.trans h3.symm
  tfae_finish

/-! ### A trivial graph divisor forces an empty bad locus -/

/-- A quasi-affine scheme proper over an affine scheme is affine: its canonical morphism to the
spectrum of its global sections is a proper open immersion, hence a closed immersion. -/
private theorem isAffine_of_isQuasiAffine_of_isProper {R : CommRingCat.{0}} {X : Scheme.{0}}
    (f : X ⟶ Spec R) [IsProper f] [X.IsQuasiAffine] : IsAffine X := by
  have h : X.toSpecΓ ≫ Spec.map f.appTop = f ≫ (Spec R).toSpecΓ :=
    (Scheme.toSpecΓ_naturality f).symm
  have : IsProper (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [h]; infer_instance
  have : IsProper X.toSpecΓ := IsProper.of_comp _ (Spec.map f.appTop)
  have : IsClosedImmersion X.toSpecΓ :=
    .of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- If the zero divisor is ample relative to a proper morphism `f`, then `f` has finite fibres:
over an affine open `V` the preimage `f⁻¹(V)` carries an ample trivial sheaf, so it is
quasi-affine, hence affine, and `f⁻¹(V) ⟶ V` is affine and proper, that is, finite. -/
private theorem finite_preimage_of_isRelativelyAmple_zero {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y) [IsProper f]
    (hL : (0 : Divisor X).IsCartier) (hamp : (0 : Divisor X).IsRelativelyAmple f hL) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨V, hV, hyV, hA⟩ := hamp y
  let e : (RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
      (Divisor.divisorialSheaf (0 : Divisor X)) ≅ Stacks.Ample.unitModule (f ⁻¹ᵁ V) :=
    (RingedSpaceModuleAdjunction.modulePullback _).mapIso Divisor.divisorialSheafZeroIso ≪≫
      Stacks.RelativeAmple.pullbackUnitModuleIso (f ⁻¹ᵁ V).ι
  haveI : (f ⁻¹ᵁ V).toScheme.IsQuasiAffine :=
    (Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ e).mpr hA
  haveI : IsAffine V := hV
  haveI : IsAffine (f ⁻¹ᵁ V) :=
    isAffine_of_isQuasiAffine_of_isProper ((f ∣_ V) ≫ V.toScheme.isoSpec.hom)
  haveI : IsFinite (f ∣_ V) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  refine (((f ∣_ V).finite_preimage_singleton ⟨y, hyV⟩).image (f ⁻¹ᵁ V).ι).subset ?_
  intro x hx
  have hfx : f x = y := hx
  have hxV : x ∈ f ⁻¹ᵁ V := by
    change f x ∈ V
    rwa [hfx]
  refine ⟨⟨x, hxV⟩, ?_, rfl⟩
  change (f ∣_ V) ⟨x, hxV⟩ = ⟨y, hyV⟩
  exact Subtype.ext ((morphismRestrict_base_coe f V ⟨x, hxV⟩).trans hfx)

/-- **A trivial graph divisor forces an empty bad locus.** If `H = 0`, then `𝒪_G = 𝒪_G(-H)` is
ample relative to `g = u ≫ f⁻`, so `g` has finite fibres; as `u`, `v` are surjective, so do `f^±`,
and a proper birational morphism onto the normal `Z` is an isomorphism over every point with
finite fibre. -/
private theorem badLocusBase_eq_empty_of_isGraphDivisor_zero
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (D : GraphData h)
    (hH : IsGraphDivisor sXm sZ sXp K B fm fp D.u D.v 0) :
    (badLocusBase fm fp : Set Z) = ∅ := by
  have hG := D.isNormalizedGraph
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := h.isProper_plus
  haveI := hG.isBirationalMorphism_minus.isDominant
  haveI := hG.isBirationalMorphism_plus.isDominant
  obtain ⟨m, -, L, hL, hLq, hamp⟩ := hH.hasRelativelyAmpleMultiple_neg
  have hL0 : L = 0 := Divisor.toQDivisor_injective (by rw [hLq, neg_zero, smul_zero, map_zero])
  subst hL0
  have hfin := finite_preimage_of_isRelativelyAmple_zero (D.u ≫ fm) hL hamp
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  refine hz ⟨?_, ?_⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_minus.1 hZ.1 fm h.comp_eq_minus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_minus)
      (((hfin z).image D.u).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.u.surjective a
    exact ⟨x, ha, rfl⟩
  · refine mem_biregularLocus_of_finite h.isNormalVariety_plus.1 hZ.1 fp h.comp_eq_plus
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.isBirationalMorphism_plus)
      (((hfin z).image D.v).subset fun a ha => ?_)
    obtain ⟨x, rfl⟩ := D.v.surjective a
    refine ⟨x, ?_, rfl⟩
    change (D.u ≫ fm) x = z
    rwa [hG.comp_eq]

/-! ### Transcendence degrees -/

section Trdeg

open Cardinal

/-- **Transcendence degree of a compositum.** If a field `K` over `k` is algebraic over the
subfield generated by the images of two `k`-embeddings `A → K`, `B → K`, then
`trdeg_k K ≤ trdeg_k A + trdeg_k B`: the images of transcendence bases of `A` and `B` together
generate a subfield over which `K` is algebraic. -/
private theorem trdeg_le_add_of_isAlgebraic {k A B K : Type} [Field k] [Field A] [Field B]
    [Field K] [Algebra k A] [Algebra k B] [Algebra k K] (i : A →ₐ[k] K) (j : B →ₐ[k] K)
    (halg : ∀ c : K, IsAlgebraic (IntermediateField.adjoin k (Set.range i ∪ Set.range j)) c) :
    Algebra.trdeg k K ≤ Algebra.trdeg k A + Algebra.trdeg k B := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k A
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k B
  set T : Set K := i '' s ∪ j '' t with hT
  set F := IntermediateField.adjoin k T
  have key : ∀ {C : Type} [Field C] [Algebra k C] (φ : C →ₐ[k] K) (r : Set C),
      φ '' r ⊆ T → IsTranscendenceBasis k ((↑) : r → C) → ∀ c : C, IsAlgebraic F (φ c) := by
    intro C _ _ φ r hr hb c
    rw [IntermediateField.isAlgebraic_adjoin_iff]
    have h1 : IsAlgebraic (Algebra.adjoin k (Set.range ((↑) : r → C))) c :=
      hb.isAlgebraic.isAlgebraic c
    have hle : ∀ x ∈ Algebra.adjoin k (Set.range ((↑) : r → C)), φ x ∈ Algebra.adjoin k T := by
      intro x hx
      have : φ x ∈ (Algebra.adjoin k (Set.range ((↑) : r → C))).map φ :=
        Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
      rw [AlgHom.map_adjoin] at this
      refine Algebra.adjoin_mono ?_ this
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact hr ⟨y, y.2, rfl⟩
    let f : Algebra.adjoin k (Set.range ((↑) : r → C)) →ₐ[k] Algebra.adjoin k T :=
      (φ.comp (Algebra.adjoin k _).val).codRestrict _ (fun x => hle x x.2)
    exact h1.ringHom_of_comp_eq (f : _ →+* _) (φ : C →+* K)
      (fun x y hxy => Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val hxy)))
      (RingHom.ext fun x => rfl)
  have hA := key i s (Set.subset_union_left) hs
  have hB := key j t (Set.subset_union_right) ht
  have hle : IntermediateField.adjoin k (Set.range i ∪ Set.range j) ≤
      (algebraicClosure F K).restrictScalars k := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact mem_algebraicClosure_iff.mpr (hA a)
    · exact mem_algebraicClosure_iff.mpr (hB b)
  haveI : Algebra.IsAlgebraic F K := by
    refine ⟨fun c => ?_⟩
    have h2 : IsAlgebraic (algebraicClosure F K) c :=
      IsAlgebraic.tower_top_of_subalgebra_le (R := k)
        (A := (IntermediateField.adjoin k (Set.range i ∪ Set.range j)).toSubalgebra)
        (B := ((algebraicClosure F K).restrictScalars k).toSubalgebra) hle (halg c)
    exact h2.restrictScalars F
  haveI : Algebra.IsAlgebraic (Algebra.adjoin k T) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp inferInstance
  calc Algebra.trdeg k K ≤ #T := Algebra.IsAlgebraic.trdeg_le_cardinalMk k T
    _ ≤ #(i '' s) + #(j '' t) := Cardinal.mk_union_le _ _
    _ ≤ #s + #t := add_le_add Cardinal.mk_image_le Cardinal.mk_image_le
    _ = _ := by rw [hs.cardinalMk_eq_trdeg, ht.cardinalMk_eq_trdeg]

end Trdeg

/-! ### Residue fields of a fibre product -/

/-- The images of `κ(x)` and `κ(y)` generate the image of `κ(x) ⊗_{κ(s)} κ(y)` in the residue
field of a point `t` of `X ×_S Y`: the subring they generate pulls back to a subring of the
pushout through which both coprojections factor, hence to everything. -/
private theorem ofPointTensor_mem_closure {X Y S : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S}
    (t : ↥(pullback f g)) (r : (Scheme.Pullback.Triplet.ofPoint t).tensor) :
    Scheme.Pullback.ofPointTensor t r ∈ Subring.closure
      (Set.range ((pullback.fst f g).residueFieldMap t) ∪
        Set.range ((pullback.snd f g).residueFieldMap t)) := by
  let T := Scheme.Pullback.Triplet.ofPoint t
  set R := Subring.closure (Set.range ((pullback.fst f g).residueFieldMap t) ∪
    Set.range ((pullback.snd f g).residueFieldMap t))
  set S' := R.comap (Scheme.Pullback.ofPointTensor t).hom
  have hinl : T.tensorInl ≫ Scheme.Pullback.ofPointTensor t =
      (pullback.fst f g).residueFieldMap t :=
    pushout.inl_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint t)
  have hinr : T.tensorInr ≫ Scheme.Pullback.ofPointTensor t =
      (pullback.snd f g).residueFieldMap t :=
    pushout.inr_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint t)
  have h1 : ∀ a, T.tensorInl a ∈ S' := fun a =>
    Subring.subset_closure (Or.inl ⟨a, by rw [← hinl]; rfl⟩)
  have h2 : ∀ b, T.tensorInr b ∈ S' := fun b =>
    Subring.subset_closure (Or.inr ⟨b, by rw [← hinr]; rfl⟩)
  let ιS : CommRingCat.of S' ⟶ T.tensor := CommRingCat.ofHom S'.subtype
  let a' : _ ⟶ CommRingCat.of S' := CommRingCat.ofHom (T.tensorInl.hom.codRestrict S' h1)
  let b' : _ ⟶ CommRingCat.of S' := CommRingCat.ofHom (T.tensorInr.hom.codRestrict S' h2)
  have hw : ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) ≫ a' =
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) ≫ b' := by
    ext z
    exact congrArg (fun φ => (ConcreteCategory.hom φ) z)
      (pushout.condition (f := (S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
        (g := (S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  let σ : T.tensor ⟶ CommRingCat.of S' := pushout.desc a' b' hw
  have hid : σ ≫ ιS = 𝟙 T.tensor := by
    apply pushout.hom_ext
    · change pushout.inl _ _ ≫ pushout.desc a' b' hw ≫ ιS = pushout.inl _ _ ≫ 𝟙 T.tensor
      rw [pushout.inl_desc_assoc]
      ext w
      rfl
    · change pushout.inr _ _ ≫ pushout.desc a' b' hw ≫ ιS = pushout.inr _ _ ≫ 𝟙 T.tensor
      rw [pushout.inr_desc_assoc]
      ext w
      rfl
  have hr : ιS (σ r) = r := by
    simpa using congrArg (fun φ => (ConcreteCategory.hom φ) r) hid
  exact hr ▸ (σ r).2

/-- The residue field at the point of `X ×_S Y` given by a prime `p` of `κ(x) ⊗_{κ(s)} κ(y)` is a
field of fractions of the image of the tensor product: it is the residue field at `p`
([Stacks, Tag 01JT]). -/
private theorem exists_mul_eq_ofPointTensor_specTensorTo {X Y S : Scheme.{0}} {f : X ⟶ S}
    {g : Y ⟶ S} (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor)
    (c : (pullback f g).residueField (T.SpecTensorTo p)) :
    ∃ r₁ r₂, Scheme.Pullback.ofPointTensor (T.SpecTensorTo p) r₂ ≠ 0 ∧
      c * Scheme.Pullback.ofPointTensor (T.SpecTensorTo p) r₂ =
        Scheme.Pullback.ofPointTensor (T.SpecTensorTo p) r₁ := by
  let ψ := Scheme.Pullback.ofPointTensor (T.SpecTensorTo p)
  let tc := Scheme.Pullback.Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm
  let ρ₀ := T.SpecTensorTo.residueFieldMap p
  let e := Scheme.Spec.residueFieldIso T.tensor p
  have hρ : IsIso (ρ₀ ≫ e.hom) :=
    Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have hspec := T.Spec_ofPointTensor_SpecTensorTo p
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hspec
  have hρinj : Function.Injective (ρ₀ ≫ e.hom) :=
    (ConcreteCategory.bijective_of_isIso (ρ₀ ≫ e.hom)).1
  have halg : ∀ r, (ρ₀ ≫ e.hom) (ψ (tc.hom r)) =
      algebraMap T.tensor p.asIdeal.ResidueField r := by
    intro r
    have h1 := ConcreteCategory.congr_hom hspec r
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CategoryTheory.comp_apply] at h1
    change e.hom (ρ₀ (ψ (tc.hom r))) = _
    rw [h1]
    exact e.inv_hom_id_apply _
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective
    (nonZeroDivisors (T.tensor ⧸ p.asIdeal)) ((ρ₀ ≫ e.hom) c)
  obtain ⟨r₁, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r₂, hr₂⟩ := Ideal.Quotient.mk_surjective (s : T.tensor ⧸ p.asIdeal)
  have hs : algebraMap (T.tensor ⧸ p.asIdeal) p.asIdeal.ResidueField s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hspec' : (ρ₀ ≫ e.hom) c * algebraMap (T.tensor ⧸ p.asIdeal) p.asIdeal.ResidueField s =
      algebraMap (T.tensor ⧸ p.asIdeal) p.asIdeal.ResidueField
        (Ideal.Quotient.mk p.asIdeal r₁) := by
    rw [← hxs]
    exact IsLocalization.mk'_spec p.asIdeal.ResidueField (Ideal.Quotient.mk p.asIdeal r₁) s
  have e₁ : algebraMap T.tensor p.asIdeal.ResidueField r₁ =
      algebraMap (T.tensor ⧸ p.asIdeal) p.asIdeal.ResidueField (Ideal.Quotient.mk p.asIdeal r₁) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have e₂ : algebraMap T.tensor p.asIdeal.ResidueField r₂ =
      algebraMap (T.tensor ⧸ p.asIdeal) p.asIdeal.ResidueField s := by
    rw [IsScalarTower.algebraMap_apply T.tensor (T.tensor ⧸ p.asIdeal), ← hr₂]; rfl
  refine ⟨tc.hom r₁, tc.hom r₂, fun h0 => hs ?_, hρinj ?_⟩
  · rw [← e₂, ← halg, h0, map_zero]
  · rw [map_mul, halg, halg, e₁, e₂, hspec']

/-- The residue field of a point `t` of `X ×_S Y` is a field of fractions of the image of
`κ(x) ⊗_{κ(s)} κ(y)`. -/
private theorem exists_mul_eq_ofPointTensor {X Y S : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ S}
    (t : ↥(pullback f g)) (c : (pullback f g).residueField t) :
    ∃ r₁ r₂, Scheme.Pullback.ofPointTensor t r₂ ≠ 0 ∧
      c * Scheme.Pullback.ofPointTensor t r₂ = Scheme.Pullback.ofPointTensor t r₁ := by
  have key := exists_mul_eq_ofPointTensor_specTensorTo (Scheme.Pullback.Triplet.ofPoint t)
    (Scheme.Pullback.SpecOfPoint t)
  rw [Scheme.Pullback.SpecTensorTo_SpecOfPoint] at key
  exact key c

/-! ### Transcendence degrees of residue fields over `ℂ` -/

/-- The `ℂ`-algebra structure on a residue field induced by a structure morphism, as in
`AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg`. -/
private abbrev residueAlgebra {X : Scheme.{0}} (s : X ⟶ Spec (.of ℂ)) (x : X) :
    Algebra ℂ (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ s.appTop ≫ X.Γevaluation x).hom.toAlgebra

/-- The residue field map of a morphism over `ℂ` is a map of `ℂ`-algebras. -/
private def residueFieldAlgHom {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (φ : X ⟶ Y) (hφ : φ ≫ sY = sX) (x : X) :
    @AlgHom ℂ (Y.residueField (φ x)) (X.residueField x) _ _ _ (residueAlgebra sY (φ x))
      (residueAlgebra sX x) :=
  letI := residueAlgebra sY (φ x)
  letI := residueAlgebra sX x
  { (φ.residueFieldMap x).hom with
    commutes' := fun c => by
      subst hφ
      change (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sY.appTop ≫ Y.Γevaluation (φ x)) ≫
        φ.residueFieldMap x) c =
        ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (φ ≫ sY).appTop ≫ X.Γevaluation x) c
      rw [Category.assoc, Category.assoc, Scheme.Γevaluation_naturality, Scheme.Hom.comp_appTop,
        Category.assoc] }

/-- **Transcendence degrees across a quasi-finite map to a fibre product.** Let `L : W ⟶ X₁ ×_S X₂`
be locally quasi-finite and locally of finite type, over `ℂ`. At `w : W` the residue field `κ(w)`
is finite over `κ(L w)`, which is a field of fractions of the image of `κ(x₁) ⊗ κ(x₂)`; so
`trdeg_ℂ κ(w) ≤ trdeg_ℂ κ(x₁) + trdeg_ℂ κ(x₂)` for the images `x_i` of `w`. -/
private theorem trdeg_residueField_le_add {X₁ X₂ S W : Scheme.{0}} {sS : S ⟶ Spec (.of ℂ)}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) (L : W ⟶ pullback f₁ f₂) [LocallyOfFiniteType L]
    [LocallyQuasiFinite L] (w : W) :
    @Algebra.trdeg ℂ (W.residueField w) _ _
        (residueAlgebra (L ≫ pullback.fst f₁ f₂ ≫ f₁ ≫ sS) w) ≤
      @Algebra.trdeg ℂ (X₁.residueField ((L ≫ pullback.fst f₁ f₂) w)) _ _
          (residueAlgebra (f₁ ≫ sS) _) +
        @Algebra.trdeg ℂ (X₂.residueField ((L ≫ pullback.snd f₁ f₂) w)) _ _
          (residueAlgebra (f₂ ≫ sS) _) := by
  letI := residueAlgebra (L ≫ pullback.fst f₁ f₂ ≫ f₁ ≫ sS) w
  letI := residueAlgebra (f₁ ≫ sS) ((L ≫ pullback.fst f₁ f₂) w)
  letI := residueAlgebra (f₂ ≫ sS) ((L ≫ pullback.snd f₁ f₂) w)
  set i := residueFieldAlgHom (sX := L ≫ pullback.fst f₁ f₂ ≫ f₁ ≫ sS) (sY := f₁ ≫ sS)
    (L ≫ pullback.fst f₁ f₂) (by simp only [Category.assoc]) w
  set j := residueFieldAlgHom (sX := L ≫ pullback.fst f₁ f₂ ≫ f₁ ≫ sS) (sY := f₂ ≫ sS)
    (L ≫ pullback.snd f₁ f₂) (by simp only [Category.assoc, pullback.condition_assoc]) w
  refine trdeg_le_add_of_isAlgebraic i j fun c => ?_
  set F' := IntermediateField.adjoin ℂ (Set.range i ∪ Set.range j)
  set θ := (L.residueFieldMap w).hom
  -- the image of `κ(L w)` lies in `F'`
  have hθ : ∀ e, θ e ∈ F' := by
    have hcl : ∀ e ∈ Subring.closure (Set.range ((pullback.fst f₁ f₂).residueFieldMap (L w)) ∪
        Set.range ((pullback.snd f₁ f₂).residueFieldMap (L w))), θ e ∈ F' := by
      intro e he
      have hle : Subring.closure (Set.range ((pullback.fst f₁ f₂).residueFieldMap (L w)) ∪
          Set.range ((pullback.snd f₁ f₂).residueFieldMap (L w))) ≤
          F'.toSubalgebra.toSubring.comap θ := by
        rw [Subring.closure_le]
        rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
        · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨a,
            ConcreteCategory.congr_hom (Scheme.residueFieldMap_comp L _ w) a⟩)
        · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨b,
            ConcreteCategory.congr_hom (Scheme.residueFieldMap_comp L _ w) b⟩)
      exact hle he
    intro e
    obtain ⟨r₁, r₂, hr₂, hmul⟩ := exists_mul_eq_ofPointTensor (L w) e
    have h1 := hcl _ (ofPointTensor_mem_closure (L w) r₁)
    have h2 := hcl _ (ofPointTensor_mem_closure (L w) r₂)
    have hne : θ (Scheme.Pullback.ofPointTensor (L w) r₂) ≠ 0 :=
      fun h0 => hr₂ (θ.injective (h0.trans (map_zero θ).symm))
    have : θ e = θ (Scheme.Pullback.ofPointTensor (L w) r₁) /
        θ (Scheme.Pullback.ofPointTensor (L w) r₂) := by
      rw [eq_div_iff hne, ← map_mul, hmul]
    rw [this]
    exact F'.div_mem h1 h2
  letI : Algebra ((pullback f₁ f₂).residueField (L w)) (W.residueField w) := θ.toAlgebra
  haveI : Module.Finite ((pullback f₁ f₂).residueField (L w)) (W.residueField w) :=
    finite_residueField_of_locallyQuasiFinite' L w
  have hc : IsAlgebraic ((pullback f₁ f₂).residueField (L w)) c :=
    (Algebra.IsAlgebraic.of_finite _ _).isAlgebraic c
  let θ' : (pullback f₁ f₂).residueField (L w) →+* F' := θ.codRestrict F'.toSubalgebra.toSubring hθ
  exact hc.ringHom_of_comp_eq θ' (RingHom.id (W.residueField w))
    (fun a b hab => θ.injective (congrArg Subtype.val hab)) (RingHom.ext fun _ => rfl)

/-! ### The dimension count -/

/-- **The dimension count.** If the generic point `ξ` of a prime divisor of the fourfold `G` lies
over `Σ`, then `3 = dim cl{ξ} ≤ dim cl{u ξ} + dim cl{v ξ} ≤ dim W⁻ + dim W⁺`. -/
private theorem three_le_of_primeDivisor (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (D : GraphData h) (E : MMP.Mori.PrimeDivisor D.G)
    (hE : (D.u ≫ fm) E.genericPoint ∈ (badLocusBase fm fp : Set Z)) :
    3 ≤ topologicalKrullDim (badLocusMinus fm fp : Set Xm) +
      topologicalKrullDim (badLocusPlus fm fp : Set Xp) := by
  have hG := D.isNormalizedGraph
  haveI := hG.isFinite
  have hXm := h.isNormalVariety_minus.1
  have hXp := h.isNormalVariety_plus.1
  haveI : LocallyOfFiniteType sXm := hXm.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sXp := hXp.toLocallyOfFiniteType
  set x := E.genericPoint
  set L := pullback.lift D.u D.v hG.comp_eq
  have hLu : L ≫ pullback.fst fm fp = D.u := pullback.lift_fst _ _ _
  have hLv : L ≫ pullback.snd fm fp = D.v := pullback.lift_snd _ _ _
  have hT := trdeg_residueField_le_add (sS := sZ) fm fp L x
  rw [h.comp_eq_minus, h.comp_eq_plus, ← Category.assoc L, hLu, hLv] at hT
  -- dimensions of the closures of the three points
  have dG := topologicalKrullDim_closure_singleton_eq_trdeg ℂ D.G (D.u ≫ sXm) x
  have dm := topologicalKrullDim_closure_singleton_eq_trdeg ℂ Xm sXm (D.u x)
  have dp := topologicalKrullDim_closure_singleton_eq_trdeg ℂ Xp sXp (D.v x)
  have hle : topologicalKrullDim (closure ({x} : Set D.G)) ≤
      topologicalKrullDim (closure ({D.u x} : Set Xm)) +
        topologicalKrullDim (closure ({D.v x} : Set Xp)) := by
    rw [dG, dm, dp, ← WithBot.coe_add, WithBot.coe_le_coe, ← map_add]
    exact OrderHomClass.mono _ hT
  -- `dim cl{ξ} = 3`
  have h3 : 3 ≤ topologicalKrullDim (closure ({x} : Set D.G)) := by
    haveI := isVariety_graph h D
    haveI := hXm
    have hdimG : topologicalKrullDim D.G = 4 := by
      rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sXm (D.u ≫ sXm)
        hG.isBirationalMorphism_minus, h.dim_minus]
    have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (D.u ≫ sXm) x
    rw [hdimG, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, dG] at hsum
    rw [dG]
    exact (ENat.WithBot.add_one_cancel.mp (hsum.trans (by norm_num))).ge
  -- the closures lie in the bad loci
  have hsub : ∀ {Y : Scheme.{0}} (W : Closeds Y) (y : Y), y ∈ (W : Set Y) →
      topologicalKrullDim (closure ({y} : Set Y)) ≤ topologicalKrullDim (W : Set Y) :=
    fun W y hy => (Topology.IsEmbedding.inclusion ((W.isClosed.closure_subset_iff).mpr
      (Set.singleton_subset_iff.mpr hy))).isInducing.topologicalKrullDim_le
  have hum : D.u x ∈ (badLocusMinus fm fp : Set Xm) := by
    rwa [coe_badLocusMinus]
  have hvp : D.v x ∈ (badLocusPlus fm fp : Set Xp) := by
    rwa [coe_badLocusPlus, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hG.comp_eq]
  exact h3.trans (hle.trans (add_le_add (hsub _ _ hum) (hsub _ _ hvp)))

/-- **Graph dimension bound.** In a step diagram of fourfolds `(X⁻, B⁻) → Z ← (X⁺, B⁺)` whose
bad locus `Σ = badLocusBase fm fp` is nonempty, the bad loci `W⁻ = badLocusMinus fm fp` and
`W⁺ = badLocusPlus fm fp` satisfy `dim W⁻ + dim W⁺ ≥ 3`. -/
@[mmp "lem_oai4_graph_c"]
public theorem IsFourfoldStepDiagram.three_le_topologicalKrullDim_badLocusMinus_add
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp)
    (hbad : (badLocusBase fm fp : Set Z).Nonempty) :
    3 ≤ topologicalKrullDim (badLocusMinus fm fp : Set Xm) +
      topologicalKrullDim (badLocusPlus fm fp : Set Xp) := by
  obtain ⟨D⟩ := exists_graphData h
  obtain ⟨H, hH⟩ := exists_isGraphDivisor h D
  obtain ⟨E, hE⟩ : ∃ E : MMP.Mori.PrimeDivisor D.G,
      (D.u ≫ fm) E.genericPoint ∈ (badLocusBase fm fp : Set Z) := by
    by_contra hne
    simp only [not_exists] at hne
    have hH0 : H = 0 := Finsupp.ext fun E =>
      coeff_eq_zero_of_mem_commonBiregularLocus h D hH E (by
        have := hne E
        rw [coe_badLocusBase, Set.mem_compl_iff, not_not] at this
        exact this)
    subst hH0
    rw [badLocusBase_eq_empty_of_isGraphDivisor_zero h D hH] at hbad
    exact Set.not_nonempty_empty hbad
  exact three_le_of_primeDivisor h D E hE

/-! ### Bad loci of small morphisms -/

/-- Let `f : X ⟶ Z` be small and `g : Y ⟶ Z` a proper birational morphism from a variety onto the
same normal variety. A point `x` of `X` of codimension at most one maps into the biregular loci
of both: off `Ex(f)` by smallness, and then `f x` has codimension at most one in `Z`, where `g` is
an isomorphism. -/
private theorem mem_biregularLocus_of_coheight_le_one {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {g : Y ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (hY : AlgebraicGeometry.IsVariety ℂ sY) (hg : g ≫ sZ = sY) [IsProper g]
    (hgb : IsBirationalMorphism g) {x : X} (hx : Order.coheight x ≤ 1) :
    f x ∈ biregularLocus f ∧ f x ∈ biregularLocus g := by
  have hxf : f x ∈ biregularLocus f := by
    by_contra hn
    exact absurd ((MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hf.two_le_codimension
      (mem_exceptionalSet.mpr hn)).trans hx) (by decide)
  refine ⟨hxf, mem_biregularLocus_of_ringKrullDim_stalk_le_one hf.isNormalVariety_target g
    (hg ▸ hY) hgb ?_⟩
  rw [ringKrullDim_stalk_eq_coheight, MMP.Positivity.coheight_map_of_mem_biregularLocus f hxf]
  exact_mod_cast hx

/-- If every irreducible closed subset of a closed set `T` has codimension at least `c` in a space
of dimension at most `a + c`, then `T` has dimension at most `a`. -/
private theorem topologicalKrullDim_le_of_le_coheight {X : Type*} [TopologicalSpace X]
    {T : Set X} (hT : IsClosed T) {a c : ℕ} (hX : topologicalKrullDim X ≤ (a + c : ℕ))
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ T → c ≤ Order.coheight W) :
    topologicalKrullDim T ≤ a := by
  let m := IrreducibleCloseds.map (Subtype.val : T → X) continuous_subtype_val
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun W => WithBot.coe_le_coe.mpr ?_
  have hW : Order.height (m W) + Order.coheight (m W) ≤ (a + c : ℕ) := by
    have : Nonempty (IrreducibleCloseds X) := ⟨m W⟩
    rw [topologicalKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty] at hX
    exact (le_iSup (fun V => Order.height V + Order.coheight V) (m W)).trans
      (WithBot.coe_le_coe.mp hX)
  refine (Order.height_le_height_apply_of_strictMono m
    (IrreducibleCloseds.map_strictMono_of_isInducing .subtypeVal) W).trans
    ((ENat.add_le_add_iff_right (ENat.coe_ne_top c)).mp ?_)
  refine (add_le_add le_rfl (hc (m W) ?_)).trans (by exact_mod_cast hW)
  rw [IrreducibleCloseds.coe_map]
  exact closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) hT

/-- A closed subset of a fourfold containing no point of codimension at most one has dimension
at most two. -/
private theorem topologicalKrullDim_le_two_of_forall_coheight_le_one {X : Scheme.{0}}
    (hX : topologicalKrullDim X = 4) (T : Closeds X)
    (hT : ∀ x : X, Order.coheight x ≤ 1 → x ∉ (T : Set X)) :
    topologicalKrullDim (T : Set X) ≤ 2 := by
  refine topologicalKrullDim_le_of_le_coheight (c := 2) T.isClosed hX.le fun W hW => ?_
  by_contra! hlt
  have hle : Order.coheight W ≤ 1 := Order.le_of_lt_add_one hlt
  rw [← codimension_eq_coheight, MMP.Flips.codimension_eq_coheight_genericPoint] at hle
  exact hT _ hle (hW (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem)

/-! ### The positive bad locus -/

/-- **The positive bad locus has dimension at most two.** In a step diagram of fourfolds
`(X⁻, B⁻) → Z ← (X⁺, B⁺)`, the positive bad locus `W⁺ = badLocusPlus fm fp` satisfies
`dim W⁺ ≤ 2`. -/
@[mmp "lem_oai4_graph_d"]
public theorem IsFourfoldStepDiagram.topologicalKrullDim_badLocusPlus_le_two
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) :
    topologicalKrullDim (badLocusPlus fm fp : Set Xp) ≤ 2 := by
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  exact topologicalKrullDim_le_two_of_forall_coheight_le_one h.dim_plus _ fun _ hx hW =>
    hW (mem_biregularLocus_of_coheight_le_one h.isSmallMorphism_plus h.isNormalVariety_minus.1
      h.comp_eq_minus h.isBirationalMorphism_minus hx).symm

/-! ### The negative bad locus of a small step -/

/-- **The negative bad locus of a small step has dimension at most two.** In a step diagram of
fourfolds `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with `f⁻` small, the negative bad locus
`W⁻ = badLocusMinus fm fp` satisfies `dim W⁻ ≤ 2`. -/
@[mmp "lem_oai4_graph_e"]
public theorem IsFourfoldStepDiagram.topologicalKrullDim_badLocusMinus_le_two
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm) :
    topologicalKrullDim (badLocusMinus fm fp : Set Xm) ≤ 2 := by
  haveI : IsProper fp := h.isProper_plus
  exact topologicalKrullDim_le_two_of_forall_coheight_le_one h.dim_minus _ fun _ hx hW =>
    hW (mem_biregularLocus_of_coheight_le_one hm h.isNormalVariety_plus.1 h.comp_eq_plus
      h.isBirationalMorphism_plus hx)

/-! ### The base bad locus of a small step -/

section SpecializationChains

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

section SpecializationOrder

attribute [local instance] specializationOrder

/-- A quasi-sober `T₀` space of dimension at least two contains a chain of two strict
specializations. -/
private theorem exists_specializes_chain_of_two_le
    (h : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ a b c : X, a ⤳ b ∧ ¬ b ⤳ a ∧ b ⤳ c ∧ ¬ c ⤳ b := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at h
  have h' : ((2 : ℕ) : WithBot ℕ∞) ≤ _ := h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h'
  have h0 := l.step ⟨0, by omega⟩
  have h1 := l.step ⟨1, by omega⟩
  exact ⟨_, _, _, h1.1, h1.2, h0.1, h0.2⟩

/-- A quasi-sober `T₀` space containing a chain of three strict specializations has dimension at
least three. -/
private theorem three_le_of_specializes_chain {a b c d : X}
    (hab : a ⤳ b) (hba : ¬ b ⤳ a) (hbc : b ⤳ c) (hcb : ¬ c ⤳ b) (hcd : c ⤳ d)
    (hdc : ¬ d ⤳ c) : (3 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  let l : LTSeries X := ⟨3, ![d, c, b, a], fun i => by
    fin_cases i
    · exact ⟨hcd, hdc⟩
    · exact ⟨hbc, hcb⟩
    · exact ⟨hab, hba⟩⟩
  exact Order.le_krullDim_iff.mpr ⟨l, rfl⟩

end SpecializationOrder

/-- A closed subset of dimension at least two of a quasi-sober `T₀` space contains a chain of two
strict specializations. -/
public theorem exists_specializes_chain_of_two_le_of_isClosed {T : Set X}
    (hT : IsClosed T) (h : (2 : WithBot ℕ∞) ≤ topologicalKrullDim T) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a ⤳ b ∧ ¬ b ⤳ a ∧ b ⤳ c ∧ ¬ c ⤳ b := by
  have : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨a, b, c, h1, h2, h3, h4⟩ := exists_specializes_chain_of_two_le h
  simp only [subtype_specializes_iff] at h1 h2 h3 h4
  exact ⟨a, a.2, b, b.2, c, c.2, h1, h2, h3, h4⟩

/-- A closed subset of a quasi-sober `T₀` space containing a chain of three strict
specializations has dimension at least three. -/
private theorem three_le_of_specializes_chain_of_isClosed {T : Set X} (hT : IsClosed T)
    {a b c d : X} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (hab : a ⤳ b) (hba : ¬ b ⤳ a) (hbc : b ⤳ c) (hcb : ¬ c ⤳ b) (hcd : c ⤳ d)
    (hdc : ¬ d ⤳ c) : (3 : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  have : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  refine three_le_of_specializes_chain (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩)
    (d := ⟨d, hd⟩) ?_ ?_ ?_ ?_ ?_ ?_ <;> simpa only [subtype_specializes_iff]

/-- A fibre of positive dimension of a continuous map from a quasi-sober space to a `T₀` space
contains a strict specialization. -/
private theorem exists_specializes_of_pos_topologicalKrullDim_preimage {Y : Type*}
    [TopologicalSpace Y] [T0Space Y] {f : X → Y} (hf : Continuous f) {z : Y}
    (h : 0 < topologicalKrullDim (f ⁻¹' {z})) :
    ∃ x x' : X, x ⤳ x' ∧ ¬ x' ⤳ x ∧ f x = z ∧ f x' = z := by
  rw [topologicalKrullDim, Order.krullDim_pos_iff] at h
  obtain ⟨A, B, hAB⟩ := h
  let m := IrreducibleCloseds.map (Subtype.val : f ⁻¹' {z} → X) continuous_subtype_val
  have hm : m A < m B := IrreducibleCloseds.map_strictMono_of_isInducing .subtypeVal hAB
  have hgen (C : IrreducibleCloseds (f ⁻¹' {z})) :
      IsGenericPoint (m C).isIrreducible.genericPoint (m C) :=
    (m C).isIrreducible.isGenericPoint_genericPoint (m C).isClosed
  have himage (C : IrreducibleCloseds (f ⁻¹' {z})) : f (m C).isIrreducible.genericPoint = z := by
    obtain ⟨c, hc⟩ := C.isIrreducible.nonempty
    have h1 : (m C).isIrreducible.genericPoint ⤳ c :=
      (hgen C).specializes (by rw [IrreducibleCloseds.coe_map]; exact subset_closure ⟨c, hc, rfl⟩)
    have h2 : f (m C).isIrreducible.genericPoint ∈ closure {z} := by
      refine closure_mono ?_ (image_closure_subset_closure_image
        (s := Subtype.val '' (C : Set (f ⁻¹' {z}))) hf ⟨_, ?_, rfl⟩)
      · rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
        exact c.2
      · rw [← IrreducibleCloseds.coe_map]
        exact (hgen C).mem
    have h3 : f (m C).isIrreducible.genericPoint ⤳ z :=
      (show f c = z from c.2) ▸ h1.map hf
    exact (h3.antisymm (specializes_iff_mem_closure.mpr h2)).eq
  refine ⟨_, _, (hgen B).specializes (hm.le (hgen A).mem), fun hBA => hm.not_ge ?_,
    himage B, himage A⟩
  change (m B : Set X) ⊆ m A
  rw [← (hgen B).def]
  exact closure_minimal (Set.singleton_subset_iff.mpr ((hgen A).specializes_iff_mem.mp hBA))
    (m A).isClosed

/-- Let `f` be a continuous specializing map from a quasi-sober `T₀` space to a `T₀` space, and
`T` a closed subset of the source containing the preimage of `S`. If `S` contains a chain
`z₂ ⤳ z₁ ⤳ z₀` of strict specializations and the fibre over `z₂` has positive dimension, then
`T` has dimension at least three. -/
private theorem three_le_topologicalKrullDim_of_specializingMap {Y : Type*}
    [TopologicalSpace Y] [T0Space Y] {f : X → Y} (hf : Continuous f) (hsp : SpecializingMap f)
    {S : Set Y} {T : Set X} (hT : IsClosed T) (hTS : ∀ x, f x ∈ S → x ∈ T) {z₂ z₁ z₀ : Y}
    (h₂ : z₂ ∈ S) (h₁ : z₁ ∈ S) (h₀ : z₀ ∈ S) (h21 : z₂ ⤳ z₁) (h12 : ¬ z₁ ⤳ z₂)
    (h10 : z₁ ⤳ z₀) (h01 : ¬ z₀ ⤳ z₁) (hfib : 0 < topologicalKrullDim (f ⁻¹' {z₂})) :
    (3 : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  obtain ⟨x, x', hxx', hx'x, hx, hx'⟩ := exists_specializes_of_pos_topologicalKrullDim_preimage
    hf hfib
  subst hx
  obtain ⟨y₁, hy₁, rfl⟩ := hsp (show f x' ⤳ z₁ from hx' ▸ h21)
  obtain ⟨y₀, hy₀, rfl⟩ := hsp (show f y₁ ⤳ z₀ from h10)
  refine three_le_of_specializes_chain_of_isClosed hT (hTS _ h₂) (hTS _ (hx' ▸ h₂))
    (hTS _ h₁) (hTS _ h₀) hxx' hx'x hy₁ (fun h => h12 ?_) hy₀ (fun h => h01 (h.map hf))
  simpa [hx'] using h.map hf

end SpecializationChains

/-- Let `f : U ⟶ R` be a proper birational morphism of varieties with `R` normal, and `T` a closed
subset of `U` containing `f⁻¹(S)`. If `S` contains a chain `z₂ ⤳ z₁ ⤳ z₀` of strict
specializations and `z₂` lies outside the biregular locus of `f`, then `dim T ≥ 3`. -/
public theorem three_le_topologicalKrullDim_of_notMem_biregularLocus {U R : Scheme.{0}}
    {sU : U ⟶ Spec (.of ℂ)} {sR : R ⟶ Spec (.of ℂ)} (hU : AlgebraicGeometry.IsVariety ℂ sU)
    (hR : AlgebraicGeometry.IsVariety ℂ sR) [IsNormal R] (f : U ⟶ R) (hf : f ≫ sR = sU)
    [IsProper f] (hb : IsBirationalMorphism f) {S : Set R} {T : Set U} (hT : IsClosed T)
    (hTS : ∀ x, f x ∈ S → x ∈ T) {z₂ z₁ z₀ : R} (h₂ : z₂ ∈ S) (h₁ : z₁ ∈ S) (h₀ : z₀ ∈ S)
    (h21 : z₂ ⤳ z₁) (h12 : ¬ z₁ ⤳ z₂) (h10 : z₁ ⤳ z₀) (h01 : ¬ z₀ ⤳ z₁)
    (hz : z₂ ∉ biregularLocus f) : (3 : WithBot ℕ∞) ≤ topologicalKrullDim T :=
  three_le_topologicalKrullDim_of_specializingMap f.continuous f.isClosedMap.specializingMap hT
    hTS h₂ h₁ h₀ h21 h12 h10 h01 <| lt_of_not_ge fun hle =>
      hz (mem_biregularLocus_of_topologicalKrullDim_le hU hR f hf hb hle)

/-- **The base bad locus of two small morphisms has dimension at most one.** If
`f⁻ : X⁻ ⟶ Z` and `f⁺ : X⁺ ⟶ Z` are small morphisms of complex varieties from fourfolds, then
`Σ = badLocusBase fm fp` satisfies `dim Σ ≤ 1`. -/
public theorem topologicalKrullDim_badLocusBase_le_one_of_isSmallMorphism
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hdm : topologicalKrullDim Xm = 4)
    (hdp : topologicalKrullDim Xp = 4) (hm : IsSmallMorphism sXm sZ fm)
    (hp : IsSmallMorphism sXp sZ fp) :
    topologicalKrullDim (badLocusBase fm fp : Set Z) ≤ 1 := by
  by_contra hlt
  obtain ⟨z₂, h₂, z₁, h₁, z₀, h₀, h21, h12, h10, h01⟩ :=
    exists_specializes_chain_of_two_le_of_isClosed (badLocusBase fm fp).isClosed
      (by exact_mod_cast ENat.WithBot.add_one_le_iff.mpr (lt_of_not_ge hlt))
  have hZ := hm.isNormalVariety_target
  have := hZ.2
  have := hm.isProper
  have := hp.isProper
  by_cases hzm : z₂ ∈ biregularLocus fm
  · have h3 := three_le_topologicalKrullDim_of_notMem_biregularLocus hp.isNormalVariety_source.1
      hZ.1 fp hp.comp_eq hp.isBirationalMorphism (badLocusPlus fm fp).isClosed
      (fun _ hx => hx) h₂ h₁ h₀ h21 h12 h10 h01 fun hzp => h₂ ⟨hzm, hzp⟩
    have h2 := topologicalKrullDim_le_two_of_forall_coheight_le_one hdp (badLocusPlus fm fp)
      fun _ hx hW =>
        hW (mem_biregularLocus_of_coheight_le_one hp hm.isNormalVariety_source.1 hm.comp_eq
          hm.isBirationalMorphism hx).symm
    exact absurd (h3.trans h2) (by decide)
  · have h3 := three_le_topologicalKrullDim_of_notMem_biregularLocus hm.isNormalVariety_source.1
      hZ.1 fm hm.comp_eq hm.isBirationalMorphism (badLocusMinus fm fp).isClosed
      (fun _ hx => hx) h₂ h₁ h₀ h21 h12 h10 h01 hzm
    have h2 := topologicalKrullDim_le_two_of_forall_coheight_le_one hdm (badLocusMinus fm fp)
      fun _ hx hW =>
        hW (mem_biregularLocus_of_coheight_le_one hm hp.isNormalVariety_source.1 hp.comp_eq
          hp.isBirationalMorphism hx)
    exact absurd (h3.trans h2) (by decide)

/-- **The base bad locus of a small step has dimension at most one.** In a step diagram of
fourfolds `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with `f⁻` small, the base bad locus
`Σ = badLocusBase fm fp` satisfies `dim Σ ≤ 1`. -/
@[mmp "lem_oai4_graph_f"]
public theorem IsFourfoldStepDiagram.topologicalKrullDim_badLocusBase_le_one
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (hm : IsSmallMorphism sXm sZ fm) :
    topologicalKrullDim (badLocusBase fm fp : Set Z) ≤ 1 :=
  topologicalKrullDim_badLocusBase_le_one_of_isSmallMorphism h.dim_minus h.dim_plus hm
    h.isSmallMorphism_plus

/-! ### Lost divisors -/

/-- **Lost divisors improve strictly.** In a step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` of
fourfolds, let `E` be a prime divisor of `X⁻` and `ξ⁺` the valuation of `k(X⁺)` corresponding to
`ord_E` (the one with the same restriction to `k(Z)`). If `ξ⁺` is exceptional over `X⁺`, then
`a(ord_E; X⁻, B⁻) < a(ord_E; X⁺, B⁺)`. -/
@[mmp "lem_oai4_singularities_preserved_d"]
public theorem IsFourfoldStepDiagram.lt_of_isExceptionalValuation_divisorialValuation
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsFourfoldStepDiagram sXm sZ sXp K B fm fp) (E : MMP.Mori.PrimeDivisor Xm)
    {ξp : Valuation Xp.functionField (WithZero (Multiplicative ℤ))}
    (hξ : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isBirationalMorphism_plus.isDominant
      ξp.comap (functionFieldMap fp) = E.divisorialValuation.comap (functionFieldMap fm))
    (hexc : MMP.Intersection.IsExceptionalValuation ℂ sXp ξp)
    {am ap : ℝ} (ham : IsValuationLogDiscrepancy sXm B E.divisorialValuation am)
    (hap : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) ξp ap) :
    am < ap := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  obtain ⟨_, Dp, hDp, hvp, -⟩ := id hap
  let D := DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus E
  have hD : D.valuation = E.divisorialValuation := by
    ext t
    exact congrArg E.divisorialValuation (functionFieldMap_id_apply t)
  refine ((IsFourfoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hξ ham hap
    (Cm := D.center) ⟨D, inferInstanceAs (IsProper (𝟙 Xm)), hD.symm, rfl⟩
    ⟨Dp, hDp, hvp.symm, rfl⟩).out 1 2).mpr ?_
  refine (badLocusMinus fm fp).isClosed.closure_subset_iff.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  exact IsFourfoldStepDiagram.support_subset_badLocusMinus h E ⟨ξp, hξ, hexc⟩ hx

end MMP.Fourfold
