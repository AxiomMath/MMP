module
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
public import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import StacksFrontier.AlgebraicGeometry.Fibres.ClosedFibreSections
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.LocalDimension

/-!
# Normal threefold slices of a resolution with derived unit

Let `f : Z ⟶ X` be a projective birational morphism of complex schemes with
`𝒪_X ≅ Rf_* 𝒪_Z`, where `X` is a normal complex fourfold, and suppose `f` is an
isomorphism off a smooth curve `T ⊆ X`. Let `t : X ⟶ B` be a morphism to a smooth complex
curve such that `T ⟶ B` is finite étale and `Z ⟶ B` is smooth, and such that
`E = (f⁻¹ T)_red = E₁ + ⋯ + E_r` is a simple normal crossing divisor all of whose strata are
smooth over `B`. Then for every closed point `b ∈ B` the fibre `X_b` is a normal scheme of pure
dimension three, `T_b = T ∩ X_b` is finite, and the induced morphism of fibres
`f_b : Z_b ⟶ X_b` is a projective resolution which is an isomorphism over `X_b ∖ T_b`. In
particular the singular points of `X_b` lie in the finite set `T_b`: they are isolated
threefold singularities.

The proof pushes forward `0 → 𝒪_Z → 𝒪_Z → 𝒪_{Z_b} → 0` (multiplication by a local
parameter at `b`): `f_* 𝒪_Z = 𝒪_X` and `R¹f_* 𝒪_Z = 0` give `𝒪_{X_b} ≅ (f_b)_* 𝒪_{Z_b}`,
from which normality of `X_b` follows since `Z_b` is smooth.

## Main results

* `MMP.Fourfold.isNormal_fiber_of_isZero_rightDerived_pushforward`.

## Implementation notes

* `𝒪_X ≅ Rf_* 𝒪_Z` is stated through the canonical map: every `f.app U : Γ(X, U) ⟶ Γ(Z, f⁻¹U)`
  is an isomorphism (`f_* 𝒪_Z = 𝒪_X`), and the higher direct images
  `Rⁱ f_* 𝒪_Z`, the right derived functors of `AlgebraicGeometry.Scheme.Modules.pushforward f`
  applied to `𝒪_Z`, vanish for `i > 0`.
* The curve `T` is a closed subscheme `ι : T ⟶ X`, smooth of relative dimension one over `ℂ`;
  the curve `B` is smooth of relative dimension one over `ℂ`. Neither is assumed connected.
* `E` is given by the finite set `s` of its prime divisors, with union `f⁻¹ T`; it is snc over
  `ℂ` (`MMP.Mori.DivisorWithCoeffs.IsSNC`). A stratum of `E` is a connected component of a
  scheme-theoretic intersection `⋂_{P ∈ J} P` (`J ⊆ s` nonempty), so "the strata are smooth over
  `B`" is smoothness over `B` of these intersections.
* The fibres are Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, `Z_b` being the fibre of
  `f ≫ t`, and `f_b` is `pullback.map` of `f`. A resolution is
  `MMP.Mori.IsSmoothResolution` over the residue field `κ(b)`, which does not ask `X_b` to be
  connected; pure dimension three is that every nonempty open of `X_b` has dimension three.
-/

section

open CategoryTheory AlgebraicGeometry Limits
open Opposite TopologicalSpace

namespace MMP.Fourfold.Internal.ConductorNormalSlice

/-- The map of fibres induced by `f` over `t`. -/
private noncomputable abbrev fiberMap {X Z B : Scheme.{0}} (f : Z ⟶ X) (t : X ⟶ B) (b : B) :
    pullback (f ≫ t) (B.fromSpecResidueField b) ⟶ pullback t (B.fromSpecResidueField b) :=
  pullback.map (f ≫ t) (B.fromSpecResidueField b) t (B.fromSpecResidueField b) f (𝟙 _) (𝟙 _)
    (by simp) (by simp)

/-- The fibre map of a projective morphism is projective: it is the base change of `f` along
`t.fiberι b`. -/
private lemma isProjectiveMorphism_fiberMap {X Z B : Scheme.{0}} (f : Z ⟶ X)
    (hfp : IsProjectiveMorphism f) (t : X ⟶ B) (b : B) :
    IsProjectiveMorphism (fiberMap f t b) := by
  unfold fiberMap
  refine IsProjectiveMorphism.of_iso (pullbackRightPullbackFstIso t (B.fromSpecResidueField b) f)
    (Iso.refl _) ?_ (hfp.baseChange (t.fiberι b))
  apply pullback.hom_ext
  · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.lift_fst]
    rw [pullbackRightPullbackFstIso_hom_fst_assoc]
    exact pullback.condition
  · simp only [Iso.refl_hom, Category.comp_id, Category.assoc, pullback.lift_snd]
    rw [pullbackRightPullbackFstIso_hom_snd]
    rfl

private lemma fiberMap_comp_fiberToSpecResidueField {X Z B : Scheme.{0}} (f : Z ⟶ X)
    (t : X ⟶ B) (b : B) :
    fiberMap f t b ≫ t.fiberToSpecResidueField b = (f ≫ t).fiberToSpecResidueField b := by
  unfold fiberMap Scheme.Hom.fiberToSpecResidueField
  erw [pullback.lift_snd, Category.comp_id]

/-- The fibre map is the base change of `f` along the inclusion of the fibre. -/
private lemma isPullback_fiberMap {X Z B : Scheme.{0}} (f : Z ⟶ X) (t : X ⟶ B) (b : B) :
    IsPullback (pullback.fst (f ≫ t) (B.fromSpecResidueField b)) (fiberMap f t b) f
      (pullback.fst t (B.fromSpecResidueField b)) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback t (B.fromSpecResidueField b))
  rw [pullback.lift_snd, Category.comp_id]
  exact IsPullback.of_hasPullback (f ≫ t) (B.fromSpecResidueField b)

/-- The trace on a fibre of `t` of a closed subscheme finite over the base is finite. -/
private lemma finite_fiberι_preimage_range {X T B : Scheme.{0}} (ι : T ⟶ X) (t : X ⟶ B)
    [IsFinite (ι ≫ t)] (b : B) : (t.fiberι b ⁻¹' Set.range ι).Finite := by
  haveI := instLocallyQuasiFiniteOfIsFinite (ι ≫ t)
  haveI := instQuasiCompactOfIsAffineHom (ι ≫ t)
  have h := (ι ≫ t).finite_preimage_singleton b
  have hinj : Function.Injective (t.fiberι b) := (t.fiberι b).isEmbedding.injective
  refine ((h.image ι).preimage hinj.injOn).subset ?_
  rintro x ⟨y, hy⟩
  refine ⟨y, ?_, hy⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply, hy]
  exact Scheme.Hom.apply_fiberι t b x

/-- Let `g : Y ⟶ W` be an isomorphism over the complement of a closed set `S ⊆ W`, and let
`p : W ⟶ K` be such that `g ≫ p` is smooth. Then the singular locus of `p` lies in `S`. -/
private lemma singularLocus_subset_of_isIso_morphismRestrict {Y W K : Scheme.{0}} (g : Y ⟶ W)
    (p : W ⟶ K) [Smooth (g ≫ p)] (S : Set W) (hS : IsClosed S)
    (hiso : ∀ V : W.Opens, (V : Set W) = Sᶜ → IsIso (g ∣_ V)) :
    (MMP.Mori.singularLocus p : Set W) ⊆ S := by
  intro x hx
  by_contra hxS
  let V : W.Opens := ⟨Sᶜ, hS.isOpen_compl⟩
  haveI := hiso V rfl
  refine hx (MMP.Mori.mem_smoothLocus_iff.mpr ⟨V, hxS, ?_⟩)
  have : V.ι ≫ p = inv (g ∣_ V) ≫ (g ⁻¹ᵁ V).ι ≫ g ≫ p := by
    rw [IsIso.eq_inv_comp, morphismRestrict_ι_assoc]
  rw [this]
  infer_instance

private lemma topologicalKrullDim_singleton {T : Type*} [TopologicalSpace T] (x : T) :
    topologicalKrullDim (↥({x} : Set T)) = 0 := by
  have : Subsingleton (↥({x} : Set T)) := Set.subsingleton_singleton.coe_sort
  haveI : DiscreteTopology (↥({x} : Set T)) := Subsingleton.discreteTopology
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) ?_
  have hne : topologicalKrullDim (↥({x} : Set T)) ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    exact ⟨⟨x, rfl⟩⟩
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd]; exact_mod_cast (zero_le : (0 : ℕ∞) ≤ d)

private lemma not_isOpen_singleton_of_smoothOfRelativeDimension_one {B : Scheme.{0}}
    (sB : B ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sB] (b : B) :
    ¬ IsOpen ({b} : Set B) := fun ho ↦ by
  have h : topologicalKrullDimAt B b ≤ 0 :=
    (iInf_le (fun U : {U : Set B // b ∈ U ∧ IsOpen U} ↦ topologicalKrullDim (↥U.val))
      ⟨{b}, rfl, ho⟩).trans_eq (topologicalKrullDim_singleton b)
  rw [show topologicalKrullDimAt B b = 1 from
    topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one sB b] at h
  exact absurd h (by decide)

/-- At a closed point of a smooth curve the maximal ideal of the local ring is principal and
nonzero. -/
private lemma exists_maximalIdeal_eq_span_and_ne_bot {B : Scheme.{0}} (sB : B ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 sB] (b : B) (hb : IsClosed ({b} : Set B)) :
    ∃ π : B.presheaf.stalk b, IsLocalRing.maximalIdeal (B.presheaf.stalk b) = Ideal.span {π} ∧
      IsLocalRing.maximalIdeal (B.presheaf.stalk b) ≠ ⊥ := by
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  have hreg := (isRegular_of_smooth_over_field sB).isRegularLocalRing_stalk b
  have h1 := topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one sB b
  rw [topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sB b hb] at h1
  have h2 := hreg.spanFinrank_maximalIdeal
  rw [h1] at h2
  have h3 : (IsLocalRing.maximalIdeal (B.presheaf.stalk b)).spanFinrank = 1 := by exact_mod_cast h2
  obtain ⟨⟨π, hπ⟩, -⟩ := (Submodule.spanFinrank_eq_one_iff _).mp h3
  refine ⟨π, hπ, fun h0 => ?_⟩
  rw [h0, Submodule.spanFinrank_bot] at h3
  exact zero_ne_one h3

/-- Krull's principal ideal theorem at a point of a fibre: if the maximal ideal of `𝒪_{B, g y}`
is principal and no proper generization of `y` maps to `g y`, then `y` has coheight `≤ 1`. -/
private lemma coheight_le_one_of_maximal_fiber {Y B : Scheme.{0}} (g : Y ⟶ B) (y : Y)
    [IsNoetherianRing (Y.presheaf.stalk y)] (π : B.presheaf.stalk (g y))
    (hπ : IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) = Ideal.span {π})
    (hmax : ∀ y' : Y, y' ⤳ y → g y' = g y → y' = y) : Order.coheight y ≤ 1 := by
  set O := Y.presheaf.stalk y
  set φ := (g.stalkMap y).hom
  set a : O := φ π
  have haM : a ∈ IsLocalRing.maximalIdeal O := by
    have hπM : π ∈ IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) :=
      hπ ▸ Ideal.mem_span_singleton_self π
    exact map_nonunit φ π hπM
  have hmin : IsLocalRing.maximalIdeal O ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr haM⟩, ?_⟩
    rintro q ⟨hq, hqa⟩ -
    let p : Spec (Y.presheaf.stalk y) := (⟨q, hq⟩ : PrimeSpectrum O)
    have hspec : Y.fromSpecStalk y p ⤳ y :=
      ((IsLocalRing.specializes_closedPoint p).map (Y.fromSpecStalk y).continuous).trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
    have hcomap : (Spec.map (g.stalkMap y)) p = IsLocalRing.closedPoint _ := by
      apply PrimeSpectrum.ext
      change Ideal.comap φ q = _
      refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
      change IsLocalRing.maximalIdeal _ ≤ _
      rw [hπ, Ideal.span_le, Set.singleton_subset_iff]
      exact hqa (Ideal.subset_span rfl)
    have hg : g (Y.fromSpecStalk y p) = g y := by
      calc g (Y.fromSpecStalk y p) = (Y.fromSpecStalk y ≫ g) p := rfl
        _ = (Spec.map (g.stalkMap y) ≫ B.fromSpecStalk (g y)) p := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
        _ = B.fromSpecStalk (g y) (Spec.map (g.stalkMap y) p) := rfl
        _ = g y := by rw [hcomap, Scheme.fromSpecStalk_closedPoint]
    have hy' := hmax _ hspec hg
    have hp : p = IsLocalRing.closedPoint O := by
      apply (Y.fromSpecStalk y).isEmbedding.injective
      rw [hy', Scheme.fromSpecStalk_closedPoint]
    exact (congrArg PrimeSpectrum.asIdeal hp).symm.le
  haveI : (Ideal.span {a}).IsPrincipal := ⟨⟨a, rfl⟩⟩
  have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have e := ringKrullDim_stalk_eq_coheight y
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at e
  have e' : Order.coheight y = (IsLocalRing.maximalIdeal O).height := by exact_mod_cast e.symm
  exact e'.trans_le hh

private lemma three_le_of_add_eq {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 4) (hc : c ≤ 1) :
    3 ≤ d := by
  have h1 : ((3 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) ≤ d + ((1 : ℕ) : WithBot ℕ∞) := by
    calc ((3 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) = d + c := by rw [h]; rfl
      _ ≤ d + ((1 : ℕ) : WithBot ℕ∞) := by
        gcongr
        exact_mod_cast hc
  exact_mod_cast ENat.WithBot.add_le_add_natCast_right_iff.mp h1

/-- On an integral scheme of finite type over `ℂ` of dimension four, a nonempty open subset has
dimension four. -/
private lemma topologicalKrullDim_opens_eq {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 4) (W : Y.Opens) [Nonempty W] :
    topologicalKrullDim W = 4 := by
  have := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  obtain ⟨y0, hy0W, hy0c⟩ := nonempty_inter_closedPoints ⟨w.1, w.2⟩ W.isOpen.isLocallyClosed
  have hcl : IsClosed ({y0} : Set Y) := mem_closedPoints_iff.mp hy0c
  have hY := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y0
  rw [hcl.closure_eq, hdim] at hY
  let y0' : (W : Scheme.{0}) := ⟨y0, hy0W⟩
  have hW := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (W.ι ≫ sY) y0'
  have hcl' : IsClosed ({y0'} : Set (W : Scheme.{0})) := by
    have : ({y0'} : Set (W : Scheme.{0})) = W.ι ⁻¹' {y0} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨by rintro rfl; rfl, fun h => W.ι.isOpenEmbedding.injective h⟩
    rw [this]
    exact hcl.preimage W.ι.continuous
  rw [hcl'.closure_eq] at hW
  have hcoh : Order.coheight y0' = Order.coheight y0 :=
    (Topology.IsOpenEmbedding.coheight_eq (x := y0') W.ι W.ι.isOpenEmbedding).symm
  rw [hcoh] at hW
  have e1 : topologicalKrullDim (↥({y0} : Set Y)) =
      topologicalKrullDim (↥({y0'} : Set (W : Scheme.{0}))) := by
    rw [topologicalKrullDim_singleton, topologicalKrullDim_singleton]
  rw [← e1, hY] at hW
  exact hW.symm

private lemma coheight_lt_top_of_isLocallyNoetherian {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (y : Y) :
    Order.coheight y < ⊤ := by
  have h := ringKrullDim_stalk_eq_coheight y
  have h2 : ringKrullDim (Y.presheaf.stalk y) < ⊤ := ringKrullDim_lt_top
  rw [h] at h2
  exact WithBot.coe_lt_coe.mp h2

/-- In a nonempty open part `W ∩ g⁻¹{b}` of a fibre over a point with principal maximal ideal
there is a point `ξ` with no proper generization in the fibre; it has coheight `≤ 1`. -/
private lemma exists_maximal_point_inter_fiber {Y B : Scheme.{0}} [IsLocallyNoetherian Y]
    (g : Y ⟶ B)
    (b : B) (hπ : ∀ y : Y, g y = b → ∃ π : B.presheaf.stalk (g y),
      IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) = Ideal.span {π})
    (W : Set Y) (hW : IsOpen W) (hne : (W ∩ g ⁻¹' {b}).Nonempty) :
    ∃ ξ ∈ W ∩ g ⁻¹' {b}, Order.coheight ξ ≤ 1 ∧ ∀ y' : Y, y' ⤳ ξ → g y' = g ξ → y' = ξ := by
  set S := g ⁻¹' {b}
  obtain ⟨u, huW, huS⟩ := hne
  let A : Set Y := {y | y ∈ S ∧ y ⤳ u}
  obtain ⟨m, ⟨ξ, ⟨hξS, hξu⟩, rfl⟩, hξmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min
    (Order.coheight '' A) ⟨_, u, ⟨huS, specializes_rfl⟩, rfl⟩
  have hξW : ξ ∈ W := hξu.mem_open hW huW
  have hmax : ∀ y' : Y, y' ⤳ ξ → g y' = g ξ → y' = ξ := by
    intro y' hy' hg
    by_contra hne'
    have hlt : ξ < y' := lt_of_le_not_ge hy' (fun h => hne' (hy'.antisymm h).eq)
    have hc := Order.coheight_strictAnti hlt (coheight_lt_top_of_isLocallyNoetherian y')
    refine hξmin _ ⟨y', ⟨?_, hy'.trans hξu⟩, rfl⟩ hc
    change g y' ∈ ({b} : Set B)
    rw [hg]; exact hξS
  obtain ⟨π, hπ'⟩ := hπ ξ hξS
  exact ⟨ξ, ⟨hξW, hξS⟩, coheight_le_one_of_maximal_fiber g ξ π hπ' hmax, hmax⟩

/-- **Lower bound for fibre dimension.** Let `Y` be an integral scheme of finite type over `ℂ` of
dimension four and `g : Y ⟶ B` such that the local ring of `B` at a closed point `b` has principal
maximal ideal. Every nonempty open part `W ∩ g⁻¹{b}` of the fibre has dimension `≥ 3`. -/
private lemma three_le_topologicalKrullDim_inter_fiber {Y B : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsIntegral Y] [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 4) (g : Y ⟶ B)
    (b : B) (hb : IsClosed ({b} : Set B))
    (hπ : ∀ y : Y, g y = b → ∃ π : B.presheaf.stalk (g y),
      IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) = Ideal.span {π})
    (W : Set Y) (hW : IsOpen W) (hne : (W ∩ g ⁻¹' {b}).Nonempty) :
    3 ≤ topologicalKrullDim ↥(W ∩ g ⁻¹' {b}) := by
  set S := g ⁻¹' {b}
  have hSc : IsClosed S := hb.preimage g.continuous
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨ξ, ⟨hξW, hξS⟩, hc1, -⟩ := exists_maximal_point_inter_fiber g b hπ W hW hne
  let W' : Y.Opens := ⟨W, hW⟩
  haveI : Nonempty W' := ⟨⟨ξ, hξW⟩⟩
  have hdimW := topologicalKrullDim_opens_eq sY hdim W'
  let ξ' : (W' : Scheme.{0}) := ⟨ξ, hξW⟩
  have hF := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (W'.ι ≫ sY) ξ'
  have hcoh : Order.coheight ξ' = Order.coheight ξ :=
    (Topology.IsOpenEmbedding.coheight_eq (x := ξ') W'.ι W'.ι.isOpenEmbedding).symm
  rw [hcoh] at hF
  have hF' : topologicalKrullDim ↥(closure {ξ'} : Set (W' : Scheme.{0})) + Order.coheight ξ = 4 :=
    hF.trans hdimW
  have h3 := three_le_of_add_eq hF' hc1
  refine h3.trans ?_
  -- the closure of `ξ'` in `W` lies in `W ∩ S`
  have hsub : ∀ z ∈ (closure {ξ'} : Set (W' : Scheme.{0})), z.1 ∈ W ∩ S := by
    intro z hz
    refine ⟨z.2, ?_⟩
    have hz' : (W'.ι z) ∈ closure ({W'.ι ξ'} : Set Y) :=
      map_mem_closure W'.ι.continuous hz fun w hw => by
        rw [Set.mem_singleton_iff.mp hw]
        exact Set.mem_singleton _
    exact hSc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξS) hz'
  let incl : ↥(closure {ξ'} : Set (W' : Scheme.{0})) → ↥(W ∩ S) :=
    fun z => ⟨z.1.1, hsub z.1 z.2⟩
  have hind : Topology.IsInducing incl := by
    have h0 := Topology.IsInducing.comp (g := Subtype.val (p := fun x : Y => x ∈ (W' : Set Y)))
      (f := Subtype.val
        (p := fun x : (W' : Scheme.{0}) => x ∈ (closure {ξ'} : Set (W' : Scheme.{0}))))
      Topology.IsInducing.subtypeVal Topology.IsInducing.subtypeVal
    have h1 : Topology.IsInducing (Subtype.val ∘ incl) := h0
    exact (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp h1
  exact hind.topologicalKrullDim_le

/-- An open subset of a fibre is homeomorphic to the trace on the fibre of an open subset of the
source. -/
private lemma exists_isOpen_topologicalKrullDim_fiber_opens_eq {Y B : Scheme.{0}} (g : Y ⟶ B)
    (b : B)
    (U : (g.fiber b).Opens) : ∃ W : Set Y, IsOpen W ∧
      topologicalKrullDim U = topologicalKrullDim ↥(W ∩ g ⁻¹' {b}) ∧
      ((U : Set (g.fiber b)).Nonempty → (W ∩ g ⁻¹' {b}).Nonempty) ∧
      W ∩ g ⁻¹' {b} = g.fiberι b '' (U : Set (g.fiber b)) := by
  have he := (g.fiberι b).isEmbedding
  obtain ⟨W, hW, hWU⟩ := he.isInducing.isOpen_iff.mp U.isOpen
  have hmem : ∀ z : U, g.fiberι b z.1 ∈ W ∩ g ⁻¹' {b} := by
    intro z
    refine ⟨?_, ?_⟩
    · have : z.1 ∈ (g.fiberι b) ⁻¹' W := by rw [hWU]; exact z.2
      exact this
    · rw [← Scheme.Hom.range_fiberι]; exact ⟨_, rfl⟩
  let φ : U → ↥(W ∩ g ⁻¹' {b}) := fun z => ⟨g.fiberι b z.1, hmem z⟩
  have hφ : IsHomeomorph φ := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, ?_⟩
    · have h1 : Topology.IsEmbedding (Subtype.val ∘ φ) :=
        he.comp Topology.IsEmbedding.subtypeVal
      exact (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp h1
    · rintro ⟨y, hyW, hyS⟩
      rw [← Scheme.Hom.range_fiberι] at hyS
      obtain ⟨z, rfl⟩ := hyS
      have hz : z ∈ (U : Set (g.fiber b)) := by rw [← hWU]; exact hyW
      exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨W, hW, IsHomeomorph.topologicalKrullDim_eq φ hφ, ?_, ?_⟩
  · rintro ⟨z, hz⟩
    exact ⟨_, hmem ⟨z, hz⟩⟩
  · ext y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := hφ.surjective ⟨y, hy⟩
      exact ⟨z.1, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz, rfl⟩
      exact hmem ⟨z, hz⟩

/-- **Upper bound for fibre dimension**: the fibre over a point not hit by the generic point of an
integral scheme of dimension four has dimension at most three. -/
private lemma topologicalKrullDim_inter_fiber_le {Y B : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (hdim : topologicalKrullDim Y = 4) (g : Y ⟶ B) (b : B)
    (hb : IsClosed ({b} : Set B)) (hη : g (genericPoint Y) ≠ b) (W : Set Y) :
    topologicalKrullDim ↥(W ∩ g ⁻¹' {b}) ≤ 3 := by
  set S := g ⁻¹' {b}
  have hSc : IsClosed S := hb.preimage g.continuous
  have hnd : IsNowhereDense S := by
    rw [hSc.isNowhereDense_iff]
    by_contra hne
    have hη' : genericPoint Y ∈ interior S :=
      ((genericPoint_spec Y).mem_open_set_iff isOpen_interior).mpr
        (by rw [Set.univ_inter]; exact Set.nonempty_iff_ne_empty.mpr hne)
    exact hη (interior_subset hη' : genericPoint Y ∈ S)
  have h1 := hnd.topologicalKrullDim_add_one_le hSc
  rw [hdim] at h1
  have h2 : topologicalKrullDim S ≤ 3 := by
    have h1' : topologicalKrullDim S + ((1 : ℕ) : WithBot ℕ∞) ≤
        ((3 : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h1
    exact_mod_cast ENat.WithBot.add_le_add_natCast_right_iff.mp h1'
  refine le_trans ?_ h2
  exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le

private lemma isOpenMap_of_smooth {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Smooth f) : IsOpenMap f := by
  have : UniversallyOpen f := UniversallyOpen.of_flat f
  exact f.isOpenMap

/-- If `f ≫ g` is open and `Z` is nonempty, then the generic point of `Y` does not map to a
closed point `b` which is not open. -/
private lemma map_genericPoint_ne {Y Z B : Scheme.{0}} [IsIntegral Y] (g : Y ⟶ B) (f : Z ⟶ Y)
    [Nonempty Z] (hopen : IsOpenMap (f ≫ g)) (b : B) (hb : IsClosed ({b} : Set B))
    (hnot : ¬ IsOpen ({b} : Set B)) : g (genericPoint Y) ≠ b := by
  intro hη
  have hall : ∀ y : Y, g y = b := fun y =>
    (((genericPoint_spec Y).specializes (Set.mem_univ y)).map g.continuous).mem_closed hb hη
  have hrange : Set.range (f ≫ g) = {b} := by
    ext c
    constructor
    · rintro ⟨z, rfl⟩
      exact hall (f z)
    · rintro rfl
      obtain ⟨z⟩ := (inferInstance : Nonempty Z)
      exact ⟨z, hall (f z)⟩
  exact hnot (hrange ▸ hopen.isOpen_range)

private lemma nonempty_of_isIso_app {X Z : Scheme.{0}} [IsIntegral X] (f : Z ⟶ X)
    (hf₀ : ∀ U : X.Opens, IsIso (f.app U)) : Nonempty Z := by
  by_contra hZ
  rw [not_nonempty_iff] at hZ
  haveI := hf₀ ⊤
  have hinj : Function.Injective (f.app ⊤).hom :=
    (ConcreteCategory.bijective_of_isIso (f.app ⊤)).1
  have : Subsingleton Γ(X, ⊤) := hinj.subsingleton
  exact not_subsingleton Γ(X, ⊤) this

private lemma exists_maximalIdeal_stalk_eq_span_of_map_eq {Y B : Scheme.{0}}
    (sB : B ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sB]
    (g : Y ⟶ B) (b : B) (hb : IsClosed ({b} : Set B)) :
    ∀ y : Y, g y = b → ∃ π : B.presheaf.stalk (g y),
      IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) = Ideal.span {π} := by
  rintro y rfl
  exact (exists_maximalIdeal_eq_span_and_ne_bot sB (g y) hb).imp fun _ h ↦ h.1

private lemma pureDim_fiber {X Z B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [IsVariety ℂ sX] (hdim : topologicalKrullDim X = 4) (f : Z ⟶ X)
    (hf₀ : ∀ U : X.Opens, IsIso (f.app U)) [SmoothOfRelativeDimension 1 sB] (t : X ⟶ B)
    [Smooth (f ≫ t)] (b : B) (hb : IsClosed {b}) :
    ∀ U : (t.fiber b).Opens, (U : Set (t.fiber b)).Nonempty → topologicalKrullDim U = 3 := by
  intro U hU
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have : Nonempty Z := nonempty_of_isIso_app f hf₀
  have hη := map_genericPoint_ne t f (isOpenMap_of_smooth (f ≫ t) inferInstance) b hb
    (not_isOpen_singleton_of_smoothOfRelativeDimension_one sB b)
  obtain ⟨W, hW, hdimU, hne, -⟩ := exists_isOpen_topologicalKrullDim_fiber_opens_eq t b U
  rw [hdimU]
  refine le_antisymm (topologicalKrullDim_inter_fiber_le hdim t b hb hη W) ?_
  exact three_le_topologicalKrullDim_inter_fiber sX hdim t b hb
    (exists_maximalIdeal_stalk_eq_span_of_map_eq sB t b hb) W hW (hne hU)

/-- The trace `T_b` of `T` on a fibre has no nontrivial specializations. -/
private lemma eq_of_specializes_fiber_range {X T B : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι]
    (t : X ⟶ B) [IsFinite (ι ≫ t)] (b : B) {a c : t.fiber b}
    (ha : a ∈ t.fiberι b ⁻¹' Set.range ι) (hc : c ∈ t.fiberι b ⁻¹' Set.range ι) (h : a ⤳ c) :
    a = c := by
  haveI := instLocallyQuasiFiniteOfIsFinite (ι ≫ t)
  obtain ⟨τa, hτa⟩ := ha
  obtain ⟨τc, hτc⟩ := hc
  have h1 : ι τa ⤳ ι τc := by rw [hτa, hτc]; exact h.map (t.fiberι b).continuous
  have h2 : τa ⤳ τc := ι.isClosedEmbedding.isInducing.specializes_iff.mp h1
  have h3 : (ι ≫ t) τa = (ι ≫ t) τc := by
    simp only [Scheme.Hom.comp_apply, hτa, hτc, Scheme.Hom.apply_fiberι]
  have h4 := MMP.Flips.eq_of_specializes_of_locallyQuasiFinite (ι ≫ t) h2 h3
  apply (t.fiberι b).isEmbedding.injective
  rw [← hτa, ← hτc, h4]

private lemma topologicalKrullDim_fiber_range_le_zero {X T B : Scheme.{0}} (ι : T ⟶ X)
    [IsClosedImmersion ι] (t : X ⟶ B) [IsFinite (ι ≫ t)] (b : B) :
    topologicalKrullDim ↥(t.fiberι b ⁻¹' Set.range ι) ≤ 0 := by
  set S := t.fiberι b ⁻¹' Set.range ι
  have hfin : S.Finite := finite_fiberι_preimage_range ι t b
  haveI : Finite S := hfin.to_subtype
  haveI : T1Space S := by
    rw [t1Space_iff_specializes_imp_eq]
    intro a c h
    exact Subtype.ext (eq_of_specializes_fiber_range ι t b a.2 c.2
      ((subtype_specializes_iff a c).mp h))
  haveI : DiscreteTopology S := Finite.instDiscreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology _

private lemma dense_compl_fiber_range {X T B : Scheme.{0}} (ι : T ⟶ X) [IsClosedImmersion ι]
    (t : X ⟶ B) [IsFinite (ι ≫ t)] (b : B)
    (hpure : ∀ U : (t.fiber b).Opens, (U : Set (t.fiber b)).Nonempty → topologicalKrullDim U = 3) :
    Dense (t.fiberι b ⁻¹' Set.range ι)ᶜ := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  by_contra hne
  have hsub : O ⊆ t.fiberι b ⁻¹' Set.range ι := by
    intro x hx
    by_contra hx'
    exact hne ⟨x, hx, hx'⟩
  have h3 := hpure ⟨O, hO⟩ hOne
  have h4 := (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le.trans
    (topologicalKrullDim_fiber_range_le_zero ι t b)
  change topologicalKrullDim ↥O = 3 at h3
  rw [h3] at h4
  exact absurd h4 (by decide)

/-- No nonempty open subset of a fibre of `g` lies in the union of finitely many prime divisors
each of which is smooth over the base. -/
private lemma not_image_subset_iUnion_support {Z B : Scheme.{0}} [IsLocallyNoetherian Z] (g : Z ⟶ B)
    (b : B) (hb : IsClosed ({b} : Set B)) (hnot : ¬ IsOpen ({b} : Set B))
    (hπ : ∀ y : Z, g y = b → ∃ π : B.presheaf.stalk (g y),
      IsLocalRing.maximalIdeal (B.presheaf.stalk (g y)) = Ideal.span {π})
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hP : ∀ P ∈ s, Smooth (P.idealSheaf.subschemeι ≫ g))
    (O : (g.fiber b).Opens) (hO : (O : Set (g.fiber b)).Nonempty) :
    ¬ (g.fiberι b '' (O : Set (g.fiber b)) ⊆ ⋃ P ∈ s, (P.support : Set Z)) := by
  intro hsub
  obtain ⟨W, hW, -, hne, himg⟩ := exists_isOpen_topologicalKrullDim_fiber_opens_eq g b O
  obtain ⟨ξ, hξ, hc1, -⟩ := exists_maximal_point_inter_fiber g b hπ W hW (hne hO)
  have hξE := hsub (himg ▸ hξ)
  simp only [Set.mem_iUnion] at hξE
  obtain ⟨P, hPs, hξP⟩ := hξE
  haveI := P.integral
  have hrange : Set.range P.idealSheaf.subschemeι = P.support :=
    Scheme.IdealSheafData.range_subschemeι _
  set p := P.genericPoint with hpdef
  have hspec : ∀ z ∈ P.support, p ⤳ z := by
    intro z hz
    rw [← hrange] at hz
    obtain ⟨w, rfl⟩ := hz
    exact ((genericPoint_spec P.idealSheaf.subscheme).specializes (Set.mem_univ w)).map
      P.idealSheaf.subschemeι.continuous
  have hp1 : Order.coheight p = 1 := by
    rw [← MMP.Flips.codimension_closureSingleton]
    exact P.codimension_closureSingleton_genericPoint
  have hpξ : p = ξ := by
    by_contra hne'
    have hlt : ξ < p := lt_of_le_not_ge (hspec ξ hξP) (fun h => hne' ((hspec ξ hξP).antisymm h).eq)
    have := Order.coheight_strictAnti hlt (coheight_lt_top_of_isLocallyNoetherian p)
    rw [hp1] at this
    exact absurd (this.trans_le hc1) (lt_irrefl _)
  have hgp : g p = b := by rw [hpξ]; exact hξ.2
  have hall : ∀ z ∈ P.support, g z = b := fun z hz =>
    ((hspec z hz).map g.continuous).mem_closed hb hgp
  have hopen := (isOpenMap_of_smooth (P.idealSheaf.subschemeι ≫ g) (hP P hPs)).isOpen_range
  have hr : Set.range (P.idealSheaf.subschemeι ≫ g) = {b} := by
    ext c
    constructor
    · rintro ⟨w, rfl⟩
      exact hall _ (hrange ▸ ⟨w, rfl⟩)
    · rintro rfl
      obtain ⟨w⟩ := (inferInstance : Nonempty P.idealSheaf.subscheme)
      exact ⟨w, hall _ (hrange ▸ ⟨w, rfl⟩)⟩
  exact hnot (hr ▸ hopen)

/-- A morphism which is an isomorphism over a dense open `V` whose preimage is dense is
birational. -/
private lemma isBirationalMorphism_of_isIso_morphismRestrict {Y X' : Scheme.{0}} (g : Y ⟶ X')
    (V : X'.Opens) (hV : Dense (V : Set X')) (hU : Dense ((g ⁻¹ᵁ V : Y.Opens) : Set Y))
    [IsIso (g ∣_ V)] : MMP.Mori.IsBirationalMorphism g := by
  have hiso : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let e : Y.PartialIso X' :=
    { source := g ⁻¹ᵁ V
      dense_source := hU
      target := V
      dense_target := hV
      iso := asIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨g ⁻¹ᵁ V, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, asIso_hom, Scheme.Hom.resLE_comp_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- `R¹f_*𝒪 = 0` restricts to an open of the target ([Stacks, Tag 01E5]). -/
private lemma isZero_rightDerived_one_morphismRestrict {X Y : Scheme.{0}} (c : X ⟶ Y)
    (hR1 : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) (V : Y.Opens) :
    IsZero (((Scheme.Modules.pushforward (c ∣_ V)).rightDerived 1).obj
      (SheafOfModules.unit (c ⁻¹ᵁ V).toScheme.ringCatSheaf)) :=
  (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) hR1).of_iso
    (((Scheme.Modules.pushforward (c ∣_ V)).rightDerived 1).mapIso
        (Scheme.Modules.restrictUnitIso (c ⁻¹ᵁ V).ι).symm ≪≫
      (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso c V 1).app
        (SheafOfModules.unit X.ringCatSheaf))

/-- **`H¹(f⁻¹U, 𝒪_Z) = 0` over an affine open `U`** when `R¹f_*𝒪_Z = 0` and `f` is
quasi-compact and quasi-separated: over the affine `U` the first cohomology upstairs is the
module of sections of `R¹(f ∣_ U)_*𝒪` ([Stacks, Tag 01XK]), which vanishes by
`isZero_rightDerived_one_morphismRestrict`. -/
private lemma isZero_rightDerived_one_sections_preimage {X Z : Scheme.{0}} (f : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Z.ringCatSheaf))) (U : X.Opens) (hU : IsAffineOpen U) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ U).toScheme).rightDerived
      1).obj (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) := by
  haveI : IsAffine U.toScheme := hU
  have h1 := isZero_rightDerived_one_morphismRestrict f hR1 U
  have e := (Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso (f ∣_ U) 1).app
    (⟨SheafOfModules.unit _, inferInstance⟩ :
      (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ U).toScheme.ringCatSheaf).FullSubcategory)
  have h2 : IsZero ((Stacks.Cohomology.AffineBase.moduleGlobalSections U.toScheme).obj
      (((Scheme.Modules.pushforward (f ∣_ U)).rightDerived 1).obj
        (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf))) :=
    Functor.map_isZero _ h1
  have h3 := h2.of_iso e
  rw [ModuleCat.isZero_iff_subsingleton] at h3 ⊢
  exact h3

section NormalSlice

/-- A finitely generated ideal each of whose elements is multiplied into `T` by an element
outside the prime `p` is multiplied into `T` by a single such element. -/
private lemma exists_uniform {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (T J : Ideal R)
    (hJ : J.FG) (h : ∀ x ∈ J, ∃ w ∉ p, w * x ∈ T) : ∃ w ∉ p, ∀ x ∈ J, w * x ∈ T := by
  classical
  obtain ⟨G, rfl⟩ := hJ
  induction G using Finset.induction_on with
  | empty => exact ⟨1, p.ne_top_iff_one.mp (Ideal.IsPrime.ne_top ‹_›), fun x hx => by
      simp only [Finset.coe_empty, Ideal.span_empty, Submodule.mem_bot] at hx
      simp [hx, T.zero_mem]⟩
  | insert g G hg ih =>
    obtain ⟨w₁, hw₁, h₁⟩ := ih fun x hx => h x (Ideal.span_mono (by simp) hx)
    obtain ⟨w₂, hw₂, h₂⟩ := h g (Ideal.subset_span (by simp))
    refine ⟨w₂ * w₁, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hw₂ hw₁, fun x hx => ?_⟩
    rw [Finset.coe_insert, Ideal.mem_span_insert] at hx
    obtain ⟨c, z, hz, rfl⟩ := hx
    have : w₂ * w₁ * (c * g + z) = (w₁ * c) * (w₂ * g) + w₂ * (w₁ * z) := by ring
    rw [this]
    exact T.add_mem (T.mul_mem_left _ h₂) (T.mul_mem_left _ (h₁ z hz))

/-- **A local parameter spread out.** If the localization of a Noetherian ring at a prime `p`
is a domain whose maximal ideal is principal and nonzero, there are `a ∈ p` and `s ∉ p` with
`s p ⊆ (a)` and `s · Ann(a) = 0`. -/
private lemma exists_param {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [IsDomain Rp] (π : Rp) (hπ : IsLocalRing.maximalIdeal Rp = Ideal.span {π})
    (hne : IsLocalRing.maximalIdeal Rp ≠ ⊥) :
    ∃ a ∈ p, ∃ s ∉ p, (∀ x ∈ p, s * x ∈ Ideal.span {a}) ∧ (∀ r, r * a = 0 → s * r = 0) := by
  obtain ⟨⟨a, u⟩, hau⟩ := IsLocalization.mk'_surjective p.primeCompl π
  have hmax : ∀ x : R, algebraMap R Rp x ∈ IsLocalRing.maximalIdeal Rp ↔ x ∈ p :=
    fun x => IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p x
  have hspan : IsLocalRing.maximalIdeal Rp = Ideal.span {algebraMap R Rp a} := by
    dsimp only at hau
    rw [hπ, ← hau, IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one (algebraMap R Rp u)
      (by rw [IsLocalization.mk'_spec, map_one])) _
  have ha : a ∈ p := (hmax a).1 (hspan ▸ Ideal.mem_span_singleton_self _)
  have hA : ∀ x ∈ p, ∃ w ∉ p, w * x ∈ Ideal.span {a} := by
    intro x hx
    have := (hmax x).2 hx
    rw [hspan, Ideal.mem_span_singleton'] at this
    obtain ⟨y, hy⟩ := this
    obtain ⟨⟨r, v⟩, hrv⟩ := IsLocalization.mk'_surjective p.primeCompl y
    dsimp only at hrv
    subst hrv
    have hy' : algebraMap R Rp (v * x) = algebraMap R Rp (r * a) := by
      rw [map_mul, ← hy, map_mul, ← mul_assoc, mul_comm (algebraMap R Rp v),
        IsLocalization.mk'_spec]
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl Rp).1 hy'
    refine ⟨c * v, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim c.2 v.2, ?_⟩
    rw [Ideal.mem_span_singleton']
    exact ⟨c * r, by rw [mul_assoc (c : R) (v : R) x, hc]; ring⟩
  have ha0 : algebraMap R Rp a ≠ 0 := by
    intro h0
    apply hne
    rw [hspan, h0, Ideal.span_singleton_eq_bot]
  have hB : ∀ r ∈ LinearMap.ker (LinearMap.mulRight R a), ∃ w ∉ p, w * r ∈ (⊥ : Ideal R) := by
    intro r hr
    have hr' : r * a = 0 := hr
    have : algebraMap R Rp r = 0 := by
      have := congrArg (algebraMap R Rp) hr'
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.1 this).resolve_right ha0
    obtain ⟨⟨c, hc⟩, hcr⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp r).1 this
    exact ⟨c, hc, by simpa using hcr⟩
  obtain ⟨w₁, hw₁, h₁⟩ := exists_uniform p _ p (IsNoetherian.noetherian p) hA
  obtain ⟨w₂, hw₂, h₂⟩ := exists_uniform p ⊥ _ (IsNoetherian.noetherian _) hB
  refine ⟨a, ha, w₁ * w₂, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hw₁ hw₂, ?_, ?_⟩
  · intro x hx
    rw [mul_comm w₁, mul_assoc]
    exact Ideal.mul_mem_left _ _ (h₁ x hx)
  · intro r hr
    have := h₂ r hr
    rw [Submodule.mem_bot] at this
    rw [mul_comm w₁, mul_assoc, mul_comm w₁, ← mul_assoc, this, zero_mul]

/-- `Spec κ(b)` lies over every open containing `b`. -/
private lemma le_preimage_fromSpecResidueField {B : Scheme.{0}} (b : B) {S : B.Opens}
    (hbS : b ∈ S) : ⊤ ≤ B.fromSpecResidueField b ⁻¹ᵁ S := by
  intro y _
  change B.fromSpecResidueField b y ∈ S
  rw [Scheme.fromSpecResidueField_apply]
  exact hbS

/-- Restriction to `Spec κ(b)` is the germ at `b` followed by the residue map. -/
private lemma fromSpecResidueField_appLE_eq {B : Scheme.{0}} (b : B) (S₁ : B.Opens) (hbS : b ∈ S₁)
    (h : ⊤ ≤ B.fromSpecResidueField b ⁻¹ᵁ S₁) :
    (B.fromSpecResidueField b).appLE S₁ ⊤ h =
      B.presheaf.germ S₁ b hbS ≫ B.residue b ≫ (Scheme.ΓSpecIso _).inv := by
  have h1 : ⊤ ≤ B.fromSpecStalk b ⁻¹ᵁ S₁ := by
    intro y _
    change B.fromSpecStalk b y ∈ S₁
    have hs : B.fromSpecStalk b y ⤳ b := by
      have hmem : B.fromSpecStalk b y ∈ Set.range (B.fromSpecStalk b) := ⟨y, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hmem
      exact hmem
    exact hs.mem_open S₁.isOpen hbS
  have h2 : ⊤ ≤ Spec.map (B.residue b) ⁻¹ᵁ (⊤ : (Spec (B.presheaf.stalk b)).Opens) := le_top
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (B.residue b)) (B.fromSpecStalk b) S₁ ⊤ ⊤ h1 h2
  refine (e.symm.trans ?_)
  have hid : ∀ (i : Opposite.op (⊤ : (Spec (B.presheaf.stalk b)).Opens) ⟶ Opposite.op ⊤),
      (Spec (B.presheaf.stalk b)).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]
  have e1 : (B.fromSpecStalk b).appLE S₁ ⊤ h1 =
      B.presheaf.germ S₁ b hbS ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hbS]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
    rw [hid, Category.comp_id]
  have e2 : (Spec.map (B.residue b)).appLE ⊤ ⊤ h2 =
      (Scheme.ΓSpecIso _).hom ≫ B.residue b ≫ (Scheme.ΓSpecIso _).inv := by
    have : (Spec.map (B.residue b)).appLE ⊤ ⊤ h2 = (Spec.map (B.residue b)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this]
    simp
  rw [e1, e2]
  simp

/-- The kernel of evaluation at `b` on an affine open is the prime ideal of `b`. -/
private lemma fromSpecResidueField_appLE_eq_zero_iff {B : Scheme.{0}} (b : B) {S₁ : B.Opens}
    (hbS : b ∈ S₁) (y : Γ(B, S₁)) :
    (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) y = 0 ↔
      B.presheaf.germ S₁ b hbS y ∈ IsLocalRing.maximalIdeal (B.presheaf.stalk b) := by
  rw [fromSpecResidueField_appLE_eq b S₁ hbS]
  simp only [CommRingCat.comp_apply]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1]
  exact IsLocalRing.residue_eq_zero_iff _

/-- **A local parameter at a closed point of a smooth curve**, on an affine open `S₁ ∋ b`:
`a` vanishes at `b`, `s` does not, `s` multiplies the ideal of `b` into `(a)` and kills the
annihilator of `a`. -/
private lemma exists_local_parameter {B : Scheme.{0}} (sB : B ⟶ Spec (.of ℂ))
    [SmoothOfRelativeDimension 1 sB] (b : B) (hb : IsClosed ({b} : Set B)) :
    ∃ (S₁ : B.Opens) (_ : IsAffineOpen S₁) (hbS : b ∈ S₁) (a s : Γ(B, S₁)),
      (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0 ∧
      b ∈ B.basicOpen s ∧
      (∀ x, (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) x = 0 →
        s * x ∈ Ideal.span {a}) ∧
      (∀ r, r * a = 0 → s * r = 0) := by
  have : Smooth sB := SmoothOfRelativeDimension.smooth 1 sB
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian sB
  haveI : IsNormal B := isNormal_of_isRegular B (isRegular_of_smooth_over_field sB)
  obtain ⟨S₁, hS₁, hbS, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top b)
  haveI : IsNoetherianRing Γ(B, S₁) := IsLocallyNoetherian.component_noetherian ⟨S₁, hS₁⟩
  let x : S₁ := ⟨b, hbS⟩
  letI : Algebra Γ(B, S₁) (B.presheaf.stalk b) :=
    TopCat.Presheaf.algebra_section_stalk B.presheaf x
  haveI : IsLocalization.AtPrime (B.presheaf.stalk b) (hS₁.primeIdealOf x).asIdeal :=
    hS₁.isLocalization_stalk x
  obtain ⟨π, hπ, hne⟩ := exists_maximalIdeal_eq_span_and_ne_bot sB b hb
  obtain ⟨a, ha, s, hs, h1, h2⟩ :=
    exists_param (hS₁.primeIdealOf x).asIdeal (B.presheaf.stalk b) π hπ hne
  have key : ∀ y, (B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS) y = 0 ↔ y ∈ (hS₁.primeIdealOf x).asIdeal :=
    fun y => (fromSpecResidueField_appLE_eq_zero_iff b hbS y).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ y)
  refine ⟨S₁, hS₁, hbS, a, s, (key a).2 ha, ?_, fun y hy => h1 y ((key y).1 hy), h2⟩
  rw [B.mem_basicOpen s b hbS]
  by_contra hu
  exact hs ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ s).1
    ((IsLocalRing.mem_maximalIdeal _).2 hu))

/-- **Functions vanishing on a fibre, over an affine open.** -/
private lemma fiberι_app_eq_zero_iff {Y B : Scheme.{0}} (h : Y ⟶ B) (b : B)
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (hbS : b ∈ S₁)
    (hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom)
    {V : Y.Opens} (hV : IsAffineOpen V) (hVS : V ≤ h ⁻¹ᵁ S₁) (x : Γ(Y, V)) :
    (h.fiberι b).app V x = 0 ↔
      x ∈ Ideal.map (h.appLE S₁ V hVS).hom (RingHom.ker ((B.fromSpecResidueField b).appLE S₁ ⊤
        (le_preimage_fromSpecResidueField b hbS)).hom) := by
  set g := B.fromSpecResidueField b with hg
  set ι := h.fiberι b with hι
  set p := h.fiberToSpecResidueField b with hp
  have H : IsPullback ι p h g := IsPullback.of_hasPullback h g
  have hTle : (⊤ : (Spec (B.residueField b)).Opens) ≤ g ⁻¹ᵁ S₁ :=
    le_preimage_fromSpecResidueField b hbS
  have hU' : ι ⁻¹ᵁ V = ι ⁻¹ᵁ V ⊓ p ⁻¹ᵁ ⊤ := by simp
  letI : Algebra Γ(B, S₁) Γ(Y, V) := (h.appLE S₁ V hVS).hom.toAlgebra
  letI : Algebra Γ(B, S₁) Γ(Spec (B.residueField b), ⊤) := (g.appLE S₁ ⊤ hTle).hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(h.fiber b, ι ⁻¹ᵁ V) :=
    (ι.appLE V (ι ⁻¹ᵁ V) (hU'.le.trans inf_le_left)).hom.toAlgebra
  letI : Algebra Γ(Spec (B.residueField b), ⊤) Γ(h.fiber b, ι ⁻¹ᵁ V) :=
    (p.appLE ⊤ (ι ⁻¹ᵁ V) (hU'.le.trans inf_le_right)).hom.toAlgebra
  letI : Algebra Γ(B, S₁) Γ(h.fiber b, ι ⁻¹ᵁ V) :=
    (h.appLE S₁ V hVS ≫ ι.appLE V (ι ⁻¹ᵁ V) (hU'.le.trans inf_le_left)).hom.toAlgebra
  have hw := (isPushout_appLE_of_isPullback H hS₁ hV hVS (isAffineOpen_top _) hTle hU').w
  haveI : IsScalarTower Γ(B, S₁) Γ(Y, V) Γ(h.fiber b, ι ⁻¹ᵁ V) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(B, S₁) Γ(Spec (B.residueField b), ⊤) Γ(h.fiber b, ι ⁻¹ᵁ V) :=
    .of_algebraMap_eq' congr($(hw).hom)
  haveI : Algebra.IsPushout Γ(B, S₁) Γ(Spec (B.residueField b), ⊤) Γ(Y, V)
      Γ(h.fiber b, ι ⁻¹ᵁ V) :=
    algebra_isPushout_appLE_of_isPullback H hS₁ hV hVS (isAffineOpen_top _) hTle hU'
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have h1 := one_tmul_eq_zero_iff_mem_smul_top_of_isPushout (R := Γ(B, S₁))
    (T := Γ(Spec (B.residueField b), ⊤)) (B := Γ(Y, V)) (C := Γ(h.fiber b, ι ⁻¹ᵁ V))
    (E := Γ(Y, V)) hsurj x
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at h1
  have h2 : (ι.app V) x = algebraMap Γ(Y, V) Γ(h.fiber b, ι ⁻¹ᵁ V) x := by
    change _ = (ι.appLE V (ι ⁻¹ᵁ V) _) x
    rw [Scheme.Hom.appLE_eq_app]
  rw [h2]
  refine Iff.trans ?_ h1
  rw [← (TensorProduct.rid Γ(Y, V) Γ(h.fiber b, ι ⁻¹ᵁ V)).map_eq_zero_iff,
    TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

/-- On an affine open over the basic open of `s`, the functions vanishing on the fibre are the
multiples of the parameter `a`. -/
private lemma fiberι_app_eq_zero_iff_mem_span {Y B : Scheme.{0}} (h : Y ⟶ B) (b : B)
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (hbS : b ∈ S₁)
    (hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom)
    (a s : Γ(B, S₁))
    (ha : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0)
    (hsK : ∀ x, (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) x
      = 0 → s * x ∈ Ideal.span {a})
    {V : Y.Opens} (hV : IsAffineOpen V) (hVS : V ≤ h ⁻¹ᵁ S₁) (hVs : V ≤ h ⁻¹ᵁ B.basicOpen s)
    (x : Γ(Y, V)) :
    (h.fiberι b).app V x = 0 ↔ x ∈ Ideal.span {h.appLE S₁ V hVS a} := by
  rw [fiberι_app_eq_zero_iff h b hS₁ hbS hsurj hV hVS x]
  set φ := (h.appLE S₁ V hVS).hom
  have hu : IsUnit (φ s) := by
    have hV' : V ≤ Y.basicOpen (h.app S₁ s) := by
      rw [← Scheme.preimage_basicOpen]; exact hVs
    have e : h.appLE S₁ V hVS = h.app S₁ ≫
        Y.presheaf.map (homOfLE (Y.basicOpen_le (h.app S₁ s))).op ≫
          Y.presheaf.map (homOfLE hV').op := by
      rw [Scheme.Hom.appLE, ← CategoryTheory.Functor.map_comp]; rfl
    change IsUnit ((h.appLE S₁ V hVS) s)
    rw [e, CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact (RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (h.app S₁ s)).map
      (Y.presheaf.map (homOfLE hV').op).hom
  suffices hK : Ideal.map φ (RingHom.ker ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom) = Ideal.span {φ a} by rw [hK]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have h1 : φ (s * y) ∈ Ideal.span {φ a} := by
      have := Ideal.mem_map_of_mem φ (hsK y hy)
      rwa [Ideal.map_span, Set.image_singleton] at this
    rw [map_mul] at h1
    obtain ⟨u, hu'⟩ := hu
    have : φ y = ↑u⁻¹ * (φ s * φ y) := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ h1
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem φ ha

/-- Over the basic open of `s`, the parameter `a` is a nonzerodivisor on the sections of a flat
`B`-scheme over affine opens. -/
private lemma eq_zero_of_appLE_mul_eq_zero {Y B : Scheme.{0}} (h : Y ⟶ B) [Flat h]
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (a s : Γ(B, S₁))
    (has : ∀ r, r * a = 0 → s * r = 0) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVS : V ≤ h ⁻¹ᵁ S₁) (hVs : V ≤ h ⁻¹ᵁ B.basicOpen s) (y : Γ(Y, V))
    (hy : h.appLE S₁ V hVS a * y = 0) : y = 0 := by
  haveI := hS₁.isLocalization_basicOpen s
  set a' := algebraMap Γ(B, S₁) Γ(B, B.basicOpen s) a with ha'
  have key : ∀ z, z * a' = 0 → z = 0 := by
    intro z hz
    obtain ⟨⟨r, ⟨_, k, rfl⟩⟩, hrz⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
    dsimp only at hrz
    subst hrz
    have hz' : IsLocalization.mk' Γ(B, B.basicOpen s) (r * a)
        (⟨s ^ k, k, rfl⟩ : Submonoid.powers s) = 0 := by
      rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, mul_right_comm,
        ← IsLocalization.mk'_eq_mul_mk'_one]
      exact hz
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.mk'_eq_zero_iff _ _).1 hz'
    have h1 := has (s ^ j * r) (by rw [mul_assoc]; exact hj)
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨s ^ (j + 1), j + 1, rfl⟩, ?_⟩
    change s ^ (j + 1) * r = 0
    rw [pow_succ', mul_assoc]
    exact h1
  have hreg : IsRegular a' := by
    refine ⟨fun x z hxz => ?_, fun x z hxz => ?_⟩
    · have hxz' : a' * x = a' * z := hxz
      have : (x - z) * a' = 0 := by rw [sub_mul, mul_comm x, mul_comm z, hxz', sub_self]
      exact sub_eq_zero.1 (key _ this)
    · have hxz' : x * a' = z * a' := hxz
      have : (x - z) * a' = 0 := by rw [sub_mul, hxz', sub_self]
      exact sub_eq_zero.1 (key _ this)
  have hflat := HasRingHomProperty.appLE @Flat h inferInstance ⟨B.basicOpen s, hS₁.basicOpen s⟩
    ⟨V, hV⟩ hVs
  letI : Algebra Γ(B, B.basicOpen s) Γ(Y, V) := (h.appLE (B.basicOpen s) V hVs).hom.toAlgebra
  haveI : Module.Flat Γ(B, B.basicOpen s) Γ(Y, V) := hflat
  have hsm := Module.Flat.isSMulRegular_of_isRegular (M := Γ(Y, V)) hreg
  apply hsm
  change a' • y = a' • 0
  rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have e : (h.appLE (B.basicOpen s) V hVs).hom a' = h.appLE S₁ V hVS a := by
    rw [ha']
    change (B.presheaf.map (homOfLE (B.basicOpen_le s)).op ≫
      h.appLE (B.basicOpen s) V hVs).hom a = _
    rw [Scheme.Hom.map_appLE]
  rw [e]
  exact hy

/-- A morphism of `𝒪_X`-modules surjective on sections over every open of a basis is an
epimorphism. -/
private lemma epi_of_surjective_app_on_basis {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (B : Set X.Opens) (hB : Opens.IsBasis B)
    (hφ : ∀ U ∈ B, Function.Surjective (φ.app U)) : Epi φ := by
  apply (SheafOfModules.toSheaf.{0} X.ringCatSheaf).epi_of_epi_map
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X.carrier)
    ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map φ)).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  exact ⟨V, hVU, hφ V hV _, hxV⟩

/-- `appLE` depends only on the morphism. -/
private lemma appLE_eq_of_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (hf : f₁ = f₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ f₁ ⁻¹ᵁ U) (e₂ : V ≤ f₂ ⁻¹ᵁ U) :
    f₁.appLE U V e₁ = f₂.appLE U V e₂ := by
  subst hf; rfl

/-- The parameter vanishes on the fibre. -/
private lemma fiberι_app_appLE_eq_zero {Y B : Scheme.{0}} (h : Y ⟶ B) (b : B) {S₁ : B.Opens}
    (hbS : b ∈ S₁) (a : Γ(B, S₁))
    (ha : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0)
    (V : Y.Opens) (hVS : V ≤ h ⁻¹ᵁ S₁) :
    (h.fiberι b).app V (h.appLE S₁ V hVS a) = 0 := by
  have hc : h.fiberι b ≫ h = h.fiberToSpecResidueField b ≫ B.fromSpecResidueField b :=
    pullback.condition
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq hc _ _ _ (by
      rw [← hc]; exact fun x hx => hVS hx), ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _
      (le_preimage_fromSpecResidueField b hbS) le_top, CommRingCat.comp_apply, ha, map_zero]

/-- Over the basic open of `s`, the parameter `a` is a nonzerodivisor on the sections of a flat
`B`-scheme over any open. -/
private lemma eq_zero_of_appLE_mul_eq_zero_of_le {Y B : Scheme.{0}} (h : Y ⟶ B) [Flat h]
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (a s : Γ(B, S₁))
    (has : ∀ r, r * a = 0 → s * r = 0) {V : Y.Opens} (hVS : V ≤ h ⁻¹ᵁ S₁)
    (hVs : V ≤ h ⁻¹ᵁ B.basicOpen s) (x : Γ(Y, V)) (hx : h.appLE S₁ V hVS a * x = 0) :
    x = 0 := by
  refine TopCat.Presheaf.section_ext Y.sheaf V x 0 fun y hy => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  have hWV : W ≤ V := hWV'
  have h0 : Y.presheaf.map (homOfLE hWV).op x = 0 := by
    apply eq_zero_of_appLE_mul_eq_zero h hS₁ a s has hW (hWV.trans hVS) (hWV.trans hVs)
    have := congrArg (Y.presheaf.map (homOfLE hWV).op) hx
    rw [map_mul, map_zero, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at this
    exact this
  change Y.presheaf.germ V y hy x = Y.presheaf.germ V y hy 0
  rw [map_zero, ← Y.presheaf.germ_res_apply (homOfLE hWV) y hyW, h0, map_zero]

/-- **Functions on the slice of a scheme with `H¹(𝒪) = 0`.** Let `h : Y ⟶ B` be flat with
`Y` over the basic open of `s`, and `H¹(Y, 𝒪_Y) = 0`. Then restriction `Γ(Y, 𝒪_Y) → Γ(Y_b, 𝒪)`
is surjective with kernel `(a)`: this is the long exact sequence of
`0 → 𝒪_Y →a 𝒪_Y → 𝒪_{Y_b} → 0`, exact on affine opens. -/
private lemma surjective_and_ker_fiberι_appTop {Y B : Scheme.{0}} (h : Y ⟶ B) [Flat h] (b : B)
    (hb : IsClosed ({b} : Set B)) {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (hbS : b ∈ S₁)
    (hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom)
    (a s : Γ(B, S₁))
    (ha : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0)
    (hsK : ∀ x, (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) x
      = 0 → s * x ∈ Ideal.span {a})
    (has : ∀ r, r * a = 0 → s * r = 0)
    (hYS : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ S₁) (hYs : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ B.basicOpen s)
    (hH1 : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf))) :
    Function.Surjective ((h.fiberι b).app ⊤) ∧
      ∀ x, (h.fiberι b).app ⊤ x = 0 ↔ x ∈ Ideal.span {h.appLE S₁ ⊤ hYS a} := by
  have hcl := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι h hb
  set j := h.fiberι b with hj
  set πY : Γ(Y, ⊤) := h.appLE S₁ ⊤ hYS a with hπY
  have hres : ∀ (V : Y.Opens) (i : op (⊤ : Y.Opens) ⟶ op V),
      Y.presheaf.map i πY = h.appLE S₁ V (le_top.trans hYS) a := by
    intro V i
    rw [hπY, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  haveI : ∀ U : (Opens Y)ᵒᵖ, IsMulCommutative (Y.ringCatSheaf.obj.obj U) :=
    fun U => inferInstanceAs (IsMulCommutative Γ(Y, U.unop))
  let M := SheafOfModules.unit Y.ringCatSheaf
  let G := (SheafOfModules.pushforward j.toRingCatSheafHom).obj
    (SheafOfModules.unit (h.fiber b).ringCatSheaf)
  let f1 : M ⟶ M :=
    (Stacks.SheafOfModules.terminalSectionToEnd Y.ringCatSheaf ⊤ isTerminalTop πY).asHom.app M
  let g1 : M ⟶ G := SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom
  have hf1 : ∀ (V : Y.Opens) (x : Γ(Y, V)),
      f1.val.app (op V) x = h.appLE S₁ V (le_top.trans hYS) a * x := by
    intro V x
    exact (Stacks.SheafOfModules.terminalSectionToEnd_apply Y.ringCatSheaf ⊤ isTerminalTop πY M
      (op V) x).trans (congrArg (· * x) (hres V _))
  have hg1 : ∀ (V : Y.Opens) (x : Γ(Y, V)), g1.val.app (op V) x = j.app V x := fun _ _ => rfl
  have hz0 : ∀ (V : (Opens Y)ᵒᵖ) (x : Γ(Y, V.unop)), g1.val.app V (f1.val.app V x) = 0 := by
    intro V x
    refine (congrArg (g1.val.app V) (hf1 V.unop x)).trans ((hg1 V.unop _).trans ?_)
    rw [map_mul, fiberι_app_appLE_eq_zero h b hbS a ha, zero_mul]
    rfl
  have hzero : f1 ≫ g1 = 0 := by
    ext V
    exact hz0 V 1
  have hinj : ∀ V : (Opens Y)ᵒᵖ, Function.Injective (f1.val.app V) := by
    intro V
    rintro (x₁ : Γ(Y, V.unop)) (x₂ : Γ(Y, V.unop)) hx
    have hx' : h.appLE S₁ V.unop (le_top.trans hYS) a * x₁ =
        h.appLE S₁ V.unop (le_top.trans hYS) a * x₂ :=
      (hf1 _ x₁).symm.trans (hx.trans (hf1 _ x₂))
    exact sub_eq_zero.1 (eq_zero_of_appLE_mul_eq_zero_of_le h hS₁ a s has (le_top.trans hYS)
      (le_top.trans hYs) (x₁ - x₂) (by rw [mul_sub, hx', sub_self]))
  haveI : Mono f1.val := PresheafOfModules.mono_of_injective (fun {V} => hinj V)
  haveI : Mono f1 :=
    (SheafOfModules.forget _).mono_of_mono_map (show Mono f1.val from inferInstance)
  haveI : Epi g1 := epi_of_surjective_app_on_basis g1 _ Y.isBasis_affineOpens
    (fun U hU => Scheme.Hom.app_surjective j U hU)
  have hex : (ShortComplex.mk f1 g1 hzero).Exact :=
      Stacks.SheafOfModules.ComplexGlue.exact_of_isAffineOpen _ fun A hA (z : Γ(Y, A)) hz => by
    have hz' : j.app A z = 0 := hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((fiberι_app_eq_zero_iff_mem_span h b hS₁ hbS
      hsurj a s ha hsK hA (le_top.trans hYS) (le_top.trans hYs) z).1 hz')
    exact ⟨c, (hf1 A c).trans (by rw [mul_comm]; exact hc)⟩
  have hS : (ShortComplex.mk f1 g1 hzero).ShortExact := ⟨hex⟩
  obtain ⟨hsur, hker⟩ := AlgebraicGeometry.sections_surjective_and_ker_eq_range_of_shortExact hS hH1
  refine ⟨hsur, fun x => ?_⟩
  have e0 := SetLike.ext_iff.1 hker x
  have e : j.app ⊤ x = 0 ↔ ∃ y : Γ(Y, ⊤), h.appLE S₁ ⊤ hYS a * y = x := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (LinearMap.mem_range (f := (Y.sectionsFunctor.map f1).hom)).1
        (e0.1 ((LinearMap.mem_ker (f := (Y.sectionsFunctor.map g1).hom)).2 hx))
      exact ⟨y, (hf1 ⊤ y).symm.trans hy⟩
    · rintro ⟨y, hy⟩
      exact (LinearMap.mem_ker (f := (Y.sectionsFunctor.map g1).hom)).1
        (e0.2 ((LinearMap.mem_range (f := (Y.sectionsFunctor.map f1).hom)).2
          ⟨y, (hf1 ⊤ y).trans hy⟩))
  rw [e, Ideal.mem_span_singleton']
  exact ⟨fun ⟨y, hy⟩ => ⟨y, (mul_comm _ _).trans hy⟩, fun ⟨y, hy⟩ => ⟨y, (mul_comm _ _).trans hy⟩⟩

/-- The global sections of a coproduct of schemes are the product of the global sections. -/
private lemma sigma_sections_bijective {ι : Type 0} (B : ι → Scheme.{0}) :
    Function.Bijective (fun (s : Γ(∐ B, ⊤)) (i : ι) =>
      (Sigma.ι B i).appTop.hom s) := by
  classical
  let T : Scheme.{0} := ∐ B
  let O (i : ι) : T.Opens := Sigma.ι B i ''ᵁ ⊤
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover B).iSup_opensRange
  let G : TopCat.Sheaf CommRingCat T.toTopCat := T.sheaf
  have hcompat (sf : ∀ i, Γ(T, O i)) :
      TopCat.Presheaf.IsCompatible G.1 O sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hd : O i ⊓ O j = ⊥ := by
        simpa only [O, Scheme.Hom.image_top_eq_opensRange] using
          (disjoint_iff.mp (disjoint_opensRange_sigmaι B i j hij))
      have : Subsingleton (G.obj.obj (Opposite.op (O i ⊓ O j))) := by
        rw [hd]
        exact CommRingCat.subsingleton_of_isTerminal T.sheaf.isTerminalOfEmpty
      exact Subsingleton.elim _ _
  have hres : Function.Bijective (fun (s : Γ(T, ⊤)) (i : ι) =>
      T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
    constructor
    · intro s t h
      obtain ⟨gl, _, huniq⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO])
        (fun i => T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) (hcompat _)
      exact (huniq s fun _ => rfl).trans (huniq t fun i => (congrFun h i).symm).symm
    · intro sf
      obtain ⟨gl, hgl, _⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO]) sf (hcompat sf)
      exact ⟨gl, funext hgl⟩
  have hcomp (i : ι) (s : Γ(T, ⊤)) :
      (Sigma.ι B i).appTop.hom s =
        ((Sigma.ι B i).appIso ⊤).hom
          (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
    let f : B i ⟶ T := Sigma.ι B i
    have hh : f.appTop ≫ (f.appIso ⊤).inv =
        T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op := by
      convert f.app_appIso_inv ⊤ using 1 <;> rfl
    change f.appTop.hom s = (f.appIso ⊤).hom
      (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s)
    calc
      f.appTop.hom s = (f.appIso ⊤).hom ((f.appIso ⊤).inv (f.appTop.hom s)) := by simp
      _ = (f.appIso ⊤).hom (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
        congr 1
        exact congrArg (fun q : Γ(T, ⊤) ⟶ Γ(T, O i) => q.hom s) hh
  constructor
  · intro s t heq
    apply hres.1
    funext i
    have hi := congrArg (fun x => ((Sigma.ι B i).appIso ⊤).inv x) (congrFun heq i)
    simpa only [hcomp, Iso.hom_inv_id_apply] using hi
  · intro sf
    obtain ⟨s, hs⟩ := hres.2 (fun i => ((Sigma.ι B i).appIso ⊤).inv (sf i))
    refine ⟨s, funext (fun i => ?_)⟩
    simp [hcomp, congrFun hs i]

/-- An integrally closed domain is a normal ring. -/
private lemma isNormalRing_of_isIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsNormalRing R := by
  rw [isNormalRing_iff]
  intro p hp
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
    p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

/-- **Global functions on a quasi-compact locally Noetherian normal scheme form a normal ring**:
the scheme is a finite coproduct of normal integral schemes, whose rings of global functions are
integrally closed domains. -/
private lemma isNormalRing_globalSections (F : Scheme.{0}) [IsNormal F] [CompactSpace F]
    [IsLocallyNoetherian F] : IsNormalRing Γ(F, ⊤) := by
  have hfin : ∀ U : F.Opens, IsCompact (U : Set F) → (irreducibleComponents U).Finite := by
    intro U hU
    haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU
    haveI : IsNoetherian U.toScheme := {}
    exact NoetherianSpace.finite_irreducibleComponents
  obtain ⟨ι, Y, hN, hI, ⟨e⟩⟩ := (isNormal_iff_exists_iso_coproduct hfin).1 inferInstance
  haveI : Finite ι := by
    haveI : CompactSpace (∐ Y : Scheme.{0}) := e.hom.homeomorph.compactSpace
    haveI : CompactSpace (Σ i, Y i) := (sigmaMk Y).symm.compactSpace
    letI : TopologicalSpace ι := ⊥
    haveI : DiscreteTopology ι := ⟨rfl⟩
    have hc := (isCompact_univ (X := Σ i, Y i)).image
      (continuous_sigma (f := fun x : Σ i, Y i => x.1) fun i => continuous_const)
    have hs : Sigma.fst '' (Set.univ : Set (Σ i, Y i)) = Set.univ := by
      ext i
      simp only [Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
      haveI := hI i
      obtain ⟨y⟩ := (inferInstance : Nonempty (Y i))
      exact ⟨⟨i, y⟩, rfl⟩
    rw [hs] at hc
    exact Set.finite_univ_iff.1 (hc.finite_of_discrete)
  let eΓ : Γ(F, ⊤) ≃+* (∀ i, Γ(Y i, ⊤)) :=
    (Scheme.Γ.mapIso e.symm.op).commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective (RingHom.pi fun i => (Sigma.ι Y i).appTop.hom)
        (sigma_sections_bijective Y))
  refine IsNormalRing.congr eΓ.symm (isNormalRing_pi fun i => ?_)
  haveI := hI i
  haveI := hN i
  haveI := normal_globalSections (Y i)
  exact isNormalRing_of_isIntegrallyClosed _

/-- A ring surjection whose kernel is principal identifies the target with the quotient. -/
private noncomputable def ringEquivQuotientOfSurjective {A C : Type*} [CommRing A] [CommRing C]
    (ρ : A →+* C) (hρ : Function.Surjective ρ) (π : A) (hker : ∀ x, ρ x = 0 ↔ x ∈ Ideal.span {π}) :
    C ≃+* A ⧸ Ideal.span {π} :=
  (RingHom.quotientKerEquivOfSurjective hρ).symm.trans
    (Ideal.quotEquivOfEq (by ext x; exact (RingHom.mem_ker).trans (hker x)))

/-- **Normality of the slice of a smooth `B`-scheme**: for `h : Y ⟶ B` smooth with `Y`
quasi-compact, the functions on the fibre `Y_b` form a normal ring, `Y_b` being smooth over
`κ(b)`. -/
private lemma isNormalRing_fiber_top {Y B : Scheme.{0}} (h : Y ⟶ B) [Smooth h] [CompactSpace Y]
    (b : B) (hb : IsClosed ({b} : Set B)) : IsNormalRing Γ(h.fiber b, ⊤) := by
  have hsm : Smooth (h.fiberToSpecResidueField b) := inferInstanceAs (Smooth (pullback.snd _ _))
  haveI : IsNormal (h.fiber b) := isNormal_of_isRegular _
    (@isRegular_of_smooth_over_field (B.residueField b) _ _ (h.fiberToSpecResidueField b) hsm)
  haveI : IsLocallyNoetherian (h.fiber b) := isLocallyNoetherian_fiber_of_locallyOfFiniteType h b
  haveI := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι h hb
  haveI : CompactSpace (h.fiber b) := QuasiCompact.compactSpace_of_compactSpace (h.fiberι b)
  exact isNormalRing_globalSections (h.fiber b)

/-- **Comparing two slices.** Let `U` be an affine open of `X` over the basic open of `s`, and
let `h : Y ⟶ B` be smooth with `Y` quasi-compact over the basic open of `s`, with
`H¹(Y, 𝒪_Y) = 0`. A ring isomorphism `Γ(U, 𝒪_X) ≅ Γ(Y, 𝒪_Y)` carrying the parameter to the
parameter identifies the functions on `U ∩ X_b` with those on `Y_b`, so they form a normal
ring. -/
private lemma isNormalRing_fiber_of_ringEquiv {X Y B : Scheme.{0}} (t : X ⟶ B) (h : Y ⟶ B)
    [Smooth h] [CompactSpace Y] (b : B) (hb : IsClosed ({b} : Set B))
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (hbS : b ∈ S₁)
    (hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom)
    (a s : Γ(B, S₁))
    (ha : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0)
    (hsK : ∀ x, (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) x
      = 0 → s * x ∈ Ideal.span {a})
    (has : ∀ r, r * a = 0 → s * r = 0)
    {U : X.Opens} (hU : IsAffineOpen U) (hUS : U ≤ t ⁻¹ᵁ S₁) (hUs : U ≤ t ⁻¹ᵁ B.basicOpen s)
    (hYS : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ S₁) (hYs : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ B.basicOpen s)
    (hH1 : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)))
    (eφ : Γ(X, U) ≃+* Γ(Y, ⊤)) (hφπ : eφ (t.appLE S₁ U hUS a) = h.appLE S₁ ⊤ hYS a) :
    IsNormalRing Γ(t.fiber b, t.fiberι b ⁻¹ᵁ U) := by
  haveI := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι t hb
  have hX := fiberι_app_eq_zero_iff_mem_span t b hS₁ hbS hsurj a s ha hsK hU hUS hUs
  have hXs : Function.Surjective ((t.fiberι b).app U) := (t.fiberι b).app_surjective U hU
  obtain ⟨hYsurj, hYker⟩ :=
    surjective_and_ker_fiberι_appTop h b hb hS₁ hbS hsurj a s ha hsK has hYS hYs hH1
  have hspan : Ideal.map eφ (Ideal.span {t.appLE S₁ U hUS a}) =
      Ideal.span {h.appLE S₁ ⊤ hYS a} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun y => Ideal.span {y}) hφπ
  let e : Γ(t.fiber b, t.fiberι b ⁻¹ᵁ U) ≃+* Γ(h.fiber b, h.fiberι b ⁻¹ᵁ ⊤) :=
    (ringEquivQuotientOfSurjective _ hXs _ hX).trans
      ((Ideal.quotientEquiv _ _ eφ hspan.symm).trans
        (ringEquivQuotientOfSurjective _ hYsurj _ hYker).symm)
  exact IsNormalRing.congr e.symm (isNormalRing_fiber_top h b hb)

/-- **Normality of the slice over an affine open.** For an affine open `U` of `X` over the basic
open of `s`, the functions on `U ∩ X_b` are those on `f⁻¹U ∩ Z_b`, a normal ring. -/
private lemma isNormalRing_fiber_sections {X Z B : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    [QuasiSeparated f] (hf₀ : ∀ U : X.Opens, IsIso (f.app U))
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Z.ringCatSheaf)))
    (t : X ⟶ B) [Smooth (f ≫ t)] (b : B) (hb : IsClosed ({b} : Set B))
    {S₁ : B.Opens} (hS₁ : IsAffineOpen S₁) (hbS : b ∈ S₁)
    (hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom)
    (a s : Γ(B, S₁))
    (ha : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) a = 0)
    (hsK : ∀ x, (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) x
      = 0 → s * x ∈ Ideal.span {a})
    (has : ∀ r, r * a = 0 → s * r = 0)
    {U : X.Opens} (hU : IsAffineOpen U) (hUs : U ≤ t ⁻¹ᵁ B.basicOpen s) :
    IsNormalRing Γ(t.fiber b, t.fiberι b ⁻¹ᵁ U) := by
  have hUS : U ≤ t ⁻¹ᵁ S₁ := hUs.trans (fun x hx => B.basicOpen_le s hx)
  have hYS : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ ((f ⁻¹ᵁ U).ι ≫ f ≫ t) ⁻¹ᵁ S₁ :=
    fun x _ => hUS x.2
  have hYs : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ ((f ⁻¹ᵁ U).ι ≫ f ≫ t) ⁻¹ᵁ B.basicOpen s :=
    fun x _ => hUs x.2
  have hH1 : IsZero (((Scheme.sectionsFunctor (f ⁻¹ᵁ U).toScheme).rightDerived 1).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)) :=
    isZero_rightDerived_one_sections_preimage f hR1 U hU
  have hWle : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ ((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U := fun x _ => x.2
  have hφ : Function.Bijective (((f ⁻¹ᵁ U).ι ≫ f).appLE U ⊤ hWle) := by
    have h1 : (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := Scheme.Opens.ι_preimage_self _
    have e1 : ((f ⁻¹ᵁ U).ι ≫ f).appLE U ⊤ hWle =
        f.app U ≫ (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ U) ⊤ h1.ge := by
      rw [Scheme.Hom.app_eq_appLE f, Scheme.Hom.appLE_comp_appLE]
    have e2 : (f ⁻¹ᵁ U).ι.appLE (f ⁻¹ᵁ U) ⊤ h1.ge = (f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ U) ≫
        (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom h1.symm).op := rfl
    haveI : IsIso ((f ⁻¹ᵁ U).ι.app (f ⁻¹ᵁ U)) := Scheme.Hom.isIso_app _ _ (by simp)
    haveI := hf₀ U
    rw [e1, e2]
    exact ConcreteCategory.bijective_of_isIso _
  have hφπ : (((f ⁻¹ᵁ U).ι ≫ f).appLE U ⊤ hWle) (t.appLE S₁ U hUS a) =
      ((f ⁻¹ᵁ U).ι ≫ f ≫ t).appLE S₁ ⊤ hYS a := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rfl
  haveI : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.1
      (QuasiCompact.isCompact_preimage (f := f) (U : Set X) U.isOpen hU.isCompact)
  exact isNormalRing_fiber_of_ringEquiv t ((f ⁻¹ᵁ U).ι ≫ f ≫ t) b hb hS₁ hbS hsurj a s ha hsK
    has hU hUS hUs hYS hYs hH1 (RingEquiv.ofBijective _ hφ) hφπ

/-- **Normality of the slice.** If `f_* 𝒪_Z = 𝒪_X`, `R¹f_* 𝒪_Z = 0` and `Z ⟶ B` is smooth
over a smooth curve, the fibre `X_b` over a closed point is normal.

Near `b` there is a parameter `a` on an affine open `S₁ ∋ b` and `s` with `b ∈ D(s)` such that
`a` generates the ideal of `b` and is a nonzerodivisor after inverting `s`
(`exists_local_parameter`). For an affine open `U ⊆ t⁻¹ D(s)` the sequence
`0 → 𝒪 →a 𝒪 → 𝒪_{(f⁻¹U)_b} → 0` on `f⁻¹ U` is exact and
`H¹(f⁻¹U, 𝒪_Z) = Γ(U, R¹f_*𝒪_Z) = 0`, so `Γ(f⁻¹U)/(a) ≅ Γ((f⁻¹U)_b)`; with
`Γ(U) ≅ Γ(f⁻¹U)` and `Γ(U)/(a) ≅ Γ(U ∩ X_b)` this identifies `Γ(U ∩ X_b)` with the functions
on the smooth quasi-compact `κ(b)`-scheme `(f⁻¹U)_b`, a normal ring
(`isNormalRing_fiber_sections`). These affine opens cover `X_b`. -/
private lemma isNormal_fiber {X Z B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
    (f : Z ⟶ X) [QuasiCompact f] [QuasiSeparated f] (hf₀ : ∀ U : X.Opens, IsIso (f.app U))
    (hR1 : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Z.ringCatSheaf)))
    [SmoothOfRelativeDimension 1 sB] (t : X ⟶ B) [Smooth (f ≫ t)]
    (b : B) (hb : IsClosed {b}) : IsNormal (t.fiber b) := by
  obtain ⟨S₁, hS₁, hbS, a, s, ha, hbs, hsK, has⟩ := exists_local_parameter sB b hb
  have hsurj : Function.Surjective ((B.fromSpecResidueField b).appLE S₁ ⊤
      (le_preimage_fromSpecResidueField b hbS)).hom := by
    haveI := isClosed_singleton_iff_isClosedImmersion.mp hb
    have h1 : B.fromSpecResidueField b ⁻¹ᵁ S₁ = ⊤ :=
      top_unique (le_preimage_fromSpecResidueField b hbS)
    have e : (B.fromSpecResidueField b).appLE S₁ ⊤ (le_preimage_fromSpecResidueField b hbS) =
        (B.fromSpecResidueField b).app S₁ ≫
          (Spec (B.residueField b)).presheaf.map (eqToHom h1.symm).op := rfl
    rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      ((B.fromSpecResidueField b).app_surjective S₁ hS₁)
  haveI := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι t hb
  let I := {U : X.affineOpens // (U : X.Opens) ≤ t ⁻¹ᵁ B.basicOpen s}
  let V : I → (t.fiber b).affineOpens :=
    fun i => ⟨t.fiberι b ⁻¹ᵁ i.1.1, i.1.2.preimage (t.fiberι b)⟩
  have htfae := (isNormal_tfae (t.fiber b)).out 3 1
  refine htfae.1 ⟨I, V, ?_, fun i => ?_⟩
  · refine IsOpenCover.mk (eq_top_iff.2 fun z _ => ?_)
    have hz : t.fiberι b z ∈ t ⁻¹ᵁ B.basicOpen s := by
      change t (t.fiberι b z) ∈ B.basicOpen s
      rw [Scheme.Hom.apply_fiberι]
      exact hbs
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz (t ⁻¹ᵁ B.basicOpen s).isOpen
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hUle⟩, hzU⟩
  · exact isNormalRing_fiber_sections f hf₀ hR1 t b hb hS₁ hbS hsurj a s ha hsK has i.1.2 i.2

end NormalSlice

end MMP.Fourfold.Internal.ConductorNormalSlice

namespace MMP.Fourfold

open MMP.Fourfold.Internal.ConductorNormalSlice in
/-- **Normal threefold slices.** Let `f : Z ⟶ X` be a projective birational morphism with
`𝒪_X ≅ Rf_* 𝒪_Z`, `X` a normal complex fourfold, which is an isomorphism off a closed smooth curve
`ι : T ⟶ X`. Let `t : X ⟶ B` be a morphism to a smooth complex curve with `T ⟶ B` finite étale
and `Z ⟶ B` smooth, such that `(f⁻¹ T)_red = ∑_{P ∈ s} P` is an snc divisor whose strata are
smooth over `B`. Then for every closed point `b ∈ B` the fibre `X_b` is normal of pure dimension
three, `T_b` is finite, and `f_b : Z_b ⟶ X_b` is a projective resolution which is an isomorphism
over `X_b ∖ T_b`; in particular `Sing X_b ⊆ T_b`. -/
@[mmp "lem_mmp_conductor_normal_slice_from_unit"]
public theorem isNormal_fiber_of_isZero_rightDerived_pushforward
    {X Z T B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)}
    [IsVariety ℂ sX] [IsNormal X] (hdim : topologicalKrullDim X = 4)
    (f : Z ⟶ X) (hfp : IsProjectiveMorphism f) (hfb : MMP.Mori.IsBirationalMorphism f)
    (hf₀ : ∀ U : X.Opens, IsIso (f.app U))
    (hfi : ∀ i > 0, IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (SheafOfModules.unit Z.ringCatSheaf)))
    (ι : T ⟶ X) [IsClosedImmersion ι] [SmoothOfRelativeDimension 1 (ι ≫ sX)]
    (hfT : ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → IsIso (f ∣_ U))
    [SmoothOfRelativeDimension 1 sB] (t : X ⟶ B) (ht : t ≫ sB = sX)
    [IsFinite (ι ≫ t)] [Etale (ι ≫ t)] [Smooth (f ≫ t)]
    (s : Finset (MMP.Mori.PrimeDivisor Z))
    (hsT : (⋃ P ∈ s, (P.support : Set Z)) = f ⁻¹' Set.range ι)
    (hsnc : MMP.Mori.DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ P ∈ s, Finsupp.single P (1 : ℤ)))
    (hstrata : ∀ J ⊆ s, J.Nonempty → Smooth ((⨆ P ∈ J, P.idealSheaf).subschemeι ≫ f ≫ t))
    (b : B) (hb : IsClosed {b}) :
    let fb : (f ≫ t).fiber b ⟶ t.fiber b :=
      pullback.map (f ≫ t) (B.fromSpecResidueField b) t (B.fromSpecResidueField b) f (𝟙 _) (𝟙 _)
        (by simp) (by simp)
    IsNormal (t.fiber b) ∧
      (∀ U : (t.fiber b).Opens, (U : Set (t.fiber b)).Nonempty → topologicalKrullDim U = 3) ∧
      (t.fiberι b ⁻¹' Set.range ι).Finite ∧
      IsProjectiveMorphism fb ∧ MMP.Mori.IsSmoothResolution (t.fiberToSpecResidueField b) fb ∧
      (∀ V : (t.fiber b).Opens, (V : Set (t.fiber b)) = (t.fiberι b ⁻¹' Set.range ι)ᶜ →
        IsIso (fb ∣_ V)) ∧
      (MMP.Mori.singularLocus (t.fiberToSpecResidueField b) : Set (t.fiber b)) ⊆
        t.fiberι b ⁻¹' Set.range ι := by
  intro fb
  have hS : IsClosed (t.fiberι b ⁻¹' Set.range ι) :=
    ι.isClosedEmbedding.isClosed_range.preimage (t.fiberι b).continuous
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hfp
  -- the instance search for `QuasiSeparated f` times out in this import environment, so the
  -- instance is assembled from the closed diagonal by hand
  have : IsClosedImmersion (pullback.diagonal f) := IsSeparated.isClosedImmersion_diagonal
  haveI : QuasiSeparated f := ⟨instQuasiCompactOfIsAffineHom _⟩
  have h_normal : IsNormal (t.fiber b) := isNormal_fiber (sB := sB) f hf₀ (hfi 1 one_pos) t b hb
  have h_pureDim : ∀ U : (t.fiber b).Opens, (U : Set (t.fiber b)).Nonempty →
      topologicalKrullDim U = 3 := pureDim_fiber (sX := sX) (sB := sB) hdim f hf₀ t b hb
  haveI : Smooth ((f ≫ t).fiberToSpecResidueField b) :=
    inferInstanceAs (Smooth (pullback.snd _ _))
  haveI hZb : Smooth (fiberMap f t b ≫ t.fiberToSpecResidueField b) := by
    rwa [fiberMap_comp_fiberToSpecResidueField]
  have h_isoOff : ∀ V : (t.fiber b).Opens,
      (V : Set (t.fiber b)) = (t.fiberι b ⁻¹' Set.range ι)ᶜ → IsIso (fb ∣_ V) := by
    intro V hV
    let U : X.Opens := ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    haveI := hfT U rfl
    have hVU : V = t.fiberι b ⁻¹ᵁ U := TopologicalSpace.Opens.ext hV
    subst hVU
    exact isIso_morphismRestrict_of_isPullback (isPullback_fiberMap f t b) U
  have h_birational : MMP.Mori.IsBirationalMorphism fb := by
    let V : (t.fiber b).Opens := ⟨(t.fiberι b ⁻¹' Set.range ι)ᶜ, hS.isOpen_compl⟩
    haveI := h_isoOff V rfl
    have hVd : Dense (V : Set (t.fiber b)) := dense_compl_fiber_range ι t b h_pureDim
    have : LocallyOfFiniteType sX := inferInstance
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
    have hP : ∀ P ∈ s, Smooth (P.idealSheaf.subschemeι ≫ f ≫ t) := by
      intro P hPs
      have h := hstrata {P} (Finset.singleton_subset_iff.mpr hPs) (Finset.singleton_nonempty P)
      have heq : (⨆ P' ∈ ({P} : Finset (MMP.Mori.PrimeDivisor Z)), P'.idealSheaf) =
          P.idealSheaf := by simp
      rwa [heq] at h
    have hUd : Dense ((fb ⁻¹ᵁ V : ((f ≫ t).fiber b).Opens) : Set ((f ≫ t).fiber b)) := by
      rw [dense_iff_inter_open]
      intro O hO hOne
      by_contra hne
      refine not_image_subset_iUnion_support (f ≫ t) b hb
        (not_isOpen_singleton_of_smoothOfRelativeDimension_one sB b)
        (exists_maximalIdeal_stalk_eq_span_of_map_eq sB (f ≫ t) b hb) s hP ⟨O, hO⟩ hOne ?_
      rintro _ ⟨z, hz, rfl⟩
      have hzV : z ∉ (fb ⁻¹ᵁ V : Set ((f ≫ t).fiber b)) := fun h => hne ⟨z, hz, h⟩
      have h1 : t.fiberι b (fb z) ∈ Set.range ι := by
        by_contra h'
        exact hzV h'
      have h2 : f ((f ≫ t).fiberι b z) = t.fiberι b (fb z) := by
        change (pullback.fst (f ≫ t) (B.fromSpecResidueField b) ≫ f) z =
          (fiberMap f t b ≫ pullback.fst t (B.fromSpecResidueField b)) z
        rw [(isPullback_fiberMap f t b).w]
      rw [hsT]
      change f ((f ≫ t).fiberι b z) ∈ Set.range ι
      rw [h2]; exact h1
    exact isBirationalMorphism_of_isIso_morphismRestrict fb V hVd hUd
  have h_resolution : MMP.Mori.IsSmoothResolution (t.fiberToSpecResidueField b) fb :=
    ⟨isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_fiberMap f hfp t b), h_birational,
      @MMP.Resolution.isSmoothScheme_of_smooth _ _ _ hZb⟩
  exact ⟨h_normal, h_pureDim, finite_fiberι_preimage_range ι t b,
    isProjectiveMorphism_fiberMap f hfp t b, h_resolution, h_isoOff,
    singularLocus_subset_of_isIso_morphismRestrict (fiberMap f t b) _ _ hS h_isoOff⟩

end MMP.Fourfold

end

/-!
## The relative `Proj` of a finitely generated divisorial algebra is a normal variety

Let `Y` be a normal variety over a field `k`, `B` a Weil divisor on `Y` and `d > 0` an integer
such that the divisorial algebra `⨁_{m ≥ 0} 𝒪_Y(mdB)` is a sheaf of finitely generated
`𝒪_Y`-algebras. Then `Proj_Y ⨁_{m ≥ 0} 𝒪_Y(mdB)` is a normal variety over `k`.

Over an affine open `U = Spec A` of `Y`, with `K` the function field, the section ring is
`R = K[t] ∩ ⋂_P V_P` inside `K(t)`, where `P` runs over the prime divisors of `U` and `V_P` is the
valuation ring of the Gauss extension `w_P(∑ aₘ tᵐ) = min_m (ord_P aₘ + md · coeff_P B)`; it is
therefore integrally closed, and so are the degree-zero parts `(R_f)₀` of its homogeneous
localizations, which are the coordinate rings of the charts of `Proj R`. Finite generation makes
the relative `Proj` of finite type over `Y`, and its generic point is that of `Proj K[t] = Spec K`.

### Main results

* `MMP.Fourfold.DivisorialSectionAlgebra.isNormalVariety_model`: the statement above.

### Implementation notes

The graded algebra `⨁_{m ≥ 0} 𝒪_Y(mdB)` is given as a
`MMP.Fourfold.DivisorialSectionAlgebra` of the divisor `d • B` along the identity `𝟙 Y`: a
quasi-coherent, nonnegatively graded `𝒪_Y`-algebra with an identification of its degree-`m`
sections over every open `U` with `𝒪_Y(mdB)(U) ⊆ 𝒦_Y(U)`, compatible with restriction, the module
structure, products and the unit. Its relative `Proj` is
`MMP.Fourfold.DivisorialSectionAlgebra.model`, over `Y` by
`MMP.Fourfold.DivisorialSectionAlgebra.toBase`. That it is a sheaf of finitely
generated `𝒪_Y`-algebras is asked affine-locally: over every affine open `U` of `Y` the graded
ring of sections `Stacks.RelativeProj.Situation.sectionRing` is a finite type `Γ(Y, U)`-algebra
through `Stacks.RelativeProj.Situation.sectionRingBaseMap` (condition (2) of Stacks 084I).
The model is a variety over `k` through the composite `Proj_Y ⟶ Y ⟶ Spec k`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 6.2
-/

section

universe u

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.Internal.DivisorialProjNormal

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}

/-- The chart `Proj R_W` over an affine open `W` is the part of the relative `Proj` lying over
`W`. -/
private theorem toBase_isPullback (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.affineOpens) :
    IsPullback (A.situation.relativeProjChart W)
      (A.situation.projInclusionToOpen W.1 W.2) A.toBase W.1.ι :=
  A.situation.relativeProjChart_isPullback W

/-- A property of morphisms local on the target holds for the structure morphism of the relative
`Proj` as soon as it holds for every chart `Proj R_W ⟶ W` over an affine open `W`. -/
private theorem toBase_of_charts (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (A : DivisorialSectionAlgebra (𝟙 Y) D)
    (H : ∀ W : Y.affineOpens, P (A.situation.projInclusionToOpen W.1 W.2)) : P A.toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) (fun W : Y.affineOpens => W.1)
    (iSup_affineOpens_eq_top Y)]
  intro W
  have e := IsPullback.isoIsPullback_hom_fst _ _ (toBase_isPullback A W).flip
    (isPullback_morphismRestrict A.toBase W.1)
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mp (e ▸ H W)

open Stacks.RelativeProj in
private theorem baseMap_eq_zeroMap (s : Situation.{u}) (U : s.base.Opens) :
    (algebraMap (s.sectionRingGrading U 0) (s.sectionRing U)).comp
      (s.sectionRingZeroMap U).hom = s.sectionRingBaseMap U := by
  refine RingHom.ext fun r => ?_
  exact DirectSum.decompose_of_mem_same _ (s.sectionRingBaseMap_mem_zero U r)

open Stacks.RelativeProj in
/-- The chart `Proj R_U ⟶ U` over an affine open is separated, and it is of finite type
when `R_U` is a finitely generated `Γ(U)`-algebra. -/
private theorem chart_props (s : Situation.{u}) (U : s.base.Opens) (hU : IsAffineOpen U)
    (hFT : (s.sectionRingBaseMap U).FiniteType) :
    IsSeparated (s.projInclusionToOpen U hU) ∧ LocallyOfFiniteType (s.projInclusionToOpen U hU) ∧
      QuasiCompact (s.projInclusionToOpen U hU) := by
  have h0 : (algebraMap (s.sectionRingGrading U 0) (s.sectionRing U)).FiniteType := by
    rw [← baseMap_eq_zeroMap] at hFT
    exact RingHom.FiniteType.of_comp_finiteType hFT
  have hz : (s.sectionRingZeroMap U).hom.FiniteType := by
    have : (s.sectionRingZeroMap U).hom =
        (GradedRing.projZeroRingHom' (s.sectionRingGrading U)).comp (s.sectionRingBaseMap U) :=
      rfl
    rw [this]
    exact hFT.comp_surjective (GradedRing.projZeroRingHom'_surjective _)
  have : Algebra.FiniteType (s.sectionRingGrading U 0) (s.sectionRing U) := h0
  have : LocallyOfFiniteType (Spec.map (s.sectionRingZeroMap U)) := by
    rwa [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  unfold Situation.projInclusionToOpen
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A scheme is normal when it is covered by the images of open immersions from normal schemes. -/
private theorem isNormal_of_isOpenImmersion {X : Scheme.{u}} {ι : Type*} (V : ι → Scheme.{u})
    (g : ∀ i, V i ⟶ X) (hi : ∀ i, IsOpenImmersion (g i)) (hV : ∀ i, IsNormal (V i))
    (hg : ∀ x : X, ∃ i y, g i y = x) : IsNormal X := by
  have key : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨i, y, rfl⟩ := hg x
    have := hV i
    have := hi i
    let e := (asIso ((g i).stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

open Stacks.RelativeProj in
/-- The section ring over an open is generated over its degree-zero part by the homogeneous
elements of positive degree. -/
private theorem adjoin_positive_eq_top (s : Situation.{u}) (U : s.base.Opens) :
    Algebra.adjoin (s.sectionRingGrading U 0)
      (Set.range fun i : Σ n : {n : ℕ // 0 < n}, s.sectionPieces U n =>
        DirectSum.of (s.sectionPieces U) i.1.1 i.2) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | of n a =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Subalgebra.algebraMap_mem _ (⟨_, a, rfl⟩ : s.sectionRingGrading U 0)
    · exact Algebra.subset_adjoin ⟨⟨⟨n, hn⟩, a⟩, rfl⟩
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy

/-- The degree-zero part `(R_f)₀` of the homogeneous localization of a graded domain at a nonzero
homogeneous element is a domain. -/
private theorem isDomain_away {σ R : Type*} [CommRing R] [IsDomain R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : R} (hf : f ≠ 0) :
    IsDomain (HomogeneousLocalization.Away 𝒜 f) := by
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  exact Function.Injective.isDomain (algebraMap (HomogeneousLocalization.Away 𝒜 f)
    (Localization.Away f)) (HomogeneousLocalization.val_injective _)

/-- In a graded domain, if `r * h` is homogeneous of degree `m + e` for a nonzero `h` of degree
`e`, then `r` is homogeneous of degree `m`. -/
private theorem mem_of_mul_mem {σ R : Type*} [CommRing R] [IsDomain R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜] {r h : R} {m e : ℕ}
    (hh : h ∈ 𝒜 e) (hh0 : h ≠ 0) (hrh : r * h ∈ 𝒜 (m + e)) : r ∈ 𝒜 m := by
  classical
  have hz : ∀ i, i ≠ m → (DirectSum.decompose 𝒜 r i : R) = 0 := by
    intro i hi
    have h1 := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := i) (a := r) hh
    rw [DirectSum.decompose_of_mem_ne 𝒜 hrh (by omega)] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hh0
  have : DirectSum.decompose 𝒜 r =
      DirectSum.of (fun i => 𝒜 i) m (DirectSum.decompose 𝒜 r m) := by
    ext i
    by_cases hi : i = m
    · subst hi; simp
    · rw [hz i hi, DirectSum.of_eq_of_ne m i _ (by omega)]; rfl
  have h2 := congrArg (DirectSum.decompose 𝒜).symm this
  rw [Equiv.symm_apply_apply, DirectSum.decompose_symm_of] at h2
  rw [h2]; exact SetLike.coe_mem _

/-- An element `y` of `R_f` with `y * b ∈ (R_f)₀` for a nonzero `b ∈ (R_f)₀` lies in `(R_f)₀`. -/
private theorem mem_range_of_mul {σ R : Type*} [CommRing R] [IsDomain R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f : R} {n : ℕ} (hf : f ∈ 𝒜 n) (hf0 : f ≠ 0) (y : Localization.Away f)
    (a b : HomogeneousLocalization.Away 𝒜 f) (hb : b ≠ 0)
    (hy : y * b.val = a.val) : ∃ z : HomogeneousLocalization.Away 𝒜 f, z.val = y := by
  obtain ⟨⟨r, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) y
  rw [HomogeneousLocalization.eq_num_div_den b, HomogeneousLocalization.eq_num_div_den a,
    ← Localization.mk_eq_mk', Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists] at hy
  obtain ⟨⟨c, hc⟩, hc'⟩ := hy
  have hc0 : c ≠ 0 := by
    obtain ⟨j, rfl⟩ := hc; exact pow_ne_zero _ hf0
  have hbnum : b.num ≠ 0 := by
    intro h0; apply hb; apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.eq_num_div_den, h0, Localization.mk_zero,
      HomogeneousLocalization.val_zero]
  have hden : ∀ x : HomogeneousLocalization.Away 𝒜 f, x.den ≠ 0 := fun x => by
    obtain ⟨j, hj⟩ := x.den_mem; rw [← hj]; exact pow_ne_zero _ hf0
  simp only [Submonoid.coe_mul] at hc'
  have key : r * (b.num * a.den) = a.num * (f ^ k * b.den) := by
    apply mul_left_cancel₀ hc0; linear_combination hc'
  have hr : r ∈ 𝒜 (n * k) := by
    refine mem_of_mul_mem 𝒜 (e := b.deg + a.deg)
      (SetLike.mul_mem_graded b.num_mem_deg a.den_mem_deg)
      (mul_ne_zero hbnum (hden a)) ?_
    rw [key]
    have := SetLike.mul_mem_graded a.num_mem_deg
      (SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) b.den_mem_deg)
    convert this using 2; ring
  refine ⟨HomogeneousLocalization.mk ⟨n * k, ⟨r, hr⟩, ⟨f ^ k, by
    rw [mul_comm]; exact SetLike.pow_mem_graded k hf⟩, ⟨k, rfl⟩⟩, ?_⟩
  rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']

/-- The degree-zero part `(R_f)₀` of the homogeneous localization of an integrally closed graded
domain at a nonzero homogeneous element of positive degree is integrally closed. -/
private theorem isIntegrallyClosed_away {σ R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [SetLike σ R] [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f : R} {n : ℕ} (hf : f ∈ 𝒜 n) (hn : 0 < n) (hf0 : f ≠ 0) :
    have := isDomain_away 𝒜 hf0
    IsIntegrallyClosed (HomogeneousLocalization.Away 𝒜 f) := by
  intro _
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization _ _ hle
  let K := FractionRing (Localization.Away f)
  let ι := algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)
  have hg : Function.Injective ((algebraMap (Localization.Away f) K).comp ι) :=
    (IsFractionRing.injective (Localization.Away f) K).comp
      (HomogeneousLocalization.val_injective _)
  have hg' : Function.Injective (algebraMap (HomogeneousLocalization.Away 𝒜 f) K) := by
    rw [IsScalarTower.algebraMap_eq (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) K]
    exact hg
  let φ := IsFractionRing.liftAlgHom (K := FractionRing (HomogeneousLocalization.Away 𝒜 f))
    (g := Algebra.ofId (HomogeneousLocalization.Away 𝒜 f) K) hg'
  rw [isIntegrallyClosed_iff (FractionRing (HomogeneousLocalization.Away 𝒜 f))]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := HomogeneousLocalization.Away 𝒜 f) x
  have hS : IsIntegral (Localization.Away f) (φ (algebraMap _ _ a / algebraMap _ _ b)) :=
    (hx.map φ).tower_top
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).1 inferInstance hS
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (Localization.Away f) K b.val ≠ 0 :=
    fun h => hb0 (hg (by simpa [ι] using h))
  have hyb : y * b.val = a.val := by
    apply IsFractionRing.injective (Localization.Away f) K
    rw [map_mul, hy, map_div₀, φ.commutes, φ.commutes]
    exact div_mul_cancel₀ _ hbK
  obtain ⟨z, rfl⟩ := mem_range_of_mul 𝒜 hf hf0 y a b hb0 hyb
  refine ⟨z, φ.toRingHom.injective ?_⟩
  change φ _ = φ _
  rw [φ.commutes, ← hy]
  rfl

section SectionRing

open Opposite Polynomial

private theorem sectionEquiv_heq (A : DivisorialSectionAlgebra (𝟙 Y) D) {i j : ℤ} (h : i = j)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (U : Y.Opens) (a : (A.algebra.piece i).val.obj (op U))
    (b : (A.algebra.piece j).val.obj (op U)) (hab : HEq a b) :
    ((A.sectionEquiv i hi U a : _) : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ U))) =
      A.sectionEquiv j hj U b := by
  subst h; cases hab; rfl

/-- The degree-`n` piece of the section ring, as rational functions. -/
private noncomputable def pieceHom (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens) (n : ℕ) :
    A.situation.sectionPieces W n →+ (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)) :=
  (((n : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W)).subtype.toAddMonoidHom.comp
    (A.sectionEquiv n (Int.natCast_nonneg n) W).toAddMonoidHom

private theorem pieceHom_apply (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens) (n : ℕ)
    (a : A.situation.sectionPieces W n) :
    pieceHom A W n a = (A.sectionEquiv n (Int.natCast_nonneg n) W a : _) := rfl

/-- The section ring embeds in the polynomial ring over the rational functions. -/
private noncomputable def polyHom (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens) :
    A.situation.sectionRing W →+*
      ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] :=
  DirectSum.toSemiring (fun n => (monomial n).toAddMonoidHom.comp (pieceHom A W n))
    (by
      have h1 := (A.situation.sectionRingStructure).one_homogeneous W
      have h2 := A.sectionEquiv_one W
      change monomial 0 (pieceHom A W 0 _) = 1
      rw [pieceHom_apply]
      exact (congrArg (monomial 0) ((sectionEquiv_heq A (i := ((0 : ℕ) : ℤ)) (j := 0) rfl _
        le_rfl W _ _ (heq_of_eq h1)).trans h2)).trans monomial_zero_one)
    (by
      intro i j a b
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, monomial_mul_monomial]
      congr 1
      rw [pieceHom_apply, pieceHom_apply, pieceHom_apply,
        sectionEquiv_heq A (j := (i : ℤ) + j) (by push_cast; rfl) _
          (add_nonneg (Int.natCast_nonneg i) (Int.natCast_nonneg j)) W _ _
          ((A.situation.sectionRingStructure).mul_homogeneous W i j a b)]
      exact A.sectionEquiv_mul i j _ _ W a b)

private theorem polyHom_of (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens) (n : ℕ)
    (a : A.situation.sectionPieces W n) :
    polyHom A W (DirectSum.of _ n a) = monomial n (pieceHom A W n a) :=
  DirectSum.toSemiring_of _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem coeff_polyHom (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens)
    (r : A.situation.sectionRing W) (m : ℕ) :
    (polyHom A W r).coeff m = pieceHom A W m (r m) := by
  induction r using DirectSum.induction_on with
  | zero => rw [map_zero, coeff_zero, DirectSum.zero_apply, map_zero]
  | of n a =>
    rw [polyHom_of, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · have h0 : (DirectSum.of (A.situation.sectionPieces W) n a) m = 0 :=
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)
      rw [if_neg h, h0, map_zero]
  | add x y hx hy => rw [map_add, coeff_add, hx, hy, DirectSum.add_apply, map_add]

private theorem polyHom_injective (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens) :
    Function.Injective (polyHom A W) := by
  intro r r' h
  ext m
  have := congrArg (fun g => g.coeff m) h
  simp only [coeff_polyHom, pieceHom_apply] at this
  exact (A.sectionEquiv m (Int.natCast_nonneg m) W).injective (Subtype.ext this)

private theorem exists_polyHom_eq (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens)
    (g : ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X])
    (hg : ∀ m : ℕ, g.coeff m ∈ ((m : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W)) :
    ∃ r, polyHom A W r = g := by
  refine ⟨∑ m ∈ g.support, DirectSum.of _ m
    ((A.sectionEquiv m (Int.natCast_nonneg m) W).symm ⟨g.coeff m, hg m⟩), ?_⟩
  rw [map_sum]
  conv_rhs => rw [g.as_sum_support]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [polyHom_of, pieceHom_apply, AddEquiv.apply_symm_apply]

attribute [local instance] Polynomial.algebra in
/-- If the image of `ψ : A → K[X]` has coefficients integral over `O`, so does every element of
`K[X]` integral over `A`; for `O` integrally closed with fraction field `K` they lie in `O`. -/
private theorem exists_algebraMap_eq_coeff {A O K : Type*} [CommRing A] [CommRing O] [IsDomain O]
    [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
    (ψ : A →+* K[X]) (hψ : ∀ a m, IsIntegral O ((ψ a).coeff m)) {y : K[X]}
    (hy : ψ.IsIntegralElem y) (m : ℕ) : ∃ o : O, algebraMap O K o = y.coeff m := by
  let C := integralClosure O[X] K[X]
  let ψ' : A →+* C := ψ.codRestrict C.toSubring fun a =>
    (Polynomial.isIntegral_iff_isIntegral_coeff (R := O)).2 (hψ a)
  have hcomp : (algebraMap C K[X]).comp ψ' = ψ := rfl
  have hy' : IsIntegral C y := RingHom.IsIntegralElem.of_comp (f := ψ') (by rwa [hcomp])
  have hy'' : IsIntegral O[X] y := isIntegral_trans y hy'
  exact IsIntegrallyClosed.isIntegral_iff.mp (hy''.coeff m)

/-- Along a prime divisor `E`, with `c` of order `b`: `v_E(f) ≥ -mb` makes `f cᵐ` integral over
`𝒪_{Y,E}`. -/
private theorem isIntegral_mul_pow_of_ordGE (E : MMP.Mori.PrimeDivisor Y) {b : ℤ}
    {c : Y.presheaf.stalk (componentGenericPoint Y E.component)}
    (hc : E.valuation c = WithZero.exp b) (m : ℕ)
    {f : Y.presheaf.stalk (componentGenericPoint Y E.component)}
    (hf : E.OrdGE (-((m : ℤ) * b)) f) :
    letI := E.toComponent.hom.toAlgebra
    IsIntegral E.localRing (f * c ^ m) := by
  letI := E.toComponent.hom.toAlgebra
  rcases hf with rfl | hf
  · rw [zero_mul]; exact isIntegral_zero
  have h1 : 1 ≤ E.valuation (f * c ^ m) := by
    rw [map_mul, map_pow, hc]
    calc (1 : WithZero (Multiplicative ℤ))
        = WithZero.exp (-((m : ℤ) * b)) * WithZero.exp b ^ m := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul, neg_add_cancel,
            WithZero.exp_zero]
      _ ≤ _ := mul_le_mul_left hf _
  obtain ⟨o, ho⟩ := E.exists_toComponent_eq_of_one_le_valuation h1
  rw [← ho]
  exact isIntegral_algebraMap

/-- Along a prime divisor `E`, with `c ≠ 0` of order `b`: if `f cᵐ` lies in `𝒪_{Y,E}`, then
`v_E(f) ≥ -mb`. -/
private theorem ordGE_of_toComponent_eq (E : MMP.Mori.PrimeDivisor Y) {b : ℤ}
    {c : Y.presheaf.stalk (componentGenericPoint Y E.component)}
    (hc : E.valuation c = WithZero.exp b) (hc0 : c ≠ 0) (m : ℕ)
    {f : Y.presheaf.stalk (componentGenericPoint Y E.component)} {o : E.localRing}
    (ho : E.toComponent.hom o = f * c ^ m) : E.OrdGE (-((m : ℤ) * b)) f := by
  have := (RationalFunctions.isField_stalk Y E.component).isDomain
  by_cases hf : f = 0
  · exact Or.inl hf
  refine Or.inr ?_
  have ho0 : o ≠ 0 := by
    rintro rfl
    rw [map_zero] at ho
    exact mul_ne_zero hf (pow_ne_zero m hc0) ho.symm
  have h1 := E.one_le_valuation_toComponent ho0
  rw [ho, map_mul, map_pow, hc] at h1
  calc WithZero.exp (-((m : ℤ) * b))
      = WithZero.exp (-((m : ℤ) * b)) * 1 := (mul_one _).symm
    _ ≤ WithZero.exp (-((m : ℤ) * b)) * (E.valuation f * WithZero.exp b ^ m) :=
        mul_le_mul_right h1 _
    _ = E.valuation f := by
        rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_comm (E.valuation f), ← mul_assoc,
          ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul]

/-- Every integer is the order along `E` of a nonzero rational function. -/
private theorem exists_valuation_eq (E : MMP.Mori.PrimeDivisor Y) (b : ℤ) :
    ∃ c : Y.presheaf.stalk (componentGenericPoint Y E.component),
      c ≠ 0 ∧ E.valuation c = WithZero.exp b := by
  letI : Field (Y.presheaf.stalk (componentGenericPoint Y E.component)) :=
    (RationalFunctions.isField_stalk Y E.component).toField
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hϖ0 : E.toComponent.hom ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (stalkToRationalFunctions_injective _ (h0.trans (map_zero _).symm))
  refine ⟨(E.toComponent.hom ϖ) ^ b, zpow_ne_zero _ hϖ0, ?_⟩
  rw [map_zpow₀, E.valuation_toComponent_of_irreducible hϖ, ← WithZero.exp_zsmul, smul_eq_mul,
    mul_one]

/-- The coefficients of an element of `K[t]` integral over the section ring satisfy the
divisorial bound along every prime divisor meeting `W`. -/
private theorem ordGE_coeff_of_isIntegralElem (A : DivisorialSectionAlgebra (𝟙 Y) D)
    (W : Y.Opens) (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ (𝟙 Y) ⁻¹ᵁ W).Nonempty)
    {g : ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X]}
    (hg : (polyHom A W).IsIntegralElem g) (m : ℕ) :
    E.OrdGE (-((m : ℤ) • D).coeff E)
      (g.coeff m ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) := by
  letI : Field (Y.presheaf.stalk (componentGenericPoint Y E.component)) :=
    (RationalFunctions.isField_stalk Y E.component).toField
  letI := E.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  have := E.isDiscreteValuationRing_localRing
  have : IsIntegrallyClosed E.localRing := IsNormal.stalk_normal _
  let ev : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)) →+*
      Y.presheaf.stalk (componentGenericPoint Y E.component) :=
    Pi.evalRingHom (fun Z : {Z : irreducibleComponents Y //
      componentGenericPoint Y Z ∈ (𝟙 Y) ⁻¹ᵁ W} => Y.presheaf.stalk (componentGenericPoint Y Z.1))
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩
  obtain ⟨c, hc0, hc⟩ := exists_valuation_eq E (D.coeff E)
  let σ := Polynomial.compRingHom (Polynomial.C c * Polynomial.X)
  have hσ (p : (Y.presheaf.stalk (componentGenericPoint Y E.component))[X]) (k : ℕ) :
      (σ p).coeff k = p.coeff k * c ^ k := comp_C_mul_X_coeff
  have hy := (hg.map (mapRingHom ev)).map σ
  have hψ : ∀ (a : A.situation.sectionRing W) (k : ℕ), IsIntegral E.localRing
      ((σ.comp ((mapRingHom ev).comp (polyHom A W)) a).coeff k) := by
    intro a k
    rw [RingHom.comp_apply, RingHom.comp_apply, hσ, coe_mapRingHom, coeff_map, coeff_polyHom,
      pieceHom_apply]
    have hmem := (A.sectionEquiv k (Int.natCast_nonneg k) W (a k)).2 E hE
    rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hmem
    exact isIntegral_mul_pow_of_ordGE E hc k hmem
  obtain ⟨o, ho⟩ := exists_algebraMap_eq_coeff (O := E.localRing) _ hψ hy m
  rw [hσ, coe_mapRingHom, coeff_map] at ho
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  exact ordGE_of_toComponent_eq E hc hc0 m ho

/-- Over a nonempty open `W` of a normal integral scheme, the ring of sections
`⨁_m H⁰(W, 𝒪(mD))` of the divisorial algebra is an integrally closed domain. -/
private theorem sectionRing_isDomain_isIntegrallyClosed [IsIntegral Y]
    (A : DivisorialSectionAlgebra (𝟙 Y) D) (W : Y.Opens)
    [Nontrivial (A.situation.sectionRing W)] :
    ∃ _ : IsDomain (A.situation.sectionRing W), IsIntegrallyClosed (A.situation.sectionRing W) := by
  let T := {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ (𝟙 Y) ⁻¹ᵁ W}
  have hT : Subsingleton T := by
    have : Subsingleton (irreducibleComponents Y) := by
      rw [irreducibleComponents_eq_singleton]; infer_instance
    infer_instance
  have hTne : Nonempty T := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Subsingleton ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W))) :=
      inferInstanceAs (Subsingleton (∀ Z : T, Y.presheaf.stalk (componentGenericPoint Y Z.1)))
    exact not_subsingleton _ (polyHom_injective A W).subsingleton
  obtain ⟨z₀⟩ := hTne
  letI : Unique T := uniqueOfSubsingleton z₀
  letI : Field (Y.presheaf.stalk (componentGenericPoint Y z₀.1)) :=
    (RationalFunctions.isField_stalk Y z₀.1).toField
  let e : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)) ≃+*
      Y.presheaf.stalk (componentGenericPoint Y z₀.1) :=
    RingEquiv.piUnique (fun Z : T => Y.presheaf.stalk (componentGenericPoint Y Z.1))
  let e' := Polynomial.mapEquiv e
  have : IsDomain ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] :=
    MulEquiv.isDomain _ e'.toMulEquiv
  have : IsIntegrallyClosed ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] :=
    IsIntegrallyClosed.of_equiv e'.symm
  have : IsDomain (A.situation.sectionRing W) :=
    Function.Injective.isDomain (polyHom A W) (polyHom_injective A W)
  refine ⟨this, ?_⟩
  letI := (polyHom A W).toAlgebra
  have : FaithfulSMul (A.situation.sectionRing W)
      ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (polyHom_injective A W)
  have : IsIntegrallyClosedIn (A.situation.sectionRing W)
      ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X] := by
    refine isIntegrallyClosedIn_iff.2 ⟨polyHom_injective A W, fun {g} hg => ?_⟩
    exact exists_polyHom_eq A W g fun m E hE => ordGE_coeff_of_isIntegralElem A W E hE hg m
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _
    ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W)))[X]

end SectionRing

/-- Every standard chart `Spec (R_f)₀` of `Proj R_W` over an affine open `W` is normal. -/
private theorem isNormal_spec_away [IsIntegral Y] (A : DivisorialSectionAlgebra (𝟙 Y) D)
    (W : Y.affineOpens) (n : ℕ) (hn : 0 < n) (a : A.situation.sectionPieces W.1 n) :
    IsNormal (Spec (.of (HomogeneousLocalization.Away (A.situation.sectionRingGrading W.1)
      (DirectSum.of (A.situation.sectionPieces W.1) n a)))) := by
  set f := DirectSum.of (A.situation.sectionPieces W.1) n a
  rcases subsingleton_or_nontrivial (HomogeneousLocalization.Away
    (A.situation.sectionRingGrading W.1) f) with h | h
  · have he : ∀ x : Spec (.of (HomogeneousLocalization.Away
        (A.situation.sectionRingGrading W.1) f)), False := fun x =>
      x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
        rw [Subsingleton.elim (1 : HomogeneousLocalization.Away
          (A.situation.sectionRingGrading W.1) f) 0]; exact x.asIdeal.zero_mem))
    exact ⟨fun x => (he x).elim, fun x => (he x).elim⟩
  have : Nontrivial (A.situation.sectionRing W.1) := by
    by_contra h'
    rw [not_nontrivial_iff_subsingleton] at h'
    have : Subsingleton (Localization.Away f) :=
      IsLocalization.subsingleton (M := Submonoid.powers f) ⟨1, Subsingleton.elim _ _⟩
    exact not_subsingleton _ ((HomogeneousLocalization.val_injective
      (𝒜 := A.situation.sectionRingGrading W.1) (Submonoid.powers f)).subsingleton)
  obtain ⟨_, _⟩ := sectionRing_isDomain_isIntegrallyClosed A W.1
  have hf0 : f ≠ 0 := by
    rintro hf
    have : Subsingleton (Localization.Away f) :=
      IsLocalization.subsingleton (M := Submonoid.powers f) ⟨1, by simp [hf]⟩
    exact not_subsingleton _ ((HomogeneousLocalization.val_injective
      (𝒜 := A.situation.sectionRingGrading W.1) (Submonoid.powers f)).subsingleton)
  have := isDomain_away (A.situation.sectionRingGrading W.1) hf0
  have := isIntegrallyClosed_away (A.situation.sectionRingGrading W.1)
    (AddMonoidHom.mem_range.2 ⟨a, rfl⟩) hn hf0
  exact isNormal_spec_of_isIntegrallyClosed _

set_option backward.isDefEq.respectTransparency false in
/-- The relative `Proj` of the divisorial algebra is normal. -/
private theorem isNormal_model [IsIntegral Y] (A : DivisorialSectionAlgebra (𝟙 Y) D) :
    IsNormal A.model := by
  let s := A.situation
  have hW (W : Y.affineOpens) : IsOpenImmersion (s.relativeProjChart W) :=
    s.chartData.isOpenImmersion_chartι W
  refine isNormal_of_isOpenImmersion
    (ι := Σ W : Y.affineOpens, Σ n : {n : ℕ // 0 < n}, s.sectionPieces W.1 n)
    (fun i => Spec (.of (HomogeneousLocalization.Away (s.sectionRingGrading i.1.1)
      (DirectSum.of (s.sectionPieces i.1.1) i.2.1.1 i.2.2))))
    (fun i => Proj.awayι (s.sectionRingGrading i.1.1)
      (DirectSum.of (s.sectionPieces i.1.1) i.2.1.1 i.2.2) ⟨i.2.2, rfl⟩ i.2.1.2 ≫
        s.relativeProjChart i.1)
    (fun i => @IsOpenImmersion.comp _ _ _ _ _ inferInstance (hW i.1))
    (fun i => isNormal_spec_away A i.1 i.2.1.1 i.2.1.2 i.2.2) ?_
  intro x
  have hx : x ∈ (⊤ : A.model.Opens) := trivial
  rw [← s.chartData.iSup_opensRange_chartι, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨W, z, rfl⟩ := hx
  have hz : z ∈ (⊤ : (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Opens) := trivial
  rw [← Proj.iSup_basicOpen_eq_top' (s.sectionRingGrading W.1)
    (fun i : Σ n : {n : ℕ // 0 < n}, s.sectionPieces W.1 n =>
      DirectSum.of (s.sectionPieces W.1) i.1.1 i.2)
    (fun i => ⟨i.1.1, AddMonoidHom.mem_range.2 ⟨i.2, rfl⟩⟩)
    (adjoin_positive_eq_top s W.1), TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨⟨n, a⟩, hz⟩ := hz
  rw [← Proj.opensRange_awayι (s.sectionRingGrading W.1) _
    (AddMonoidHom.mem_range.2 ⟨a, rfl⟩) n.2] at hz
  obtain ⟨y, rfl⟩ := hz
  exact ⟨⟨W, n, a⟩, y, rfl⟩

/-- A space covered by preirreducible open sets, any two of which meet, is irreducible. -/
private theorem irreducibleSpace_of_cover {Z : Type*} [TopologicalSpace Z] [Nonempty Z]
    {ι : Type*} (U : ι → Set Z) (hU : ∀ i, IsOpen (U i)) (hirr : ∀ i, IsPreirreducible (U i))
    (hcov : ∀ x, ∃ i, x ∈ U i) (hint : ∀ i j, (U i ∩ U j).Nonempty) : IrreducibleSpace Z := by
  have hpre : IsPreirreducible (Set.univ : Set Z) := by
    rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
    obtain ⟨i, hi⟩ := hcov x
    obtain ⟨j, hj⟩ := hcov y
    obtain ⟨z, hzi, hzu, hzj⟩ := hirr i u (U j) hu (hU j) ⟨x, hi, hx⟩ (hint i j)
    obtain ⟨w, -, hwu, hwv⟩ := hirr j u v hu hv ⟨z, hzj, hzu⟩ ⟨y, hj, hy⟩
    exact ⟨w, trivial, hwu, hwv⟩
  exact @IrreducibleSpace.mk Z _ ⟨hpre⟩ ‹_›

open Stacks.RelativeProj in
set_option backward.isDefEq.respectTransparency false in
/-- The projective spectrum of the section ring over an open is irreducible when the section
ring is a domain and the spectrum is nonempty: the charts `D₊(f)` are spectra of domains, and
`D₊(f) ∩ D₊(g) = D₊(fg)` is nonempty. -/
private theorem irreducibleSpace_proj (s : Situation.{u}) (U : s.base.Opens)
    [IsDomain (s.sectionRing U)] [Nonempty (AlgebraicGeometry.Proj (s.sectionRingGrading U))] :
    IrreducibleSpace (AlgebraicGeometry.Proj (s.sectionRingGrading U)) := by
  let f : (Σ n : {n : ℕ // 0 < n}, s.sectionPieces U n) → s.sectionRing U :=
    fun i => DirectSum.of (s.sectionPieces U) i.1.1 i.2
  have hf : ∀ i, f i ∈ s.sectionRingGrading U i.1.1 := fun i => AddMonoidHom.mem_range.2 ⟨i.2, rfl⟩
  have h0 : ∀ i, ((Proj.basicOpen (s.sectionRingGrading U) (f i) :
      Set (AlgebraicGeometry.Proj (s.sectionRingGrading U)))).Nonempty → f i ≠ 0 := by
    intro i ⟨x, hx⟩ h
    rw [h, Proj.basicOpen_zero] at hx
    exact hx
  refine irreducibleSpace_of_cover
    (ι := {i // ((Proj.basicOpen (s.sectionRingGrading U) (f i) :
      Set (AlgebraicGeometry.Proj (s.sectionRingGrading U)))).Nonempty})
    (fun i => ((Proj.basicOpen (s.sectionRingGrading U) (f i.1) :
      (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens) :
        Set (AlgebraicGeometry.Proj (s.sectionRingGrading U))))
    (fun i => (Proj.basicOpen _ _).isOpen) (fun i => ?_) (fun x => ?_) (fun i j => ?_)
  · have := isDomain_away (s.sectionRingGrading U) (h0 i.1 i.2)
    rw [← Proj.opensRange_awayι _ _ (hf i.1) i.1.1.2, Scheme.Hom.coe_opensRange, ← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image _
      (Proj.awayι _ _ (hf i.1) i.1.1.2).continuous.continuousOn).isPreirreducible
  · have hx : x ∈ (⊤ : (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens) := trivial
    rw [← Proj.iSup_basicOpen_eq_top' _ f (fun i => ⟨i.1.1, hf i⟩) (adjoin_positive_eq_top s U),
      TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨⟨i, x, hi⟩, hi⟩
  · have hfg : f i.1 * f j.1 ∈ s.sectionRingGrading U (i.1.1.1 + j.1.1.1) :=
      SetLike.mul_mem_graded (hf i.1) (hf j.1)
    have hpos : 0 < i.1.1.1 + j.1.1.1 := Nat.add_pos_left i.1.1.2 _
    have := isDomain_away (s.sectionRingGrading U) (mul_ne_zero (h0 i.1 i.2) (h0 j.1 j.2))
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum
      (HomogeneousLocalization.Away (s.sectionRingGrading U) (f i.1 * f j.1))) := inferInstance
    refine ⟨Proj.awayι _ _ hfg hpos p, ?_⟩
    have hmem : Proj.awayι _ _ hfg hpos p ∈ Proj.basicOpen _ (f i.1 * f j.1) := by
      rw [← Proj.opensRange_awayι _ _ hfg hpos]; exact ⟨p, rfl⟩
    rw [Proj.basicOpen_mul] at hmem
    exact hmem

set_option backward.isDefEq.respectTransparency false in
/-- The chart over an affine open `W` covers exactly the points of the relative `Proj` lying
over `W`. -/
private theorem range_relativeProjChart (A : DivisorialSectionAlgebra (𝟙 Y) D)
    (W : Y.affineOpens) :
    Set.range (A.situation.relativeProjChart W) = A.toBase ⁻¹' (W.1 : Set Y) := by
  have hP := toBase_isPullback A W
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (A.situation.relativeProjChart W ≫ A.toBase) y ∈ (W.1 : Set Y)
    rw [hP.w, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  · intro hx
    have : x ∈ Set.range (CategoryTheory.Limits.pullback.fst A.toBase W.1.ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]; exact hx
    obtain ⟨z, rfl⟩ := this
    exact ⟨hP.isoPullback.inv z, (Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun g => g z) hP.isoPullback_inv_fst)⟩

open Opposite Polynomial in
set_option backward.isDefEq.respectTransparency false in
/-- Over a nonempty open `W` meeting no prime divisor of the support of `D`, the constant `1` is a
nonzero section of `𝒪(D)`, so the chart `Proj R_W` is nonempty. -/
private theorem nonempty_proj [IsIntegral Y] (A : DivisorialSectionAlgebra (𝟙 Y) D)
    (W : Y.Opens) (hW : (W : Set Y).Nonempty)
    (hWD : ∀ E : MMP.Mori.PrimeDivisor Y, D.coeff E ≠ 0 →
      ¬ (E.support ∩ ((𝟙 Y) ⁻¹ᵁ W : Set Y)).Nonempty) :
    Nonempty (AlgebraicGeometry.Proj (A.situation.sectionRingGrading W)) := by
  have h1 : (1 : (rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W))) ∈
      (((1 : ℕ) : ℤ) • D).divisorialSubmodule ((𝟙 Y) ⁻¹ᵁ W) := by
    intro E hE
    have hc : D.coeff E = 0 := by
      by_contra hc
      exact hWD E hc hE
    rw [DivisorWithCoeffs.coeff_smul, hc, smul_zero, neg_zero]
    refine Or.inr ?_
    change WithZero.exp 0 ≤ E.valuation 1
    rw [map_one, WithZero.exp_zero]
  let a : A.situation.sectionPieces W 1 :=
    (A.sectionEquiv ((1 : ℕ) : ℤ) (Int.natCast_nonneg 1) W).symm ⟨1, h1⟩
  let fa := DirectSum.of (A.situation.sectionPieces W) 1 a
  let Z₀ : irreducibleComponents Y :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩
  have hZ₀ : componentGenericPoint Y Z₀ ∈ (𝟙 Y) ⁻¹ᵁ W :=
    (genericPoint_mem_iff Z₀ ((𝟙 Y) ⁻¹ᵁ W)).2 (by simpa [Z₀] using hW)
  have : Nontrivial (Y.presheaf.stalk (componentGenericPoint Y Z₀)) :=
    (RationalFunctions.isField_stalk Y Z₀).nontrivial
  have : Nontrivial ((rationalFunctionsPresheaf Y).obj (op ((𝟙 Y) ⁻¹ᵁ W))) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrFun h ⟨Z₀, hZ₀⟩
    exact zero_ne_one this
  have hfa : fa ≠ 0 := by
    intro h
    have h2 := congrArg (polyHom A W) h
    rw [polyHom_of, pieceHom_apply, AddEquiv.apply_symm_apply, map_zero,
      monomial_eq_zero_iff] at h2
    exact one_ne_zero h2
  have : Nontrivial (A.situation.sectionRing W) := nontrivial_of_ne fa 0 hfa
  obtain ⟨_, _⟩ := sectionRing_isDomain_isIntegrallyClosed A W
  have := isDomain_away (A.situation.sectionRingGrading W) hfa
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum
    (HomogeneousLocalization.Away (A.situation.sectionRingGrading W) fa)) := inferInstance
  exact ⟨Proj.awayι _ fa (AddMonoidHom.mem_range.2 ⟨a, rfl⟩) one_pos p⟩

set_option backward.isDefEq.respectTransparency false in
/-- The relative `Proj` of the divisorial algebra over a normal integral scheme is integral. -/
private theorem isIntegral_model [IsIntegral Y] (A : DivisorialSectionAlgebra (𝟙 Y) D) :
    IsIntegral A.model := by
  let s := A.situation
  have : IsNormal s.relativeProj := isNormal_model A
  show IsIntegral s.relativeProj
  let OD : Y.Opens := ⟨(D.supp : Set Y)ᶜ, D.isClosed_supp.isOpen_compl⟩
  have hη : genericPoint Y ∈ OD := MMP.Fourfold.genericPoint_notMem_supp D
  have haff : ∀ (O : Y.Opens) (y : Y), y ∈ O → ∃ W : Y.affineOpens, y ∈ W.1 ∧ W.1 ≤ O := by
    intro O y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy O.2
    exact ⟨⟨V, hV⟩, hyV, hVO⟩
  have key : ∀ W : Y.affineOpens, genericPoint Y ∈ W.1 → W.1 ≤ OD →
      (Set.range (s.relativeProjChart W)).Nonempty := by
    intro W hW hWO
    obtain ⟨p⟩ := nonempty_proj A W.1 ⟨_, hW⟩ fun E hE ⟨x, hxE, hxW⟩ =>
      hWO hxW (DivisorWithCoeffs.support_subset_supp hE hxE)
    exact ⟨_, p, rfl⟩
  have hirrW : ∀ W : Y.affineOpens, (Set.range (s.relativeProjChart W)).Nonempty →
      IsIrreducible (Set.range (s.relativeProjChart W)) := by
    rintro W ⟨-, p, -⟩
    have : Nonempty (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) := ⟨p⟩
    have : Nontrivial (s.sectionRing W.1) := by
      by_contra h'
      rw [not_nontrivial_iff_subsingleton] at h'
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
        rw [Subsingleton.elim (1 : s.sectionRing W.1) 0]; exact Ideal.zero_mem _))
    obtain ⟨_, _⟩ := sectionRing_isDomain_isIntegrallyClosed A W.1
    have := irreducibleSpace_proj s W.1
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (s.relativeProjChart W).continuous.continuousOn
  have : Nonempty s.relativeProj := by
    obtain ⟨W, hW, hWO⟩ := haff OD _ hη
    obtain ⟨x, -⟩ := key W hW hWO
    exact ⟨x⟩
  have hgen : ∀ W : Y.affineOpens, (Set.range (s.relativeProjChart W)).Nonempty →
      genericPoint Y ∈ W.1 := by
    rintro W ⟨x, hx⟩
    rw [range_relativeProjChart] at hx
    exact ((genericPoint_spec Y).mem_open_set_iff W.1.isOpen).2 ⟨_, trivial, hx⟩
  have hpair : ∀ W W' : Y.affineOpens, genericPoint Y ∈ W.1 → genericPoint Y ∈ W'.1 →
      (Set.range (s.relativeProjChart W) ∩ Set.range (s.relativeProjChart W')).Nonempty := by
    intro W W' hW hW'
    have hmem : genericPoint Y ∈ W.1 ⊓ W'.1 ⊓ OD :=
      TopologicalSpace.Opens.mem_inf.2 ⟨TopologicalSpace.Opens.mem_inf.2 ⟨hW, hW'⟩, hη⟩
    obtain ⟨W'', hW'', hW''O⟩ := haff _ _ hmem
    obtain ⟨x, hx⟩ := key W'' hW'' (hW''O.trans inf_le_right)
    rw [range_relativeProjChart] at hx
    refine ⟨x, ?_, ?_⟩
    · rw [range_relativeProjChart]
      exact (hW''O.trans (inf_le_left.trans inf_le_left)) hx
    · rw [range_relativeProjChart]
      exact (hW''O.trans (inf_le_left.trans inf_le_right)) hx
  have : IrreducibleSpace s.relativeProj := by
    refine irreducibleSpace_of_cover
      (ι := {W : Y.affineOpens // (Set.range (s.relativeProjChart W)).Nonempty})
      (fun W => Set.range (s.relativeProjChart W.1))
      (fun W => by
        have := s.chartData.isOpenImmersion_chartι W.1
        exact (s.relativeProjChart W.1).isOpenEmbedding.isOpen_range)
      (fun W => (hirrW W.1 W.2).isPreirreducible) (fun x => ?_)
      (fun W W' => hpair W.1 W'.1 (hgen W.1 W.2) (hgen W'.1 W'.2))
    have hx : x ∈ (⊤ : s.relativeProj.Opens) := trivial
    rw [← s.chartData.iSup_opensRange_chartι, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨W, z, rfl⟩ := hx
    exact ⟨⟨W, _, z, rfl⟩, z, rfl⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced s.relativeProj

end MMP.Fourfold.Internal.DivisorialProjNormal

namespace MMP.Fourfold.DivisorialSectionAlgebra

set_option backward.isDefEq.respectTransparency false in
open MMP.Fourfold.Internal.DivisorialProjNormal in
/-- The relative `Proj` of a finitely generated divisorial algebra is a normal variety: for a
normal variety `Y` over `k`, a Weil divisor `B` on `Y` and `d > 0` such that
`⨁_{m ≥ 0} 𝒪_Y(mdB)` is a sheaf of finitely generated `𝒪_Y`-algebras,
`Proj_Y ⨁_{m ≥ 0} 𝒪_Y(mdB)` is a normal variety over `k`. -/
@[mmp "lem_mmp_foundation_divisorial_proj_normal"]
public theorem isNormalVariety_model {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k f)
    (B : Divisor Y) (d : ℕ) (hd : 0 < d) (A : DivisorialSectionAlgebra (𝟙 Y) (d • B))
    (hA : ∀ U : Y.Opens, IsAffineOpen U → (A.situation.sectionRingBaseMap U).FiniteType) :
    IsNormalVariety k (A.toBase ≫ f) := by
  have : AlgebraicGeometry.IsVariety k f := hY.1
  have h (W : Y.affineOpens) := chart_props A.situation W.1 W.2 (hA W.1 W.2)
  have : IsSeparated A.toBase := toBase_of_charts _ A fun W => (h W).1
  have : LocallyOfFiniteType A.toBase := toBase_of_charts _ A fun W => (h W).2.1
  have : QuasiCompact A.toBase := toBase_of_charts _ A fun W => (h W).2.2
  have : IsIntegral Y := hY.1.toIsIntegral
  have := isIntegral_model A
  exact ⟨{ }, isNormal_model A⟩

end MMP.Fourfold.DivisorialSectionAlgebra

end

/-!
## Negative definiteness of the curves contracted by a resolution of a normal surface

Let `X` be a normal surface over a field `k`, `f : Y ⟶ X` a resolution (a proper birational
morphism with `Y` smooth over `k`), and `E₁, …, E_r` distinct irreducible curves on `Y` each of
which `f` maps to a point. Then the intersection matrix `((Eᵢ · Eⱼ))` is negative definite.

### Main results

* `MMP.Mori.posDef_neg_intersectionMatrix_of_isSmoothResolution`: the matrix
  `-((Eᵢ · Eⱼ))` is positive definite.

### Implementation notes

An irreducible curve `Eᵢ` on the surface `Y` plays two roles in `(Eᵢ · Eⱼ)`: as the prime
divisor `Pᵢ` on the left and as the proper curve `Cⱼ` on the right. It is recorded as a prime
divisor `Pᵢ` together with a proper curve `Cᵢ` with the same generic point. A curve contracted
to a closed point by the proper morphism `f` is proper over `k`, so recording `Cᵢ` as a proper
curve is no restriction; the intersection number `(D · C)` is only defined for proper `C`.
The prime divisors on the smooth scheme `Y` are Cartier, which supplies the `ℚ`-Cartier
hypothesis of `MMP.Mori.QDivisor.intersectionNumber`.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §2.2]
-/

section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Mori

/-- **The curves contracted by a resolution of a normal surface have negative definite
intersection matrix.** Let `X` be a normal surface over `k`, `f : Y ⟶ X` a resolution, and
`E₁, …, E_r` distinct irreducible curves on `Y` (prime divisors `Pᵢ` with proper curves `Cᵢ`
having the same generic points) each contracted to a point by `f`. Then the matrix
`((Eᵢ · Eⱼ))` is negative definite. -/
@[mmp "lem_mmp_foundation_km_algebraic_exceptional_matrix"]
public theorem posDef_neg_intersectionMatrix_of_isSmoothResolution {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) {f : Y ⟶ X} (hf : IsSmoothResolution sX f)
    [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact (f ≫ sX)]
    {r : ℕ} (P : Fin r → PrimeDivisor Y) (hP : Function.Injective P)
    (C : Fin r → ProperCurve (f ≫ sX)) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy f) :
    (-(Matrix.of fun i j : Fin r =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k (f ≫ sX) (C j).ι
        (C j).dim_le
        (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hf.isSmoothScheme (P i)) :
          ℝ))).PosDef := by
  obtain ⟨⟨hY, -⟩, hdimY, -⟩ := hf.isNormalVariety hX
  have : IsProper f := hf.isProper
  exact MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism hY
    hf.isSmoothScheme (hdimY.trans hdim) hX.1 rfl hf.isBirationalMorphism P hP C hC hexc

end MMP.Mori

end

/-!
## The intersection number of two curves on a smooth surface is a sum of local terms

Let `Y` be a smooth surface over a field `k` and let `C ≠ D` be integral curves on `Y` (prime
divisors), with `C` proper over `k`. Then `C ∩ D` is a finite set of points, the intersection
number is

  `(D · C) = ∑_{y ∈ C ∩ D} i_y(C, D)`,

where `i_y(C, D) = dim_k 𝒪_{Y,y} / (h_C, h_D)` is the local intersection number, and every
summand is a positive integer. In particular `(D · C) ≥ 0`, with equality exactly when
`C ∩ D = ∅`.

### Main results

* `MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne`: `C ∩ D` is finite,
  `(D · C) = ∑_{y ∈ C ∩ D} i_y(C, D)`, and `0 < i_y(C, D)` for every `y ∈ C ∩ D`.

### Implementation notes

The intersection number `(D · C)` is `MMP.Mori.IsIntersectionNumber` of the `ℚ`-divisor `D`
with the ideal sheaf of `C`, and the local term is `MMP.Mori.localIntersectionNumber` of the
divisors `C` and `D`. The latter is a `Module.finrank`, hence `0` when the quotient is
infinite-dimensional; positivity of the local terms therefore also records that they are finite.
The standing hypotheses that `Y` is locally Noetherian, normal and quasi-compact over `k` enter as
instance arguments, which the intersection number needs; they hold on a smooth surface.

### References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Chapter 4
* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.50
-/

section

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori.Internal.SurfaceIntersectionLocalSum

section LocalTrivialization

open Opposite DivisorWithCoeffs

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

/-- Multiplication by a unit `ψ` of `K(Y)` maps `𝒪_Y(D)(U)` to `𝒪_Y(D')(U)` when
`D = D' + div(ψ)` at every prime divisor meeting `U`. -/
private noncomputable def mulOn (ψ : (RationalFunctions Y)ˣ) {D D' : Divisor Y} (U : Y.Opens)
    (h : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ U).Nonempty →
      D.coeff E = D'.coeff E + E.ord ψ) :
    D.divisorialSubmodule U →ₗ[Γ(Y, U)] D'.divisorialSubmodule U where
  toFun φ := ⟨fun Z => (ψ : RationalFunctions Y) Z.1 * φ.1 Z, fun E hE => by
    have hψ : E.OrdGE (E.ord ψ) ((ψ : RationalFunctions Y) E.component) :=
      Or.inr (E.valuation_component ψ).ge
    refine (hψ.mul (φ.2 E hE)).mono (le_of_eq ?_)
    rw [h E hE]
    ring⟩
  map_add' φ φ' := Subtype.ext (funext fun Z => mul_add _ _ _)
  map_smul' r φ := Subtype.ext (funext fun Z => mul_left_comm _ _ _)

/-- Multiplication by `ψ` as an isomorphism `𝒪_Y(D)(U) ≃ 𝒪_Y(D')(U)`, with inverse the
multiplication by `ψ⁻¹`. -/
private noncomputable def mulEquivOn (ψ : (RationalFunctions Y)ˣ) {D D' : Divisor Y} (U : Y.Opens)
    (h : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ U).Nonempty →
      D.coeff E = D'.coeff E + E.ord ψ) :
    D.divisorialSubmodule U ≃ₗ[Γ(Y, U)] D'.divisorialSubmodule U :=
  { mulOn ψ U h with
    invFun := mulOn ψ⁻¹ U (fun E hE => by rw [h E hE, PrimeDivisor.ord_inv]; ring)
    left_inv := fun φ => Subtype.ext (funext fun Z => by
      change (ψ⁻¹ : (RationalFunctions Y)ˣ).1 Z.1 * ((ψ : RationalFunctions Y) Z.1 * φ.1 Z) =
        φ.1 Z
      rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Pi.one_apply, one_mul])
    right_inv := fun φ => Subtype.ext (funext fun Z => by
      change (ψ : RationalFunctions Y) Z.1 * ((ψ⁻¹ : (RationalFunctions Y)ˣ).1 Z.1 * φ.1 Z) =
        φ.1 Z
      rw [← mul_assoc, ← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Pi.one_apply, one_mul]) }

/-- Where `I_P = (f)` on an affine open `W`, `𝒪_Y(P)` is trivial on `W`, with the canonical
section `1` corresponding to `f`. -/
private theorem exists_linearEquiv_oneSection (P : MMP.Mori.PrimeDivisor Y) {W : Y.Opens}
    (hW : IsAffineOpen W) {f : Γ(Y, W)} (hf : IsRegular f)
    (hspan : P.idealSheaf.ideal ⟨W, hW⟩ = Ideal.span {f})
    (heff : (0 : Divisor Y) ≤ Finsupp.single P 1) :
    ∃ e : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), W) ≃ₗ[Γ(Y, W)] Γ(Y, W),
      e (((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op) (MMP.Threefold.Mori.oneSection heff)) = f := by
  classical
  haveI := P.integral
  have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
      Ideal.span {(Y.presheaf.germ W y hy).hom f} := by
    intro y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (Y.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  have hfield : ∀ Z : irreducibleComponents Y,
      IsField (Y.presheaf.stalk (componentGenericPoint Y Z)) :=
    fun Z => RationalFunctions.isField_stalk Y Z
  let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
    fun Z => if h : componentGenericPoint Y Z ∈ W then
      (by
        letI := (hfield Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  let φ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm u
  have hφZ : ∀ (Z : irreducibleComponents Y) (hZW : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZW).hom f := by
    intro Z hZW
    change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y Z)) = _
    simp only [u]
    rw [dif_pos hZW]
    rfl
  have hord : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W).Nonempty →
      DivisorWithCoeffs.coeff (Finsupp.single P 1 : Divisor Y) E =
        DivisorWithCoeffs.coeff (0 : Divisor Y) E + E.ord φ := by
    rintro E ⟨y, hyE, hyW⟩
    rw [DivisorWithCoeffs.coeff_zero, zero_add]
    have hηW : E.genericPoint ∈ W := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
      exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
    have hZW : componentGenericPoint Y E.component ∈ W :=
      E.specializes_genericPoint.mem_open W.isOpen hηW
    have key : E.toComponent.hom ((Y.presheaf.germ W _ hηW).hom f) =
        (φ : RationalFunctions Y) E.component := by
      rw [hφZ _ hZW]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    by_cases hEP : P = E
    · subst hEP
      rw [coeff_single_self]
      have hmem : P.genericPoint ∈ P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      have hg0 := nonZeroDivisors.ne_zero (hnzd _ hηW)
      have hprime : Prime ((Y.presheaf.germ W _ hηW).hom f) := by
        rw [← Ideal.span_singleton_prime hg0, ← hgerm _ hηW]
        have hxr : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
          rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
        obtain ⟨y', hy'⟩ := hxr
        rw [← hy']
        rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
        exact RingHom.ker_isPrime _
      exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
    · rw [coeff_single_of_ne hEP]
      have hnm : E.genericPoint ∉ P.support := fun h =>
        hEP (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P E h)
      have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
        P.idealSheaf _).2 hnm
      rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
      exact (E.ord_eq_zero_of_isUnit htop key).symm
  let g₀ : Γ(Y, W) →ₗ[Γ(Y, W)] (0 : Divisor Y).divisorialSubmodule W :=
    { toFun := fun r => ⟨algebraMap Γ(Y, W) _ r, Divisor.isDivisorialSection_algebraMap le_rfl r⟩
      map_add' := fun r s => Subtype.ext (map_add _ r s)
      map_smul' := fun r s => Subtype.ext (by
        change algebraMap Γ(Y, W) _ (r * s) = r • algebraMap Γ(Y, W) _ s
        rw [Algebra.smul_def, map_mul]) }
  have hbij : Function.Bijective g₀ := by
    refine ⟨fun r s h => ?_, fun φ => ?_⟩
    · exact MMP.Mori.toRationalFunctionsPresheaf_app_injective W (congrArg Subtype.val h)
    · obtain ⟨s, hs⟩ := Divisor.IsDivisorialSection.exists_eq φ.2
      exact ⟨s, Subtype.ext hs⟩
  let g := LinearEquiv.ofBijective g₀ hbij
  let e := (mulEquivOn φ W hord).trans g.symm
  refine ⟨e, ?_⟩
  let x : Divisor.divisorialSubmodule (Finsupp.single P 1 : Divisor Y) W :=
    ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op) (MMP.Threefold.Mori.oneSection heff)
  change g.symm (mulEquivOn φ W hord x) = f
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext Z
  change (φ : RationalFunctions Y) Z.1 * x.1 Z = Y.presheaf.germ W _ Z.2 f
  have hL : x.1 Z = 1 := by
    have e1 := congrFun (Divisor.coe_structureSheafToDivisorialSheaf_app heff ⊤ (1 : Γ(Y, ⊤)))
      ⟨Z.1, trivial⟩
    change ((rationalFunctionsPresheaf Y).map (homOfLE (le_top : W ≤ ⊤)).op
      (((MMP.Threefold.Mori.oneSection heff :
        Divisor.divisorialSubmodule (Finsupp.single P 1 : Divisor Y) ⊤)).1)) Z = 1
    rw [rationalFunctionsPresheaf_map_apply]
    refine Eq.trans e1 ?_
    exact map_one (Y.presheaf.germ ⊤ (componentGenericPoint Y Z.1) trivial).hom
  rw [hL, mul_one, hφZ Z.1 Z.2]

/-- The stalk of the zero scheme of the canonical section of `𝒪_Y(P)` at a point of `Y` is the
stalk of the ideal of `P`. -/
private theorem stalk_zeroScheme_oneSection (P : MMP.Mori.PrimeDivisor Y)
    (hP : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf)
    (heff : (0 : Divisor Y) ≤ Finsupp.single P 1)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y))] (y : Y) :
    IdealSheafData.stalk (Stacks.Divisors.zeroScheme Y
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y))
      (MMP.Threefold.Mori.oneSection heff)) y = IdealSheafData.stalk P.idealSheaf y := by
  obtain ⟨W, hW, hyW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor P.idealSheaf hP y
  obtain ⟨e, he⟩ := exists_linearEquiv_oneSection P hW hf hspan heff
  rw [Stacks.Divisors.stalk_zeroScheme_eq_span_germ _ _ ⟨W, hW⟩ e f he y hyW,
    AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hyW, hspan,
    Ideal.map_span, Set.image_singleton]

/-- The `k`-dimension of the local ring at `x` of a `k`-scheme mapping to `Y` by `g`, surjectively
on the local ring at `x`, is the `k`-dimension of `𝒪_{Y,g x}` modulo the kernel. -/
private theorem finrank_stalk_eq_finrank_quotient {k : Type u} [Field k] {X : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (x : X) (sX : X ⟶ Spec (.of k)) (hs : g ≫ sY = sX)
    (hsurj : Function.Surjective (g.stalkMap x)) {I : Ideal (Y.presheaf.stalk (g x))}
    (hker : RingHom.ker (g.stalkMap x).hom = I) :
    letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop).hom).toAlgebra
    letI := MMP.Mori.stalkAlgebra sY (g x)
    Module.finrank k (X.presheaf.stalk x) = Module.finrank k (Y.presheaf.stalk (g x) ⧸ I) := by
  subst hs
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ ⊤ x (by simp)).hom.comp
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ sY).appTop).hom).toAlgebra
  letI := MMP.Mori.stalkAlgebra sY (g x)
  let e : (Y.presheaf.stalk (g x) ⧸ I) ≃+* X.presheaf.stalk x :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ c : k, e (algebraMap k _ c) = algebraMap k _ c := by
    intro c
    change g.stalkMap x (Y.presheaf.germ ⊤ (g x) _ (sY.appTop ((Scheme.ΓSpecIso (.of k)).inv c))) =
      X.presheaf.germ ⊤ x _ ((g ≫ sY).appTop ((Scheme.ΓSpecIso (.of k)).inv c))
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.comp_appTop]
    rfl
  let eₗ : (Y.presheaf.stalk (g x) ⧸ I) ≃ₗ[k] X.presheaf.stalk x :=
    { e with
      map_smul' := fun c y => by
        rw [Algebra.smul_def, Algebra.smul_def]
        exact (map_mul e _ _).trans (by rw [he]; rfl) }
  exact eₗ.finrank_eq.symm

end LocalTrivialization

section

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

omit [QuasiCompact sY] [IsNormal Y] in
/-- The support of the divisor `1 · D` is `D`. -/
private theorem supp_single_one (D : MMP.Mori.PrimeDivisor Y) :
    (DivisorWithCoeffs.supp (Finsupp.single D 1 : MMP.Mori.Divisor Y) : Set Y) = D.support :=
  le_antisymm (DivisorWithCoeffs.supp_single_le D 1)
    (DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_single_self]))

/-- A point common to two distinct prime divisors of a surface is a closed point. -/
private theorem isClosed_singleton_of_mem_inter (hdim : topologicalKrullDim Y = 2)
    {C D : MMP.Mori.PrimeDivisor Y} (hCD : C ≠ D) {y : Y} (hy : y ∈ C.support ∩ D.support) :
    IsClosed ({y} : Set Y) := by
  have hne : y ≠ C.genericPoint := by
    rintro rfl
    exact hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C hy.2).symm
  have hle : y ≤ C.genericPoint := by
    have h := hy.1
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
    exact specializes_iff_mem_closure.mpr h
  have hlt : y < C.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show y ⤳ C.genericPoint from h)
      (show C.genericPoint ⤳ y from hle)).eq
  have h2 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  have hwy : w ≤ y := specializes_iff_mem_closure.mpr hw
  by_contra hne
  have hlt' : w < y := lt_of_le_not_ge hwy fun h => hne (Specializes.antisymm
    (show w ⤳ y from h) (show y ⤳ w from hwy)).eq
  have h4 := Order.coheight_add_one_le hlt'
  have h5 := coheight_le_topologicalKrullDim w
  rw [hdim] at h5
  have h6 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
    (add_le_add h2 (le_refl (1 : ℕ∞))).trans (h4.trans (WithBot.coe_le_coe.mp h5))
  exact absurd h6 (by decide)

/-- On a smooth scheme over `k` the ideal sheaf of a prime divisor is an effective Cartier
divisor. -/
private theorem isEffectiveCartierDivisor_idealSheaf (hY : MMP.Mori.IsVariety k sY)
    (hsm : IsSmoothScheme sY)
    (P : MMP.Mori.PrimeDivisor Y) :
    Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf := by
  haveI := P.integral
  have := hY.toLocallyOfFiniteType
  have : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sY hsm
  exact isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid P.idealSheaf
    P.codimension_one (fun x _ => uniqueFactorizationMonoid_stalk_of_smooth sY x)

include sY in
/-- **Finiteness of the intersection.** Two distinct prime divisors on a surface quasi-compact
over `k` meet in finitely many points. -/
private theorem finite_inter (hdim : topologicalKrullDim Y = 2) {C D : MMP.Mori.PrimeDivisor Y}
    (hCD : C ≠ D) : (C.support ∩ D.support : Set Y).Finite := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  have hcl : IsClosed (C.support ∩ D.support : Set Y) :=
    C.idealSheaf.support.isClosed.inter D.idealSheaf.support.isClosed
  obtain ⟨S, hS, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hcl
  rw [hSeq]
  refine hS.sUnion fun t ht => Set.Subsingleton.finite ?_
  have hts : t ⊆ C.support ∩ D.support := hSeq ▸ Set.subset_sUnion_of_mem ht
  have hg := (hSirr t ht).isGenericPoint_genericPoint_closure
  rw [(hScl t ht).closure_eq] at hg
  have hgt : (hSirr t ht).genericPoint ∈ t := hg.mem
  have hclosed := isClosed_singleton_of_mem_inter hdim hCD (hts hgt)
  rw [← hg.def, hclosed.closure_eq]
  exact Set.subsingleton_singleton

/-- **The local intersection numbers compute the degree of `𝒪_Y(D)` on `C`, and are positive.**
The canonical section of `𝒪_Y(D)` restricts to a nonzero section of `𝒪_Y(D)|_C`, whose zero scheme
`Z` is finite over `k`, embedded in `Y` with image `C ∩ D`, and whose local ring at the point over
`y` is `𝒪_{Y,y}/(I_C + I_D)`. Its global sections have dimension `(D · C)`, which is the sum of
the dimensions `i_y(C, D)` of its local rings; each is positive, a local ring of `Z` being a
nonzero finite-dimensional `k`-algebra. -/
private theorem degreeOn_single_eq_sum_and_pos (hY : MMP.Mori.IsVariety k sY)
    (hsm : IsSmoothScheme sY) {C D : MMP.Mori.PrimeDivisor Y} (hCD : C ≠ D)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sY))
    (hdim1 : topologicalKrullDim C.idealSheaf.subscheme ≤ 1)
    (hfin : (C.support ∩ D.support : Set Y).Finite) :
    MMP.Mori.Divisor.degreeOn k sY C.idealSheaf.subschemeι hdim1 (Finsupp.single D 1)
        (MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm D) =
      ∑ y ∈ hfin.toFinset,
        (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℤ) ∧
      ∀ y ∈ C.support ∩ D.support,
        0 < localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) := by
  classical
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := C.integral
  haveI := hC
  set i := C.idealSheaf.subschemeι with hi
  set M : Y.Modules := MMP.Mori.Divisor.divisorialSheaf (Finsupp.single D 1) with hM
  have hcart := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm D
  haveI := hcart.isInvertibleModule_divisorialSheaf
  have heff : (0 : MMP.Mori.Divisor Y) ≤ Finsupp.single D 1 :=
    Finsupp.single_nonneg.mpr zero_le_one
  have hgen : C.genericPoint ∈ Set.range i := by
    rw [hi, Scheme.IdealSheafData.range_subschemeι]
    exact (show C.genericPoint ∈ C.support by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  obtain ⟨c₀, hc₀⟩ := hgen
  have hc : ∃ c, i c ∈ Stacks.Ample.nonvanishingLocus M (MMP.Threefold.Mori.oneSection heff) := by
    refine ⟨c₀, ?_⟩
    rw [MMP.Threefold.Mori.nonvanishingLocus_oneSection heff hcart, hc₀, supp_single_one]
    exact fun h => hCD (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support D C h).symm
  have hs := MMP.Threefold.Mori.eval_pullbackSection_ne_zero i M _ hc
  haveI : SheafOfModules.IsInvertible C.idealSheaf.subscheme.presheaf _
      ((Scheme.Modules.pullback i).obj M) := MMP.Mori.isInvertible_pullback_obj i M
  haveI := isFinite_zeroScheme_of_eval_top_ne_zero k (i ≫ sY) hdim1 _ _ hs
  set Z := zeroScheme C.idealSheaf.subscheme
    (Stacks.NonvanishingSpelling.toSheafOfModules C.idealSheaf.subscheme
      ((Scheme.Modules.pullback i).obj M))
    (((Stacks.NonvanishingSpelling.sectionsEquiv C.idealSheaf.subscheme
      ((Scheme.Modules.pullback i).obj M)).symm
      (Stacks.NonvanishingPullback.pullbackGlobalSection i M
        (MMP.Threefold.Mori.oneSection heff))).eval (Opposite.op ⊤)) with hZ
  set j : Z.subscheme ⟶ Y := Z.subschemeι ≫ i with hj
  /- The zero scheme `Z` of the restricted canonical section sits over `C ∩ D`: the composite
  `Z ⟶ C ⟶ Y` of closed immersions is injective, and its image is `C ∩ D` because the canonical
  section of `𝒪_Y(D)` vanishes exactly on `Supp D`. -/
  have hjinj : Function.Injective j := by
    rw [hj]
    exact (Z.subschemeι ≫ i).isClosedEmbedding.injective
  have hsupp : (Z.support : Set C.idealSheaf.subscheme) =
      i ⁻¹' D.support := by
    have h1 := nonvanishingLocus_eq_compl_supportSet_zeroScheme _ _ hs
    rw [MMP.Threefold.Mori.nonvanishingLocus_pullbackSection,
      MMP.Threefold.Mori.nonvanishingLocus_oneSection heff hcart, supp_single_one,
      Set.preimage_compl] at h1
    exact (compl_injective h1).symm
  have hrange_i : Set.range i = C.support := by
    rw [hi, Scheme.IdealSheafData.range_subschemeι]
  have hjrange : Set.range j = C.support ∩ D.support := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : Z.subschemeι z ∈ (Z.support : Set C.idealSheaf.subscheme) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
      rw [hsupp] at hz
      have hjz : j z = i (Z.subschemeι z) := rfl
      rw [hjz]
      exact ⟨hrange_i ▸ ⟨_, rfl⟩, hz⟩
    · rintro ⟨hyC, hyD⟩
      obtain ⟨c, rfl⟩ : y ∈ Set.range i := hrange_i ▸ hyC
      have hc : c ∈ (Z.support : Set C.idealSheaf.subscheme) := by
        rw [hsupp]; exact hyD
      rw [← Scheme.IdealSheafData.range_subschemeι] at hc
      obtain ⟨z, hz⟩ := hc
      exact ⟨z, by rw [← hz]; rfl⟩
  have hterm : ∀ z : Z.subscheme,
      letI : Algebra k (Z.subscheme.presheaf.stalk z) :=
        ((Z.subscheme.presheaf.germ ⊤ z (by simp)).hom.comp
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ i ≫ sY).appTop).hom).toAlgebra
      Module.finrank k (Z.subscheme.presheaf.stalk z) =
        localIntersectionNumber sY (j z) (Finsupp.single C 1) (Finsupp.single D 1) := by
    intro z
    /- The stalk of `Z` at `z` is `𝒪_{C,p}/(h_D|_C) ≅ 𝒪_{Y,y}/(I_{C,y} + I_{D,y})` as a
    `k`-algebra, where `p` is the image of `z` in `C`, `y = j z`, and `h_D` a local equation of
    `D` at `y`. -/
    haveI hMinv : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M :=
      inferInstanceAs (SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M)
    have hZeq : Z = (Stacks.Divisors.zeroScheme Y M (MMP.Threefold.Mori.oneSection heff)).comap i :=
      Eq.trans rfl (Stacks.Divisors.zeroScheme_pullback i M (MMP.Threefold.Mori.oneSection heff))
    have hker : RingHom.ker ((Z.subschemeι ≫ i).stalkMap z).hom =
        IdealSheafData.stalk C.idealSheaf (j z) ⊔ IdealSheafData.stalk D.idealSheaf (j z) := by
      have hcomp : RingHom.ker ((Z.subschemeι ≫ i).stalkMap z).hom =
          Ideal.comap (i.stalkMap (Z.subschemeι z)).hom
            (RingHom.ker (Z.subschemeι.stalkMap z).hom) := by
        ext a
        simp only [RingHom.mem_ker, Ideal.mem_comap]
        rw [Scheme.Hom.stalkMap_comp]
        rfl
      rw [hcomp, Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      change _ = IdealSheafData.stalk C.idealSheaf (i (Z.subschemeι z)) ⊔
        IdealSheafData.stalk D.idealSheaf (i (Z.subschemeι z))
      generalize Z.subschemeι z = p
      rw [hZeq, IdealSheafData.stalk_comap, Ideal.comap_map_of_surjective _
        (Scheme.Hom.stalkMap_surjective i _), ← RingHom.ker_eq_comap_bot, hi,
        Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk,
        stalk_zeroScheme_oneSection D (isEffectiveCartierDivisor_idealSheaf sY hY hsm D) heff,
        sup_comm]
    have hloc : ∀ P : MMP.Mori.PrimeDivisor Y,
        localIdeal (j z) (Finsupp.single P 1) = IdealSheafData.stalk P.idealSheaf (j z) := by
      intro P
      rw [localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
        Finsupp.single_eq_same, Int.toNat_one, pow_one]
    unfold localIntersectionNumber
    rw [hloc, hloc]
    exact finrank_stalk_eq_finrank_quotient sY (Z.subschemeι ≫ i) z (Z.subschemeι ≫ i ≫ sY)
      (Category.assoc _ _ _) (Scheme.Hom.stalkMap_surjective _ z) hker
  refine ⟨?_, fun y hy => ?_⟩
  · change invertibleCurveDegree k (i ≫ sY) hdim1 ((Scheme.Modules.pullback i).obj M) = _
    rw [invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one k (i ≫ sY) hdim1
      _ _ hs _ rfl, finrank_globalSections_eq_finsum_finrank_stalk k _]
    refine (congrArg (fun n : ℕ => (n : ℤ)) (finsum_congr
      (g := fun z => localIntersectionNumber sY (j z) (Finsupp.single C 1) (Finsupp.single D 1))
      hterm)).trans ?_
    dsimp only
    rw [← finsum_mem_range (f := fun y =>
        localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1)) hjinj, hjrange,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  · obtain ⟨z, rfl⟩ := hjrange ▸ hy
    letI : Algebra k (Z.subscheme.presheaf.stalk z) :=
      ((Z.subscheme.presheaf.germ ⊤ z (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ i ≫ sY).appTop).hom).toAlgebra
    haveI := finite_stalk_of_isFinite_over_field k (Z.subschemeι ≫ i ≫ sY) z
    rw [← hterm z]
    exact Module.finrank_pos

end

end MMP.Mori.Internal.SurfaceIntersectionLocalSum

namespace MMP.Mori

variable {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

open MMP.Mori.Internal.SurfaceIntersectionLocalSum in
/-- **Local intersections sum to the intersection number.** Let `C ≠ D` be prime divisors on a
smooth surface `Y` over a field `k`, with `C` proper over `k`. Then
`C ∩ D` is finite, `(D · C) = ∑_{y ∈ C ∩ D} i_y(C, D)`, and every local intersection number
`i_y(C, D)` with `y ∈ C ∩ D` is positive. -/
@[mmp "lem_mmp_threefold_surface_intersection_local_sum"]
public theorem isIntersectionNumber_finsum_localIntersectionNumber_of_ne (hY : IsVariety k sY)
    (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2) {C D : PrimeDivisor Y}
    (hCD : C ≠ D) (hC : IsProper (C.idealSheaf.subschemeι ≫ sY)) :
    (C.support ∩ D.support).Finite ∧
      IsIntersectionNumber sY (Finsupp.single D 1) C.idealSheaf
        (∑ᶠ y ∈ C.support ∩ D.support,
          (localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) : ℚ)) ∧
      ∀ y ∈ C.support ∩ D.support,
        0 < localIntersectionNumber sY y (Finsupp.single C 1) (Finsupp.single D 1) := by
  have hfin := finite_inter sY hdim hCD
  haveI := C.integral
  have hdim1 : topologicalKrullDim C.idealSheaf.subscheme ≤ 1 :=
    Stacks.ResolutionOfSurfaces.topologicalKrullDim_subscheme_le_one hdim C.idealSheaf
      (isEffectiveCartierDivisor_idealSheaf sY hY hsm C)
  obtain ⟨hsum, hpos⟩ := degreeOn_single_eq_sum_and_pos sY hY hsm hCD hC hdim1 hfin
  refine ⟨hfin, ?_, hpos⟩
  have hcart := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm D
  have hQ := MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm D
  rw [show (Finsupp.single D 1 : MMP.Mori.QDivisor Y) = Divisor.toQDivisor (Finsupp.single D 1) by
    rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]]
  refine ⟨hC, hdim1, hQ, ?_⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sY _ hdim1 _ hcart hQ, hsum,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rfl

end MMP.Mori

end
