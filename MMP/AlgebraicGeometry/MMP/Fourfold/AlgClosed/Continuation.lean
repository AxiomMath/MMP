module

import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.AlgClosedExtension
public import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
public import MMP.AlgebraicGeometry.MMP.Fourfold.AlgClosed.RayContraction
public import MMP.AlgebraicGeometry.SpreadingOut.ProjectiveDiagram
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.CountableDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.Continuation
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.Geometrically.NumericalDivisorClassesBaseChange
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.Analysis.Convex.FiniteDimensional
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
public import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import MMP.AlgebraicGeometry.Morphisms.FiniteFunctionField

/-!
# Continuation through a birational contraction over any algebraically closed field

Let `k` be an algebraically closed field of characteristic zero, `(X, B)` a projective lc
fourfold pair over `k` with rational boundary and canonical divisor `K`, `D = K + B`, `R` a
`D`-negative extremal ray of `NE̅(X)` and `f : X ⟶ Z` a contraction of `R` which is birational.
Then `f` extends to a permitted step: there is a small projective birational `f⁺ : X⁺ ⟶ Z`
(possibly an isomorphism) such that, with `B⁺` the strict transform of `f_* B`, the pair
`(X⁺, B⁺)` is lc and `K_{X⁺} + B⁺` is `f⁺`-ample. The proof descends the data to a countable
algebraically closed subfield, continues over `ℂ`, spreads the complex step out and specializes
it back.

## Main results

* `MMP.Fourfold.IsContractionOfRay.exists_isPermittedStep_of_isAlgClosed`: a birational
  contraction of a negative extremal ray of a projective lc fourfold pair extends to a permitted
  step.

## Implementation notes

The boundary `B⁺` of a permitted step (`MMP.Fourfold.IsPermittedStep`) is the strict transform
of `f_* B`, so it is not a separate witness. That `Z` is a normal projective variety, that
`ρ(X/Z) = 1` and that `-D` is `f`-ample are part of the conclusion, not hypotheses: they follow
from `f` being a contraction of `R`. The boundary is a `ℚ`-divisor, so it is rational, and
"fourfold" is `topologicalKrullDim X = 4`.
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold
  MMP.ProgramBaseChange

namespace Proof_lem_oai4_finite_existence_transfer

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

section FieldChangeBasics

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- Normality, integrality and dimension are insensitive to a base change along
`Spec K ⟶ Spec k₀`, in any pullback square. -/
private lemma invariants_of_isPullback {X W : Scheme.{u}} (f : X ⟶ Spec (.of k₀))
    [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    (IsNormal X ↔ IsNormal W) ∧ (IsIntegral X ↔ IsIntegral W) ∧
      topologicalKrullDim W = topologicalKrullDim X := by
  obtain ⟨-, hint, hnor, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  let e := h.isoPullback
  refine ⟨hnor.trans ⟨fun _ => MMP.ProgramBaseChange.isNormal_of_iso e,
    fun _ => MMP.ProgramBaseChange.isNormal_of_iso e.symm⟩,
    hint.trans ⟨fun _ => MMP.isIntegral_of_iso e.symm,
      fun _ => MMP.isIntegral_of_iso e⟩, ?_⟩
  have h1 := hdim Set.univ (IsOpen.isLocallyClosed isOpen_univ)
  rw [Set.preimage_univ] at h1
  rw [(Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq,
    ← (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq,
    ← (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq]
  exact h1

end FieldChangeBasics

section Square

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] {X W : Scheme.{u}}
  (f : X ⟶ Spec (.of k₀)) [LocallyOfFiniteType f] {p : W ⟶ X} {s : W ⟶ Spec (.of K)}

/-- The preimage of a locally closed subset under the projection of a base change of the ground
field has the same dimension. -/
private lemma topologicalKrullDim_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZ : IsLocallyClosed Z) : topologicalKrullDim (p ⁻¹' Z) = topologicalKrullDim Z := by
  obtain ⟨-, -, -, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  rw [← hdim Z hZ]
  have hp (w : W) : p w = pullback.fst f _ (h.isoPullback.hom w) := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  refine (Homeomorph.subtype (Scheme.homeoOfIso h.isoPullback) fun w => ?_).isHomeomorph
    |>.topologicalKrullDim_eq
  simp only [Set.mem_preimage, Scheme.homeoOfIso_apply]
  rw [hp w]

/-- The preimage of an irreducible closed subset under the projection of a base change of an
algebraically closed ground field is irreducible. -/
private lemma isIrreducible_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZc : IsClosed Z) (hZ : IsIrreducible Z) : IsIrreducible (p ⁻¹' Z) := by
  let C : TopologicalSpace.Closeds X := ⟨Z, hZc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible C hZ
  have : LocallyOfFiniteType (I.subschemeι ≫ f) := inferInstance
  have hsq : IsPullback (pullback.snd p I.subschemeι) (pullback.fst p I.subschemeι ≫ s)
      (I.subschemeι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (IsPullback.of_hasPullback p I.subschemeι).flip.paste_vert h
  obtain ⟨-, hint, -⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) (I.subschemeι ≫ f)
  have : IsIntegral (pullback (I.subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) := hint.1 ‹_›
  have : IsIntegral (pullback p I.subschemeι) :=
    MMP.isIntegral_of_iso hsq.isoPullback.symm
  have hr : Set.range (pullback.fst p I.subschemeι) = p ⁻¹' Z := by
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- Under a base change of an algebraically closed ground field of an integral scheme, coheights
can only grow, and every point has a preimage of the same coheight (the generic point of its
preimage closure). -/
private lemma coheight_le_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] :
    (∀ w : W, Order.coheight (p w) ≤ Order.coheight w) ∧
      ∀ x : X, ∃ w, p w = x ∧ Order.coheight w ≤ Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X := (invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl (x : X) : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  constructor
  · intro w
    have hsub : closure {w} ⊆ p ⁻¹' closure {p w} :=
      closure_minimal (Set.singleton_subset_iff.mpr (subset_closure rfl))
        (isClosed_closure.preimage p.continuous)
    have hle : topologicalKrullDim (closure {w} : Set W) ≤
        topologicalKrullDim (closure {p w} : Set X) := by
      rw [← hcl]; exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    exact le_of_add_eq_add_of_le (hW w) (hX (p w)) hle
  · intro x
    have hirr := isIrreducible_preimage_of_isPullback f h (isClosed_closure (s := {x}))
      isIrreducible_singleton.closure
    obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage p.continuous)
    have hpw : p w = x := map_eq_of_closure_eq hw.def
    refine ⟨w, hpw, ?_⟩
    have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact le_of_add_eq_add_of_le (hX x) (hW w) heq.ge

/-- The generic point of the preimage of the closure of a point `x` lies over `x` and has the
coheight of `x`. -/
private lemma coheight_eq_of_isGenericPoint_preimage
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] {x : X} {w : W}
    (hw : IsGenericPoint w (p ⁻¹' closure {x})) :
    p w = x ∧ Order.coheight w = Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X := (invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  have hpw : p w = x := map_eq_of_closure_eq hw.def
  refine ⟨hpw, le_antisymm ?_ ?_⟩
  · have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact le_of_add_eq_add_of_le (hX x) (hW w) heq.ge
  · have := (coheight_le_of_isPullback f h).1 w
    rwa [hpw] at this

/-- The base change of a normal variety along an extension of an algebraically closed ground
field is a normal variety. -/
private lemma isNormalVariety_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hv : MMP.Mori.IsNormalVariety k₀ f) : MMP.Mori.IsNormalVariety K s := by
  obtain ⟨hn, hi, -⟩ := invariants_of_isPullback f h
  have := hv.1.toIsIntegral
  exact ⟨{ toIsIntegral := hi.1 ‹_›
           toIsSeparated := MorphismProperty.of_isPullback (P := @IsSeparated) h
             hv.1.toIsSeparated
           toLocallyOfFiniteType :=
             MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
           toQuasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) h
             hv.1.toQuasiCompact }, hn.1 hv.2⟩

end Square

section Helpers

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-! ### Varieties and morphisms -/

/-- A morphism of finite type over `k₀` whose base change to `K` is H-projective is
H-projective. -/
private lemma isProjectiveMorphism_of_isPullback {X₀ X : Scheme.{u}}
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    [LocallyOfFiniteType s₀] [QuasiCompact s₀] (hs : IsProjectiveMorphism s) :
    IsProjectiveMorphism s₀ := by
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  have hY : Stacks.HProjective.IsQuasiProjective (𝟙 (Spec (.of k₀))) :=
    (isQuasiProjective_iff_hProjectiveIsQuasiProjective _).mp
      (isProjectiveMorphism_id _).isQuasiProjective
  have : LocallyOfFiniteType (s₀ ≫ 𝟙 _) := by rw [Category.comp_id]; infer_instance
  have : QuasiCompact (s₀ ≫ 𝟙 _) := by rw [Category.comp_id]; infer_instance
  haveI := Stacks.Ample.isInvertibleModule_unit X₀
  have key := (MMP.isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension k₀ K
    (𝟙 _) s₀ hY (Stacks.Ample.unitModule X₀)).2
  refine key.2 ?_
  set q := pullback.fst (𝟙 (Spec (.of k₀))) φ
  have hsq1 : IsPullback (pullback.fst s₀ q) (pullback.snd s₀ q) s₀ q :=
    IsPullback.of_hasPullback s₀ q
  have hsq2 : IsPullback q (pullback.snd (𝟙 _) φ) (𝟙 _) φ := IsPullback.of_hasPullback _ _
  have hsq := hsq1.paste_vert hsq2
  rw [Category.comp_id] at hsq
  let e : X ≅ pullback s₀ q := h.isoIsPullback _ _ hsq
  have : IsIso (pullback.snd (𝟙 (Spec (.of k₀))) φ) := inferInstance
  refine IsProjectiveMorphism.of_iso e (asIso (pullback.snd (𝟙 (Spec (.of k₀))) φ)).symm ?_ hs
  rw [Iso.symm_hom, asIso_inv, IsIso.eq_comp_inv, Category.assoc]
  exact h.isoIsPullback_hom_snd _ _ hsq

/-- Projectivity of a variety is unchanged by base change along `Spec K ⟶ Spec k₀`. -/
private theorem isProjectiveVariety_iff_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) :
    MMP.Mori.IsProjectiveVariety k₀ s₀ ↔ MMP.Mori.IsProjectiveVariety K s := by
  have hφ := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  simp only [MMP.Mori.isProjectiveVariety_iff, MMP.Mori.isVariety_iff]
  constructor
  · rintro ⟨⟨hi, hsep, hlft, hqc⟩, hp⟩
    have hint := (invariants_of_isPullback s₀ h).2.1
    have : IsProjectiveMorphism (h.isoPullback.hom ≫ pullback.snd s₀ _) :=
      IsProjectiveMorphism.iso_comp _ (hp.baseChange _)
    rw [h.isoPullback_hom_snd] at this
    exact ⟨⟨hint.1 hi, MorphismProperty.of_isPullback (P := @IsSeparated) h hsep,
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h hlft,
      MorphismProperty.of_isPullback (P := @QuasiCompact) h hqc⟩, this⟩
  · rintro ⟨⟨hi, hsep, hlft, hqc⟩, hp⟩
    have : LocallyOfFiniteType s₀ :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hφ hlft
    have : QuasiCompact s₀ :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) h.flip hφ hqc
    have hp₀ := isProjectiveMorphism_of_isPullback h hp
    have := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hp₀).2
    exact ⟨⟨(invariants_of_isPullback s₀ h).2.1.2 hi, inferInstance, inferInstance,
      inferInstance⟩, hp₀⟩

/-- Dimension is unchanged by base change along `Spec K ⟶ Spec k₀`. -/
private theorem topologicalKrullDim_eq_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) :
    topologicalKrullDim X = topologicalKrullDim X₀ := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  exact (invariants_of_isPullback s₀ h).2.2

/-! ### Prime divisors under base change -/

/-- The base change of a prime divisor: `π⁻¹(closure P₀)` is the closure of the generic point of a
prime divisor of `X`, lying over the generic point of `P₀`. -/
private theorem exists_primeDivisor_baseChange {X₀ X : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P₀ : MMP.Mori.PrimeDivisor X₀) :
    ∃ P : MMP.Mori.PrimeDivisor X, closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} ∧
      π P.genericPoint = P₀.genericPoint := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := surjective_of_isPullback h
  set x := P₀.genericPoint
  have hirr := isIrreducible_preimage_of_isPullback s₀ h (isClosed_closure (s := {x}))
    isIrreducible_singleton.closure
  obtain ⟨w, hw⟩ := QuasiSober.sober hirr (isClosed_closure.preimage π.continuous)
  have hpw : π w = x := map_eq_of_closure_eq hw.def
  obtain ⟨h1, h2⟩ := coheight_le_of_isPullback s₀ h
  obtain ⟨w', hw'x, hw'⟩ := h2 x
  have hww' : w ⤳ w' := by
    rw [specializes_iff_mem_closure, hw.def]
    show π w' ∈ closure {x}
    rw [hw'x]; exact subset_closure rfl
  have hcoh : Order.coheight w = 1 := by
    have hx1 : Order.coheight x = 1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₀
    have hle : Order.coheight w ≤ Order.coheight w' := Order.coheight_anti hww'
    refine le_antisymm (hle.trans (hw'.trans hx1.le)) ?_
    rw [← hx1, ← hpw]
    exact h1 w
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh, ?_, ?_⟩
  · change closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint} = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hw.def
  · change π (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hpw

/-- Every proper curve on `X` is numerically equivalent to the base change of a proper curve on
`X₀`. -/
private theorem exists_properCurve_numericalClass_eq {X₀ X : Scheme.{u}}
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (C : ProperCurve s) :
    ∃ (C₀ : ProperCurve s₀) (C₀K : ProperCurve s),
      closure {C₀K.point} = π.base ⁻¹' closure {C₀.point} ∧
      OneCycle.numericalClass s (C₀K.cycle ℝ) = OneCycle.numericalClass s (C.cycle ℝ) ∧
      ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
        C₀K.degree K L = C.degree K L := by
  obtain ⟨C₀, C₀K, hcl, hdeg⟩ := exists_properCurve_degree_eq_of_isPullback s₀ s π h hX₀ C
  refine ⟨C₀, C₀K, hcl, ?_, hdeg⟩
  rw [OneCycle.numericalClass_eq_iff]
  intro L _
  rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hdeg L]

/-! ### Birational transforms of prime divisors under base change -/

section Transforms

open TopologicalSpace

/-- **Prime divisors over a point of codimension one are base changes.** A prime divisor of the
base change `X` whose generic point does not lie over the generic point of `X₀` is the base
change of a prime divisor of `X₀`. -/
private theorem exists_closure_eq_of_map_ne_genericPoint {X₀ X : Scheme.{u}} [IsIntegral X₀]
    [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P : MMP.Mori.PrimeDivisor X) (hP : π P.genericPoint ≠ genericPoint X₀) :
    ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := surjective_of_isPullback h
  obtain ⟨h1, -⟩ := coheight_le_of_isPullback s₀ h
  have hP1 : Order.coheight P.genericPoint = 1 :=
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P
  have hx : Order.coheight (π P.genericPoint) = 1 := by
    refine le_antisymm (hP1 ▸ h1 _) ?_
    have hgen : genericPoint X₀ ⤳ π P.genericPoint := (genericPoint_spec X₀).specializes trivial
    have hle : π P.genericPoint ≤ genericPoint X₀ := hgen
    have hlt : π P.genericPoint < genericPoint X₀ :=
      lt_of_le_not_ge hle fun h' => hP (hgen.antisymm h').eq.symm
    exact le_add_self.trans (Order.coheight_add_one_le hlt)
  obtain ⟨P', hP'c, hP'π⟩ := exists_primeDivisor_baseChange h
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx)
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx, ?_⟩
  have hgp : (AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π P.genericPoint) hx).genericPoint =
      π P.genericPoint := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hsp : P'.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, hP'c, Set.mem_preimage]
    change π P.genericPoint ∈ closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne
      (π P.genericPoint) hx).genericPoint}
    rw [hgp]; exact subset_closure rfl
  have heq := eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P') hP1
  rw [← hP'c, heq]

end Transforms

open RingedSpaceModuleAdjunction in
/-- `𝒪_Y(nL) ≅ 𝒪_Y(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {L : Divisor Y} (hL : L.IsCartier) (n : ℕ) (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule Y L.divisorialSheaf (n : ℤ)) := by
  have := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso Y _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso Y _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso Y _).symm

open RingedSpaceModuleAdjunction in
/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso hL n hn
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

section Model

variable {X₀ X : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
  [IsNormal X₀] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is the base change of `L₀`. -/
private theorem isBaseChange_pullback
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    [LocallyOfFiniteType s₀] {L₀ : Divisor X₀} (hL₀ : L₀.IsCartier)
    (hB : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ L₀.supp) :
    IsBaseChange π L₀ (L₀.pullback hL₀ hB) := by
  have : Surjective π := surjective_of_isPullback h
  have : IsDominant π := inferInstance
  have hL := Divisor.isPullback_pullback hL₀ hB
  refine ⟨fun P₀ P hP => ?_, fun P hP => ?_⟩
  · have hπ : π P.genericPoint = P₀.genericPoint := map_eq_of_closure_eq hP
    obtain ⟨U, hU, φ, hφ⟩ := hL₀ P₀.genericPoint
    have hE : (P.support ∩ π ⁻¹ᵁ U).Nonempty :=
      (P.genericPoint_mem_iff (π ⁻¹ᵁ U)).mp (show π P.genericPoint ∈ U by rw [hπ]; exact hU)
    have h1 := MMP.Fourfold.valuation_fieldMap_of_isPullback π hL hφ P hE P₀.component
    rw [valuation_fieldMap_of_closure_eq h hP, P₀.valuation_component,
      ← hφ P₀ ((P₀.genericPoint_mem_iff U).mp hU)] at h1
    exact (WithZero.exp_injective h1).symm
  · by_contra hne
    have hgen : π P.genericPoint = genericPoint X₀ := by
      by_contra hg
      exact hne (exists_closure_eq_of_map_ne_genericPoint h P hg)
    obtain ⟨U, hU, φ, hφ⟩ := hL₀ (π P.genericPoint)
    have hE : (P.support ∩ π ⁻¹ᵁ U).Nonempty := (P.genericPoint_mem_iff (π ⁻¹ᵁ U)).mp hU
    obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X₀) := ⟨pointComponent (genericPoint X₀)⟩
    have h1 := MMP.Fourfold.valuation_fieldMap_of_isPullback π hL hφ P hE Z₀
    have hu : IsUnit ((φ : RationalFunctions X₀) Z₀) :=
      φ.isUnit.map (RationalFunctions.component X₀ Z₀)
    rw [valuation_fieldMap_eq_one hgen Z₀ hu] at h1
    apply hP
    have := WithZero.exp_injective (h1.symm.trans WithZero.exp_zero.symm)
    exact this

/-- **Base change of Cartier divisors.** The pull-back of a Cartier divisor `L₀` to the base change
is a Cartier divisor which is the base change of `L₀`, and its sheaf is the pull-back of
`𝒪_{X₀}(L₀)`. -/
private theorem exists_isBaseChange_of_isCartier
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {L₀ : Divisor X₀} (hL₀ : L₀.IsCartier) :
    ∃ L : Divisor X, L.IsCartier ∧ IsBaseChange π L₀ L ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback π).obj L₀.divisorialSheaf) := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : Surjective π := surjective_of_isPullback h
  have : IsDominant π := inferInstance
  have hB : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ L₀.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant π L₀
  exact ⟨L₀.pullback hL₀ hB, Divisor.IsCartier.isCartier_pullback hL₀ π hB,
    isBaseChange_pullback h hL₀ hB, Divisor.nonempty_divisorialSheaf_pullback_iso hL₀ π hB⟩

/-- Equality of base-changed divisors is detected over `k₀`. -/
private theorem eq_iff_of_isBaseChange {R : Type*} [Zero R]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    [hs₀ : LocallyOfFiniteType s₀] {D₀ E₀ : DivisorWithCoeffs R X₀}
    {D E : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) (hE : IsBaseChange π E₀ E) :
    D₀ = E₀ ↔ D = E := by
  constructor
  · rintro rfl
    ext P
    change D P = E P
    by_cases hP : D P = 0 ∧ E P = 0
    · rw [hP.1, hP.2]
    · obtain ⟨P₀, hP₀⟩ : ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
          closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
        by_cases hD0 : D P = 0
        · exact hE.2 P fun h0 => hP ⟨hD0, h0⟩
        · exact hD.2 P hD0
      rw [hD.1 P₀ P hP₀, hE.1 P₀ P hP₀]
  · intro hDE
    ext P₀
    change D₀ P₀ = E₀ P₀
    obtain ⟨P, hP, -⟩ := exists_primeDivisor_baseChange h P₀
    rw [← hD.1 P₀ P hP, ← hE.1 P₀ P hP, hDE]

/-- **Curve forms are detected over `k₀`.** On the base change `C` of a proper curve `C₀`, the
curve form of the base change of a `ℚ`-Cartier divisor is that of the divisor on `C₀`. -/
private theorem curveForm_numericalClass_eq_of_isBaseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D) (hD₀ : D₀.IsQCartier) (hD' : D.IsQCartier)
    (C₀ : ProperCurve s₀) (C : ProperCurve s)
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
    QDivisor.curveForm s D hD' (OneCycle.numericalClass s (C.cycle ℝ)) =
      QDivisor.curveForm s₀ D₀ hD₀ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) := by
  haveI : QuasiCompact s₀ := hX₀.toQuasiCompact
  haveI : QuasiCompact s := MorphismProperty.of_isPullback h hX₀.toQuasiCompact
  obtain ⟨m, hm, L₀, hL₀, hL₀c⟩ := hD₀.exists_pos
  obtain ⟨L, hLc, hLb, ⟨eL⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hL₀c
  have hL : Divisor.toQDivisor L = ((m : ℤ) • D) :=
    (eq_iff_of_isBaseChange (hs₀ := hX₀.toLocallyOfFiniteType) h hLb.toQDivisor
      (hD.zsmul m)).mp hL₀
  rw [curveForm_numericalClass_cycle, curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul K s C.ι C.dim_le
      (Divisor.degreeOn_add K s C.ι C.dim_le) D hD' hm L hLc hL,
    QDivisor.intersectionNumber_eq_of_toQDivisor_eq_smul k₀ s₀ C₀.ι C₀.dim_le
      (Divisor.degreeOn_add k₀ s₀ C₀.ι C₀.dim_le) D₀ hD₀ hm L₀ hL₀c hL₀]
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hL₀c.isInvertibleModule_divisorialSheaf
  rw [← ProperCurve.degree_divisorialSheaf C L hLc, ← ProperCurve.degree_divisorialSheaf C₀ L₀ hL₀c,
    degree_congr C eL]
  congr 3
  exact degree_pullback_eq_of_closure_eq s₀ s π h hC _

/-- Negative extremal rays are detected over `k₀`, the ray being transported by `φ`. -/
private theorem isNegativeExtremalRayOf_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {D₀ : QDivisor X₀} {D : QDivisor X}
    (hD : IsBaseChange π D₀ D) (hQD₀ : D₀.IsQCartier) (hQD : D.IsQCartier)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsNegativeExtremalRayOf s₀ D₀ R₀ ↔ IsNegativeExtremalRayOf s D (φ '' R₀) := by
  have hQ : D₀.IsQCartier ↔ D.IsQCartier := ⟨fun _ => hQD, fun _ => hQD₀⟩
  let e := numericalCurveClassesBaseChange s₀ s π h hX₀
  have he := numericalCurveClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  have hφe : φ = e.toLinearMap := linearMap_ext_numericalClass_cycle s₀ fun C₀ => by
    obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
    rw [hφ C₀ C hC, LinearEquiv.coe_coe, he C₀ C hC]
  have hcone : (closedConeOfCurves s : Set (NumericalCurveClasses s)) =
      e '' (closedConeOfCurves s₀ : Set (NumericalCurveClasses s₀)) := by
    rw [← map_closedConeOfCurves_eq_of_isPullback s₀ s π h hX₀ φ hφ, PointedCone.coe_map, hφe,
      LinearEquiv.coe_coe]
  have hRim : φ '' R₀ = e '' R₀ := by rw [hφe, LinearEquiv.coe_coe]
  have hform (hD₀ : D₀.IsQCartier) (hD' : D.IsQCartier) (u : NumericalCurveClasses s₀) :
      QDivisor.curveForm s D hD' (e u) = QDivisor.curveForm s₀ D₀ hD₀ u := by
    have := linearMap_ext_numericalClass_cycle s₀
      (φ := (QDivisor.curveForm s D hD').comp e.toLinearMap)
      (ψ := QDivisor.curveForm s₀ D₀ hD₀) fun C₀ => by
        obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, he C₀ C hC]
        exact curveForm_numericalClass_eq_of_isBaseChange h hX₀ hD hD₀ hD' C₀ C hC
    exact congrArg (fun F : NumericalCurveClasses s₀ →ₗ[ℝ] ℝ => F u) this
  rw [hRim]
  constructor
  · rintro ⟨hD₀, hext, hneg⟩
    refine ⟨hQ.mp hD₀, ?_, ?_⟩
    · rw [hcone]; exact isExtremalRay_image e hext
    · rintro _ ⟨u, hu, rfl⟩ hne
      rw [hform hD₀]
      exact hneg u hu fun h0 => hne (by rw [h0, map_zero])
  · rintro ⟨hD', hext, hneg⟩
    refine ⟨hQ.mpr hD', ?_, ?_⟩
    · rw [hcone] at hext; exact (isExtremalRay_image_iff e).mp hext
    · intro u hu hne
      rw [← hform (hQ.mpr hD') hD']
      exact hneg (e u) ⟨u, hu, rfl⟩ fun h0 => hne (e.injective (h0.trans (map_zero e).symm))

variable {Z₀ Z : Scheme.{u}} {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀}

/-- Relative Picard numbers are unchanged by base change: the base-change isomorphism
`N¹(X₀)_ℝ ≃ N¹(X)_ℝ` carries `f₀^* N¹(Z₀)_ℝ` onto `f^* N¹(Z)_ℝ`. -/
private theorem relativePicardNumberN1_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    relativePicardNumberN1 s₀ f₀ = relativePicardNumberN1 s f := by
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hv₀ : AlgebraicGeometry.IsVariety k₀ t₀ := hZ₀.toIsVariety
  haveI : IsIntegral Z₀ := hv₀.toIsIntegral
  haveI : IsIntegral Z := hZK.toIsVariety.toIsIntegral
  haveI : IsSeparated t := MorphismProperty.of_isPullback hZ hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t := MorphismProperty.of_isPullback hZ hv₀.toLocallyOfFiniteType
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.flip hφsurj.1.1
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  haveI : IsDominant π := inferInstance
  haveI : IsDominant πZ := inferInstance
  let e := numericalDivisorClassesBaseChange s₀ s π h hX₀
  have he := numericalDivisorClassesBaseChange_eq_of_isPullback s₀ s π h hX₀
  let eZ := numericalDivisorClassesBaseChange t₀ t πZ hZ hZ₀
  have heZ := numericalDivisorClassesBaseChange_eq_of_isPullback t₀ t πZ hZ hZ₀
  -- chosen lifts of Cartier divisors
  choose pX hpX using exists_isPullback s₀ s π h hX₀
  choose pZ hpZ using exists_isPullback t₀ t πZ hZ hZ₀
  have hq (G : Z₀.CartierDivisor) := exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f₀).obj (MMP.CartierDivisor.sheaf G))
  choose q hq using hq
  have hqK (G : Z.CartierDivisor) := exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf G))
  choose qK hqK using hqK
  have hsh (D₀ : X₀.CartierDivisor) : Nonempty (MMP.CartierDivisor.sheaf (pX D₀) ≅
      (Scheme.Modules.pullback π).obj (MMP.CartierDivisor.sheaf D₀)) :=
    ⟨(nonempty_pullback_sheaf_iso π (hpX D₀)).some.symm⟩
  have hshZ (G : Z₀.CartierDivisor) : Nonempty (MMP.CartierDivisor.sheaf (pZ G) ≅
      (Scheme.Modules.pullback πZ).obj (MMP.CartierDivisor.sheaf G)) :=
    ⟨(nonempty_pullback_sheaf_iso πZ (hpZ G)).some.symm⟩
  -- `f^* πZ^* = π^* f₀^*`
  have hcomm (M : Z₀.Modules) : (Scheme.Modules.pullback f).obj
      ((Scheme.Modules.pullback πZ).obj M) ≅
        (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback f₀).obj M) :=
    (Scheme.Modules.pullbackComp f πZ).app M ≪≫ (Scheme.Modules.pullbackCongr hfπ).app M ≪≫
      ((Scheme.Modules.pullbackComp π f₀).app M).symm
  have hcomp : e.toLinearMap ∘ₗ numericalDivisorClass s₀ =
      numericalDivisorClass s ∘ₗ Finsupp.lmapDomain ℝ ℝ pX := by
    ext D₀
    simpa [KCartierDivisor.ofCartier] using he D₀ (pX D₀) (hpX D₀)
  -- the classes of the lifts `q c₀` lie in `f₀^* N¹(Z₀)`
  have h4 (c₀ : KCartierDivisor ℝ Z₀) : numericalDivisorClass s₀ (Finsupp.lmapDomain ℝ ℝ q c₀) ∈
      pullbackNumericalClasses s₀ f₀ := by
    induction c₀ using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
    | single G r =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ← mul_one r, ← smul_eq_mul,
        ← Finsupp.smul_single, map_smul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨q G,
        MMP.CartierDivisor.sheaf G, inferInstance, ⟨(hq G).some.symm⟩, rfl⟩)
  have key : (pullbackNumericalClasses s₀ f₀).map e.toLinearMap = pullbackNumericalClasses s f := by
    apply le_antisymm
    · rw [pullbackNumericalClasses, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨E₀, M₀, hM₀, ⟨σ⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨pX E₀, (Scheme.Modules.pullback πZ).obj M₀, inferInstance,
        ⟨(hsh E₀).some ≪≫ (Scheme.Modules.pullback π).mapIso σ ≪≫ (hcomm M₀).symm⟩,
        he E₀ (pX E₀) (hpX E₀)⟩
    · rw [pullbackNumericalClasses, Submodule.span_le]
      rintro _ ⟨E, M, hM, ⟨σ⟩, rfl⟩
      obtain ⟨EM, ⟨τ⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf M
      obtain ⟨c₀, hc₀⟩ := exists_numericalDivisorClass_eq_lmapDomain pZ eZ
        (fun G => heZ G (pZ G) (hpZ G)) (KCartierDivisor.ofCartier ℝ EM)
      -- `[E] = [qK EM]`
      have hlm (p : Z.CartierDivisor → X.CartierDivisor) (G : Z.CartierDivisor) :
          Finsupp.lmapDomain ℝ ℝ p (KCartierDivisor.ofCartier ℝ G) =
            KCartierDivisor.ofCartier ℝ (p G) := by
        simp [KCartierDivisor.ofCartier, Finsupp.lmapDomain_apply]
      have h1 : numericalDivisorClass s (KCartierDivisor.ofCartier ℝ E) =
          numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ qK (KCartierDivisor.ofCartier ℝ EM)) := by
        rw [hlm]
        refine numericalDivisorClass_eq_of_forall fun C => ?_
        rw [intersectionNumber_cycle_ofCartier, intersectionNumber_cycle_ofCartier,
          degree_congr C (σ ≪≫ (Scheme.Modules.pullback f).mapIso τ ≪≫ (hqK EM).some)]
      -- `[qK EM] = [qK (pZ c₀)]`
      have h2 := numericalDivisorClass_lmapDomain_eq_of_forall f hf qK
        (fun G => ⟨(hqK G).some.symm⟩) (intersectionNumber_eq_of_numericalDivisorClass_eq' hc₀)
      -- `[qK (pZ c₀)] = [pX (q c₀)]`
      have h3 : numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ qK
            (Finsupp.lmapDomain ℝ ℝ pZ c₀)) =
          numericalDivisorClass s (Finsupp.lmapDomain ℝ ℝ pX (Finsupp.lmapDomain ℝ ℝ q c₀)) := by
        have e1 : Finsupp.lmapDomain ℝ ℝ qK (Finsupp.lmapDomain ℝ ℝ pZ c₀) =
            Finsupp.lmapDomain ℝ ℝ (qK ∘ pZ) c₀ := by
          simp only [Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_comp.symm
        have e2 : Finsupp.lmapDomain ℝ ℝ pX (Finsupp.lmapDomain ℝ ℝ q c₀) =
            Finsupp.lmapDomain ℝ ℝ (pX ∘ q) c₀ := by
          simp only [Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_comp.symm
        rw [e1, e2]
        exact numericalDivisorClass_lmapDomain_eq _ _ (fun G =>
          ⟨(hqK (pZ G)).some.symm ≪≫ (Scheme.Modules.pullback f).mapIso (hshZ G).some ≪≫
            hcomm _ ≪≫ (Scheme.Modules.pullback π).mapIso (hq G).some ≪≫
            (hsh (q G)).some.symm⟩) c₀
      refine ⟨_, h4 c₀, ?_⟩
      change e.toLinearMap _ = _
      rw [← LinearMap.comp_apply, hcomp, LinearMap.comp_apply, ← h3, ← h2, h1]
  unfold relativePicardNumberN1
  exact congrArg Cardinal.toENat
    (Submodule.Quotient.equiv _ _ e key).rank_eq

/-- Relatively ample multiples are detected over `k₀`. -/
private theorem hasRelativelyAmpleMultiple_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) {D₀ : QDivisor X₀} {D : QDivisor X} (hD : IsBaseChange π D₀ D)
    (hQD₀ : D₀.IsQCartier) :
    D₀.HasRelativelyAmpleMultiple f₀ ↔ D.HasRelativelyAmpleMultiple f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  haveI : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  haveI : IsProper f := isProper_of_comp_eq hXK hZK hf
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Flat πZ := MorphismProperty.of_isPullback (P := @Flat) hZ.flip hφsurj.1.2
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  haveI : QuasiCompact πZ := MorphismProperty.of_isPullback (P := @QuasiCompact) hZ.flip hφsurj.2
  have hamp (L₀ : Divisor X₀) (hL₀ : L₀.IsCartier) (L : Divisor X) (hL : L.IsCartier)
      (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback π).obj L₀.divisorialSheaf) :
      L₀.IsRelativelyAmple f₀ hL₀ ↔ L.IsRelativelyAmple f hL := by
    haveI := hL₀.isInvertibleModule_divisorialSheaf
    haveI := hL.isInvertibleModule_divisorialSheaf
    exact isRelativelyAmple_iff_of_isPullback hsq _ _ e
  constructor
  · rintro ⟨m, hm, L₀, hL₀c, hL₀, hA⟩
    obtain ⟨L, hLc, hLb, ⟨eL⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hL₀c
    exact ⟨m, hm, L, hLc, (eq_iff_of_isBaseChange (hs₀ := hX₀.toLocallyOfFiniteType) h
      hLb.toQDivisor (hD.zsmul m)).mp hL₀,
      (hamp L₀ hL₀c L hLc eL).mp hA⟩
  · rintro ⟨m, hm, L, hLc, hL, hA⟩
    obtain ⟨n, hn, N₀, hN₀, hN₀c⟩ := hQD₀.exists_pos
    have hM₀c : (m • N₀).IsCartier := hN₀c.nsmul m
    obtain ⟨M, hMc, hMb, ⟨eM⟩⟩ := exists_isBaseChange_of_isCartier h hX₀ hM₀c
    have hM₀ : Divisor.toQDivisor (m • N₀) = ((n * m : ℕ) : ℤ) • D₀ := by
      rw [map_nsmul, hN₀, ← natCast_zsmul, smul_smul]
      congr 1
      push_cast
      ring
    have hM : Divisor.toQDivisor M = Divisor.toQDivisor (n • L) := by
      rw [(eq_iff_of_isBaseChange (hs₀ := hX₀.toLocallyOfFiniteType) h hMb.toQDivisor
          (hD.zsmul ((n * m : ℕ) : ℤ))).mp hM₀,
        map_nsmul, hL, ← natCast_zsmul, smul_smul]
      congr 1
    have hnL := isRelativelyAmple_nsmul hLc hA n hn
    have hMa : M.IsRelativelyAmple f hMc := by
      obtain rfl := Divisor.toQDivisor_injective hM
      exact hnL
    exact ⟨n * m, Nat.mul_pos hn hm, m • N₀, hM₀c, hM₀, (hamp _ hM₀c M hMc eM).mpr hMa⟩

/-- Projective morphisms are detected over `k₀`. -/
private theorem isProjectiveMorphism_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    IsProjectiveMorphism f₀ ↔ IsProjectiveMorphism f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  constructor
  · intro hp
    have := IsProjectiveMorphism.iso_comp hsq.isoPullback (hp.baseChange πZ)
    rwa [hsq.isoPullback_hom_snd] at this
  · intro hp
    have hY : Stacks.HProjective.IsQuasiProjective t₀ :=
      (isQuasiProjective_iff_hProjectiveIsQuasiProjective _).mp
        ((MMP.Mori.isProjectiveVariety_iff _ _).mp hZ₀).2.isQuasiProjective
    have : LocallyOfFiniteType (f₀ ≫ t₀) := by rw [hf₀]; exact hX₀.toLocallyOfFiniteType
    have : QuasiCompact (f₀ ≫ t₀) := by rw [hf₀]; exact hX₀.toQuasiCompact
    haveI := Stacks.Ample.isInvertibleModule_unit X₀
    refine (MMP.isRelativelyAmple_iff_and_isProjectiveMorphism_iff_of_fieldExtension k₀ K
      t₀ f₀ hY (Stacks.Ample.unitModule X₀)).2.2 ?_
    obtain ⟨e, eZ, he, -, -⟩ := exists_iso_pullback_of_isPullback hsq hZ
    exact IsProjectiveMorphism.of_iso e eZ he hp

/-- Contractions of rays are detected over `k₀`. -/
private theorem isContractionOfRay_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀)
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    (R₀ : Set (NumericalCurveClasses s₀)) :
    IsContractionOfRay s₀ t₀ R₀ f₀ ↔ IsContractionOfRay s t (φ '' R₀) f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hv₀ : AlgebraicGeometry.IsVariety k₀ t₀ := hZ₀.toIsVariety
  haveI : IsSeparated t := MorphismProperty.of_isPullback hZ hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t := MorphismProperty.of_isPullback hZ hv₀.toLocallyOfFiniteType
  haveI : IsSeparated t₀ := hv₀.toIsSeparated
  haveI : LocallyOfFiniteType t₀ := hv₀.toLocallyOfFiniteType
  haveI : QuasiCompact t₀ := hv₀.toQuasiCompact
  haveI : QuasiCompact t := MorphismProperty.of_isPullback hZ hv₀.toQuasiCompact
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : QuasiCompact s₀ := hX₀.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace t
  haveI : IsAffineHom πZ := MorphismProperty.of_isPullback hZ.flip inferInstance
  haveI : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have hφsurj := specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)
  haveI : Surjective πZ := MorphismProperty.of_isPullback (P := @Surjective) hZ.flip hφsurj.1.1
  -- an ample invertible sheaf `H` on `Z₀`, whose pull-back `H_K` to `Z` is ample
  obtain ⟨H, _, hHa⟩ := exists_isAmple_of_isProjectiveVariety hZ₀
  have hHKa : Scheme.Modules.IsAmple Z ((Scheme.Modules.pullback πZ).obj H) :=
    Scheme.Modules.isAmple_pullback_of_isAffineHom πZ H hHa
  have hdegH {C₀ : ProperCurve s₀} {C : ProperCurve s}
      (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
      C.degree K ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H)) =
        C₀.degree k₀ ((Scheme.Modules.pullback f₀).obj H) := by
    have e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H) ≅
        (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback f₀).obj H) :=
      (Scheme.Modules.pullbackComp f πZ).app H ≪≫ (Scheme.Modules.pullbackCongr hfπ).app H ≪≫
        ((Scheme.Modules.pullbackComp π f₀).app H).symm
    rw [degree_congr C e]
    exact degree_pullback_eq_of_closure_eq s₀ s π h hC _
  -- contraction is read off the degree of `f^* H_K`
  have hcontrK (C : ProperCurve s) : C.IsContractedBy f ↔
      C.degree K ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback πZ).obj H)) = 0 :=
    ⟨fun hc => ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf C hc _,
      fun h0 => isContractedBy_of_degree_pullback_eq_zero f hf _ hHKa C h0⟩
  have hcontr {C₀ : ProperCurve s₀} {C : ProperCurve s}
      (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point}) :
      C₀.IsContractedBy f₀ ↔ C.IsContractedBy f := by
    rw [hcontrK, hdegH hC]
    exact ⟨fun hc => ProperCurve.degree_pullback_eq_zero_of_isContractedBy f₀ hf₀ C₀ hc H,
      fun h0 => isContractedBy_of_degree_pullback_eq_zero f₀ hf₀ H hHa C₀ h0⟩
  have hinj : Function.Injective φ := injective_of_map_numericalClass s₀ s π h φ hφ
  -- the contraction conditions
  have hpush := (MMP.Foundations.isPushout_app_pullbackMap_and_isIso_app_iff (K := K) s₀ t₀ f₀
    hf₀).2
  obtain ⟨eX, heX⟩ : ∃ eX : X ≅ pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))),
      eX.hom ≫ pullback.fst _ _ = π ∧ eX.hom ≫ pullback.snd _ _ = s :=
    ⟨h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
  have hw : eX.hom ≫ pullback.map s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) t₀
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) f₀ (𝟙 _) (𝟙 _) (by simp [hf₀])
      (by simp) = f ≫ hZ.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, heX.1, Category.assoc,
        hZ.isoPullback_hom_fst, hfπ]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, heX.2, Category.assoc,
        hZ.isoPullback_hom_snd, hf]
  have hiso : (∀ U : Z₀.Opens, IsIso (f₀.app U)) ↔ ∀ U : Z.Opens, IsIso (f.app U) := by
    rw [hpush]
    exact ⟨fun H U => forall_isIso_app_of_iso eX.symm hZ.isoPullback.symm (by
        rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_comp_inv, Category.assoc, ← hw,
          Iso.inv_hom_id_assoc]) H U,
      fun H U => forall_isIso_app_of_iso eX hZ.isoPullback hw H U⟩
  have hproj := isProjectiveMorphism_iff h hZ hX₀ hZ₀ f₀ hf₀ f hf hfπ
  have hnor := (invariants_of_isPullback t₀ hZ).1
  constructor
  · intro H₀
    refine
      { isNormalVariety_source := isNormalVariety_of_isPullback s₀ h H₀.isNormalVariety_source
        isNormalVariety_target := isNormalVariety_of_isPullback t₀ hZ H₀.isNormalVariety_target
        comp_eq := hf
        isProjectiveMorphism := hproj.1 H₀.isProjectiveMorphism
        surjective := ?_
        isIso_app := hiso.1 H₀.isIso_app
        isContractedBy_iff := fun C => ?_ }
    · haveI : Surjective f₀ := ⟨H₀.surjective⟩
      exact (MorphismProperty.of_isPullback (P := @Surjective) hsq ‹_›).surj
    · obtain ⟨C₀, C₀K, hcl, hcls, hdeg⟩ := exists_properCurve_numericalClass_eq h hX₀ C
      rw [hcontrK, ← hdeg, ← hcontrK, ← hcontr hcl, H₀.isContractedBy_iff C₀, ← hcls,
        ← hφ C₀ C₀K hcl, hinj.mem_set_image]
  · intro H
    refine
      { isNormalVariety_source := ⟨hX₀.toIsVariety, inferInstance⟩
        isNormalVariety_target := ⟨hZ₀.toIsVariety, hnor.2 H.isNormalVariety_target.2⟩
        comp_eq := hf₀
        isProjectiveMorphism := hproj.2 H.isProjectiveMorphism
        surjective := fun z₀ => ?_
        isIso_app := hiso.2 H.isIso_app
        isContractedBy_iff := fun C₀ => ?_ }
    · obtain ⟨z, rfl⟩ := πZ.surjective z₀
      obtain ⟨x, rfl⟩ := H.surjective z
      exact ⟨π x, by rw [← Scheme.Hom.comp_apply, ← hfπ, Scheme.Hom.comp_apply]⟩
    · obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
      rw [hcontr hC, H.isContractedBy_iff C, ← hφ C₀ C hC, hinj.mem_set_image]

/-- Birational morphisms are detected over `k₀`. -/
private theorem isBirationalMorphism_iff
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    [IsNormal Z₀] (f₀ : X₀ ⟶ Z₀) (hf₀ : f₀ ≫ t₀ = s₀) (f : X ⟶ Z) (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀) :
    IsBirationalMorphism f₀ ↔ IsBirationalMorphism f := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral Z := hZK.toIsIntegral
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  have : IsNormal Z := (invariants_of_isPullback t₀ hZ).1.1 ‹_›
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have : IsProper f := isProper_of_comp_eq hXK hZK hf
  have : Surjective πZ := surjective_of_isPullback hZ
  rw [isBirationalMorphism_iff_isIso_fiberToSpecResidueField f₀,
    isBirationalMorphism_iff_isIso_fiberToSpecResidueField f,
    isIso_fiberToSpecResidueField_iff_of_isPullback hsq,
      AlgebraicGeometry.map_genericPoint_of_isDominant πZ]

end Model

end Helpers

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-- The base change of an integral normal scheme of finite type over `k₀` along
`Spec K ⟶ Spec k₀` is a normal integral Noetherian scheme. -/
private theorem isIntegral_isNormal_of_isPullback {X₀ X : Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) [IsNormal X₀] :
    IsIntegral X ∧ CompactSpace X ∧ IsLocallyNoetherian X ∧ IsNormal X := by
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : QuasiCompact s₀ := hX₀.toQuasiCompact
  have : IsIntegral X₀ := hX₀.toIsIntegral
  have hinv := invariants_of_isPullback s₀ h
  have : LocallyOfFiniteType s := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : QuasiCompact s := MorphismProperty.of_isPullback (P := @QuasiCompact) h ‹_›
  exact ⟨hinv.2.1.1 ‹_›, QuasiCompact.compactSpace_of_compactSpace s,
    LocallyOfFiniteType.isLocallyNoetherian s, hinv.1.1 ‹_›⟩

/-- **Base change of divisors.** Every divisor of `X₀` has a base change to `X`. -/
private theorem exists_isBaseChange {R : Type*} [AddCommMonoid R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (D₀ : DivisorWithCoeffs R X₀) : ∃ D : DivisorWithCoeffs R X, IsBaseChange π D₀ D := by
  have : Surjective π := surjective_of_isPullback h
  choose b hb _ using exists_primeDivisor_baseChange h
  have hinj : Function.Injective b := fun P₀ Q₀ e =>
    primeDivisor_eq_of_closure_eq (hb P₀) (e ▸ hb Q₀)
  refine ⟨Finsupp.mapDomain b D₀, fun P₀ P hP => ?_, fun P hP => ?_⟩
  · obtain rfl : b P₀ = P := primeDivisor_eq_of_closure_eq' (hb P₀) hP
    exact Finsupp.mapDomain_apply_of_injective hinj D₀ P₀
  · by_contra hne
    push Not at hne
    exact hP (Finsupp.mapDomain_notin_range D₀ P fun ⟨P₀, e⟩ => hne P₀ (e ▸ hb P₀))

/-- A prime divisor of `X` lying over the generic point of a prime divisor `P₀` of `X₀` is the
base change of `P₀`. -/
private theorem closure_eq_of_map_eq {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {P₀ : MMP.Mori.PrimeDivisor X₀} {P : MMP.Mori.PrimeDivisor X}
    (hP : π P.genericPoint = P₀.genericPoint) :
    closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  obtain ⟨Q, hQ, -⟩ := exists_primeDivisor_baseChange h P₀
  have hsp : Q.genericPoint ⤳ P.genericPoint := by
    rw [specializes_iff_mem_closure, hQ, Set.mem_preimage]
    change π P.genericPoint ∈ closure {P₀.genericPoint}
    rw [hP]
    exact subset_closure rfl
  have heq := eq_of_specializes_of_coheight_eq_one hsp
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  rw [← heq, hQ]

/-- A divisor of `X` is the base change of a divisor `D₀` of `X₀` as soon as its coefficient at a
prime divisor lying over the generic point of a prime divisor `E₀` is that of `D₀` at `E₀`, and
its other coefficients vanish. -/
private theorem isBaseChange_of_forall_map_genericPoint {R : Type*} [Zero R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X}
    (h1 : ∀ (E : MMP.Mori.PrimeDivisor X) (E₀ : MMP.Mori.PrimeDivisor X₀),
      π E.genericPoint = E₀.genericPoint → D.coeff E = D₀.coeff E₀)
    (h2 : ∀ E : MMP.Mori.PrimeDivisor X,
      (∀ E₀ : MMP.Mori.PrimeDivisor X₀, π E.genericPoint ≠ E₀.genericPoint) → D.coeff E = 0) :
    IsBaseChange π D₀ D := by
  have : Surjective π := surjective_of_isPullback h
  refine ⟨fun P₀ P hP => h1 P P₀ (map_eq_of_closure_eq hP), fun P hP => ?_⟩
  by_contra hne
  push Not at hne
  exact hP (h2 P fun E₀ hE => hne E₀ (closure_eq_of_map_eq h hE))

/-- **Base change of divisors restricts to opens.** If `D` is the base change of `D₀` along `π`,
then over an open `U ⊆ X₀` the restriction `D|_{π⁻¹U}` is the base change of `D₀|_U` along
`π|_U`. -/
private theorem isBaseChange_restrictOpen {R : Type*} [Zero R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (U : X₀.Opens) [Nonempty U] [Nonempty (π ⁻¹ᵁ U)] {D₀ : DivisorWithCoeffs R X₀}
    {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) :
    IsBaseChange (π ∣_ U) (DivisorWithCoeffs.restrictOpen U D₀)
      (DivisorWithCoeffs.restrictOpen (π ⁻¹ᵁ U) D) := by
  have hU : IsPullback (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ s) (U.ι ≫ s₀)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (isPullback_morphismRestrict π U).paste_vert h
  have : Surjective π := surjective_of_isPullback h
  have : Surjective (π ∣_ U) := surjective_of_isPullback hU
  have gp {Y : Scheme.{u}} (V : Y.Opens) (W : MMP.Mori.PrimeDivisor V.toScheme) :
      MMP.Mori.PrimeDivisor.genericPoint
        (OpenWeilRestriction.primeDivisorMap V.ι W : MMP.Mori.PrimeDivisor Y) =
          V.ι W.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ W
  have hmap (W : (π ⁻¹ᵁ U).toScheme) : U.ι ((π ∣_ U) W) = π ((π ⁻¹ᵁ U).ι W) :=
    morphismRestrict_base_coe π U W
  refine ⟨fun P₀ P hP => ?_, fun P hP => ?_⟩
  · have h1 : (π ∣_ U) P.genericPoint = P₀.genericPoint := map_eq_of_closure_eq hP
    have h2 : π (MMP.Mori.PrimeDivisor.genericPoint
        (OpenWeilRestriction.primeDivisorMap (π ⁻¹ᵁ U).ι P : MMP.Mori.PrimeDivisor X)) =
          MMP.Mori.PrimeDivisor.genericPoint
            (OpenWeilRestriction.primeDivisorMap U.ι P₀ : MMP.Mori.PrimeDivisor X₀) := by
      rw [gp, gp, ← hmap, h1]
    exact hD.1 _ _ (closure_eq_of_map_eq h h2)
  · obtain ⟨P₀', hP₀'⟩ := hD.2 _ hP
    have h1 : π (MMP.Mori.PrimeDivisor.genericPoint
        (OpenWeilRestriction.primeDivisorMap (π ⁻¹ᵁ U).ι P : MMP.Mori.PrimeDivisor X)) =
          P₀'.genericPoint := map_eq_of_closure_eq hP₀'
    have hmem : (π ⁻¹ᵁ U).ι P.genericPoint ∈ π ⁻¹ᵁ U := by
      have : (π ⁻¹ᵁ U).ι P.genericPoint ∈ Set.range (π ⁻¹ᵁ U).ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    have hP₀U : P₀'.genericPoint ∈ Set.range U.ι := by
      rw [Scheme.Opens.range_ι, ← h1, gp]
      exact hmem
    obtain ⟨P₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι P₀').mpr hP₀U
    refine ⟨P₀, closure_eq_of_map_eq hU ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [hmap, ← gp (π ⁻¹ᵁ U) P, h1, gp]

end BaseChange

section Iso

variable {k : Type u} [Field k] {X Z Z' : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] (sX : X ⟶ Spec (.of k))

/-- The relative Picard number does not see an isomorphism of the target. -/
private theorem relativePicardNumberN1_comp_iso (f : X ⟶ Z) (e : Z ≅ Z') :
    relativePicardNumberN1 sX (f ≫ e.hom) = relativePicardNumberN1 sX f := by
  have key : pullbackNumericalClasses sX (f ≫ e.hom) = pullbackNumericalClasses sX f := by
    unfold pullbackNumericalClasses
    congr 1
    ext d
    constructor
    · rintro ⟨E, M, hM, ⟨σ⟩, rfl⟩
      haveI := MMP.Mori.isInvertible_pullback_obj e.hom M
      exact ⟨E, (Scheme.Modules.pullback e.hom).obj M, inferInstance,
        ⟨σ ≪≫ ((Scheme.Modules.pullbackComp f e.hom).app M).symm⟩, rfl⟩
    · rintro ⟨E, M, hM, ⟨σ⟩, rfl⟩
      haveI := MMP.Mori.isInvertible_pullback_obj e.inv M
      refine ⟨E, (Scheme.Modules.pullback e.inv).obj M, inferInstance, ⟨σ ≪≫ ?_⟩, rfl⟩
      exact (Scheme.Modules.pullback f).mapIso (((Scheme.Modules.pullbackId Z).app M).symm ≪≫
        (Scheme.Modules.pullbackCongr e.hom_inv_id.symm).app M ≪≫
        ((Scheme.Modules.pullbackComp e.hom e.inv).app M).symm) ≪≫
        (Scheme.Modules.pullbackComp f e.hom).app _
  unfold relativePicardNumberN1
  rw [key]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- Relative ampleness of an invertible sheaf does not see an isomorphism of the target. -/
private theorem isRelativelyAmple_comp_iso (f : X ⟶ Z) (e : Z ≅ Z') (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    MMP.Mori.IsRelativelyAmple (f ≫ e.hom) L ↔ MMP.Mori.IsRelativelyAmple f L := by
  constructor
  · intro h y
    obtain ⟨V, hV, hyV, hA⟩ := h (e.hom y)
    exact ⟨e.hom ⁻¹ᵁ V, hV.preimage e.hom, hyV, hA⟩
  · intro h y
    obtain ⟨V, hV, hyV, hA⟩ := h (e.inv y)
    refine ⟨e.inv ⁻¹ᵁ V, hV.preimage e.inv, hyV, ?_⟩
    have hW : f ⁻¹ᵁ V = (f ≫ e.hom) ⁻¹ᵁ e.inv ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]
    have key : ∀ U U' : X.Opens, U = U' →
        Stacks.Ample.IsAmple U.toScheme
          ((RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj L) →
        Stacks.Ample.IsAmple U'.toScheme
          ((RingedSpaceModuleAdjunction.modulePullback U'.ι.toLRSHom.toShHom).obj L) := by
      rintro U _ rfl hU
      exact hU
    exact key _ _ hW hA

/-- Relative ampleness does not see an isomorphism of the target. -/
private theorem hasRelativelyAmpleMultiple_comp_iso (D : QDivisor X) (f : X ⟶ Z) (e : Z ≅ Z') :
    D.HasRelativelyAmpleMultiple (f ≫ e.hom) ↔ D.HasRelativelyAmpleMultiple f := by
  unfold QDivisor.HasRelativelyAmpleMultiple
  refine exists_congr fun m => and_congr_right fun _ => exists_congr fun L =>
    exists_congr fun hL => and_congr_right fun _ => ?_
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact isRelativelyAmple_comp_iso f e _

end Iso

private theorem isQCartier_of_isLogCanonicalPair {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {K : Divisor X} {B : QDivisor X}
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    (Divisor.toQDivisor K + B).IsQCartier := by
  obtain ⟨n, hn⟩ := hK
  obtain ⟨m, K', hK', hQ⟩ := hlc.1.isQCartier_of_linearlyEquivalent
  exact hQ K (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hlc.1.1 hn hK')

/-- The models of the program without steps are all `X`. -/
private def constSeqHom {X₀ X : Scheme.{u}} (π : X ⟶ X₀) :
    ∀ i, modelSeq X (fun _ => X) i ⟶ modelSeq X₀ (fun _ => X₀) i
  | 0 => π
  | _ + 1 => π

/-- The identification of the models of the program without steps with `X`. -/
private def constSeqTo (X : Scheme.{u}) : ∀ i, modelSeq X (fun _ => X) i ⟶ X
  | 0 => 𝟙 X
  | _ + 1 => 𝟙 X

/-- The program from `(X, B)` with no step and no final contraction. -/
private def trivialProgram {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) : Program sX K B where
  n := 0
  Y _ := X
  sY _ := sX
  KY _ := K
  BY _ := B
  R _ := ∅
  Z _ := X
  sZ _ := sX
  f := constSeqTo X
  fp _ := 𝟙 X
  isProjectiveVariety := hproj
  isLogCanonicalPair := hlc
  isCanonicalDivisor := hK
  isPermittedStep i hi := absurd hi (by simp)
  KY_eq i hi := absurd hi (by simp)
  BY_eq i hi := absurd hi (by simp)
  hasFinal := False
  finalRay := ∅
  T := X
  sT := sX
  g := constSeqTo X _
  final_spec h := h.elim

/-- **Descent of the pair.** A projective lc pair over `k` is the base change of a projective lc
pair over a countable algebraically closed subfield `k₀ ⊆ k`, with base-changed canonical divisor
and boundary. -/
private theorem exists_descent {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hproj : MMP.Mori.IsProjectiveVariety k sX) (hlc : MMP.Intersection.IsLogCanonicalPair sX B)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀)
      (X₀ : Scheme.{0}) (_ : IsIntegral X₀) (_ : CompactSpace X₀) (_ : IsLocallyNoetherian X₀)
      (_ : IsNormal X₀) (s₀ : X₀ ⟶ Spec (.of k₀)) (K₀ : Divisor X₀) (B₀ : QDivisor X₀)
      (π : X ⟶ X₀),
      IsPullback π sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
      MMP.Mori.IsProjectiveVariety k₀ s₀ ∧ MMP.Intersection.IsLogCanonicalPair s₀ B₀ ∧
      (∃ n : ℕ, K₀.IsCanonicalDivisor s₀ n) ∧ IsBaseChange π K₀ K ∧ IsBaseChange π B₀ B := by
  obtain ⟨k₀, hc, ha, X₀, _, _, _, _, s₀, K₀, B₀, P₀, -, πX, -, -, h0, -, -, -⟩ :=
    (trivialProgram hproj hlc hK).exists_countable_isAlgClosed_subfield_program
  obtain ⟨hpb, hcoef, hzero⟩ := h0 0 (by simp [trivialProgram])
  have hpb' : IsPullback (πX 0) sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) := hpb
  have hproj₀ : MMP.Mori.IsProjectiveVariety k₀ s₀ := P₀.isProjectiveVariety
  haveI : LocallyOfFiniteType s₀ := hproj₀.toLocallyOfFiniteType
  exact ⟨k₀, hc, ha, X₀, inferInstance, inferInstance, inferInstance, inferInstance, s₀, K₀, B₀,
    πX 0, hpb', hproj₀, P₀.isLogCanonicalPair, P₀.isCanonicalDivisor,
    isBaseChange_of_forall_map_genericPoint (s₀ := s₀) hpb' (fun E E₀ hE => (hcoef E E₀ hE).1)
      fun E hE => (hzero E hE).1,
    isBaseChange_of_forall_map_genericPoint (s₀ := s₀) hpb' (fun E E₀ hE => (hcoef E E₀ hE).2)
      fun E hE => (hzero E hE).2⟩

/-! ### One step as a program -/

section OneStep

/-- The morphisms `f, f⁺, f⁺, …` out of the models `X, X⁺, X⁺, …` of a one-step program. -/
private def stepSeqHom {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∀ i, modelSeq X (fun _ => Y) i ⟶ Z
  | 0 => f
  | _ + 1 => g

/-- The maps `π, π⁺, π⁺, …` between the models of two one-step programs. -/
private def stepSeqMap {X₀ X Y₀ Y : Scheme.{u}} (π : X ⟶ X₀) (πY : Y ⟶ Y₀) :
    ∀ i, modelSeq X (fun _ => Y) i ⟶ modelSeq X₀ (fun _ => Y₀) i
  | 0 => π
  | _ + 1 => πY

private lemma eq_zero_of_lt_one {i : ℕ} (hi : (i : ℕ∞) < 1) : i = 0 := by
  have : i < 1 := by exact_mod_cast hi
  omega

private lemma eq_zero_or_eq_one_of_le_one {i : ℕ} (hi : (i : ℕ∞) ≤ 1) : i = 0 ∨ i = 1 := by
  have : i ≤ 1 := by exact_mod_cast hi
  omega

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
  [CharZero k₀]

/-- **Base change of a permitted step.** A permitted step `X₀ ⟶ Z₀ ⟵ X₀⁺` over `k₀` base changes
to a permitted step over `K` for the base-changed data `(X, B, R, f)`: here `X`, `Z` are the base
changes of `X₀`, `Z₀`, the divisors are base changed, the ray is transported by the base-extension
map of curve classes and `f` lies over `f₀`. -/
private theorem exists_isPermittedStep_of_isPullback
    {X₀ Z₀ Xp₀ X Z : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
    [IsNormal X₀] [IsIntegral Xp₀] [CompactSpace Xp₀] [IsLocallyNoetherian Xp₀] [IsNormal Xp₀]
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {t₀ : Z₀ ⟶ Spec (.of k₀)} {sXp₀ : Xp₀ ⟶ Spec (.of k₀)}
    {s : X ⟶ Spec (.of K)} {t : Z ⟶ Spec (.of K)} {π : X ⟶ X₀} {πZ : Z ⟶ Z₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {K₀ : Divisor X₀} {B₀ : QDivisor X₀} {KX : Divisor X} {BX : QDivisor X}
    (hKb : IsBaseChange π K₀ KX) (hBb : IsBaseChange π B₀ BX)
    {R₀ : Set (NumericalCurveClasses s₀)}
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass _ (C₀.cycle ℝ)) = OneCycle.numericalClass _ (C.cycle ℝ))
    {f₀ : X₀ ⟶ Z₀} {fp₀ : Xp₀ ⟶ Z₀} {f : X ⟶ Z} (hf : f ≫ t = s) (hfπ : f ≫ πZ = π ≫ f₀)
    (hstep₀ : IsPermittedStep s₀ t₀ sXp₀ K₀ B₀ R₀ f₀ fp₀) :
    ∃ (Xp : Scheme.{u}) (_ : IsIntegral Xp) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp)
      (_ : IsNormal Xp) (sXp : Xp ⟶ Spec (.of K)) (fp : Xp ⟶ Z),
      IsPermittedStep s t sXp KX BX (φ '' R₀) f fp := by
  classical
  set φk := Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  have hXp₀ := hstep₀.isProjectiveVariety_step
  haveI : LocallyOfFiniteType sXp₀ := hXp₀.toLocallyOfFiniteType
  have hp : IsPullback (pullback.fst sXp₀ φk) (pullback.snd sXp₀ φk) sXp₀ φk :=
    IsPullback.of_hasPullback _ _
  obtain ⟨_, _, _, _⟩ := isIntegral_isNormal_of_isPullback sXp₀ _ _ hp hXp₀
  set Xp := pullback sXp₀ φk
  set πp := pullback.fst sXp₀ φk
  set sXp := pullback.snd sXp₀ φk
  have hw : (πp ≫ fp₀) ≫ t₀ = sXp ≫ φk := by
    rw [Category.assoc, hstep₀.isSmallMorphism_step.comp_eq]
    exact pullback.condition
  let fp : Xp ⟶ Z := hZ.lift (πp ≫ fp₀) sXp hw
  have hfp : fp ≫ t = sXp := hZ.lift_snd _ _ hw
  have hfpπ : fp ≫ πZ = πp ≫ fp₀ := hZ.lift_fst _ _ hw
  obtain ⟨KY, hKY⟩ := exists_isBaseChange hp (flipTransform f₀ fp₀ K₀)
  obtain ⟨BY, hBY⟩ := exists_isBaseChange hp (flipTransform f₀ fp₀ B₀)
  let φp := numericalCurveClassesBaseChange sXp₀ sXp πp hp hXp₀
  have hφp := numericalCurveClassesBaseChange_eq_of_isPullback sXp₀ sXp πp hp hXp₀
  have hR₀ : R₀ ⊆ closedConeOfCurves s₀ := hstep₀.isNegativeExtremalRayOf.2.1.1.1
  have hiff := program_conditions_iff_of_isPullback (K := K) 1 False s₀ K₀ B₀
    (Y₀ := fun _ => Xp₀) (fun _ => sXp₀) (fun _ => flipTransform f₀ fp₀ K₀)
    (fun _ => flipTransform f₀ fp₀ B₀)
    (fun i => match i with
      | 0 => R₀
      | _ + 1 => ∅)
    (fun i hi => by obtain rfl := eq_zero_of_lt_one hi; exact hR₀)
    (Z₀ := fun _ => Z₀) (fun _ => t₀) (stepSeqHom f₀ fp₀)
    (fun i hi => by obtain rfl := eq_zero_of_lt_one hi; exact hstep₀.isContractionOfRay.comp_eq)
    (fun _ => fp₀) (fun i hi => hstep₀.isSmallMorphism_step.comp_eq) ∅ (fun h => h.elim)
    (T₀ := modelSeq X₀ (fun _ => Xp₀) (1 : ℕ∞).toNat) (modelStr s₀ (fun _ => sXp₀) _) (𝟙 _)
    (fun h => h.elim) s KX BX (Y := fun _ => Xp) (fun _ => sXp) (fun _ => KY) (fun _ => BY)
    (fun i => match i with
      | 0 => φ '' R₀
      | _ + 1 => ∅)
    (Z := fun _ => Z) (fun _ => t) (stepSeqHom f fp)
    (fun i hi => by obtain rfl := eq_zero_of_lt_one hi; exact hf) (fun _ => fp) (fun i hi => hfp)
    ∅ (T := modelSeq X (fun _ => Xp) (1 : ℕ∞).toNat) (modelStr s (fun _ => sXp) _) (𝟙 _)
    (fun h => h.elim) (stepSeqMap π πp)
    (fun i hi => by
      rcases eq_zero_or_eq_one_of_le_one hi with rfl | rfl
      · exact h
      · exact hp)
    (fun _ => πZ) (fun i hi => hZ) (stepSeqMap π πp _) (fun h => h.elim)
    (fun i hi => by obtain rfl := eq_zero_of_lt_one hi; exact hfπ) (fun i hi => hfpπ)
    (fun h => h.elim)
    (fun i hi P₀ P hP => by
      rcases eq_zero_or_eq_one_of_le_one hi with rfl | rfl
      · exact ⟨hKb.1 P₀ P hP, hBb.1 P₀ P hP⟩
      · exact ⟨hKY.1 P₀ P hP, hBY.1 P₀ P hP⟩)
    (fun i hi P hP => by
      rcases eq_zero_or_eq_one_of_le_one hi with rfl | rfl
      · rcases hP with hP | hP
        · exact hKb.2 P hP
        · exact hBb.2 P hP
      · rcases hP with hP | hP
        · exact hKY.2 P hP
        · exact hBY.2 P hP)
    (fun i => match i with
      | 0 => φ
      | _ + 1 => φp.toLinearMap)
    (fun i hi => by
      rcases eq_zero_or_eq_one_of_le_one hi with rfl | rfl
      · exact hφ
      · exact hφp)
    (fun i hi => by obtain rfl := eq_zero_of_lt_one hi; rfl) (fun h => h.elim)
  obtain ⟨-, -, -, hs, -⟩ := hiff.mp ⟨hstep₀.isProjectiveVariety, hstep₀.isLogCanonicalPair,
    hstep₀.isCanonicalDivisor, fun i hi => by obtain rfl := eq_zero_of_lt_one hi; exact hstep₀,
    fun i hi => by obtain rfl := eq_zero_of_lt_one hi; rfl,
    fun i hi => by obtain rfl := eq_zero_of_lt_one hi; rfl, fun h => h.elim⟩
  exact ⟨Xp, inferInstance, inferInstance, inferInstance, inferInstance, sXp, fp, hs 0 (by simp)⟩

end OneStep

/-! ### Isomorphisms of stage models -/

section StageIso

open MMP.CoefficientModels

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) {i₀ : I}

/-- Two lifts at a common stage compose to the identity once their composite agrees with the
identity on the second factor after a stage map. -/
private lemma stageLift_comp_stageLift_eq_id {W W' : Over (D.obj i₀)} {m₁ m₂ m₃ m : Over i₀}
    (H₁ : stageObj D W m₁ ⟶ W'.left) (hH₁ : H₁ ≫ W'.hom = pullback.snd _ _ ≫ W.hom)
    (H₂ : stageObj D W' m₂ ⟶ W.left) (hH₂ : H₂ ≫ W.hom = pullback.snd _ _ ≫ W'.hom)
    (b₁ : m₃ ⟶ m₁) (b₂ : m₃ ⟶ m₂) (e : m ⟶ m₃)
    (h : stageMap D W e ≫ stageLift H₁ hH₁ b₁ ≫ stageLift H₂ hH₂ b₂ ≫ pullback.snd _ _ =
      stageMap D W e ≫ pullback.snd _ _) :
    stageLift H₁ hH₁ (e ≫ b₁) ≫ stageLift H₂ hH₂ (e ≫ b₂) = 𝟙 _ := by
  have hu := stageLift_stageMap H₁ hH₁ e b₁ (e ≫ b₁) rfl
  have hv := stageLift_stageMap H₂ hH₂ e b₂ (e ≫ b₂) rfl
  refine pullback.hom_ext (by simp) ?_
  calc stageLift H₁ hH₁ (e ≫ b₁) ≫ stageLift H₂ hH₂ (e ≫ b₂) ≫ pullback.snd _ _
      = stageLift H₁ hH₁ (e ≫ b₁) ≫ stageLift H₂ hH₂ (e ≫ b₂) ≫ stageMap D W e ≫
          pullback.snd _ _ := by rw [stageMap_snd]
    _ = stageLift H₁ hH₁ (e ≫ b₁) ≫ stageMap D W' e ≫ stageLift H₂ hH₂ b₂ ≫
          pullback.snd _ _ := by rw [reassoc_of% hv]
    _ = stageMap D W e ≫ stageLift H₁ hH₁ b₁ ≫ stageLift H₂ hH₂ b₂ ≫ pullback.snd _ _ := by
          rw [reassoc_of% hu]
    _ = 𝟙 _ ≫ pullback.snd _ _ := by rw [h, stageMap_snd, Category.id_comp]

variable [IsCofiltered I] [Quiver.IsThin I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **Two stage models of one scheme are isomorphic at a later stage** (Stacks 01ZM), compatibly
with the projections from the scheme over the limit. -/
private theorem exists_stage_iso {c : Cone D} (hc : IsLimit c) {W W' : Over (D.obj i₀)}
    (hW : FinitePresentation W.hom) (hW' : FinitePresentation W'.hom) (X : Over c.pt)
    (g : X.left ⟶ W.left) (hpb : IsPullback g X.hom W.hom (c.π.app i₀))
    (g' : X.left ⟶ W'.left) (hpb' : IsPullback g' X.hom W'.hom (c.π.app i₀)) :
    ∃ (m : Over i₀) (e : stageObj D W m ≅ stageObj D W' m),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        leg D W c X g hpb m ≫ e.hom = leg D W' c X g' hpb' m := by
  haveI : LocallyOfFinitePresentation W.hom := hW.1
  haveI : LocallyOfFinitePresentation W'.hom := hW'.1
  have hthin : ∀ {a b : Over i₀} (x y : a ⟶ b), x = y := fun x y =>
    Over.OverMorphism.ext (Subsingleton.elim _ _)
  obtain ⟨m₁, H₁, hl₁, hH₁⟩ := exists_stage_hom D W c X g hpb hc hW W' g' hpb'.w
  obtain ⟨m₂, H₂, hl₂, hH₂⟩ := exists_stage_hom D W' c X g' hpb' hc hW' W g hpb.w
  let m₃ := IsCofiltered.min m₁ m₂
  let b₁ : m₃ ⟶ m₁ := IsCofiltered.minToLeft m₁ m₂
  let b₂ : m₃ ⟶ m₂ := IsCofiltered.minToRight m₁ m₂
  have hu (m : Over i₀) (b : m ⟶ m₁) :
      leg D W c X g hpb m ≫ stageLift H₁ hH₁ b = leg D W' c X g' hpb' m := by
    simpa using leg_stageLift D W c X g hpb hpb' (𝟙 X) H₁ hH₁ b (by simpa using hl₁)
  have hv (m : Over i₀) (b : m ⟶ m₂) :
      leg D W' c X g' hpb' m ≫ stageLift H₂ hH₂ b = leg D W c X g hpb m := by
    simpa using leg_stageLift D W' c X g' hpb' hpb (𝟙 X) H₂ hH₂ b (by simpa using hl₂)
  obtain ⟨m₄, e₄, h₄⟩ := exists_stage_eq D W c X g hpb hc hW W
    (stageLift H₁ hH₁ b₁ ≫ stageLift H₂ hH₂ b₂ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by simp [hH₁, hH₂, reassoc_of% hH₁, reassoc_of% hH₂]) rfl
    (by rw [reassoc_of% hu, reassoc_of% hv])
  obtain ⟨m₅, e₅, h₅⟩ := exists_stage_eq D W' c X g' hpb' hc hW' W'
    (stageLift H₂ hH₂ b₂ ≫ stageLift H₁ hH₁ b₁ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by simp [hH₁, hH₂, reassoc_of% hH₁, reassoc_of% hH₂]) rfl
    (by rw [reassoc_of% hv, reassoc_of% hu])
  let m₆ := IsCofiltered.min m₄ m₅
  let e₆ : m₆ ⟶ m₃ := IsCofiltered.minToLeft m₄ m₅ ≫ e₄
  have he₄ : e₆ = IsCofiltered.minToLeft m₄ m₅ ≫ e₄ := rfl
  have he₅ : e₆ = IsCofiltered.minToRight m₄ m₅ ≫ e₅ := hthin _ _
  refine ⟨m₆, ⟨stageLift H₁ hH₁ (e₆ ≫ b₁), stageLift H₂ hH₂ (e₆ ≫ b₂), ?_, ?_⟩, by simp,
    hu _ _⟩
  · refine stageLift_comp_stageLift_eq_id D H₁ hH₁ H₂ hH₂ b₁ b₂ e₆ ?_
    rw [he₄, stageMap_comp, Category.assoc, h₄, Category.assoc]
  · refine stageLift_comp_stageLift_eq_id D H₂ hH₂ H₁ hH₁ b₂ b₁ e₆ ?_
    rw [he₅, stageMap_comp, Category.assoc, h₅, Category.assoc]

end StageIso

/-! ### Descent of a permitted step -/

/-- **Push-forwards commute with base change.** For `f₀ : X₀ ⟶ Z₀` over `k₀` with base change
`f : X ⟶ Z`, the push-forward `f_* D` of the base change `D` of a divisor `D₀` is the base change
of `f₀_* D₀`. -/
private theorem isBaseChange_transformDivisor
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    {R : Type*} [AddCommMonoid R]
    {X₀ Z₀ X Z : Scheme.{u}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {t₀ : Z₀ ⟶ Spec (.of k₀)}
    {s : X ⟶ Spec (.of K)} {t : Z ⟶ Spec (.of K)} {π : X ⟶ X₀} {πZ : Z ⟶ Z₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    {f₀ : X₀ ⟶ Z₀} (hf₀ : f₀ ≫ t₀ = s₀) {f : X ⟶ Z} (hf : f ≫ t = s)
    (hfπ : f ≫ πZ = π ≫ f₀)
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) :
    IsBaseChange πZ (MMP.Mori.RationalMap.transformDivisor f₀.toRationalMap D₀)
      (MMP.Mori.RationalMap.transformDivisor f.toRationalMap D) := by
  have hsq := isPullback_of_isPullback_comp h hZ hf₀ hf hfπ
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hXK := (isProjectiveVariety_iff_of_isPullback _ _ _ h).1 hX₀
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral Z := hZK.toIsIntegral
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  have : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have : IsProper f₀ := isProper_of_comp_eq hX₀ hZ₀ hf₀
  have : IsProper f := isProper_of_comp_eq hXK hZK hf
  have : Surjective π := surjective_of_isPullback h
  have : Surjective πZ := surjective_of_isPullback hZ
  have : IsSeparated t := hZK.toIsSeparated
  have : IsSeparated t₀ := hZ₀.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = t ≫ (Spec (.of K) ↘ ⊤_ Scheme) from Subsingleton.elim _ _]
    infer_instance
  have : IsSeparated (Z₀ ↘ ⊤_ Scheme) := by
    rw [show (Z₀ ↘ ⊤_ Scheme) = t₀ ≫ (Spec (.of k₀) ↘ ⊤_ Scheme) from Subsingleton.elim _ _]
    infer_instance
  have heq {w w' : Z} {x x' : Z₀} (hw : closure {w} = πZ.base ⁻¹' closure {x})
      (hw' : closure {w'} = πZ.base ⁻¹' closure {x'}) : w = w' ↔ x = x' := by
    constructor
    · rintro rfl
      exact (inseparable_iff_closure_eq.mpr
        ((Set.preimage_injective.mpr πZ.surjective) (hw.symm.trans hw'))).eq
    · rintro rfl
      exact (inseparable_iff_closure_eq.mpr (hw.trans hw'.symm)).eq
  have hcoh (E : MMP.Mori.PrimeDivisor Z) : E.genericPoint ≠ genericPoint Z := by
    intro he
    have h1 : Order.coheight E.genericPoint = 1 := MMP.Mori.PrimeDivisor.coheight_genericPoint E
    rw [he, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at h1
    exact zero_ne_one h1
  have hexX : ∀ P₀ : MMP.Mori.PrimeDivisor X₀, ∃ P : MMP.Mori.PrimeDivisor X,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} :=
    fun P₀ => (exists_primeDivisor_baseChange h P₀).imp fun _ hP => hP.1
  refine IsBaseChange.mapPrimeDivisors hexX (fun P₀ P hP F₀ F hF => ?_)
    (fun P₀ P hP F hPF => ?_) hD
  · rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff,
      MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, eq_comm (a := f₀ _),
      eq_comm (a := f _)]
    exact heq hF (closure_singleton_map_eq hsq f.isClosedMap f₀.isClosedMap hP)
  · rw [MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff, eq_comm] at hPF
    refine exists_closure_eq_of_map_ne_genericPoint hZ F fun hgen => ?_
    have hc := closure_singleton_map_eq hsq f.isClosedMap f₀.isClosedMap hP
    have h1 : πZ F.genericPoint = f₀ P₀.genericPoint := by
      rw [hPF, ← Scheme.Hom.comp_apply, hfπ, Scheme.Hom.comp_apply, map_eq_of_closure_eq hP]
    rw [h1] at hgen
    rw [hgen, (genericPoint_spec Z₀).def, Set.preimage_univ, ← hPF] at hc
    exact hcoh F ((genericPoint_spec Z).eq (isGenericPoint_def.mpr hc)).symm

/-! ### The diagram of a small modification with a log resolution -/

/-- The vertices of the diagram `Z ⟵ X⁺ ⟵ W` of a small modification `X⁺ ⟶ Z` and a log
resolution `W ⟶ X⁺`, with `m` prime divisors on `X⁺` and `n` prime divisors on `W`. -/
private inductive Vtx (m n : ℕ) : Type u
  | z | p | w | c (l : Fin m) | e (l : Fin n)

namespace Vtx

variable {m n : ℕ}

/-- The order of the vertices: every vertex lies below `z`, the leaves below their parents. -/
private def le : Vtx.{u} m n → Vtx.{u} m n → Prop
  | _, z => True
  | p, p => True | w, p => True | c _, p => True | e _, p => True
  | w, w => True | e _, w => True
  | c l, c l' => l = l'
  | e l, e l' => l = l'
  | _, _ => False

/-- The partial order of the vertices. -/
@[instance_reducible] private def partialOrder : PartialOrder (Vtx.{u} m n) where
  le := le
  le_refl a := by cases a <;> simp [le]
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [le]
  le_antisymm a b := by cases a <;> cases b <;> simp_all [le]

/-- The vertices form a finite type. -/
@[instance_reducible] private noncomputable def fintype : Fintype (Vtx.{u} m n) :=
  Fintype.ofEquiv (Unit ⊕ Unit ⊕ Unit ⊕ Fin m ⊕ Fin n)
    { toFun := fun | .inl _ => z | .inr (.inl _) => p | .inr (.inr (.inl _)) => w
                   | .inr (.inr (.inr (.inl l))) => c l | .inr (.inr (.inr (.inr l))) => e l
      invFun := fun | z => .inl () | p => .inr (.inl ()) | w => .inr (.inr (.inl ()))
                    | c l => .inr (.inr (.inr (.inl l))) | e l => .inr (.inr (.inr (.inr l)))
      left_inv := by rintro (_ | _ | _ | _ | _) <;> rfl
      right_inv := by rintro (_ | _ | _ | _ | _) <;> rfl }

attribute [local instance] partialOrder fintype

/-- The vertices form a finite category. -/
@[instance_reducible] private noncomputable def finCategory : FinCategory (Vtx.{u} m n) := by
  classical exact inferInstance

section Diagram

variable {K : Type u} [Field K] {Z Xp W : Scheme.{u}} (t : Z ⟶ Spec (.of K))
  (sXp : Xp ⟶ Spec (.of K)) (fp : Xp ⟶ Z) (μ : W ⟶ Xp) {P : Fin m → Scheme.{u}}
  (ιP : ∀ l, P l ⟶ Xp) {E : Fin n → Scheme.{u}} (ιE : ∀ l, E l ⟶ W)

/-- The schemes of the diagram, over `K`. -/
private noncomputable def diagObj : Vtx.{u} m n → Over (Spec (.of K))
  | z => Over.mk t
  | p => Over.mk sXp
  | w => Over.mk (μ ≫ sXp)
  | c l => Over.mk (ιP l ≫ sXp)
  | e l => Over.mk (ιE l ≫ μ ≫ sXp)

/-- The morphisms of the diagram. -/
private noncomputable def diagMap : ∀ a b : Vtx.{u} m n, le a b →
    ((diagObj t sXp μ ιP ιE a).left ⟶ (diagObj t sXp μ ιP ιE b).left)
  | z, z, _ => 𝟙 _
  | p, z, _ => fp
  | w, z, _ => μ ≫ fp
  | c l, z, _ => ιP l ≫ fp
  | e l, z, _ => ιE l ≫ μ ≫ fp
  | p, p, _ => 𝟙 _
  | w, p, _ => μ
  | c l, p, _ => ιP l
  | e l, p, _ => ιE l ≫ μ
  | w, w, _ => 𝟙 _
  | e l, w, _ => ιE l
  | c l, c l', h => eqToHom (by cases h; rfl)
  | e l, e l', h => eqToHom (by cases h; rfl)

private lemma diagMap_w (hfp : fp ≫ t = sXp) : ∀ (a b : Vtx.{u} m n) (h : le a b),
    diagMap t sXp fp μ ιP ιE a b h ≫ (diagObj t sXp μ ιP ιE b).hom =
      (diagObj t sXp μ ιP ιE a).hom
  | z, z, _ => by simp [diagMap]
  | p, z, _ => by simpa [diagMap, diagObj] using hfp
  | w, z, _ => by simp [diagMap, diagObj, hfp]
  | c l, z, _ => by simp [diagMap, diagObj, hfp]
  | e l, z, _ => by simp [diagMap, diagObj, hfp]
  | p, p, _ => by simp [diagMap]
  | w, p, _ => by simp [diagMap, diagObj]
  | c l, p, _ => by simp [diagMap, diagObj]
  | e l, p, _ => by simp [diagMap, diagObj]
  | w, w, _ => by simp [diagMap]
  | e l, w, _ => by simp [diagMap, diagObj]
  | c l, c l', h => by cases h; simp [diagMap]
  | e l, e l', h => by cases h; simp [diagMap]

/-- The diagram `Z ⟵ X⁺ ⟵ W` with the prime divisors `P l ⟶ X⁺` and `E l ⟶ W`. -/
private noncomputable def diagram (hfp : fp ≫ t = sXp) : Vtx.{u} m n ⥤ Over (Spec (.of K)) where
  obj := diagObj t sXp μ ιP ιE
  map {a b} h := Over.homMk (diagMap t sXp fp μ ιP ιE a b (leOfHom h))
    (diagMap_w t sXp fp μ ιP ιE hfp a b _)
  map_id a := by ext; cases a <;> simp [diagMap]
  map_comp {a b c} f g := by
    have hf : le a b := leOfHom f
    have hg : le b c := leOfHom g
    ext
    cases a <;> cases b <;> cases c <;> simp only [le] at hf hg <;>
      first | exact (hf.elim) | exact (hg.elim) | (subst_vars; simp [diagMap]; done) |
        (simp only [Over.comp_left, Over.homMk_left]; rfl) | rfl

end Diagram

end Vtx

/-- A closed subscheme of a projective scheme is projective. -/
private lemma isProjective_comp_of_isClosedImmersion {X Y S : Scheme.{u}} (ι : X ⟶ Y)
    [IsClosedImmersion ι] {g : Y ⟶ S} (hg : IsProjective g) : IsProjective (ι ≫ g) := by
  obtain ⟨E, h1, h2, hqc, i, hi, rfl⟩ := hg
  exact ⟨E, h1, h2, hqc, ι ≫ i, inferInstance, by rw [Category.assoc]⟩

/-- **Points of finitely generated algebras.** A finitely generated subalgebra `A ⊆ K` over an
algebraically closed field `k₀` has a `k₀`-point: `Spec k₀ ⟶ Spec A` is a section of the structure
morphism (Hilbert's Nullstellensatz). -/
private theorem exists_comp_specMap_eq_id {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] (A : Subalgebra k₀ K) (hA : A.FG) :
    ∃ x : Spec (.of k₀) ⟶ Spec (.of A),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k₀ (A ⧸ m) :=
    AlgebraicGeometry.FieldExtensionDescent.finite_quotient_of_isMaximal k₀ K ⟨A, hA⟩ m
  haveI : Algebra.IsIntegral k₀ (A ⧸ m) := Algebra.IsIntegral.of_finite k₀ _
  let e : k₀ ≃ₐ[k₀] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k₀ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : A →ₐ[k₀] k₀ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k₀ m)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ψ.toRingHom.comp (algebraMap k₀ A) = RingHom.id k₀ := by
    ext a
    simp
  rw [this]
  exact Spec.map_id _

/-- A `k₀`-point of a finitely generated subalgebra `A ⊆ K` avoiding the zero sets of finitely
many nonzero elements of `A`. -/
private theorem exists_comp_specMap_eq_id_notMem {k₀ K : Type u} [Field k₀] [Field K]
    [Algebra k₀ K] [IsAlgClosed k₀] (A : Subalgebra k₀ K) (hA : A.FG) (r : A) (hr : r ≠ 0) :
    ∃ x : Spec (.of k₀) ⟶ Spec (.of A),
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ ∧
        r ∉ (x.base (IsLocalRing.closedPoint k₀)).asIdeal := by
  classical
  let B : Subalgebra k₀ K := A ⊔ Algebra.adjoin k₀ {(r : K)⁻¹}
  have h1 : (Algebra.adjoin k₀ ({(r : K)⁻¹} : Set K)).FG := by
    simpa using Subalgebra.fg_adjoin_finset (R := k₀) ({(r : K)⁻¹} : Finset K)
  have hAB : A ≤ B := le_sup_left
  obtain ⟨y, hy⟩ := exists_comp_specMap_eq_id B (hA.sup h1)
  let φ : CommRingCat.of A ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (Subalgebra.inclusion hAB).toRingHom
  refine ⟨y ≫ Spec.map φ, ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, ← hy]
    rfl
  · change r ∉ ((Spec.map φ).base (y.base (IsLocalRing.closedPoint k₀))).asIdeal
    intro hmem'
    have hmem : φ.hom r ∈ (y.base (IsLocalRing.closedPoint k₀)).asIdeal := hmem'
    have hunit : IsUnit (φ.hom r) := by
      have hinv : (r : K)⁻¹ ∈ B := le_sup_right (a := A) (Algebra.subset_adjoin rfl)
      refine IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) ?_
      apply Subtype.ext
      have : (r : K) ≠ 0 := fun h => hr (Subtype.ext h)
      simp [φ, this]
    exact (y.base (IsLocalRing.closedPoint k₀)).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-! ### Inverse transforms over a smooth open, and fibre geometry -/

section SmallPullback

open MMP.Threefold.Resolution MMP.Threefold.Mori.OpenRestriction MMP.Resolution

variable {Y Z : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]

private theorem isPullback_restrictOpen_inverseTransform_single {k : Type u} [Field k]
    (g : Y ⟶ Z) (hg : ∀ P : MMP.Mori.PrimeDivisor Y, g P.genericPoint ∈ biregularLocus g)
    (U : Z.Opens) {sU : U.toScheme ⟶ Spec (.of k)} (hU : MMP.Mori.IsSmoothScheme sU)
    [Nonempty (g ⁻¹ᵁ U)] (Q : MMP.Mori.PrimeDivisor Z)
    (hB : ∀ Z' : irreducibleComponents (g ⁻¹ᵁ U).toScheme,
      (g ∣_ U) (componentGenericPoint _ Z') ∉
        (DivisorWithCoeffs.restrictOpen U (Finsupp.single Q 1 : Divisor Z)).supp) :
    Divisor.IsPullback (g ∣_ U) (DivisorWithCoeffs.restrictOpen U (Finsupp.single Q 1 : Divisor Z)) hB
      (DivisorWithCoeffs.restrictOpen (g ⁻¹ᵁ U) (inverseTransformDivisor g (Finsupp.single Q 1 : Divisor Z))) := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  haveI : CompactSpace (g ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have hcart : ∀ D : Divisor U.toScheme, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hU
  obtain ⟨B', hB'⟩ := (hcart _).exists_isPullback hB
  suffices hBeq : B' =
      DivisorWithCoeffs.restrictOpen (g ⁻¹ᵁ U) (inverseTransformDivisor g (Finsupp.single Q 1 : Divisor Z)) from
    hBeq ▸ hB'
  -- the coefficient of the inverse transform at a prime divisor `P` of `g⁻¹U`
  have hinv (P : MMP.Mori.PrimeDivisor (g ⁻¹ᵁ U).toScheme) :
      (DivisorWithCoeffs.restrictOpen (g ⁻¹ᵁ U) (inverseTransformDivisor g (Finsupp.single Q 1 : Divisor Z))).coeff P
        = if g ((g ⁻¹ᵁ U).ι P.genericPoint) = Q.genericPoint then 1 else 0 := by
    rw [DivisorWithCoeffs.coeff_restrictOpen, inverseTransformDivisor_single]
    set P' : MMP.Mori.PrimeDivisor Y := OpenWeilRestriction.primeDivisorMap (g ⁻¹ᵁ U).ι P
    have hP' : MMP.Mori.PrimeDivisor.genericPoint P' = (g ⁻¹ᵁ U).ι P.genericPoint :=
      OpenWeilRestriction.genericPoint_primeDivisorMap _ P
    split_ifs with h
    · rw [inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (E := P') (by rw [hP']; exact h)
        (hP' ▸ hg P')]
      exact Finsupp.single_eq_same
    · rcases hQ : inverseTransformPrimeDivisor g Q with _ | P''
      · rfl
      · change (Finsupp.single P'' (1 : ℤ)) P' = 0
        refine Finsupp.single_eq_of_ne fun hne => h ?_
        rw [← hP', hne]
        exact (map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ).1
  ext P
  rw [hinv P]
  have hPU' : (g ⁻¹ᵁ U).ι P.genericPoint ∈ g ⁻¹ᵁ U := by
    have : (g ⁻¹ᵁ U).ι P.genericPoint ∈ Set.range (g ⁻¹ᵁ U).ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hPU : g ((g ⁻¹ᵁ U).ι P.genericPoint) ∈ U := hPU'
  by_cases hQU : Q.genericPoint ∈ U
  swap
  · -- `Q` misses `U`: both sides vanish
    have hD₁ : DivisorWithCoeffs.restrictOpen U (Finsupp.single Q 1 : Divisor Z) = 0 := by
      ext W
      rw [DivisorWithCoeffs.coeff_restrictOpen]
      refine Finsupp.single_eq_of_ne fun hW => hQU ?_
      have h1 : MMP.Mori.PrimeDivisor.genericPoint
          (OpenWeilRestriction.primeDivisorMap U.ι W : MMP.Mori.PrimeDivisor Z) =
            U.ι W.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ W
      rw [← hW, h1]
      exact (W.genericPoint).2
    have h0 : Divisor.IsPullback (g ∣_ U)
        (DivisorWithCoeffs.restrictOpen U (Finsupp.single Q 1 : Divisor Z)) hB 0 :=
      Divisor.IsPullback.of_eq hD₁.symm (Divisor.isPullback_zero fun Z' => hD₁ ▸ hB Z')
    rw [Divisor.IsPullback.eq (hcart _) hB' h0, if_neg fun h : g ((g ⁻¹ᵁ U).ι P.genericPoint) = Q.genericPoint => hQU (h ▸ hPU)]
    rfl
  -- `Q` meets `U`: it is the closure of a prime divisor `Q₁` of `U`
  obtain ⟨Q₁, hQ₁⟩ : Q ∈ Set.range (OpenWeilRestriction.primeDivisorMap U.ι) :=
    (OpenWeilRestriction.mem_range_primeDivisorMap_iff U.ι Q).mpr (by
      rw [Scheme.Opens.range_ι]; exact hQU)
  have hQ₁g : U.ι (MMP.Mori.PrimeDivisor.genericPoint Q₁) = Q.genericPoint := by
    rw [← hQ₁]; exact (OpenWeilRestriction.genericPoint_primeDivisorMap _ Q₁).symm
  have hD₁ : DivisorWithCoeffs.restrictOpen U (Finsupp.single Q 1 : Divisor Z) =
      Finsupp.single Q₁ 1 := by
    ext W
    rw [DivisorWithCoeffs.coeff_restrictOpen, ← hQ₁]
    change (Finsupp.single _ (1 : ℤ)) _ = (Finsupp.single Q₁ (1 : ℤ)) W
    by_cases hW : W = Q₁
    · subst hW; rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne
        (fun h => hW (OpenWeilRestriction.primeDivisorMap_injective _ h)),
        Finsupp.single_eq_of_ne hW]
  have hcB : ∀ Z' : irreducibleComponents (g ⁻¹ᵁ U).toScheme,
      (g ∣_ U) (componentGenericPoint _ Z') ∉
        DivisorWithCoeffs.supp (Finsupp.single Q₁ 1 : Divisor U.toScheme) :=
    fun Z' => hD₁ ▸ hB Z'
  have hB₁ : Divisor.IsPullback (g ∣_ U) (Finsupp.single Q₁ 1 : Divisor U.toScheme) hcB B' :=
    Divisor.IsPullback.of_eq hD₁ hB'
  have hCe : Stacks.Divisors.IsEffectiveCartierDivisor Q₁.idealSheaf :=
    isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hU Q₁
  obtain ⟨n, hn, hcoef⟩ := coeff_isPullback_single_eq_idealOrder Q₁ hCe hB₁ P
  rw [hcoef]
  have hbir : g ((g ⁻¹ᵁ U).ι P.genericPoint) ∈ biregularLocus g := by
    have := hg (OpenWeilRestriction.primeDivisorMap (g ⁻¹ᵁ U).ι P)
    rwa [show MMP.Mori.PrimeDivisor.genericPoint
      (OpenWeilRestriction.primeDivisorMap (g ⁻¹ᵁ U).ι P : MMP.Mori.PrimeDivisor Y) =
        (g ⁻¹ᵁ U).ι P.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ P]
      at this
  have hiso : IsIso ((g ∣_ U).stalkMap P.genericPoint) := by
    have h1 : IsIso (g.stalkMap ((g ⁻¹ᵁ U).ι P.genericPoint)) :=
      isIso_stalkMap_of_mem_biregularLocus g hbir
    exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap g U P.genericPoint)).mpr h1
  have hn' : idealOrder (IdealSheafData.stalk Q₁.idealSheaf ((g ∣_ U) P.genericPoint)) = n := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_comap] at hn
    rw [← hn]
    exact (idealOrder_map_ringEquiv
      (asIso ((g ∣_ U).stalkMap P.genericPoint)).commRingCatIsoToRingEquiv _).symm
  have hgU : U.ι ((g ∣_ U) P.genericPoint) = g ((g ⁻¹ᵁ U).ι P.genericPoint) :=
    morphismRestrict_base_coe g U P.genericPoint
  split_ifs with h
  · have hy : (g ∣_ U) P.genericPoint = MMP.Mori.PrimeDivisor.genericPoint Q₁ := by
      apply U.ι.isOpenEmbedding.injective
      rw [hgU, h, hQ₁g]
    rw [hy, stalk_idealSheaf_genericPoint_eq_maximalIdeal Q₁ hCe] at hn'
    have := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing Q₁
    rw [idealOrder_maximalIdeal] at hn'
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) hn'.symm : n = 1)
  · have hy : (g ∣_ U) P.genericPoint ∉ Q₁.idealSheaf.support := by
      intro hm
      apply h
      have hcoh : Order.coheight ((g ∣_ U) P.genericPoint) = 1 := by
        rw [← coheight_eq_of_isOpenImmersion U.ι, hgU,
          MMP.Positivity.coheight_map_of_mem_biregularLocus g hbir,
          coheight_eq_of_isOpenImmersion (g ⁻¹ᵁ U).ι]
        exact P.coheight_genericPoint
      have := MMP.Mori.PrimeDivisor.eq_genericPoint_of_mem_support Q₁ hm hcoh
      rw [← hgU, this, hQ₁g]
    rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).2 hy, idealOrder_top] at hn'
    exact_mod_cast (Nat.cast_injective (R := ℕ∞) hn'.symm : n = 0)

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z] in
private theorem restrictOpen_add {X : Scheme.{u}} (U : X.Opens) (D₁ D₂ : Divisor X) :
    DivisorWithCoeffs.restrictOpen U (D₁ + D₂) =
      DivisorWithCoeffs.restrictOpen U D₁ + DivisorWithCoeffs.restrictOpen U D₂ := by
  ext W
  rfl

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z] in
private theorem restrictOpen_zsmul {X : Scheme.{u}} (U : X.Opens) (n : ℤ) (D : Divisor X) :
    DivisorWithCoeffs.restrictOpen U (n • D) = n • DivisorWithCoeffs.restrictOpen U D := by
  ext W
  rfl

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z] in
private theorem restrictOpen_zero {X : Scheme.{u}} (U : X.Opens) :
    DivisorWithCoeffs.restrictOpen U (0 : Divisor X) = 0 := by
  ext W
  rfl

/-- **Inverse transforms along a morphism biregular in codimension one are pull-backs.** Let
`g : Y ⟶ Z` be a morphism of integral normal locally Noetherian schemes, biregular at the image
of the generic point of every prime divisor of `Y`, and `U ⊆ Z` an open subscheme smooth over a
field. Over `U`, the inverse transform `g⁻¹_* E` of a divisor `E` of `Z` is the pull-back of
`E|_U`. -/
private theorem isPullback_restrictOpen_inverseTransformDivisor {k : Type u} [Field k]
    (g : Y ⟶ Z) (hg : ∀ P : MMP.Mori.PrimeDivisor Y, g P.genericPoint ∈ biregularLocus g)
    (U : Z.Opens) {sU : U.toScheme ⟶ Spec (.of k)} (hU : MMP.Mori.IsSmoothScheme sU)
    [Nonempty (g ⁻¹ᵁ U)] [IsDominant (g ∣_ U)] (E : Divisor Z) :
    ∃ hB, Divisor.IsPullback (g ∣_ U) (DivisorWithCoeffs.restrictOpen U E) hB
      (DivisorWithCoeffs.restrictOpen (g ⁻¹ᵁ U) (inverseTransformDivisor g E)) := by
  classical
  have hcart : ∀ D : Divisor U.toScheme, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hU
  have hB : ∀ (D : Divisor U.toScheme) (Z' : irreducibleComponents (g ⁻¹ᵁ U).toScheme),
      (g ∣_ U) (componentGenericPoint _ Z') ∉ DivisorWithCoeffs.supp D := fun D Z' =>
    map_componentGenericPoint_notMem_supp_of_isDominant' (g ∣_ U) D Z'
  refine ⟨hB _, ?_⟩
  induction E using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, restrictOpen_zero, restrictOpen_zero]
    exact Divisor.isPullback_zero _
  | add E₁ E₂ h₁ h₂ =>
    rw [map_add, restrictOpen_add, restrictOpen_add]
    exact Divisor.IsPullback.add (hcart _) (hcart _) (hB _) h₁ h₂
  | single Q n =>
    have hs : (Finsupp.single Q n : Divisor Z) = n • Finsupp.single Q 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul, restrictOpen_zsmul, restrictOpen_zsmul]
    exact Divisor.IsPullback.zsmul (hcart _)
      (isPullback_restrictOpen_inverseTransform_single g hg U hU Q (hB _)) n (hB _)

/-- **The divisorial sheaf of an inverse transform over a smooth open.** In the situation of
`isPullback_restrictOpen_inverseTransformDivisor`,
`𝒪_Y(g⁻¹_* E)|_{g⁻¹U} ≅ (g|_U)^* (𝒪_Z(E)|_U)`. -/
private theorem nonempty_restrict_divisorialSheaf_inverseTransformDivisor_iso [CompactSpace Z]
    {k : Type u} [Field k]
    (g : Y ⟶ Z) (hg : ∀ P : MMP.Mori.PrimeDivisor Y, g P.genericPoint ∈ biregularLocus g)
    (U : Z.Opens) {sU : U.toScheme ⟶ Spec (.of k)} (hU : MMP.Mori.IsSmoothScheme sU)
    [Nonempty U] [Nonempty (g ⁻¹ᵁ U)] [IsDominant (g ∣_ U)] (E : Divisor Z) :
    Nonempty ((Divisor.divisorialSheaf (inverseTransformDivisor g E)).restrict (g ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (g ∣_ U)).obj (E.divisorialSheaf.restrict U.ι)) := by
  haveI : IsNoetherian Y := ⟨⟩
  haveI : IsNoetherian Z := ⟨⟩
  haveI : CompactSpace (g ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  obtain ⟨hB, h⟩ := isPullback_restrictOpen_inverseTransformDivisor g hg U hU E
  have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hU (DivisorWithCoeffs.restrictOpen U E)
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hc (g ∣_ U) hB
  rw [h.pullback_eq hc] at e
  exact ⟨(Divisor.divisorialSheafRestrictOpenIso _ (g ⁻¹ᵁ U)).symm ≪≫ e ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso (Divisor.divisorialSheafRestrictOpenIso E U)⟩

end SmallPullback

section FibreGeometry

/-- The restriction of a dominant morphism from an irreducible scheme to the preimage of an open
is dominant. -/
private theorem isDominant_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) : IsDominant (f ∣_ U) := by
  refine ⟨Dense.mono ?_ (Dense.preimage (Scheme.Hom.denseRange f) U.ι.isOpenEmbedding.isOpenMap)⟩
  rintro y ⟨x, hx⟩
  have hxU : x ∈ f ⁻¹ᵁ U := by
    show f x ∈ U
    rw [hx]
    exact y.2
  exact ⟨⟨x, hxU⟩, Subtype.ext ((morphismRestrict_base_coe f U ⟨x, hxU⟩).trans hx)⟩

/-- A small morphism is biregular at the image of the generic point of every prime divisor of its
source. -/
private theorem map_genericPoint_mem_biregularLocus_of_isSmallMorphism {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}
    (h : IsSmallMorphism sX sZ f) (P : MMP.Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra hP
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h.two_le_codimension
    P.genericPoint hP
  rw [P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- **An invertible sheaf is the divisorial sheaf of a Cartier divisor.** -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [hL : Stacks.Ample.IsInvertibleModule Y L] :
    ∃ N : Divisor Y, N.IsCartier ∧ Nonempty (N.divisorialSheaf ≅ L) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- Relative ampleness is invariant under isomorphism of invertible sheaves. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple f L') : MMP.Mori.IsRelativelyAmple f L := by
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  rwa [Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)]

/-- **A relatively ample sheaf agreeing with `𝒪_Z(E)` over a smooth open.** Let `g : Y ⟶ Z` be a
small morphism and `U ⊆ Z` a smooth open containing every point of codimension at most one. If a
`g`-ample invertible sheaf `𝓝` on `Y` agrees over `g⁻¹ U` with the pull-back of `𝒪_Z(E)|_U`,
then `g⁻¹_* E` is a `g`-ample Cartier divisor. -/
private theorem exists_isRelativelyAmple_inverseTransformDivisor {k : Type u} [Field k]
    {Y Z : Scheme.{u}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {g : Y ⟶ Z} (hg : IsSmallMorphism sY sZ g)
    (U : Z.Opens) (hU : MMP.Mori.IsSmoothScheme (U.ι ≫ sZ))
    (hUc : ∀ z : Z, Order.coheight z ≤ 1 → z ∈ U) (E : Divisor Z) (𝓝 : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y 𝓝] (h𝓝 : MMP.Mori.IsRelativelyAmple g 𝓝)
    (e : 𝓝.restrict (g ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (g ∣_ U)).obj (E.divisorialSheaf.restrict U.ι)) :
    ∃ hc : Divisor.IsCartier (inverseTransformDivisor g E),
      Divisor.IsRelativelyAmple g (inverseTransformDivisor g E) hc := by
  have hbir := map_genericPoint_mem_biregularLocus_of_isSmallMorphism hg
  haveI : IsDominant g := hg.isBirationalMorphism.isDominant
  have hYU : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.genericPoint ∈ g ⁻¹ᵁ U := fun Γ => hUc _ (by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g (hbir Γ), Γ.coheight_genericPoint])
  have hηU : genericPoint Y ∈ g ⁻¹ᵁ U := hUc _ (by
    show Order.coheight (g (genericPoint Y)) ≤ 1
    rw [map_genericPoint_of_isDominant, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero]
    exact zero_le_one)
  haveI : Nonempty (g ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := isDominant_morphismRestrict g U
  obtain ⟨e'⟩ := nonempty_restrict_divisorialSheaf_inverseTransformDivisor_iso g hbir U hU E
  obtain ⟨N, hN, ⟨eN⟩⟩ := exists_isCartier_divisorialSheaf_iso 𝓝
  have hlin : Divisor.LinearlyEquivalent (inverseTransformDivisor g E) N :=
    MMP.Threefold.Mori.CanonUniq.linearlyEquivalent_of_iso hYU
      (e' ≪≫ e.symm ≪≫ (Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).mapIso eN.symm)
  have hc := Divisor.IsCartier.of_linearlyEquivalent hlin hN
  refine ⟨hc, ?_⟩
  obtain ⟨eL⟩ := hlin.nonempty_divisorialSheaf_iso
  haveI := hc.isInvertibleModule_divisorialSheaf
  exact isRelativelyAmple_of_iso g (eL ≪≫ eN) h𝓝

/-- The image of a prime divisor `P` under a proper morphism `f` is the closure of `f(η_P)`. -/
private theorem range_subschemeι_comp_eq_closure {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (P : MMP.Mori.PrimeDivisor X) :
    Set.range (P.idealSheaf.subschemeι ≫ f).base = closure {f P.genericPoint} := by
  rw [← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous f.continuous,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨P.idealSheaf.subschemeι y, ?_, rfl⟩
    have : P.idealSheaf.subschemeι y ∈ Set.range P.idealSheaf.subschemeι.base := ⟨y, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ : x ∈ Set.range P.idealSheaf.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
    exact ⟨y, rfl⟩

end FibreGeometry

/-! ### Stages, fibres and base change -/

section Stages

open Stacks.AlgebraicGeometry.ModuleLimits MMP.Spreading in
/-- **Isomorphisms of modules of finite presentation descend to a later stage** (Stacks 01ZR). -/
private theorem exists_stage_iso_pullback {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    {i₀ : (MMP.CoefficientModels.FGSub k₀ K)ᵒᵖ}
    (W : Over ((MMP.CoefficientModels.specDiagram k₀ K).obj i₀)) (hW : FinitePresentation W.hom)
    {XK : Scheme.{u}} (sK : XK ⟶ Spec (.of K)) (g : XK ⟶ W.left)
    (hpb : IsPullback g sK W.hom ((MMP.CoefficientModels.specCone k₀ K).π.app i₀))
    (A B : W.left.Modules) [A.IsFinitePresentation] [B.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback g).obj A ≅ (Scheme.Modules.pullback g).obj B) :
    ∃ m : Over i₀, Nonempty ((Scheme.Modules.pullback (pullback.snd
        ((MMP.CoefficientModels.specDiagram k₀ K).map m.hom) W.hom)).obj A ≅
      (Scheme.Modules.pullback (pullback.snd
        ((MMP.CoefficientModels.specDiagram k₀ K).map m.hom) W.hom)).obj B) := by
  let D := MMP.CoefficientModels.specDiagram k₀ K
  have : ∀ {a b : Over i₀} (f : a ⟶ b),
      IsAffineHom ((MMP.CoefficientModels.stageDiagram D W).map f) := fun f =>
    MMP.CoefficientModels.isAffineHom_stageMap D W f
  have : ∀ a, CompactSpace ((MMP.CoefficientModels.stageDiagram D W).obj a) := fun a =>
    MMP.CoefficientModels.compactSpace_stageObj D W hW a
  have : ∀ a, QuasiSeparatedSpace ((MMP.CoefficientModels.stageDiagram D W).obj a) := fun a =>
    MMP.CoefficientModels.quasiSeparatedSpace_stageObj D W hW a
  let i : Over i₀ := Over.mk (𝟙 _)
  let s := pullback.snd (D.map i.hom) W.hom
  have hsA := isFinitePresentation_pullback s A
  have hsB := isFinitePresentation_pullback s B
  let c' := MMP.CoefficientModels.legCone D W (MMP.CoefficientModels.specCone k₀ K)
    (Over.mk sK) g hpb
  have hl : c'.π.app i ≫ s = g := MMP.CoefficientModels.leg_snd D W _ _ _ hpb i
  obtain ⟨k, e, ⟨ψ⟩⟩ := exists_iso_of_isLimit (MMP.CoefficientModels.stageDiagram D W) c'
    (MMP.CoefficientModels.isLimitLegCone D W _ _ _ hpb
      (MMP.CoefficientModels.isLimitSpecCone k₀ K)) i
    ((Scheme.Modules.pullback s).obj A) ((Scheme.Modules.pullback s).obj B) hsA hsB
    (canIso _ s _ hl A ≪≫ φ ≪≫ (canIso _ s _ hl B).symm)
  have hk : (MMP.CoefficientModels.stageDiagram D W).map e ≫ s =
      pullback.snd (D.map k.hom) W.hom :=
    MMP.CoefficientModels.stageMap_snd D W e
  exact ⟨k, ⟨(canIso _ s _ hk A).symm ≪≫ ψ ≪≫ canIso _ s _ hk B⟩⟩

/-- **The fibre of a constant family over a section is the original scheme.** -/
private theorem isPullback_section_fibre {C : Type*} [Category C] [HasPullbacks C]
    {Z₀ T A B : C} (t₀ : Z₀ ⟶ T) (b : B ⟶ T) (a : A ⟶ B) (x : T ⟶ A) (hx : x ≫ a ≫ b = 𝟙 T) :
    ∃ jj : Z₀ ⟶ pullback a (pullback.snd t₀ b),
      jj ≫ pullback.snd _ _ ≫ pullback.fst _ _ = 𝟙 Z₀ ∧
        IsPullback jj t₀ (pullback.fst a (pullback.snd t₀ b)) x := by
  have h₁ : 𝟙 Z₀ ≫ t₀ = (t₀ ≫ x ≫ a) ≫ b := by
    rw [Category.id_comp, Category.assoc, Category.assoc, hx, Category.comp_id]
  let jj : Z₀ ⟶ pullback a (pullback.snd t₀ b) :=
    pullback.lift (t₀ ≫ x) (pullback.lift (𝟙 Z₀) (t₀ ≫ x ≫ a) h₁) (by
      rw [pullback.lift_snd, Category.assoc])
  have hjq : jj ≫ pullback.snd _ _ ≫ pullback.fst _ _ = 𝟙 Z₀ := by
    rw [pullback.lift_snd_assoc, pullback.lift_fst]
  refine ⟨jj, hjq, ?_⟩
  have hR : IsPullback (pullback.snd a (pullback.snd t₀ b) ≫ pullback.fst t₀ b)
      (pullback.fst a (pullback.snd t₀ b)) t₀ (a ≫ b) :=
    (IsPullback.of_hasPullback a (pullback.snd t₀ b)).flip.paste_horiz
      (IsPullback.of_hasPullback t₀ b)
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) hR
  rw [hjq, hx]
  exact IsPullback.id_horiz t₀

/-- **The fibre of a model over a later point maps to the stage model.** -/
private theorem isPullback_lift_fibre {C : Type*} [Category C] [HasPullbacks C] {Y A B T : C}
    (f : Y ⟶ B) (a : A ⟶ B) (x : T ⟶ A) :
    IsPullback (pullback.lift (pullback.snd f (x ≫ a) ≫ x) (pullback.fst f (x ≫ a))
      (by rw [Category.assoc, ← pullback.condition]))
      (pullback.snd f (x ≫ a)) (pullback.fst a f) x := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback a f).flip
  rw [pullback.lift_snd]
  exact IsPullback.of_hasPullback f (x ≫ a)

/-- A morphism followed by an isomorphism of the target is biregular over the transported
biregular locus. -/
private theorem mem_biregularLocus_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ≅ Z) {x : X}
    (hx : f x ∈ biregularLocus f) : (f ≫ e.hom) x ∈ biregularLocus (f ≫ e.hom) := by
  have hV := isBiregular_biregularLocus f
  set V := biregularLocus f
  let V' : Z.Opens := e.inv ⁻¹ᵁ V
  have hVV : e.hom ⁻¹ᵁ V' = V := by
    rw [← Scheme.Hom.comp_preimage, e.hom_inv_id, Scheme.Hom.id_preimage]
  haveI h1 : IsIso (f ∣_ (e.hom ⁻¹ᵁ V')) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictEq f hVV)).mpr hV
  have h2 : IsBiregular (f ≫ e.hom) V' := by
    change IsIso ((f ≫ e.hom) ∣_ V')
    rw [morphismRestrict_comp]
    haveI : IsIso (e.hom ∣_ V') := inferInstance
    exact IsIso.comp_isIso' h1 this
  refine le_biregularLocus h2 ?_
  show e.inv ((f ≫ e.hom) x) ∈ V
  rw [← Scheme.Hom.comp_apply, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact hx

/-- **Smallness is invariant under an isomorphism of the target.** -/
private theorem isSmallMorphism_comp_iso {k : Type u} [Field k] {X Z Z' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (h : IsSmallMorphism sX sZ f)
    (e : Z ≅ Z') {sZ' : Z' ⟶ Spec (.of k)} (he : e.hom ≫ sZ' = sZ)
    (hZ' : MMP.Mori.IsNormalVariety k sZ') [IrreducibleSpace X] [IrreducibleSpace Z'] :
    IsSmallMorphism sX sZ' (f ≫ e.hom) := by
  have key : ∀ x : X, Order.coheight x ≤ 1 → (f ≫ e.hom) x ∈ biregularLocus (f ≫ e.hom) := by
    intro x hx
    refine mem_biregularLocus_comp_iso f e ?_
    by_contra hfx
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h.two_le_codimension x hfx
    exact absurd (h2.trans hx) (by decide)
  haveI : IsProper f := h.isProper
  refine ⟨h.isNormalVariety_source, hZ', by rw [Category.assoc, he, h.comp_eq], inferInstance,
    ?_, ?_⟩
  · have hη : Order.coheight (genericPoint X) = 0 :=
      Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
    have hmem := key _ (hη ▸ zero_le_one)
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (f ≫ e.hom)
      ((f ≫ e.hom) ⁻¹ᵁ biregularLocus (f ≫ e.hom)) (biregularLocus (f ≫ e.hom))
      ⟨_, hmem⟩ ⟨_, hmem⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact isBiregular_biregularLocus _
  · refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => ?_
    by_contra hlt
    refine hx (key x ?_)
    rcases le_or_gt (Order.coheight x) 1 with h1 | h1
    · exact h1
    · exact absurd (Order.add_one_le_of_lt h1) (by rw [one_add_one_eq_two]; exact hlt)

/-- Smoothness of a morphism to the spectrum of a field, in the two spellings. -/
private theorem isSmoothScheme_iff_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] :
    MMP.Mori.IsSmoothScheme f ↔ Smooth f := by
  rw [MMP.Mori.IsSmoothScheme, MMP.Mori.smoothLocus_eq_smoothLocus,
    Scheme.Hom.smoothLocus_eq_top_iff]

/-- **Relative ampleness is stable under base change** (Stacks 0893). -/
private theorem isRelativelyAmple_pullback_of_isPullback {X S X' S' : Scheme.{u}} {p : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback p f' f g) [QuasiCompact f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    haveI := MMP.Fourfold.isInvertibleModule_pullback p L
    MMP.Mori.IsRelativelyAmple f' ((Scheme.Modules.pullback p).obj L) := by
  haveI := MMP.Fourfold.isInvertibleModule_pullback p L
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq ‹_›
  have hL' : Stacks.RelativeAmple.IsRelativelyAmple f L :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f L
      ‹_›).mpr hL
  have h2 := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq L hL'
  have h3 := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr f' _ _
    ((AlgebraicGeometry.GrothendieckExistence.modulePullbackIsoPullback p).app L)).mp h2
  exact (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f' _
    ‹_›).mp h3

open MMP.Threefold.Resolution in
/-- For a morphism biregular at the image of the generic point of a prime divisor `P`, the inverse
transform of a divisor has at `P` the coefficient of the prime divisor through `g(η_P)`. -/
private theorem exists_inverseTransformDivisor_apply_eq {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (P : MMP.Mori.PrimeDivisor Y) (hP : g P.genericPoint ∈ biregularLocus g) :
    ∃ Q : MMP.Mori.PrimeDivisor Z, MMP.Mori.PrimeDivisor.genericPoint Q = g P.genericPoint ∧
      ∀ {R : Type} [AddCommMonoid R] (F : DivisorWithCoeffs R Z),
        inverseTransformDivisor g F P = F Q := by
  have hcoh : Order.coheight (g P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus g hP, P.coheight_genericPoint]
  let Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = g P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨Q, hQ, fun F => ?_⟩
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ.symm hP)
    (fun E' h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((map_genericPoint_of_inverseTransformPrimeDivisor_eq_some h).1.symm.trans hQ.symm)) F

/-- **Every prime divisor of the normal target of a proper birational morphism is an image.** -/
private theorem exists_primeDivisor_map_genericPoint_eq {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (g : Y ⟶ Z) [IsProper g]
    (hg : MMP.Mori.IsBirationalMorphism g) (Q : MMP.Mori.PrimeDivisor Z) :
    ∃ P : MMP.Mori.PrimeDivisor Y, g P.genericPoint = Q.genericPoint ∧
      g P.genericPoint ∈ biregularLocus g := by
  have hQ : Q.genericPoint ∈ biregularLocus g :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
      (Q.coheight_genericPoint).le
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  let q : (biregularLocus g).toScheme := ⟨Q.genericPoint, hQ⟩
  let y := (inv (g ∣_ biregularLocus g)) q
  have hy' : (g ∣_ biregularLocus g) y = q := by
    change (inv (g ∣_ biregularLocus g) ≫ (g ∣_ biregularLocus g)) q = q
    rw [IsIso.inv_hom_id]
    rfl
  have hy : g y.1 = Q.genericPoint := by
    rw [← morphismRestrict_base_coe g (biregularLocus g) y, hy']
  have hcoh : Order.coheight y.1 = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hy ▸ hQ), hy,
      Q.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y.1 hcoh, ?_, ?_⟩
  · change g (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y.1 hcoh).genericPoint = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]
  · change g (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y.1 hcoh).genericPoint ∈ _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hy]
    exact hQ

/-- A projective scheme over a Noetherian ring is of finite presentation. -/
private theorem finitePresentation_of_isProjective {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) (hf : IsProjective f) : FinitePresentation f := by
  have hp := (isProjective_iff_isProjectiveMorphism_of_isAffine f).mp hf
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hp
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A diagram isomorphic to a base change is cartesian over it. -/
private lemma isCartesian_of_iso {J : Type u} [SmallCategory J] {S T : Scheme.{u}} (t : T ⟶ S)
    {X : J ⥤ Over T} {Y : J ⥤ Over S} (e : X ≅ Y ⋙ Over.pullback t) :
    MMP.Spreading.IsCartesian t X Y
      (fun j => (e.hom.app j).left ≫ pullback.fst (Y.obj j).hom t) where
  w {j j'} g := by
    have h := congrArg CommaMorphism.left (e.hom.naturality g)
    simp only [Functor.comp_map, Over.comp_left] at h
    have h2 : ((Over.pullback t).map (Y.map g)).left ≫ pullback.fst (Y.obj j').hom t =
        pullback.fst (Y.obj j).hom t ≫ (Y.map g).left :=
      (MMP.Spreading.isCartesian_pullback t Y).w g
    rw [← Category.assoc, h, Category.assoc, h2, Category.assoc]
  isPullback j := by
    have hsq : CommSq ((e.hom.app j).left ≫ pullback.fst (Y.obj j).hom t) (X.obj j).hom
        (Y.obj j).hom t := ⟨by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ t) (Over.w (e.hom.app j))⟩
    exact IsPullback.of_iso_pullback hsq ((Over.forget T).mapIso (e.app j)) rfl
      (Over.w (e.hom.app j))

end Stages

/-! ### The adjoint divisor over the smooth locus, before descent -/

section KSide

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]

/-- **The adjoint sheaf over a smooth open, before descent.** Let `Z` be the base change of `Z₀`,
`f⁺ : X⁺ ⟶ Z` biregular at the images of the generic points of prime divisors and `U ⊆ Z₀` a
smooth open. Over `V = (f⁺)⁻¹(π⁻¹ U)` the divisorial sheaf of the inverse transform of the base
change `E` of `E₀` is the pull-back of `𝒪_{Z₀}(E₀)|_U`. -/
private theorem nonempty_restrict_divisorialSheaf_inverseTransformDivisor_baseChange_iso
    {Z₀ Z Xp : Scheme.{u}} [IsIntegral Z₀] [CompactSpace Z₀] [IsLocallyNoetherian Z₀]
    [IsNormal Z₀] [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀} [LocallyOfFiniteType t₀]
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (fp : Xp ⟶ Z) [IsDominant fp]
    (hg : ∀ P : MMP.Mori.PrimeDivisor Xp, fp P.genericPoint ∈ biregularLocus fp)
    (U : Z₀.Opens) (hU : Smooth (U.ι ≫ t₀)) {E₀ : Divisor Z₀} {E : Divisor Z}
    (hE : IsBaseChange πZ E₀ E) (V : Xp.Opens) [Nonempty V] (hV : V = fp ⁻¹ᵁ πZ ⁻¹ᵁ U)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι = V.ι ≫ fp ≫ πZ) :
    Nonempty ((Divisor.divisorialSheaf (inverseTransformDivisor fp E)).restrict V.ι ≅
      (Scheme.Modules.pullback q).obj (E₀.divisorialSheaf.restrict U.ι)) := by
  subst hV
  have hq' : q = fp ∣_ (πZ ⁻¹ᵁ U) ≫ πZ ∣_ U := by
    rw [← cancel_mono U.ι, hq, Category.assoc, morphismRestrict_ι,
      ← Category.assoc (fp ∣_ (πZ ⁻¹ᵁ U)), morphismRestrict_ι, Category.assoc]
  subst hq'
  have : LocallyOfFiniteType t := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hZ ‹_›
  have hUsq : IsPullback (πZ ∣_ U) ((πZ ⁻¹ᵁ U).ι ≫ t) (U.ι ≫ t₀)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (isPullback_morphismRestrict πZ U).paste_vert hZ
  haveI : Nonempty (πZ ⁻¹ᵁ U) := ⟨(fp ∣_ (πZ ⁻¹ᵁ U)) (Classical.arbitrary _)⟩
  haveI : Nonempty U := ⟨(πZ ∣_ U) (Classical.arbitrary _)⟩
  have hUs : MMP.Mori.IsSmoothScheme (U.ι ≫ t₀) := (isSmoothScheme_iff_smooth _).mpr hU
  have hUKs : MMP.Mori.IsSmoothScheme ((πZ ⁻¹ᵁ U).ι ≫ t) :=
    (isSmoothScheme_iff_smooth _).mpr (MorphismProperty.of_isPullback (P := @Smooth) hUsq hU)
  haveI := isDominant_morphismRestrict fp (πZ ⁻¹ᵁ U)
  obtain ⟨e₁⟩ :=
    nonempty_restrict_divisorialSheaf_inverseTransformDivisor_iso fp hg (πZ ⁻¹ᵁ U) hUKs E
  have : Surjective (πZ ∣_ U) := surjective_of_isPullback hUsq
  haveI : IsNoetherian Z₀ := ⟨⟩
  haveI : IsNoetherian Z := ⟨⟩
  haveI : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  haveI : CompactSpace (πZ ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have hc := MMP.Fourfold.isCartier_of_isSmoothScheme hUs (DivisorWithCoeffs.restrictOpen U E₀)
  have hB : ∀ Z' : irreducibleComponents (πZ ⁻¹ᵁ U).toScheme,
      (πZ ∣_ U) (componentGenericPoint _ Z') ∉
        DivisorWithCoeffs.supp (DivisorWithCoeffs.restrictOpen U E₀) :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' (πZ ∣_ U) _
  have hbc := isBaseChange_pullback hUsq hc hB
  have hres := isBaseChange_restrictOpen hZ U hE
  have heq : Divisor.pullback (DivisorWithCoeffs.restrictOpen U E₀) hc hB =
      DivisorWithCoeffs.restrictOpen (πZ ⁻¹ᵁ U) E :=
    (eq_iff_of_isBaseChange hUsq hbc hres).mp rfl
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hc (πZ ∣_ U) hB
  rw [heq] at e₂
  exact ⟨e₁ ≪≫ (Scheme.Modules.pullback (fp ∣_ (πZ ⁻¹ᵁ U))).mapIso
      ((Divisor.divisorialSheafRestrictOpenIso E (πZ ⁻¹ᵁ U)).symm ≪≫ e₂ ≪≫
        (Scheme.Modules.pullback (πZ ∣_ U)).mapIso
          (Divisor.divisorialSheafRestrictOpenIso E₀ U)) ≪≫
    (Scheme.Modules.pullbackComp (fp ∣_ (πZ ⁻¹ᵁ U)) (πZ ∣_ U)).app _⟩

/-- **The integral adjoint divisor and its descent.** If `L = m (f⁺⁻¹_* C + f⁺⁻¹_* D)` is
integral, where `C`, `D` are base changes of `C₀`, `D₀` and `f⁺` is proper, birational and
biregular at the images of the generic points of prime divisors, then `L = f⁺⁻¹_* E` for the base
change `E` of an integral divisor `E₀` with `E₀ = m (C₀ + D₀)`. -/
private theorem exists_isBaseChange_inverseTransformDivisor_eq {Z₀ Z Xp : Scheme.{u}}
    [IsIntegral Z₀] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Xp]
    {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀} [LocallyOfFiniteType t₀]
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {C₀ : Divisor Z₀} {D₀ : QDivisor Z₀} {C : Divisor Z} {D : QDivisor Z}
    (hC : IsBaseChange πZ C₀ C) (hD : IsBaseChange πZ D₀ D) (fp : Xp ⟶ Z) [IsProper fp]
    (hfp : MMP.Mori.IsBirationalMorphism fp)
    (hg : ∀ P : MMP.Mori.PrimeDivisor Xp, fp P.genericPoint ∈ biregularLocus fp)
    (m : ℕ) (L : Divisor Xp)
    (hL : Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor (inverseTransformDivisor fp C) +
      inverseTransformDivisor fp D)) :
    ∃ (E₀ : Divisor Z₀) (E : Divisor Z), IsBaseChange πZ E₀ E ∧
      inverseTransformDivisor fp E = L ∧
        Divisor.toQDivisor E₀ = (m : ℤ) • (Divisor.toQDivisor C₀ + D₀) := by
  classical
  have : Surjective πZ := surjective_of_isPullback hZ
  have hLP (P : MMP.Mori.PrimeDivisor Xp) (Q : MMP.Mori.PrimeDivisor Z)
      (hQ : ∀ {R : Type} [AddCommMonoid R] (F : DivisorWithCoeffs R Z),
        inverseTransformDivisor fp F P = F Q) :
      ((L P : ℤ) : ℚ) = (m : ℚ) * ((C Q : ℚ) + D Q) := by
    have h := congrArg (fun F : QDivisor Xp => F P) hL
    have h1 : (Divisor.toQDivisor (inverseTransformDivisor fp C)) P =
        ((inverseTransformDivisor fp C P : ℤ) : ℚ) := rfl
    have h2 : (Divisor.toQDivisor L) P = ((L P : ℤ) : ℚ) := rfl
    simp only [Finsupp.smul_apply, Finsupp.add_apply, h1, h2, hQ C, hQ D, zsmul_eq_mul,
      Int.cast_natCast] at h
    exact h
  have hint (Q : MMP.Mori.PrimeDivisor Z) : ∃ n : ℤ, (n : ℚ) = (m : ℚ) * ((C Q : ℚ) + D Q) := by
    obtain ⟨P, hPQ, hPb⟩ := exists_primeDivisor_map_genericPoint_eq fp hfp Q
    obtain ⟨Q', hQ', hF⟩ := exists_inverseTransformDivisor_apply_eq fp P hPb
    obtain rfl : Q' = Q :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hQ'.trans hPQ)
    exact ⟨L P, hLP P Q' hF⟩
  choose nE hnE using hint
  have hint₀ (Q₀ : MMP.Mori.PrimeDivisor Z₀) :
      ∃ n : ℤ, (n : ℚ) = (m : ℚ) * ((C₀ Q₀ : ℚ) + D₀ Q₀) := by
    obtain ⟨Q, hQ, -⟩ := exists_primeDivisor_baseChange hZ Q₀
    refine ⟨nE Q, ?_⟩
    rw [hnE Q, show C Q = C₀ Q₀ from hC.1 Q₀ Q hQ, show D Q = D₀ Q₀ from hD.1 Q₀ Q hQ]
  choose nE₀ hnE₀ using hint₀
  have hsupp {X : Scheme.{u}} (c : Divisor X) (d : QDivisor X) (n : MMP.Mori.PrimeDivisor X → ℤ)
      (hn : ∀ Q, (n Q : ℚ) = (m : ℚ) * ((c Q : ℚ) + d Q)) (Q : MMP.Mori.PrimeDivisor X)
      (hQ : n Q ≠ 0) : Q ∈ c.support ∪ d.support := by
    by_contra hQs
    simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hQs
    apply hQ
    have h := hn Q
    rw [hQs.1, hQs.2] at h
    exact_mod_cast (by simpa using h : (n Q : ℚ) = 0)
  let E : Divisor Z := Finsupp.onFinset (C.support ∪ D.support) nE (hsupp C D nE hnE)
  let E₀ : Divisor Z₀ := Finsupp.onFinset (C₀.support ∪ D₀.support) nE₀ (hsupp C₀ D₀ nE₀ hnE₀)
  have hEQ (Q : MMP.Mori.PrimeDivisor Z) : E Q = nE Q := Finsupp.onFinset_apply
  have hE₀Q (Q₀ : MMP.Mori.PrimeDivisor Z₀) : E₀ Q₀ = nE₀ Q₀ := Finsupp.onFinset_apply
  refine ⟨E₀, E, ⟨fun P₀ P hP => ?_, fun P hP => ?_⟩, ?_, ?_⟩
  · change E P = E₀ P₀
    rw [hEQ, hE₀Q]
    apply Int.cast_injective (α := ℚ)
    rw [hnE, hnE₀, show C P = C₀ P₀ from hC.1 P₀ P hP, show D P = D₀ P₀ from hD.1 P₀ P hP]
  · change E P ≠ 0 at hP
    rw [hEQ] at hP
    rcases Finset.mem_union.mp (hsupp C D nE hnE P hP) with h | h
    · exact hC.2 P (Finsupp.mem_support_iff.mp h)
    · exact hD.2 P (Finsupp.mem_support_iff.mp h)
  · ext P
    obtain ⟨Q, -, hF⟩ := exists_inverseTransformDivisor_apply_eq fp P (hg P)
    change inverseTransformDivisor fp E P = L P
    rw [hF E, hEQ]
    apply Int.cast_injective (α := ℚ)
    rw [hnE, hLP P Q hF]
  · ext Q₀
    change ((E₀ Q₀ : ℤ) : ℚ) = ((m : ℤ) • (Divisor.toQDivisor C₀ + D₀)) Q₀
    rw [hE₀Q, hnE₀, Finsupp.smul_apply, Finsupp.add_apply, zsmul_eq_mul, Int.cast_natCast]
    rfl

end KSide

/-- **Small lc models descend along an extension of algebraically closed fields.** Let
`k₀ ⊆ K` be algebraically closed fields of characteristic zero, `Z₀` a normal projective variety
over `k₀` with base change `Z`, and `C₀`, `D₀` divisors on `Z₀` with base changes `C`, `D`. Let
`f⁺ : X⁺ ⟶ Z` be a small projective morphism from a normal projective variety such that
`(X⁺, f⁺⁻¹_* D)` is lc and `f⁺⁻¹_* (C + D)` is `f⁺`-ample. Then there is such a small projective
`g : Y ⟶ Z₀` over `k₀`, with `(Y, g⁻¹_* D₀)` lc and `g⁻¹_* (C₀ + D₀)` `g`-ample. -/
private theorem exists_small_lc_model_of_isPullback
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    [CharZero k₀] {Z₀ Z Xp : Scheme.{u}} [IsNormal Z₀]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {t₀ : Z₀ ⟶ Spec (.of k₀)} {t : Z ⟶ Spec (.of K)} {πZ : Z ⟶ Z₀}
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    {C₀ : Divisor Z₀} {D₀ : QDivisor Z₀} {C : Divisor Z} {D : QDivisor Z}
    (hC : IsBaseChange πZ C₀ C) (hD : IsBaseChange πZ D₀ D)
    {sXp : Xp ⟶ Spec (.of K)} {fp : Xp ⟶ Z} (hXp : MMP.Mori.IsProjectiveVariety K sXp)
    (hdXp : topologicalKrullDim Xp ≠ 0)
    (hsmall : IsSmallMorphism sXp t fp) (hproj : IsProjectiveMorphism fp)
    (hlc : MMP.Intersection.IsLogCanonicalPair sXp (inverseTransformDivisor fp D))
    (hamp : (Divisor.toQDivisor (inverseTransformDivisor fp C) +
      inverseTransformDivisor fp D).HasRelativelyAmpleMultiple fp) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of k₀)) (g : Y ⟶ Z₀),
      MMP.Mori.IsProjectiveVariety k₀ sY ∧ IsSmallMorphism sY t₀ g ∧ IsProjectiveMorphism g ∧
        MMP.Intersection.IsLogCanonicalPair sY (inverseTransformDivisor g D₀) ∧
        (Divisor.toQDivisor (inverseTransformDivisor g C₀) +
          inverseTransformDivisor g D₀).HasRelativelyAmpleMultiple g := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k₀ K).injective
  -- the boundary `B⁺`, a log resolution `μ : W ⟶ X⁺` of `(X⁺, B⁺)` and the crepant boundary
  set Bp : QDivisor Xp := inverseTransformDivisor fp D with hBp
  have hXpN : MMP.Mori.IsNormalVariety K sXp := ⟨hXp.toIsVariety, inferInstance⟩
  obtain ⟨W, μ, hμ, hμp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sXp hXpN
    (MMP.Mori.QDivisor.toRDivisor Bp)
  obtain ⟨-, n, KXp, hKXp, -⟩ := hlc.1
  have hW : MMP.Mori.IsNormalVariety K (μ ≫ sXp) :=
    (MMP.Mori.IsSmoothResolution.isNormalVariety hXpN hμ.toIsSmoothResolution).1
  obtain ⟨⟨BW, hBW, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hlc.1 hKXp μ hW
    hμ.isBirationalMorphism
  -- the components of `B⁺` and of `B_W`
  let P : Fin Bp.support.card → MMP.Mori.PrimeDivisor Xp := fun l => (Bp.support.equivFin.symm l).1
  let P' : Fin BW.support.card → MMP.Mori.PrimeDivisor W := fun l => (BW.support.equivFin.symm l).1
  have hBpsum : ∑ l, Finsupp.single (P l) (Bp (P l)) = Bp :=
    ((Equiv.sum_comp Bp.support.equivFin.symm fun x => Finsupp.single x.1 (Bp x.1)).trans
      (Finset.sum_coe_sort _ fun x => Finsupp.single x (Bp x))).trans (Finsupp.sum_single Bp)
  have hBWsum : ∑ l, Finsupp.single (P' l) (BW (P' l)) = BW :=
    ((Equiv.sum_comp BW.support.equivFin.symm fun x => Finsupp.single x.1 (BW x.1)).trans
      (Finset.sum_coe_sort _ fun x => Finsupp.single x (BW x))).trans (Finsupp.sum_single BW)
  -- the relatively ample multiple of the adjoint
  obtain ⟨mL, hmL, L, hL, hLeq, hLamp⟩ := hamp
  haveI hLinv := hL.isInvertibleModule_divisorialSheaf
  -- the diagram `Z ⟵ X⁺ ⟵ W` with the components as closed subschemes
  letI := Vtx.partialOrder (m := Bp.support.card) (n := BW.support.card)
  letI := Vtx.fintype (m := Bp.support.card) (n := BW.support.card)
  letI := Vtx.finCategory (m := Bp.support.card) (n := BW.support.card)
  let ιP : ∀ l, (P l).idealSheaf.subscheme ⟶ Xp := fun l => (P l).idealSheaf.subschemeι
  let ιE : ∀ l, (P' l).idealSheaf.subscheme ⟶ W := fun l => (P' l).idealSheaf.subschemeι
  let Xd := Vtx.diagram t sXp fp μ ιP ιE hsmall.comp_eq
  obtain ⟨_, _, _, _⟩ := isIntegral_isNormal_of_isPullback t₀ t πZ hZ hZ₀
  have hZK := (isProjectiveVariety_iff_of_isPullback _ _ _ hZ).1 hZ₀
  have hint : ∀ j, IsIntegral (Xd.obj j).left := by
    intro j
    cases j with
    | z => exact inferInstanceAs (IsIntegral Z)
    | p => exact inferInstanceAs (IsIntegral Xp)
    | w => exact hW.1.toIsIntegral
    | c l => exact (P l).integral
    | e l => exact (P' l).integral
  have hprojd : ∀ j, IsProjective (Xd.obj j).hom := by
    intro j
    cases j with
    | z => exact hZK.isProjective.isProjective
    | p => exact hXp.isProjective.isProjective
    | w => exact (hμp.comp hXp.isProjective).isProjective
    | c l => exact isProjective_comp_of_isClosedImmersion (ιP l) hXp.isProjective.isProjective
    | e l =>
      have hWp := (hμp.comp hXp.isProjective).isProjective
      exact isProjective_comp_of_isClosedImmersion (ιE l) hWp
  obtain ⟨R, hR, Y, e, 𝓜, h𝓜, h𝓛, hY₁, hY₂, -, hY₃, -, hY₅, -, -, hfib⟩ :=
    MMP.exists_fg_subalgebra_model_of_isProjective_of_finCategory k₀ K Xd hint hprojd
      (ι := PUnit.{u + 1}) (fun _ => Vtx.p) (fun _ => L.divisorialSheaf)
      (h𝓛 := fun _ => by exact hLinv)
  -- the noetherian stage ring and the base maps
  haveI : IsNoetherianRing R := MMP.CoefficientModels.isNoetherianRing_of_fg k₀ K ⟨R, hR⟩
  let κR := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let φR := Spec.map (CommRingCat.ofHom (algebraMap k₀ R))
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) = κR ≫ φR := by
    change _ = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ R))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  -- the arrows of the diagram
  let hpz : (Vtx.p : Vtx.{u} Bp.support.card BW.support.card) ⟶ Vtx.z := homOfLE trivial
  let hwp : (Vtx.w : Vtx.{u} Bp.support.card BW.support.card) ⟶ Vtx.p := homOfLE trivial
  let hcp : ∀ l, (Vtx.c l : Vtx.{u} Bp.support.card BW.support.card) ⟶ Vtx.p :=
    fun _ => homOfLE trivial
  let hcz : ∀ l, (Vtx.c l : Vtx.{u} Bp.support.card BW.support.card) ⟶ Vtx.z :=
    fun _ => homOfLE trivial
  let hew : ∀ l, (Vtx.e l : Vtx.{u} Bp.support.card BW.support.card) ⟶ Vtx.w :=
    fun _ => homOfLE trivial
  have hXdpz : (Xd.map hpz).left = fp := rfl
  have hXdwp : (Xd.map hwp).left = μ := rfl
  have hXdcp (l) : (Xd.map (hcp l)).left = ιP l := rfl
  have hXdcz (l) : (Xd.map (hcz l)).left = ιP l ≫ fp := rfl
  have hXdew (l) : (Xd.map (hew l)).left = ιE l := rfl
  -- the model is cartesian over `K`
  have hcart := isCartesian_of_iso κR e
  let leg : ∀ v, (Xd.obj v).left ⟶ (Y.obj v).left :=
    fun v => (e.hom.app v).left ≫ pullback.fst (Y.obj v).hom κR
  have hfp (v) : FinitePresentation (Y.obj v).hom :=
    finitePresentation_of_isProjective _ (hY₁ v).1
  -- the smooth locus of `Z₀` and the integral adjoint divisors
  have : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  haveI : IsIntegral Z₀ := hZ₀.toIsIntegral
  haveI : QuasiCompact t₀ := hZ₀.toQuasiCompact
  haveI : CompactSpace Z₀ := QuasiCompact.compactSpace_of_compactSpace t₀
  haveI : IsLocallyNoetherian Z₀ := LocallyOfFiniteType.isLocallyNoetherian t₀
  have hZ₀N : MMP.Mori.IsNormalVariety k₀ t₀ := ⟨hZ₀.toIsVariety, inferInstance⟩
  obtain ⟨U, -, hUsm, hUc⟩ := MMP.Spreading.exists_smooth_open_of_isNormalVariety t₀ hZ₀N
  have hbirfp := map_genericPoint_mem_biregularLocus_of_isSmallMorphism hsmall
  haveI : IsProper fp := hsmall.isProper
  haveI : IsDominant fp := hsmall.isBirationalMorphism.isDominant
  obtain ⟨E₀, E, hEb, hEL, hE₀⟩ := exists_isBaseChange_inverseTransformDivisor_eq hZ hC hD fp
    hsmall.isBirationalMorphism hbirfp mL L hLeq
  -- the constant model of `Z₀` and the stage at which it agrees with the model of `Z`
  let D' := MMP.CoefficientModels.specDiagram k₀ K
  let cc := MMP.CoefficientModels.specCone k₀ K
  have hcc := MMP.CoefficientModels.isLimitSpecCone k₀ K
  let i₀ : (MMP.CoefficientModels.FGSub k₀ K)ᵒᵖ := Opposite.op ⟨R, hR⟩
  let Wp : Over (D'.obj i₀) := Y.obj Vtx.p
  let Wz : Over (D'.obj i₀) := Y.obj Vtx.z
  let W' : Over (D'.obj i₀) := Over.mk (pullback.snd t₀ φR)
  have hg'w : πZ ≫ t₀ = (t ≫ κR) ≫ φR := by rw [hZ.w, hφ, Category.assoc]
  let g' : Z ⟶ W'.left := pullback.lift πZ (t ≫ κR) hg'w
  have hpb' : IsPullback g' (Over.mk t).hom W'.hom (cc.π.app i₀) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst t₀ φR) (h₂₂ := φR) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback t₀ φR)
    rw [pullback.lift_fst]
    change IsPullback πZ t t₀ (κR ≫ φR)
    rw [← hφ]
    exact hZ
  have hfp₀ : FinitePresentation t₀ :=
    finitePresentation_of_isProjective t₀ hZ₀.isProjective.isProjective
  have hW' : FinitePresentation W'.hom :=
    ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback t₀ φR) hfp₀.1,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback t₀ φR) hfp₀.2.1,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback t₀ φR) hfp₀.2.2⟩
  obtain ⟨m₁, e₁, he₁, hle₁⟩ := exists_stage_iso D' hcc (W := Wz) (hfp Vtx.z) hW'
    (Over.mk t) (leg Vtx.z) (hcart.isPullback Vtx.z) g' hpb'
  -- the model of `X⁺` at the stage `m₁`, and its map to `Z₀`
  haveI : IsNoetherianRing m₁.left.unop.1 :=
    MMP.CoefficientModels.isNoetherianRing_of_fg k₀ K m₁.left.unop
  let 𝒳₁ := MMP.CoefficientModels.stageObj D' Wp m₁
  haveI : LocallyOfFinitePresentation (pullback.fst (D'.map m₁.hom) Wp.hom) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip (hfp Vtx.p).1
  haveI : QuasiCompact (pullback.fst (D'.map m₁.hom) Wp.hom) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip (hfp Vtx.p).2.1
  haveI : QuasiSeparated (pullback.fst (D'.map m₁.hom) Wp.hom) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip (hfp Vtx.p).2.2
  haveI : IsLocallyNoetherian 𝒳₁ :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (D'.map m₁.hom) Wp.hom)
  let g₁ : 𝒳₁ ⟶ MMP.CoefficientModels.stageObj D' Wz m₁ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ (Y.map hpz).left) (by
      rw [pullback.condition]
      exact congrArg (fun φ => pullback.snd (D'.map m₁.hom) Wp.hom ≫ φ)
        (Over.w (Y.map hpz)).symm)
  let q₀ : MMP.CoefficientModels.stageObj D' W' m₁ ⟶ Z₀ :=
    pullback.snd _ _ ≫ pullback.fst t₀ φR
  let h₁ : 𝒳₁ ⟶ Z₀ := g₁ ≫ e₁.hom ≫ q₀
  let legp := MMP.CoefficientModels.leg D' Wp cc (Over.mk sXp) (leg Vtx.p)
    (hcart.isPullback Vtx.p) m₁
  let legz := MMP.CoefficientModels.leg D' Wz cc (Over.mk t) (leg Vtx.z)
    (hcart.isPullback Vtx.z) m₁
  have hpf : legp ≫ pullback.fst _ _ = sXp ≫ cc.π.app m₁.left :=
    MMP.CoefficientModels.leg_fst _ _ _ _ _ _ _
  have hps : legp ≫ pullback.snd _ _ = leg Vtx.p := MMP.CoefficientModels.leg_snd _ _ _ _ _ _ _
  have hzf : legz ≫ pullback.fst _ _ = t ≫ cc.π.app m₁.left :=
    MMP.CoefficientModels.leg_fst _ _ _ _ _ _ _
  have hzs : legz ≫ pullback.snd _ _ = leg Vtx.z := MMP.CoefficientModels.leg_snd _ _ _ _ _ _ _
  have hlegp : legp ≫ h₁ = fp ≫ πZ := by
    have h1 : legp ≫ g₁ = fp ≫ legz := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hpf, Category.assoc, hzf,
          ← show fp ≫ t = sXp from hsmall.comp_eq]
        exact Category.assoc _ _ _
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hps, Category.assoc, hzs]
        exact (hcart.w hpz).symm
    have h2 : MMP.CoefficientModels.leg D' W' cc (Over.mk t) g' hpb' m₁ ≫ q₀ = πZ := by
      have h3 : MMP.CoefficientModels.leg D' W' cc (Over.mk t) g' hpb' m₁ ≫
          pullback.snd _ _ = g' := MMP.CoefficientModels.leg_snd _ _ _ _ _ _ _
      change MMP.CoefficientModels.leg D' W' cc (Over.mk t) g' hpb' m₁ ≫
        pullback.snd _ _ ≫ pullback.fst t₀ φR = πZ
      rw [← Category.assoc, h3]
      exact pullback.lift_fst _ _ _
    calc legp ≫ h₁ = (legp ≫ g₁) ≫ e₁.hom ≫ q₀ := by simp only [h₁, Category.assoc]
      _ = fp ≫ (legz ≫ e₁.hom) ≫ q₀ := by rw [h1]; simp only [Category.assoc]
      _ = fp ≫ πZ := by rw [hle₁, h2]
  -- the open over the smooth locus, its sheaves, and their isomorphism over `K`
  let 𝒱₁ : 𝒳₁.Opens := h₁ ⁻¹ᵁ U
  let VK : Xp.Opens := legp ⁻¹ᵁ 𝒱₁
  have hVK : VK = fp ⁻¹ᵁ πZ ⁻¹ᵁ U := by
    change legp ⁻¹ᵁ h₁ ⁻¹ᵁ U = fp ⁻¹ᵁ πZ ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, hlegp, Scheme.Hom.comp_preimage]
  have hηXp : genericPoint Xp ∈ VK := by
    rw [hVK]
    have hsurj : Surjective πZ := surjective_of_isPullback hZ
    show πZ (fp (genericPoint Xp)) ∈ U
    rw [map_genericPoint_of_isDominant, map_genericPoint_of_isDominant]
    exact hUc _ (by
      rw [Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y]
      exact zero_le_one)
  haveI : Nonempty VK := ⟨⟨_, hηXp⟩⟩
  haveI : Nonempty U := ⟨⟨πZ (fp (genericPoint Xp)), by
    have h := hηXp
    rw [hVK] at h
    exact h⟩⟩
  let gK : VK.toScheme ⟶ 𝒱₁.toScheme := legp ∣_ 𝒱₁
  have hcU : Divisor.IsCartier (DivisorWithCoeffs.restrictOpen U E₀) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme ((isSmoothScheme_iff_smooth _).mpr hUsm) _
  haveI : IsNoetherian Z₀ := ⟨⟩
  haveI : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  let 𝓔 : U.toScheme.Modules := Divisor.divisorialSheaf (DivisorWithCoeffs.restrictOpen U E₀)
  haveI h𝓔 : Stacks.Ample.IsInvertibleModule U.toScheme 𝓔 := hcU.isInvertibleModule_divisorialSheaf
  let A : 𝒱₁.toScheme.Modules :=
    (Scheme.Modules.pullback (𝒱₁.ι ≫ pullback.snd _ _)).obj (𝓜 PUnit.unit)
  let B : 𝒱₁.toScheme.Modules := (Scheme.Modules.pullback (h₁ ∣_ U)).obj 𝓔
  obtain ⟨θ⟩ := h𝓛 PUnit.unit
  have hAleg : gK ≫ 𝒱₁.ι ≫ pullback.snd _ _ = VK.ι ≫ leg Vtx.p := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hps]
  have hBleg : (gK ≫ h₁ ∣_ U) ≫ U.ι = VK.ι ≫ fp ≫ πZ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      hlegp]
  obtain ⟨eK⟩ := nonempty_restrict_divisorialSheaf_inverseTransformDivisor_baseChange_iso hZ fp
    hbirfp U hUsm hEb VK hVK (gK ≫ h₁ ∣_ U) hBleg
  rw [hEL] at eK
  let φK : (Scheme.Modules.pullback gK).obj A ≅ (Scheme.Modules.pullback gK).obj B :=
    (Scheme.Modules.pullbackComp gK _).app _ ≪≫ (Scheme.Modules.pullbackCongr hAleg).app _ ≪≫
    ((Scheme.Modules.pullbackComp VK.ι (leg Vtx.p)).app _).symm ≪≫
    (Scheme.Modules.pullback VK.ι).mapIso
      (θ.symm : (Scheme.Modules.pullback (leg Vtx.p)).obj (𝓜 PUnit.unit) ≅ _) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback VK.ι).symm.app _ ≪≫ eK ≪≫
    (Scheme.Modules.pullback (gK ≫ h₁ ∣_ U)).mapIso
      (Divisor.divisorialSheafRestrictOpenIso E₀ U).symm ≪≫
    ((Scheme.Modules.pullbackComp gK (h₁ ∣_ U)).app _).symm
  -- the isomorphism descends to a later stage `m₂`
  let W'' : Over (D'.obj m₁.left) :=
    Over.mk (𝒱₁.ι ≫ pullback.fst (D'.map m₁.hom) Wp.hom)
  have hW'' : FinitePresentation W''.hom :=
    ⟨(inferInstance : LocallyOfFinitePresentation (𝒱₁.ι ≫ pullback.fst (D'.map m₁.hom) Wp.hom)),
      (inferInstance : QuasiCompact (𝒱₁.ι ≫ pullback.fst (D'.map m₁.hom) Wp.hom)),
      (inferInstance : QuasiSeparated (𝒱₁.ι ≫ pullback.fst (D'.map m₁.hom) Wp.hom))⟩
  have hpbK : IsPullback gK (VK.ι ≫ sXp) W''.hom (cc.π.app m₁.left) :=
    (isPullback_morphismRestrict legp 𝒱₁).paste_vert
      (MMP.CoefficientModels.isPullback_leg D' Wp cc (Over.mk sXp) (leg Vtx.p)
        (hcart.isPullback Vtx.p) m₁)
  haveI := h𝓜 PUnit.unit
  haveI : LocallyOfFinitePresentation (Y.obj Vtx.p).hom := (hfp Vtx.p).1
  haveI : IsLocallyNoetherian (Y.obj Vtx.p).left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y.obj Vtx.p).hom
  haveI : (𝓜 PUnit.unit).IsFinitePresentation :=
    have := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _
      (𝓜 PUnit.unit)
    isFinitePresentation_of_isCoherent (𝓜 PUnit.unit)
  haveI : 𝓔.IsFinitePresentation :=
    have := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ 𝓔
    isFinitePresentation_of_isCoherent 𝓔
  haveI : A.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ _
  haveI : B.IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ _
  obtain ⟨m₂, ⟨ψ⟩⟩ := exists_stage_iso_pullback W'' hW'' (VK.ι ≫ sXp) gK hpbK A B φK
  -- the components of the boundary are base changes
  have hrangeP (l : Fin Bp.support.card) :
      Set.range (ιP l ≫ fp).base = closure {fp (P l).genericPoint} :=
    range_subschemeι_comp_eq_closure fp (P l)
  have hcomp (l : Fin Bp.support.card) : ∃ Q₀ : MMP.Mori.PrimeDivisor Z₀,
      Bp (P l) = D₀ Q₀ ∧ Set.range (ιP l ≫ fp).base = πZ.base ⁻¹' Q₀.support := by
    obtain ⟨G, hG, hGF⟩ := exists_inverseTransformDivisor_apply_eq fp (P l) (hbirfp (P l))
    have hBG : Bp (P l) = D G := hGF D
    have hne : D G ≠ 0 := by
      rw [← hBG]; exact Finsupp.mem_support_iff.mp (Bp.support.equivFin.symm l).2
    obtain ⟨Q₀, hQ₀⟩ := hD.2 G hne
    refine ⟨Q₀, hBG.trans (hD.1 Q₀ G hQ₀), ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hQ₀]
    change _ = closure {MMP.Mori.PrimeDivisor.genericPoint G}
    rw [hG, hrangeP]
  choose Q hQD hQr using hcomp
  -- properness of the model
  have hvprop (v) : IsProper (Y.obj v).hom :=
    isProper_of_isProjectiveMorphism _
      ((isProjective_iff_isProjectiveMorphism_of_isAffine _).mp (hY₁ v).1)
  have hmprop {v v'} (f : v ⟶ v') : IsProper (Y.map f).left := by
    haveI := hvprop v
    haveI := hvprop v'
    haveI : IsProper ((Y.map f).left ≫ (Y.obj v').hom) := by rw [Over.w (Y.map f)]; infer_instance
    exact IsProper.of_comp (Y.map f).left (Y.obj v').hom
  -- at the stage `m₁`, the images of the components on the model of `Z` are those of `Q l`
  let S₁ := m₁.left.unop
  let 𝒲₁ := MMP.CoefficientModels.stageObj D' W' m₁
  let f𝒲 : 𝒲₁ ⟶ Spec (.of S₁.1) := pullback.fst (D'.map m₁.hom) W'.hom
  have hf𝒲 : FinitePresentation f𝒲 :=
    ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D'.map m₁.hom) W'.hom).flip
        hW'.1,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D'.map m₁.hom) W'.hom).flip
        hW'.2.1,
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D'.map m₁.hom) W'.hom).flip
        hW'.2.2⟩
  let leg' := MMP.CoefficientModels.leg D' W' cc (Over.mk t) g' hpb' m₁
  have hleg'pb : IsPullback leg' t f𝒲 (Spec.map (CommRingCat.ofHom (algebraMap S₁.1 K))) :=
    MMP.CoefficientModels.isPullback_leg D' W' cc (Over.mk t) g' hpb' m₁
  have hleg'q : leg' ≫ q₀ = πZ := by
    have h3 : leg' ≫ pullback.snd _ _ = g' := MMP.CoefficientModels.leg_snd _ _ _ _ _ _ _
    change leg' ≫ pullback.snd _ _ ≫ pullback.fst t₀ φR = πZ
    rw [← Category.assoc, h3]
    exact pullback.lift_fst _ _ _
  have hlegzinv : leg' ≫ e₁.inv = legz := by
    change MMP.CoefficientModels.leg D' W' cc (Over.mk t) g' hpb' m₁ ≫ e₁.inv = legz
    rw [← hle₁, Category.assoc, e₁.hom_inv_id, Category.comp_id]
  let Tl (l : Fin Bp.support.card) : TopologicalSpace.Closeds (Y.obj Vtx.z).left :=
    ⟨Set.range (Y.map (hcz l)).left.base,
      have := hmprop (hcz l)
      (Y.map (hcz l)).left.isClosedMap.isClosed_range⟩
  let C₁ (l : Fin Bp.support.card) : TopologicalSpace.Closeds 𝒲₁ :=
    ⟨(e₁.inv ≫ pullback.snd (D'.map m₁.hom) Wz.hom).base ⁻¹' (Tl l),
      (Tl l).isClosed.preimage (Scheme.Hom.continuous _)⟩
  let C₂ (l : Fin Bp.support.card) : TopologicalSpace.Closeds 𝒲₁ :=
    ⟨q₀.base ⁻¹' (Q l).support,
      (Q l).idealSheaf.support.isClosed.preimage (Scheme.Hom.continuous _)⟩
  have hC (l) : leg'.base ⁻¹' (C₁ l) = leg'.base ⁻¹' (C₂ l) := by
    change (leg' ≫ e₁.inv ≫ pullback.snd _ _).base ⁻¹' (Tl l) =
      (leg' ≫ q₀).base ⁻¹' (Q l).support
    rw [← Category.assoc, hlegzinv, hzs, hleg'q]
    change (leg Vtx.z).base ⁻¹' Set.range (Y.map (hcz l)).left.base = _
    rw [← MMP.Spreading.range_snd_of_isPullback (hcart.isPullback_map (hcz l))]
    exact hQr l
  have hr₁ (l : Fin Bp.support.card) : ∃ r : S₁.1, r ≠ 0 ∧
      ∀ (t' : Spec (.of k₀) ⟶ Spec (.of S₁.1)),
        r ∉ (t'.base (IsLocalRing.closedPoint k₀)).asIdeal → ∀ {F : Scheme.{u}}
          (fst : F ⟶ 𝒲₁) (snd : F ⟶ Spec (.of k₀)), IsPullback fst snd f𝒲 t' →
            fst.base ⁻¹' (C₁ l) = fst.base ⁻¹' (C₂ l) := by
    obtain ⟨ra, hra, Ha⟩ := MMP.Spreading.exists_forall_preimage_subset f𝒲 hf𝒲 leg' t hleg'pb
      (C₁ l) (C₂ l) (hC l).subset
    obtain ⟨rb, hrb, Hb⟩ := MMP.Spreading.exists_forall_preimage_subset f𝒲 hf𝒲 leg' t hleg'pb
      (C₂ l) (C₁ l) (hC l).superset
    refine ⟨ra * rb, mul_ne_zero hra hrb, fun t' ht' F fst snd hF => ?_⟩
    have hta : ra ∉ (t'.base (IsLocalRing.closedPoint k₀)).asIdeal := fun h =>
      ht' (Ideal.mul_mem_right _ _ h)
    have htb : rb ∉ (t'.base (IsLocalRing.closedPoint k₀)).asIdeal := fun h =>
      ht' (Ideal.mul_mem_left _ _ h)
    exact (Ha k₀ t' hta fst snd hF).antisymm (Hb k₀ t' htb fst snd hF)
  choose r₁ hr₁0 hr₁ using hr₁
  -- distinct components of the crepant boundary meet in codimension two on the fibres
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (μ ≫ sXp) := hW.1.toLocallyOfFiniteType
  obtain ⟨dW, hdW⟩ : ∃ d : ℕ, topologicalKrullDim W = d :=
    ⟨_, MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg (μ ≫ sXp)⟩
  have hdist (l l' : Fin BW.support.card) : ∃ r : R, r ≠ 0 ∧
      ∀ (t' : Spec (.of k₀) ⟶ Spec (.of R)),
        r ∉ (t'.base (IsLocalRing.closedPoint k₀)).asIdeal → ∀ {F : Scheme.{u}}
          (fst : F ⟶ (Y.obj Vtx.w).left) (snd : F ⟶ Spec (.of k₀)),
          IsPullback fst snd (Y.obj Vtx.w).hom t' → l ≠ l' →
            fst.base ⁻¹' (Set.range (Y.map (hew l)).left.base ∩
                Set.range (Y.map (hew l')).left.base) = ∅ ∨
              (2 ≤ dW ∧ topologicalKrullDim (fst.base ⁻¹' (Set.range (Y.map (hew l)).left.base ∩
                Set.range (Y.map (hew l')).left.base)) ≤ ((dW - 2 : ℕ) : WithBot ℕ∞)) := by
    by_cases hll : l = l'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ _ _ h => absurd hll h⟩
    let Dc : TopologicalSpace.Closeds (Y.obj Vtx.w).left :=
      ⟨Set.range (Y.map (hew l)).left.base ∩ Set.range (Y.map (hew l')).left.base,
        have := hmprop (hew l)
        have := hmprop (hew l')
        (Y.map (hew l)).left.isClosedMap.isClosed_range.inter
          (Y.map (hew l')).left.isClosedMap.isClosed_range⟩
    have hrange (i : Fin BW.support.card) :
        (leg Vtx.w).base ⁻¹' Set.range (Y.map (hew i)).left.base = (P' i).support := by
      rw [← MMP.Spreading.range_snd_of_isPullback (hcart.isPullback_map (hew i))]
      exact Scheme.IdealSheafData.range_subschemeι _
    have hK : (leg Vtx.w).base ⁻¹' (Dc : Set (Y.obj Vtx.w).left) =
        (P' l).support ∩ (P' l').support := by
      change (leg Vtx.w).base ⁻¹' (Set.range (Y.map (hew l)).left.base ∩
        Set.range (Y.map (hew l')).left.base) = _
      rw [Set.preimage_inter, hrange l, hrange l']
      rfl
    have hcoh : ∀ x ∈ (P' l).support ∩ (P' l').support,
        ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
      rintro x ⟨hx, hx'⟩
      by_contra hlt
      have hle : Order.coheight x ≤ 1 := by
        rcases le_or_gt (Order.coheight x) 1 with h1 | h1
        · exact h1
        · exact absurd (Order.add_one_le_of_lt h1) (by rw [one_add_one_eq_two]; exact_mod_cast hlt)
      have key : ∀ E : MMP.Mori.PrimeDivisor W, x ∈ E.support → x = E.genericPoint := by
        intro E hE
        have hsp : E.genericPoint ⤳ x := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact specializes_iff_mem_closure.mpr hE
        by_contra hne
        have hlt' : x < E.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hsp)
          (fun h => hne ((Scheme.le_iff_specializes.1 h).antisymm hsp).eq)
        have h2 := Order.coheight_add_one_le hlt'
        rw [E.coheight_genericPoint] at h2
        exact absurd (h2.trans hle) (by decide)
      apply hll
      have hP : (P' l) = (P' l') :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((key _ hx).symm.trans (key _ hx'))
      exact BW.support.equivFin.symm.injective (Subtype.ext hP)
    have hCcl : IsClosed ((P' l).support ∩ (P' l').support) :=
      (P' l).idealSheaf.support.isClosed.inter (P' l').idealSheaf.support.isClosed
    rcases (MMP.Spreading.forall_le_coheight_iff (μ ≫ sXp) hdW hCcl 2).mp hcoh with h0 | ⟨h2, hdim⟩
    · obtain ⟨r, hr, H⟩ := MMP.Spreading.exists_forall_preimage_eq_empty (Y.obj Vtx.w).hom
        (hfp _) (leg Vtx.w) (μ ≫ sXp) (hcart.isPullback Vtx.w) Dc (hK.trans h0)
      exact ⟨r, hr, fun t' ht' F fst snd hF _ => Or.inl (H k₀ t' ht' fst snd hF)⟩
    · obtain ⟨r, hr, H⟩ := MMP.Spreading.exists_forall_topologicalKrullDim_preimage_le
        (Y.obj Vtx.w).hom (hfp _) (leg Vtx.w) (μ ≫ sXp) (hcart.isPullback Vtx.w) Dc (dW - 2)
        (by rw [hK]; exact hdim)
      exact ⟨r, hr, fun t' ht' F fst snd hF _ => Or.inr ⟨h2, H k₀ t' ht' fst snd hF⟩⟩
  choose r₀ hr₀0 hr₀ using hdist
  -- a `k₀`-point of the last stage outside the bad loci
  let S₂ := m₂.left.unop
  have hRS₁ : R ≤ S₁.1 := leOfHom m₁.hom.unop
  have hS₁S₂ : S₁.1 ≤ S₂.1 := leOfHom m₂.hom.unop
  let ι₀₂ : R →ₐ[k₀] S₂.1 := Subalgebra.inclusion (hRS₁.trans hS₁S₂)
  let ι₁₂ : S₁.1 →ₐ[k₀] S₂.1 := Subalgebra.inclusion hS₁S₂
  let rr : S₂.1 := (∏ l, ∏ l', ι₀₂ (r₀ l l')) * ∏ l, ι₁₂ (r₁ l)
  have hrr : rr ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun l _ => Finset.prod_ne_zero_iff.mpr
      fun l' _ => ?_) (Finset.prod_ne_zero_iff.mpr fun l _ => ?_)
    · exact fun h => hr₀0 l l' ((Subalgebra.inclusion_injective _) (h.trans (map_zero _).symm))
    · exact fun h => hr₁0 l ((Subalgebra.inclusion_injective _) (h.trans (map_zero _).symm))
  obtain ⟨x₂, hx₂, hx₂r⟩ := exists_comp_specMap_eq_id_notMem S₂.1 S₂.2 rr hrr
  let x₁ : Spec (.of k₀) ⟶ Spec (.of S₁.1) := x₂ ≫ D'.map m₂.hom
  let x' : Spec (.of k₀) ⟶ Spec (.of R) := x₁ ≫ D'.map m₁.hom
  have hprime := (x₂.base (IsLocalRing.closedPoint k₀)).isPrime
  have hx₁r (l : Fin Bp.support.card) : r₁ l ∉ (x₁.base (IsLocalRing.closedPoint k₀)).asIdeal := by
    intro h
    have h' : ι₁₂ (r₁ l) ∈ (x₂.base (IsLocalRing.closedPoint k₀)).asIdeal := h
    exact hx₂r (Ideal.mul_mem_left _ _ ((hprime.prod_mem_iff).mpr ⟨l, Finset.mem_univ _, h'⟩))
  have hx'r (l l' : Fin BW.support.card) :
      r₀ l l' ∉ (x'.base (IsLocalRing.closedPoint k₀)).asIdeal := by
    intro h
    have h' : ι₀₂ (r₀ l l') ∈ (x₂.base (IsLocalRing.closedPoint k₀)).asIdeal := h
    exact hx₂r (Ideal.mul_mem_right _ _ ((hprime.prod_mem_iff).mpr ⟨l, Finset.mem_univ _,
      (hprime.prod_mem_iff).mpr ⟨l', Finset.mem_univ _, h'⟩⟩))
  have e₂ : D'.map m₂.hom = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₁S₂).toRingHom) :=
    rfl
  have e₁' : D'.map m₁.hom = Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS₁).toRingHom) :=
    rfl
  have hcompS : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hS₁S₂).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRS₁).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ S₂.1)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hx₁s : x₁ ≫ D'.map m₁.hom ≫ φR = 𝟙 _ := by
    have h := (congrArg (fun f => x₂ ≫ f) hcompS).trans hx₂
    exact (Category.assoc x₂ (D'.map m₂.hom) (D'.map m₁.hom ≫ φR)).trans h
  -- the fibre of `Z` over `x'` is `Z₀`
  obtain ⟨jj, hjj1, hjjpb⟩ := isPullback_section_fibre t₀ φR (D'.map m₁.hom) x₁ hx₁s
  have hjjf : IsPullback jj t₀ f𝒲 x₁ := hjjpb
  let j : Z₀ ⟶ (Y.obj Vtx.z).left := jj ≫ e₁.inv ≫ pullback.snd (D'.map m₁.hom) Wz.hom
  have hjpb : IsPullback j t₀ (Y.obj Vtx.z).hom x' := by
    have he₁inv : e₁.inv ≫ pullback.fst (D'.map m₁.hom) Wz.hom = f𝒲 := by
      rw [← he₁, Iso.inv_hom_id_assoc]
    have hsq : IsPullback (e₁.inv ≫ pullback.snd (D'.map m₁.hom) Wz.hom) f𝒲 Wz.hom
        (D'.map m₁.hom) :=
      IsPullback.of_iso (IsPullback.of_hasPullback (D'.map m₁.hom) Wz.hom).flip e₁
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ((Category.comp_id _).trans he₁.symm)
        (by simp) ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact hjjf.paste_horiz hsq
  let jz : Z₀ ≅ pullback (Y.obj Vtx.z).hom x' := hjpb.isoPullback
  have hjz₁ : jz.hom ≫ pullback.fst _ _ = j := hjpb.isoPullback_hom_fst
  have hjz₂ : jz.inv ≫ t₀ = pullback.snd (Y.obj Vtx.z).hom x' := hjpb.isoPullback_inv_snd
  -- the fibre of the model of `X⁺` and its map to `Z₀`
  obtain ⟨hfv, hfm, -, hflr⟩ := hfib k₀ x'
  let Yf := pullback (Y.obj Vtx.p).hom x'
  let sY : Yf ⟶ Spec (.of k₀) := pullback.snd (Y.obj Vtx.p).hom x'
  let gz : Yf ⟶ pullback (Y.obj Vtx.z).hom x' := ((Y ⋙ Over.pullback x').map hpz).left
  let g : Yf ⟶ Z₀ := gz ≫ jz.inv
  have hgs : g ≫ t₀ = sY := by
    change gz ≫ jz.inv ≫ t₀ = sY
    rw [hjz₂]
    exact Over.w ((Y ⋙ Over.pullback x').map hpz)
  obtain ⟨hYint, hYdim, hYnor⟩ := hfv Vtx.p
  haveI : IsIntegral Yf := hYint
  haveI : IsNormal Yf := hYnor (inferInstanceAs (IsNormal Xp))
  haveI : LocallyOfFinitePresentation (Y.obj Vtx.p).hom := (hfp Vtx.p).1
  haveI : QuasiCompact (Y.obj Vtx.p).hom := (hfp Vtx.p).2.1
  haveI : LocallyOfFiniteType sY :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Y.obj Vtx.p).hom x') inferInstance
  haveI : QuasiCompact sY :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Y.obj Vtx.p).hom x') inferInstance
  haveI : CompactSpace Yf := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian Yf := LocallyOfFiniteType.isLocallyNoetherian sY
  have hYpm : IsProjectiveMorphism sY :=
    ((isProjective_iff_isProjectiveMorphism_of_isAffine _).mp (hY₁ Vtx.p).1).baseChange x'
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hYpm
  have hYvar : MMP.Mori.IsProjectiveVariety k₀ sY :=
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr
      ⟨(MMP.Mori.isVariety_iff _ _).mpr ⟨inferInstance, inferInstance, inferInstance,
        inferInstance⟩, hYpm⟩
  have hsmallY : IsSmallMorphism sY t₀ g :=
    isSmallMorphism_comp_iso ((hfm hpz).2 hsmall) jz.symm hjz₂ hZ₀N
  haveI : IsSeparated t₀ := hZ₀.toIsSeparated
  have hprojY : IsProjectiveMorphism g := IsProjectiveMorphism.of_comp g t₀ (by rw [hgs]; exact hYpm)
  -- the fibre maps into the stage models
  let ιf : Yf ⟶ 𝒳₁ := pullback.lift (pullback.snd _ _ ≫ x₁) (pullback.fst _ _)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let ιfz : pullback (Y.obj Vtx.z).hom x' ⟶ MMP.CoefficientModels.stageObj D' Wz m₁ :=
    pullback.lift (pullback.snd _ _ ≫ x₁) (pullback.fst _ _)
      ((Category.assoc _ _ _).trans pullback.condition.symm)
  have hιfg : ιf ≫ g₁ = gz ≫ ιfz := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact Eq.symm ((Category.assoc gz _ x₁).symm.trans
        (congrArg (fun f => f ≫ x₁) (Over.w ((Y ⋙ Over.pullback x').map hpz))))
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc,
        pullback.lift_snd]
      exact ((MMP.Spreading.isCartesian_pullback x' Y).w hpz).symm
  have hjzι : jz.hom ≫ ιfz = jj ≫ e₁.inv := by
    apply pullback.hom_ext
    · have he₁inv : e₁.inv ≫ pullback.fst (D'.map m₁.hom) Wz.hom = f𝒲 := by
        rw [← he₁, Iso.inv_hom_id_assoc]
      have l1 : jz.hom ≫ pullback.snd (Y.obj Vtx.z).hom x' ≫ x₁ = t₀ ≫ x₁ :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ x₁) hjpb.isoPullback_hom_snd)
      have r1 : (jj ≫ e₁.inv) ≫ pullback.fst (D'.map m₁.hom) Wz.hom = t₀ ≫ x₁ :=
        (Category.assoc _ _ _).trans ((congrArg (fun f => jj ≫ f) he₁inv).trans hjjf.w)
      rw [Category.assoc, pullback.lift_fst]
      exact l1.trans r1.symm
    · rw [Category.assoc, pullback.lift_snd, hjz₁]
      exact (Category.assoc _ _ _).symm
  have hιfz : ιfz ≫ e₁.hom ≫ q₀ = jz.inv := by
    rw [← cancel_epi jz.hom, ← Category.assoc, hjzι, Iso.hom_inv_id]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => jj ≫ f) (Iso.inv_hom_id_assoc e₁ q₀)).trans hjj1)
  have hιg : ιf ≫ h₁ = g := by
    change ιf ≫ g₁ ≫ e₁.hom ≫ q₀ = gz ≫ jz.inv
    rw [← Category.assoc, hιfg, Category.assoc, hιfz]
  -- the isomorphism over the preimage of `U` on the fibre
  let Vf : Yf.Opens := g ⁻¹ᵁ U
  have hVf : Vf ≤ ιf ⁻¹ᵁ 𝒱₁ := fun y hy => by
    show h₁ (ιf y) ∈ U
    rw [← Scheme.Hom.comp_apply, hιg]
    exact hy
  let ι₁' : Vf.toScheme ⟶ 𝒱₁.toScheme := ιf.resLE 𝒱₁ Vf hVf
  have hι₁' : ι₁' ≫ 𝒱₁.ι = Vf.ι ≫ ιf := Scheme.Hom.resLE_comp_ι _ _
  let ι₂ : Vf.toScheme ⟶ pullback (D'.map m₂.hom) W''.hom :=
    pullback.lift (Vf.ι ≫ pullback.snd _ _ ≫ x₂) ι₁' (by
      change (Vf.ι ≫ pullback.snd _ _ ≫ x₂) ≫ D'.map m₂.hom =
        ι₁' ≫ 𝒱₁.ι ≫ pullback.fst (D'.map m₁.hom) Wp.hom
      rw [← Category.assoc ι₁', hι₁', Category.assoc, pullback.lift_fst]
      exact (Category.assoc _ _ _).trans (congrArg (fun f => Vf.ι ≫ f) (Category.assoc _ _ _)))
  have hι₂ : ι₂ ≫ pullback.snd _ _ = ι₁' := pullback.lift_snd _ _ _
  have hι₂A : ι₂ ≫ pullback.snd _ _ ≫ 𝒱₁.ι ≫ pullback.snd (D'.map m₁.hom) Wp.hom =
      Vf.ι ≫ pullback.fst (Y.obj Vtx.p).hom x' := by
    rw [← Category.assoc, hι₂, ← Category.assoc, hι₁', Category.assoc, pullback.lift_snd]
  have hι₂B : (ι₂ ≫ pullback.snd _ _) ≫ h₁ ∣_ U = g ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, hι₂,
      ← Category.assoc, hι₁', Category.assoc, hιg]
  let 𝓝 : Yf.Modules :=
    (Scheme.Modules.pullback (pullback.fst (Y.obj Vtx.p).hom x')).obj (𝓜 PUnit.unit)
  haveI h𝓝 : Stacks.Ample.IsInvertibleModule Yf 𝓝 := MMP.Fourfold.isInvertibleModule_pullback _ _
  let eV : 𝓝.restrict Vf.ι ≅
      (Scheme.Modules.pullback (g ∣_ U)).obj (E₀.divisorialSheaf.restrict U.ι) :=
    (Scheme.Modules.restrictFunctorIsoPullback Vf.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp Vf.ι (pullback.fst _ _)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hι₂A.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp ι₂ _).app _).symm ≪≫
    (Scheme.Modules.pullback ι₂).mapIso
      (((Scheme.Modules.pullbackComp (pullback.snd _ _) (𝒱₁.ι ≫ pullback.snd _ _)).app _).symm) ≪≫
    (Scheme.Modules.pullback ι₂).mapIso ψ ≪≫
    (Scheme.Modules.pullbackComp ι₂ (pullback.snd _ _)).app _ ≪≫
    (Scheme.Modules.pullbackComp (ι₂ ≫ pullback.snd _ _) (h₁ ∣_ U)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hι₂B).app _ ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso (Divisor.divisorialSheafRestrictOpenIso E₀ U)
  -- the relatively ample sheaf on the fibre
  have hampM : MMP.Mori.IsRelativelyAmple (Y.map hpz).left (𝓜 PUnit.unit) :=
    hY₅ PUnit.unit hpz hLamp
  have hsqpz := (MMP.Spreading.isCartesian_pullback x' Y).isPullback_map hpz
  haveI : QuasiCompact (Y.map hpz).left := by haveI := hmprop hpz; infer_instance
  have h𝓝gz : MMP.Mori.IsRelativelyAmple gz 𝓝 :=
    isRelativelyAmple_pullback_of_isPullback hsqpz (𝓜 PUnit.unit) hampM
  have h𝓝g : MMP.Mori.IsRelativelyAmple g 𝓝 := (isRelativelyAmple_comp_iso gz jz.symm 𝓝).mpr h𝓝gz
  obtain ⟨hcY, hampY⟩ := exists_isRelativelyAmple_inverseTransformDivisor hsmallY U
    ((isSmoothScheme_iff_smooth _).mpr hUsm) hUc E₀ 𝓝 h𝓝g eV
  have hampg : (Divisor.toQDivisor (inverseTransformDivisor g C₀) +
      inverseTransformDivisor g D₀).HasRelativelyAmpleMultiple g := by
    refine ⟨mL, hmL, inverseTransformDivisor g E₀, hcY, ?_, hampY⟩
    rw [← MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor, hE₀, map_zsmul, map_add,
      MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]
  -- the log resolution and crepant boundary on the fibre
  have hsuppP (l : Fin Bp.support.card) :
      (P l).support = Set.range (Xd.map (hcp l)).left.base :=
    (Scheme.IdealSheafData.range_subschemeι _).symm
  have hsuppP' (l : Fin BW.support.card) :
      (P' l).support = Set.range (Xd.map (hew l)).left.base :=
    (Scheme.IdealSheafData.range_subschemeι _).symm
  have hlrK : MMP.Fourfold.IsLogResolution sXp (∑ l, Finsupp.single (P l) (Bp (P l))) μ := by
    rw [hBpsum]
    exact ⟨hμ, hμp⟩
  have hcrK : ∃ (K₀ : Divisor Xp) (hW₀ : _) (hμ₀ : _),
      MMP.Mori.IsCrepantBoundary sXp n K₀ (∑ l, Finsupp.single (P l) (Bp (P l)))
        μ hW₀ hμ₀ (∑ l, Finsupp.single (P' l) (BW (P' l))) :=
    ⟨KXp, hW, hμ.isBirationalMorphism, by rw [hBpsum, hBWsum]; exact hBW⟩
  haveI : IsLocallyNoetherian (Xd.obj Vtx.p).left := inferInstanceAs (IsLocallyNoetherian Xp)
  haveI : IsNormal (Xd.obj Vtx.p).left := inferInstanceAs (IsNormal Xp)
  haveI : IsLocallyNoetherian ((Y ⋙ Over.pullback x').obj Vtx.p).left :=
    inferInstanceAs (IsLocallyNoetherian Yf)
  haveI : IsNormal ((Y ⋙ Over.pullback x').obj Vtx.p).left := inferInstanceAs (IsNormal Yf)
  haveI : IsIntegral ((Y ⋙ Over.pullback x').obj Vtx.p).left := inferInstanceAs (IsIntegral Yf)
  obtain ⟨Ps, Ps', hPs, hPs', hlrf, Ks, hWf, hμf, hcrf⟩ := hflr hwp n hcp P (fun l => Bp (P l))
    hew P' (fun l => BW (P' l)) hsuppP hsuppP' hlrK hcrK
  -- the images of the fibres of the components of the boundary
  have hsurjπZ : Surjective πZ := surjective_of_isPullback hZ
  have hQinj : Function.Injective Q := by
    intro l l' hll
    have h1 : closure {fp (P l).genericPoint} = closure {fp (P l').genericPoint} := by
      rw [← hrangeP, ← hrangeP, hQr, hQr, hll]
    have h2 : fp (P l).genericPoint = fp (P l').genericPoint :=
      (inseparable_iff_closure_eq.mpr h1).eq
    obtain ⟨G, hG, -⟩ := exists_inverseTransformDivisor_apply_eq fp (P l) (hbirfp (P l))
    have e1 := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hG.symm (hbirfp (P l))
    have e2 := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (hG.trans h2).symm
      (hbirfp (P l'))
    have hPP : P l = P l' := Option.some_injective _ (e1.symm.trans e2)
    exact Bp.support.equivFin.symm.injective (Subtype.ext hPP)
  have hgj : g ≫ j = gz ≫ pullback.fst (Y.obj Vtx.z).hom x' :=
    (Category.assoc _ _ _).trans (congrArg (fun f => gz ≫ f)
      ((congrArg (fun f => jz.inv ≫ f) hjz₁.symm).trans (Iso.inv_hom_id_assoc jz _)))
  have hj_T (l : Fin Bp.support.card) : j.base ⁻¹' (Tl l) = (Q l).support := by
    have h := hr₁ l x₁ (hx₁r l) jj t₀ hjjf
    refine h.trans ?_
    change (jj ≫ q₀).base ⁻¹' (Q l).support = _
    rw [show jj ≫ q₀ = 𝟙 Z₀ from hjj1]
    rfl
  have hgimg (l : Fin Bp.support.card) : g.base '' (Ps l).support = (Q l).support := by
    have hczc : ((Y ⋙ Over.pullback x').map (hcp l)).left ≫ gz =
        ((Y ⋙ Over.pullback x').map (hcz l)).left := by
      rw [← Over.comp_left, ← Functor.map_comp]
      exact congrArg (fun f => ((Y ⋙ Over.pullback x').map f).left) (Subsingleton.elim _ _)
    have hrz := MMP.Spreading.range_snd_of_isPullback
      ((MMP.Spreading.isCartesian_pullback x' Y).isPullback_map (hcz l))
    rw [hPs l, ← hj_T l]
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      show j (g (((Y ⋙ Over.pullback x').map (hcp l)).left y)) ∈ (Tl l : Set _)
      have e3 : j (g (((Y ⋙ Over.pullback x').map (hcp l)).left y)) =
          pullback.fst (Y.obj Vtx.z).hom x' (((Y ⋙ Over.pullback x').map (hcz l)).left y) := by
        rw [← Scheme.Hom.comp_apply, hgj, ← hczc]
        rfl
      rw [e3]
      have : ((Y ⋙ Over.pullback x').map (hcz l)).left y ∈
          Set.range ((Y ⋙ Over.pullback x').map (hcz l)).left.base := ⟨y, rfl⟩
      rw [hrz] at this
      exact this
    · intro hz
      have hz' : jz.hom z ∈ Set.range ((Y ⋙ Over.pullback x').map (hcz l)).left.base := by
        rw [hrz]
        show (jz.hom ≫ pullback.fst _ _) z ∈ (Tl l : Set _)
        rw [hjz₁]
        exact hz
      obtain ⟨y, hy⟩ := hz'
      refine ⟨((Y ⋙ Over.pullback x').map (hcp l)).left y, ⟨y, rfl⟩, ?_⟩
      change ((((Y ⋙ Over.pullback x').map (hcp l)).left ≫ gz) ≫ jz.inv) y = z
      rw [hczc, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  haveI : IsProper g := hsmallY.isProper
  have hgPs (l : Fin Bp.support.card) : g (Ps l).genericPoint = (Q l).genericPoint := by
    have h1 : closure ({g (Ps l).genericPoint} : Set Z₀) = closure {(Q l).genericPoint} := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hgimg l,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← Set.image_singleton]
      exact g.isClosedMap.closure_image_eq_of_continuous g.continuous _
    exact (inseparable_iff_closure_eq.mpr h1).eq
  have hPsinj : Function.Injective Ps := fun l l' h => hQinj
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hgPs l).symm.trans ((congrArg (fun F => g (AlgebraicGeometry.PrimeDivisor.genericPoint F))
        h).trans (hgPs l'))))
  -- the boundary of the fibre is the strict transform of `D₀`
  have hbirg := map_genericPoint_mem_biregularLocus_of_isSmallMorphism hsmallY
  have hBY : inverseTransformDivisor g D₀ = ∑ l, Finsupp.single (Ps l) (Bp (P l)) := by
    ext F
    change (inverseTransformDivisor g D₀) F = (∑ l, Finsupp.single (Ps l) (Bp (P l))) F
    obtain ⟨QF, hQF, hgF⟩ := exists_inverseTransformDivisor_apply_eq g F (hbirg F)
    rw [hgF D₀, Finsupp.finset_sum_apply]
    by_cases hF : ∃ l, Ps l = F
    · obtain ⟨l, rfl⟩ := hF
      rw [Finset.sum_eq_single l (fun l' _ hl' => Finsupp.single_eq_of_ne
        (fun h => hl' (hPsinj h).symm)) (fun h => absurd (Finset.mem_univ l) h),
        Finsupp.single_eq_same]
      have hQQ : QF = Q l :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hQF.trans (hgPs l))
      rw [hQQ, hQD l]
    · push Not at hF
      rw [Finset.sum_eq_zero (fun l _ => Finsupp.single_eq_of_ne (fun h => hF l h.symm))]
      by_contra hne
      obtain ⟨G, hG, -⟩ := exists_primeDivisor_baseChange hZ QF
      have hDG : D G = D₀ QF := hD.1 QF G hG
      obtain ⟨P₁, hP₁, hP₁b⟩ := exists_primeDivisor_map_genericPoint_eq fp
        hsmall.isBirationalMorphism G
      obtain ⟨G', hG', hG'F⟩ := exists_inverseTransformDivisor_apply_eq fp P₁ hP₁b
      obtain rfl : G' = G := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hG'.trans hP₁)
      have hP₁s : P₁ ∈ Bp.support := Finsupp.mem_support_iff.mpr (by
        change Bp P₁ ≠ 0
        rw [show Bp P₁ = D G' from hG'F D, hDG]
        exact hne)
      let l := Bp.support.equivFin ⟨P₁, hP₁s⟩
      have hPl : P l = P₁ := by
        change ((Bp.support.equivFin.symm (Bp.support.equivFin ⟨P₁, hP₁s⟩)) : _) = P₁
        rw [Equiv.symm_apply_apply]
      have hQl : Q l = QF := by
        have h1 : πZ.base ⁻¹' (Q l).support = πZ.base ⁻¹' QF.support := by
          rw [← hQr l, hrangeP l, hPl, hP₁, AlgebraicGeometry.PrimeDivisor.support_eq_closure QF]
          exact hG
        have h2 : (Q l).support = QF.support := (Set.preimage_injective.mpr πZ.surjective) h1
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h2
        exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (inseparable_iff_closure_eq.mpr h2).eq
      have e1 := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hQF.symm (hbirg F)
      have e2 := MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        ((hgPs l).trans (congrArg _ hQl)) (hbirg (Ps l))
      exact hF l (Option.some_injective _ (e2.symm.trans e1))
  -- the components of the crepant boundary on the fibre are distinct
  haveI : IsIntegral ((Y ⋙ Over.pullback x').obj Vtx.w).left := (hfv Vtx.w).1
  haveI : LocallyOfFinitePresentation (Y.obj Vtx.w).hom := (hfp Vtx.w).1
  haveI : LocallyOfFiniteType ((Y ⋙ Over.pullback x').obj Vtx.w).hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Y.obj Vtx.w).hom x') inferInstance
  have hdWf : topologicalKrullDim ((Y ⋙ Over.pullback x').obj Vtx.w).left = dW :=
    (hfv Vtx.w).2.1.trans hdW
  have hPs'inj : Function.Injective Ps' := by
    intro l l' hll'
    by_contra hne
    have hrw (i : Fin BW.support.card) := MMP.Spreading.range_snd_of_isPullback
      ((MMP.Spreading.isCartesian_pullback x' Y).isPullback_map (hew i))
    have hpre : (pullback.fst (Y.obj Vtx.w).hom x').base ⁻¹'
        (Set.range (Y.map (hew l)).left.base ∩ Set.range (Y.map (hew l')).left.base) =
          (Ps' l).support := by
      rw [Set.preimage_inter, ← hrw l, ← hrw l', ← hPs' l, ← hPs' l', hll', Set.inter_self]
    obtain ⟨h1, hsupp⟩ := MMP.Spreading.topologicalKrullDim_support
      ((Y ⋙ Over.pullback x').obj Vtx.w).hom hdWf (Ps' l)
    rcases hr₀ l l' x' (hx'r l l') (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback (Y.obj Vtx.w).hom x') hne with h0 | ⟨h2, hdim⟩
    · rw [hpre] at h0
      have hmem : (Ps' l).genericPoint ∈ (Ps' l).support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      rw [h0] at hmem
      exact hmem
    · rw [hpre, hsupp] at hdim
      have : dW - 1 ≤ dW - 2 := by exact_mod_cast hdim
      omega
  -- log canonicity of the fibre
  have hleK : ∀ F, BW.coeff F ≤ 1 :=
    (isLogCanonicalPair_iff_forall_coeff_le_one sXp ⟨inferInstance, inferInstance, hlc.1, hlc.2.1⟩
      ⟨hμ, hμp⟩ hW hBW).mp hlc
  have hle : ∀ F, DivisorWithCoeffs.coeff (∑ l, Finsupp.single (Ps' l) (BW (P' l))) F ≤ 1 := by
    intro F
    change (∑ l, Finsupp.single (Ps' l) (BW (P' l))) F ≤ 1
    rw [Finsupp.finset_sum_apply]
    by_cases hF : ∃ l, Ps' l = F
    · obtain ⟨l, rfl⟩ := hF
      rw [Finset.sum_eq_single l (fun l' _ hl' => Finsupp.single_eq_of_ne
        (fun h => hl' (hPs'inj h).symm)) (fun h => absurd (Finset.mem_univ l) h),
        Finsupp.single_eq_same]
      exact hleK (P' l)
    · push Not at hF
      rw [Finset.sum_eq_zero (fun l _ => Finsupp.single_eq_of_ne (fun h => hF l h.symm))]
      exact zero_le_one
  have hnonneg : ∀ F, 0 ≤ DivisorWithCoeffs.coeff (∑ l, Finsupp.single (Ps l) (Bp (P l))) F := by
    intro F
    change 0 ≤ (∑ l, Finsupp.single (Ps l) (Bp (P l))) F
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun l _ => ?_
    by_cases h : Ps l = F
    · rw [h, Finsupp.single_eq_same]; exact hlc.2.1 (P l)
    · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
  haveI : MMP.Mori.IsVariety K sXp := hXp.toIsVariety
  haveI : MMP.Mori.IsVariety K (μ ≫ sXp) := hW.1
  have hdW0 : dW ≠ 0 := by
    intro h0
    apply hdXp
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sXp (μ ≫ sXp)
      hμ.isBirationalMorphism, hdW, h0]
    rfl
  obtain ⟨F₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdWf hdW0
  have hlcY : MMP.Intersection.IsLogCanonicalPair sY (inverseTransformDivisor g D₀) := by
    rw [hBY]
    exact (isLogCanonicalPair_iff_forall_coeff_le_one sY
      ⟨inferInstance, inferInstance, (hcrf F₀).isPair, hnonneg⟩ hlrf hWf hcrf).mpr hle
  exact ⟨Yf, inferInstance, inferInstance, inferInstance, inferInstance, sY, g, hYvar, hsmallY,
    hprojY, hlcY, hampg⟩

/-- **Descent of a permitted step along an extension of algebraically closed fields.** Let
`k₀ ⊆ K` be algebraically closed fields of characteristic zero, `(X₀, B₀)` a projective lc
fourfold pair over `k₀` with canonical divisor `K₀`, `R₀` a `(K₀ + B₀)`-negative extremal ray and
`f₀ : X₀ ⟶ Z₀` a birational contraction of `R₀` onto a normal projective variety with
`ρ(X₀/Z₀) = 1` and `-(K₀ + B₀)` `f₀`-ample. If the base change `f : X ⟶ Z` of `f₀` to `K` extends
to a permitted step for the base-changed data, then `f₀` extends to a permitted step over `k₀`. -/
private theorem exists_isPermittedStep_of_isPullback_of_isPermittedStep
    {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K]
    [CharZero k₀]
    {X₀ Z₀ X Z Xp : Scheme.{u}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀]
    [IsNormal X₀] [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {t₀ : Z₀ ⟶ Spec (.of k₀)}
    {s : X ⟶ Spec (.of K)} {t : Z ⟶ Spec (.of K)} {π : X ⟶ X₀} {πZ : Z ⟶ Z₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hZ : IsPullback πZ t t₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {K₀ : Divisor X₀} {B₀ : QDivisor X₀} {KX : Divisor X} {BX : QDivisor X}
    (hKb : IsBaseChange π K₀ KX) (hBb : IsBaseChange π B₀ BX)
    {R₀ : Set (NumericalCurveClasses s₀)}
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    {f₀ : X₀ ⟶ Z₀} {f : X ⟶ Z} (hf : f ≫ t = s) (hfπ : f ≫ πZ = π ≫ f₀)
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) (hdX : topologicalKrullDim X ≠ 0)
    (hlc₀ : MMP.Intersection.IsLogCanonicalPair s₀ B₀) (hK₀ : ∃ n : ℕ, K₀.IsCanonicalDivisor s₀ n)
    (hR₀ : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) R₀)
    (hf₀ : IsContractionOfRay s₀ t₀ R₀ f₀) (hZ₀ : MMP.Mori.IsProjectiveVariety k₀ t₀)
    (hρ₀ : relativePicardNumberN1 s₀ f₀ = 1)
    (ha₀ : (-(Divisor.toQDivisor K₀ + B₀)).HasRelativelyAmpleMultiple f₀)
    (hbir₀ : IsBirationalMorphism f₀)
    {sXp : Xp ⟶ Spec (.of K)} {fp : Xp ⟶ Z}
    (hstep : IsPermittedStep s t sXp KX BX (φ '' R₀) f fp) :
    ∃ (Xp₀ : Scheme.{u}) (_ : IsIntegral Xp₀) (_ : CompactSpace Xp₀)
      (_ : IsLocallyNoetherian Xp₀) (_ : IsNormal Xp₀) (sXp₀ : Xp₀ ⟶ Spec (.of k₀))
      (fp₀ : Xp₀ ⟶ Z₀), IsPermittedStep s₀ t₀ sXp₀ K₀ B₀ R₀ f₀ fp₀ := by
  haveI : IsNormal Z₀ := hf₀.isNormalVariety_target.2
  have hKZ := isBaseChange_transformDivisor h hZ hX₀ hZ₀ hf₀.comp_eq hf hfπ hKb
  have hBZ := isBaseChange_transformDivisor h hZ hX₀ hZ₀ hf₀.comp_eq hf hfπ hBb
  have hdXp : topologicalKrullDim Xp ≠ 0 := by
    haveI := hstep.isProjectiveVariety.toIsVariety
    haveI := hstep.isProjectiveVariety_target.toIsVariety
    haveI := hstep.isProjectiveVariety_step.toIsVariety
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism t sXp
      hstep.isSmallMorphism_step.isBirationalMorphism,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism t s hstep.isBirationalMorphism]
    exact hdX
  obtain ⟨Y, _, _, _, _, sY, g, hY, hsmall, hproj, hlc, hamp⟩ :=
    exists_small_lc_model_of_isPullback hZ hZ₀ hKZ hBZ hstep.isProjectiveVariety_step hdXp
      hstep.isSmallMorphism_step hstep.isProjectiveMorphism_step
      hstep.isLogCanonicalPair_step hstep.hasRelativelyAmpleMultiple_step
  exact ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, sY, g,
    { isProjectiveVariety := hX₀
      isLogCanonicalPair := hlc₀
      isCanonicalDivisor := hK₀
      isNegativeExtremalRayOf := hR₀
      isContractionOfRay := hf₀
      isProjectiveVariety_target := hZ₀
      relativePicardNumber_eq_one := hρ₀
      hasRelativelyAmpleMultiple := ha₀
      isBirationalMorphism := hbir₀
      isProjectiveVariety_step := hY
      isSmallMorphism_step := hsmall
      isProjectiveMorphism_step := hproj
      isLogCanonicalPair_step := hlc
      hasRelativelyAmpleMultiple_step := hamp }⟩

/-- Two morphisms into an affine scheme agree once they agree after a morphism which is an
isomorphism on global sections. -/
private lemma eq_of_comp_eq_of_isIso_appTop {X Y W : Scheme.{u}} [IsAffine W] (g : X ⟶ Y)
    [IsIso g.appTop] {a b : Y ⟶ W} (hab : g ≫ a = g ≫ b) : a = b := by
  refine ext_of_isAffine ?_
  have := congrArg Scheme.Hom.appTop hab
  simp only [Scheme.Hom.comp_appTop] at this
  exact (cancel_mono _).1 this

private theorem solution : ∀ {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 4)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sZ R f) (hbir : IsBirationalMorphism f),
    ∃ (Xp : Scheme.{0}) (_ : IsIntegral Xp) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp)
      (_ : IsNormal Xp) (sXp : Xp ⟶ Spec (.of k)) (fp : Xp ⟶ Z),
      IsPermittedStep sX sZ sXp K B R f fp := by
  classical
  intro k _ _ _ X Z sX sZ _ _ _ _ K B R f hX hdim hB hK hR hf hbir
  -- the pair descends to a countable algebraically closed `k₀ ⊆ k`
  obtain ⟨k₀, _, _, X₀, _, _, _, _, s₀, K₀, B₀, π, hπ, hproj₀, hlc₀, hK₀, hKb, hBb⟩ :=
    exists_descent hX hB hK
  have hdim₀ : topologicalKrullDim X₀ = 4 :=
    (topologicalKrullDim_eq_of_isPullback s₀ sX π hπ hproj₀).symm.trans hdim
  have hDb : IsBaseChange π (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor K + B) :=
    hKb.toQDivisor.add hBb
  have hQ₀ := isQCartier_of_isLogCanonicalPair hlc₀ hK₀
  let e := numericalCurveClassesBaseChange s₀ sX π hπ hproj₀
  have he := numericalCurveClassesBaseChange_eq_of_isPullback s₀ sX π hπ hproj₀
  have hRe : e '' (e ⁻¹' R) = R := Set.image_preimage_eq R e.surjective
  have hR₀ : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) (e ⁻¹' R) := by
    rw [isNegativeExtremalRayOf_iff hπ hproj₀ hDb hQ₀ hR.1 e.toLinearMap he, LinearEquiv.coe_coe,
      hRe]
    exact hR
  -- the contraction of the ray over `k₀`
  obtain ⟨Z₀, t₀, f₀, hc₀, hZ₀, hρ₀, ha₀⟩ :=
    exists_isContractionOfRay_of_isNegativeExtremalRayOf_of_isAlgClosed hproj₀ hlc₀ hK₀ hdim₀ hR₀
  haveI : IsNormal Z₀ := hc₀.isNormalVariety_target.2
  set φk := Spec.map (CommRingCat.ofHom (algebraMap k₀ k))
  have hZk : IsPullback (pullback.fst t₀ φk) (pullback.snd t₀ φk) t₀ φk :=
    IsPullback.of_hasPullback t₀ φk
  let f₀k : X ⟶ pullback t₀ φk :=
    pullback.lift (π ≫ f₀) sX (by rw [Category.assoc, hc₀.comp_eq, hπ.w])
  have hf₀k : f₀k ≫ pullback.snd t₀ φk = sX := pullback.lift_snd _ _ _
  have hf₀kπ : f₀k ≫ pullback.fst t₀ φk = π ≫ f₀ := pullback.lift_fst _ _ _
  have hc₀k : IsContractionOfRay sX (pullback.snd t₀ φk) R f₀k := by
    have := (isContractionOfRay_iff hπ hZk hproj₀ hZ₀ f₀ hc₀.comp_eq f₀k hf₀k hf₀kπ
      e.toLinearMap he (e ⁻¹' R)).mp hc₀
    rwa [LinearEquiv.coe_coe, hRe] at this
  -- it agrees with `f` up to an isomorphism of the targets
  have hRf (C : ProperCurve sX) (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) :
      C.IsContractedBy f := (hf.isContractedBy_iff C).mpr hC
  have hRf₀ (C : ProperCurve sX) (hC : OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) :
      C.IsContractedBy f₀k := (hc₀k.isContractedBy_iff C).mpr hC
  obtain ⟨u, hu, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR.2.1 hRf hc₀k
  obtain ⟨v, hv, -⟩ := existsUnique_comp_eq_of_isContractionOfRay hX hc₀k.isProjectiveMorphism
    hf₀k hR.2.1 hRf₀ hf
  have hu₃ := existsUnique_comp_eq_of_isContractionOfRay hX hf.isProjectiveMorphism
    hf.comp_eq hR.2.1 hRf hf
  have hu₄ := existsUnique_comp_eq_of_isContractionOfRay hX hc₀k.isProjectiveMorphism
    hf₀k hR.2.1 hRf₀ hc₀k
  let eZ : pullback t₀ φk ≅ Z :=
    { hom := u
      inv := v
      hom_inv_id := hu₄.unique (by rw [← Category.assoc, hu, hv]) (Category.comp_id _)
      inv_hom_id := hu₃.unique (by rw [← Category.assoc, hv, hu]) (Category.comp_id _) }
  have hfe : f₀k ≫ eZ.hom = f := hu
  haveI : IsIso f.appTop := hf.isIso_app ⊤
  have hsZ : eZ.inv ≫ pullback.snd t₀ φk = sZ :=
    eq_of_comp_eq_of_isIso_appTop f (by
      rw [hf.comp_eq, ← hfe, Category.assoc, eZ.hom_inv_id_assoc, hf₀k])
  set πZ := eZ.inv ≫ pullback.fst t₀ φk
  have hπZ : IsPullback πZ sZ t₀ φk :=
    IsPullback.of_iso_pullback ⟨by rw [← hsZ, Category.assoc, Category.assoc, pullback.condition]⟩
      eZ.symm rfl hsZ
  have hfπZ : f ≫ πZ = π ≫ f₀ := by
    rw [← hfe, Category.assoc, eZ.hom_inv_id_assoc, hf₀kπ]
  have hbir₀ : IsBirationalMorphism f₀ :=
    (isBirationalMorphism_iff hπ hπZ hproj₀ hZ₀ f₀ hc₀.comp_eq f hf.comp_eq hfπZ).2 hbir
  -- the complex picture
  obtain ⟨σ⟩ := MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1 k₀
  letI : Algebra k₀ ℂ := σ.toAlgebra
  haveI : LocallyOfFiniteType s₀ := hproj₀.toLocallyOfFiniteType
  set φC := Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))
  have hC : IsPullback (pullback.fst s₀ φC) (pullback.snd s₀ φC) s₀ φC :=
    IsPullback.of_hasPullback _ _
  set XC := pullback s₀ φC
  set πC := pullback.fst s₀ φC
  set sC := pullback.snd s₀ φC
  obtain ⟨_, _, _, _⟩ := isIntegral_isNormal_of_isPullback s₀ sC πC hC hproj₀
  obtain ⟨KC, hKC⟩ : ∃ KC : Divisor XC, IsBaseChange πC K₀ KC := exists_isBaseChange hC K₀
  obtain ⟨BC, hBC⟩ : ∃ BC : QDivisor XC, IsBaseChange πC B₀ BC := exists_isBaseChange hC B₀
  let eC := numericalCurveClassesBaseChange s₀ sC πC hC hproj₀
  have heC := numericalCurveClassesBaseChange_eq_of_isPullback s₀ sC πC hC hproj₀
  have hiff := program_conditions_iff_of_isPullback (K := ℂ) 0 False s₀ K₀ B₀
    (Y₀ := fun _ => X₀) (fun _ => s₀) (fun _ => K₀) (fun _ => B₀) (fun _ => ∅)
    (fun i hi => absurd hi (by simp)) (Z₀ := fun _ => X₀) (fun _ => s₀) (constSeqTo X₀)
    (fun i hi => absurd hi (by simp)) (fun _ => 𝟙 X₀) (fun i hi => absurd hi (by simp)) ∅
    (fun h => h.elim) s₀ (constSeqTo X₀ _) (fun h => h.elim) sC KC BC (Y := fun _ => XC)
    (fun _ => sC) (fun _ => KC) (fun _ => BC) (fun _ => ∅) (Z := fun _ => XC) (fun _ => sC)
    (constSeqTo XC) (fun i hi => absurd hi (by simp)) (fun _ => 𝟙 XC)
    (fun i hi => absurd hi (by simp)) ∅ sC (constSeqTo XC _) (fun h => h.elim)
    (constSeqHom πC) (fun i hi => by obtain rfl : i = 0 := (by simpa using hi); exact hC)
    (fun _ => πC) (fun i hi => absurd hi (by simp)) πC (fun h => h.elim)
    (fun i hi => absurd hi (by simp)) (fun i hi => absurd hi (by simp)) (fun h => h.elim)
    (fun i hi P₀ P hP => by
      obtain rfl : i = 0 := by simpa using hi
      exact ⟨hKC.1 P₀ P hP, hBC.1 P₀ P hP⟩)
    (fun i hi P hP => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hP with hP | hP
      · exact hKC.2 P hP
      · exact hBC.2 P hP)
    (fun i => match i with
      | 0 => eC.toLinearMap
      | _ + 1 => 0)
    (fun i hi => by obtain rfl : i = 0 := (by simpa using hi); exact heC)
    (fun i hi => absurd hi (by simp)) (fun h => h.elim)
  obtain ⟨hprojC, hlcC, hKC', -⟩ := hiff.mp ⟨hproj₀, hlc₀, hK₀, fun i hi => absurd hi (by simp),
    fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp), fun h => h.elim⟩
  have hdimC : topologicalKrullDim XC = 4 :=
    (topologicalKrullDim_eq_of_isPullback s₀ sC πC hC hproj₀).trans hdim₀
  have hDC : IsBaseChange πC (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor KC + BC) :=
    hKC.toQDivisor.add hBC
  have hQC := isQCartier_of_isLogCanonicalPair hlcC hKC'
  have hRC := (isNegativeExtremalRayOf_iff hC hproj₀ hDC hR₀.1 hQC eC.toLinearMap heC
    (e ⁻¹' R)).mp hR₀
  -- the base change of `f₀` to `ℂ` is a birational contraction of the complex ray
  have hZC : IsPullback (pullback.fst t₀ φC) (pullback.snd t₀ φC) t₀ φC :=
    IsPullback.of_hasPullback t₀ φC
  let fC : XC ⟶ pullback t₀ φC :=
    pullback.lift (πC ≫ f₀) sC (by rw [Category.assoc, hc₀.comp_eq, hC.w])
  have hfC : fC ≫ pullback.snd t₀ φC = sC := pullback.lift_snd _ _ _
  have hfCπ : fC ≫ pullback.fst t₀ φC = πC ≫ f₀ := pullback.lift_fst _ _ _
  have hcC := (isContractionOfRay_iff hC hZC hproj₀ hZ₀ f₀ hc₀.comp_eq fC hfC hfCπ
    eC.toLinearMap heC (e ⁻¹' R)).mp hc₀
  have hbirC := (isBirationalMorphism_iff hC hZC hproj₀ hZ₀ f₀ hc₀.comp_eq fC hfC hfCπ).1 hbir₀
  -- the complex continuation, its descent to `k₀` and its base change to `k`
  obtain ⟨XpC, _, _, _, _, sXpC, fpC, hstepC⟩ :=
    MMP.Fourfold.IsContractionOfRay.exists_isPermittedStep hprojC hdimC hKC' hlcC hRC hcC hbirC
  obtain ⟨Xp₀, _, _, _, _, sXp₀, fp₀, hstep₀⟩ :=
    exists_isPermittedStep_of_isPullback_of_isPermittedStep hC hZC hKC hBC eC.toLinearMap
      hfC hfCπ hproj₀ (by rw [hdimC]; decide) hlc₀ hK₀ hR₀ hc₀ hZ₀ hρ₀ ha₀ hbir₀ hstepC
  obtain ⟨Xp, _, _, _, _, sXp, fp, hstep⟩ :=
    exists_isPermittedStep_of_isPullback hπ hπZ hKb hBb e.toLinearMap he hf.comp_eq hfπZ hstep₀
  rw [LinearEquiv.coe_coe, hRe] at hstep
  exact ⟨Xp, inferInstance, inferInstance, inferInstance, inferInstance, sXp, fp, hstep⟩

end Proof_lem_oai4_finite_existence_transfer

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Continuation over any algebraically closed field.** Let `(X, B)` be a projective lc
fourfold pair over an algebraically closed field `k` of characteristic zero, with canonical
divisor `K`, let `R` be a `(K + B)`-negative extremal ray of `NE̅(X)` and let `f : X ⟶ Z` be a
birational contraction of `R`. Then there are a normal projective variety `X⁺` and a small
projective birational morphism `f⁺ : X⁺ ⟶ Z` such that `(X⁺, B⁺, f⁺)` is a permitted step for
`(X, B, R, f)`. -/
@[mmp "lem_oai4_finite_existence_transfer"]
public theorem IsContractionOfRay.exists_isPermittedStep_of_isAlgClosed {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hdim : topologicalKrullDim X = 4)
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sZ R f) (hbir : IsBirationalMorphism f) :
    ∃ (Xp : Scheme.{0}) (_ : IsIntegral Xp) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp)
      (_ : IsNormal Xp) (sXp : Xp ⟶ Spec (.of k)) (fp : Xp ⟶ Z),
      IsPermittedStep sX sZ sXp K B R f fp :=
        by revert k X Z sX sZ K B R f hX hdim hB hK hR hf hbir; first | exact Proof_lem_oai4_finite_existence_transfer.solution | exact Proof_lem_oai4_finite_existence_transfer.solution _ | exact Proof_lem_oai4_finite_existence_transfer.solution _ _ | exact Proof_lem_oai4_finite_existence_transfer.solution _ _ _ | exact Proof_lem_oai4_finite_existence_transfer.solution _ _ _ _

end MMP.Fourfold

