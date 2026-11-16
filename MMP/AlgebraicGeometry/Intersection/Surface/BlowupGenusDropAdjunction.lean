module
public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorAdjunction
public import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryStepEuler
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafSmoothCurve
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.SepClosedComponents

/-!
# Genus drop under point blow-ups, adjunction on surfaces, and the system `(*)`

This file proves three facts about curves on a smooth surface `Y` over an algebraically closed
field `k` and their application to log discrepancies of surface germs.

**Genus drop.**
Let `Y` be a smooth surface over an algebraically closed field `k` of arbitrary characteristic,
`C ⊆ Y` a reduced proper curve, `y ∈ C` a closed point of multiplicity `m = mult_y C`, and
`π : Y' = Bl_y Y ⟶ Y` the blow-up of `y`. The strict transform `C' ⊆ Y'` of `C` is the reduced
closed subscheme on the closure of `π⁻¹(C ∖ {y})`. Then `C'` is proper over `k` and
`p_a(C') = p_a(C) - m(m-1)/2`.

## Main results

* `MMP.Threefold.Resolution.arithmeticGenus_strictTransform_blowUp_singleton`: the genus drop
  `p_a(C') = p_a(C) - m(m-1)/2`.
* `MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic`:
  adjunction `(K_Y + C) · C = -2 χ(C, 𝒪_C)` for a reduced proper curve `C`, proved for smooth `C`
  by the conormal sequence and in general by blowing up singular points, where both sides drop by
  `m(m-1)`.
* `MMP.Flips.isGermLogDiscrepancyVector_iff_sum_mul_eq_neg`: the system `(*)` of FA 3.0.2,
  `∑_k a_k (E_k · E_j) = -c_j`, characterises the log discrepancy vector of a surface germ.
* `MMP.Flips.IsWeightedDualGraph.isGermLogDiscrepancyVector_iff`: that system is the one
  defining a log discrepancy vector of the weighted dual graph `Γ(g)`.

## Implementation notes

A reduced curve is presented by its underlying closed set `C : Closeds Y`, with the reduced
induced structure `Scheme.IdealSheafData.vanishingIdeal C`; that every irreducible component of
`C` is one-dimensional is what makes it a curve. Its strict transform is likewise the reduced
induced structure on `closure (π⁻¹(C ∖ {y}))`. The multiplicity `mult_y C` is
`MMP.Resolution.multAt`, the order of the ideal of `C` in `𝒪_{Y,y}`, and the arithmetic genus
`p_a = 1 - χ(𝒪)` is `MMP.Mori.arithmeticGenus`. The number `m(m-1)/2` is written `m.choose 2`.
Properness of `C'` over `k` is part of the conclusion, since the genus is only defined for proper
schemes.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], 1.38
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.0.2, 3.1.1
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

universe u w

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MMP
open Ideal MvPolynomial

namespace MMP.Proofs.lem_mmp_threefold_surface_blowup_genus_drop

/-- The underlying closed set `C' = closure (π⁻¹(C ∖ {y}))` of the strict transform of `C` under
the blow-up `π` of the closed point `y`. -/
private abbrev strictTransformCloseds {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :=
  ⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
    ((C : Set Y) \ {y})), isClosed_closure⟩

private theorem vanishingIdeal_le_map_strictTransformCloseds {Y : Scheme.{w}} (C : Closeds Y)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Scheme.IdealSheafData.vanishingIdeal C ≤
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).map
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) := by
  rw [Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  change closure _ ⊆ _
  rw [Scheme.IdealSheafData.support_comap]
  refine closure_minimal ?_ ?_
  · intro z hz
    change (blowUpToBase _).base z ∈ ((Scheme.IdealSheafData.vanishingIdeal C).support : Set Y)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hz.1
  · exact Closeds.isClosed _

/-- The morphism `g : C' ⟶ C` from the strict transform to the curve, induced by the blow-up. -/
private noncomputable abbrev strictTransformToCurve {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ _ (vanishingIdeal_le_map_strictTransformCloseds C hy)

private theorem strictTransformToCurve_subschemeι {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    strictTransformToCurve C hy ≫ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- `g : C' ⟶ C` is proper. -/
private theorem isProper_strictTransformToCurve
    {k : Type w} [Field k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (C : Closeds Y) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsProper (strictTransformToCurve C hy) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsProper (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian _)
  have : IsProper (strictTransformToCurve C hy ≫
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι) := by
    rw [strictTransformToCurve_subschemeι]; infer_instance
  exact IsProper.of_comp _ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι

/-- The strict transform of a proper curve under the blow-up of a point is proper over `k`. -/
private theorem isProper_strictTransform
    {k : Type w} [Field k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (C : Closeds Y)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)]
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) := by
  have := isProper_strictTransformToCurve hY C hy
  rw [← Category.assoc, ← strictTransformToCurve_subschemeι, Category.assoc]
  infer_instance

/-- In a space all of whose irreducible components have dimension one, no closed point is
isolated. -/
private theorem not_isOpen_singleton_of_forall_topologicalKrullDim_eq_one {T : Type*}
    [TopologicalSpace T] (hT : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = 1) {t : T}
    (ht : IsClosed ({t} : Set T)) : ¬ IsOpen ({t} : Set T) := by
  intro ho
  obtain ⟨Z, hZ, htZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {t}
    isIrreducible_singleton
  have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.isPreirreducible ho
    ⟨t, htZ rfl, rfl⟩
  have h2 : Z = {t} := by
    refine Set.Subset.antisymm (fun z hz ↦ ?_) htZ
    have := closure_mono Set.inter_subset_right (h1 hz)
    rwa [ht.closure_eq] at this
  have h3 := hT Z hZ
  subst h2
  haveI : Nonempty ({t} : Set T) := ⟨⟨t, rfl⟩⟩
  haveI : Subsingleton ({t} : Set T) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  rw [AlgebraicGeometry.topologicalKrullDim_eq_zero_of_nonempty_subsingleton] at h3
  exact zero_ne_one h3

/-- An open subset of `C` lying over the closed point `y` is empty, when every irreducible
component of `C` is a curve. -/
private theorem eq_bot_of_forall_subschemeι_eq {Y : Scheme.{w}} (C : Closeds Y)
    (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    (O : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens)
    (hO : ∀ x ∈ O, (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x = y) : O = ⊥ := by
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hrange : Set.range iC = (C : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := (Opens.ne_bot_iff_nonempty O).mp hne
  have hx₀y : iC x₀ = y := hO x₀ hx₀
  have hOx : (O : Set _) = {x₀} := by
    refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.singleton_subset_iff.mpr hx₀)
    exact iC.isClosedEmbedding.injective ((hO x hx).trans hx₀y.symm)
  have hOo : IsOpen ({x₀} : Set (Scheme.IdealSheafData.vanishingIdeal C).subscheme) := by
    rw [← hOx]; exact O.2
  obtain ⟨W, hW, hWO⟩ := iC.isClosedEmbedding.isInducing.isOpen_iff.mp hOo
  have hyC : y ∈ (C : Set Y) := hrange ▸ ⟨x₀, hx₀y⟩
  refine not_isOpen_singleton_of_forall_topologicalKrullDim_eq_one hC (t := ⟨y, hyC⟩) ?_ ?_
  · have : ({⟨y, hyC⟩} : Set (C : Set Y)) = Subtype.val ⁻¹' {y} := by
      ext c
      rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
    rw [this]; exact hy.preimage continuous_subtype_val
  · have : ({⟨y, hyC⟩} : Set (C : Set Y)) = Subtype.val ⁻¹' W := by
      ext c
      rw [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
      constructor
      · intro hc
        have : x₀ ∈ iC ⁻¹' W := hWO ▸ rfl
        rw [hc]; change y ∈ W; rw [← hx₀y]; exact this
      · intro hc
        obtain ⟨x, hx⟩ : (c : Y) ∈ Set.range iC := by rw [hrange]; exact c.2
        have : x ∈ iC ⁻¹' W := by
          change iC x ∈ W; rw [hx]; exact hc
        rw [hWO] at this
        change (c : Y) = y
        rw [← hx, this, hx₀y]
    rw [this]; exact hW.preimage continuous_subtype_val

/-- A closed proper subset `S` of a proper irreducible closed subset `Z` of an irreducible `T0`
space of dimension at most two is finite, when `S` is Noetherian: every irreducible closed subset
of `S` is a point, since otherwise it would start a chain of length three. -/
private theorem finite_of_ssubset_of_isIrreducible {X : Type*} [TopologicalSpace X] [T0Space X]
    [IrreducibleSpace X] (hX : topologicalKrullDim X ≤ 2) {Z : Set X} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) (hZu : Z ≠ Set.univ) {S : Set X} (hSc : IsClosed S) (hSZ : S ⊆ Z)
    (hSne : S ≠ Z) [NoetherianSpace S] : S.Finite := by
  have key : ∀ K : Set X, IsIrreducible K → IsClosed K → K ⊆ S → K.Subsingleton := by
    intro K hK hKc hKS
    have hcl : ∀ c ∈ K, closure {c} = K := by
      intro c hc
      by_contra hne
      let a : IrreducibleCloseds X := ⟨closure {c}, isIrreducible_singleton.closure,
        isClosed_closure⟩
      let b : IrreducibleCloseds X := ⟨K, hK, hKc⟩
      let d : IrreducibleCloseds X := ⟨Z, hZ, hZc⟩
      let e : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X,
        isClosed_univ⟩
      have h1 : a < b := SetLike.coe_ssubset_coe.mp
        ((closure_minimal (Set.singleton_subset_iff.mpr hc) hKc).ssubset_of_ne hne)
      have h2 : b < d := SetLike.coe_ssubset_coe.mp
        ((hKS.trans hSZ).ssubset_of_ne fun h ↦ hSne (Set.Subset.antisymm hSZ (h ▸ hKS)))
      have h3 : d < e := SetLike.coe_ssubset_coe.mp ((Set.subset_univ _).ssubset_of_ne hZu)
      have hm : StrictMono ![a, b, d, e] := by
        refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
        fin_cases i
        · exact h1
        · exact h2
        · exact h3
      have hp : ((3 : ℕ) : WithBot ℕ∞) ≤ 2 :=
        (Order.LTSeries.length_le_krullDim (LTSeries.mk 3 _ hm)).trans hX
      exact absurd hp (by decide)
    intro a ha b hb
    exact (inseparable_iff_closure_eq.mpr ((hcl a ha).trans (hcl b hb).symm)).eq
  have hS : S = ⋃ c ∈ irreducibleComponents S, Subtype.val '' c := by
    rw [← Set.image_iUnion₂, ← Set.sUnion_eq_biUnion, sUnion_irreducibleComponents,
      Set.image_univ, Subtype.range_coe]
  rw [hS]
  refine (NoetherianSpace.finite_irreducibleComponents).biUnion fun c hc ↦ ?_
  exact (key _ (hc.1.image _ continuous_subtype_val.continuousOn)
    (hSc.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents c hc))
    (Subtype.coe_image_subset _ _)).finite

/-- In a Noetherian irreducible `T0` space of dimension at most two, a proper closed subset
`closure A` meets a closed set `E` disjoint from `A` in finitely many points. -/
private theorem finite_closure_inter_of_disjoint {X : Type*} [TopologicalSpace X] [T0Space X]
    [IrreducibleSpace X] [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 2) {A E : Set X}
    (hE : IsClosed E) (hAE : Disjoint A E) (hA : closure A ≠ Set.univ) :
    (closure A ∩ E).Finite := by
  have hAu : A = ⋃ c ∈ irreducibleComponents A, Subtype.val '' c := by
    rw [← Set.image_iUnion₂, ← Set.sUnion_eq_biUnion, sUnion_irreducibleComponents,
      Set.image_univ, Subtype.range_coe]
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := A)
  have hcl : closure A = ⋃ c ∈ irreducibleComponents A, closure (Subtype.val '' c) := by
    conv_lhs => rw [hAu]
    exact hfin.closure_biUnion _
  rw [hcl, Set.iUnion₂_inter]
  refine hfin.biUnion fun c hc ↦ ?_
  have hZsub : closure (Subtype.val '' c) ⊆ closure A :=
    closure_mono (Subtype.coe_image_subset _ _)
  obtain ⟨a, ha⟩ := hc.1.nonempty
  refine finite_of_ssubset_of_isIrreducible hX
    (hc.1.image _ continuous_subtype_val.continuousOn).closure isClosed_closure
    (fun h ↦ hA (Set.eq_univ_of_univ_subset (h ▸ hZsub))) (isClosed_closure.inter hE)
    Set.inter_subset_left fun h ↦ ?_
  have : (a : X) ∈ closure (Subtype.val '' c) ∩ E := by
    rw [h]; exact subset_closure (Set.mem_image_of_mem _ ha)
  exact hAE.notMem_of_mem_left a.2 this.2

/-- **(a)** `g : C' ⟶ C` is finite. -/
private theorem isFinite_strictTransformToCurve
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ C) :
    IsFinite (strictTransformToCurve C hy) := by
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsIntegral Y := hY.toIsIntegral
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)
  set π := blowUpToBase I
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  set iC' := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι
  set g := strictTransformToCurve C hy
  have hsupp : ((I.support : Closeds Y) : Set Y) = {y} :=
    MMP.Threefold.Resolution.support_vanishingIdeal_singleton hy
  have hirr := MMP.Threefold.Resolution.isIrreducible_support_vanishingIdeal_singleton hy
  have hc := MMP.Threefold.Resolution.one_le_codimension_vanishingIdeal_singleton hYd hy
  have hdim : topologicalKrullDim (blowUp I) = 2 :=
    MMP.Threefold.Resolution.topologicalKrullDim_blowUp sY I
      (MMP.Threefold.Resolution.isSmoothBlowup_vanishingIdeal_singleton sY hYs hy) hirr hc (d := 2)
      (by exact_mod_cast hYd)
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc
  have hvar := MMP.Threefold.Resolution.isVariety_blowUp_singleton hY hYd hy
  have : LocallyOfFiniteType (π ≫ sY) := hvar.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  have : CompactSpace (blowUp I) := MMP.Threefold.Resolution.compactSpace_blowUp_singleton hY hYd hy
  have : IsNoetherian (blowUp I) := {}
  -- `C ≠ Y`
  have hCne : (C : Set Y) ≠ Set.univ := by
    intro hCu
    have e : (C : Set Y) ≃ₜ Y := (Homeomorph.setCongr hCu).trans (Homeomorph.Set.univ Y)
    have : IrreducibleSpace (C : Set Y) := (e.irreducibleSpace_iff).mpr inferInstance
    have h1 := hC Set.univ (by rw [irreducibleComponents_eq_singleton]; rfl)
    have h2 : topologicalKrullDim (Set.univ : Set (C : Set Y)) = topologicalKrullDim Y :=
      IsHomeomorph.topologicalKrullDim_eq _ ((Homeomorph.Set.univ _).trans e).isHomeomorph
    rw [h1, hYd] at h2
    exact absurd h2 (by decide)
  -- `C' ≠ Y'`
  set A := π.base ⁻¹' ((C : Set Y) \ {y})
  have hC'ne : closure A ≠ Set.univ := by
    intro hAu
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).mp hCne
    obtain ⟨w, hw⟩ := exists_blowUpToBase_eq_of_notMem_support I (x := z)
      (by rw [hsupp]; rintro rfl; exact hz hyC)
    obtain ⟨a, haW, haA⟩ := (dense_iff_closure_eq.mpr hAu).inter_open_nonempty
      (π.base ⁻¹' (C : Set Y)ᶜ) ((C.isClosed.isOpen_compl).preimage π.continuous)
      ⟨w, show π w ∉ (C : Set Y) by rw [hw]; exact hz⟩
    exact haW haA.1
  have hfin : (closure A ∩ π.base ⁻¹' {y}).Finite :=
    finite_closure_inter_of_disjoint hdim.le (hy.preimage π.continuous)
      (Set.disjoint_left.mpr fun a ha hb ↦ ha.2 hb) hC'ne
  have hrange' : Set.range iC' = closure A := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hg : g ≫ iC = iC' ≫ π := strictTransformToCurve_subschemeι C hy
  have : IsProper g := isProper_strictTransformToCurve hY C hy
  have : LocallyQuasiFinite g := by
    refine locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun z ↦ ?_
    have hmem : ∀ w ∈ g ⁻¹' {z}, iC' w ∈ closure A ∧ π (iC' w) = iC z := by
      intro w hw
      refine ⟨hrange' ▸ Set.mem_range_self w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hg, Scheme.Hom.comp_apply]
      exact congrArg iC hw
    refine Set.Finite.of_finite_image ?_ iC'.isClosedEmbedding.injective.injOn
    by_cases hz : iC z = y
    · refine hfin.subset ?_
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨(hmem w hw).1, by change π (iC' w) = y; rw [(hmem w hw).2, hz]⟩
    · refine Set.Subsingleton.finite ?_
      rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
      refine blowUpToBase_injective_of_notMem_support I ?_ ?_
      · rw [hsupp, (hmem w₁ hw₁).2]; exact hz
      · rw [(hmem w₁ hw₁).2, (hmem w₂ hw₂).2]
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- **(c)** `g : C' ⟶ C` is an isomorphism over `C ∖ {y}`. -/
private theorem isIso_strictTransformToCurve_restrict {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) :
    IsIso (strictTransformToCurve C hy ∣_
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ ⟨{y}ᶜ, hy.isOpen_compl⟩)) := by
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  set iC' := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι
  set g := strictTransformToCurve C hy
  set V : Y.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  have hsupp : (((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
      Closeds Y) : Set Y) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hπV : IsIso (π ∣_ V) :=
    isIso_blowUpToBase_restrict_of_subset_compl_support _ V (fun z hz ↦ by rw [hsupp]; exact hz)
  have hg : g ≫ iC = iC' ≫ π := strictTransformToCurve_subschemeι C hy
  have hci : IsClosedImmersion ((g ≫ iC) ∣_ V) := by
    rw [hg, morphismRestrict_comp]
    have : IsClosedImmersion (iC' ∣_ (π ⁻¹ᵁ V)) :=
      IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
    exact @IsClosedImmersion.comp _ _ _ _ _ this inferInstance
  rw [morphismRestrict_comp] at hci
  have : IsClosedImmersion (iC ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
  have : IsClosedImmersion (g ∣_ (iC ⁻¹ᵁ V)) :=
    @IsClosedImmersion.of_comp _ _ _ _ (iC ∣_ V) hci inferInstance
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  have : Surjective (g ∣_ (iC ⁻¹ᵁ V)) := by
    refine ⟨fun z ↦ ?_⟩
    have hz : iC z.1 ≠ y := z.2
    have hzC : iC z.1 ∈ (C : Set Y) := by
      have := Set.mem_range_self (f := iC) z.1
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    obtain ⟨w', hw'⟩ := exists_blowUpToBase_eq_of_notMem_support
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) (x := iC z.1)
      (by rw [hsupp]; exact hz)
    have hw'C : w' ∈ (strictTransformCloseds C hy : Set _) :=
      subset_closure ⟨by rw [hw']; exact hzC, by rw [hw']; exact hz⟩
    obtain ⟨w, rfl⟩ : w' ∈ Set.range iC' := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hw'C
    have hgw : g w = z.1 := by
      apply iC.isClosedEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
      exact hw'
    refine ⟨⟨w, ?_⟩, Subtype.ext ?_⟩
    · change iC (g w) ∈ V
      rw [hgw]
      exact z.2
    · exact (morphismRestrict_base_coe g _ _).trans hgw
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The maps of sections of `g : C' ⟶ C` are injective. -/
private theorem injective_app_strictTransformToCurve {Y : Scheme.{w}}
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ∀ W, Function.Injective ((strictTransformToCurve C hy).app W).hom := by
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  set g := strictTransformToCurve C hy
  set U := iC ⁻¹ᵁ (⟨{y}ᶜ, hy.isOpen_compl⟩ : Y.Opens)
  have hiso : IsIso (g ∣_ U) := isIso_strictTransformToCurve_restrict C hy
  have : IsReduced (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
  have hnopen : ∀ O : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Opens,
      (O : Set (Scheme.IdealSheafData.vanishingIdeal C).subscheme) ⊆ (↑U)ᶜ → O = ⊥ :=
    fun O hO ↦ eq_bot_of_forall_subschemeι_eq C hC hy O fun x hx ↦ by
      by_contra h; exact hO hx h
  intro W
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hle : W ⊓ U ≤ U := inf_le_right
  have hI : IsIso (g.app (W ⊓ U)) :=
    Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict g U _ hle
  have hres : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.map
      (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s = 0 := by
    have h := ConcreteCategory.congr_hom
      (g.naturality (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) s
    simp only [ConcreteCategory.comp_apply, hs, map_zero] at h
    exact (ConcreteCategory.injective_of_mono_of_preservesPullback (g.app (W ⊓ U)))
      (h.trans (map_zero _).symm)
  have hb : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.basicOpen s ⊓ U = ⊥ := by
    have := congrArg (Scheme.basicOpen _) hres
    rw [Scheme.basicOpen_res, Scheme.basicOpen_zero] at this
    rw [← this]
    exact le_antisymm
      (le_inf (le_inf (inf_le_left.trans (Scheme.basicOpen_le _ s)) inf_le_right) inf_le_left)
      (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  refine eq_zero_of_basicOpen_eq_bot s (hnopen _ fun x hx hxU ↦ ?_)
  have : x ∈ (Scheme.IdealSheafData.vanishingIdeal C).subscheme.basicOpen s ⊓ U := ⟨hx, hxU⟩
  rw [hb] at this
  exact this

/-- **(b)** `𝒪_C ⟶ g_*𝒪_{C'}` is a monomorphism. -/
private theorem mono_pushforwardAlgebra_strictTransformToCurve {Y : Scheme.{w}}
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
      (strictTransformToCurve C hy)).hom := by
  have key := injective_app_strictTransformToCurve C hC hy
  refine (TopCat.Sheaf.forget CommRingCat.{w} _).mono_of_mono_map ?_
  exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _
    (fun W => ConcreteCategory.mono_of_injective _ (key W.unop))

/-- `dim_k H⁰(X, ℱ)` is the `k`-dimension of the stalk at `x₀` for a coherent `ℱ` supported in
`{x₀}` on a proper `k`-scheme. -/
private theorem finrank_cohomologyOverField_zero_eq_finrank_stalk_of_supp_subset
    (k : Type w) [Field k] {X : Scheme.{w}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] {x₀ : X} (hsupp : SheafOfModules.supp F ⊆ {x₀}) :
    Module.finrank k (cohomologyOverField k f F 0) =
      Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appLE ⊤ ⊤ (by simp) ≫ X.presheaf.germ ⊤ x₀ trivial).hom).obj
          (OXModule.stalk F x₀)) := by
  have hF : topologicalKrullDim (SheafOfModules.supp F) ≤ 0 := by
    refine (topologicalKrullDim_le_of_subset hsupp).trans ?_
    have : Subsingleton ({x₀} : Set X) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    have : Nonempty ({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
    exact le_of_eq topologicalKrullDim_eq_zero_of_nonempty_subsingleton
  letI : Fintype ↥(SheafOfModules.supp F) := (finite_supp_of_supp_le_zero k f F hF).fintype
  rw [finrank_cohomologyOverField_zero_eq_sum_finrank_stalk k f F hF]
  by_cases hx : x₀ ∈ SheafOfModules.supp F
  · rw [Fintype.sum_eq_single ⟨x₀, hx⟩ fun x hne ↦ absurd (Subtype.ext (hsupp x.2)) hne]
  · have h0 : Subsingleton ((Scheme.Modules.presheaf F).stalk x₀) :=
      subsingleton_stalk_of_notMem_supp F hx
    have hE : IsEmpty ↥(SheafOfModules.supp F) :=
      ⟨fun x ↦ hx (by rw [← hsupp x.2]; exact x.2)⟩
    rw [Fintype.sum_empty, eq_comm]
    haveI : Subsingleton ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        f.appLE ⊤ ⊤ (by simp) ≫ X.presheaf.germ ⊤ x₀ trivial).hom).obj
          (OXModule.stalk F x₀)) := h0
    exact Module.finrank_zero_of_subsingleton

/-! ### Commutative algebra of the first neighbourhood ring -/

section Algebra

private theorem span_pair_pow_succ_le {R : Type*} [CommRing R] (x t : R) (k : ℕ) :
    span {x, t} ^ (k + 1) ≤ span {x} * span {x, t} ^ k ⊔ span {t ^ (k + 1)} := by
  induction k with
  | zero =>
    simp only [zero_add, pow_one, pow_zero]
    rw [Ideal.span_insert, mul_one]
  | succ k ih =>
    rw [pow_succ']
    calc span {x, t} * span {x, t} ^ (k + 1)
        ≤ span {x, t} * (span {x} * span {x, t} ^ k ⊔ span {t ^ (k + 1)}) :=
          Ideal.mul_mono_right ih
      _ ≤ span {x} * span {x, t} ^ (k + 1) ⊔ span {t ^ (k + 1 + 1)} := by
        rw [Ideal.mul_sup]
        refine sup_le ?_ ?_
        · rw [← mul_assoc, mul_comm (span {x, t}) (span {x}), mul_assoc, ← pow_succ']
          exact le_sup_left
        · rw [Ideal.span_insert, Ideal.sup_mul]
          refine sup_le ?_ ?_
          · refine le_sup_of_le_left (Ideal.mul_mono_right ?_)
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)) _
          · refine le_sup_of_le_right ?_
            rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']

private theorem span_pair_pow_succ_eq_of_mem {R : Type*} [CommRing R] (x t : R) (n : ℕ)
    (hrel : t ^ (n + 1) ∈ span {x} * span {x, t} ^ n) :
    span {x, t} ^ (n + 1) = span {x} * span {x, t} ^ n := by
  refine le_antisymm ((span_pair_pow_succ_le x t n).trans (sup_le le_rfl ?_)) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hrel
  · rw [pow_succ']
    exact Ideal.mul_mono_left (by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.subset_span (Set.mem_insert x _))

private theorem exists_mul_eq_of_mem_pow {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (x t : R) (τ : B) (hτ : algebraMap R B x * τ = algebraMap R B t) (k : ℕ) :
    ∀ r ∈ span {x, t} ^ k, ∃ b : B, algebraMap R B (x ^ k) * b = algebraMap R B r := by
  induction k with
  | zero => intro r _; exact ⟨algebraMap R B r, by simp⟩
  | succ k ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha c hc
      obtain ⟨b, hb⟩ := ih a ha
      obtain ⟨α, β, rfl⟩ : ∃ α β : R, α * x + β * t = c := Ideal.mem_span_pair.mp hc
      refine ⟨b * (algebraMap R B α + algebraMap R B β * τ), ?_⟩
      rw [map_mul, ← hb]
      simp only [map_add, map_mul, map_pow, ← hτ]
      ring
    · rintro a c ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
      exact ⟨b₁ + b₂, by rw [mul_add, h₁, h₂, map_add]⟩

private theorem length_quotient_range_add {S R B : Type*} [CommRing S] [CommRing R] [CommRing B]
    [Algebra R B] [Algebra S R] [Algebra S B] [IsScalarTower S R B]
    (hinj : Function.Injective (algebraMap R B)) (x t : R) (τ : B)
    (hτ : algebraMap R B x * τ = algebraMap R B t) (hgen : Algebra.adjoin R {τ} = ⊤)
    (hx : IsLeftRegular (algebraMap R B x)) (n : ℕ)
    (hrel : t ^ (n + 1) ∈ span {x} * span {x, t} ^ n) :
    Module.length S (B ⧸ LinearMap.range (Algebra.linearMap R B)) +
      Module.length S (R ⧸ span {x, t} ^ (n + 1)) =
      Module.length S (R ⧸ span {x ^ (n + 1)}) := by
  set ι := algebraMap R B
  set I := span {x, t} ^ (n + 1) with hI
  have hIeq : I = span {x} * span {x, t} ^ n := span_pair_pow_succ_eq_of_mem x t n hrel
  have hxN : IsLeftRegular (ι (x ^ (n + 1))) := by rw [map_pow]; exact hx.pow _
  -- every element of `B` times `x^(n+1)` lies in the image of `I`
  have hall : ∀ b : B, ∃ r ∈ I, ι (x ^ (n + 1)) * b = ι r := by
    let P : Submodule R B :=
      { carrier := {b | ∃ r ∈ I, ι (x ^ (n + 1)) * b = ι r}
        add_mem' := by
          rintro a c ⟨r₁, h₁, e₁⟩ ⟨r₂, h₂, e₂⟩
          exact ⟨r₁ + r₂, I.add_mem h₁ h₂, by rw [mul_add, e₁, e₂, map_add]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨r, h, e⟩
          refine ⟨c * r, I.mul_mem_left c h, ?_⟩
          rw [Algebra.smul_def, mul_left_comm, e, map_mul] }
    have hτP : ∀ b ∈ P, τ * b ∈ P := by
      rintro b ⟨r, hr, e⟩
      rw [hIeq] at hr
      obtain ⟨s, hs, rfl⟩ := Ideal.mem_span_singleton_mul.mp hr
      refine ⟨t * s, ?_, ?_⟩
      · rw [hI, pow_succ']
        exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hs
      · rw [mul_left_comm, e, map_mul, map_mul, ← hτ]; ring
    have h1 : (1 : B) ∈ P := ⟨x ^ (n + 1), Ideal.pow_mem_pow (Ideal.subset_span
      (Set.mem_insert x _)) _, by simp⟩
    intro b
    have hb : b ∈ Algebra.adjoin R {τ} := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨p, rfl⟩ := hb
    change Polynomial.aeval τ p ∈ P
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact P.add_mem hp hq
    | monomial k c =>
      rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
      refine P.smul_mem c ?_
      induction k with
      | zero => simpa using h1
      | succ k ih => rw [pow_succ']; exact hτP _ ih
  let μ : B →ₗ[R] B := LinearMap.mulLeft R (ι (x ^ (n + 1)))
  have hμ : Function.Injective μ := hxN
  have hrange : LinearMap.range μ = Submodule.map (Algebra.linearMap R B) (I : Submodule R R) := by
    ext b
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨r, hr, e⟩ := hall c
      exact Submodule.mem_map.mpr ⟨r, hr, e.symm⟩
    · intro hb
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hb
      exact exists_mul_eq_of_mem_pow x t τ hτ _ r hr
  let e : B ≃ₗ[R] I := (LinearEquiv.ofInjective μ hμ).trans ((LinearEquiv.ofEq _ _ hrange).trans
    (Submodule.equivMapOfInjective (Algebra.linearMap R B) hinj I).symm)
  have he : ∀ b, ι ((e b : I) : R) = ι (x ^ (n + 1)) * b := by
    intro b
    exact congrArg Subtype.val ((Submodule.equivMapOfInjective (Algebra.linearMap R B) hinj
      I).apply_symm_apply ((LinearEquiv.ofEq _ _ hrange) (LinearEquiv.ofInjective μ hμ b)))
  set J : Submodule R R := span {x ^ (n + 1)}
  have hJI : J ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert x _)) _
  set J' : Submodule R I := J.comap I.subtype
  have hmap : (LinearMap.range (Algebra.linearMap R B)).map (e : B →ₗ[R] I) = J' := by
    ext z
    rw [Submodule.mem_map_equiv]
    obtain ⟨b, rfl⟩ := e.surjective z
    rw [LinearEquiv.symm_apply_apply]
    constructor
    · rintro ⟨r, rfl⟩
      change ((e (ι r) : I) : R) ∈ J
      have h1 := he (ι r)
      rw [← map_mul] at h1
      rw [hinj h1, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · intro hz
      change ((e b : I) : R) ∈ J at hz
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨r, hxN ?_⟩
      change ι (x ^ (n + 1)) * ι r = ι (x ^ (n + 1)) * b
      rw [← he b, ← hr, map_mul, mul_comm]
  have hlen1 : Module.length S (B ⧸ LinearMap.range (Algebra.linearMap R B)) =
      Module.length S (I ⧸ J') :=
    ((Submodule.Quotient.equiv _ _ e hmap).restrictScalars S).length_eq
  rw [hlen1]
  let f : (I ⧸ J') →ₗ[R] (R ⧸ J) := J'.liftQ (J.mkQ ∘ₗ I.subtype) (by
    intro z hz
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hz)
  let g : (R ⧸ J) →ₗ[R] (R ⧸ I) := J.mapQ I LinearMap.id hJI
  refine (Module.length_eq_add_of_exact (f.restrictScalars S) (g.restrictScalars S) ?_ ?_ ?_).symm
  · have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
      ext z
      simp [J', Ideal.Quotient.eq_zero_iff_mem]
    exact hf
  · intro q
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  · intro q
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    constructor
    · intro h
      change Submodule.Quotient.mk (p := I) r = 0 at h
      rw [Submodule.Quotient.mk_eq_zero] at h
      exact ⟨Submodule.Quotient.mk ⟨r, h⟩, rfl⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [← hz]
      change Submodule.Quotient.mk (p := I) (w : R) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact w.2

private theorem length_quotient_eq_add_of_colon {S A : Type*} [CommRing S] [CommRing A] [Algebra S
    A]
    (I L : Ideal A) (e : A) (hL : ∀ a, a * e ∈ I ↔ a ∈ L) :
    Module.length S (A ⧸ I) = Module.length S (A ⧸ L) + Module.length S (A ⧸ (I ⊔ span {e})) := by
  let f : (A ⧸ L) →ₗ[A] (A ⧸ I) := L.liftQ (I.mkQ ∘ₗ LinearMap.mulRight A e) (by
    intro a ha
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hL a).mpr ha)
  let g : (A ⧸ I) →ₗ[A] (A ⧸ (I ⊔ span {e})) := I.mapQ _ LinearMap.id le_sup_left
  refine Module.length_eq_add_of_exact (f.restrictScalars S) (g.restrictScalars S) ?_ ?_ ?_
  · have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
      ext a
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (hL a).symm
    exact hf
  · intro q
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  · intro q
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    constructor
    · intro h
      change Submodule.Quotient.mk (p := I ⊔ span {e}) b = 0 at h
      rw [Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨i, hi, c, hc, rfl⟩ := Submodule.mem_sup.mp h
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (p := I) (a * e) = Submodule.Quotient.mk (i + a * e)
      rw [Submodule.Quotient.eq]
      simpa using I.neg_mem hi
    · rintro ⟨z, hz⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [← hz]
      change Submodule.Quotient.mk (p := I ⊔ span {e}) (a * e) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self e))

private theorem length_quotient_top {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] (I :
    Ideal A)
    (hI : I = ⊤) : Module.length S (A ⧸ I) = 0 := by
  subst hI
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.length_eq_zero

private theorem length_quotient_maximalIdeal {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] (hres : Function.Surjective (algebraMap k (A ⧸ IsLocalRing.maximalIdeal A))) :
    Module.length k (A ⧸ IsLocalRing.maximalIdeal A) = 1 := by
  have hbij : Function.Bijective (Algebra.linearMap k (A ⧸ IsLocalRing.maximalIdeal A)) :=
    ⟨(algebraMap k _).injective, hres⟩
  rw [← (LinearEquiv.ofBijective _ hbij).length_eq, Module.length_eq_finrank, Module.finrank_self]
  rfl

private theorem length_quotient_span_pair_pow {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] (hres : Function.Surjective (algebraMap k (A ⧸ IsLocalRing.maximalIdeal A)))
    {x t : A} (hm : span {x, t} = IsLocalRing.maximalIdeal A) (hx : Prime x)
    (ht : t ∉ span {x}) (n : ℕ) : Module.length k (A ⧸ span {x, t ^ n}) = n := by
  induction n with
  | zero =>
    refine length_quotient_top _ ?_
    rw [pow_zero, Ideal.eq_top_iff_one]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  | succ n ih =>
    rw [length_quotient_eq_add_of_colon (S := k) (span {x, t ^ (n + 1)})
      (IsLocalRing.maximalIdeal A) (t ^ n), length_quotient_maximalIdeal hres]
    · have hsup : span {x, t ^ (n + 1)} ⊔ span {t ^ n} = span {x, t ^ n} := by
        apply le_antisymm
        · refine sup_le ?_ ?_
          · rw [Ideal.span_le]
            rintro z (rfl | rfl)
            · exact Ideal.subset_span (Set.mem_insert _ _)
            · rw [pow_succ]
              exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
          · rw [Ideal.span_le, Set.singleton_subset_iff]
            exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
        · rw [Ideal.span_le]
          rintro z (rfl | rfl)
          · exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
          · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      rw [hsup, ih]
      push_cast; ring
    · intro a
      rw [← hm]
      constructor
      · intro h
        obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp h
        have h1 : t ^ n * (a - v * t) ∈ span {x} := by
          rw [Ideal.mem_span_singleton']
          exact ⟨u, by rw [pow_succ] at huv; linear_combination huv⟩
        rcases (Ideal.span_singleton_prime hx.ne_zero).mpr hx |>.mem_or_mem h1 with h2 | h2
        · exact absurd ((Ideal.span_singleton_prime hx.ne_zero).mpr hx |>.mem_of_pow_mem _ h2) ht
        · obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h2
          exact Ideal.mem_span_pair.mpr ⟨w, v, by linear_combination hw⟩
      · intro h
        obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp h
        exact Ideal.mem_span_pair.mpr ⟨u * t ^ n, v, by ring⟩

private theorem mem_span_of_mul_mem_span {A : Type*} [CommRing A] [IsDomain A] {x t f a g : A} {m :
    ℕ}
    (hx : Prime x) (ht : t ∉ span {x}) (ha : IsUnit a) (hf : f = a * t ^ m + x * g) (c : A)
    (hc : c * x ∈ span {f}) : c ∈ span {f} := by
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hc
  have h1 : x ∣ d * a * t ^ m := ⟨c - d * g, by rw [hf] at hd; linear_combination hd⟩
  rcases hx.dvd_or_dvd h1 with h2 | h2
  · rcases hx.dvd_or_dvd h2 with ⟨d', rfl⟩ | h3
    · refine Ideal.mem_span_singleton'.mpr ⟨d', ?_⟩
      have : x * (d' * f) = x * c := by linear_combination hd
      exact (mul_left_cancel₀ hx.ne_zero this).symm ▸ rfl
    · exact absurd (isUnit_of_dvd_unit h3 ha) hx.not_isUnit
  · exact absurd (Ideal.mem_span_singleton.mpr (hx.dvd_of_dvd_pow h2)) ht

private theorem mem_span_of_pow_mul_mem_span {A : Type*} [CommRing A] [IsDomain A] {x t f a g : A}
    {m : ℕ} (hx : Prime x) (ht : t ∉ span {x}) (ha : IsUnit a) (hf : f = a * t ^ m + x * g)
    (n : ℕ) (c : A) (hc : c * x ^ n ∈ span {f}) : c ∈ span {f} := by
  induction n generalizing c with
  | zero => simpa using hc
  | succ n ih =>
    refine ih c (mem_span_of_mul_mem_span hx ht ha hf _ ?_)
    rw [mul_assoc, ← pow_succ]; exact hc

private theorem length_quotient_sup_span_pow {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [IsDomain A] [Algebra k A]
    (hres : Function.Surjective (algebraMap k (A ⧸ IsLocalRing.maximalIdeal A)))
    {x t f a g : A} {m : ℕ} (hm : span {x, t} = IsLocalRing.maximalIdeal A) (hx : Prime x)
    (ht : t ∉ span {x}) (ha : IsUnit a) (hf : f = a * t ^ m + x * g) (n : ℕ) :
    Module.length k (A ⧸ (span {f} ⊔ span {x ^ n})) = n * m := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    refine length_quotient_top (S := k) _ ?_
    rw [pow_zero, Ideal.span_singleton_one, sup_top_eq]
  | succ n ih =>
    rw [length_quotient_eq_add_of_colon (S := k) (A := A) (span {f} ⊔ span {x ^ (n + 1)})
      (span {f} ⊔ span {x}) (x ^ n)]
    · have hsup : span {f} ⊔ span {x ^ (n + 1)} ⊔ span {x ^ n} = span {f} ⊔ span {x ^ n} := by
        rw [sup_assoc]
        congr 1
        refine sup_eq_right.mpr ?_
        rw [Ideal.span_singleton_le_span_singleton, pow_succ]
        exact dvd_mul_right _ _
      have hfx : span {f} ⊔ span {x} = span {x, t ^ m} := by
        rw [Ideal.span_insert, sup_comm]
        apply le_antisymm
        · refine sup_le le_sup_left ?_
          rw [Ideal.span_singleton_le_iff_mem, hf]
          exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _
            (Ideal.mem_span_singleton_self _)))
            (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
        · refine sup_le le_sup_left ?_
          rw [Ideal.span_singleton_le_iff_mem]
          obtain ⟨u, hu⟩ := ha.exists_left_inv
          have : t ^ m = u * f - u * g * x := by
            rw [hf]; linear_combination (-(t ^ m)) * hu
          rw [this]
          exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _
            (Ideal.mem_span_singleton_self _)))
            (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [hsup, ih, hfx, length_quotient_span_pair_pow hres hm hx ht]
      push_cast; ring
    · intro c
      constructor
      · intro h
        obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp h
        obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hq
        have h1 : (c - v * x) * x ^ n ∈ span {f} := by
          have : (c - v * x) * x ^ n = p := by rw [pow_succ] at hpq; linear_combination -hpq
          rw [this]; exact hp
        have h2 := mem_span_of_pow_mul_mem_span hx ht ha hf n _ h1
        have : c = (c - v * x) + v * x := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h2)
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · intro h
        obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp h
        obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hq
        rw [add_mul]
        refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ hp)) ?_
        refine Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨v, ?_⟩)
        ring

private theorem length_quotient_map_eq {k A R : Type*} [Field k] [CommRing A] [Algebra k
    A] [CommRing R]
    [Algebra k R] (φ : A →ₐ[k] R) (hφ : Function.Surjective φ) (J : Ideal A) :
    Module.length k (R ⧸ J.map (φ : A →+* R)) =
      Module.length k (A ⧸ (RingHom.ker φ ⊔ J)) := by
  let ψ : A →ₐ[k] R ⧸ J.map (φ : A →+* R) := (Ideal.Quotient.mkₐ k (J.map (φ : A →+* R))).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ψ = RingHom.ker φ ⊔ J := by
    change RingHom.ker ((Ideal.Quotient.mk (J.map (φ : A →+* R))).comp (φ : A →+* R)) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective (φ : A →+* R) hφ,
      sup_comm, ← RingHom.ker_eq_comap_bot]
    rfl
  have e : (A ⧸ (RingHom.ker φ ⊔ J)) ≃ₐ[k] R ⧸ J.map (φ : A →+* R) :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hψ)
  exact e.toLinearEquiv.length_eq.symm

private theorem length_quotient_range_eq_sum {k A R B : Type*} [Field k] [CommRing A] [IsLocalRing
    A]
    [IsDomain A] [Algebra k A]
    (hres : Function.Surjective (algebraMap k (A ⧸ IsLocalRing.maximalIdeal A)))
    {x t f a g : A} {m : ℕ} (hm1 : 1 ≤ m) (hm : span {x, t} = IsLocalRing.maximalIdeal A)
    (hx : Prime x) (ht : t ∉ span {x}) (ha : IsUnit a) (hf : f = a * t ^ m + x * g)
    (hg : g ∈ span {x, t} ^ (m - 1))
    (hHilb : FiniteDimensional k (A ⧸ IsLocalRing.maximalIdeal A ^ m) ∧
      2 * Module.finrank k (A ⧸ IsLocalRing.maximalIdeal A ^ m) = m * (m + 1))
    [CommRing R] [Algebra k R] (φ : A →ₐ[k] R) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = span {f})
    [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    (hinj : Function.Injective (algebraMap R B)) (τ : B)
    (hτ : algebraMap R B (φ x) * τ = algebraMap R B (φ t)) (hgen : Algebra.adjoin R {τ} = ⊤)
    (hreg : IsLeftRegular (algebraMap R B (φ x))) :
    Module.length k (B ⧸ LinearMap.range (Algebra.linearMap R B)) =
      ((∑ j ∈ Finset.range m, j : ℕ) : ℕ∞) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hg
  have hfker : φ f = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self f
  have hmapI : ∀ j : ℕ, (span {x, t} ^ j).map (φ : A →+* R) = span {φ x, φ t} ^ j := by
    intro j
    rw [Ideal.map_pow, Ideal.map_span]
    congr 2
    simp [Set.image_insert_eq]
  have hrel : φ t ^ (n + 1) ∈ span {φ x} * span {φ x, φ t} ^ n := by
    obtain ⟨u, hu⟩ := ha.exists_left_inv
    have h1 : φ t ^ (n + 1) = φ x * (-(φ u * φ g)) := by
      have := congrArg φ hf
      rw [hfker, map_add, map_mul, map_mul, map_pow] at this
      have hu' : φ u * φ a = 1 := by rw [← map_mul, hu, map_one]
      linear_combination (-(φ u)) * this + (-(φ t ^ (n + 1))) * hu'
    rw [h1]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    rw [← hmapI]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hg))
  have hmain := length_quotient_range_add (S := k) hinj (φ x) (φ t) τ hτ hgen hreg n hrel
  have hx' : span {φ x ^ (n + 1)} = (span {x ^ (n + 1)}).map (φ : A →+* R) := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]; rfl
  rw [hx', length_quotient_map_eq φ hφ, hker,
    length_quotient_sup_span_pow hres hm hx ht ha hf, ← hmapI, length_quotient_map_eq φ hφ,
    hker] at hmain
  have htm : t ∈ span {x, t} := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton t))
  have hxm : x ∈ span {x, t} := Ideal.subset_span (Set.mem_insert x _)
  have hfm : f ∈ span {x, t} ^ (n + 1) := by
    rw [hf]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow htm _)) ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul hxm hg
  have hsup : span {f} ⊔ span {x, t} ^ (n + 1) = IsLocalRing.maximalIdeal A ^ (n + 1) := by
    rw [sup_eq_right.mpr (Ideal.span_singleton_le_iff_mem _ |>.mpr hfm), hm]
  rw [hsup] at hmain
  haveI := hHilb.1
  rw [Module.length_eq_finrank k (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))] at hmain
  have hsum : (∑ j ∈ Finset.range (n + 1), j) * 2 = (n + 1) * n :=
    Finset.sum_range_id_mul_two (n + 1)
  set s := ∑ j ∈ Finset.range (n + 1), j
  set h := Module.finrank k (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1))
  have h2 := hHilb.2
  have hsh : s + h = (n + 1) * (n + 1) := by nlinarith
  have hmain' : Module.length k (B ⧸ LinearMap.range (Algebra.linearMap R B)) + (h : ℕ∞) =
      (s : ℕ∞) + h := by
    rw [hmain, ← Nat.cast_add, hsh]; push_cast; ring
  exact WithTop.add_right_cancel (ENat.natCast_ne_top h) hmain'

private theorem exists_isHomogeneous_aeval_eq {A : Type*} [CommRing A] (v : Fin 2 → A) (m : ℕ) :
    ∀ f ∈ span (Set.range v) ^ m, ∃ F : MvPolynomial (Fin
        2) A, F.IsHomogeneous m ∧ aeval v F = f := by
  induction m with
  | zero => intro f _; exact ⟨C f, isHomogeneous_C _ f, by simp⟩
  | succ m ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro p hp q hq
      obtain ⟨P, hP, rfl⟩ := ih p hp
      obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨P * ∑ i, C (w i) * X i, hP.mul (IsHomogeneous.sum _ _ _ fun i _ =>
        isHomogeneous_C_mul_X _ _), ?_⟩
      simp [smul_eq_mul]
    · rintro p q ⟨P, hP, rfl⟩ ⟨Q, hQ, rfl⟩
      exact ⟨P + Q, hP.add hQ, map_add _ _ _⟩

private theorem aeval_monomial_fin_two {A : Type*} [CommRing A] (v : Fin 2 → A) (d : Fin 2 →₀ ℕ) (a
    : A) :
    aeval v (monomial d a) = a * (v 0 ^ d 0 * v 1 ^ d 1) := by
  rw [aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, Finsupp.prod_fintype _ _
    (fun _ => pow_zero _), Fin.prod_univ_two]

private theorem add_pow_sub_pow_mem {A : Type*} [CommRing A] (I : Ideal A) {x y : A} (hx : x ∈ I)
    (hy : y ∈ I) (n : ℕ) : (x + y) ^ (n + 1) - y ^ (n + 1) ∈ span {x} * I ^ n := by
  induction n with
  | zero => simpa using Ideal.mem_span_singleton_self x
  | succ n ih =>
    have : (x + y) ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        (x + y) * ((x + y) ^ (n + 1) - y ^ (n + 1)) + x * y ^ (n + 1) := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x)
      (Ideal.pow_mem_pow hy _))
    have h := Ideal.mul_mem_mul (I.add_mem hx hy) ih
    have e : I * (span {x} * I ^ n) = span {x} * I ^ (n + 1) := by ring
    exact e ▸ h

private theorem aeval_sub_mem_of_isHomogeneous {A : Type*} [CommRing A] (I : Ideal A) {x t c : A}
    (hx : x ∈ I) (ht : t ∈ I) {F : MvPolynomial (Fin 2) A} {m : ℕ} (hF : F.IsHomogeneous m) :
    aeval ![x + c * t, t] F - aeval ![c, 1] F * t ^ m ∈ span {x} * I ^ (m - 1) := by
  rw [F.as_sum, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : d 0 + d 1 = m := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  simp only [aeval_monomial_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
  · rw [h0] at hdeg ⊢
    simp only [pow_zero, one_mul, zero_add] at hdeg ⊢
    rw [hdeg, mul_one, sub_self]
    exact Ideal.zero_mem _
  · obtain ⟨n, hn⟩ : ∃ n, d 0 = n + 1 := ⟨d 0 - 1, by omega⟩
    have hm : m - 1 = n + d 1 := by omega
    have key : F.coeff d * ((x + c * t) ^ d 0 * t ^ d 1) - F.coeff d * c ^ d 0 * t ^ m =
        F.coeff d * t ^ d 1 * ((x + c * t) ^ (n + 1) - (c * t) ^ (n + 1)) := by
      rw [← hdeg, hn, mul_pow, pow_add]; ring
    rw [key, hm]
    have hD := add_pow_sub_pow_mem I hx (I.mul_mem_left c ht) n
    have h := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht (d 1)) hD
    have e : I ^ d 1 * (span {x} * I ^ n) = span {x} * I ^ (n + d 1) := by ring
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ (e ▸ h)

private theorem aeval_mem_mul_pow_of_coeff_mem {A : Type*} [CommRing A] (I J : Ideal A) (v : Fin 2
    → A)
    (hv : ∀ i, v i ∈ I) {F : MvPolynomial (Fin 2) A} {n : ℕ} (hF : F.IsHomogeneous n)
    (hJ : ∀ d, F.coeff d ∈ J) : aeval v F ∈ J * I ^ n := by
  rw [F.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : d 0 + d 1 = n := by
    have := hF (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  rw [aeval_monomial_fin_two, ← hdeg, pow_add]
  exact Ideal.mul_mem_mul (hJ d) (Ideal.mul_mem_mul (Ideal.pow_mem_pow (hv 0) _)
    (Ideal.pow_mem_pow (hv 1) _))

private theorem exists_transversal {k A : Type*} [Field k] [Infinite k] [CommRing A] [IsLocalRing A]
    [Algebra k A] (hres : Function.Surjective (algebraMap k (A ⧸ IsLocalRing.maximalIdeal A)))
    {x₀ t₀ f : A} {m : ℕ} (hm : span {x₀, t₀} = IsLocalRing.maximalIdeal A)
    (hf : f ∈ IsLocalRing.maximalIdeal A ^ m) (hf' : f ∉ IsLocalRing.maximalIdeal A ^ (m + 1)) :
    ∃ c : k, ∃ a g : A, IsUnit a ∧
      g ∈ span {x₀ - algebraMap k A c * t₀, t₀} ^ (m - 1) ∧
      f = a * t₀ ^ m + (x₀ - algebraMap k A c * t₀) * g := by
  set 𝔪 := IsLocalRing.maximalIdeal A
  set v : Fin 2 → A := ![x₀, t₀]
  have hv : span (Set.range v) = 𝔪 := by
    rw [← hm]; congr 1; ext z; simp [v, Matrix.range_cons, Set.mem_insert_iff, eq_comm, or_comm]
  obtain ⟨F, hF, hFf⟩ := exists_isHomogeneous_aeval_eq v m f (hv ▸ hf)
  set K := A ⧸ 𝔪
  let mk : A →+* K := Ideal.Quotient.mk 𝔪
  have hFbar : map mk F ≠ 0 := by
    intro h0
    refine hf' ?_
    rw [← hFf, pow_succ']
    refine aeval_mem_mul_pow_of_coeff_mem 𝔪 𝔪 v (fun i => ?_) hF (fun d => ?_)
    · rw [← hv]; exact Ideal.subset_span ⟨i, rfl⟩
    · have : (map mk F).coeff d = 0 := by
        rw [h0, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      rw [coeff_map] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hD : MMP.Resolution.dehomogenize K (1 : Fin 2) (map mk F) ≠ 0 := fun h =>
    hFbar (MMP.Resolution.eq_zero_of_isHomogeneous_of_dehomogenize_eq_zero (hF.map mk) h)
  have : Infinite K := Infinite.of_injective (algebraMap k K) (algebraMap k K).injective
  obtain ⟨z, hz⟩ : ∃ z : {i : Fin 2 // i ≠ 1} → K,
      eval z (MMP.Resolution.dehomogenize K (1 : Fin 2) (map mk F)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hD (MvPolynomial.funext fun z => by rw [hcon z, map_zero])
  obtain ⟨c, hc⟩ := hres (z ⟨0, by decide⟩)
  set a := aeval ![algebraMap k A c, 1] F
  have ha : IsUnit a := by
    by_contra hna
    have hmem : a ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal a).mpr hna
    apply hz
    have h1 : mk a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [← h1]
    change eval₂ (RingHom.id K) z (MMP.Resolution.dehomogenize K 1 (map mk F)) = _
    rw [MMP.Resolution.eval₂_dehomogenize, ← MvPolynomial.eval_map, MvPolynomial.map_id,
      MvPolynomial.eval_map]
    have hw : (fun i : Fin 2 => if h : i = 1 then (1 : K) else z ⟨i, h⟩) =
        mk ∘ ![algebraMap k A c, 1] := by
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, zero_ne_one, ↓reduceDIte, Function.comp_apply,
          Matrix.cons_val_zero]
        rw [← hc]; rfl
      · simp
    rw [hw]
    simp only [a, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, Algebra.algebraMap_self,
      RingHom.comp_id]
  set x := x₀ - algebraMap k A c * t₀
  have hxI : x ∈ span {x, t₀} := Ideal.subset_span (Set.mem_insert _ _)
  have htI : t₀ ∈ span {x, t₀} := Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have key := aeval_sub_mem_of_isHomogeneous (span {x, t₀}) hxI htI (c := algebraMap k A c) hF
  have hvx : ![x + algebraMap k A c * t₀, t₀] = v := by
    simp only [v, x, sub_add_cancel]
  rw [hvx, hFf] at key
  obtain ⟨g, hg, hfg⟩ := Ideal.mem_span_singleton_mul.mp key
  exact ⟨c, a, g, ha, hg, by linear_combination -hfg⟩

private theorem not_le_span_singleton_of_spanFinrank_eq_two {A : Type*} [CommRing A] [IsLocalRing A]
    (h2 : (IsLocalRing.maximalIdeal A).spanFinrank = 2) {u : A}
    (hu : u ∈ IsLocalRing.maximalIdeal A) (hle : IsLocalRing.maximalIdeal A ≤ span
        {u}) : False := by
  have heq : IsLocalRing.maximalIdeal A = span {u} :=
    le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr hu)
  have h1 : (span {u} : Ideal A).spanFinrank ≤ 1 := by
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Set.finite_singleton u)
  rw [← heq, h2] at h1
  omega

private theorem prime_and_notMem_of_span_pair_eq {A : Type*} [CommRing A] [IsRegularLocalRing A]
    (h2 : (IsLocalRing.maximalIdeal A).spanFinrank = 2) {x t : A}
    (hm : span {x, t} = IsLocalRing.maximalIdeal A) : Prime x ∧ t ∉ span {x} := by
  have hxm : x ∈ IsLocalRing.maximalIdeal A := hm ▸ Ideal.subset_span (Set.mem_insert _ _)
  have htm : t ∈ IsLocalRing.maximalIdeal A :=
    hm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx2 : x ∉ IsLocalRing.maximalIdeal A ^ 2 := by
    intro hx2
    refine not_le_span_singleton_of_spanFinrank_eq_two h2 htm ?_
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) ?_
    rw [Ideal.smul_eq_mul, ← pow_two]
    conv_lhs => rw [← hm, Ideal.span_insert]
    refine sup_le ?_ le_sup_left
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_right hx2
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Ideal.zero_mem _)
  refine ⟨IsRegularLocalRing.prime_of_isRegularLocalRing_quotient_span_singleton hx0
    (Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hxm hx2),
    fun ht => not_le_span_singleton_of_spanFinrank_eq_two h2 hxm ?_⟩
  rw [← hm, Ideal.span_le]
  rintro z (rfl | rfl)
  · exact Ideal.mem_span_singleton_self _
  · exact ht

private theorem iInf_eq_span_prod {A : Type*} [CommRing A] [IsDomain A] (π : Ideal A → A)
    (T : Finset (Ideal A)) (hπ : ∀ P ∈ T, Prime (π P)) (hT : ∀ P ∈ T, P = span {π P}) :
    (⨅ P ∈ T, P) = span {∏ P ∈ T, π P} := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert Q T hQ ih =>
    rw [Finset.iInf_insert, ih (fun P hP => hπ P (Finset.mem_insert_of_mem hP))
      (fun P hP => hT P (Finset.mem_insert_of_mem hP)), Finset.prod_insert hQ]
    have hπQ := hπ Q (Finset.mem_insert_self _ _)
    set q := π Q
    have hQq : Q = span {q} := hT Q (Finset.mem_insert_self _ _)
    rw [hQq]
    apply le_antisymm
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Submodule.mem_inf.mp ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha2
      have hdvd : q ∣ b * ∏ P ∈ T, π P := Ideal.mem_span_singleton.mp ha1
      rcases hπQ.dvd_or_dvd hdvd with ⟨c, rfl⟩ | h
      · exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
      · obtain ⟨P, hP, hQP⟩ := (hπQ.dvd_finsetProd_iff _).mp h
        have hassoc := hπQ.associated_of_dvd (hπ P (Finset.mem_insert_of_mem hP)) hQP
        have : Q = P := by
          rw [hQq, hT P (Finset.mem_insert_of_mem hP),
            Ideal.span_singleton_eq_span_singleton.mpr hassoc]
        exact absurd (this ▸ hP) hQ
    · rw [le_inf_iff, Ideal.span_singleton_le_span_singleton,
        Ideal.span_singleton_le_span_singleton]
      exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩

private theorem exists_eq_span_singleton_of_isRadical {A : Type*} [CommRing A] [IsRegularLocalRing
    A]
    (hdim : ringKrullDim A = 2) {I : Ideal A} (hrad : I.IsRadical) (hI0 : I ≠ ⊥)
    (hmin : ∀ P ∈ I.minimalPrimes, P ≠ IsLocalRing.maximalIdeal A) :
    ∃ f : A, I = span {f} := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : UniqueFactorizationMonoid A := IsRegularLocalRing.uniqueFactorizationMonoid A
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
  have hprinc : ∀ P ∈ I.minimalPrimes, ∃ p : A, Prime p ∧ P = span {p} := by
    intro P hP
    have hPp : P.IsPrime := hP.1.1
    have hIP : I ≤ P := hP.1.2
    have hP0 : P ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIP))
    have hlt : P < IsLocalRing.maximalIdeal A :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hPp.ne_top) (hmin P hP)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : (IsLocalRing.maximalIdeal A).height = 2 := by
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
      rw [hdim] at this
      exact WithBot.coe_injective this
    rw [h2] at h1
    have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    have hh : P.height = 1 := by
      have hle : P.height ≤ 1 := by
        have : P.height + 1 ≤ 1 + 1 := h1
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
      rcases (ENat.le_one_iff_eq_zero_or_eq_one).mp hle with h | h
      · exact absurd h h0
      · exact h
    obtain ⟨p, hp⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨p, ?_, hp⟩
    have hp0 : p ≠ 0 := by rintro rfl; exact hP0 (by rw [hp]; simp)
    rw [hp] at hPp
    exact (Ideal.span_singleton_prime hp0).mp hPp
  choose! π hπ hπspan using hprinc
  obtain ⟨T, hT⟩ : ∃ T : Finset (Ideal A), (T : Set (Ideal A)) = I.minimalPrimes :=
    ⟨hfin.toFinset, hfin.coe_toFinset⟩
  refine ⟨∏ P ∈ T, π P, ?_⟩
  have hI : I = sInf I.minimalPrimes := by rw [Ideal.sInf_minimalPrimes, hrad.radical]
  rw [← hT, sInf_eq_iInf] at hI
  simp only [Finset.mem_coe] at hI
  rw [hI]
  exact iInf_eq_span_prod π T (fun P hP => hπ P (hT ▸ hP)) (fun P hP => hπspan P (hT ▸ hP))

end Algebra

/-- The stalk map of a morphism on a germ of a global section pulled back from a base. -/
private theorem stalkMap_germ_top_appTop {X Y Z : Scheme.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (c : Γ(Z, ⊤)) :
    (f.stalkMap x).hom ((Y.presheaf.germ ⊤ (f x) trivial).hom (g.appTop.hom c)) =
      (X.presheaf.germ ⊤ x trivial).hom (((f ≫ g).appLE ⊤ ⊤ (by simp)).hom c) := by
  change (f.stalkMap x).hom ((Y.presheaf.germ ⊤ (f x) (show f x ∈ (⊤ : Y.Opens) from
    Set.mem_univ _)).hom (g.appTop.hom c)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  erw [Scheme.Hom.appLE_eq_app]
  rw [Scheme.Hom.comp_app]
  rfl

/-- Changing the first of two generators by a multiple of the second keeps the ideal. -/
private theorem span_pair_sub_mul {R : Type*} [CommRing R] (a b c : R) :
    Ideal.span {a - c * b, b} = Ideal.span {a, b} := by
  simpa [sub_eq_add_neg, mul_comm] using Ideal.span_pair_add_right_mul a b (-c)

/-- The order of the zero ideal is infinite. -/
private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    MMP.Resolution.idealOrder (⊥ : Ideal R) = ⊤ := by
  refine eq_top_iff.mpr (ENat.forall_natCast_le_iff_le.mp fun j _ => ?_)
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ IsLocalRing.maximalIdeal R ^ j) =>
    (j : ℕ∞)) j bot_le le_rfl

/-- A point of a closed subset all of whose irreducible components are curves has a proper
generalization: the maximal ideal of its local ring is not a minimal prime. -/
private theorem exists_isPrime_lt_maximalIdeal_stalk {Y : Scheme.{w}} (C : Closeds Y)
    (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    (x₀ : (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
    (hy : IsClosed ({(Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀} : Set Y)) :
    ∃ Q : Ideal ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀),
      Q.IsPrime ∧ Q < IsLocalRing.maximalIdeal _ := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι = (C : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hyC : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ ∈ (C : Set Y) :=
    hrange ▸ Set.mem_range_self x₀
  let s₀ : (C : Set Y) := ⟨_, hyC⟩
  obtain ⟨Z, hZ, hsZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {s₀}
    isIrreducible_singleton
  have hZ1 := hC Z hZ
  have hWirr : IsIrreducible (Subtype.val '' Z : Set Y) :=
    hZ.1.image _ continuous_subtype_val.continuousOn
  have hη := hWirr.isGenericPoint_genericPoint_closure
  set η := hWirr.genericPoint
  have hcl : closure (Subtype.val '' Z : Set Y) ⊆ (C : Set Y) :=
    closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) C.isClosed
  have hηx : η ⤳ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ :=
    hη.specializes (subset_closure ⟨s₀, hsZ rfl, rfl⟩)
  have hne : η ≠ (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ := by
    intro h
    have hclW : closure (Subtype.val '' Z : Set Y) = {((Scheme.IdealSheafData.vanishingIdeal
        C).subschemeι x₀)} := by
      rw [← hη.def, h, hy.closure_eq]
    have hZs : Z = {s₀} := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.mpr (hsZ rfl))
      have : (z : Y) ∈ closure (Subtype.val '' Z : Set Y) := subset_closure ⟨z, hz, rfl⟩
      rw [hclW] at this
      exact Subtype.ext this
    subst hZs
    haveI : Nonempty ({s₀} : Set (C : Set Y)) := ⟨⟨s₀, rfl⟩⟩
    haveI : Subsingleton ({s₀} : Set (C : Set Y)) :=
      ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    rw [AlgebraicGeometry.topologicalKrullDim_eq_zero_of_nonempty_subsingleton] at hZ1
    exact zero_ne_one hZ1
  obtain ⟨η', hη'⟩ : η ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι :=
    hrange ▸ hcl hη.mem
  have hsp : η' ⤳ x₀ := by
    rw [← (Scheme.IdealSheafData.vanishingIdeal
        C).subschemeι.isClosedEmbedding.isInducing.specializes_iff,
      hη']
    exact hηx
  obtain ⟨p, hp⟩ : η' ∈ Set.range ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.fromSpecStalk
      x₀) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  refine ⟨p.asIdeal, p.isPrime, lt_of_le_of_ne (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) ?_⟩
  intro hpm
  have hpc : p = IsLocalRing.closedPoint _ := PrimeSpectrum.ext hpm
  apply hne
  rw [← hη', ← hp, hpc, Scheme.fromSpecStalk_closedPoint]

/-- Coordinates at a closed point: an affine neighbourhood on which two sections generate the
ideal of the point over every affine open. -/
private theorem exists_generators_vanishingIdeal_singleton
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (hyU : y ∈ U) (x t : Γ(Y, U)),
      ∀ (V : Y.affineOpens) (h : V.1 ≤ U),
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal V =
          Ideal.span {(Y.presheaf.map (homOfLE h).op).hom x,
            (Y.presheaf.map (homOfLE h).op).hom t} := by
  classical
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hsb := MMP.Threefold.Resolution.isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := MMP.Threefold.Resolution.isIrreducible_support_vanishingIdeal_singleton hy
  have hsupp : (((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
      Closeds Y) : Set Y) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hc : ((2 : ℕ) : ℕ∞) = codimension (⟨(Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hy⟩ : Closeds Y)).support, hirr, (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ : IrreducibleCloseds Y) := by
    have heq : (⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support, hirr,
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support.isClosed⟩ :
          IrreducibleCloseds Y) = IrreducibleCloseds.closureSingleton y := by
      apply IrreducibleCloseds.ext
      change (((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).support :
        Closeds Y) : Set Y) = closure {y}
      rw [hsupp, hy.closure_eq]
    rw [heq,
      Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight,
      MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hY hYd hy]
    rfl
  obtain ⟨-, U, hU, hηU, n, x, -, hcut⟩ :=
    MMP.Threefold.Resolution.exists_isLocalCoordinates_genericPoint (sY := sY) (h := hsb)
      (hirr := hirr) (hc := hc)
  have key : ∀ z, (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).subschemeι z = y :=
    fun z => by
      have hmem := Set.mem_range_self (f :=
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).subschemeι) z
      rw [Scheme.IdealSheafData.range_subschemeι, hsupp] at hmem
      exact hmem
  have hyU : y ∈ U := key _ ▸ hηU
  let a : Γ(Y, U) := if h : 0 < n then x ⟨0, h⟩ else 0
  let b : Γ(Y, U) := if h : 1 < n then x ⟨1, h⟩ else 0
  refine ⟨U, hU, hyU, a, b, fun V h => ?_⟩
  rw [hcut V h]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < 2 := hi
    have hin := i.2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h0 | h1
    · have hn : 0 < n := by omega
      have hi0 : i = ⟨0, hn⟩ := Fin.ext (by simp; omega)
      refine Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inl ?_))
      simp only [a, dif_pos hn, hi0]
    · have hn : 1 < n := by omega
      have hi1 : i = ⟨1, hn⟩ := Fin.ext h1
      refine Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr ?_))
      simp only [b, dif_pos hn, hi1]
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · by_cases h0 : 0 < n
      · simp only [a, dif_pos h0]
        exact Ideal.subset_span ⟨⟨0, h0⟩, show (0 : ℕ) < 2 by omega, rfl⟩
      · simp only [a, dif_neg h0, map_zero]
        exact Ideal.zero_mem _
    · by_cases h1 : 1 < n
      · simp only [b, dif_pos h1]
        exact Ideal.subset_span ⟨⟨1, h1⟩, show (1 : ℕ) < 2 by omega, rfl⟩
      · simp only [b, dif_neg h1, map_zero]
        exact Ideal.zero_mem _

/-! ### The strict transform near the fibre -/

private theorem stalkLinearMap_cokernel_π_apply' {X : Scheme.{w}} {M N : X.Modules} (φ : M ⟶ N) (x
    : X)
    (z : N.presheaf.stalk x) :
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom
        (AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x z) =
      cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ) z := by
  change ConcreteCategory.hom ((Scheme.Modules.stalkFunctor X x).map (cokernel.π φ) ≫
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom) z = _
  exact congrArg (fun m : (Scheme.Modules.stalkFunctor X x).obj N ⟶
      cokernel ((Scheme.Modules.stalkFunctor X x).map φ) => ConcreteCategory.hom m z)
    (PreservesCokernel.π_iso_hom (Scheme.Modules.stalkFunctor X x) φ)

private theorem surjective_stalkLinearMap_cokernel_π' {X : Scheme.{w}} {M N : X.Modules} (φ : M ⟶ N)
    (x : X) :
    Function.Surjective (AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x) := by
  intro q
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ))).mp inferInstance
    ((PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom q)
  exact ⟨z, (ConcreteCategory.bijective_of_isIso
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom).1
    ((stalkLinearMap_cokernel_π_apply' φ x z).trans hz)⟩

private theorem ker_stalkLinearMap_cokernel_π' {X : Scheme.{w}} {M N : X.Modules} (φ : M ⟶ N) (x :
    X) :
    LinearMap.ker (AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x) =
      LinearMap.range (AlgebraicGeometry.stalkLinearMap M N φ x) := by
  ext z
  constructor
  · intro hz
    have h0 : cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ) z = 0 := by
      rw [← stalkLinearMap_cokernel_π_apply' φ x z, LinearMap.mem_ker.mp hz]
      exact map_zero _
    have hce := ShortComplex.cokernelSequence_exact ((Scheme.Modules.stalkFunctor X x).map φ)
    rw [ShortComplex.moduleCat_exact_iff] at hce
    exact hce z h0
  · rintro ⟨w, rfl⟩
    have h : cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ)
        (AlgebraicGeometry.stalkLinearMap M N φ x w) = 0 := by
      change ConcreteCategory.hom ((Scheme.Modules.stalkFunctor X x).map φ ≫
        cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ)) w = 0
      rw [cokernel.condition]
      rfl
    refine LinearMap.mem_ker.mpr ((ConcreteCategory.bijective_of_isIso
      (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom).1 ?_)
    rw [stalkLinearMap_cokernel_π_apply', h]
    exact (map_zero _).symm

/-- The stalk of `g_*𝒪_{X'}/𝒪_X` at `x` is the quotient of the stalk of `g_*𝒪_{X'}` as a ring by
the image of `𝒪_{X,x}`, for an affine morphism `g`. -/
private theorem nonempty_linearEquiv_stalk_cokernel {X' X : Scheme.{w}} (g : X' ⟶ X) [IsAffineHom g]
    (x : X) :
    Nonempty (OXModule.stalk (cokernel (Stacks.GlueSquishFactor.structureUnitHom g)) x ≃ₗ[
        X.presheaf.stalk x] (g.pushforwardStalk x) ⧸ LinearMap.range
          (Algebra.linearMap (X.presheaf.stalk x) (g.pushforwardStalk x))) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  let N : X.Modules := (Scheme.Modules.pushforward g).obj
    (SheafOfModules.unit.{w} X'.ringCatSheaf)
  haveI := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X'
  haveI : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom g _
  let _ : Algebra Γ(X, V) Γ(X', g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra Γ(X', g ⁻¹ᵁ V) (g.pushforwardStalk x) := (g.pushforwardGerm V x hxV).hom.toAlgebra
  let _ : Algebra Γ(X, V) (g.pushforwardStalk x) :=
    (g.app V ≫ g.pushforwardGerm V x hxV).hom.toAlgebra
  have _ : IsScalarTower Γ(X, V) Γ(X', g ⁻¹ᵁ V) (g.pushforwardStalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have _ : IsScalarTower Γ(X, V) (X.presheaf.stalk x) (g.pushforwardStalk x) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (g.app V ≫ g.pushforwardGerm V x hxV).hom r =
      (g.pushforwardStalkMap x).hom ((X.presheaf.germ V x hxV).hom r)
    rw [← CommRingCat.comp_apply, ← show _ ≫ g.pushforwardStalkMap x =
      g.app V ≫ g.pushforwardGerm V x hxV from TopCat.Presheaf.stalkFunctor_map_germ V x hxV g.c]
  have _ : IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let _ : Module (X.presheaf.stalk x) (N.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier N.val x
  let _ := affineStalkModule N V x hxV
  have _ : IsScalarTower Γ(X, V) (X.presheaf.stalk x) (N.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h₁ : IsLocalizedModule (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (affineGerm N V x hxV) := affineGerm_isLocalized N V hV x hxV
  have h₂ : IsLocalizedModule (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (IsScalarTower.toAlgHom Γ(X, V) Γ(X', g ⁻¹ᵁ V) (g.pushforwardStalk x)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr (g.isLocalization_pushforwardStalk hV hxV)
  let e := (@IsLocalizedModule.linearEquiv _ _ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    _ _ _ _ _ _ _ _ _ (affineGerm N V x hxV)
    (IsScalarTower.toAlgHom Γ(X, V) Γ(X', g ⁻¹ᵁ V) (g.pushforwardStalk
        x)).toLinearMap h₁ h₂).extendScalarsOfIsLocalization
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.presheaf.stalk x)
  set φ := Stacks.GlueSquishFactor.structureUnitHom g
  have e₁ := (LinearMap.quotKerEquivOfSurjective _ (surjective_stalkLinearMap_cokernel_π' φ x)).symm
  rw [ker_stalkLinearMap_cokernel_π'] at e₁
  -- every germ of `𝒪_X` is a multiple of the germ of `1`
  set u := (Stacks.GlueSquishFactor.unitModule X).presheaf.germ V x hxV
    (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from (1 : Γ(X, V))) with hu
  have hgen : ∀ w : (Stacks.GlueSquishFactor.unitModule X).presheaf.stalk x,
      ∃ r : X.presheaf.stalk x, w = r • u := by
    intro w
    obtain ⟨W, hxW, m, rfl⟩ := (Stacks.GlueSquishFactor.unitModule X).presheaf.exists_germ_eq w
    refine ⟨X.presheaf.germ W x hxW m, ?_⟩
    have hone : ∀ (U : X.Opens) (hU : x ∈ U), (Stacks.GlueSquishFactor.unitModule X).presheaf.germ
        U x hU (show Γ(Stacks.GlueSquishFactor.unitModule X, U) from (1 : Γ(X, U))) = u := by
      intro U hU
      have e1 := TopCat.Presheaf.germ_res_apply (Stacks.GlueSquishFactor.unitModule X).presheaf
        (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hU, hxV⟩
        (show Γ(Stacks.GlueSquishFactor.unitModule X, U) from (1 : Γ(X, U)))
      have e2 := TopCat.Presheaf.germ_res_apply (Stacks.GlueSquishFactor.unitModule X).presheaf
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hU, hxV⟩
        (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from (1 : Γ(X, V)))
      rw [← e1, hu, ← e2]
      congr 1
      exact (map_one (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom).trans
        (map_one (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom).symm
    have hsm := PresheafOfModules.germ_smul (M := (Stacks.GlueSquishFactor.unitModule X).val) x W
      hxW m (show Γ(Stacks.GlueSquishFactor.unitModule X, W) from (1 : Γ(X, W)))
    rw [← hone W hxW]
    refine Eq.trans ?_ hsm
    congr 1
    exact (mul_one (show Γ(X, W) from m)).symm
  have key : e (AlgebraicGeometry.stalkLinearMap _ _ φ x u) = 1 := by
    rw [hu, AlgebraicGeometry.stalkLinearMap_germ]
    have := @IsLocalizedModule.linearEquiv_apply _ _
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _ _ _ _ _ _ _ _ (affineGerm N V x hxV)
      (IsScalarTower.toAlgHom Γ(X, V) Γ(X', g ⁻¹ᵁ V) (g.pushforwardStalk x)).toLinearMap h₁ h₂
      (φ.val.app (Opposite.op V) (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from
        (1 : Γ(X, V))))
    refine Eq.trans (b := (IsScalarTower.toAlgHom Γ(X, V) Γ(X', g ⁻¹ᵁ V)
      (g.pushforwardStalk x)).toLinearMap (φ.val.app (Opposite.op V)
        (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from (1 : Γ(X, V))))) this ?_
    change (g.pushforwardGerm V x hxV).hom (φ.val.app (Opposite.op V)
      (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from (1 : Γ(X, V)))) = 1
    have hval : φ.val.app (Opposite.op V) (show Γ(Stacks.GlueSquishFactor.unitModule X, V) from
        (1 : Γ(X, V))) = (g.app V).hom 1 :=
      Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app _ (Opposite.op V) _
    rw [hval, map_one, map_one]
  have hsm : ∀ r : X.presheaf.stalk x,
      e (AlgebraicGeometry.stalkLinearMap _ _ φ x (r • u)) = algebraMap _ _ r := by
    intro r
    have h1 := (AlgebraicGeometry.stalkLinearMap _ _ φ x).map_smul r u
    have h2 := e.map_smul r (AlgebraicGeometry.stalkLinearMap _ _ φ x u)
    rw [h1]
    refine h2.trans ?_
    rw [key, Algebra.smul_def, mul_one]
  have hmap : (LinearMap.range (AlgebraicGeometry.stalkLinearMap _ _ φ x)).map
      (e : N.presheaf.stalk x →ₗ[X.presheaf.stalk x] g.pushforwardStalk x) =
      LinearMap.range (Algebra.linearMap (X.presheaf.stalk x) (g.pushforwardStalk x)) := by
    ext b
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨r, rfl⟩ := hgen w
      exact ⟨r, (hsm r).symm⟩
    · rintro ⟨r, rfl⟩
      exact ⟨AlgebraicGeometry.stalkLinearMap _ _ φ x (r • u), ⟨r • u, rfl⟩, hsm r⟩
  exact ⟨e₁.trans (Submodule.Quotient.equiv _ _ e hmap)⟩

/-- A point of `U` at which both generators of the ideal of `y` vanish is `y`. -/
private theorem eq_of_notMem_basicOpen {Y : Scheme.{w}} {y : Y} (hy : IsClosed ({y} : Set Y))
    {U : Y.Opens} (hU : IsAffineOpen U) {x t : Γ(Y, U)}
    (hxt : (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩ = Ideal.span {x, t})
    {z : Y} (hzU : z ∈ U) (hx : z ∉ Y.basicOpen x) (ht : z ∉ Y.basicOpen t) : z = y := by
  have hstalk := AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ
    (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) z ⟨U, hU⟩ hzU
  rw [hxt, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at hstalk
  have hne : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) z ≠ ⊤ := by
    rw [hstalk, ne_eq, Ideal.eq_top_iff_one]
    intro h1
    have hle : Ideal.span {(Y.presheaf.germ U z hzU).hom x, (Y.presheaf.germ U z hzU).hom t} ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.span_le]
      rintro w (rfl | rfl)
      · exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hx (by
          rw [Scheme.mem_basicOpen _ _ _ hzU]; exact hu)
      · exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ht (by
          rw [Scheme.mem_basicOpen _ _ _ hzU]; exact hu)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr (hle h1))
  rw [ne_eq, IdealSheafData.stalk_eq_top_iff_notMem_support, not_not, ← SetLike.mem_coe,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at hne
  exact hne

/-- On the chart `D₊(x)` of the blow-up of `I = (x, t)` over an affine `U`, the sections are
generated over `Γ(U)` by the fraction `t/x`. -/
private theorem adjoin_chartFraction_eq_top {Y : Scheme.{w}} (I : Y.IdealSheafData) (U :
    Y.affineOpens)
    {x t : Γ(Y, U.1)} (hI : I.ideal U = Ideal.span {x, t}) (hxI : x ∈ I.ideal U)
    (τ₀ : Γ(blowUp I, (blowUpChartOpen I U ⟨x, hxI⟩).1))
    (hτ₀ : (blowUpChartMap I U ⟨x, hxI⟩).hom t = (blowUpChartMap I U ⟨x, hxI⟩).hom x * τ₀) :
    letI := (blowUpChartMap I U ⟨x, hxI⟩).hom.toAlgebra
    Algebra.adjoin Γ(Y, U.1) {τ₀} = ⊤ := by
  letI := (blowUpChartMap I U ⟨x, hxI⟩).hom.toAlgebra
  set σ := (blowUpChartMap I U ⟨x, hxI⟩).hom
  have key : ∀ n : ℕ, ∀ z ∈ Ideal.span {x, t} ^ n, ∃ b ∈ Algebra.adjoin Γ(Y, U.1) {τ₀},
      σ x ^ n * b = σ z := by
    intro n
    induction n with
    | zero => intro z _; exact ⟨σ z, Subalgebra.algebraMap_mem _ z, by simp⟩
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro p hp q hq
        obtain ⟨b, hb, hbp⟩ := ih p hp
        obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hq
        refine ⟨b * (algebraMap _ _ α + algebraMap _ _ β * τ₀),
          Subalgebra.mul_mem _ hb (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
            (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
              (Algebra.subset_adjoin rfl))), ?_⟩
        change σ x ^ (n + 1) * (b * (σ α + σ β * τ₀)) = σ (p * (α * x + β * t))
        rw [map_mul, ← hbp, map_add, map_mul, map_mul, hτ₀]
        ring
      · rintro p q ⟨b₁, hb₁, h₁⟩ ⟨b₂, hb₂, h₂⟩
        exact ⟨b₁ + b₂, Subalgebra.add_mem _ hb₁ hb₂, by rw [mul_add, h₁, h₂, map_add]⟩
  refine eq_top_iff.mpr fun w _ => ?_
  obtain ⟨n, z, hz, hzw⟩ := exists_mem_pow_mul_eq_blowUpChartMap I U ⟨x, hxI⟩ w
  rw [hI] at hz
  obtain ⟨b, hb, hbz⟩ := key n z hz
  have hreg := blowUpChartMap_self_mem_nonZeroDivisors I U ⟨x, hxI⟩
  have hw : w = b := by
    have h1 : (σ x) ^ n * w = (σ x) ^ n * b := by rw [hbz, ← hzw, mul_comm]
    exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hreg n)).mp h1
  rw [hw]; exact hb

/-- An open subset of the strict transform lying over `y` is empty: the strict transform is the
closure of the part off the exceptional fibre. -/
private theorem eq_bot_of_forall_blowUpToBase_eq {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    (O : (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme.Opens)
    (hO : ∀ w ∈ O, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) = y) :
    O = ⊥ := by
  set iC' := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
  have hrange : Set.range iC' = closure (π.base ⁻¹' ((C : Set Y) \ {y})) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  by_contra hne
  obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty O).mp hne
  obtain ⟨O', hO', hOO'⟩ := iC'.isClosedEmbedding.isInducing.isOpen_iff.mp O.2
  have hwO' : iC' w ∈ O' := by
    have : w ∈ iC' ⁻¹' O' := by rw [hOO']; exact hw
    exact this
  have hcl : iC' w ∈ closure (π.base ⁻¹' ((C : Set Y) \ {y})) := hrange ▸ Set.mem_range_self w
  obtain ⟨p, hpO', hpT⟩ := mem_closure_iff.mp hcl O' hO' hwO'
  obtain ⟨w', rfl⟩ : p ∈ Set.range iC' := hrange ▸ subset_closure hpT
  have hw' : w' ∈ O := by
    have : w' ∈ iC' ⁻¹' O' := hpO'
    rw [hOO'] at this
    exact this
  exact hpT.2 (hO w' hw')

/-- On the strict transform, a section killed by two functions which vanish together only over
`y` is zero. -/
private theorem eq_zero_of_mul_eq_zero {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    {W : (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme.Opens}
    {s a b : Γ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme, W)}
    (hab : ∀ w ∈ W, w ∉ (Scheme.IdealSheafData.vanishingIdeal
      (strictTransformCloseds C hy)).subscheme.basicOpen a →
      w ∉ (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C
          hy)).subscheme.basicOpen b →
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
        ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) = y)
    (has : a * s = 0) (hbs : b * s = 0) : s = 0 := by
  haveI := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (strictTransformCloseds C hy)
  refine eq_zero_of_basicOpen_eq_bot s (eq_bot_of_forall_blowUpToBase_eq C hy _ fun w hw => ?_)
  have hwW : w ∈ W := Scheme.basicOpen_le _ s hw
  refine hab w hwW (fun ha => ?_) (fun hb => ?_)
  · have : w ∈ (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C
      hy)).subscheme.basicOpen
        (a * s) := by rw [Scheme.basicOpen_mul]; exact ⟨ha, hw⟩
    rw [has, Scheme.basicOpen_zero] at this
    exact this
  · have : w ∈ (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C
      hy)).subscheme.basicOpen
        (b * s) := by rw [Scheme.basicOpen_mul]; exact ⟨hb, hw⟩
    rw [hbs, Scheme.basicOpen_zero] at this
    exact this

private theorem appLE_app_map_eqToHom {X' X Y' Y : Scheme.{w}} (g : X' ⟶ X) (iC : X ⟶ Y) (iC' : X'
    ⟶ Y')
    (π : Y' ⟶ Y) (hg : g ≫ iC = iC' ≫ π) (U : Y.Opens) (O : Y'.Opens) (hO : O ≤ π ⁻¹ᵁ U)
    (hOV : g ⁻¹ᵁ (iC ⁻¹ᵁ U) = iC' ⁻¹ᵁ O) :
    π.appLE U O hO ≫ iC'.app O ≫ X'.presheaf.map (eqToHom hOV).op =
      iC.app U ≫ g.app (iC ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_app, Scheme.Hom.congr_app hg U, Scheme.Hom.comp_app, Scheme.Hom.appLE]
  simp only [Category.assoc, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

/-- **The core of the first-neighbourhood computation.** If the strict transform over `U` lies in
the chart `D₊(x)`, the stalk of `g_*𝒪_{C'}` at `x₀` is generated over `𝒪_{C,x₀}` by the image `τ`
of `t/x`, contains `𝒪_{C,x₀}`, and `x` is a nonzerodivisor on it. -/
private theorem stalk_pushforward_presentation {Y : Scheme.{w}} (C : Closeds Y)
    (x₀ : (Scheme.IdealSheafData.vanishingIdeal C).subscheme) {y : Y}
    (hy : IsClosed ({y} : Set Y))
    (hx₀ : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ = y)
    [IsAffineHom (strictTransformToCurve C hy)]
    (hginj : ∀ W, Function.Injective ((strictTransformToCurve C hy).app W).hom)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (hyU : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ ∈ U) (x t : Γ(Y, U))
    (hI : (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩ = Ideal.span {x, t})
    (hxI : x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩)
    (hcont : ∀ w, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) ∈ U →
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w ∈
        (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩
          ⟨x, hxI⟩).1) :
    Function.Injective (algebraMap ((Scheme.IdealSheafData.vanishingIdeal
        C).subscheme.presheaf.stalk
      x₀) ((strictTransformToCurve C hy).pushforwardStalk x₀)) ∧
    ∃ τ : (strictTransformToCurve C hy).pushforwardStalk x₀,
      algebraMap _ _ (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom
          (Y.presheaf.germ U _ hyU x)) * τ =
        algebraMap _ _ (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom
          (Y.presheaf.germ U _ hyU t)) ∧
      Algebra.adjoin ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) {τ} =
        ⊤ ∧
      IsLeftRegular (algebraMap ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk
        x₀) ((strictTransformToCurve C hy).pushforwardStalk x₀)
          (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom
            (Y.presheaf.germ U _ hyU x))) := by
  classical
  set g := strictTransformToCurve C hy with hgdef
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι with hiC
  set iC' := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι
    with hiC'
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) with hπ
  set O := blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩
    ⟨x, hxI⟩ with hO
  have hg : g ≫ iC = iC' ≫ π := strictTransformToCurve_subschemeι C hy
  have hV : IsAffineOpen (iC ⁻¹ᵁ U) := hU.preimage iC
  have hxV : x₀ ∈ iC ⁻¹ᵁ U := hyU
  have hOle : O.1 ≤ π ⁻¹ᵁ U := blowUpChartOpen_le _ _ _
  have hOV : g ⁻¹ᵁ (iC ⁻¹ᵁ U) = iC' ⁻¹ᵁ O.1 := by
    ext w
    have hw : iC (g w) = π (iC' w) := by
      rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
    constructor
    · intro h
      exact hcont w (hw ▸ h)
    · intro h
      change iC (g w) ∈ U
      rw [hw]
      exact hOle h
  -- the chart fraction `τ₀ = t/x` and the generation of the chart ring
  set σ := (blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩
    ⟨x, hxI⟩).hom with hσ
  have htI : t ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩ :=
    hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨τ₀, hτ₀⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow
    (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩ ⟨x, hxI⟩ (n := 1)
    (x := t) (by rw [pow_one]; exact htI)
  rw [pow_one] at hτ₀
  have hgen₀ := adjoin_chartFraction_eq_top _ ⟨U, hU⟩ hI hxI τ₀ hτ₀
  -- restriction to the strict transform
  let ρ : Γ(blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩), O.1) ⟶
      Γ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme,
        g ⁻¹ᵁ (iC ⁻¹ᵁ U)) :=
    iC'.app O.1 ≫ (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C
        hy)).subscheme.presheaf.map
      (eqToHom hOV).op
  have hρsurj : Function.Surjective ρ.hom := by
    have h1 := Scheme.IdealSheafData.subschemeι_app_surjective
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)) O
    have h2 : Function.Surjective ((Scheme.IdealSheafData.vanishingIdeal
        (strictTransformCloseds C hy)).subscheme.presheaf.map (eqToHom hOV).op).hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    exact h2.comp h1
  have hcompat : ∀ r : Γ(Y, U), ρ.hom (σ r) = (g.app (iC ⁻¹ᵁ U)).hom ((iC.app U).hom r) := by
    intro r
    exact congrArg (fun φ => φ.hom r) (appLE_app_map_eqToHom g iC iC' π hg U O.1 hOle hOV)
  -- the stalk of `g_*𝒪_{C'}` as a localization
  set R := (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀
  set B := g.pushforwardStalk x₀
  letI : Algebra Γ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme,
      g ⁻¹ᵁ (iC ⁻¹ᵁ U)) B := (g.pushforwardGerm (iC ⁻¹ᵁ U) x₀ hxV).hom.toAlgebra
  have hloc := g.isLocalization_pushforwardStalk hV hxV
  letI : Algebra Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, iC ⁻¹ᵁ U) R :=
    TopCat.Presheaf.algebra_section_stalk _ (⟨x₀, hxV⟩ : iC ⁻¹ᵁ U)
  have hRloc : IsLocalization (hV.primeIdealOf ⟨x₀, hxV⟩).asIdeal.primeCompl R :=
    hV.isLocalization_stalk ⟨x₀, hxV⟩
  have hPg : ∀ r, algebraMap R B ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.germ
      (iC ⁻¹ᵁ U) x₀ hxV r) = (g.pushforwardGerm (iC ⁻¹ᵁ U) x₀ hxV).hom
        ((g.app (iC ⁻¹ᵁ U)).hom r) := fun r =>
    congrArg (fun φ => φ.hom r) (show _ ≫ g.pushforwardStalkMap x₀ =
      g.app (iC ⁻¹ᵁ U) ≫ g.pushforwardGerm (iC ⁻¹ᵁ U) x₀ hxV from
        TopCat.Presheaf.stalkFunctor_map_germ (iC ⁻¹ᵁ U) x₀ hxV g.c)
  have hφg : ∀ r : Γ(Y, U), (iC.stalkMap x₀).hom (Y.presheaf.germ U _ hyU r) =
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.germ (iC ⁻¹ᵁ U) x₀ hxV
        ((iC.app U).hom r) := fun r => Scheme.Hom.germ_stalkMap_apply iC U x₀ hyU r
  let θ := (g.pushforwardGerm (iC ⁻¹ᵁ U) x₀ hxV).hom.comp ρ.hom
  have hθσ : ∀ r : Γ(Y, U), θ (σ r) = algebraMap R B ((iC.stalkMap x₀).hom
      (Y.presheaf.germ U _ hyU r)) := by
    intro r
    change (g.pushforwardGerm (iC ⁻¹ᵁ U) x₀ hxV).hom (ρ.hom (σ r)) = _
    rw [hcompat, hφg, hPg]
  refine ⟨?_, θ τ₀, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a₀, m₀⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hV.primeIdealOf ⟨x₀, hxV⟩).asIdeal.primeCompl r
    have h1 : algebraMap R B (algebraMap _ R a₀) = 0 := by
      rw [← IsLocalization.mk'_spec R a₀ m₀, map_mul, hr, zero_mul]
    have h2 : algebraMap _ B ((g.app (iC ⁻¹ᵁ U)).hom a₀) = 0 := (hPg a₀).symm.trans h1
    obtain ⟨⟨c, hc⟩, hca⟩ := (IsLocalization.map_eq_zero_iff
      ((hV.primeIdealOf ⟨x₀, hxV⟩).asIdeal.primeCompl.map (g.app (iC ⁻¹ᵁ U)).hom) B _).mp h2
    obtain ⟨c₀, hc₀, rfl⟩ := Submonoid.mem_map.mp hc
    have h3 : c₀ * a₀ = 0 := hginj _ (by rw [map_mul, map_zero]; exact hca)
    exact (IsLocalization.mk'_eq_zero_iff a₀ m₀).mpr ⟨⟨c₀, hc₀⟩, h3⟩
  · rw [← hθσ, ← hθσ, ← map_mul, hτ₀]
  · letI := (blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩
      ⟨x, hxI⟩).hom.toAlgebra
    refine eq_top_iff.mpr fun b hb => ?_
    clear hb
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective
      ((hV.primeIdealOf ⟨x₀, hxV⟩).asIdeal.primeCompl.map (g.app (iC ⁻¹ᵁ U)).hom) b
    obtain ⟨m₀, hm₀, hm₀eq⟩ := Submonoid.mem_map.mp m.2
    obtain ⟨w, rfl⟩ := hρsurj s
    have hθw : θ w ∈ Algebra.adjoin R {θ τ₀} := by
      have hw : w ∈ Algebra.adjoin Γ(Y, U) {τ₀} := by rw [hgen₀]; trivial
      induction hw using Algebra.adjoin_induction with
      | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact Algebra.subset_adjoin rfl
      | algebraMap r =>
        change θ (σ r) ∈ _
        rw [hθσ]
        exact Subalgebra.algebraMap_mem _ _
      | add a b _ _ ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
    set c := algebraMap R B (IsLocalization.mk' R
      (1 : Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, iC ⁻¹ᵁ U)) ⟨m₀, hm₀⟩)
    have hc : algebraMap _ B ((g.app (iC ⁻¹ᵁ U)).hom m₀) * c = 1 := by
      have e1 : algebraMap _ B ((g.app (iC ⁻¹ᵁ U)).hom m₀) =
          algebraMap R B (algebraMap _ R m₀) := (hPg m₀).symm
      rw [e1, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self,
        map_one]
    have hmk : IsLocalization.mk' B (ρ.hom w) m = θ w * c := by
      rw [IsLocalization.mk'_eq_iff_eq_mul, ← hm₀eq]
      change θ w = θ w * c * _
      rw [mul_assoc, mul_comm c, hc, mul_one]
    change IsLocalization.mk' B (ρ.hom w) m ∈ _
    rw [hmk]
    exact Subalgebra.mul_mem _ hθw (Subalgebra.algebraMap_mem _ _)
  · -- `x` is a nonzerodivisor on the sections of the strict transform
    have hreg₁ : ∀ s, ρ.hom (σ x) * s = 0 → s = 0 := by
      intro s hs
      have hbs : ρ.hom (σ t) * s = 0 := by
        rw [hτ₀, map_mul, mul_comm (ρ.hom (σ x)), mul_assoc, hs, mul_zero]
      refine eq_zero_of_mul_eq_zero C hy (fun w hw ha hb => ?_) hs hbs
      have hgw : iC (g w) ∈ U := hw
      have key : ∀ r : Γ(Y, U), w ∉ (Scheme.IdealSheafData.vanishingIdeal
          (strictTransformCloseds C hy)).subscheme.basicOpen (ρ.hom (σ r)) →
          iC (g w) ∉ Y.basicOpen r := fun r hr hmem =>
        hr (by rwa [hcompat, ← Scheme.preimage_basicOpen, ← Scheme.preimage_basicOpen])
      have := eq_of_notMem_basicOpen hy hU hI hgw (key x ha) (key t hb)
      have hw' : π (iC' w) = iC (g w) := by
        rw [← Scheme.Hom.comp_apply, ← hg, Scheme.Hom.comp_apply]
      exact hw'.trans this
    rw [← hθσ x]
    intro b₁ b₂ hb
    have hb0 : θ (σ x) * (b₁ - b₂) = 0 := by
      change θ (σ x) * b₁ = θ (σ x) * b₂ at hb
      rw [mul_sub, hb, sub_self]
    rw [← sub_eq_zero]
    obtain ⟨⟨s, m⟩, hsm⟩ := IsLocalization.mk'_surjective
      ((hV.primeIdealOf ⟨x₀, hxV⟩).asIdeal.primeCompl.map (g.app (iC ⁻¹ᵁ U)).hom) (b₁ - b₂)
    change IsLocalization.mk' B s m = _ at hsm
    rw [← hsm] at hb0 ⊢
    have h4 : IsLocalization.mk' B (ρ.hom (σ x) * s) m = 0 := by
      rw [← hb0, IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one s, map_mul,
        mul_assoc]
      rfl
    obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ m).mp h4
    have h5 : (c : Γ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme,
        g ⁻¹ᵁ (iC ⁻¹ᵁ U))) * s = 0 :=
      hreg₁ _ (by rw [mul_left_comm]; exact hc)
    exact (IsLocalization.mk'_eq_zero_iff s m).mpr ⟨c, h5⟩

/-- A section of the reduced ideal of a closed set vanishes at its points. -/
private theorem notMem_basicOpen_of_mem_vanishingIdeal {Y : Scheme.{w}} (Z : Closeds Y) {U :
    Y.Opens}
    (hU : IsAffineOpen U) {s : Γ(Y, U)}
    (hs : s ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hU⟩) {z : Y} (hzZ : z ∈ Z)
    (hzU : z ∈ U) : z ∉ Y.basicOpen s := by
  intro hz
  have h1 := AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ
    (Scheme.IdealSheafData.vanishingIdeal Z) z ⟨U, hU⟩ hzU
  have hmem : (Y.presheaf.germ U z hzU).hom s ∈
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) z := by
    rw [h1]; exact Ideal.mem_map_of_mem _ hs
  have hne : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) z ≠ ⊤ := by
    rw [ne_eq, IdealSheafData.stalk_eq_top_iff_notMem_support, not_not, ← SetLike.mem_coe,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hzZ
  rw [Scheme.mem_basicOpen _ _ _ hzU] at hz
  exact hne (Ideal.eq_top_of_isUnit_mem _ hmem hz)

/-- Off the exceptional divisor, the denominator of a chart is invertible. -/
private theorem mem_basicOpen_blowUpChartMap {Y : Scheme.{w}} (I : Y.IdealSheafData) (U :
    Y.affineOpens)
    (a : I.ideal U) {p : blowUp I} (hp : p ∈ (blowUpChartOpen I U a).1)
    (hpI : blowUpToBase I p ∉ I.support) :
    p ∈ (blowUp I).basicOpen ((blowUpChartMap I U a).hom (a : Γ(Y, U.1))) := by
  have hpU : blowUpToBase I p ∈ U.1 := blowUpChartOpen_le I U a hp
  have h1 := (mem_blowUpChartOpen_iff I U a p hpU).mp hp
  have h2 : IdealSheafData.stalk (exceptionalIdeal I) p = ⊤ := by
    rw [IdealSheafData.stalk_eq_top_iff_notMem_support]
    change p ∉ (I.comap (blowUpToBase I)).support
    rw [Scheme.IdealSheafData.support_comap]
    exact hpI
  rw [h1, Ideal.span_singleton_eq_top] at h2
  rw [Scheme.mem_basicOpen _ _ _ hp, germ_blowUpChartMap]
  exact h2

/-- **Transversality.** If `f = a tᵐ + x g` is an equation of `C` on `U` with `a` a unit, then
every point of the strict transform over `y` lies on the chart `D₊(x)`. -/
private theorem mem_blowUpChartOpen_of_blowUpToBase_eq {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (U : Y.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U)
    {x t : Γ(Y, U)}
    (hI : (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩ = Ideal.span {x, t})
    (hxI : x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩).ideal ⟨U, hU⟩)
    {m : ℕ} (hm1 : 1 ≤ m) {F a G : Γ(Y, U)}
    (hF : F ∈ (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩)
    (hrel : F = a * t ^ m + x * G) (ha : IsUnit a) (hG : G ∈ Ideal.span {x, t} ^ (m - 1))
    (w : (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme)
    (hw : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) = y) :
    (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w ∈
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ⟨U, hU⟩ ⟨x, hxI⟩).1 := by
  classical
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) with hIdef
  set π := blowUpToBase I with hπ
  set q := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w
  have hsupp : ((I.support : Closeds Y) : Set Y) = {y} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have htI : t ∈ I.ideal ⟨U, hU⟩ := hI ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hyU' : π q ∈ U := hw ▸ hyU
  -- the two charts cover the preimage of `U`
  have hcover := iSup_blowUpChartOpen I ⟨U, hU⟩ {⟨x, hxI⟩, ⟨t, htI⟩}
    (Finset.insert_nonempty _ _) (by
    rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    exact hI.symm)
  have hqU : q ∈ π ⁻¹ᵁ U := hyU'
  rw [← hcover] at hqU
  simp only [Opens.mem_iSup, Finset.mem_insert, Finset.mem_singleton] at hqU
  obtain ⟨b, hb, hqb⟩ := hqU
  rcases hb with rfl | rfl
  · exact hqb
  by_contra hqx
  set Ot := blowUpChartOpen I ⟨U, hU⟩ ⟨t, htI⟩
  set σt := (blowUpChartMap I ⟨U, hU⟩ ⟨t, htI⟩).hom
  obtain ⟨ρx, hρx⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow I ⟨U, hU⟩ ⟨t, htI⟩ (n := 1)
    (x := x) (by rw [pow_one]; exact hxI)
  obtain ⟨G₂, hG₂⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow I ⟨U, hU⟩ ⟨t, htI⟩ (n := m - 1)
    (x := G) (by rw [hI]; exact hG)
  rw [pow_one] at hρx
  set f₂ := σt a + ρx * G₂
  have hFf : σt F = σt t ^ m * f₂ := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [hrel, map_add, map_mul, map_mul, map_pow, hρx, hG₂]
    simp only [f₂, Nat.add_sub_cancel]
    ring
  -- the chart fraction `x/t` vanishes at `q`
  have hρq : ¬ IsUnit ((blowUp I).presheaf.germ Ot.1 q hqb ρx) := by
    intro hu
    apply hqx
    rw [mem_blowUpChartOpen_iff I _ _ q hyU']
    rw [(mem_blowUpChartOpen_iff I _ _ q hyU').mp hqb]
    have h1 := congrArg ((blowUp I).presheaf.germ Ot.1 q hqb).hom hρx
    rw [map_mul, germ_blowUpChartMap, germ_blowUpChartMap] at h1
    change _ = Ideal.span {(((blowUpToBase I).stalkMap q).hom
      ((Y.presheaf.germ U (π q) hyU').hom x))}
    rw [h1]
    exact (Ideal.span_singleton_mul_right_unit hu _).symm
  -- the residual equation `f₂` is a unit at `q`
  have hf₂q : q ∈ (blowUp I).basicOpen f₂ := by
    rw [Scheme.mem_basicOpen _ _ _ hqb]
    have hau : IsUnit ((blowUp I).presheaf.germ Ot.1 q hqb (σt a)) :=
      (ha.map σt).map _
    have hm : (blowUp I).presheaf.germ Ot.1 q hqb (ρx * G₂) ∈ IsLocalRing.maximalIdeal _ := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hρq)
    by_contra hnu
    have hsum : (blowUp I).presheaf.germ Ot.1 q hqb f₂ ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : (blowUp I).presheaf.germ Ot.1 q hqb (σt a) ∈ IsLocalRing.maximalIdeal _ := by
      simpa only [f₂, map_add, add_sub_cancel_right] using Ideal.sub_mem _ hsum hm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hau
  -- `q` is in the closure of the part of `π⁻¹ C` off the fibre
  have hqcl : q ∈ closure (π.base ⁻¹' ((C : Set Y) \ {y})) := by
    have := Set.mem_range_self (f := (Scheme.IdealSheafData.vanishingIdeal
      (strictTransformCloseds C hy)).subschemeι) w
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  obtain ⟨p, hpW, hpT⟩ := mem_closure_iff.mp hqcl _ ((blowUp I).basicOpen f₂).isOpen hf₂q
  have hpOt : p ∈ Ot.1 := (blowUp I).basicOpen_le f₂ hpW
  have hpU : π p ∈ U := blowUpChartOpen_le I _ _ hpOt
  have hFp : π p ∉ Y.basicOpen F :=
    notMem_basicOpen_of_mem_vanishingIdeal C hU hF hpT.1 hpU
  have hpF : p ∉ (blowUp I).basicOpen (σt F) := by
    intro h
    apply hFp
    rw [Scheme.mem_basicOpen _ _ _ hpOt, germ_blowUpChartMap] at h
    rw [Scheme.mem_basicOpen _ _ _ hpU]
    exact (isUnit_map_iff _ _).mp h
  rw [hFf, Scheme.basicOpen_mul] at hpF
  have hpt : p ∉ (blowUp I).basicOpen (σt t) := by
    intro h
    refine hpF ⟨?_, hpW⟩
    have hpow : ∀ n : ℕ, p ∈ (blowUp I).basicOpen (σt t ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero, Scheme.basicOpen_one]; exact hpOt
      | succ n ih => rw [pow_succ, Scheme.basicOpen_mul]; exact ⟨ih, h⟩
    exact hpow m
  refine hpt (mem_basicOpen_blowUpChartMap I ⟨U, hU⟩ ⟨t, htI⟩ hpOt ?_)
  rw [← SetLike.mem_coe, hsupp]
  exact hpT.2

/-- **Shrinking to the chart.** If the fibre of the strict transform over `y` lies in an open
`O` and `g : C' ⟶ C` is a closed map, there is a basic open `D(s) ∋ y` of `U` such that the whole
strict transform over `D(s)` lies in `O`. -/
private theorem exists_basicOpen_forall_mem {Y : Scheme.{w}} (C : Closeds Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) (hgc : IsClosedMap (strictTransformToCurve C hy))
    (U : Y.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U)
    (O : (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).Opens)
    (hO : ∀ w, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
      ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) = y →
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w ∈ O) :
    ∃ s : Γ(Y, U), y ∈ Y.basicOpen s ∧ ∀ w,
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
        ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) ∈
          Y.basicOpen s →
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w ∈ O := by
  set g := strictTransformToCurve C hy
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  set iC' := (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)
  have hg : g ≫ iC = iC' ≫ π := strictTransformToCurve_subschemeι C hy
  have hgw : ∀ w, iC (g w) = π (iC' w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  set Z' : Set _ := (iC' ⁻¹' (O : Set _))ᶜ
  have hZ' : IsClosed Z' := (O.isOpen.preimage iC'.continuous).isClosed_compl
  set K : Set Y := iC '' (g '' Z')
  have hK : IsClosed K := iC.isClosedEmbedding.isClosedMap _ (hgc _ hZ')
  have hyK : y ∉ K := by
    rintro ⟨_, ⟨w, hwZ, rfl⟩, hw⟩
    exact hwZ (hO w ((hgw w).symm.trans hw))
  obtain ⟨s, hsle, hys⟩ := hU.exists_basicOpen_le (V := U ⊓ ⟨Kᶜ, hK.isOpen_compl⟩)
    ⟨y, hyU, hyK⟩ hyU
  refine ⟨s, hys, fun w hw => ?_⟩
  by_contra hwO
  have := (hsle hw).2
  exact this ⟨g w, ⟨w, hwO, rfl⟩, hgw w⟩

/-- **Spreading out the local equation.** A stalk relation `f = a tᵐ + x g` between a generator
`f` of the ideal of `C`, a unit `a` and `g ∈ (x, t)^{m-1}` holds, after clearing denominators, as
an equation of sections on a basic open neighbourhood of `y`. -/
private theorem exists_basicOpen_equation {Y : Scheme.{w}} (C : Closeds Y) {y : Y} {U : Y.Opens}
    (hU : IsAffineOpen U) (hyU : y ∈ U) (x t : Γ(Y, U)) {m : ℕ}
    (f a g : Y.presheaf.stalk y)
    (hf : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C) y = Ideal.span {f})
    (hfa : f = a * Y.presheaf.germ U y hyU t ^ m + Y.presheaf.germ U y hyU x * g)
    (ha : IsUnit a)
    (hg : g ∈ Ideal.span {Y.presheaf.germ U y hyU x, Y.presheaf.germ U y hyU t} ^ (m - 1)) :
    ∃ r : Γ(Y, U), y ∈ Y.basicOpen r ∧ ∃ F A G : Γ(Y, U),
      F ∈ (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩ ∧
      G ∈ Ideal.span {x, t} ^ (m - 1) ∧
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom F =
        (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom (A * t ^ m + x * G) ∧
      IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom A) := by
  classical
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyU⟩ : U)
  set P := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  have hloc : IsLocalization P.primeCompl (Y.presheaf.stalk y) := hU.isLocalization_stalk ⟨y, hyU⟩
  have hgerm : ∀ r : Γ(Y, U), algebraMap Γ(Y, U) (Y.presheaf.stalk y) r =
      Y.presheaf.germ U y hyU r := fun _ => rfl
  -- clear the denominators of `f`, `g` and `a`
  have hfmem : f ∈ ((Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U, hU⟩).map
      (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) := by
    have h1 := AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ
      (Scheme.IdealSheafData.vanishingIdeal C) y ⟨U, hU⟩ hyU
    rw [hf] at h1
    change f ∈ Ideal.map (Y.presheaf.germ U y hyU).hom _
    rw [← h1]
    exact Ideal.mem_span_singleton_self f
  obtain ⟨⟨⟨F₀, hF₀⟩, ⟨s, hs⟩⟩, hFs⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp
    hfmem
  have hgmem : g ∈ (Ideal.span {x, t} ^ (m - 1)).map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) := by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    exact hg
  obtain ⟨⟨⟨g₀, hg₀⟩, ⟨sg, hsg⟩⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp
    hgmem
  obtain ⟨⟨a₀, ⟨sa, hsa⟩⟩, has⟩ := IsLocalization.mk'_surjective P.primeCompl a
  change IsLocalization.mk' _ a₀ ⟨sa, hsa⟩ = a at has
  have haa : a * algebraMap _ _ sa = algebraMap _ _ a₀ := by
    rw [← has, IsLocalization.mk'_spec]
  have ha₀ : a₀ ∈ P.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) P, ← haa]
    exact ha.mul ((IsLocalization.AtPrime.isUnit_to_map_iff _ P sa).mpr hsa)
  -- the relation, multiplied out
  have hrel : algebraMap Γ(Y, U) (Y.presheaf.stalk y) (F₀ * sa * sg) =
      algebraMap Γ(Y, U) (Y.presheaf.stalk y) (a₀ * s * sg * t ^ m + x * (s * sa * g₀)) := by
    simp only [hgerm] at hFs haa hgs ⊢
    simp only [map_mul, map_add, map_pow]
    rw [← hFs, ← haa, ← hgs, hfa]
    ring
  obtain ⟨⟨c, hc⟩, hcrel⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hrel
  set r := c * s * sa * sg * a₀
  have hr : r ∈ P.primeCompl :=
    P.primeCompl.mul_mem (P.primeCompl.mul_mem (P.primeCompl.mul_mem
      (P.primeCompl.mul_mem hc hs) hsa) hsg) ha₀
  have hyr : y ∈ Y.basicOpen r := by
    rw [Scheme.mem_basicOpen _ _ _ hyU, ← hgerm]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ P r).mpr hr
  set res := (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom
  have hru : IsUnit (res r) := Y.toRingedSpace.isUnit_res_basicOpen r
  have hfac : ∀ z w : Γ(Y, U), r = z * w → IsUnit (res z) := fun z w h =>
    isUnit_of_mul_isUnit_left (by rw [← map_mul, ← h]; exact hru)
  refine ⟨r, hyr, F₀ * sa * sg, a₀ * s * sg, s * sa * g₀,
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hF₀),
    Ideal.mul_mem_left _ _ hg₀, ?_, ?_⟩
  · have hcu : IsUnit (res c) := hfac c (s * sa * sg * a₀) (by simp only [r]; ring)
    have h1 : res (c * (F₀ * sa * sg)) =
        res (c * (a₀ * s * sg * t ^ m + x * (s * sa * g₀))) := congrArg res hcrel
    rw [map_mul res c, map_mul res c] at h1
    exact hcu.mul_left_cancel h1
  · exact hfac _ (c * sa) (by simp only [r]; ring)

/-- **The first neighbourhood ring.** With coordinates `x, t` at `y` on an affine `U` and a local
equation `f = a tᵐ + x g` of `C` at `y`, `a` a unit, the stalk at `x₀` of `g_*𝒪_{C'}/𝒪_C` is the
quotient `B/𝒪_{C,x₀}` of an `𝒪_{C,x₀}`-algebra `B ⊇ 𝒪_{C,x₀}` generated by one element `τ` with
`x τ = t`, on which `x` is a nonzerodivisor. -/
private theorem exists_presentation_stalk_cokernel
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    (x₀ : (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
    (hy : IsClosed ({(Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀} : Set Y))
    {m : ℕ} (hm1 : 1 ≤ m) (U : Y.Opens) (hU : IsAffineOpen U)
    (hyU : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ ∈ U) (x t : Γ(Y, U))
    (hxt : ∀ (V : Y.affineOpens) (h : V.1 ≤ U),
      (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩).ideal V =
        Ideal.span {(Y.presheaf.map (homOfLE h).op).hom x, (Y.presheaf.map (homOfLE h).op).hom t})
    (f a g : Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀))
    (hf : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C)
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀) = Ideal.span {f})
    (hfa : f = a * Y.presheaf.germ U _ hyU t ^ m + Y.presheaf.germ U _ hyU x * g)
    (ha : IsUnit a)
    (hg : g ∈ Ideal.span {Y.presheaf.germ U _ hyU x, Y.presheaf.germ U _ hyU t} ^ (m - 1)) :
    ∃ (B : Type w) (_ : CommRing B)
      (_ : Algebra ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B),
      Function.Injective (algebraMap
        ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B) ∧
      ∃ τ : B, algebraMap _ B (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap
          x₀).hom (Y.presheaf.germ U _ hyU x)) * τ =
        algebraMap _ B (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom
          (Y.presheaf.germ U _ hyU t)) ∧
      Algebra.adjoin ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) {τ} =
        ⊤ ∧
      IsLeftRegular (algebraMap _ B (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap
          x₀).hom (Y.presheaf.germ U _ hyU x))) ∧
      Nonempty (OXModule.stalk
        (cokernel (Stacks.GlueSquishFactor.structureUnitHom (strictTransformToCurve C hy))) x₀ ≃ₗ[
          (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀]
        B ⧸ LinearMap.range (Algebra.linearMap
          ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B)) := by
  classical
  have hyC : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ ∈ C := by
    have := Set.mem_range_self (f := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι) x₀
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  haveI : IsFinite (strictTransformToCurve C hy) :=
    isFinite_strictTransformToCurve hY hYs hYd C hC hy hyC
  have hgc : IsClosedMap (strictTransformToCurve C hy) := by
    haveI := isProper_strictTransformToCurve hY C hy
    exact (strictTransformToCurve C hy).isClosedMap
  have hginj := injective_app_strictTransformToCurve C hC hy
  -- spread the local equation to a basic open `U₁`
  obtain ⟨r₁, hyr₁, F, A, G, hF, hG, hrel, hA⟩ :=
    exists_basicOpen_equation C hU hyU x t f a g hf hfa ha hg
  set U₁ := Y.basicOpen r₁ with hU₁def
  have hU₁ : IsAffineOpen U₁ := hU.basicOpen r₁
  have hU₁U : U₁ ≤ U := Y.basicOpen_le r₁
  set res₁ := (Y.presheaf.map (homOfLE hU₁U).op).hom
  have hI₁ := hxt ⟨U₁, hU₁⟩ hU₁U
  have hxI₁ : res₁ x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩).ideal ⟨U₁, hU₁⟩ :=
    hI₁ ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hF₁ : res₁ F ∈ (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨U₁, hU₁⟩ := by
    have := ((Scheme.IdealSheafData.vanishingIdeal C).map_ideal_basicOpen ⟨U, hU⟩ r₁).le
      (Ideal.mem_map_of_mem _ hF)
    exact this
  have hrel₁ : res₁ F = res₁ A * res₁ t ^ m + res₁ x * res₁ G := by
    rw [hrel, map_add, map_mul, map_mul, map_pow]
  have hG₁ : res₁ G ∈ Ideal.span {res₁ x, res₁ t} ^ (m - 1) := by
    have := Ideal.mem_map_of_mem res₁ hG
    rwa [Ideal.map_pow, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at this
  -- transversality and shrinking to `U₂ ⊆ U₁`
  have htrans := mem_blowUpChartOpen_of_blowUpToBase_eq C hy U₁ hU₁ hyr₁ hI₁ hxI₁ hm1 hF₁ hrel₁
    hA hG₁
  obtain ⟨r₂, hyr₂, hcont₂⟩ := exists_basicOpen_forall_mem C hy hgc U₁ hU₁ hyr₁ _ htrans
  set U₂ := Y.basicOpen r₂ with hU₂def
  have hU₂ : IsAffineOpen U₂ := hU₁.basicOpen r₂
  have hU₂U₁ : U₂ ≤ U₁ := Y.basicOpen_le r₂
  have hU₂U : U₂ ≤ U := hU₂U₁.trans hU₁U
  have hI₂ := hxt ⟨U₂, hU₂⟩ hU₂U
  have hxI₂ : (Y.presheaf.map (homOfLE hU₂U).op).hom x ∈
      (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩).ideal ⟨U₂, hU₂⟩ :=
    hI₂ ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hres₂ : (Y.presheaf.map (homOfLE hU₂U).op).hom x =
      (Y.presheaf.map (homOfLE hU₂U₁).op).hom (res₁ x) := by
    change _ = ((Y.presheaf.map (homOfLE hU₁U).op) ≫ (Y.presheaf.map (homOfLE hU₂U₁).op)).hom x
    rw [← Y.presheaf.map_comp]
    rfl
  have hcont : ∀ w, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩)
      ((Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w) ∈ U₂ →
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subschemeι w ∈
        (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩) ⟨U₂, hU₂⟩
          ⟨_, hxI₂⟩).1 := by
    intro w hw
    have e := MMP.Flips.ResolutionInputs.blowUpChartOpen_restrict
      (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩) (V := ⟨U₂, hU₂⟩) (W := ⟨U₁, hU₁⟩) hU₂U₁
      ⟨res₁ x, hxI₁⟩ (hres₂ ▸ hxI₂)
    have hsub : (⟨(Y.presheaf.map (homOfLE hU₂U).op).hom x, hxI₂⟩ :
        (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩).ideal ⟨U₂, hU₂⟩) =
        ⟨(Y.presheaf.map (homOfLE hU₂U₁).op).hom (res₁ x), hres₂ ▸ hxI₂⟩ := Subtype.ext hres₂
    rw [hsub, e]
    exact ⟨hcont₂ w hw, hw⟩
  obtain ⟨hinj, τ, hτ, hgen, hreg⟩ := stalk_pushforward_presentation C x₀ hy rfl hginj U₂ hU₂
    hyr₂ _ _ hI₂ hxI₂ hcont
  have hgerm : ∀ z : Γ(Y, U), Y.presheaf.germ U₂ _ hyr₂ ((Y.presheaf.map (homOfLE hU₂U).op).hom z) =
      Y.presheaf.germ U _ hyU z := fun z =>
    TopCat.Presheaf.germ_res_apply _ (homOfLE hU₂U) _ hyr₂ z
  rw [hgerm, hgerm] at hτ
  rw [hgerm] at hreg
  obtain ⟨e⟩ := nonempty_linearEquiv_stalk_cokernel (strictTransformToCurve C hy) x₀
  exact ⟨_, inferInstance, inferInstance, hinj, τ, hτ, hgen, hreg, ⟨e⟩⟩

/-- **(d')** The `k`-dimension of the stalk of `g_*𝒪_{C'}/𝒪_C` at the point `x₀` over `y` is
`∑_{j<m} j`. -/
private theorem finrank_stalk_cokernel_strictTransformToCurve
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)]
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ C) {m : ℕ}
    (hm : MMP.Resolution.multAt (Scheme.IdealSheafData.vanishingIdeal C) y = m)
    (x₀ : (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
    (hx₀ : (Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀ = y) :
    Module.finrank k ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.germ ⊤ x₀ trivial).hom).obj
      (OXModule.stalk
        (cokernel (Stacks.GlueSquishFactor.structureUnitHom (strictTransformToCurve C hy)))
        x₀)) = ∑ j ∈ Finset.range m, j := by
  classical
  subst hx₀
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hsm : Smooth sY := MMP.Resolution.Aux.smooth_of_isSmoothScheme' sY hYs
  letI : Algebra k (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀)) :=
    MMP.Mori.stalkAlgebra sY ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀)
  haveI : IsRegularLocalRing (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
      x₀)) := isRegularLocalRing_stalk_of_smooth_over_field sY _
  have : IsDomain (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
      x₀)) := IsRegularLocalRing.isDomain (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
          C).subschemeι x₀))
  have hdimA : ringKrullDim (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
      x₀)) = 2 := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hY hYd _ hy
  have h2 := MMP.Mori.SurfaceAux.spanFinrank_eq_two_of_ringKrullDim hdimA
  have hres := MMP.Mori.SurfaceAux.residue_surjective sY
    ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀) hy
  -- the local ring of `C` at `x₀`
  let ψ : k →+* (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀ :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY).appLE ⊤ ⊤ (by simp) ≫
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.germ ⊤ x₀ trivial).hom
  letI : Algebra k ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) :=
    ψ.toAlgebra
  let φ : (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
      x₀)) →ₐ[k] (Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀ :=
    { toRingHom := ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom
      commutes' := fun c => stalkMap_germ_top_appTop _ sY x₀ _ }
  have hφ : Function.Surjective φ :=
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap_surjective x₀
  have hker : RingHom.ker φ = IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C)
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀) :=
    Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk _ x₀
  set Iy := IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal C)
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀) with hIy
  -- the ideal of `C` at `y` is principal, generated by an element of order `m`
  have hord : MMP.Resolution.idealOrder Iy = m := by
    unfold MMP.Resolution.multAt at hm; exact hm
  have hI0 : Iy ≠ ⊥ := by
    intro h
    rw [h, idealOrder_bot] at hord
    exact ENat.top_ne_coe m hord
  have hmin : ∀ P ∈ Iy.minimalPrimes, P ≠ IsLocalRing.maximalIdeal (Y.presheaf.stalk
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀)) := by
    rintro P hP rfl
    obtain ⟨Q, hQ, hQlt⟩ := exists_isPrime_lt_maximalIdeal_stalk C hC x₀ hy
    have hQ' : (Q.comap (φ : (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
        x₀)) →+* _)).IsPrime := Ideal.comap_isPrime _ _
    have hle : Iy ≤ Q.comap (φ : (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
        C).subschemeι x₀)) →+* _) := by
      rw [← hker]
      intro z hz
      have h0 : φ z = 0 := RingHom.mem_ker.mp hz
      simp [Ideal.mem_comap, h0]
    have hmQ := hP.2 ⟨hQ', hle⟩ (IsLocalRing.le_maximalIdeal hQ'.ne_top)
    obtain ⟨z, hzm, hzQ⟩ := SetLike.exists_of_lt hQlt
    obtain ⟨w, rfl⟩ := hφ z
    have hw : w ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
        C).subschemeι x₀)) := by
      rw [IsLocalRing.mem_maximalIdeal] at hzm ⊢
      exact fun hu => hzm (hu.map φ)
    exact hzQ (hmQ hw)
  have hrad : Iy.IsRadical := by
    haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal C
    haveI : IsReduced ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) :=
      inferInstance
    have hsurj : Function.Surjective
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap x₀).hom :=
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι.stalkMap_surjective x₀
    have e := RingHom.quotientKerEquivOfSurjective hsurj
    rw [hIy, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk _ x₀]
    refine (Ideal.isRadical_iff_quotient_reduced _).mpr ?_
    exact isReduced_of_injective e e.injective
  obtain ⟨f, hf⟩ := exists_eq_span_singleton_of_isRadical hdimA hrad hI0 hmin
  have hfm : f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
      C).subschemeι x₀)) ^ m := by
    have := MMP.Resolution.le_pow_of_le_idealOrder (le_of_eq hord.symm)
    rw [hf] at this
    exact this (Ideal.mem_span_singleton_self f)
  have hfm' : f ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
      C).subschemeι x₀)) ^ (m + 1) := by
    intro hmem
    have : ((m + 1 : ℕ) : ℕ∞) ≤ MMP.Resolution.idealOrder Iy :=
      le_iSup₂_of_le (f := fun (j : ℕ) (_ : Iy ≤ IsLocalRing.maximalIdeal (Y.presheaf.stalk
          ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀)) ^ j) => (j : ℕ∞))
        (m + 1) (by rw [hf, Ideal.span_singleton_le_iff_mem]; exact hmem) le_rfl
    rw [hord] at this
    exact absurd (by exact_mod_cast this : m + 1 ≤ m) (by omega)
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    have hfu : IsUnit f := by
      by_contra hfu
      exact hfm' (by simpa using (IsLocalRing.mem_maximalIdeal f).mpr hfu)
    have htop : Iy = ⊤ := by rw [hf, Ideal.span_singleton_eq_top]; exact hfu
    rw [hIy, IdealSheafData.stalk_eq_top_iff_notMem_support] at htop
    exact htop (by
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hyC)
  -- coordinates at `y`, made transversal to `f`
  obtain ⟨U, hU, hyU, x₁, t, hxt⟩ := exists_generators_vanishingIdeal_singleton hY hYs hYd hy
  have hspan₁ : Ideal.span {Y.presheaf.germ U _ hyU x₁, Y.presheaf.germ U _ hyU t} =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
          C).subschemeι x₀)) := by
    have h1 := hxt ⟨U, hU⟩ le_rfl
    have hid : ∀ z : Γ(Y, U), (Y.presheaf.map (homOfLE (le_refl U)).op).hom z = z := fun z => by
      rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]; rfl
    simp only [hid] at h1
    rw [← AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton _ hy,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ _ ⟨U, hU⟩ hyU, h1, Ideal.map_span,
      Set.image_insert_eq, Set.image_singleton]
  have : Infinite k := inferInstance
  obtain ⟨c, a, g, ha, hg, hfa⟩ := exists_transversal hres hspan₁ hfm hfm'
  let cU : Γ(Y, U) := (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
    (((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop).hom c)
  have hcU : Y.presheaf.germ U _ hyU cU = algebraMap k (Y.presheaf.stalk
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι x₀)) c := by
    change (Y.presheaf.germ U _ hyU).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom _) = _
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  let x : Γ(Y, U) := x₁ - cU * t
  have hgx : Y.presheaf.germ U _ hyU x =
      Y.presheaf.germ U _ hyU x₁ - algebraMap k (Y.presheaf.stalk
          ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι
              x₀)) c * Y.presheaf.germ U _ hyU t := by
    simp only [x, map_sub, map_mul, hcU]
  have hxt' : ∀ (V : Y.affineOpens) (h : V.1 ≤ U),
      (Scheme.IdealSheafData.vanishingIdeal ⟨{_}, hy⟩).ideal V =
        Ideal.span {(Y.presheaf.map (homOfLE h).op).hom x,
          (Y.presheaf.map (homOfLE h).op).hom t} := by
    intro V h
    rw [hxt V h, ← span_pair_sub_mul _ _ ((Y.presheaf.map (homOfLE h).op).hom cU)]
    simp only [x, map_sub, map_mul]
  have hspan : Ideal.span {Y.presheaf.germ U _ hyU x, Y.presheaf.germ U _ hyU t} =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk ((Scheme.IdealSheafData.vanishingIdeal
          C).subschemeι x₀)) := by
    rw [← hspan₁, hgx, span_pair_sub_mul]
  obtain ⟨hxprime, htx⟩ := prime_and_notMem_of_span_pair_eq h2 hspan
  have hHilb := MMP.Mori.SurfaceAux.finite_finrank_quotient_pow h2 hres m
  rw [← hgx] at hfa hg
  obtain ⟨B, _, _, hinj, τ, hτ, hgen, hreg, ⟨e⟩⟩ := exists_presentation_stalk_cokernel hY hYs hYd
    C hC x₀ hy hm1 U hU hyU x t hxt' f a g hf hfa ha hg
  letI : Algebra k B := ((algebraMap ((Scheme.IdealSheafData.vanishingIdeal
      C).subscheme.presheaf.stalk
    x₀) B).comp ψ).toAlgebra
  haveI : IsScalarTower k ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk
      x₀) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hlen := length_quotient_range_eq_sum hres hm1 hspan hxprime htx ha hfa hg hHilb φ hφ
    (hker.trans hf) hinj τ hτ hgen hreg
  have hne : Module.length k (B ⧸ LinearMap.range (Algebra.linearMap
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B)) ≠ ⊤ := by
    rw [hlen]; exact ENat.coe_ne_top _
  have : Module.Finite k (B ⧸ LinearMap.range (Algebra.linearMap
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B)) := by
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hne)).1
    exact Module.IsNoetherian.finite k _
  rw [Module.length_eq_finrank] at hlen
  have key : Module.finrank k (B ⧸ LinearMap.range (Algebra.linearMap
      ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) B)) =
      ∑ j ∈ Finset.range m, j := by exact_mod_cast hlen
  rw [← key]
  refine LinearEquiv.finrank_eq ?_
  exact
    { toFun := e
      invFun := e.symm
      map_add' := e.map_add
      map_smul' := fun c z => (e.map_smul (ψ c) z).trans
        (IsScalarTower.algebraMap_smul
          ((Scheme.IdealSheafData.vanishingIdeal C).subscheme.presheaf.stalk x₀) c (e z))
      left_inv := e.left_inv
      right_inv := e.right_inv }

/-- **(d)** `dim_k H⁰(C, g_*𝒪_{C'}/𝒪_C) = ∑_{j<m} j`. -/
private theorem finrank_cokernel_strictTransformToCurve
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)]
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ C) {m : ℕ}
    (hm : MMP.Resolution.multAt (Scheme.IdealSheafData.vanishingIdeal C) y = m) :
    Module.finrank k (cohomologyOverField k
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)
      (cokernel (Stacks.GlueSquishFactor.structureUnitHom (strictTransformToCurve C hy))) 0) =
      ∑ j ∈ Finset.range m, j := by
  set iC := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  set g := strictTransformToCurve C hy
  have : IsFinite g := isFinite_strictTransformToCurve hY hYs hYd C hC hy hyC
  have : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (iC ≫ sY)
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (strictTransformCloseds C hy)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (g ≫ iC ≫ sY)
  have h1 : (Stacks.GlueSquishFactor.unitModule
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have h1' : (Stacks.GlueSquishFactor.unitModule
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have h2 : ((Scheme.Modules.pushforward g).obj (Stacks.GlueSquishFactor.unitModule
      (Scheme.IdealSheafData.vanishingIdeal (strictTransformCloseds C hy)).subscheme)).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite g _
  have h2' : ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g).underlyingModule :
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Modules).IsCoherent := h2
  have : (cokernel (Stacks.GlueSquishFactor.structureUnitHom g)).IsCoherent :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_cokernel' _ h1 h2'
  have hiso := isIso_strictTransformToCurve_restrict C hy
  obtain ⟨x₀, hx₀⟩ : y ∈ Set.range iC := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hyC
  have hsupp : SheafOfModules.supp (cokernel (Stacks.GlueSquishFactor.structureUnitHom g)) ⊆
      {x₀} := by
    refine (Stacks.GlueSquishFactor.supp_subset_compl_cokernel_structureUnitHom g
      (iC ⁻¹ᵁ ⟨{y}ᶜ, hy.isOpen_compl⟩)).trans ?_
    intro z hz
    have hzy : iC z = y := by by_contra h; exact hz h
    exact iC.isClosedEmbedding.injective (hzy.trans hx₀.symm)
  rw [finrank_cohomologyOverField_zero_eq_finrank_stalk_of_supp_subset k (iC ≫ sY)
    (cokernel (Stacks.GlueSquishFactor.structureUnitHom g)) hsupp]
  exact finrank_stalk_cokernel_strictTransformToCurve hY hYs hYd C hC hy hyC hm x₀ hx₀

/-- The Euler characteristic across a finite morphism `g : X' ⟶ X` over `k` with
`𝒪_X ⊂ g_*𝒪_{X'}` that is an isomorphism off one point, for a structure morphism `q` of `X'`
given as `g ≫ p` up to equality. -/
private theorem eulerCharacteristic_eq_add_of_comp_eq (k : Type w) [Field k] {X' X : Scheme.{w}}
    (g : X' ⟶ X) [IsFinite g] (p : X ⟶ Spec (.of k)) [IsProper p] (q : X' ⟶ Spec (.of k))
    [IsProper q] (hq : g ≫ p = q)
    (hmono : Mono (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra g).hom)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (g ∣_ U)] (n : ℕ)
    (hn :
      Module.finrank k (cohomologyOverField k p
        (cokernel (Stacks.GlueSquishFactor.structureUnitHom g)) 0) = n) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k p
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k q
    eulerCharacteristic k q (SheafOfModules.unit _) =
      eulerCharacteristic k p (SheafOfModules.unit _) + (n : ℤ) := by
  subst hq
  have h := Stacks.GlueSquishFactor.eulerCharacteristic_unit_eq_add_finrank k g p hmono hU
  rw [hn] at h
  exact h

/-- `χ(𝒪_{C'}) = χ(𝒪_C) + m(m-1)/2`. -/
private theorem eulerCharacteristic_strictTransform
    {k : Type w} [Field k] [IsAlgClosed k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)]
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ C) {m : ℕ}
    (hm : MMP.Resolution.multAt (Scheme.IdealSheafData.vanishingIdeal C) y = m)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
          ((C : Set Y) \ {y})), isClosed_closure⟩ :
          Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)] :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
          ((C : Set Y) \ {y})), isClosed_closure⟩ :
          Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
    eulerCharacteristic k ((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
          ((C : Set Y) \ {y})), isClosed_closure⟩ :
          Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
        (SheafOfModules.unit _) =
      eulerCharacteristic k ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)
        (SheafOfModules.unit _) + ((∑ j ∈ Finset.range m, j : ℕ) : ℤ) := by
  have hfin := isFinite_strictTransformToCurve hY hYs hYd C hC hy hyC
  have hiso := isIso_strictTransformToCurve_restrict C hy
  obtain ⟨x, hx⟩ : y ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hyC
  have hU : (((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ⁻¹ᵁ
      ⟨{y}ᶜ, hy.isOpen_compl⟩ : Opens _) : Set _) = {x}ᶜ := by
    ext z
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Set.mem_compl_iff,
      Set.mem_singleton_iff, ← hx]
    exact (Scheme.IdealSheafData.subschemeι _).isClosedEmbedding.injective.ne_iff
  exact eulerCharacteristic_eq_add_of_comp_eq k (strictTransformToCurve C hy) _ _
    (by rw [← Category.assoc, strictTransformToCurve_subschemeι, Category.assoc])
    (mono_pushforwardAlgebra_strictTransformToCurve C hC hy) hU _
    (finrank_cokernel_strictTransformToCurve hY hYs hYd C hC hy hyC hm)

end MMP.Proofs.lem_mmp_threefold_surface_blowup_genus_drop

namespace MMP.Threefold.Resolution

open MMP.Proofs.lem_mmp_threefold_surface_blowup_genus_drop in
/-- **Genus drop under a surface point blow-up.** Let `Y` be a smooth surface over an
algebraically closed field `k`, `C ⊆ Y` a reduced curve (a closed subset all of whose
irreducible components are one-dimensional, with its reduced induced structure) proper over `k`,
`y ∈ C` a closed point with `mult_y C = m`, and `π : Bl_y Y ⟶ Y` the blow-up of `y`. Then the
strict transform `C'`, the reduced closure of `π⁻¹(C ∖ {y})`, is proper over `k` and
`p_a(C') = p_a(C) - m(m-1)/2`. -/
@[mmp "lem_mmp_threefold_surface_blowup_genus_drop"]
public theorem arithmeticGenus_strictTransform_blowUp_singleton
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : Mori.IsVariety k sY) (hYs : Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    (C : Closeds Y) (hC : ∀ Z ∈ irreducibleComponents (C : Set Y), topologicalKrullDim Z = 1)
    [IsProper ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)]
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ C) {m : ℕ}
    (hm : MMP.Resolution.multAt (Scheme.IdealSheafData.vanishingIdeal C) y = m) :
    ∃ _ : IsProper ((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
          ((C : Set Y) \ {y})), isClosed_closure⟩ :
          Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY),
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY)
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
            ((C : Set Y) \ {y})), isClosed_closure⟩ :
            Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
      Mori.arithmeticGenus ((Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
            ((C : Set Y) \ {y})), isClosed_closure⟩ :
            Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))).subschemeι ≫
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) =
        Mori.arithmeticGenus ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ sY) -
          (m.choose 2 : ℤ) := by
  haveI := isProper_strictTransform hY C hy
  refine ⟨this, ?_⟩
  have h := eulerCharacteristic_strictTransform hY hYs hYd C hC hy hyC hm
  rw [Finset.sum_range_id, ← Nat.choose_two_right] at h
  simp only [MMP.Mori.arithmeticGenus]
  rw [h]
  ring

end MMP.Threefold.Resolution

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MonoidalCategory

variable {k : Type w} [Field k] {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}

namespace MMP.Proofs.thm_mmp_threefold_surface_adjunction_by_blowups

/-- On a locally Noetherian normal scheme, the order of vanishing along a prime divisor `Q` of a
nonzero element `t` of `𝒪_{X,Q}` is `length(𝒪_{X,Q}/(t))`. -/
private theorem valuation_toComponent_eq_length {X : Scheme.{w}} [IsLocallyNoetherian X]
    [IsNormal X] (Q : MMP.Mori.PrimeDivisor X) {t : Q.localRing} (ht : t ≠ 0) :
    Q.valuation (Q.toComponent.hom t) =
      WithZero.exp ((Module.length Q.localRing (Q.localRing ⧸ Ideal.span {t})).toNat : ℤ) := by
  let := Q.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Q.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Q.localRing := krullDimLE_of_coheight_le Q.coheight_genericPoint.le
  have := Q.isDiscreteValuationRing_localRing
  change Ring.ordFrac Q.localRing (IsLocalization.algEquiv (nonZeroDivisors Q.localRing) _
    (FractionRing Q.localRing) (algebraMap Q.localRing _ t)) = _
  rw [AlgEquiv.commutes, Ring.ordFrac_eq_ord _ ht]
  have hnz : t ∈ nonZeroDivisors Q.localRing := mem_nonZeroDivisors_of_ne_zero ht
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ hnz (n := (Ring.ord Q.localRing t).toNat)
    (ENat.coe_toNat (Ring.ord_ne_top hnz)).symm]
  rfl

/-- **Gluing local equations into an effective Cartier divisor.** On a locally Noetherian normal
integral scheme, let `D` be a divisor and `I` an ideal sheaf such that every point has an affine
neighbourhood `U` with a regular function `g` which is a local equation of `D` on `U` and generates
the ideal of `I` on `U`. Then `I` is the closed subscheme of an effective Cartier divisor `τ` whose
Weil divisor is `D`: two local generators generate the same ideal of each local ring, so they
differ by a unit and glue. -/
private theorem exists_cartierDivisor_of_localEquations
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y]
    (D : Divisor Y) (I : Y.IdealSheafData)
    (hD : ∀ x : Y, ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
      ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
          (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
        Divisor.IsLocalEquation D U φ ∧ I.ideal U = Ideal.span {g}) :
    ∃ τ : Y.CartierDivisor, MMP.Intersection.IsEffective τ ∧
      MMP.Intersection.IsSubschemeOfEffective τ I ∧
      ∀ _ : IsNoetherian Y, (weilDivisorEquivFinsupp (cartierWeilDivisor τ) : Divisor Y) = D := by
  choose U hxU g φ hgerm hloc hideal using hD
  have hmemZ : ∀ (x : Y) (Z : irreducibleComponents Y), x ∈ Z.1 := fun x Z => by
    have h := Z.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
    rw [h]
    trivial
  have hcomp : ∀ (x : Y) (Z : irreducibleComponents Y),
      componentGenericPoint Y Z ∈ (U x : Y.Opens) := fun x Z =>
    ((isGenericPoint_componentGenericPoint Y Z).specializes (hmemZ x Z)).mem_open
      (U x).1.isOpen (hxU x)
  have hg0 : ∀ (x y : Y) (hy : y ∈ (U x : Y.Opens)), Y.presheaf.germ (U x) y hy (g x) ≠ 0 := by
    intro x y hy h0
    have hz : g x = 0 := germ_injective_of_isIntegral Y y hy (by rw [h0, map_zero])
    let Z := MMP.Mori.pointComponent x
    have h1 := hgerm x Z (hcomp x Z)
    rw [hz, map_zero] at h1
    haveI := (RationalFunctions.isField_stalk Y Z).nontrivial
    exact (Pi.isUnit_iff.1 (φ x).isUnit Z).ne_zero h1
  have hu : ∀ x, IsUnit (MMP.Intersection.toTotalQuotient (U x : Y.Opens) (g x)) := fun x =>
    isUnit_toTotalQuotientSheaf_app Y.sheaf (U x : Y.Opens) (g x)
      (fun y hy => show Y.presheaf.germ (U x) y hy (g x) ∈ nonZeroDivisors (Y.presheaf.stalk y)
        from mem_nonZeroDivisors_of_ne_zero (hg0 x y hy))
  have hst : ∀ (x p : Y) (hp : p ∈ (U x : Y.Opens)),
      I.stalkIdeal p = Ideal.span {(Y.presheaf.germ (U x) p hp).hom (g x)} := by
    intro x p hp
    rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ p (U x) hp, hideal x, Ideal.map_span,
      Set.image_singleton]
  have hU : iSup (fun x => (U x : Y.Opens)) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨C, hC⟩ := MMP.Intersection.exists_isLocalEquationOn_of_germ_eq_mul
    (fun x => (U x : Y.Opens)) hU (fun x => (hu x).unit) (by
    intro i j p hi hj
    have hassoc : Associated (Y.presheaf.germ (U i) p hi (g i))
        (Y.presheaf.germ (U j) p hj (g j)) :=
      Ideal.span_singleton_eq_span_singleton.mp ((hst i p hi).symm.trans (hst j p hj))
    obtain ⟨w, hw⟩ := hassoc
    refine ⟨w, ?_⟩
    simp only [IsUnit.unit_spec]
    rw [MMP.Intersection.germ_toTotalQuotient, MMP.Intersection.germ_toTotalQuotient, ← hw,
      map_mul])
  refine ⟨C, fun x => ⟨U x, hxU x, g x, hu x, hC x⟩,
    fun x => ⟨U x, hxU x, g x, hu x, hC x, hideal x⟩, fun _ => ?_⟩
  ext Q
  set x := Q.genericPoint
  haveI : Nonempty (U x : Y.Opens) := ⟨⟨x, hxU x⟩⟩
  change (cartierWeilDivisor C).1 Q = _
  rw [cartierWeilDivisor_apply_of_local_eq C Q (U x : Y.Opens) (hxU x) (g x) 1 one_ne_zero
      (Additive.ofMul (hu x).unit) (by
        change (MMP.Intersection.toTotalQuotient (U x : Y.Opens) (g x)) *
          MMP.Intersection.toTotalQuotient (U x : Y.Opens) 1 = _
        rw [map_one, mul_one]; rfl)
      ((hC x).symm.trans (MMP.Intersection.cartierClass_eq_raw _ _))]
  have h1 : Module.length (Y.presheaf.stalk Q.genericPoint)
      ((Y.presheaf.stalk Q.genericPoint) ⧸
        Ideal.span {Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x) 1}) = 0 := by
    rw [map_one, Ideal.span_singleton_one]
    have : Subsingleton ((Y.presheaf.stalk Q.genericPoint) ⧸ (⊤ : _root_.Ideal _)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
  rw [h1, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  -- the coefficient of `P` at `Q` is the order of `g` along `Q`
  have hQ : (Q.support ∩ ((U x : Y.Opens) : Set Y)).Nonempty :=
    (MMP.Mori.PrimeDivisor.genericPoint_mem_iff Q _).mp (hxU x)
  have hc := hloc x Q hQ
  rw [hc]
  have ht0 : Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x) (g x) ≠ 0 := hg0 x _ _
  have hv := Q.valuation_component (φ x)
  rw [hgerm x Q.component (hcomp x Q.component)] at hv
  have hsp : Q.toComponent.hom ((Y.presheaf.germ (U x : Y.Opens) Q.genericPoint (hxU x)).hom
      (g x)) = (Y.presheaf.germ (U x : Y.Opens) _ (hcomp x Q.component)).hom (g x) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply ..
  rw [← hsp, valuation_toComponent_eq_length Q ht0] at hv
  exact WithZero.exp_injective hv

/-- If `g j` divides `g i * a` only when it divides `a` (for `i ≠ j`), then `g j` divides
`(∏_{i ∈ s} g i) * b` only when it divides `b`, for `j ∉ s`. -/
private theorem dvd_of_dvd_prod_mul {R ι : Type*} [CommMonoid R] [DecidableEq ι] {s : Finset ι}
    {g : ι → R} {j : ι} (hj : j ∉ s) (hg : ∀ i ∈ s, ∀ a, g j ∣ g i * a → g j ∣ a) {b : R}
    (h : g j ∣ (∏ i ∈ s, g i) * b) : g j ∣ b := by
  induction s using Finset.induction_on generalizing b with
  | empty => simpa using h
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, mul_assoc] at h
    exact ih (fun h' => hj (Finset.mem_insert_of_mem h'))
      (fun i' hi' => hg i' (Finset.mem_insert_of_mem hi'))
      (hg i (Finset.mem_insert_self i s) _ h)

/-- **An intersection of principal ideals is principal**, generated by the product, when no
generator divides a product with another generator without dividing the cofactor. -/
private theorem finset_inf_span_singleton_eq_span_prod {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (g : ι → R)
    (hg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, g j ∣ g i * a → g j ∣ a) :
    s.inf (fun i => Ideal.span {g i}) = Ideal.span {∏ i ∈ s, g i} := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.inf_insert, ih (fun i hi i' hi' => hg i (Finset.mem_insert_of_mem hi) i'
      (Finset.mem_insert_of_mem hi')), Finset.prod_insert hj]
    refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
    · rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hx
      obtain ⟨b, rfl⟩ := hx.2
      obtain ⟨c, rfl⟩ := dvd_of_dvd_prod_mul hj (fun i hi => hg i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_self j s) (fun h => hj (h ▸ hi))) hx.1
      exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
    · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
    · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

/-- The vanishing ideal of a finite union of closed subsets is the intersection of the vanishing
ideals, on every affine open. -/
private theorem ideal_vanishingIdeal_finset_sup {ι : Type*} (s : Finset ι)
    (Z : ι → TopologicalSpace.Closeds Y) (U : Y.affineOpens) :
    (Scheme.IdealSheafData.vanishingIdeal (s.sup Z)).ideal U =
      s.inf (fun i => (Scheme.IdealSheafData.vanishingIdeal (Z i)).ideal U) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup, Finset.inf_insert, ← ih]
    rfl

/-- A reduced divisor is the sum of its prime components. -/
private theorem eq_sum_single_of_reduced {X : Scheme.{w}} [IsLocallyNoetherian X] [IsNormal X]
    (C : Divisor X) (hC : ∀ E ∈ C.support, C E = 1) :
    C = ∑ P ∈ C.support, Finsupp.single P (1 : ℤ) := by
  conv_lhs => rw [← Finsupp.sum_single C]
  exact Finset.sum_congr rfl fun P hP => by rw [hC P hP]

/-- The reduced support of a divisor, as a closed subscheme, has the support as its image. -/
private theorem range_subschemeι_suppIdeal {X : Scheme.{w}} [IsLocallyNoetherian X] [IsNormal X]
    (C : Divisor X) : Set.range C.suppIdeal.subschemeι = (C.supp : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal]

/-- The reduced support of a divisor is contained in each of its components. -/
private theorem suppIdeal_le_idealSheaf {X : Scheme.{w}} [IsLocallyNoetherian X] [IsNormal X]
    (C : Divisor X) {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ C.support) :
    C.suppIdeal ≤ P.idealSheaf := by
  have := P.integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl,
    DivisorWithCoeffs.suppIdeal, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  intro z hz
  have h1 : z ∈ (C.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hP) hz
  rw [← DivisorWithCoeffs.coe_support_suppIdeal] at h1
  exact h1

/-- The closed subscheme of an ideal sheaf has the dimension of its support. -/
private theorem topologicalKrullDim_idealSheaf_subscheme {X : Scheme.{w}}
    (I : X.IdealSheafData) :
    topologicalKrullDim I.subscheme = topologicalKrullDim (I.support : Set X) := by
  have he := I.subschemeι.isClosedEmbedding.isEmbedding
  rw [IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph,
    Scheme.IdealSheafData.range_subschemeι]

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal (P : MMP.Mori.PrimeDivisor Y) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal P.idealSheaf.support := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

/-- On an affine open `V` meeting a prime divisor `P`, the ideal of `P` is prime; on an affine
open not meeting `P` it is the unit ideal. -/
private theorem isPrime_ideal_primeDivisor (P : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hPV : (P.support ∩ (V : Set Y)).Nonempty) : (P.idealSheaf.ideal V).IsPrime := by
  have hU : IsAffineOpen (V : Y.Opens) := V.2
  rw [idealSheaf_eq_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal,
    ← PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime]
  change IsIrreducible (hU.fromSpec ⁻¹' (P.support))
  refine IsIrreducible.preimage ?_ hU.fromSpec.isOpenEmbedding ?_
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  · rw [hU.range_fromSpec]
    exact hPV

private theorem ideal_primeDivisor_eq_top (P : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hPV : ¬ (P.support ∩ (V : Set Y)).Nonempty) : P.idealSheaf.ideal V = ⊤ := by
  have hU : IsAffineOpen (V : Y.Opens) := V.2
  rw [idealSheaf_eq_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' (P.support)) = ⊤
  convert PrimeSpectrum.vanishingIdeal_empty
  refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => hPV ⟨_, hz, ?_⟩
  rw [← hU.range_fromSpec]
  exact ⟨z, rfl⟩

/-- Two prime divisors are equal if, on an affine open containing the generic point of the
second, the ideal of the first is contained in that of the second. -/
private theorem eq_of_ideal_le_ideal (P Q : MMP.Mori.PrimeDivisor Y) (V : Y.affineOpens)
    (hQ : Q.genericPoint ∈ (V : Set Y)) (hle : P.idealSheaf.ideal V ≤ Q.idealSheaf.ideal V) :
    P = Q := by
  have hQQ : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hQP : Q.genericPoint ∈ P.support := by
    have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := Q.idealSheaf) hQ).mp hQQ
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.idealSheaf) hQ).mpr ?_
    rw [Scheme.mem_zeroLocus_iff] at h1 ⊢
    exact fun f hf => h1 f (hle hf)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hQP
  have hle' : Q.genericPoint ≤ P.genericPoint := Scheme.le_iff_specializes.mpr hQP
  by_contra hne
  have hlt : Q.genericPoint < P.genericPoint := by
    refine lt_of_le_not_ge hle' fun h => hne ?_
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hQP.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, MMP.Mori.PrimeDivisor.coheight_genericPoint]
    at this
  exact absurd this (by decide)

/-- **Local equations of a reduced curve.** On a locally Noetherian normal scheme on which the
ideal of every prime divisor is locally generated by a local equation, every point has an affine
neighbourhood `V` carrying, for each component `P` of a divisor `C`, a local equation `φ_P` of `P`
with regular representative `g_P` generating the ideal of `P` on `V`; and the ideal of the reduced
support of `C` on `V` is generated by `∏_P g_P`, since distinct components have non-associate
prime local equations. -/
private theorem exists_affineOpen_ideal_suppIdeal_eq_span_prod
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hloc : ∀ (P : MMP.Mori.PrimeDivisor Y) (x : Y), ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
      ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
          (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) U φ ∧
        P.idealSheaf.ideal U = Ideal.span {g})
    (C : Divisor Y) (x : Y) :
    ∃ V : Y.affineOpens, x ∈ (V : Y.Opens) ∧ ∃ (gP : MMP.Mori.PrimeDivisor Y → Γ(Y, V))
      (φP : MMP.Mori.PrimeDivisor Y → (RationalFunctions Y)ˣ),
      (∀ P ∈ C.support,
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V : Y.Opens)),
          (φP P : RationalFunctions Y) Z = Y.presheaf.germ V _ hZ (gP P)) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) V (φP P) ∧
        P.idealSheaf.ideal V = Ideal.span {gP P}) ∧
      C.suppIdeal.ideal V = Ideal.span {∏ P ∈ C.support, gP P} := by
  classical
  choose U hxU g φ hgerm hlocE hideal using hloc
  -- an affine neighbourhood of `x` inside the neighbourhoods of all components of `C`
  have hWo : IsOpen (⋂ P ∈ C.support, ((U P x : Y.Opens) : Set Y)) :=
    isOpen_biInter_finset fun P _ => (U P x : Y.Opens).isOpen
  have hxW : x ∈ ⋂ P ∈ C.support, ((U P x : Y.Opens) : Set Y) :=
    Set.mem_iInter₂.mpr fun P _ => hxU P x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hxW hWo
  let V' : Y.affineOpens := ⟨V, hV⟩
  have hVU : ∀ P ∈ C.support, V' ≤ U P x := fun P hP y hy =>
    Set.mem_iInter₂.mp (hVW hy) P hP
  -- the local data of each component, restricted to `V`
  have hdata : ∀ P ∈ C.support, ∃ gP : Γ(Y, V'),
      (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (V' : Y.Opens)),
        (φ P x : RationalFunctions Y) Z = Y.presheaf.germ V' _ hZ gP) ∧
      Divisor.IsLocalEquation (Finsupp.single P 1) V' (φ P x) ∧
      P.idealSheaf.ideal V' = Ideal.span {gP} := by
    intro P hP
    refine ⟨Y.presheaf.map (homOfLE (hVU P hP)).op (g P x), fun Z hZ => ?_,
      (hlocE P x).mono (hVU P hP), ?_⟩
    · rw [hgerm P x Z (hVU P hP hZ)]
      exact (Y.presheaf.germ_res_apply _ _ _ _).symm
    · rw [← Scheme.IdealSheafData.map_ideal _ (hVU P hP), hideal P x, Ideal.map_span,
        Set.image_singleton]
  haveI : Nonempty Γ(Y, V') := ⟨0⟩
  choose! gP hgP hlP hiP using hdata
  refine ⟨V', hxV, gP, fun P => φ P x, fun P hP => ⟨hgP P hP, hlP P hP, hiP P hP⟩, ?_⟩
  rw [DivisorWithCoeffs.suppIdeal, DivisorWithCoeffs.supp, ideal_vanishingIdeal_finset_sup]
  rw [Finset.inf_congr rfl fun P hP => by rw [← idealSheaf_eq_vanishingIdeal, hiP P hP]]
  refine finset_inf_span_singleton_eq_span_prod _ _ fun i hi j hj hij a hdiv => ?_
  by_cases hjV : (j.support ∩ (V' : Set Y)).Nonempty
  · have hprime : (Ideal.span {gP j}).IsPrime := hiP j hj ▸ isPrime_ideal_primeDivisor j V' hjV
    rw [← Ideal.mem_span_singleton] at hdiv ⊢
    refine (hprime.mem_or_mem hdiv).resolve_left fun h => ?_
    obtain ⟨y, hyj, hyV⟩ := hjV
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hyj
    refine hij (eq_of_ideal_le_ideal i j V' (hyj.mem_open (V' : Y.Opens).isOpen hyV) ?_)
    rw [hiP i hi, hiP j hj]
    exact Ideal.span_singleton_le_span_singleton.mpr (Ideal.mem_span_singleton.mp h)
  · have hu : IsUnit (gP j) := by
      rw [← Ideal.span_singleton_eq_top, ← hiP j hj]
      exact ideal_primeDivisor_eq_top j V' hjV
    exact hu.dvd

/-- On a locally Noetherian normal integral scheme on which the ideal of every prime divisor is
locally generated by a local equation, a reduced effective divisor `C` is the Weil divisor of an
effective Cartier divisor whose closed subscheme is the reduced support of `C`. -/
private theorem exists_cartierDivisor_isSubschemeOfEffective_suppIdeal
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y]
    (hloc : ∀ (P : MMP.Mori.PrimeDivisor Y) (x : Y), ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
      ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
          (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) U φ ∧
        P.idealSheaf.ideal U = Ideal.span {g})
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1) :
    ∃ τ : Y.CartierDivisor, MMP.Intersection.IsEffective τ ∧
      MMP.Intersection.IsSubschemeOfEffective τ C.suppIdeal ∧
      ∀ _ : IsNoetherian Y, (weilDivisorEquivFinsupp (cartierWeilDivisor τ) : Divisor Y) = C := by
  classical
  refine exists_cartierDivisor_of_localEquations C C.suppIdeal fun x => ?_
  obtain ⟨V, hxV, gP, φP, hV, hCV⟩ := exists_affineOpen_ideal_suppIdeal_eq_span_prod hloc C x
  refine ⟨V, hxV, ∏ P ∈ C.support, gP P, ∏ P ∈ C.support, φP P, fun Z hZ => ?_, ?_, hCV⟩
  · rw [map_prod, Units.coe_prod, Finset.prod_apply]
    exact Finset.prod_congr rfl fun P hP => (hV P hP).1 Z hZ
  · have key : ∀ t ⊆ C.support, Divisor.IsLocalEquation (∑ P ∈ t, Finsupp.single P (1 : ℤ))
        V (∏ P ∈ t, φP P) := by
      intro t ht
      induction t using Finset.induction_on with
      | empty => simpa using Divisor.isLocalEquation_zero (V : Y.Opens)
      | insert P t hPt ih =>
        rw [Finset.sum_insert hPt, Finset.prod_insert hPt]
        exact (hV P (ht (Finset.mem_insert_self P t))).2.1.add
          (ih fun Q hQ => ht (Finset.mem_insert_of_mem hQ))
    have h := key _ subset_rfl
    rwa [← eq_sum_single_of_reduced C hC] at h

/-- A prime divisor on a surface is one-dimensional. -/
private theorem topologicalKrullDim_support_primeDivisor (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (E : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim E.support = 1 := by
  haveI : IsIntegral Y := hY.toIsIntegral
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY E.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, hYd,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hne : topologicalKrullDim E.support ≠ ⊥ := by
    rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty, not_isEmpty_iff]
    exact ⟨⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩⟩
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at h ⊢
  induction d with
  | top => exact absurd h (by decide)
  | coe n =>
    have h2 : (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast; exact h
    have := Nat.cast_injective (WithBot.coe_injective h2)
    have hn : n = 1 := by omega
    subst hn
    rfl

/-- The reduced support of a divisor, as a subscheme, is homeomorphic to the support. -/
private theorem topologicalKrullDim_suppIdeal_subscheme_eq (C : Divisor Y) :
    topologicalKrullDim C.suppIdeal.subscheme = topologicalKrullDim (C.supp : Set Y) := by
  rw [topologicalKrullDim_idealSheaf_subscheme, DivisorWithCoeffs.coe_support_suppIdeal]

/-- The reduced support of a divisor on a surface has dimension at most one. -/
private theorem topologicalKrullDim_suppIdeal_subscheme_le_one
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y) :
    topologicalKrullDim C.suppIdeal.subscheme ≤ 1 := by
  rw [topologicalKrullDim_suppIdeal_subscheme_eq, DivisorWithCoeffs.coe_supp]
  exact topologicalKrullDim_biUnion_le C.support (fun E => E.idealSheaf.support.isClosed)
    (fun E _ => (topologicalKrullDim_support_primeDivisor hY hYd E).le)

/-- The support of a divisor on a surface is the union of its prime components, which are
one-dimensional: every irreducible component of the support is one-dimensional. -/
private theorem topologicalKrullDim_of_mem_irreducibleComponents_supp
    (hY : MMP.Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2) (C : Divisor Y)
    {Z : Set (C.supp : Set Y)} (hZ : Z ∈ irreducibleComponents (C.supp : Set Y)) :
    topologicalKrullDim Z = 1 := by
  classical
  have hSc : IsClosed (C.supp : Set Y) := C.supp.isClosed
  have hZi : IsIrreducible (Subtype.val '' Z : Set Y) :=
    hZ.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨T, hT, hZT⟩ := isIrreducible_iff_sUnion_isClosed.mp hZi
    (C.support.image fun E => E.support) (by
      intro T hT
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.mp hT
      exact E.idealSheaf.support.isClosed) (by
      rintro y ⟨z, -, rfl⟩
      obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp z.2
      exact ⟨E.support, Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hE)), hzE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hT
  have hES : E.support ⊆ (C.supp : Set Y) :=
    DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE)
  have hEirr : IsIrreducible E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hZE : Z ⊆ Subtype.val ⁻¹' E.support := fun z hz => hZT ⟨z, hz, rfl⟩
  have heq : Z = Subtype.val ⁻¹' E.support :=
    le_antisymm hZE (hZ.2 (isIrreducible_preimage_subtypeVal hEirr hES) hZE)
  rw [heq, topologicalKrullDim_preimage_val _ _ hES,
    topologicalKrullDim_support_primeDivisor hY hYd E]

/-- A smooth reduced divisor on a surface is smooth of relative dimension one over `k`. -/
private theorem smoothOfRelativeDimension_one_suppIdeal
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y)
    [Smooth (C.suppIdeal.subschemeι ≫ sY)] :
    SmoothOfRelativeDimension 1 (C.suppIdeal.subschemeι ≫ sY) := by
  classical
  have he := C.suppIdeal.subschemeι.isClosedEmbedding.isEmbedding
  have hr := range_subschemeι_suppIdeal C
  by_cases hC0 : C.support = ∅
  · haveI : IsEmpty C.suppIdeal.subscheme := by
      rw [← not_nonempty_iff]
      rintro ⟨x⟩
      have hx : C.suppIdeal.subschemeι x ∈ (C.supp : Set Y) := by rw [← hr]; exact ⟨x, rfl⟩
      rw [DivisorWithCoeffs.coe_supp, hC0] at hx
      simp at hx
    exact Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 1
      isEmptyElim
  · obtain ⟨E, hE⟩ := Finset.nonempty_iff_ne_empty.mpr hC0
    let e : C.suppIdeal.subscheme ≃ₜ (C.supp : Set Y) :=
      he.toHomeomorph.trans (Homeomorph.setCongr hr)
    refine smoothOfRelativeDimension_of_equidimensional k _
      (TopologicalSpace.Equidimensional.of_homeomorph e ?_) 1 ?_
    · intro Z hZ W hW
      rw [topologicalKrullDim_of_mem_irreducibleComponents_supp hY hYd C hZ,
        topologicalKrullDim_of_mem_irreducibleComponents_supp hY hYd C hW]
    · refine le_antisymm (topologicalKrullDim_suppIdeal_subscheme_le_one hY hYd C) ?_
      rw [topologicalKrullDim_suppIdeal_subscheme_eq]
      have h1 := topologicalKrullDim_support_primeDivisor hY hYd E
      calc ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim E.support := by rw [h1]; rfl
        _ ≤ _ := topologicalKrullDim_le_of_subset
          (DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE))

/-- **Serre duality on a smooth proper curve, at the level of Euler characteristics**:
`χ(Ω¹_{X/k}) = -χ(𝒪_X)` for `X` proper and smooth of relative dimension one over `k`, not
necessarily connected. -/
private theorem eulerCharacteristic_relativeDifferentialForms_one {X : Scheme.{w}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (hdim : topologicalKrullDim X ≤ 1)
    [(Scheme.Hom.relativeDifferentialForms f 1).IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k f (Scheme.Hom.relativeDifferentialForms f 1) =
      -eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) := by
  haveI := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  haveI := Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace
    (Scheme.Hom.relativeDifferentials f)
  haveI hO := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  haveI : (Scheme.Hom.relativeDifferentials f).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f _ 1
  obtain ⟨eω⟩ := Stacks.Duality.nonempty_dualizingSheafOverField_iso_relativeDifferentials f
  have hvan : ∀ (M : X.Modules) (m : ℕ), 2 ≤ m → Limits.IsZero (cohomologyOverField k f M m) :=
    fun M m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k f M (d := 1)
      (by exact_mod_cast hdim) (by omega)
  have eF : Scheme.Hom.relativeDifferentialForms f 1 ≅ Scheme.Hom.relativeDifferentials f :=
    Scheme.Modules.exteriorPowerOneIsoSelf (Scheme.Hom.relativeDifferentials f)
  have hΩ := eulerCharacteristic_eq_sub_of_isZero k f (Scheme.Hom.relativeDifferentials f)
    (fun m hm => hvan _ m hm)
  have hU := eulerCharacteristic_eq_sub_of_isZero k f (SheafOfModules.unit X.ringCatSheaf)
    (fun m hm => hvan _ m hm)
  rw [eulerCharacteristic_eq_of_iso k f eF, hΩ, hU]
  have h0 := finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one f hdim
    (SheafOfModules.unit X.ringCatSheaf) 1
  have h1 := finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one f hdim
    (Scheme.Hom.relativeDifferentials f) 1
  haveI := Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace
    (SheafOfModules.unit X.ringCatSheaf)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let D : X.Modules := Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 O
  let ev : D ⊗ O ≅ O := Stacks.SheafOfModules.Scheme.evaluationIso X O
  let eO : D ≅ O := (ρ_ D).symm ≪≫ ev
  let eA := whiskerRightIso eO (Stacks.Duality.dualizingSheafOverField f) ≪≫ λ_ _ ≪≫ eω
  let eB := whiskerLeftIso _ eω ≪≫
    Stacks.SheafOfModules.Scheme.evaluationIso X (Scheme.Hom.relativeDifferentials f)
  have hA : Module.finrank k (cohomologyOverField k f (Scheme.Hom.relativeDifferentials f) 0) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    (finrank_cohomologyOverField_eq_of_iso k f eA 0).symm.trans h0
  have hB : Module.finrank k (cohomologyOverField k f (Scheme.Hom.relativeDifferentials f) 1) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :=
    h1.symm.trans (finrank_cohomologyOverField_eq_of_iso k f eB 0)
  rw [hA, hB]
  ring

/-- Adjunction for a *smooth* reduced proper curve: the conormal sequence gives
`Ω¹_C ≅ 𝒪_Y(K_Y + C)|_C`, and the degree of `Ω¹` on each component is `2 p_a - 2`. -/
private theorem adjunction_of_smooth
    [IsAlgClosed k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY))
    (hCs : MMP.Mori.IsSmoothScheme (C.suppIdeal.subschemeι ≫ sY)) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
      (-2 * eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
        (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)) := by
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI hYsm : Smooth sY := (isSmoothScheme_iff sY).mp hYs
  haveI : IsSmoothVariety k sY := { toIsVariety := hY, toSmooth := hYsm }
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsSeparated sY := hY.toIsSeparated
  haveI : SmoothOfRelativeDimension 2 sY :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety sY 2 (by exact_mod_cast hYd)
  obtain ⟨hcart, hloc, -, hiso, -, hQ⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  haveI : IsNoetherian Y := ⟨⟩
  set i := C.suppIdeal.subschemeι with hi
  haveI hCsm : Smooth (i ≫ sY) := (isSmoothScheme_iff _).mp hCs
  obtain ⟨τ, -, hτs, hτW⟩ := exists_cartierDivisor_isSubschemeOfEffective_suppIdeal hloc C hC
  have eC : Nonempty (C.divisorialSheaf ≅ MMP.CartierDivisor.sheaf τ) := by
    rw [← hτW ⟨⟩]; exact hiso τ
  obtain ⟨eC⟩ := eC
  obtain ⟨eAdj⟩ := MMP.Intersection.nonempty_pullback_canonical_twist_iso sY (n := 1)
    C.suppIdeal τ hτs
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_of_isCanonicalDivisor hYs hK
  let eKC : (K + C).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms sY ((1 : ℕ) + 1) ⊗ MMP.CartierDivisor.sheaf τ :=
    ((hcart K).divisorialSheafTensorIso (hcart C)).symm ≪≫
      whiskerRightIso (eK ≪≫ eqToIso (by push_cast; rfl)) _ ≪≫ whiskerLeftIso _ eC
  let e : (Scheme.Modules.pullback i).obj (K + C).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms (i ≫ sY) 1 :=
    (Scheme.Modules.pullback i).mapIso eKC ≪≫ eAdj
  have hdim : topologicalKrullDim C.suppIdeal.subscheme ≤ 1 :=
    topologicalKrullDim_suppIdeal_subscheme_le_one hY hYd C
  haveI : SmoothOfRelativeDimension 1 (i ≫ sY) := smoothOfRelativeDimension_one_suppIdeal hY hYd C
  haveI := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials (i ≫ sY)
  haveI hinvΩ := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := C.suppIdeal.subscheme.toRingedSpace) _
    (h := Stacks.Discriminant.isInvertible_relativeDifferentialForms (i ≫ sY) 1)
  haveI := (hcart (K + C)).isInvertibleModule_divisorialSheaf
  haveI : (Scheme.Hom.relativeDifferentialForms (i ≫ sY) 1).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k (i ≫ sY)
      _ 1
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ sY)
  refine ⟨hCp, hdim, hQ _, ?_⟩
  rw [QDivisor.intersectionNumber_toQDivisor k sY i hdim (K + C) (hcart _)]
  have h1 : Divisor.degreeOn k sY i hdim (K + C) (hcart _) =
      invertibleCurveDegree k (i ≫ sY) hdim (Scheme.Hom.relativeDifferentialForms (i ≫ sY) 1) :=
    invertibleCurveDegree_eq_of_iso k (i ≫ sY) hdim e
  rw [h1]
  change ((eulerCharacteristic k (i ≫ sY) (Scheme.Hom.relativeDifferentialForms (i ≫ sY) 1) -
    eulerCharacteristic k (i ≫ sY) (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf) :
      ℤ) : ℚ) = _
  rw [eulerCharacteristic_relativeDifferentialForms_one (i ≫ sY) hdim]
  push_cast
  ring

open Stacks.AlgebraicGeometry.ProperSectionsGeom in
/-- **The arithmetic genus is bounded below by the number of components**:
`χ(𝒪_C) ≤ dim_k H⁰(C, 𝒪_C) ≤ #(components of C)` for a reduced proper curve over an algebraically
closed field. -/
private theorem eulerCharacteristic_le_card_support
    [IsAlgClosed k] [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY)) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
        (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf) ≤ C.support.card := by
  classical
  haveI := hCp
  haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (C.suppIdeal.subschemeι ≫ sY)
  have hdim := topologicalKrullDim_suppIdeal_subscheme_le_one hY hYd C
  have hvan : ∀ (M : C.suppIdeal.subscheme.Modules) (m : ℕ), 2 ≤ m →
      Limits.IsZero (cohomologyOverField k (C.suppIdeal.subschemeι ≫ sY) M m) :=
    fun M m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k _ M (d := 1)
      (by exact_mod_cast hdim) (by omega)
  have hU := eulerCharacteristic_eq_sub_of_isZero k (C.suppIdeal.subschemeι ≫ sY)
    (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf) (fun m hm => hvan _ m hm)
  rw [hU]
  have h0 := AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections
    k (C.suppIdeal.subschemeι ≫ sY)
  haveI : IsReduced C.suppIdeal.subscheme :=
    inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme)
  have h1 := finrank_globalSections_eq_card_connectedComponents
    k (C.suppIdeal.subschemeι ≫ sY)
  have h2 : Nat.card (_root_.ConnectedComponents C.suppIdeal.subscheme) ≤ C.support.card := by
    have he := C.suppIdeal.subschemeι.isClosedEmbedding.isEmbedding
    have hr := range_subschemeι_suppIdeal C
    let e : C.suppIdeal.subscheme ≃ₜ (C.supp : Set Y) :=
      he.toHomeomorph.trans (Homeomorph.setCongr hr)
    have hgen : ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ E.support := fun E => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have hmem : ∀ E ∈ C.support, E.genericPoint ∈ (C.supp : Set Y) := fun E hE =>
      DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) (hgen E)
    let g : C.support → _root_.ConnectedComponents C.suppIdeal.subscheme := fun E =>
      ConnectedComponents.mk (e.symm ⟨E.1.genericPoint, hmem E.1 E.2⟩)
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp (e x).2
      refine ⟨⟨E, Finsupp.mem_support_iff.mpr hE⟩, ?_⟩
      have hES : E.support ⊆ (C.supp : Set Y) := DivisorWithCoeffs.support_subset_supp hE
      have hEirr : IsIrreducible E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have hT : _root_.IsPreconnected (e ⁻¹' (Subtype.val ⁻¹' E.support)) :=
        ((isIrreducible_preimage_subtypeVal hEirr hES).2.preimage
          e.isOpenEmbedding).isPreconnected
      refine (ConnectedComponents.coe_eq_coe').mpr (hT.subset_connectedComponent hxE ?_)
      change ((e (e.symm _)) : Y) ∈ E.support
      rw [e.apply_symm_apply]
      exact hgen E
    calc Nat.card _ ≤ Nat.card C.support := Nat.card_le_card_of_surjective g hg
      _ = C.support.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
  have : (Module.finrank k (cohomologyOverField k (C.suppIdeal.subschemeι ≫ sY)
      (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf) 0) : ℤ) ≤ C.support.card := by
    rw [h0, h1]; exact_mod_cast h2
  omega

/-- **A singular reduced curve on a smooth surface has a closed point of multiplicity at least
two.** -/
private theorem exists_two_le_multAt_of_not_isSmoothScheme
    [IsAlgClosed k] [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) (C : Divisor Y)
    (hC : ∀ E ∈ C.support, C E = 1)
    (hCs : ¬ MMP.Mori.IsSmoothScheme (C.suppIdeal.subschemeι ≫ sY)) :
    ∃ (y : Y) (_ : IsClosed ({y} : Set Y)) (m : ℕ), y ∈ (C.supp : Set Y) ∧ 2 ≤ m ∧
      MMP.Resolution.multAt C.suppIdeal y = m := by
  classical
  by_contra hne
  push Not at hne
  apply hCs
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.toQuasiCompact
  haveI hYsm : Smooth sY := (isSmoothScheme_iff sY).mp hYs
  haveI : IsSmoothVariety k sY := { toIsVariety := hY, toSmooth := hYsm }
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨-, hloc, -, -, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  obtain ⟨τ, -, hτs, -⟩ := exists_cartierDivisor_isSubschemeOfEffective_suppIdeal hloc C hC
  set i := C.suppIdeal.subschemeι with hi
  -- `C` is nonzero at the generic point of `Y`
  have hgen : MMP.Resolution.IsNonzeroAtGenericPoints C.suppIdeal := by
    intro η hη hbot
    have hηC : η ∈ C.suppIdeal.support := by
      by_contra hη'
      rw [← Stacks.Divisors.stalk_eq_top_iff_notMem_support] at hη'
      rw [hη'] at hbot
      exact top_ne_bot hbot
    have huniv : closure ({η} : Set Y) = Set.univ := by
      obtain ⟨Z, hZ⟩ : ∃ Z, Z ∈ irreducibleComponents Y := ⟨_, hη⟩
      have h1 := IrreducibleSpace.isIrreducible_univ (X := Y)
      exact Set.eq_univ_of_univ_subset (hη.2 h1 (Set.subset_univ _))
    have hsub : (Set.univ : Set Y) ⊆ (C.supp : Set Y) := by
      rw [← huniv, ← DivisorWithCoeffs.coe_support_suppIdeal]
      exact (C.suppIdeal.support.isClosed.closure_subset_iff).mpr
        (Set.singleton_subset_iff.mpr hηC)
    have h1 := topologicalKrullDim_le_of_subset hsub
    rw [← topologicalKrullDim_suppIdeal_subscheme_eq] at h1
    have h2 := h1.trans (topologicalKrullDim_suppIdeal_subscheme_le_one hY hYd C)
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph, hYd] at h2
    exact absurd h2 (by decide)
  -- regularity of `C` at its closed points
  have hregC : ∀ z : C.suppIdeal.subscheme, IsClosed ({z} : Set C.suppIdeal.subscheme) →
      IsRegularLocalRing (C.suppIdeal.subscheme.presheaf.stalk z) := by
    intro z hz
    have hp : IsClosed ({i z} : Set Y) := by
      rw [← Set.image_singleton]
      exact i.isClosedEmbedding.isClosedMap _ hz
    have hpC : i z ∈ C.suppIdeal.support := by
      show i z ∈ (C.suppIdeal.support : Set Y)
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    obtain ⟨U, hpU, s, -, -, hUs⟩ := hτs (i z)
    have hst : IdealSheafData.stalk C.suppIdeal (i z) =
        Ideal.span {Y.presheaf.germ U (i z) hpU s} := by
      rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ (i z) U hpU, hUs, Ideal.map_span,
        Set.image_singleton]
    have htop := MMP.Resolution.multAt_ne_top_of_isNonzeroAtGenericPoints hgen (i z)
    have hone : 1 ≤ MMP.Resolution.multAt C.suppIdeal (i z) := by
      have hne' : IdealSheafData.stalk C.suppIdeal (i z) ≠ ⊤ := fun h =>
        ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).1 h) hpC
      unfold MMP.Resolution.multAt
      rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by simp, MMP.Resolution.natCast_le_idealOrder_iff',
        pow_one]
      exact IsLocalRing.le_maximalIdeal hne'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hn1 : n = 1 := by
      have h1 : 1 ≤ n := by rw [← hn] at hone; exact_mod_cast hone
      by_contra h
      exact hne (i z) hp n (by rw [← DivisorWithCoeffs.coe_support_suppIdeal]; exact hpC)
        (by omega) hn.symm
    have hm1 : MMP.Resolution.multAt C.suppIdeal (i z) = 1 := by rw [← hn, hn1]; rfl
    have hf0 : Y.presheaf.germ U (i z) hpU s ≠ 0 := by
      intro h0
      rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hst
      apply htop
      unfold MMP.Resolution.multAt
      rw [hst]
      refine top_unique (ENat.forall_natCast_le_iff_le.mp fun m _ => ?_)
      rw [MMP.Resolution.natCast_le_idealOrder_iff']
      exact bot_le
    have hq := (MMP.Resolution.Kollar.isRegularLocalRing_stalk_quotient_iff_multAt_eq_one hp
      (isRegularLocalRing_stalk_of_smooth_over_field sY (i z))
      (MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hY hYd (i z) hp) C.suppIdeal hpC _ hst
      hf0).mpr hm1
    exact isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient C.suppIdeal z hq
  -- the smooth locus contains every closed point, hence is everything
  have hloc' := smoothAt_locus_eq_regular_locus k (i ≫ sY)
  have hall : ∀ z, InfinitesimalLifting.SmoothAt (i ≫ sY) z := by
    by_contra hns
    push Not at hns
    have hcl : IsClosed {z | ¬ InfinitesimalLifting.SmoothAt (i ≫ sY) z} :=
      (isOpen_smoothAt_locus (i ≫ sY)).isClosed_compl
    haveI : CompactSpace C.suppIdeal.subscheme := QuasiCompact.compactSpace_of_compactSpace i
    obtain ⟨z, hz, hzc⟩ := hcl.exists_closed_singleton hns
    have : z ∈ {x | InfinitesimalLifting.SmoothAt (i ≫ sY) x} := by
      rw [hloc']; exact hregC z hzc
    exact hz this
  rw [MMP.Mori.IsSmoothScheme, eq_top_iff]
  intro z _
  obtain ⟨U, hzU, hU⟩ := hall z
  refine MMP.Mori.mem_smoothLocus_iff.mpr ⟨U, hzU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι (i ≫ sY) (U := ⊤) (V := U) le_top]
  infer_instance

open scoped Classical in
/-- **Strict transform of a reduced divisor.** If every prime divisor `E` of `X` has a strict
transform `T E` under `g`, with `T` injective, then the strict transform of a reduced divisor `C`
is the reduced divisor with components `T E` for `E` a component of `C`. -/
private theorem inverseTransformDivisor_of_reduced {X X' : Scheme.{w}} [IsLocallyNoetherian X]
    [IsNormal X] {g : X' ⟶ X} {T : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor X'}
    (hT : ∀ E, inverseTransformPrimeDivisor g E = some (T E)) (hTinj : Function.Injective T)
    (C : Divisor X) (hC : ∀ E ∈ C.support, C E = 1) :
    (inverseTransformDivisor g C : Divisor X') = ∑ E ∈ C.support, Finsupp.single (T E) 1 ∧
      (inverseTransformDivisor g C : Divisor X').support = C.support.image T ∧
      ∀ E' ∈ (inverseTransformDivisor g C : Divisor X').support,
        (inverseTransformDivisor g C : Divisor X') E' = 1 := by
  classical
  have hsum : (inverseTransformDivisor g C : Divisor X') =
      ∑ E ∈ C.support, Finsupp.single (T E) 1 := by
    conv_lhs => rw [eq_sum_single_of_reduced C hC]
    rw [map_sum]
    exact Finset.sum_congr rfl fun E _ => inverseTransformDivisor_single_of_eq_some (hT E) 1
  have hcoef : ∀ E', (inverseTransformDivisor g C : Divisor X') E' =
      if E' ∈ C.support.image T then 1 else 0 := fun E' => by
    rw [hsum, ← Finset.sum_image (f := fun E' => Finsupp.single E' (1 : ℤ))
      fun a _ b _ h => hTinj h, Finset.sum_apply']
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hsupp : (inverseTransformDivisor g C : Divisor X').support = C.support.image T := by
    ext E'
    rw [Finsupp.mem_support_iff, hcoef]
    split_ifs with h <;> simp [h]
  exact ⟨hsum, hsupp, fun E' hE' => by rw [hcoef, if_pos (hsupp ▸ hE')]⟩

open MMP.Threefold.Resolution in
/-- **The strict transform of a reduced curve under a point blow-up.** For the blow-up
`π : Y' ⟶ Y` of a closed point `y` of a smooth surface, the birational transform `C' = π⁻¹_* C` of
a reduced divisor `C` is reduced, has as many components as `C`, and its support is the closure of
`π⁻¹(C ∖ {y})`. -/
private theorem inverseTransformDivisor_blowUp_singleton_reduced
    [IsAlgClosed k] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y)) :
    (∀ E ∈ (inverseTransformDivisor (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _).support,
      (inverseTransformDivisor (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _) E = 1) ∧
    (inverseTransformDivisor (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _).support.card =
      C.support.card ∧
    ((inverseTransformDivisor (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _).supp :
          Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))) =
      closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
        ((C.supp : Set Y) \ {y})) := by
  classical
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) with hπ
  obtain ⟨-, F, hF, -, -⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY _
      (isSmoothBlowup_vanishingIdeal_singleton sY hYs hy)
      (isIrreducible_support_vanishingIdeal_singleton hy)
      (one_le_codimension_vanishingIdeal_singleton hYd hy)
  have hV : ∀ x : Y, x ∈ biregularLocus π ↔ x ≠ y := fun x =>
    ⟨fun hx hxy => notMem_biregularLocus_blowUpToBase_singleton hY hYd hy hF
      (Eq.subst (motive := fun z => z ∈ biregularLocus π) hxy hx),
      mem_biregularLocus_blowUpToBase_singleton hy⟩
  have hηV : ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ biregularLocus π := by
    intro E
    rw [hV]
    intro h
    have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint E
    have h2 := coheight_eq_two_of_isClosed hY hYd hy
    rw [h] at h1
    rw [h1] at h2
    exact absurd h2 (by decide)
  choose T hT hTη using fun E =>
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := π) E (hηV E)
  have hTinj : Function.Injective T := fun E₁ E₂ h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
      have h1 := hTη E₁
      rw [h, hTη E₂] at h1
      exact h1.symm)
  obtain ⟨-, hsupp', hcoef⟩ := inverseTransformDivisor_of_reduced hT hTinj C hC
  refine ⟨hcoef, ?_, ?_⟩
  · rw [hsupp', Finset.card_image_of_injective _ hTinj]
  · rw [DivisorWithCoeffs.coe_supp, hsupp', Finset.set_biUnion_finset_image]
    have hTs : ∀ E, (T E).support = closure (π ⁻¹' (E.support ∩ biregularLocus π)) := fun E => by
      rw [support_inverseTransformPrimeDivisor (hT E)]
      rfl
    simp_rw [hTs]
    rw [← Finset.closure_biUnion]
    congr 1
    rw [DivisorWithCoeffs.coe_supp]
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff,
      Set.mem_singleton_iff, SetLike.mem_coe, hV, exists_prop]
    tauto

/-! ### Intersection numbers with the components of a reduced curve -/

/-- A prime component of a divisor whose reduced support is proper over `k` is proper over `k`. -/
private theorem isProper_idealSheaf_of_mem_support {X : Scheme.{w}} {s : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] (C : Divisor X)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ s)) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∈ C.support) : IsProper (P.idealSheaf.subschemeι ≫ s) := by
  have hle := suppIdeal_le_idealSheaf C hP
  have h1 : Scheme.IdealSheafData.inclusion hle ≫ C.suppIdeal.subschemeι =
      P.idealSheaf.subschemeι := Scheme.IdealSheafData.inclusion_subschemeι hle
  haveI : IsProper (Scheme.IdealSheafData.inclusion hle ≫ C.suppIdeal.subschemeι) := by
    rw [h1]; infer_instance
  haveI : IsProper (Scheme.IdealSheafData.inclusion hle) :=
    IsProper.of_comp _ C.suppIdeal.subschemeι
  rw [← h1, Category.assoc]
  infer_instance

/-- A one-dimensional prime divisor proper over `k` is a proper curve. -/
private theorem isProperCurve_genericPoint {X : Scheme.{w}} {s : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X)
    (hp : IsProper (P.idealSheaf.subschemeι ≫ s)) (hd : topologicalKrullDim P.support = 1) :
    IsProperCurve s P.genericPoint := by
  have h := MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf P
  refine ⟨?_, ?_⟩
  · change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({P.genericPoint} : Set X))).subscheme = 1
    rw [h, topologicalKrullDim_idealSheaf_subscheme]
    exact hd
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({P.genericPoint} : Set X))).subschemeι ≫ s)
    rw [h]
    exact hp

/-- On a smooth surface, every `ℚ`-divisor has an intersection number with every prime divisor
proper over `k`. -/
private theorem exists_isIntersectionNumber_primeDivisor {X : Scheme.{w}}
    {s : X ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsVariety k s) (hXs : MMP.Mori.IsSmoothScheme s)
    (hXd : topologicalKrullDim X = 2) (D : QDivisor X) (P : MMP.Mori.PrimeDivisor X)
    (hp : IsProper (P.idealSheaf.subschemeι ≫ s)) :
    ∃ x : ℚ, IsIntersectionNumber s D P.idealSheaf x := by
  have hdim : topologicalKrullDim P.idealSheaf.subscheme ≤ 1 := by
    rw [topologicalKrullDim_idealSheaf_subscheme]
    exact (topologicalKrullDim_support_primeDivisor hX hXd P).le
  exact ⟨_, hp, hdim, MMP.Fourfold.isQCartier_of_isSmoothScheme hXs D, rfl⟩

/-- The degree of an invertible sheaf depends only on the structure morphism. -/
private theorem invertibleCurveDegree_congr_hom {Z : Scheme.{w}} {t t' : Z ⟶ Spec (.of k)}
    (h : t = t')
    [IsProper t] [IsProper t'] (hdim : topologicalKrullDim Z ≤ 1) (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    invertibleCurveDegree k t hdim L = invertibleCurveDegree k t' hdim L := by
  subst h; rfl

/-- The degree of the pull-back along equal morphisms. -/
private theorem invertibleCurveDegree_pullback_congr {Z X : Scheme.{w}} {g g' : Z ⟶ X} (h : g = g')
    (s : X ⟶ Spec (.of k)) [IsProper (g ≫ s)] [IsProper (g' ≫ s)]
    (hdim : topologicalKrullDim Z ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k (g ≫ s) hdim ((Scheme.Modules.pullback g).obj L) =
      invertibleCurveDegree k (g' ≫ s) hdim ((Scheme.Modules.pullback g').obj L) := by
  subst h; rfl

open Stacks.AlgebraicGeometry.ComponentDegrees Stacks.AlgebraicGeometry.ComponentDegreeDevissage in
/-- **The degree on a reduced curve is the sum of the degrees on its components** [Stacks,
Tag 0AYW]: for a Cartier divisor `E` and a divisor `C` whose reduced support is a proper curve
with one-dimensional components `P`, `deg_C 𝒪(E) = ∑_P deg_P 𝒪(E)`. -/
private theorem degreeOn_suppIdeal_eq_sum {X : Scheme.{w}} {s : X ⟶ Spec (.of k)}
    [QuasiCompact s] [IsLocallyNoetherian X] [IsNormal X] (C : Divisor X)
    [IsProper (C.suppIdeal.subschemeι ≫ s)]
    (hdimC : topologicalKrullDim C.suppIdeal.subscheme ≤ 1)
    (hdim : ∀ P ∈ C.support, topologicalKrullDim P.support = 1) (E : Divisor X)
    (hE : E.IsCartier) (d : MMP.Mori.PrimeDivisor X → ℚ)
    (hd : ∀ P ∈ C.support, ∀ (_ : IsProper (P.idealSheaf.subschemeι ≫ s))
      (hdP : topologicalKrullDim P.idealSheaf.subscheme ≤ 1),
      (E.degreeOn k s P.idealSheaf.subschemeι hdP hE : ℚ) = d P) :
    (E.degreeOn k s C.suppIdeal.subschemeι hdimC hE : ℚ) = ∑ P ∈ C.support, d P := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI := hE.isInvertibleModule_divisorialSheaf
  haveI : IsReduced C.suppIdeal.subscheme := by
    rw [DivisorWithCoeffs.suppIdeal]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hle : ∀ P ∈ C.support, C.suppIdeal ≤ P.idealSheaf := fun P hP =>
    suppIdeal_le_idealSheaf C hP
  have hZ : ∀ P ∈ C.support, topologicalKrullDim P.idealSheaf.subscheme = 1 := fun P hP => by
    rw [topologicalKrullDim_idealSheaf_subscheme]; exact hdim P hP
  have hci : ∀ P (hP : P ∈ C.support),
      IsClosedImmersion (Scheme.IdealSheafData.inclusion (hle P hP)) := fun P hP => by
    have h : IsClosedImmersion (Scheme.IdealSheafData.inclusion (hle P hP) ≫
        C.suppIdeal.subschemeι) := by
      rw [Scheme.IdealSheafData.inclusion_subschemeι]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ C.suppIdeal.subschemeι
  have hgen : ∀ P : MMP.Mori.PrimeDivisor X,
      haveI := P.integral
      P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := by
    intro P
    haveI := P.integral
    refine IsGenericPoint.eq (MMP.Resolution.closure_subschemeι_genericPoint P.idealSheaf) ?_
    change closure {P.genericPoint} = (P.support : Set X)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  let g : {P // P ∈ C.support} → genericPointsOne C.suppIdeal.subscheme := fun P =>
    haveI := P.1.integral
    haveI := hci P.1 P.2
    ⟨Scheme.IdealSheafData.inclusion (hle P.1 P.2) (genericPoint P.1.idealSheaf.subscheme),
      genericPoint_mem_genericPointsOne _ hdimC (hZ P.1 P.2)⟩
  have hgι : ∀ P, C.suppIdeal.subschemeι (g P).1 = P.1.genericPoint := by
    intro P
    haveI := P.1.integral
    change C.suppIdeal.subschemeι (Scheme.IdealSheafData.inclusion (hle P.1 P.2)
      (genericPoint P.1.idealSheaf.subscheme)) = _
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
    exact hgen P.1
  have hinj : Function.Injective g := fun P Q h => Subtype.ext
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hgι P).symm.trans ((congrArg (⇑C.suppIdeal.subschemeι)
        (congrArg Subtype.val h)).trans (hgι Q))))
  have hsurj : Function.Surjective g := by
    rintro ⟨ξ, hξ⟩
    have hmem : C.suppIdeal.subschemeι ξ ∈ (C.supp : Set X) := by
      rw [← DivisorWithCoeffs.coe_support_suppIdeal, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨ξ, rfl⟩
    obtain ⟨P, hP, hzP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hP' : P ∈ C.support := Finsupp.mem_support_iff.mpr hP
    refine ⟨⟨P, hP'⟩, Subtype.ext ?_⟩
    have hsp : P.genericPoint ⤳ C.suppIdeal.subschemeι ξ := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hzP
    rw [← hgι ⟨P, hP'⟩] at hsp
    have hsp' : (g ⟨P, hP'⟩).1 ⤳ ξ :=
      C.suppIdeal.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hsp
    have hmax := isMax_of_mem_genericPoints ξ (mem_genericPointsOne_iff.mp hξ).1
    have h := Scheme.le_iff_specializes.mpr hsp'
    exact (hsp'.antisymm (Scheme.le_iff_specializes.mp (hmax h))).eq
  let e := Equiv.ofBijective g ⟨hinj, hsurj⟩
  have h1 : E.degreeOn k s C.suppIdeal.subschemeι hdimC hE =
      ∑ᶠ ξ : genericPointsOne C.suppIdeal.subscheme,
        componentDegree k (C.suppIdeal.subschemeι ≫ s) hdimC
          ((Scheme.Modules.pullback C.suppIdeal.subschemeι).obj E.divisorialSheaf) 1 ξ := by
    change invertibleCurveDegree k _ hdimC _ = _
    rw [invertibleCurveDegree_eq_curveDegree_one,
      Stacks.AlgebraicGeometry.ComponentDegreeDevissage.curveDegree_eq_finsum_componentDegree,
      finsum_componentMultiplicity_mul_of_isReduced]
  rw [h1, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Int.cast_sum,
    ← Finset.sum_coe_sort C.support d]
  refine Fintype.sum_congr _ _ fun P => ?_
  haveI := P.1.integral
  haveI := hci P.1 P.2
  have hPp : IsProper (P.1.idealSheaf.subschemeι ≫ s) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι (hle P.1 P.2), Category.assoc]
    infer_instance
  rw [← hd P.1 P.2 hPp (hZ P.1 P.2).le]
  congr 1
  have h2 := curveDegree_pullback_eq_componentDegree k (C.suppIdeal.subschemeι ≫ s) hdimC
    (Scheme.IdealSheafData.inclusion (hle P.1 P.2)) (hZ P.1 P.2)
    ((Scheme.Modules.pullback C.suppIdeal.subschemeι).obj E.divisorialSheaf) 1
  change componentDegree k _ hdimC _ 1 (g P) = _
  rw [show g P = ⟨_, genericPoint_mem_genericPointsOne _ hdimC (hZ P.1 P.2)⟩ from rfl, ← h2,
    ← invertibleCurveDegree_eq_curveDegree_one]
  refine (invertibleCurveDegree_eq_of_iso k _ _
    (L := (Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion (hle P.1 P.2))).obj
      ((Scheme.Modules.pullback C.suppIdeal.subschemeι).obj E.divisorialSheaf))
    (L' := (Scheme.Modules.pullback (Scheme.IdealSheafData.inclusion (hle P.1 P.2) ≫
      C.suppIdeal.subschemeι)).obj E.divisorialSheaf)
    ((Scheme.Modules.pullbackComp (Scheme.IdealSheafData.inclusion (hle P.1 P.2))
        C.suppIdeal.subschemeι).app E.divisorialSheaf)).trans ?_
  haveI : IsProper ((Scheme.IdealSheafData.inclusion (hle P.1 P.2) ≫
      C.suppIdeal.subschemeι) ≫ s) := by rw [Category.assoc]; infer_instance
  rw [invertibleCurveDegree_congr_hom (Category.assoc _ _ _).symm,
    invertibleCurveDegree_pullback_congr (Scheme.IdealSheafData.inclusion_subschemeι _)]
  rfl

/-- **Intersection numbers are additive over the components of a reduced curve**: if `C` has
reduced support proper over `k` with one-dimensional components `P`, and `(D · P) = x_P`, then
`(D · C_red) = ∑_P x_P`. -/
private theorem isIntersectionNumber_suppIdeal_sum {X : Scheme.{w}} {s : X ⟶ Spec (.of k)}
    [QuasiCompact s] [IsLocallyNoetherian X] [IsNormal X] (C : Divisor X)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ s))
    (hdim : ∀ P ∈ C.support, topologicalKrullDim P.support = 1) {D : QDivisor X}
    (hD : D.IsQCartier) {x : MMP.Mori.PrimeDivisor X → ℚ}
    (h : ∀ P ∈ C.support, IsIntersectionNumber s D P.idealSheaf (x P)) :
    IsIntersectionNumber s D C.suppIdeal (∑ P ∈ C.support, x P) := by
  classical
  have hdimC : topologicalKrullDim C.suppIdeal.subscheme ≤ 1 := by
    rw [topologicalKrullDim_suppIdeal_subscheme_eq, DivisorWithCoeffs.coe_supp]
    exact topologicalKrullDim_biUnion_le C.support (fun E => E.idealSheaf.support.isClosed)
      (fun E hE => (hdim E hE).le)
  refine ⟨hCp, hdimC, hD, ?_⟩
  haveI := hCp
  have hF := QDivisor.isCartierDivisor_cartierIndex_smul hD
  have hm : (D.cartierIndex hD : ℚ) ≠ 0 := by
    exact_mod_cast (QDivisor.cartierIndex_pos hD).ne'
  have key := degreeOn_suppIdeal_eq_sum C hdimC hdim _ hF.isCartier_toDivisor
    (fun P => x P * D.cartierIndex hD) (by
      intro P hP hPp hdP
      haveI := hPp
      obtain ⟨_, _, _, hx⟩ := h P hP
      rw [← hx, QDivisor.intersectionNumber_eq_of_toQDivisor_eq k s _ _ D _ _
        hF.isCartier_toDivisor hF.toQDivisor_toDivisor]
      field_simp)
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k s _ hdimC D hD _ hF.isCartier_toDivisor
    hF.toQDivisor_toDivisor, key, ← Finset.sum_mul, mul_div_cancel_right₀ _ hm]

/-- **Symmetry of intersection numbers of two distinct curves on a smooth surface**: both are the
sum of the local intersection numbers over `P ∩ Q`. -/
private theorem isIntersectionNumber_single_comm {X : Scheme.{w}} {s : X ⟶ Spec (.of k)}
    [QuasiCompact s] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsVariety k s) (hXs : MMP.Mori.IsSmoothScheme s)
    (hXd : topologicalKrullDim X = 2) {P Q : MMP.Mori.PrimeDivisor X} (hPQ : P ≠ Q)
    (hP : IsProper (P.idealSheaf.subschemeι ≫ s)) (hQ : IsProper (Q.idealSheaf.subschemeι ≫ s))
    {x : ℚ} (h : IsIntersectionNumber s (Finsupp.single P 1) Q.idealSheaf x) :
    IsIntersectionNumber s (Finsupp.single Q 1) P.idealSheaf x := by
  obtain ⟨-, h1, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hX hXs hXd hPQ.symm hQ
  obtain ⟨-, h2, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hX hXs hXd hPQ hP
  rw [h.unique h1]
  convert h2 using 1
  rw [Set.inter_comm]
  congr 1
  funext z
  rw [MMP.Mori.localIntersectionNumber, MMP.Mori.localIntersectionNumber, sup_comm]

set_option hygiene false in
/-- The blow-up `π : Y' ⟶ Y` of the reduced closed point `y`. -/
local notation "πy" => blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
  (⟨{y}, hy⟩ : TopologicalSpace.Closeds _))

set_option hygiene false in
/-- The blow-up `Y'` of the reduced closed point `y`. -/
local notation "Y'y" => blowUp (Scheme.IdealSheafData.vanishingIdeal
  (⟨{y}, hy⟩ : TopologicalSpace.Closeds _))

open MMP.Threefold.Resolution in
/-- The blow-up of a closed point of a smooth surface is a surface. -/
private theorem topologicalKrullDim_blowUp_singleton [IsAlgClosed k]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    topologicalKrullDim Y'y = 2 := by
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  exact topologicalKrullDim_blowUp sY _ (isSmoothBlowup_vanishingIdeal_singleton sY hYs hy)
    (isIrreducible_support_vanishingIdeal_singleton hy)
    (one_le_codimension_vanishingIdeal_singleton hYd hy) (d := 2) (by exact_mod_cast hYd)

open MMP.Threefold.Resolution in
/-- **The strict transforms of curves under a point blow-up**: every prime divisor `E` of `Y` has
a strict transform `T E`, an injective assignment never hitting the exceptional curve `F`. -/
private theorem exists_strictTransform_blowUp_singleton [IsAlgClosed k] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : MMP.Mori.IsVariety k sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y'y] [IsNormal Y'y]
    {F : MMP.Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :
    ∃ T : MMP.Mori.PrimeDivisor Y → MMP.Mori.PrimeDivisor Y'y,
      (∀ E, inverseTransformPrimeDivisor πy E = some (T E)) ∧ Function.Injective T ∧
        ∀ E, T E ≠ F := by
  haveI : IsIntegral Y := hY.toIsIntegral
  have hV : ∀ x : Y, x ∈ biregularLocus πy ↔ x ≠ y := fun x =>
    ⟨fun hx hxy => notMem_biregularLocus_blowUpToBase_singleton hY hYd hy hF
      (Eq.subst (motive := fun z => z ∈ biregularLocus πy) hxy hx),
      mem_biregularLocus_blowUpToBase_singleton hy⟩
  have hne : ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ≠ y := by
    intro E h
    have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint E
    have h2 := coheight_eq_two_of_isClosed hY hYd hy
    rw [h] at h1
    rw [h1] at h2
    exact absurd h2 (by decide)
  choose T hT hTη using fun E =>
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := πy) E ((hV _).mpr (hne E))
  refine ⟨T, hT, fun E₁ E₂ h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
    have h1 := hTη E₁
    rw [h, hTη E₂] at h1
    exact h1.symm), fun E hE => hne E ?_⟩
  rw [← hTη E, hE]
  exact (mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF _).mp (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)

open MMP.Threefold.Resolution in
/-- **The exceptional curve of a point blow-up**: `F` is proper, `F² = -1`, and `(π^* D · F) = 0`
for every divisor `D` of `Y`. -/
private theorem isIntersectionNumber_exceptional [IsAlgClosed k] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) {F : MMP.Mori.PrimeDivisor Y'y}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    [IsLocallyNoetherian Y'y] [IsNormal Y'y] [QuasiCompact (πy ≫ sY)] :
    haveI := compactSpace_blowUp_singleton hY hYd hy
    IsProper (F.idealSheaf.subschemeι ≫ πy ≫ sY) ∧
      IsIntersectionNumber (πy ≫ sY) (Divisor.toQDivisor (Finsupp.single F 1)) F.idealSheaf
        (-1) ∧
      ∀ D : Divisor Y, IsIntersectionNumber (πy ≫ sY)
        (Divisor.toQDivisor (D.pullback (f := πy) (MMP.Fourfold.isCartier_of_isSmoothScheme hYs D)
          (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy D))) F.idealSheaf 0 := by
  have hYsm := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have hvar := isVariety_blowUp_singleton hY hYd hy
  haveI : IsIntegral Y'y := hvar.toIsIntegral
  haveI : IsSeparated sY := hY.toIsSeparated
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := compactSpace_blowUp_singleton hY hYd hy
  obtain ⟨-, -, -, -, F₀, hF₀, -, hprop, hself⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hY hYs hYd hy
  have hFF₀ : F₀ = F := MMP.Mori.PrimeDivisor.ext_idealSheaf (by rw [hF₀, hF])
  subst hFF₀
  set F' : ProperCurve (πy ≫ sY) := ⟨F₀.genericPoint, hprop⟩
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hy hF
  refine ⟨?_, ?_, fun D => ?_⟩
  · have h := hprop.isProper
    change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({F₀.genericPoint} : Set _))).subschemeι ≫ _) at h
    rwa [MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf] at h
  · have h := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (Finsupp.single F₀ 1))
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hYsm F₀) F' F₀ rfl
    rw [hself F' rfl] at h
    exact h
  · have hD := MMP.Fourfold.isCartier_of_isSmoothScheme hYs D
    have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy D
    have hcon : F'.IsContractedBy πy := by
      intro q hq
      change q ∈ closure {F₀.genericPoint} at hq
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hq
      rw [(hFmem q).mp hq, (hFmem _).mp (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)]
    have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy (sY := sY)
      (sX := πy ≫ sY) πy rfl hD hB F' hcon
    have hD'c := hD.isCartier_pullback πy hB
    haveI : IsProper (F'.ι ≫ πy ≫ sY) := ProperCurve.isProper_ι_comp F'
    have hpb := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (Divisor.pullback
      (f := πy) _ hD hB)) (QDivisor.isQCartier_toQDivisor hD'c) F' F₀ rfl
    rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD'c, h0, Int.cast_zero] at hpb
    exact hpb

open MMP.Threefold.Resolution in
/-- **Projection formula for a strict transform.** For a divisor `D` of `Y`, a prime divisor `P`
proper over `k` and its strict transform `P'`, `(π^* D · P') = (D · P)`: the push-forward of
`[P']` is `[P]`, `π` being an isomorphism at the generic point of `P'`. -/
private theorem isIntersectionNumber_pullback_of_inverseTransform [IsAlgClosed k]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] (hY : MMP.Mori.IsVariety k sY)
    (hYs : MMP.Mori.IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2) {y : Y}
    (hy : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y'y] [IsNormal Y'y]
    [QuasiCompact (πy ≫ sY)] (D : Divisor Y) {P : MMP.Mori.PrimeDivisor Y}
    {P' : MMP.Mori.PrimeDivisor Y'y} (hP' : inverseTransformPrimeDivisor πy P = some P')
    (hPp : IsProper (P.idealSheaf.subschemeι ≫ sY))
    (hP'p : IsProper (P'.idealSheaf.subschemeι ≫ πy ≫ sY)) {x : ℚ}
    (h : IsIntersectionNumber sY (Divisor.toQDivisor D) P.idealSheaf x) :
    haveI := compactSpace_blowUp_singleton hY hYd hy
    IsIntersectionNumber (πy ≫ sY)
      (Divisor.toQDivisor (D.pullback (f := πy) (MMP.Fourfold.isCartier_of_isSmoothScheme hYs D)
        (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy D))) P'.idealSheaf x := by
  have hvar := isVariety_blowUp_singleton hY hYd hy
  haveI : IsIntegral Y'y := hvar.toIsIntegral
  haveI : IsSeparated sY := hY.toIsSeparated
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := compactSpace_blowUp_singleton hY hYd hy
  have hD := MMP.Fourfold.isCartier_of_isSmoothScheme hYs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy D
  have hdP := topologicalKrullDim_support_primeDivisor hY hYd P
  have hdP' := topologicalKrullDim_support_primeDivisor hvar
    (topologicalKrullDim_blowUp_singleton hY hYs hYd hy) P'
  let E : ProperCurve sY := ⟨P.genericPoint, isProperCurve_genericPoint P hPp hdP⟩
  let E' : ProperCurve (πy ≫ sY) := ⟨P'.genericPoint, isProperCurve_genericPoint P' hP'p hdP'⟩
  obtain ⟨hmap, hV⟩ := map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP'
  have hpt : πy E'.point = E.point := hmap
  have hproj := Divisor.degreeOn_pullback_eq_degree_pushforward (sY := sY)
    (sX := πy ≫ sY) πy rfl hD hB E'
  have hprop : IsProperCurve sY (πy E'.point) := by rw [hpt]; exact E.isProperCurve
  have hres : residueFieldDegree πy E'.point = 1 :=
    MMP.Flips.residueFieldDegree_eq_one_of_isIso_stalkMap _ _
      (isIso_stalkMap_of_mem_biregularLocus πy hV)
  have hcurve : (⟨πy E'.point, hprop⟩ : ProperCurve sY) = E := ProperCurve.ext hpt
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint] at hproj
  simp only [hprop, ↓reduceDIte] at hproj
  rw [hres, hcurve, OneCycle.degree_apply, Finsupp.sum_single_index (by simp), Nat.cast_one,
    one_mul] at hproj
  haveI : IsProper (E.ι ≫ sY) := ProperCurve.isProper_ι_comp E
  haveI : IsProper (E'.ι ≫ πy ≫ sY) := ProperCurve.isProper_ι_comp E'
  have h1 := isIntersectionNumber_of_properCurve (Divisor.toQDivisor D)
    (QDivisor.isQCartier_toQDivisor hD) E P rfl
  rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ D hD] at h1
  rw [h.unique h1]
  have hD' := hD.isCartier_pullback πy hB
  have h2 := isIntersectionNumber_of_properCurve (Divisor.toQDivisor (D.pullback hD hB))
    (QDivisor.isQCartier_toQDivisor hD') E' P' rfl
  rw [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', hproj] at h2
  exact h2

/-- Under the hypotheses of `exists_affineOpen_ideal_suppIdeal_eq_span_prod`, the ideal of the
reduced support of a divisor in a local ring is the product of the ideals of its components. -/
private theorem stalk_suppIdeal_eq_prod [IsLocallyNoetherian Y] [IsNormal Y]
    (hloc : ∀ (P : MMP.Mori.PrimeDivisor Y) (x : Y), ∃ U : Y.affineOpens, x ∈ (U : Y.Opens) ∧
      ∃ (g : Γ(Y, U)) (φ : (RationalFunctions Y)ˣ),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (U : Y.Opens)),
          (φ : RationalFunctions Y) Z = Y.presheaf.germ U _ hZ g) ∧
        Divisor.IsLocalEquation (Finsupp.single P 1) U φ ∧
        P.idealSheaf.ideal U = Ideal.span {g})
    (C : Divisor Y) (x : Y) :
    AlgebraicGeometry.IdealSheafData.stalk C.suppIdeal x =
      ∏ P ∈ C.support, AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf x := by
  obtain ⟨V, hxV, gP, φP, hiP, hC⟩ := exists_affineOpen_ideal_suppIdeal_eq_span_prod hloc C x
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ C.suppIdeal x V hxV, hC, Ideal.map_span,
    Set.image_singleton, map_prod, ← Ideal.prod_span_singleton]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf x V hxV, (hiP P hP).2.2,
    Ideal.map_span, Set.image_singleton]

/-- In a discrete valuation ring the order of ideals is additive. -/
private theorem idealOrder_mul_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (I J : Ideal R) :
    MMP.Resolution.idealOrder (I * J) =
      MMP.Resolution.idealOrder I + MMP.Resolution.idealOrder J := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, rfl⟩ := Submodule.IsPrincipal.principal I
  obtain ⟨b, rfl⟩ := Submodule.IsPrincipal.principal J
  change MMP.Resolution.idealOrder (Ideal.span {a} * Ideal.span {b}) =
    MMP.Resolution.idealOrder (Ideal.span {a}) + MMP.Resolution.idealOrder (Ideal.span {b})
  rw [Ideal.span_singleton_mul_span_singleton]
  by_cases ha : a = 0
  · subst ha
    simp [Ideal.span_singleton_eq_bot.2 rfl,
      MMP.Proofs.lem_mmp_threefold_surface_blowup_genus_drop.idealOrder_bot]
  by_cases hb : b = 0
  · subst hb
    simp [Ideal.span_singleton_eq_bot.2 rfl,
      MMP.Proofs.lem_mmp_threefold_surface_blowup_genus_drop.idealOrder_bot]
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨l, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rw [show (u : R) * ϖ ^ n * ((v : R) * ϖ ^ l) = ((u * v : Rˣ) : R) * ϖ ^ (n + l) by
      push_cast; ring,
    MMP.Threefold.Resolution.idealOrder_span_unit_mul_pow hϖ,
    MMP.Threefold.Resolution.idealOrder_span_unit_mul_pow hϖ,
    MMP.Threefold.Resolution.idealOrder_span_unit_mul_pow hϖ]
  push_cast
  rfl

/-- In a discrete valuation ring the order of a finite product of ideals is the sum. -/
private theorem idealOrder_prod_of_isDiscreteValuationRing {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    MMP.Resolution.idealOrder (∏ i ∈ s, I i) = ∑ i ∈ s, MMP.Resolution.idealOrder (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MMP.Threefold.Resolution.idealOrder_top (R := R)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, idealOrder_mul_of_isDiscreteValuationRing, ih]

open MMP.Resolution MMP.Threefold.Resolution in
/-- **The multiplicity of a reduced curve at a point** is the sum of the multiplicities of its
components: `mult_y C = ∑_P mult_y P`, the order of the ideal of `C` in `𝒪_{Y,y}` being the
order of the product of local equations of the components. -/
private theorem multiplicityAt_eq_of_multAt_suppIdeal [IsAlgClosed k] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    {y : Y} (hy : IsClosed ({y} : Set Y)) {m : ℕ}
    (hm : MMP.Resolution.multAt C.suppIdeal y = m) : C.multiplicityAt y = (m : ℤ) := by
  classical
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.toQuasiCompact
  haveI hYsm : Smooth sY := (isSmoothScheme_iff sY).mp hYs
  haveI : IsSmoothVariety k sY := { toIsVariety := hY, toSmooth := hYsm }
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨-, hloc, -, -, -, -⟩ := Divisor.cartier_weil_dictionary_of_isSmoothVariety k sY
  -- the order along the exceptional divisor of the blow-up of `y` is `mult_y`
  have hsb := isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := isIrreducible_support_vanishingIdeal_singleton hy
  have hcodim := one_le_codimension_vanishingIdeal_singleton hYd hy
  have hYs' := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').2
  haveI : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :=
    (isVariety_blowUp_singleton hY hYd hy).toIsIntegral
  set Fe := exceptionalPrimeDivisor sY _ hsb hirr hcodim with hFe
  have hy' : hirr.genericPoint = y := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    have h2 : closure ((Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ :
        TopologicalSpace.Closeds Y)).support : Set Y) = closure {y} := by
      rw [support_vanishingIdeal_singleton hy]
    rw [h2] at h1
    exact h1.eq isGenericPoint_closure
  have key : ∀ J : Y.IdealSheafData, multAt J y = idealOrder
      ((AlgebraicGeometry.IdealSheafData.stalk J
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) Fe.genericPoint)).map
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).stalkMap
          Fe.genericPoint).hom) := by
    intro J
    have hord := orderAlong_comap_blowUpToBase_eq sY _ hsb hirr hcodim J
    simp only [orderAlong, multAt] at hord
    rw [isIrreducible_genericPoint_eq _ (isIrreducible_support_exceptionalPrimeDivisor sY _ hsb
      hirr hcodim), hy', AlgebraicGeometry.IdealSheafData.stalk_comap] at hord
    rw [multAt]
    exact hord.symm
  haveI : IsDiscreteValuationRing
      ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).presheaf.stalk Fe.genericPoint) :=
    MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing (D := Fe)
  have hP : ∀ P : MMP.Mori.PrimeDivisor Y, P.multiplicityAt y = idealOrder
      ((AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) Fe.genericPoint)).map
        ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).stalkMap
          Fe.genericPoint).hom) := by
    intro P
    rw [← key]
    simp only [MMP.Mori.PrimeDivisor.multiplicityAt, multAt, idealOrder,
      Scheme.IdealSheafData.stalkIdeal_eq_stalk]
  have hsum : multAt C.suppIdeal y = ∑ P ∈ C.support, P.multiplicityAt y := by
    rw [key, stalk_suppIdeal_eq_prod hloc, ← Ideal.mapHom_apply, map_prod,
      idealOrder_prod_of_isDiscreteValuationRing]
    exact Finset.sum_congr rfl fun P _ => (hP P).symm
  have hfin : ∀ P : MMP.Mori.PrimeDivisor Y,
      P.multiplicityAt y = ((P.multiplicityAt y).toNat : ℕ∞) := fun P =>
    (ENat.coe_toNat (multiplicityAt_ne_top P
      (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hYs P) y)).symm
  rw [hm, Finset.sum_congr rfl fun P _ => hfin P, ← Nat.cast_sum] at hsum
  have hm' : m = ∑ P ∈ C.support, (P.multiplicityAt y).toNat := by exact_mod_cast hsum
  rw [DivisorWithCoeffs.multiplicityAt, Finsupp.sum, hm']
  push_cast
  exact Finset.sum_congr rfl fun P hP => by rw [hC P hP, nsmul_eq_mul, mul_one]

open MMP.Threefold.Resolution in
/-- **The adjunction defect is invariant under a point blow-up.** With `π : Y' ⟶ Y` the blow-up
of a closed point `y` of multiplicity `m` of the reduced curve `C`, `F` the exceptional curve,
`K' = π^*K + F` and `C' = π⁻¹_* C = π^*C - mF`:
`(K' + C') · C' = (K + C) · C - m(m-1)`. This is the projection formula for the birational
morphism `C' ⟶ C` together with `F · C' = m` and `F² = -1`. -/
private theorem isIntersectionNumber_of_blowUp_singleton
    [IsAlgClosed k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY))
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ (C.supp : Set Y)) {m : ℕ}
    (hm : MMP.Resolution.multAt C.suppIdeal y = m)
    {F : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))}
    (hF : F.idealSheaf = exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))]
    [QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)] :
    haveI := compactSpace_blowUp_singleton hY hYd hy
    ∀ n : ℚ, IsIntersectionNumber
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
        (Divisor.toQDivisor
          (Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
              K (MMP.Fourfold.isCartier_of_isSmoothScheme hYs K)
              (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy K) +
            Finsupp.single F 1 +
            inverseTransformDivisor
              (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C))
        (inverseTransformDivisor
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _).suppIdeal
        n →
      IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
        (n + (m : ℚ) * ((m : ℚ) - 1)) := by
  classical
  intro n hn
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI := compactSpace_blowUp_singleton hY hYd hy
  have hY' := isVariety_blowUp_singleton hY hYd hy
  have hYs' := isSmoothScheme_blowUp_singleton hY hYs hYd hy
  have hYd' := topologicalKrullDim_blowUp_singleton hY hYs hYd hy
  obtain ⟨hFp, hFF, hF0⟩ := isIntersectionNumber_exceptional hY hYs hYd hy hF
  obtain ⟨T, hT, hTinj, hTF⟩ := exists_strictTransform_blowUp_singleton hY hYd hy hF
  set S := C.support with hS
  set C' := (inverseTransformDivisor
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C : Divisor _) with hC'
  obtain ⟨hC'sum, hC'supp, -⟩ := inverseTransformDivisor_of_reduced hT hTinj C hC
  rw [← hC'] at hC'sum hC'supp
  have hC'p : IsProper (C'.suppIdeal.subschemeι ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) := hn.1
  have hPp : ∀ P ∈ S, IsProper (P.idealSheaf.subschemeι ≫ sY) := fun P hP =>
    isProper_idealSheaf_of_mem_support C hCp hP
  have hTp : ∀ P ∈ S, IsProper ((T P).idealSheaf.subschemeι ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) := fun P hP =>
    isProper_idealSheaf_of_mem_support C' hC'p (by rw [hC'supp]; exact Finset.mem_image_of_mem T hP)
  have hdimY : ∀ P ∈ C.support, topologicalKrullDim P.support = 1 := fun P _ =>
    topologicalKrullDim_support_primeDivisor hY hYd P
  have hdimY' : ∀ P ∈ C'.support, topologicalKrullDim P.support = 1 := fun P _ =>
    topologicalKrullDim_support_primeDivisor hY' hYd' P
  -- the intersection numbers with the components
  choose! a ha using fun P (hP : P ∈ S) =>
    exists_isIntersectionNumber_primeDivisor hY hYs hYd (Divisor.toQDivisor K) P (hPp P hP)
  choose! b hb using fun P (hP : P ∈ S) =>
    exists_isIntersectionNumber_primeDivisor hY hYs hYd (Divisor.toQDivisor C) P (hPp P hP)
  choose! c hc using fun P (hP : P ∈ S) =>
    exists_isIntersectionNumber_primeDivisor hY' hYs' hYd' (Finsupp.single (T P) (1 : ℚ)) F hFp
  have hsingle : ∀ E : MMP.Mori.PrimeDivisor
      (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)),
      Divisor.toQDivisor (Finsupp.single E 1) = Finsupp.single E (1 : ℚ) := fun E => by
    rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
  -- on `Y`
  have hKC := isIntersectionNumber_suppIdeal_sum C hCp hdimY
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs _) ha
  have hCC := isIntersectionNumber_suppIdeal_sum C hCp hdimY
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs _) hb
  -- on `Y'`
  have hreindex : ∀ x : MMP.Mori.PrimeDivisor Y → ℚ,
      ∑ Q ∈ C'.support, (∑ P ∈ S, if T P = Q then x P else 0) = ∑ P ∈ S, x P := by
    intro x
    rw [hC'supp, Finset.sum_image (fun _ _ _ _ h => hTinj h)]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Finset.sum_eq_single_of_mem P hP (fun P' _ hP' => if_neg fun h => hP' (hTinj h)),
      if_pos rfl]
  have hcomp : ∀ (D : QDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)))
      (x : MMP.Mori.PrimeDivisor Y → ℚ),
      (∀ P ∈ S, IsIntersectionNumber
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) D
        (T P).idealSheaf (x P)) →
      IsIntersectionNumber (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
        D C'.suppIdeal (∑ P ∈ S, x P) := by
    intro D x hx
    rw [← hreindex]
    refine isIntersectionNumber_suppIdeal_sum C' hC'p hdimY'
      (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs' _) fun Q hQ => ?_
    rw [hC'supp] at hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    rw [Finset.sum_eq_single_of_mem P hP (fun P' _ hP' => if_neg fun h => hP' (hTinj h)),
      if_pos rfl]
    exact hx P hP
  have hKC' := hcomp _ a fun P hP =>
    isIntersectionNumber_pullback_of_inverseTransform hY hYs hYd hy K (hT P) (hPp P hP)
      (hTp P hP) (ha P hP)
  have hCC' := hcomp _ b fun P hP =>
    isIntersectionNumber_pullback_of_inverseTransform hY hYs hYd hy C (hT P) (hPp P hP)
      (hTp P hP) (hb P hP)
  have hFC' := hcomp (Divisor.toQDivisor (Finsupp.single F 1)) c fun P hP => by
    rw [hsingle]
    exact isIntersectionNumber_single_comm hY' hYs' hYd' (hTF P) (hTp P hP) hFp (hc P hP)
  -- `F · C' = mult_y C`
  have hCP := Divisor.IsPullback.pullback_eq (MMP.Fourfold.isCartier_of_isSmoothScheme hYs C)
    (MMP.Threefold.Resolution.isPullback_blowUp_singleton hY hYs hYd hy hF C
      (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy C))
  rw [← hC'] at hCP
  have he : Divisor.toQDivisor (Finsupp.single F (C.multiplicityAt y)) =
      (C.multiplicityAt y : ℚ) • Divisor.toQDivisor (Finsupp.single F 1) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single, MMP.Threefold.Resolution.toQDivisor_single,
      Finsupp.smul_single, smul_eq_mul, Int.cast_one, mul_one]
  have hμ : ∑ P ∈ S, c P = (C.multiplicityAt y : ℚ) := by
    have h1 := hF0 C
    have hCF : IsIntersectionNumber
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY)
        (Divisor.toQDivisor C') F.idealSheaf (∑ P ∈ S, c P) := by
      rw [hC'sum, map_sum]
      simp_rw [hsingle]
      exact MMP.Mori.isIntersectionNumber_sum S (MMP.Flips.isIntersectionNumber_zero hFF) hc
    have h2 := MMP.Flips.isIntersectionNumber_add hCF
      (hFF.smul (C.multiplicityAt y : ℚ) (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs' _))
    rw [← he, ← map_add, ← hCP] at h2
    have := h1.unique h2
    linarith
  -- the intersection number on `Y'`
  have hA : Divisor.toQDivisor
      (Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
          K (MMP.Fourfold.isCartier_of_isSmoothScheme hYs K)
          (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy K) +
        Finsupp.single F 1 + C') =
      Divisor.toQDivisor
          (Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
            K (MMP.Fourfold.isCartier_of_isSmoothScheme hYs K)
            (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy K)) +
        Divisor.toQDivisor
          (Divisor.pullback (f := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩))
            C (MMP.Fourfold.isCartier_of_isSmoothScheme hYs C)
            (blowUpToBase_componentGenericPoint_notMem_supp hY hYd hy C)) +
        (1 - (C.multiplicityAt y : ℚ)) • Divisor.toQDivisor (Finsupp.single F 1) := by
    rw [hCP, map_add, map_add, map_add, he, sub_smul, one_smul]
    abel
  have hval := MMP.Flips.isIntersectionNumber_add (MMP.Flips.isIntersectionNumber_add hKC' hCC')
    (hFC'.smul (1 - (C.multiplicityAt y : ℚ)) (MMP.Fourfold.isQCartier_of_isSmoothScheme hYs' _))
  rw [← hA] at hval
  have hn' := hn.unique hval
  have hμm := multiplicityAt_eq_of_multAt_suppIdeal hY hYs hYd C hC hy hm
  rw [map_add]
  convert MMP.Flips.isIntersectionNumber_add hKC hCC using 1
  rw [hn', hμ, hμm]
  push_cast
  ring

/-- **One blow-up step.** Blowing up a closed point `y` of multiplicity `m` of a reduced proper
curve `C` on a smooth surface `Y` gives a smooth surface `Y'` with canonical divisor
`K' = π^*K + F` and the strict transform `C'`, a reduced proper curve with as many components as
`C`, with `χ(𝒪_{C'}) = χ(𝒪_C) + m(m-1)/2` and `(K' + C') · C' = (K + C) · C - m(m-1)`. -/
private theorem exists_blowUp_step
    [IsAlgClosed k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY))
    {y : Y} (hy : IsClosed ({y} : Set Y)) (hyC : y ∈ (C.supp : Set Y)) {m : ℕ}
    (hm : MMP.Resolution.multAt C.suppIdeal y = m) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    ∃ (Y' : Scheme.{w}) (sY' : Y' ⟶ Spec (.of k)) (_ : QuasiCompact sY')
      (_ : IsLocallyNoetherian Y') (_ : IsNormal Y'),
      MMP.Mori.IsVariety k sY' ∧ MMP.Mori.IsSmoothScheme sY' ∧ topologicalKrullDim Y' = 2 ∧
      ∃ K' : Divisor Y', K'.IsCanonicalDivisor sY' 2 ∧
      ∃ C' : Divisor Y', (∀ E ∈ C'.support, C' E = 1) ∧
      ∃ hCp' : IsProper (C'.suppIdeal.subschemeι ≫ sY'),
        haveI := hCp'
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (C'.suppIdeal.subschemeι ≫ sY')
        C'.support.card = C.support.card ∧
        eulerCharacteristic k (C'.suppIdeal.subschemeι ≫ sY')
            (SheafOfModules.unit C'.suppIdeal.subscheme.ringCatSheaf) =
          eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
            (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf) + (m.choose 2 : ℤ) ∧
        ∀ n : ℚ, IsIntersectionNumber sY' (Divisor.toQDivisor (K' + C')) C'.suppIdeal n →
          IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
            (n + (m : ℚ) * ((m : ℚ) - 1)) := by
  classical
  haveI : IsIntegral Y := hY.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  have hsmB := MMP.Threefold.Resolution.isSmoothBlowup_vanishingIdeal_singleton sY hYs hy
  have hirr := MMP.Threefold.Resolution.isIrreducible_support_vanishingIdeal_singleton hy
  have hc1 := MMP.Threefold.Resolution.one_le_codimension_vanishingIdeal_singleton hYd hy
  obtain ⟨hYs', F, hF, -, -⟩ :=
    MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal sY _ hsmB hirr
      hc1
  have hY' := MMP.Threefold.Resolution.isVariety_blowUp_singleton hY hYd hy
  have hYd' := MMP.Threefold.Resolution.topologicalKrullDim_blowUp sY _ hsmB hirr hc1
    (d := 2) (by exact_mod_cast hYd)
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYs').2
  haveI hqc' : QuasiCompact
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩) ≫ sY) :=
    hY'.toQuasiCompact
  have hK' := MMP.Threefold.Resolution.isCanonicalDivisor_pullback_add_single_blowUp_singleton
    hY hYs hYd hy hF hK
  obtain ⟨hC'1, hcard, hsupp⟩ :=
    inverseTransformDivisor_blowUp_singleton_reduced hY hYs hYd C hC hy
  have htr := isIntersectionNumber_of_blowUp_singleton hY hYs hYd hK C hC hCp hy hyC hm hF
  -- the genus drop
  have hcomp : ∀ Z ∈ irreducibleComponents (C.supp : Set Y), topologicalKrullDim Z = 1 :=
    fun Z hZ => topologicalKrullDim_of_mem_irreducibleComponents_supp hY hYd C hZ
  haveI : IsProper ((Scheme.IdealSheafData.vanishingIdeal C.supp).subschemeι ≫ sY) := hCp
  obtain ⟨hp', hg⟩ := MMP.Threefold.Resolution.arithmeticGenus_strictTransform_blowUp_singleton
    hY hYs hYd C.supp hcomp hy hyC hm
  set C' : Divisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) :=
    inverseTransformDivisor (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)) C
    with hC'
  have hS : C'.suppIdeal = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩)).base ⁻¹'
        ((C.supp : Set Y) \ {y})), isClosed_closure⟩ := by
    rw [DivisorWithCoeffs.suppIdeal]
    congr 1
    exact TopologicalSpace.Closeds.ext hsupp
  refine ⟨_, _, hqc', inferInstance, inferInstance, hY', hYs', hYd', _, hK', C', hC'1, ?_⟩
  rw [hS]
  refine ⟨hp', hcard, ?_, ?_⟩
  · have hg' := hg
    simp only [MMP.Mori.arithmeticGenus] at hg'
    rw [sub_sub, sub_right_inj] at hg'
    exact hg'
  · intro n hn
    rw [← hS] at hn
    exact htr n (by simpa only [add_assoc] using hn)

/-- **Adjunction for reduced curves, by point blow-ups.** The singular case is reduced to
`adjunction_of_smooth` by blowing up singular points of the strict transform: the difference of
the two sides is invariant under each blow-up (`isIntersectionNumber_of_blowUp_singleton` and
`arithmeticGenus_strictTransform_blowUp_singleton`), and the process terminates since
`#(components of C) - χ(𝒪_C) ≥ 0` (`eulerCharacteristic_le_card_support`) drops by `m(m-1)/2`. -/
private theorem adjunction_of_blowUps
    [IsAlgClosed k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsVariety k sY) (hYs : MMP.Mori.IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY)) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
      (-2 * eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
        (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)) := by
  -- strong induction on `#(components of C) - χ(𝒪_C) ≥ 0`, which drops under each blow-up
  have key : ∀ (n : ℕ) {Y : Scheme.{w}} {sY : Y ⟶ Spec (.of k)}
      [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y],
      MMP.Mori.IsVariety k sY → MMP.Mori.IsSmoothScheme sY → topologicalKrullDim Y = 2 →
      ∀ {K : Divisor Y}, K.IsCanonicalDivisor sY 2 →
      ∀ (C : Divisor Y), (∀ E ∈ C.support, C E = 1) →
      ∀ (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY)),
      haveI := hCp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (C.suppIdeal.subschemeι ≫ sY)
      ((C.support.card : ℤ) - eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
          (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)).toNat = n →
      IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
        (-2 * eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
          (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y sY _ _ _ hY hYs hYd K hK C hC hCp hn
      by_cases hCs : MMP.Mori.IsSmoothScheme (C.suppIdeal.subschemeι ≫ sY)
      · exact adjunction_of_smooth hY hYs hYd hK C hC hCp hCs
      · obtain ⟨y, hy, m, hyC, hm2, hm⟩ :=
          exists_two_le_multAt_of_not_isSmoothScheme hY hYs hYd C hC hCs
        obtain ⟨Y', sY', _, _, _, hY', hYs', hYd', K', hK', C', hC', hCp', hcard, hχ, htr⟩ :=
          exists_blowUp_step hY hYs hYd hK C hC hCp hy hyC hm
        haveI := hCp
        haveI := hCp'
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (C.suppIdeal.subschemeι ≫ sY)
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (C'.suppIdeal.subschemeι ≫ sY')
        have hR := eulerCharacteristic_le_card_support hY' hYd' C' hC' hCp'
        have hc2 : 1 ≤ m.choose 2 := Nat.choose_pos hm2
        have hlt : ((C'.support.card : ℤ) - eulerCharacteristic k (C'.suppIdeal.subschemeι ≫ sY')
            (SheafOfModules.unit C'.suppIdeal.subscheme.ringCatSheaf)).toNat < n := by
          rw [← hn, hcard, hχ]
          rw [hcard] at hR
          omega
        have h := htr _ (ih _ hlt hY' hYs' hYd' hK' C' hC' hCp' rfl)
        convert h using 1
        rw [hχ]
        push_cast
        rw [Nat.cast_choose_two]
        ring
  exact key _ hY hYs hYd hK C hC hCp rfl

end MMP.Proofs.thm_mmp_threefold_surface_adjunction_by_blowups

namespace MMP.Threefold

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

open MMP.Proofs.thm_mmp_threefold_surface_adjunction_by_blowups in
/-- **Adjunction for a reduced curve on a smooth surface.** Let `Y` be a smooth surface over an
algebraically closed field `k`, `K` a canonical divisor of `Y` and `C = ∑ Cᵢ` a reduced divisor
whose support is proper over `k`. Then the intersection number `((K + C) · C)` is defined and
equals `-2 χ(C, 𝒪_C)`, where `C` is the reduced closed subscheme on the support. -/
@[mmp "thm_mmp_threefold_surface_adjunction_by_blowups"]
public theorem isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
    [IsAlgClosed k] [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hYs : IsSmoothScheme sY) (hYd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (C : Divisor Y) (hC : ∀ E ∈ C.support, C E = 1)
    (hCp : IsProper (C.suppIdeal.subschemeι ≫ sY)) :
    haveI := hCp
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (C.suppIdeal.subschemeι ≫ sY)
    IsIntersectionNumber sY (Divisor.toQDivisor (K + C)) C.suppIdeal
      (-2 * eulerCharacteristic k (C.suppIdeal.subschemeι ≫ sY)
        (SheafOfModules.unit C.suppIdeal.subscheme.ringCatSheaf)) :=
  adjunction_of_blowUps hY hYs hYd hK C hC hCp

end MMP.Threefold

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

namespace MMP.Proofs.lem_fa3_system_star

/-- The reduced subscheme on the support of the divisor `E` of a prime divisor is `E`. -/
private theorem suppIdeal_single_one {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = E.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E, DivisorWithCoeffs.suppIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E, DivisorWithCoeffs.coe_supp]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

/-- Adjunction along a prime divisor `E` of arithmetic genus `p` on a smooth surface:
`((K_Y + E) · E) = 2p - 2`. -/
private theorem isIntersectionNumber_canonical_add_single {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : MMP.Mori.IsVariety k sY) (hYs : IsSmoothScheme sY)
    (hYd : topologicalKrullDim Y = 2) {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 2)
    (E : MMP.Mori.PrimeDivisor Y) {p : ℤ} (hp : IsArithmeticGenusOf sY E p) :
    IsIntersectionNumber sY (Divisor.toQDivisor K + Finsupp.single E 1) E.idealSheaf
      (2 * p - 2) := by
  obtain ⟨hpr, hcoh, rfl⟩ := hp
  have hI := suppIdeal_single_one E
  have hC : ∀ F ∈ (Finsupp.single E (1 : ℤ) : Divisor Y).support,
      (Finsupp.single E (1 : ℤ) : Divisor Y) F = 1 := by
    intro F hF
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hF
    rw [hF, Finsupp.single_eq_same]
  have hpr' : IsProper ((DivisorWithCoeffs.suppIdeal
      (Finsupp.single E (1 : ℤ) : Divisor Y)).subschemeι ≫ sY) := by
    rw [hI]; exact hpr
  have h := MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
    hY hYs hYd hK _ hC hpr'
  rw [map_add, MMP.Threefold.Resolution.toQDivisor_single] at h
  revert h hpr'
  generalize DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = I at hI ⊢
  subst hI
  intro _ h
  convert h using 1
  rw [MMP.Mori.arithmeticGenus]
  push_cast
  try ring

/-- The intersection numbers of the log canonical divisor of a candidate vector `a`: for every
canonical divisor `K_Y`,
`((K_Y + g⁻¹_* B + ∑_l (1 - a_l) E_l) · E_j) = -c_j - ∑_l a_l (E_l · E_j)`.
-/
private theorem isIntersectionNumber_logCanonical {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X}
    {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hg : IsGermResolution sX P g)
    {m : Fin n → Fin n → ℚ}
    (hm : ∀ k j, IsIntersectionNumber (g ≫ sX) (Finsupp.single (E k) 1) (E j).idealSheaf
      (m k j))
    {c : Fin n → ℚ} (hc : ∀ j, IsGermC sX P B g E j (c j)) (a : Fin n → ℚ)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor (g ≫ sX) 2) (j : Fin n) :
    IsIntersectionNumber (g ≫ sX) (Divisor.toQDivisor K + inverseTransformDivisor g B +
      ∑ l, Finsupp.single (E l) (1 - a l)) (E j).idealSheaf (-c j - ∑ l, a l * m l j) := by
  have hsm := hg.isSmoothResolution.isSmoothScheme
  obtain ⟨-, -, -, p, x, hp, hx, hcj⟩ := hc j
  have h3 : IsIntersectionNumber (g ≫ sX) (∑ l, (-a l) • Finsupp.single (E l) (1 : ℚ))
      (E j).idealSheaf (∑ l, (-a l) * m l j) :=
    MMP.Mori.isIntersectionNumber_sum _ (isIntersectionNumber_zero (hm j j)) fun l _ =>
      (hm l j).smul _ (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  have h := isIntersectionNumber_add (isIntersectionNumber_add
    (isIntersectionNumber_canonical_add_single hg.isVariety hsm hg.topologicalKrullDim_eq hK
      (E j) hp) hx) h3
  convert h using 1
  · have hs : ∑ l, Finsupp.single (E l) (1 - a l) =
        ∑ l, Finsupp.single (E l) (1 : ℚ) + ∑ l, (-a l) • Finsupp.single (E l) (1 : ℚ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, ← Finsupp.single_add, sub_eq_add_neg]
    rw [hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    abel
  · rw [hcj]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

end MMP.Proofs.lem_fa3_system_star

namespace MMP.Flips

open MMP.Proofs.lem_fa3_system_star in
/-- **The system `(*)`** (FA 3.0.2). Let `g` be a resolution of the surface germ with boundary
`(X, P; B)` with exceptional curves `E_1, …, E_n`, let `m k j = (E_k · E_j)` and let `c j` be the
number `c_j` (`MMP.Flips.IsGermC`). Then `a ∈ ℚ^n` is the log discrepancy vector of `(X, P; B)`
on `g` if and only if `∑_k a_k (E_k · E_j) = -c_j` for every `j`. -/
@[mmp "lem_fa3_system_star"]
public theorem isGermLogDiscrepancyVector_iff_sum_mul_eq_neg {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X}
    {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y}
    (hB : IsSurfaceGermWithBoundary sX P B) (hg : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E)
    {m : Fin n → Fin n → ℚ}
    (hm : ∀ k j, IsIntersectionNumber (g ≫ sX) (Finsupp.single (E k) 1) (E j).idealSheaf
      (m k j))
    {c : Fin n → ℚ} (hc : ∀ j, IsGermC sX P B g E j (c j)) (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔ ∀ j, ∑ k, a k * m k j = -c j := by
  constructor
  · rintro ⟨-, -, -, h⟩ j
    have := hg.isIntegral sX
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
    have hdim : topologicalKrullDim Y = ((2 : ℕ) : WithBot ℕ∞) := hg.topologicalKrullDim_eq
    obtain ⟨K, hK⟩ := @exists_isCanonicalDivisor_of_isSmoothScheme Y _ _ _ _ k _ (g ≫ sX)
      hg.isVariety hg.isSmoothResolution.isSmoothScheme 2 hdim
    linarith [(isIntersectionNumber_logCanonical hg hm hc a hK j).unique (h K hK j)]
  · refine fun h => ⟨hB, hg, hE, fun K hK j => ?_⟩
    have := isIntersectionNumber_logCanonical hg hm hc a hK j
    rwa [h j, sub_neg_eq_add, neg_add_cancel] at this

end MMP.Flips

end

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  {sX : X ⟶ Spec (CommRingCat.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
  [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
  {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

namespace MMP.Proofs.lem_fa3_dual_graph_log_discrepancies_agree

/-- The entries of `M(Γ)` are the intersection numbers `(E_i · E_j)`: the diagonal by the
`weight` field, the off-diagonal entries by the `edgeWeight` field. -/
private theorem isIntersectionNumber_matrix (hΓ : IsWeightedDualGraph sX P B g E Γ) (i j : Fin n) :
    IsIntersectionNumber (g ≫ sX) (Finsupp.single (E i) 1) (E j).idealSheaf
      ((Γ.matrix i j : ℤ) : ℚ) := by
  by_cases h : i = j
  · subst h; simpa [WeightedGraph.matrix] using hΓ.weight i
  · simpa [WeightedGraph.matrix, h] using hΓ.edgeWeight i j h

/-- The geometric number `c_j` of the resolution is the graph number `c_j(Γ)`: the intersection
`((B' + ∑_{l ≠ j} E_l) · E_j)` splits as the boundary weight plus the edge weights at `j`. -/
private theorem isGermC_c (hΓ : IsWeightedDualGraph sX P B g E Γ) (j : Fin n) :
    IsGermC sX P B g E j (Γ.c j) :=
  ⟨hΓ.isSurfaceGermWithBoundary, hΓ.isGermResolution, hΓ.isExceptionalCurveEnumeration,
    Γ.genus j, Γ.boundary j + ∑ l ∈ Finset.univ.erase j, (Γ.edgeWeight j l : ℚ), hΓ.genus j,
    isIntersectionNumber_add (hΓ.boundary j) <|
      isIntersectionNumber_sum _ (isIntersectionNumber_zero (hΓ.boundary j)) fun l hl => by
        rw [Γ.edgeWeight_symm]; exact hΓ.edgeWeight l j (Finset.ne_of_mem_erase hl),
    by rw [WeightedGraph.c]; push_cast; ring⟩

end MMP.Proofs.lem_fa3_dual_graph_log_discrepancies_agree

namespace MMP.Flips

open MMP.Proofs.lem_fa3_dual_graph_log_discrepancies_agree in
/-- **The log discrepancy vector of a resolution is that of its dual graph** (FA 3.0.2, 3.1.1).
If `Γ` is the weighted dual graph `Γ(g)` of a resolution `g` of the surface germ with boundary
`(X, P; B)` with exceptional curves `E_1, …, E_n`, then `a ∈ ℚ^n` is the log discrepancy vector
of `(X, P; B)` on `g` if and only if it is a log discrepancy vector of `Γ`. -/
@[mmp "lem_fa3_dual_graph_log_discrepancies_agree"]
public theorem IsWeightedDualGraph.isGermLogDiscrepancyVector_iff {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X}
    {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) (a : Fin n → ℚ) :
    IsGermLogDiscrepancyVector sX P B g E a ↔ Γ.IsLogDiscrepancyVector a :=
  isGermLogDiscrepancyVector_iff_sum_mul_eq_neg hΓ.isSurfaceGermWithBoundary
    hΓ.isGermResolution hΓ.isExceptionalCurveEnumeration (isIntersectionNumber_matrix hΓ)
    (isGermC_c hΓ) a

end MMP.Flips

end

end
