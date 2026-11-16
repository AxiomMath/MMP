module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle

/-!
# The general fibres of the exceptional divisor over a curve

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ Fᵢ`, and
`T ⊆ Y` a curve. Over a general open of `T`, every component `E` of `F` is either smooth over `T`
(generic smoothness, when `E` dominates `T`) or misses the fibres. So the irreducible components
of the fibre `E_y` over a general closed point `y ∈ T` are pairwise disjoint surfaces.

## Main results

* `MMP.Fourfold.exists_forall_of_finite`: finitely many properties holding over opens meeting `T`
  hold together over one.
* `MMP.Fourfold.exists_disjoint_maximal_fibre_of_mem`: for one component `E`, the components of
  the general fibres of `E` are pairwise disjoint surfaces.
* `MMP.Fourfold.exists_disjoint_maximal_fibre`: the components of the general fibres of every
  component of `F` are pairwise disjoint.
* `MMP.Fourfold.exists_maximal_fibre_transport_of_homeomorph`: a component-preserving
  homeomorphism between general fibres of `F` carries the complex points of each component of
  `E_b` onto those of a component of `E_t`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Intersection.Scheme (Subvariety)
open MMP.UnderlyingSpace
open MMP.Mori

namespace MMP.Fourfold

/-- If two opens `U` and `V` each meet the irreducible closed set `T`, then `U ⊓ V` meets `T`. -/
theorem inter_inter_nonempty_of_irreducibleCloseds {Y : Scheme.{0}} (T : IrreducibleCloseds Y)
    {U V : Y.Opens} (hU : ((U : Set Y) ∩ T).Nonempty) (hV : ((V : Set Y) ∩ T).Nonempty) :
    (((U ⊓ V : Y.Opens) : Set Y) ∩ T).Nonempty := by
  obtain ⟨x, hxT, hxU, hxV⟩ := T.isIrreducible.2 U V U.2 V.2 (by rwa [Set.inter_comm])
    (by rwa [Set.inter_comm])
  exact ⟨x, ⟨hxU, hxV⟩, hxT⟩

/-- The preimage of an irreducible set lying in the image of an embedding is irreducible. -/
private theorem isIrreducible_preimage_of_isEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) {C : Set B}
    (hC : IsIrreducible C) (hCr : C ⊆ Set.range φ) : IsIrreducible (φ ⁻¹' C) := by
  refine ⟨?_, fun u v hu hv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hC.nonempty
    obtain ⟨a, rfl⟩ := hCr hc
    exact ⟨a, hc⟩
  · obtain ⟨u', hu', rfl⟩ := hφ.isInducing.isOpen_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := hφ.isInducing.isOpen_iff.1 hv
    obtain ⟨c, hcC, hcu, hcv⟩ := hC.2 u' v' hu' hv' ⟨φ a, has, hau⟩ ⟨φ b, hbs, hbv⟩
    obtain ⟨d, rfl⟩ := hCr hcC
    exact ⟨d, hcC, hcu, hcv⟩

/-- An irreducible subset of `S` lies in a maximal irreducible subset of `S`. -/
theorem exists_subset_maximal_of_isIrreducible {B : Type*} [TopologicalSpace B]
    {S s : Set B} (hs : IsIrreducible s) (hsS : s ⊆ S) :
    ∃ t, s ⊆ t ∧ Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) t := by
  have hemb : Topology.IsEmbedding ((↑) : S → B) := Topology.IsEmbedding.subtypeVal
  have hs' := isIrreducible_preimage_of_isEmbedding hemb hs (by rwa [Subtype.range_coe])
  obtain ⟨u, hu, hsu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hs'
  refine ⟨(↑) '' u, fun x hx ↦ ⟨⟨x, hsS hx⟩, hsu hx, rfl⟩,
    ⟨hu.1.image _ continuous_subtype_val.continuousOn, Subtype.coe_image_subset _ _⟩, ?_⟩
  rintro t ⟨ht, htS⟩ hut
  have ht' := isIrreducible_preimage_of_isEmbedding hemb ht (by rwa [Subtype.range_coe])
  exact fun x hx ↦ ⟨⟨x, htS hx⟩, hu.2 ht' (fun x hx ↦ hut ⟨x, hx, rfl⟩) hx, rfl⟩

/-- The maximal irreducible subsets of the preimage of `S` under an embedding are the preimages
of the maximal irreducible subsets of `S` lying in the image, when each of these lies in the
image or misses it. -/
private theorem maximal_preimage_iff {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {φ : A → B} (hφ : Topology.IsEmbedding φ) {S : Set B}
    (hsep : ∀ C, Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C →
      C ⊆ Set.range φ ∨ Disjoint C (Set.range φ)) (A' : Set A) :
    Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ φ ⁻¹' S) A' ↔
      ∃ C, Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C ∧ C ⊆ Set.range φ ∧ A' = φ ⁻¹' C := by
  constructor
  · rintro ⟨⟨hA, hAS⟩, hmax⟩
    obtain ⟨C, hAC, hC⟩ := exists_subset_maximal_of_isIrreducible
      (hA.image φ hφ.continuous.continuousOn) (Set.image_subset_iff.2 hAS)
    have hCr : C ⊆ Set.range φ := by
      refine (hsep C hC).resolve_right fun hd ↦ ?_
      obtain ⟨a, ha⟩ := hA.nonempty
      exact Set.disjoint_left.1 hd (hAC ⟨a, ha, rfl⟩) ⟨a, rfl⟩
    refine ⟨C, hC, hCr, le_antisymm (fun a ha ↦ hAC ⟨a, ha, rfl⟩) ?_⟩
    exact hmax ⟨isIrreducible_preimage_of_isEmbedding hφ hC.1.1 hCr,
      Set.preimage_mono hC.1.2⟩ fun a ha ↦ hAC ⟨a, ha, rfl⟩
  · rintro ⟨C, hC, hCr, rfl⟩
    refine ⟨⟨isIrreducible_preimage_of_isEmbedding hφ hC.1.1 hCr, Set.preimage_mono hC.1.2⟩, ?_⟩
    rintro X ⟨hX, hXS⟩ hCX
    have hle : C ⊆ φ '' X := by
      rw [← Set.image_preimage_eq_of_subset hCr]
      exact Set.image_mono hCX
    have := hC.2 ⟨hX.image φ hφ.continuous.continuousOn, Set.image_subset_iff.2 hXS⟩ hle
    exact fun a ha ↦ this ⟨a, ha, rfl⟩

/-- A subset in the image of an embedding has the dimension of its preimage. -/
theorem topologicalKrullDim_preimage_of_isEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) {S : Set B}
    (hS : S ⊆ Set.range φ) : topologicalKrullDim (φ ⁻¹' S) = topologicalKrullDim S := by
  have hemb : Topology.IsEmbedding (fun s : (φ ⁻¹' S : Set A) ↦ φ s.1) :=
    hφ.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun s : (φ ⁻¹' S : Set A) ↦ φ s.1) = S := by
    rw [Set.range_comp' φ Subtype.val, Subtype.range_coe, Set.image_preimage_eq_of_subset hS]
  exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq

/-- Under an embedding with range `S`, the preimage of a maximal irreducible subset of `S` is an
irreducible component. -/
theorem mem_irreducibleComponents_preimage_of_maximal {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) {S C : Set B}
    (hr : Set.range φ = S) (hC : Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C) :
    φ ⁻¹' C ∈ irreducibleComponents A := by
  have hmax := (maximal_preimage_iff hφ (S := S) (fun C' hC' ↦ Or.inl (hr ▸ hC'.1.2))
    (φ ⁻¹' C)).2 ⟨C, hC, hr ▸ hC.1.2, rfl⟩
  rw [← hr, Set.preimage_range] at hmax
  exact ⟨hmax.1.1, fun X hX hle ↦ hmax.2 ⟨hX, Set.subset_univ _⟩ hle⟩

private theorem eq_two_of_add_one_eq_three {e : WithBot ℕ∞}
    (h : e + ((1 : ℕ) : WithBot ℕ∞) = ((3 : ℕ) : WithBot ℕ∞)) : e = ((2 : ℕ) : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h' : e + 1 = 3 := WithBot.coe_injective (by rwa [WithBot.coe_add])
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe e =>
      have : e + 1 = 3 := by exact_mod_cast h'
      obtain rfl : e = 2 := by omega
      rfl

/-- Finitely many properties, each holding over an open meeting the irreducible `T`, hold
together over one open meeting `T`. -/
theorem exists_forall_of_finite {Y : Scheme.{0}} (T : IrreducibleCloseds Y)
    {κ : Type*} [Fintype κ] (P : κ → Y → Prop)
    (h : ∀ i, ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, P i y) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, ∀ i, P i y := by
  classical
  choose U hU hP using h
  have hne : ∀ s : Finset κ, (((s.inf U : Y.Opens) : Set Y) ∩ T).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
      exact ⟨x, by simp, hx⟩
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact inter_inter_nonempty_of_irreducibleCloseds T (hU a) ih
  refine ⟨Finset.univ.inf U, hne _, fun y hy i ↦ hP i y ⟨?_, hy.2⟩⟩
  exact (Finset.inf_le (Finset.mem_univ i) : Finset.univ.inf U ≤ U i) hy.1

/-- The fibre of `p` over `t` has pairwise disjoint maximal irreducible subsets when it is smooth
over the residue field of `t`. -/
theorem disjoint_of_maximal_fibre_of_smooth {V S : Scheme} (p : V ⟶ S) (t : S)
    (hsm : Smooth (p.fiberToSpecResidueField t)) {A B : Set V}
    (hA : Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ p.base ⁻¹' {t}) A)
    (hB : Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ p.base ⁻¹' {t}) B) (hAB : A ≠ B) :
    Disjoint A B := by
  set φ := (p.fiberι t).base
  have hφ : Topology.IsEmbedding φ := (p.fiberι t).isEmbedding
  have hφr : Set.range φ = p.base ⁻¹' {t} := p.range_fiberι t
  have hAr : A ⊆ Set.range φ := hφr ▸ hA.1.2
  have hBr : B ⊆ Set.range φ := hφr ▸ hB.1.2
  have hne : φ ⁻¹' A ≠ φ ⁻¹' B := fun h ↦ hAB (by
    rw [← Set.image_preimage_eq_of_subset hAr, h, Set.image_preimage_eq_of_subset hBr])
  have hd := @MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth _ _ _
    (p.fiberToSpecResidueField t) hsm _ _ (mem_irreducibleComponents_preimage_of_maximal hφ hφr hA)
    (mem_irreducibleComponents_preimage_of_maximal hφ hφr hB) hne
  refine Set.disjoint_left.2 fun a haA haB ↦ ?_
  obtain ⟨a', rfl⟩ := hAr haA
  exact Set.disjoint_left.1 hd haA haB

/-- A maximal irreducible subset of the fibre of `p` over `t` has the dimension of the
irreducible components of the fibre scheme. -/
theorem topologicalKrullDim_add_of_maximal_fibre {V S : Scheme} (p : V ⟶ S) (t : S)
    (hd : ∀ C ∈ irreducibleComponents (p.fiber t),
      topologicalKrullDim C + topologicalKrullDim S = topologicalKrullDim V) {A : Set V}
    (hA : Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ p.base ⁻¹' {t}) A) :
    topologicalKrullDim A + topologicalKrullDim S = topologicalKrullDim V := by
  have hφ : Topology.IsEmbedding (p.fiberι t).base := (p.fiberι t).isEmbedding
  have hφr : Set.range (p.fiberι t).base = p.base ⁻¹' {t} := p.range_fiberι t
  rw [← topologicalKrullDim_preimage_of_isEmbedding hφ (hφr ▸ hA.1.2 : A ⊆ _)]
  exact hd _ (mem_irreducibleComponents_preimage_of_maximal hφ hφr hA)

private theorem range_curveι_base_eq {Y : Scheme.{0}} (T : IrreducibleCloseds Y) :
    Set.range (curveι T).base = (T : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- If `T` is not contained in the closed image `r(I)`, then over an open meeting `T` the fibres
of `I ⟶ Y` are empty, so have no maximal irreducible subsets. -/
theorem exists_forall_not_maximal_fibre_of_not_subset {Z Y : Scheme} (r : Z ⟶ Y)
    (I : Z.IdealSheafData) (T : Set Y) (hKcl : IsClosed (r.base '' (I.support : Set Z)))
    (hTK : ¬ T ⊆ r.base '' (I.support : Set Z)) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, ∀ A : Set I.subscheme,
      ¬ Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (I.subschemeι ≫ r).base ⁻¹' {y}) A := by
  obtain ⟨t, htT, htK⟩ := Set.not_subset.1 hTK
  refine ⟨⟨_, hKcl.isOpen_compl⟩, ⟨t, htK, htT⟩, fun y hy A hA ↦ ?_⟩
  obtain ⟨x, hx⟩ := hA.1.1.nonempty
  exact hy.1 ⟨I.subschemeι.base x, I.range_subschemeι ▸ ⟨x, rfl⟩, hA.1.2 hx⟩

/-- A component `E` of `F` dominating the curve `T` maps to the reduced curve `T`, smoothly with
equidimensional fibres over a dense open of `T` (generic smoothness). -/
theorem exists_curveScheme_lift_smooth_fibre
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) (T : IrreducibleCloseds Y) (E : F.support)
    (hKT : r.base '' (E.1.idealSheaf.support : Set Z) = T) :
    ∃ p : E.1.idealSheaf.subscheme ⟶ curveScheme T,
      p ≫ curveι T = E.1.idealSheaf.subschemeι ≫ r ∧
      ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧ ∀ t ∈ U,
        Smooth (p.fiberToSpecResidueField t) ∧ ∀ C ∈ irreducibleComponents (p.fiber t),
          topologicalKrullDim C + topologicalKrullDim (curveScheme T) =
            topologicalKrullDim E.1.idealSheaf.subscheme := by
  classical
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  haveI : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]
    exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  set ι := E.1.idealSheaf.subschemeι
  have hrangef : Set.range (ι ≫ r).base = (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, E.1.idealSheaf.range_subschemeι,
      hKT]
  have hker : (curveι T).ker ≤ (ι ≫ r).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangef, T.isClosed.closure_eq]
    rfl
  let p := IsClosedImmersion.lift (curveι T) (ι ≫ r) hker
  have hp : p ≫ curveι T = ι ≫ r := IsClosedImmersion.lift_fac _ _ _
  letI : E.1.idealSheaf.subscheme.Over (Spec (.of ℂ)) := ⟨ι ≫ (Z ↘ Spec (.of ℂ))⟩
  letI : (curveScheme T).Over (Spec (.of ℂ)) := ⟨curveι T ≫ sY⟩
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  haveI : p.IsOver (Spec (.of ℂ)) := ⟨by
    change p ≫ curveι T ≫ sY = ι ≫ (Z ↘ Spec (.of ℂ))
    rw [← Category.assoc, hp, Category.assoc, hM.comp_eq]⟩
  haveI : Smooth (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change Smooth (ι ≫ (Z ↘ Spec (.of ℂ)))
    rw [← hM.comp_eq]
    exact (MMP.Mori.isSmoothScheme_iff _).1 (hM.isSNC.1 E.1 E.2)
  haveI : LocallyOfFiniteType (curveScheme T ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (curveι T ≫ sY))
  haveI : QuasiCompact (curveScheme T ↘ Spec (.of ℂ)) :=
    inferInstanceAs (QuasiCompact (curveι T ≫ sY))
  haveI : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (ι ≫ (Z ↘ Spec (.of ℂ))))
  haveI : QuasiCompact (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (QuasiCompact (ι ≫ (Z ↘ Spec (.of ℂ))))
  have hpsurj : Function.Surjective p.base := fun t ↦ by
    obtain ⟨x, hx⟩ : (curveι T).base t ∈ Set.range (ι ≫ r).base := by
      rw [hrangef, ← range_curveι_base_eq T]
      exact ⟨t, rfl⟩
    refine ⟨x, (curveι T).isClosedEmbedding.injective ?_⟩
    change (p ≫ curveι T).base x = _
    rw [hp]
    exact hx
  obtain ⟨U, hU, -, -, hfib⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  exact ⟨p, hp, U, hU, hfib ⟨hpsurj.denseRange⟩⟩

/-- The fibre components of a component `E` dominating `T` over a general point of `T` are
pairwise disjoint and are surfaces. -/
theorem exists_disjoint_maximal_fibre_of_image_eq
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) (E : F.support)
    (hKT : r.base '' (E.1.idealSheaf.support : Set Z) = T) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      (∀ A B : Set E.1.idealSheaf.subscheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
        A ≠ B → Disjoint A B) ∧
      ∀ A : Set E.1.idealSheaf.subscheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
        topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞) := by
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  haveI : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  obtain ⟨p, hp, U', hU'd, hfib⟩ := exists_curveScheme_lift_smooth_fibre hM T E hKT
  have hdE : topologicalKrullDim E.1.idealSheaf.subscheme = ((3 : ℕ) : WithBot ℕ∞) := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    exact MMP.Fourfold.ConductorBlowup.topologicalKrullDim_support_eq_three hdimZ E.1
  have hdT : topologicalKrullDim (curveScheme T) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hT1
  obtain ⟨W, hW, hWU⟩ := (curveι T).isClosedEmbedding.isInducing.isOpen_iff.1 U'.2
  refine ⟨⟨W, hW⟩, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨t, ht⟩ := hU'd.nonempty
    refine ⟨(curveι T).base t, ?_, range_curveι_base_eq T ▸ ⟨t, rfl⟩⟩
    change (curveι T).base t ∈ W
    rw [← Set.mem_preimage, hWU]
    exact ht
  obtain ⟨t, rfl⟩ : y ∈ Set.range (curveι T).base := range_curveι_base_eq T ▸ hy.2
  have ht : t ∈ U' := by
    have h : t ∈ (curveι T).base ⁻¹' W := hy.1
    rwa [hWU] at h
  have hfibset : (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {(curveι T).base t} =
      p.base ⁻¹' {t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hp]
    exact (curveι T).isClosedEmbedding.injective.eq_iff
  obtain ⟨hsm, hd⟩ := hfib t ht
  rw [hfibset]
  refine ⟨fun A B hA hB ↦ disjoint_of_maximal_fibre_of_smooth p t hsm hA hB, fun A hA ↦ ?_⟩
  have h := topologicalKrullDim_add_of_maximal_fibre p t hd hA
  rw [hdE, hdT] at h
  exact eq_two_of_add_one_eq_three h

/-- The fibre components of one component `E` over a general point of `T` are pairwise disjoint
and are surfaces. -/
theorem exists_disjoint_maximal_fibre_of_mem
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) (E : F.support) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      (∀ A B : Set E.1.idealSheaf.subscheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
        A ≠ B → Disjoint A B) ∧
      ∀ A : Set E.1.idealSheaf.subscheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
        topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞) := by
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  haveI : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  set K : Set Y := r.base '' (E.1.idealSheaf.support : Set Z)
  have hKcl : IsClosed K := r.isClosedMap _ E.1.idealSheaf.support.isClosed
  have hEirr : IsIrreducible (E.1.idealSheaf.support : Set Z) := by
    change IsIrreducible (E.1.support : Set Z)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hKirr : IsIrreducible K := hEirr.image _ r.continuous.continuousOn
  by_cases hTK : (T : Set Y) ⊆ K
  swap
  · obtain ⟨U, hU, hempty⟩ :=
      exists_forall_not_maximal_fibre_of_not_subset r E.1.idealSheaf T hKcl hTK
    exact ⟨U, hU, fun y hy ↦
      ⟨fun A _ hA _ _ ↦ (hempty y hy A hA).elim, fun A hA ↦ (hempty y hy A hA).elim⟩⟩
  refine exists_disjoint_maximal_fibre_of_image_eq hM T hT1 E ?_
  by_contra hne
  have hle := hM.topologicalKrullDim_image_le E.1 E.2
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hKirr T.isClosed hTK
    (Ne.symm hne) (ne_top_of_le_ne_top (by decide) hle)
  rw [hT1] at hlt
  exact (hlt.trans_le hle).false

/-- **Disjoint fibre components.** Over a general open of `T`, the irreducible components of the
fibre of every component `E` of `F` are pairwise disjoint. -/
theorem exists_disjoint_maximal_fibre
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, ∀ (E : F.support)
      (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B := by
  obtain ⟨U, hU, hP⟩ := exists_forall_of_finite T _
    (exists_disjoint_maximal_fibre_of_mem hM T hT1)
  exact ⟨U, hU, fun y hy E ↦ (hP y hy E).1⟩

/-- The maximal irreducible subsets of any subset of a Noetherian space are finitely many. -/
theorem finite_setOf_maximal {B : Type*} [TopologicalSpace B] [NoetherianSpace B]
    (S : Set B) : {A | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) A}.Finite := by
  have hr : Set.range ((↑) : S → B) = S := Subtype.range_coe
  refine Set.Finite.of_finite_image (f := fun A ↦ ((↑) : S → B) ⁻¹' A)
    ((NoetherianSpace.finite_irreducibleComponents (α := S)).subset ?_) ?_
  · rintro _ ⟨A, hA, rfl⟩
    exact mem_irreducibleComponents_preimage_of_maximal Topology.IsEmbedding.subtypeVal hr hA
  · intro A hA A' hA' h
    simp only at h
    have hAr : A ⊆ Set.range ((↑) : S → B) := by rw [hr]; exact hA.1.2
    have hA'r : A' ⊆ Set.range ((↑) : S → B) := by rw [hr]; exact hA'.1.2
    rw [← Set.image_preimage_eq_of_subset hAr, h, Set.image_preimage_eq_of_subset hA'r]

/-- A maximal irreducible subset of a closed set is closed. -/
theorem isClosed_of_maximal {B : Type*} [TopologicalSpace B] {S A : Set B}
    (hS : IsClosed S) (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ S) A) : IsClosed A :=
  closure_subset_iff_isClosed.1 (hA.2 ⟨hA.1.1.closure, closure_minimal hA.1.2 hS⟩ subset_closure)

/-- **The connected components of a finite closed partition.** If `S` is the union of finitely
many pairwise disjoint closed preconnected sets, these are the connected components of `S`. -/
theorem connectedComponentIn_eq_of_pairwiseDisjoint {X : Type*} [TopologicalSpace X]
    {S : Set X} {Ps : Set (Set X)} (hfin : Ps.Finite) (hcl : ∀ P ∈ Ps, IsClosed P)
    (hconn : ∀ P ∈ Ps, IsPreconnected P) (hdisj : Ps.PairwiseDisjoint id) (hS : ⋃₀ Ps = S)
    {P : Set X} (hP : P ∈ Ps) {x : X} (hx : x ∈ P) : connectedComponentIn S x = P := by
  have hxS : x ∈ S := hS ▸ Set.mem_sUnion_of_mem hx hP
  apply Set.Subset.antisymm
  · set R : Set X := ⋃ Q ∈ Ps \ {P}, Q
    have hsub : connectedComponentIn S x ⊆ P ∪ R := by
      intro y hy
      have hyS := connectedComponentIn_subset S x hy
      rw [← hS] at hyS
      obtain ⟨Q, hQ, hyQ⟩ := hyS
      by_cases hQP : Q = P
      · exact Or.inl (hQP ▸ hyQ)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨Q, ⟨hQ, hQP⟩, hyQ⟩)
    have hRcl : IsClosed R :=
      (hfin.subset Set.diff_subset).isClosed_biUnion fun Q hQ ↦ hcl Q hQ.1
    have hd : Disjoint P R :=
      Set.disjoint_iUnion₂_right.2 fun Q hQ ↦ hdisj hP hQ.1 (Ne.symm hQ.2)
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
      P R (hcl P hP) hRcl hsub
      (by rw [Set.disjoint_iff_inter_eq_empty.1 hd, Set.inter_empty]) with h | h
    · exact h
    · obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 (h (mem_connectedComponentIn hxS))
      exact absurd (hdisj hP hQ.1 (Ne.symm hQ.2)) (Set.not_disjoint_iff.2 ⟨x, hx, hxQ⟩)
  · exact (hconn P hP).subset_connectedComponentIn hx (hS ▸ Set.subset_sUnion_of_mem hP)

/-- **The complex points of an irreducible closed set are connected.** -/
theorem isConnected_pointsOver_of_isIrreducible {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {S : Set Z} (hS : IsClosed S) (hirr : IsIrreducible S) :
    IsConnected (pointsOver (K := ℂ) S) := by
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩
  haveI : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hirr
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hZne : (∅ : Set I.subscheme) ≠ Set.univ := by
    obtain ⟨x, hx⟩ := hirr.nonempty
    rw [← hrange] at hx
    obtain ⟨w, -⟩ := hx
    exact fun h ↦ (h ▸ Set.mem_univ w : w ∈ (∅ : Set I.subscheme))
  have hconn := MMP.UnderlyingSpace.isConnected_regularPart_diff
    (X := I.subscheme) isClosed_empty hZne
  have hdense := MMP.UnderlyingSpace.dense_regularPart_diff
    (X := I.subscheme) isClosed_empty hZne
  have hAconn : IsConnected (Set.univ : Set (UnderlyingSpace ℂ I.subscheme)) :=
    hconn.subset_closure (fun p _ ↦ Set.mem_univ p)
      (by rw [hdense.closure_eq])
  have himage : map (K := ℂ) I.subschemeι '' Set.univ = pointsOver (K := ℂ) S := by
    rw [Set.image_univ, range_map_of_isClosedImmersion, hrange]
  rw [← himage]
  exact hAconn.image _ (map (K := ℂ) I.subschemeι).continuous.continuousOn

section Fibre

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F : Divisor Z}

/-- The points over a subset of a component `E` lie over `E`. -/
theorem mem_pointsOver_support_of_mem_image {E : Mori.PrimeDivisor Z}
    {A : Set E.idealSheaf.subscheme} {w : UnderlyingSpace ℂ Z}
    (hw : w ∈ pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' A)) :
    w ∈ pointsOver (K := ℂ) (E.support : Set Z) := by
  obtain ⟨y, -, hy⟩ := hw
  change w.toHom (IsLocalRing.closedPoint ℂ) ∈ (E.idealSheaf.support : Set Z)
  rw [← hy, ← E.idealSheaf.range_subschemeι]
  exact ⟨y, rfl⟩

/-- The points of a fibre component `G ⊆ E_y` lie in the fibre `F_y`. -/
theorem pointsOver_image_subset_fibre [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support)
    {y : UnderlyingSpace ℂ Y} {G : Set E.idealSheaf.subscheme}
    (hG : G ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) :
    pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' G) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y} := by
  rintro p ⟨x, hx, hpx⟩
  refine ⟨?_, ?_⟩
  · change p.toHom (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z)
    rw [← hpx, DivisorWithCoeffs.coe_supp]
    exact Set.mem_iUnion₂.2 ⟨E, hE, (E.idealSheaf.range_subschemeι ▸ ⟨x, rfl⟩ :
      E.idealSheaf.subschemeι.base x ∈ (E.idealSheaf.support : Set Z))⟩
  · change mapFun r p = y
    apply (equivClosedPoints (K := ℂ) Y).injective
    apply Subtype.ext
    rw [equivClosedPoints_apply, equivClosedPoints_apply, toHom_mapFun]
    have h1 : (E.idealSheaf.subschemeι ≫ r).base x = y.toHom (IsLocalRing.closedPoint ℂ) := hG hx
    change r.base (E.idealSheaf.subschemeι.base x) = _ at h1
    rw [hpx] at h1
    exact h1

/-- A point of the fibre `F_y` lying over a component `E` lies over a component of `E_y`. -/
theorem exists_maximal_fibre_of_mem_pointsOver_support {E : Mori.PrimeDivisor Z}
    {y : UnderlyingSpace ℂ Y} (w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}))
    (hw : (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.support : Set Z)) :
    ∃ B, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {y.toHom (IsLocalRing.closedPoint ℂ)}) B ∧
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' B) := by
  obtain ⟨x, hx⟩ : (w : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈
      Set.range E.idealSheaf.subschemeι.base := by
    rw [E.idealSheaf.range_subschemeι]
    exact hw
  have hxFib : x ∈ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
      {y.toHom (IsLocalRing.closedPoint ℂ)} := by
    change r.base (E.idealSheaf.subschemeι.base x) = y.toHom (IsLocalRing.closedPoint ℂ)
    rw [hx]
    exact congrArg (fun q : UnderlyingSpace ℂ Y ↦ q.toHom (IsLocalRing.closedPoint ℂ))
      (w.2.2 : mapFun r (w : UnderlyingSpace ℂ Z) = y)
  obtain ⟨B, hxB, hB⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
    (Set.singleton_subset_iff.2 hxFib)
  exact ⟨B, hB, x, hxB rfl, hx⟩

/-- A nonempty closed subset `G` of the fibre `E_y` has a complex point in the fibre `F_y`. -/
theorem exists_mem_pointsOver_image_of_subset_fibre [IsComplexScheme Z] [CompactSpace Z]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support)
    {y : UnderlyingSpace ℂ Y} {G : Set E.idealSheaf.subscheme} (hGcl : IsClosed G)
    (hGne : G.Nonempty)
    (hG : G ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) :
    ∃ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}),
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.idealSheaf.subschemeι.base '' G) := by
  set ι := E.idealSheaf.subschemeι
  haveI : CompactSpace E.idealSheaf.subscheme := ι.isClosedEmbedding.compactSpace
  obtain ⟨x, hx, hxcl⟩ := hGcl.exists_closed_singleton hGne
  have hιx : IsClosed ({ι.base x} : Set Z) := by
    rw [← Set.image_singleton]
    exact ι.isClosedEmbedding.isClosedMap _ hxcl
  set p := (equivClosedPoints (K := ℂ) Z).symm ⟨ι.base x, hιx⟩ with hpdef
  have hp : p.toHom (IsLocalRing.closedPoint ℂ) = ι.base x := by
    rw [← equivClosedPoints_apply, hpdef, Equiv.apply_symm_apply]
  have hpG : p ∈ pointsOver (K := ℂ) (ι.base '' G) := ⟨x, hx, hp.symm⟩
  exact ⟨⟨p, pointsOver_image_subset_fibre hE hG hpG⟩, hpG⟩

end Fibre

section Transport

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-- Over a general point `y` of `T`, the complex points of the components of the fibre `E_y` are
the connected components of `E(ℂ) ∩ F_y`, read in the fibre `F_y = F(ℂ) ∩ r⁻¹ y`. -/
private theorem connectedComponentIn_fibre_eq [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support) {y : UnderlyingSpace ℂ Y}
    (hdisj : ∀ A B : Set E.idealSheaf.subscheme,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {y.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {y.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B → Disjoint A B)
    {A : Set E.idealSheaf.subscheme}
    (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.idealSheaf.subschemeι ≫ r).base ⁻¹'
        {y.toHom (IsLocalRing.closedPoint ℂ)}) A)
    (z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}))
    (hz : (z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.idealSheaf.subschemeι.base '' A)) :
    connectedComponentIn {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)} z =
      {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (E.idealSheaf.subschemeι.base '' A)} := by
  classical
  set ι := E.idealSheaf.subschemeι
  set Fib : Set E.idealSheaf.subscheme := (ι ≫ r).base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}
  set M : Set (Set E.idealSheaf.subscheme) := {A | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Fib) A}
  set Fy := pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}
  let Q : Set E.idealSheaf.subscheme → Set Fy := fun A ↦
    {w | (w : UnderlyingSpace ℂ Z) ∈ pointsOver (ι.base '' A)}
  have hycl : IsClosed ({y.toHom (IsLocalRing.closedPoint ℂ)} : Set Y) :=
    (equivClosedPoints (K := ℂ) Y y).2
  have hFibcl : IsClosed Fib := hycl.preimage (ι ≫ r).base.hom.continuous
  haveI : CompactSpace E.idealSheaf.subscheme := ι.isClosedEmbedding.compactSpace
  haveI : IsNoetherian E.idealSheaf.subscheme :=
    (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  have hMcl : ∀ B ∈ M, IsClosed B := fun B hB ↦ isClosed_of_maximal hFibcl hB
  refine connectedComponentIn_eq_of_pairwiseDisjoint (Ps := Q '' M)
    ((finite_setOf_maximal Fib).image Q) ?_ ?_ ?_ ?_ ⟨A, hA, rfl⟩ hz
  · rintro _ ⟨B, hB, rfl⟩
    exact (isClosed_pointsOver (ι.isClosedEmbedding.isClosedMap _ (hMcl B hB))).preimage
      continuous_subtype_val
  · rintro _ ⟨B, hB, rfl⟩
    have hsub : pointsOver (K := ℂ) (ι.base '' B) ⊆ Fy :=
      pointsOver_image_subset_fibre hE hB.1.2
    have hconn := isConnected_pointsOver_of_isIrreducible (Z := Z)
      (ι.isClosedEmbedding.isClosedMap _ (hMcl B hB))
      (hB.1.1.image _ ι.base.hom.continuous.continuousOn)
    have himg : (Subtype.val : Fy → UnderlyingSpace ℂ Z) '' Q B = pointsOver (ι.base '' B) := by
      change Subtype.val '' (Subtype.val ⁻¹' _) = _
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
    exact hconn.isPreconnected
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ hne
    have hd := hdisj B B' hB hB' fun h ↦ hne (by rw [h])
    refine Set.disjoint_left.2 fun w hw hw' ↦ ?_
    obtain ⟨x, hx, hxw⟩ := hw
    obtain ⟨x', hx', hxw'⟩ := hw'
    exact Set.disjoint_left.1 hd hx (ι.isClosedEmbedding.injective (hxw.trans hxw'.symm) ▸ hx')
  · ext w
    simp only [Set.sUnion_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨_, _, x, hx, hxw⟩ ↦ mem_pointsOver_support_of_mem_image ⟨x, hx, hxw⟩,
      exists_maximal_fibre_of_mem_pointsOver_support w⟩

/-- **Fibre components are carried to fibre components.** Over a general open `U` of `T`, a
homeomorphism `h : F_b ≃ₜ F_t` between the fibres over two closed points of `U ∩ T` preserving
every component `E` of `F` carries the complex points of every component `G_b` of `E_b` onto
those of a component `G_t` of `E_t`. -/
theorem exists_maximal_fibre_transport_of_homeomorph
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ b t : UnderlyingSpace ℂ Y, b.toHom (IsLocalRing.closedPoint ℂ) ∈ (U : Set Y) ∩ T →
        t.toHom (IsLocalRing.closedPoint ℂ) ∈ (U : Set Y) ∩ T →
        ∀ h : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) ≃ₜ
          ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}),
        (∀ E ∈ F.support, ∀ z, (h z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
          (z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)) →
        ∀ (E : F.support) (Gb : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
            {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _) →
          ∃ Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
            Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
              {t.toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _) ∧
            ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
              (z : UnderlyingSpace ℂ Z) ∈
                pointsOver (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
              (h z : UnderlyingSpace ℂ Z) ∈
                pointsOver (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _)) := by
  classical
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  obtain ⟨U, hU, hP⟩ := exists_forall_of_finite T _
    (exists_disjoint_maximal_fibre_of_mem (sY := Y ↘ Spec (.of ℂ)) hM T hT1)
  refine ⟨U, hU, fun b t hb ht h hh E Gb hGb ↦ ?_⟩
  set ι := E.1.idealSheaf.subschemeι
  obtain ⟨z₀, hz₀⟩ := exists_mem_pointsOver_image_of_subset_fibre (G := (Gb.1.support : Set _))
    E.2 Gb.1.ideal.support.isClosed hGb.1.1.nonempty hGb.1.2
  have hz₀E := mem_pointsOver_support_of_mem_image hz₀
  obtain ⟨B, hB, hhz₀B⟩ :=
    exists_maximal_fibre_of_mem_pointsOver_support (h z₀) ((hh E.1 E.2 z₀).2 hz₀E)
  have hccb := connectedComponentIn_fibre_eq E.2 (hP _ hb E).1 hGb z₀ hz₀
  have hcct := connectedComponentIn_fibre_eq E.2 (hP _ ht E).1 hB (h z₀) hhz₀B
  have hS : h '' {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.1.support : Set Z)} =
      {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.1.support : Set Z)} := by
    ext w
    rw [← h.apply_symm_apply w, h.injective.mem_set_image]
    exact (hh E.1 E.2 (h.symm w)).symm
  have himg := h.image_connectedComponentIn
    (s := {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.1.support : Set Z)}) (x := z₀) hz₀E
  rw [hS, hccb, hcct] at himg
  have hBcl : IsClosed B :=
    isClosed_of_maximal
      (((equivClosedPoints (K := ℂ) Y t).2 : IsClosed _).preimage (ι ≫ r).base.hom.continuous) hB
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨B, hBcl⟩ with hI
  have hsupp : (I.support : Set E.1.idealSheaf.subscheme) = B := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨⟨⟨I, StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hB.1.1⟩,
    ⟨2, rfl, ?_⟩⟩, ?_, fun z ↦ ?_⟩
  · change topologicalKrullDim I.subscheme = _
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq, hsupp]
    exact (hP _ ht E).2 B hB
  · change Maximal _ (I.support : Set E.1.idealSheaf.subscheme)
    exact hsupp ▸ hB
  · change _ ↔ (h z : UnderlyingSpace ℂ Z) ∈
      pointsOver (ι.base '' (I.support : Set E.1.idealSheaf.subscheme))
    rw [hsupp]
    have : z ∈ {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (ι.base '' (Gb.1.support : Set _))} ↔
        h z ∈ {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}) |
          (w : UnderlyingSpace ℂ Z) ∈ pointsOver (ι.base '' B)} := by
      rw [← himg]
      exact h.injective.mem_set_image.symm
    exact this

end Transport

end MMP.Fourfold
