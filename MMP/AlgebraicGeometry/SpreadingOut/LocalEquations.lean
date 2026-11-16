module

import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSectionsSupplement
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import StacksFrontier.Topology.Dimension.KrullSeparation

/-!
# Spread local equations on late fibres

Let `M` be a model of a finite diagram `X` of integral projective schemes over an algebraically
closed field `K` of characteristic zero. The crepant boundary of a log resolution is carried to
the late fibres of `M` through local equations. A nonzero rational top form `dz₁ ∧ ⋯ ∧ dzₙ` is
built from étale coordinates of a stage, and its orders on every fibre are computed by chart
Jacobians, which are fractions of sections. The Cartier divisors supported on the prime divisors
presented by arrows and on the divisor of this form are a finitely generated group, and a
generator has local equations that are fractions of sections on finitely many affine charts of a
stage. This file proves that every such divisor has *spread local equations* on late fibres, and
that decompositions of fibre products as finite disjoint unions are kept on late fibres.

## Main definitions

* `MMP.Spreading.HasSpreadLocalEquations`: a divisor has local equations whose orders along the
  prime divisors of a fibre are the orders along the prime divisors of which they are fibres.

## Main results

* `MMP.Spreading.Model.exists_form_spreading`: a nonzero rational top form with computable
  orders on late fibres.
* `MMP.Spreading.Model.exists_spread_cartier`: Cartier divisors have spread local equations on
  late fibres.
* `MMP.Spreading.isCrepantBoundary_of_spreading`: crepant boundaries from spread local
  equations.
* `MMP.Spreading.eventually_fibreDecomp`: decompositions of fibre products are kept.

## References

* [EGA IV, 8.10, 9.7, 12.2]
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

noncomputable section

section Properties

variable {k₀ K : Type u} [Field k₀] [Field K] [IsAlgClosed k₀] [IsAlgClosed K] [CharZero k₀]
  [Algebra k₀ K] {J : Type u} [SmallCategory J] [FinCategory J] {X : J ⥤ Over (Spec (.of K))}
  (hint : ∀ j, IsIntegral (X.obj j).left)
  {ι : Type u} [Finite ι] {v : ι → J} {𝓛 : ∀ i, (X.obj (v i)).left.Modules}
  [h𝓛 : ∀ i, Stacks.Ample.IsInvertibleModule _ (𝓛 i)]

variable (M : Model k₀ X v 𝓛)

include hint in
/-- **Smooth opens descend to a stage**: a quasi-compact open of a vertex over `K` on which the
vertex is smooth is the preimage of an open of a late stage on which the model is smooth. -/
private lemma Model.exists_smooth_open {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (Uk : (X.obj j).left.Opens) (hUk : IsCompact (Uk : Set (X.obj j).left))
    (hsm : Smooth (Uk.ι ≫ (X.obj j).hom)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (U : ((M.stage (h₀.trans h₁)).obj j).left.Opens),
      M.cmp (h₀.trans h₁) j ⁻¹ᵁ U = Uk ∧ Smooth (U.ι ≫ ((M.stage (h₀.trans h₁)).obj j).hom) := by
  have : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨Sa, ha, Ha⟩ := M.exists_open j Uk hUk
  let S₂ : CoefficientModels.FGSub k₀ K := ⟨S₀.1 ⊔ Sa.1, S₀.2.sup Sa.2⟩
  have h₀₂ : S₀ ≤ S₂ := le_sup_left (a := S₀.1)
  have ha₂ : Sa ≤ S₂ := le_sup_right (b := Sa.1)
  obtain ⟨V, hVc, hV⟩ := Ha S₂ ha₂
  have h₂ : M.R ≤ S₂ := h₀.trans h₀₂
  have : Algebra.FiniteType k₀ S₂.1 := (Subalgebra.fg_iff_finiteType _).mp S₂.2
  have : IsNoetherianRing S₂.1 := Algebra.FiniteType.isNoetherianRing k₀ S₂.1
  have := (M.finitePresentation_stage h₂ j).1
  have := M.compactSpace_stage h₂ j
  have := M.quasiSeparatedSpace_stage h₂ j
  have := M.isLocallyNoetherian_stage h₂ j
  let A : Over (Spec (.of S₂.1)) := Over.mk (V.ι ≫ ((M.stage h₂).obj j).hom)
  have : CompactSpace A.left := isCompact_iff_compactSpace.mp hVc
  have : QuasiSeparatedSpace A.left := inferInstanceAs (QuasiSeparatedSpace V)
  have : LocallyOfFinitePresentation A.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (V.ι ≫ ((M.stage h₂).obj j).hom))
  have hsqK : IsPullback (M.cmp h₂ j ∣_ V) ((M.cmp h₂ j ⁻¹ᵁ V).ι ≫ (X.obj j).hom)
      (V.ι ≫ ((M.stage h₂).obj j).hom) (κ S₂.1) :=
    (AlgebraicGeometry.isPullback_morphismRestrict (M.cmp h₂ j) V).paste_vert
      ((M.isCartesian_cmp h₂).isPullback j)
  have hsmK : Smooth ((M.cmp h₂ j ⁻¹ᵁ V).ι ≫ (X.obj j).hom) := by
    rwa [hV]
  have hA : Smooth ((Over.pullback (κ S₂.1)).obj A).hom :=
    prop_snd_of_isPullback @Smooth hsqK (IsPullback.of_hasPullback A.hom (κ S₂.1)) hsmK
  obtain ⟨S₃, h₂₃, H⟩ := exists_stage_smooth S₂ A hA
  refine ⟨S₃, h₀₂.trans h₂₃, M.stageCmp h₂ h₂₃ j ⁻¹ᵁ V, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]
    exact hV
  · have hsq : IsPullback (M.stageCmp h₂ h₂₃ j ∣_ V)
        ((M.stageCmp h₂ h₂₃ j ⁻¹ᵁ V).ι ≫ ((M.stage (h₂.trans h₂₃)).obj j).hom)
        (V.ι ≫ ((M.stage h₂).obj j).hom) (π (show S₂.1 ≤ S₃.1 from h₂₃)) :=
      (AlgebraicGeometry.isPullback_morphismRestrict (M.stageCmp h₂ h₂₃ j) V).paste_vert
        ((M.isCartesian_stageCmp h₂ h₂₃).isPullback j)
    exact prop_snd_of_isPullback @Smooth (IsPullback.of_hasPullback A.hom _) hsq (H S₃ le_rfl)

/-- **Disjointness from an open spreads to the fibres of models of prime divisors.** -/
private lemma Model.evAbove_disjoint {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    {𝓘 : ((M.stage h₀).obj j).left.IdealSheafData} {E : Mori.PrimeDivisor (X.obj j).left}
    (h𝓘 : 𝓘.comap (M.cmp h₀ j) = E.idealSheaf) (V : ((M.stage h₀).obj j).left.Opens)
    (hEV : ¬ (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty) :
    EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      (Γ : Mori.PrimeDivisor ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left),
      Γ.idealSheaf = 𝓘.comap (M.fibreMap h₀ hS t j) →
      ¬ (Γ.support ∩ M.fibreMap h₀ hS t j ⁻¹ᵁ V).Nonempty := by
  have hK : M.cmp h₀ j ⁻¹' (𝓘.support : Set _) ⊆ M.cmp h₀ j ⁻¹' (V.compl : Set _) := by
    intro x hx hxV
    apply hEV
    refine ⟨x, ?_, hxV⟩
    have hx' : x ∈ (𝓘.comap (M.cmp h₀ j)).support := by
      rwa [Scheme.IdealSheafData.support_comap]
    rwa [h𝓘] at hx'
  obtain ⟨S₂, h₂, H⟩ := M.exists_preimage_subset h₀ j _ _ hK
  refine ⟨S₂, h₂, fun S h L _ t Γ hΓ hΓV => ?_⟩
  obtain ⟨x, hxΓ, hxV⟩ := hΓV
  have hx' : x ∈ (𝓘.comap (M.fibreMap h₀ (h₂.trans h) t j)).support := by
    rwa [← hΓ]
  rw [Scheme.IdealSheafData.support_comap] at hx'
  exact H S h L t hx' hxV

include hint in
/-- **Codimension bounds off an open spread to the fibres.** -/
private lemma Model.evAbove_le_coheight {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J) (U : ((M.stage h₀).obj j).left.Opens) (r : ℕ)
    (hU : ∀ x : (X.obj j).left, M.cmp h₀ j x ∉ U → (r : ℕ∞) ≤ Order.coheight x) :
    EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      IsIntegral ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left →
      topologicalKrullDim ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      ∀ x, M.fibreMap h₀ hS t j x ∉ U → (r : ℕ∞) ≤ Order.coheight x := by
  have hK : ∀ x ∈ (((Scheme.IdealSheafData.vanishingIdeal U.compl).comap
      (M.cmp h₀ j)).support : Set (X.obj j).left), (r : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    change M.cmp h₀ j x ∈ SetLike.coe
      (Scheme.IdealSheafData.vanishingIdeal U.compl).support at hx
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx
    exact hU x hx
  obtain ⟨S₂, h₂, H⟩ := M.exists_le_coheight_comap hint h₀ j _ r hK
  refine ⟨S₂, h₂, fun S h L _ t hI hd x hx => H S h L t hI hd x ?_⟩
  rw [Scheme.IdealSheafData.support_comap]
  change M.fibreMap h₀ (h₂.trans h) t j x ∈ SetLike.coe
    (Scheme.IdealSheafData.vanishingIdeal U.compl).support
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hx

include hint in
/-- **Generic points of fibres lie over opens meeting the generic fibre.** -/
private lemma Model.evAbove_genericPoint_mem {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J) (U : ((M.stage h₀).obj j).left.Opens) [Nonempty (M.cmp h₀ j ⁻¹ᵁ U)] :
    EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      [IsIntegral ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left],
      topologicalKrullDim ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      genericPoint ((M.stage (h₀.trans hS) ⋙ Over.pullback t).obj j).left ∈
        M.fibreMap h₀ hS t j ⁻¹ᵁ U := by
  have := hint j
  have hη : genericPoint (X.obj j).left ∈ M.cmp h₀ j ⁻¹ᵁ U :=
    ((genericPoint_spec (X.obj j).left).mem_open_set_iff (M.cmp h₀ j ⁻¹ᵁ U).isOpen).mpr
      (Set.univ_inter _ ▸ (Set.nonempty_coe_sort.mp ‹_›))
  refine (M.evAbove_le_coheight hint h₀ j U 1 fun x hx => ?_).mono
    fun S hS H L _ t _ hd => ?_
  · rw [Nat.cast_one, Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h0
    have hmax := Order.coheight_eq_zero.mp h0
    have hle : x ≤ genericPoint (X.obj j).left := genericPoint_specializes x
    have hsp : x ⤳ genericPoint (X.obj j).left := hmax hle
    exact hx (hsp.mem_open (M.cmp h₀ j ⁻¹ᵁ U).isOpen hη)
  · by_contra hn
    have := H L t inferInstance hd _ hn
    rw [Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at this
    exact absurd this (by norm_num)

/-- Eventual properties over a stage are eventual over every later stage. -/
public lemma EvAbove.of_le {S₀ S₀' : CoefficientModels.FGSub k₀ K}
    {P : ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop} (hP : EvAbove S₀ P)
    (h : S₀ ≤ S₀') : EvAbove S₀' fun S hS => P S (h.trans hS) := by
  obtain ⟨S₂, h₂, H⟩ := hP
  refine ⟨⟨S₂.1 ⊔ S₀'.1, S₂.2.sup S₀'.2⟩, le_sup_right (b := S₀'.1), fun S hS => ?_⟩
  exact H S ((le_sup_left (a := S₂.1)).trans hS)

/-- Finitely many eventual properties hold together eventually. -/
public lemma EvAbove.forall_of_finite {S₀ : CoefficientModels.FGSub k₀ K} {α : Type*} [Finite α]
    {P : α → ∀ S : CoefficientModels.FGSub k₀ K, S₀ ≤ S → Prop}
    (hP : ∀ a, EvAbove S₀ (P a)) : EvAbove S₀ fun S h => ∀ a, P a S h := by
  have := Fintype.ofFinite α
  exact (EvAbove.forall_finset Finset.univ fun a _ => hP a).mono
    fun S h H a => H a (Finset.mem_univ a)

/-- **Images of arrows presenting prime divisors are the fibres of their models.** -/
public lemma Model.evAbove_range_eq {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) {c j₀ : J}
    (a : c ⟶ j₀) {𝓘 : ((M.stage h₀).obj j₀).left.IdealSheafData}
    {P : Mori.PrimeDivisor (X.obj j₀).left} (h𝓘 : 𝓘.comap (M.cmp h₀ j₀) = P.idealSheaf)
    (hP : P.support = Set.range (X.map a).left.base) :
    EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap h₀ hS t j₀ ⁻¹' (𝓘.support : Set _) =
        Set.range ((M.stage (h₀.trans hS) ⋙ Over.pullback t).map a).left.base := by
  have hK₁ : M.cmp h₀ j₀ ⁻¹' (𝓘.support : Set _) = P.support := by
    change _ = SetLike.coe P.idealSheaf.support
    rw [← h𝓘, Scheme.IdealSheafData.support_comap]
    rfl
  have hK₂ : M.cmp h₀ j₀ ⁻¹' (M.rangeClosed h₀ a : Set _) = Set.range (X.map a).left.base :=
    (range_snd_of_isPullback ((M.isCartesian_cmp h₀).isPullback_map a)).symm
  obtain ⟨S₃, h₃, H₃⟩ := M.exists_preimage_subset h₀ j₀ 𝓘.support (M.rangeClosed h₀ a)
    (by rw [hK₁, hK₂, hP])
  obtain ⟨S₄, h₄, H₄⟩ := M.exists_preimage_subset h₀ j₀ (M.rangeClosed h₀ a) 𝓘.support
    (by rw [hK₁, hK₂, hP])
  have e₃ : EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap h₀ hS t j₀ ⁻¹' (𝓘.support : Set _) ⊆
        M.fibreMap h₀ hS t j₀ ⁻¹' (M.rangeClosed h₀ a : Set _) := ⟨S₃, h₃, fun S h => H₃ S h⟩
  have e₄ : EvAbove S₀ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap h₀ hS t j₀ ⁻¹' (M.rangeClosed h₀ a : Set _) ⊆
        M.fibreMap h₀ hS t j₀ ⁻¹' (𝓘.support : Set _) := ⟨S₄, h₄, fun S h => H₄ S h⟩
  refine (e₃.and e₄).mono fun S hS H L _ t => ?_
  rw [(range_snd_of_isPullback ((M.isCartesian_fibre h₀ hS t).isPullback_map a))]
  exact Set.Subset.antisymm (H.1 L t) (H.2 L t)

private lemma Model.isAffineHom_cmp {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) (j : J) :
    IsAffineHom (M.cmp h j) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) ((M.isCartesian_cmp h).isPullback j).flip
    inferInstance

include hint in
/-- **Rational functions are fractions of sections of a chart at a stage.** -/
private lemma Model.exists_frac {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (V : ((M.stage h₀).obj j).left.Opens) (hV : IsAffineOpen V) [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)]
    (f : (X.obj j).left.functionField) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (p q : Γ(((M.stage (h₀.trans h₁)).obj j).left, M.stageCmp h₀ h₁ j ⁻¹ᵁ V))
      (_ : Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V))),
      (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ q) ≠ 0 ∧
      (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ p) =
        f * (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ q) := by
  have := hint j
  have := M.isAffineHom_cmp h₀ j
  have hVa : IsAffineOpen (M.cmp h₀ j ⁻¹ᵁ V) := hV.preimage _
  have := functionField_isFractionRing_of_isAffineOpen _ _ hVa
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective
      (A := Γ((X.obj j).left, M.cmp h₀ j ⁻¹ᵁ V)) f
  obtain ⟨S₁, h₁, x, hx⟩ := M.exists_section_family h₀ j V hV.isCompact ![a, b]
  have hN : Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (M.cmp h₀ j ⁻¹ᵁ V)›
    refine ⟨⟨y, ?_⟩⟩
    change (M.cmp (h₀.trans h₁) j ≫ M.stageCmp h₀ h₁ j) y ∈ V
    rw [M.cmp_stageCmp]
    exact hy
  have hκ : ∀ i, (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ (x i)) =
      algebraMap Γ((X.obj j).left, M.cmp h₀ j ⁻¹ᵁ V) (X.obj j).left.functionField (![a, b] i) := by
    intro i
    rw [← hx i]
    change _ = (X.obj j).left.germToFunctionField _ _
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have hb0 : algebraMap Γ((X.obj j).left, M.cmp h₀ j ⁻¹ᵁ V) (X.obj j).left.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨S₁, h₁, x 0, x 1, hN, ?_, ?_⟩
  · rwa [hκ 1]
  · rw [hκ 0, hκ 1, ← hab]
    simp [div_mul_cancel₀ _ hb0]

/-- Generic germs of pulled-back sections are insensitive to restriction. -/
public lemma germToFunctionField_app_map {F Y : Scheme.{u}} [IsIntegral F] (f : F ⟶ Y)
    {V V' : Y.Opens} (h : V' ≤ V) (z : Γ(Y, V)) [Nonempty (f ⁻¹ᵁ V')] [Nonempty (f ⁻¹ᵁ V)] :
    F.germToFunctionField (f ⁻¹ᵁ V') (f.app V' (Y.presheaf.map (homOfLE h).op z)) =
      F.germToFunctionField (f ⁻¹ᵁ V) (f.app V z) := by
  have e : f.app V' (Y.presheaf.map (homOfLE h).op z) =
      F.presheaf.map (homOfLE (Scheme.Hom.preimage_mono f h)).op (f.app V z) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
    congr 1
    exact congrArg CommRingCat.Hom.hom (f.naturality (homOfLE h).op)
  rw [e]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- The number of étale coordinates of a chart meeting a fibre is the dimension of the fibre. -/
public lemma chart_dim_eq_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] [PerfectField L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y}
    {snd : F ⟶ Spec (.of L)} (hpb : IsPullback fst snd q t) [IsIntegral F]
    [LocallyOfFiniteType snd] {n : ℕ} (hn : topologicalKrullDim F = n) (V : Y.Opens)
    (hV : IsAffineOpen V) {m : ℕ} (g : MvPolynomial (Fin m) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom)
    (hne : genericPoint F ∈ fst ⁻¹ᵁ V) : m = n := by
  obtain ⟨b, -⟩ := exists_basis_kaehler_stalk_of_isPullback hpb V hV g hg hgC (genericPoint F) hne
  letI := MMP.Mori.functionFieldAlgebra snd
  have : Algebra.EssFiniteType L F.functionField := MMP.Mori.essFiniteType_functionField (sX := snd)
  have h1 : Module.finrank F.functionField Ω[F.functionField⁄L] = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [MMP.Mori.finrank_kaehlerDifferential_eq_trdeg,
    MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn] at h1
  exact h1.symm

/-- The generic germ of `g^*(φ^* a)` equals the generic germ of `f^* a` when `g ≫ φ = f`. -/
public lemma germToFunctionField_app_app_of_comp_eq {F Y Y' : Scheme.{u}} [IsIntegral F]
    (g : F ⟶ Y') (φ : Y' ⟶ Y) (f : F ⟶ Y) (hf : g ≫ φ = f) (V : Y.Opens) (a : Γ(Y, V))
    [h₁ : Nonempty (g ⁻¹ᵁ (φ ⁻¹ᵁ V))] [h₂ : Nonempty (f ⁻¹ᵁ V)] :
    F.germToFunctionField (g ⁻¹ᵁ (φ ⁻¹ᵁ V)) (g.app _ (φ.app V a)) =
      F.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) := by
  have := germToFunctionField_app_appLE g φ f hf V (φ ⁻¹ᵁ V) le_rfl a h₁ h₂
  rw [← this, Scheme.Hom.app_eq_appLE (f := φ)]

open Classical in
include hint in
/-- **Orders of a section spread to the fibres**, with the models at a later stage. -/
private lemma Model.exists_ord_section_of_le {S₀ S₁ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h₁ : S₀ ≤ S₁) (j : J) [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    (V : ((M.stage h₀).obj j).left.Opens) (a : Γ(((M.stage h₀).obj j).left, V))
    [Nonempty (M.cmp h₀ j ⁻¹ᵁ V)]
    (ha : (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a) ≠ 0)
    (T : Finset (Mori.PrimeDivisor (X.obj j).left))
    (𝓘 : Mori.PrimeDivisor (X.obj j).left → ((M.stage (h₀.trans h₁)).obj j).left.IdealSheafData)
    (h𝓘 : ∀ E ∈ T, (𝓘 E).comap (M.cmp (h₀.trans h₁) j) = E.idealSheaf)
    (hT : ∀ E : Mori.PrimeDivisor (X.obj j).left, (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a))
        E.genericPoint ≠ 0 → E ∈ T) :
    EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      [IsIntegral ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
      [IsLocallyNoetherian ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left],
      topologicalKrullDim ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left =
        topologicalKrullDim (X.obj j).left →
      (∀ E ∈ T, ∃ Ps : Mori.PrimeDivisor
          ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
        Ps.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j)) →
      ∀ [Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V)],
      ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField
          (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V) ((M.fibreMap h₀ (h₁.trans hS) t j).app V a) ≠ 0 ∧
      ∀ Γ : Mori.PrimeDivisor ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
        (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V).Nonempty →
        Scheme.ord (((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj
            j).left.germToFunctionField
            (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V) ((M.fibreMap h₀ (h₁.trans hS) t j).app V a))
            Γ.genericPoint =
          ∑ E ∈ T, if Γ.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j) then
            Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V)
              ((M.cmp h₀ j).app V a)) E.genericPoint else 0 := by
  have := hint j
  have eK : M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) = M.cmp h₀ j ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]
  haveI : Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)) := by
    rw [eK]; infer_instance
  have gK : (X.obj j).left.germToFunctionField _
      ((M.cmp (h₀.trans h₁) j).app _ ((M.stageCmp h₀ h₁ j).app V a)) =
      (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V) ((M.cmp h₀ j).app V a) :=
    germToFunctionField_app_app_of_comp_eq _ _ _ (M.cmp_stageCmp h₀ h₁ j) V a
  have hT' : ∀ E : Mori.PrimeDivisor (X.obj j).left,
      (E.support ∩ M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField _
        ((M.cmp (h₀.trans h₁) j).app _ ((M.stageCmp h₀ h₁ j).app V a))) E.genericPoint ≠ 0 →
      E ∈ T := by
    intro E hE hE'
    rw [eK] at hE
    rw [gK] at hE'
    exact hT E hE hE'
  have H := M.exists_ord_section hint (h₀.trans h₁) j (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)
    ((M.stageCmp h₀ h₁ j).app V a) (by rwa [gK]) T 𝓘 h𝓘 hT'
  refine H.mono fun S hS H L _ t _ _ hd hT _ => ?_
  have eF : M.fibreMap (h₀.trans h₁) hS t j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) =
      M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, M.fibreMap_comp]
  haveI : Nonempty (M.fibreMap (h₀.trans h₁) hS t j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)) := by
    rw [eF]; infer_instance
  have gF := germToFunctionField_app_app_of_comp_eq (M.fibreMap (h₀.trans h₁) hS t j)
    (M.stageCmp h₀ h₁ j) _ (M.fibreMap_comp h₀ h₁ hS t j) V a
  obtain ⟨H1, H2⟩ := H L t hd hT
  refine ⟨by rwa [← gF], fun Γ hΓ => ?_⟩
  rw [← gF, H2 Γ (by rwa [eF]), gK]

/-- **Disjointness spreads to the fibres**, with the model at a later stage than the open. -/
private lemma Model.evAbove_disjoint_of_le {S₀ S₁ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h₁ : S₀ ≤ S₁) (j : J) {𝓘 : ((M.stage (h₀.trans h₁)).obj j).left.IdealSheafData}
    {E : Mori.PrimeDivisor (X.obj j).left} (h𝓘 : 𝓘.comap (M.cmp (h₀.trans h₁) j) = E.idealSheaf)
    (V : ((M.stage h₀).obj j).left.Opens) (hEV : ¬ (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V).Nonempty) :
    EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      (Γ : Mori.PrimeDivisor ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left),
      Γ.idealSheaf = 𝓘.comap (M.fibreMap (h₀.trans h₁) hS t j) →
      ¬ (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V).Nonempty := by
  have eK : M.cmp (h₀.trans h₁) j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) = M.cmp h₀ j ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]
  refine (M.evAbove_disjoint (h₀.trans h₁) j h𝓘 (M.stageCmp h₀ h₁ j ⁻¹ᵁ V)
    (by rwa [eK])).mono fun S hS H L _ t Γ hΓ => ?_
  have eF : M.fibreMap (h₀.trans h₁) hS t j ⁻¹ᵁ (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) =
      M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, M.fibreMap_comp]
  rw [← eF]
  exact H L t Γ hΓ

include hint in
/-- **Étale charts at a stage.** A quasi-compact open of a vertex of dimension `n` on which the
vertex is smooth over `K` is covered by the preimages of finitely many affine opens of a late stage
carrying étale coordinates `g(X₁), …, g(Xₙ)` over the coefficient ring. -/
public lemma Model.exists_charts {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J) {n : ℕ}
    (hn : topologicalKrullDim (X.obj j).left = n) (Uk : (X.obj j).left.Opens)
    (hUk : IsCompact (Uk : Set (X.obj j).left)) (hsm : Smooth (Uk.ι ≫ (X.obj j).hom)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁) (B : Type u) (_ : Fintype B)
      (V : B → ((M.stage (h₀.trans h₁)).obj j).left.Opens)
      (g : ∀ b, MvPolynomial (Fin n) Γ(Spec (.of S₁.1), ⊤) →+*
        Γ(((M.stage (h₀.trans h₁)).obj j).left, V b)),
      (∀ b, IsAffineOpen (V b)) ∧ (∀ b, (g b).Etale) ∧
      (∀ b, (g b).comp MvPolynomial.C =
        (((M.stage (h₀.trans h₁)).obj j).hom.appLE ⊤ (V b) le_top).hom) ∧
      (∀ b, Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ V b)) ∧
      ∀ x ∈ Uk, ∃ b, M.cmp (h₀.trans h₁) j x ∈ V b := by
  classical
  have := hint j
  obtain ⟨S₁, h₁, U, hU, hsmU⟩ := M.exists_smooth_open hint h₀ j Uk hUk hsm
  choose V hVU hVa hyV m g hg hgC using fun y : U =>
    exists_etale_chart_of_smooth_on ((M.stage (h₀.trans h₁)).obj j).hom U y.1 y.2
  have hmem : ∀ x : Uk, M.cmp (h₀.trans h₁) j x.1 ∈ U := fun x => by
    have : x.1 ∈ M.cmp (h₀.trans h₁) j ⁻¹ᵁ U := hU ▸ x.2
    exact this
  let W : Uk → (X.obj j).left.Opens := fun x =>
    M.cmp (h₀.trans h₁) j ⁻¹ᵁ V ⟨_, hmem x⟩
  obtain ⟨s, hs⟩ := hUk.elim_finite_subcover (fun x : Uk => (W x : Set (X.obj j).left))
    (fun x => (W x).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hyV ⟨_, hmem ⟨x, hx⟩⟩⟩)
  have hpb := (M.isCartesian_cmp (h₀.trans h₁)).isPullback j
  have hlft := M.locallyOfFiniteType_obj j
  have hdim : ∀ x : Uk, m ⟨_, hmem x⟩ = n := fun x => by
    have hne : Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ V ⟨_, hmem x⟩) := ⟨⟨x.1, hyV ⟨_, hmem x⟩⟩⟩
    refine chart_dim_eq_of_isPullback hpb hn _ (hVa _) (g _) (hg _) (hgC _) ?_
    exact ((genericPoint_spec (X.obj j).left).mem_open_set_iff (W x).isOpen).mpr
      ⟨x.1, trivial, hyV ⟨_, hmem x⟩⟩
  refine ⟨S₁, h₁, s, inferInstance, fun b => V ⟨_, hmem b.1⟩,
    fun b => (g ⟨_, hmem b.1⟩).comp (MvPolynomial.renameEquiv _
      (finCongr (hdim b.1).symm)).toRingEquiv.toRingHom,
    fun b => hVa _, fun b => ?_, fun b => ?_, fun b => ⟨⟨b.1.1, hyV ⟨_, hmem b.1⟩⟩⟩,
    fun x hx => ?_⟩
  · exact RingHom.Etale.respectsIso.2 _ _ (hg _)
  · rw [RingHom.comp_assoc, ← hgC ⟨_, hmem b.1⟩]
    congr 1
    ext r
    simp
  · obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨⟨b, hb⟩, hxb⟩

/-- **A chart form is a multiple of the coordinate form.** In the situation of
`ordForm_eq_ord_of_isPullback`, the rational form `dz₁ ∧ ⋯ ∧ dzₙ` of the fibre is the germ of
`h₀` times the wedge of the differentials of the coordinates. -/
public lemma form_eq_smul_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] {V : Y.Opens} {n : ℕ}
    (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)) (W : Y.Opens)
    (hWV : W ≤ V) [Nonempty (fst ⁻¹ᵁ W)] (z : Fin n → Γ(Y, W)) (h₀ : Γ(Y, W))
    (hrel : letI := (q.appLE ⊤ W le_top).hom.toAlgebra
      exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W) (z i)) =
        h₀ • exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W)
          (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i))))) :
    letI := MMP.Mori.functionFieldAlgebra snd
    exteriorPower.ιMulti F.functionField n (fun i =>
        KaehlerDifferential.D L F.functionField
            (F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W (z i)))) =
      F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W h₀) •
        exteriorPower.ιMulti F.functionField n (fun i =>
          KaehlerDifferential.D L F.functionField (F.germToFunctionField (fst ⁻¹ᵁ W)
            (fst.app W (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i)))))) := by
  letI : Algebra Γ(Spec R, ⊤) Γ(Y, W) := (q.appLE ⊤ W le_top).hom.toAlgebra
  letI : Algebra Γ(Y, W) F.functionField :=
    (fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom.toAlgebra
  letI : Algebra Γ(Spec R, ⊤) L := (t.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom.toAlgebra
  letI := MMP.Mori.functionFieldAlgebra snd
  letI : Algebra Γ(Spec R, ⊤) F.functionField :=
    (q.appLE ⊤ W le_top ≫ fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom.toAlgebra
  have : IsScalarTower Γ(Spec R, ⊤) Γ(Y, W) F.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Spec R, ⊤) L F.functionField := IsScalarTower.of_algebraMap_eq' (by
    change (q.appLE ⊤ W le_top ≫ fst.app W ≫ F.germToFunctionField (fst ⁻¹ᵁ W)).hom = _
    rw [appLE_comp_germToFunctionField_of_isPullback hpb W]
    rfl)
  exact ιMulti_D_algebraMap_eq_smul (R := Γ(Spec R, ⊤)) (L := L) (K := F.functionField) z _
    h₀ hrel

/-- **Chart Jacobians as fractions.** Around a point of an open `O` in an affine chart `V` with
étale coordinates, there is a basic open `D(f) ⊆ O` of `V` on which the wedge of the differentials
of sections `z` over `O` is `h₀` times the coordinate form, with `h₀ f^N = a` for a section `a`
over `V`. -/
private lemma exists_chart_jacobian {Y : Scheme.{u}} {R : CommRingCat.{u}} (q : Y ⟶ Spec R)
    {V : Y.Opens} (hV : IsAffineOpen V) {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) (O : Y.Opens)
    (z : Fin n → Γ(Y, O)) (y : Y) (hyO : y ∈ O) (hyV : y ∈ V) :
    ∃ (f : Γ(Y, V)) (hfO : Y.basicOpen f ≤ O) (h₀ : Γ(Y, Y.basicOpen f)) (a : Γ(Y, V)) (N : ℕ),
      y ∈ Y.basicOpen f ∧
      (letI := (q.appLE ⊤ (Y.basicOpen f) le_top).hom.toAlgebra;
        exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
            (Y.presheaf.map (homOfLE hfO).op (z i))) =
          h₀ • exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
            KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
              (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g (MvPolynomial.X i))))) ∧
      h₀ * (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op f) ^ N =
        Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a := by
  obtain ⟨f, hfO, hyf⟩ := hV.exists_basicOpen_le (V := O) ⟨y, hyO⟩ hyV
  obtain ⟨h₀, hrel⟩ := exists_wedge_eq_smul q V hV g hg hgC f
    (fun i => Y.presheaf.map (homOfLE hfO).op (z i))
  letI : Algebra Γ(Y, V) Γ(Y, Y.basicOpen f) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(Y, Y.basicOpen f) := hV.isLocalization_basicOpen f
  obtain ⟨N, a, ha⟩ := IsLocalization.Away.surj f h₀
  exact ⟨f, hfO, h₀, a, N, hyf, hrel, ha⟩

/-- **Orders of a chart form through a fraction of sections.** In the situation of
`exists_chart_jacobian`, along a prime divisor of a fibre with generic point over the chart `V`,
the order of the rational form `dz₁ ∧ ⋯ ∧ dzₙ` is `v(a) - N v(f)`. -/
private lemma ordForm_eq_ord_sub_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] [IsLocallyNoetherian F] {V : Y.Opens}
    (hV : IsAffineOpen V) {n : ℕ} (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V))
    (hg : g.Etale) (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) {O : Y.Opens}
    (z : Fin n → Γ(Y, O)) (f : Γ(Y, V)) (hfO : Y.basicOpen f ≤ O) (h₀ : Γ(Y, Y.basicOpen f))
    (a : Γ(Y, V)) (N : ℕ)
    (hrel : letI := (q.appLE ⊤ (Y.basicOpen f) le_top).hom.toAlgebra;
        exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
          KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
            (Y.presheaf.map (homOfLE hfO).op (z i))) =
          h₀ • exteriorPower.ιMulti Γ(Y, Y.basicOpen f) n (fun i =>
            KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, Y.basicOpen f)
              (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (g (MvPolynomial.X i)))))
    (hfrac : h₀ * (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op f) ^ N =
        Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a)
    [Nonempty (fst ⁻¹ᵁ Y.basicOpen f)] [Nonempty (fst ⁻¹ᵁ V)] [Nonempty (fst ⁻¹ᵁ O)]
    (ha : F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V a) ≠ 0)
    (Γ : Mori.PrimeDivisor F) (hΓ : Γ.genericPoint ∈ fst ⁻¹ᵁ V) (ω : Mori.RationalTopForms snd n)
    (hω : letI := MMP.Mori.functionFieldAlgebra snd
      ω = exteriorPower.ιMulti F.functionField n fun i =>
        KaehlerDifferential.D L F.functionField (F.germToFunctionField (fst ⁻¹ᵁ O)
          (fst.app O (z i)))) :
    Γ.ordForm (ω.toPluriForms snd) =
      F.ord (F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V a)) Γ.genericPoint -
        N * F.ord (F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f)) Γ.genericPoint := by
  letI := MMP.Mori.functionFieldAlgebra snd
  have hfV : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have e := ordForm_eq_ord_of_isPullback hpb V hV g hg hgC (Y.basicOpen f) hfV
    (fun i => Y.presheaf.map (homOfLE hfO).op (z i)) h₀ hrel Γ hΓ ω (hω.trans (by
      first
      | (congr 1; funext i; rw [germToFunctionField_app_map fst hfO (z i)])
      | congr 1))
  rw [e]
  have hres : ∀ x : Γ(Y, V), F.germToFunctionField (fst ⁻¹ᵁ Y.basicOpen f)
      (fst.app _ (Y.presheaf.map (homOfLE hfV).op x)) =
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V x) := fun x =>
    germToFunctionField_app_map fst hfV x
  have hunit : IsUnit (Y.presheaf.map (homOfLE hfV).op f) :=
    Y.toRingedSpace.isUnit_res_basicOpen f
  have hf0 : F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f) ≠ 0 := by
    rw [← hres]
    exact ((hunit.map (fst.app _).hom).map (F.germToFunctionField _).hom).ne_zero
  have key : F.germToFunctionField (fst ⁻¹ᵁ Y.basicOpen f) (fst.app _ h₀) *
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f) ^ N =
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V a) := by
    rw [← hres, ← hres, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hfrac]
  have e2 : F.germToFunctionField (fst ⁻¹ᵁ Y.basicOpen f) (fst.app _ h₀) =
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V a) *
        F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f) ^ (-(N : ℤ)) := by
    rw [← key, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hf0), mul_one]
  rw [e2, Scheme.ord_mul ha (zpow_ne_zero _ hf0), MMP.Mori.ord_zpow _ hf0]
  ring

/-- **The coordinate form of an étale chart is a nonzero rational form** on every integral fibre
meeting the chart. -/
public lemma coordForm_ne_zero_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] {V : Y.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)) (hg : g.Etale)
    (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) [Nonempty (fst ⁻¹ᵁ V)] :
    letI := MMP.Mori.functionFieldAlgebra snd
    exteriorPower.ιMulti F.functionField n (fun i =>
        KaehlerDifferential.D L F.functionField
          (F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V (g (MvPolynomial.X i))))) ≠ 0 := by
  letI := MMP.Mori.functionFieldAlgebra snd
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty (fst ⁻¹ᵁ V)›
  obtain ⟨b, hb⟩ := exists_basis_kaehler_stalk_of_isPullback hpb V hV g hg hgC x hx
  letI := MMP.Mori.stalkAlgebra snd x
  haveI := MMP.Mori.isScalarTower_stalk_functionField snd x
  obtain ⟨-, h0⟩ := span_ιMulti_D_and_ne_zero snd x _ b hb
  rw [MMP.Mori.topFormsMap_ιMulti] at h0
  simp only [KaehlerDifferential.map_D] at h0
  convert h0 using 4 with i
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]

/-- **Chart forms with nonzero Jacobian are nonzero.** -/
private lemma form_ne_zero_of_isPullback {Y F : Scheme.{u}} {R : CommRingCat.{u}} {L : Type u}
    [Field L] {q : Y ⟶ Spec R} {t : Spec (.of L) ⟶ Spec R} {fst : F ⟶ Y} {snd : F ⟶ Spec (.of L)}
    (hpb : IsPullback fst snd q t) [IsIntegral F] {V : Y.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (g : MvPolynomial (Fin n) Γ(Spec R, ⊤) →+* Γ(Y, V)) (hg : g.Etale)
    (hgC : g.comp MvPolynomial.C = (q.appLE ⊤ V le_top).hom) (W : Y.Opens)
    (hWV : W ≤ V) [Nonempty (fst ⁻¹ᵁ W)] (z : Fin n → Γ(Y, W)) (h₀ : Γ(Y, W))
    (hrel : letI := (q.appLE ⊤ W le_top).hom.toAlgebra
      exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W) (z i)) =
        h₀ • exteriorPower.ιMulti Γ(Y, W) n (fun i => KaehlerDifferential.D Γ(Spec R, ⊤) Γ(Y, W)
          (Y.presheaf.map (homOfLE hWV).op (g (MvPolynomial.X i)))))
    (h0 : F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W h₀) ≠ 0) :
    letI := MMP.Mori.functionFieldAlgebra snd
    exteriorPower.ιMulti F.functionField n (fun i =>
        KaehlerDifferential.D L F.functionField
          (F.germToFunctionField (fst ⁻¹ᵁ W) (fst.app W (z i)))) ≠ 0 := by
  letI := MMP.Mori.functionFieldAlgebra snd
  haveI : Nonempty (fst ⁻¹ᵁ V) := by
    obtain ⟨x⟩ := ‹Nonempty (fst ⁻¹ᵁ W)›
    exact ⟨⟨x.1, hWV x.2⟩⟩
  rw [form_eq_smul_of_isPullback hpb g W hWV z h₀ hrel]
  refine smul_ne_zero h0 ?_
  convert coordForm_ne_zero_of_isPullback hpb hV g hg hgC using 4 with i
  exact germToFunctionField_app_map fst hWV _

/-- A prime divisor meeting an open has its generic point in the open. -/
private lemma genericPoint_mem_of_nonempty {F : Scheme.{u}} (E : Mori.PrimeDivisor F) (U : F.Opens)
    (h : (E.support ∩ U).Nonempty) : E.genericPoint ∈ U := by
  obtain ⟨x, hxE, hxU⟩ := h
  have hsp : E.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxE
  exact hsp.mem_open U.isOpen hxU

/-- A nonzero rational function has nonzero order along only finitely many prime divisors. -/
private lemma finite_ord_ne_zero_of_ne_zero {F : Scheme.{u}} [IsIntegral F] [IsLocallyNoetherian F]
    [IsNormal F] [CompactSpace F] {g : F.functionField} (hg : g ≠ 0) :
    {E : Mori.PrimeDivisor F | F.ord g E.genericPoint ≠ 0}.Finite := by
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hg
  refine (Mori.principalDivisor φ).support.finite_toSet.subset fun E hE => ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  change (Mori.principalDivisor φ).coeff E ≠ 0
  rw [Mori.coeff_principalDivisor, hφ]
  exact hE

/-- A section is a unit on its basic open, so its germ is nonzero on an integral scheme over it. -/
private lemma germ_ne_zero_of_basicOpen {F Y : Scheme.{u}} [IsIntegral F] (fst : F ⟶ Y)
    {V : Y.Opens}
    (f : Γ(Y, V)) [Nonempty (fst ⁻¹ᵁ Y.basicOpen f)] [Nonempty (fst ⁻¹ᵁ V)] :
    F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f) ≠ 0 := by
  rw [← germToFunctionField_app_map fst (Y.basicOpen_le f) f]
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op f) :=
    Y.toRingedSpace.isUnit_res_basicOpen f
  exact ((hu.map (fst.app _).hom).map (F.germToFunctionField _).hom).ne_zero

/-- Germs of a fraction `h₀ = a / f^N` on a basic open. -/
private lemma germ_mul_pow_eq_of_frac {F Y : Scheme.{u}} [IsIntegral F] (fst : F ⟶ Y) {V : Y.Opens}
    (f : Γ(Y, V)) (h₀ : Γ(Y, Y.basicOpen f)) (a : Γ(Y, V)) (N : ℕ)
    (hfrac : h₀ * (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op f) ^ N =
        Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op a)
    [Nonempty (fst ⁻¹ᵁ Y.basicOpen f)] [Nonempty (fst ⁻¹ᵁ V)] :
    F.germToFunctionField (fst ⁻¹ᵁ Y.basicOpen f) (fst.app _ h₀) *
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V f) ^ N =
      F.germToFunctionField (fst ⁻¹ᵁ V) (fst.app V a) := by
  rw [← germToFunctionField_app_map fst (Y.basicOpen_le f) f,
    ← germToFunctionField_app_map fst (Y.basicOpen_le f) a, ← map_pow, ← map_pow, ← map_mul,
    ← map_mul, hfrac]

open Classical in
include hint in
/-- **Orders of a rational top form spread to the fibres.** Let `dz₁ ∧ ⋯ ∧ dzₙ` be a nonzero
rational top form of a normal vertex given by sections `z` of a stage over an open `O`, and let
the vertex be covered in codimension one by étale charts of the stage. There is a finite set `T₀`
of prime divisors such that for every finite `T ⊇ T₀` with models, on every late fibre the form
`dz₁ ∧ ⋯ ∧ dzₙ` is nonzero and its order along each prime divisor is the sum of its orders along
the prime divisors of `T` of which it is the fibre. -/
public lemma Model.exists_form_spreading {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left] [CompactSpace (X.obj j).left]
    {n : ℕ} {B : Type u} [Finite B] (V : B → ((M.stage h₀).obj j).left.Opens)
    (g : ∀ b, MvPolynomial (Fin n) Γ(Spec (.of S₀.1), ⊤) →+* Γ(((M.stage h₀).obj j).left, V b))
    (hVa : ∀ b, IsAffineOpen (V b)) (hg : ∀ b, (g b).Etale)
    (hgC : ∀ b, (g b).comp MvPolynomial.C =
      (((M.stage h₀).obj j).hom.appLE ⊤ (V b) le_top).hom)
    (hVne : ∀ b, Nonempty (M.cmp h₀ j ⁻¹ᵁ V b))
    (hcov : ∀ x : (X.obj j).left, Order.coheight x ≤ 1 → ∃ b, M.cmp h₀ j x ∈ V b)
    (O : ((M.stage h₀).obj j).left.Opens) [Nonempty (M.cmp h₀ j ⁻¹ᵁ O)]
    (z : Fin n → Γ(((M.stage h₀).obj j).left, O)) (σK : Mori.RationalTopForms (X.obj j).hom n)
    (hσK : letI := MMP.Mori.functionFieldAlgebra (X.obj j).hom
      σK = exteriorPower.ιMulti (X.obj j).left.functionField n fun i =>
        KaehlerDifferential.D K (X.obj j).left.functionField
          ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ O) ((M.cmp h₀ j).app O (z i))))
    (hσ0 : σK ≠ 0) :
    ∃ T₀ : Finset (Mori.PrimeDivisor (X.obj j).left), ∀ T, T₀ ⊆ T →
      ∀ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
        (𝓘 : Mori.PrimeDivisor (X.obj j).left →
          ((M.stage (h₀.trans h₁)).obj j).left.IdealSheafData),
        (∀ E ∈ T, (𝓘 E).comap (M.cmp (h₀.trans h₁) j) = E.idealSheaf) →
      EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
        [IsIntegral ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
        [IsLocallyNoetherian ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left],
        topologicalKrullDim ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        (∀ E ∈ T, ∃ Ps : Mori.PrimeDivisor
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j)) →
        genericPoint ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left ∈
          M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ O ∧
        ∀ [Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ O)]
          (σ : Mori.RationalTopForms
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).hom n),
          (letI := MMP.Mori.functionFieldAlgebra
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).hom;
            σ = exteriorPower.ιMulti
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left.functionField n
              fun i => KaehlerDifferential.D L
                ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left.functionField
                (((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj
                    j).left.germToFunctionField
                  (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ O)
                  ((M.fibreMap h₀ (h₁.trans hS) t j).app O (z i)))) →
          σ ≠ 0 ∧
          ∀ Γ : Mori.PrimeDivisor
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
            Γ.ordForm (σ.toPluriForms _) =
              ∑ E ∈ T, if Γ.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j) then
                E.ordForm (σK.toPluriForms (X.obj j).hom) else 0 := by
  have := hint j
  have := Fintype.ofFinite B
  have hpbK := (M.isCartesian_cmp h₀).isPullback j
  have hgen : ∀ U : (X.obj j).left.Opens, Nonempty U → genericPoint (X.obj j).left ∈ U :=
    fun U hU => ((genericPoint_spec (X.obj j).left).mem_open_set_iff U.isOpen).mpr
      (Set.univ_inter _ ▸ (Set.nonempty_coe_sort.mp hU))
  have hηO : genericPoint (X.obj j).left ∈ M.cmp h₀ j ⁻¹ᵁ O := hgen _ inferInstance
  have hηV : ∀ b, genericPoint (X.obj j).left ∈ M.cmp h₀ j ⁻¹ᵁ V b := fun b => hgen _ (hVne b)
  choose f hfO h a N hyf hrel hfrac using fun b =>
    exists_chart_jacobian ((M.stage h₀).obj j).hom (hVa b) (g b) (hg b) (hgC b) O z
      (M.cmp h₀ j (genericPoint (X.obj j).left)) hηO (hηV b)
  have hneK : ∀ b, Nonempty (M.cmp h₀ j ⁻¹ᵁ ((M.stage h₀).obj j).left.basicOpen (f b)) :=
    fun b => ⟨⟨_, hyf b⟩⟩
  have hfK : ∀ b, (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V b)
      ((M.cmp h₀ j).app (V b) (f b)) ≠ 0 := fun b =>
    haveI := hneK b; haveI := hVne b; germ_ne_zero_of_basicOpen _ (f b)
  have haK : ∀ b, (X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V b)
      ((M.cmp h₀ j).app (V b) (a b)) ≠ 0 := by
    intro b ha0
    haveI := hneK b; haveI := hVne b
    have key := germ_mul_pow_eq_of_frac (M.cmp h₀ j) (f b) (h b) (a b) (N b) (hfrac b)
    rw [ha0] at key
    have hh0 := (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ (hfK b))
    apply hσ0
    letI := MMP.Mori.functionFieldAlgebra (X.obj j).hom
    rw [hσK]
    have e := form_eq_smul_of_isPullback hpbK (g b) _
      (((M.stage h₀).obj j).left.basicOpen_le (f b))
      (fun i => ((M.stage h₀).obj j).left.presheaf.map (homOfLE (hfO b)).op (z i)) (h b) (hrel b)
    rw [hh0, zero_smul] at e
    have e' : (exteriorPower.ιMulti (X.obj j).left.functionField n fun i =>
        KaehlerDifferential.D K (X.obj j).left.functionField
          ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ O) ((M.cmp h₀ j).app O (z i)))) =
        exteriorPower.ιMulti (X.obj j).left.functionField n fun i =>
        KaehlerDifferential.D K (X.obj j).left.functionField
          ((X.obj j).left.germToFunctionField _ ((M.cmp h₀ j).app _
            (((M.stage h₀).obj j).left.presheaf.map (homOfLE (hfO b)).op (z i)))) := by
      congr 1
      funext i
      rw [germToFunctionField_app_map (M.cmp h₀ j) (hfO b) (z i)]
    exact e'.trans e
  let T₀ : Finset (Mori.PrimeDivisor (X.obj j).left) := Finset.univ.biUnion fun b =>
    (finite_ord_ne_zero_of_ne_zero (haK b)).toFinset ∪
      (finite_ord_ne_zero_of_ne_zero (hfK b)).toFinset
  refine ⟨T₀, fun T hT S₁ h₁ 𝓘 h𝓘 => ?_⟩
  have hTa : ∀ b (E : Mori.PrimeDivisor (X.obj j).left),
      (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V b).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V b)
        ((M.cmp h₀ j).app (V b) (a b))) E.genericPoint ≠ 0 → E ∈ T := fun b E _ hE =>
    hT (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_union_left _
      ((Set.Finite.mem_toFinset _).mpr hE)⟩)
  have hTf : ∀ b (E : Mori.PrimeDivisor (X.obj j).left),
      (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V b).Nonempty →
      Scheme.ord ((X.obj j).left.germToFunctionField (M.cmp h₀ j ⁻¹ᵁ V b)
        ((M.cmp h₀ j).app (V b) (f b))) E.genericPoint ≠ 0 → E ∈ T := fun b E _ hE =>
    hT (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_union_right _
      ((Set.Finite.mem_toFinset _).mpr hE)⟩)
  have eB := EvAbove.forall_of_finite fun b => by
    haveI := hVne b
    haveI := hneK b
    have e1 := M.exists_ord_section_of_le hint h₀ h₁ j (V b) (a b) (haK b) T 𝓘 h𝓘 (hTa b)
    have e2 := M.exists_ord_section_of_le hint h₀ h₁ j (V b) (f b) (hfK b) T 𝓘 h𝓘 (hTf b)
    have e3 : EvAbove S₁ fun S hS => ∀ E ∈ T, ¬ (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V b).Nonempty →
        ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
        (Γ : Mori.PrimeDivisor
          ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left),
        Γ.idealSheaf = (𝓘 E).comap (M.fibreMap (h₀.trans h₁) hS t j) →
        ¬ (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V b).Nonempty := by
      refine EvAbove.forall_finset T fun E hE => ?_
      by_cases hEV : (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V b).Nonempty
      · exact (EvAbove.true S₁).mono fun S hS _ h' => absurd hEV h'
      · exact (M.evAbove_disjoint_of_le h₀ h₁ j (h𝓘 E hE) (V b) hEV).mono
          fun S hS H _ => H
    have e4 := (M.evAbove_genericPoint_mem hint h₀ j
      (((M.stage h₀).obj j).left.basicOpen (f b))).of_le h₁
    exact (e1.and e2).and (e3.and e4)
  have eO := (M.evAbove_genericPoint_mem hint h₀ j O).of_le h₁
  have hU : ∀ x : (X.obj j).left, M.cmp h₀ j x ∉ ⨆ b, V b →
      ((2 : ℕ) : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    by_contra hlt
    have hle : Order.coheight x ≤ 1 := by
      have : Order.coheight x < 1 + 1 := by
        rw [not_le] at hlt
        exact_mod_cast hlt
      exact Order.le_of_lt_add_one this
    obtain ⟨b, hb⟩ := hcov x hle
    exact hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨b, hb⟩)
  have eC := (M.evAbove_le_coheight hint h₀ j _ 2 hU).of_le h₁
  refine ((eB.and eO).and eC).mono fun S hS H L _ t _ _ hd hmod => ?_
  obtain ⟨⟨HB, HO⟩, HC⟩ := H
  have hpbF := M.isPullback_fibreMap h₀ (h₁.trans hS) t j
  refine ⟨HO L t hd, fun σ hσ => ⟨?_, fun Γ => ?_⟩⟩
  · obtain ⟨b, hb⟩ := hcov (genericPoint (X.obj j).left)
      ((Stacks.EtaleCohomology.coheight_genericPoint_eq_zero _).trans_le zero_le_one)
    obtain ⟨⟨Ha, -⟩, -, Hg⟩ := HB b
    haveI : Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ
        ((M.stage h₀).obj j).left.basicOpen (f b)) := ⟨⟨_, Hg L t hd⟩⟩
    haveI : Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V b) :=
      ⟨⟨_, ((M.stage h₀).obj j).left.basicOpen_le (f b) (Hg L t hd)⟩⟩
    obtain ⟨ha0, -⟩ := Ha L t hd hmod
    have key := germ_mul_pow_eq_of_frac (M.fibreMap h₀ (h₁.trans hS) t j) (f b) (h b) (a b)
      (N b) (hfrac b)
    have hh0 := left_ne_zero_of_mul (by rwa [key])
    have hne := form_ne_zero_of_isPullback hpbF (hVa b) (g b) (hg b) (hgC b) _
      (((M.stage h₀).obj j).left.basicOpen_le (f b))
      (fun i => ((M.stage h₀).obj j).left.presheaf.map (homOfLE (hfO b)).op (z i)) (h b)
      (hrel b) hh0
    rw [hσ]
    refine ne_of_eq_of_ne ?_ hne
    congr 1
    funext i
    rw [germToFunctionField_app_map _ (hfO b) (z i)]
  · have hη : M.fibreMap h₀ (h₁.trans hS) t j Γ.genericPoint ∈ ⨆ b, V b := by
      by_contra hn
      have := HC L t inferInstance hd _ hn
      rw [Γ.coheight_genericPoint] at this
      exact absurd this (by decide)
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hη
    obtain ⟨⟨Ha, Hf⟩, Hd, Hg⟩ := HB b
    haveI : Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ
        ((M.stage h₀).obj j).left.basicOpen (f b)) := ⟨⟨_, Hg L t hd⟩⟩
    haveI : Nonempty (M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V b) := ⟨⟨_, hb⟩⟩
    obtain ⟨ha0, Ha2⟩ := Ha L t hd hmod
    obtain ⟨-, Hf2⟩ := Hf L t hd hmod
    have hmeet : (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ V b).Nonempty :=
      ⟨_, genericPoint_mem_support Γ, hb⟩
    have e := ordForm_eq_ord_sub_of_isPullback hpbF (hVa b) (g b) (hg b) (hgC b) z (f b) (hfO b)
      (h b) (a b) (N b) (hrel b) (hfrac b) ha0 Γ hb σ hσ
    refine e.trans ?_
    rw [Ha2 Γ hmeet, Hf2 Γ hmeet, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun E hE => ?_
    split_ifs with hΓE
    · have hEm : (E.support ∩ M.cmp h₀ j ⁻¹ᵁ V b).Nonempty := by
        by_contra hn
        exact Hd E hE hn L t Γ hΓE hmeet
      haveI := hneK b; haveI := hVne b
      rw [ordForm_eq_ord_sub_of_isPullback hpbK (hVa b) (g b) (hg b) (hgC b) z (f b) (hfO b)
        (h b) (a b) (N b) (hrel b) (hfrac b) (haK b) E (genericPoint_mem_of_nonempty E _ hEm)
        σK hσK]
    · simp

/-- The map of function fields of a dominant morphism sends the germ of a section to the germ of
its pull-back. -/
public lemma functionFieldMap_germToFunctionField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] (V : Y.Opens) [Nonempty V] (W : X.Opens)
    [Nonempty W] (hVW : W ≤ f ⁻¹ᵁ V) (s : Γ(Y, V)) :
    AlgebraicGeometry.functionFieldMap f (Y.germToFunctionField V s) =
      X.germToFunctionField W (f.appLE V W hVW s) := by
  simp only [AlgebraicGeometry.functionFieldMap, Scheme.germToFunctionField,
    TopCat.Presheaf.stalkCongr_hom, Scheme.Hom.appLE, ← ConcreteCategory.comp_apply,
    Category.assoc, TopCat.Presheaf.germ_res, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.Hom.germ_stalkMap]
  erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

/-- Germs of pull-backs along equal morphisms agree. -/
private lemma germ_app_congr {F Y : Scheme.{u}} [IsIntegral F] {f f' : F ⟶ Y} (h : f = f')
    (V : Y.Opens) (s : Γ(Y, V)) [Nonempty (f ⁻¹ᵁ V)] [Nonempty (f' ⁻¹ᵁ V)] :
    F.germToFunctionField (f ⁻¹ᵁ V) (f.app V s) = F.germToFunctionField (f' ⁻¹ᵁ V) (f'.app V s) :=
        by
  subst h
  rfl

/-- **Germs along a commutative square.** If `F ⟶ Y` and `G ⟶ Y'` are compatible with a dominant
morphism `φ : F ⟶ G` and `m : Y ⟶ Y'`, the germ in `k(F)` of the pull-back along `m` of a section
of `Y'` is the image under `φ^*` of its germ in `k(G)`. -/
public lemma germ_app_eq_functionFieldMap {F G Y Y' : Scheme.{u}} [IsIntegral F] [IsIntegral G]
    (φ : F ⟶ G) [IsDominant φ] (fm : F ⟶ Y) (fm' : G ⟶ Y') (m : Y ⟶ Y')
    (hsq : fm ≫ m = φ ≫ fm') (V : Y'.Opens) (s : Γ(Y', V)) [Nonempty (fm' ⁻¹ᵁ V)]
    [Nonempty (fm ⁻¹ᵁ (m ⁻¹ᵁ V))] :
    F.germToFunctionField (fm ⁻¹ᵁ (m ⁻¹ᵁ V)) (fm.app _ (m.app V s)) =
      AlgebraicGeometry.functionFieldMap φ (G.germToFunctionField (fm' ⁻¹ᵁ V) (fm'.app V s)) := by
  have e1 : fm ⁻¹ᵁ (m ⁻¹ᵁ V) = φ ⁻¹ᵁ (fm' ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq]
  haveI : Nonempty ((fm ≫ m) ⁻¹ᵁ V) := by rw [Scheme.Hom.comp_preimage]; infer_instance
  haveI : Nonempty (φ ⁻¹ᵁ (fm' ⁻¹ᵁ V)) := by rw [← e1]; infer_instance
  haveI : Nonempty ((φ ≫ fm') ⁻¹ᵁ V) := by rw [Scheme.Hom.comp_preimage]; infer_instance
  rw [functionFieldMap_germToFunctionField φ _ (φ ⁻¹ᵁ (fm' ⁻¹ᵁ V)) le_rfl,
    ← Scheme.Hom.app_eq_appLE, germToFunctionField_app_app_of_comp_eq fm m _ rfl V s,
    germToFunctionField_app_app_of_comp_eq φ fm' _ rfl V s]
  exact germ_app_congr hsq V s

/-- **Pull-back of a wedge of differentials.** Along a birational morphism of integral schemes of
dimension `n` over a perfect field, the pull-back of `dw₁ ∧ ⋯ ∧ dwₙ` is
`d(μ^*w₁) ∧ ⋯ ∧ d(μ^*wₙ)`. -/
public lemma pullbackRationalPluriForms_ιMulti {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] [LocallyOfFiniteType sZ] (μ : W ⟶ Z) [IsIntegral W]
    [IsDominant μ] (hbij : Function.Bijective (AlgebraicGeometry.functionFieldMap μ)) {n : ℕ}
    (hn : topologicalKrullDim Z = n) (ω : Mori.RationalTopForms sZ n) (hω : ω ≠ 0)
    (w : Fin n → Z.functionField)
    (hωw : letI := MMP.Mori.functionFieldAlgebra sZ
      ω = exteriorPower.ιMulti Z.functionField n fun i => KaehlerDifferential.D k Z.functionField
          (w i))
    (ω' : Mori.RationalTopForms (μ ≫ sZ) n)
    (hω' : letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
      ω' = exteriorPower.ιMulti W.functionField n fun i =>
        KaehlerDifferential.D k W.functionField (AlgebraicGeometry.functionFieldMap μ (w i))) :
    Mori.pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ) = ω'.toPluriForms (μ ≫ sZ) := by
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective sZ μ hbij
    (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have hω₁ := isPullbackGenerator_of_ne_zero hω₀ hω
  have := MMP.Fourfold.pullbackForms_smul_formPow hω₁ 1 (1 : Z.functionField)
  rw [one_smul, map_one, one_smul] at this
  change _ = MMP.Fourfold.formPow (ω' : ⋀[W.functionField]^n Ω[W.functionField⁄k]) 1
  refine this.trans ?_
  congr 1
  rw [hω', hωw, MMP.Mori.topFormsMap_ιMulti]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- **Orders of a wedge of differentials do not depend on the presentation of the structure
morphism.** -/
public lemma ordForm_congr_hom {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] {s s' : X ⟶ Spec (.of k)} (h : s = s') {n : ℕ}
    (w : Fin n → X.functionField) (ω : Mori.RationalTopForms s n)
    (hω : letI := MMP.Mori.functionFieldAlgebra s
      ω = exteriorPower.ιMulti X.functionField n fun i => KaehlerDifferential.D k X.functionField
          (w i))
    (ω' : Mori.RationalTopForms s' n)
    (hω' : letI := MMP.Mori.functionFieldAlgebra s'
      ω' = exteriorPower.ιMulti X.functionField n fun i => KaehlerDifferential.D k X.functionField
          (w i))
    (Γ : Mori.PrimeDivisor X) :
    Γ.ordForm (ω.toPluriForms s) = Γ.ordForm (ω'.toPluriForms s') := by
  subst h
  rw [hω.trans hω'.symm]

/-- The comparison of a fibre with an earlier stage is natural in the vertex. -/
public lemma Model.fibreMap_naturality {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) {j j' : J}
    (g : j ⟶ j') :
    ((M.stage (h₀.trans h) ⋙ Over.pullback t).map g).left ≫ M.fibreMap h₀ h t j' =
      M.fibreMap h₀ h t j ≫ ((M.stage h₀).map g).left := by
  dsimp only [Model.fibreMap]
  rw [← Category.assoc, (isCartesian_pullback t (M.stage (h₀.trans h))).w g, Category.assoc,
    (M.isCartesian_stageCmp h₀ h).w g, Category.assoc]

open Classical in
/-- Sums of coefficients of a `ℚ`-divisor `∑ₗ qₗ Pₗ` over the prime divisors related to a given
one. -/
private lemma sum_ite_coeff_sum_single {X : Type*} [DecidableEq X] (T : Finset X) (R : X → Prop)
    {m : ℕ} (P : Fin m → X) (hP : ∀ l, P l ∈ T) (q : Fin m → ℚ) :
    (∑ E ∈ T, if R E then ((∑ l, Finsupp.single (P l) (q l) : X →₀ ℚ) E) else 0) =
      ∑ l, if R (P l) then q l else 0 := by
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_congr rfl fun E _ => (show (if R E then ∑ l, (if P l = E then q l else 0) else 0) =
    ∑ l, (if P l = E then (if R E then q l else 0) else 0) by
      split_ifs with h <;> simp [h])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq]
  simp [hP l]

open Classical in
/-- **Crepant boundaries on a fibre from spreading data.** Let `μ : W ⟶ Z` and `μₛ : Wₛ ⟶ Zₛ`
be birational morphisms of normal varieties of dimension `n` over perfect fields, related by
finite sets `T_Z`, `T_W` of prime divisors of `Z`, `W` and relations `R_Z`, `R_W` (a prime divisor
of the fibre is the fibre of one of `T`). If the orders of a nonzero top form `ω` on `Z` and of
its pull-back to `W` are carried to those of a top form `ωₛ` and its pull-back, the boundaries
correspond, and every Cartier divisor supported on `T₁ ⊆ T_Z` has local equations on `Z` and the
fibre related in the same way, then a crepant boundary over `Z` gives a crepant boundary over the
fibre with the same coefficients. -/
public lemma isCrepantBoundary_of_spreading {K L : Type u} [Field K] [PerfectField K] [Field L]
    [PerfectField L] {Z W Zs Ws : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of K)} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [LocallyOfFiniteType sZ] (hZ : Mori.IsNormalVariety K sZ) {n : ℕ}
        (hn : topologicalKrullDim Z = n)
    {μ : W ⟶ Z} (hW : Mori.IsNormalVariety K (μ ≫ sZ)) (hμ : Mori.IsBirationalMorphism μ)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (hnW : topologicalKrullDim W = n)
    {sZs : Zs ⟶ Spec (.of L)} [IsIntegral Zs] [IsLocallyNoetherian Zs] [IsNormal Zs]
    [CompactSpace Zs] [LocallyOfFiniteType sZs] (hZs : Mori.IsNormalVariety L sZs)
    (hns : topologicalKrullDim Zs = n)
    {μs : Ws ⟶ Zs} (hWs : Mori.IsNormalVariety L (μs ≫ sZs)) (hμs : Mori.IsBirationalMorphism μs)
    [IsIntegral Ws] [IsLocallyNoetherian Ws] [IsNormal Ws] (hnWs : topologicalKrullDim Ws = n)
    (TZ : Finset (Mori.PrimeDivisor Z)) (RZ : Mori.PrimeDivisor Zs → Mori.PrimeDivisor Z → Prop)
    (hRZ : ∀ E Γ Γ', RZ Γ E → RZ Γ' E → Γ = Γ')
    (TW : Finset (Mori.PrimeDivisor W)) (RW : Mori.PrimeDivisor Ws → Mori.PrimeDivisor W → Prop)
    {ω : Mori.RationalTopForms sZ n} (hω : ω ≠ 0) {ωs : Mori.RationalTopForms sZs n}
    (hωs : ωs ≠ 0)
    (hZf : ∀ Γ : Mori.PrimeDivisor Zs, Γ.ordForm (ωs.toPluriForms sZs) =
      ∑ E ∈ TZ, if RZ Γ E then E.ordForm (ω.toPluriForms sZ) else 0)
    (hWf : haveI := hμ.isDominant; haveI := hμs.isDominant;
      ∀ F : Mori.PrimeDivisor Ws,
      F.ordForm (Mori.pullbackRationalPluriForms sZs μs (ωs.toPluriForms sZs)) =
        ∑ E ∈ TW, if RW F E then E.ordForm (Mori.pullbackRationalPluriForms sZ μ
            (ω.toPluriForms sZ))
          else 0)
    (T₁ : Finset (Mori.PrimeDivisor Z)) (hT₁ : T₁ ⊆ TZ)
    (hT₁ω : ∀ E, E.ordForm (ω.toPluriForms sZ) ≠ 0 → E ∈ T₁)
    (hgood : haveI := hμ.isDominant; haveI := hμs.isDominant;
      ∀ D : Mori.Divisor Z, D.IsCartier → (∀ E, D.coeff E ≠ 0 → E ∈ T₁) → ∀ x : Zs,
      ∃ (U : Zs.Opens) (ψ : Zs.functionField) (UK : Z.Opens) (φ : Z.functionField),
        x ∈ U ∧ ψ ≠ 0 ∧ φ ≠ 0 ∧
        (∀ Γ : Mori.PrimeDivisor Zs, (Γ.support ∩ U).Nonempty →
          (∑ E ∈ TZ, if RZ Γ E then D.coeff E else 0) = Zs.ord ψ Γ.genericPoint) ∧
        (∀ E : Mori.PrimeDivisor Z, (E.support ∩ UK).Nonempty →
          D.coeff E = Z.ord φ E.genericPoint) ∧
        ∀ F : Mori.PrimeDivisor Ws, μs F.genericPoint ∈ U →
          Ws.ord (AlgebraicGeometry.functionFieldMap μs ψ) F.genericPoint =
            (∑ E ∈ TW, if RW F E then
              W.ord (AlgebraicGeometry.functionFieldMap μ φ) E.genericPoint else 0) ∧
          ∀ E ∈ TW, RW F E → μ E.genericPoint ∈ UK)
    {m₁ : ℕ} (P : Fin m₁ → Mori.PrimeDivisor Z) (q : Fin m₁ → ℚ)
    (Ps : Fin m₁ → Mori.PrimeDivisor Zs) (hPT : ∀ l, P l ∈ T₁)
    (hPs : ∀ l Γ, RZ Γ (P l) ↔ Γ = Ps l)
    {m₂ : ℕ} (P' : Fin m₂ → Mori.PrimeDivisor W) (q' : Fin m₂ → ℚ)
    (Ps' : Fin m₂ → Mori.PrimeDivisor Ws) (hP'T : ∀ l, P' l ∈ TW)
    (hPs' : ∀ l F, RW F (P' l) ↔ F = Ps' l)
    (K₀ : Mori.Divisor Z)
    (hCr : Mori.IsCrepantBoundary sZ n K₀ (∑ l, Finsupp.single (P l) (q l)) μ hW hμ
      (∑ l, Finsupp.single (P' l) (q' l))) :
    Mori.IsCrepantBoundary sZs n (Mori.topFormDivisor sZs ωs) (∑ l, Finsupp.single (Ps l) (q l))
      μs hWs hμs (∑ l, Finsupp.single (Ps' l) (q' l)) := by
  haveI := hμ.isDominant
  haveI := hμs.isDominant
  have : LocallyOfFiniteType (μ ≫ sZ) := hW.1.toLocallyOfFiniteType
  intro Fs
  -- a prime divisor of `W`
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hne : genericPoint Ws ≠ Fs.genericPoint := fun h => by
      have := Fs.coheight_genericPoint
      rw [← h, Stacks.EtaleCohomology.coheight_genericPoint_eq_zero] at this
      exact absurd this (by decide)
    have := one_le_topologicalKrullDim_of_specializes_of_ne (genericPoint_specializes _) hne
    rw [hnWs] at this
    exact absurd this (by decide)
  obtain ⟨F₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hnW hn0
  have hK₀ : K₀.IsCanonicalDivisor sZ n := (hCr F₀).2.1
  have ha₀ := isDiscrepancy_of_linearlyEquivalent (hCr F₀)
    (CanonExist.linearlyEquivalent_topFormDivisor hZ hn hω hK₀)
  obtain ⟨-, -, m, hm, ⟨D, hD, hDc⟩, -⟩ := ha₀
  have hcoeff : ∀ E : Mori.PrimeDivisor Z, (D.coeff E : ℚ) =
      m * ((E.ordForm (ω.toPluriForms sZ) : ℚ) +
        (∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor Z).coeff E) := by
    intro E
    have := congrArg (fun G : Mori.QDivisor Z => G.coeff E) hD
    simp only [Mori.Divisor.coeff_toQDivisor, Mori.DivisorWithCoeffs.coeff_smul,
      Mori.DivisorWithCoeffs.coeff_add, Mori.coeff_topFormDivisor] at this
    rw [this, zsmul_eq_mul]
    push_cast
    ring
  have hDT : ∀ E, D.coeff E ≠ 0 → E ∈ T₁ := by
    intro E hE
    by_contra hET
    apply hE
    have h1 : E.ordForm (ω.toPluriForms sZ) = 0 := by
      by_contra h
      exact hET (hT₁ω E h)
    have h2 : (∑ l, Finsupp.single (P l) (q l) : Mori.QDivisor Z).coeff E = 0 := by
      change (∑ l, Finsupp.single (P l) (q l) : Mori.PrimeDivisor Z →₀ ℚ) E = 0
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hET (hPT l)
    have := hcoeff E
    rw [h1, h2] at this
    exact_mod_cast (by simpa using this : (D.coeff E : ℚ) = 0)
  -- the divisor on the fibre
  let Ds : Mori.Divisor Zs := ∑ E ∈ TZ, D.coeff E •
    (if h : ∃ Γ, RZ Γ E then Finsupp.single h.choose (1 : ℤ) else 0)
  have hDs : ∀ Γ, Ds.coeff Γ = ∑ E ∈ TZ, if RZ Γ E then D.coeff E else 0 := by
    intro Γ
    change (Ds : Mori.PrimeDivisor Zs →₀ ℤ) Γ = _
    simp only [Ds, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs with h1 h2 h2
    · rw [Finsupp.single_apply, if_pos (hRZ E _ _ h1.choose_spec h2), mul_one]
    · rw [Finsupp.single_apply, if_neg (fun e : h1.choose = Γ => h2 (e ▸ h1.choose_spec)),
        mul_zero]
    · exact absurd ⟨Γ, h2⟩ h1
    · simp
  have hDsc : Ds.IsCartier := by
    intro x
    obtain ⟨U, ψ, UK, φ, hxU, hψ, -, hloc, -⟩ := hgood D hDc hDT x
    obtain ⟨φu, hφu⟩ := MMP.Positivity.exists_units_of_ne_zero hψ
    exact ⟨U, hxU, φu, fun Γ hΓ => by rw [hDs, hloc Γ hΓ, hφu]⟩
  have hDsQ : Mori.Divisor.toQDivisor Ds = (m : ℤ) •
      (Mori.Divisor.toQDivisor (Mori.topFormDivisor sZs ωs) +
        ∑ l, Finsupp.single (Ps l) (q l)) := by
    ext Γ
    change (Mori.Divisor.toQDivisor Ds).coeff Γ = (((m : ℤ) • (Mori.Divisor.toQDivisor
      (Mori.topFormDivisor sZs ωs) + ∑ l, Finsupp.single (Ps l) (q l))) : Mori.QDivisor Zs).coeff Γ
    simp only [Mori.Divisor.coeff_toQDivisor, Mori.DivisorWithCoeffs.coeff_smul,
      Mori.DivisorWithCoeffs.coeff_add, Mori.coeff_topFormDivisor, hDs, hZf]
    push_cast
    rw [zsmul_eq_mul]
    simp only [apply_ite (fun x : ℤ => (x : ℚ)), Int.cast_zero, hcoeff]
    have hΔ := sum_ite_coeff_sum_single TZ (fun E => RZ Γ E) P (fun l => hT₁ (hPT l)) q
    have hΔs : (∑ l, Finsupp.single (Ps l) (q l) : Mori.QDivisor Zs).coeff Γ =
        ∑ l, if RZ Γ (P l) then q l else 0 := by
      change (∑ l, Finsupp.single (Ps l) (q l) : Mori.PrimeDivisor Zs →₀ ℚ) Γ = _
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finsupp.single_apply]
      by_cases h : RZ Γ (P l)
      · rw [if_pos ((hPs l Γ).mp h).symm, if_pos h]
      · rw [if_neg (fun e => h ((hPs l Γ).mpr e.symm)), if_neg h]
    rw [hΔs, ← hΔ, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs
    · rw [mul_add]
      simp [Mori.DivisorWithCoeffs.coeff]
    · simp
  refine isCrepantBoundary_of_localEquations hZs hns hWs hμs hnWs hωs hm hDsQ hDsc
    (fun F => ?_) Fs
  obtain ⟨U, ψ, UK, φ, hxU, hψ, hφ, hloc, hlocK, hW'⟩ := hgood D hDc hDT (μs F.genericPoint)
  obtain ⟨hordF, hmem⟩ := hW' F hxU
  refine ⟨U, ψ, hψ, hxU, fun Γ hΓ => by rw [hDs, hloc Γ hΓ], ?_⟩
  have hΔWs : (∑ l, Finsupp.single (Ps' l) (q' l) : Mori.QDivisor Ws).coeff F =
      ∑ E ∈ TW, if RW F E then (∑ l, Finsupp.single (P' l) (q' l) : Mori.QDivisor W).coeff E
        else 0 := by
    have hΔ := sum_ite_coeff_sum_single TW (fun E => RW F E) P' hP'T q'
    change (∑ l, Finsupp.single (Ps' l) (q' l) : Mori.PrimeDivisor Ws →₀ ℚ) F = _
    rw [Finsupp.finset_sum_apply]
    refine (Finset.sum_congr rfl fun l _ => ?_).trans hΔ.symm
    rw [Finsupp.single_apply]
    by_cases h : RW F (P' l)
    · rw [if_pos ((hPs' l F).mp h).symm, if_pos h]
    · rw [if_neg (fun e => h ((hPs' l F).mpr e.symm)), if_neg h]
  rw [hordF, hWf F, hΔWs]
  push_cast
  have hE : ∀ E ∈ TW, (if RW F E then (W.ord (AlgebraicGeometry.functionFieldMap μ φ)
      E.genericPoint : ℚ) else 0) = (m : ℚ) * ((if RW F E then
        (E.ordForm (Mori.pullbackRationalPluriForms sZ μ (ω.toPluriForms sZ)) : ℚ) else 0) +
      if RW F E then (∑ l, Finsupp.single (P' l) (q' l) : Mori.QDivisor W).coeff E else 0) := by
    intro E hET
    split_ifs with hRE
    · rw [ord_eq_of_isDiscrepancy hZ hn hW hμ hnW hK₀ hω hm hD hDc hφ hlocK E (hmem E hET hRE)
        (hCr E)]
      ring
    · simp
  rw [Finset.sum_congr rfl hE, ← Finset.mul_sum, Finset.sum_add_distrib]

include hint in
/-- **Local fractions at a stage.** A rational function on a vertex is, near any point and inside
any neighbourhood of it, a fraction `p / q` of sections of an affine open of a late stage. -/
private lemma Model.exists_local_frac {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (x : (X.obj j).left) (U : (X.obj j).left.Opens) (hx : x ∈ U)
    (f : (X.obj j).left.functionField) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (V : ((M.stage (h₀.trans h₁)).obj j).left.Opens) (_ : IsAffineOpen V)
      (p q : Γ(((M.stage (h₀.trans h₁)).obj j).left, V))
      (_ : Nonempty (M.cmp (h₀.trans h₁) j ⁻¹ᵁ V)),
      x ∈ M.cmp (h₀.trans h₁) j ⁻¹ᵁ V ∧ M.cmp (h₀.trans h₁) j ⁻¹ᵁ V ≤ U ∧
      (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ q) ≠ 0 ∧
      (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ p) =
        f * (X.obj j).left.germToFunctionField _ ((M.cmp (h₀.trans h₁) j).app _ q) := by
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset hx
  obtain ⟨Sa, ha, Ha⟩ := M.exists_open j A hA.isCompact
  let S₂ : CoefficientModels.FGSub k₀ K := ⟨S₀.1 ⊔ Sa.1, S₀.2.sup Sa.2⟩
  have h₀₂ : S₀ ≤ S₂ := le_sup_left (a := S₀.1)
  have ha₂ : Sa ≤ S₂ := le_sup_right (b := Sa.1)
  obtain ⟨V', -, hV'⟩ := Ha S₂ ha₂
  have hxV' : M.cmp (h₀.trans h₀₂) j x ∈ V' := by
    have : x ∈ M.cmp (ha.trans ha₂) j ⁻¹ᵁ V' := hV' ▸ hxA
    exact this
  obtain ⟨V'', hV''a, hxV'', hV''V'⟩ := exists_isAffineOpen_mem_and_subset hxV'
  haveI : Nonempty (M.cmp (h₀.trans h₀₂) j ⁻¹ᵁ V'') := ⟨⟨x, hxV''⟩⟩
  obtain ⟨S₁, h₁, p, q, hne, hq, hpq⟩ := M.exists_frac hint (h₀.trans h₀₂) j V'' hV''a f
  have hst := M.isAffineHom_stageCmp (h₀.trans h₀₂) h₁ j
  have e : M.cmp ((h₀.trans h₀₂).trans h₁) j ⁻¹ᵁ (M.stageCmp (h₀.trans h₀₂) h₁ j ⁻¹ᵁ V'') =
      M.cmp (h₀.trans h₀₂) j ⁻¹ᵁ V'' := by
    rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]
  refine ⟨S₁, h₀₂.trans h₁, _, hV''a.preimage _, p, q, hne, ?_, ?_, hq, hpq⟩
  · change x ∈ M.cmp ((h₀.trans h₀₂).trans h₁) j ⁻¹ᵁ (M.stageCmp (h₀.trans h₀₂) h₁ j ⁻¹ᵁ V'')
    rw [e]
    exact hxV''
  · change M.cmp ((h₀.trans h₀₂).trans h₁) j ⁻¹ᵁ (M.stageCmp (h₀.trans h₀₂) h₁ j ⁻¹ᵁ V'') ≤ U
    rw [e]
    intro y hy
    have : y ∈ M.cmp (ha.trans ha₂) j ⁻¹ᵁ V' := hV''V' hy
    rw [hV'] at this
    exact hAU this

private lemma ord_one_eq_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X) :
    X.ord 1 x = 0 := by
  simpa using MMP.Mori.ord_zpow x (one_ne_zero (α := X.functionField)) 0

open Classical in
/-- **Spread local equations.** A divisor `D` of `Z` has *spread local equations* for a fibre
`Zₛ` (with `μₛ : Wₛ ⟶ Zₛ` over `μ : W ⟶ Z`) if every point of `Zₛ` has a neighbourhood on which
the divisor `∑_{E ∈ T_Z} coeff_E(D) · [E]ₛ` has a local equation `ψ`, and `D` has a local
equation `φ` on an open of `Z`, so that along every prime divisor of `Wₛ` over the neighbourhood
the order of `μₛ^*ψ` is the sum of the orders of `μ^*φ` along the prime divisors of `T_W` of
which it is the fibre, all of them lying over the open of `Z`. -/
@[expose] public def HasSpreadLocalEquations {Z W Zs Ws : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z]
    [IsIntegral W] [IsLocallyNoetherian W] [IsIntegral Zs] [IsLocallyNoetherian Zs]
    [IsIntegral Ws] [IsLocallyNoetherian Ws] (μ : W ⟶ Z) [IsDominant μ] (μs : Ws ⟶ Zs)
    [IsDominant μs] (TZ : Finset (Mori.PrimeDivisor Z))
    (RZ : Mori.PrimeDivisor Zs → Mori.PrimeDivisor Z → Prop) (TW : Finset (Mori.PrimeDivisor W))
    (RW : Mori.PrimeDivisor Ws → Mori.PrimeDivisor W → Prop) (D : Mori.Divisor Z) : Prop :=
  ∀ x : Zs, ∃ (U : Zs.Opens) (ψ : Zs.functionField) (UK : Z.Opens) (φ : Z.functionField),
    x ∈ U ∧ ψ ≠ 0 ∧ φ ≠ 0 ∧
    (∀ Γ : Mori.PrimeDivisor Zs, (Γ.support ∩ U).Nonempty →
      (∑ E ∈ TZ, if RZ Γ E then D.coeff E else 0) = Zs.ord ψ Γ.genericPoint) ∧
    (∀ E : Mori.PrimeDivisor Z, (E.support ∩ UK).Nonempty →
      D.coeff E = Z.ord φ E.genericPoint) ∧
    ∀ F : Mori.PrimeDivisor Ws, μs F.genericPoint ∈ U →
      Ws.ord (AlgebraicGeometry.functionFieldMap μs ψ) F.genericPoint =
        (∑ E ∈ TW, if RW F E then
          W.ord (AlgebraicGeometry.functionFieldMap μ φ) E.genericPoint else 0) ∧
      ∀ E ∈ TW, RW F E → μ E.genericPoint ∈ UK

section HasSpreadLocalEquations

variable {Z W Zs Ws : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsIntegral W] [IsLocallyNoetherian W] [IsIntegral Zs] [IsLocallyNoetherian Zs]
    [IsIntegral Ws] [IsLocallyNoetherian Ws] {μ : W ⟶ Z} [IsDominant μ] {μs : Ws ⟶ Zs}
    [IsDominant μs] {TZ : Finset (Mori.PrimeDivisor Z)}
    {RZ : Mori.PrimeDivisor Zs → Mori.PrimeDivisor Z → Prop} {TW : Finset (Mori.PrimeDivisor W)}
    {RW : Mori.PrimeDivisor Ws → Mori.PrimeDivisor W → Prop}

open Classical in
private lemma hasSpreadLocalEquations_zero : HasSpreadLocalEquations μ μs TZ RZ TW RW 0 := by
  intro x
  refine ⟨⊤, 1, ⊤, 1, trivial, one_ne_zero, one_ne_zero, fun Γ _ => ?_, fun E _ => ?_,
    fun F _ => ⟨?_, fun E _ _ => trivial⟩⟩
  · simp [ord_one_eq_zero, Mori.DivisorWithCoeffs.coeff_zero]
  · simp [ord_one_eq_zero, Mori.DivisorWithCoeffs.coeff_zero]
  · simp [ord_one_eq_zero]

open Classical in
private lemma HasSpreadLocalEquations.add {D D' : Mori.Divisor Z}
    (h : HasSpreadLocalEquations μ μs TZ RZ TW RW D)
    (h' : HasSpreadLocalEquations μ μs TZ RZ TW RW D') :
    HasSpreadLocalEquations μ μs TZ RZ TW RW (D + D') := by
  intro x
  obtain ⟨U, ψ, UK, φ, hx, hψ, hφ, hl, hlK, hW⟩ := h x
  obtain ⟨U', ψ', UK', φ', hx', hψ', hφ', hl', hlK', hW'⟩ := h' x
  refine ⟨U ⊓ U', ψ * ψ', UK ⊓ UK', φ * φ', ⟨hx, hx'⟩, mul_ne_zero hψ hψ',
    mul_ne_zero hφ hφ', fun Γ hΓ => ?_, fun E hE => ?_, fun F hF => ?_⟩
  · obtain ⟨y, hy, hyU, hyU'⟩ := hΓ
    rw [Scheme.ord_mul hψ hψ', ← hl Γ ⟨y, hy, hyU⟩, ← hl' Γ ⟨y, hy, hyU'⟩,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs <;> simp [Mori.DivisorWithCoeffs.coeff_add]
  · obtain ⟨y, hy, hyU, hyU'⟩ := hE
    rw [Mori.DivisorWithCoeffs.coeff_add, Scheme.ord_mul hφ hφ', hlK E ⟨y, hy, hyU⟩,
      hlK' E ⟨y, hy, hyU'⟩]
  · obtain ⟨h1, h2⟩ := hW F hF.1
    obtain ⟨h1', h2'⟩ := hW' F hF.2
    refine ⟨?_, fun E hE hR => ⟨h2 E hE hR, h2' E hE hR⟩⟩
    rw [map_mul, Scheme.ord_mul ((map_ne_zero _).mpr hψ) ((map_ne_zero _).mpr hψ'), h1, h1',
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs
    · rw [map_mul, Scheme.ord_mul ((map_ne_zero _).mpr hφ) ((map_ne_zero _).mpr hφ')]
    · simp

open Classical in
private lemma HasSpreadLocalEquations.zsmul {D : Mori.Divisor Z}
    (h : HasSpreadLocalEquations μ μs TZ RZ TW RW D) (z : ℤ) :
    HasSpreadLocalEquations μ μs TZ RZ TW RW (z • D) := by
  intro x
  obtain ⟨U, ψ, UK, φ, hx, hψ, hφ, hl, hlK, hW⟩ := h x
  refine ⟨U, ψ ^ z, UK, φ ^ z, hx, zpow_ne_zero _ hψ, zpow_ne_zero _ hφ, fun Γ hΓ => ?_,
    fun E hE => ?_, fun F hF => ?_⟩
  · rw [MMP.Mori.ord_zpow _ hψ, ← hl Γ hΓ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs <;> simp [Mori.DivisorWithCoeffs.coeff_smul]
  · rw [Mori.DivisorWithCoeffs.coeff_smul, MMP.Mori.ord_zpow _ hφ, hlK E hE, smul_eq_mul]
  · obtain ⟨h1, h2⟩ := hW F hF
    refine ⟨?_, h2⟩
    rw [map_zpow₀, MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr hψ), h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    split_ifs
    · rw [map_zpow₀, MMP.Mori.ord_zpow _ ((map_ne_zero _).mpr hφ)]
    · simp

/-- Divisors with spread local equations form a subgroup: every integral combination of divisors
with spread local equations has them. -/
public lemma HasSpreadLocalEquations.of_mem_span {G : Set (Mori.Divisor Z)}
    (hG : ∀ g ∈ G, HasSpreadLocalEquations μ μs TZ RZ TW RW g) {D : Mori.Divisor Z}
    (hD : D ∈ Submodule.span ℤ G) : HasSpreadLocalEquations μ μs TZ RZ TW RW D := by
  induction hD using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => exact hasSpreadLocalEquations_zero
  | add a b _ _ ha hb => exact ha.add hb
  | smul z a _ ha => exact ha.zsmul z

end HasSpreadLocalEquations

/-- **Cartier divisors supported on finitely many prime divisors are finitely generated.** -/
public lemma exists_finset_span_cartier {Z : Scheme.{u}} [IsLocallyNoetherian Z] [IsNormal Z]
    (T₁ : Finset (Mori.PrimeDivisor Z)) :
    ∃ G : Finset (Mori.Divisor Z), (∀ g ∈ G, g.IsCartier ∧ ∀ E, g.coeff E ≠ 0 → E ∈ T₁) ∧
      ∀ D : Mori.Divisor Z, D.IsCartier → (∀ E, D.coeff E ≠ 0 → E ∈ T₁) →
        D ∈ Submodule.span ℤ (G : Set (Mori.Divisor Z)) := by
  let N : Submodule ℤ (Mori.Divisor Z) :=
    { carrier := {D | D.IsCartier ∧ ∀ E, D.coeff E ≠ 0 → E ∈ T₁}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun E hE => by
        rw [Mori.DivisorWithCoeffs.coeff_add] at hE
        by_contra h
        exact hE (by rw [not_imp_comm.mp (ha.2 E) h, not_imp_comm.mp (hb.2 E) h, add_zero])⟩
      zero_mem' := ⟨Mori.Divisor.isCartier_zero, fun E hE => absurd rfl hE⟩
      smul_mem' := fun z a ha => ⟨ha.1.zsmul z, fun E hE => by
        rw [Mori.DivisorWithCoeffs.coeff_smul] at hE
        by_contra h
        exact hE (by rw [not_imp_comm.mp (ha.2 E) h, smul_zero])⟩ }
  let Sp := Finsupp.supported ℤ ℤ (T₁ : Set (Mori.PrimeDivisor Z))
  have hNS : N ≤ Sp := fun D hD => by
    rw [Finsupp.mem_supported]
    intro E hE
    exact hD.2 E (Finsupp.mem_support_iff.mp hE)
  haveI : IsNoetherian ℤ Sp :=
    isNoetherian_of_linearEquiv (Finsupp.supportedEquivFinsupp (M := ℤ) (R := ℤ)
      (T₁ : Set (Mori.PrimeDivisor Z))).symm
  have hfg : (N.comap Sp.subtype).FG := IsNoetherian.noetherian _
  have hfg' : N.FG := by
    have := hfg.map Sp.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hNS] at this
  obtain ⟨G, hG⟩ := hfg'
  refine ⟨G, fun g hg => ?_, fun D hD hDT => ?_⟩
  · have : g ∈ N := hG ▸ Submodule.subset_span hg
    exact this
  · rw [hG]
    exact ⟨hD, hDT⟩

private lemma ord_mul_inv {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {a b : X.functionField}
    (ha : a ≠ 0) (hb : b ≠ 0) (x : X) : X.ord (a * b⁻¹) x = X.ord a x - X.ord b x := by
  rw [Scheme.ord_mul ha (inv_ne_zero hb), ← zpow_neg_one, MMP.Mori.ord_zpow _ hb]
  ring

open Classical in
include hint in
/-- **Spread local equations on one chart.** Let `g = p / q` be a fraction of sections of an
affine open `V` of a stage of the target of `μ : j ⟶ j₀`, a local equation over `K` of a divisor
`D` on the preimage of `V`. There are finite sets of prime divisors such that, for all larger
finite sets with models, on every late fibre the fraction `p / q` and its pull-back along `μ`
give spread local equations of `D` over the preimage of `V`. -/
private lemma Model.exists_spread_chart {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    {j₀ j : J}
    (μ : j ⟶ j₀) [IsLocallyNoetherian (X.obj j₀).left] [IsNormal (X.obj j₀).left]
    [CompactSpace (X.obj j₀).left] [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    [CompactSpace (X.obj j).left] [IsDominant (X.map μ).left] (D : Mori.Divisor (X.obj j₀).left)
    (V : ((M.stage h₀).obj j₀).left.Opens) (p q : Γ(((M.stage h₀).obj j₀).left, V))
    [Nonempty (M.cmp h₀ j₀ ⁻¹ᵁ V)] {g : (X.obj j₀).left.functionField} (hg : g ≠ 0)
    (hq : (X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V q) ≠ 0)
    (hpq : (X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V p) =
      g * (X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V q))
    (hloc : ∀ E : Mori.PrimeDivisor (X.obj j₀).left, (E.support ∩ M.cmp h₀ j₀ ⁻¹ᵁ V).Nonempty →
      D.coeff E = (X.obj j₀).left.ord g E.genericPoint) :
    ∃ (T₀Z : Finset (Mori.PrimeDivisor (X.obj j₀).left))
      (T₀W : Finset (Mori.PrimeDivisor (X.obj j).left)),
      ∀ TZ, T₀Z ⊆ TZ → ∀ TW, T₀W ⊆ TW → ∀ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
        (𝓘Z : Mori.PrimeDivisor (X.obj j₀).left →
          ((M.stage (h₀.trans h₁)).obj j₀).left.IdealSheafData)
        (𝓘W : Mori.PrimeDivisor (X.obj j).left →
          ((M.stage (h₀.trans h₁)).obj j).left.IdealSheafData),
        (∀ E ∈ TZ, (𝓘Z E).comap (M.cmp (h₀.trans h₁) j₀) = E.idealSheaf) →
        (∀ E ∈ TW, (𝓘W E).comap (M.cmp (h₀.trans h₁) j) = E.idealSheaf) →
      EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
        [IsIntegral ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left]
        [IsLocallyNoetherian ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left]
        [IsIntegral ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
        [IsLocallyNoetherian ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
        [IsDominant ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).map μ).left],
        topologicalKrullDim ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left =
          topologicalKrullDim (X.obj j₀).left →
        topologicalKrullDim ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        (∀ E ∈ TZ, ∃ Ps : Mori.PrimeDivisor
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left,
          Ps.idealSheaf = (𝓘Z E).comap (M.fibreMap (h₀.trans h₁) hS t j₀)) →
        (∀ E ∈ TW, ∃ Ps : Mori.PrimeDivisor
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘W E).comap (M.fibreMap (h₀.trans h₁) hS t j)) →
        ∀ x, M.fibreMap h₀ (h₁.trans hS) t j₀ x ∈ V →
        ∃ (U : ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left.Opens)
          (ψ : ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left.functionField)
          (UK : (X.obj j₀).left.Opens) (φ : (X.obj j₀).left.functionField),
          x ∈ U ∧ ψ ≠ 0 ∧ φ ≠ 0 ∧
          (∀ Γ : Mori.PrimeDivisor
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left,
            (Γ.support ∩ U).Nonempty →
            (∑ E ∈ TZ, if Γ.idealSheaf = (𝓘Z E).comap (M.fibreMap (h₀.trans h₁) hS t j₀) then
              D.coeff E else 0) =
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left.ord ψ
                Γ.genericPoint) ∧
          (∀ E : Mori.PrimeDivisor (X.obj j₀).left, (E.support ∩ UK).Nonempty →
            D.coeff E = (X.obj j₀).left.ord φ E.genericPoint) ∧
          ∀ F : Mori.PrimeDivisor
              ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).map μ).left F.genericPoint ∈ U →
            ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left.ord
              (AlgebraicGeometry.functionFieldMap
                ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).map μ).left ψ)
              F.genericPoint =
              (∑ E ∈ TW, if F.idealSheaf = (𝓘W E).comap (M.fibreMap (h₀.trans h₁) hS t j) then
                (X.obj j).left.ord (AlgebraicGeometry.functionFieldMap (X.map μ).left φ)
                  E.genericPoint else 0) ∧
            ∀ E ∈ TW, F.idealSheaf = (𝓘W E).comap (M.fibreMap (h₀.trans h₁) hS t j) →
              (X.map μ).left E.genericPoint ∈ UK := by
  have := hint j₀
  have := hint j
  set μst := ((M.stage h₀).map μ).left with hμst
  have hsqK : M.cmp h₀ j ≫ μst = (X.map μ).left ≫ M.cmp h₀ j₀ :=
    ((M.isCartesian_cmp h₀).w μ).symm
  have ePK : M.cmp h₀ j ⁻¹ᵁ (μst ⁻¹ᵁ V) = (X.map μ).left ⁻¹ᵁ (M.cmp h₀ j₀ ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsqK]
  haveI : Nonempty (M.cmp h₀ j ⁻¹ᵁ (μst ⁻¹ᵁ V)) := by
    rw [ePK]
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty (M.cmp h₀ j₀ ⁻¹ᵁ V)›
    have hd : Dense (Set.range (X.map μ).left) := (X.map μ).left.denseRange
    obtain ⟨_, hz, ⟨w, rfl⟩⟩ := hd.inter_open_nonempty _ (M.cmp h₀ j₀ ⁻¹ᵁ V).isOpen ⟨y, hy⟩
    exact ⟨⟨w, hz⟩⟩
  have hp : (X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V p) ≠ 0 := by
    rw [hpq]
    exact mul_ne_zero hg hq
  have gK : ∀ s : Γ(((M.stage h₀).obj j₀).left, V),
      (X.obj j).left.germToFunctionField _ ((M.cmp h₀ j).app _ (μst.app V s)) =
        AlgebraicGeometry.functionFieldMap (X.map μ).left
          ((X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V s)) := fun s =>
    germ_app_eq_functionFieldMap _ _ _ _ hsqK V s
  have hpW : (X.obj j).left.germToFunctionField _ ((M.cmp h₀ j).app _ (μst.app V p)) ≠ 0 := by
    rw [gK]
    exact (map_ne_zero _).mpr hp
  have hqW : (X.obj j).left.germToFunctionField _ ((M.cmp h₀ j).app _ (μst.app V q)) ≠ 0 := by
    rw [gK]
    exact (map_ne_zero _).mpr hq
  refine ⟨(finite_ord_ne_zero_of_ne_zero hp).toFinset ∪ (finite_ord_ne_zero_of_ne_zero hq).toFinset,
    (finite_ord_ne_zero_of_ne_zero hpW).toFinset ∪ (finite_ord_ne_zero_of_ne_zero hqW).toFinset,
    fun TZ hTZ TW hTW S₁ h₁ 𝓘Z 𝓘W h𝓘Z h𝓘W => ?_⟩
  have a1 := M.exists_ord_section_of_le hint h₀ h₁ j₀ V p hp TZ 𝓘Z h𝓘Z fun E _ hE =>
    hTZ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hE))
  have a2 := M.exists_ord_section_of_le hint h₀ h₁ j₀ V q hq TZ 𝓘Z h𝓘Z fun E _ hE =>
    hTZ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hE))
  have b1 := M.exists_ord_section_of_le hint h₀ h₁ j (μst ⁻¹ᵁ V) (μst.app V p) hpW TW 𝓘W h𝓘W
    fun E _ hE => hTW (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr hE))
  have b2 := M.exists_ord_section_of_le hint h₀ h₁ j (μst ⁻¹ᵁ V) (μst.app V q) hqW TW 𝓘W h𝓘W
    fun E _ hE => hTW (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr hE))
  have a3 : EvAbove S₁ fun S hS => ∀ E ∈ TZ, ¬ (E.support ∩ M.cmp h₀ j₀ ⁻¹ᵁ V).Nonempty →
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      (Γ : Mori.PrimeDivisor
        ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left),
      Γ.idealSheaf = (𝓘Z E).comap (M.fibreMap (h₀.trans h₁) hS t j₀) →
      ¬ (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j₀ ⁻¹ᵁ V).Nonempty := by
    refine EvAbove.forall_finset TZ fun E hE => ?_
    by_cases hEV : (E.support ∩ M.cmp h₀ j₀ ⁻¹ᵁ V).Nonempty
    · exact (EvAbove.true S₁).mono fun S hS _ h' => absurd hEV h'
    · exact (M.evAbove_disjoint_of_le h₀ h₁ j₀ (h𝓘Z E hE) V hEV).mono fun S hS H _ => H
  have b3 : EvAbove S₁ fun S hS => ∀ E ∈ TW,
      ¬ (E.support ∩ M.cmp h₀ j ⁻¹ᵁ (μst ⁻¹ᵁ V)).Nonempty →
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
      (Γ : Mori.PrimeDivisor
        ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left),
      Γ.idealSheaf = (𝓘W E).comap (M.fibreMap (h₀.trans h₁) hS t j) →
      ¬ (Γ.support ∩ M.fibreMap h₀ (h₁.trans hS) t j ⁻¹ᵁ (μst ⁻¹ᵁ V)).Nonempty := by
    refine EvAbove.forall_finset TW fun E hE => ?_
    by_cases hEV : (E.support ∩ M.cmp h₀ j ⁻¹ᵁ (μst ⁻¹ᵁ V)).Nonempty
    · exact (EvAbove.true S₁).mono fun S hS _ h' => absurd hEV h'
    · exact (M.evAbove_disjoint_of_le h₀ h₁ j (h𝓘W E hE) _ hEV).mono fun S hS H _ => H
  refine (((a1.and a2).and a3).and ((b1.and b2).and b3)).mono
    fun S hS H L _ t _ _ _ _ _ hdZ hdW hmZ hmW x hx => ?_
  obtain ⟨⟨⟨A1, A2⟩, A3⟩, ⟨B1, B2⟩, B3⟩ := H
  let fmZ := M.fibreMap h₀ (h₁.trans hS) t j₀
  let fmW := M.fibreMap h₀ (h₁.trans hS) t j
  let μs := ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).map μ).left
  have hsqF : fmW ≫ μst = μs ≫ fmZ := (M.fibreMap_naturality h₀ (h₁.trans hS) t μ).symm
  haveI : Nonempty (fmZ ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  obtain ⟨hp0, Hp⟩ := A1 L t hdZ hmZ
  obtain ⟨hq0, Hq⟩ := A2 L t hdZ hmZ
  let Zs := ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left
  let ps := Zs.germToFunctionField (fmZ ⁻¹ᵁ V) (fmZ.app V p)
  let qs := Zs.germToFunctionField (fmZ ⁻¹ᵁ V) (fmZ.app V q)
  have hgK : g = (X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V p) *
      ((X.obj j₀).left.germToFunctionField _ ((M.cmp h₀ j₀).app V q))⁻¹ := by
    rw [hpq, mul_assoc, mul_inv_cancel₀ hq, mul_one]
  refine ⟨fmZ ⁻¹ᵁ V, ps * qs⁻¹, M.cmp h₀ j₀ ⁻¹ᵁ V, g, hx, mul_ne_zero hp0 (inv_ne_zero hq0), hg,
    fun Γ hΓ => ?_, hloc, fun F hF => ?_⟩
  · rw [ord_mul_inv hp0 hq0, Hp Γ hΓ, Hq Γ hΓ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun E hE => ?_
    split_ifs with hΓE
    · have hEm : (E.support ∩ M.cmp h₀ j₀ ⁻¹ᵁ V).Nonempty := by
        by_contra hn
        exact A3 E hE hn L t Γ hΓE hΓ
      rw [hloc E hEm, hgK, ord_mul_inv hp hq]
    · simp
  · have hFV : F.genericPoint ∈ fmW ⁻¹ᵁ (μst ⁻¹ᵁ V) := by
      change (fmW ≫ μst) F.genericPoint ∈ V
      rw [hsqF]
      exact hF
    haveI : Nonempty (fmW ⁻¹ᵁ (μst ⁻¹ᵁ V)) := ⟨⟨_, hFV⟩⟩
    have hmeet : (F.support ∩ fmW ⁻¹ᵁ (μst ⁻¹ᵁ V)).Nonempty :=
      ⟨_, genericPoint_mem_support F, hFV⟩
    obtain ⟨hpW0, HpW⟩ := B1 L t hdW hmW
    obtain ⟨hqW0, HqW⟩ := B2 L t hdW hmW
    have gF : ∀ s : Γ(((M.stage h₀).obj j₀).left, V),
        ((M.stage ((h₀.trans h₁).trans hS) ⋙ Over.pullback t).obj j).left.germToFunctionField _
          (fmW.app _ (μst.app V s)) =
        AlgebraicGeometry.functionFieldMap μs (Zs.germToFunctionField _ (fmZ.app V s)) :=
      fun s => germ_app_eq_functionFieldMap _ _ _ _ hsqF V s
    refine ⟨?_, fun E hE hFE => ?_⟩
    · rw [map_mul, map_inv₀, ← gF, ← gF, ord_mul_inv hpW0 hqW0, HpW F hmeet, HqW F hmeet,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun E _ => ?_
      split_ifs
      · rw [gK, gK, hgK, map_mul, map_inv₀, ord_mul_inv ((map_ne_zero _).mpr hp)
          ((map_ne_zero _).mpr hq)]
      · simp
    · have hEm : (E.support ∩ M.cmp h₀ j ⁻¹ᵁ (μst ⁻¹ᵁ V)).Nonempty := by
        by_contra hn
        exact B3 E hE hn L t F hFE hmeet
      have hη := genericPoint_mem_of_nonempty E _ hEm
      change (M.cmp h₀ j ≫ μst) E.genericPoint ∈ V at hη
      rw [hsqK] at hη
      exact hη

open Classical in
include hint in
/-- **Cartier divisors have spread local equations on late fibres.** For a Cartier divisor `D`
on the target of `μ : j ⟶ j₀` there are finite sets of prime divisors such that, for all larger
finite sets with models, on every late fibre `D` has spread local equations. -/
public lemma Model.exists_spread_cartier {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    {j₀ j : J}
    (μ : j ⟶ j₀) [IsLocallyNoetherian (X.obj j₀).left] [IsNormal (X.obj j₀).left]
    [CompactSpace (X.obj j₀).left] [IsLocallyNoetherian (X.obj j).left] [IsNormal (X.obj j).left]
    [CompactSpace (X.obj j).left] [IsDominant (X.map μ).left] (D : Mori.Divisor (X.obj j₀).left)
    (hD : D.IsCartier) :
    ∃ (Sa : CoefficientModels.FGSub k₀ K) (ha : S₀ ≤ Sa)
      (T₀Z : Finset (Mori.PrimeDivisor (X.obj j₀).left))
      (T₀W : Finset (Mori.PrimeDivisor (X.obj j).left)),
      ∀ TZ, T₀Z ⊆ TZ → ∀ TW, T₀W ⊆ TW → ∀ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : Sa ≤ S₁)
        (𝓘Z : Mori.PrimeDivisor (X.obj j₀).left →
          ((M.stage ((h₀.trans ha).trans h₁)).obj j₀).left.IdealSheafData)
        (𝓘W : Mori.PrimeDivisor (X.obj j).left →
          ((M.stage ((h₀.trans ha).trans h₁)).obj j).left.IdealSheafData),
        (∀ E ∈ TZ, (𝓘Z E).comap (M.cmp ((h₀.trans ha).trans h₁) j₀) = E.idealSheaf) →
        (∀ E ∈ TW, (𝓘W E).comap (M.cmp ((h₀.trans ha).trans h₁) j) = E.idealSheaf) →
      EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
        [IsIntegral ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left]
        [IsLocallyNoetherian
          ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left]
        [IsIntegral ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
        [IsLocallyNoetherian
          ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j).left]
        [IsDominant ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).map μ).left],
        topologicalKrullDim
            ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left =
          topologicalKrullDim (X.obj j₀).left →
        topologicalKrullDim
            ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j).left =
          topologicalKrullDim (X.obj j).left →
        (∀ E ∈ TZ, ∃ Ps : Mori.PrimeDivisor
            ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j₀).left,
          Ps.idealSheaf = (𝓘Z E).comap (M.fibreMap ((h₀.trans ha).trans h₁) hS t j₀)) →
        (∀ E ∈ TW, ∃ Ps : Mori.PrimeDivisor
            ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).obj j).left,
          Ps.idealSheaf = (𝓘W E).comap (M.fibreMap ((h₀.trans ha).trans h₁) hS t j)) →
        HasSpreadLocalEquations (X.map μ).left
          ((M.stage (((h₀.trans ha).trans h₁).trans hS) ⋙ Over.pullback t).map μ).left TZ
          (fun Γ E => Γ.idealSheaf = (𝓘Z E).comap (M.fibreMap ((h₀.trans ha).trans h₁) hS t j₀))
          TW (fun F E => F.idealSheaf = (𝓘W E).comap (M.fibreMap ((h₀.trans ha).trans h₁) hS t j))
          D := by
  have := hint j₀
  have := hint j
  -- local equations over `K`
  choose U hxU φu hφu using hD
  choose g hg hgo using fun x => MMP.Positivity.exists_ord_eq_of_units (φu x)
  choose Sx hx V hVa p q hne hxV hVU hq hpq using fun x =>
    M.exists_local_frac hint h₀ j₀ x (U x) (hxU x) (g x)
  have hloc : ∀ x (E : Mori.PrimeDivisor (X.obj j₀).left),
      (E.support ∩ M.cmp (h₀.trans (hx x)) j₀ ⁻¹ᵁ V x).Nonempty →
      D.coeff E = (X.obj j₀).left.ord (g x) E.genericPoint := by
    intro x E ⟨y, hyE, hyV⟩
    rw [hφu x E ⟨y, hyE, hVU x hyV⟩, hgo]
  choose T₀Z T₀W H using fun x =>
    haveI := hne x
    M.exists_spread_chart hint (h₀.trans (hx x)) μ D (V x) (p x) (q x) (hg x) (hq x) (hpq x)
      (hloc x)
  -- a finite cover
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (M.cmp (h₀.trans (hx x)) j₀ ⁻¹ᵁ V x : Set (X.obj j₀).left))
    (fun x => (M.cmp (h₀.trans (hx x)) j₀ ⁻¹ᵁ V x).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩)
  obtain ⟨Sa, hSa⟩ := Finset.exists_le (insert S₀ (s.image Sx))
  have ha : S₀ ≤ Sa := hSa _ (Finset.mem_insert_self _ _)
  have hxa : ∀ x ∈ s, Sx x ≤ Sa := fun x hxs =>
    hSa _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxs))
  let Ustar : ((M.stage (h₀.trans ha)).obj j₀).left.Opens :=
    ⨆ x : s, M.stageCmp (h₀.trans (hx x.1)) (hxa x.1 x.2) j₀ ⁻¹ᵁ V x.1
  have hC : M.cmp (h₀.trans ha) j₀ ⁻¹' (Ustar.compl : Set _) = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hy
    apply hy
    obtain ⟨x, hxs, hyx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hxs⟩, ?_⟩
    change (M.cmp ((h₀.trans (hx x)).trans (hxa x hxs)) j₀ ≫
      M.stageCmp (h₀.trans (hx x)) (hxa x hxs) j₀) y ∈ V x
    rw [M.cmp_stageCmp]
    exact hyx
  obtain ⟨S₂, h₂, HC⟩ := M.exists_preimage_eq_empty (h₀.trans ha) j₀ _ hC
  refine ⟨Sa, ha, s.biUnion T₀Z, s.biUnion T₀W, fun TZ hTZ TW hTW S₁ h₁ 𝓘Z 𝓘W h𝓘Z h𝓘W => ?_⟩
  have eH := EvAbove.forall_of_finite (α := s) fun x =>
    (H x.1 TZ (fun E hE => hTZ (Finset.mem_biUnion.mpr ⟨x.1, x.2, hE⟩)) TW
      (fun E hE => hTW (Finset.mem_biUnion.mpr ⟨x.1, x.2, hE⟩)) S₁ ((hxa x.1 x.2).trans h₁)
      𝓘Z 𝓘W h𝓘Z h𝓘W)
  have eC : EvAbove S₁ fun S hS => ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap (h₀.trans ha) (h₁.trans hS) t j₀ ⁻¹' (Ustar.compl : Set _) = ∅ := by
    refine ⟨⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩, le_sup_left (a := S₁.1), fun S hS L _ t => ?_⟩
    exact HC S ((le_sup_right (b := S₂.1)).trans hS) L t
  refine (eH.and eC).mono fun S hS HH L _ t _ _ _ _ _ hdZ hdW hmZ hmW y => ?_
  obtain ⟨HH, HC'⟩ := HH
  have hy : M.fibreMap (h₀.trans ha) (h₁.trans hS) t j₀ y ∈ Ustar := by
    by_contra hn
    have : y ∈ M.fibreMap (h₀.trans ha) (h₁.trans hS) t j₀ ⁻¹' (Ustar.compl : Set _) := hn
    rw [HC' L t] at this
    exact this
  obtain ⟨⟨x, hxs⟩, hyx⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  have hyx' : M.fibreMap (h₀.trans (hx x)) ((hxa x hxs).trans (h₁.trans hS)) t j₀ y ∈ V x := by
    rw [← M.fibreMap_comp (h₀.trans (hx x)) (hxa x hxs) (h₁.trans hS) t j₀]
    exact hyx
  exact HH ⟨x, hxs⟩ L t hdZ hdW hmZ hmW y hyx'

/-- **The smooth locus of a normal variety contains all points of codimension at most one.** -/
public lemma exists_smooth_open_of_isNormalVariety {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] (hX : Mori.IsNormalVariety k sX) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ Smooth (U.ι ≫ sX) ∧
      ∀ x : X, Order.coheight x ≤ 1 → x ∈ U := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNormal X := hX.2
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hTeq : MMP.Mori.smoothLocus sX = sX.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sX
  refine ⟨MMP.Mori.smoothLocus sX, TopologicalSpace.NoetherianSpace.isCompact _, ?_, fun x hx => ?_⟩
  · rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq,
      Scheme.Opens.ι_preimage_self]
  · rcases (le_iff_lt_or_eq.mp hx) with hlt | h1
    · have h0 : Order.coheight x = 0 := by
        have := Order.lt_one_iff.mp hlt
        exact this
      have hmax := Order.coheight_eq_zero.mp h0
      have hx : x = genericPoint X := by
        have h1 : x ⤳ genericPoint X := hmax (genericPoint_specializes x)
        exact h1.antisymm (genericPoint_specializes x) |>.eq
      rw [hx, hTeq]
      exact sX.genericPoint_mem_smoothLocus_of_perfectField
    · have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
      convert this using 1
      exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1).symm

/-- A field receiving a point of `Spec` of a `k₀`-algebra, `k₀` of characteristic zero, is
perfect. -/
public lemma perfectField_of_spec_hom {A : Type u} [CommRing A] [Algebra k₀ A] {L : Type u}
    [Field L]
    (t : Spec (.of L) ⟶ Spec (.of A)) : PerfectField L := by
  let φ : k₀ →+* L := ((Scheme.ΓSpecIso (.of A)).inv ≫ t.appTop ≫
    (Scheme.ΓSpecIso (.of L)).hom).hom.comp (algebraMap k₀ A)
  have : CharZero L := (RingHom.charZero_iff φ.injective).mp inferInstance
  infer_instance

/-- The support of a prime divisor whose ideal sheaf is a pull-back. -/
private lemma support_eq_of_idealSheaf_eq {F Y : Scheme.{u}} {fm : F ⟶ Y} {𝓘 : Y.IdealSheafData}
    (Γ : Mori.PrimeDivisor F) (h : Γ.idealSheaf = 𝓘.comap fm) :
    Γ.support = fm ⁻¹' (𝓘.support : Set Y) := by
  change SetLike.coe Γ.idealSheaf.support = _
  rw [h, Scheme.IdealSheafData.support_comap]
  rfl

/-- Prime divisors with the same pull-back ideal sheaf agree. -/
public lemma eq_of_idealSheaf_eq_comap {F Y : Scheme.{u}} {fm : F ⟶ Y} {𝓘 : Y.IdealSheafData}
    {Γ Γ' : Mori.PrimeDivisor F} (h : Γ.idealSheaf = 𝓘.comap fm)
    (h' : Γ'.idealSheaf = 𝓘.comap fm) : Γ = Γ' :=
  AlgebraicGeometry.PrimeDivisor.eq_of_support_eq (by
    rw [support_eq_of_idealSheaf_eq Γ h, support_eq_of_idealSheaf_eq Γ' h'])

/-- **The fibre of a model of an arrow-presented prime divisor.** If the preimage of the support
of a model is the image of an arrow, which is the support of a prime divisor `Ps` of the fibre,
and the model has a prime divisor as fibre, then that fibre is `Ps`. -/
public lemma idealSheaf_eq_comap_iff {F Y : Scheme.{u}} {fm : F ⟶ Y} {𝓘 : Y.IdealSheafData}
    {Ps : Mori.PrimeDivisor F} (hrange : fm ⁻¹' (𝓘.support : Set Y) = Ps.support)
    (hex : ∃ Ps' : Mori.PrimeDivisor F, Ps'.idealSheaf = 𝓘.comap fm) (Γ : Mori.PrimeDivisor F) :
    Γ.idealSheaf = 𝓘.comap fm ↔ Γ = Ps := by
  have key : ∀ Γ : Mori.PrimeDivisor F, Γ.idealSheaf = 𝓘.comap fm → Γ = Ps := fun Γ h =>
    AlgebraicGeometry.PrimeDivisor.eq_of_support_eq
        (by rw [support_eq_of_idealSheaf_eq Γ h, hrange])
  refine ⟨key Γ, fun e => ?_⟩
  obtain ⟨Ps', hPs'⟩ := hex
  rw [e, ← key Ps' hPs', hPs']

/-- **The pull-back of a nonzero wedge of differentials along a birational morphism is
nonzero.** -/
public lemma ιMulti_functionFieldMap_ne_zero {k : Type u} [Field k] [PerfectField k]
    {Z W : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] [LocallyOfFiniteType sZ] (μ : W ⟶ Z) [IsIntegral W]
    [IsDominant μ] (hbij : Function.Bijective (AlgebraicGeometry.functionFieldMap μ)) {n : ℕ}
    (hn : topologicalKrullDim Z = n) (w : Fin n → Z.functionField)
    (hω : letI := MMP.Mori.functionFieldAlgebra sZ
      (exteriorPower.ιMulti Z.functionField n fun i =>
        KaehlerDifferential.D k Z.functionField (w i)) ≠ 0)
    (sW : W ⟶ Spec (.of k)) (hsW : μ ≫ sZ = sW) :
    letI := MMP.Mori.functionFieldAlgebra sW
    (exteriorPower.ιMulti W.functionField n fun i =>
      KaehlerDifferential.D k W.functionField (AlgebraicGeometry.functionFieldMap μ (w i))) ≠ 0 :=
          by
  subst hsW
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (μ ≫ sZ)
  letI := MMP.Mori.functionFieldMapAlgebra μ
  haveI := MMP.Mori.isScalarTower_functionFieldMap sZ μ
  obtain ⟨ω₀, hω₀⟩ := MMP.Mori.exists_isPullbackGenerator_of_bijective sZ μ hbij
    (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  have hω₁ := isPullbackGenerator_of_ne_zero hω₀ hω
  have := hω₁.2.2
  rw [MMP.Mori.topFormsMap_ιMulti] at this
  simp only [KaehlerDifferential.map_D] at this
  exact this

/-- Models pulled back to a later stage are models. -/
public lemma Model.comap_stageCmp_comap_cmp {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) (j : J) (𝓘 : ((M.stage h₀).obj j).left.IdealSheafData) :
    (𝓘.comap (M.stageCmp h₀ h j)).comap (M.cmp (h₀.trans h) j) = 𝓘.comap (M.cmp h₀ j) := by
  rw [← Scheme.IdealSheafData.comap_comp, M.cmp_stageCmp]

/-- Fibres of models pulled back to a later stage are the fibres of the models. -/
public lemma Model.comap_stageCmp_comap_fibreMap {S₀ S₁ S : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀) (h₁ : S₀ ≤ S₁) (h₂ : S₁ ≤ S) {L : Type u} [Field L]
    (t : Spec (.of L) ⟶ Spec (.of S.1)) (j : J) (𝓘 : ((M.stage h₀).obj j).left.IdealSheafData) :
    (𝓘.comap (M.stageCmp h₀ h₁ j)).comap (M.fibreMap (h₀.trans h₁) h₂ t j) =
      𝓘.comap (M.fibreMap h₀ (h₁.trans h₂) t j) := by
  rw [← Scheme.IdealSheafData.comap_comp, M.fibreMap_comp]

include hint in
/-- **Decompositions of fibre products on the fibres.** -/
public lemma eventually_fibreDecomp : M.Eventually fun S h =>
    ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      FibreDecomp X (M.stage h ⋙ Over.pullback t) := by
  classical
  have : Fintype J := FinCategory.fintypeObj
  have hne : ∀ j, Nonempty (X.obj j).left := fun j => by
    have := hint j; infer_instance
  let B : J → J → ℕ := fun j₁ j₂ => Fintype.card (Σ v : J, (v ⟶ j₁) × (v ⟶ j₂))
  have key : ∀ {j₁ j₂ j : J} (f : j₁ ⟶ j) (g : j₂ ⟶ j) (n : ℕ) (w : Fin n → J)
      (a : ∀ k, w k ⟶ j₁) (b : ∀ k, w k ⟶ j₂), M.Eventually fun S h =>
        ∀ (hh : ∀ k, a k ≫ f = b k ≫ g), IsIso (decompMap X f g w a b hh) →
          IsIso (decompMap (M.stage h) f g w a b hh) := by
    intro j₁ j₂ j f g n w a b
    by_cases hd : ∃ hh : ∀ k, a k ≫ f = b k ≫ g, IsIso (decompMap X f g w a b hh)
    · obtain ⟨hh, hiso⟩ := hd
      have hK := (M.cart.isIso_decompMap_iff f g w a b hh).mp hiso
      -- finiteness of the source and target of the comparison map
      have := fun k => M.compactSpace (w k)
      have := fun k => M.quasiSeparatedSpace (w k)
      have := M.compactSpace j₁
      have := M.quasiSeparatedSpace j₁
      have := M.isLocallyNoetherian j₁
      have hc₁ : CompactSpace (∐ fun k => (M.Y.obj (w k)).left : Scheme.{u}) :=
        (finiteSigmaHomeomorph (fun k => (M.Y.obj (w k)).left)).compactSpace
      have hq₁ : QuasiSeparatedSpace (∐ fun k => (M.Y.obj (w k)).left : Scheme.{u}) :=
        (quasiSeparatedSpace_congr (finiteSigmaHomeomorph (fun k => (M.Y.obj (w k)).left))).mp
          quasiSeparatedSpace_finite_sigma
      have := (M.fp j₂).2.1
      have := (M.fp j).2.2
      have := (M.fp j₂).2.2
      have := (M.fp j₂).1
      have : QuasiCompact ((M.Y.map g).left ≫ (M.Y.obj j).hom) := by rw [Over.w]; infer_instance
      have := QuasiCompact.of_comp (M.Y.map g).left (M.Y.obj j).hom
      have : QuasiSeparated ((M.Y.map g).left ≫ (M.Y.obj j).hom) := by rw [Over.w]; infer_instance
      have := QuasiSeparated.of_comp (M.Y.map g).left (M.Y.obj j).hom
      have : LocallyOfFiniteType ((M.Y.map g).left ≫ (M.Y.obj j).hom) := by
        rw [Over.w]; infer_instance
      have := LocallyOfFiniteType.of_comp (f := (M.Y.map g).left) (g := (M.Y.obj j).hom) this
      have hc₂ : CompactSpace (pullback (C := Scheme.{u}) (M.Y.map f).left (M.Y.map g).left) :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
      have hq₂ : QuasiSeparatedSpace (pullback (C := Scheme.{u}) (M.Y.map f).left (M.Y.map g).left)
          :=
        quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
      have : IsLocallyNoetherian (pullback (C := Scheme.{u}) (M.Y.map f).left (M.Y.map g).left) :=
        LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (M.Y.map f).left (M.Y.map g).left)
      have hl : LocallyOfFinitePresentation (decompMap M.Y f g w a b hh) := by
        have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
          HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
        refine LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
          (IsZariskiLocalAtSource.sigmaDesc fun k => ?_)
        have := (M.fp (w k)).1
        have hj₁ : LocallyOfFiniteType (M.Y.obj j₁).hom := by
          have := (M.fp j₁).1; infer_instance
        have hfst : LocallyOfFiniteType (pullback.fst (M.Y.map f).left (M.Y.map g).left) :=
          MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
            (IsPullback.of_hasPullback (M.Y.map f).left (M.Y.map g).left).flip ‹_›
        have : LocallyOfFiniteType (pullback.fst (M.Y.map f).left (M.Y.map g).left ≫
            (M.Y.obj j₁).hom) :=
          MorphismProperty.comp_mem @LocallyOfFiniteType _ _ hfst hj₁
        have : LocallyOfFiniteType (pullback.lift (M.Y.map (a k)).left (M.Y.map (b k)).left
            (by rw [← Over.comp_left, ← Over.comp_left, ← Functor.map_comp, ← Functor.map_comp,
              hh k]) ≫ pullback.fst (M.Y.map f).left (M.Y.map g).left ≫ (M.Y.obj j₁).hom) := by
          rw [pullback.lift_fst_assoc, Over.w]; infer_instance
        exact LocallyOfFiniteType.of_comp (g := pullback.fst (M.Y.map f).left (M.Y.map g).left ≫
            (M.Y.obj j₁).hom) this
      have : CompactSpace (Over.mk (decompMap M.Y f g w a b hh ≫ pullback.fst _ _ ≫
          (M.Y.obj j₁).hom)).left := hc₁
      have : QuasiSeparatedSpace (Over.mk (decompMap M.Y f g w a b hh ≫ pullback.fst _ _ ≫
          (M.Y.obj j₁).hom)).left := hq₁
      have : CompactSpace (Over.mk (pullback.fst (M.Y.map f).left (M.Y.map g).left ≫
          (M.Y.obj j₁).hom)).left := hc₂
      have : QuasiSeparatedSpace (Over.mk (pullback.fst (M.Y.map f).left (M.Y.map g).left ≫
          (M.Y.obj j₁).hom)).left := hq₂
      have : LocallyOfFinitePresentation (decompOver f g w a b hh M.Y).left := hl
      refine (M.eventually_of_exists (MorphismProperty.isomorphisms _) _
        (M.exists_isIso (decompOver f g w a b hh M.Y) hK)).mono fun S h hS _ _ => ?_
      exact ((isCartesian_pullback _ M.Y).isIso_decompMap_iff f g w a b hh).mpr hS
    · exact M.eventually_true.mono fun _ _ _ hh hiso => absurd ⟨hh, hiso⟩ hd
  have H : M.Eventually fun S h => ∀ (j₁ j₂ j : J) (f : j₁ ⟶ j) (g : j₂ ⟶ j)
      (n : Fin (B j₁ j₂ + 1)) (w : Fin n → J) (a : ∀ k, w k ⟶ j₁) (b : ∀ k, w k ⟶ j₂)
      (hh : ∀ k, a k ≫ f = b k ≫ g), IsIso (decompMap X f g w a b hh) →
        IsIso (decompMap (M.stage h) f g w a b hh) :=
    Model.Eventually.forall fun j₁ => Model.Eventually.forall fun j₂ =>
      Model.Eventually.forall fun j => Model.Eventually.forall fun f =>
        Model.Eventually.forall fun g => Model.Eventually.forall fun n =>
          Model.Eventually.forall fun w => Model.Eventually.forall fun a =>
            Model.Eventually.forall fun b => key f g n w a b
  refine H.mono fun S h H L _ t j₁ j₂ j f g n w a b hh hiso => ?_
  have hn : n < B j₁ j₂ + 1 :=
    Nat.lt_succ_of_le (le_card_of_isIso_decompMap X hne f g w a b hh hiso)
  exact (isCartesian_pullback t (M.stage h)).isIso_decompMap f g w a b hh
    (H j₁ j₂ j f g ⟨n, hn⟩ w a b hh hiso)

end Properties

end

end MMP.Spreading
