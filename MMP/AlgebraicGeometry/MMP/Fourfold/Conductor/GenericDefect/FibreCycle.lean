module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Geometrically.BertiniGenericFibres
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Chow.CycleClassRestrict

/-!
# The fibre cycle of a divisor on the general fibres of a curve-and-point model

Let `r : Z ⟶ Y` be a curve-and-point exceptional model with exceptional divisor `F = ∑ Fᵢ`, `T` an
irreducible curve of `Sing Y` and `L E` a `ℚ`-divisor on each component `E` of `F`. For a point
`t` of `T`, the fibre cycle of `(L E)` over `t` is `∑_E ∑_P c_P [P ×_Y t]`, the fundamental cycles
`[P ×_Y t]_1` (Stacks, Tag 02QU) of the fibres of the prime divisors `P` of the `L E`, as closed
subschemes of `F_t = Z ×_Y t`.

For `t` in a dense open of `T` every fibre `P ×_Y t` is reduced (characteristic zero), so its
fundamental cycle is the sum of its components with multiplicity one, and the class of the fibre
cycle is the sum `∑_E ∑_P c_P ∑_C cl(C)` of the cycle classes `MMP.Chow.pointCycleClass` of the
curves `C = closure {x}` which are maximal irreducible subsets of `P ∩ F_t`. In particular, if
these sums vanish for all but finitely many points of an open `T₀` of `T`, the class of the fibre
cycle vanishes on a dense open of `T`.

## Main results

* `MMP.Fourfold.exists_nonempty_open_forall_isReduced_pullback`: over a nonempty open of an
  integral base of finite type over `ℂ`, the fibres of a morphism with reduced source are reduced.
* `MMP.Fourfold.rationalCycleClass_cycleAssociatedToClosedSubscheme_of_isReduced`: the class of
  the fundamental cycle `[W]_1` (Stacks, Tag 02QU) of a reduced closed subscheme `W` is the sum of
  the cycle classes of its curves.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_dense_rationalCycleClass_fibreCycle_eq_zero`:
  the fibre cycle of a divisor vanishes on a dense open of `T` once the sums of the cycle
  classes of the fibre curves vanish at all but finitely many points.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver TensorProduct

universe u

namespace MMP.Fourfold

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-! ### Components of a closed subset and the class of a reduced closed subscheme -/

section Components

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

/-- The maximal irreducible subsets of the image of an embedding `φ` are the images of the
irreducible components of its source. -/
theorem maximal_isIrreducible_subset_range_iff {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) (S : Set B) :
    Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ Set.range φ) S ↔
      ∃ C ∈ irreducibleComponents A, S = φ '' C := by
  constructor
  · rintro ⟨⟨hS, hSr⟩, hmax⟩
    refine ⟨φ ⁻¹' S, ⟨isIrreducible_preimage_of_isEmbedding hφ hS hSr, fun Z' hZ' hle ↦ ?_⟩,
      (Set.image_preimage_eq_of_subset hSr).symm⟩
    exact fun a ha ↦ hmax ⟨hZ'.image φ hφ.continuous.continuousOn, Set.image_subset_range _ _⟩
      ((Set.image_preimage_eq_of_subset hSr).symm.trans_subset (Set.image_mono hle)) ⟨a, ha, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    refine ⟨⟨hC.1.image φ hφ.continuous.continuousOn, Set.image_subset_range _ _⟩,
      fun X ⟨hX, hXr⟩ hle ↦ ?_⟩
    exact (Set.image_preimage_eq_of_subset hXr).symm.trans_subset <| Set.image_mono <|
      hC.2 (isIrreducible_preimage_of_isEmbedding hφ hX hXr) fun a ha ↦ hle ⟨a, ha, rfl⟩

end Components

section ReducedClass

open Stacks.Chow TensorProduct

variable {X W : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

omit [X.Over (Spec (.of ℂ))] [IsComplexScheme X] in
/-- For a closed immersion `j : W ⟶ X`, the closure of a point `x` of `X` is a maximal irreducible
subset of `j(W)` exactly when `x` is the image of a generic point of `W`. -/
theorem maximal_closure_singleton_iff_exists_genericPoints (j : W ⟶ X) [IsClosedImmersion j]
    (x : X) :
    Maximal (fun A : Set X ↦ IsIrreducible A ∧ A ⊆ Set.range j.base) (closure {x}) ↔
      ∃ ξ : genericPoints W, j.base ξ.1 = x := by
  have hemb := j.isClosedEmbedding
  rw [maximal_isIrreducible_subset_range_iff hemb.isEmbedding]
  constructor
  · rintro ⟨Z, hZ, hxZ⟩
    obtain ⟨ξ, rfl⟩ : ∃ ξ : W, closure {ξ} = Z :=
      ⟨_, Chow.closure_componentGenericPoint ⟨Z, hZ⟩⟩
    refine ⟨⟨ξ, hZ⟩, (inseparable_iff_closure_eq.mpr ?_).eq⟩
    rw [hxZ, ← hemb.closure_image_eq, Set.image_singleton]
  · rintro ⟨ξ, rfl⟩
    exact ⟨_, ξ.2, by rw [← hemb.closure_image_eq, Set.image_singleton]⟩

open Classical in
/-- **The class of a reduced closed subscheme.** For a closed immersion `j : W ⟶ X` of a reduced
scheme, the class of the `1`-dimensional part `[j(W)]_1` of the fundamental cycle of `W` (Stacks,
Tag 02QU), as a cycle on `X`, is the sum of the cycle classes `cl_X(x)` of the curves
`closure {x}` which are maximal irreducible subsets of `j(W)`. -/
theorem rationalCycleClass_cycleAssociatedToClosedSubscheme_of_isReduced (j : W ⟶ X)
    [IsClosedImmersion j] [IsReduced W] :
    Chow.rationalCycleClass X 1 ((1 : ℚ) ⊗ₜ cycleAssociatedToClosedSubscheme
        (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) j ((1 : ℕ) : ℤ)) =
      ∑ᶠ (x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) x = (1 : ℕ)})
        (_ : Maximal (fun A : Set X ↦ IsIrreducible A ∧ A ⊆ Set.range j.base) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2 := by
  set α := cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) j
    ((1 : ℕ) : ℤ)
  have hS := Chow.finite_support_cycle α
  have hval : ∀ x : X, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = (1 : ℕ) →
      α.1 x = if ∃ ξ : genericPoints W, j.base ξ.1 = x then 1 else 0 := by
    intro x hx
    split_ifs with h
    · obtain ⟨ξ, rfl⟩ := h
      rw [cycleAssociatedToClosedSubscheme_apply (fieldChowSituation ℂ) _ j _ ξ hx,
        componentMultiplicity_eq_one_of_reduced]
    · exact cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ j _ x
        fun ⟨ξ, hξ, _⟩ ↦ h ⟨ξ, hξ⟩
  have hdim : ∀ x ∈ hS.toFinset, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = (1 : ℕ) := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ _ α.1).mp α.2 x
      (hS.mem_toFinset.mp hx)
  rw [Chow.rationalCycleClass_tmul, one_smul, Chow.cycleClass_eq_sum,
    finsum_cond_eq_sum_of_cond_iff _ (t := hS.toFinset.subtype fun x ↦
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = (1 : ℕ))
      fun {x} _ ↦ by
        rw [maximal_closure_singleton_iff_exists_genericPoints, Finset.mem_subtype,
          hS.mem_toFinset, Function.mem_support, hval x.1 x.2]
        split_ifs with h
        · exact iff_of_true h one_ne_zero
        · exact iff_of_false h fun h' ↦ h' rfl]
  rw [show (∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x =
          (1 : ℕ), Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x =
          (1 : ℕ), Chow.pointCycleClassOrZero ℚ 1 x.1 from
      Finset.sum_congr rfl fun x _ ↦ by rw [Chow.pointCycleClassOrZero, dif_pos x.2],
    Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hdim]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hne : α.1 x ≠ 0 := hS.mem_toFinset.mp hx
  rw [hval x (hdim x hx)] at hne ⊢
  rw [if_pos (not_not.1 fun h ↦ hne (if_neg h)), one_smul]

end ReducedClass

/-! ### Reduced fibres over a general point -/

section GenericReduced

/-- A base change `X ×_S Spec K` of `f : X ⟶ S` to a field is reduced when the fibre of `f` over
the image point is geometrically reduced. -/
theorem isReduced_pullback_of_geometricallyReduced_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    {K : Type u} [Field K] (y : Spec (.of K) ⟶ S)
    (h : ∀ a, GeometricallyReduced (f.fiberToSpecResidueField (y.base a))) :
    IsReduced (pullback f y) := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective y
  change IsReduced (pullback f (Spec.map φ ≫ S.fromSpecResidueField s))
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of K)))
  have ha : (Spec.map φ ≫ S.fromSpecResidueField s).base a = s := by simp
  have hgr := h a
  change GeometricallyReduced (f.fiberToSpecResidueField
    ((Spec.map φ ≫ S.fromSpecResidueField s).base a)) at hgr
  rw [ha] at hgr
  have : IsReduced (pullback (f.fiberToSpecResidueField s) (Spec.map φ)) :=
    hgr.geometrically_isReduced _ _ _ (IsPullback.of_hasPullback _ _)
  have : IsReduced (pullback (pullback.snd f (S.fromSpecResidueField s)) (Spec.map φ)) := this
  exact isReduced_of_isOpenImmersion
    (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) (Spec.map φ)).inv

/-- **Reduced fibres over a general point.** Let `B` be an integral scheme locally of finite type
over `ℂ` and `p : X ⟶ B` quasi-compact and locally of finite type with `X` reduced. Over a
nonempty open `U` of `B`, the base change of `p` along any field-valued point `Spec K ⟶ B` with
image in `U` is reduced. -/
theorem exists_nonempty_open_forall_isReduced_pullback {X B : Scheme.{0}} [IsReduced X]
    [IsIntegral B] (sB : B ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sB] (p : X ⟶ B)
    [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ U : B.Opens, (U : Set B).Nonempty ∧ ∀ (K : Type) [Field K] (y : Spec (.of K) ⟶ B),
      Set.range y.base ⊆ U → IsReduced (pullback p y) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  obtain ⟨V, hV, hbV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show b ∈ (⊤ : B.Opens) from trivial)
  have : Nonempty V := ⟨⟨b, hbV⟩⟩
  let : Algebra ℂ Γ(B, V) :=
    ((sB.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra
  have : Algebra.FiniteType ℂ Γ(B, V) := by
    have h1 := sB.finiteType_appLE (isAffineOpen_top _) hV (by simp)
    have h2 : (Scheme.ΓSpecIso (.of ℂ)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h1.comp h2
  have : IsReduced (pullback p hV.fromSpec) := isReduced_of_isOpenImmersion (pullback.fst _ _)
  obtain ⟨a, ha0, ha⟩ :=
    MMP.exists_ne_zero_forall_geometricallyReduced_fiberToSpecResidueField ℂ
      (pullback.snd p hV.fromSpec)
  refine ⟨B.basicOpen a, ?_, fun K _ y hy ↦ ?_⟩
  · rwa [Set.nonempty_iff_ne_empty, ← Opens.coe_bot, Ne, SetLike.coe_set_eq,
      basicOpen_eq_bot_iff]
  have hyV : Set.range y.base ⊆ Set.range hV.fromSpec.base := by
    rw [hV.range_fromSpec]
    exact hy.trans (B.basicOpen_le a)
  rw [← IsOpenImmersion.lift_fac hV.fromSpec y hyV]
  have : IsReduced (pullback (pullback.snd p hV.fromSpec)
      (IsOpenImmersion.lift hV.fromSpec y hyV)) := by
    refine isReduced_pullback_of_geometricallyReduced_fiber _ _ fun x ↦ ha _ ?_
    have hx : y.base x ∈ B.basicOpen a := hy ⟨x, rfl⟩
    rwa [← IsOpenImmersion.lift_fac hV.fromSpec y hyV, Scheme.Hom.comp_apply,
      ← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen] at hx
  exact isReduced_of_isOpenImmersion
    (pullbackLeftPullbackSndIso p hV.fromSpec (IsOpenImmersion.lift hV.fromSpec y hyV)).inv

end GenericReduced

/-! ### The fibres of a prime divisor of a component of `F` over a general point of a curve -/

section PrimeDivisorFibre

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The closed immersion `curveScheme T ⟶ Y` has image `T`. -/
theorem range_curveι_base (T : IrreducibleCloseds Y) :
    Set.range (curveι T).base = (T : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- If `curveScheme T` is a single point, then `T` has Krull dimension at most zero. -/
theorem topologicalKrullDim_le_zero_of_singleton_eq_univ (T : IrreducibleCloseds Y)
    {η : curveScheme T} (huniv : ({η} : Set (curveScheme T)) = Set.univ) :
    topologicalKrullDim (T : Set Y) ≤ 0 := by
  have hsubT : Subsingleton (T : Set Y) := by
    refine ⟨fun a b ↦ Subtype.ext ?_⟩
    obtain ⟨c, hc⟩ : (a : Y) ∈ Set.range (curveι T).base := by
      rw [range_curveι_base]; exact a.2
    obtain ⟨d, hd⟩ : (b : Y) ∈ Set.range (curveι T).base := by
      rw [range_curveι_base]; exact b.2
    have hc' : c ∈ ({η} : Set (curveScheme T)) := huniv ▸ Set.mem_univ c
    have hd' : d ∈ ({η} : Set (curveScheme T)) := huniv ▸ Set.mem_univ d
    rw [← hc, ← hd, Set.mem_singleton_iff.1 hc', Set.mem_singleton_iff.1 hd']
  have : Subsingleton (IrreducibleCloseds (T : Set Y)) := ⟨fun A B ↦ by
    ext x
    obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
    obtain ⟨b, hb⟩ := B.isIrreducible.nonempty
    exact ⟨fun _ ↦ by rwa [Subsingleton.elim x b], fun _ ↦ by rwa [Subsingleton.elim x a]⟩⟩
  exact Order.krullDim_nonpos_of_subsingleton

omit [IsComplexScheme Z] in
/-- **The fibres of a prime divisor of an exceptional component over a general point of `T`.**
Let `T ⊆ Y` be an irreducible curve, `E` a component of `F` and `P` a prime divisor of `E`. Over
a nonempty open of `T`, every fibre `P ×_Y Spec K` over a field-valued point of that open is
reduced. -/
theorem IsCurvePointExceptionalModel.exists_nonempty_open_isReduced_pullback
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (T : IrreducibleCloseds Y)
    (hT1 : topologicalKrullDim (T : Set Y) = 1) (E : F.support)
    (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) :
    ∃ U : (curveScheme T).Opens, (U : Set (curveScheme T)).Nonempty ∧
      ∀ (K : Type) [Field K] (y : Spec (.of K) ⟶ curveScheme T), Set.range y.base ⊆ U →
        IsReduced (pullback (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
          (y ≫ curveι T)) := by
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  have : AlgebraicGeometry.IsVariety ℂ sY := hr.isResolution.1
  have : IsIntegral P.idealSheaf.subscheme := P.integral
  set φ := P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r with hφ
  have hTc : Set.range (curveι T).base = (T : Set Y) := range_curveι_base T
  by_cases hIm : Set.range φ.base ⊆ (T : Set Y)
  · have hker : (curveι T).ker ≤ φ.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
        ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      intro x hx
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact closure_minimal hIm T.isClosed hx
    let p := IsClosedImmersion.lift (curveι T) φ hker
    have hp : p ≫ curveι T = φ := IsClosedImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (p ≫ curveι T) := by rw [hp]; infer_instance
    have : QuasiCompact (p ≫ curveι T) := by rw [hp]; infer_instance
    have : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p (curveι T)
    have : QuasiCompact p := QuasiCompact.of_comp p (curveι T)
    have : IsIntegral (curveScheme T) :=
      MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
    obtain ⟨U, hU, hred⟩ :=
      exists_nonempty_open_forall_isReduced_pullback (curveι T ≫ sY) p
    refine ⟨U, hU, fun K _ y hy ↦ ?_⟩
    rw [← hp]
    exact @isReduced_of_isOpenImmersion _ _
      (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono p y (curveι T))).isoPullback.inv _
      (hred K y hy)
  · have hφirr : IsIrreducible (Set.range φ.base) := by
      rw [← Set.image_univ]
      exact (irreducibleSpace_def _).1 inferInstance |>.image _ φ.continuous.continuousOn
    have hφE : Set.range φ.base ⊆ r.base '' (E.1.support : Set Z) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨(P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι).base x, ?_, rfl⟩
      change E.1.idealSheaf.subschemeι.base _ ∈ (E.1.idealSheaf.support : Set Z)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    have hdimφ : topologicalKrullDim (Set.range φ.base) ≤ 1 :=
      ((Topology.IsInducing.of_comp (continuous_inclusion hφE) continuous_subtype_val
        Topology.IsInducing.subtypeVal).topologicalKrullDim_le).trans
        (hr.topologicalKrullDim_image_le E.1 E.2)
    have hTφ : ¬ (T : Set Y) ⊆ Set.range φ.base := by
      intro hTφ
      have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hφirr T.isClosed hTφ
        (fun h ↦ hIm h.symm.le) (ne_top_of_le_ne_top (by decide) hdimφ)
      rw [hT1] at hlt
      exact (hlt.trans_le hdimφ).false
    obtain ⟨b, hbT, hbφ⟩ := Set.not_subset.1 hTφ
    have hφcl : IsClosed (Set.range φ.base) := φ.isClosedMap.isClosed_range
    refine ⟨(curveι T) ⁻¹ᵁ ⟨(Set.range φ.base)ᶜ, hφcl.isOpen_compl⟩, ?_, ?_⟩
    · obtain ⟨c, rfl⟩ : b ∈ Set.range (curveι T).base := hTc ▸ hbT
      exact ⟨c, hbφ⟩
    intro K _ y hy
    let Q : Scheme.{0} := pullback φ (y ≫ curveι T)
    have hempty : IsEmpty Q := by
      refine ⟨fun z ↦ ?_⟩
      have h := congrArg (fun f : _ ⟶ Y ↦ f.base z)
        (pullback.condition : pullback.fst φ (y ≫ curveι T) ≫ φ =
          pullback.snd φ (y ≫ curveι T) ≫ y ≫ curveι T)
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at h
      exact hy ⟨_, rfl⟩ ⟨_, h⟩
    have : ∀ z : Q, _root_.IsReduced (Q.presheaf.stalk z) := fun z ↦ (IsEmpty.false z).elim
    exact isReduced_of_isReduced_stalk Q

end PrimeDivisorFibre

/-! ### The fibre cycle at a point with reduced fibres -/

section PointFibreCycle

variable {Z Y : Scheme.{0}} {r : Z ⟶ Y}

/-- The base change `P ×_Y S ⟶ Z ×_Y S` of a closed immersion `i : P ⟶ Z` is a closed
immersion. -/
theorem isClosedImmersion_pullback_map_of_comp_eq {P S : Scheme.{0}} (i : P ⟶ Z)
    [IsClosedImmersion i] (r : Z ⟶ Y) {φ : P ⟶ Y} (hφ : i ≫ r = φ) (g : S ⟶ Y) :
    IsClosedImmersion (pullback.map φ g r g i (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hφ])
      (by simp)) := by
  subst hφ
  have h : IsPullback (pullback.fst (i ≫ r) g)
      (pullback.map (i ≫ r) g r g i (𝟙 _) (𝟙 _) (by simp) (by simp)) i (pullback.fst r g) :=
    IsPullback.of_bot (by simpa using IsPullback.of_hasPullback (i ≫ r) g) (by simp)
      (IsPullback.of_hasPullback r g)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance

/-- The image of `P ×_Y S ⟶ Z ×_Y S` is the preimage of the image of `P`. -/
theorem range_pullback_map_of_comp_eq {P S : Scheme.{0}} (i : P ⟶ Z) (r : Z ⟶ Y) {φ : P ⟶ Y}
    (hφ : i ≫ r = φ) (g : S ⟶ Y) :
    Set.range (pullback.map φ g r g i (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hφ])
      (by simp)).base = (pullback.fst r g).base ⁻¹' Set.range i.base := by
  subst hφ
  rw [Scheme.Pullback.range_map]
  ext x
  exact ⟨And.left, fun h ↦ ⟨h, (pullback.snd r g).base x, rfl⟩⟩

open Classical in
/-- **The fibre cycle at a point with reduced fibres.** Let `g, g' : Spec ℂ ⟶ Y` be equal
points and `L E` divisors on closed subschemes `E` of `Z`. If the fibres `P ×_Y Spec ℂ` of the
prime divisors `P` of the `L E` are reduced, the class of the fibre cycle
`∑_E ∑_P c_P [P ×_Y Spec ℂ]` in `Z ×_Y Spec ℂ` vanishes as soon as the corresponding sum of the
cycle classes of the curves which are maximal irreducible subsets of the fibres vanishes. -/
theorem rationalCycleClass_fibreCycle_eq_zero_of_isReduced {F : Divisor Z}
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (g g' : Spec (.of ℂ) ⟶ Y) (hg : g' = g) :
    letI : (pullback r g).Over (Spec (.of ℂ)) := ⟨pullback.snd r g⟩
    letI : (pullback r g').Over (Spec (.of ℂ)) := ⟨pullback.snd r g'⟩
    ∀ [IsComplexScheme (pullback r g)] [IsComplexScheme (pullback r g')],
    (∀ E : F.support, ∀ P ∈ (L E).support,
      IsReduced (pullback (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g)) →
    (∑ E : F.support, (L E).sum fun P c ↦ c •
        ∑ᶠ (x : {x : ↥(pullback r g' : Scheme.{0}) // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (pullback r g' ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A : Set ↥(pullback r g' : Scheme.{0}) ↦ IsIrreducible A ∧
            A ⊆ (pullback.fst r g').base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) = 0 →
    Chow.rationalCycleClass (pullback r g) 1
      (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
        haveI := isClosedImmersion_pullback_map_of_comp_eq
          (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _) g
        (1 : ℚ) ⊗ₜ[ℤ] Stacks.Chow.cycleAssociatedToClosedSubscheme
          (Stacks.Chow.fieldChowSituation ℂ) (pullback r g ↘ Spec (.of ℂ))
          (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r) g r g
            (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)) ((1 : ℕ) : ℤ)) = 0 := by
  subst hg
  intro _ _ hred h0
  let : (pullback r g').Over (Spec (.of ℂ)) := ⟨pullback.snd r g'⟩
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun E _ ↦ ?_) h0
  rw [map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  have := hred E P hP
  have := isClosedImmersion_pullback_map_of_comp_eq
    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _) g'
  rw [map_smul, rationalCycleClass_cycleAssociatedToClosedSubscheme_of_isReduced,
    range_pullback_map_of_comp_eq _ r (Category.assoc _ _ _), Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Scheme.IdealSheafData.range_subschemeι]

end PointFibreCycle

/-! ### The fibre cycle vanishes on a dense open of `T` -/

omit [IsComplexScheme Z] in
/-- **The fibre cycle of a divisor vanishes on a dense open of each curve.** Let `r : Z ⟶ Y` be a
curve-and-point exceptional model, `T ⊆ Sing Y` an irreducible curve with an adapted open
`T₀ ⊆ T`, and `L E` a `ℚ`-divisor on each component `E` of `F`. Suppose that for all but finitely
many `t ∈ T₀(ℂ)` the sum `∑_E ∑_P c_P ∑_C [C]` vanishes in `H_2(F_t, ℚ)`, `C` running over the
curves which are maximal irreducible subsets of `P ∩ F_t`. Then on a dense open `U` of `T`, the
class in `H_2(F_t, ℚ)` of the fibre cycle `∑_E ∑_P c_P [P ×_Y t]` vanishes for every
`t ∈ U(ℂ)`. -/
theorem IsCurvePointExceptionalModel.exists_dense_rationalCycleClass_fibreCycle_eq_zero
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D)
    (T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hT₀ : ∀ T, IsAdaptedOpen sY r (T₀ T)) (T)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (hev : ∀ᶠ t : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
      ∃ _ : IsComplexScheme (pointFibre sY r (T₀ T) t),
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : pointFibre sY r (T₀ T) t // Stacks.Chow.relativeDimension
              (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A : Set (pointFibre sY r (T₀ T) t) ↦ IsIrreducible A ∧
              A ⊆ (pointFibreFst sY r (T₀ T) t).base ⁻¹'
                (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∃ U : (curveScheme T.1).Opens, Dense (U : Set (curveScheme T.1)) ∧
      ∀ (t : ComplexPoints (U.ι ≫ curveι T.1 ≫ sY))
        [IsComplexScheme (pointFibre sY r U t)],
        Chow.rationalCycleClass (pointFibre sY r U t) 1
          (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
            (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
              (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
              (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                (t.hom ≫ U.ι ≫ curveι T.1) r (t.hom ≫ U.ι ≫ curveι T.1)
                (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (isClosedImmersion_pullback_map_of_comp_eq
                (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                (t.hom ≫ U.ι ≫ curveι T.1)) ((1 : ℕ) : ℤ)) = 0 := by
  have : IsProper r := (IsProjectiveMorphism.isProjective hr.isResolution.2.2.2.1).isProper
  have : AlgebraicGeometry.IsVariety ℂ sY := hr.isResolution.1
  have : IsIntegral (curveScheme T.1) :=
    isIntegral_subscheme_vanishingIdeal ⟨(T.1 : Set Y), T.1.isClosed⟩ T.1.isIrreducible
  choose Ured hUne hUred using
    fun (E : F.support) (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) ↦
      hr.exists_nonempty_open_isReduced_pullback T.1 T.2.2 E P
  let Q : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) → Prop := fun t ↦
    ∃ _ : IsComplexScheme (pointFibre sY r (T₀ T) t),
      (∑ E : F.support, (L E).sum fun P c ↦ c •
        ∑ᶠ (x : {x : pointFibre sY r (T₀ T) t // Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
            (pointFibre sY r (T₀ T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A : Set (pointFibre sY r (T₀ T) t) ↦ IsIrreducible A ∧
            A ⊆ (pointFibreFst sY r (T₀ T) t).base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) = 0
  have hS : {t | ¬ Q t}.Finite := Filter.eventually_cofinite.1 hev
  let pt : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) → curveScheme T.1 := fun t ↦
    (t.hom ≫ (T₀ T).ι).base (IsLocalRing.closedPoint ℂ)
  have hcl : ∀ t, IsClosed ({pt t} : Set (curveScheme T.1)) := fun t ↦
    (pointEquivClosedPoint (curveι T.1 ≫ sY)
      ⟨t.hom ≫ (T₀ T).ι, by rw [Category.assoc]; exact t.2⟩).2
  set Bad : Set (curveScheme T.1) := ⋃ t ∈ {t | ¬ Q t}, {pt t} with hBad
  have hBadcl : IsClosed Bad := hS.isClosed_biUnion fun t _ ↦ hcl t
  set Ugen : Set (curveScheme T.1) :=
    ⋂ E : F.support, ⋂ P ∈ (L E).support, (Ured E P : Set (curveScheme T.1)) with hUgen
  have hUgeno : IsOpen Ugen :=
    isOpen_iInter_of_finite fun E ↦ isOpen_biInter_finset fun P _ ↦ (Ured E P).isOpen
  let U : (curveScheme T.1).Opens :=
    ⟨(T₀ T : Set (curveScheme T.1)) ∩ Ugen ∩ Badᶜ,
      ((T₀ T).isOpen.inter hUgeno).inter hBadcl.isOpen_compl⟩
  set η := genericPoint (curveScheme T.1) with hηdef
  have hη : closure ({η} : Set (curveScheme T.1)) = Set.univ := genericPoint_spec _
  have hmemη : ∀ V : (curveScheme T.1).Opens, (V : Set (curveScheme T.1)).Nonempty → η ∈ V :=
    fun V hV ↦ ((genericPoint_spec (curveScheme T.1)).mem_open_set_iff V.isOpen).2
      (by rw [Set.univ_inter]; exact hV)
  have hηU : η ∈ U := by
    refine ⟨⟨hmemη _ (hT₀ T).dense.nonempty, ?_⟩, ?_⟩
    · exact Set.mem_iInter.2 fun E ↦ Set.mem_iInter₂.2 fun P _ ↦ hmemη _ (hUne E P)
    · intro hηB
      obtain ⟨t, -, ht⟩ := Set.mem_iUnion₂.1 hηB
      rw [Set.mem_singleton_iff] at ht
      have huniv : ({η} : Set (curveScheme T.1)) = Set.univ := by
        rw [← hη, ht]; exact (hcl t).closure_eq.symm
      have hle := topologicalKrullDim_le_zero_of_singleton_eq_univ T.1 huniv
      rw [T.2.2] at hle
      exact absurd hle (by decide)
  refine ⟨U, fun x ↦ closure_mono (Set.singleton_subset_iff.2 hηU) (hη ▸ Set.mem_univ x), ?_⟩
  intro t ht
  have hleU : U ≤ T₀ T := fun x hx ↦ hx.1.1
  let t' : analyticSpace ((T₀ T).ι ≫ curveι T.1 ≫ sY) :=
    ⟨t.hom ≫ (curveScheme T.1).homOfLE hleU, by
      rw [Category.assoc, Scheme.homOfLE_ι_assoc]; exact t.2⟩
  have hg : t'.hom ≫ (T₀ T).ι ≫ curveι T.1 = t.hom ≫ U.ι ≫ curveι T.1 := by
    change (t.hom ≫ (curveScheme T.1).homOfLE hleU) ≫ (T₀ T).ι ≫ curveι T.1 = _
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]
  have hmemU : ∀ a, (t.hom ≫ U.ι).base a ∈ U := fun a ↦ by
    rw [Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← Scheme.Opens.range_ι U]
    exact ⟨_, rfl⟩
  have hgood : Q t' := by
    by_contra hbad
    have hB : pt t' ∈ Bad := Set.mem_biUnion hbad (Set.mem_singleton _)
    have hpt : pt t' = (t.hom ≫ U.ι).base (IsLocalRing.closedPoint ℂ) := by
      change ((t.hom ≫ (curveScheme T.1).homOfLE hleU) ≫ (T₀ T).ι).base _ = _
      rw [Category.assoc, Scheme.homOfLE_ι]
    rw [hpt] at hB
    exact (hmemU _).2 hB
  obtain ⟨hc, h0⟩ := hgood
  have hred : ∀ E : F.support, ∀ P ∈ (L E).support,
      IsReduced (pullback (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
        (t.hom ≫ U.ι ≫ curveι T.1)) := by
    intro E P hP
    have h := hUred E P ℂ (t.hom ≫ U.ι) (by
      rintro _ ⟨a, rfl⟩
      exact Set.mem_iInter₂.1 (Set.mem_iInter.1 (hmemU a).1.2 E) P hP)
    rwa [Category.assoc] at h
  let : (pullback r (t.hom ≫ U.ι ≫ curveι T.1)).Over (Spec (.of ℂ)) := ⟨pullback.snd _ _⟩
  let : (pullback r (t'.hom ≫ (T₀ T).ι ≫ curveι T.1)).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ _⟩
  have : IsComplexScheme (pullback r (t.hom ≫ U.ι ≫ curveι T.1)) := ht
  have : IsComplexScheme (pullback r (t'.hom ≫ (T₀ T).ι ≫ curveι T.1)) := hc
  exact rationalCycleClass_fibreCycle_eq_zero_of_isReduced (r := r) L
    (t.hom ≫ U.ι ≫ curveι T.1) (t'.hom ≫ (T₀ T).ι ≫ curveι T.1) hg hred h0

end MMP.Fourfold
