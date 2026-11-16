module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Blowup
import MMP.AlgebraicGeometry.MMP.Surface.AdjunctionPerfectField
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionUnique
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward

/-!
# Existence and uniqueness of the minimal resolution of a surface in characteristic zero

Let `k` be a field of characteristic zero and `Y` a quasi-projective surface over `k`. Then `Y`
has a minimal resolution: a projective birational morphism `f : X ⟶ Y` from a smooth surface
`X` with `K_X` nef over `Y`. Any two minimal resolutions of `Y` are isomorphic over `Y` by a
unique isomorphism.

## Main results

* `MMP.Resolution.exists_isMinimalSurfaceResolution`: a quasi-projective surface over a field of
  characteristic zero has a minimal resolution, unique up to unique isomorphism over `Y`.

## Implementation notes

The first resolution comes from Lipman's criterion rather than from strong resolution of
singularities: it gives a regular modification `f : X ⟶ Y`, projective since `X` is a regular
surface and `Y` carries an ample line bundle, and smooth since `k` is perfect. While `K_X` is not
`f`-nef, an `f`-exceptional curve `E` with `K_X · E < 0` exists and is contracted; this lowers
the (finite) number of contracted curves, so the process stops at a minimal resolution.
Uniqueness is `existsUnique_iso_comp_eq_of_isMinimalSurfaceResolution`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution], Theorem 2.16.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- A birational (Stacks, Tag 01RO) morphism of integral schemes, locally of finite type, is a
birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    MMP.Mori.IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A quasi-projective surface over a field of characteristic zero has a projective
resolution. -/
private theorem exists_isProjectiveSurfaceResolution {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sY]
    (hY : topologicalKrullDim Y = 2) :
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsNoetherian X) (f : X ⟶ Y)
      (_ : LocallyOfFiniteType (f ≫ sY)), IsProjectiveSurfaceResolution sY f := by
  have hvar : AlgebraicGeometry.IsVariety k sY := inferInstance
  haveI : IsIntegral Y := hvar.toIsIntegral
  haveI : IsNoetherian Y := isNoetherian_of_finiteType sY
  have hk : IsExcellent k := isExcellent_of_standard_classes_and_finiteType.{u, u}.1 k
  let hYc : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_isCompact Y
  let ν := Scheme.normalization Y hYc
  haveI hνfin : IsFinite ν :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sY) hYc
  haveI : IsLocallyNoetherian (Y.normalizationScheme hYc) :=
    LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace (Y.normalizationScheme hYc) := QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian (Y.normalizationScheme hYc) := {}
  haveI : IsNormal (Y.normalizationScheme hYc) := Scheme.isNormal_normalizationScheme Y hYc
  have hdimN : topologicalKrullDim (Y.normalizationScheme hYc) ≤ 2 :=
    hY ▸ topologicalKrullDim_le_of_isIntegralHom ν
  have hT := (tfae_exists_isAlteration_isRegular Y hY).out 4 2
  obtain ⟨X, f, ⟨hbir, hprop, hint⟩, hreg⟩ := hT.1
    ⟨hYc, hνfin, finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hk (ν ≫ sY) hdimN,
      fun y _ => isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing _
        (isExcellent_stalk_of_locallyOfFiniteType hk (ν ≫ sY) y)
        (Stacks.Models.isNormalRing_stalk inferInstance y)⟩
  haveI := hprop
  haveI := hint
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  have hdimX : topologicalKrullDim X = 2 :=
    (topologicalKrullDim_eq_of_isModification f ⟨hbir, hprop, hint⟩).trans hY
  obtain ⟨-, L, hLinv, hLamp⟩ : Stacks.HProjective.IsQuasiProjective sY :=
    IsQuasiProjectiveVariety.isQuasiProjective (f := sY)
  haveI := hLinv
  have hfp : IsProjectiveMorphism f := isProjectiveMorphism_of_isProjective f L
    (Stacks.HProjective.isAmple_of_isRelativelyAmple_of_isAffine sY L hLamp)
    (isProjective_of_isRegular_of_topologicalKrullDim_le_two f hreg hdimX.le)
  have hregs := (isRegular_iff_regular_stalks X).1 hreg
  refine ⟨X, hint, inferInstance, f, inferInstance, hvar, hY, hfp,
    isBirationalMorphism_of_isBirational f hbir, ?_, hdimX⟩
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨V, hxV, hV⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp _ x).1
    ((smoothAt_locus_eq_regular_locus k (f ≫ sY)).symm.subset (hregs.2 x))
  exact MMP.Mori.le_smoothLocus (f ≫ sY) hV hxV

/-- A resolution which is not minimal has a `K`-negative exceptional curve, for a canonical
divisor `K` given by a nonzero rational `2`-form. -/
private theorem exists_cartierCurveIntersection_neg_of_not_isMinimalSurfaceResolution
    {k : Type u} [Field k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral X]
    [IsNoetherian X] (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)]
    (hf : IsProjectiveSurfaceResolution sY f) (hmin : ¬ IsMinimalSurfaceResolution sY f) :
    ∃ (E : MMP.Mori.ProperCurve (f ≫ sY)) (_ : IsContractedProjectiveCurve (f ≫ sY) f E)
      (K : X.CartierDivisor),
      (∃ ω : MMP.Mori.RationalPluriForms (f ≫ sY) 2 1, ω ≠ 0 ∧
        ∀ P : AlgebraicGeometry.PrimeDivisor X,
          (cartierWeilDivisor K).1 P = (divisorOfFormOnSmoothLocus ω) P) ∧
      cartierCurveIntersection K E < 0 := by
  classical
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sY) := {}
  haveI : LocallyOfFinitePresentation (f ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sY)).mpr inferInstance
  haveI : Smooth (f ≫ sY) := (MMP.Mori.isSmoothScheme_iff (f ≫ sY)).1 hf.isSmoothScheme
  haveI : IsSmoothVariety k (f ≫ sY) := {}
  unfold IsMinimalSurfaceResolution at hmin
  push Not at hmin
  obtain ⟨ω, hω, hK⟩ := hmin hf
  obtain ⟨K, hKeq⟩ := (MMP.Mori.Divisor.cartier_weil_dictionary_of_isSmoothVariety k
    (f ≫ sY)).2.2.1.2 (divisorOfFormOnSmoothLocus ω)
  have hKP : ∀ P : AlgebraicGeometry.PrimeDivisor X,
      (cartierWeilDivisor K).1 P = (divisorOfFormOnSmoothLocus ω) P := fun P => by
    have := DFunLike.congr_fun hKeq P
    dsimp only at this
    rw [weilDivisorEquivFinsupp_cartierWeilDivisor, Finsupp.ofSupportFinite_coe] at this
    rw [cartierWeilDivisor_apply]
    exact this
  have hnef := hK K hKP
  unfold IsNefOnContractedCurves at hnef
  push Not at hnef
  obtain ⟨E, hE, hneg⟩ := hnef
  refine ⟨E, hE, K, ⟨ω, hω, hKP⟩, ?_⟩
  simp only [curveIntersectionPairing, MMP.Mori.KCartierDivisor.ofCartier,
    MMP.Mori.ProperCurve.cycle, Finsupp.linearCombination_single, LinearMap.smul_apply,
    one_smul] at hneg
  exact_mod_cast hneg

/-- The curves contracted by a resolution form a finite set. -/
private theorem finite_setOf_isContractedBy_of_isProjectiveSurfaceResolution {k : Type u}
    [Field k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ sY)] (hf : IsProjectiveSurfaceResolution sY f) :
    {C : MMP.Mori.ProperCurve (f ≫ sY) | C.IsContractedBy f}.Finite := by
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsIntegral Y := hf.isVariety.toIsIntegral
  haveI : IsNoetherian Y := isNoetherian_of_finiteType sY
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sY) := {}
  exact finite_setOf_isContractedBy (k := k) (sX := f ≫ sY) inferInstance hf.dim_source_eq.le
    (MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism
      hf.isBirationalMorphism)

/-- A morphism which is an isomorphism over an open `U` hits every point of `U`. -/
private theorem exists_eq_of_isIso_morphismRestrict {X X₁ : Scheme.{u}} (h : X ⟶ X₁)
    (U : X₁.Opens) [IsIso (h ∣_ U)] {y : X₁} (hy : y ∈ U) : ∃ x : X, h.base x = y := by
  obtain ⟨x, hx⟩ := (asIso (h ∣_ U)).hom.homeomorph.surjective ⟨y, hy⟩
  exact ⟨x.1, (morphismRestrict_base_coe h U x).symm.trans (congrArg Subtype.val hx)⟩

/-- The contraction of a curve is surjective. -/
private theorem surjective_base_of_contraction {X X₁ : Scheme.{u}} (h : X ⟶ X₁) (p : X)
    (x₁ : X₁) (hx₁ : IsClosed ({x₁} : Set X₁)) (hfib : h.base ⁻¹' {x₁} = closure {p})
    (hiso : IsIso (h ∣_ ⟨{x₁}ᶜ, hx₁.isOpen_compl⟩)) : Function.Surjective h.base := by
  intro z
  by_cases hz : z = x₁
  · subst hz
    have hp : p ∈ h.base ⁻¹' {z} := hfib ▸ subset_closure rfl
    exact ⟨p, hp⟩
  · exact exists_eq_of_isIso_morphismRestrict h ⟨{x₁}ᶜ, hx₁.isOpen_compl⟩ hz

section Curves

variable {k : Type u} [Field k] {S : Scheme.{u}}

/-- The closure of the generic point of a proper curve has dimension one. -/
private theorem topologicalKrullDim_closure_singleton_point_eq_one {sS : S ⟶ Spec (.of k)}
    (C : MMP.Mori.ProperCurve sS) : topologicalKrullDim (closure ({C.point} : Set S)) = 1 := by
  rw [← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (MMP.Mori.range_curveSubschemeAtι C.point))).isHomeomorph).symm

/-- The generic point of a proper curve is not closed. -/
private theorem not_isClosed_singleton_point {sS : S ⟶ Spec (.of k)}
    (C : MMP.Mori.ProperCurve sS) : ¬ IsClosed ({C.point} : Set S) := fun hcl => by
  have h : topologicalKrullDim ({C.point} : Set S) ≤ 0 :=
    @topologicalKrullDim_zero_of_discreteTopology _ _
      (@Subsingleton.discreteTopology _ _ (Set.subsingleton_singleton (a := C.point)).coe_sort)
  rw [← hcl.closure_eq, topologicalKrullDim_closure_singleton_point_eq_one] at h
  exact absurd h (by decide)

end Curves

/-- On a surface `X`, proper over a `k`-variety `Y`, a non-closed point `x` whose closure is a
proper closed subset contracted by `f` to a point is the generic point of a proper curve. -/
private theorem isProperCurve_of_isContracted {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hX : topologicalKrullDim X ≤ 2) {x : X}
    (hxc : ¬ IsClosed ({x} : Set X)) (hne : closure ({x} : Set X) ≠ Set.univ)
    (hcon : ∀ z ∈ closure ({x} : Set X), f.base z = f.base x) :
    MMP.Mori.IsProperCurve (f ≫ sY) x := by
  obtain ⟨c, hc, hcx⟩ : ∃ c ∈ closure ({x} : Set X), c ≠ x := by
    by_contra! hcon'
    exact hxc (closure_subset_iff_isClosed.mp fun z hz => hcon' z hz)
  haveI : IsIntegral (MMP.Mori.curveSubschemeAt x) :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hfx : IsClosed ({f.base x} : Set Y) := by
    convert f.isClosedMap _ (isClosed_closure (s := ({x} : Set X))) using 1
    ext w
    exact ⟨by rintro rfl; exact ⟨x, subset_closure rfl, rfl⟩,
      by rintro ⟨z, hz, rfl⟩; exact hcon z hz⟩
  have hprop := MMP.Mori.isProper_comp_of_range_subset_singleton sY
    (MMP.Mori.curveSubschemeAtι x ≫ f) hfx (by
      rintro _ ⟨z, rfl⟩
      exact hcon _ (MMP.Mori.range_curveSubschemeAtι x ▸ ⟨z, rfl⟩))
  rw [Category.assoc] at hprop
  refine ⟨?_, hprop⟩
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact MMP.Mori.topologicalKrullDim_eq_one_of_ne_univ hX isClosed_closure hne
    (subset_closure rfl) hc (specializes_iff_mem_closure.mpr hc) hcx.symm

/-- A curve contracted by `f₁` is the image of a curve contracted by `f` other than the
contracted curve `E`, when `f = h ≫ f₁` and `h` contracts `E` to a closed point `x₁` and is an
isomorphism over the complement of `x₁`. -/
private theorem exists_properCurve_of_contraction {k : Type u} [Field k] {X X₁ Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y)
    (hf : IsProjectiveSurfaceResolution sY f) (f₁ : X₁ ⟶ Y)
    (hf₁ : IsProjectiveSurfaceResolution sY f₁) (h : X ⟶ X₁) (hh : h ≫ f₁ = f) (p : X) (x₁ : X₁)
    (hx₁ : IsClosed ({x₁} : Set X₁)) (hfib : h.base ⁻¹' {x₁} = closure {p})
    (hiso : IsIso (h ∣_ ⟨{x₁}ᶜ, hx₁.isOpen_compl⟩))
    (C₁ : MMP.Mori.ProperCurve (f₁ ≫ sY)) (hC₁ : C₁.IsContractedBy f₁) :
    ∃ C : MMP.Mori.ProperCurve (f ≫ sY), C.IsContractedBy f ∧ h.base C.point = C₁.point ∧
      C.point ≠ p := by
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  have hyc : ¬ IsClosed ({C₁.point} : Set X₁) := not_isClosed_singleton_point C₁
  have hyU : C₁.point ∈ (⟨{x₁}ᶜ, hx₁.isOpen_compl⟩ : X₁.Opens) := fun hyx =>
    hyc (Set.mem_singleton_iff.mp hyx ▸ hx₁)
  obtain ⟨x, hx⟩ := exists_eq_of_isIso_morphismRestrict h _ hyU
  have hmaps : ∀ z ∈ closure ({x} : Set X), h.base z ∈ closure ({C₁.point} : Set X₁) :=
    fun z hz => hx ▸ Set.image_singleton (f := h.base) ▸
      image_closure_subset_closure_image h.continuous ⟨z, hz, rfl⟩
  have hcon : ∀ z ∈ closure ({x} : Set X), f.base z = f.base x := fun z hz => by
    subst hh
    change f₁.base (h.base z) = f₁.base (h.base x)
    rw [hx]
    exact hC₁ _ (hmaps z hz)
  have hxc : ¬ IsClosed ({x} : Set X) := fun hc => hyc (by
    haveI : IsProper (h ≫ f₁) := hh ▸ ‹IsProper f›
    haveI : IsProper f₁ := isProper_of_isProjectiveMorphism f₁ hf₁.isProjectiveMorphism
    haveI : IsProper h := IsProper.of_comp h f₁
    simpa [hx] using h.isClosedMap _ hc)
  have hne : closure ({x} : Set X) ≠ Set.univ := fun huniv => by
    have hsurj := surjective_base_of_contraction h p x₁ hx₁ hfib hiso
    have h1 : closure ({C₁.point} : Set X₁) = Set.univ := Set.eq_univ_of_forall fun z => by
      obtain ⟨w, rfl⟩ := hsurj z
      exact hmaps w (huniv ▸ Set.mem_univ w)
    have h2 := topologicalKrullDim_closure_singleton_point_eq_one C₁
    rw [h1, (Homeomorph.Set.univ X₁).isHomeomorph.topologicalKrullDim_eq, hf₁.dim_source_eq] at h2
    exact absurd h2 (by decide)
  refine ⟨⟨x, isProperCurve_of_isContracted sY f hf.dim_source_eq.le hxc hne hcon⟩, hcon, hx, ?_⟩
  rintro rfl
  exact hyU (hx ▸ (show x ∈ h.base ⁻¹' {x₁} from hfib ▸ subset_closure rfl))

/-- Contracting a curve `E` decreases the number of contracted curves. -/
private theorem ncard_lt_of_contraction {k : Type u} [Field k] {X X₁ Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y)
    [LocallyOfFiniteType (f ≫ sY)] (hf : IsProjectiveSurfaceResolution sY f)
    (f₁ : X₁ ⟶ Y) (hf₁ : IsProjectiveSurfaceResolution sY f₁) (h : X ⟶ X₁) (hh : h ≫ f₁ = f)
    (E : MMP.Mori.ProperCurve (f ≫ sY)) (hE : E.IsContractedBy f) (x₁ : X₁)
    (hx₁ : IsClosed ({x₁} : Set X₁)) (hfib : h.base ⁻¹' {x₁} = closure {E.point})
    (hiso : IsIso (h ∣_ ⟨{x₁}ᶜ, hx₁.isOpen_compl⟩)) :
    {C : MMP.Mori.ProperCurve (f₁ ≫ sY) | C.IsContractedBy f₁}.ncard <
      {C : MMP.Mori.ProperCurve (f ≫ sY) | C.IsContractedBy f}.ncard := by
  classical
  have hinj : ∀ {Z : Scheme.{u}} {sX : Z ⟶ Spec (.of k)} (s : Set (MMP.Mori.ProperCurve sX)),
      Set.InjOn MMP.Mori.ProperCurve.point s :=
    fun _ _ _ _ _ hab => MMP.Mori.ProperCurve.ext hab
  have hS := finite_setOf_isContractedBy_of_isProjectiveSurfaceResolution sY f hf
  rw [← (hinj _).ncard_image, ← (hinj _).ncard_image]
  set P := MMP.Mori.ProperCurve.point ''
    {C : MMP.Mori.ProperCurve (f ≫ sY) | C.IsContractedBy f}
  have hP : P.Finite := hS.image _
  have hsub : MMP.Mori.ProperCurve.point ''
      {C : MMP.Mori.ProperCurve (f₁ ≫ sY) | C.IsContractedBy f₁} ⊆
        h.base '' (P \ {E.point}) := by
    rintro _ ⟨C₁, hC₁, rfl⟩
    obtain ⟨C, hC, hpt, hne⟩ := exists_properCurve_of_contraction sY f hf f₁ hf₁ h hh E.point x₁
      hx₁ hfib hiso C₁ hC₁
    exact ⟨C.point, ⟨⟨C, hC, rfl⟩, hne⟩, hpt⟩
  calc _ ≤ (h.base '' (P \ {E.point})).ncard := Set.ncard_le_ncard hsub ((hP.diff).image _)
    _ ≤ (P \ {E.point}).ncard := Set.ncard_image_le hP.diff
    _ < P.ncard := Set.ncard_diff_singleton_lt_of_mem ⟨E, hE, rfl⟩ hP

/-- The irreducible source of a resolution is integral and Noetherian, and of finite type over
`k`. -/
private theorem
    isIntegral_and_isNoetherian_and_locallyOfFiniteType_of_isProjectiveSurfaceResolution
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IrreducibleSpace X] (sY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : IsProjectiveSurfaceResolution sY f) :
    IsIntegral X ∧ IsNoetherian X ∧ LocallyOfFiniteType (f ≫ sY) := by
  haveI : AlgebraicGeometry.IsVariety k sY := hf.isVariety
  haveI : IsNoetherian Y := isNoetherian_of_finiteType sY
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf.isProjectiveMorphism
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNormal X :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      hf.isSmoothScheme).2
  exact ⟨isIntegral_of_irreducibleSpace_of_isReduced X, {}, inferInstance⟩

/-- If some projective resolution of `Y` contracts at most `n` curves, then `Y` has a minimal
resolution. -/
private theorem exists_isMinimalSurfaceResolution_of_ncard_le {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sY]
    (n : ℕ) :
    ∀ (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] (f : X ⟶ Y)
      [LocallyOfFiniteType (f ≫ sY)], IsProjectiveSurfaceResolution sY f →
      {C : MMP.Mori.ProperCurve (f ≫ sY) | C.IsContractedBy f}.ncard ≤ n →
      ∃ (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsNoetherian X) (f : X ⟶ Y)
        (_ : LocallyOfFiniteType (f ≫ sY)), IsMinimalSurfaceResolution sY f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ f _ hf hn
  by_cases hmin : IsMinimalSurfaceResolution sY f
  · exact ⟨X, ‹_›, ‹_›, f, ‹_›, hmin⟩
  obtain ⟨E, hE, K, hK, hKE⟩ :=
    exists_cartierCurveIntersection_neg_of_not_isMinimalSurfaceResolution sY f hf hmin
  obtain ⟨X₁, h, f₁, hh, hf₁, x₁, hx₁, -, -, hfib, hiso⟩ :=
    exists_isProjectiveSurfaceResolution_of_cartierCurveIntersection_neg sY
      (IsQuasiProjectiveVariety.isQuasiProjective (f := sY)) f hf E hE K hK hKE
  have hsurj := surjective_base_of_contraction h E.point x₁ hx₁ hfib hiso
  haveI : IrreducibleSpace X₁ := by
    have hirr := (IrreducibleSpace.isIrreducible_univ X).image h.base h.continuous.continuousOn
    rw [Set.image_univ, hsurj.range_eq] at hirr
    exact (irreducibleSpace_def X₁).2 hirr
  obtain ⟨_, _, _⟩ :=
    isIntegral_and_isNoetherian_and_locallyOfFiniteType_of_isProjectiveSurfaceResolution sY f₁ hf₁
  exact ih _ (lt_of_lt_of_le (ncard_lt_of_contraction sY f hf f₁ hf₁ h hh E hE.2 x₁ hx₁ hfib
    hiso) hn) X₁ f₁ hf₁ le_rfl

/-- **Minimal resolution of surfaces in characteristic zero.** A quasi-projective surface `Y`
over a field `k` of characteristic zero has a minimal resolution `f : X ⟶ Y` (a projective
birational morphism from a smooth surface with `K_X` nef over `Y`), and every minimal resolution
`f' : X' ⟶ Y` is isomorphic to it over `Y` by a unique isomorphism `φ` with `φ.hom ≫ f' = f`. -/
@[mmp "thm_mmp_threefold_characteristic_zero_minimal_resolution"]
public theorem exists_isMinimalSurfaceResolution {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsQuasiProjectiveVariety k sY]
    (hY : topologicalKrullDim Y = 2) :
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsNoetherian X) (f : X ⟶ Y)
      (_ : LocallyOfFiniteType (f ≫ sY)),
      IsMinimalSurfaceResolution sY f ∧
        ∀ (X' : Scheme.{u}) [IsIntegral X'] [IsNoetherian X'] (f' : X' ⟶ Y)
          [LocallyOfFiniteType (f' ≫ sY)], IsMinimalSurfaceResolution sY f' →
            ∃! φ : X ≅ X', φ.hom ≫ f' = f := by
  obtain ⟨X₀, _, _, f₀, _, hf₀⟩ := exists_isProjectiveSurfaceResolution sY hY
  obtain ⟨X, _, _, f, _, hf⟩ :=
    exists_isMinimalSurfaceResolution_of_ncard_le sY _ X₀ f₀ hf₀ le_rfl
  exact ⟨X, ‹_›, ‹_›, f, ‹_›, hf, fun X' _ _ f' _ hf' =>
    existsUnique_iso_comp_eq_of_isMinimalSurfaceResolution sY
      (IsQuasiProjectiveVariety.isQuasiProjective (f := sY)) f f' hf hf'⟩

end MMP.Resolution

end
