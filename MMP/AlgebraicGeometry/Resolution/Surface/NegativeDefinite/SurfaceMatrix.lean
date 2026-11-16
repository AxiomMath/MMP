/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DegreeBound
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinate

/-!
# Negative definiteness of the exceptional curves of a surface

Let `f : Y ⟶ X` be a proper birational morphism from a smooth surface over a field `k` to a
variety, and `E₁, …, Eₙ` distinct proper curves on `Y` whose images are points. Then the
intersection matrix `((Eᵢ · Eⱼ))` is negative definite; in particular `(Eᵢ · Eᵢ) < 0`.

Curves over distinct points are disjoint, so the matrix is block diagonal along the fibres of
`f`. The curves over a point `x` lie in `V = f⁻¹ U` for an affine open neighbourhood `U` of `x`,
the restriction `V ⟶ U` is again proper and finite over a neighbourhood of the generic point,
and Kollár 2.12 over an affine base applies on `V`. What makes the passage to `V` possible is
that intersection numbers of prime divisors with proper curves contained in `V` can be computed
on `V`: on a smooth scheme `𝒪_Y(P)` is the invertible sheaf of the effective Cartier divisor
`P`, whose pull-back to `V` is the invertible sheaf of `P ∩ V` ([Stacks, Tag 0C4U]), and the
curve, as a closed subscheme of `V`, is isomorphic over `Y` to the curve as a closed subscheme of
`Y`, which leaves the degree unchanged ([Stacks, Tag 0B59]).

## Main results

* `MMP.Threefold.Resolution.intersectionNumber_restrict_open`: `(P|_V · C) = (P · C)` for a
  proper curve `C ⊆ V`.
* `MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism`: the
  intersection matrix of the curves contracted by a proper birational morphism from a smooth
  surface to a variety is negative definite.
* `MMP.Threefold.Resolution.intersectionNumber_self_neg_of_isBirationalMorphism`: each contracted
  curve has negative self-intersection.

## Implementation notes

The source assumes `k` algebraically closed and `X` a normal surface; neither is used, and `X`
is only required to be a variety over `k`. As in
`MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism_of_isAffine`,
each curve `Eᵢ` is a prime divisor `Pᵢ` together with the proper curve `Cᵢ` of the same generic
point, and `(Eᵢ · Eⱼ)` is the intersection number of `Pᵢ` with `Cⱼ`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 2.12]
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Threefold.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Threefold.Resolution

/-- Equal ideal sheaves have isomorphic closed subschemes, over the ambient scheme. -/
theorem exists_subscheme_iso_of_eq {Y : Scheme.{u}} {I J : Y.IdealSheafData} (h : I = J) :
    ∃ e : I.subscheme ≅ J.subscheme, e.hom ≫ J.subschemeι = I.subschemeι := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

/-- The inverse image of the reduced closed subscheme on the closure of `j x` under an open
immersion `j` is the reduced closed subscheme on the closure of `x`. -/
theorem comap_vanishingIdeal_closure_singleton {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] (x : V) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set Y))).comap j =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set V)) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set Y))
  have : IsReduced (I.comap j).subscheme :=
    isReduced_of_isOpenImmersion ((I.comapIso j).hom ≫ Limits.pullback.snd j I.subschemeι)
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  rw [Scheme.IdealSheafData.support_comap]
  apply Closeds.ext
  rw [Closeds.coe_preimage, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    Closeds.coe_closure, j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
    Set.image_singleton]

/-- **A curve in an open subscheme.** If the closure of `j x` lies in the image of the open
immersion `j : V ⟶ Y`, the reduced closed subscheme of `V` on the closure of `x` is isomorphic,
over `Y`, to the reduced closed subscheme of `Y` on the closure of `j x`. -/
theorem exists_curveSubschemeAt_iso {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j] (x : V)
    {y : Y} (hxy : j x = y) (hx : closure ({y} : Set Y) ⊆ Set.range j) :
    ∃ e : curveSubschemeAt x ≅ curveSubschemeAt y,
      e.hom ≫ curveSubschemeAtι y = curveSubschemeAtι x ≫ j := by
  subst hxy
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({j x} : Set Y))
  obtain ⟨e₁, he₁⟩ := exists_subscheme_iso_of_eq (comap_vanishingIdeal_closure_singleton j x)
  have hsurj : Function.Surjective (Limits.pullback.snd j I.subschemeι) := by
    intro z
    have hz : I.subschemeι z ∈ closure ({j x} : Set Y) := by
      have : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    obtain ⟨v, hv⟩ := hx hz
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback v z hv
    exact ⟨w, hw⟩
  have : Epi (Limits.pullback.snd j I.subschemeι).base :=
    (TopCat.epi_iff_surjective _).2 hsurj
  have : IsIso (Limits.pullback.snd j I.subschemeι) := IsOpenImmersion.isIso _
  refine ⟨e₁.symm ≪≫ I.comapIso j ≪≫ asIso (Limits.pullback.snd j I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← Limits.pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc, ← he₁,
    Category.assoc, Iso.inv_hom_id_assoc]

variable (k : Type u) [Field k]

/-- The degree of an invertible sheaf on a curve depends on the structure morphism only through
its value. -/
theorem invertibleCurveDegree_congr {C : Scheme.{u}} {f f' : C ⟶ Spec (.of k)} [IsProper f]
    [IsProper f'] (h : f = f') (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L = invertibleCurveDegree k f' hdim L := by
  subst h
  rfl

/-- The degree along a curve is unchanged by an isomorphism of curves over `X`. -/
theorem degreeOn_eq_of_iso_comp {X C C' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (i : C ⟶ X)
    (i' : C' ⟶ X) [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Mori.degreeOn k sX i hdim L = Mori.degreeOn k sX i' hdim' L := by
  subst he
  have h1 := invertibleCurveDegree_pullback_of_isIso e.hom (i' ≫ sX) hdim hdim'
    ((Scheme.Modules.pullback i').obj L)
  rw [Mori.degreeOn_eq_invertibleCurveDegree, Mori.degreeOn_eq_invertibleCurveDegree, ← h1]
  rw [invertibleCurveDegree_congr k (Category.assoc e.hom i' sX)]
  exact invertibleCurveDegree_eq_of_iso k _ hdim
    ((Scheme.Modules.pullbackComp e.hom i').app L).symm

/-- The degree along `i ≫ g` of `L` is the degree along `i` of the pull-back `g^* L`. -/
theorem degreeOn_comp {X V C : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (g : V ⟶ X) (i : C ⟶ V)
    [IsProper ((i ≫ g) ≫ sX)] [IsProper (i ≫ g ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Mori.degreeOn k sX (i ≫ g) hdim L =
      Mori.degreeOn k (g ≫ sX) i hdim ((Scheme.Modules.pullback g).obj L) := by
  rw [Mori.degreeOn_eq_invertibleCurveDegree, Mori.degreeOn_eq_invertibleCurveDegree,
    invertibleCurveDegree_congr k (Category.assoc i g sX)]
  exact invertibleCurveDegree_eq_of_iso k _ hdim
    ((Scheme.Modules.pullbackComp i g).app L).symm

/-- An open subscheme of a scheme smooth over `k` is smooth over `k`. -/
theorem isSmoothScheme_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)} (hsm : IsSmoothScheme s)
    (V : Y.Opens) : IsSmoothScheme (V.ι ≫ s) := by
  rw [IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 (hsm ▸ trivial : V.ι x ∈ smoothLocus s)
  refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ W, hxW, ?_⟩
  have : Smooth (W.ι ≫ s) := hW
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- The ideal sheaf of a prime divisor restricts, along an open immersion, to the ideal sheaf of
its restriction. -/
theorem comap_idealSheaf_primeDivisorMap {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]
    (V : Y.Opens) [IsNormal V.toScheme] (PV : Mori.PrimeDivisor V.toScheme) :
    (OpenWeilRestriction.primeDivisorMap V.ι PV).idealSheaf.comap V.ι = PV.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf,
    ← vanishingIdeal_closure_genericPoint_eq_idealSheaf PV,
    show Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap V.ι PV) =
      V.ι PV.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap V.ι PV]
  exact comap_vanishingIdeal_closure_singleton V.ι _

/-- The invertible sheaf of an effective Cartier divisor is invertible, in the spelling of
`MMP.Mori.degreeOn`. -/
instance isInvertible_invertibleSheaf' {Y : Scheme.{u}} (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.invertibleSheaf' D : Y.Modules) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Divisors.isTensorInvertible_invertibleSheaf D)

/-- Equal effective Cartier divisors have isomorphic invertible sheaves. -/
theorem nonempty_invertibleSheaf'_iso_of_eq {Y : Scheme.{u}} {D D' : Y.IdealSheafData}
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D']
    (h : D = D') :
    Nonempty ((Stacks.Divisors.invertibleSheaf' D : Y.Modules) ≅
      (Stacks.Divisors.invertibleSheaf' D' : Y.Modules)) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- On a scheme smooth over `k`, the intersection number of a prime divisor `P` with a proper
curve is the degree along the curve of the invertible sheaf of the effective Cartier divisor
`P`. -/
theorem intersectionNumber_single_eq_degreeOn_invertibleSheaf' {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme s) (P : Mori.PrimeDivisor Y)
    [Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf] (C : ProperCurve s) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k s C.ι C.dim_le
        (isQCartier_single_of_isSmoothScheme hsm P) =
      Mori.degreeOn k s C.ι C.dim_le
        (Stacks.Divisors.invertibleSheaf' P.idealSheaf : Y.Modules) := by
  have := QuasiCompact.compactSpace_of_compactSpace s
  have hcart := isCartier_single_of_isSmoothScheme hsm P
  rw [QDivisor.intersectionNumber_toQDivisor k s C.ι C.dim_le _ hcart]
  obtain ⟨b⟩ := nonempty_divisorialSheaf_single_iso_invertibleSheaf' P inferInstance hcart
  have := hcart.isInvertibleModule_divisorialSheaf
  exact congrArg (fun n : ℤ => (n : ℚ)) (Mori.degreeOn_eq_of_iso k s C.ι C.dim_le b)

/-- **Intersection numbers can be computed on an open subscheme.** Let `Y` be smooth over `k`,
`V ⊆ Y` open, `P` a prime divisor of `Y` with restriction `P_V` to `V`, and `C` a proper curve
of `Y` contained in `V`, which is the proper curve `C_V` of `V`. Then `(P_V · C_V) = (P · C)`. -/
theorem intersectionNumber_restrict_open {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme s)
    (V : Y.Opens) [QuasiCompact (V.ι ≫ s)] [IsNormal V.toScheme]
    (P : Mori.PrimeDivisor Y) (PV : Mori.PrimeDivisor V.toScheme)
    (hP : OpenWeilRestriction.primeDivisorMap V.ι PV = P) (C : ProperCurve s)
    (CV : ProperCurve (V.ι ≫ s)) (hC : V.ι CV.point = C.point)
    (hCV : closure ({C.point} : Set Y) ⊆ V) :
    (Divisor.toQDivisor (Finsupp.single PV 1)).intersectionNumber k (V.ι ≫ s) CV.ι CV.dim_le
        (isQCartier_single_of_isSmoothScheme (isSmoothScheme_ι k hsm V) PV) =
      (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k s C.ι C.dim_le
        (isQCartier_single_of_isSmoothScheme hsm P) := by
  subst hP
  set P := OpenWeilRestriction.primeDivisorMap V.ι PV
  have hsmV := isSmoothScheme_ι k hsm V
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsmV PV
  have hcomap := comap_idealSheaf_primeDivisorMap V PV
  have : Stacks.Divisors.IsPullbackDefined V.ι P.idealSheaf := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (P.idealSheaf.comap V.ι)
    rw [hcomap]
    infer_instance
  rw [intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsm P C,
    intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsmV PV CV]
  obtain ⟨e, he⟩ := exists_curveSubschemeAt_iso V.ι CV.point hC (by rwa [Scheme.Opens.range_ι])
  have : IsProper ((CV.ι ≫ V.ι) ≫ s) := by
    rw [Category.assoc]
    infer_instance
  have h1 := degreeOn_eq_of_iso_comp k s C.ι (CV.ι ≫ V.ι) C.dim_le CV.dim_le e.symm (by
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    exact he.symm)
    (Stacks.Divisors.invertibleSheaf' P.idealSheaf : Y.Modules)
  have h2 := degreeOn_comp k s V.ι CV.ι CV.dim_le
    (Stacks.Divisors.invertibleSheaf' P.idealSheaf : Y.Modules)
  obtain ⟨e₂⟩ := nonempty_invertibleSheaf'_iso_of_eq hcomap
  have h3 := Mori.degreeOn_eq_of_iso k (V.ι ≫ s) CV.ι CV.dim_le
    (Stacks.Divisors.invertibleSheafPullbackIso V.ι P.idealSheaf ≪≫ e₂)
  exact congrArg (fun n : ℤ => (n : ℚ)) (h1.trans (h2.trans h3)).symm

/-- A proper curve of `Y` contained in an open `V` is a proper curve of `V`. -/
theorem exists_properCurve_of_closure_subset {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (V : Y.Opens) (C : ProperCurve s) (hCV : closure ({C.point} : Set Y) ⊆ V) :
    ∃ CV : ProperCurve (V.ι ≫ s), V.ι CV.point = C.point := by
  obtain ⟨x, hx⟩ : C.point ∈ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact hCV (subset_closure rfl)
  obtain ⟨e, he⟩ := exists_curveSubschemeAt_iso V.ι x hx (by rwa [Scheme.Opens.range_ι])
  refine ⟨⟨x, ⟨?_, ?_⟩⟩, hx⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · rw [← Category.assoc, ← he, Category.assoc]
    have : IsProper (curveSubschemeAtι C.point ≫ s) := C.isProper_ι_comp
    infer_instance

/-- A prime divisor of `Y` whose generic point lies in the open `V` is the image of a prime
divisor of `V`. -/
theorem exists_primeDivisorMap_eq {Y : Scheme.{u}} (V : Y.Opens) (P : Mori.PrimeDivisor Y)
    (hP : Mori.PrimeDivisor.genericPoint P ∈ V) :
    ∃ PV : Mori.PrimeDivisor V.toScheme, OpenWeilRestriction.primeDivisorMap V.ι PV = P :=
  (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι P).2 (by rwa [Scheme.Opens.range_ι])

/-- A matrix indexed by an empty type is positive definite. -/
theorem _root_.MMP.MatrixPosDef.posDef_of_isEmpty {n : Type*} [IsEmpty n]
    (M : Matrix n n ℝ) : M.PosDef :=
  ⟨Matrix.ext isEmptyElim, fun x hx => absurd (Subsingleton.elim x 0) hx⟩

variable {k} {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}

private theorem ι_morphismRestrict_apply (f : Y ⟶ X) (U : X.Opens)
    (y : (f ⁻¹ᵁ U).toScheme) :
    U.ι ((f ∣_ U) y) = f ((f ⁻¹ᵁ U).ι y) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- The restriction over an open `U` of a birational morphism of integral schemes, with integral
inverse image of `U`, is finite over an open of `U` meeting its range. -/
theorem exists_isFinite_morphismRestrict_restrict_of_isBirationalMorphism [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] {f : Y ⟶ X} [IsProper f]
    (hb : MMP.Mori.IsBirationalMorphism f) (U : X.Opens) [IsIntegral U.toScheme]
    [IsIntegral (f ⁻¹ᵁ U).toScheme] :
    ∃ W : U.toScheme.Opens, ((W : Set U) ∩ Set.range (f ∣_ U).base).Nonempty ∧
      IsFinite ((f ∣_ U) ∣_ W) := by
  set V : Y.Opens := f ⁻¹ᵁ U
  have hpre := preimage_genericPoint f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)
  have hηU : U.ι (genericPoint U) = genericPoint X :=
    Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion U.ι
  have hηV : V.ι (genericPoint V) = genericPoint Y :=
    Stacks.Intersection.RationalEquivalenceProduct.genericPoint_image_of_isOpenImmersion V.ι
  have hfη : f (genericPoint Y) = genericPoint X := (Set.ext_iff.1 hpre (genericPoint Y)).2 rfl
  have hmem : ∀ y : V.toScheme, (f ∣_ U) y = genericPoint U → V.ι y = genericPoint Y := by
    intro y hy
    have h : V.ι y ∈ f.base ⁻¹' {genericPoint X} := by
      change f (V.ι y) = genericPoint X
      rw [← ι_morphismRestrict_apply, hy, hηU]
    rwa [hpre] at h
  have hfin : ((f ∣_ U).base ⁻¹' {genericPoint U}).Finite :=
    Set.Subsingleton.finite fun y₁ hy₁ y₂ hy₂ =>
      V.ι.isOpenEmbedding.injective ((hmem y₁ hy₁).trans (hmem y₂ hy₂).symm)
  obtain ⟨W, hW, hfinW⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton (f ∣_ U) _ hfin
  refine ⟨W, ⟨genericPoint U, hW, genericPoint V, ?_⟩, hfinW⟩
  apply U.ι.isOpenEmbedding.injective
  rw [ι_morphismRestrict_apply, hηV, hfη, hηU]

/-- A curve on `f⁻¹ U` lying over a curve contracted by `f` is contracted by `f ∣_ U`. -/
theorem isContractedBy_morphismRestrict {f : Y ⟶ X} (U : X.Opens) {C : ProperCurve sY}
    (hC : C.IsContractedBy f) (CV : ProperCurve ((f ⁻¹ᵁ U).ι ≫ sY))
    (hCV : (f ⁻¹ᵁ U).ι CV.point = C.point) : CV.IsContractedBy (f ∣_ U) := by
  intro y hy
  apply U.ι.isOpenEmbedding.injective
  rw [ι_morphismRestrict_apply, ι_morphismRestrict_apply, hCV]
  refine hC _ (map_mem_closure (f ⁻¹ᵁ U).ι.continuous hy fun z hz => ?_)
  rw [Set.mem_singleton_iff.1 hz, hCV]
  rfl

/-- If a proper curve `C` has the generic point of a prime divisor `P`, its restriction to an
open `V` has the generic point of the restriction of `P`. -/
theorem point_eq_genericPoint_of_primeDivisorMap_eq (V : Y.Opens) {P : Mori.PrimeDivisor Y}
    {PV : Mori.PrimeDivisor V.toScheme} (hP : OpenWeilRestriction.primeDivisorMap V.ι PV = P)
    {C : ProperCurve sY} {CV : ProperCurve (V.ι ≫ sY)} (hCV : V.ι CV.point = C.point)
    (hC : C.point = P.genericPoint) : CV.point = PV.genericPoint := by
  apply V.ι.isOpenEmbedding.injective
  rw [hCV, hC, ← hP]
  exact OpenWeilRestriction.genericPoint_primeDivisorMap V.ι _

/-- **Negative definiteness of the exceptional curves.** Let `f : Y ⟶ X` be a proper birational
morphism from a smooth surface `Y` to a variety `X` (for instance a normal surface), and
`E₁, …, Eₙ` distinct proper curves on `Y` (prime divisors `Pᵢ` with proper curves `Cᵢ` having
the same generic points) whose images are points. Then the intersection matrix `((Eᵢ · Eⱼ))` is
negative definite. -/
@[mmp "lem_mmp_foundation_alg_closed_surface_exceptional_matrix"]
theorem posDef_neg_intersectionMatrix_of_isBirationalMorphism [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2)
    (hX : Mori.IsVariety k sX)
    {f : Y ⟶ X} (hfs : f ≫ sX = sY) [IsProper f] (hb : MMP.Mori.IsBirationalMorphism f)
    {n : ℕ} (P : Fin n → Mori.PrimeDivisor Y) (hP : Function.Injective P)
    (C : Fin n → ProperCurve sY) (hC : ∀ i, (C i).point = (P i).genericPoint)
    (hexc : ∀ i, (C i).IsContractedBy f) :
    (-(Matrix.of fun i j : Fin n =>
      ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sY (C j).ι
        (C j).dim_le (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (P i)) :
          ℝ))).PosDef := by
  classical
  refine posDef_neg_intersectionMatrix_of_forall_fibre hsm P C hC hexc fun x => ?_
  by_cases hS : IsEmpty {i // f (C i).point = x}
  · exact MMP.MatrixPosDef.posDef_of_isEmpty _
  obtain ⟨⟨i₀, hi₀⟩⟩ := not_isEmpty_iff.1 hS
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsAffine U := hU
  set V : Y.Opens := f ⁻¹ᵁ U
  have hsub : ∀ i : {i // f (C i).point = x}, closure ({(C i.1).point} : Set Y) ⊆ V :=
    fun i z hz => show f z ∈ U from (hexc i.1 z hz).trans i.2 ▸ hxU
  have : Nonempty V := ⟨⟨(C i₀).point, hsub ⟨i₀, hi₀⟩ (subset_closure rfl)⟩⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hYV := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sY V
  have hXU := Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k sX U
  have : IsNormal V.toScheme := isNormal_of_isOpenImmersion V.ι
  have : IsIntegral V.toScheme := hYV.toIsIntegral
  have : IsIntegral U.toScheme := hXU.toIsIntegral
  have hdimV : topologicalKrullDim V = 2 := by
    rw [Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sY V, hdim]
  have hfs' : (f ∣_ U) ≫ U.ι ≫ sX = V.ι ≫ sY := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hfs]
  let e : Fin (Fintype.card {i // f (C i).point = x}) ≃ {i // f (C i).point = x} :=
    (Fintype.equivFin _).symm
  choose PV hPV using fun i : {i // f (C i).point = x} =>
    exists_primeDivisorMap_eq V (P i.1) (hC i.1 ▸ hsub i (subset_closure rfl))
  choose CV hCV using fun i : {i // f (C i).point = x} =>
    exists_properCurve_of_closure_subset k V _ (hsub i)
  have hinj : Function.Injective fun j => PV (e j) := by
    intro a b hab
    have h := congrArg (OpenWeilRestriction.primeDivisorMap V.ι) hab
    simp only [hPV] at h
    exact e.injective (Subtype.ext (hP h))
  convert (posDef_neg_intersectionMatrix_of_isAffine (k := k) (sX := U.ι ≫ sX) hYV
    (isSmoothScheme_ι k hsm V) hdimV hXU hfs'
    (exists_isFinite_morphismRestrict_restrict_of_isBirationalMorphism hb U)
    (fun j => PV (e j)) hinj (fun j => CV (e j))
    (fun j => point_eq_genericPoint_of_primeDivisorMap_eq V (hPV (e j)) (hCV (e j)) (hC _))
    fun j => isContractedBy_morphismRestrict U (hexc _) _ (hCV (e j))).submatrix
    e.symm.injective using 1
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply, Matrix.of_apply]
  rw [intersectionNumber_restrict_open k hsm V (P (e a).1) (PV (e a)) (hPV (e a)) (C (e b).1)
    (CV (e b)) (hCV (e b)) (hsub (e b))]

/-- **Each contracted curve has negative self-intersection.** Under the hypotheses of
`MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism`,
`(Eᵢ · Eᵢ) < 0`. -/
@[mmp "lem_mmp_foundation_alg_closed_surface_exceptional_matrix"]
theorem intersectionNumber_self_neg_of_isBirationalMorphism [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2)
    (hX : Mori.IsVariety k sX)
    {f : Y ⟶ X} (hfs : f ≫ sX = sY) [IsProper f] (hb : MMP.Mori.IsBirationalMorphism f)
    (E : Mori.PrimeDivisor Y) (C : ProperCurve sY) (hC : C.point = E.genericPoint)
    (hexc : C.IsContractedBy f) :
    (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sY C.ι C.dim_le
      (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm E) < 0 := by
  have h := (posDef_neg_intersectionMatrix_of_isBirationalMorphism hY hsm hdim hX
    hfs hb (fun _ : Fin 1 => E) (fun a b _ => Subsingleton.elim a b) (fun _ => C)
    (fun _ => hC) fun _ => hexc).diag_pos (i := 0)
  simp only [Matrix.neg_apply, Matrix.of_apply, neg_pos] at h
  exact_mod_cast h

end MMP.Threefold.Resolution
