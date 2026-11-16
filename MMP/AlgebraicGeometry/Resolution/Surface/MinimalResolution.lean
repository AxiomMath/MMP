module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical

/-!
# Minimal resolutions of surfaces and surface germs

Let `k` be an algebraically closed field of arbitrary characteristic and `X` a normal surface
over `k`. A resolution `f : Y ⟶ X` (proper, birational, `Y` smooth) is *minimal* if no prime
divisor in its exceptional set is a smooth rational curve of self-intersection `-1`.

* Minimal resolutions exist and are isomorphisms over the smooth locus of `X`: among all
  resolutions take one with the fewest exceptional prime divisors, since a `(-1)`-curve could be
  contracted over `X` (Castelnuovo), lowering that number; over the smooth locus the resolution
  factors into point blowups, and the last of them would produce a `(-1)`-curve.
* A minimal resolution is dominated by every resolution, over `X` and over every open subset of
  `X`. Resolve the birational map `V ⇢ Y` by point blowups `Z ⟶ V`; the exceptional curve of the
  last blowup is contracted on `Y`, because otherwise its image would be an `f`-exceptional curve
  `C` with `C² = -1 + s`, `s ≥ 0`, and negativity of `C²` forces `C` to be a `(-1)`-curve. So the
  map descends one blowup at a time.

For a surface germ `(X, P)` (`X ∖ {P}` smooth), this gives the minimal resolution of the germ,
through which every resolution of a neighbourhood of `P` factors. As an application, if `(X, B)`
is log terminal near `P`, every entry of the log discrepancy vector of `(X, P; B)` on the minimal
resolution is positive: the birational transform of each exceptional curve on a log resolution
witnessing log terminality is exceptional, with the same valuation.

## Main results

* `MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq`: a resolution without
  contracted `(-1)`-curves is dominated, uniquely, by every resolution, over `X` and over every
  open `U ⊆ X`.
* `MMP.Mori.exists_isMinimalSurfaceResolution`: existence of minimal resolutions of normal
  surfaces, isomorphic over the smooth locus.
* `MMP.Flips.exists_isMinimalGermResolution`: every surface germ has a minimal resolution.
* `MMP.Flips.IsMinimalGermResolution.isMinimalSurfaceResolution`: a minimal resolution of a
  surface germ is a minimal resolution of the surface.
* `MMP.Flips.IsMinimalGermResolution.existsUnique_comp_eq`: every resolution of a neighbourhood
  of `P` factors uniquely through the minimal resolution of the germ.
* `MMP.Flips.IsGermLogDiscrepancyVector.pos_of_isLogTerminal`: log terminal germs have positive
  log discrepancy vectors.

## Implementation notes

Minimality (`MMP.Mori.IsMinimalSurfaceResolution`) forbids `(-1)`-curves among the prime divisors
contained in the exceptional set `MMP.Mori.exceptionalSet f`. A curve contracted by `f` lies in
the exceptional set, so this is at least as strong as forbidding contracted `(-1)`-curves. The
instance hypotheses that the minimality predicates need on the source are quantified as
propositions inside the existentials.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollar-mori], Chapter 4
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.0.2, 3.0.3,
  3.2.2
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

open Stacks.Intersection.RationalEquivalenceProduct (isVariety_opens_ι topologicalKrullDim_opens)

section Universal

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- For resolutions `f : Y ⟶ X` and `h : V ⟶ X` of a normal variety, there is an open `W` of `X`
over which `f` is an isomorphism and whose preimage under `h` is dense: the locus of finite
fibres of `f` contains the image of the generic point of `V`. -/
private theorem exists_isIso_morphismRestrict_dense_preimage (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) {V : Scheme.{u}}
    {h : V ⟶ X} (hh : IsSmoothResolution sX h) :
    ∃ W : X.Opens, IsIso (f ∣_ W) ∧ Dense ((h ⁻¹ᵁ W : V.Opens) : Set V) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsIntegral Y := hf.isIntegral
  have : IsIntegral V := hh.isIntegral
  have : IsProper f := hf.isProper
  have : IsProper h := hh.isProper
  have hbf := (hf.isNormalVariety hX).2.2
  have hbh := (hh.isNormalVariety hX).2.2
  obtain ⟨hW, hiso⟩ :=
    (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hbf).1 inferInstance
  set W : X.Opens := ⟨_, hW⟩
  have hgen : genericPoint V ∈ h ⁻¹ᵁ W := by
    show h (genericPoint V) ∈ W
    rw [map_genericPoint_eq h hbh, ← map_genericPoint_eq f hbf]
    exact map_genericPoint_mem_finiteFibreLocus f hbf
  have hdense : Dense ((h ⁻¹ᵁ W : V.Opens) : Set V) :=
    (h ⁻¹ᵁ W).isOpen.dense ⟨_, hgen⟩
  exact ⟨W, hiso, hdense⟩

/-- Factorizations through a resolution are unique. -/
private theorem eq_of_comp_eq (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hf : IsSmoothResolution sX f) {V : Scheme.{u}} {h : V ⟶ X}
    (hh : IsSmoothResolution sX h) {a₁ a₂ : V ⟶ Y} (e₁ : a₁ ≫ f = h) (e₂ : a₂ ≫ f = h) :
    a₁ = a₂ := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral V := hh.isIntegral
  have : IsProper f := hf.isProper
  obtain ⟨W, hiso, hdense⟩ := exists_isIso_morphismRestrict_dense_preimage sX hX hf hh
  have : IsDominant (h ⁻¹ᵁ W).ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have hle : ∀ {a : V ⟶ Y}, a ≫ f = h → h ⁻¹ᵁ W ≤ a ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rintro a rfl x hx
    exact hx
  refine ext_of_isDominant_of_isSeparated f (by rw [e₁, e₂]) (h ⁻¹ᵁ W).ι ?_
  rw [← Scheme.Hom.resLE_comp_ι a₁ (hle e₁), ← Scheme.Hom.resLE_comp_ι a₂ (hle e₂)]
  congr 1
  rw [← cancel_mono (f ∣_ W ≫ W.ι)]
  simp only [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, e₁, e₂]

/-- Over a nonempty open `U` of `X`, the restriction `f ∣_ U` of a resolution is a resolution
of `U`. -/
private theorem isSmoothResolution_morphismRestrict (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) (U : X.Opens)
    [Nonempty U] :
    IsSmoothResolution (U.ι ≫ sX) (f ∣_ U) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hf.isIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : Nonempty (f ⁻¹ᵁ U) := by
    have : IsDominant f := (hf.isNormalVariety hX).2.2.isDominant
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty U›
    obtain ⟨y, hy⟩ := f.denseRange.exists_mem_open U.isOpen ⟨x, hx⟩
    exact ⟨⟨y, hy⟩⟩
  refine ⟨IsZariskiLocalAtTarget.restrict hf.isProper U,
    isBirationalMorphism_morphismRestrict hf.isBirationalMorphism U, ?_⟩
  have : Smooth (f ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hf.isSmoothScheme
  rw [morphismRestrict_ι_assoc]
  exact (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance

/-- A point of `f ⁻¹ᵁ U` over the biregular locus of `f` lies over the biregular locus of
`f ∣_ U`. -/
private theorem mem_biregularLocus_morphismRestrict (f : Y ⟶ X) (U : X.Opens) (w : f ⁻¹ᵁ U)
    (hw : f w.1 ∈ biregularLocus f) : (f ∣_ U) w ∈ biregularLocus (f ∣_ U) := by
  have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ biregularLocus f) ≤ biregularLocus f := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
  have hB : IsBiregular f (U.ι ''ᵁ (U.ι ⁻¹ᵁ biregularLocus f)) :=
    isBiregular_iff_le_biregularLocus.mpr hle
  have : IsBiregular (f ∣_ U) (U.ι ⁻¹ᵁ biregularLocus f) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f U _)).mpr hB
  refine le_biregularLocus this ?_
  change (f ∣_ U ≫ U.ι) w ∈ biregularLocus f
  rw [morphismRestrict_ι]
  exact hw

section OpenCurves

open MMP.Threefold.Resolution Stacks.Intersection

/-- A prime divisor whose reduced subscheme is one-dimensional and proper over `k` is a proper
curve, at its generic point. -/
private theorem isProperCurve_genericPoint {W : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W]
    (s : W ⟶ Spec (.of k))
    (P : MMP.Mori.PrimeDivisor W) (hdim : topologicalKrullDim P.idealSheaf.subscheme = 1)
    [IsProper (P.idealSheaf.subschemeι ≫ s)] : IsProperCurve s P.genericPoint := by
  obtain ⟨e, he⟩ := exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf P)
  refine ⟨?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact hdim
  · change IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {P.genericPoint})).subschemeι ≫ s)
    rw [← he, Category.assoc]
    infer_instance

open MMP.Threefold.Mori in
/-- Intersection numbers of a prime divisor with a proper curve may be computed on an open
subscheme `j : Z ⟶ W` containing the curve: `(P · C_Z) = (j_* P · C)`. -/
private theorem intersectionNumber_single_primeDivisorMap {W Z : Scheme.{u}}
    {s : W ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian W] [IsNormal W]
    (hsm : IsSmoothScheme s) (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact (j ≫ s)]
    [IsLocallyNoetherian Z] [IsNormal Z] (hsmZ : IsSmoothScheme (j ≫ s))
    (P : MMP.Mori.PrimeDivisor Z) (CZ : ProperCurve (j ≫ s)) (C : ProperCurve s)
    (hC : j CZ.point = C.point) (hCZ : closure ({C.point} : Set W) ⊆ Set.range j) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (j ≫ s) CZ.ι CZ.dim_le
        (isQCartier_single_of_isSmoothScheme hsmZ P) =
      (Divisor.toQDivisor (Finsupp.single (OpenWeilRestriction.primeDivisorMap j P) 1)
        ).intersectionNumber k s C.ι C.dim_le (isQCartier_single_of_isSmoothScheme hsm _) := by
  set P' := OpenWeilRestriction.primeDivisorMap j P
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm P'
  have := isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsmZ P
  have hcomap : P'.idealSheaf.comap j = P.idealSheaf := by
    rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf,
      ← vanishingIdeal_closure_genericPoint_eq_idealSheaf P,
      show MMP.Mori.PrimeDivisor.genericPoint P' = j P.genericPoint from
        OpenWeilRestriction.genericPoint_primeDivisorMap j P]
    exact comap_vanishingIdeal_closure_singleton j _
  have : Stacks.Divisors.IsPullbackDefined j P'.idealSheaf := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (P'.idealSheaf.comap j)
    rw [hcomap]; infer_instance
  rw [intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsm P' C,
    intersectionNumber_single_eq_degreeOn_invertibleSheaf' k hsmZ P CZ]
  obtain ⟨e, he⟩ := exists_curveSubschemeAt_iso j CZ.point hC hCZ
  have : IsProper ((CZ.ι ≫ j) ≫ s) := by rw [Category.assoc]; infer_instance
  have h1 := degreeOn_eq_of_iso_comp k s C.ι (CZ.ι ≫ j) C.dim_le CZ.dim_le e.symm (by
    rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm)
    (Stacks.Divisors.invertibleSheaf' P'.idealSheaf : W.Modules)
  have h2 := degreeOn_comp k s j CZ.ι CZ.dim_le
    (Stacks.Divisors.invertibleSheaf' P'.idealSheaf : W.Modules)
  obtain ⟨e₂⟩ := nonempty_invertibleSheaf'_iso_of_eq hcomap
  haveI := MMP.Mori.isInvertible_pullback_obj j
    (Stacks.Divisors.invertibleSheaf' P'.idealSheaf : W.Modules)
  have h3 := MMP.Mori.degreeOn_eq_of_iso k (j ≫ s) CZ.ι CZ.dim_le
    (Stacks.Divisors.invertibleSheafPullbackIso j P'.idealSheaf ≪≫ e₂)
  refine congrArg (fun n : ℤ => (n : ℚ)) ?_
  exact (h1.trans (h2.trans h3)).symm

open MMP.Threefold.Mori in
/-- A smooth rational `(-1)`-curve `F` on an open subscheme `j : Z ⟶ Y`, lying over the
exceptional set of `f`, is the restriction of a smooth rational `f`-exceptional `(-1)`-curve
of `Y`: its closure `j(F)`. -/
private theorem exists_exceptional_minusOneCurve_of_isOpenImmersion (sX : X ⟶ Spec (.of k))
    (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (f ≫ sX)] (hsm : IsSmoothScheme (f ≫ sX)) {Z : Scheme.{u}} (j : Z ⟶ Y)
    [IsOpenImmersion j] (sZ : Z ⟶ Spec (.of k)) (hsZ : j ≫ f ≫ sX = sZ) [QuasiCompact sZ]
    [IsLocallyNoetherian Z] [IsNormal Z] (hsmZ : IsSmoothScheme sZ)
    (F : MMP.Mori.PrimeDivisor Z) (hF : IsSmoothRationalCurve sZ F.idealSheaf)
    (hnum : IsIntersectionNumber sZ (Finsupp.single F 1) F.idealSheaf (-1))
    (hexc : ∀ w ∈ (F.support : Set Z), j w ∈ (exceptionalSet f : Set Y)) :
    ∃ E : MMP.Mori.PrimeDivisor Y, E.support ⊆ (exceptionalSet f : Set Y) ∧
      IsSmoothRationalCurve (f ≫ sX) E.idealSheaf ∧
      IsIntersectionNumber (f ≫ sX) (Finsupp.single E 1) E.idealSheaf (-1) := by
  subst hsZ
  set E := OpenWeilRestriction.primeDivisorMap j F with hEdef
  set η := F.genericPoint with hηdef
  have hEη : E.genericPoint = j η := OpenWeilRestriction.genericPoint_primeDivisorMap j F
  obtain ⟨⟨-, hprop, -⟩, eF, heF⟩ := hF
  have hηF : η ∈ (F.support : Set Z) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have : IsProper (F.idealSheaf.subschemeι ≫ j) := by
    have : IsProper ((F.idealSheaf.subschemeι ≫ j) ≫ f ≫ sX) := by
      simpa only [Category.assoc] using hprop
    exact IsProper.of_comp _ (f ≫ sX)
  have hclosed : IsClosed (j.base '' (F.support : Set Z)) := by
    have h := (F.idealSheaf.subschemeι ≫ j).isClosedMap.isClosed_range
    convert h using 1
    show j.base '' (F.idealSheaf.support : Set Z) = _
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.range_comp]
    rfl
  have hEsupp : (E.support : Set Y) ⊆ j.base '' (F.support : Set Z) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hEη]
    exact closure_minimal (Set.singleton_subset_iff.2 ⟨η, hηF, rfl⟩) hclosed
  have hErange : closure ({E.genericPoint} : Set Y) ⊆ Set.range j := by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hEsupp.trans (Set.image_subset_range _ _)
  obtain ⟨e₁, he₁⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf F)
  obtain ⟨e₂, he₂⟩ := exists_curveSubschemeAt_iso j η hEη.symm hErange
  obtain ⟨e₃, he₃⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf E)
  let eE : F.idealSheaf.subscheme ≅ E.idealSheaf.subscheme := e₁.symm ≪≫ e₂ ≪≫ e₃
  have heE : eE.hom ≫ E.idealSheaf.subschemeι = F.idealSheaf.subschemeι ≫ j := by
    simp only [eE, Iso.trans_hom, Iso.symm_hom, Category.assoc, he₃, he₂]
    rw [← Category.assoc]
    congr 1
    exact (Iso.inv_comp_eq _).2 he₁.symm
  have hdimP : topologicalKrullDim (projectiveLine k) = 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq (projectiveLineIsoProj k).hom
      (projectiveLineIsoProj k).hom.homeomorph.isHomeomorph]
    exact topologicalKrullDim_projectiveLineProj k
  have hdimF : topologicalKrullDim F.idealSheaf.subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq eF.hom eF.hom.homeomorph.isHomeomorph]
    exact hdimP
  have hdimE : topologicalKrullDim E.idealSheaf.subscheme = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq eE.hom eE.hom.homeomorph.isHomeomorph]
    exact hdimF
  have hCE : IsCurveIn E.idealSheaf := ⟨E.integral, hdimE⟩
  have hpropE : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) := by
    have : E.idealSheaf.subschemeι = eE.inv ≫ F.idealSheaf.subschemeι ≫ j := by
      rw [← heE, Iso.inv_hom_id_assoc]
    rw [this]
    simp only [Category.assoc]
    infer_instance
  let eP := eF ≪≫ eE
  have heP : eP.hom ≫ E.idealSheaf.subschemeι ≫ f ≫ sX = projectiveLine k ↘ Spec (.of k) := by
    simp only [eP, Iso.trans_hom, Category.assoc, reassoc_of% heE]
    exact heF
  have hexcE : (E.support : Set Y) ⊆ (exceptionalSet f : Set Y) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hEsupp hz
    exact hexc w hw
  let CZ : ProperCurve (j ≫ f ≫ sX) := ⟨η, isProperCurve_genericPoint _ F hdimF⟩
  let CE : ProperCurve (f ≫ sX) := ⟨E.genericPoint, isProperCurve_genericPoint _ E hdimE⟩
  have hkey := intersectionNumber_single_primeDivisorMap hsm j hsmZ F CZ CE hEη.symm hErange
  have hFnum := isIntersectionNumber_of_properCurve _
    (isQCartier_single_of_isSmoothScheme hsmZ F) CZ F rfl
  have h1 : IsIntersectionNumber (j ≫ f ≫ sX) (Divisor.toQDivisor (Finsupp.single F 1))
      F.idealSheaf (-1) := by
    rw [toQDivisor_single, Int.cast_one]
    exact hnum
  have hval := hFnum.unique h1
  have hEnum := isIntersectionNumber_of_properCurve _
    (isQCartier_single_of_isSmoothScheme hsm E) CE E rfl
  rw [← hkey, hval, toQDivisor_single, Int.cast_one] at hEnum
  exact ⟨E, hexcE, ⟨⟨hCE, hpropE, eP.hom, heP, inferInstance, isBirationalMorphism_of_isIso _⟩,
    eP, heP⟩, hEnum⟩

end OpenCurves

section Chains

open MMP.Threefold.Resolution MMP.Threefold.Mori Stacks.ResolutionOfSurfaces

/-- Every scheme in a chain of point blowups of a smooth surface is a smooth surface. -/
private theorem pointBlowupChain_isSmoothSurface [IsAlgClosed k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} (hV : AlgebraicGeometry.IsVariety k sV) (hVs : IsSmoothScheme sV)
    (hVd : topologicalKrullDim V = 2) {T : Set V} {W : Scheme.{u}} {h : W ⟶ V}
    (hc : PointBlowupChain V T W h) :
    AlgebraicGeometry.IsVariety k (h ≫ sV) ∧ IsSmoothScheme (h ≫ sV) ∧
      topologicalKrullDim W = 2 ∧ IsProper h := by
  induction hc with
  | refl => simpa using ⟨hV, hVs, hVd, inferInstanceAs (IsProper (𝟙 V))⟩
  | @step W₀ h₀ hh w hw hwT ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have : IsIntegral W₀ := h1.toIsIntegral
    have : LocallyOfFiniteType (h₀ ≫ sV) := h1.toLocallyOfFiniteType
    have := (blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection
      h1 h2 h3 hw).2.1
    rw [Category.assoc]
    exact ⟨isVariety_blowUp_singleton h1 h3 hw, isSmoothScheme_blowUp_singleton h1 h2 h3 hw,
      topologicalKrullDim_blowUp _ _ (isSmoothBlowup_vanishingIdeal_singleton _ h2 hw)
        (isIrreducible_support_vanishingIdeal_singleton hw)
        (one_le_codimension_vanishingIdeal_singleton h3 hw) h3, inferInstance⟩

/-- Intersection numbers only depend on the structure morphism through its value. -/
private theorem isIntersectionNumber_congr {W : Scheme.{u}} {s s' : W ⟶ Spec (.of k)}
    [QuasiCompact s] [QuasiCompact s'] [IsLocallyNoetherian W] [IsNormal W] (hs : s = s')
    {D : QDivisor W} {C : W.IdealSheafData} {n : ℚ} (hn : IsIntersectionNumber s D C n) :
    IsIntersectionNumber s' D C n := by
  subst hs
  exact hn

/-- Equal points have isomorphic closures, over the ambient scheme. -/
private theorem exists_curveSubschemeAt_iso_of_eq {W : Scheme.{u}} {x x' : W} (h : x = x') :
    ∃ e : curveSubschemeAt x ≅ curveSubschemeAt x',
      e.hom ≫ curveSubschemeAtι x' = curveSubschemeAtι x := by
  subst h
  exact ⟨Iso.refl _, by simp⟩

/-- The image of a proper curve `C` under a morphism `f` into a separated `k`-scheme is a proper
curve when the image of the generic point of `C` is not closed. -/
private theorem isProperCurve_map_of_not_isClosed {W Y' : Scheme.{u}} {sY : Y' ⟶ Spec (.of k)}
    [IsSeparated sY] [LocallyOfFiniteType sY] (f : W ⟶ Y') (C : ProperCurve (f ≫ sY))
    (hcl : ¬ IsClosed ({f C.point} : Set Y')) : IsProperCurve sY (f C.point) := by
  have hP : IsProper ((C.ι ≫ f) ≫ sY) := by rw [Category.assoc]; infer_instance
  have hP' : IsProper (C.ι ≫ f) := IsProper.of_comp _ sY
  have hc : ¬ ∃ y, ∀ z, (C.ι ≫ f).base z = y := by
    rintro ⟨y, hy⟩
    apply hcl
    have hr := C.range_ι_comp f
    have hsub : closure ({f C.point} : Set Y') ⊆ {y} := by
      rw [← hr]
      rintro _ ⟨z, rfl⟩
      exact hy z
    have hfy : f C.point = y := hsub (subset_closure rfl)
    have : closure ({f C.point} : Set Y') = {f C.point} :=
      le_antisymm (hfy ▸ hsub) subset_closure
    rw [← this]
    exact isClosed_closure
  set x := C.point with hxdef
  let D := curveSubschemeAt (f.base x)
  let ιD : D ⟶ Y' := curveSubschemeAtι (f.base x)
  let h : C.scheme ⟶ D := Stacks.Chow.integralComponentMap f x
  have hh : h ≫ ιD = C.ι ≫ f := Stacks.Chow.integralComponentMap_subschemeι f x
  have : IsIntegral D := Stacks.Chow.isIntegral_integralComponentAt (f.base x)
  have : IsProper (h ≫ ιD) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h ιD
  have hrangeD : Set.range ιD.base = closure ({f.base x} : Set Y') := by
    change Set.range (curveSubschemeAtι (f.base x)).base = _
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hsurj : Function.Surjective h.base := by
    intro d
    have hd : ιD.base d ∈ Set.range (C.ι ≫ f).base := by
      rw [C.range_ι_comp f, ← hrangeD]; exact ⟨d, rfl⟩
    obtain ⟨c, hc⟩ := hd
    refine ⟨c, ιD.isClosedEmbedding.injective ?_⟩
    rw [← hc, ← Scheme.Hom.comp_apply, hh]
  have : Surjective h := ⟨hsurj⟩
  have : UniversallyClosed (h ≫ ιD ≫ sY) := by
    rw [← Category.assoc, hh, Category.assoc]; infer_instance
  have : UniversallyClosed (ιD ≫ sY) := UniversallyClosed.of_comp_surjective h _
  have : IsProper (ιD ≫ sY) := ⟨⟩
  have hnc : ¬ ∃ y : D, ∀ z, h.base z = y := by
    rintro ⟨y, hy⟩
    exact hc ⟨ιD.base y, fun z => by rw [← hh, Scheme.Hom.comp_apply, hy]⟩
  have hdimD : topologicalKrullDim D = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← C.dim_eq]
      exact topologicalKrullDim_le_of_surjective_of_isClosedMap h hsurj h.isClosedMap
    · refine Stacks.Curves.StableModel.one_le_topologicalKrullDim_of_not_subsingleton D ?_
      intro hsub
      exact hnc ⟨h.base (Classical.arbitrary _), fun z => Subsingleton.elim _ _⟩
  exact ⟨hdimD, inferInstance⟩

/-- **The self-intersection of a strict transform under one point blowup.** Let `W` be a smooth
surface over an algebraically closed field, `b : W' ⟶ W` the blowup of a closed point `w` and
`P` a prime divisor of `W'` with `b(P) ≠ w`, with image the prime divisor `D` of `W` (the
closure of `b(η_P)`). Then `D² = P² + m²` with `m = mult_w D`, and if `m = 0`, `P ≅ D` over `W`.
Indeed `b^*D = P + m F`, `(b^*D · P) = (D · D)` and `(b^*D · F) = 0`, with `F² = -1`. -/
private theorem exists_isIntersectionNumber_blowUp_singleton [IsAlgClosed k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} (hW : AlgebraicGeometry.IsVariety k sW) (hWs : IsSmoothScheme sW)
    (hWd : topologicalKrullDim W = 2) {w : W} (hw : IsClosed ({w} : Set W))
    [IsLocallyNoetherian W] [IsNormal W] [QuasiCompact sW]
    [IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))]
    [IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))]
    [QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ sW)]
    (P : MMP.Mori.PrimeDivisor (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)))
    (hP : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) P.genericPoint ≠ w)
    {n : ℚ} (hn : IsIntersectionNumber
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ sW)
      (Finsupp.single P 1) P.idealSheaf n) :
    ∃ (hc : Order.coheight
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) P.genericPoint) = 1)
      (m : ℕ),
      IsIntersectionNumber sW (Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc) 1)
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc).idealSheaf (n + (m : ℚ) ^ 2) ∧
      (m = 0 → ∃ e : curveSubschemeAt P.genericPoint ≅ curveSubschemeAt
          (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) P.genericPoint),
        e.hom ≫ curveSubschemeAtι _ = curveSubschemeAtι P.genericPoint ≫
          blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) := by
  classical
  set b := blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds W))
    with hbdef
  have hW's := isSmoothScheme_blowUp_singleton hW hWs hWd hw
  have hW'v := isVariety_blowUp_singleton hW hWd hw
  have : IsIntegral W := hW.toIsIntegral
  have : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have : IsSeparated sW := hW.toIsSeparated
  have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal
    (⟨{w}, hw⟩ : TopologicalSpace.Closeds W))) := hW'v.toIsIntegral
  have hW'd : topologicalKrullDim (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : TopologicalSpace.Closeds W))) = 2 :=
    topologicalKrullDim_blowUp _ _ (isSmoothBlowup_vanishingIdeal_singleton _ hWs hw)
      (isIrreducible_support_vanishingIdeal_singleton hw)
      (one_le_codimension_vanishingIdeal_singleton hWd hw) hWd
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have := compactSpace_blowUp_singleton hW hWd hw
  have hreg : b P.genericPoint ∈ biregularLocus b := mem_biregularLocus_blowUpToBase_singleton hw hP
  have hc : Order.coheight (b P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus b hreg]
    exact P.coheight_genericPoint
  refine ⟨hc, ?_⟩
  set D : MMP.Mori.PrimeDivisor W := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc with hDdef
  have hDξ : D.genericPoint = b P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  obtain ⟨-, -, -, hiso, E, hE, -, hEprop, hEnum⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hW hWs hWd hw
  have hit : inverseTransformPrimeDivisor b D = some P :=
    inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hDξ.symm hreg
  have hpull := pullback_single_blowUp_singleton hW hWs hWd hw hE D
  rw [inverseTransformDivisor_single, hit] at hpull
  set m := (D.multiplicityAt w).toNat with hm
  -- the three curves
  have hPprop : IsProper (P.idealSheaf.subschemeι ≫ b ≫ sW) := hn.1
  have hPdim : topologicalKrullDim P.idealSheaf.subscheme = 1 :=
    (MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hW'v hW'd P).2
  let CP : ProperCurve (b ≫ sW) := ⟨P.genericPoint, isProperCurve_genericPoint _ P hPdim⟩
  let CE : ProperCurve (b ≫ sW) := ⟨E.genericPoint, hEprop⟩
  have hbcl : ¬ IsClosed ({b CP.point} : Set W) := by
    intro h
    have h2 := coheight_eq_two_of_isClosed hW hWd h
    change Order.coheight (b P.genericPoint) = 2 at h2
    rw [hc] at h2
    exact absurd h2 (by decide)
  have hprop : IsProperCurve sW (b CP.point) := isProperCurve_map_of_not_isClosed b CP hbcl
  let CD : ProperCurve sW := ⟨b P.genericPoint, hprop⟩
  haveI : IsProper (CD.ι ≫ sW) := CD.isProper_ι_comp
  haveI : IsProper (CE.ι ≫ b ≫ sW) := CE.isProper_ι_comp
  haveI : IsProper (CP.ι ≫ b ≫ sW) := CP.isProper_ι_comp
  -- the projection formula
  have hD := isCartier_single_of_isSmoothScheme hWs D
  have hB := blowUpToBase_componentGenericPoint_notMem_supp hW hWd hw
    (Finsupp.single D 1 : MMP.Mori.Divisor W)
  have hproj := Divisor.degreeOn_pullback_eq_degree_pushforward (sY := sW) (sX := b ≫ sW) b rfl
    hD hB CP
  have hres : residueFieldDegree b CP.point = 1 :=
    MMP.Flips.residueFieldDegree_eq_one_of_isIso_stalkMap _ _
      (isIso_stalkMap_of_mem_biregularLocus b hreg)
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint] at hproj
  simp only [hprop, ↓reduceDIte] at hproj
  rw [hres, OneCycle.degree_apply, Finsupp.sum_single_index (by simp), Nat.cast_one,
    one_mul] at hproj
  set x : ℚ := (Divisor.degreeOn k sW CD.ι CD.dim_le (Finsupp.single D 1) hD : ℚ)
    with hxdef
  have I0 : IsIntersectionNumber sW (Divisor.toQDivisor (Finsupp.single D 1)) D.idealSheaf x := by
    have h := isIntersectionNumber_of_properCurve
      (Divisor.toQDivisor (Finsupp.single D 1 : MMP.Mori.Divisor W))
      (QDivisor.isQCartier_toQDivisor hD) CD D hDξ.symm
    rwa [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD] at h
  have hD' := hD.isCartier_pullback b hB
  have I1 : IsIntersectionNumber (b ≫ sW) (Divisor.toQDivisor (Divisor.pullback
      (Finsupp.single D 1 : MMP.Mori.Divisor W) hD hB)) P.idealSheaf x := by
    have h := isIntersectionNumber_of_properCurve
      (Divisor.toQDivisor (Divisor.pullback (Finsupp.single D 1 : MMP.Mori.Divisor W) hD hB))
      (QDivisor.isQCartier_toQDivisor hD') CP P rfl
    rwa [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', hproj] at h
  have hFmem := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hw hE
  have hcon : CE.IsContractedBy b := by
    intro q hq
    change q ∈ closure ({E.genericPoint} : Set _) at hq
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hq
    rw [(hFmem q).mp hq, (hFmem _).mp (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)]
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy (sY := sW) (sX := b ≫ sW) b rfl
    hD hB CE hcon
  have I2 : IsIntersectionNumber (b ≫ sW) (Divisor.toQDivisor (Divisor.pullback
      (Finsupp.single D 1 : MMP.Mori.Divisor W) hD hB)) E.idealSheaf 0 := by
    have h := isIntersectionNumber_of_properCurve
      (Divisor.toQDivisor (Divisor.pullback (Finsupp.single D 1 : MMP.Mori.Divisor W) hD hB))
      (QDivisor.isQCartier_toQDivisor hD') CE E rfl
    rwa [QDivisor.intersectionNumber_toQDivisor k _ _ _ _ hD', h0, Int.cast_zero] at h
  have hpullQ : Divisor.toQDivisor (Divisor.pullback (Finsupp.single D 1 : MMP.Mori.Divisor W)
      hD hB) = Finsupp.single P 1 + (m : ℚ) • Finsupp.single E 1 := by
    rw [hpull, map_add, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp [toQDivisor_single]
  rw [hpullQ] at I1 I2
  have hQP := isQCartier_single_of_isSmoothScheme hW's P
  have hQE := isQCartier_single_of_isSmoothScheme hW's E
  have I3 : IsIntersectionNumber (b ≫ sW) (Finsupp.single E 1) E.idealSheaf (-1) := by
    have h := isIntersectionNumber_of_properCurve _ hQE CE E rfl
    rwa [hEnum CE rfl, toQDivisor_single, Int.cast_one] at h
  set y := (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k (b ≫ sW) CE.ι
    CE.dim_le hQP with hydef
  have I4 : IsIntersectionNumber (b ≫ sW) (Finsupp.single P 1) E.idealSheaf y := by
    have h := isIntersectionNumber_of_properCurve _ hQP CE E rfl
    change IsIntersectionNumber _ _ _ y at h
    rwa [toQDivisor_single, Int.cast_one] at h
  have I5 : IsIntersectionNumber (b ≫ sW) (Finsupp.single E 1) P.idealSheaf y := by
    have h := isIntersectionNumber_of_properCurve _ hQE CP P rfl
    rw [intersectionNumber_single_comm hW's P E CP CE rfl rfl] at h
    change IsIntersectionNumber _ _ _ y at h
    rwa [toQDivisor_single, Int.cast_one] at h
  have J2 := MMP.Flips.isIntersectionNumber_add I4
    (I3.smul (m : ℚ) (MMP.Fourfold.isQCartier_of_isSmoothScheme hW's _))
  have hy : y + (m : ℚ) * (-1) = 0 := J2.unique I2
  have J1 := MMP.Flips.isIntersectionNumber_add hn
    (I5.smul (m : ℚ) (MMP.Fourfold.isQCartier_of_isSmoothScheme hW's _))
  have hx : n + (m : ℚ) * y = x := J1.unique I1
  refine ⟨m, ?_, ?_⟩
  · have hx' : x = n + (m : ℚ) ^ 2 := by
      have : y = m := by linarith
      rw [← hx, this]; ring
    rw [← hx']
    rwa [toQDivisor_single, Int.cast_one] at I0
  · intro hm0
    have hwD : w ∉ (D.support : Set W) := by
      intro hwD
      have h1 : (1 : ℕ∞) ≤ D.multiplicityAt w := by
        refine le_iSup₂_of_le 1 ?_ (by simp)
        rw [pow_one]
        exact D.idealSheaf.stalkIdeal_le_maximalIdeal_of_mem_support hwD
      have hne := multiplicityAt_ne_top D
        (isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hWs D) w
      have : 1 ≤ m := by simpa [hm] using ENat.toNat_le_toNat h1 hne
      omega
    set U : W.Opens := ⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩ with hU
    haveI : IsIso (b ∣_ U) := hiso
    have hclD : closure ({b P.genericPoint} : Set W) ⊆ (U : Set W) := by
      intro z hz hzw
      apply hwD
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        show AlgebraicGeometry.PrimeDivisor.genericPoint D = b P.genericPoint from hDξ]
      rwa [Set.mem_singleton_iff.mp hzw] at hz
    let u : U.toScheme := ⟨b P.genericPoint, hP⟩
    obtain ⟨e₁, he₁⟩ := exists_curveSubschemeAt_iso U.ι u (y := b P.genericPoint) rfl
      (by rwa [Scheme.Opens.range_ι])
    let j : U.toScheme ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : TopologicalSpace.Closeds W)) := inv (b ∣_ U) ≫ (b ⁻¹ᵁ U).ι
    have hjb : j ≫ b = U.ι := by
      simp only [j, Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    have hinv : ∀ q : (b ⁻¹ᵁ U).toScheme, j ((b ∣_ U) q) = q.1 := by
      intro q
      show (inv (b ∣_ U) ≫ (b ⁻¹ᵁ U).ι) ((b ∣_ U) q) = q.1
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id_assoc]
      rfl
    let q₀ : (b ⁻¹ᵁ U).toScheme := ⟨P.genericPoint, hP⟩
    have hju : j u = P.genericPoint := by
      have hp : (b ∣_ U) q₀ = u :=
        Subtype.ext (morphismRestrict_base_coe b U _)
      rw [← hp, hinv]
    have hcl : closure ({P.genericPoint} : Set _) ⊆ Set.range j := by
      intro z hz
      have hbz : b z ∈ closure ({b P.genericPoint} : Set W) := by
        have := image_closure_subset_closure_image (s := ({P.genericPoint} : Set _))
          b.continuous ⟨z, hz, rfl⟩
        simpa using this
      have hzU : z ∈ b ⁻¹ᵁ U := hclD hbz
      exact ⟨(b ∣_ U) (⟨z, hzU⟩ : (b ⁻¹ᵁ U).toScheme), hinv _⟩
    obtain ⟨e₂, he₂⟩ := exists_curveSubschemeAt_iso j u hju hcl
    refine ⟨e₂.symm ≪≫ e₁, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he₁, ← hjb,
      ← Category.assoc (curveSubschemeAtι u) j b, ← he₂, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- **Self-intersections of strict transforms along a chain of point blowups.** Let `c : W ⟶ V` be
a chain of point blowups of a smooth surface `V` and `P` a prime divisor of `W` not contracted by
`c`, with image the prime divisor `Q` of `V`. Then `Q² = P² + s` for some `s ∈ ℕ` (the sum of the
squared multiplicities of the successive images at the centres), and if `s = 0`, `P ≅ Q` over
`V`. -/
private theorem exists_isIntersectionNumber_pointBlowupChain [IsAlgClosed k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} (hV : AlgebraicGeometry.IsVariety k sV) (hVs : IsSmoothScheme sV)
    (hVd : topologicalKrullDim V = 2) [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    {T : Set V} {W : Scheme.{u}} {c : W ⟶ V} (hc : PointBlowupChain V T W c) :
    ∀ [IsLocallyNoetherian W] [IsNormal W] [QuasiCompact (c ≫ sV)]
      (P : MMP.Mori.PrimeDivisor W) (hP : Order.coheight (c P.genericPoint) = 1) {n : ℚ},
      IsIntersectionNumber (c ≫ sV) (Finsupp.single P 1) P.idealSheaf n →
      ∃ s : ℕ, IsIntersectionNumber sV
          (Finsupp.single (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP) 1)
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP).idealSheaf (n + s) ∧
        (s = 0 → ∃ e : curveSubschemeAt P.genericPoint ≅ curveSubschemeAt (c P.genericPoint),
          e.hom ≫ curveSubschemeAtι _ = curveSubschemeAtι P.genericPoint ≫ c) := by
  induction hc with
  | refl =>
    intro _ _ _ P hP n hn
    refine ⟨0, ?_, fun _ => ?_⟩
    · have hQ : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP = P :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
          rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; rfl)
      rw [hQ, Nat.cast_zero, add_zero]
      exact isIntersectionNumber_congr (Category.id_comp sV) hn
    · obtain ⟨e, he⟩ := exists_curveSubschemeAt_iso_of_eq (x := P.genericPoint)
        (x' := (𝟙 V : V ⟶ V) P.genericPoint) rfl
      exact ⟨e, by rw [he, Category.comp_id]⟩
  | @step W₀ c₀ hh w hw hwT ih =>
    intro _ _ _ P hP n hn
    obtain ⟨h1, h2, h3, h4⟩ := pointBlowupChain_isSmoothSurface hV hVs hVd hh
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme h2).1
    haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme h2).2
    haveI : QuasiCompact (c₀ ≫ sV) := h1.toQuasiCompact
    haveI : QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds W₀)) ≫ c₀ ≫ sV) :=
      (isVariety_blowUp_singleton h1 h3 hw).toQuasiCompact
    set b := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : TopologicalSpace.Closeds W₀)) with hbdef
    have hbw : b P.genericPoint ≠ w := by
      intro hbw
      have hcl : IsClosed ({c₀ w} : Set V) := by
        have : IsClosed (c₀ '' {w}) := c₀.isClosedMap _ hw
        rwa [Set.image_singleton] at this
      have h2' := coheight_eq_two_of_isClosed hV hVd hcl
      have : (b ≫ c₀) P.genericPoint = c₀ w := by rw [Scheme.Hom.comp_apply, hbw]
      rw [this, h2'] at hP
      exact absurd hP (by decide)
    have hn' : IsIntersectionNumber (b ≫ c₀ ≫ sV) (Finsupp.single P 1) P.idealSheaf n :=
      isIntersectionNumber_congr (Category.assoc _ _ _) hn
    obtain ⟨hc₁, m, hD, hiso⟩ := exists_isIntersectionNumber_blowUp_singleton h1 h2 h3 hw P hbw hn'
    set P₀ : MMP.Mori.PrimeDivisor W₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc₁
      with hP₀def
    have hP₀ξ : P₀.genericPoint = b P.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hP₀ : Order.coheight (c₀ P₀.genericPoint) = 1 := by
      rwa [hP₀ξ, ← Scheme.Hom.comp_apply]
    obtain ⟨s₀, hs₀, hiso₀⟩ := ih P₀ hP₀ hD
    have hQ : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP₀ =
        AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
        rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hP₀ξ,
          Scheme.Hom.comp_apply])
    refine ⟨m ^ 2 + s₀, ?_, fun hs => ?_⟩
    · rw [← hQ]
      convert hs₀ using 1
      push_cast
      ring
    · have hm2 : m ^ 2 = 0 := (Nat.add_eq_zero_iff.mp hs).1
      have hm : m = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hm2
      obtain ⟨e₁, he₁⟩ := hiso hm
      obtain ⟨e₀, he₀⟩ := hiso₀ (Nat.add_eq_zero_iff.mp hs).2
      obtain ⟨ea, hea⟩ := exists_curveSubschemeAt_iso_of_eq hP₀ξ.symm
      obtain ⟨eb, heb⟩ := exists_curveSubschemeAt_iso_of_eq
        (show c₀ P₀.genericPoint = (b ≫ c₀) P.genericPoint by
          rw [hP₀ξ, Scheme.Hom.comp_apply])
      refine ⟨e₁ ≪≫ ea ≪≫ e₀ ≪≫ eb, ?_⟩
      rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
        Category.assoc, heb, he₀, ← Category.assoc ea.hom, hea, ← Category.assoc e₁.hom, he₁,
        Category.assoc]

open Stacks.AlgebraicGeometry.ProjPolyChart in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- `ℙ¹_k`, glued from two affine lines, is `ℙ^{ULift (Fin 2)}_k` over `k`. -/
private theorem exists_iso_projSpace_projectiveLine :
    ∃ e : projectiveLine k ≅ MMP.Intersection.ProjSpace k (ULift.{u} (Fin 2)),
      e.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ = projectiveLine k ↘ Spec (.of k) := by
  refine ⟨projectiveLineIsoProj k ≪≫ (MMP.Intersection.ProjSpace.isoPolyGrading k 1).symm, ?_⟩
  have h : (MMP.Intersection.ProjSpace.isoPolyGrading k 1).hom ≫
      projToSpecCoeff k 1 =
        MMP.Intersection.ProjSpace.toSpec k _ := by
    rw [MMP.Intersection.ProjSpace.isoPolyGrading_hom,
      projToSpecCoeff, Proj.map_toSpecZero_assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, MMP.Intersection.ProjSpace.toSpec]
    congr 3
    refine RingHom.ext fun a => Subtype.ext ?_
    have hC : MvPolynomial.C a ∈ polyGrading k 1 0 :=
      MvPolynomial.isHomogeneous_C _ a
    have h0 := GradedRing.projZeroRingHom'_apply_coe (polyGrading k 1) ⟨_, hC⟩
    change MvPolynomial.rename ULift.up ((GradedRing.projZeroRingHom' (polyGrading k 1)
      (MvPolynomial.C a) : polyGrading k 1 0) : MvPolynomial (Fin (1 + 1)) k) = MvPolynomial.C a
    rw [h0, MvPolynomial.rename_C]
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← h, Iso.inv_hom_id_assoc,
    projectiveLineIsoProj_hom_comp_projToSpecCoeff]

/-- **The exceptional curve of the last blowup is contracted.** Let `f : Y ⟶ X` be a resolution
of a normal surface with no `f`-exceptional `(-1)`-curve, `q₀ : Z₀ ⟶ X` a proper birational
morphism from a smooth surface, `b : Z ⟶ Z₀` the blowup of a closed point `w` with exceptional
curve `F`, and `g : Z ⟶ Y` with `g ≫ f = b ≫ q₀`. Then `g` maps `F` to a point. Otherwise
`C = g(F)` is an `f`-exceptional curve; factoring `g` into point blowups,
`C² = F² + s = -1 + s` with `s ≥ 0`, and `C² < 0` forces `s = 0`, so `C ≅ F ≅ ℙ¹` would be an
`f`-exceptional `(-1)`-curve. -/
private theorem exists_const_of_isMinimalSurfaceResolution [IsAlgClosed k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) {Z₀ : Scheme.{u}} {s₀ : Z₀ ⟶ Spec (.of k)}
    (hZ₀ : AlgebraicGeometry.IsVariety k s₀) (hZ₀s : IsSmoothScheme s₀)
    (hZ₀d : topologicalKrullDim Z₀ = 2) (q₀ : Z₀ ⟶ X) (hq₀ : q₀ ≫ sX = s₀) [IsProper q₀]
    (hq₀b : IsBirational q₀) {w : Z₀} (hw : IsClosed ({w} : Set Z₀))
    (g : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ⟶ Y)
    (hg : g ≫ f = blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ q₀) :
    ∃ y : Y, ∀ z : (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).subscheme,
      g ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)).subschemeι z) =
        y := by
  classical
  by_contra hnc
  set b := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
    (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀)) with hbdef
  -- the target `X` and the resolution `Y`
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsIntegral Z₀ := hZ₀.toIsIntegral
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨hYn, hYd, hfb⟩ := hf.1.isNormalVariety hX
  rw [hdim] at hYd
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hYn.1
  have hYs : IsSmoothScheme (f ≫ sX) := hf.1.isSmoothScheme
  have : IsProper f := hf.1.isProper
  have : IsIntegral Y := hYv.toIsIntegral
  have : IsSeparated (f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  -- the blowup `Z`
  obtain ⟨-, hbprop, hbbir, -, E, hE, ⟨eP, heP⟩, hEprop, hEnum⟩ :=
    blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection hZ₀ hZ₀s hZ₀d hw
  have hZv := isVariety_blowUp_singleton hZ₀ hZ₀d hw
  have hZs := isSmoothScheme_blowUp_singleton hZ₀ hZ₀s hZ₀d hw
  have hZd : topologicalKrullDim
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀))) =
        2 :=
    topologicalKrullDim_blowUp _ _ (isSmoothBlowup_vanishingIdeal_singleton _ hZ₀s hw)
      (isIrreducible_support_vanishingIdeal_singleton hw)
      (one_le_codimension_vanishingIdeal_singleton hZ₀d hw) hZ₀d
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hZs).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hZs).2
  haveI : QuasiCompact (b ≫ s₀) := hZv.toQuasiCompact
  have : IsIntegral (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀))) := hZv.toIsIntegral
  have hgs : g ≫ f ≫ sX = b ≫ s₀ := by rw [← Category.assoc, hg, Category.assoc, hq₀]
  -- the generic point `ξ` of `F` and its image `c`
  set ξ := E.genericPoint with hξdef
  have hsuppE := mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hw hE
  have hξE : ξ ∈ (E.support : Set _) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hnc' : ¬ ∃ y, ∀ z ∈ (E.support : Set _), g z = y := by
    rintro ⟨y, hy⟩
    refine hnc ⟨y, fun z => hy _ ?_⟩
    have hsupp : ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀))).support : Set _) = (E.support : Set _) := by
      rw [← hE]
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  set c := g ξ with hcdef
  have hcncl : ¬ IsClosed ({c} : Set Y) := by
    intro hcl
    refine hnc' ⟨c, fun z hz => ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
    have := image_closure_subset_closure_image (s := ({ξ} : Set _)) g.continuous
      ⟨z, hz, rfl⟩
    rwa [Set.image_singleton, hcl.closure_eq] at this
  have hEprop' : IsProperCurve (g ≫ f ≫ sX) ξ := hgs ▸ hEprop
  let CE : ProperCurve (g ≫ f ≫ sX) := ⟨ξ, hEprop'⟩
  haveI : IsProper (CE.ι ≫ g ≫ f ≫ sX) := CE.isProper_ι_comp
  have hCprop : IsProperCurve (f ≫ sX) c := isProperCurve_map_of_not_isClosed g CE hcncl
  have hcoh : Order.coheight c = 1 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX) c
    have hd : topologicalKrullDim (closure ({c} : Set Y)) = 1 := by
      have h1 := hCprop.dim_eq
      change topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({c} : Set Y))).subscheme = 1 at h1
      rwa [MMP.Flips.topologicalKrullDim_subscheme,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
    rw [hd, hYd] at h
    generalize Order.coheight c = d at h ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : ((1 + d : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by push_cast; exact h
      have := Nat.cast_injective (R := WithBot ℕ∞) h'
      have : d = 1 := by omega
      subst this
      rfl
  set Q : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh
    with hQdef
  have hQξ : Q.genericPoint = c := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hQξ' : AlgebraicGeometry.PrimeDivisor.genericPoint Q = c := hQξ
  -- `f` contracts `Q` to the closed point `x₀ = q₀ w`
  have hfc : f c = q₀ w := by
    rw [hcdef, ← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply, (hsuppE ξ).mp hξE]
  have hx₀cl : IsClosed ({q₀ w} : Set X) := by
    have := q₀.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  have hfQ : ∀ y ∈ closure ({c} : Set Y), f y = q₀ w := by
    intro y hy
    have := image_closure_subset_closure_image (s := ({c} : Set Y)) f.continuous ⟨y, hy, rfl⟩
    rwa [Set.image_singleton, hfc, hx₀cl.closure_eq] at this
  let CQ : ProperCurve (f ≫ sX) := ⟨c, hCprop⟩
  haveI : IsProper (CQ.ι ≫ f ≫ sX) := CQ.isProper_ι_comp
  have hCQcon : CQ.IsContractedBy f := fun y hy => by
    rw [hfQ y hy, hfQ c (subset_closure rfl)]
  have hneg := intersectionNumber_self_neg_of_isBirationalMorphism hYv hYs hYd hXv rfl
    hf.1.isBirationalMorphism Q CQ hQξ.symm hCQcon
  -- `Q` lies in the exceptional set of `f`
  have hQexc : (Q.support : Set Y) ⊆ (exceptionalSet f : Set Y) := by
    intro y hy hybir
    have hyc : y ∈ closure ({c} : Set Y) := by
      rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hQξ'] at hy
    have hbir : f c ∈ biregularLocus f := by
      have : f y ∈ biregularLocus f := hybir
      rwa [hfQ y hyc, ← hfc] at this
    obtain ⟨q, hq, hqcl⟩ := IsClosed.exists_closed_singleton isClosed_closure
      ⟨c, subset_closure (Set.mem_singleton c)⟩
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus f hbir
    have h2 := MMP.Positivity.coheight_map_of_mem_biregularLocus f
      (show f q ∈ biregularLocus f by rwa [hfQ q hq, ← hfc])
    rw [hfQ q hq, ← hfc, h1, hcoh, coheight_eq_two_of_isClosed hYv hYd hqcl] at h2
    exact absurd h2 (by decide)
  -- factor `g` into point blowups
  have hgb : IsBirational g := by
    refine isBirational_of_comp_of_isBirational g f ?_ hfb ?_
    · rw [hg]
      exact (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbbir).comp hq₀b
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      exact preimage_genericPoint f hfb
  have : IsProper g := by
    have : IsProper (g ≫ f) := by rw [hg]; infer_instance
    exact IsProper.of_comp g f
  have hZv' : AlgebraicGeometry.IsVariety k (g ≫ f ≫ sX) := hgs ▸ hZv
  have hZs' : IsSmoothScheme (g ≫ f ≫ sX) := hgs ▸ hZs
  obtain ⟨Ym, cY, hchain, eY, heY⟩ :=
    MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface k hYv hYs hYd hZv' hZs' hZd
      g rfl hgb
  obtain ⟨hYmv, hYms, hYmd, hcYp⟩ := pointBlowupChain_isSmoothSurface hYv hYs hYd hchain
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYms).1
  haveI := (isLocallyNoetherian_and_isNormal_of_isSmoothScheme hYms).2
  haveI : QuasiCompact (cY ≫ f ≫ sX) := hYmv.toQuasiCompact
  have hs' : eY.hom ≫ cY ≫ f ≫ sX = b ≫ s₀ := by rw [← Category.assoc, heY, hgs]
  haveI : QuasiCompact (eY.hom ≫ cY ≫ f ≫ sX) := by rw [hs']; infer_instance
  have hZs'' : IsSmoothScheme (eY.hom ≫ cY ≫ f ≫ sX) := hs' ▸ hZs
  -- the exceptional curve on `Ym`
  set F' := OpenWeilRestriction.primeDivisorMap eY.hom E with hF'def
  have hF'ξ : F'.genericPoint = eY.hom ξ := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  let CZ : ProperCurve (eY.hom ≫ cY ≫ f ≫ sX) := ⟨ξ, hs' ▸ hEprop⟩
  haveI : IsProper (CZ.ι ≫ eY.hom ≫ cY ≫ f ≫ sX) := CZ.isProper_ι_comp
  have hncl : ¬ IsClosed ({eY.hom CZ.point} : Set Ym) := by
    intro hcl
    apply hcncl
    have := cY.isClosedMap _ hcl
    rwa [Set.image_singleton, ← Scheme.Hom.comp_apply, heY] at this
  let CF : ProperCurve (cY ≫ f ≫ sX) :=
    ⟨eY.hom ξ, isProperCurve_map_of_not_isClosed eY.hom CZ hncl⟩
  haveI : IsProper (CF.ι ≫ cY ≫ f ≫ sX) := CF.isProper_ι_comp
  have hrange : closure ({CF.point} : Set Ym) ⊆ Set.range eY.hom := by
    intro z _
    refine ⟨eY.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hkey := intersectionNumber_single_primeDivisorMap hYms eY.hom hZs'' E CZ CF rfl hrange
  have hE1 : IsIntersectionNumber (b ≫ s₀) (Finsupp.single E 1) E.idealSheaf (-1) := by
    let CE₀ : ProperCurve (b ≫ s₀) := ⟨ξ, hEprop⟩
    haveI : IsProper (CE₀.ι ≫ b ≫ s₀) := CE₀.isProper_ι_comp
    have h := isIntersectionNumber_of_properCurve _
      (isQCartier_single_of_isSmoothScheme hZs E) CE₀ E rfl
    rwa [hEnum CE₀ rfl, toQDivisor_single, Int.cast_one] at h
  have hE1' := isIntersectionNumber_congr hs'.symm hE1
  have hCZval : (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k
      (eY.hom ≫ cY ≫ f ≫ sX) CZ.ι CZ.dim_le (isQCartier_single_of_isSmoothScheme hZs'' E) = -1 := by
    have h := isIntersectionNumber_of_properCurve _
      (isQCartier_single_of_isSmoothScheme hZs'' E) CZ E rfl
    set vZ := (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k
      (eY.hom ≫ cY ≫ f ≫ sX) CZ.ι CZ.dim_le (isQCartier_single_of_isSmoothScheme hZs'' E)
    rw [toQDivisor_single, Int.cast_one] at h
    exact h.unique hE1'
  have hF'num : IsIntersectionNumber (cY ≫ f ≫ sX) (Finsupp.single F' 1) F'.idealSheaf (-1) := by
    have h := isIntersectionNumber_of_properCurve _
      (isQCartier_single_of_isSmoothScheme hYms F') CF F' hF'ξ.symm
    rwa [← hkey, hCZval, toQDivisor_single, Int.cast_one] at h
  have hP' : Order.coheight (cY F'.genericPoint) = 1 := by
    rwa [hF'ξ, ← Scheme.Hom.comp_apply, heY]
  obtain ⟨s, hs, hiso⟩ :=
    exists_isIntersectionNumber_pointBlowupChain hYv hYs hYd hchain F' hP' hF'num
  have hQ' : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hP' = Q :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective (by
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hQξ', hF'ξ,
        ← Scheme.Hom.comp_apply, heY])
  rw [hQ'] at hs
  -- negativity forces `s = 0`
  set v := (Divisor.toQDivisor (Finsupp.single Q 1)).intersectionNumber k (f ≫ sX) CQ.ι
    CQ.dim_le (isQCartier_single_of_isSmoothScheme hYs Q) with hvdef
  have hQv : IsIntersectionNumber (f ≫ sX) (Finsupp.single Q 1) Q.idealSheaf v := by
    have h := isIntersectionNumber_of_properCurve _
      (isQCartier_single_of_isSmoothScheme hYs Q) CQ Q hQξ.symm
    change IsIntersectionNumber _ _ _ v at h
    rwa [toQDivisor_single, Int.cast_one] at h
  have hval := hs.unique hQv
  have hs0 : s = 0 := by
    have h1 : (s : ℚ) < 1 := by linarith
    have h2 : s < 1 := by exact_mod_cast h1
    omega
  obtain ⟨eC, heC⟩ := hiso hs0
  rw [hs0, Nat.cast_zero, add_zero] at hs
  -- `Q ≅ F ≅ ℙ¹`
  obtain ⟨eL, heL⟩ := exists_iso_projSpace_projectiveLine (k := k)
  obtain ⟨e1, he1⟩ := exists_subscheme_iso_of_eq hE
  obtain ⟨e2, he2⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf E)
  obtain ⟨e3, he3⟩ := exists_curveSubschemeAt_iso eY.hom ξ rfl hrange
  obtain ⟨e4, he4⟩ := exists_curveSubschemeAt_iso_of_eq hF'ξ.symm
  obtain ⟨e5, he5⟩ := exists_curveSubschemeAt_iso_of_eq
    (show cY F'.genericPoint = Q.genericPoint by
      rw [hQξ, hF'ξ, ← Scheme.Hom.comp_apply, heY])
  obtain ⟨e6, he6⟩ :=
    exists_subscheme_iso_of_eq (vanishingIdeal_closure_genericPoint_eq_idealSheaf Q)
  let eR := e3 ≪≫ e4 ≪≫ eC ≪≫ e5 ≪≫ e6
  have hR : eR.hom ≫ Q.idealSheaf.subschemeι = curveSubschemeAtι ξ ≫ g := by
    simp only [eR, Iso.trans_hom, Category.assoc]
    rw [he6, he5, heC, ← Category.assoc e4.hom, he4, ← Category.assoc e3.hom, he3,
      Category.assoc, heY]
  have k2 : e2.inv ≫ curveSubschemeAtι ξ = E.idealSheaf.subschemeι :=
    (Iso.inv_comp_eq _).2 he2.symm
  have k1 : e1.inv ≫ E.idealSheaf.subschemeι =
      (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀))).subschemeι := by
    rw [← he1, Iso.inv_hom_id_assoc]
  have k0 : eP.inv ≫ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀))).subschemeι ≫ b ≫ s₀ =
      MMP.Intersection.ProjSpace.toSpec k _ := by
    rw [← heP, Iso.inv_hom_id_assoc]
  let eQ : projectiveLine k ≅ Q.idealSheaf.subscheme := eL ≪≫ eP.symm ≪≫ e1.symm ≪≫ e2.symm ≪≫ eR
  have heQ : eQ.hom ≫ Q.idealSheaf.subschemeι ≫ f ≫ sX = projectiveLine k ↘ Spec (.of k) := by
    simp only [eQ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [reassoc_of% hR, hgs, reassoc_of% k2, reassoc_of% k1, k0, heL]
  have hcurveQ := MMP.Flips.isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd Q
  have hQprop : IsProper (Q.idealSheaf.subschemeι ≫ f ≫ sX) := by
    have h1 : Q.idealSheaf.subschemeι ≫ f ≫ sX =
        eQ.inv ≫ eL.hom ≫ MMP.Intersection.ProjSpace.toSpec k _ := by
      rw [heL, ← heQ, Iso.inv_hom_id_assoc]
    rw [h1]
    infer_instance
  exact hf.2 ⟨Q, hQexc, ⟨⟨hcurveQ, hQprop, eQ.hom, heQ, inferInstance,
    isBirationalMorphism_of_isIso _⟩, eQ, heQ⟩, hs⟩

/-- **Descending along a chain of point blowups.** Let `f : Y ⟶ X` be a resolution of a normal
surface with no `f`-exceptional `(-1)`-curve, `h : V ⟶ X` a resolution and `p : Z ⟶ V` a chain of
point blowups. Every `g : Z ⟶ Y` with `g ≫ f = p ≫ h` descends, one blowup at a time, to some
`a : V ⟶ Y` with `a ≫ f = h`: the last exceptional curve is contracted by `g`
(`exists_const_of_isMinimalSurfaceResolution`), so `g` factors through the contraction. -/
private theorem exists_comp_eq_of_pointBlowupChain [IsAlgClosed k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) {V : Scheme.{u}} (h : V ⟶ X)
    (hh : IsSmoothResolution sX h) [IsNoetherian V]
    (hreg : ∀ x : V, IsRegularLocalRing (V.presheaf.stalk x)) {T : Set V}
    (hT : ∀ x ∈ T, ringKrullDim (V.presheaf.stalk x) = 2) {Z : Scheme.{u}} {p : Z ⟶ V}
    (hp : PointBlowupChain V T Z p) :
    ∀ g : Z ⟶ Y, g ≫ f = p ≫ h → ∃ a : V ⟶ Y, a ≫ f = h := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral V := hh.isIntegral
  obtain ⟨hVn, hVd, hhb⟩ := hh.isNormalVariety hX
  rw [hdim] at hVd
  have hVv : AlgebraicGeometry.IsVariety k (h ≫ sX) := hVn.1
  have hVs := hh.isSmoothScheme
  have : IsProper h := hh.isProper
  induction hp with
  | refl =>
    intro g hg
    exact ⟨g, by rw [hg, Category.id_comp]⟩
  | @step Z₀ p₀ hh₀ w hw hwT ih =>
    intro g hg
    obtain ⟨hZ₀v, hZ₀s, hZ₀d, hp₀⟩ := pointBlowupChain_isSmoothSurface hVv hVs hVd hh₀
    obtain ⟨hZ₀N, -, hZ₀reg, hZ₀dim⟩ := hh₀.isNoetherian_and_regular hreg hT
    have hb := isContractionOfExceptionalCurve_blowUpToBase w hw (hZ₀reg w) (hZ₀dim w hw hwT)
    have hg' : g ≫ f = blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀)) ≫ (p₀ ≫ h) := by
      rw [hg, Category.assoc]
    have hq₀b : IsBirational (p₀ ≫ h) :=
      (isBirational_of_pointBlowupChain hh₀ inferInstance inferInstance hVd).comp hhb
    have hconst := exists_const_of_isMinimalSurfaceResolution sX f hX hdim hf hZ₀v hZ₀s hZ₀d
      (p₀ ≫ h) (Category.assoc _ _ _) hq₀b hw g hg'
    obtain ⟨g₀, hg₀, -⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ _ hb g
      hconst
    obtain ⟨y₀, hy₀⟩ := hb.exists_const_on_subscheme
    obtain ⟨ψ, -, hψu⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ _ hb
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : TopologicalSpace.Closeds Z₀)) ≫ p₀ ≫ h)
      ⟨(p₀ ≫ h) y₀, fun z => by rw [Scheme.Hom.comp_apply, hy₀ z]⟩
    have h1 : g₀ ≫ f = p₀ ≫ h := by
      rw [hψu (g₀ ≫ f) (by beta_reduce; rw [← Category.assoc, hg₀, hg']),
        hψu (p₀ ≫ h) rfl]
    exact ih g₀ h1

/-- **Resolving `V ⇢ Y` by point blowups.** For resolutions `f : Y ⟶ X` and `h : V ⟶ X` of a
normal surface, the birational map `V ⇢ Y` over `X` (defined over the open of `X` where `f` is an
isomorphism) is resolved by a chain of point blowups `p : Z ⟶ V` at points with two-dimensional
local rings: there is `g : Z ⟶ Y` with `g ≫ f = p ≫ h` ([Stacks, Tag 0C5H]). -/
private theorem exists_pointBlowupChain_comp_eq (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) {f : Y ⟶ X} (hf : IsSmoothResolution sX f) {V : Scheme.{u}}
    (h : V ⟶ X) (hh : IsSmoothResolution sX h) [IsNoetherian V]
    (hreg : ∀ x : V, IsRegularLocalRing (V.presheaf.stalk x))
    (hdimV : ∀ x : V, ringKrullDim (V.presheaf.stalk x) ≤ 2) :
    ∃ (T : Set V) (_ : ∀ x ∈ T, ringKrullDim (V.presheaf.stalk x) = 2) (Z : Scheme.{u})
      (p : Z ⟶ V) (g : Z ⟶ Y), PointBlowupChain V T Z p ∧ g ≫ f = p ≫ h := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsProper f := hf.isProper
  obtain ⟨W, hiso, hdense⟩ := exists_isIso_morphismRestrict_dense_preimage sX hX hf hh
  letI : V.Over X := ⟨h⟩
  letI : Y.Over X := ⟨f⟩
  let φ : V.PartialMap Y := ⟨h ⁻¹ᵁ W, hdense, (h ∣_ W) ≫ inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι⟩
  haveI : φ.IsOver X := by
    rw [Scheme.PartialMap.isOver_iff]
    show ((h ∣_ W) ≫ inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι) ≫ f = (h ⁻¹ᵁ W).ι ≫ h
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  haveI : IsProper (Y ↘ X) := inferInstanceAs (IsProper f)
  obtain ⟨T, Z, p, g, -, hTdim, -, hchain, hS, -⟩ :=
    Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_isNoetherian
      (S := X) hreg hdimV φ
  exact ⟨T, hTdim, Z, p, g, hchain, hS⟩

/-- **Existence of the factorization** through a resolution `f` without contracted
`(-1)`-curves: every resolution `h : V ⟶ X` of the normal surface `X` is `a ≫ f` for some `a`.
The birational map `V ⇢ Y` is resolved by a chain of point blowups `p : Z ⟶ V` with
`g : Z ⟶ Y` (`exists_pointBlowupChain_comp_eq`), and `g` descends along the chain
(`exists_comp_eq_of_pointBlowupChain`). -/
private theorem exists_comp_eq [IsAlgClosed k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) {V : Scheme.{u}} (h : V ⟶ X)
    (hh : IsSmoothResolution sX h) : ∃ a : V ⟶ Y, a ≫ f = h := by
  obtain ⟨hVn, hVd, -⟩ := hh.isNormalVariety hX
  rw [hdim] at hVd
  have hVv : AlgebraicGeometry.IsVariety k (h ≫ sX) := hVn.1
  have hVs := hh.isSmoothScheme
  have : LocallyOfFiniteType (h ≫ sX) := hVv.toLocallyOfFiniteType
  have : QuasiCompact (h ≫ sX) := hVv.toQuasiCompact
  have : IsNoetherian V := isNoetherian_of_finiteType (h ≫ sX)
  have hreg := ((isRegular_iff_regular_stalks V).1
    (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme (h ≫ sX) hVs)).2
  have hdimV : ∀ x : V, ringKrullDim (V.presheaf.stalk x) ≤ 2 := fun x => by
    rw [← hVd, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk V]
    exact le_iSup (fun z : V => ringKrullDim (V.presheaf.stalk z)) x
  obtain ⟨T, hT, Z, p, g, hchain, hg⟩ :=
    exists_pointBlowupChain_comp_eq sX hX hf.1 h hh hreg hdimV
  exact exists_comp_eq_of_pointBlowupChain sX f hX hdim hf h hh hreg hT hchain g hg

end Chains

/-- Over an open `U` of `X`, the restriction `f ∣_ U` of a resolution without contracted
`(-1)`-curves again has none: a contracted curve of `f ∣_ U` is a contracted curve of `f`, with
the same self-intersection. -/
private theorem isMinimalSurfaceResolution_morphismRestrict
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hf : IsMinimalSurfaceResolution sX f)
    (U : X.Opens) [QuasiCompact (f ∣_ U ≫ U.ι ≫ sX)] [IsLocallyNoetherian (f ⁻¹ᵁ U)]
    [IsNormal (f ⁻¹ᵁ U)] [Nonempty U] : IsMinimalSurfaceResolution (U.ι ≫ sX) (f ∣_ U) := by
  refine ⟨isSmoothResolution_morphismRestrict sX hX hf.1 U, ?_⟩
  rintro ⟨F, hFexc, hF, hnum⟩
  apply hf.2
  have hs : (f ⁻¹ᵁ U).ι ≫ f ≫ sX = f ∣_ U ≫ U.ι ≫ sX := (morphismRestrict_ι_assoc _ _ _).symm
  have : IsSeparated (f ≫ sX) := (hf.1.isNormalVariety hX).1.1.toIsSeparated
  exact exists_exceptional_minusOneCurve_of_isOpenImmersion sX f hf.1.isSmoothScheme
    (f ⁻¹ᵁ U).ι _ hs (isSmoothResolution_morphismRestrict sX hX hf.1 U).isSmoothScheme F hF hnum
    fun w hw hbir => hFexc hw (mem_biregularLocus_morphismRestrict f U w hbir)

/-- The restriction of a resolution of a normal surface over a nonempty open `U` is a
resolution of the normal surface `U`, without contracted `(-1)`-curves if `f` has none. -/
private theorem exists_isMinimalSurfaceResolution_morphismRestrict
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) (U : X.Opens) (hU : U ≠ ⊥) :
    ∃ (_ : QuasiCompact (f ∣_ U ≫ U.ι ≫ sX)) (_ : IsLocallyNoetherian (f ⁻¹ᵁ U))
      (_ : IsNormal (f ⁻¹ᵁ U)), IsNormalVariety k (U.ι ≫ sX) ∧
      topologicalKrullDim U = 2 ∧ IsMinimalSurfaceResolution (U.ι ≫ sX) (f ∣_ U) := by
  have : Nonempty U := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hU
    exact ⟨⟨x, hx⟩⟩
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsNormal X := hX.2
  have hqc : QuasiCompact (f ∣_ U ≫ U.ι ≫ sX) := by
    rw [morphismRestrict_ι_assoc]
    have : QuasiCompact (f ⁻¹ᵁ U).ι := inferInstance
    infer_instance
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  refine ⟨hqc, inferInstance, inferInstance, ⟨isVariety_opens_ι k sX U, inferInstance⟩,
    (topologicalKrullDim_opens k sX U).trans hdim,
    isMinimalSurfaceResolution_morphismRestrict sX f hX hf U⟩

/-- **A resolution with no contracted `(-1)`-curve is dominated by every resolution.** Let `k` be
algebraically closed, `X` a normal surface over `k` and `f : Y ⟶ X` a resolution with no
contracted smooth rational curve of self-intersection `-1`. Then every resolution `h : V ⟶ X`
factors as `h = a ≫ f` for a unique `a : V ⟶ Y`; and for every open `U ⊆ X`, every resolution
`h : V ⟶ U` factors uniquely through the restriction `f ∣_ U : f ⁻¹ᵁ U ⟶ U`. -/
@[mmp "lem_mmp_foundation_no_minus_one_resolution_universal"]
public theorem IsMinimalSurfaceResolution.existsUnique_comp_eq [IsAlgClosed k]
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    (hf : IsMinimalSurfaceResolution sX f) :
    (∀ (V : Scheme.{u}) (h : V ⟶ X), IsSmoothResolution sX h → ∃! a : V ⟶ Y, a ≫ f = h) ∧
      ∀ (U : X.Opens) (V : Scheme.{u}) (h : V ⟶ U), IsSmoothResolution (U.ι ≫ sX) h →
        ∃! a : V ⟶ f ⁻¹ᵁ U, a ≫ f ∣_ U = h := by
  refine ⟨fun V h hh => ?_, fun U V h hh => ?_⟩
  · obtain ⟨a, ha⟩ := exists_comp_eq sX f hX hdim hf h hh
    exact ⟨a, ha, fun b hb => eq_of_comp_eq sX hX hf.1 hh hb ha⟩
  · by_cases hU : U = ⊥
    · subst hU
      have : IsEmpty ((⊥ : X.Opens) : Scheme) := ⟨fun x => x.2⟩
      have : IsEmpty V := ⟨fun v => isEmptyElim (h v)⟩
      have hi := isInitialOfIsEmpty (X := V)
      exact ⟨hi.to _, hi.hom_ext _ _, fun _ _ => hi.hom_ext _ _⟩
    obtain ⟨_, _, _, hUX, hUd, hfU⟩ :=
      exists_isMinimalSurfaceResolution_morphismRestrict sX f hX hdim hf U hU
    obtain ⟨a, ha⟩ := exists_comp_eq (U.ι ≫ sX) (f ∣_ U) hUX hUd hfU h hh
    exact ⟨a, ha, fun b hb => eq_of_comp_eq (U.ι ≫ sX) hUX hfU.1 hh hb ha⟩

end Universal

section Existence

open TopologicalSpace

/-- A resolution of a normal surface has only finitely many prime divisors in its exceptional
set. -/
private theorem finite_setOf_support_subset_exceptionalSet (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hf : IsSmoothResolution sX f) :
    {E : MMP.Mori.PrimeDivisor Y | E.support ⊆ (exceptionalSet f : Set Y)}.Finite := by
  classical
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsNormal X := hX.2
  have : IsIntegral Y := hY.toIsIntegral
  have : IsProper f := hf.isProper
  have : QuasiCompact (f ≫ sX) := hY.toQuasiCompact
  have : IsLocallyNoetherian Y :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
      hf.isSmoothScheme).1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  -- the biregular locus is nonempty, so the exceptional set is not everything
  have hcod := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hY) sX f
    hf.isBirationalMorphism
  have hB : (biregularLocus f : Set X).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hle : closedsCodimension (biregularLocus f).compl ≤
        codimension (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
          IrreducibleCloseds X) :=
      iInf₂_le _ (by simp [TopologicalSpace.Opens.compl, hne])
    have h0 : codimension (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
        IrreducibleCloseds X) = 0 := by
      rw [codimension_eq_coheight, Order.coheight_eq_zero]
      intro W _
      exact fun x _ ↦ Set.mem_univ x
    have := hcod.trans (hle.trans h0.le)
    norm_num at this
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  obtain ⟨y0, hy0⟩ : ∃ y : Y, f y ∈ biregularLocus f := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := f.denseRange.inter_open_nonempty _
      (biregularLocus f).isOpen hB
    exact ⟨y, hy⟩
  set Z : Set Y := (exceptionalSet f : Set Y)
  have hy0Z : y0 ∉ Z := fun h ↦ h hy0
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irr, h𝒮cover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (exceptionalSet f).isClosed
  lift 𝒮 to Finset (Set Y) using h𝒮fin
  refine Set.Finite.of_finite_image (f := fun E : MMP.Mori.PrimeDivisor Y ↦ E.support)
    (𝒮.finite_toSet.subset ?_) ?_
  · rintro - ⟨E, hE, rfl⟩
    have hEcl := AlgebraicGeometry.PrimeDivisor.support_eq_closure E
    have hEirr : IsIrreducible E.support := hEcl ▸ isIrreducible_singleton.closure
    have hsub : E.support ⊆ ⋃₀ (𝒮 : Set (Set Y)) := by rwa [← h𝒮cover]
    obtain ⟨t, ht, hEt⟩ := isIrreducible_iff_sUnion_isClosed.mp hEirr
      𝒮 (fun s hs ↦ h𝒮closed s hs) hsub
    have htZ : t ⊆ Z := by
      intro x hx; change x ∈ (exceptionalSet f : Set Y); rw [h𝒮cover]; exact ⟨t, ht, hx⟩
    suffices htE : t ⊆ E.support by
      change E.support ∈ (𝒮 : Set (Set Y))
      rwa [Set.Subset.antisymm hEt htE]
    by_contra htE
    let Ei : IrreducibleCloseds Y := IrreducibleCloseds.closureSingleton E.genericPoint
    let ti : IrreducibleCloseds Y := ⟨t, h𝒮irr t ht, h𝒮closed t ht⟩
    let ui : IrreducibleCloseds Y :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
    have h1 : Ei < ti := by
      refine lt_of_le_of_ne (fun x hx ↦ hEt ?_) fun h ↦ htE ?_
      · rwa [hEcl]
      · rw [hEcl]; exact (congrArg (fun W : IrreducibleCloseds Y ↦ (W : Set Y)) h).symm.le
    have h2 : ti < ui := lt_of_le_of_ne (fun x _ ↦ Set.mem_univ x) fun h ↦ hy0Z (htZ (by
      have : y0 ∈ (ui : Set Y) := Set.mem_univ _
      rwa [← h] at this))
    have hc := E.codimension_closureSingleton_genericPoint
    rw [codimension_eq_coheight] at hc
    have : (1 : ℕ∞) + 1 ≤ 1 :=
      calc (1 : ℕ∞) + 1 ≤ Order.coheight ti + 1 := by
            gcongr
            exact le_add_self.trans (Order.coheight_add_one_le h2)
        _ ≤ Order.coheight Ei := Order.coheight_add_one_le h1
        _ = 1 := hc
    exact absurd this (by norm_num)
  · intro a _ b _ hab
    have ha := AlgebraicGeometry.PrimeDivisor.support_eq_closure a
    have hb := AlgebraicGeometry.PrimeDivisor.support_eq_closure b
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have hab' : a.support = b.support := hab
    have : IsGenericPoint a.genericPoint (closure ({b.genericPoint} : Set Y)) := by
      rw [← hb, ← hab', ha]; exact isGenericPoint_closure
    exact this.eq isGenericPoint_closure

/-- A prime divisor in the exceptional set of a resolution of a normal surface is contracted to
a point: the image of the exceptional set is a finite set of closed points, since its complement
contains every point of codimension at most one. -/
private theorem exists_image_support_eq_singleton (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hf : IsSmoothResolution sX f)
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.support ⊆ (exceptionalSet f : Set Y)) :
    ∃ x : X, f.base '' E.support = {x} := by
  have : IsNormal X := hX.2
  have : IsProper f := hf.isProper
  have hcod := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hY) sX f
    hf.isBirationalMorphism
  set x := f.base E.genericPoint
  have hEcl := AlgebraicGeometry.PrimeDivisor.support_eq_closure E
  have hxB : closure ({x} : Set X) ⊆ ((biregularLocus f).compl : Set X) := by
    refine (isClosed_compl_iff.mpr (biregularLocus f).isOpen).closure_subset_iff.mpr ?_
    rintro _ rfl
    exact hE (hEcl ▸ subset_closure rfl)
  -- every irreducible closed subset of the non-biregular locus has codimension at least two
  have h2 : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ closure {x} → 2 ≤ Order.coheight W :=
    fun W hW ↦ hcod.trans (iInf₂_le W (hW.trans hxB))
  have hdimle : ∀ W : IrreducibleCloseds X, Order.coheight W ≤ 2 := by
    intro W
    have := Order.coheight_le_krullDim W
    rw [← topologicalKrullDim, hdim] at this
    exact WithBot.coe_le_coe.mp this
  have hcl : closure ({x} : Set X) = {x} := by
    refine Set.Subset.antisymm (fun y hy ↦ ?_) subset_closure
    by_contra hyx
    let Wy : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton y
    let Wx : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton x
    have hlt : Wy < Wx := by
      refine lt_of_le_of_ne (show closure ({y} : Set X) ⊆ closure {x} from
        closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure) fun h ↦ hyx ?_
      have h' : closure ({y} : Set X) = closure {x} :=
        congrArg (fun W : IrreducibleCloseds X ↦ (W : Set X)) h
      exact (inseparable_iff_closure_eq.mpr h').eq
    have h3 := Order.coheight_add_one_le hlt
    have h4 := h2 Wx (le_refl _)
    have h5 := hdimle Wy
    have : (2 : ℕ∞) + 1 ≤ 2 :=
      (show (2 : ℕ∞) + 1 ≤ Order.coheight Wx + 1 by gcongr).trans (h3.trans h5)
    exact absurd this (by norm_num)
  refine ⟨x, Set.Subset.antisymm ?_ ?_⟩
  · rw [← hcl, hEcl]
    exact (image_closure_subset_closure_image f.continuous).trans (by rw [Set.image_singleton])
  · rintro _ rfl
    exact ⟨E.genericPoint, hEcl ▸ subset_closure rfl, rfl⟩

/-- Strict transforms through the contraction `c` of a curve `E` contracted by `f = c ≫ f'`:
`f'` is birational, and its exceptional prime divisors inject into those of `f` other than
`E`. -/
private theorem exists_injOn_of_isIso_morphismRestrict (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Y' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (f : Y ⟶ X) (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hf : IsSmoothResolution sX f)
    (E : MMP.Mori.PrimeDivisor Y) (hE : E.support ⊆ (exceptionalSet f : Set Y))
    (c : Y ⟶ Y') (f' : Y' ⟶ X)
    (hY' : AlgebraicGeometry.IsVariety k (f' ≫ sX)) (hY'd : topologicalKrullDim Y' = 2)
    [IsProper c] (hc : IsBirationalMorphism c) (q : Y') (U : Y'.Opens)
    (hU : (U : Set Y') = {q}ᶜ) (hcU : (c ⁻¹ᵁ U : Set Y) = E.supportᶜ) (hiso : IsIso (c ∣_ U))
    [IsProper f'] (hcf : c ≫ f' = f) :
    IsBirationalMorphism f' ∧
      ∃ φ : MMP.Mori.PrimeDivisor Y' → MMP.Mori.PrimeDivisor Y,
        Set.InjOn φ {E' | E'.support ⊆ (exceptionalSet f' : Set Y')} ∧
        Set.MapsTo φ {E' | E'.support ⊆ (exceptionalSet f' : Set Y')}
          ({E | E.support ⊆ (exceptionalSet f : Set Y)} \ {E}) := by
  classical
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsNormal X := hX.2
  have : IsProper f := hf.isProper
  have : IsIntegral Y := hY.toIsIntegral
  have : IsIntegral Y' := hY'.toIsIntegral
  have : IsDominant c := hc.isDominant
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  set W := biregularLocus f with hWdef
  have hcod := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hY) sX f
    hf.isBirationalMorphism
  -- `q` is the image of a point of `E`, which `f` maps outside `W`
  have hq : q ∈ Set.range c.base := by
    rw [← c.isClosedMap.isClosed_range.closure_eq, c.denseRange.closure_range]
    trivial
  obtain ⟨e, he⟩ := hq
  have heE : e ∈ E.support := by
    by_contra h
    have h' : e ∈ (c ⁻¹ᵁ U : Set Y) := by rwa [hcU]
    have h'' : c e ∈ (U : Set Y') := h'
    rw [hU, he] at h''
    exact h'' rfl
  have hfq : f' q ∉ W := by
    have h : f e ∉ W := hE heE
    rwa [← hcf, Scheme.Hom.comp_apply, he] at h
  have hWU : f' ⁻¹ᵁ W ≤ U := by
    intro y hy
    change y ∈ (U : Set Y')
    rw [hU]
    rintro rfl
    exact hfq hy
  have hcW : IsIso (c ∣_ (f' ⁻¹ᵁ W)) :=
    isBiregular_iff_le_biregularLocus.mpr (hWU.trans (le_biregularLocus hiso))
  have hfW : IsIso (f' ∣_ W) := by
    have h1 : IsIso (f ∣_ W) := isBiregular_biregularLocus f
    have h2 : IsIso ((c ≫ f') ∣_ W) := by rwa [hcf]
    rw [morphismRestrict_comp] at h2
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (c ∣_ (f' ⁻¹ᵁ W)) (f' ∣_ W) hcW h2
  have hW : (W : Set X).Nonempty := by
    have := MMP.Flips.nonempty_compl_of_two_le_closedsCodimension _ hcod
    simpa [TopologicalSpace.Closeds.compl, TopologicalSpace.Opens.compl] using this
  obtain ⟨y0, hy0⟩ : ∃ y : Y, f y ∈ W := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := f.denseRange.inter_open_nonempty _ W.isOpen hW
    exact ⟨y, hy⟩
  have hb' : IsBirationalMorphism f' := by
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f' (f' ⁻¹ᵁ W) W ⟨c y0, ?_⟩ hW le_rfl ?_
    · change f' (c y0) ∈ W
      rw [← Scheme.Hom.comp_apply, hcf]
      exact hy0
    · rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact hfW
  refine ⟨hb', ?_⟩
  -- every point of `U` comes from a point off `E`
  have hpre : ∀ y' ∈ (U : Set Y'), ∃ y ∈ E.supportᶜ, c y = y' := by
    intro y' hy'
    obtain ⟨p, hp⟩ := (c ∣_ U).surjective ⟨y', hy'⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [← hcU]
      exact p.2
    · have h : U.ι ((c ∣_ U) p) = c p.1 := by
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
        rfl
      rw [← h, hp]
      rfl
  have hqcl : IsClosed ({q} : Set Y') := by
    rw [← isOpen_compl_iff, ← hU]; exact U.isOpen
  have hq2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hY' hY'd hqcl
  have hmemU : ∀ E' : MMP.Mori.PrimeDivisor Y',
      AlgebraicGeometry.PrimeDivisor.genericPoint E' ∈ (U : Set Y') := by
    intro E'
    rw [hU]
    intro h
    have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E'
    rw [Set.mem_singleton_iff.mp h, hq2] at h1
    exact absurd h1 (by norm_num)
  have hcoh : ∀ E' : MMP.Mori.PrimeDivisor Y',
      Order.coheight (hpre _ (hmemU E')).choose = 1 := by
    intro E'
    have hspec := (hpre _ (hmemU E')).choose_spec
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus c (le_biregularLocus hiso (by
      rw [hspec.2]; exact hmemU E')), hspec.2]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E'
  let φ : MMP.Mori.PrimeDivisor Y' → MMP.Mori.PrimeDivisor Y := fun E' ↦
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hcoh E')
  have hφ : ∀ E',
      AlgebraicGeometry.PrimeDivisor.genericPoint (φ E') = (hpre _ (hmemU E')).choose :=
    fun E' ↦ AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hcφ : ∀ E', c (AlgebraicGeometry.PrimeDivisor.genericPoint (φ E')) =
      AlgebraicGeometry.PrimeDivisor.genericPoint E' := fun E' ↦ by
    rw [hφ]; exact (hpre _ (hmemU E')).choose_spec.2
  refine ⟨φ, fun a _ b _ hab ↦ ?_, fun E' hE' ↦ ⟨?_, ?_⟩⟩
  · apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [← hcφ a, ← hcφ b, hab]
  · -- the strict transform of `E'` lies in `Ex(f)`
    change (φ E').support ⊆ (exceptionalSet f : Set Y)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine (exceptionalSet f).isClosed.closure_subset_iff.mpr ?_
    rintro _ rfl
    rw [SetLike.mem_coe, mem_exceptionalSet]
    intro hmem
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus f hmem
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
    have hx : (AlgebraicGeometry.PrimeDivisor.genericPoint E') ∈ exceptionalSet f' := by
      have := AlgebraicGeometry.PrimeDivisor.support_eq_closure E'
      exact hE' (this ▸ subset_closure rfl)
    have h2 : f (AlgebraicGeometry.PrimeDivisor.genericPoint (φ E')) =
        f' (AlgebraicGeometry.PrimeDivisor.genericPoint E') := by
      rw [← hcf, Scheme.Hom.comp_apply, hcφ]
    have hcod' := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hY')
      sX f' hb'
    have h3 : 2 ≤ Order.coheight (f' (AlgebraicGeometry.PrimeDivisor.genericPoint E')) := by
      have hsub : ((irreducibleSetEquivPoints (α := X)).symm
          (f' (AlgebraicGeometry.PrimeDivisor.genericPoint E')) : Set X) ⊆
          ((biregularLocus f').compl : Set X) :=
        (biregularLocus f').compl.isClosed.closure_subset_iff.mpr
          (Set.singleton_subset_iff.mpr hx)
      have := le_closedsCodimension_iff.mp hcod' _ hsub
      rwa [codimension_eq_coheight, Order.coheight_orderIso] at this
    rw [← h2, h1] at h3
    exact absurd h3 (by norm_num)
  · -- the strict transform of `E'` is not `E`
    intro h
    have h1 : (AlgebraicGeometry.PrimeDivisor.genericPoint (φ E')) ∈ E.support := by
      rw [Set.mem_singleton_iff.mp h, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    rw [hφ] at h1
    exact (hpre _ (hmemU E')).choose_spec.1 h1

/-- Contracting a `(-1)`-curve `E` in the exceptional set of a resolution `f` gives a resolution
`f'` whose exceptional prime divisors inject, by strict transform, into those of `f` other than
`E`. -/
private theorem exists_injOn_of_isMinusOneCurve (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hf : IsSmoothResolution sX f)
    (hYd : topologicalKrullDim Y = 2) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (hE : E.support ⊆ (exceptionalSet f : Set Y))
    (hEr : IsSmoothRationalCurve (f ≫ sX) E.idealSheaf)
    (hEE : IsIntersectionNumber (f ≫ sX) (Finsupp.single E 1) E.idealSheaf (-1)) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), AlgebraicGeometry.IsVariety k (f' ≫ sX) ∧
      IsSmoothResolution sX f' ∧ topologicalKrullDim Y' = 2 ∧
      ∃ φ : MMP.Mori.PrimeDivisor Y' → MMP.Mori.PrimeDivisor Y,
        Set.InjOn φ {E' | E'.support ⊆ (exceptionalSet f' : Set Y')} ∧
        Set.MapsTo φ {E' | E'.support ⊆ (exceptionalSet f' : Set Y')}
          ({E | E.support ⊆ (exceptionalSet f : Set Y)} \ {E}) := by
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsSeparated sX := hXv.toIsSeparated
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : IsProper f := hf.isProper
  have hC : IsMinusOneCurve (f ≫ sX) E := ⟨hEE.1, hEr.2, hEE⟩
  obtain ⟨Y', c, f', ⟨hY', hsm', hY'd⟩, _, hc, ⟨q, U, hU, hcU, hiso⟩, _, hcf⟩ :=
    MMP.Resolution.Bridges.exists_contraction_of_isMinusOneCurve (sY := f ≫ sX) (sZ := sX)
      hY hf.isSmoothScheme hYd f rfl E hC
      (exists_image_support_eq_singleton k sX hX hdim f hY hf E hE)
  obtain ⟨hb', φ, hinj, hmaps⟩ := exists_injOn_of_isIso_morphismRestrict k sX hX f hY hf
    E hE c f' hY' hY'd hc q U hU hcU hiso hcf
  exact ⟨Y', f', hY', ⟨‹_›, hb', hsm'⟩, hY'd, φ, hinj, hmaps⟩

/-- Contracting a `(-1)`-curve in the exceptional set of a resolution gives a resolution with
fewer exceptional prime divisors. -/
private theorem exists_ncard_lt_of_isMinusOneCurve (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hf : IsSmoothResolution sX f)
    (hYd : topologicalKrullDim Y = 2) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (hE : E.support ⊆ (exceptionalSet f : Set Y))
    (hEr : IsSmoothRationalCurve (f ≫ sX) E.idealSheaf)
    (hEE : IsIntersectionNumber (f ≫ sX) (Finsupp.single E 1) E.idealSheaf (-1)) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), AlgebraicGeometry.IsVariety k (f' ≫ sX) ∧
      IsSmoothResolution sX f' ∧ topologicalKrullDim Y' = 2 ∧
      {E' : MMP.Mori.PrimeDivisor Y' | E'.support ⊆ (exceptionalSet f' : Set Y')}.ncard <
        {E : MMP.Mori.PrimeDivisor Y | E.support ⊆ (exceptionalSet f : Set Y)}.ncard := by
  obtain ⟨Y', f', hY', hf', hY'd, φ, hinj, hmaps⟩ :=
    exists_injOn_of_isMinusOneCurve k sX hX hdim f hY hf hYd E hE hEr hEE
  have hfin := finite_setOf_support_subset_exceptionalSet k sX hX f hY hf
  refine ⟨Y', f', hY', hf', hY'd, ?_⟩
  calc _ = (φ '' {E' : MMP.Mori.PrimeDivisor Y' |
          E'.support ⊆ (exceptionalSet f' : Set Y')}).ncard := hinj.ncard_image.symm
    _ ≤ ({E : MMP.Mori.PrimeDivisor Y | E.support ⊆ (exceptionalSet f : Set Y)} \ {E}).ncard :=
        Set.ncard_le_ncard hmaps.image_subset hfin.sdiff
    _ < _ := Set.ncard_sdiff_singleton_lt_of_mem hE hfin

open MMP.Threefold.Resolution MMP.Threefold.Mori Stacks.Intersection in
/-- A minimal resolution is an isomorphism over the smooth locus. -/
private theorem isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution (k : Type u)
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hYd : topologicalKrullDim Y = 2)
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsMinimalSurfaceResolution sX f) :
    IsIso (f ∣_ smoothLocus sX) := by
  classical
  set V := smoothLocus sX with hVdef
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have : IsIntegral Y := hY.toIsIntegral
  have hf1 := hf.1
  have : IsProper f := hf1.isProper
  have : IsDominant f := hf1.isBirationalMorphism.isDominant
  by_cases hV : V = ⊥
  · have : IsEmpty V.toScheme := ⟨fun x => by
      have h : x.1 ∈ (V : Set X) := x.2
      have h' : (V : Set X) = ∅ := by rw [hV]; rfl
      rwa [h'] at h⟩
    exact (isInitialOfIsEmpty (X := V.toScheme)).isIso_to _
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hV
    exact ⟨⟨x, hx⟩⟩
  have : Nonempty (f ⁻¹ᵁ V) := by
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty V›
    obtain ⟨y, hy⟩ := f.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨⟨y, hy⟩⟩
  have hVv : AlgebraicGeometry.IsVariety k (V.ι ≫ sX) := isVariety_opens_ι k sX V
  have hVd : topologicalKrullDim V = 2 := (topologicalKrullDim_opens k sX V).trans hdim
  have hVs : IsSmoothScheme (V.ι ≫ sX) := by
    rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, ← Scheme.Hom.preimage_smoothLocus_eq,
      ← smoothLocus_eq_smoothLocus, ← hVdef, Scheme.Opens.ι_preimage_self]
  have hgs : f ∣_ V ≫ V.ι ≫ sX = (f ⁻¹ᵁ V).ι ≫ f ≫ sX := morphismRestrict_ι_assoc _ _ _
  have hZv : AlgebraicGeometry.IsVariety k (f ∣_ V ≫ V.ι ≫ sX) := by
    rw [hgs]; exact isVariety_opens_ι k (f ≫ sX) (f ⁻¹ᵁ V)
  have hZd : topologicalKrullDim (f ⁻¹ᵁ V) = 2 :=
    (topologicalKrullDim_opens k (f ≫ sX) (f ⁻¹ᵁ V)).trans hYd
  have hZs : IsSmoothScheme (f ∣_ V ≫ V.ι ≫ sX) := by
    have : Smooth (f ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hf1.isSmoothScheme
    rw [hgs]; exact (MMP.Mori.isSmoothScheme_iff _).mpr inferInstance
  have : IsProper (f ∣_ V) := IsZariskiLocalAtTarget.restrict hf1.isProper V
  have hgb : IsBirational (f ∣_ V) := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    (isBirationalMorphism_morphismRestrict hf1.isBirationalMorphism V)
  obtain ⟨W, h, hchain, e, he⟩ := MMP.Resolution.Bridges.factorsAsPointBlowups_of_isSmoothSurface
    k hVv hVs hVd hZv hZs hZd (f ∣_ V) rfl hgb
  cases hchain with
  | refl =>
    rw [← he, Category.comp_id]; infer_instance
  | @step W₀ h₀ hh w hw hwT =>
    exfalso
    obtain ⟨h1, h2, h3, -⟩ := pointBlowupChain_isSmoothSurface hVv hVs hVd hh
    obtain ⟨hBv, hBs, hBd, -⟩ := pointBlowupChain_isSmoothSurface hVv hVs hVd (hh.step w hw hwT)
    rw [Category.assoc] at hBv hBs
    obtain ⟨-, -, -, -, F, hF, hEP, -, hnum⟩ :=
      blowUp_singleton_smooth_isProper_isBirational_exceptional_selfIntersection
        h1 h2 h3 hw
    set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) with hπ
    set sB := π ≫ h₀ ≫ V.ι ≫ sX with hsB
    have : QuasiCompact sB := hBv.toQuasiCompact
    have := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBs).1
    have := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hBs).2
    have hsupp : ∀ b ∈ F.support, π b = w := fun b hb ↦
      (MMP.Threefold.Resolution.mem_support_iff_of_idealSheaf_eq_exceptionalIdeal hw hF b).mp hb
    -- the exceptional curve as a smooth rational curve
    obtain ⟨eL, heL⟩ := exists_iso_projSpace_projectiveLine (k := k)
    obtain ⟨eP, heP⟩ := hEP
    revert eP heP
    rw [← hF]
    intro eP heP
    have heP' : eP.inv ≫ F.idealSheaf.subschemeι ≫ sB = MMP.Intersection.ProjSpace.toSpec k _ := by
      rw [Iso.inv_comp_eq, heP]
    have : IsProper (F.idealSheaf.subschemeι ≫ sB) := by
      rw [← Iso.hom_inv_id_assoc eP (F.idealSheaf.subschemeι ≫ sB), heP']; infer_instance
    have hdimF : topologicalKrullDim F.idealSheaf.subscheme = 1 := by
      rw [IsHomeomorph.topologicalKrullDim_eq eP.hom eP.hom.homeomorph.isHomeomorph]
      exact MMP.Threefold.Resolution.topologicalKrullDim_projSpace_one k
    let eC : projectiveLine k ≅ F.idealSheaf.subscheme := eL ≪≫ eP.symm
    have heC : eC.hom ≫ F.idealSheaf.subschemeι ≫ sB = projectiveLine k ↘ Spec (.of k) := by
      simp only [eC, Iso.trans_hom, Iso.symm_hom, Category.assoc, heP', heL]
    have hrat : IsSmoothRationalCurve sB F.idealSheaf :=
      ⟨⟨⟨F.integral, hdimF⟩, ‹_›, eC.hom, heC, inferInstance, isBirationalMorphism_of_isIso _⟩,
        eC, heC⟩
    let CB : ProperCurve sB := ⟨F.genericPoint, isProperCurve_genericPoint _ F hdimF⟩
    have hnum' := MMP.Mori.isIntersectionNumber_of_properCurve _
      (isQCartier_single_of_isSmoothScheme hBs F) CB F rfl
    rw [hnum CB rfl, toQDivisor_single, Int.cast_one] at hnum'
    -- transport it to `Y`
    let j := e.inv ≫ (f ⁻¹ᵁ V).ι
    have hj : j ≫ f ≫ sX = sB := by
      simp only [j, Category.assoc]
      rw [← hgs, ← he]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    have hjf : ∀ b, f (j b) = V.ι (h₀ (π b)) := by
      intro b
      have : j ≫ f = π ≫ h₀ ≫ V.ι := by
        simp only [j, Category.assoc]
        rw [← morphismRestrict_ι, ← he]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Scheme.Hom.comp_apply, this]
      rfl
    apply hf.2
    refine exists_exceptional_minusOneCurve_of_isOpenImmersion sX f hf1.isSmoothScheme j sB hj
      hBs F hrat hnum' fun b hb hbir ↦ ?_
    -- a point of `F` over the biregular locus: compare coheights at `ξ` and a closed point
    have hξ : F.genericPoint ∈ F.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have : CompactSpace (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) :=
      QuasiCompact.compactSpace_of_compactSpace sB
    obtain ⟨c, hc, hccl⟩ := IsClosed.exists_closed_singleton F.idealSheaf.support.isClosed ⟨_, hξ⟩
    have hfx : ∀ b' ∈ F.support, f (j b') = f (j b) := fun b' hb' ↦ by
      rw [hjf, hjf, hsupp b' hb', hsupp b hb]
    have hcoh : ∀ b' ∈ F.support, Order.coheight (f (j b')) = Order.coheight b' := by
      intro b' hb'
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f (by rw [hfx b' hb']; exact hbir)]
      exact Topology.IsOpenEmbedding.coheight_eq _ j.isOpenEmbedding
    have h1' := hcoh _ hξ
    have h2' := hcoh _ hc
    rw [hfx _ hξ] at h1'
    rw [hfx _ hc, h1', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
      MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hBv hBd hccl] at h2'
    exact absurd h2' (by norm_num)

/-- **Existence of minimal resolutions of normal surfaces.** Over an algebraically closed field
`k`, every normal surface `X` admits a proper birational `k`-morphism `f : Y ⟶ X` from a smooth
surface `Y` which is a minimal resolution (no `f`-exceptional smooth rational curve of
self-intersection `-1`) and restricts to an isomorphism over the smooth locus of `X`. -/
@[mmp "lem_mmp_foundation_alg_closed_minimal_surface_resolution"]
public theorem exists_isMinimalSurfaceResolution {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX)
    (hdim : topologicalKrullDim X = 2) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      AlgebraicGeometry.IsVariety k (f ≫ sX) ∧ topologicalKrullDim Y = 2 ∧
      (∃ (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y),
        IsMinimalSurfaceResolution sX f) ∧
      IsIso (f ∣_ smoothLocus sX) := by
  classical
  have hex : ∃ n : ℕ, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), AlgebraicGeometry.IsVariety k (f ≫ sX) ∧
      IsSmoothResolution sX f ∧ topologicalKrullDim Y = 2 ∧
      {E : MMP.Mori.PrimeDivisor Y | E.support ⊆ (exceptionalSet f : Set Y)}.ncard = n := by
    obtain ⟨Y, sY, f, hY, hsm, hYd, rfl, hp, hb⟩ :=
      exists_smooth_isProper_isBirationalMorphism_of_isNormalVariety k sX hX hdim
    have : Smooth (f ≫ sX) := hsm
    have hs : IsSmoothScheme (f ≫ sX) := top_le_iff.mp (le_sSup (by
      change Smooth ((⊤ : Y.Opens).ι ≫ (f ≫ sX)); infer_instance))
    exact ⟨_, Y, f, hY, ⟨hp, hb, hs⟩, hYd, rfl⟩
  obtain ⟨Y, f, hY, hf, hYd, hn⟩ := Nat.find_spec hex
  have : QuasiCompact (f ≫ sX) := hY.toQuasiCompact
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme
    hf.isSmoothScheme
  have hmin : IsMinimalSurfaceResolution sX f := ⟨hf, fun ⟨E, hE, hEr, hEE⟩ => by
    obtain ⟨Y', f', hY', hf', hY'd, hlt⟩ :=
      exists_ncard_lt_of_isMinusOneCurve k sX hX hdim f hY hf hYd E hE hEr hEE
    exact Nat.find_min hex (hn ▸ hlt) ⟨Y', f', hY', hf', hY'd, rfl⟩⟩
  exact ⟨Y, f, hY, hYd, ⟨‹_›, ‹_›, ‹_›, hmin⟩,
    isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution k sX hX hdim f hY hYd hmin⟩

end Existence

end MMP.Mori

namespace MMP.Flips

open MMP.Mori

section MinimalGermResolution

/-- A morphism restricting to an isomorphism over `V` is injective on `f⁻¹(V)`. -/
private lemma eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : Y ⟶ X) (V : X.Opens)
    [IsIso (f ∣_ V)] {y₁ y₂ : Y} (h₁ : y₁ ∈ f ⁻¹ᵁ V) (h : f y₁ = f y₂) : y₁ = y₂ := by
  have h₂ : y₂ ∈ f ⁻¹ᵁ V := show f y₂ ∈ V from h ▸ h₁
  have key (a : (f ⁻¹ᵁ V).toScheme) : V.ι ((f ∣_ V) a) = f ((f ⁻¹ᵁ V).ι a) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h' := (key ⟨y₁, h₁⟩).trans (h.trans (key ⟨y₂, h₂⟩).symm)
  exact congrArg Subtype.val
    ((f ∣_ V).isOpenEmbedding.injective (V.ι.isOpenEmbedding.injective h'))

/-- A curve is not supported at a single point. -/
private lemma not_subsingleton_support_of_isCurveIn {Z : Scheme.{u}} {C : Z.IdealSheafData}
    (hC : IsCurveIn C) : ¬ (C.support : Set Z).Subsingleton := fun hs => by
  have : Subsingleton C.subscheme := ⟨fun a b => C.subschemeι.isClosedEmbedding.injective <|
    hs (C.range_subschemeι ▸ ⟨a, rfl⟩) (C.range_subschemeι ▸ ⟨b, rfl⟩)⟩
  have : DiscreteTopology C.subscheme := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.subscheme
  rw [hC.2] at h0
  exact absurd h0 (by decide)

/-- An exceptional curve of `f` over `P` does not meet the open set over which `f` is an
isomorphism: there `f` is injective, so the curve would collapse to a point. -/
private lemma notMem_preimage_of_isGermExceptionalCurve {X Y : Scheme.{u}} {f : Y ⟶ X} {P : X}
    {E : MMP.Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P E) (V : X.Opens)
    (hV : IsIso (f ∣_ V))
    {y : Y} (hy : y ∈ E.support) : y ∉ f ⁻¹ᵁ V := fun hyV =>
  not_subsingleton_support_of_isCurveIn hE.2 fun z hz z' hz' => by
    have hP {w} (hw : w ∈ E.support) : f w = f y :=
      (hE.1.prop.2 hw).trans (hE.1.prop.2 hy).symm
    have hmem {w} (hw : w ∈ E.support) : w ∈ f ⁻¹ᵁ V := by
      change f w ∈ V; rw [hP hw]; exact hyV
    exact eq_of_isIso_morphismRestrict f V (hmem hz) ((hP hz).trans (hP hz').symm)

/-- **Existence of minimal resolutions of surface germs.** Over an algebraically closed field
`k` of arbitrary characteristic, every surface germ `(X, P)` (`MMP.Mori.IsSurfaceGerm`) admits a
minimal resolution `f : Y ⟶ X` (`MMP.Flips.IsMinimalGermResolution`). -/
@[mmp "lem_mmp_foundation_fa3_minimal_resolution_all_char"]
public theorem exists_isMinimalGermResolution {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {P : X} (hP : IsSurfaceGerm sX P) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : QuasiCompact (f ≫ sX)) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y), IsMinimalGermResolution sX P f := by
  obtain ⟨Y, f, -, hdimY, ⟨hqc, hln, hn, hmin⟩, hiso⟩ :=
    exists_isMinimalSurfaceResolution sX hP.1 hP.2.1
  have hle : smoothLocus sX ≤ biregularLocus f := le_biregularLocus hiso
  refine ⟨Y, f, hqc, hln, hn, ⟨hP, hmin.1, hdimY, ⟨⟨{P}ᶜ, hP.2.2.1.isOpen_compl⟩, rfl,
    isBiregular_iff_le_biregularLocus.mpr (le_trans hP.2.2.2 hle)⟩⟩, ?_⟩
  rintro ⟨E, hE, hsr, hint⟩
  exact hmin.2 ⟨E, fun y hy hyV =>
    notMem_preimage_of_isGermExceptionalCurve hE _ (isBiregular_biregularLocus f) hy hyV, hsr, hint⟩

/-- A minimal resolution of a surface germ is a minimal surface resolution: an `f`-exceptional
prime divisor lies over `P`, so a smooth rational `(-1)`-curve among them would be an exceptional
curve of the germ resolution. -/
public theorem IsMinimalGermResolution.isMinimalSurfaceResolution {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsMinimalGermResolution sX P f) : IsMinimalSurfaceResolution sX f := by
  refine ⟨hf.1.isSmoothResolution, ?_⟩
  rintro ⟨E, hEsub, hsm, hint⟩
  have : IsIntegral Y := hf.1.isIntegral sX
  obtain ⟨hScl, hSne⟩ := hf.1.isClosed_preimage_and_ne_univ
  obtain ⟨U, hU, hiso⟩ := hf.1.isIso_away
  have hsub : (E.support : Set Y) ⊆ f.base ⁻¹' {P} := fun y hy ↦ by_contra fun hne ↦
    hEsub hy (le_biregularLocus (V := U) hiso (show f y ∈ (U : Set X) from hU ▸ hne))
  exact hf.2 ⟨E, ⟨maximal_support_of_subset hScl hSne E hsub, hsm.1.1⟩, hsm, hint⟩

/-- **Every resolution dominates the minimal resolution.** Let `f : Y ⟶ X` be a minimal
resolution of the surface germ `(X, P)` over an algebraically closed field `k`, `U` an open
neighbourhood of `P` and `h : Y' ⟶ U` a resolution of `U` (`IsSmoothResolution`).
Then there is a unique `h' : Y' ⟶ f ⁻¹ᵁ U` with `h' ≫ f ∣_ U = h`. -/
@[mmp "lem_mmp_foundation_fa3_every_resolution_dominates_minimal"]
public theorem IsMinimalGermResolution.existsUnique_comp_eq {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    (hf : IsMinimalGermResolution sX P f) {U : X.Opens} (hPU : P ∈ U) {Y' : Scheme.{u}}
    (h : Y' ⟶ U) (hh : IsSmoothResolution (U.ι ≫ sX) h) :
    ∃! h' : Y' ⟶ f ⁻¹ᵁ U, h' ≫ f ∣_ U = h :=
  (MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f hf.1.isSurfaceGerm.1
    hf.1.isSurfaceGerm.2.1 hf.isMinimalSurfaceResolution).2 U Y' h hh

end MinimalGermResolution

section LogTerminal

open TopologicalSpace

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y}

/-- A proper morphism `h'` of integral schemes into a normal noetherian `Y₂` is birational when
its composite with a proper birational `g : Y₂ ⟶ Z` is: `h'` sends the generic point to the
generic point and its stalk map there is an isomorphism, since those of `g` and `h' ≫ g` are. -/
private theorem isBirationalMorphism_of_comp {Y₁ Y₂ Z : Scheme.{u}} [IsIntegral Y₁]
    [IsIntegral Y₂] [IsIntegral Z] [IsNormal Y₂] [IsLocallyNoetherian Y₂] [IsLocallyNoetherian Z]
    (h' : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Z) [IsProper h'] [IsProper g]
    (hg : IsBirationalMorphism g) (hh : IsBirationalMorphism (h' ≫ g)) :
    IsBirationalMorphism h' := by
  have hbg := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg
  have hbh := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hh
  have := hh.isDominant
  have hη : h' (genericPoint Y₁) = genericPoint Y₂ := by
    have hm : h' (genericPoint Y₁) ∈ g ⁻¹' {genericPoint Z} := by
      change g (h' _) = _
      rw [← Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
    rwa [preimage_genericPoint g hbg] at hm
  have hb' : AlgebraicGeometry.IsBirational h' := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hη]
      exact Set.bijOn_singleton.mpr rfl
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      have h1 := hbh.isIso_stalkMap (genericPoint Y₁) (by rw [genericPoints_eq_singleton]; rfl)
      rw [Scheme.Hom.stalkMap_comp] at h1
      exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
        (hbg.isIso_stalkMap (h' (genericPoint Y₁)) (by rw [hη, genericPoints_eq_singleton]; rfl))
        h1
  have hid : AlgebraicGeometry.IsBirational (𝟙 Y₂) :=
    MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism (isBirationalMorphism_of_isIso _)
  simpa using isBirationalMorphism_comp_of_isBirational (𝟙 Y₂) h' hid hb'

/-- The identity of a normal variety is a small morphism. -/
private theorem isSmallMorphism_id {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    (hZ : IsNormalVariety k sZ) : MMP.Fourfold.IsSmallMorphism sZ sZ (𝟙 Z) where
  isNormalVariety_source := hZ
  isNormalVariety_target := hZ
  comp_eq := Category.id_comp _
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso _
  two_le_codimension := by
    rw [(exceptionalSet_eq_bot_iff (𝟙 Z)).mpr inferInstance, le_closedsCodimension_iff]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hW hx) (by simp)

/-- **The birational transform of an exceptional curve on a log resolution.** Let `f` be a
minimal resolution of `(X, P)`, `U ∋ P` open and `h : Y' ⟶ U` a log resolution. A prime divisor
`E₀` of `f⁻¹(U)` lying over `P` has a birational transform `E'` on `Y'` (through the factorization
`h = h' ≫ f ∣_ U` of `MMP.Flips.IsMinimalGermResolution.existsUnique_comp_eq`) which is
`h`-exceptional and has the valuation of `E₀`. -/
private theorem exists_isExceptional_valuation_eq [IsAlgClosed k]
    (hf : IsMinimalGermResolution sX P f) [IsProper f] {U : X.Opens} (hPU : P ∈ U) [Nonempty U]
    [CompactSpace U] (hdimU : topologicalKrullDim U = 2) {D : RDivisor U} {Y' : Scheme.{u}}
    (h : Y' ⟶ U) (hh : MMP.Flips.IsLogResolution (U.ι ≫ sX) D h)
    (hYU : IsNormalVariety k ((f ∣_ U) ≫ U.ι ≫ sX)) (hfU : IsBirationalMorphism (f ∣_ U))
    (E₀ : MMP.Mori.PrimeDivisor (f ⁻¹ᵁ U)) (hE₀ : ∀ y ∈ E₀.support, f ((f ⁻¹ᵁ U).ι y) = P) :
    ∃ (hY : IsNormalVariety k (h ≫ U.ι ≫ sX)) (hb : IsBirationalMorphism h) (hp : IsProper h)
      (E' : MMP.Mori.PrimeDivisor Y'),
      (ProperDivisorOver.mk ⟨Y', h, hY, hb, E'⟩ hp).IsExceptional ∧
      (ProperDivisorOver.mk ⟨Y', h, hY, hb, E'⟩ hp).valuation =
        (⟨_, f ∣_ U, hYU, hfU, E₀⟩ : DivisorOver k (U.ι ≫ sX)).valuation := by
  obtain ⟨hlogv, -, hsm, hp, hb, -⟩ := hh
  have hres : IsSmoothResolution (U.ι ≫ sX) h := ⟨hp, hb, hsm⟩
  obtain ⟨hY, -, -⟩ := hres.isNormalVariety hlogv.isNormalVariety
  obtain ⟨h', hh', -⟩ := hf.existsUnique_comp_eq hPU h hres
  subst hh'
  haveI := hYU.1.toIsIntegral
  haveI := hYU.2
  haveI : IsLocallyNoetherian (f ⁻¹ᵁ U) := inferInstance
  haveI : CompactSpace (f ⁻¹ᵁ U) := QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  haveI : NoetherianSpace (f ⁻¹ᵁ U) := (haveI : IsNoetherian (f ⁻¹ᵁ U) := {}; inferInstance)
  haveI := hY.1.toIsIntegral
  haveI := hY.2
  haveI : LocallyOfFiniteType ((h' ≫ f ∣_ U) ≫ U.ι ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y' :=
    LocallyOfFiniteType.isLocallyNoetherian ((h' ≫ f ∣_ U) ≫ U.ι ≫ sX)
  haveI : IsProper (h' ≫ f ∣_ U) := hp
  haveI : IsProper h' := IsProper.of_comp h' (f ∣_ U)
  have hb' := isBirationalMorphism_of_comp h' (f ∣_ U) hfU hb
  haveI := hb'.isDominant
  haveI := hfU.isDominant
  haveI := hb.isDominant
  obtain ⟨E', Q, hv, hE'Q, hQ⟩ :=
    MMP.Fourfold.exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hYU hb'
      (isSmallMorphism_id hYU) E₀
  refine ⟨hY, hb, hp, E', ?_, ?_⟩
  · have hmem : h' E'.genericPoint ∈ E₀.support := by
      have : h' E'.genericPoint ∈ Q.support := hE'Q ▸ ⟨_, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, rfl⟩
      rw [← hQ] at this
      simpa using this
    have hpt : (h' ≫ f ∣_ U) E'.genericPoint = ⟨P, hPU⟩ := Subtype.ext (by
      rw [Scheme.Hom.comp_apply, morphismRestrict_base_coe]
      exact hE₀ _ hmem)
    have hcl : IsClosed {(h' ≫ f ∣_ U) E'.genericPoint} := by
      have := hf.1.isSurfaceGerm.2.2.1.preimage U.ι.continuous
      convert this using 1
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage, hpt, Scheme.Opens.ι_apply]
      exact ⟨fun hx => hx ▸ rfl, fun hx => Subtype.ext hx⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    change topologicalKrullDim (closure {(h' ≫ f ∣_ U) E'.genericPoint} : Set _) + 2 ≤ _
    rw [hcl.closure_eq, hdimU]
    calc _ ≤ (0 : WithBot ℕ∞) + 2 :=
          add_le_add_left (topologicalKrullDim_zero_of_discreteTopology _) 2
      _ = 2 := by simp
  · ext t
    change E'.divisorialValuation (functionFieldMap (h' ≫ f ∣_ U) t) =
      E₀.divisorialValuation (functionFieldMap (f ∣_ U) t)
    rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    have := congrArg (fun v => v (functionFieldMap (f ∣_ U) t)) hv
    simpa only [PrimeDivisor.valuationOver_apply, functionFieldMap_id_apply] using this

/-- Restricting to an open subscheme commutes with forming `K + B` as an `ℝ`-divisor. -/
private theorem restrictOpen_toRDivisor_add {Z : Scheme.{u}} (U : Z.Opens) (K : Divisor Z)
    (B : QDivisor Z) :
    (Divisor.toRDivisor K + QDivisor.toRDivisor B).restrictOpen U =
      Divisor.toRDivisor (K.restrictOpen U) + (QDivisor.toRDivisor B).restrictOpen U :=
  Finsupp.ext fun _ => rfl

/-- Restricting a `ℚ`-divisor to an open subscheme commutes with viewing it as an `ℝ`-divisor. -/
private theorem toRDivisor_restrictOpen {Z : Scheme.{u}} (U : Z.Opens) (B : QDivisor Z) :
    QDivisor.toRDivisor (B.restrictOpen U) = (QDivisor.toRDivisor B).restrictOpen U :=
  Finsupp.ext fun _ => rfl

open scoped WithZero in
/-- A discrepancy `a(F, D_X)` is computed on a divisor `(Y, f, E)` over `X` with `ord_E = F`, and
`1 + a` is the log discrepancy of that divisor in the sense of
`MMP.Intersection.IsLogDiscrepancy`. -/
private theorem exists_isLogDiscrepancy_of_isDiscrepancy {n : ℕ} {K : Divisor X}
    {D_X : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : MMP.Flips.IsDiscrepancy sX n K D_X F a) :
    ∃ E : ProperDivisorOver k sX, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sX n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, rfl, hX, -, hω0, hLc, hL, L', hLpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r, L,
    L', hLc, fun Γ => ?_, hLpb, by ring⟩
  have := congrArg (fun G : RDivisor X => G.coeff Γ) hL
  simp only [coeff_sum_smul_toRDivisor] at this
  rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]

/-- **Log terminal germs have positive log discrepancy vectors** (FA 3.0.3, 3.2.2). If `(X, B)`
is log terminal near `P` (on some open neighbourhood `U` of `P`, `(U, B|_U)` is log terminal with
canonical divisor `K_X|_U`), the ground field `k` is algebraically closed, and `a` is the log
discrepancy vector of `(X, P; B)` on a minimal
resolution `f` of `(X, P)` with exceptional curves `E_1, …, E_n`, then `0 < a_j` for every
`j`. -/
@[mmp "lem_fa3_lt_implies_log_discrepancies_pos"]
public theorem IsGermLogDiscrepancyVector.pos_of_isLogTerminal [IsAlgClosed k] {a : Fin n → ℚ}
    (ha : IsGermLogDiscrepancyVector sX P B f E a) (hf : IsMinimalGermResolution sX P f)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    (hlt : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogTerminal (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)))
    (j : Fin n) : 0 < a j := by
  classical
  obtain ⟨(U : X.Opens), hPU, hltU⟩ := hlt
  have hPU : P ∈ U := hPU rfl
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨P, hPU⟩)
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
  obtain ⟨hlogU, hKU, hKBU, Y', h, hlog, hpos⟩ := hltU
  obtain ⟨hB, hgr, hE, -⟩ := id ha
  have hX : IsNormalVariety k sX := hB.1.1
  obtain ⟨hY, -, -⟩ := hgr.isSmoothResolution.isNormalVariety hX
  have hg := hgr.isSmoothResolution.isBirationalMorphism
  have hp := hgr.isSmoothResolution.isProper
  obtain ⟨a', hd, haj⟩ := ha.isLogDiscrepancy hK ⟨U, Set.singleton_subset_iff.mpr hPU,
    (restrictOpen_toRDivisor_add U K B ▸ hKBU : IsCartierCombination
      (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor K + QDivisor.toRDivisor B)))⟩
    j hY hg hp
  have hpair : IsPairWith sX 2 K B := ⟨hX, hK, QDivisor.isQCartier_of_isCartierCombination
    (by rw [map_add, QDivisor.toRDivisor_toQDivisor]; exact hd.2.1)⟩
  let D : DivisorOver k sX := ⟨Y, f, hY, hg, E j⟩
  obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK D
  obtain ⟨E₁, hE₁, hlog₁⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hd
  have hlogD := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hq hp
  have h1 : 1 + a' = 1 + (q : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hlogD hE₁
  have hgP : ∀ y ∈ (E j).support, f y = P := fun y hy =>
    (hE.isGermExceptionalCurve j).1.prop.2 hy
  have hmem : (E j).genericPoint ∈ (E j).support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨P, by rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure (hgP _ hmem).symm,
      hPU⟩
  obtain ⟨hYU, hfU, E', hE', -, hiff⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff hpair D U hcen
  have hqU := (hiff q).mp hq
  have hlogU' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hqU
    (inferInstance : IsProper (f ∣_ U))
  have hXU : IsNormalVariety k (U.ι ≫ sX) := hlogU.isNormalVariety
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXU hKU
  have hωK : divisorOfForm ω = K.restrictOpen U := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hω]
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨(E j).genericPoint, show f _ ∈ U from (hgP _ hmem) ▸ hPU⟩⟩
  have := hYU.isIntegral
  have := hYU.isNormal
  have := hYU.isLocallyNoetherian
  have : LocallyOfFiniteType ((f ∣_ U) ≫ U.ι ≫ sX) := hYU.1.toLocallyOfFiniteType
  have : IsDominant (f ∣_ U) := hfU.isDominant
  have : CompactSpace (f ⁻¹ᵁ U) := QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  have hKD : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm ω) + (QDivisor.toRDivisor B).restrictOpen U) :=
    hωK ▸ hKBU
  obtain ⟨G, hG, -⟩ := existsUnique_isRCartierPullback (f ∣_ U) hKD
  have hdU := isDiscrepancy_ordPullback_sub_coeff_pullback hXU ω hω0 (hωK ▸ hKU) hKD (f ∣_ U)
    hYU hfU hG E'
  rw [hωK] at hdU
  obtain ⟨E₂, hE₂, hlog₂⟩ := exists_isLogDiscrepancy_of_isDiscrepancy hdU
  have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₂
    (toRDivisor_restrictOpen U B ▸ hlogU') hE₂
  have hE'P : ∀ y ∈ E'.support, f ((f ⁻¹ᵁ U).ι y) = P := fun y hy =>
    hgP _ (by
      rw [← show OpenWeilRestriction.primeDivisorMap (f ⁻¹ᵁ U).ι E' = E j from hE']
      exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff _ E' y).mpr hy)
  obtain ⟨hY', hb', hp', E'', hex, hv⟩ := exists_isExceptional_valuation_eq hf hPU
    hKU.topologicalKrullDim_eq h hlog hYU hfU E' hE'P
  have h3 := hpos hY' hb' hp' E'' hex _ ⟨_, by rw [hv]; exact hdU, rfl⟩
  rw [h2, ← h1, ← haj] at h3
  exact_mod_cast h3

end LogTerminal

end MMP.Flips

end
